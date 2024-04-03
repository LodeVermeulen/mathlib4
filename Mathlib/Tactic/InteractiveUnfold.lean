/-
Copyright (c) 2023 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
import Lean
import Std.Lean.Position
import Std.Lean.Name
import Mathlib.Tactic.Widget.SelectPanelUtils
import Mathlib.Lean.SubExpr
import Mathlib.Lean.Meta.KAbstractPositions

/-! # Interactive unfolding -/

open Lean Meta Server Widget ProofWidgets Jsx

namespace Mathlib.Tactic.InteractiveUnfold

/-- same as `unfoldDefinition?`, except it handles well founded recursive definitions better. -/
def unfold? (e : Expr) : MetaM (Option Expr) := do
  if let .const n lvls := e.getAppFn then
    /- unfolding a constant defined with well founded recursion -/
    if let some info := Elab.WF.eqnInfoExt.find? (← getEnv) n then
      if info.levelParams.length == lvls.length then
        return (info.value.instantiateLevelParams info.levelParams lvls).beta e.getAppArgs
    /- unfolding any other constant -/
    else if let some e ← unfoldDefinition? e then
      return e
  return none

/-- Unfold a class projection when the instance is tagged with `@[default_instance]`.
similar to `Lean.Meta.unfoldProjInst?`. -/
def unfoldProjDefaultInst? (e : Expr) : MetaM (Option Expr) := do
  match e.getAppFn with
  | .const declName .. =>
    match ← getProjectionFnInfo? declName with
    | some { fromClass := true, ctorName, .. } => do
      -- get the list of default instances of the class
      let some (ConstantInfo.ctorInfo c) := (← getEnv).find? ctorName | return none
      let defaults ← getDefaultInstances c.induct
      if defaults.isEmpty then return none

      let some e ← withDefault <| unfoldDefinition? e | return none
      let .proj _ i c := e.getAppFn | return none
      -- check that the structure `c` comes from one of the default instances
      let .const inst _ := c.getAppFn | return none
      unless defaults.any (·.1 == inst) do return none

      let some r ← project? c i | return none
      return mkAppN r e.getAppArgs |>.headBeta
    | _ => return none
  | _ => return none

/-- Return the consecutive unfoldings of `e`. -/
partial def unfolds (e : Expr) : MetaM (Array Expr) := do
  let e' ← whnfCore e
  go e' (if e == e' then #[] else #[e'])
where
  /-- Append the unfoldings of `e` to `acc`. Assume `e` is in `whnfCore` form. -/
  go (e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
    withCatchingRuntimeEx do
    try
      withoutCatchingRuntimeEx do withIncRecDepth do
      if let some e := e.etaExpandedStrict? then
        return ← go e (acc.push e)
      if let some e ← reduceNat? e then
        return acc.push e
      if let some e ← reduceNative? e then
        return acc.push e
      if let some e ← unfoldProjDefaultInst? e then
        let e ← whnfCore e
        return ← go e acc
      if let some e ← unfold? e then
        -- Note: whnfCore can give a recursion depth error
        let e ← whnfCore e
        return ← go e (acc.push e)
      return acc
    catch _ =>
      return acc

/-- Determine whether `e` contains no internal names. -/
def isUserFriendly (e : Expr) : Bool :=
  !e.foldConsts (init := false) (fun name => (· || name.isInternalDetail))

/-- Return the consecutive unfoldings of `e` that are user friendly. -/
def filteredUnfolds (e : Expr) : MetaM (Array Expr) :=
  return (← unfolds e).filter isUserFriendly

end InteractiveUnfold

/-- Return the rewrite tactic string `rw (config := ..) [← ..] at ..` -/
def mkRewrite (occ : Option Nat) (symm : Bool) (rewrite : String)
    (loc : Option Name) : String :=
  let cfg := match occ with
    | some n => s! " (config := \{ occs := .pos [{n}]})"
    | none => ""
  let loc := match loc with
    | some n => s! " at {n}"
    | none => ""
  let symm := if symm then "← " else ""
  s! "rw{cfg} [{symm}{rewrite}]{loc}"

/-- Return a string representation of the expression suitable for pasting into the editor. -/
def PasteString (e : Expr) : MetaM String :=
  withOptions (fun _ => Options.empty
    |>.setBool `pp.universes false
    |>.setBool `pp.match false
    |>.setBool `pp.unicode.fun true) do
  return Format.pretty (← Meta.ppExpr e) (width := 90) (indent := 2)

namespace InteractiveUnfold

/-- Return the tactic string that does the unfolding. -/
def tacticString (e unfold : Expr) (occ : Option Nat) (loc : Option Name) : MetaM String := do
  let rfl := s! "show {← PasteString (← mkEq e unfold)} from rfl"
  return mkRewrite occ false rfl loc

/-- Render the unfolds of `e` as given by `filteredUnfolds`, with buttons at each suggestion
for pasting the rewrite tactic. Return `none` when there are no unfolds. -/
def renderUnfolds (e : Expr) (occ : Option Nat) (loc : Option Name) (range : Lsp.Range)
    (doc : FileWorker.EditableDocument) : MetaM (Option Html) := do
  let results ← filteredUnfolds e
  if results.isEmpty then
    return none
  let core ← results.mapM fun unfold => do
    let tactic ← tacticString e unfold occ loc
    return <li> {
      .element "p" #[] <|
        #[<span className="font-code" style={json% { "white-space" : "pre-wrap" }}> {
          Html.ofComponent MakeEditLink
            (.ofReplaceRange doc.meta range tactic)
            #[.text $ Format.pretty $ (← Meta.ppExpr unfold)] }
        </span>]
      } </li>
  return <details «open»={true}>
    <summary className="mv2 pointer">
      {.text "Definitional rewrites:"}
    </summary>
    {.element "ul" #[("style", json% { "padding-left" : "30px"})] core}
  </details>


@[server_rpc_method_cancellable]
private def rpc (props : SelectInsertParams) : RequestM (RequestTask Html) :=
  RequestM.asTask do
  let doc ← RequestM.readDoc
  let some loc := props.selectedLocations.back? |
    return .text "unfold?: Please shift-click an expression."
  if loc.loc matches .hypValue .. then
    return .text "unfold? doesn't work on the value of a let-bound free variable."
  let some goal := props.goals[0]? |
    return .text "There is no goal to solve!"
  if loc.mvarId != goal.mvarId then
    return .text "The selected expression should be in the main goal."
  goal.ctx.val.runMetaM {} do
    let md ← goal.mvarId.getDecl
    let lctx := md.lctx |>.sanitizeNames.run' {options := (← getOptions)}
    Meta.withLCtx lctx md.localInstances do

      let some (subExpr, occ) ← viewKAbstractSubExpr (← loc.rootExpr) loc.pos |
        return .text "expressions with bound variables are not supported"
      let html ← renderUnfolds subExpr occ (← loc.location) props.replaceRange doc
      return html.getD
        <span>
          No unfolds found for {<InteractiveCode fmt={← ppExprTagged subExpr}/>}
        </span>

/-- The component called by the `unfold?` tactic -/
@[widget_module]
def UnfoldComponent : Component SelectInsertParams :=
  mk_rpc_widget% InteractiveUnfold.rpc


/-- Unfold the selected expression any number of times.
- After each unfold?, we apply `whnfCore` to simplify the expression.
- Explicit natural number expressions are evaluated.
- The results of class projections of instances marked with `@[default_instance]` are not shown.
  This is relevant for notational type classes like `+`: we don't want to suggest `Add.add a b`
  as an unfolding of `a + b`. Similarly for `OfNat n : Nat` which unfolds into `n : Nat`.

To use `unfold?`, shift-click an expression in the tactic state.
This gives a list of rewrite suggestions for the selected expression.
Click on a suggestion to replace `unfold?` by a tactic that performs this rewrite.
-/
elab stx:"unfold?" : tactic => do
  let some range := (← getFileMap).rangeOfStx? stx | return
  Widget.savePanelWidgetInfo (hash UnfoldComponent.javascript)
    (pure $ json% { replaceRange : $range }) stx

/-- `#unfold? e` gives all unfolds of `e`.
In tactic mode, use `unfold?` instead. -/
syntax (name := unfoldCommand) "#unfold?" term : command

open Elab
/-- Elaborate a `#unfold?` command. -/
@[command_elab unfoldCommand]
def elabUnfoldCommand : Command.CommandElab := fun stx =>
  withoutModifyingEnv <| Command.runTermElabM fun _ => Term.withDeclName `_unfold do
    let e ← Term.elabTerm stx[1] none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← Term.levelMVarToParam (← instantiateMVars e)  let e ← instantiateMVars e
    let unfolds ← filteredUnfolds e
    if unfolds.isEmpty then
      logInfo m! "No unfolds found for {e}"
    else
      let unfolds := unfolds.toList.map (m! "· {·}")
      logInfo (m! "Unfolds for {e}:\n"
        ++ .joinSep unfolds "\n")
