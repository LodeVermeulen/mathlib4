/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.SetTheory.Game.Basic
import Mathlib.SetTheory.Ordinal.NaturalOps

#align_import set_theory.game.ordinal from "leanprover-community/mathlib"@"b90e72c7eebbe8de7c8293a80208ea2ba135c834"

/-!
# Ordinals as games

We define the canonical map `Ordinal → SetTheory.PGame`, where every ordinal is mapped to the
game whose left set consists of all previous ordinals.

The map to surreals is defined in `Ordinal.toSurreal`.

# Main declarations

- `Ordinal.toPGame`: The canonical map between ordinals and pre-games.
- `Ordinal.toPGameEmbedding`: The order embedding version of the previous map.
-/


universe u

open SetTheory PGame

open scoped NaturalOps PGame

namespace Ordinal

/-- Converts an ordinal into the corresponding pre-game. -/
noncomputable def toPGame : Ordinal.{u} → PGame.{u}
  | o =>
    have : IsWellOrder o.out.α (· < ·) := isWellOrder_out_lt o
    ⟨o.out.α, PEmpty, fun x =>
      have := Ordinal.typein_lt_self x
      (typein (· < ·) x).toPGame,
      PEmpty.elim⟩
termination_by toPGame x => x

@[nolint unusedHavesSuffices]
theorem toPGame_def (o : Ordinal) :
    have : IsWellOrder o.out.α (· < ·) := isWellOrder_out_lt o
    o.toPGame = ⟨o.out.α, PEmpty, fun x => (typein (· < ·) x).toPGame, PEmpty.elim⟩ := by
  rw [toPGame]

@[simp, nolint unusedHavesSuffices]
theorem toPGame_leftMoves (o : Ordinal) : o.toPGame.LeftMoves = o.out.α := by
  rw [toPGame, LeftMoves]

@[simp, nolint unusedHavesSuffices]
theorem toPGame_rightMoves (o : Ordinal) : o.toPGame.RightMoves = PEmpty := by
  rw [toPGame, RightMoves]

instance isEmpty_zero_toPGame_leftMoves : IsEmpty (toPGame 0).LeftMoves := by
  rw [toPGame_leftMoves]; infer_instance

instance isEmpty_toPGame_rightMoves (o : Ordinal) : IsEmpty o.toPGame.RightMoves := by
  rw [toPGame_rightMoves]; infer_instance

/-- Converts an ordinal less than `o` into a move for the `PGame` corresponding to `o`, and vice
versa. -/
noncomputable def toLeftMovesToPGame {o : Ordinal} : Set.Iio o ≃ o.toPGame.LeftMoves :=
  (enumIsoOut o).toEquiv.trans (Equiv.cast (toPGame_leftMoves o).symm)

@[simp]
theorem toLeftMovesToPGame_symm_lt {o : Ordinal} (i : o.toPGame.LeftMoves) :
    ↑(toLeftMovesToPGame.symm i) < o :=
  (toLeftMovesToPGame.symm i).prop

@[nolint unusedHavesSuffices]
theorem toPGame_moveLeft_hEq {o : Ordinal} :
    have : IsWellOrder o.out.α (· < ·) := isWellOrder_out_lt o
    HEq o.toPGame.moveLeft fun x : o.out.α => (typein (· < ·) x).toPGame := by
  rw [toPGame]
  rfl

@[simp]
theorem toPGame_moveLeft' {o : Ordinal} (i) :
    o.toPGame.moveLeft i = (toLeftMovesToPGame.symm i).val.toPGame :=
  (congr_heq toPGame_moveLeft_hEq.symm (cast_heq _ i)).symm

theorem toPGame_moveLeft {o : Ordinal} (i) :
    o.toPGame.moveLeft (toLeftMovesToPGame i) = i.val.toPGame := by simp

/-- `0.to_pgame` has the same moves as `0`. -/
noncomputable def zeroToPgameRelabelling : toPGame 0 ≡r 0 :=
  Relabelling.isEmpty _

noncomputable instance uniqueOneToPgameLeftMoves : Unique (toPGame 1).LeftMoves :=
  (Equiv.cast <| toPGame_leftMoves 1).unique

@[simp]
theorem one_toPGame_leftMoves_default_eq :
    (default : (toPGame 1).LeftMoves) = @toLeftMovesToPGame 1 ⟨0, Set.mem_Iio.mpr zero_lt_one⟩ :=
  rfl

@[simp]
theorem to_leftMoves_one_toPGame_symm (i) :
    (@toLeftMovesToPGame 1).symm i = ⟨0, Set.mem_Iio.mpr zero_lt_one⟩ := by
  simp

theorem one_toPGame_moveLeft (x) : (toPGame 1).moveLeft x = toPGame 0 := by simp

/-- `1.to_pgame` has the same moves as `1`. -/
noncomputable def oneToPGameRelabelling : toPGame 1 ≡r 1 :=
  ⟨Equiv.equivOfUnique _ _, Equiv.equivOfIsEmpty _ _, fun i => by
    simpa using zeroToPgameRelabelling, isEmptyElim⟩

theorem toPGame_lf {a b : Ordinal} (h : a < b) : a.toPGame ⧏ b.toPGame := by
  convert moveLeft_lf (toLeftMovesToPGame ⟨a, h⟩); rw [toPGame_moveLeft]

theorem toPGame_le {a b : Ordinal} (h : a ≤ b) : a.toPGame ≤ b.toPGame := by
  refine' le_iff_forall_lf.2 ⟨fun i => _, isEmptyElim⟩
  rw [toPGame_moveLeft']
  exact toPGame_lf ((toLeftMovesToPGame_symm_lt i).trans_le h)

theorem toPGame_lt {a b : Ordinal} (h : a < b) : a.toPGame < b.toPGame :=
  ⟨toPGame_le h.le, toPGame_lf h⟩

theorem toPGame_nonneg (a : Ordinal) : 0 ≤ a.toPGame :=
  zeroToPgameRelabelling.ge.trans <| toPGame_le <| Ordinal.zero_le a

@[simp]
theorem toPGame_lf_iff {a b : Ordinal} : a.toPGame ⧏ b.toPGame ↔ a < b :=
  ⟨by contrapose; rw [not_lt, not_lf]; exact toPGame_le, toPGame_lf⟩

@[simp]
theorem toPGame_le_iff {a b : Ordinal} : a.toPGame ≤ b.toPGame ↔ a ≤ b :=
  ⟨by contrapose; rw [not_le, PGame.not_le]; exact toPGame_lf, toPGame_le⟩

@[simp]
theorem toPGame_lt_iff {a b : Ordinal} : a.toPGame < b.toPGame ↔ a < b :=
  ⟨by contrapose; rw [not_lt]; exact fun h => not_lt_of_le (toPGame_le h), toPGame_lt⟩

@[simp]
theorem toPGame_equiv_iff {a b : Ordinal} : (a.toPGame ≈ b.toPGame) ↔ a = b := by
  -- Porting note: was `rw [PGame.Equiv]`
  change _ ≤_ ∧ _ ≤ _ ↔ _
  rw [le_antisymm_iff, toPGame_le_iff, toPGame_le_iff]

theorem toPGame_injective : Function.Injective Ordinal.toPGame := fun _ _ h =>
  toPGame_equiv_iff.1 <| equiv_of_eq h

@[simp]
theorem toPGame_eq_iff {a b : Ordinal} : a.toPGame = b.toPGame ↔ a = b :=
  toPGame_injective.eq_iff

/-- The order embedding version of `toPGame`. -/
@[simps]
noncomputable def toPGameEmbedding : Ordinal.{u} ↪o PGame.{u} where
  toFun := Ordinal.toPGame
  inj' := toPGame_injective
  map_rel_iff' := @toPGame_le_iff

/-- The sum of ordinals as games corresponds to natural addition of ordinals. -/
theorem toPGame_add : ∀ a b : Ordinal.{u}, a.toPGame + b.toPGame ≈ (a ♯ b).toPGame
  | a, b => by
    refine' ⟨le_of_forall_lf (fun i => _) isEmptyElim, le_of_forall_lf (fun i => _) isEmptyElim⟩
    · apply leftMoves_add_cases i <;>
      intro i <;>
      let wf := toLeftMovesToPGame_symm_lt i <;>
      (try rw [add_moveLeft_inl]) <;>
      (try rw [add_moveLeft_inr]) <;>
      rw [toPGame_moveLeft', lf_congr_left (toPGame_add _ _), toPGame_lf_iff]
      · exact nadd_lt_nadd_right wf _
      · exact nadd_lt_nadd_left wf _
    · rw [toPGame_moveLeft']
      rcases lt_nadd_iff.1 (toLeftMovesToPGame_symm_lt i) with (⟨c, hc, hc'⟩ | ⟨c, hc, hc'⟩) <;>
      rw [← toPGame_le_iff, ← le_congr_right (toPGame_add _ _)] at hc' <;>
      apply lf_of_le_of_lf hc'
      · apply add_lf_add_right
        rwa [toPGame_lf_iff]
      · apply add_lf_add_left
        rwa [toPGame_lf_iff]
termination_by toPGame_add a b => (a, b)

@[simp]
theorem toPGame_add_mk' (a b : Ordinal) : (⟦a.toPGame⟧ + ⟦b.toPGame⟧ : Game) = ⟦(a ♯ b).toPGame⟧ :=
  Quot.sound (toPGame_add a b)

end Ordinal
