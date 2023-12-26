/-
Copyright (c) 2024 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Local graph operations

This file defines some single-graph operations that modify a finite number of vertices
and proves basic theorems about them. When the graph itself has a finite number of vertices
we also prove theorems about the number of edges in the modified graphs.

## Main definitions

* `G.replaceVertex s t` is `G` with `t` replaced by a copy of `s`,
  removing the `s-t` edge if present.
* `G.addEdge s t` is `G` with the `s-t` edge added, if that is a valid edge.
-/


open Finset

namespace SimpleGraph

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) (s t : V)

section ReplaceVertex

/-- The graph formed by forgetting `t`'s neighbours and instead giving it those of `s`. The `s-t`
edge is removed if present. -/
abbrev replaceVertex : SimpleGraph V where
  Adj v w := if v = t then if w = t then False else G.Adj s w
                      else if w = t then G.Adj v s else G.Adj v w
  symm v w := by dsimp only; split_ifs <;> simp [adj_comm]

/-- There is never an `s-t` edge in `G.replaceVertex s t`. -/
theorem not_adj_replaceVertex_same : ¬(G.replaceVertex s t).Adj s t := by simp

@[simp]
theorem replaceVertex_self : G.replaceVertex s s = G := by
  ext; dsimp only; split_ifs <;> simp_all [adj_comm]

/-- Except possibly for `t`, the neighbours of `s` in `G.replaceVertex s t` are its neighbours in
`G`. -/
lemma adj_replaceVertex_iff_of_ne_left {w : V} (hw : w ≠ t) :
    (G.replaceVertex s t).Adj s w ↔ G.Adj s w := by simp [hw]

/-- Except possibly for itself, the neighbours of `t` in `G.replaceVertex s t` are the neighbours of
`s` in `G`. -/
lemma adj_replaceVertex_iff_of_ne_right {w : V} (hw : w ≠ t) :
    (G.replaceVertex s t).Adj t w ↔ G.Adj s w := by simp [hw]

/-- Adjacency in `G.replaceVertex s t` which does not involve `t` is the same as that of `G`. -/
lemma adj_replaceVertex_iff_of_ne {v w : V} (hv : v ≠ t) (hw : w ≠ t) :
    (G.replaceVertex s t).Adj v w ↔ G.Adj v w := by simp [hv, hw]

variable [Fintype V] {s t} [DecidableRel G.Adj]

theorem edgeFinset_replaceVertex_of_not_adj (hn : ¬G.Adj s t) : (G.replaceVertex s t).edgeFinset =
    G.edgeFinset \ G.incidenceFinset t ∪ (G.neighborFinset s).image (fun v => ⟦(v, t)⟧) := by
  ext e
  refine' e.inductionOn _
  simp only [Set.mem_toFinset, mem_edgeSet, mem_union, mem_sdiff, mem_incidenceFinset,
    mk'_mem_incidenceSet_iff]
  intros; split_ifs
  · simp_all
  · aesop
  · constructor <;> (simp only [adj_comm]; aesop)
  · aesop

theorem card_edgeFinset_replaceVertex_of_not_adj (hn : ¬G.Adj s t) :
    (G.replaceVertex s t).edgeFinset.card = G.edgeFinset.card + G.degree s - G.degree t := by
  have inc : G.incidenceFinset t ⊆ G.edgeFinset := by
    unfold incidenceFinset edgeFinset
    simp [G.incidenceSet_subset t]
  rw [G.edgeFinset_replaceVertex_of_not_adj hn, card_disjoint_union, card_sdiff inc,
    tsub_add_eq_add_tsub <| card_le_of_subset inc, card_incidenceFinset_eq_degree]
  · congr 2
    rw [card_image_of_injective, card_neighborFinset_eq_degree]
    unfold Function.Injective
    aesop
  · rw [disjoint_iff_ne]
    intro e1 he1 e2 he2
    have yes : t ∈ e2 := by
      simp only [mem_image, mem_neighborFinset] at he2
      obtain ⟨_, ⟨_, p⟩⟩ := he2
      rw [← p]
      exact Sym2.mem_mk''_right _ t
    have no : t ∉ e1 := by
      rw [mem_sdiff, mem_incidenceFinset] at he1
      obtain ⟨ha, hb⟩ := he1
      contrapose hb
      rw [not_not] at hb ⊢
      simp_all [incidenceSet]
    intro
    simp_all only [Sym2.mem_iff, or_true, not_true_eq_false]

theorem edgeFinset_replaceVertex_of_adj (ha : G.Adj s t) :
    (G.replaceVertex s t).edgeFinset = (G.edgeFinset \ G.incidenceFinset t ∪
      (G.neighborFinset s).image (fun v => ⟦(v, t)⟧)) \ {⟦(t, t)⟧} := by
  ext e
  refine' e.inductionOn _
  simp only [Set.mem_toFinset, mem_edgeSet, mem_union, mem_sdiff, mem_incidenceFinset,
    mk'_mem_incidenceSet_iff]
  intros; split_ifs
  · simp_all
  · aesop
  · constructor <;> (simp only [adj_comm]; aesop)
  · aesop

theorem card_edgeFinset_replaceVertex_of_adj (ha : G.Adj s t) :
    (G.replaceVertex s t).edgeFinset.card = G.edgeFinset.card + G.degree s - G.degree t - 1 := by
  have inc : G.incidenceFinset t ⊆ G.edgeFinset := by
    unfold incidenceFinset edgeFinset
    simp [G.incidenceSet_subset t]
  rw [G.edgeFinset_replaceVertex_of_adj ha, card_sdiff, card_disjoint_union, card_sdiff inc,
    tsub_add_eq_add_tsub <| card_le_of_subset inc, card_incidenceFinset_eq_degree]
  · congr 2
    rw [card_image_of_injective, card_neighborFinset_eq_degree]
    unfold Function.Injective
    aesop
  · rw [disjoint_iff_ne]
    intro e1 he1 e2 he2
    have yes : t ∈ e2 := by
      simp only [mem_image, mem_neighborFinset] at he2
      obtain ⟨_, ⟨_, p⟩⟩ := he2
      rw [← p]
      exact Sym2.mem_mk''_right _ t
    have no : t ∉ e1 := by
      rw [mem_sdiff, mem_incidenceFinset] at he1
      obtain ⟨ha, hb⟩ := he1
      contrapose hb
      rw [not_not] at hb ⊢
      simp_all [incidenceSet]
    intro
    simp_all only [Sym2.mem_iff, or_true, not_true_eq_false]
  · simp [ha]

end ReplaceVertex

section AddEdge

/-- Given a vertex pair, add the corresponding edge to the graph's edge set if not present. -/
abbrev addEdge : SimpleGraph V where
  Adj v w := G.Adj v w ∨ s ≠ t ∧ (s = v ∧ t = w ∨ s = w ∧ t = v)
  symm v w := by simp_rw [adj_comm]; (conv_lhs => arg 2; arg 2; rw [or_comm]); exact id

@[simp]
lemma addEdge_self : G.addEdge s s = G := by ext; simp

lemma addEdge_adj (h : G.Adj s t) : G.addEdge s t = G := by
  ext
  simp only [ne_eq, G.ne_of_adj h, not_false_eq_true, true_and, or_iff_left_iff_imp]
  rintro (_ | _) <;> simp_all [adj_comm]

variable [Fintype V] {s t} [DecidableRel G.Adj]

theorem edgeFinset_addEdge (hn : ¬G.Adj s t) (h : s ≠ t) :
    (G.addEdge s t).edgeFinset = G.edgeFinset ∪ {⟦(s, t)⟧} := by
  ext e
  refine' e.inductionOn _
  aesop

theorem card_edgeFinset_addEdge (hn : ¬G.Adj s t) (h : s ≠ t) :
    (G.addEdge s t).edgeFinset.card = G.edgeFinset.card + 1 := by
  rw [G.edgeFinset_addEdge hn h, card_disjoint_union (by simpa using hn)]; · rfl

end AddEdge
