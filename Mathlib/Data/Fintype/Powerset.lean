/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Powerset

#align_import data.fintype.powerset from "leanprover-community/mathlib"@"509de852e1de55e1efa8eacfa11df0823f26f226"

/-!
# fintype instance for `Set α`, when `α` is a fintype
-/


variable {α : Type*}

open Finset

instance Finset.fintype [Fintype α] : Fintype (Finset α) :=
  ⟨univ.powerset, fun _ => Finset.mem_powerset.2 (Finset.subset_univ _)⟩

@[simp]
theorem Fintype.card_finset [Fintype α] : Fintype.card (Finset α) = 2 ^ Fintype.card α :=
  Finset.card_powerset Finset.univ

namespace Finset
variable [Fintype α] {s : Finset α} {k : ℕ}

@[simp] lemma powerset_univ : (univ : Finset α).powerset = univ :=
  coe_injective <| by simp [-coe_eq_univ]

lemma filter_subset_univ [DecidableEq α] (s : Finset α) :
    filter (fun t ↦ t ⊆ s) univ = powerset s := by ext; simp

@[simp] lemma powerset_eq_univ : s.powerset = univ ↔ s = univ := by
  rw [← Finset.powerset_univ, powerset_inj]

@[simp] lemma mem_powersetCard_univ : s ∈ powersetCard k (univ : Finset α) ↔ card s = k :=
  mem_powersetCard.trans <| and_iff_right <| subset_univ _

variable (α)

@[simp] lemma univ_filter_card_eq (k : ℕ) :
    (univ : Finset (Finset α)).filter (fun s ↦ s.card = k) = univ.powersetCard k := by ext; simp

end Finset

@[simp]
theorem Fintype.card_finset_len [Fintype α] (k : ℕ) :
    Fintype.card { s : Finset α // s.card = k } = Nat.choose (Fintype.card α) k := by
  simp [Fintype.subtype_card, Finset.card_univ]

instance Set.fintype [Fintype α] : Fintype (Set α) :=
  ⟨(@Finset.univ α _).powerset.map ⟨(↑), coe_injective⟩, fun s => by
    classical
      refine' mem_map.2 ⟨Finset.univ.filter s, Finset.mem_powerset.2 (Finset.subset_univ _), _⟩
      apply (coe_filter _ _).trans
      simp
      rfl⟩

-- Not to be confused with `Set.Finite`, the predicate
instance Set.finite' [Finite α] : Finite (Set α) := by
  cases nonempty_fintype α
  infer_instance

@[simp]
theorem Fintype.card_set [Fintype α] : Fintype.card (Set α) = 2 ^ Fintype.card α :=
  (Finset.card_map _).trans (Finset.card_powerset _)
