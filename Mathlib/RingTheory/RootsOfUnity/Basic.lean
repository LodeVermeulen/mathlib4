/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Data.Polynomial.RingDivision
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.NumberTheory.Divisors
import Mathlib.RingTheory.IntegralDomain
import Mathlib.Tactic.Zify

#align_import ring_theory.roots_of_unity.basic from "leanprover-community/mathlib"@"7fdeecc0d03cd40f7a165e6cf00a4d2286db599f"

/-!
# Roots of unity and primitive roots of unity

We define roots of unity in the context of an arbitrary commutative monoid,
as a subgroup of the group of units. We also define a predicate `IsPrimitiveRoot` on commutative
monoids, expressing that an element is a primitive root of unity.

## Main definitions

* `rootsOfUnity n M`, for `n : ℕ+` is the subgroup of the units of a commutative monoid `M`
  consisting of elements `x` that satisfy `x ^ n = 1`.
* `IsPrimitiveRoot ζ k`: an element `ζ` is a primitive `k`-th root of unity if `ζ ^ k = 1`,
  and if `l` satisfies `ζ ^ l = 1` then `k ∣ l`.
* `primitiveRoots k R`: the finset of primitive `k`-th roots of unity in an integral domain `R`.
* `IsPrimitiveRoot.autToPow`: the monoid hom that takes an automorphism of a ring to the power
  it sends that specific primitive root, as a member of `(ZMod n)ˣ`.

## Main results

* `rootsOfUnity.isCyclic`: the roots of unity in an integral domain form a cyclic group.
* `IsPrimitiveRoot.zmodEquivZpowers`: `ZMod k` is equivalent to
  the subgroup generated by a primitive `k`-th root of unity.
* `IsPrimitiveRoot.zpowers_eq`: in an integral domain, the subgroup generated by
  a primitive `k`-th root of unity is equal to the `k`-th roots of unity.
* `IsPrimitiveRoot.card_primitiveRoots`: if an integral domain
   has a primitive `k`-th root of unity, then it has `φ k` of them.

## Implementation details

It is desirable that `rootsOfUnity` is a subgroup,
and it will mainly be applied to rings (e.g. the ring of integers in a number field) and fields.
We therefore implement it as a subgroup of the units of a commutative monoid.

We have chosen to define `rootsOfUnity n` for `n : ℕ+`, instead of `n : ℕ`,
because almost all lemmas need the positivity assumption,
and in particular the type class instances for `Fintype` and `IsCyclic`.

On the other hand, for primitive roots of unity, it is desirable to have a predicate
not just on units, but directly on elements of the ring/field.
For example, we want to say that `exp (2 * pi * I / n)` is a primitive `n`-th root of unity
in the complex numbers, without having to turn that number into a unit first.

This creates a little bit of friction, but lemmas like `IsPrimitiveRoot.isUnit` and
`IsPrimitiveRoot.coe_units_iff` should provide the necessary glue.

-/


open scoped Classical BigOperators Polynomial

noncomputable section

open Polynomial

open Finset

variable {M N G R S F : Type*}

variable [CommMonoid M] [CommMonoid N] [DivisionCommMonoid G]

section rootsOfUnity

variable {k l : ℕ+}

/-- `rootsOfUnity k M` is the subgroup of elements `m : Mˣ` that satisfy `m ^ k = 1`. -/
def rootsOfUnity (k : ℕ+) (M : Type*) [CommMonoid M] : Subgroup Mˣ where
  carrier := {ζ | ζ ^ (k : ℕ) = 1}
  one_mem' := one_pow _
  mul_mem' _ _ := by simp_all only [Set.mem_setOf_eq, mul_pow, one_mul]
  inv_mem' _ := by simp_all only [Set.mem_setOf_eq, inv_pow, inv_one]

@[simp]
theorem mem_rootsOfUnity (k : ℕ+) (ζ : Mˣ) : ζ ∈ rootsOfUnity k M ↔ ζ ^ (k : ℕ) = 1 :=
  Iff.rfl

theorem mem_rootsOfUnity' (k : ℕ+) (ζ : Mˣ) : ζ ∈ rootsOfUnity k M ↔ (ζ : M) ^ (k : ℕ) = 1 := by
  rw [mem_rootsOfUnity]; norm_cast

theorem rootsOfUnity.coe_injective {n : ℕ+} :
    Function.Injective (fun x : rootsOfUnity n M ↦ x.val.val) :=
  Units.ext.comp fun _ _ => Subtype.eq

/-- Make an element of `rootsOfUnity` from a member of the base ring, and a proof that it has
a positive power equal to one. -/
@[simps! coe_val]
def rootsOfUnity.mkOfPowEq (ζ : M) {n : ℕ+} (h : ζ ^ (n : ℕ) = 1) : rootsOfUnity n M :=
  ⟨Units.ofPowEqOne ζ n h n.ne_zero, Units.pow_ofPowEqOne _ _⟩

@[simp]
theorem rootsOfUnity.coe_mkOfPowEq {ζ : M} {n : ℕ+} (h : ζ ^ (n : ℕ) = 1) :
    ((rootsOfUnity.mkOfPowEq _ h : Mˣ) : M) = ζ :=
  rfl

theorem rootsOfUnity_le_of_dvd (h : k ∣ l) : rootsOfUnity k M ≤ rootsOfUnity l M := by
  obtain ⟨d, rfl⟩ := h
  intro ζ h
  simp_all only [mem_rootsOfUnity, PNat.mul_coe, pow_mul, one_pow]

theorem map_rootsOfUnity (f : Mˣ →* Nˣ) (k : ℕ+) : (rootsOfUnity k M).map f ≤ rootsOfUnity k N := by
  rintro _ ⟨ζ, h, rfl⟩
  simp_all only [← map_pow, mem_rootsOfUnity, SetLike.mem_coe, MonoidHom.map_one]

@[norm_cast]
theorem rootsOfUnity.coe_pow [CommMonoid R] (ζ : rootsOfUnity k R) (m : ℕ) :
    ((ζ ^ m : Rˣ) : R) = ((ζ : Rˣ) : R) ^ m := by
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]

section CommSemiring

variable [CommSemiring R] [CommSemiring S]

/-- Restrict a ring homomorphism to the nth roots of unity. -/
def restrictRootsOfUnity [RingHomClass F R S] (σ : F) (n : ℕ+) :
    rootsOfUnity n R →* rootsOfUnity n S :=
  let h : ∀ ξ : rootsOfUnity n R, (σ (ξ : Rˣ)) ^ (n : ℕ) = 1 := fun ξ => by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, show (ξ : Rˣ) ^ (n : ℕ) = 1 from ξ.2, Units.val_one,
      map_one σ]
  { toFun := fun ξ =>
      ⟨@unitOfInvertible _ _ _ (invertibleOfPowEqOne _ _ (h ξ) n.ne_zero), by
        ext; rw [Units.val_pow_eq_pow_val]; exact h ξ⟩
    map_one' := by ext; exact map_one σ
    map_mul' := fun ξ₁ ξ₂ => by ext; rw [Subgroup.coe_mul, Units.val_mul]; exact map_mul σ _ _ }

@[simp]
theorem restrictRootsOfUnity_coe_apply [RingHomClass F R S] (σ : F) (ζ : rootsOfUnity k R) :
    (restrictRootsOfUnity σ k ζ : Sˣ) = σ (ζ : Rˣ) :=
  rfl

/-- Restrict a ring isomorphism to the nth roots of unity. -/
nonrec def RingEquiv.restrictRootsOfUnity (σ : R ≃+* S) (n : ℕ+) :
    rootsOfUnity n R ≃* rootsOfUnity n S where
  toFun := restrictRootsOfUnity σ.toRingHom n
  invFun := restrictRootsOfUnity σ.symm.toRingHom n
  left_inv ξ := by ext; exact σ.symm_apply_apply (ξ : Rˣ)
  right_inv ξ := by ext; exact σ.apply_symm_apply (ξ : Sˣ)
  map_mul' := (restrictRootsOfUnity _ n).map_mul

@[simp]
theorem RingEquiv.restrictRootsOfUnity_coe_apply (σ : R ≃+* S) (ζ : rootsOfUnity k R) :
    (σ.restrictRootsOfUnity k ζ : Sˣ) = σ (ζ : Rˣ) :=
  rfl

@[simp]
theorem RingEquiv.restrictRootsOfUnity_symm (σ : R ≃+* S) :
    (σ.restrictRootsOfUnity k).symm = σ.symm.restrictRootsOfUnity k :=
  rfl

end CommSemiring

section IsDomain

variable [CommRing R] [IsDomain R]

theorem mem_rootsOfUnity_iff_mem_nthRoots {ζ : Rˣ} :
    ζ ∈ rootsOfUnity k R ↔ (ζ : R) ∈ nthRoots k (1 : R) := by
  simp only [mem_rootsOfUnity, mem_nthRoots k.pos, Units.ext_iff, Units.val_one,
    Units.val_pow_eq_pow_val]

variable (k R)

/-- Equivalence between the `k`-th roots of unity in `R` and the `k`-th roots of `1`.

This is implemented as equivalence of subtypes,
because `rootsOfUnity` is a subgroup of the group of units,
whereas `nthRoots` is a multiset. -/
def rootsOfUnityEquivNthRoots : rootsOfUnity k R ≃ { x // x ∈ nthRoots k (1 : R) } := by
  refine'
    { toFun := fun x => ⟨(x : Rˣ), mem_rootsOfUnity_iff_mem_nthRoots.mp x.2⟩
      invFun := fun x => ⟨⟨x, ↑x ^ (k - 1 : ℕ), _, _⟩, _⟩
      left_inv := _
      right_inv := _ }
  pick_goal 4; · rintro ⟨x, hx⟩; ext; rfl
  pick_goal 4; · rintro ⟨x, hx⟩; ext; rfl
  all_goals
    rcases x with ⟨x, hx⟩; rw [mem_nthRoots k.pos] at hx
    simp only [Subtype.coe_mk, ← pow_succ, ← pow_succ', hx,
      tsub_add_cancel_of_le (show 1 ≤ (k : ℕ) from k.one_le)]
  · show (_ : Rˣ) ^ (k : ℕ) = 1
    simp only [Units.ext_iff, hx, Units.val_mk, Units.val_one, Subtype.coe_mk,
      Units.val_pow_eq_pow_val]

variable {k R}

@[simp]
theorem rootsOfUnityEquivNthRoots_apply (x : rootsOfUnity k R) :
    (rootsOfUnityEquivNthRoots R k x : R) = ((x : Rˣ) : R) :=
  rfl

@[simp]
theorem rootsOfUnityEquivNthRoots_symm_apply (x : { x // x ∈ nthRoots k (1 : R) }) :
    (((rootsOfUnityEquivNthRoots R k).symm x : Rˣ) : R) = (x : R) :=
  rfl

variable (k R)

instance rootsOfUnity.fintype : Fintype (rootsOfUnity k R) :=
  Fintype.ofEquiv { x // x ∈ nthRoots k (1 : R) } <| (rootsOfUnityEquivNthRoots R k).symm

instance rootsOfUnity.isCyclic : IsCyclic (rootsOfUnity k R) :=
  isCyclic_of_subgroup_isDomain ((Units.coeHom R).comp (rootsOfUnity k R).subtype)
    (Units.ext.comp Subtype.val_injective)

theorem card_rootsOfUnity : Fintype.card (rootsOfUnity k R) ≤ k :=
  calc
    Fintype.card (rootsOfUnity k R) = Fintype.card { x // x ∈ nthRoots k (1 : R) } :=
      Fintype.card_congr (rootsOfUnityEquivNthRoots R k)
    _ ≤ Multiset.card (nthRoots k (1 : R)).attach := (Multiset.card_le_of_le (Multiset.dedup_le _))
    _ = Multiset.card (nthRoots k (1 : R)) := Multiset.card_attach
    _ ≤ k := card_nthRoots k 1

variable {k R}

theorem map_rootsOfUnity_eq_pow_self [RingHomClass F R R] (σ : F) (ζ : rootsOfUnity k R) :
    ∃ m : ℕ, σ (ζ : Rˣ) = ((ζ : Rˣ) : R) ^ m := by
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic (restrictRootsOfUnity σ k)
  rw [← restrictRootsOfUnity_coe_apply, hm, zpow_eq_mod_orderOf, ← Int.toNat_of_nonneg
      (m.emod_nonneg (Int.coe_nat_ne_zero.mpr (pos_iff_ne_zero.mp (orderOf_pos ζ)))),
    zpow_ofNat, rootsOfUnity.coe_pow]
  exact ⟨(m % orderOf ζ).toNat, rfl⟩

end IsDomain

section Reduced

variable (R) [CommRing R] [IsReduced R]

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

-- @[simp] -- Porting note: simp normal form is `mem_rootsOfUnity_prime_pow_mul_iff'`
theorem mem_rootsOfUnity_prime_pow_mul_iff (p k : ℕ) (m : ℕ+) [hp : Fact p.Prime] [CharP R p]
    {ζ : Rˣ} : ζ ∈ rootsOfUnity (⟨p, hp.1.pos⟩ ^ k * m) R ↔ ζ ∈ rootsOfUnity m R := by
  simp only [mem_rootsOfUnity', PNat.mul_coe, PNat.pow_coe, PNat.mk_coe,
    CharP.pow_prime_pow_mul_eq_one_iff]

@[simp]
theorem mem_rootsOfUnity_prime_pow_mul_iff' (p k : ℕ) (m : ℕ+) [hp : Fact p.Prime] [CharP R p]
    {ζ : Rˣ} : ζ ^ (p ^ k * ↑m) = 1 ↔ ζ ∈ rootsOfUnity m R := by
  rw [← PNat.mk_coe p hp.1.pos, ← PNat.pow_coe, ← PNat.mul_coe, ← mem_rootsOfUnity,
    mem_rootsOfUnity_prime_pow_mul_iff]

end Reduced

end rootsOfUnity

/-- An element `ζ` is a primitive `k`-th root of unity if `ζ ^ k = 1`,
and if `l` satisfies `ζ ^ l = 1` then `k ∣ l`. -/
@[mk_iff IsPrimitiveRoot.iff_def]
structure IsPrimitiveRoot (ζ : M) (k : ℕ) : Prop where
  pow_eq_one : ζ ^ (k : ℕ) = 1
  dvd_of_pow_eq_one : ∀ l : ℕ, ζ ^ l = 1 → k ∣ l

/-- Turn a primitive root μ into a member of the `rootsOfUnity` subgroup. -/
@[simps!]
def IsPrimitiveRoot.toRootsOfUnity {μ : M} {n : ℕ+} (h : IsPrimitiveRoot μ n) : rootsOfUnity n M :=
  rootsOfUnity.mkOfPowEq μ h.pow_eq_one

section primitiveRoots

variable {k : ℕ}

/-- `primitiveRoots k R` is the finset of primitive `k`-th roots of unity
in the integral domain `R`. -/
def primitiveRoots (k : ℕ) (R : Type*) [CommRing R] [IsDomain R] : Finset R :=
  (nthRoots k (1 : R)).toFinset.filter fun ζ => IsPrimitiveRoot ζ k

variable [CommRing R] [IsDomain R]

@[simp]
theorem mem_primitiveRoots {ζ : R} (h0 : 0 < k) : ζ ∈ primitiveRoots k R ↔ IsPrimitiveRoot ζ k := by
  rw [primitiveRoots, mem_filter, Multiset.mem_toFinset, mem_nthRoots h0, and_iff_right_iff_imp]
  exact IsPrimitiveRoot.pow_eq_one

@[simp]
theorem primitiveRoots_zero : primitiveRoots 0 R = ∅ := by
  rw [primitiveRoots, nthRoots_zero, Multiset.toFinset_zero, Finset.filter_empty]

theorem isPrimitiveRoot_of_mem_primitiveRoots {ζ : R} (h : ζ ∈ primitiveRoots k R) :
    IsPrimitiveRoot ζ k :=
  k.eq_zero_or_pos.elim (fun hk => by simp [hk] at h) fun hk => (mem_primitiveRoots hk).1 h

end primitiveRoots

namespace IsPrimitiveRoot

variable {k l : ℕ}

theorem mk_of_lt (ζ : M) (hk : 0 < k) (h1 : ζ ^ k = 1) (h : ∀ l : ℕ, 0 < l → l < k → ζ ^ l ≠ 1) :
    IsPrimitiveRoot ζ k := by
  refine' ⟨h1, fun l hl => _⟩
  suffices k.gcd l = k by exact this ▸ k.gcd_dvd_right l
  rw [eq_iff_le_not_lt]
  refine' ⟨Nat.le_of_dvd hk (k.gcd_dvd_left l), _⟩
  intro h'; apply h _ (Nat.gcd_pos_of_pos_left _ hk) h'
  exact pow_gcd_eq_one _ h1 hl

section CommMonoid

variable {ζ : M} {f : F} (h : IsPrimitiveRoot ζ k)

@[nontriviality]
theorem of_subsingleton [Subsingleton M] (x : M) : IsPrimitiveRoot x 1 :=
  ⟨Subsingleton.elim _ _, fun _ _ => one_dvd _⟩

theorem pow_eq_one_iff_dvd (l : ℕ) : ζ ^ l = 1 ↔ k ∣ l :=
  ⟨h.dvd_of_pow_eq_one l, by
    rintro ⟨i, rfl⟩; simp only [pow_mul, h.pow_eq_one, one_pow, PNat.mul_coe]⟩

theorem isUnit (h : IsPrimitiveRoot ζ k) (h0 : 0 < k) : IsUnit ζ := by
  apply isUnit_of_mul_eq_one ζ (ζ ^ (k - 1))
  rw [← pow_succ, tsub_add_cancel_of_le h0.nat_succ_le, h.pow_eq_one]

theorem pow_ne_one_of_pos_of_lt (h0 : 0 < l) (hl : l < k) : ζ ^ l ≠ 1 :=
  mt (Nat.le_of_dvd h0 ∘ h.dvd_of_pow_eq_one _) <| not_le_of_lt hl

theorem ne_one (hk : 1 < k) : ζ ≠ 1 :=
  h.pow_ne_one_of_pos_of_lt zero_lt_one hk ∘ (pow_one ζ).trans

theorem pow_inj (h : IsPrimitiveRoot ζ k) ⦃i j : ℕ⦄ (hi : i < k) (hj : j < k) (H : ζ ^ i = ζ ^ j) :
    i = j := by
  wlog hij : i ≤ j generalizing i j
  · exact (this hj hi H.symm (le_of_not_le hij)).symm
  apply le_antisymm hij
  rw [← tsub_eq_zero_iff_le]
  apply Nat.eq_zero_of_dvd_of_lt _ (lt_of_le_of_lt tsub_le_self hj)
  apply h.dvd_of_pow_eq_one
  rw [← ((h.isUnit (lt_of_le_of_lt (Nat.zero_le _) hi)).pow i).mul_left_inj, ← pow_add,
    tsub_add_cancel_of_le hij, H, one_mul]

theorem one : IsPrimitiveRoot (1 : M) 1 :=
  { pow_eq_one := pow_one _
    dvd_of_pow_eq_one := fun _ _ => one_dvd _ }

@[simp]
theorem one_right_iff : IsPrimitiveRoot ζ 1 ↔ ζ = 1 := by
  clear h
  constructor
  · intro h; rw [← pow_one ζ, h.pow_eq_one]
  · rintro rfl; exact one

@[simp]
theorem coe_submonoidClass_iff {M B : Type*} [CommMonoid M] [SetLike B M] [SubmonoidClass B M]
    {N : B} {ζ : N} : IsPrimitiveRoot (ζ : M) k ↔ IsPrimitiveRoot ζ k := by
  simp_rw [iff_def]
  norm_cast

@[simp]
theorem coe_units_iff {ζ : Mˣ} : IsPrimitiveRoot (ζ : M) k ↔ IsPrimitiveRoot ζ k := by
  simp only [iff_def, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one]

-- Porting note `variable` above already contains `(h : IsPrimitiveRoot ζ k)`
theorem pow_of_coprime (i : ℕ) (hi : i.Coprime k) : IsPrimitiveRoot (ζ ^ i) k := by
  by_cases h0 : k = 0
  · subst k; simp_all only [pow_one, Nat.coprime_zero_right]
  rcases h.isUnit (Nat.pos_of_ne_zero h0) with ⟨ζ, rfl⟩
  rw [← Units.val_pow_eq_pow_val]
  rw [coe_units_iff] at h ⊢
  refine'
    { pow_eq_one := by rw [← pow_mul', pow_mul, h.pow_eq_one, one_pow]
      dvd_of_pow_eq_one := _ }
  intro l hl
  apply h.dvd_of_pow_eq_one
  rw [← pow_one ζ, ← zpow_ofNat ζ, ← hi.gcd_eq_one, Nat.gcd_eq_gcd_ab, zpow_add, mul_pow,
    ← zpow_ofNat, ← zpow_mul, mul_right_comm]
  simp only [zpow_mul, hl, h.pow_eq_one, one_zpow, one_pow, one_mul, zpow_ofNat]

theorem pow_of_prime (h : IsPrimitiveRoot ζ k) {p : ℕ} (hprime : Nat.Prime p) (hdiv : ¬p ∣ k) :
    IsPrimitiveRoot (ζ ^ p) k :=
  h.pow_of_coprime p (hprime.coprime_iff_not_dvd.2 hdiv)

theorem pow_iff_coprime (h : IsPrimitiveRoot ζ k) (h0 : 0 < k) (i : ℕ) :
    IsPrimitiveRoot (ζ ^ i) k ↔ i.Coprime k := by
  refine' ⟨_, h.pow_of_coprime i⟩
  intro hi
  obtain ⟨a, ha⟩ := i.gcd_dvd_left k
  obtain ⟨b, hb⟩ := i.gcd_dvd_right k
  suffices b = k by
    -- Porting note: was `rwa [this, ← one_mul k, mul_left_inj' h0.ne', eq_comm] at hb`
    rw [this, eq_comm, Nat.mul_left_eq_self_iff h0] at hb
    rwa [Nat.Coprime]
  rw [ha] at hi
  rw [mul_comm] at hb
  apply Nat.dvd_antisymm ⟨i.gcd k, hb⟩ (hi.dvd_of_pow_eq_one b _)
  rw [← pow_mul', ← mul_assoc, ← hb, pow_mul, h.pow_eq_one, one_pow]

protected theorem orderOf (ζ : M) : IsPrimitiveRoot ζ (orderOf ζ) :=
  ⟨pow_orderOf_eq_one ζ, fun _ => orderOf_dvd_of_pow_eq_one⟩

theorem unique {ζ : M} (hk : IsPrimitiveRoot ζ k) (hl : IsPrimitiveRoot ζ l) : k = l :=
  Nat.dvd_antisymm (hk.2 _ hl.1) (hl.2 _ hk.1)

theorem eq_orderOf : k = orderOf ζ :=
  h.unique (IsPrimitiveRoot.orderOf ζ)

protected theorem iff (hk : 0 < k) :
    IsPrimitiveRoot ζ k ↔ ζ ^ k = 1 ∧ ∀ l : ℕ, 0 < l → l < k → ζ ^ l ≠ 1 := by
  refine' ⟨fun h => ⟨h.pow_eq_one, fun l hl' hl => _⟩,
    fun ⟨hζ, hl⟩ => IsPrimitiveRoot.mk_of_lt ζ hk hζ hl⟩
  rw [h.eq_orderOf] at hl
  exact pow_ne_one_of_lt_orderOf' hl'.ne' hl

protected theorem not_iff : ¬IsPrimitiveRoot ζ k ↔ orderOf ζ ≠ k :=
  ⟨fun h hk => h <| hk ▸ IsPrimitiveRoot.orderOf ζ,
    fun h hk => h.symm <| hk.unique <| IsPrimitiveRoot.orderOf ζ⟩

theorem pow_of_dvd (h : IsPrimitiveRoot ζ k) {p : ℕ} (hp : p ≠ 0) (hdiv : p ∣ k) :
    IsPrimitiveRoot (ζ ^ p) (k / p) := by
  suffices orderOf (ζ ^ p) = k / p by exact this ▸ IsPrimitiveRoot.orderOf (ζ ^ p)
  rw [orderOf_pow' _ hp, ← eq_orderOf h, Nat.gcd_eq_right hdiv]

protected theorem mem_rootsOfUnity {ζ : Mˣ} {n : ℕ+} (h : IsPrimitiveRoot ζ n) :
    ζ ∈ rootsOfUnity n M :=
  h.pow_eq_one

/-- If there is an `n`-th primitive root of unity in `R` and `b` divides `n`,
then there is a `b`-th primitive root of unity in `R`. -/
theorem pow {n : ℕ} {a b : ℕ} (hn : 0 < n) (h : IsPrimitiveRoot ζ n) (hprod : n = a * b) :
    IsPrimitiveRoot (ζ ^ a) b := by
  subst n
  simp only [iff_def, ← pow_mul, h.pow_eq_one, eq_self_iff_true, true_and_iff]
  intro l hl
  -- Porting note: was `by rintro rfl; simpa only [Nat.not_lt_zero, zero_mul] using hn`
  have ha0 : a ≠ 0 := left_ne_zero_of_mul hn.ne'
  rw [← mul_dvd_mul_iff_left ha0]
  exact h.dvd_of_pow_eq_one _ hl

section Maps

open Function

theorem map_of_injective [MonoidHomClass F M N] (h : IsPrimitiveRoot ζ k) (hf : Injective f) :
    IsPrimitiveRoot (f ζ) k where
  pow_eq_one := by rw [← map_pow, h.pow_eq_one, _root_.map_one]
  dvd_of_pow_eq_one := by
    rw [h.eq_orderOf]
    intro l hl
    rw [← map_pow, ← map_one f] at hl
    exact orderOf_dvd_of_pow_eq_one (hf hl)

theorem of_map_of_injective [MonoidHomClass F M N] (h : IsPrimitiveRoot (f ζ) k)
    (hf : Injective f) : IsPrimitiveRoot ζ k where
  pow_eq_one := by apply_fun f; rw [map_pow, _root_.map_one, h.pow_eq_one]
  dvd_of_pow_eq_one := by
    rw [h.eq_orderOf]
    intro l hl
    apply_fun f at hl
    rw [map_pow, _root_.map_one] at hl
    exact orderOf_dvd_of_pow_eq_one hl

theorem map_iff_of_injective [MonoidHomClass F M N] (hf : Injective f) :
    IsPrimitiveRoot (f ζ) k ↔ IsPrimitiveRoot ζ k :=
  ⟨fun h => h.of_map_of_injective hf, fun h => h.map_of_injective hf⟩

end Maps

end CommMonoid

section CommMonoidWithZero

variable {M₀ : Type*} [CommMonoidWithZero M₀]

theorem zero [Nontrivial M₀] : IsPrimitiveRoot (0 : M₀) 0 :=
  ⟨pow_zero 0, fun l hl => by
    simpa [zero_pow_eq, show ∀ p, ¬p → False ↔ p from @Classical.not_not] using hl⟩

protected theorem ne_zero [Nontrivial M₀] {ζ : M₀} (h : IsPrimitiveRoot ζ k) : k ≠ 0 → ζ ≠ 0 :=
  mt fun hn => h.unique (hn.symm ▸ IsPrimitiveRoot.zero)

end CommMonoidWithZero

section DivisionCommMonoid

variable {ζ : G}

theorem zpow_eq_one (h : IsPrimitiveRoot ζ k) : ζ ^ (k : ℤ) = 1 := by
  rw [zpow_ofNat]; exact h.pow_eq_one

theorem zpow_eq_one_iff_dvd (h : IsPrimitiveRoot ζ k) (l : ℤ) : ζ ^ l = 1 ↔ (k : ℤ) ∣ l := by
  by_cases h0 : 0 ≤ l
  · lift l to ℕ using h0; rw [zpow_ofNat]; norm_cast; exact h.pow_eq_one_iff_dvd l
  · have : 0 ≤ -l := by simp only [not_le, neg_nonneg] at h0 ⊢; exact le_of_lt h0
    lift -l to ℕ using this with l' hl'
    rw [← dvd_neg, ← hl']
    norm_cast
    rw [← h.pow_eq_one_iff_dvd, ← inv_inj, ← zpow_neg, ← hl', zpow_ofNat, inv_one]

theorem inv (h : IsPrimitiveRoot ζ k) : IsPrimitiveRoot ζ⁻¹ k :=
  { pow_eq_one := by simp only [h.pow_eq_one, inv_one, eq_self_iff_true, inv_pow]
    dvd_of_pow_eq_one := by
      intro l hl
      apply h.dvd_of_pow_eq_one l
      rw [← inv_inj, ← inv_pow, hl, inv_one] }

@[simp]
theorem inv_iff : IsPrimitiveRoot ζ⁻¹ k ↔ IsPrimitiveRoot ζ k := by
  refine' ⟨_, fun h => inv h⟩; intro h; rw [← inv_inv ζ]; exact inv h

theorem zpow_of_gcd_eq_one (h : IsPrimitiveRoot ζ k) (i : ℤ) (hi : i.gcd k = 1) :
    IsPrimitiveRoot (ζ ^ i) k := by
  by_cases h0 : 0 ≤ i
  · lift i to ℕ using h0
    rw [zpow_ofNat]
    exact h.pow_of_coprime i hi
  have : 0 ≤ -i := by simp only [not_le, neg_nonneg] at h0 ⊢; exact le_of_lt h0
  lift -i to ℕ using this with i' hi'
  rw [← inv_iff, ← zpow_neg, ← hi', zpow_ofNat]
  apply h.pow_of_coprime
  rw [Int.gcd, ← Int.natAbs_neg, ← hi'] at hi
  exact hi

end DivisionCommMonoid

section CommRing

variable [CommRing R]  {n : ℕ} (hn : 1 < n) {ζ : R} (hζ : IsPrimitiveRoot ζ n)

theorem sub_one_ne_zero : ζ - 1 ≠ 0 := sub_ne_zero.mpr <| hζ.ne_one hn

end CommRing

section IsDomain

variable {ζ : R}

variable [CommRing R] [IsDomain R]

@[simp]
theorem primitiveRoots_one : primitiveRoots 1 R = {(1 : R)} := by
  apply Finset.eq_singleton_iff_unique_mem.2
  constructor
  · simp only [IsPrimitiveRoot.one_right_iff, mem_primitiveRoots zero_lt_one]
  · intro x hx
    rw [mem_primitiveRoots zero_lt_one, IsPrimitiveRoot.one_right_iff] at hx
    exact hx

theorem neZero' {n : ℕ+} (hζ : IsPrimitiveRoot ζ n) : NeZero ((n : ℕ) : R) := by
  let p := ringChar R
  have hfin := multiplicity.finite_nat_iff.2 ⟨CharP.char_ne_one R p, n.pos⟩
  obtain ⟨m, hm⟩ := multiplicity.exists_eq_pow_mul_and_not_dvd hfin
  by_cases hp : p ∣ n
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (multiplicity.pos_of_dvd hfin hp).ne'
    haveI : NeZero p := NeZero.of_pos (Nat.pos_of_dvd_of_pos hp n.pos)
    haveI hpri : Fact p.Prime := CharP.char_is_prime_of_pos R p
    have := hζ.pow_eq_one
    rw [hm.1, hk, pow_succ, mul_assoc, pow_mul', ← frobenius_def, ← frobenius_one p] at this
    exfalso
    have hpos : 0 < p ^ k * m := by
      refine' mul_pos (pow_pos hpri.1.pos _) (Nat.pos_of_ne_zero fun h => _)
      have H := hm.1
      rw [h] at H
      simp at H
    refine' hζ.pow_ne_one_of_pos_of_lt hpos _ (frobenius_inj R p this)
    · rw [hm.1, hk, pow_succ, mul_assoc, mul_comm p]
      exact lt_mul_of_one_lt_right hpos hpri.1.one_lt
  · exact NeZero.of_not_dvd R hp

nonrec theorem mem_nthRootsFinset (hζ : IsPrimitiveRoot ζ k) (hk : 0 < k) :
    ζ ∈ nthRootsFinset k R :=
  (mem_nthRootsFinset hk).2 hζ.pow_eq_one

end IsDomain

section IsDomain

variable [CommRing R]

variable {ζ : Rˣ} (h : IsPrimitiveRoot ζ k)

theorem eq_neg_one_of_two_right [NoZeroDivisors R] {ζ : R} (h : IsPrimitiveRoot ζ 2) : ζ = -1 := by
  apply (eq_or_eq_neg_of_sq_eq_sq ζ 1 _).resolve_left
  · rw [← pow_one ζ]; apply h.pow_ne_one_of_pos_of_lt <;> decide
  · simp only [h.pow_eq_one, one_pow]

theorem neg_one (p : ℕ) [Nontrivial R] [h : CharP R p] (hp : p ≠ 2) :
    IsPrimitiveRoot (-1 : R) 2 := by
  convert IsPrimitiveRoot.orderOf (-1 : R)
  rw [orderOf_neg_one, if_neg]
  rwa [ringChar.eq_iff.mpr h]

/-- If `1 < k` then `(∑ i in range k, ζ ^ i) = 0`. -/
theorem geom_sum_eq_zero [IsDomain R] {ζ : R} (hζ : IsPrimitiveRoot ζ k) (hk : 1 < k) :
    ∑ i in range k, ζ ^ i = 0 := by
  refine' eq_zero_of_ne_zero_of_mul_left_eq_zero (sub_ne_zero_of_ne (hζ.ne_one hk).symm) _
  rw [mul_neg_geom_sum, hζ.pow_eq_one, sub_self]

/-- If `1 < k`, then `ζ ^ k.pred = -(∑ i in range k.pred, ζ ^ i)`. -/
theorem pow_sub_one_eq [IsDomain R] {ζ : R} (hζ : IsPrimitiveRoot ζ k) (hk : 1 < k) :
    ζ ^ k.pred = -∑ i in range k.pred, ζ ^ i := by
  rw [eq_neg_iff_add_eq_zero, add_comm, ← sum_range_succ, ← Nat.succ_eq_add_one,
    Nat.succ_pred_eq_of_pos (pos_of_gt hk), hζ.geom_sum_eq_zero hk]

/-- The (additive) monoid equivalence between `ZMod k`
and the powers of a primitive root of unity `ζ`. -/
def zmodEquivZpowers (h : IsPrimitiveRoot ζ k) : ZMod k ≃+ Additive (Subgroup.zpowers ζ) :=
  AddEquiv.ofBijective
    (AddMonoidHom.liftOfRightInverse (Int.castAddHom <| ZMod k) _ ZMod.int_cast_rightInverse
      ⟨{  toFun := fun i => Additive.ofMul (⟨_, i, rfl⟩ : Subgroup.zpowers ζ)
          map_zero' := by simp only [zpow_zero]; rfl
          map_add' := by intro i j; simp only [zpow_add]; rfl }, fun i hi => by
        simp only [AddMonoidHom.mem_ker, CharP.int_cast_eq_zero_iff (ZMod k) k, AddMonoidHom.coe_mk,
          Int.coe_castAddHom] at hi ⊢
        obtain ⟨i, rfl⟩ := hi
        simp [zpow_mul, h.pow_eq_one, one_zpow, zpow_ofNat]⟩)
    (by
      constructor
      · rw [injective_iff_map_eq_zero]
        intro i hi
        rw [Subtype.ext_iff] at hi
        have := (h.zpow_eq_one_iff_dvd _).mp hi
        rw [← (CharP.int_cast_eq_zero_iff (ZMod k) k _).mpr this, eq_comm]
        exact ZMod.int_cast_rightInverse i
      · rintro ⟨ξ, i, rfl⟩
        refine' ⟨Int.castAddHom (ZMod k) i, _⟩
        rw [AddMonoidHom.liftOfRightInverse_comp_apply]
        rfl)

@[simp]
theorem zmodEquivZpowers_apply_coe_int (i : ℤ) :
    h.zmodEquivZpowers i = Additive.ofMul (⟨ζ ^ i, i, rfl⟩ : Subgroup.zpowers ζ) := by
  rw [zmodEquivZpowers, AddEquiv.ofBijective_apply] -- Porting note: Original proof didn't have `rw`
  exact AddMonoidHom.liftOfRightInverse_comp_apply _ _ ZMod.int_cast_rightInverse _ _

@[simp]
theorem zmodEquivZpowers_apply_coe_nat (i : ℕ) :
    h.zmodEquivZpowers i = Additive.ofMul (⟨ζ ^ i, i, rfl⟩ : Subgroup.zpowers ζ) := by
  have : (i : ZMod k) = (i : ℤ) := by norm_cast
  simp only [this, zmodEquivZpowers_apply_coe_int, zpow_ofNat]

@[simp]
theorem zmodEquivZpowers_symm_apply_zpow (i : ℤ) :
    h.zmodEquivZpowers.symm (Additive.ofMul (⟨ζ ^ i, i, rfl⟩ : Subgroup.zpowers ζ)) = i := by
  rw [← h.zmodEquivZpowers.symm_apply_apply i, zmodEquivZpowers_apply_coe_int]

@[simp]
theorem zmodEquivZpowers_symm_apply_zpow' (i : ℤ) : h.zmodEquivZpowers.symm ⟨ζ ^ i, i, rfl⟩ = i :=
  h.zmodEquivZpowers_symm_apply_zpow i

@[simp]
theorem zmodEquivZpowers_symm_apply_pow (i : ℕ) :
    h.zmodEquivZpowers.symm (Additive.ofMul (⟨ζ ^ i, i, rfl⟩ : Subgroup.zpowers ζ)) = i := by
  rw [← h.zmodEquivZpowers.symm_apply_apply i, zmodEquivZpowers_apply_coe_nat]

@[simp]
theorem zmodEquivZpowers_symm_apply_pow' (i : ℕ) : h.zmodEquivZpowers.symm ⟨ζ ^ i, i, rfl⟩ = i :=
  h.zmodEquivZpowers_symm_apply_pow i

variable [IsDomain R]

theorem zpowers_eq {k : ℕ+} {ζ : Rˣ} (h : IsPrimitiveRoot ζ k) :
    Subgroup.zpowers ζ = rootsOfUnity k R := by
  apply SetLike.coe_injective
  haveI F : Fintype (Subgroup.zpowers ζ) := Fintype.ofEquiv _ h.zmodEquivZpowers.toEquiv
  refine'
    @Set.eq_of_subset_of_card_le Rˣ (Subgroup.zpowers ζ) (rootsOfUnity k R) F
      (rootsOfUnity.fintype R k)
      (Subgroup.zpowers_le_of_mem <| show ζ ∈ rootsOfUnity k R from h.pow_eq_one) _
  calc
    Fintype.card (rootsOfUnity k R) ≤ k := card_rootsOfUnity R k
    _ = Fintype.card (ZMod k) := (ZMod.card k).symm
    _ = Fintype.card (Subgroup.zpowers ζ) := Fintype.card_congr h.zmodEquivZpowers.toEquiv

-- Porting note: rephrased the next few lemmas to avoid `∃ (Prop)`
theorem eq_pow_of_mem_rootsOfUnity {k : ℕ+} {ζ ξ : Rˣ} (h : IsPrimitiveRoot ζ k)
    (hξ : ξ ∈ rootsOfUnity k R) : ∃ (i : ℕ), i < k ∧ ζ ^ i = ξ := by
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, ζ ^ n = ξ := by rwa [← h.zpowers_eq] at hξ
  have hk0 : (0 : ℤ) < k := by exact_mod_cast k.pos
  let i := n % k
  have hi0 : 0 ≤ i := Int.emod_nonneg _ (ne_of_gt hk0)
  lift i to ℕ using hi0 with i₀ hi₀
  refine' ⟨i₀, _, _⟩
  · zify; rw [hi₀]; exact Int.emod_lt_of_pos _ hk0
  · rw [← zpow_ofNat, hi₀, ← Int.emod_add_ediv n k, zpow_add, zpow_mul, h.zpow_eq_one, one_zpow,
      mul_one]

theorem eq_pow_of_pow_eq_one {k : ℕ} {ζ ξ : R} (h : IsPrimitiveRoot ζ k) (hξ : ξ ^ k = 1)
    (h0 : 0 < k) : ∃ i < k, ζ ^ i = ξ := by
  lift ζ to Rˣ using h.isUnit h0
  lift ξ to Rˣ using isUnit_ofPowEqOne hξ h0.ne'
  lift k to ℕ+ using h0
  simp only [← Units.val_pow_eq_pow_val, ← Units.ext_iff]
  rw [coe_units_iff] at h
  apply h.eq_pow_of_mem_rootsOfUnity
  rw [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, hξ, Units.val_one]

theorem isPrimitiveRoot_iff' {k : ℕ+} {ζ ξ : Rˣ} (h : IsPrimitiveRoot ζ k) :
    IsPrimitiveRoot ξ k ↔ ∃ i < (k : ℕ), i.Coprime k ∧ ζ ^ i = ξ := by
  constructor
  · intro hξ
    obtain ⟨i, hik, rfl⟩ := h.eq_pow_of_mem_rootsOfUnity hξ.pow_eq_one
    rw [h.pow_iff_coprime k.pos] at hξ
    exact ⟨i, hik, hξ, rfl⟩
  · rintro ⟨i, -, hi, rfl⟩; exact h.pow_of_coprime i hi

theorem isPrimitiveRoot_iff {k : ℕ} {ζ ξ : R} (h : IsPrimitiveRoot ζ k) (h0 : 0 < k) :
    IsPrimitiveRoot ξ k ↔ ∃ i < k, i.Coprime k ∧ ζ ^ i = ξ := by
  constructor
  · intro hξ
    obtain ⟨i, hik, rfl⟩ := h.eq_pow_of_pow_eq_one hξ.pow_eq_one h0
    rw [h.pow_iff_coprime h0] at hξ
    exact ⟨i, hik, hξ, rfl⟩
  · rintro ⟨i, -, hi, rfl⟩; exact h.pow_of_coprime i hi

theorem card_rootsOfUnity' {n : ℕ+} (h : IsPrimitiveRoot ζ n) :
    Fintype.card (rootsOfUnity n R) = n := by
  let e := h.zmodEquivZpowers
  haveI F : Fintype (Subgroup.zpowers ζ) := Fintype.ofEquiv _ e.toEquiv
  calc
    Fintype.card (rootsOfUnity n R) = Fintype.card (Subgroup.zpowers ζ) :=
      Fintype.card_congr <| by rw [h.zpowers_eq]
    _ = Fintype.card (ZMod n) := (Fintype.card_congr e.toEquiv.symm)
    _ = n := ZMod.card n

theorem card_rootsOfUnity {ζ : R} {n : ℕ+} (h : IsPrimitiveRoot ζ n) :
    Fintype.card (rootsOfUnity n R) = n := by
  obtain ⟨ζ, hζ⟩ := h.isUnit n.pos
  rw [← hζ, IsPrimitiveRoot.coe_units_iff] at h
  exact h.card_rootsOfUnity'

/-- The cardinality of the multiset `nthRoots ↑n (1 : R)` is `n`
if there is a primitive root of unity in `R`. -/
nonrec theorem card_nthRoots {ζ : R} {n : ℕ} (h : IsPrimitiveRoot ζ n) :
    Multiset.card (nthRoots n (1 : R)) = n := by
  cases' Nat.eq_zero_or_pos n with hzero hpos
  · simp only [hzero, Multiset.card_zero, nthRoots_zero]
  rw [eq_iff_le_not_lt]
  use card_nthRoots n 1
  · rw [not_lt]
    have hcard :
        Fintype.card { x // x ∈ nthRoots n (1 : R) } ≤ Multiset.card (nthRoots n (1 : R)).attach :=
      Multiset.card_le_of_le (Multiset.dedup_le _)
    rw [Multiset.card_attach] at hcard
    rw [← PNat.toPNat'_coe hpos] at hcard h ⊢
    set m := Nat.toPNat' n
    rw [← Fintype.card_congr (rootsOfUnityEquivNthRoots R m), card_rootsOfUnity h] at hcard
    exact hcard

/-- The multiset `nthRoots ↑n (1 : R)` has no repeated elements
if there is a primitive root of unity in `R`. -/
theorem nthRoots_nodup {ζ : R} {n : ℕ} (h : IsPrimitiveRoot ζ n) : (nthRoots n (1 : R)).Nodup := by
  cases' Nat.eq_zero_or_pos n with hzero hpos
  · simp only [hzero, Multiset.nodup_zero, nthRoots_zero]
  apply (Multiset.dedup_eq_self (α := R)).1
  rw [eq_iff_le_not_lt]
  constructor
  · exact Multiset.dedup_le (nthRoots n (1 : R))
  · by_contra ha
    replace ha := Multiset.card_lt_of_lt ha
    rw [card_nthRoots h] at ha
    have hrw : Multiset.card (nthRoots n (1 : R)).dedup =
        Fintype.card { x // x ∈ nthRoots n (1 : R) } := by
      set fs := (⟨(nthRoots n (1 : R)).dedup, Multiset.nodup_dedup _⟩ : Finset R)
      rw [← Finset.card_mk, Fintype.card_of_subtype fs _]
      intro x
      simp only [Multiset.mem_dedup, Finset.mem_mk]
    rw [← PNat.toPNat'_coe hpos] at h hrw ha
    set m := Nat.toPNat' n
    rw [hrw, ← Fintype.card_congr (rootsOfUnityEquivNthRoots R m), card_rootsOfUnity h] at ha
    exact Nat.lt_asymm ha ha

@[simp]
theorem card_nthRootsFinset {ζ : R} {n : ℕ} (h : IsPrimitiveRoot ζ n) :
    (nthRootsFinset n R).card = n := by
  rw [nthRootsFinset, ← Multiset.toFinset_eq (nthRoots_nodup h), card_mk, h.card_nthRoots]

open scoped Nat

/-- If an integral domain has a primitive `k`-th root of unity, then it has `φ k` of them. -/
theorem card_primitiveRoots {ζ : R} {k : ℕ} (h : IsPrimitiveRoot ζ k) :
    (primitiveRoots k R).card = φ k := by
  by_cases h0 : k = 0
  · simp [h0]
  symm
  refine' Finset.card_congr (fun i _ => ζ ^ i) _ _ _
  · simp only [true_and_iff, and_imp, mem_filter, mem_range, mem_univ]
    rintro i - hi
    rw [mem_primitiveRoots (Nat.pos_of_ne_zero h0)]
    exact h.pow_of_coprime i hi.symm
  · simp only [true_and_iff, and_imp, mem_filter, mem_range, mem_univ]
    rintro i j hi - hj - H
    exact h.pow_inj hi hj H
  · simp only [exists_prop, true_and_iff, mem_filter, mem_range, mem_univ]
    intro ξ hξ
    rw [mem_primitiveRoots (Nat.pos_of_ne_zero h0),
      h.isPrimitiveRoot_iff (Nat.pos_of_ne_zero h0)] at hξ
    rcases hξ with ⟨i, hin, hi, H⟩
    exact ⟨i, ⟨hin, hi.symm⟩, H⟩

/-- The sets `primitiveRoots k R` are pairwise disjoint. -/
theorem disjoint {k l : ℕ} (h : k ≠ l) : Disjoint (primitiveRoots k R) (primitiveRoots l R) :=
  Finset.disjoint_left.2 fun _ hk hl =>
    h <|
      (isPrimitiveRoot_of_mem_primitiveRoots hk).unique <| isPrimitiveRoot_of_mem_primitiveRoots hl

/-- `nthRoots n` as a `Finset` is equal to the union of `primitiveRoots i R` for `i ∣ n`
if there is a primitive root of unity in `R`.
This holds for any `Nat`, not just `PNat`, see `nthRoots_one_eq_bUnion_primitive_roots`. -/
theorem nthRoots_one_eq_biUnion_primitiveRoots' {ζ : R} {n : ℕ+} (h : IsPrimitiveRoot ζ n) :
    nthRootsFinset n R = (Nat.divisors ↑n).biUnion fun i => primitiveRoots i R := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro x
    simp only [nthRootsFinset, ← Multiset.toFinset_eq (nthRoots_nodup h), exists_prop,
      Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range, mem_nthRoots, Finset.mem_mk,
      Nat.mem_divisors, and_true_iff, Ne.def, PNat.ne_zero, PNat.pos, not_false_iff]
    rintro ⟨a, ⟨d, hd⟩, ha⟩
    have hazero : 0 < a := by
      contrapose! hd with ha0
      simp_all only [nonpos_iff_eq_zero, zero_mul]
      exact n.ne_zero
    rw [mem_primitiveRoots hazero] at ha
    rw [hd, pow_mul, ha.pow_eq_one, one_pow]
  · apply le_of_eq
    rw [h.card_nthRootsFinset, Finset.card_biUnion]
    · nth_rw 1 [← Nat.sum_totient n]
      refine' sum_congr rfl _
      simp only [Nat.mem_divisors]
      rintro k ⟨⟨d, hd⟩, -⟩
      rw [mul_comm] at hd
      rw [(h.pow n.pos hd).card_primitiveRoots]
    · intro i _ j _ hdiff
      exact disjoint hdiff

/-- `nthRoots n` as a `Finset` is equal to the union of `primitiveRoots i R` for `i ∣ n`
if there is a primitive root of unity in `R`. -/
theorem nthRoots_one_eq_biUnion_primitiveRoots {ζ : R} {n : ℕ} (h : IsPrimitiveRoot ζ n) :
    nthRootsFinset n R = (Nat.divisors n).biUnion fun i => primitiveRoots i R := by
  by_cases hn : n = 0
  · simp [hn]
  exact nthRoots_one_eq_biUnion_primitiveRoots' (n := ⟨n, Nat.pos_of_ne_zero hn⟩) h

end IsDomain

section Automorphisms

variable [CommRing S] [IsDomain S] {μ : S} {n : ℕ+} (hμ : IsPrimitiveRoot μ n) (R) [CommRing R]
  [Algebra R S]

/-- The `MonoidHom` that takes an automorphism to the power of μ that μ gets mapped to under it. -/
noncomputable def autToPow : (S ≃ₐ[R] S) →* (ZMod n)ˣ :=
  let μ' := hμ.toRootsOfUnity
  have ho : orderOf μ' = n := by
    rw [hμ.eq_orderOf, ← hμ.val_toRootsOfUnity_coe, orderOf_units, orderOf_subgroup]
  MonoidHom.toHomUnits
    { toFun := fun σ => (map_rootsOfUnity_eq_pow_self σ.toAlgHom μ').choose
      map_one' := by
        dsimp only
        generalize_proofs h1
        have h := h1.choose_spec
        dsimp only [AlgEquiv.one_apply, AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe,
          RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv] at *
        replace h : μ' = μ' ^ h1.choose :=
          rootsOfUnity.coe_injective (by simpa only [rootsOfUnity.coe_pow] using h)
        nth_rw 1 [← pow_one μ'] at h
        rw [← Nat.cast_one, ZMod.nat_cast_eq_nat_cast_iff, ← ho, ← pow_eq_pow_iff_modEq μ', h]
      map_mul' := by
        intro x y
        dsimp only
        generalize_proofs hxy' hx' hy'
        have hxy := hxy'.choose_spec
        have hx := hx'.choose_spec
        have hy := hy'.choose_spec
        dsimp only [AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe,
          RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv, AlgEquiv.mul_apply] at *
        replace hxy : x (((μ' : Sˣ) : S) ^ hy'.choose) = ((μ' : Sˣ) : S) ^ hxy'.choose := hy ▸ hxy
        rw [x.map_pow] at hxy
        replace hxy : (((μ' : Sˣ) : S) ^ hx'.choose) ^ hy'.choose = ((μ' : Sˣ) : S) ^ hxy'.choose :=
          hx ▸ hxy
        rw [← pow_mul] at hxy
        replace hxy : μ' ^ (hx'.choose * hy'.choose) = μ' ^ hxy'.choose :=
          rootsOfUnity.coe_injective (by simpa only [rootsOfUnity.coe_pow] using hxy)
        rw [← Nat.cast_mul, ZMod.nat_cast_eq_nat_cast_iff, ← ho, ← pow_eq_pow_iff_modEq μ', hxy] }

-- We are not using @[simps] in aut_to_pow to avoid a timeout.
theorem coe_autToPow_apply (f : S ≃ₐ[R] S) :
    (autToPow R hμ f : ZMod n) =
      ((map_rootsOfUnity_eq_pow_self f hμ.toRootsOfUnity).choose : ZMod n) :=
  rfl

@[simp]
theorem autToPow_spec (f : S ≃ₐ[R] S) : μ ^ (hμ.autToPow R f : ZMod n).val = f μ := by
  rw [IsPrimitiveRoot.coe_autToPow_apply]
  generalize_proofs h
  have := h.choose_spec
  dsimp only [AlgEquiv.toAlgHom_eq_coe, AlgEquiv.coe_algHom] at this
  refine' (_ : ((hμ.toRootsOfUnity : Sˣ) : S) ^ _ = _).trans this.symm
  rw [← rootsOfUnity.coe_pow, ← rootsOfUnity.coe_pow]
  congr 2
  rw [pow_eq_pow_iff_modEq, ZMod.val_nat_cast, hμ.eq_orderOf, ← orderOf_subgroup, ← orderOf_units]
  exact Nat.mod_modEq _ _

end Automorphisms

end IsPrimitiveRoot
