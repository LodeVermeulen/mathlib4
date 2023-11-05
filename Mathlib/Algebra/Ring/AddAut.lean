/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.GroupTheory.GroupAction.Group
import Mathlib.Algebra.Module.Basic

#align_import algebra.ring.add_aut from "leanprover-community/mathlib"@"a437a2499163d85d670479f69f625f461cc5fef9"

/-!
# Multiplication on the left/right as additive automorphisms

In this file we define `AddAut.mulLeft` and `AddAut.mulRight`.

See also `AddMonoidHom.mulLeft`, `AddMonoidHom.mulRight`, `AddMonoid.End.mulLeft`, and
`AddMonoid.End.mulRight` for multiplication by `R` as an endomorphism instead of multiplication by
`Rˣ` as an automorphism.
-/


namespace AddAut

variable {R : Type*} [Semiring R]

/-- Left multiplication by a unit of a semiring as an additive automorphism. -/
@[simps! (config := { simpRhs := true })]
def mulLeft : Rˣ →* AddAut R :=
  DistribMulAction.toAddAut _ _

/-- Right multiplication by a unit of a semiring as an additive automorphism. -/
def mulRight (u : Rˣ) : AddAut R :=
  DistribMulAction.toAddAut Rᵐᵒᵖˣ R (Units.opEquiv.symm <| MulOpposite.op u)

@[simp]
theorem mulRight_apply (u : Rˣ) (x : R) : mulRight u x = x * u :=
  rfl

@[simp]
theorem mulRight_symm_apply (u : Rˣ) (x : R) : (mulRight u).symm x = x * u⁻¹ :=
  rfl

end AddAut
