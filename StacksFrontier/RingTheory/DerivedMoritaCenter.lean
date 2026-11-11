module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import StacksFrontier.Algebra.DifferentialGraded.Module.DegreeZeroDerivedStructure
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedEquivalenceCenter

import StacksCore.Tactic.StacksAttribute

/-!
# Derived equivalent algebras have isomorphic centres: [Stacks, Tag 09SD]

Let `R` be a commutative ring and let `A` and `B` be `R`-algebras. If `D(A)` and `D(B)` are
equivalent as `R`-linear triangulated categories, then the centres of `A` and `B` are isomorphic
as `R`-algebras; in particular, if `A` and `B` are commutative, then `A ≅ B`.

## Main results

* `DerivedEquivalence.nonempty_centerAlgEquiv_of_derivedEquivalence`: **Stacks 09SD.**
* `DerivedEquivalence.nonempty_algEquiv_of_derivedEquivalence`: **Stacks 09SD**, the commutative
  case.

## Implementation notes

The derived categories are Mathlib's `DerivedCategory (ModuleCat A)` of left `A`-modules, in any
universes. The hypothesis on the equivalence is that its functor is additive, `R`-linear and
commutes with the shift; an `R`-linear equivalence of triangulated categories is such, so this is
weaker than the source's hypothesis, and the conclusion is the source's. The base ring and the two
algebras live in one universe `u`, as the differential graded derived categories through which
the proof goes require.

The proof is `DifferentialGradedModule.nonempty_centerAlgEquiv_of_derivedEquivalence`, applied to
the differential graded algebras `Aᵐᵒᵖ` and `Bᵐᵒᵖ` placed in degree zero (a left `A`-module being a
right `Aᵐᵒᵖ`-module) through the degree-zero comparison
`DifferentialGradedModule.degreeZeroDerivedEquivalence`; see that declaration's file for the
argument, which follows Rickard. The conditional declarations
`DerivedEquivalence.centerAlgEquiv` and `DerivedEquivalence.algEquiv` of
`StacksFrontier/RingTheory/DerivedEquivalenceCenter.lean` are not used.

## References

* [Stacks Project, Tag 09SD](https://stacks.math.columbia.edu/tag/09SD)
* J. Rickard, *Derived equivalences as derived functors*, Proposition 9.2.
-/

@[expose] public section

open CategoryTheory

namespace DerivedEquivalence

open scoped ModuleCat.Algebra

universe w₁ w₂ u

/-! ### Stacks 09SD -/

section Unconditional

variable (R : Type u) [CommRing R]

/-- The centre of an algebra and the centre of its opposite algebra are isomorphic as
`R`-algebras, by `a ↦ op a`. -/
def centerOpAlgEquiv (A : Type*) [Ring A] [Algebra R A] :
    Subalgebra.center R A ≃ₐ[R] Subalgebra.center R Aᵐᵒᵖ where
  toFun a := ⟨MulOpposite.op (a : A), by
    rw [Subalgebra.mem_center_iff]
    intro b
    induction b using MulOpposite.rec' with | _ b => ?_
    rw [← MulOpposite.op_mul, ← MulOpposite.op_mul, Subalgebra.mem_center_iff.1 a.2 b]⟩
  invFun c := ⟨MulOpposite.unop (c : Aᵐᵒᵖ), by
    rw [Subalgebra.mem_center_iff]
    intro g
    apply MulOpposite.op_injective
    rw [MulOpposite.op_mul, MulOpposite.op_mul, MulOpposite.op_unop,
      Subalgebra.mem_center_iff.1 c.2 (MulOpposite.op g)]⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' a b := Subtype.ext (by
    change MulOpposite.op ((a : A) * b) = MulOpposite.op (a : A) * MulOpposite.op (b : A)
    rw [← MulOpposite.op_mul, Subalgebra.mem_center_iff.1 a.2 (b : A)])
  map_add' _ _ := rfl
  commutes' _ := rfl

variable (A : Type u) [Ring A] [Algebra R A] [HasDerivedCategory.{w₁} (ModuleCat.{u} A)]
variable (B : Type u) [Ring B] [Algebra R B] [HasDerivedCategory.{w₂} (ModuleCat.{u} B)]

/-- **Stacks 09SD: derived equivalent algebras have isomorphic centres.** Let `R` be a
commutative ring and let `A` and `B` be `R`-algebras. If the derived categories `D(A)` and `D(B)`
of `A`-modules and of `B`-modules are equivalent through an additive, `R`-linear,
shift-commuting equivalence — in particular, if they are equivalent as `R`-linear triangulated
categories — then the centres of `A` and `B` are isomorphic as `R`-algebras.

The proof reads the equivalence in the differential graded derived categories of `Aᵐᵒᵖ` and
`Bᵐᵒᵖ` placed in degree zero and applies
`DifferentialGradedModule.nonempty_centerAlgEquiv_of_derivedEquivalence`; the centre of an algebra
is the centre of its opposite (`DerivedEquivalence.centerOpAlgEquiv`). -/
@[stacks 09SD "the centres of A and B are isomorphic R-algebras, for an additive R-linear \
shift-commuting equivalence D(A) ≌ D(B) of the derived categories of modules (an R-linear \
triangulated equivalence is one); unconditional"]
theorem nonempty_centerAlgEquiv_of_derivedEquivalence
    (E : DerivedCategory (ModuleCat.{u} A) ≌ DerivedCategory (ModuleCat.{u} B))
    [E.functor.Additive] [E.functor.Linear R] [E.functor.CommShift ℤ] :
    Nonempty (Subalgebra.center R A ≃ₐ[R] Subalgebra.center R B) := by
  let := DifferentialGradedAlgebra.IsOppositeAlgebra.opSelf R A
  let := DifferentialGradedAlgebra.IsOppositeAlgebra.opSelf R B
  let EA := DifferentialGradedModule.degreeZeroDerivedEquivalence (R := R) (S := Aᵐᵒᵖ) (A := A)
  let EB := DifferentialGradedModule.degreeZeroDerivedEquivalence (R := R) (S := Bᵐᵒᵖ) (A := B)
  have := EB.commShiftInverse ℤ
  let G := EA.trans (E.trans EB.symm)
  have : G.functor.Additive := by
    change (EA.functor ⋙ E.functor ⋙ EB.inverse).Additive
    infer_instance
  have : G.functor.Linear R := by
    change (EA.functor ⋙ E.functor ⋙ EB.inverse).Linear R
    infer_instance
  have : G.functor.CommShift ℤ := by
    change (EA.functor ⋙ E.functor ⋙ EB.inverse).CommShift ℤ
    infer_instance
  obtain ⟨e⟩ := DifferentialGradedModule.nonempty_centerAlgEquiv_of_derivedEquivalence
    (R := R) Aᵐᵒᵖ Bᵐᵒᵖ G
  exact ⟨(centerOpAlgEquiv R A).trans (e.trans (centerOpAlgEquiv R B).symm)⟩

end Unconditional

section UnconditionalCommutative

variable (R : Type u) [CommRing R]
variable (A : Type u) [CommRing A] [Algebra R A] [HasDerivedCategory.{w₁} (ModuleCat.{u} A)]
variable (B : Type u) [CommRing B] [Algebra R B] [HasDerivedCategory.{w₂} (ModuleCat.{u} B)]

/-- **Stacks 09SD, the commutative case: derived equivalent commutative algebras are
isomorphic.** Let `R` be a commutative ring and let `A` and `B` be commutative `R`-algebras whose
derived categories are equivalent through an additive, `R`-linear, shift-commuting equivalence.
Then `A ≅ B` as `R`-algebras: a commutative algebra is its own centre, so this is
`DerivedEquivalence.nonempty_centerAlgEquiv_of_derivedEquivalence`. -/
@[stacks 09SD "in particular, if A and B are commutative then A ≅ B as R-algebras; unconditional"]
theorem nonempty_algEquiv_of_derivedEquivalence
    (E : DerivedCategory (ModuleCat.{u} A) ≌ DerivedCategory (ModuleCat.{u} B))
    [E.functor.Additive] [E.functor.Linear R] [E.functor.CommShift ℤ] :
    Nonempty (A ≃ₐ[R] B) := by
  obtain ⟨e⟩ := nonempty_centerAlgEquiv_of_derivedEquivalence R A B E
  exact ⟨(Subalgebra.topEquiv.symm.trans
      (Subalgebra.equivOfEq _ _ (Subalgebra.center_eq_top R A).symm)).trans <|
    e.trans <| (Subalgebra.equivOfEq _ _ (Subalgebra.center_eq_top R B)).trans
      Subalgebra.topEquiv⟩

end UnconditionalCommutative

end DerivedEquivalence

end
