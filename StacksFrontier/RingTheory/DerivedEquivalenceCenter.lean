module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import StacksFrontier.Algebra.Category.ModuleCat.Center
public import StacksFrontier.CategoryTheory.Center.Shift

import StacksCore.Tactic.StacksAttribute

/-!
# Derived equivalent algebras have isomorphic centres

Let `R` be a commutative ring and let `A` and `B` be `R`-algebras. [Stacks, Tag 09SD] says: if
`D(A)` and `D(B)` are equivalent as `R`-linear triangulated categories, then the centres of `A`
and `B` are isomorphic as `R`-algebras; in particular, if `A` and `B` are commutative, then
`A ≅ B`. The Stacks project defers the "rather tricky" proof to Rickard and to König–Zimmermann.

## Main results

* `DerivedEquivalence.nonempty_centerAlgEquiv_of_derivedEquivalence`: **Stacks 09SD.** An
  additive, `R`-linear, shift-commuting equivalence `D(A) ≌ D(B)` of the derived categories of
  (left) modules gives an isomorphism `Z(A) ≃ₐ[R] Z(B)`.
* `DerivedEquivalence.nonempty_algEquiv_of_derivedEquivalence`: **Stacks 09SD, the commutative
  case.** For commutative `A` and `B` it gives `A ≃ₐ[R] B`.

Both are unconditional, and live in `StacksFrontier/RingTheory/DerivedMoritaCenter.lean`. The
proof is `DifferentialGradedModule.nonempty_centerAlgEquiv_of_derivedEquivalence`, in the
differential graded derived categories of `Aᵐᵒᵖ` and `Bᵐᵒᵖ` placed in degree zero (a left
`A`-module is a right `Aᵐᵒᵖ`-module), carried there along the degree-zero comparison
`DifferentialGradedModule.degreeZeroDerivedEquivalence`, and the identification of the centre of
`A` with the centre of `Aᵐᵒᵖ`. The given equivalence is not used directly: the proof replaces it
by the equivalence of the proof of [Stacks, Tag 09SA], built from derived tensor products, which
carries the action of a central element of one algebra on its derived category to the action of
a central element of the other. See the file
`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedEquivalenceCenter.lean` for the argument.

## The conditional route through the shift-compatible centre

The declarations `DerivedEquivalence.centerShiftCenterDerivedAlgEquiv`,
`DerivedEquivalence.centerAlgEquiv` and `DerivedEquivalence.algEquiv` below are an older,
conditional approach, kept for reference and carrying no tag. They compare `Z(A)` with the
shift-compatible part `CategoryTheory.CatCenter.shiftSubalgebra R (DerivedCategory (ModuleCat A)) ℤ`
of the centre of the category `D(A)`, through the canonical map
`ModuleCat.centerToShiftCenterDerived R A`, which is injective
(`ModuleCat.centerToShiftCenterDerived_injective`), and transport that centre along the
equivalence (`CategoryTheory.CatCenter.transportShiftAlgEquiv`). They **assume** the surjectivity
of `ModuleCat.centerToShiftCenterDerived R A` and of the same map for `B`, as hypotheses `hA` and
`hB`; that surjectivity is not proved in this library, and it is not known to hold in general —
it is not what Rickard or König–Zimmermann prove, and natural endomorphisms of the identity of a
derived category can be larger than the centre of the ring. So these declarations are strictly
weaker than Tag 09SD and are not a formalization of it.

## Implementation notes

The tagged theorems take an additive, `R`-linear, shift-commuting equivalence; an `R`-linear
equivalence of triangulated categories is in particular one, so this is weaker than the source's
hypothesis, and the conclusion is the source's. The algebras and the base ring live in one
universe `u`, as the differential graded derived categories of this library require; the derived
categories of modules may be taken in any universes.

## References

* [Stacks Project, Tag 09SD](https://stacks.math.columbia.edu/tag/09SD)
* [Stacks Project, Tag 09SA](https://stacks.math.columbia.edu/tag/09SA)
* J. Rickard, *Derived equivalences as derived functors*, Proposition 9.2.
* S. König and A. Zimmermann, *Derived equivalences for group rings*, Proposition 6.3.2.
-/

@[expose] public section

open CategoryTheory

namespace DerivedEquivalence

open scoped ModuleCat.Algebra

universe w₁ w₂ u v

section

variable (R : Type*) [CommRing R]
variable (A : Type u) [Ring A] [Algebra R A] [HasDerivedCategory.{w₁} (ModuleCat.{u} A)]
variable (B : Type v) [Ring B] [Algebra R B] [HasDerivedCategory.{w₂} (ModuleCat.{v} B)]

/-- **The centre of an algebra and the shift-compatible centre of its derived category.** The
canonical map `ModuleCat.centerToShiftCenterDerived` is always injective, so if it is also
surjective it is an isomorphism of `R`-algebras. Surjectivity is assumed, not proved; see the
note on the conditional route at the top of this file. -/
noncomputable def centerShiftCenterDerivedAlgEquiv
    (h : Function.Surjective (ModuleCat.centerToShiftCenterDerived R A)) :
    Subalgebra.center R A ≃ₐ[R]
      CatCenter.shiftSubalgebra R (DerivedCategory (ModuleCat.{u} A)) ℤ :=
  AlgEquiv.ofBijective (ModuleCat.centerToShiftCenterDerived R A)
    ⟨ModuleCat.centerToShiftCenterDerived_injective R A, h⟩

/-- **Conditional comparison of centres through the shift-compatible centre.** Let `A` and `B`
be algebras over a commutative ring `R` whose derived categories are equivalent through an
additive, `R`-linear, shift-commuting equivalence `E`. If the canonical maps from `Z(A)` and from
`Z(B)` to the shift-compatible centres of `D(A)` and of `D(B)` are surjective — which is assumed
here, is not proved in this library and is not known to hold in general — then `Z(A)` and `Z(B)`
are isomorphic as `R`-algebras, by transporting the shift-compatible centre along `E`.

This is not [Stacks, Tag 09SD], which has no such hypothesis; that tag is
`DerivedEquivalence.nonempty_centerAlgEquiv_of_derivedEquivalence`. -/
noncomputable def centerAlgEquiv
    (hA : Function.Surjective (ModuleCat.centerToShiftCenterDerived R A))
    (hB : Function.Surjective (ModuleCat.centerToShiftCenterDerived R B))
    (E : DerivedCategory (ModuleCat.{u} A) ≌ DerivedCategory (ModuleCat.{v} B))
    [E.functor.Additive] [E.functor.Linear R] [E.functor.CommShift ℤ] :
    (Subalgebra.center R A) ≃ₐ[R] (Subalgebra.center R B) :=
  (centerShiftCenterDerivedAlgEquiv R A hA).trans <|
    (CatCenter.transportShiftAlgEquiv (A := ℤ) E R).trans
      (centerShiftCenterDerivedAlgEquiv R B hB).symm

end

section

variable (R : Type*) [CommRing R]
variable (A : Type u) [CommRing A] [Algebra R A] [HasDerivedCategory.{w₁} (ModuleCat.{u} A)]
variable (B : Type v) [CommRing B] [Algebra R B] [HasDerivedCategory.{w₂} (ModuleCat.{v} B)]

/-- **Conditional comparison of commutative algebras through the shift-compatible centre.** A
commutative algebra is its own centre, so the isomorphism of `DerivedEquivalence.centerAlgEquiv`
is an isomorphism `A ≃ₐ[R] B` when `A` and `B` are commutative. The same surjectivity of
`ModuleCat.centerToShiftCenterDerived` is assumed and not proved.

This is not the commutative case of [Stacks, Tag 09SD], which has no such hypothesis; that is
`DerivedEquivalence.nonempty_algEquiv_of_derivedEquivalence`. -/
noncomputable def algEquiv
    (hA : Function.Surjective (ModuleCat.centerToShiftCenterDerived R A))
    (hB : Function.Surjective (ModuleCat.centerToShiftCenterDerived R B))
    (E : DerivedCategory (ModuleCat.{u} A) ≌ DerivedCategory (ModuleCat.{v} B))
    [E.functor.Additive] [E.functor.Linear R] [E.functor.CommShift ℤ] :
    A ≃ₐ[R] B :=
  (Subalgebra.topEquiv.symm.trans
      (Subalgebra.equivOfEq _ _ (Subalgebra.center_eq_top R A).symm)).trans <|
    (centerAlgEquiv R A B hA hB E).trans <|
      (Subalgebra.equivOfEq _ _ (Subalgebra.center_eq_top R B)).trans Subalgebra.topEquiv

end

end DerivedEquivalence

end
