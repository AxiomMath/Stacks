module

public import Mathlib.CategoryTheory.Localization.Triangulated
public import StacksFrontier.Algebra.DifferentialGraded.Module.QuasiIsomorphism
public import StacksCore.Tactic.StacksAttribute

/-! # The derived category of a differential graded algebra

For a differential graded algebra `(A, d)` over a commutative ring `R`, the derived category
`D(A, d)` is the localization of the homotopy category `K(A, d)` of right differential graded
`A`-modules at the quasi-isomorphisms. Since the quasi-isomorphisms are exactly the morphisms
whose cone is acyclic (Tag 09KW), this localization *is* the Verdier quotient of `K(A, d)` by
the triangulated subcategory of acyclic modules, so it inherits a calculus of fractions and a
triangulated structure. Degree-zero cohomology, which inverts quasi-isomorphisms, descends to
`D(A, d)` uniquely up to a unique compatible natural isomorphism.

## Main definitions

* `DifferentialGradedModule.derivedCategory'`: the derived category `D(A, d)`.

## Main results

* `DifferentialGradedModule.quasiIsomorphisms_hasLeftCalculusOfFractions'` and
  `DifferentialGradedModule.quasiIsomorphisms_isCompatibleWithTriangulation'`: the
  quasi-isomorphisms admit a left calculus of fractions compatible with the triangulation of
  `K(A, d)`, so `D(A, d)` is triangulated and the quotient functor is exact.
* `DifferentialGradedModule.derivedCategory_eq_verdierQuotient'`: `D(A, d)` is the Verdier
  quotient of `K(A, d)` by the acyclic modules.
* `DifferentialGradedModule.degreeZeroCohomology_unique'`: any factorization of degree-zero
  cohomology through the quotient functor agrees with
  `DifferentialGradedModule.degreeZeroCohomologyOnLocalization'` by a unique natural isomorphism
  compatible with the given one.

## Implementation notes

The localization at the quasi-isomorphisms is taken as the definition, so that its quotient
functor `(quasiIsomorphisms' A).Q` and the descended cohomology functor
`DifferentialGradedModule.degreeZeroCohomologyOnLocalization'` of Tag 09KW are available at
once. Everything about the triangulated structure is then transported along
`DifferentialGradedModule.acyclic_trW_eq_quasiIsomorphisms'`, which identifies the two classes
of morphisms, and the identification with the Verdier quotient is the congruence of
`CategoryTheory.MorphismProperty.Localization` along that equality.

Uniqueness of the descent is uniqueness up to a unique natural isomorphism, which is the
appropriate statement for a functor on a localized category: a functor out of
`(quasiIsomorphisms' A).Q` is determined by its restriction only up to such an isomorphism, and
`CategoryTheory.Localization.liftNatIso` produces it while
`CategoryTheory.Localization.natTrans_ext` gives its uniqueness.

## Naming

The primed names here are the Tag 09KX results for the derived category built from
`DifferentialGradedModule.quasiIsomorphisms'`. The unprimed
`DifferentialGradedModule.derivedCategory`,
`DifferentialGradedModule.derivedCategory_eq_verdierQuotient` and
`DifferentialGradedModule.degreeZeroCohomology_unique` are the same results for the parallel
treatment built from `DifferentialGradedModule.quasiIsomorphisms`; the two rest on different
pretriangulated structures on `K(A, d)` and cannot be mixed.

## References

* [Stacks Project, Tag 09KX](https://stacks.math.columbia.edu/tag/09KX)
-/

@[expose] public section

open CategoryTheory

/- This file is stated against the admissible-sequence pretriangulated structure of Tag 09KH,
which is not an instance; it is activated here explicitly. -/
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R)

/-- The derived category `D(A, d)` of right differential graded `A`-modules: the localization
of the homotopy category `K(A, d)` at the quasi-isomorphisms. -/
@[stacks 09KX "derived category"]
abbrev derivedCategory' : Type (u + 1) := (quasiIsomorphisms' A).Localization

/-- The quasi-isomorphisms admit a left calculus of fractions: they are the morphisms whose
cone is acyclic, and the acyclic modules form a triangulated subcategory. -/
instance quasiIsomorphisms_hasLeftCalculusOfFractions' :
    (quasiIsomorphisms' A).HasLeftCalculusOfFractions := by
  rw [← acyclic_trW_eq_quasiIsomorphisms' A]
  infer_instance

/-- The localization of `K(A, d)` at the quasi-isomorphisms is compatible with its
triangulation, so the derived category is triangulated and the quotient functor is exact. -/
instance quasiIsomorphisms_isCompatibleWithTriangulation' :
    (quasiIsomorphisms' A).IsCompatibleWithTriangulation := by
  rw [← acyclic_trW_eq_quasiIsomorphisms' A]
  infer_instance

add_to_stacks 09KX "degree-zero cohomology on the derived category"
  DifferentialGradedModule.degreeZeroCohomologyOnLocalization'
add_to_stacks 09KX "factorization of degree-zero cohomology through the derived category"
  DifferentialGradedModule.degreeZeroCohomologyOnLocalizationIso'

/-- The derived category is the Verdier quotient of the homotopy category by the triangulated
subcategory of acyclic differential graded modules. -/
@[stacks 09KX "Verdier quotient"]
theorem derivedCategory_eq_verdierQuotient' :
    derivedCategory' A = (acyclic' A).verdierQuotient :=
  congrArg MorphismProperty.Localization (acyclic_trW_eq_quasiIsomorphisms' A).symm

/-- Degree-zero cohomology on the derived category is the unique descent of degree-zero
cohomology on the homotopy category: a functor `G` on `D(A, d)` together with an identification
`α` of its restriction along the quotient functor with
`DifferentialGradedModule.degreeZeroCohomologyOnHomotopy'` agrees with
`DifferentialGradedModule.degreeZeroCohomologyOnLocalization'` by a unique natural isomorphism
compatible with `α`. -/
@[stacks 09KX "uniqueness of degree-zero cohomology"]
theorem degreeZeroCohomology_unique' (G : derivedCategory' A ⥤ ModuleCat.{u} R)
    (α : (quasiIsomorphisms' A).Q ⋙ G ≅ degreeZeroCohomologyOnHomotopy' A) :
    ∃! e : G ≅ degreeZeroCohomologyOnLocalization' A,
      Functor.whiskerLeft (quasiIsomorphisms' A).Q e.hom ≫
        (degreeZeroCohomologyOnLocalizationIso' A).hom = α.hom := by
  let Q := (quasiIsomorphisms' A).Q
  let W := quasiIsomorphisms' A
  let F := degreeZeroCohomologyOnLocalization' A
  let δ := degreeZeroCohomologyOnLocalizationIso' A
  let β : Q ⋙ G ≅ Q ⋙ F := α ≪≫ δ.symm
  let e : G ≅ F := Localization.liftNatIso Q W (Q ⋙ G) (Q ⋙ F) G F β
  have he : Functor.whiskerLeft Q e.hom = β.hom := by
    ext X x
    simp [e, β, Localization.liftNatIso]
  have he_prop : Functor.whiskerLeft Q e.hom ≫ δ.hom = α.hom := by
    rw [he]
    simp [β]
  refine ⟨e, he_prop, fun e' he' => Iso.ext <| Localization.natTrans_ext Q W fun X =>
    (cancel_mono (δ.hom.app X)).1 (NatTrans.congr_app (he'.trans he_prop.symm) X)⟩

end DifferentialGradedModule

end
