module

public import StacksFrontier.Algebra.DGA.Octahedron
public import StacksFrontier.Algebra.DGA.QuasiIsomorphisms

/-!
# The derived category of a differential graded algebra

Let `A` be a differential graded algebra. Its *derived category* is obtained from the homotopy
category of right differential graded `A`-modules by inverting the quasi-isomorphisms, which is
the same thing as killing the acyclic modules. This file introduces the derived category as the
localization at the quasi-isomorphisms of Tag 09KW, and records that degree-zero cohomology on
it is the unique descent of degree-zero cohomology on the homotopy category.

## Main definitions

* `DifferentialGradedModule.derivedCategory` is the derived category of `A`.

## Main results

* `DifferentialGradedModule.quasiIsomorphisms_hasLeftCalculusOfFractions` and
  `DifferentialGradedModule.quasiIsomorphisms_isCompatibleWithTriangulation`: the
  quasi-isomorphisms admit a left calculus of fractions compatible with the triangulation of the
  homotopy category, so the derived category is triangulated and the localization functor is
  exact.
* `DifferentialGradedModule.derivedCategory_eq_verdierQuotient`: the derived category is the
  Verdier quotient of the homotopy category by the acyclic modules.
* `DifferentialGradedModule.degreeZeroCohomology_unique`: the descent of degree-zero cohomology
  through the localization functor is unique up to a unique compatible natural isomorphism.

## Implementation notes

The localization at the quasi-isomorphisms is chosen as the defining model, rather than the
Verdier quotient by the acyclic objects, because its localization functor and its lift of
degree-zero cohomology are the ones Tag 09KW already constructs. The identification with the
Verdier quotient is then the equality of the two classes of morphisms, which is
`DifferentialGradedModule.acyclic_trW_eq_quasiIsomorphisms` of Tag 09KW; the same equality
transports the calculus of fractions and the compatibility with the triangulation from the
acyclic objects to the quasi-isomorphisms.

Uniqueness of the descended functor is uniqueness up to a natural isomorphism compatible with
the localization functor, which is the appropriate statement for a functor on a localized
category: the universal property determines a functor out of a localization only up to such an
isomorphism, and that isomorphism is then itself unique. The proof is the universal property
twice over, through `CategoryTheory.Localization.liftNatIso` for existence and
`CategoryTheory.Localization.natTrans_ext` for uniqueness.

The derived category is stated as an `abbrev` so that the instances carried by
`CategoryTheory.MorphismProperty.Localization` — in particular its category structure — are
found on it without transport.

## References

* [Stacks Project, Tag 09KX](https://stacks.math.columbia.edu/tag/09KX)
-/

@[expose] public section

open CategoryTheory

namespace DifferentialGradedModule

universe u v w

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra.{u, v} R)

/-- The derived category of a differential graded algebra `A`: the localization of the homotopy
category of right differential graded `A`-modules at the quasi-isomorphisms. -/
@[stacks 09KX "derived category"]
abbrev derivedCategory : Type _ :=
  (quasiIsomorphisms.{u, v, w} A).Localization

/-- The quasi-isomorphisms admit a left calculus of fractions: they are the class of morphisms
whose cone is acyclic, and the acyclic objects form a full triangulated subcategory of the
homotopy category, which is itself triangulated. -/
instance quasiIsomorphisms_hasLeftCalculusOfFractions :
    (quasiIsomorphisms.{u, v, w} A).HasLeftCalculusOfFractions := by
  rw [← acyclic_trW_eq_quasiIsomorphisms A]
  infer_instance

/-- The quasi-isomorphisms are compatible with the triangulation of the homotopy category, for
the same reason. -/
instance quasiIsomorphisms_isCompatibleWithTriangulation :
    (quasiIsomorphisms.{u, v, w} A).IsCompatibleWithTriangulation := by
  rw [← acyclic_trW_eq_quasiIsomorphisms A]
  infer_instance

/-- The derived category is the Verdier quotient of the homotopy category by the full
triangulated subcategory of acyclic modules: the two descriptions are localizations of the
homotopy category at the same class of morphisms, by
`DifferentialGradedModule.acyclic_trW_eq_quasiIsomorphisms`. -/
@[stacks 09KX "Verdier quotient"]
theorem derivedCategory_eq_verdierQuotient :
    derivedCategory.{u, v, w} A = (acyclic.{u, v, w} A).verdierQuotient :=
  congrArg MorphismProperty.Localization (acyclic_trW_eq_quasiIsomorphisms A).symm

add_to_stacks 09KX "degree-zero cohomology"
  DifferentialGradedModule.degreeZeroCohomologyOnLocalization
add_to_stacks 09KX "cohomology factorization"
  DifferentialGradedModule.degreeZeroCohomologyOnLocalizationIso

/-- Degree-zero cohomology on the derived category is the unique descent of degree-zero
cohomology on the homotopy category: any functor on the derived category whose composite with the
localization functor is degree-zero cohomology on the homotopy category is uniquely isomorphic to
`DifferentialGradedModule.degreeZeroCohomologyOnLocalization`, by an isomorphism compatible with
the given identification. -/
@[stacks 09KX "uniqueness of degree-zero cohomology"]
theorem degreeZeroCohomology_unique
    (G : derivedCategory.{u, v, w} A ⥤ ModuleCat.{w} R)
    (α : (quasiIsomorphisms A).Q ⋙ G ≅ degreeZeroCohomologyOnHomotopy A) :
    ∃! e : G ≅ degreeZeroCohomologyOnLocalization A,
      Functor.whiskerLeft (quasiIsomorphisms A).Q e.hom ≫
        (degreeZeroCohomologyOnLocalizationIso A).hom = α.hom := by
  let β : (quasiIsomorphisms.{u, v, w} A).Q ⋙ G ≅
      (quasiIsomorphisms.{u, v, w} A).Q ⋙ degreeZeroCohomologyOnLocalization.{u, v, w} A :=
    α ≪≫ (degreeZeroCohomologyOnLocalizationIso.{u, v, w} A).symm
  let e : G ≅ degreeZeroCohomologyOnLocalization.{u, v, w} A :=
    Localization.liftNatIso (quasiIsomorphisms.{u, v, w} A).Q (quasiIsomorphisms.{u, v, w} A)
      _ _ G (degreeZeroCohomologyOnLocalization.{u, v, w} A) β
  have he : Functor.whiskerLeft (quasiIsomorphisms.{u, v, w} A).Q e.hom = β.hom := by
    ext X
    simp [e]
  have he_prop : Functor.whiskerLeft (quasiIsomorphisms.{u, v, w} A).Q e.hom ≫
      (degreeZeroCohomologyOnLocalizationIso.{u, v, w} A).hom = α.hom := by
    rw [he]
    simp [β]
  exact ⟨e, he_prop, fun e' he' => Iso.ext <|
    Localization.natTrans_ext (quasiIsomorphisms.{u, v, w} A).Q (quasiIsomorphisms.{u, v, w} A)
      fun X => (cancel_mono ((degreeZeroCohomologyOnLocalizationIso.{u, v, w} A).hom.app X)).1
        (congrArg (fun η => η.app X) (he'.trans he_prop.symm))⟩

end DifferentialGradedModule

end
