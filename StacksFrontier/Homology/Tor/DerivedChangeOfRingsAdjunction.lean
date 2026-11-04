module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.CategoryTheory.Adjunction.CounitTransport
public import StacksFrontier.Homology.Tor.DerivedChangeOfRings
public import StacksCore.Tactic.StacksAttribute

@[expose] public noncomputable section

/-!
# Derived extension and restriction of scalars are adjoint

Let `f : R →+* A` be a homomorphism of commutative rings. Extension of scalars `M ↦ A ⊗_R M` is
left adjoint to restriction of scalars. Restriction of scalars is exact, so it descends to the
derived categories as it stands, while extension of scalars has to be derived. The adjunction
survives: derived extension of scalars `D(R) ⥤ D(A)` is left adjoint to derived restriction of
scalars `D(A) ⥤ D(R)`.

## Main definitions

* `CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction`: the adjunction
  between any total left-derived model of extension of scalars and derived restriction of
  scalars.

## Main results

Derived extension of scalars is left adjoint to derived restriction of scalars.

* `CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_counit_app`: on a
  localized complex the counit of the adjunction is the degreewise counit of extension and
  restriction of scalars, read through the comparison of the chosen model with degreewise
  extension of scalars.
* `CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_counit_app_eq`: the
  same formula solved for the counit, which is the direction a consumer rewrites with.
* `CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_counit_app_eq_of_iso`:
  the same formula at an object merely *isomorphic* to a localized complex, which is the shape in
  which the counit actually occurs in a composite.
* `CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_unit_app`: on a
  localized complex the unit of the adjunction is the degreewise unit `X ⟶ A ⊗_R X` of extension
  and restriction of scalars, read through the same two comparisons.
* `CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_unit_app_eq`: the
  same formula solved for the unit, which needs the comparison to be invertible at the complex.
* `CochainComplex.DerivedExtensionScalars.isIso_comparison_app_of_kFlat`: the comparison of any
  left derived model with degreewise extension of scalars is invertible on K-flat complexes.
* `CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_unit_app_eq_of_kFlat`:
  the unit solved for at a K-flat complex, where the previous two combine unconditionally.

## Implementation notes

The adjunction is produced from the degreewise adjunction on complexes by the general criterion
that a left derived functor of the left adjoint is left adjoint to a right derived functor of the
right adjoint, once both derived functors remain derived after postcomposition with the other.

For restriction of scalars this is automatic: it inverts quasi-isomorphisms, so its descent to
derived categories is a derived functor of itself, and so is any composite with it. For extension
of scalars it is the absoluteness statement proved from K-flat resolutions: the specified counit
is invertible on K-flat complexes, and that property is preserved by arbitrary postcomposition.
Consequently no absoluteness hypothesis has to be imposed on the chosen model `F`.

The two ring universes and the module universe are independent; the ambient module universe is
taken above both ring universes. The `letI` bindings in the statement supply the adjunction
instances for the degreewise functors at that universe and introduce no hypotheses.

The two derived categories are **instance arguments**: the statement takes
`[HasDerivedCategory.{wR} (ModuleCat.{max uR uA uM} R)]` and
`[HasDerivedCategory.{wA} (ModuleCat.{max uR uA uM} A)]` rather than fixing them with a
file-level `attribute [local instance] HasDerivedCategory.standard`. That matters because
`HasDerivedCategory` is `CategoryTheory.MorphismProperty.HasLocalization`, a class carrying
*data* — the localized category together with its localization functor — so
`DerivedCategory (ModuleCat R)` at two instances is literally two different types, and an
adjunction built at the standard model says nothing about any other. Instantiating the binders
at `HasDerivedCategory.standard`, that is at `wR = wA = max uR uA uM + 1`, recovers the old
statement verbatim, so nothing is lost; what is gained is that the adjunction is now available
at the locally small models of `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean` and
`StacksFrontier/AlgebraicGeometry/DerivedTilde/Basic.lean`, whose morphism universe is
`max uR uA uM` rather than its successor, and which is where the direct-sum and
dualizing-complex statements about `D(R)` and `D(𝒪_X)` have content.

## References

* [The Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

open CategoryTheory

universe uR uA uM wR wA

namespace CochainComplex.DerivedExtensionScalars

/-- **Stacks 0GMT.** Derived extension of scalars along a homomorphism of commutative rings is
left adjoint to derived restriction of scalars. The extension functor may be any model equipped
with the total-left-derived universal property, since uniqueness of left derived functors
identifies it with the model computed by K-flat resolutions. -/
@[stacks 0GMT]
public def derivedExtensionScalarsAdjunction
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
    [HasDerivedCategory.{wR} (ModuleCat.{max uR uA uM} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max uR uA uM} A)] :
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    ∀ (F : CategoryTheory.Functor (DerivedCategory (ModuleCat.{max uR uA uM} R))
      (DerivedCategory (ModuleCat.{max uR uA uM} A)))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))],
    F ⊣ (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategory := by
  letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
  letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
  letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
  intro F comparison hF
  haveI := hF
  let adj₀ := ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f
  letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).Additive :=
    adj₀.left_adjoint_additive
  let W_R := HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (.up ℤ)
  let W_A := HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} A) (.up ℤ)
  let S := ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f
  let β := S.mapDerivedCategoryFactors.inv
  have : S.mapDerivedCategory.IsRightDerivedFunctor β W_A :=
    Functor.isRightDerivedFunctor_of_inverts W_A _ S.mapDerivedCategoryFactors
  have : (S.mapDerivedCategory ⋙ F).IsRightDerivedFunctor
      (Functor.whiskerRight β F ≫ (Functor.associator _ _ _).hom) W_A :=
    Functor.isRightDerivedFunctor_of_inverts W_A _
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight S.mapDerivedCategoryFactors F)
  let α : DerivedCategory.Q ⋙ F ⟶
      CochainComplex.extendScalarsLarge.{uM, uR, uA} f ⋙ DerivedCategory.Q := comparison
  haveI : F.IsLeftDerivedFunctor α W_R := hF
  have : (F ⋙ S.mapDerivedCategory).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight comparison S.mapDerivedCategory)
      W_R :=
    CochainComplex.DerivedTensor.KFlatDerived.isLeftDerivedFunctor_extension_postcomp.{uR, uA, uM}
      f F α S.mapDerivedCategory
  exact (adj₀.mapHomologicalComplex (.up ℤ)).derived W_R W_A comparison β

/-- The counit of `derivedExtensionScalarsAdjunction` at a localized complex
`DerivedCategory.Q.obj X` is the degreewise counit `A ⊗_R X ⟶ X` of the extension–restriction
adjunction on cochain complexes, read through the comparison `comparison` of the chosen model
with degreewise extension of scalars and through the factorization
`CategoryTheory.Functor.mapDerivedCategoryFactors` of derived restriction of scalars.

This records that the derived adjunction is *normalized*: nothing beyond the degreewise counit
enters it, so a consumer evaluating the counit on an object in the image of
`DerivedCategory.Q` never has to look inside the Kan extension defining it. -/
public theorem derivedExtensionScalarsAdjunction_counit_app
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
    [HasDerivedCategory.{wR} (ModuleCat.{max uR uA uM} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max uR uA uM} A)] :
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).Additive :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).left_adjoint_additive
    ∀ (F : CategoryTheory.Functor (DerivedCategory (ModuleCat.{max uR uA uM} R))
      (DerivedCategory (ModuleCat.{max uR uA uM} A)))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]
    (X : CochainComplex (ModuleCat.{max uR uA uM} A) ℤ),
    F.map ((ModuleCat.restrictScalars.{max uR uA uM, uR, uA}
          f).mapDerivedCategoryFactors.inv.app X) ≫
        (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).counit.app
          (DerivedCategory.Q.obj X) =
      comparison.app (((ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj X) ≫
        DerivedCategory.Q.map
          (((ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).counit.app X) := by
  let adj₀ := ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f
  have := adj₀.left_adjoint_additive
  intro F comparison hF X
  let W_A := HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} A) (.up ℤ)
  let S := ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f
  let β := S.mapDerivedCategoryFactors.inv
  have : S.mapDerivedCategory.IsRightDerivedFunctor β W_A :=
    Functor.isRightDerivedFunctor_of_inverts W_A _ S.mapDerivedCategoryFactors
  have : (S.mapDerivedCategory ⋙ F).IsRightDerivedFunctor
      (Functor.whiskerRight β F ≫ (Functor.associator _ _ _).hom) W_A :=
    Functor.isRightDerivedFunctor_of_inverts W_A _
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight S.mapDerivedCategoryFactors F)
  exact (adj₀.mapHomologicalComplex (.up ℤ)).derivedε_fac_app W_A comparison β X

/-- `derivedExtensionScalarsAdjunction_counit_app` solved for the counit: at a localized complex
`DerivedCategory.Q.obj X`, the counit of `derivedExtensionScalarsAdjunction` is the degreewise
counit of the extension–restriction adjunction on cochain complexes, transported forward along
`CategoryTheory.Functor.mapDerivedCategoryFactors` and the comparison `comparison`.

This is the direction consumers rewrite with: the counit itself appears alone on the left, so an
occurrence of it can be replaced by the explicit composite without first producing the
isomorphism `(ModuleCat.restrictScalars f).mapDerivedCategoryFactors` out of thin air. -/
public theorem derivedExtensionScalarsAdjunction_counit_app_eq
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
    [HasDerivedCategory.{wR} (ModuleCat.{max uR uA uM} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max uR uA uM} A)] :
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).Additive :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).left_adjoint_additive
    ∀ (F : CategoryTheory.Functor (DerivedCategory (ModuleCat.{max uR uA uM} R))
      (DerivedCategory (ModuleCat.{max uR uA uM} A)))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]
    (X : CochainComplex (ModuleCat.{max uR uA uM} A) ℤ),
    (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).counit.app
        (DerivedCategory.Q.obj X) =
      F.map ((ModuleCat.restrictScalars.{max uR uA uM, uR, uA}
          f).mapDerivedCategoryFactors.hom.app X) ≫
        comparison.app (((ModuleCat.restrictScalars.{max uR uA uM, uR, uA}
            f).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫
          DerivedCategory.Q.map
            (((ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).counit.app X) := by
  intro F comparison hF X
  rw [← derivedExtensionScalarsAdjunction_counit_app.{uR, uA, uM} f F comparison X,
    ← Category.assoc, ← F.map_comp, Iso.hom_inv_id_app, F.map_id, Category.id_comp]

/-- **The counit of `derivedExtensionScalarsAdjunction` at an object merely isomorphic to a
localized complex.**  Given an isomorphism `e : N ≅ DerivedCategory.Q.obj X`, the counit at `N` is
the counit at `DerivedCategory.Q.obj X` -- which
`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_counit_app_eq` values --
conjugated by `e`.

This is the shape a consumer needs. `…_counit_app_eq` values the counit only at an object
*presented* as a localization, while the occurrences a composite contains are at objects built by
other functors, for which only an isomorphism to such a presentation is available; and such an
isomorphism always exists, since `DerivedCategory.Q` is essentially surjective. So the counit is
determinate at every object, not only at the classes. -/
public theorem derivedExtensionScalarsAdjunction_counit_app_eq_of_iso
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
    [HasDerivedCategory.{wR} (ModuleCat.{max uR uA uM} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max uR uA uM} A)] :
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).Additive :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).left_adjoint_additive
    ∀ (F : CategoryTheory.Functor (DerivedCategory (ModuleCat.{max uR uA uM} R))
      (DerivedCategory (ModuleCat.{max uR uA uM} A)))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]
    (N : DerivedCategory (ModuleCat.{max uR uA uM} A))
    (X : CochainComplex (ModuleCat.{max uR uA uM} A) ℤ) (e : N ≅ DerivedCategory.Q.obj X),
    (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).counit.app N =
      F.map ((ModuleCat.restrictScalars.{max uR uA uM, uR, uA}
            f).mapDerivedCategory.map e.hom) ≫
        (F.map ((ModuleCat.restrictScalars.{max uR uA uM, uR, uA}
              f).mapDerivedCategoryFactors.hom.app X) ≫
            comparison.app (((ModuleCat.restrictScalars.{max uR uA uM, uR, uA}
                f).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫
              DerivedCategory.Q.map
                (((ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).mapHomologicalComplex
                  (ComplexShape.up ℤ)).counit.app X)) ≫
          e.inv := by
  intro F comparison hF N X e
  rw [Stacks.Adjunction.counit_app_of_iso
      (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison) e,
    derivedExtensionScalarsAdjunction_counit_app_eq.{uR, uA, uM} f F comparison X]

/-- The unit of `derivedExtensionScalarsAdjunction` at a localized complex
`DerivedCategory.Q.obj X` is the degreewise unit `X ⟶ A ⊗_R X` of the extension–restriction
adjunction on cochain complexes, read through the factorization
`CategoryTheory.Functor.mapDerivedCategoryFactors` of derived restriction of scalars and through
the comparison `comparison` of the chosen model with degreewise extension of scalars.

This is the unit counterpart of `derivedExtensionScalarsAdjunction_counit_app`, and records the
same normalization: nothing beyond the degreewise unit enters the derived adjunction, so a
consumer evaluating the unit on an object in the image of `DerivedCategory.Q` never has to look
inside the Kan extension defining it.

Unlike the counit formula, the comparison appears on the *left-hand* side, because it is the unit
that the chosen model's comparison has to be composed with before the degreewise data is reached.
It can only be cancelled where `comparison` is invertible, which is on the K-flat complexes; see
`derivedExtensionScalarsAdjunction_unit_app_eq_of_kFlat`. -/
public theorem derivedExtensionScalarsAdjunction_unit_app
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
    [HasDerivedCategory.{wR} (ModuleCat.{max uR uA uM} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max uR uA uM} A)] :
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).Additive :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).left_adjoint_additive
    ∀ (F : CategoryTheory.Functor (DerivedCategory (ModuleCat.{max uR uA uM} R))
      (DerivedCategory (ModuleCat.{max uR uA uM} A)))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]
    (X : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ),
    (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app
          (DerivedCategory.Q.obj X) ≫
        (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategory.map
          (comparison.app X) =
      DerivedCategory.Q.map
          (((ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app X) ≫
        (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategoryFactors.inv.app
          (((ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj X) := by
  let adj₀ := ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f
  have := adj₀.left_adjoint_additive
  intro F comparison hF X
  let W_R := HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (.up ℤ)
  let S := ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f
  let β := S.mapDerivedCategoryFactors.inv
  let α : DerivedCategory.Q ⋙ F ⟶
      CochainComplex.extendScalarsLarge.{uM, uR, uA} f ⋙ DerivedCategory.Q := comparison
  have : F.IsLeftDerivedFunctor α W_R := hF
  have : (F ⋙ S.mapDerivedCategory).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight comparison S.mapDerivedCategory)
      W_R :=
    CochainComplex.DerivedTensor.KFlatDerived.isLeftDerivedFunctor_extension_postcomp.{uR, uA, uM}
      f F α S.mapDerivedCategory
  exact (adj₀.mapHomologicalComplex (.up ℤ)).derivedη_fac_app W_R comparison β X

/-- `derivedExtensionScalarsAdjunction_unit_app` solved for the unit, wherever the comparison is
invertible at the complex: the unit of `derivedExtensionScalarsAdjunction` at
`DerivedCategory.Q.obj X` is the degreewise unit of the extension–restriction adjunction on
cochain complexes, transported along `CategoryTheory.Functor.mapDerivedCategoryFactors` and then
back along the comparison `comparison`.

This is the direction consumers rewrite with, as
`derivedExtensionScalarsAdjunction_counit_app_eq` is for the counit: the unit itself appears
alone on the left. The `IsIso (comparison.app X)` instance is the one hypothesis the counit
formula did not need; it holds at every K-flat complex by `isIso_comparison_app_of_kFlat`, and
`derivedExtensionScalarsAdjunction_unit_app_eq_of_kFlat` is this lemma with that instance already
supplied. -/
public theorem derivedExtensionScalarsAdjunction_unit_app_eq
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
    [HasDerivedCategory.{wR} (ModuleCat.{max uR uA uM} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max uR uA uM} A)] :
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).Additive :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).left_adjoint_additive
    ∀ (F : CategoryTheory.Functor (DerivedCategory (ModuleCat.{max uR uA uM} R))
      (DerivedCategory (ModuleCat.{max uR uA uM} A)))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]
    (X : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ) [IsIso (comparison.app X)],
    (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app
        (DerivedCategory.Q.obj X) =
      DerivedCategory.Q.map
          (((ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app X) ≫
        (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategoryFactors.inv.app
            (((ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj X) ≫
          (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategory.map
            (inv (comparison.app X)) := by
  intro F comparison hF X hc
  rw [← Category.assoc,
    ← derivedExtensionScalarsAdjunction_unit_app.{uR, uA, uM} f F comparison X,
    Category.assoc, ← CategoryTheory.Functor.map_comp, IsIso.hom_inv_id,
    CategoryTheory.Functor.map_id]
  exact (Category.comp_id _).symm

/-- The comparison of a left derived model of extension of scalars with degreewise extension of
scalars is invertible at every K-flat complex.

This is
`CochainComplex.DerivedTensor.KFlatDerived.isIso_extensionCounit_app_of_kFlat` restated for a
comparison spelled with `CategoryTheory.Functor.mapHomologicalComplex`, which is the spelling
`derivedExtensionScalarsAdjunction` and its unit and counit formulas use. The two spellings are
definitionally equal but not syntactically so, which is enough to stop instance search; this
lemma crosses that gap once. -/
public theorem isIso_comparison_app_of_kFlat
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
    [HasDerivedCategory.{wR} (ModuleCat.{max uR uA uM} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max uR uA uM} A)]
    [(ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).Additive]
    (F : CategoryTheory.Functor (DerivedCategory (ModuleCat.{max uR uA uM} R))
      (DerivedCategory (ModuleCat.{max uR uA uM} A)))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]
    (X : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (hX : CochainComplex.KFlat.{uR, max uM uA} X) :
    IsIso (comparison.app X) := by
  let W_R := HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (.up ℤ)
  let α : DerivedCategory.Q ⋙ F ⟶
      CochainComplex.extendScalarsLarge.{uM, uR, uA} f ⋙ DerivedCategory.Q := comparison
  have : F.IsLeftDerivedFunctor α W_R := ‹_›
  exact CochainComplex.DerivedTensor.KFlatDerived.isIso_extensionCounit_app_of_kFlat.{uR, uA, uM}
    f F α X hX

/-- **The unit of `derivedExtensionScalarsAdjunction` at a K-flat complex.** At a K-flat `X` the
comparison `comparison` is invertible, so `derivedExtensionScalarsAdjunction_unit_app` solves
outright: the unit at `DerivedCategory.Q.obj X` is the degreewise unit `X ⟶ A ⊗_R X` of the
extension–restriction adjunction on cochain complexes, transported along
`CategoryTheory.Functor.mapDerivedCategoryFactors` and back along `comparison`.

This is the form the derived base-change comparison of Chapter 47 consumes: the monoidality
isomorphism of [stacks 068I] is pinned down at exactly the K-flat complexes, so that is where a
transpose of this unit has to be evaluated. -/
public theorem derivedExtensionScalarsAdjunction_unit_app_eq_of_kFlat
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
    [HasDerivedCategory.{wR} (ModuleCat.{max uR uA uM} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max uR uA uM} A)] :
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).Additive :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).left_adjoint_additive
    ∀ (F : CategoryTheory.Functor (DerivedCategory (ModuleCat.{max uR uA uM} R))
      (DerivedCategory (ModuleCat.{max uR uA uM} A)))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]
    (X : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (hX : CochainComplex.KFlat.{uR, max uM uA} X),
    letI : IsIso (comparison.app X) :=
      isIso_comparison_app_of_kFlat.{uR, uA, uM} f F comparison X hX
    (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app
        (DerivedCategory.Q.obj X) =
      DerivedCategory.Q.map
          (((ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app X) ≫
        (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategoryFactors.inv.app
            (((ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj X) ≫
          (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategory.map
            (inv (comparison.app X)) := by
  have := (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).left_adjoint_additive
  intro F comparison hF X hX
  have : IsIso (comparison.app X) :=
    isIso_comparison_app_of_kFlat.{uR, uA, uM} f F comparison X hX
  exact derivedExtensionScalarsAdjunction_unit_app_eq.{uR, uA, uM} f F comparison X

end CochainComplex.DerivedExtensionScalars

end
