module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PushforwardOfSupportedPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModelDerivedEquivalence
public import StacksFrontier.CategoryTheory.Functor.FlipObjOfUncurryIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BraidingNatIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryTargetNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualTensorSheafHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.Duals
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluationPerfect

/-!
# The derived internal Hom on an algebraic space

Let `X` be an algebraic space. This file defines the derived internal Hom

`R𝓗om(-, -) : D(𝒪_X)ᵒᵖ ⥤ D(𝒪_X) ⥤ D(𝒪_X)`

on the derived category of `𝒪_X`-modules, and proves the tensor–Hom adjunction and, for a
perfect source `E`, the identification `R𝓗om(E, G) ≅ E^∨ ⊗^L G`, together with the perfectness
of `E^∨` and the isomorphism `(E^∨)^∨ ≅ E`.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDerivedSheafHom`: `R𝓗om(-, -)` on `D(𝒪_X)`.
* `AlgebraicGeometry.Space.smallEtaleDerivedTensorSheafHomAdjunction`: the adjunction
  `- ⊗^L P ⊣ R𝓗om(P, -)`.
* `AlgebraicGeometry.Space.smallEtaleDerivedDual`: the dual `E^∨ = R𝓗om(E, 𝒪_X)`.
* `AlgebraicGeometry.Space.smallEtaleDerivedSheafHomIsoTensorDual`:
  `R𝓗om(E, G) ≅ E^∨ ⊗^L G` for `E` perfect.
* `AlgebraicGeometry.Space.smallEtaleDerivedBidualIso`: `(E^∨)^∨ ≅ E` for `E` perfect.

## Main results

* `AlgebraicGeometry.Space.isPerfect_smallEtaleDerivedDual`: the dual of a perfect object is
  perfect.

## References

* [Stacks Project, Tag 08DH](https://stacks.math.columbia.edu/tag/08DH)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] hasMapBifunctor_sheafTensor_smallEtaleModel

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **The derived internal Hom** `R𝓗om(-, -)` on `D(𝒪_X)` for an algebraic space `X`,
contravariant in its first variable: the derived internal Hom of the equi-universe model of the
small étale ringed site, read through the derived equivalence with the model. -/
def smallEtaleDerivedSheafHom :
    (DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))ᵒᵖ ⥤
      DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ⥤
        DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :=
  (smallEtaleModelDerivedEquivalence B S hS X).functor.op ⋙
    RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS X.1 X.2) ⋙
      (Functor.whiskeringLeft _ _ _).obj (smallEtaleModelDerivedEquivalence B S hS X).functor ⋙
        (Functor.whiskeringRight _ _ _).obj (smallEtaleModelDerivedEquivalence B S hS X).inverse

/-- `R𝓗om(P, G)` is the derived internal Hom of the model at the images of `P` and `G`, brought
back along the derived equivalence. -/
theorem smallEtaleDerivedSheafHom_obj_obj
    (P G : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    ((smallEtaleDerivedSheafHom B S hS X).obj (op P)).obj G =
      (smallEtaleModelDerivedEquivalence B S hS X).inverse.obj
        (((RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS X.1 X.2)).obj
          (op ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj P))).obj
            ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj G)) := rfl

/-- Tensoring with `P` on `X` is tensoring with the image of `P` on the model, read through the
derived equivalence. -/
def smallEtaleDerivedTensorRightIso
    (P : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    (smallEtaleDerivedTensor B S hS X).flip.obj P ≅
      (smallEtaleModelDerivedEquivalence B S hS X).functor ⋙
        (Stacks.SheafOfModules.derivedTensorProductFunctor
          (smallEtaleModelRingedSite B S hS X.1 X.2)).flip.obj
            ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj P) ⋙
          (smallEtaleModelDerivedEquivalence B S hS X).inverse :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (smallEtaleModelDerivedEquivalence B S hS X).unitIso ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.flipObjIsoOfUncurryIso (smallEtaleModelDerivedTensorIso B S hS X) P) _ ≪≫
    Functor.associator _ _ _

/-- For `P` in `D(𝒪_X)`, tensoring with `P` is left adjoint to `R𝓗om(P, -)`:
`Hom(K ⊗^L P, G) ≃ Hom(K, R𝓗om(P, G))`, naturally in `K` and `G`. -/
def smallEtaleDerivedTensorSheafHomAdjunction
    (P : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    (smallEtaleDerivedTensor B S hS X).flip.obj P ⊣
      (smallEtaleDerivedSheafHom B S hS X).obj (op P) :=
  (((smallEtaleModelDerivedEquivalence B S hS X).toAdjunction.comp
    (RingedSite.derivedTensorSheafHomAdjunction (smallEtaleModelRingedSite B S hS X.1 X.2)
      ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj P))).comp
        (smallEtaleModelDerivedEquivalence B S hS X).symm.toAdjunction).ofNatIsoLeft
    (smallEtaleDerivedTensorRightIso B S hS X P).symm

/-- The module equivalence with the model carries `𝒪_X` to the structure sheaf of the model. -/
def smallEtaleModelModulesUnitIso :
    (smallEtaleModelModulesEquivalence B S hS X).functor.obj
        (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X)) ≅
      SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS X.1 X.2).O) :=
  Iso.refl _

/-- The derived equivalence with the model carries `𝒪_X` in degree zero to the structure sheaf
of the model in degree zero. -/
def smallEtaleModelDerivedStructureSheafIso :
    (smallEtaleModelDerivedEquivalence B S hS X).functor.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X))) ≅
      RingedSite.derivedStructureSheaf (smallEtaleModelRingedSite B S hS X.1 X.2) :=
  ((smallEtaleModelModulesEquivalence B S hS X).functor.mapDerivedCategorySingleFunctor 0).app
      (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X)) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (smallEtaleModelModulesUnitIso B S hS X)

/-- **The derived dual** `E^∨ = R𝓗om(E, 𝒪_X)` of an object of `D(𝒪_X)`. -/
abbrev smallEtaleDerivedDual
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :=
  ((smallEtaleDerivedSheafHom B S hS X).obj (Opposite.op E)).obj
    ((DerivedCategory.singleFunctor _ 0).obj
          (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X)))

/-- The derived dual on `X` read on the model is the derived dual of the model. -/
def smallEtaleModelDerivedDualIso
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    (smallEtaleModelDerivedEquivalence B S hS X).functor.obj (smallEtaleDerivedDual B S hS X E) ≅
      RingedSite.derivedDual (smallEtaleModelRingedSite B S hS X.1 X.2)
        ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj E) :=
  (smallEtaleModelDerivedEquivalence B S hS X).counitIso.app _ ≪≫
    ((RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS X.1 X.2)).obj
      (Opposite.op ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj E))).mapIso
        (smallEtaleModelDerivedStructureSheafIso B S hS X)

/-- The derived dual of a perfect object of `D(𝒪_X)` is perfect. -/
theorem isPerfect_smallEtaleDerivedDual
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E) :
    RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2)
      (smallEtaleDerivedDual B S hS X E) := by
  exact RingedSite.IsPerfect.of_iso _
    (isPerfect_smallEtaleModelDerivedEquivalence_inverse_obj B S hS X _
      (RingedSite.isPerfect_derivedDual (smallEtaleModelRingedSite B S hS X.1 X.2) _
        (isPerfect_smallEtaleModelDerivedEquivalence_functor_obj B S hS X E hE)))
    ((smallEtaleModelDerivedEquivalence B S hS X).inverse.mapIso
      (((RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS X.1 X.2)).obj
        (Opposite.op ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj E))).mapIso
          (smallEtaleModelDerivedStructureSheafIso B S hS X)).symm)

/-- For `E` perfect and any `G` in `D(𝒪_X)`, the derived internal Hom out of `E` is tensoring
with its dual: `R𝓗om(E, G) ≅ E^∨ ⊗^L G`. -/
def smallEtaleDerivedSheafHomIsoTensorDual
    (E G : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E) :
    ((smallEtaleDerivedSheafHom B S hS X).obj (Opposite.op E)).obj G ≅
      ((smallEtaleDerivedTensor B S hS X).obj (smallEtaleDerivedDual B S hS X E)).obj G :=
  (smallEtaleModelDerivedEquivalence B S hS X).inverse.mapIso
      ((RingedSite.derivedDualTensorSheafHomIso (smallEtaleModelRingedSite B S hS X.1 X.2)
          ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj E)
          ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj G)
          (isPerfect_smallEtaleModelDerivedEquivalence_functor_obj B S hS X E hE)).symm ≪≫
        ((Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingNatIso
          (smallEtaleModelRingedSite B S hS X.1 X.2)
          (RingedSite.canonicalRingedSiteDerivedTensorProduct
            (smallEtaleModelRingedSite B S hS X.1 X.2))).app _).app _ ≪≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor
          (smallEtaleModelRingedSite B S hS X.1 X.2)).mapIso
            (smallEtaleModelDerivedDualIso B S hS X E).symm).app _ ≪≫
        ((smallEtaleModelDerivedTensorIso B S hS X).app
          (smallEtaleDerivedDual B S hS X E, G)).symm) ≪≫
    ((smallEtaleModelDerivedEquivalence B S hS X).unitIso.app _).symm

/-- A perfect object `E` of `D(𝒪_X)` is isomorphic to its double dual: `(E^∨)^∨ ≅ E`. -/
def smallEtaleDerivedBidualIso
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E) :
    smallEtaleDerivedDual B S hS X (smallEtaleDerivedDual B S hS X E) ≅ E :=
  let e := smallEtaleModelDerivedEquivalence B S hS X
  let M := smallEtaleModelRingedSite B S hS X.1 X.2
  haveI := RingedSite.isIso_derivedBidual_of_isPerfect M
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct M) (e.functor.obj E)
    (isPerfect_smallEtaleModelDerivedEquivalence_functor_obj B S hS X E hE)
  e.fullyFaithfulFunctor.preimageIso
    (smallEtaleModelDerivedDualIso B S hS X (smallEtaleDerivedDual B S hS X E) ≪≫
      ((RingedSite.derivedSheafHomBifunctor M).mapIso
          (smallEtaleModelDerivedDualIso B S hS X E).op.symm).app
        (RingedSite.derivedStructureSheaf M) ≪≫
      (asIso (RingedSite.derivedBidual M (Stacks.SheafOfModules.canonicalDerivedTensorProduct M)
        (e.functor.obj E))).symm)

end AlgebraicGeometry.Space

end
