module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentSixTermFirstTerms
public import StacksFrontier.AlgebraicGeometry.RingedSpace.NaiveCotangentComplex
public import StacksFrontier.Cotangent.SheavesOfRings.RingedSpaceInverseImageExt
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentInverseImage
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentPresentationInvariance

/-!
# `Ext` out of the derived pullback of a naive cotangent complex

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces, `a : 𝒜 ⟶ 𝒪_Y` a homomorphism of
sheaves of rings on `Y`, and `𝒢` an `𝒪_X`-module.  This file identifies

`Ext^n_{𝒪_X}(Lf^*NL_{𝒪_Y/𝒜}, 𝒢) = Ext^n_{f⁻¹𝒪_Y}(NL_{f⁻¹𝒪_Y/f⁻¹𝒜}, 𝒢)`,

the right-hand `𝒢` being read as an `f⁻¹𝒪_Y`-module by restriction of scalars along
`f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X`.  This is the reduction step of the proof of Stacks Tag 08U8: the passage to
the inverse-image ringed space (`AlgebraicGeometry.RingedSpace.derivedPullbackExtAddEquiv`),
followed by `f⁻¹NL_{𝒪_Y/𝒜} = NL_{f⁻¹𝒪_Y/f⁻¹𝒜}` (Tag 08TM,
`Stacks.SheafOfModules.naiveCotangentComplexInverseImageIso`).

## Main definitions

* `AlgebraicGeometry.RingedSpace.modulePullbackNaiveCotangentIso`: `π^*NL_{𝒪_Y/𝒜}` is
  `NL_{f⁻¹𝒪_Y/f⁻¹𝒜}`, as complexes of `f⁻¹𝒪_Y`-modules.
* `AlgebraicGeometry.RingedSpace.naiveCotangentExtEquivDerivedPullback`: the identification of
  the two `Ext^n` groups, for an arbitrary `a`.
* `AlgebraicGeometry.RingedSpace.presentationExtEquivDerivedPullback`: the same with `NL(α)` of
  an arbitrary presentation `α` of `f⁻¹𝒪_Y` over `f⁻¹𝒜` on the left (Tag 08TL), as in the
  source's proof of Tag 08U8.
* `AlgebraicGeometry.RingedSpace.relativeNaiveCotangentExtEquivDerivedPullback`: for morphisms
  `f : X ⟶ Y` and `t : Y ⟶ S`, `Ext^n_{f⁻¹𝒪_Y}(NL_{X_A/S}, ι_*𝒢) = Ext^n_{𝒪_X}(Lf^*NL_{Y/S}, 𝒢)`
  with `X_A = (X, f⁻¹𝒪_Y)`; natural in `𝒢`
  (`relativeNaiveCotangentExtEquivDerivedPullback_naturality`).

## Implementation notes

The model of the derived categories is `HasDerivedCategory.standard` as a local instance.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace AlgebraicGeometry.RingedSpace

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (A : TopCat.Sheaf CommRingCat.{u} Y.carrier)
  (a : A ⟶ Y.sheaf)

/-- `NL_{𝒪_Y/𝒜}` as a complex of `𝒪_Y`-modules. -/
abbrev naiveCotangentOver : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ :=
  Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology Y.carrier)
    A Y.sheaf a

/-- `NL_{f⁻¹𝒪_Y/f⁻¹𝒜}` as a complex of modules over the structure sheaf `f⁻¹𝒪_Y` of the
inverse-image ringed space. -/
abbrev inverseImageNaiveCotangent :
    CochainComplex (SheafOfModules.{u} (structureSheafRing (inverseImage Y f.hom.base))) ℤ :=
  Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology X.carrier)
    ((TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj A)
    ((TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj Y.sheaf)
    ((TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).map a)

/-- **Stacks 08TM along the projection of the inverse-image ringed space**: the pullback
`π^*NL_{𝒪_Y/𝒜}` along `π : (X, f⁻¹𝒪_Y) ⟶ (Y, 𝒪_Y)` is `NL_{f⁻¹𝒪_Y/f⁻¹𝒜}`. -/
def modulePullbackNaiveCotangentIso :
    ((modulePullback (inverseImageProjection Y f.hom.base)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (naiveCotangentOver A a) ≅
      inverseImageNaiveCotangent f A a :=
  Stacks.SheafOfModules.naiveCotangentComplexInverseImageIso f.hom.base A Y.sheaf a

/-- `π^*NL_{𝒪_Y/𝒜} ≅ NL_{f⁻¹𝒪_Y/f⁻¹𝒜}` in `D(f⁻¹𝒪_Y)`. -/
def mapDerivedCategoryNaiveCotangentIso :
    (modulePullback (inverseImageProjection Y f.hom.base)).mapDerivedCategory.obj
        (DerivedCategory.Q.obj (naiveCotangentOver A a)) ≅
      DerivedCategory.Q.obj (inverseImageNaiveCotangent f A a) :=
  (modulePullback (inverseImageProjection Y f.hom.base)).mapDerivedCategoryFactors.app
      (naiveCotangentOver A a) ≪≫
    DerivedCategory.Q.mapIso (modulePullbackNaiveCotangentIso f A a)

/-- **`Ext^n_{f⁻¹𝒪_Y}(NL_{f⁻¹𝒪_Y/f⁻¹𝒜}, ι_*𝒢) = Ext^n_{𝒪_X}(Lf^*NL_{𝒪_Y/𝒜}, 𝒢)`**, where
`ι_*𝒢` is `𝒢` read as an `f⁻¹𝒪_Y`-module along `f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X`. -/
def naiveCotangentExtEquivDerivedPullback (G : SheafOfModules.{u} (structureSheafRing X))
    (n : ℤ) :
    (DerivedCategory.Q.obj (inverseImageNaiveCotangent f A a) ⟶
        ((DerivedCategory.singleFunctor _ 0).obj
          ((modulePushforward (inverseImageSourceInclusion f)).obj G))⟦n⟧) ≃+
      ((derivedPullback f).obj (DerivedCategory.Q.obj (naiveCotangentOver A a)) ⟶
        ((DerivedCategory.singleFunctor _ 0).obj G)⟦n⟧) :=
  derivedPullbackExtEquivOfIso f _ (mapDerivedCategoryNaiveCotangentIso f A a) G n

/-- **`Ext^n_{f⁻¹𝒪_Y}(NL(α), ι_*𝒢) = Ext^n_{𝒪_X}(Lf^*NL_{𝒪_Y/𝒜}, 𝒢)`** for an arbitrary
presentation `α : ℰ ⟶ f⁻¹𝒪_Y` of `f⁻¹𝒪_Y` as a quotient of the polynomial algebra
`f⁻¹𝒜[ℰ]`: the previous identification composed with `NL(α) ≅ NL_{f⁻¹𝒪_Y/f⁻¹𝒜}` in `D(f⁻¹𝒪_Y)`
(Tag 08TL, `Stacks.SheafOfModules.presentationNaiveCotangentDerivedIso`). -/
def presentationExtEquivDerivedPullback (E : X.carrier.Presheaf (Type u))
    (α : E ⟶ Stacks.Sites.FreeAlgebra.underlyingPresheaf (Opens.grothendieckTopology X.carrier)
      ((TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj Y.sheaf))
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
      (Stacks.SheafOfModules.presentation (Opens.grothendieckTopology X.carrier)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj A)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj Y.sheaf)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).map a) E α).hom]
    (G : SheafOfModules.{u} (structureSheafRing X)) (n : ℤ) :
    (DerivedCategory.Q.obj
          (show CochainComplex
              (SheafOfModules.{u} (structureSheafRing (inverseImage Y f.hom.base))) ℤ from
            Stacks.SheafOfModules.presentationNaiveCotangentComplex.{u, u, u, u}
              (Opens.grothendieckTopology X.carrier)
              ((TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj A)
              ((TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj Y.sheaf)
              ((TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).map a) E α) ⟶
        ((DerivedCategory.singleFunctor _ 0).obj
          ((modulePushforward (inverseImageSourceInclusion f)).obj G))⟦n⟧) ≃+
      ((derivedPullback f).obj (DerivedCategory.Q.obj (naiveCotangentOver A a)) ⟶
        ((DerivedCategory.singleFunctor _ 0).obj G)⟦n⟧) :=
  derivedPullbackExtEquivOfIso f _
    (mapDerivedCategoryNaiveCotangentIso f A a ≪≫
      (Stacks.SheafOfModules.presentationNaiveCotangentDerivedIso
        ((TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj A)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj Y.sheaf)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).map a) E α).symm) G n

/-! ### The case of `NL_{Y/S}`, read on `NL_{X_A/S}` -/

variable {S : RingedSpace.{u, u}} (t : Y ⟶ S)

/-- The structure map `π⁻¹𝒪_Y ⟶ 𝒪_{X_A}` of the projection of the inverse-image ringed space is
the identity: `𝒪_{X_A}` *is* `π⁻¹𝒪_Y`. -/
theorem ringedSpaceStructureMap_inverseImageProjection :
    Stacks.SheafOfModules.ringedSpaceStructureMap (inverseImageProjection Y f.hom.base) = 𝟙 _ :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).homEquiv_counit _ _
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app
        Y.sheaf)).trans
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
      f.hom.base).left_triangle_components Y.sheaf)

/-- The structure map of `NL_{f⁻¹𝒪_Y/f⁻¹t⁻¹𝒪_S}` is the one of the iterated spelling of the
structure map of `π ≫ t`. -/
theorem inverseImageStructureMap_eq_tower :
    (TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).map
        (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap t) =
      Stacks.SheafOfModules.inverseImageFirstRingMap (inverseImageProjection Y f.hom.base) t ≫
        Stacks.SheafOfModules.ringedSpaceStructureMap (inverseImageProjection Y f.hom.base) := by
  rw [ringedSpaceStructureMap_inverseImageProjection]
  exact (Category.comp_id _).symm

/-- `NL_{f⁻¹𝒪_Y/f⁻¹t⁻¹𝒪_S}` is `NL_{X_A/S}`, the naive cotangent complex of
`π ≫ t : X_A ⟶ S` (Tag 08TN): the base rings `f⁻¹t⁻¹𝒪_S` and `(t ∘ π)⁻¹𝒪_S` are identified by
`Stacks.SheafOfModules.naiveCotangentComplexCompIso`. -/
def inverseImageNaiveCotangentIsoComp :
    inverseImageNaiveCotangent f (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageSheaf t)
        (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap t) ≅
      naiveCotangentComplex (inverseImageProjection Y f.hom.base ≫ t) :=
  eqToIso (congrArg (Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u}
      (Opens.grothendieckTopology X.carrier) _ _) (inverseImageStructureMap_eq_tower f t)) ≪≫
    (Stacks.SheafOfModules.naiveCotangentComplexCompIso
      (inverseImageProjection Y f.hom.base) t).symm

/-- `π^*NL_{Y/S} ≅ NL_{X_A/S}` in `D(f⁻¹𝒪_Y)`. -/
def mapDerivedCategoryRelativeNaiveCotangentIso :
    (modulePullback (inverseImageProjection Y f.hom.base)).mapDerivedCategory.obj
        (DerivedCategory.Q.obj
          (show CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ from
            naiveCotangentComplex t)) ≅
      DerivedCategory.Q.obj
        (show CochainComplex
            (SheafOfModules.{u} (structureSheafRing (inverseImage Y f.hom.base))) ℤ from
          naiveCotangentComplex (inverseImageProjection Y f.hom.base ≫ t)) :=
  mapDerivedCategoryNaiveCotangentIso f _ _ ≪≫
    DerivedCategory.Q.mapIso (inverseImageNaiveCotangentIsoComp f t)

/-- **The transfer `Ext¹_{f⁻¹𝒪_Y}(NL_{X_A/S}, ι_*𝒢) = Ext¹_{𝒪_X}(Lf^*NL_{Y/S}, 𝒢)`**, for
morphisms of ringed spaces `f : X ⟶ Y` and `t : Y ⟶ S` and an `𝒪_X`-module `𝒢`, in every degree
`n`.  Here `X_A = (X, f⁻¹𝒪_Y)` is the inverse-image ringed space, `π : X_A ⟶ Y` its projection,
`ι : X ⟶ X_A` the factorization of `f`, and `NL_{X_A/S}` the naive cotangent complex of
`π ≫ t`.  It is precomposition with `π^*NL_{Y/S} ≅ NL_{X_A/S}` followed by the adjunction
`Lι^* ⊣ Rι_* = ι_*` and `Lf^* = Lι^* ∘ π^*`. -/
def relativeNaiveCotangentExtEquivDerivedPullback
    (G : SheafOfModules.{u} (structureSheafRing X)) (n : ℤ) :
    (DerivedCategory.Q.obj
          (show CochainComplex
              (SheafOfModules.{u} (structureSheafRing (inverseImage Y f.hom.base))) ℤ from
            naiveCotangentComplex (inverseImageProjection Y f.hom.base ≫ t)) ⟶
        ((DerivedCategory.singleFunctor _ 0).obj
          ((modulePushforward (inverseImageSourceInclusion f)).obj G))⟦n⟧) ≃+
      ((derivedPullback f).obj (DerivedCategory.Q.obj
          (show CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ from
            naiveCotangentComplex t)) ⟶
        ((DerivedCategory.singleFunctor _ 0).obj G)⟦n⟧) :=
  derivedPullbackExtEquivOfIso f _ (mapDerivedCategoryRelativeNaiveCotangentIso f t) G n

/-- **Naturality of the transfer in the coefficient module.** -/
theorem relativeNaiveCotangentExtEquivDerivedPullback_naturality
    {G G' : SheafOfModules.{u} (structureSheafRing X)} (g : G ⟶ G') (n : ℤ)
    (x : DerivedCategory.Q.obj
          (show CochainComplex
              (SheafOfModules.{u} (structureSheafRing (inverseImage Y f.hom.base))) ℤ from
            naiveCotangentComplex (inverseImageProjection Y f.hom.base ≫ t)) ⟶
        ((DerivedCategory.singleFunctor _ 0).obj
          ((modulePushforward (inverseImageSourceInclusion f)).obj G))⟦n⟧) :
    relativeNaiveCotangentExtEquivDerivedPullback f t G' n
        (x ≫ ((DerivedCategory.singleFunctor _ 0).map
          ((modulePushforward (inverseImageSourceInclusion f)).map g))⟦n⟧') =
      relativeNaiveCotangentExtEquivDerivedPullback f t G n x ≫
        ((DerivedCategory.singleFunctor _ 0).map g)⟦n⟧' :=
  derivedPullbackExtEquivOfIso_naturality f _ _ g n x

end AlgebraicGeometry.RingedSpace

end
