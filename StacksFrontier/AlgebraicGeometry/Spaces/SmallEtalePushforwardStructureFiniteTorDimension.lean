module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.AffineLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.AffineGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.QcqsOverAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineTorAmplitude
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTorIndependentBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModelDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.TorIndependenceComp
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.DerivedPullbackOfToposHomTorAmplitude

/-!
# Finite Tor dimension of the direct image of the structure sheaf under base change

Let `g : U' ⟶ U` be a morphism of affine objects of the big fppf site, with rings `R ⟶ R'`, let
`f : X ⟶ U` be a morphism of algebraic spaces and let `X' = U' ×_U X`, with projections
`g' : X' ⟶ X` and `f' : X' ⟶ U'`.  If `X` and `U'` are Tor independent over `U` and `R'` has
finite Tor dimension over `R`, then `Rg'_*𝒪_{X'}` has finite Tor dimension, on the small étale
site of `X` and on its equi-universe model.

This is the input of the proof of Stacks 0E4S, case (2): by Stacks 08IR at `𝒪_{U'}` for the
transposed square, `Rg'_*𝒪_{X'} ≅ Lf^*Rg_*𝒪_{U'}`; `Rg_*𝒪_{U'}` is the module associated with
`R'` viewed over `R`, which has finite Tor dimension by Stacks 08E9 read on the small étale site
(`AlgebraicGeometry.Space.hasTorAmplitude_representedAffineDerivedAssociated_iff`); and `Lf^*`
and the derived equivalence with the model preserve finite Tor dimension by Stacks 08H5.

## Main results

All declarations live in the namespace `AlgebraicGeometry.Space`.

* `hasTorAmplitude_smallEtaleDerivedModulePullback`: Stacks 08H5 for a morphism of algebraic
  spaces, at arbitrary derived tensor product data.
* `hasFiniteTorDimension_smallEtaleModelDerivedEquivalence_functor_obj`:
  finite Tor dimension passes to the equi-universe model.
* `hasFiniteTorDimension_derivedPushforward_structureDerived_representedSpaceMap`:
  `Rg_*𝒪_{U'}` has finite Tor dimension when `R'` has finite Tor dimension over `R`.
* `hasFiniteTorDimension_derivedPushforward_structureDerived_of_torIndependent`:
  `Rg'_*𝒪_{X'}` has finite Tor dimension.
* `hasFiniteTorDimension_smallEtaleModel_derivedPushforward_structureDerived`:
  the same on the equi-universe model of the small étale site of `X`, and
  `hasFiniteTorDimension_canonical_smallEtaleModel_derivedPushforward_structureDerived`
  at its canonical derived tensor product.

## References

* [Stacks Project, Tag 0E4S](https://stacks.math.columbia.edu/tag/0E4S)
* [Stacks Project, Tag 08IR](https://stacks.math.columbia.edu/tag/08IR)
* [Stacks Project, Tag 08E9](https://stacks.math.columbia.edu/tag/08E9)
* [Stacks Project, Tag 08H5](https://stacks.math.columbia.edu/tag/08H5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPushforward (derivedPushforward)
open Stacks.SheafOfModules Stacks.SheafOfModules.DerivedTensorProduct

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

/- `SheafOfModules.hasBinBiprod`, brought into scope by the base version of
`StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineTorAmplitude`'s imports, gives a second
route to the biproducts of sheaves of modules and leaves the module universe stuck at
`max ?v ?w =?= u`. -/
attribute [-instance] SheafOfModules.hasBinBiprod

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Derived pullback along a morphism of algebraic spaces -/

/-- **Stacks 08H5 for a morphism of algebraic spaces.**  For `f : X ⟶ Y`, the derived pullback
`Lf^*E` of an object `E` of `D(𝒪_Y)` of Tor amplitude in `[a, b]` has Tor amplitude in `[a, b]`,
for arbitrary derived tensor product data on the two small étale sites. -/
theorem hasTorAmplitude_smallEtaleDerivedModulePullback {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (T : DerivedTensorProduct (smallEtaleRingedSite B S hS Y.1 Y.2))
    (T' : DerivedTensorProduct (smallEtaleRingedSite B S hS X.1 X.2))
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) (a b : ℤ)
    (h : HasTorAmplitude T E a b) :
    HasTorAmplitude T' ((smallEtaleDerivedModulePullback B S hS f).obj E) a b :=
  hasTorAmplitude_derivedPullbackOfToposHom.{u, u + 1, u, u, u + 1, u}
    (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
    (smallEtaleRingedToposHom B S hS f) T T' E a b h

/-- **Finite Tor dimension is preserved by derived pullback along a morphism of algebraic
spaces**, for arbitrary derived tensor product data on the two small étale sites. -/
theorem hasFiniteTorDimension_smallEtaleDerivedModulePullback {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (T : DerivedTensorProduct (smallEtaleRingedSite B S hS Y.1 Y.2))
    (T' : DerivedTensorProduct (smallEtaleRingedSite B S hS X.1 X.2))
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (h : HasFiniteTorDimension T E) :
    HasFiniteTorDimension T' ((smallEtaleDerivedModulePullback B S hS f).obj E) :=
  hasFiniteTorDimension_derivedPullbackOfToposHom.{u, u + 1, u, u, u + 1, u}
    (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
    (smallEtaleRingedToposHom B S hS f) T T' E h

/-! ### Passage to the equi-universe model -/

/-- **Tor amplitude passes to the equi-universe model**: the derived equivalence
`D(𝒪_X) ≌ D(𝒪_model)` is the derived pullback along the morphism of ringed topoi from the model
to the small étale site, so Stacks 08H5 applies to it. -/
theorem hasTorAmplitude_smallEtaleModelDerivedEquivalence_functor_obj (X : AlgebraicSpaces B S hS)
    (T : DerivedTensorProduct (smallEtaleRingedSite B S hS X.1 X.2))
    (T' : DerivedTensorProduct (smallEtaleModelRingedSite B S hS X.1 X.2))
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) (a b : ℤ)
    (h : HasTorAmplitude T E a b) :
    HasTorAmplitude T' ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj E) a b :=
  (hasTorAmplitude_derivedPullbackOfToposHom (smallEtaleModelRingedToposHom B S hS X) T T' E a b
    h).of_iso ((smallEtaleModelDerivedPullbackIso B S hS X).app E)

/-- **Finite Tor dimension passes to the equi-universe model.** -/
theorem hasFiniteTorDimension_smallEtaleModelDerivedEquivalence_functor_obj
    (X : AlgebraicSpaces B S hS)
    (T : DerivedTensorProduct (smallEtaleRingedSite B S hS X.1 X.2))
    (T' : DerivedTensorProduct (smallEtaleModelRingedSite B S hS X.1 X.2))
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (h : HasFiniteTorDimension T E) :
    HasFiniteTorDimension T' ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj E) := by
  obtain ⟨a, b, h⟩ := h
  exact ⟨a, b, hasTorAmplitude_smallEtaleModelDerivedEquivalence_functor_obj B S hS X T T' E a b h⟩

/-! ### The direct image of the structure sheaf along a morphism of affine objects -/

section Affine

variable {U' U : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')] (g : U' ⟶ U)

/-- The morphism of represented algebraic spaces induced by a morphism of affine objects is
affine. -/
private theorem isAffineHom_representedSpaceMap :
    IsAffineHom B S hS (representedSpaceMap B S hS g).hom :=
  isAffineHom_of_isAffineSpace B S hS _ (isAffineSpace_yoneda B S hS U' inferInstance)
    (isAffineSpace_yoneda B S hS U inferInstance)

/-- **`Rg_*𝒪_{U'}` has finite Tor dimension when `R'` has finite Tor dimension over `R`.**  For a
morphism `g : U' ⟶ U` of affine objects with rings `R ⟶ R'`, the direct image `Rg_*𝒪_{U'}` is
the module associated with `R'` viewed over `R` (`g` is affine), and Stacks 08E9, read on the
small étale site, carries the Tor amplitude of `R'` over `R` to it. -/
theorem hasFiniteTorDimension_derivedPushforward_structureDerived_representedSpaceMap
    (hR : HasFiniteTorDimensionRingHom (representedAffineCommRingCatHom B S hS g).hom) :
    HasFiniteTorDimension
      (smallEtaleDerivedTensorProduct B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      ((derivedModulePushforward B S hS (representedSpaceMap B S hS g)).obj
        (structureDerived ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩)) := by
  let := (representedAffineCommRingCatHom B S hS g).hom.toAlgebra
  obtain ⟨a, b, h⟩ := hR
  have hg := isAffineHom_representedSpaceMap B S hS g
  have hT := isIso_representedAffineTransportUnit B S hS g hg
    ((DerivedCategory.singleFunctor
        (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)) 0).obj
      (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)))
  refine ⟨a, b, ((hasTorAmplitude_representedAffineDerivedAssociated_iff B S hS U _ a b).2
    h).of_iso ?_⟩
  refine (representedAffineDerivedAssociated B S hS U).mapIso
    ((DerivedCategory.singleFunctorIsoCompQ
        (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) 0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso
        (@id (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
              Γ((BigFppfOver.toScheme B S hS).obj U', ⊤) ≅
            (ModuleCat.restrictScalars (representedAffineCommRingCatHom B S hS g).hom).obj
              (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)
                Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)))
          (StacksDraft.TorAmplitude.FaithfullyFlat.restrictScalarsSelfEquiv
            Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
            Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)).toModuleIso.symm) ≪≫
      (((ModuleCat.restrictScalars
        (representedAffineCommRingCatHom B S hS g).hom).mapDerivedCategorySingleFunctor 0).app
          _).symm) ≪≫
    @asIso _ _ _ _ (representedAffineTransportUnit B S hS g _) hT ≪≫ ?_
  exact (derivedModulePushforward B S hS (representedSpaceMap B S hS g)).mapIso
    (representedAffineDerivedAssociatedSingleUnitIso B S hS U' 0)

end Affine

/-! ### Base change of the structure sheaf of an affine object -/

section BaseChange

variable {U' U : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')] {X X' : AlgebraicSpaces B S hS}
  (g : U' ⟶ U) (f : X ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
  (f' : X' ⟶ ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩) (g' : X' ⟶ X)

/-- **`Rg'_*𝒪_{X'}` has finite Tor dimension.**  Let `g : U' ⟶ U` be a morphism of affine
objects with rings `R ⟶ R'`, `f : X ⟶ U` a morphism of algebraic spaces and
`X' = U' ×_U X` with projections `g'`, `f'`.  If `X` and `U'` are Tor independent over `U` and
`R'` has finite Tor dimension over `R`, then `Rg'_*𝒪_{X'}` has finite Tor dimension, for an
arbitrary derived tensor product datum on the small étale site of `X`.

Stacks 08IR at `𝒪_{U'}`, for the transposed square whose top morphism `U' ⟶ U` is affine and
hence quasi-compact and quasi-separated, gives `Lf^*Rg_*𝒪_{U'} ≅ Rg'_*Lf'^*𝒪_{U'} ≅
Rg'_*𝒪_{X'}`; `Rg_*𝒪_{U'}` has finite Tor dimension by
`hasFiniteTorDimension_derivedPushforward_structureDerived_representedSpaceMap`, and `Lf^*`
preserves it by Stacks 08H5. -/
theorem hasFiniteTorDimension_derivedPushforward_structureDerived_of_torIndependent
    (sq : IsPullback g' f' f (representedSpaceMap B S hS g))
    (hTor : TorIndependent X.2 (isAlgebraicSpace_yoneda B S hS U')
      (isAlgebraicSpace_yoneda B S hS U) f.hom (representedSpaceMap B S hS g).hom)
    (hR : HasFiniteTorDimensionRingHom (representedAffineCommRingCatHom B S hS g).hom)
    (T : DerivedTensorProduct (smallEtaleRingedSite B S hS X.1 X.2)) :
    HasFiniteTorDimension T
      ((derivedPushforward (X := smallEtaleRingedTopos B S hS X')
        (Y := smallEtaleRingedTopos B S hS X) (smallEtaleRingedToposHom B S hS g')).obj
          (structureDerived X')) := by
  have hg := isAffineHom_representedSpaceMap B S hS g
  have hbc := isIso_smallEtaleDerivedBaseChangeMap_of_torIndependent B S hS
    (representedSpaceMap B S hS g) f g' f' sq.flip (isQuasiCompact_of_isAffineHom_hom _ hg)
    (isQuasiSeparated_of_isAffineHom_hom _ hg) hTor.symm
    (structureDerived ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩)
    (qcohDerived_singleFunctor_structureModule (X := yoneda.obj U')
      (hX := isAlgebraicSpace_yoneda B S hS U'))
  obtain ⟨a, b, h⟩ :=
    hasFiniteTorDimension_derivedPushforward_structureDerived_representedSpaceMap B S hS g hR
  refine ⟨a, b, (hasTorAmplitude_smallEtaleDerivedModulePullback B S hS f _ T _ a b h).of_iso
    (@asIso _ _ _ _ (smallEtaleDerivedModuleBaseChangeMap B S hS (representedSpaceMap B S hS g) f g'
      f' sq.flip.w (structureDerived ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩)) hbc ≪≫
    (derivedPushforward (X := smallEtaleRingedTopos B S hS X')
      (Y := smallEtaleRingedTopos B S hS X) (smallEtaleRingedToposHom B S hS g')).mapIso
        (smallEtaleDerivedModulePullbackUnitIso f'))⟩

/-- **`Rg'_*𝒪_{X'}` has finite Tor dimension on the equi-universe model**: the conclusion of
`hasFiniteTorDimension_derivedPushforward_structureDerived_of_torIndependent` read through the
derived equivalence `D(𝒪_X) ≌ D(𝒪_model)`, for an arbitrary derived tensor product datum on
the model. -/
theorem hasFiniteTorDimension_smallEtaleModel_derivedPushforward_structureDerived
    (sq : IsPullback g' f' f (representedSpaceMap B S hS g))
    (hTor : TorIndependent X.2 (isAlgebraicSpace_yoneda B S hS U')
      (isAlgebraicSpace_yoneda B S hS U) f.hom (representedSpaceMap B S hS g).hom)
    (hR : HasFiniteTorDimensionRingHom (representedAffineCommRingCatHom B S hS g).hom)
    (T' : DerivedTensorProduct (smallEtaleModelRingedSite B S hS X.1 X.2)) :
    HasFiniteTorDimension T'
      ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj
        ((derivedPushforward (X := smallEtaleRingedTopos B S hS X')
          (Y := smallEtaleRingedTopos B S hS X) (smallEtaleRingedToposHom B S hS g')).obj
            (structureDerived X'))) :=
  hasFiniteTorDimension_smallEtaleModelDerivedEquivalence_functor_obj B S hS X
    (smallEtaleDerivedTensorProduct B S hS X) T' _
    (hasFiniteTorDimension_derivedPushforward_structureDerived_of_torIndependent B S hS g f f' g'
      sq hTor hR _)

/-- `hasFiniteTorDimension_smallEtaleModel_derivedPushforward_structureDerived` at the canonical
derived tensor product of the equi-universe model. -/
theorem hasFiniteTorDimension_canonical_smallEtaleModel_derivedPushforward_structureDerived
    (sq : IsPullback g' f' f (representedSpaceMap B S hS g))
    (hTor : TorIndependent X.2 (isAlgebraicSpace_yoneda B S hS U')
      (isAlgebraicSpace_yoneda B S hS U) f.hom (representedSpaceMap B S hS g).hom)
    (hR : HasFiniteTorDimensionRingHom (representedAffineCommRingCatHom B S hS g).hom) :
    HasFiniteTorDimension
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct
        (smallEtaleModelRingedSite B S hS X.1 X.2))
      ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj
        ((derivedPushforward (X := smallEtaleRingedTopos B S hS X')
          (Y := smallEtaleRingedTopos B S hS X) (smallEtaleRingedToposHom B S hS g')).obj
            (structureDerived X'))) :=
  hasFiniteTorDimension_smallEtaleModel_derivedPushforward_structureDerived B S hS g f f' g' sq
    hTor hR _

end BaseChange

end AlgebraicGeometry.Space

end
