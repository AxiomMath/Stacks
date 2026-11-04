module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorHomDiagonalLeftTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorHomDiagonalLeftTensorSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartwiseBaseChangeTensorRight
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.AssociativityGeneral
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleKFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityRightAdjointBaseChangeAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeSheafHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeSheafHomSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTensor
public import StacksFrontier.CategoryTheory.Adjunction.PullbackInternalHomPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedSheafHomQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedTensorHomDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.DerivedPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineBaseChangeCompCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineBaseChangeCompCriterionSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineDerivedPullbackBoundedBelow
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChangeCompCondition
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChangeCompConditionSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChangeCompKunneth
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChangeCompKunnethSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleLeftTensorHomDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleLeftTensorHomDiagonalSupplement
public import StacksFrontier.CategoryTheory.Adjunction.PullbackInternalHomTensorDiagonal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.AssociativityGeneral

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedBaseChangeSupplement
/-!
# Condition (2) of Stacks 0DKG for `R𝓗om` out of a pseudo-coherent object, on an affine chart

Let `U' = U ×_V V'` be a cartesian square of affine objects of the big fppf site, with
`R = Γ(V) ⟶ R' = Γ(V')` of finite Tor dimension. For `P` pseudo-coherent on `U`,
`M ∈ D^+_QCoh(𝒪_U)`, `M' ∈ D_QCoh(𝒪_{U'})` and `φ₀ : L(g')^*M ⟶ M'`, if the composite
`RΓ(U, M) ⊗ᴸ_R R' ⟶ RΓ(U', M')` of Stacks 065Z with `φ₀` is invertible, so is the composite for
`R𝓗om(P, M)`, `R𝓗om(L(g')^*P, M')` and the map of Stacks 08JF followed by
`R𝓗om(L(g')^*P, φ₀)`. This is the chart step of Stacks 0DKI (3), with `g` of finite Tor
dimension.

The proof is the source's, read on sheaves. By the Künneth argument (Stacks 08IR) the condition
is the invertibility of `E ⊗ᴸ Q ⟶ R(g')_*(K' ⊗ᴸ L(f')^*𝒪_{V'})` with `Q = Lf^*Rg_*𝒪_{V'}`.
That map for `R𝓗om(P, M)` is, up to isomorphisms, the tensor–Hom diagonal
`Q ⊗ᴸ R𝓗om(P, M) ⟶ R𝓗om(P, Q ⊗ᴸ M)`, invertible by Stacks 0E4Q since `Q` has finite Tor
dimension, followed by `R𝓗om(P, -)` of the map for `M`
(`CategoryTheory.PullbackInternalHom.isIso_tensorBaseChangeComp_pullbackHomMap`). The hypothesis
also forces `M'` to be bounded below, so that `R𝓗om(L(g')^*P, M')` has quasi-coherent cohomology.

## Main results

All in the namespace `AlgebraicGeometry.Space`.

* `isIso_smallEtaleTensorBaseChangeCompMap_sheafHom`: the Künneth form of condition (2) of
  Stacks 0DKG passes to `R𝓗om(P, -)`.
* `isBoundedBelow_of_isIso_smallEtaleTensorBaseChangeCompMap_representedAffine`: on affines, the
  Künneth form of the condition forces the second object to be bounded below.
* `isIso_representedAffineSectionsBaseChangeComp_sheafHom_of_isPseudoCoherent`: condition (2) of
  Stacks 0DKG passes to `R𝓗om` out of a pseudo-coherent object, on an affine chart.

## References

* [Stacks Project, Tag 0DKI](https://stacks.math.columbia.edu/tag/0DKI)
* [Stacks Project, Tag 0E4Q](https://stacks.math.columbia.edu/tag/0E4Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Prod
open Stacks.Cohomology.DerivedPushforward (derivedPushforward)



universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

/- The standard model of the derived category: the derived functors this file uses (derived
pullback, pushforward, tensor product and internal Hom on ringed sites and topoi) are stated
on it, so the statements here must be too. -/
attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective
  isGrothendieckAbelian_smallEtaleRingedToposModules

section General

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)

/-- **The Künneth form of condition (2) of Stacks 0DKG passes to `R𝓗om(P, -)`.** For a
commutative square of algebraic spaces, `P, M ∈ D(𝒪_X)`, `K' ∈ D(𝒪_{X'})` and
`φ₀ : L(g')^*M ⟶ K'`: if the map `M ⊗ᴸ Lf^*Rg_*𝒪_{Y'} ⟶ R(g')_*(K' ⊗ᴸ L(f')^*𝒪_{Y'})` attached
to `φ₀` is invertible and the tensor–Hom diagonal at `Lf^*Rg_*𝒪_{Y'}` is invertible at `(P, M)`,
the map attached to `R𝓗om(P, M)`, `R𝓗om(L(g')^*P, K')` and Stacks 08JF followed by
`R𝓗om(L(g')^*P, φ₀)` is invertible. -/
theorem isIso_smallEtaleTensorBaseChangeCompMap_sheafHom (w : g' ≫ f = f' ≫ g)
    (P M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (φ₀ : (smallEtaleDerivedModulePullback B S hS g').obj M ⟶ K')
    (hδ : IsIso (CategoryTheory.PullbackInternalHom.leftTensorHomDiagonal
      (smallEtaleDerivedTensor B S hS X) (smallEtaleDerivedSheafHom B S hS X)
      (smallEtaleDerivedTensorSheafHomAdjunction B S hS X) (smallEtaleDerivedTensorAssociator X)
      ((smallEtaleDerivedModulePullback B S hS f).obj
        ((derivedPushforward (X := smallEtaleRingedTopos B S hS Y')
          (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS g)).obj
            (structureDerived Y'))) P M))
    (h : IsIso (smallEtaleTensorBaseChangeCompMap B S hS f g f' g' w M K' φ₀)) :
    IsIso (smallEtaleTensorBaseChangeCompMap B S hS f g f' g' w
      (((smallEtaleDerivedSheafHom B S hS X).obj (op P)).obj M)
      (((smallEtaleDerivedSheafHom B S hS X').obj
        (op ((smallEtaleDerivedModulePullback B S hS g').obj P))).obj K')
      (smallEtaleDerivedPullbackSheafHomMap g' P M ≫
        ((smallEtaleDerivedSheafHom B S hS X').obj
          (op ((smallEtaleDerivedModulePullback B S hS g').obj P))).map φ₀)) := by
  unfold smallEtaleTensorBaseChangeCompMap
    Stacks.CategoryTheory.KunnethBaseChange.tensorBaseChangeCompMap at h ⊢
  rw [smallEtaleDerivedPullbackSheafHomMap_eq]
  exact CategoryTheory.PullbackInternalHom.isIso_tensorBaseChangeComp_pullbackHomMap
    (smallEtaleDerivedAdjunction B S hS g') (smallEtaleDerivedTensor B S hS X)
    (smallEtaleDerivedTensor B S hS X') (smallEtaleDerivedPullbackTensorIso g')
    (smallEtaleDerivedSheafHom B S hS X) (smallEtaleDerivedSheafHom B S hS X')
    (smallEtaleDerivedTensorSheafHomAdjunction B S hS X)
    (smallEtaleDerivedTensorSheafHomAdjunction B S hS X')
    (smallEtaleDerivedTensorAssociator X) (smallEtaleDerivedTensorAssociator X')
    (fun A A' => (smallEtaleDerivedTensorProduct B S hS X).braiding A A')
    (fun A A' => (smallEtaleDerivedTensorProduct B S hS X').braiding A A')
    (smallEtaleDerivedPullbackTensorIso_associativity g')
    (fun a A' A'' =>
      (smallEtaleDerivedTensorProduct B S hS X').associatorGeneral_naturality_left a A' A'')
    (fun A _ _ b A'' =>
      (smallEtaleDerivedTensorProduct B S hS X').associatorGeneral_naturality_middle A b A'')
    (fun a A' A'' =>
      (smallEtaleDerivedTensorProduct B S hS X).associatorGeneral_naturality_left a A' A'')
    (smallEtaleDerivedPullbackTensorIso_braiding g')
    (fun a b => (smallEtaleDerivedTensorProduct B S hS X).braiding_hom_naturality a b)
    (fun a b => (smallEtaleDerivedTensorProduct B S hS X').braiding_hom_naturality a b)
    (structureDerived X') (smallEtaleDerivedTensorLeftUnitor X')
    (fun A A' => (smallEtaleDerivedTensorProduct B S hS X').leftUnitor_tensor A A')
    (smallEtaleDerivedModulePullbackUnitIso f') _ P M φ₀ hδ h

end General

section Affine

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U V U' V' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V')]
  (f₀ : U ⟶ V) (g₀ : V' ⟶ V) (f₀' : U' ⟶ V') (g₀' : U' ⟶ U) (w₀ : g₀' ≫ f₀ = f₀' ≫ g₀)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] in
/-- `Lf^*Rg_*𝒪_{V'}` has finite Tor dimension on `U` when `Γ(V) ⟶ Γ(V')` has. -/
theorem hasFiniteTorDimension_smallEtaleDerivedModulePullback_derivedPushforward_representedSpaceMap
    (hfin : HasFiniteTorDimensionRingHom (representedAffineRingCatHom B S hS g₀).hom)
    (T : Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, u + 1}
      (smallEtaleRingedSite B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))) :
    Stacks.SheafOfModules.DerivedTensorProduct.HasFiniteTorDimension.{u + 1, u, u, u + 1} T
      ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS f₀)).obj
        ((derivedModulePushforward B S hS (representedSpaceMap B S hS g₀)).obj
            (structureDerived ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩))) :=
  hasFiniteTorDimension_smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS f₀)
    (smallEtaleDerivedTensorProduct B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩) T _
    (hasFiniteTorDimension_derivedPushforward_structureDerived_representedSpaceMap B S hS g₀ hfin)

/-- `Lf^*Rg_*𝒪_{V'}` has finite Tor dimension on `U`, transported to the model of the derived
category. -/
private theorem hasFiniteTorDimension_model_pullback_pushforward_structureDerived
    {U V V' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V')] (f₀ : U ⟶ V) (g₀ : V' ⟶ V)
    (hfin : HasFiniteTorDimensionRingHom (representedAffineRingCatHom B S hS g₀).hom) :
    Stacks.SheafOfModules.DerivedTensorProduct.HasFiniteTorDimension.{u, u, u, u + 1}
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct
        (smallEtaleModelRingedSite B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)))
      ((smallEtaleModelDerivedEquivalence B S hS
        ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).functor.obj
        ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS f₀)).obj
          ((derivedModulePushforward B S hS (representedSpaceMap B S hS g₀)).obj
            (structureDerived ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩)))) :=
  hasFiniteTorDimension_smallEtaleModelDerivedEquivalence_functor_obj B S hS
    ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ _
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct
      (smallEtaleModelRingedSite B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))) _
    (hasFiniteTorDimension_smallEtaleDerivedModulePullback_derivedPushforward_representedSpaceMap
      B S hS f₀ g₀ hfin
      (smallEtaleDerivedTensorProduct B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩))

/-- **The Künneth form of condition (2) of Stacks 0DKG bounds the second object below.** For a
commutative square of affines with `Γ(V) ⟶ Γ(V')` of finite Tor dimension, `M` bounded below and
quasi-coherent, `M'` quasi-coherent and `φ₀ : L(g')^*M ⟶ M'`, if
`M ⊗ᴸ Lf^*Rg_*𝒪_{V'} ⟶ R(g')_*(M' ⊗ᴸ L(f')^*𝒪_{V'})` is invertible then `M'` is bounded
below. -/
theorem isBoundedBelow_of_isIso_smallEtaleTensorBaseChangeCompMap_representedAffine
    (hfin : HasFiniteTorDimensionRingHom (representedAffineRingCatHom B S hS g₀).hom)
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)))
    (hM : DerivedCategoryB.derivedCategoryBPlus
          (A := SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
            ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩))
          (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
              (isAlgebraicSpace_yoneda B S hS U)).O))) M)
    (M' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩)))
    (hM' : QcohDerived B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩ M')
    (φ₀ : (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).obj M ⟶ M')
    (h : IsIso (smallEtaleTensorBaseChangeCompMap B S hS (representedSpaceMap B S hS f₀)
      (representedSpaceMap B S hS g₀) (representedSpaceMap B S hS f₀')
      (representedSpaceMap B S hS g₀') (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀)
      M M' φ₀)) :
    DerivedCategoryB.IsBoundedBelow M' := by
  have hfinM := hasFiniteTorDimension_model_pullback_pushforward_structureDerived B S hS f₀ g₀ hfin
  have hbM :=
    Stacks.SheafOfModules.DerivedTensorProduct.isBoundedBelow_tensor_of_hasFiniteTorDimension
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct
        (smallEtaleModelRingedSite B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)))
      _ _ hfinM (isBoundedBelow_smallEtaleModelDerivedEquivalence_functor_obj B S hS _ M hM.1)
  have hb := isBoundedBelow_of_isBoundedBelow_smallEtaleModelDerivedEquivalence_functor_obj B S hS
    ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ _ (DerivedCategoryB.isBoundedBelow_of_iso
      ((smallEtaleModelDerivedTensorIso B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).app
        ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS f₀)).obj
          ((derivedModulePushforward B S hS (representedSpaceMap B S hS g₀)).obj
              (structureDerived ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩)), M)).symm hbM)
  have hb' := DerivedCategoryB.isBoundedBelow_of_iso
    ((smallEtaleDerivedTensorProduct B S hS
        ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).braiding _ M ≪≫ @asIso _ _ _ _ _ h) hb
  have hO : QcohDerived B S hS ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩
      (structureDerived ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩) :=
    qcohDerived_singleFunctor_structureModule (X := yoneda.obj V')
      (hX := isAlgebraicSpace_yoneda B S hS V')
  have hT : QcohDerived B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩
      (((smallEtaleDerivedTensor B S hS
          ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩).obj M').obj
        ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS f₀')).obj
          (structureDerived ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩))) :=
    qcohDerived_smallEtaleDerivedTensor _ _ _ hM'
      (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ _ _ hO)
  obtain ⟨n, hn⟩ := hb'
  have hb'' : DerivedCategoryB.IsBoundedBelow
      (((smallEtaleDerivedTensor B S hS
          ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩).obj M').obj
        ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS f₀')).obj
          (structureDerived ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩))) :=
    ⟨n, fun i hi =>
      isZero_homology_of_isZero_homology_derivedModulePushforward_representedSpaceMap B S hS g₀' _
        hT i (hn i hi)⟩
  exact DerivedCategoryB.isBoundedBelow_of_iso
    (((smallEtaleDerivedTensor B S hS
          ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩).obj M').mapIso
        (smallEtaleDerivedModulePullbackUnitIso (representedSpaceMap B S hS f₀')) ≪≫
      (smallEtaleDerivedTensorProduct B S hS
          ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩).braiding M' _ ≪≫
      (smallEtaleDerivedTensorLeftUnitor ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩).app M')
    hb''

/-- **Condition (2) of Stacks 0DKG passes to `R𝓗om` out of a pseudo-coherent object, on an affine
chart** (the chart step of Stacks 0DKI (3), with `g` of finite Tor dimension). Let
`U' = U ×_V V'` be a cartesian square of affine objects with `R = Γ(V) ⟶ R' = Γ(V')` of finite
Tor dimension, `P` pseudo-coherent on `U`, `M ∈ D^+_QCoh(𝒪_U)`, `M' ∈ D_QCoh(𝒪_{U'})` and
`φ₀ : L(g')^*M ⟶ M'`. If `RΓ(U, M) ⊗ᴸ_R R' ⟶ RΓ(U', M')` (Stacks 065Z followed by `φ₀`) is
invertible, so is the same composite for `R𝓗om(P, M)`, `R𝓗om(L(g')^*P, M')` and the map of
Stacks 08JF followed by `R𝓗om(L(g')^*P, φ₀)`. -/
theorem isIso_representedAffineSectionsBaseChangeComp_sheafHom_of_isPseudoCoherent
    (hpb : IsPullback g₀' f₀' f₀ g₀)
    (hfin : HasFiniteTorDimensionRingHom (representedAffineRingCatHom B S hS g₀).hom)
    (P : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)))
    (hP : RingedSite.IsPseudoCoherent
      (smallEtaleRingedSite B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)) P)
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)))
    (hM : DerivedCategoryB.derivedCategoryBPlus
          (A := SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
            ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩))
          (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
              (isAlgebraicSpace_yoneda B S hS U)).O))) M)
    (M' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩)))
    (hM' : QcohDerived B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩ M')
    (φ₀ : (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).obj M ⟶ M')
    (h : IsIso (representedAffineSectionsBaseChangeComp B S hS f₀ g₀ f₀' g₀' w₀ M M' φ₀)) :
    IsIso (representedAffineSectionsBaseChangeComp B S hS f₀ g₀ f₀' g₀' w₀
      (((smallEtaleDerivedSheafHom B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).obj
        (op P)).obj M)
      (((smallEtaleDerivedSheafHom B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩).obj
        (op ((smallEtaleDerivedModulePullback B S hS
          (representedSpaceMap B S hS g₀')).obj P))).obj M')
      (smallEtaleDerivedPullbackSheafHomMap (representedSpaceMap B S hS g₀') P M ≫
        ((smallEtaleDerivedSheafHom B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩).obj
          (op ((smallEtaleDerivedModulePullback B S hS
            (representedSpaceMap B S hS g₀')).obj P))).map
            φ₀)) := by
  have sq := isPullback_representedSpaceMap B S hS hpb
  have hf : IsAffineHom B S hS (representedSpaceMap B S hS f₀).hom :=
    isAffineHom_of_isAffineSpace B S hS _ (isAffineSpace_yoneda B S hS U inferInstance)
      (isAffineSpace_yoneda B S hS V inferInstance)
  have hg : IsAffineHom B S hS (representedSpaceMap B S hS g₀).hom :=
    isAffineHom_of_isAffineSpace B S hS _ (isAffineSpace_yoneda B S hS V' inferInstance)
      (isAffineSpace_yoneda B S hS V inferInstance)
  have hfqc := isQuasiCompact_of_isAffineHom_hom _ hf
  have hfqs := isQuasiSeparated_of_isAffineHom_hom _ hf
  have hgqc := isQuasiCompact_of_isAffineHom_hom _ hg
  have hgqs := isQuasiSeparated_of_isAffineHom_hom _ hg
  have hBC := (isIso_smallEtaleDerivedBaseChangeComp_representedAffine_iff B S hS f₀ g₀ f₀' g₀' w₀
    M hM.2 M' hM' φ₀).2 h
  have hK := isIso_smallEtaleTensorBaseChangeCompMap_of_isIso B S hS _ _ _ _ sq hfqc hfqs hgqc hgqs
    (isAffineSpace_yoneda B S hS U inferInstance) M hM.2 M' hM' φ₀ hBC
  have hM'b := isBoundedBelow_of_isIso_smallEtaleTensorBaseChangeCompMap_representedAffine B S hS
    f₀ g₀ f₀' g₀' w₀ hfin M hM M' hM' φ₀ hK
  have hδ : IsIso (CategoryTheory.PullbackInternalHom.leftTensorHomDiagonal
      (smallEtaleDerivedTensor B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      (smallEtaleDerivedSheafHom B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      (smallEtaleDerivedTensorSheafHomAdjunction B S hS
        ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      (smallEtaleDerivedTensorAssociator ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS f₀)).obj
        ((derivedModulePushforward B S hS (representedSpaceMap B S hS g₀)).obj
            (structureDerived ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩))) P M) :=
    isIso_leftTensorHomDiagonal_of_model _ _ P M (by
      rw [← RingedSite.derivedTensorHomDiagonal_eq_leftTensorHomDiagonal]
      exact isIso_derivedTensorHomDiagonal_of_isPseudoCoherent B S hS _ _ _ _ _
        (isPseudoCoherent_smallEtaleModelDerivedEquivalence_functor_obj B S hS _ P hP)
        (isBoundedBelow_smallEtaleModelDerivedEquivalence_functor_obj B S hS _ M hM.1)
        (hasFiniteTorDimension_model_pullback_pushforward_structureDerived B S hS f₀ g₀ hfin))
  have hK₂ := isIso_smallEtaleTensorBaseChangeCompMap_sheafHom _ _ _ _ sq.w P M M' φ₀ hδ hK
  have hH := qcohDerived_smallEtaleDerivedSheafHom _ P M (Or.inl ⟨hP, hM⟩)
  have hH' := qcohDerived_smallEtaleDerivedSheafHom
    ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩
    ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).obj P) M'
    (Or.inl ⟨isPseudoCoherent_smallEtaleDerivedModulePullback (representedSpaceMap B S hS g₀') P hP,
      ⟨hM'b, hM'⟩⟩)
  have hBC₂ := isIso_smallEtaleDerivedBaseChangeComp_of_isIso_tensorBaseChangeCompMap B S hS _ _ _ _
    sq hfqc hfqs hgqc hgqs (isAffineSpace_yoneda B S hS V' inferInstance) _ hH _ hH' _ hK₂
  exact (isIso_smallEtaleDerivedBaseChangeComp_representedAffine_iff B S hS f₀ g₀ f₀' g₀' w₀ _ hH
    _ hH' _).1 hBC₂

end Affine

end AlgebraicGeometry.Space

end
