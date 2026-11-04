module

public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.QcqsCompactGeneration
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityBaseChangeMap
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityPullbackComparisonCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityPushforwardTraceCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleDerivedPullbackSheafHomMap
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackTensorComp
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.GlobalDerivedHomBaseChangeIso
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPushforwardGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackTensorCoherence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CompactObjects.RightAdjointCoproducts
public import StacksFrontier.CategoryTheory.Triangulated.CompactGenerationAdjunction
public import StacksFrontier.CategoryTheory.Adjunction.InternalHomTraceBaseChange
public meta import StacksFrontier.Tactic.HEqCongr

/-!
# The base change map of the right adjoint of `Rf_*` over an affine base (Stacks 0E5I)

Consider a cartesian square of quasi-compact and quasi-separated algebraic spaces

```
X' --g'--> X
|f'        |f
Y' --g---> Y
```

with `X` and `Y'` Tor independent over `Y`, and the base change map
`α_K : L(g')^* a(K) ⟶ a'(Lg^* K)` of Stacks 0E5D. The proof of Stacks 0E5I shows that `α_K` is an
isomorphism by testing it against the generator `L(g')^*M`, for `M` a perfect generator of
`D_QCoh(𝒪_X)`. Here the test is `Rf'_* R𝓗om(L(g')^*M, α_K)`, which is identified with
`Lg^*` of the trace map `Rf_* R𝓗om(M, a(K)) ⟶ R𝓗om(Rf_*M, K)` of Stacks 0E57 followed by the map
`Lg^* R𝓗om(Rf_*M, K) ⟶ R𝓗om(Lg^*Rf_*M, Lg^*K)` of Stacks 08JF
(`CategoryTheory.InternalHomTrace.pushforwardTrace_baseChange`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedPushforward (derivedPushforward)

universe u

/- `SheafOfModules.hasBinBiprod`, imported on the base, makes instance search for the binary
biproducts of these categories of modules stall on a universe constraint. -/
attribute [-instance] SheafOfModules.hasBinBiprod

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits
attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (hZ : B.Contains (⊤_ Scheme.{u}))


/-- **`Rf_*` reflects isomorphisms of `D_QCoh` for an affine morphism `f`** (Stacks 0E4R): its
cone is sent to zero, hence is zero. -/
theorem reflectsIsomorphisms_quasicoherentDerivedPushforward_of_isAffineHom
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom) (hf : IsAffineHom B S hS f.hom) :
    (quasicoherentDerivedPushforward B S hS f hfqc hfqs).ReflectsIsomorphisms := by
  refine ⟨fun {A A'} φ hφ => ?_⟩
  obtain ⟨Z, g, k, mem⟩ := Pretriangulated.distinguished_cocone_triangle φ
  have hT := (quasicoherentDerivedPushforward B S hS f hfqc hfqs).map_distinguished _ mem
  have h₃ : IsZero ((quasicoherentDerivedPushforward B S hS f hfqc hfqs).obj Z) :=
    (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ hT).2 hφ
  exact (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ mem).1
    ((isZero_quasicoherentDerivedPushforward_obj_iff_of_isAffineHom f hfqc hfqs hf Z).1 h₃)

/-- The map of Stacks 08JF along an affine morphism is invertible once `Rg_*` of it is, as `Rg_*`
reflects isomorphisms of `D_QCoh` (Stacks 0E4R). -/
private theorem isIso_smallEtaleDerivedPullbackSheafHomMap_of_isIso_derivedPushforward_map
    {X X' : AlgebraicSpaces B S hS} (g : X' ⟶ X) (hg : IsAffineHom B S hS g.hom)
    (M K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hH : QcohDerived B S hS X (((smallEtaleDerivedSheafHom B S hS X).obj (op M)).obj K))
    (ht : QcohDerived B S hS X' (((smallEtaleDerivedSheafHom B S hS X').obj
      (op ((smallEtaleDerivedModulePullback B S hS g).obj M))).obj
      ((smallEtaleDerivedModulePullback B S hS g).obj K)))
    (h : IsIso ((derivedPushforward (X := smallEtaleRingedTopos B S hS X')
      (Y := smallEtaleRingedTopos B S hS X) (smallEtaleRingedToposHom B S hS g)).map
        (smallEtaleDerivedPullbackSheafHomMap g M K))) :
    IsIso (smallEtaleDerivedPullbackSheafHomMap g M K) := by
  have hgqc := isQuasiCompact_of_isAffineHom_hom g hg
  have hgqs := isQuasiSeparated_of_isAffineHom_hom g hg
  have hs : QcohDerived B S hS X' ((smallEtaleDerivedModulePullback B S hS g).obj
      (((smallEtaleDerivedSheafHom B S hS X).obj (op M)).obj K)) :=
    derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ g _ hH
  let φ : (⟨_, hs⟩ : QuasicoherentDerivedCategory.{u, u} B S hS X'.1 X'.2) ⟶ ⟨_, ht⟩ :=
    ObjectProperty.homMk (smallEtaleDerivedPullbackSheafHomMap g M K)
  have : IsIso ((QcohDerived B S hS X).ι.map
      ((quasicoherentDerivedPushforward B S hS g hgqc hgqs).map φ)) := h
  have := isIso_of_reflects_iso ((quasicoherentDerivedPushforward B S hS g hgqc hgqs).map φ)
    (QcohDerived B S hS X).ι
  have := reflectsIsomorphisms_quasicoherentDerivedPushforward_of_isAffineHom g hgqc hgqs hg
  have := isIso_of_reflects_iso φ (quasicoherentDerivedPushforward B S hS g hgqc hgqs)
  exact (inferInstance : IsIso ((QcohDerived B S hS X').ι.map φ))

/-- **The map of Stacks 08JF along an affine morphism is invertible at a perfect object.** For
`g : X' ⟶ X` affine, `M` perfect and `K ∈ D_QCoh(𝒪_X)`, the map
`Lg^*R𝓗om(M, K) ⟶ R𝓗om(Lg^*M, Lg^*K)` is an isomorphism: both sides lie in `D_QCoh(𝒪_{X'})`,
`Rg_*` of the map is invertible (Stacks 0E4Q, as in the proof of Stacks 0E4S) and `Rg_*` reflects
isomorphisms of `D_QCoh` (Stacks 0E4R). -/
theorem isIso_smallEtaleDerivedPullbackSheafHomMap_of_isAffineHom {X X' : AlgebraicSpaces B S hS}
    (g : X' ⟶ X) (hg : IsAffineHom B S hS g.hom)
    (M K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hM : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) M)
    (hK : QcohDerived B S hS X K) :
    IsIso (smallEtaleDerivedPullbackSheafHomMap g M K) := by
  have hgqc := isQuasiCompact_of_isAffineHom_hom g hg
  have hgqs := isQuasiSeparated_of_isAffineHom_hom g hg
  have hH := qcohDerived_smallEtaleDerivedSheafHom X M K (Or.inr ⟨hM, hK⟩)
  have h := isIso_derivedPushforward_map_smallEtaleDerivedPullbackSheafHomMap g hgqc hgqs M K hH hK
    (isIso_leftTensorHomDiagonal_of_model X _ M K (by
      rw [← RingedSite.derivedTensorHomDiagonal_eq_leftTensorHomDiagonal]
      exact isIso_derivedTensorHomDiagonal_of_isPerfect B S hS X.1 X.2 _ _ _
        (isPerfect_smallEtaleModelDerivedEquivalence_functor_obj B S hS X M hM)))
  have ht : QcohDerived B S hS X' (((smallEtaleDerivedSheafHom B S hS X').obj
      (op ((smallEtaleDerivedModulePullback B S hS g).obj M))).obj
      ((smallEtaleDerivedModulePullback B S hS g).obj K)) :=
    qcohDerived_smallEtaleDerivedSheafHom X' _ _
      (Or.inr ⟨isPerfect_smallEtaleDerivedModulePullback g M hM,
        derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ g K hK⟩)
  exact isIso_smallEtaleDerivedPullbackSheafHomMap_of_isIso_derivedPushforward_map g hg M K hH ht h

/-- **The map of Stacks 08JF along an affine morphism of finite Tor dimension is invertible at a
pseudo-coherent object and a bounded below one.** For `g : X' ⟶ X` affine with `Rg_*𝒪_{X'}` of
finite Tor dimension, `M` pseudo-coherent, `K ∈ D^+_QCoh(𝒪_X)` and `Lg^*K` bounded below, the map
`Lg^*R𝓗om(M, K) ⟶ R𝓗om(Lg^*M, Lg^*K)` is an isomorphism (Stacks 0E4Q (3) after `Rg_*`, and
Stacks 0E4R). -/
theorem isIso_smallEtaleDerivedPullbackSheafHomMap_of_isAffineHom_of_isPseudoCoherent
    {X X' : AlgebraicSpaces B S hS} (g : X' ⟶ X) (hg : IsAffineHom B S hS g.hom)
    (M K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hM : RingedSite.IsPseudoCoherent (smallEtaleRingedSite B S hS X.1 X.2) M)
    (hK : DerivedCategoryB.derivedCategoryBPlus
          (A := SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
          (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) K)
    (hgK : DerivedCategoryB.IsBoundedBelow ((smallEtaleDerivedModulePullback B S hS g).obj K))
    (hfin : Stacks.SheafOfModules.DerivedTensorProduct.HasFiniteTorDimension
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct
        (smallEtaleModelRingedSite B S hS X.1 X.2))
      ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj
        ((derivedPushforward (X := smallEtaleRingedTopos B S hS X')
          (Y := smallEtaleRingedTopos B S hS X) (smallEtaleRingedToposHom B S hS g)).obj
            (structureDerived X')))) :
    IsIso (smallEtaleDerivedPullbackSheafHomMap g M K) := by
  have hgqc := isQuasiCompact_of_isAffineHom_hom g hg
  have hgqs := isQuasiSeparated_of_isAffineHom_hom g hg
  have hH := qcohDerived_smallEtaleDerivedSheafHom X M K (Or.inl ⟨hM, hK⟩)
  have h := isIso_derivedPushforward_map_smallEtaleDerivedPullbackSheafHomMap g hgqc hgqs M K hH
    hK.2 (isIso_leftTensorHomDiagonal_of_model X _ M K (by
      rw [← RingedSite.derivedTensorHomDiagonal_eq_leftTensorHomDiagonal]
      exact isIso_derivedTensorHomDiagonal_of_isPseudoCoherent B S hS X.1 X.2 _ _ _
        (isPseudoCoherent_smallEtaleModelDerivedEquivalence_functor_obj B S hS X M hM)
        (isBoundedBelow_smallEtaleModelDerivedEquivalence_functor_obj B S hS X K hK.1) hfin))
  have ht : QcohDerived B S hS X' (((smallEtaleDerivedSheafHom B S hS X').obj
      (op ((smallEtaleDerivedModulePullback B S hS g).obj M))).obj
      ((smallEtaleDerivedModulePullback B S hS g).obj K)) :=
    qcohDerived_smallEtaleDerivedSheafHom X' _ _
      (Or.inl ⟨isPseudoCoherent_smallEtaleDerivedModulePullback g M hM,
        ⟨hgK, derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ g K hK.2⟩⟩)
  exact isIso_smallEtaleDerivedPullbackSheafHomMap_of_isIso_derivedPushforward_map g hg M K hH ht h

section Square

variable {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
  {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
  (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
  (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
  (hY'qc : IsQuasiCompactSpace B S hS Y'.1) (hY'qs : IsAbsolutelyQuasiSeparated B S hS hZ Y'.1)
  (hTor : TorIndependent X.2 Y'.2 Y.2 f.hom g.hom)

/-- The map of Stacks 08JF on algebraic spaces is the abstract pullback map of internal Homs. -/
theorem smallEtaleDerivedPullbackSheafHomMap_eq {X X' : AlgebraicSpaces B S hS} (g : X' ⟶ X)
    (M K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    smallEtaleDerivedPullbackSheafHomMap g M K =
      PullbackInternalHom.pullbackHomMap (smallEtaleDerivedTensor B S hS X)
        (smallEtaleDerivedTensor B S hS X') (smallEtaleDerivedPullbackTensorIso g)
        (smallEtaleDerivedSheafHom B S hS X) (smallEtaleDerivedSheafHom B S hS X')
        (smallEtaleDerivedTensorSheafHomAdjunction B S hS X)
        (smallEtaleDerivedTensorSheafHomAdjunction B S hS X') M K := by
  rw [smallEtaleDerivedPullbackSheafHomMap_eq_homEquiv_counit]
  unfold PullbackInternalHom.pullbackHomMap
  congr 1

/-- **The trace map of Stacks 0E57 under base change.** `Rf'_*` of the map of Stacks 08JF
followed by `R𝓗om(L(g')^*M, α_K)` and the trace map of `f'`, after the base change map and read in
`R𝓗om(Lg^*Rf_*M, Lg^*K)`, is `Lg^*` of the trace map of `f` followed by the map of Stacks 08JF. -/
theorem smallEtalePushforwardTrace_baseChange
    (M : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2)
    [IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' sq.w M.obj)] :
    Stacks.CategoryTheory.BaseChange.map (smallEtaleDerivedModuleAdjunction B S hS f)
        (smallEtaleDerivedModuleAdjunction B S hS f')
        (smallEtaleDerivedModulePullbackCompIso B S hS f' g)
        (smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' sq.w)
        (((smallEtaleDerivedSheafHom B S hS X).obj (op M.obj)).obj
          ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj K).obj) ≫
      (derivedModulePushforward B S hS f').map
        (PullbackInternalHom.pullbackHomMap (smallEtaleDerivedTensor B S hS X)
            (smallEtaleDerivedTensor B S hS X') (smallEtaleDerivedPullbackTensorIso g')
            (smallEtaleDerivedSheafHom B S hS X) (smallEtaleDerivedSheafHom B S hS X')
            (smallEtaleDerivedTensorSheafHomAdjunction B S hS X)
            (smallEtaleDerivedTensorSheafHomAdjunction B S hS X') M.obj
            ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj K).obj) ≫
      (derivedModulePushforward B S hS f').map
          (((smallEtaleDerivedSheafHom B S hS X').obj
            (op ((smallEtaleDerivedModulePullback B S hS g').obj M.obj))).map
            (((quasicoherentDerivedRightAdjointBaseChangeMap hZ sq hXqc hXqs hYqs hY'qc hY'qs
              hTor).app K).hom : (smallEtaleDerivedModulePullback B S hS g').obj
                ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj K).obj ⟶ _)) ≫
      InternalHomTrace.pushforwardTrace (smallEtaleDerivedModuleAdjunction B S hS f')
        (smallEtaleDerivedTensor B S hS X') (smallEtaleDerivedTensor B S hS Y')
        (smallEtaleDerivedPullbackTensorIso f').hom (smallEtaleDerivedSheafHom B S hS X')
        (smallEtaleDerivedSheafHom B S hS Y') (smallEtaleDerivedTensorSheafHomAdjunction B S hS X')
        (smallEtaleDerivedTensorSheafHomAdjunction B S hS Y')
        ((smallEtaleDerivedModulePullback B S hS g').obj M.obj)
        (((squareAdjF' hZ sq hXqc hXqs hYqs hY'qc hY'qs).counit.app
          ((quasicoherentDerivedModulePullback g).obj K)).hom :
            _ ⟶ (smallEtaleDerivedModulePullback B S hS g).obj K.obj) ≫
      (InternalHomTrace.internalHomPrecompIso (smallEtaleDerivedTensor B S hS Y')
        (smallEtaleDerivedSheafHom B S hS Y') (smallEtaleDerivedTensorSheafHomAdjunction B S hS Y')
        (asIso (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' sq.w M.obj))).hom.app
          ((smallEtaleDerivedModulePullback B S hS g).obj K.obj) =
      (smallEtaleDerivedModulePullback B S hS g).map
          (InternalHomTrace.pushforwardTrace (smallEtaleDerivedModuleAdjunction B S hS f)
            (smallEtaleDerivedTensor B S hS X) (smallEtaleDerivedTensor B S hS Y)
            (smallEtaleDerivedPullbackTensorIso f).hom (smallEtaleDerivedSheafHom B S hS X)
            (smallEtaleDerivedSheafHom B S hS Y)
            (smallEtaleDerivedTensorSheafHomAdjunction B S hS X)
            (smallEtaleDerivedTensorSheafHomAdjunction B S hS Y) M.obj
            ((squareAdjF hZ hXqc hXqs hYqs).counit.app K).hom) ≫
        PullbackInternalHom.pullbackHomMap (smallEtaleDerivedTensor B S hS Y)
          (smallEtaleDerivedTensor B S hS Y') (smallEtaleDerivedPullbackTensorIso g)
          (smallEtaleDerivedSheafHom B S hS Y) (smallEtaleDerivedSheafHom B S hS Y')
          (smallEtaleDerivedTensorSheafHomAdjunction B S hS Y)
          (smallEtaleDerivedTensorSheafHomAdjunction B S hS Y')
          ((derivedModulePushforward B S hS f).obj M.obj) K.obj := by
  have hL := congrArg InducedCategory.Hom.hom
    (quasicoherentDerivedRightAdjointBaseChangeMap_trace hZ sq hXqc hXqs hYqs hY'qc hY'qs hTor K)
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom] at hL
  have h := InternalHomTrace.pushforwardTrace_baseChange
    (smallEtaleDerivedModuleAdjunction B S hS f) (smallEtaleDerivedModuleAdjunction B S hS f')
    (smallEtaleDerivedModulePullbackCompIso B S hS f' g)
    (smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' sq.w)
    (smallEtaleDerivedTensor B S hS Y) (smallEtaleDerivedTensor B S hS X)
    (smallEtaleDerivedTensor B S hS Y') (smallEtaleDerivedTensor B S hS X')
    (smallEtaleDerivedPullbackTensorIso f).hom (smallEtaleDerivedPullbackTensorIso f').hom
    (smallEtaleDerivedPullbackTensorIso g) (smallEtaleDerivedPullbackTensorIso g')
    (smallEtaleDerivedSheafHom B S hS Y) (smallEtaleDerivedSheafHom B S hS X)
    (smallEtaleDerivedSheafHom B S hS Y') (smallEtaleDerivedSheafHom B S hS X')
    (smallEtaleDerivedTensorSheafHomAdjunction B S hS Y)
    (smallEtaleDerivedTensorSheafHomAdjunction B S hS X)
    (smallEtaleDerivedTensorSheafHomAdjunction B S hS Y')
    (smallEtaleDerivedTensorSheafHomAdjunction B S hS X') M.obj
    ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj K).obj
    ((squareAdjF hZ hXqc hXqs hYqs).counit.app K).hom
    ((quasicoherentDerivedRightAdjointBaseChangeMap hZ sq hXqc hXqs hYqs hY'qc hY'qs
      hTor).app K).hom
    ((squareAdjF' hZ sq hXqc hXqs hYqs hY'qc hY'qs).counit.app
      ((quasicoherentDerivedModulePullback g).obj K)).hom hL
    (asIso (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' sq.w M.obj)) rfl
    (tensorComparisonCompatible_smallEtaleDerivedPullbackTensorIso f g f' g' sq.w _ _)
  refine Eq.trans ?_ (h.trans ?_)
  · exact eq_of_heq (by heq_congr)
  · rfl

end Square

end AlgebraicGeometry.Space

end
