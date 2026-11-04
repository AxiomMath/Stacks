module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.GlobalDerivedHomBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedSheafHomQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedTensorHomDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleLeftTensorHomDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModelPseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePushforwardStructureFiniteTorDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFamiliesForget
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorHomDiagonalLeftTensor

/-!
# Stacks 0E4S: derived Hom commutes with Tor independent affine base change

Let `g : S' ⟶ S` be a morphism of affine schemes, `S = Spec R`, `S' = Spec R'`, and let
`X' = X ×_S S'` for a quasi-compact and quasi-separated algebraic space `X` over `S` Tor
independent of `S'`. For `M`, `K ∈ D(𝒪_X)` the canonical map

`RHom_X(M, K) ⊗^L_R R' ⟶ RHom_{X'}(L(g')^*M, L(g')^*K)`

of `AlgebraicGeometry.Space.globalDerivedHomBaseChangeMap` is an isomorphism when (1) `M` is
perfect and `K ∈ D_QCoh(𝒪_X)`, or (2) `M` is pseudo-coherent, `K ∈ D^+_QCoh(𝒪_X)` and `R'` has
finite Tor dimension over `R`. The proof is the one of the source: `R𝓗om(M, K) ∈ D_QCoh` by
Stacks 0A8A; the map is `RΓ(X', -)` of the map of Stacks 08JF after the base change of `RΓ`
(Stacks 08IR), `R(g')_*` of which is, by Stacks 08IJ and the compatibility of Stacks 07A4 with the
associators, the tensor–Hom diagonal at `R(g')_*𝒪_{X'}`; that diagonal is invertible by
Stacks 0E4Q, in case (2) because `R(g')_*𝒪_{X'} = Lf^*g_*𝒪_{S'}` has finite Tor dimension
(Stacks 08IR, 08E9, 08HF, 08H5).

## Main results

* `AlgebraicGeometry.Space.isIso_globalDerivedHomBaseChangeMap_of_isPerfect`: Stacks 0E4S (1).
* `AlgebraicGeometry.Space.isIso_globalDerivedHomBaseChangeMap_of_isPseudoCoherent`:
  Stacks 0E4S (2).

## References

* [Stacks Project, Tag 0E4S](https://stacks.math.columbia.edu/tag/0E4S)
* [Stacks Project, Tag 0E4Q](https://stacks.math.columbia.edu/tag/0E4Q)
* [Stacks Project, Tag 0A8A](https://stacks.math.columbia.edu/tag/0A8A)
-/

/- Instances that come into scope here only through the base versions of imported modules,
and that would change the elaboration below (universe joins, the small model of `D(R)`). -/
attribute [-instance] SheafOfModules.hasBinBiprod

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedPushforward (derivedPushforward)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {U' U : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]

variable {X X' : AlgebraicSpaces B S hS} (g : U' ⟶ U)
  (f : X ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
  (f' : X' ⟶ ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩) (g' : X' ⟶ X)

/-- **The base change `g'` of a morphism of affine schemes is quasi-compact and
quasi-separated.** -/
theorem isQuasiCompact_isQuasiSeparated_of_isPullback_affine
    (sq : IsPullback g' f' f (representedSpaceMap B S hS g)) :
    IsQuasiCompact B S hS g'.hom ∧ IsQuasiSeparated B S hS g'.hom := by
  have sqh := AlgebraicSpaces.isPullback_hom B S hS sq
  have hgqc : IsQuasiCompact B S hS (representedSpaceMap B S hS g).hom :=
    isQuasiCompact_yoneda_map B S hS g inferInstance
  have hgqs : IsQuasiSeparated B S hS (representedSpaceMap B S hS g).hom :=
    isQuasiSeparated_of_isSeparated B S hS ((isSeparated_yoneda_map_iff B S hS g).2
      (_root_.AlgebraicGeometry.IsSeparated.of_isAffineHom _))
  exact ⟨isQuasiCompact_of_isPullback B S hS sqh.flip hgqc,
    isQuasiSeparated_of_isPullback B S hS sqh.flip hgqs⟩

/-- **Stacks 0E4S, case (1).** Let `g : S' ⟶ S` be a morphism of affine schemes, `R = Γ(S, 𝒪)`,
`R' = Γ(S', 𝒪)`, and let `X' = X ×_S S'` for `f : X ⟶ S` quasi-compact and quasi-separated with
`X` and `S'` Tor independent over `S`. For `M ∈ D(𝒪_X)` perfect and `K ∈ D_QCoh(𝒪_X)` the
canonical map `RHom_X(M, K) ⊗^L_R R' ⟶ RHom_{X'}(L(g')^*M, L(g')^*K)` is an isomorphism. -/
@[stacks 0E4S "case (1): M perfect, K in D_QCoh"]
theorem isIso_globalDerivedHomBaseChangeMap_of_isPerfect
    (sq : IsPullback g' f' f (representedSpaceMap B S hS g))
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hTor : TorIndependent X.2 (isAlgebraicSpace_yoneda B S hS U')
      (isAlgebraicSpace_yoneda B S hS U) f.hom (representedSpaceMap B S hS g).hom)
    (M K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hM : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) M)
    (hK : QcohDerived B S hS X K) :
    IsIso (globalDerivedHomBaseChangeMap B S hS g f f' g' sq.w M K) := by
  have hH := qcohDerived_smallEtaleDerivedSheafHom X M K (Or.inr ⟨hM, hK⟩)
  obtain ⟨hg'qc, hg'qs⟩ := isQuasiCompact_isQuasiSeparated_of_isPullback_affine B S hS g f f' g' sq
  refine isIso_globalDerivedHomBaseChangeMap_of_isIso_derivedPushforward B S hS g f f' g' sq hfqc
    hfqs hTor M K hH ?_
  refine isIso_derivedPushforward_map_smallEtaleDerivedPullbackSheafHomMap g' hg'qc hg'qs M K hH hK
    (isIso_leftTensorHomDiagonal_of_model X _ M K ?_)
  rw [← RingedSite.derivedTensorHomDiagonal_eq_leftTensorHomDiagonal]
  exact isIso_derivedTensorHomDiagonal_of_isPerfect B S hS X.1 X.2 _ _ _
    (isPerfect_smallEtaleModelDerivedEquivalence_functor_obj B S hS X M hM)

/-- **Stacks 0E4S, case (2).** Let `g : S' ⟶ S` be a morphism of affine schemes, `R = Γ(S, 𝒪)`,
`R' = Γ(S', 𝒪)`, and let `X' = X ×_S S'` for `f : X ⟶ S` quasi-compact and quasi-separated with
`X` and `S'` Tor independent over `S`. If `R'` has finite Tor dimension over `R`, then for
`M ∈ D(𝒪_X)` pseudo-coherent and `K ∈ D^+_QCoh(𝒪_X)` the canonical map
`RHom_X(M, K) ⊗^L_R R' ⟶ RHom_{X'}(L(g')^*M, L(g')^*K)` is an isomorphism. -/
@[stacks 0E4S "case (2): M pseudo-coherent, K in D^+_QCoh, R' of finite tor dimension over R"]
theorem isIso_globalDerivedHomBaseChangeMap_of_isPseudoCoherent
    (sq : IsPullback g' f' f (representedSpaceMap B S hS g))
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hTor : TorIndependent X.2 (isAlgebraicSpace_yoneda B S hS U')
      (isAlgebraicSpace_yoneda B S hS U) f.hom (representedSpaceMap B S hS g).hom)
    (hR' : AlgebraicGeometry.HasFiniteTorDimensionRingHom
      (representedAffineCommRingCatHom B S hS g).hom)
    (M K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hM : RingedSite.IsPseudoCoherent (smallEtaleRingedSite B S hS X.1 X.2) M)
    (hK : DerivedCategoryB.derivedCategoryBPlus
          (A := SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
          (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) K) :
    IsIso (globalDerivedHomBaseChangeMap B S hS g f f' g' sq.w M K) := by
  have hH := qcohDerived_smallEtaleDerivedSheafHom X M K (Or.inl ⟨hM, hK⟩)
  obtain ⟨hg'qc, hg'qs⟩ := isQuasiCompact_isQuasiSeparated_of_isPullback_affine B S hS g f f' g' sq
  refine isIso_globalDerivedHomBaseChangeMap_of_isIso_derivedPushforward B S hS g f f' g' sq hfqc
    hfqs hTor M K hH ?_
  refine isIso_derivedPushforward_map_smallEtaleDerivedPullbackSheafHomMap g' hg'qc hg'qs M K hH
    hK.2 (isIso_leftTensorHomDiagonal_of_model X _ M K ?_)
  rw [← RingedSite.derivedTensorHomDiagonal_eq_leftTensorHomDiagonal]
  exact isIso_derivedTensorHomDiagonal_of_isPseudoCoherent B S hS X.1 X.2 _ _ _
    (isPseudoCoherent_smallEtaleModelDerivedEquivalence_functor_obj B S hS X M hM)
    (isBoundedBelow_smallEtaleModelDerivedEquivalence_functor_obj B S hS X K hK.1)
    (hasFiniteTorDimension_canonical_smallEtaleModel_derivedPushforward_structureDerived B S hS
      g f f' g' sq hTor hR')

end AlgebraicGeometry.Space

end

