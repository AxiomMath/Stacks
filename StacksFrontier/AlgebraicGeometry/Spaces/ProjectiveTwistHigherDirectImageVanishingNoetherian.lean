module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.BaseChange
public import StacksFrontier.AlgebraicGeometry.AmplePullback.Basic
public import StacksFrontier.AlgebraicGeometry.HProjective.QuasiProjectiveOfHQuasiProjective
public import StacksFrontier.AlgebraicGeometry.ProperAmpleCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeAmpleAffineBase.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionFunctorial
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeIdEtaleChartTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartZariskiCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowNoetherianRelativeAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowTwistWitness
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSchemeNonAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesTensorQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveTwistHigherDirectImageVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedTwistCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackTensor
public import StacksFrontier.AlgebraicGeometry.TwistInvertibleOverBase.Basic

/-!
# Vanishing of the higher direct images of a large twist along a projective immersion, proved

Let `i : X ⟶ P^n_Y` be a closed immersion of algebraic spaces over a scheme `S`, with `Y`
Noetherian, let `f : X ⟶ Y` be the composite with the projection and put
`L = i^* O_{P^n_Y}(1)`.  [Stacks, Tag 08AQ] asserts that for a coherent `𝒪_X`-module `F` there is
a `d₀` with `R^p f_*(F ⊗ L^{⊗ d}) = 0` for all `d ≥ d₀` and all `p > 0`.

The diagram, the twist and the tensor powers are those of
`StacksFrontier/AlgebraicGeometry/Spaces/ProjectiveTwistHigherDirectImageVanishing.lean`, whose
`AlgebraicGeometry.Space.exists_isZero_rightDerived_modulePushforward_tensor_twist` performs the
étale-local reduction of the source's proof and carries the scheme case as a hypothesis.  Here the
scheme case is proved, so the statement holds with exactly the source's hypotheses.

## Main results

* `AlgebraicGeometry.isAmple_pullbackModule_twistingSheaf_of_isClosedImmersion`: the inverse
  image of `𝒪(1)` to a closed subscheme of `W ×_S P^n_S`, for `W` affine, is ample.
* `AlgebraicGeometry.Space.restrictToChartTensorObjIso`: restricting a tensor product of
  quasi-coherent modules to an étale chart gives the tensor product of the restrictions.
* `AlgebraicGeometry.Space.ProjectiveSpaceImmersion.isClosedImmersion_chartEmbedding`: over an
  étale chart `A` of `Y`, the map `A ×_Y X ⟶ A ×_S P^n_S` induced by `i` is a closed immersion of
  schemes.
* `AlgebraicGeometry.Space.exists_twistBound_isZero_rightDerived_modulePushforward`:
  **[Stacks, Tag 08AQ]**.

## Implementation notes

The proof is the source's.  The assertion is étale local on `Y`.  Since `Y` is Noetherian it has
one surjective étale chart `A` whose scheme is affine with Noetherian ring of functions.
`AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_isZero_chart` (Stacks 071Z,
0720, and the Leray collapse over the affine `A`) reduces `R^p f_*(F ⊗ L^{⊗ d}) = 0` to the
vanishing of the Zariski cohomology of the restriction of `F ⊗ L^{⊗ d}` to the scheme
`T = A ×_Y X` (Stacks 03DW).  That restriction is `G ⊗ L_T^{⊗ d}`, where `G` is the coherent
restriction of `F` and `L_T` is the inverse image of `𝒪(1)` along the closed immersion
`T ⟶ A ×_S P^n_S`.  `L_T` is ample and `T ⟶ A` is proper, so Serre's vanishing theorem for an
ample invertible module over a Noetherian affine base
(`Stacks.AlgebraicGeometry.ProperAmpleCohomology.exists_isZero_Hgroup_tensorPowTwist`, the
affine case of Stacks 02O1 with one bound for every degree) applies.  A single chart does the
job, so no bound has to be taken uniformly over charts.

## References

* [Stacks Project, Tag 08AQ](https://stacks.math.columbia.edu/tag/08AQ)
* [Stacks Project, Tag 02O1](https://stacks.math.columbia.edu/tag/02O1)
* [Stacks Project, Tag 071Z](https://stacks.math.columbia.edu/tag/071Z)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe u

namespace AlgebraicGeometry

open Stacks.Ample Stacks.AmpleLocallyClosed

/-- **The inverse image of `𝒪(1)` to a closed subscheme of projective space over an affine
scheme is ample.**  Let `Q = W ×_S P^n_S` (any cartesian square over the structure morphism of
`P^n_S`) with `W` affine, and let `ι : T ⟶ Q` be a closed immersion.  `𝒪(1)` is ample relative
to `P^n_S ⟶ S`, so its inverse image to `Q` is ample relative to `Q ⟶ W`, which over the affine
`W` is ampleness; ampleness pulls back along the affine morphism `ι`. -/
theorem isAmple_pullbackModule_twistingSheaf_of_isClosedImmersion
    {n : ℕ} {S W Q T : Scheme.{u}} [IsAffine W]
    {c : W ⟶ S} {q₁ : Q ⟶ projectiveSpaceOver n S} {q₂ : Q ⟶ W}
    (hsq : IsPullback q₁ q₂ (projectiveSpaceOver n S ↘ S) c) (ι : T ⟶ Q) [IsClosedImmersion ι] :
    IsAmple T (pullbackModule (ι ≫ q₁)
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n S)) := by
  let O := Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n S
  have hQ : IsAmple Q (pullbackModule q₁ O) :=
    (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple q₂ _).1
      (Stacks.AmpleBridge.isRelativelyAmple_pullbackModule_of_isPullback hsq O
        (Stacks.HProjective.isRelativelyAmple_projectiveSpaceTwistingSheaf n S))
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _
    (Stacks.RelativeVeryAmple.modulePullbackPairIso ι q₁ O)).1
    (Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom ι _ hQ)

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] modulesMonoidalCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

open Stacks.AmpleLocallyClosed (pullbackModule)

/-! ### Restriction to an étale chart -/

section ChartRestriction

variable {X : AlgebraicSpaces B S hS} (U : SmallEtale B S hS X.1)

/-- **Restriction to an étale chart is monoidal on quasi-coherent modules**:
`(M ⊗ N)|_U ≅ M|_U ⊗ N|_U` on the Zariski site of the chart's scheme.  The restriction to `U` is
the identity-chart restriction of the inverse image to the algebraic space `U` represents
(`AlgebraicGeometry.Space.restrictToChartIsoChartSpaceIdEtaleChart`); the inverse image is
monoidal (Stacks 03EL, `AlgebraicGeometry.Space.modulePullbackTensorIso`), and so is the
identity-chart restriction on quasi-coherent modules
(`AlgebraicGeometry.Space.restrictToChartSchemeIdEtaleChartTensorIso`). -/
noncomputable def restrictToChartTensorObjIso (M N : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) :
    restrictToChart B S hS X.2 (M ⊗ N) U ≅
      Stacks.RelativeVeryAmple.tensorModules (chartScheme U)
        (restrictToChart B S hS X.2 M U) (restrictToChart B S hS X.2 N U) :=
  let φ := chartToSpace B S hS X U
  have hMN : (M ⊗ N).IsQuasicoherentOnSite :=
    haveI := hM; haveI := hN; isQuasicoherentOnSite_tensorObj B S hS X.1 X.2 M N
  restrictToChartIsoChartSpaceIdEtaleChart B S hS X U (M ⊗ N) hMN ≪≫
    (restrictToChartSchemeFunctor B S hS (chartSpace B S hS X U).1 (chartSpace B S hS X U).2
      (idEtaleChart B S hS ((SmallEtale.toOver B S hS X.1).obj U))).mapIso
      (modulePullbackTensorIso B S hS φ M N) ≪≫
    restrictToChartSchemeIdEtaleChartTensorIso B S hS ((SmallEtale.toOver B S hS X.1).obj U) _ _
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS φ M hM)
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS φ N hN) ≪≫
    eqToIso (_root_.AlgebraicGeometry.SmallEtale.tensorSheafBifunctorZariski_obj
      (chartScheme U) _ _) ≪≫
    Stacks.RelativeVeryAmple.tensorModulesMapIso (chartScheme U)
      (restrictToChartIsoChartSpaceIdEtaleChart B S hS X U M hM).symm
      (restrictToChartIsoChartSpaceIdEtaleChart B S hS X U N hN).symm

/-- The positive tensor powers of a quasi-coherent module are quasi-coherent. -/
theorem isQuasicoherentOnSite_tensorPow_of_pos {Z : AlgebraicSpaces B S hS}
    (L : Modules.{u, u} B S hS Z.1 Z.2) (hL : L.IsQuasicoherentOnSite) :
    ∀ d : ℕ, 0 < d → (tensorPow B S hS L d).IsQuasicoherentOnSite
  | 1, _ => hL
  | (d + 2), _ =>
    have := isQuasicoherentOnSite_tensorPow_of_pos L hL (d + 1) d.succ_pos
    have := hL
    isQuasicoherentOnSite_tensorObj B S hS Z.1 Z.2 (tensorPow B S hS L (d + 1)) L

/-- **The restriction to an étale chart of a positive tensor power** of a quasi-coherent module
`L` is the corresponding power of an invertible module `L'` identified with the restriction of
`L`. -/
theorem nonempty_restrictToChart_tensorPow_iso_tensorPowModule
    (L : Modules.{u, u} B S hS X.1 X.2) (hL : L.IsQuasicoherentOnSite)
    (L' : (chartScheme U).Modules) [Stacks.Ample.IsInvertibleModule (chartScheme U) L']
    (e : restrictToChart B S hS X.2 L U ≅ L') :
    ∀ d : ℕ, 0 < d → Nonempty (restrictToChart B S hS X.2 (tensorPow B S hS L d) U ≅
      Stacks.Ample.tensorPowModule (chartScheme U) L' (d : ℤ))
  | 1, _ => ⟨e ≪≫ (Stacks.Ample.tensorPowModuleOneIso (chartScheme U) L').symm⟩
  | (d + 2), _ => by
    obtain ⟨ih⟩ := nonempty_restrictToChart_tensorPow_iso_tensorPowModule L hL L' e (d + 1)
      d.succ_pos
    exact ⟨restrictToChartTensorObjIso U (tensorPow B S hS L (d + 1)) L
        (isQuasicoherentOnSite_tensorPow_of_pos L hL (d + 1) d.succ_pos) hL ≪≫
      Stacks.RelativeVeryAmple.tensorModulesMapIso (chartScheme U) ih
        (e ≪≫ (Stacks.Ample.tensorPowModuleOneIso (chartScheme U) L').symm) ≪≫
      Stacks.Ample.tensorPowModuleAddIso (chartScheme U) L' ((d + 1 : ℕ) : ℤ) 1 ≪≫
      Stacks.RelativeVeryAmple.tensorPowModuleCongr (chartScheme U) L' (by push_cast; ring)⟩

/-- **The cohomology over an étale chart vanishes with the Zariski cohomology of the
restriction.**  For an étale chart `U` of `X`, a quasi-coherent `𝒪_X`-module `M` and `q > 0`, if
`H^q(U, M|_U) = 0` on the Zariski site of the chart's scheme then the degree-`q` cohomology over
the identity chart of the inverse image of `M` to the algebraic space `U` represents vanishes.
This is Stacks 03DW in the direction needed
(`AlgebraicGeometry.Space.isZero_rightDerived_evaluation_of_isZero_hgroup`), read through the
identifications of the several readings of the restriction. -/
theorem isZero_rightDerived_evaluation_chartSpace_of_isZero_hgroup_restrictToChart
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite) (q : ℕ) (hq : 0 < q)
    (h : IsZero (Hgroup (chartScheme U).ringCatSheaf ⊤ q (restrictToChart B S hS X.2 M U))) :
    IsZero (((SheafOfModules.evaluation
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
          (chartSpace B S hS X U).1 (chartSpace B S hS X U).2).O)
        (op (idEtaleChart B S hS (chartFppfObject B S hS X U)))).rightDerived q).obj
        ((etaleModulePullback B S hS (chartToSpace B S hS X U)
          (isEtale_chartToSpace B S hS X U)).obj M)) := by
  have := isContinuous_chartComparisonFunctor B S hS (chartSpace B S hS X U)
    (idEtaleChart B S hS (chartFppfObject B S hS X U))
  let M' := (etaleModulePullback B S hS (chartToSpace B S hS X U)
    (isEtale_chartToSpace B S hS X U)).obj M
  have hM' : M'.IsQuasicoherentOnSite := isQuasicoherentOnSite_etaleModulePullback B S hS
    (chartToSpace B S hS X U) (isEtale_chartToSpace B S hS X U) M hM
  have e : (SheafOfModules.pushforward.{u} (chartComparisonRingMap B S hS (chartSpace B S hS X U)
      (idEtaleChart B S hS (chartFppfObject B S hS X U)))).obj M' ≅
        restrictToChart B S hS X.2 M U :=
    (restrictToChartSchemeIsoChartComparisonPushforward B S hS (chartSpace B S hS X U)
      (idEtaleChart B S hS (chartFppfObject B S hS X U)) M').symm ≪≫
    eqToIso (restrictToChartScheme_etaleModulePullback_idEtaleChart B S hS X M U) ≪≫
    (restrictToChartIsoRestrictToChartScheme B S hS X.2 M U).symm
  exact isZero_rightDerived_evaluation_of_isZero_hgroup B S hS (chartSpace B S hS X U)
    (idEtaleChart B S hS (chartFppfObject B S hS X U)) M' hM' q hq
    (h.of_iso ((Hfunctor (chartScheme U).ringCatSheaf ⊤ q).mapIso e))

/-- **The restriction to an étale chart of an inverse image from a represented algebraic
space.**  Let `φ : X ⟶ V` be a morphism to the algebraic space represented by `V`, let `U` be an
étale chart of `X` and `g` a morphism from the chart's object to `V` through which `U ⟶ X ⟶ V`
factors.  For a quasi-coherent `𝒪_V`-module `N`, `(φ^* N)|_U ≅ g^*(N|_V)`. -/
theorem nonempty_restrictToChart_modulePullback_iso_pullbackModule {V : BigFppfOver B S hS}
    (φ : X ⟶ schemeSpace V) (g : (SmallEtale.toOver B S hS X.1).obj U ⟶ V)
    (hg : chartToSpace B S hS X U ≫ φ = representedSpaceMap B S hS g)
    (N : Modules.{u, u} B S hS (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V))
    (hN : N.IsQuasicoherentOnSite) :
    Nonempty (restrictToChart B S hS X.2 ((modulePullback B S hS φ).obj N) U ≅
      pullbackModule ((BigFppfOver.toScheme B S hS).map g)
        (restrictToChartScheme B S hS (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V) N
          (idEtaleChart B S hS V))) := by
  obtain ⟨e⟩ := nonempty_restrictToChartScheme_baseChange_of_isQuasicoherent g N hN
  exact ⟨restrictToChartIsoChartSpaceIdEtaleChart B S hS X U _
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS φ N hN) ≪≫
    (restrictToChartSchemeFunctor B S hS (chartSpace B S hS X U).1 (chartSpace B S hS X U).2
      (idEtaleChart B S hS ((SmallEtale.toOver B S hS X.1).obj U))).mapIso
      ((modulePullbackCompIso B S hS (chartToSpace B S hS X U) φ).app N ≪≫
        eqToIso (congrArg (fun k : chartSpace B S hS X U ⟶ schemeSpace V =>
          (modulePullback B S hS k).obj N) hg)) ≪≫ e⟩

/-- On a locally Noetherian algebraic space, the restriction of a coherent module to an étale
chart is coherent. -/
private theorem isCoherent_restrictToChart_of_isLocallyNoetherian
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F)
    (hX : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V)) :
    (restrictToChart B S hS X.2 F U).IsCoherent :=
  Stacks.AlgebraicGeometry.RelativeSerreVanishing.isCoherent_of_iso
    (restrictToChartIsoChartSchemeModule B S hS X F hF.toIsQuasicoherentOnSite U).symm
    (isCoherent_chartSchemeModule_of_isLocallyNoetherian B S hS X F hF U
      (isLocallyNoetherian_chart B S hS hX U))

end ChartRestriction

/-- **The module associated with a quasi-coherent module on a scheme restricts back to it**
along the identity chart of the represented algebraic space (Descent, Proposition 03DX). -/
theorem nonempty_restrictToChartScheme_idEtaleChart_representedAssociatedModule
    (V : BigFppfOver B S hS) (F : ((BigFppfOver.toScheme B S hS).obj V).Modules)
    (hF : SheafOfModules.IsQuasicoherent F) :
    Nonempty (restrictToChartScheme B S hS (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V)
      ((representedAssociatedModule B S hS V (isAlgebraicSpace_yoneda B S hS V)).obj F)
      (idEtaleChart B S hS V) ≅ F) := by
  obtain ⟨e⟩ := nonempty_chartZariskiPushforward_idEtaleChart_iso B S hS V F hF
  exact ⟨restrictToChartSchemeIsoChartComparisonPushforward B S hS (schemeSpace V)
    (idEtaleChart B S hS V) _ ≪≫ e⟩

/-! ### The diagram over an étale chart of the base -/

namespace ProjectiveSpaceImmersion

variable {n : ℕ} {hP : B.Contains (projectiveSpaceOver n S)} {X Y : AlgebraicSpaces B S hS}
  (D : ProjectiveSpaceImmersion B S hS n hP X Y) (A : SmallEtale B S hS Y.1)

/-- The structure morphism `Y ⟶ S` of the diagram, with target the presheaf represented by the
base scheme. -/
noncomputable abbrev baseToYoneda : Y.1 ⟶ yoneda.obj (baseSiteObj B S hS) := D.base.hom

/-- The homogeneous coordinates `P^n_Y ⟶ P^n_S`, with target the presheaf represented by
`P^n_S`. -/
noncomputable abbrev coordToYoneda :
    D.projSpace.1 ⟶ yoneda.obj (projectiveSpaceSiteObj B S hS n hP) :=
  D.coord.hom

/-- The square `P^n_Y = Y ×_S P^n_S`, with the targets read as represented presheaves. -/
theorem isPullback_yoneda : IsPullback D.proj.hom D.coordToYoneda D.baseToYoneda
    (yoneda.map (projectiveSpaceSiteObjToBase B S hS n hP)) := D.isPullback

/-- The structure morphism to the base scheme of an étale chart `A` of `Y`. -/
noncomputable def chartBaseMap : A.1.left ⟶ baseSiteObj B S hS :=
  yoneda.preimage (A.1.hom ≫ D.baseToYoneda)

/-- Projective `n`-space `A ×_S P^n_S` over an étale chart `A` of `Y`, as an object of the big
fppf site; it is the chart of `P^n_Y` over `A`. -/
noncomputable abbrev chartProjSpace : BigFppfOver B S hS :=
  pullback (D.chartBaseMap A) (projectiveSpaceSiteObjToBase B S hS n hP)

/-- The homogeneous coordinates `A ×_Y X ⟶ X ⟶ P^n_Y ⟶ P^n_S` of the base change of `X` to an
étale chart `A` of `Y`. -/
noncomputable def chartCoordinates :
    D.relativelyRepresentable_hom.pullback A.1.hom ⟶ projectiveSpaceSiteObj B S hS n hP :=
  yoneda.preimage (D.relativelyRepresentable_hom.fst A.1.hom ≫ D.imm.hom ≫ D.coordToYoneda)

/-- Under the Yoneda embedding, `chartCoordinates` is the composite
`A ×_Y X ⟶ X ⟶ P^n_Y ⟶ P^n_S`. -/
theorem yoneda_map_chartCoordinates :
    yoneda.map (D.chartCoordinates A) =
      D.relativelyRepresentable_hom.fst A.1.hom ≫ D.imm.hom ≫ D.coordToYoneda :=
  Functor.map_preimage _ _

/-- The coordinates of `A ×_Y X` followed by `P^n_S ⟶ S` agree with the projection to `A`
followed by the structure morphism `A ⟶ S`. -/
theorem chartCoordinates_comp_toBase :
    D.chartCoordinates A ≫ projectiveSpaceSiteObjToBase B S hS n hP =
      D.relativelyRepresentable_hom.snd A.1.hom ≫ D.chartBaseMap A := by
  apply yoneda.map_injective
  have h₁ : D.relativelyRepresentable_hom.fst A.1.hom ≫ D.imm.hom ≫ D.proj.hom =
      yoneda.map (D.relativelyRepresentable_hom.snd A.1.hom) ≫ A.1.hom :=
    (D.relativelyRepresentable_hom.isPullback A.1.hom).w
  rw [Functor.map_comp, Functor.map_comp, yoneda_map_chartCoordinates, chartBaseMap,
    Functor.map_preimage, Category.assoc, Category.assoc, ← D.isPullback_yoneda.w,
    reassoc_of% h₁]

/-- The morphism `A ×_Y X ⟶ A ×_S P^n_S` induced by `i` over an étale chart `A` of `Y`. -/
noncomputable def chartEmbedding :
    D.relativelyRepresentable_hom.pullback A.1.hom ⟶ D.chartProjSpace A :=
  pullback.lift _ _ (D.chartCoordinates_comp_toBase A).symm

/-- The first component of `chartEmbedding` is the projection `A ×_Y X ⟶ A`. -/
@[reassoc]
theorem chartEmbedding_fst :
    D.chartEmbedding A ≫ pullback.fst _ _ = D.relativelyRepresentable_hom.snd A.1.hom :=
  pullback.lift_fst _ _ _

/-- The second component of `chartEmbedding` is `chartCoordinates`. -/
@[reassoc]
theorem chartEmbedding_snd : D.chartEmbedding A ≫ pullback.snd _ _ = D.chartCoordinates A :=
  pullback.lift_snd _ _ _

/-- The underlying schemes of `A ×_S P^n_S` form a cartesian square over `P^n_S ⟶ S`. -/
theorem isPullback_toScheme_chartProjSpace :
    IsPullback ((BigFppfOver.toScheme B S hS).map
        (pullback.snd (D.chartBaseMap A) (projectiveSpaceSiteObjToBase B S hS n hP)))
      ((BigFppfOver.toScheme B S hS).map
        (pullback.fst (D.chartBaseMap A) (projectiveSpaceSiteObjToBase B S hS n hP)))
      (projectiveSpaceOver n S ↘ S) ((BigFppfOver.toScheme B S hS).map (D.chartBaseMap A)) :=
  (IsPullback.of_hasPullback (D.chartBaseMap A)
    (projectiveSpaceSiteObjToBase B S hS n hP)).flip.map (BigFppfOver.toScheme B S hS)

/-- Over an étale chart `A` of `Y`, the map `A ×_Y X ⟶ A ×_S P^n_S` is a closed immersion of
schemes. -/
theorem isClosedImmersion_chartEmbedding :
    _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (D.chartEmbedding A)) := by
  let ρ := D.relativelyRepresentable_hom
  let s := pullback.fst (D.chartBaseMap A) (projectiveSpaceSiteObjToBase B S hS n hP)
  let t := pullback.snd (D.chartBaseMap A) (projectiveSpaceSiteObjToBase B S hS n hP)
  have hsq : IsPullback (yoneda.map s) (yoneda.map t) (A.1.hom ≫ D.baseToYoneda)
      (yoneda.map (projectiveSpaceSiteObjToBase B S hS n hP)) := by
    have h := (IsPullback.of_hasPullback (D.chartBaseMap A)
      (projectiveSpaceSiteObjToBase B S hS n hP)).map yoneda
    rwa [chartBaseMap, Functor.map_preimage] at h
  -- the chart `A ×_S P^n_S ⟶ P^n_Y` of `P^n_Y` over `A`
  let k : yoneda.obj (D.chartProjSpace A) ⟶ D.projSpace.1 :=
    D.isPullback_yoneda.lift (yoneda.map s ≫ A.1.hom) (yoneda.map t)
      (by rw [Category.assoc]; exact hsq.w)
  have hk₁ : k ≫ D.proj.hom = yoneda.map s ≫ A.1.hom := D.isPullback_yoneda.lift_fst _ _ _
  have hk₂ : k ≫ D.coordToYoneda = yoneda.map t := D.isPullback_yoneda.lift_snd _ _ _
  have hk : IsPullback k (yoneda.map s) D.proj.hom A.1.hom := by
    refine IsPullback.of_right (h₁₂ := D.coordToYoneda) (h₂₂ := D.baseToYoneda) ?_ hk₁
      D.isPullback_yoneda.flip
    rw [hk₂]
    exact hsq.flip
  have hX : IsPullback (ρ.fst A.1.hom) (yoneda.map (D.chartEmbedding A)) D.imm.hom k := by
    refine IsPullback.of_bot ?_ ?_ hk
    · rw [← Functor.map_comp, chartEmbedding_fst]
      exact ρ.isPullback A.1.hom
    · refine D.isPullback_yoneda.hom_ext ?_ ?_
      · rw [Category.assoc, Category.assoc, hk₁, ← Functor.map_comp_assoc, chartEmbedding_fst]
        exact (ρ.isPullback A.1.hom).w
      · rw [Category.assoc, Category.assoc, hk₂, ← Functor.map_comp, chartEmbedding_snd,
          yoneda_map_chartCoordinates]
  exact D.imm_isClosedImmersion.property _ _ _ hX

/-- **The restriction of the twist `L` to `A ×_Y X`** is the inverse image of
`𝒪_{P^n_S}(1)` along `A ×_Y X ⟶ A ×_S P^n_S ⟶ P^n_S`. -/
theorem nonempty_restrictToChart_twist_iso_pullbackModule :
    Nonempty (restrictToChart B S hS X.2 D.twist
        ((smallBaseChange B S hS D.hom D.relativelyRepresentable_hom).obj A) ≅
      pullbackModule ((BigFppfOver.toScheme B S hS).map (D.chartEmbedding A) ≫
          (BigFppfOver.toScheme B S hS).map (pullback.snd _ _))
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n S)) := by
  let O := Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n S
  have hO : SheafOfModules.IsQuasicoherent O :=
    Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule O
  let P := projectiveSpaceSiteObj B S hS n hP
  let N := (representedAssociatedModule B S hS P (isAlgebraicSpace_yoneda B S hS P)).obj O
  have hN : N.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_representedAssociatedModule B S hS P _ O hO
  let T := (smallBaseChange B S hS D.hom D.relativelyRepresentable_hom).obj A
  let c : (SmallEtale.toOver B S hS X.1).obj T ⟶ P := D.chartCoordinates A
  -- `T ⟶ X ⟶ P^n_S` is the image of the chart coordinates
  have hcomm : chartToSpace B S hS X T ≫ (D.imm ≫ D.coord) = representedSpaceMap B S hS c :=
    ObjectProperty.hom_ext _ (D.yoneda_map_chartCoordinates A).symm
  obtain ⟨e₁⟩ := nonempty_restrictToChart_modulePullback_iso_pullbackModule T (D.imm ≫ D.coord) c
    hcomm N hN
  obtain ⟨e₂⟩ := nonempty_restrictToChartScheme_idEtaleChart_representedAssociatedModule P O hO
  have e₃ : pullbackModule ((BigFppfOver.toScheme B S hS).map c) O =
      pullbackModule ((BigFppfOver.toScheme B S hS).map (D.chartEmbedding A) ≫
        (BigFppfOver.toScheme B S hS).map (pullback.snd _ _)) O := by
    rw [← Functor.map_comp, chartEmbedding_snd]
    rfl
  exact ⟨restrictToChartIso B S hS X.2 ((modulePullbackCompIso B S hS D.imm D.coord).app N) T ≪≫
    e₁ ≪≫ (RingedSpaceModuleAdjunction.modulePullback
      ((BigFppfOver.toScheme B S hS).map c).toLRSHom.toShHom).mapIso e₂ ≪≫ eqToIso e₃⟩

/-- Over an étale chart `A` of `Y`, the composite `A ×_Y X ⟶ A ×_S P^n_S ⟶ A` is proper. -/
private theorem isProper_chartEmbedding_comp_fst :
    _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map (D.chartEmbedding A) ≫
      (BigFppfOver.toScheme B S hS).map
        (pullback.fst (D.chartBaseMap A) (projectiveSpaceSiteObjToBase B S hS n hP))) := by
  have := D.isClosedImmersion_chartEmbedding A
  have : _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map
      (pullback.fst (D.chartBaseMap A) (projectiveSpaceSiteObjToBase B S hS n hP))) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @_root_.AlgebraicGeometry.IsProper)
      (D.isPullback_toScheme_chartProjSpace A) (isProper_projectiveSpaceOver n S)
  have : _root_.AlgebraicGeometry.IsProper
      ((BigFppfOver.toScheme B S hS).map (D.chartEmbedding A)) := inferInstance
  infer_instance

/-- The twist `L = i^* 𝒪_{P^n_Y}(1)` is quasi-coherent. -/
private theorem isQuasicoherentOnSite_twist : D.twist.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS D.imm _
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS D.coord _
      (isQuasicoherentOnSite_representedAssociatedModule B S hS
        (projectiveSpaceSiteObj B S hS n hP) (isAlgebraicSpace_yoneda B S hS _)
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n S)
        (Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule _)))

end ProjectiveSpaceImmersion

/-! ### Stacks 08AQ -/

attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

/-- **Stacks 08AQ.** Let `i : X ⟶ P^n_Y` be a closed immersion of algebraic spaces over `S` with
`Y` Noetherian, let `f : X ⟶ Y` be the composite with the projection and let
`L = i^* O_{P^n_Y}(1)`. For a coherent `𝒪_X`-module `F` there is a `d₀` such that

`R^p f_*(F ⊗ L^{⊗ d}) = 0` for all `d ≥ d₀` and all `p > 0`. -/
@[stacks 08AQ]
theorem exists_twistBound_isZero_rightDerived_modulePushforward
    (hZ : B.Contains (⊤_ Scheme.{u})) (n : ℕ)
    (hP : B.Contains (projectiveSpaceOver n S)) {X Y : AlgebraicSpaces B S hS}
    (D : ProjectiveSpaceImmersion B S hS n hP X Y)
    (hY : IsNoetherian B S hS hZ Y.1) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : IsCoherent B S hS X.1 X.2 F) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ p : ℕ, 0 < p →
      IsZero (((modulePushforward B S hS D.hom).rightDerived p).obj
        (F ⊗ tensorPow B S hS D.twist d)) := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have hρ := D.relativelyRepresentable_hom
  have hf := D.isProper_hom
  obtain ⟨A, ⟨hAaff, hANoeth⟩, hAsurj, -⟩ :=
    exists_surjective_isNoetherianAffineChart B S hS hZ Y hY
  let T := (smallBaseChange B S hS D.hom hρ).obj A
  have hXln : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V) :=
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS X.2 Y.2 D.hom.hom hf.2.1.1 hY.2.2
  let G : (chartScheme T).Modules := restrictToChart B S hS X.2 F T
  have hGcoh : G.IsCoherent := isCoherent_restrictToChart_of_isLocallyNoetherian T F hF hXln
  let O := Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n S
  let ι := (BigFppfOver.toScheme B S hS).map (D.chartEmbedding A)
  let LT := pullbackModule (ι ≫ (BigFppfOver.toScheme B S hS).map (pullback.snd _ _)) O
  have hOinv : Stacks.Ample.IsInvertibleModule (projectiveSpaceOver n S) O := inferInstance
  have hLTinv : Stacks.Ample.IsInvertibleModule (chartScheme T) LT :=
    @Stacks.InvertiblePullback.isInvertibleModule_pullback _ _ _ _ hOinv
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj A.1.left) := hAaff
  have : IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj A.1.left, ⊤) := hANoeth
  have : _root_.AlgebraicGeometry.IsClosedImmersion ι := D.isClosedImmersion_chartEmbedding A
  have hLT : Stacks.Ample.IsAmple (chartScheme T) LT :=
    isAmple_pullbackModule_twistingSheaf_of_isClosedImmersion
      (D.isPullback_toScheme_chartProjSpace A) ι
  have := D.isProper_chartEmbedding_comp_fst A
  have hg : _root_.AlgebraicGeometry.IsProper
      ((ι ≫ (BigFppfOver.toScheme B S hS).map (pullback.fst _ _)) ≫
        ((BigFppfOver.toScheme B S hS).obj A.1.left).isoSpec.hom) := inferInstance
  obtain ⟨d₀, hd₀⟩ :=
    @Stacks.AlgebraicGeometry.ProperAmpleCohomology.exists_isZero_Hgroup_tensorPowTwist
    (chartScheme T) Γ((BigFppfOver.toScheme B S hS).obj A.1.left, ⊤) _ _
    ((ι ≫ (BigFppfOver.toScheme B S hS).map (pullback.fst _ _)) ≫
      ((BigFppfOver.toScheme B S hS).obj A.1.left).isoSpec.hom) hg G LT hGcoh hLTinv hLT
  obtain ⟨eL⟩ := D.nonempty_restrictToChart_twist_iso_pullbackModule A
  have hLqc := D.isQuasicoherentOnSite_twist
  refine ⟨max d₀ 1, fun d hd p hp => ?_⟩
  have hd1 : 0 < d := lt_of_lt_of_le Nat.one_pos (le_of_max_le_right hd)
  have hPqc := isQuasicoherentOnSite_tensorPow_of_pos D.twist hLqc d hd1
  have hMqc : (F ⊗ tensorPow B S hS D.twist d).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_tensorObj B S hS X.1 X.2 F _
  obtain ⟨eP⟩ := nonempty_restrictToChart_tensorPow_iso_tensorPowModule T D.twist hLqc LT eL d hd1
  have eM : restrictToChart B S hS X.2 (F ⊗ tensorPow B S hS D.twist d) T ≅
      Stacks.RelativeVeryAmple.tensorModules (chartScheme T) G
        (Stacks.Ample.tensorPowModule (chartScheme T) LT (d : ℤ)) :=
    restrictToChartTensorObjIso T F _ hF.toIsQuasicoherentOnSite hPqc ≪≫
      Stacks.RelativeVeryAmple.tensorModulesMapIso (chartScheme T) (Iso.refl G) eP
  exact isZero_rightDerived_modulePushforward_of_isZero_chart B S hS D.hom hρ hf.2.1.2
    (isQuasiSeparated_of_isSeparated B S hS hf.1) A hAaff hAsurj _ hMqc p
    (isZero_rightDerived_evaluation_chartSpace_of_isZero_hgroup_restrictToChart T _ hMqc p hp
      ((hd₀ d p (le_of_max_le_left hd) hp).of_iso
        ((Hfunctor (chartScheme T).ringCatSheaf ⊤ p).mapIso eM)))

end AlgebraicGeometry.Space

end
