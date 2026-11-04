module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPullbackStability
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSpaceGlobalPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatteningByBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModulePullbackPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae03KM
public import StacksFrontier.AlgebraicGeometry.Spaces.UniformHigherDirectImageVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleFpqcDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleGeometricPointCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentLocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteOfFinitePresentation

/-!
# Flattening blowups on a surjective étale cover of the source

Finite presentation of a module on the small étale site of an algebraic space, and flatness of
a quasi-coherent module over a base, descend along surjective étale morphisms.  Consequently a
flattening blowup in the sense of Stacks 087C may be recognized after replacing the source by
a surjective étale cover, which is the first reduction of the proof of Stacks 087C; and the
hypotheses of Stacks 087C pass to such a cover.

## Main results

* `AlgebraicGeometry.Space.isFinitePresentationOnSite_of_modulePullback_of_isEtale`: finite
  presentation descends along a surjective étale morphism.  The pullback is of finite
  presentation on the chart of the target obtained by composing a surjective chart of the
  cover with the cover, and finite presentation is local on a covering of the final object
  (Stacks 03DN).
* `AlgebraicGeometry.Space.isFlatOver_of_modulePullback_of_isEtale`: flatness over a base
  descends along a surjective étale morphism (Stacks 05VY).
* `AlgebraicGeometry.Space.IsFlatteningBlowup.of_comp_etale`: a flattening blowup for `g ≫ f`
  and `g^*F`, with `g` surjective and étale, is a flattening blowup for `f` and `F`; the strict
  transform commutes with étale localization (Stacks 0863, part (3)).
* `AlgebraicGeometry.Space.flatteningHypotheses_comp_etale`: the hypotheses of Stacks 087C on
  the module pass to a surjective étale cover of the source.

## References

* [Stacks Project, Tag 087C](https://stacks.math.columbia.edu/tag/087C)
* [Stacks Project, Tag 0863](https://stacks.math.columbia.edu/tag/0863)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 05VY](https://stacks.math.columbia.edu/tag/05VY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Finite presentation descends along a surjective étale morphism.**  If `c : Q ⟶ P` is
surjective and étale and `c^*M` is of finite presentation on the small étale site of `Q`, then
`M` is of finite presentation on the small étale site of `P`. -/
theorem isFinitePresentationOnSite_of_modulePullback_of_isEtale {P Q : AlgebraicSpaces B S hS}
    (c : Q ⟶ P) (hc : IsEtale B S hS c.hom) (hs : IsSurjective B S hS c.hom)
    (M : Modules.{u, u} B S hS P.1 P.2)
    (h : ((modulePullback B S hS c).obj M).IsFinitePresentationOnSite) :
    M.IsFinitePresentationOnSite := by
  obtain ⟨V, a, hasurj, haet⟩ := Q.2.exists_atlas
  let WQ : SmallEtale B S hS Q.1 := ⟨CostructuredArrow.mk a, haet⟩
  let WP : SmallEtale B S hS P.1 := ⟨CostructuredArrow.mk (a ≫ c.hom), hc _ _ haet⟩
  have hWP : IsSurjective B S hS WP.1.hom := isSurjective_comp B S hS
    ((presheafSurjective_iff_isSurjective_yoneda B S hS Q.1 Q.2 V a).1 hasurj) hs
  let k : chartSpace B S hS P WP ⟶ Q := ObjectProperty.homMk a
  have hk : k ≫ c = chartToSpace B S hS P WP := rfl
  have h0 : ((modulePullback B S hS (k ≫ c)).obj M).IsFinitePresentationOnSite :=
    SheafOfModules.IsFinitePresentationOnSite.of_iso ((modulePullbackCompIso B S hS k c).app M)
      (isFinitePresentationOnSite_modulePullback B S hS k _ h)
  rw [hk] at h0
  have h1 : ((etaleModulePullback B S hS (chartToSpace B S hS P WP)
      (isEtale_chartToSpace B S hS P WP)).obj M).IsFinitePresentationOnSite :=
    SheafOfModules.IsFinitePresentationOnSite.of_iso
      ((modulePullbackIsoEtaleModulePullback B S hS _ (isEtale_chartToSpace B S hS P WP)).app M)
      h0
  let (W : SmallEtale B S hS P.1) : HasSheafify ((SmallEtale.topology B S hS P.1).over W)
      AddCommGrpCat.{u} := AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  let M' : SheafOfModules.{u} (structureRingSheaf B S hS P) := M
  have h2 : (M'.over WP).IsFinitePresentation :=
    (isFinitePresentation_chartSmallEtaleRestriction_iff B S hS P M' WP).1
      (SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite' _ h1)
  refine SheafOfModules.isFinitePresentationOnSite_of_isFinitePresentation M' (h := ?_)
  exact (Stacks.SheafOfModules.isFinitePresentation_iff_exists_cover_isFinitePresentation M').2
    ⟨PUnit, fun _ => WP, SmallEtale.coversTop_of_isSurjective B S hS P.1 P.2 WP hWP,
      fun _ => h2⟩

/-- **Flatness over the base descends along a surjective étale morphism of sources.**  This is
Stacks 05VY at a surjective étale morphism, which is flat. -/
theorem isFlatOver_of_modulePullback_of_isEtale {P Q Z : AlgebraicSpaces B S hS} (c : Q ⟶ P)
    (hc : IsEtale B S hS c.hom) (hs : IsSurjective B S hS c.hom) (g : P ⟶ Z)
    (M : Modules.{u, u} B S hS P.1 P.2) (hM : M.IsQuasicoherentOnSite)
    (h : IsFlatOver B S hS Q.2 (c ≫ g).hom ((modulePullback B S hS c).obj M)) :
    IsFlatOver B S hS P.2 g.hom M :=
  have := hM
  (isFlatOver_modulePullback_iff_of_isSurjective_of_isFlat B S hS c g M hs
    (isFlat_of_isEtale B S hS hc)).2 h

variable {A X : AlgebraicSpaces B S hS}

/-- The comparison map between a pullback along `g ≫ f` and one along `f` is a base change of
`g`. -/
private theorem isPullback_of_lift_comp {C : Type*} [Category C] {V' X' V X A A' : C}
    {l : V' ⟶ X'} {p₁ : V' ⟶ V} {q₁ : V' ⟶ A'} {p₂ : X' ⟶ X} {q₂ : X' ⟶ A'} {g : V ⟶ X}
    {f : X ⟶ A} {b : A' ⟶ A} (h₁ : IsPullback p₁ q₁ (g ≫ f) b) (h₂ : IsPullback p₂ q₂ f b)
    (hp : l ≫ p₂ = p₁ ≫ g) (hq : l ≫ q₂ = q₁) : IsPullback l p₁ p₂ g :=
  IsPullback.of_right (by rw [hq]; exact h₁.flip) hp h₂.flip

/-- The base change of a surjective étale morphism is surjective and étale. -/
private theorem isEtale_and_isSurjective_of_isPullback {P Q P' Q' : AlgebraicSpaces B S hS}
    {fst : P' ⟶ Q'} {snd : P' ⟶ P} {g' : Q' ⟶ Q} {c : P ⟶ Q}
    (sq : IsPullback fst snd g' c) (hg : IsEtale B S hS c.hom)
    (hgs : IsSurjective B S hS c.hom) :
    IsEtale B S hS fst.hom ∧ IsSurjective B S hS fst.hom :=
  ⟨isEtale_of_isPullback B S hS _ _ _ _ sq.flip hg, isSurjective_of_isPullback B S hS sq.flip hgs⟩

/-- The morphism `V ×_A A' ⟶ X ×_A A'` of ambient base changes induced by `g : V ⟶ X` over
`A`. -/
noncomputable def strictTransformPullbackMapSource {V A' : AlgebraicSpaces B S hS} (g : V ⟶ X)
    (f : X ⟶ A) (b : A' ⟶ A) :
    strictTransformPullback B S hS (g ≫ f) b ⟶ strictTransformPullback B S hS f b :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS f b).lift
    (strictTransformPullbackToSource B S hS (g ≫ f) b ≫ g)
    (strictTransformPullbackToBlowUp B S hS (g ≫ f) b)
    (by rw [Category.assoc]; exact (AlgebraicSpaces.isPullback_fiberProduct B S hS (g ≫ f) b).w)

/-- `AlgebraicGeometry.Space.strictTransformPullbackMapSource` lies over `g`. -/
theorem strictTransformPullbackMapSource_toSource {V A' : AlgebraicSpaces B S hS} (g : V ⟶ X)
    (f : X ⟶ A) (b : A' ⟶ A) :
    strictTransformPullbackMapSource g f b ≫ strictTransformPullbackToSource B S hS f b =
      strictTransformPullbackToSource B S hS (g ≫ f) b ≫ g :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS f b).lift_fst _ _ _

/-- `AlgebraicGeometry.Space.strictTransformPullbackMapSource` lies over `A'`. -/
theorem strictTransformPullbackMapSource_toBlowUp {V A' : AlgebraicSpaces B S hS} (g : V ⟶ X)
    (f : X ⟶ A) (b : A' ⟶ A) :
    strictTransformPullbackMapSource g f b ≫ strictTransformPullbackToBlowUp B S hS f b =
      strictTransformPullbackToBlowUp B S hS (g ≫ f) b :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS f b).lift_snd _ _ _

/-- The square exhibiting `V ×_A A' ⟶ X ×_A A'` as the base change of `g : V ⟶ X`. -/
theorem isPullback_strictTransformPullbackMapSource {V A' : AlgebraicSpaces B S hS} (g : V ⟶ X)
    (f : X ⟶ A) (b : A' ⟶ A) :
    IsPullback (strictTransformPullbackMapSource g f b)
      (strictTransformPullbackToSource B S hS (g ≫ f) b)
      (strictTransformPullbackToSource B S hS f b) g :=
  isPullback_of_lift_comp (AlgebraicSpaces.isPullback_fiberProduct B S hS (g ≫ f) b)
    (AlgebraicSpaces.isPullback_fiberProduct B S hS f b)
    (strictTransformPullbackMapSource_toSource g f b)
    (strictTransformPullbackMapSource_toBlowUp g f b)

/-- **A flattening blowup may be recognized on a surjective étale cover of the source.**  Let
`g : V ⟶ X` be surjective and étale.  If `b : A' ⟶ A` is a flattening blowup for `g ≫ f` and
`g^*F`, then it is one for `f` and `F`.

The strict transform of `g^*F` is the pullback of the strict transform of `F` along the étale
surjection `V ×_A A' ⟶ X ×_A A'` (Stacks 0863, part (3), in the form
`AlgebraicGeometry.Space.strictTransformSheafEtaleRestrictionIso`), and finite presentation and
flatness over `A'` descend along it. -/
theorem IsFlatteningBlowup.of_comp_etale {V A' : AlgebraicSpaces B S hS} (g : V ⟶ X)
    (hg : IsEtale B S hS g.hom) (hgs : IsSurjective B S hS g.hom) {f : X ⟶ A}
    {F : Modules.{u, u} B S hS X.1 X.2} {U : OpenSubspaces B S hS A.1}
    {Z : ClosedSubspaces B S hS A.1} {b : A' ⟶ A}
    (h : IsFlatteningBlowup (g ≫ f) ((modulePullback B S hS g).obj F) U Z b) :
    IsFlatteningBlowup f F U Z b := by
  obtain ⟨hZ, hUZ, hb, hfp, hflat⟩ := h
  have sq := isPullback_strictTransformPullbackMapSource g f b
  obtain ⟨hcan, hcans⟩ := isEtale_and_isSurjective_of_isPullback sq hg hgs
  have e := strictTransformSheafEtaleRestrictionIso B S hS f b (Z.1.preimage b.hom) g (g ≫ f) b
    (Z.1.preimage b.hom) (𝟙 A') (strictTransformPullbackMapSource g f b) hcan
    (strictTransformPullbackMapSource_toSource g f b)
    (by rw [strictTransformPullbackMapSource_toBlowUp, Category.comp_id])
    (by rw [show (𝟙 A' : A' ⟶ A').hom = 𝟙 A'.1 from rfl, pointsMap_id, Set.preimage_id])
    F
  have hfpX : (strictTransformSheaf B S hS f b (Z.1.preimage b.hom) F).IsFinitePresentationOnSite :=
    isFinitePresentationOnSite_of_modulePullback_of_isEtale _ hcan hcans _
      (SheafOfModules.IsFinitePresentationOnSite.of_iso e.symm hfp)
  refine ⟨hZ, hUZ, hb, hfpX, ?_⟩
  refine isFlatOver_of_modulePullback_of_isEtale _ hcan hcans _ _ inferInstance ?_
  rw [strictTransformPullbackMapSource_toBlowUp]
  exact (isFlatOver_iff_of_iso B S hS _ _ e).2 hflat

/-! ### The hypotheses of Stacks 087C on a surjective étale cover of the source -/

/-- The morphism `V_U ⟶ X_U` of restrictions over an open `U ⊆ A` induced by `g : V ⟶ X`. -/
noncomputable def restrictOverMap {V : AlgebraicSpaces B S hS} (g : V ⟶ X) (f : X ⟶ A)
    (U : OpenSubspaces B S hS A.1) : restrictOver (g ≫ f) U ⟶ restrictOver f U :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS f U.toSpaceι).lift
    (restrictOverι (g ≫ f) U ≫ g) (restrictOverHom (g ≫ f) U)
    (by rw [Category.assoc]; exact (AlgebraicSpaces.isPullback_fiberProduct B S hS (g ≫ f)
      U.toSpaceι).w)

/-- `AlgebraicGeometry.Space.restrictOverMap` lies over `g`. -/
theorem restrictOverMap_ι {V : AlgebraicSpaces B S hS} (g : V ⟶ X) (f : X ⟶ A)
    (U : OpenSubspaces B S hS A.1) :
    restrictOverMap g f U ≫ restrictOverι f U = restrictOverι (g ≫ f) U ≫ g :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS f U.toSpaceι).lift_fst _ _ _

/-- `AlgebraicGeometry.Space.restrictOverMap` lies over `U`. -/
theorem restrictOverMap_hom {V : AlgebraicSpaces B S hS} (g : V ⟶ X) (f : X ⟶ A)
    (U : OpenSubspaces B S hS A.1) :
    restrictOverMap g f U ≫ restrictOverHom f U = restrictOverHom (g ≫ f) U :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS f U.toSpaceι).lift_snd _ _ _

/-- The square exhibiting `V_U ⟶ X_U` as the base change of `g : V ⟶ X`. -/
theorem isPullback_restrictOverMap {V : AlgebraicSpaces B S hS} (g : V ⟶ X) (f : X ⟶ A)
    (U : OpenSubspaces B S hS A.1) :
    IsPullback (restrictOverMap g f U) (restrictOverι (g ≫ f) U) (restrictOverι f U) g :=
  isPullback_of_lift_comp (AlgebraicSpaces.isPullback_fiberProduct B S hS (g ≫ f) U.toSpaceι)
    (AlgebraicSpaces.isPullback_fiberProduct B S hS f U.toSpaceι)
    (restrictOverMap_ι g f U) (restrictOverMap_hom g f U)

/-- The restriction over `U` of the pullback of `F` to `V` is the pullback to `V_U` of the
restriction of `F` over `U`. -/
noncomputable def restrictOverModuleIso {V : AlgebraicSpaces B S hS} (g : V ⟶ X) (f : X ⟶ A)
    (U : OpenSubspaces B S hS A.1) (F : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullback B S hS (restrictOverι (g ≫ f) U)).obj ((modulePullback B S hS g).obj F) ≅
      (modulePullback B S hS (restrictOverMap g f U)).obj
        ((modulePullback B S hS (restrictOverι f U)).obj F) :=
  ((modulePullbackCompIso B S hS (restrictOverι (g ≫ f) U) g).app F) ≪≫
    eqToIso (by rw [← restrictOverMap_ι]) ≪≫
    ((modulePullbackCompIso B S hS (restrictOverMap g f U) (restrictOverι f U)).app F).symm

/-- **The hypotheses of Stacks 087C pass to a surjective étale cover of the source**, except
quasi-compactness of the cover, which depends on the cover: if `F` is quasi-coherent of finite
type and `F_U` is of finite presentation and flat over `U`, then so are `g^*F` and
`(g^*F)_U`, for `g : V ⟶ X` surjective and étale, and `g ≫ f` is locally of finite
presentation as soon as `f` is. -/
theorem flatteningHypotheses_comp_etale {V : AlgebraicSpaces B S hS} (g : V ⟶ X)
    (hg : IsEtale B S hS g.hom) (hgs : IsSurjective B S hS g.hom) (f : X ⟶ A)
    (hf : IsLocallyOfFinitePresentation B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hFqc : F.IsQuasicoherentOnSite)
    (hFft : F.IsFiniteTypeOnSite) (U : OpenSubspaces B S hS A.1)
    (hFUfp : ((modulePullback B S hS (restrictOverι f U)).obj F).IsFinitePresentationOnSite)
    (hFUflat : IsFlatOver B S hS (restrictOver f U).2 (restrictOverHom f U).hom
      ((modulePullback B S hS (restrictOverι f U)).obj F)) :
    IsLocallyOfFinitePresentation B S hS (g ≫ f).hom ∧
      ((modulePullback B S hS g).obj F).IsQuasicoherentOnSite ∧
      ((modulePullback B S hS g).obj F).IsFiniteTypeOnSite ∧
      ((modulePullback B S hS (restrictOverι (g ≫ f) U)).obj
        ((modulePullback B S hS g).obj F)).IsFinitePresentationOnSite ∧
      IsFlatOver B S hS (restrictOver (g ≫ f) U).2 (restrictOverHom (g ≫ f) U).hom
        ((modulePullback B S hS (restrictOverι (g ≫ f) U)).obj
          ((modulePullback B S hS g).obj F)) := by
  have sq := isPullback_restrictOverMap g f U
  obtain ⟨hgU, hgUs⟩ := isEtale_and_isSurjective_of_isPullback sq hg hgs
  have e := restrictOverModuleIso g f U F
  refine ⟨isLocallyOfFinitePresentation_comp B S hS V.2 X.2 A.2 _ _
      (isLocallyOfFinitePresentation_of_isEtale B S hS hg) hf,
    isQuasicoherentOnSite_modulePullback_of_isEtale B S hS g hg F hFqc,
    isFiniteTypeOnSite_modulePullback B S hS g F hFft,
    SheafOfModules.IsFinitePresentationOnSite.of_iso e.symm
      (isFinitePresentationOnSite_modulePullback B S hS _ _ hFUfp), ?_⟩
  have hqc : ((modulePullback B S hS (restrictOverι f U)).obj F).IsQuasicoherentOnSite :=
    have := hFUfp
    inferInstance
  have := hqc
  refine (isFlatOver_iff_of_iso B S hS _ _ e).2 ?_
  rw [← restrictOverMap_hom]
  exact (isFlatOver_modulePullback_iff_of_isSurjective_of_isFlat B S hS _ _ _ hgUs
    (isFlat_of_isEtale B S hS hgU)).1 hFUflat

/-- **Stacks 087C reduces to a source which is a scheme.**  Suppose the conclusion of Stacks
087C holds, over the base `A` and the open `U`, for every morphism from a quasi-compact scheme
satisfying its hypotheses.  Then it holds for every `f : X ⟶ A` with `X` quasi-compact
satisfying its hypotheses: a quasi-compact algebraic space has a surjective étale chart by a
quasi-compact scheme, the hypotheses pass to the chart
(`AlgebraicGeometry.Space.flatteningHypotheses_comp_etale`), and a flattening blowup for the
chart is one for `X` (`AlgebraicGeometry.Space.IsFlatteningBlowup.of_comp_etale`).

This is the first paragraph of the proof of Stacks 087C. -/
theorem exists_isFlatteningBlowup_of_isRepresentableSpace_source
    (U : OpenSubspaces B S hS A.1)
    (hrep : ∀ (V : AlgebraicSpaces B S hS) (f' : V ⟶ A) (G : Modules.{u, u} B S hS V.1 V.2),
      IsRepresentableSpace B S hS V → IsQuasiCompactSpace B S hS V.1 →
      IsLocallyOfFinitePresentation B S hS f'.hom → G.IsQuasicoherentOnSite →
      G.IsFiniteTypeOnSite →
      ((modulePullback B S hS (restrictOverι f' U)).obj G).IsFinitePresentationOnSite →
      IsFlatOver B S hS (restrictOver f' U).2 (restrictOverHom f' U).hom
        ((modulePullback B S hS (restrictOverι f' U)).obj G) →
      ∃ (Z : ClosedSubspaces B S hS A.1) (A' : AlgebraicSpaces B S hS) (b : A' ⟶ A),
        IsFlatteningBlowup f' G U Z b)
    (f : X ⟶ A) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hf : IsLocallyOfFinitePresentation B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hFqc : F.IsQuasicoherentOnSite)
    (hFft : F.IsFiniteTypeOnSite)
    (hFUfp : ((modulePullback B S hS (restrictOverι f U)).obj F).IsFinitePresentationOnSite)
    (hFUflat : IsFlatOver B S hS (restrictOver f U).2 (restrictOverHom f U).hom
      ((modulePullback B S hS (restrictOverι f U)).obj F)) :
    ∃ (Z : ClosedSubspaces B S hS A.1) (A' : AlgebraicSpaces B S hS) (b : A' ⟶ A),
      IsFlatteningBlowup f F U Z b := by
  obtain ⟨V₀, a, hcpt, hsurj, het⟩ := hXqc
  let V : AlgebraicSpaces B S hS := ⟨yoneda.obj V₀, isAlgebraicSpace_yoneda B S hS V₀⟩
  let g : V ⟶ X := ObjectProperty.homMk a
  have hgs : IsSurjective B S hS g.hom :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS X.1 X.2 V₀ a).1 hsurj
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    flatteningHypotheses_comp_etale g het hgs f hf F hFqc hFft U hFUfp hFUflat
  obtain ⟨Z, A', b, hb⟩ := hrep V (g ≫ f) ((modulePullback B S hS g).obj F)
    ⟨V₀, ⟨Iso.refl _⟩⟩ (isQuasiCompactSpace_yoneda B S hS V₀ hcpt) h1 h2 h3 h4 h5
  exact ⟨Z, A', b, hb.of_comp_etale g het hgs⟩

end AlgebraicGeometry.Space

end
