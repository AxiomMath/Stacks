module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStack
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatDimensionStagePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.RetractionReductionExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismToAffineScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleChartDiagramSectionsCriterion
public import StacksFrontier.RingTheory.SplitPushoutKernel
public import StacksFrontier.RingTheory.Flat.SquareZeroRelation

/-!
# Base change of `Coh_{X/Y}` along a split square-zero thickening of test schemes

Let `D` be the situation of Stacks 08KB, `T₀` and `T₁` affine test schemes over `Y` and
`π : T₁ ⟶ T₀`, `β : T₀ ⟶ T₁` morphisms of test schemes with `β ≫ π = 𝟙`. Let `ι₀` be a family of
functions on `T₁`, indexed additively by a `k`-vector space `M`, generating the kernel of the
pullback of functions along `β`, with vanishing pairwise products and `k`-linear for the scalars
`k ⟶ Γ(T₀) ⟶ Γ(T₁)`. This is the shape of `T₁ = Spec k[M]` over `T₀ = Spec k`.

Then the base change `X_{T₁}` is a split square-zero thickening of `X_{T₀}` in the sense of
`AlgebraicGeometry.Space.IsSplitThickeningBy`, with retraction `X_π`, section `X_β` and the
pullbacks of the `ι₀ v` as square-zero functions; and a module on `X_{T₁}` which is flat over
`T₁` satisfies the flatness hypothesis of `AlgebraicGeometry.Space.retractionCopowerExtension`.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.isSplitThickeningBy`: `X_{T₁}` is a split
  square-zero thickening of `X_{T₀}`.
* `AlgebraicGeometry.Space.CoherentSituation.splitFlat_of_isFlatOver`: a module on `X_{T₁}`
  flat over `T₁` satisfies the flatness hypothesis of
  `AlgebraicGeometry.Space.retractionCopowerExtension`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

namespace CoherentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : CoherentSituation B S hS) {T₀ T₁ : SchemesOver D.Y} (π : T₁ ⟶ T₀) (β : T₀ ⟶ T₁)
  (hβπ : β ≫ π = 𝟙 T₀)

/-- The global functions of a test scheme. -/
abbrev testRing (T : SchemesOver D.Y) : CommRingCat.{u} :=
  Γ((BigFppfOver.toScheme B S hS).obj T.left, ⊤)

/-- Pullback of functions along a morphism of the site. -/
abbrev siteΓ {A A' : BigFppfOver B S hS} (g : A ⟶ A') :
    Γ((BigFppfOver.toScheme B S hS).obj A', ⊤) ⟶ Γ((BigFppfOver.toScheme B S hS).obj A, ⊤) :=
  ((BigFppfOver.toScheme B S hS).map g).appTop

/-- Pullback of functions along a composite is the composite of the pullbacks. -/
theorem siteΓ_comp {A A' A'' : BigFppfOver B S hS} (g : A ⟶ A') (g' : A' ⟶ A'') :
    siteΓ (g ≫ g') = siteΓ g' ≫ siteΓ g := by
  rw [siteΓ, Functor.map_comp, Scheme.Hom.comp_appTop]

/-- Pullback of functions along the identity is the identity. -/
theorem siteΓ_id (A : BigFppfOver B S hS) : siteΓ (𝟙 A) = 𝟙 _ := by
  rw [siteΓ, CategoryTheory.Functor.map_id, Scheme.Hom.id_appTop]

/-- The representability of the morphism of base changes along `π`. -/
abbrev splitRep : yoneda.relativelyRepresentable (D.relativeMap π).hom :=
  relativelyRepresentable_baseChangeMap B S hS D.f π

include hβπ in
/-- The base change of `β` followed by the base change of `π` is the identity of `X_{T₀}`. -/
theorem relativeMap_comp_relativeMap_eq_id : D.relativeMap β ≫ D.relativeMap π = 𝟙 _ := by
  rw [← baseChangeMap_comp, hβπ, baseChangeMap_id]

/-- The morphism of the site from a chart of `X_T` to `T`. -/
def chartToTest (T : SchemesOver D.Y) (U : SmallEtale B S hS (D.space T).1) :
    U.1.left ⟶ T.left :=
  (identityTargetChartDiagram B S hS (D.projection T) U).g

/-- Under the Yoneda embedding, `chartToTest T U` is the structure map of the chart `U` followed
by the projection `X_T ⟶ T`. -/
theorem yoneda_map_chartToTest (T : SchemesOver D.Y) (U : SmallEtale B S hS (D.space T).1) :
    yoneda.map (D.chartToTest T U) = U.1.hom ≫ (D.projection T).hom :=
  yoneda_map_identityTargetChartDiagram_g B S hS (D.projection T) U

/-- The morphism of the site from a base-changed chart of `X_{T₁}` to `T₁`, typed at the
representable pullback. -/
def splitChartToTest (U : SmallEtale B S hS (D.space T₀).1) :
    (D.splitRep π).pullback U.1.hom ⟶ T₁.left :=
  D.chartToTest T₁ ((smallBaseChange B S hS (D.relativeMap π) (D.splitRep π)).obj U)

/-- Under the Yoneda embedding, `splitChartToTest π U` is the first projection of the pullback
followed by the projection `X_{T₁} ⟶ T₁`. -/
theorem yoneda_map_splitChartToTest (U : SmallEtale B S hS (D.space T₀).1) :
    yoneda.map (D.splitChartToTest π U) = (D.splitRep π).fst U.1.hom ≫ (D.projection T₁).hom :=
  D.yoneda_map_chartToTest T₁ _

/-- The base-changed chart of `X_{T₁}` is the fibre product of the chart of `X_{T₀}` with `T₁`
over `T₀`, as schemes. -/
theorem isPullback_splitChart (U : SmallEtale B S hS (D.space T₀).1) :
    IsPullback
      ((BigFppfOver.toScheme B S hS).map ((D.splitRep π).snd U.1.hom))
      ((BigFppfOver.toScheme B S hS).map (D.splitChartToTest π U))
      ((BigFppfOver.toScheme B S hS).map (D.chartToTest T₀ U))
      ((BigFppfOver.toScheme B S hS).map π.left) :=
  isPullback_chartScheme_stageChart B S hS D.f π U

/-- The chart map `U ⟶ U ×_{X_{T₀}} X_{T₁}` of the section, followed by the map to `T₁`, is the
map to `T₀` followed by `β`. -/
theorem retractionChartMap_comp_chartToTest (U : SmallEtale B S hS (D.space T₀).1) :
    retractionChartMap B S hS (D.relativeMap π) (D.splitRep π) (D.relativeMap β)
        (D.relativeMap_comp_relativeMap_eq_id π β hβπ) U ≫ D.splitChartToTest π U =
    D.chartToTest T₀ U ≫ β.left := by
  apply yoneda.map_injective
  rw [Functor.map_comp, Functor.map_comp, yoneda_map_splitChartToTest, yoneda_map_chartToTest]
  have hcomp : (D.relativeMap β).hom ≫ (D.projection T₁).hom =
      (D.projection T₀).hom ≫ yoneda.map β.left :=
    congrArg (fun f => f.hom) (baseChangeMap_comp_inclusion D.f β)
  have hfst := retractionChartMap_fst B S hS (D.relativeMap π) (D.splitRep π) (D.relativeMap β)
    (D.relativeMap_comp_relativeMap_eq_id π β hβπ) U
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (D.projection T₁).hom) hfst).trans
    ((Category.assoc _ _ _).trans ((congrArg (U.1.hom ≫ ·) hcomp).trans
      (Category.assoc _ _ _).symm)))

variable {k : Type u} [Field k] (M : FGModuleCat.{u} k)
  (ε : k →+* D.testRing T₀) (ι₀ : ↥M →+ D.testRing T₁)

/-- The scalars of `X_{T₀}`: the pullbacks of `ε`. -/
abbrev splitScalars₀ : k →+* Stacks.Cohomology.SiteModules.GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (D.space T₀).1
      (D.space T₀).2).O) :=
  (pullbackToGlobalFunctions B S hS (D.space T₀) T₀.left (D.projection T₀)).comp ε

/-- The scalars of `X_{T₁}`: the pullbacks of `ε` along `π`. -/
abbrev splitScalars₁ : k →+* Stacks.Cohomology.SiteModules.GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (D.space T₁).1
      (D.space T₁).2).O) :=
  (pullbackToGlobalFunctions B S hS (D.space T₁) T₁.left (D.projection T₁)).comp
    ((siteΓ π.left).hom.comp ε)

/-- The square-zero functions on `X_{T₁}`: the pullbacks of the `ι₀ v`. -/
abbrev splitFunctions : ↥M →+ Stacks.Cohomology.SiteModules.GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (D.space T₁).1
      (D.space T₁).2).O) :=
  (pullbackToGlobalFunctions B S hS (D.space T₁) T₁.left (D.projection T₁)).toAddMonoidHom.comp ι₀

/-- The section of `splitFunctions M ι₀ v` on a chart `U` of `X_{T₁}` is the pullback of `ι₀ v`
along `chartToTest T₁ U`. -/
theorem splitFunctions_app (v : ↥M) (U : SmallEtale B S hS (D.space T₁).1) :
    (D.splitFunctions M ι₀ v).1 (op U) = (siteΓ (D.chartToTest T₁ U)).hom (ι₀ v) := rfl

/-- The section on a chart `U` of `X_T` of the pullback of a function `x` on `T` is the pullback
of `x` along `chartToTest T U`. -/
theorem pullbackToGlobalFunctions_app (T : SchemesOver D.Y) (x : D.testRing T)
    (U : SmallEtale B S hS (D.space T).1) :
    (pullbackToGlobalFunctions B S hS (D.space T) T.left (D.projection T) x).1 (op U) =
      (siteΓ (D.chartToTest T U)).hom x := rfl

/-- Restriction along the chart map of the section of the pullback of a function on `T₁` is the
pullback along `β` of that function, pulled back to the chart. -/
theorem chartDiagramRestrict_retraction_siteΓ (U : SmallEtale B S hS (D.space T₀).1)
    (x : D.testRing T₁) :
    chartDiagramRestrict B S hS (D.relativeMap β)
        (retractionChartDiagram B S hS (D.relativeMap π) (D.splitRep π) (D.relativeMap β)
          (D.relativeMap_comp_relativeMap_eq_id π β hβπ) U)
        ((siteΓ (D.splitChartToTest π U)).hom x) =
      (siteΓ (D.chartToTest T₀ U)).hom ((siteΓ β.left).hom x) := by
  have h := congrArg (fun g => (siteΓ g).hom x) (D.retractionChartMap_comp_chartToTest π β hβπ U)
  rw [siteΓ_comp, siteΓ_comp] at h
  exact h

variable (hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀.left))
  (hT₁ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₁.left))

include hT₀ hT₁ in
/-- The base-changed charts of affine charts are affine. -/
theorem isAffine_splitChart (U : SmallEtale B S hS (D.space T₀).1)
    (hU : IsAffine ((SmallEtale.toOver B S hS (D.space T₀).1 ⋙ BigFppfOver.toScheme B S hS).obj
      U)) :
    IsAffine ((SmallEtale.toOver B S hS (D.space T₁).1 ⋙ BigFppfOver.toScheme B S hS).obj
      ((smallBaseChange B S hS (D.relativeMap π) (D.splitRep π)).obj U)) := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left) := hU
  have := hT₁
  have := hT₀
  exact IsAffine.of_isPullback (D.isPullback_splitChart π U)

variable (h₁ : ∀ v, (siteΓ β.left).hom (ι₀ v) = 0)
  (h₂ : RingHom.ker (siteΓ β.left).hom = Ideal.span (Set.range ι₀))
  (h₃ : ∀ v w, ι₀ v * ι₀ w = 0)
  (h₄ : ∀ (c : k) (v : ↥M), ι₀ (c • v) = (siteΓ π.left).hom (ε c) * ι₀ v)

include hT₀ hT₁ h₂ in
/-- **The ideal of the special fibre on a base-changed affine chart** is generated by the
pullbacks of the `ι₀ v`. -/
theorem ker_chartDiagramRestrict_split (U : SmallEtale B S hS (D.space T₀).1)
    (hU : IsAffine ((SmallEtale.toOver B S hS (D.space T₀).1 ⋙ BigFppfOver.toScheme B S hS).obj
      U)) :
    RingHom.ker (chartDiagramRestrict B S hS (D.relativeMap β)
        (retractionChartDiagram B S hS (D.relativeMap π) (D.splitRep π) (D.relativeMap β)
          (D.relativeMap_comp_relativeMap_eq_id π β hβπ) U)) =
      Ideal.span (Set.range fun v : ↥M => (D.splitFunctions M ι₀ v).1
        (op ((smallBaseChange B S hS (D.relativeMap π) (D.splitRep π)).obj U))) := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left) := hU
  have := hT₁
  have := hT₀
  have hpo := isPushout_appTop_of_isPullback (D.isPullback_splitChart π U)
  have hβπ' : (siteΓ π.left) ≫ (siteΓ β.left) = 𝟙 _ := by
    rw [← siteΓ_comp, show β.left ≫ π.left = 𝟙 _ from congrArg CommaMorphism.left hβπ, siteΓ_id]
  let ρ := retractionChartMap B S hS (D.relativeMap π) (D.splitRep π) (D.relativeMap β)
    (D.relativeMap_comp_relativeMap_eq_id π β hβπ) U
  have hgl : siteΓ ((D.splitRep π).snd U.1.hom) ≫ siteΓ ρ = 𝟙 _ := by
    rw [← siteΓ_comp, retractionChartMap_snd, siteΓ_id]
  have hgr : siteΓ (D.splitChartToTest π U) ≫ siteΓ ρ =
      siteΓ β.left ≫ siteΓ (D.chartToTest T₀ U) := by
    rw [← siteΓ_comp, ← siteΓ_comp, D.retractionChartMap_comp_chartToTest π β hβπ U]
  have key := RingHom.ker_eq_span_of_isPushout_of_retraction hpo (siteΓ β.left) hβπ' (siteΓ ρ)
    hgl hgr (Set.range ι₀) h₂
  refine key.trans ?_
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    exact ⟨v, rfl⟩
  · rintro ⟨v, rfl⟩
    exact ⟨ι₀ v, ⟨v, rfl⟩, rfl⟩

include hT₀ hT₁ h₁ h₂ h₃ h₄ in
/-- **`X_{T₁}` is a split square-zero thickening of `X_{T₀}`.** -/
theorem isSplitThickeningBy :
    IsSplitThickeningBy B S hS (D.relativeMap π) (D.splitRep π) (D.relativeMap β)
      (D.relativeMap_comp_relativeMap_eq_id π β hβπ) M (D.splitScalars₀ ε)
      (D.splitScalars₁ π ε) (D.splitFunctions M ι₀) where
  isAffine U hU := D.isAffine_splitChart π hT₀ hT₁ U hU
  surjective U _ a := ⟨(smallBaseChangeSharp B S hS (D.relativeMap π) (D.splitRep π)).hom.app
      (op U) a,
    chartDiagramRestrict_retractionChartDiagram_smallBaseChangeSharp B S hS _ _ _ _ U a⟩
  ker_eq U hU := D.ker_chartDiagramRestrict_split π β hβπ M ι₀ hT₀ hT₁ h₂ U hU
  mul_eq_zero v w := by
    show pullbackToGlobalFunctions B S hS (D.space T₁) T₁.left (D.projection T₁) (ι₀ v) *
      pullbackToGlobalFunctions B S hS (D.space T₁) T₁.left (D.projection T₁) (ι₀ w) = 0
    rw [← map_mul, h₃, map_zero]
  map_smul c v := by
    show pullbackToGlobalFunctions B S hS (D.space T₁) T₁.left (D.projection T₁) (ι₀ (c • v)) =
      pullbackToGlobalFunctions B S hS (D.space T₁) T₁.left (D.projection T₁)
        ((siteΓ π.left).hom (ε c)) *
      pullbackToGlobalFunctions B S hS (D.space T₁) T₁.left (D.projection T₁) (ι₀ v)
    rw [← map_mul, h₄]
  scalars c U := by
    have hw := congrArg (fun g => g.appTop.hom (ε c)) (D.isPullback_splitChart π U).w
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at hw
    exact hw.symm

/-! ### Flatness -/

section Flat

variable (ρ' : D.testRing T₁ →+* k) (hinj : Function.Injective ι₀)
  (hmul : ∀ (v : ↥M) (a : D.testRing T₁), ι₀ v * a = ι₀ (ρ' a • v))
  (hker : ∀ a, ρ' a = 0 → (siteΓ β.left).hom a = 0)

include hT₀ hT₁ hinj hmul hker in
/-- **A module on `X_{T₁}` flat over `T₁` satisfies the flatness hypothesis of
`AlgebraicGeometry.Space.retractionCopowerExtension`.** -/
theorem splitFlat_of_isFlatOver (F : Modules.{u, u} B S hS (D.space T₁).1 (D.space T₁).2)
    (hF : F.IsQuasicoherentOnSite)
    (hflat : IsFlatOver B S hS (D.space T₁).2 (D.projection T₁).hom F)
    (U : SmallEtale B S hS (D.space T₀).1)
    (hU : IsAffine ((SmallEtale.toOver B S hS (D.space T₀).1 ⋙ BigFppfOver.toScheme B S hS).obj
      U))
    (n : Fin (Module.finrank k M) → F.val.obj (op (retractionChartDiagram B S hS (D.relativeMap π)
      (D.splitRep π) (D.relativeMap β) (D.relativeMap_comp_relativeMap_eq_id π β hβπ) U).V))
    (hn : ∑ j, (D.splitFunctions M ι₀ (Deformation.ModuleDeformation.stdBasis M j)).1
        (op (retractionChartDiagram B S hS (D.relativeMap π) (D.splitRep π) (D.relativeMap β)
          (D.relativeMap_comp_relativeMap_eq_id π β hβπ) U).V) • n j = 0) (j : Fin _) :
    n j ∈ (RingHom.ker (chartDiagramRestrict B S hS (D.relativeMap β)
        (retractionChartDiagram B S hS (D.relativeMap π) (D.splitRep π) (D.relativeMap β)
          (D.relativeMap_comp_relativeMap_eq_id π β hβπ) U))) •
      (⊤ : Submodule (chartRing B S hS (D.space T₁).1 (D.space T₁).2
          (retractionChartDiagram B S hS (D.relativeMap π) (D.splitRep π) (D.relativeMap β)
            (D.relativeMap_comp_relativeMap_eq_id π β hβπ) U).V)
        (F.val.obj (op (retractionChartDiagram B S hS (D.relativeMap π) (D.splitRep π)
          (D.relativeMap β) (D.relativeMap_comp_relativeMap_eq_id π β hβπ) U).V))) := by
  let U' := (smallBaseChange B S hS (D.relativeMap π) (D.splitRep π)).obj U
  have hU' := D.isAffine_splitChart π hT₀ hT₁ U hU
  let d' := identityTargetChartDiagram B S hS (D.projection T₁) U'
  have hfl := (isFlatOverOnChartDiagram_iff_flat_sections B S hS (D.projection T₁) F hF d' hU'
    hT₁).1 (hflat d')
  let : Module Γ(chartScheme d'.V, ⊤) (F.val.obj (op d'.U)) :=
    Module.compHom _ ((BigFppfOver.toScheme B S hS).map d'.g).appTop.hom
  have : Module.Flat Γ(chartScheme d'.V, ⊤) (F.val.obj (op d'.U)) := hfl
  let ρ'' : Γ(chartScheme d'.V, ⊤) →+* k := ρ'
  let ι₀' : ↥M →+ Γ(chartScheme d'.V, ⊤) := ι₀
  have hmul' : ∀ (v : ↥M) (a : Γ(chartScheme d'.V, ⊤)), ι₀' v * a = ι₀' (ρ'' a • v) := hmul
  let n' : Fin (Module.finrank k M) → F.val.obj (op d'.U) := n
  have hn' : ∑ j, ι₀' (Deformation.ModuleDeformation.stdBasis M j) • n' j = 0 := hn
  have hmem := Module.Flat.mem_ker_smul_top_of_sum_smul_eq_zero ρ'' ι₀' hinj hmul'
    (Deformation.ModuleDeformation.stdBasis M) n' hn' j
  refine Submodule.smul_induction_on (p := fun (x : F.val.obj (op d'.U)) =>
    x ∈ (RingHom.ker (chartDiagramRestrict B S hS
      (D.relativeMap β) (retractionChartDiagram B S hS (D.relativeMap π) (D.splitRep π)
        (D.relativeMap β) (D.relativeMap_comp_relativeMap_eq_id π β hβπ) U))) •
      (⊤ : Submodule (chartRing B S hS (D.space T₁).1 (D.space T₁).2
          (retractionChartDiagram B S hS (D.relativeMap π) (D.splitRep π) (D.relativeMap β)
            (D.relativeMap_comp_relativeMap_eq_id π β hβπ) U).V)
        (F.val.obj (op (retractionChartDiagram B S hS (D.relativeMap π) (D.splitRep π)
          (D.relativeMap β) (D.relativeMap_comp_relativeMap_eq_id π β hβπ) U).V)))) hmem ?_ ?_
  · intro r hr m _
    have hr' : chartDiagramRestrict B S hS (D.relativeMap β)
        (retractionChartDiagram B S hS (D.relativeMap π) (D.splitRep π) (D.relativeMap β)
          (D.relativeMap_comp_relativeMap_eq_id π β hβπ) U)
        ((siteΓ (D.splitChartToTest π U)).hom r) = 0 := by
      rw [D.chartDiagramRestrict_retraction_siteΓ π β hβπ U r, hker r (RingHom.mem_ker.mp hr)]
      exact map_zero _
    let m' : F.val.obj (op (retractionChartDiagram B S hS (D.relativeMap π) (D.splitRep π)
        (D.relativeMap β) (D.relativeMap_comp_relativeMap_eq_id π β hβπ) U).V) := m
    let r' : chartRing B S hS (D.space T₁).1 (D.space T₁).2
        (retractionChartDiagram B S hS (D.relativeMap π) (D.splitRep π) (D.relativeMap β)
          (D.relativeMap_comp_relativeMap_eq_id π β hβπ) U).V :=
      (siteΓ (D.splitChartToTest π U)).hom r
    have key : r' • m' ∈ (RingHom.ker (chartDiagramRestrict B S hS
        (D.relativeMap β) (retractionChartDiagram B S hS (D.relativeMap π) (D.splitRep π)
          (D.relativeMap β) (D.relativeMap_comp_relativeMap_eq_id π β hβπ) U))) •
        (⊤ : Submodule (chartRing B S hS (D.space T₁).1 (D.space T₁).2
            (retractionChartDiagram B S hS (D.relativeMap π) (D.splitRep π) (D.relativeMap β)
              (D.relativeMap_comp_relativeMap_eq_id π β hβπ) U).V)
          (F.val.obj (op (retractionChartDiagram B S hS (D.relativeMap π) (D.splitRep π)
            (D.relativeMap β) (D.relativeMap_comp_relativeMap_eq_id π β hβπ) U).V))) :=
      Submodule.smul_mem_smul (RingHom.mem_ker.mpr hr') Submodule.mem_top
    exact key
  · intro x y hx hy
    exact Submodule.add_mem _ hx hy

end Flat

end CoherentSituation

end AlgebraicGeometry.Space

end
