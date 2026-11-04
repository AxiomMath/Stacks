module

public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorAffineSpaceChartsRepresentable
public import StacksFrontier.AlgebraicGeometry.Picard.SymmetricPower.ChartScheme
public import StacksFrontier.AlgebraicGeometry.Picard.SymmetricPower.OpenSubfunctor
import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitEqualizerTorsion

/-!
# The chart schemes of the Hilbert scheme of points of an affine scheme

Let `X ⟶ S` be a morphism of affine schemes and `w : Fin d → Γ(X)`. The chart scheme
`C_w = Spec (chartRing Γ(S) w)` carries a universal family, and so a morphism
`yoneda C_w ⟶ hilbPresheaf X d`. This file shows that, over an affine base, the sections in its
image are the families lying in the chart, and that the morphism is injective on sections over
affine schemes.

## Main definitions

* `Stacks.Hilbert.Chart.chartScheme`, `Stacks.Hilbert.Chart.chartStructure`: the chart.
* `Stacks.Hilbert.Chart.universalFamily`: its universal family.
* `Stacks.Hilbert.Chart.chartMap`: the morphism `yoneda C_w ⟶ hilbPresheaf X d`.

## Main results

* `Stacks.Hilbert.Chart.exists_chartMap_iff_isChart`: over an affine base, a section is in the
  image of the chart exactly when its family lies in the chart.
* `Stacks.Hilbert.Chart.chartMap_injective_of_isAffine`: the chart is injective on sections
  over affine schemes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct

universe u

namespace Stacks.Hilbert.Chart

variable {S : Scheme.{u}} [IsAffine S] {X : Over S} [IsAffine X.left] {d : ℕ}
  (w : Fin d → Γ(X.left, ⊤))

attribute [local instance] baseAlgebra

/-- The coordinate ring of the chart, as a commutative ring. -/
abbrev chartRingCat : CommRingCat.{u} := CommRingCat.of (chartRing Γ(S, ⊤) w)

/-- The chart scheme `Spec (chartRing Γ(S) w)`. -/
abbrev chartScheme : Scheme.{u} := Spec (chartRingCat w)

/-- The structure morphism of the chart scheme to `S`. -/
def chartStructure : chartScheme w ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) (chartRing Γ(S, ⊤) w))) ≫ S.isoSpec.inv

/-- The chart scheme as an `S`-scheme. -/
abbrev chartOver : Over S := Over.mk (chartStructure w)

/-- On global sections, `Spec.map φ` corresponds to `φ` under the isomorphisms `Γ(Spec R) ≅ R`. -/
alias SpecMap_appTop_apply := AlgebraicGeometry.Scheme.appTop_specMap_ΓSpecIso_inv_apply

omit [IsAffine X.left] in
/-- On global sections, the structure morphism of the chart scheme is the algebra map
`Γ(S) → chartRing Γ(S) w`. -/
theorem chartStructure_appTop_apply (r : Γ(S, ⊤)) :
    (chartStructure w).appTop r =
      (Scheme.ΓSpecIso (chartRingCat w)).inv (algebraMap Γ(S, ⊤) (chartRing Γ(S, ⊤) w) r) := by
  rw [chartStructure, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    Stacks.Hilbert.isoSpec_inv_appTop_apply]
  exact SpecMap_appTop_apply (CommRingCat.ofHom (algebraMap Γ(S, ⊤) (chartRing Γ(S, ⊤) w))) r

/-- The identification of the coordinate ring of the chart with the global sections of the chart
scheme, as a map of `Γ(S)`-algebras. -/
def chartRingAlgHom :
    chartRing Γ(S, ⊤) w →ₐ[Γ(S, ⊤)] Γ((chartOver w).left, ⊤) where
  toRingHom := (Scheme.ΓSpecIso (chartRingCat w)).inv.hom
  commutes' r := (chartStructure_appTop_apply w r).symm

omit [IsAffine X.left] in
/-- The map `chartRingAlgHom w` is bijective. -/
theorem chartRingAlgHom_bijective : Function.Bijective (chartRingAlgHom w) :=
  ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (chartRingCat w)).inv

/-- The chart scheme is affine. -/
instance : IsAffine (chartOver w).left := inferInstanceAs (IsAffine (chartScheme w))

omit [IsAffine X.left] in
/-- The universal coordinates, transported to the global sections of the chart scheme, form a chart
function. -/
theorem isChartFunction_universal :
    IsChartFunction Γ(S, ⊤) w fun l a => chartRingAlgHom w (tUniv Γ(S, ⊤) w l a) :=
  isChartFunction_comp (chartRingAlgHom w)

/-- **The universal family over the chart scheme.** -/
def universalFamily : HilbertFamily X (chartOver w) d :=
  chartFamily X w (chartOver w) (isChartFunction_universal w)

/-- **The chart**, as a morphism `yoneda C_w ⟶ hilbPresheaf X d`. -/
def chartMap : yoneda.obj (chartScheme w) ⟶ hilbPresheaf X d :=
  yonedaEquiv.symm ⟨chartStructure w, universalFamily w⟩

/-- The section classified by a morphism to the chart scheme, over a given structure morphism. -/
theorem chartMap_app_eq {T : Scheme.{u}} (c : T ⟶ chartScheme w) (s : T ⟶ S)
    (e : c ≫ chartStructure w = s) :
    (chartMap w).app (op T) c =
      ⟨s, baseChange X (Over.homMk c e : Over.mk s ⟶ chartOver w) (universalFamily w)⟩ := by
  show (hilbPresheaf X d).map c.op ⟨chartStructure w, universalFamily w⟩ = _
  show (⟨c ≫ chartStructure w, familyPullback X d c rfl (universalFamily w)⟩ :
    HilbSections X d T) = _
  rw [sigma_eq_iff]
  refine ⟨e, ?_⟩
  rw [baseChange_ideal, familyPullback_ideal, ← Scheme.IdealSheafData.comap_comp,
    familyBaseChangeMap_comp_homMk (hab := by simpa using e)]
  exact congrArg _ (familyBaseChangeMap_homMk_congr X (Category.id_comp c).symm _ _)

/-- The source of `Over.mk s` is affine when `T` is. -/
instance isAffine_over_mk_left {T : Scheme.{u}} [IsAffine T] (s : T ⟶ S) :
    IsAffine (Over.mk s).left :=
  ‹IsAffine T›

/-- The family `chartFamily X w T ht` depends only on the chart function `t`. -/
theorem chartFamily_congr (T : Over S) [IsAffine T.left]
    {t t' : Fin d → Γ(X.left, ⊤) → Γ(T.left, ⊤)} (ht : IsChartFunction Γ(S, ⊤) w t)
    (e : t = t') : chartFamily X w T ht = chartFamily X w T (e ▸ ht) := by
  subst e
  rfl

/-- The base change of the universal family along `g : T ⟶ C_w` is the chart family of the
composite of `chartRingAlgHom w` with the map `g` induces on global sections. -/
theorem baseChange_universalFamily {T : Over S} [IsAffine T.left] (g : T ⟶ chartOver w) :
    baseChange X g (universalFamily w) = chartFamily X w T
      (isChartFunction_comp ((appTopAlgHom g).comp (chartRingAlgHom w))) := by
  rw [universalFamily, baseChange_chartFamily]
  rfl

/-- The morphism to the chart scheme defined by a ring map out of the chart ring. -/
def chartPoint {T : Scheme.{u}} (φ : chartRingCat w ⟶ Γ(T, ⊤)) : T ⟶ chartScheme w :=
  T.toSpecΓ ≫ Spec.map φ

omit [IsAffine S] [IsAffine X.left] in
/-- On global sections, `chartPoint w φ` is `φ`. -/
theorem chartPoint_appTop_apply {T : Scheme.{u}} (φ : chartRingCat w ⟶ Γ(T, ⊤))
    (x : chartRing Γ(S, ⊤) w) :
    (chartPoint w φ).appTop ((Scheme.ΓSpecIso (chartRingCat w)).inv x) = φ x := by
  rw [chartPoint, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, SpecMap_appTop_apply,
    Scheme.toSpecΓ_appTop]
  exact Iso.inv_hom_id_apply _ _

/-- A section in the image of the chart over a point `c` has the base change of the universal
family along `c` as its family. -/
private theorem exists_baseChange_universalFamily_eq {T : Scheme.{u}} (c : T ⟶ chartScheme w)
    {s : T ⟶ S} {Z : HilbertFamily X (Over.mk s) d}
    (h : (chartMap w).app (op T) c = ⟨s, Z⟩) :
    ∃ e : c ≫ chartStructure w = s,
      baseChange X (Over.homMk c e : Over.mk s ⟶ chartOver w) (universalFamily w) = Z := by
  have e : c ≫ chartStructure w = s :=
    congrArg Sigma.fst ((chartMap_app_eq w c _ rfl).symm.trans h)
  rw [chartMap_app_eq w c s e] at h
  exact ⟨e, eq_of_heq (Sigma.mk.inj_iff.mp h).2⟩

/-- **Over an affine base, the image of the chart consists of the families in the chart.** -/
theorem inImage_chartMap_iff {T : Scheme.{u}} [IsAffine T] (s : T ⟶ S)
    (Z : HilbertFamily X (Over.mk s) d) :
    InImage (chartMap w) (⟨s, Z⟩ : (hilbPresheaf X d).obj (op T)) ↔ IsChart w Z := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨e, hZ⟩ := exists_baseChange_universalFamily_eq w c hc
    rw [← hZ, baseChange_universalFamily]
    exact isChart_chartFamily X w _ _
  · intro h
    let t := chartFunctionOf w h
    have ht := isChartFunction_chartFunctionOf X w h
    let φ := lift ht
    let c : T ⟶ chartScheme w := chartPoint w (T := T) (CommRingCat.ofHom φ.toRingHom)
    have e : c ≫ chartStructure w = s := by
      apply ext_of_isAffine
      ext r
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, chartStructure_appTop_apply,
        chartPoint_appTop_apply]
      exact φ.commutes r
    refine ⟨c, ?_⟩
    rw [chartMap_app_eq w c s e, baseChange_universalFamily]
    congr 1
    conv_rhs => rw [← chartFamily_chartFunctionOf X w h]
    refine (chartFamily_congr w _ _ ?_).trans rfl
    funext l a
    show c.appTop ((Scheme.ΓSpecIso (chartRingCat w)).inv (tUniv Γ(S, ⊤) w l a)) = t l a
    rw [chartPoint_appTop_apply]
    exact lift_tUniv ht l a

/-- **The chart is injective on sections over affine schemes.** -/
theorem chartMap_injective_of_isAffine (T : Scheme.{u}) [IsAffine T] :
    Function.Injective ((chartMap w).app (op T)) := by
  intro c c' h
  let s := c ≫ chartStructure w
  obtain ⟨e', hZ⟩ := exists_baseChange_universalFamily_eq w c'
    (h.symm.trans (chartMap_app_eq w c s rfl))
  rw [baseChange_universalFamily, baseChange_universalFamily] at hZ
  have hk := congrArg familyKernel hZ.symm
  rw [familyKernel_chartFamily, familyKernel_chartFamily] at hk
  have ht := eq_of_chartIdeal_eq (isChartFunction_comp _) hk
  have hφ : (appTopAlgHom (Over.homMk c rfl : Over.mk s ⟶ chartOver w)).comp (chartRingAlgHom w) =
      (appTopAlgHom (Over.homMk c' e' : Over.mk s ⟶ chartOver w)).comp (chartRingAlgHom w) :=
    algHom_ext fun l a => congrFun (congrFun ht l) a
  exact ext_of_isAffine ((cancel_epi (Scheme.ΓSpecIso (chartRingCat w)).inv).mp
    (CommRingCat.hom_ext (RingHom.ext fun x => congrArg (fun ψ => ψ x) hφ)))

/-- Restricting to a standard open `D(f)` with `f` in an ideal extends that ideal to the unit
ideal. -/
theorem map_appTop_basicOpen_eq_top {T : Scheme.{u}} {I : Ideal Γ(T, ⊤)} {f : Γ(T, ⊤)}
    (hf : f ∈ I) : Ideal.map (T.basicOpen f).ι.appTop.hom I = ⊤ := by
  refine Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hf) ?_
  have he : (T.basicOpen f).ι ''ᵁ ⊤ = T.basicOpen f := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
  have key : ∀ (U : T.Opens) (h : U ≤ ⊤), U = T.basicOpen f →
      IsUnit (T.presheaf.map (homOfLE h).op f) := by
    rintro U h rfl
    exact T.toRingedSpace.isUnit_res_basicOpen f
  exact key _ le_top he

/-- If the extension of an ideal `I` along `g` is the unit ideal, then at every point `t'` of `T'`
some `f ∈ I` does not vanish at `g t'`. -/
theorem exists_mem_basicOpen_of_map_eq_top {T T' : Scheme.{u}} (g : T' ⟶ T) {I : Ideal Γ(T, ⊤)}
    (hI : Ideal.map g.appTop.hom I = ⊤) (t' : T') : ∃ f ∈ I, g t' ∈ T.basicOpen f := by
  by_contra hcon
  push Not at hcon
  have h1 : g t' ∈ T.zeroLocus (I : Set Γ(T, ⊤)) := by
    rwa [Scheme.mem_zeroLocus_iff]
  have h2 : t' ∈ T'.zeroLocus ((g.app ⊤).hom '' (I : Set Γ(T, ⊤))) := by
    rwa [← Scheme.preimage_zeroLocus]
  rw [← Scheme.zeroLocus_span] at h2
  change t' ∈ T'.zeroLocus (Ideal.map g.appTop.hom I : Set Γ(T', ⊤)) at h2
  rw [hI, Submodule.top_coe, Scheme.zeroLocus_univ] at h2
  exact h2 trivial

/-- Over an affine base, the pullback of a section along `g` lies in the image of the chart exactly
when the base change of its family along `g` lies in the chart. -/
theorem inImage_chartMap_map_iff {T : Scheme.{u}} [IsAffine T] (s : T ⟶ S)
    (Z : HilbertFamily X (Over.mk s) d) {T' : Scheme.{u}} [IsAffine T'] (g : T' ⟶ T) :
    InImage (chartMap w) ((hilbPresheaf X d).map g.op (⟨s, Z⟩ : HilbSections X d T)) ↔
      IsChart w (baseChange X (Over.homMk g rfl : Over.mk (g ≫ s) ⟶ Over.mk s) Z) :=
  inImage_chartMap_iff w (g ≫ s) _

/-- **The locus of the chart, over affine schemes.** If the pullback of a section `p` along
`g : T' ⟶ T` lies in the image of the chart, then every point `g t'` has an open neighbourhood `O`
such that the restriction of `p` to `O` lies in the image of the chart. -/
theorem exists_open_inImage_chartMap {T : Scheme.{u}} [IsAffine T]
    (p : (hilbPresheaf X d).obj (op T)) {T' : Scheme.{u}} [IsAffine T'] (g : T' ⟶ T)
    (hg : InImage (chartMap w) ((hilbPresheaf X d).map g.op p)) (t' : T') :
    ∃ O : T.Opens, g t' ∈ O ∧ InImage (chartMap w) ((hilbPresheaf X d).map O.ι.op p) := by
  obtain ⟨s, Z⟩ := p
  rw [inImage_chartMap_map_iff, isChart_baseChange_iff] at hg
  obtain ⟨f, hf, hft⟩ := exists_mem_basicOpen_of_map_eq_top g hg t'
  refine ⟨T.basicOpen f, hft, ?_⟩
  have : IsAffine (T.basicOpen f).toScheme := (isAffineOpen_top T).basicOpen f
  rw [inImage_chartMap_map_iff, isChart_baseChange_iff]
  exact map_appTop_basicOpen_eq_top hf

end Stacks.Hilbert.Chart
