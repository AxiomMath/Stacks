module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartFullGraded

/-!
# The morphism `r_{L, ψ} : U(ψ) ⟶ Proj A` of Stacks Tag 01NK

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `T` a scheme, `L` an invertible `𝒪_T`-module and
`ψ : A → Γ_*(T, L)` a graded map in the degreewise spelling
`Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections`. For a homogeneous `f` of positive
degree the chart `T_{ψ(f)} ⟶ D₊(f) ⊆ Proj 𝒜` is `Spec` of the dehomogenisation ring map
`A_{(f)} ⟶ Γ(T_{ψ(f)}, 𝒪_T)`, and the charts of two homogeneous elements agree on the overlap even
when their degrees differ. This file glues them into the morphism

  `r_{L, ψ} : U(ψ) ⟶ Proj 𝒜`,   `U(ψ) = ⋃_{f ∈ A_+ homogeneous} T_{ψ(f)}`,

of [Stacks, Tag 01NK], and proves clause (1) of that tag together with the characterisation of
`r_{L, ψ}` by its restrictions to the charts.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.coveringCover`: the family
  `{T_{ψ(f)}}`, `f` homogeneous of positive degree, as an open cover of `U(ψ)`.
* `Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.glued`: the morphism
  `r_{L, ψ} : U(ψ) ⟶ Proj 𝒜` of [Stacks, Tag 01NK].

## Main results

* `Stacks.AlgebraicGeometry.ProjChartFullGraded.ratioOf_res`: the ratio of two global sections
  over a smaller open is the restriction of the ratio over the larger one.
* `Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.lift_res`: the chart ring map
  `A_{(f)} ⟶ Γ(T_{ψ(f)}, 𝒪_T)` is compatible with restriction, and
  `Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.homOfLE_chartToProj`: so is the
  chart.
* `Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.comp_chartToProj_eq`: the charts of
  two homogeneous elements agree after composing with a pair of morphisms agreeing over `T`.
* `Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.homOfLE_glued_of_pos`: `r_{L, ψ}`
  restricts on each `T_{ψ(f)}` to the dehomogenisation chart of `f`.
* `Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.preimage_basicOpen_glued`: clause
  (1) of [Stacks, Tag 01NK], `r_{L, ψ}^{-1}(D₊(f)) = T_{ψ(f)}` for every homogeneous `f` of
  positive degree.
* `Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.image_preimage_basicOpen_glued`:
  clause (1) read as an equality of opens of `T`.
* `Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.eq_glued_of_homOfLE_eq`: `r_{L, ψ}`
  is the unique morphism `U(ψ) ⟶ Proj 𝒜` restricting to the dehomogenisation chart on each
  `T_{ψ(f)}`.
* `Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.eq_glued_of_appLE_eq`: a morphism
  `U(ψ) ⟶ Proj 𝒜` with the same preimages of the standard opens as `r_{L, ψ}` and the same effect
  on their sections is `r_{L, ψ}`.

## Implementation notes

Clause (1) asks for the preimage of `D₊(f)` with `f` of degree `e`, computed on the chart of
another element `g`, of some other degree `e'`. The controlling fraction is Mathlib's
`HomogeneousLocalization.Away.isLocalizationElem`, with numerator `f ^ e'`, so
`chartToProj_preimage_basicOpen` is stated for two elements of different degrees.

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry HomogeneousLocalization
open Stacks.TensorPowers (natTensorPow)
open Stacks.TensorPowerTrivialize (resTop)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.AlgebraicGeometry.ProjChartCocycle
open Stacks.MorphismToProj (HomogeneousRatios)

universe u w

namespace Stacks.AlgebraicGeometry.ProjChartFullGraded

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-! ### Ratios and restriction -/

section Ratio

variable {T : Scheme.{u}} (L : T.Modules) [Stacks.Ample.IsInvertibleModule T L]

/-- **The ratio of two global sections is compatible with restriction.** The ratio computed over a
smaller open is the restriction of the ratio computed over the larger one. -/
theorem ratioOf_res {n : ℕ} {V V' : T.Opens} (t : Γ(natTensorPow L n, ⊤))
    (hV : V ≤ nonvanishingOpen T (natTensorPow L n) t) (h : V' ≤ V)
    (x : Γ(natTensorPow L n, ⊤)) :
    T.presheaf.map (homOfLE h).op (ratioOf L t hV x) = ratioOf L t (h.trans hV) x := by
  refine (ratioOf_eq_of_resTop_eq L t (h.trans hV) ?_).symm
  have h0 := congrArg (fun z : Γ(natTensorPow L n, V) =>
    (natTensorPow L n).presheaf.map (homOfLE h).op z) (resTop_eq_ratioOf_smul L t hV x)
  rwa [Stacks.TensorPowerTrivialize.res_resTop,
    Stacks.TensorPowerTrivialize.map_smul_resTop] at h0

end Ratio

/-! ### The preimage of a standard open under a chart, across degrees -/

section OneChart

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {e : ℕ} {f : A} {hf : f ∈ 𝒜 e}
  {X : Scheme.{u}} {U : X.Opens}

/-- **The preimage of `D₊(g)` under a chart is a basic open, for `g` of any positive degree.** For
`f` homogeneous of positive degree `e` and `g` homogeneous of positive degree `e'`, the preimage
of the standard open `D₊(g)` under the chart `U ⟶ Proj 𝒜` attached to a family of homogeneous
ratios for `f` is the basic open of the value of the induced ring map on Mathlib's
`HomogeneousLocalization.Away.isLocalizationElem`, the fraction with numerator `g ^ e`. -/
theorem chartToProj_preimage_basicOpen (R : HomogeneousRatios 𝒜 hf ↥Γ(X, U)) (he : 0 < e)
    {e' : ℕ} {g : A} (hg : g ∈ 𝒜 e') (he' : 0 < e') :
    R.chartToProj he ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 g =
      U.ι ⁻¹ᵁ X.basicOpen (R.lift he (Away.isLocalizationElem hf hg)) := by
  have h1 : R.chartToProj he ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 g =
      R.toSpecAway he ⁻¹ᵁ
        (AlgebraicGeometry.Proj.awayι 𝒜 f hf he ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 g) :=
    Scheme.Hom.comp_preimage _ _ _
  have h2 : AlgebraicGeometry.Proj.awayι 𝒜 f hf he ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 g =
      PrimeSpectrum.basicOpen (Away.isLocalizationElem hf hg) :=
    AlgebraicGeometry.Proj.awayι_preimage_basicOpen (f_deg := hf) (hm := he) (g_deg := hg)
      (hm' := he')
  refine h1.trans ((congrArg (fun W => R.toSpecAway he ⁻¹ᵁ W) h2).trans ?_)
  exact (Scheme.Hom.comp_preimage _ _ _).trans
    (Scheme.Opens.toSpecΓ_preimage_basicOpen U (R.lift he (Away.isLocalizationElem hf hg)))

end OneChart

/-! ### Opens and morphisms determined by an open cover -/

section Cover

/-- **Two opens with the same preimage on every member of an open cover are equal.** -/
theorem opens_ext_of_cover {X : Scheme.{u}} (𝒰 : X.OpenCover) {Z Z' : X.Opens}
    (h : ∀ i, 𝒰.f i ⁻¹ᵁ Z = 𝒰.f i ⁻¹ᵁ Z') : Z = Z' := by
  refine TopologicalSpace.Opens.ext (Set.ext fun x => ?_)
  obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
  exact SetLike.ext_iff.mp (h i) y

end Cover

/-! ### Uniqueness of a morphism into `Proj 𝒜` -/

section Uniqueness

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- **Two morphisms into `Proj 𝒜` with the same preimages of the standard opens and the same
effect on their sections are equal.** The standard opens are indexed by a family of homogeneous
elements of positive degree whose preimages cover the source. -/
theorem eq_of_appLE_eq {X : Scheme.{u}} {Φ Φ' : X ⟶ Proj 𝒜} {I : Type*} {d : I → ℕ} {a : I → A}
    (ha : ∀ i, a i ∈ 𝒜 (d i)) (hd : ∀ i, 0 < d i) {W : I → X.Opens}
    (hW : ∀ i, Φ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (a i) = W i)
    (hW' : ∀ i, Φ' ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (a i) = W i)
    (hcover : ⨆ i, W i = ⊤)
    (happ : ∀ i, Φ.appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 (a i)) (W i) (hW i).ge =
      Φ'.appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 (a i)) (W i) (hW' i).ge) :
    Φ = Φ' := by
  refine Scheme.hom_ext_of_forall _ _ fun p => ?_
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcover ▸ (Opens.mem_top p : p ∈ (⊤ : X.Opens)))
  refine ⟨W i, hi, ?_⟩
  have haff : IsAffine (AlgebraicGeometry.Proj.basicOpen 𝒜 (a i)).toScheme :=
    AlgebraicGeometry.Proj.isAffineOpen_basicOpen 𝒜 (a i) (ha i) (hd i)
  rw [← Scheme.Hom.resLE_comp_ι Φ (hW i).ge, ← Scheme.Hom.resLE_comp_ι Φ' (hW' i).ge]
  refine congrArg (· ≫ _) (AlgebraicGeometry.ext_of_isAffine ?_)
  simp only [Scheme.Hom.resLE_app_top, happ i]

/-- **Two morphisms into `Proj 𝒜` with the same preimages of the standard opens and the same
effect on the fractions `x / (a i) ^ n` of their sections are equal.** The standard opens are
indexed by a family of homogeneous elements of positive degree whose preimages cover the source. -/
theorem eq_of_appLE_eq_on_away {X : Scheme.{u}} {Φ Φ' : X ⟶ Proj 𝒜} {I : Type*} {d : I → ℕ}
    {a : I → A} (ha : ∀ i, a i ∈ 𝒜 (d i)) (hd : ∀ i, 0 < d i) {W : I → X.Opens}
    (hW : ∀ i, Φ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (a i) = W i)
    (hW' : ∀ i, Φ' ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (a i) = W i)
    (hcover : ⨆ i, W i = ⊤)
    (happ : ∀ (i : I) (n : ℕ) (x : A) (hx : x ∈ 𝒜 (n • d i)),
      Φ.appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 (a i)) (W i) (hW i).ge
          (AlgebraicGeometry.Proj.awayToSection 𝒜 (a i) (Away.mk 𝒜 (ha i) n x hx)) =
        Φ'.appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 (a i)) (W i) (hW' i).ge
          (AlgebraicGeometry.Proj.awayToSection 𝒜 (a i) (Away.mk 𝒜 (ha i) n x hx))) :
    Φ = Φ' := by
  refine eq_of_appLE_eq 𝒜 ha hd hW hW' hcover fun i => ?_
  ext z
  obtain ⟨n, x, hx, hmk⟩ := Away.mk_surjective 𝒜 (ha i)
    ((AlgebraicGeometry.Proj.basicOpenIsoAway 𝒜 (a i) (ha i) (hd i)).inv z)
  have hz : AlgebraicGeometry.Proj.awayToSection 𝒜 (a i) (Away.mk 𝒜 (ha i) n x hx) = z := by
    rw [← AlgebraicGeometry.Proj.basicOpenIsoAway_hom 𝒜 (a i) (ha i) (hd i), hmk]
    exact ConcreteCategory.congr_hom
      (AlgebraicGeometry.Proj.basicOpenIsoAway 𝒜 (a i) (ha i) (hd i)).inv_hom_id z
  rw [← hz]
  exact happ i n x hx

end Uniqueness

namespace GradedSections

/-! ### Compatibility of a chart with restriction -/

section Restriction

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {T : Scheme.{u}} {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L] (ψ : GradedSections 𝒜 L) {e : ℕ} {f : A} {V : T.Opens}

variable (hf : f ∈ 𝒜 e)
  (hV : V ≤ nonvanishingOpen T (natTensorPow L e) (ψ.toFun e ⟨f, hf⟩))

include hV

/-- **The chart ring map `A_{(f)} ⟶ Γ(T_{ψ(f)}, 𝒪_T)` is compatible with restriction**, on the
fractions `a / f ^ n`. -/
theorem lift_mk_res (he : 0 < e) {V' : T.Opens} (h : V' ≤ V) (n : ℕ) (x : A)
    (hx : x ∈ 𝒜 (n • e)) :
    T.presheaf.map (homOfLE h).op
        ((ψ.homogeneousRatios hf hV).lift he (HomogeneousLocalization.Away.mk 𝒜 hf n x hx))
      = (ψ.homogeneousRatios hf (h.trans hV)).lift he
          (HomogeneousLocalization.Away.mk 𝒜 hf n x hx) := by
  have hxm : x ∈ 𝒜 (n * e) := by simpa [smul_eq_mul] using hx
  rw [ψ.lift_mk hf hV he n x hx ⟨x, hxm⟩ rfl,
    ψ.lift_mk hf (h.trans hV) he n x hx ⟨x, hxm⟩ rfl]
  exact ratioOf_res L _ (ψ.le_nonvanishingOpen_pow hf hV n) h _

/-- **The chart ring map for a smaller open is the restriction of the chart ring map for `V`**, as
an equality of ring maps out of `A_{(f)}`. -/
theorem lift_res (he : 0 < e) {V' : T.Opens} (h : V' ≤ V) :
    (ψ.homogeneousRatios hf (h.trans hV)).lift he
      = (CommRingCat.Hom.hom (T.presheaf.map (homOfLE h).op)).comp
          ((ψ.homogeneousRatios hf hV).lift he) :=
  Stacks.ProjGlobalSectionsAppTop.away_ringHom_ext 𝒜 hf fun n x hx =>
    (ψ.lift_mk_res hf hV he h n x hx).symm

/-- **The chart agrees with the chart of a smaller open.** The charts over `V` and over an open
`V' ≤ V` are compatible with the inclusion. -/
theorem homOfLE_chart (he : 0 < e) {V' : T.Opens} (h : V' ≤ V) :
    T.homOfLE h ≫ ψ.chart hf hV he = ψ.chart hf (h.trans hV) he := by
  unfold chart HomogeneousRatios.chart
  rw [← Category.assoc, (ψ.homogeneousRatios hf hV).homOfLE_toSpecAway he h
    (ψ.homogeneousRatios hf (h.trans hV)) (ψ.lift_res hf hV he h)]

/-- **The chart into `Proj 𝒜` agrees with the chart of a smaller open.** The charts
`V ⟶ Proj 𝒜` and `V' ⟶ Proj 𝒜` for an open `V' ≤ V` are compatible with the inclusion. -/
theorem homOfLE_chartToProj (he : 0 < e) {V' : T.Opens} (h : V' ≤ V) :
    T.homOfLE h ≫ ψ.chartToProj hf hV he = ψ.chartToProj hf (h.trans hV) he := by
  rw [← ψ.chart_ι hf hV he, ← ψ.chart_ι hf (h.trans hV) he, ← Category.assoc,
    ψ.homOfLE_chart hf hV he h]

end Restriction

/-! ### The cocycle condition in the shape the gluing consumes -/

section Overlap

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {T : Scheme.{u}} {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L] (ψ : GradedSections 𝒜 L)

/-- **The cocycle condition, pulled back along an arbitrary pair of morphisms.** If a scheme `S`
maps to `V` and to `V'` compatibly over `T`, then the chart of `f` over `V` and the chart of `g`
over `V'` agree after composing with those two morphisms, even when `f` and `g` have different
degrees. -/
theorem comp_chartToProj_eq {e e' : ℕ} {f g : A} (hf : f ∈ 𝒜 e) (hg : g ∈ 𝒜 e')
    {V V' : T.Opens}
    (hVf : V ≤ nonvanishingOpen T (natTensorPow L e) (ψ.toFun e ⟨f, hf⟩))
    (hV'g : V' ≤ nonvanishingOpen T (natTensorPow L e') (ψ.toFun e' ⟨g, hg⟩))
    (he : 0 < e) (he' : 0 < e') (hE : 0 < e + e') {S : Scheme.{u}} (a : S ⟶ V.toScheme)
    (b : S ⟶ V'.toScheme) (hab : a ≫ V.ι = b ≫ V'.ι) :
    a ≫ ψ.chartToProj hf hVf he = b ≫ ψ.chartToProj hg hV'g he' := by
  have hrange : Set.range (a ≫ V.ι).base ⊆ Set.range (V ⊓ V' : T.Opens).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro z ⟨s, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [Scheme.Hom.comp_base]
      exact (Scheme.Opens.range_ι V) ▸ Set.mem_range_self (a.base s)
    · rw [hab, Scheme.Hom.comp_base]
      exact (Scheme.Opens.range_ι V') ▸ Set.mem_range_self (b.base s)
  have hc := IsOpenImmersion.lift_fac (V ⊓ V' : T.Opens).ι (a ≫ V.ι) hrange
  have hfac : ∀ {W : T.Opens} (c : S ⟶ W.toScheme) (hc' : c ≫ W.ι = a ≫ V.ι) (hW : V ⊓ V' ≤ W),
      c = IsOpenImmersion.lift (V ⊓ V' : T.Opens).ι (a ≫ V.ι) hrange ≫ T.homOfLE hW := by
    intro W c hc' hW
    rw [← cancel_mono W.ι, Category.assoc, Scheme.homOfLE_ι, hc, hc']
  rw [hfac a rfl inf_le_left, hfac b hab.symm inf_le_right,
    Category.assoc, Category.assoc,
    ψ.homOfLE_chartToProj hf hVf he inf_le_left,
    ψ.homOfLE_chartToProj hg hV'g he' inf_le_right,
    ψ.chartToProj_eq hf hg (inf_le_left.trans hVf) (inf_le_right.trans hV'g) he he' hE]

end Overlap

/-! ### The cover of `U(ψ)`, and the glued morphism -/

section Glue

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {T : Scheme.{u}} {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L] (ψ : GradedSections 𝒜 L)

/-- **Every `T_{ψ(f)}` with `f` homogeneous of positive degree lies in `U(ψ)`**, with the degree
given as a positive natural number rather than as a successor. -/
theorem nonvanishingOpenAt_le_coveringOpen_of_pos {e : ℕ} {f : A} (hf : f ∈ 𝒜 e) (he : 0 < e) :
    nonvanishingOpen T (natTensorPow L e) (ψ.toFun e ⟨f, hf⟩) ≤ ψ.coveringOpen := by
  obtain ⟨e', rfl⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
  exact ψ.nonvanishingOpenAt_le_coveringOpen e' ⟨f, hf⟩

/-- **The family `{T_{ψ(f)}}`, `f` homogeneous of positive degree, as an open cover of the open
subscheme `U(ψ)`.** -/
def coveringCover : ψ.coveringOpen.toScheme.OpenCover :=
  Scheme.Opens.iSupOpenCover fun p : (e : ℕ) × 𝒜 (e + 1) => ψ.nonvanishingOpenAt (p.1 + 1) p.2

/-- The map of `coveringCover` at the index `p` is the inclusion `T_{ψ(p.2)} ⟶ U(ψ)`. -/
@[simp] theorem coveringCover_f (p : (k : ℕ) × 𝒜 (k + 1)) :
    ψ.coveringCover.f p = T.homOfLE (ψ.nonvanishingOpenAt_le_coveringOpen p.1 p.2) := rfl

/-- **The charts of two members of the cover agree over the pullback of the two inclusions**
`T_{ψ(f)} ⟶ U(ψ)` and `T_{ψ(g)} ⟶ U(ψ)`. -/
theorem pullback_chartToProj_eq (p q : (k : ℕ) × 𝒜 (k + 1)) :
    Limits.pullback.fst (T.homOfLE (ψ.nonvanishingOpenAt_le_coveringOpen p.1 p.2))
            (T.homOfLE (ψ.nonvanishingOpenAt_le_coveringOpen q.1 q.2))
          ≫ ψ.chartToProj p.2.2 (le_refl (ψ.nonvanishingOpenAt (p.1 + 1) p.2))
              (Nat.succ_pos p.1)
      = Limits.pullback.snd (T.homOfLE (ψ.nonvanishingOpenAt_le_coveringOpen p.1 p.2))
            (T.homOfLE (ψ.nonvanishingOpenAt_le_coveringOpen q.1 q.2))
          ≫ ψ.chartToProj q.2.2 (le_refl (ψ.nonvanishingOpenAt (q.1 + 1) q.2))
              (Nat.succ_pos q.1) := by
  refine ψ.comp_chartToProj_eq p.2.2 q.2.2
    (le_refl (ψ.nonvanishingOpenAt (p.1 + 1) p.2))
    (le_refl (ψ.nonvanishingOpenAt (q.1 + 1) q.2)) (Nat.succ_pos p.1)
    (Nat.succ_pos q.1) (by omega) _ _ ?_
  rw [← T.homOfLE_ι (ψ.nonvanishingOpenAt_le_coveringOpen p.1 p.2),
    ← T.homOfLE_ι (ψ.nonvanishingOpenAt_le_coveringOpen q.1 q.2),
    ← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ ψ.coveringOpen.ι) Limits.pullback.condition

/-- **The morphism `r_{L, ψ} : U(ψ) ⟶ Proj 𝒜` of [Stacks, Tag 01NK].** On the member `T_{ψ(f)}` of
the cover of `U(ψ)` it is the chart of `f`, that is `Spec` of the dehomogenisation ring map
`A_{(f)} ⟶ Γ(T_{ψ(f)}, 𝒪_T)`, `a / f ^ n ↦ ψ(a) / ψ(f ^ n)`. -/
def glued : ψ.coveringOpen.toScheme ⟶ Proj 𝒜 :=
  ψ.coveringCover.glueMorphisms
    (fun p => ψ.chartToProj p.2.2 (le_refl (ψ.nonvanishingOpenAt (p.1 + 1) p.2))
      (Nat.succ_pos p.1))
    fun p q => ψ.pullback_chartToProj_eq p q

/-- **`r_{L, ψ}` restricts on each member of the cover to the chart there.** -/
theorem homOfLE_glued (p : (k : ℕ) × 𝒜 (k + 1)) :
    T.homOfLE (ψ.nonvanishingOpenAt_le_coveringOpen p.1 p.2) ≫ ψ.glued
      = ψ.chartToProj p.2.2 (le_refl (ψ.nonvanishingOpenAt (p.1 + 1) p.2))
          (Nat.succ_pos p.1) :=
  Scheme.Cover.ι_glueMorphisms ψ.coveringCover _ _ p

/-- **`r_{L, ψ}` restricts on `T_{ψ(f)}` to the dehomogenisation chart of `f`**, for every
homogeneous `f` of positive degree. -/
theorem homOfLE_glued_of_pos {e : ℕ} {f : A} (hf : f ∈ 𝒜 e) (he : 0 < e) :
    T.homOfLE (ψ.nonvanishingOpenAt_le_coveringOpen_of_pos hf he) ≫ ψ.glued
      = ψ.chartToProj hf
          (le_refl (nonvanishingOpen T (natTensorPow L e) (ψ.toFun e ⟨f, hf⟩))) he := by
  obtain ⟨e', rfl⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
  exact ψ.homOfLE_glued ⟨e', ⟨f, hf⟩⟩

/-- **The members of the cover, read as opens of `U(ψ)`, cover `U(ψ)`.** -/
theorem iSup_preimage_nonvanishingOpenAt_eq_top :
    ⨆ p : (e : ℕ) × 𝒜 (e + 1),
        ψ.coveringOpen.ι ⁻¹ᵁ ψ.nonvanishingOpenAt (p.1 + 1) p.2 = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup]
  exact ψ.coveringOpen.ι_preimage_self

end Glue

/-! ### Clause (1) of Stacks Tag 01NK -/

section Preimage

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {T : Scheme.{u}} {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L] (ψ : GradedSections 𝒜 L)

/-- **The nonvanishing open of a positive power of a value of `ψ` is that of the value itself:**
`T_{ψ(g ^ n)} = T_{ψ(g)}` for `n > 0`. -/
theorem nonvanishingOpen_pow_eq {e' : ℕ} {g : A} (hg : g ∈ 𝒜 e') {n : ℕ} (hn : 0 < n) :
    nonvanishingOpen T (natTensorPow L (n * e'))
        (ψ.toFun (n * e') ⟨g ^ n, HomogeneousRatios.pow_mem hg n⟩)
      = nonvanishingOpen T (natTensorPow L e') (ψ.toFun e' ⟨g, hg⟩) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  refine le_antisymm ?_ (ψ.le_nonvanishingOpen_pow hg le_rfl (m + 1))
  have hgm : (g : A) ^ m ∈ 𝒜 (m * e') := HomogeneousRatios.pow_mem hg m
  have hstep : (g : A) ^ m * g ∈ 𝒜 (m * e' + e') := SetLike.mul_mem_graded hgm hg
  have h := ψ.nonvanishingOpen_mul hgm hg hstep
  rw [ψ.nonvanishingOpen_congr hstep (HomogeneousRatios.pow_mem hg (m + 1))
      (Nat.succ_mul m e').symm (pow_succ g m).symm] at h
  exact h.le.trans inf_le_right

variable {e : ℕ} {f : A} {V : T.Opens} (hf : f ∈ 𝒜 e)
  (hV : V ≤ nonvanishingOpen T (natTensorPow L e) (ψ.toFun e ⟨f, hf⟩))

include hV

/-- **The value of the chart ring map on the fraction controlling the overlap with `D₊(g)`.** For
`g` homogeneous of degree `e'`, Mathlib's `HomogeneousLocalization.Away.isLocalizationElem` is the
fraction with numerator `g ^ e` and denominator `f ^ {e'}`, and the chart ring map sends it to the
ratio `ψ(g ^ e) / ψ(f ^ {e'})` of two global sections of `L ^⊗ (e' e)`. -/
theorem lift_isLocalizationElem_eq_ratioOf (he : 0 < e) {e' : ℕ} {g : A} (hg : g ∈ 𝒜 e')
    (hgm : g ^ e ∈ 𝒜 (e' * e)) :
    (ψ.homogeneousRatios hf hV).lift he (Away.isLocalizationElem hf hg)
      = ratioOf L (ψ.toFun (e' * e) ⟨f ^ e', HomogeneousRatios.pow_mem hf e'⟩)
          (ψ.le_nonvanishingOpen_pow hf hV e') (ψ.toFun (e' * e) ⟨g ^ e, hgm⟩) :=
  ψ.lift_mk hf hV he e' (g ^ e) (by simpa [smul_eq_mul] using hgm) ⟨g ^ e, hgm⟩ rfl

/-- **The preimage of `D₊(g)` under the chart of `f` is `T_{ψ(g)} ⊓ V`**, for `f` and `g`
homogeneous of arbitrary positive degrees. -/
theorem chartToProj_preimage_basicOpen_eq_inf (he : 0 < e) {e' : ℕ} {g : A} (hg : g ∈ 𝒜 e')
    (he' : 0 < e') :
    ψ.chartToProj hf hV he ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 g
      = V.ι ⁻¹ᵁ (nonvanishingOpen T (natTensorPow L e') (ψ.toFun e' ⟨g, hg⟩) ⊓ V) := by
  have hgm : g ^ e ∈ 𝒜 (e' * e) := by
    rw [Nat.mul_comm]
    exact HomogeneousRatios.pow_mem hg e
  have hbase : ψ.chartToProj hf hV he ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 g
      = V.ι ⁻¹ᵁ T.basicOpen
        ((ψ.homogeneousRatios hf hV).lift he (Away.isLocalizationElem hf hg)) :=
    chartToProj_preimage_basicOpen (ψ.homogeneousRatios hf hV) he hg he'
  rw [hbase, ψ.lift_isLocalizationElem_eq_ratioOf hf hV he hg hgm,
    ← Stacks.SectionExtension.nonvanishingOpen_inf_eq_basicOpen
      (ψ.toFun (e' * e) ⟨f ^ e', HomogeneousRatios.pow_mem hf e'⟩)
      (ψ.toFun (e' * e) ⟨g ^ e, hgm⟩) (ψ.le_nonvanishingOpen_pow hf hV e') _
      (resTop_eq_ratioOf_smul L (ψ.toFun (e' * e) ⟨f ^ e', HomogeneousRatios.pow_mem hf e'⟩)
        (ψ.le_nonvanishingOpen_pow hf hV e') (ψ.toFun (e' * e) ⟨g ^ e, hgm⟩)),
    ψ.nonvanishingOpen_congr hgm (HomogeneousRatios.pow_mem hg e) (Nat.mul_comm e' e) rfl,
    ψ.nonvanishingOpen_pow_eq hg he]

omit hV

/-- **Clause (1) of [Stacks, Tag 01NK] on one member of the cover of `U(ψ)`:** the preimage of
`D₊(f)` under `r_{L, ψ}` and the preimage of `T_{ψ(f)}` have the same preimage in the member
`T_{ψ(g)}` of the cover indexed by `p = ⟨k, g⟩`. -/
theorem homOfLE_preimage_basicOpen_glued (he : 0 < e) (p : (k : ℕ) × 𝒜 (k + 1)) :
    T.homOfLE (ψ.nonvanishingOpenAt_le_coveringOpen p.1 p.2)
          ⁻¹ᵁ (ψ.glued ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f)
      = T.homOfLE (ψ.nonvanishingOpenAt_le_coveringOpen p.1 p.2) ⁻¹ᵁ (ψ.coveringOpen.ι ⁻¹ᵁ
          nonvanishingOpen T (natTensorPow L e) (ψ.toFun e ⟨f, hf⟩)) := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage,
    ψ.homOfLE_glued p, Scheme.homOfLE_ι,
    ψ.chartToProj_preimage_basicOpen_eq_inf p.2.2
      (le_refl (ψ.nonvanishingOpenAt (p.1 + 1) p.2)) (Nat.succ_pos p.1) hf he,
    Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, inf_top_eq]

/-- **Clause (1) of [Stacks, Tag 01NK]**: the preimage of the standard open `D₊(f)` under
`r_{L, ψ}` is `T_{ψ(f)}`, for every homogeneous `f` of positive degree. Both sides are read as
opens of the source `U(ψ)`. -/
theorem preimage_basicOpen_glued (he : 0 < e) :
    ψ.glued ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f
      = ψ.coveringOpen.ι ⁻¹ᵁ nonvanishingOpen T (natTensorPow L e) (ψ.toFun e ⟨f, hf⟩) :=
  opens_ext_of_cover ψ.coveringCover fun p =>
    ψ.homOfLE_preimage_basicOpen_glued hf he p

/-- **Clause (1) of [Stacks, Tag 01NK], read as an equality of opens of `T`.** The image in `T` of
the preimage of `D₊(f)` under `r_{L, ψ}` is the nonvanishing open `T_{ψ(f)}` itself. -/
theorem image_preimage_basicOpen_glued (he : 0 < e) :
    ψ.coveringOpen.ι ''ᵁ (ψ.glued ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f)
      = nonvanishingOpen T (natTensorPow L e) (ψ.toFun e ⟨f, hf⟩) := by
  rw [ψ.preimage_basicOpen_glued hf he, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι, inf_eq_right]
  exact ψ.nonvanishingOpenAt_le_coveringOpen_of_pos hf he

end Preimage

/-! ### The characterisation of `r_{L, ψ}` -/

section Characterisation

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {T : Scheme.{u}} {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L] (ψ : GradedSections 𝒜 L)

/-- **Two morphisms out of `U(ψ)` agreeing on every `T_{ψ(f)}` are equal.** -/
theorem hom_ext_of_homOfLE_eq {Z : Scheme.{u}} {Φ Φ' : ψ.coveringOpen.toScheme ⟶ Z}
    (h : ∀ (e : ℕ) (f : 𝒜 (e + 1)),
      T.homOfLE (ψ.nonvanishingOpenAt_le_coveringOpen e f) ≫ Φ
        = T.homOfLE (ψ.nonvanishingOpenAt_le_coveringOpen e f) ≫ Φ') :
    Φ = Φ' :=
  Scheme.Cover.hom_ext ψ.coveringCover Φ Φ' fun p => h p.1 p.2

/-- **`r_{L, ψ}` is the unique morphism `U(ψ) ⟶ Proj 𝒜` that restricts on each `T_{ψ(f)}` to the
dehomogenisation chart of `f`.** -/
theorem eq_glued_of_homOfLE_eq {Φ : ψ.coveringOpen.toScheme ⟶ Proj 𝒜}
    (h : ∀ (e : ℕ) (f : A) (hf : f ∈ 𝒜 e) (he : 0 < e),
      T.homOfLE (ψ.nonvanishingOpenAt_le_coveringOpen_of_pos hf he) ≫ Φ
        = ψ.chartToProj hf
            (le_refl (nonvanishingOpen T (natTensorPow L e) (ψ.toFun e ⟨f, hf⟩))) he) :
    Φ = ψ.glued :=
  ψ.hom_ext_of_homOfLE_eq fun e g =>
    (h (e + 1) (g : A) g.2 (Nat.succ_pos e)).trans
      (ψ.homOfLE_glued_of_pos g.2 (Nat.succ_pos e)).symm

/-- **The uniqueness of `r_{L, ψ}` in the spelling of the source's argument.** A morphism
`Φ : U(ψ) ⟶ Proj 𝒜` whose preimages of the standard opens are the `T_{ψ(f)}` — clause (1) — and
whose effect on the sections `a / f ^ n` of `Γ(Proj 𝒜, D₊(f))` is that of `r_{L, ψ}` equals
`r_{L, ψ}`. -/
theorem eq_glued_of_appLE_eq {Φ : ψ.coveringOpen.toScheme ⟶ Proj 𝒜}
    (hpre : ∀ (e : ℕ) (f : 𝒜 (e + 1)),
      Φ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)
        = ψ.coveringOpen.ι ⁻¹ᵁ ψ.nonvanishingOpenAt (e + 1) f)
    (happ : ∀ (e : ℕ) (f : 𝒜 (e + 1)) (n : ℕ) (x : A) (hx : x ∈ 𝒜 (n • (e + 1))),
      Φ.appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A))
          (ψ.coveringOpen.ι ⁻¹ᵁ ψ.nonvanishingOpenAt (e + 1) f) (hpre e f).ge
          (AlgebraicGeometry.Proj.awayToSection 𝒜 (f : A) (Away.mk 𝒜 f.2 n x hx))
        = ψ.glued.appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A))
            (ψ.coveringOpen.ι ⁻¹ᵁ ψ.nonvanishingOpenAt (e + 1) f)
            (ψ.preimage_basicOpen_glued f.2 (Nat.succ_pos e)).ge
          (AlgebraicGeometry.Proj.awayToSection 𝒜 (f : A) (Away.mk 𝒜 f.2 n x hx))) :
    Φ = ψ.glued :=
  eq_of_appLE_eq_on_away 𝒜 (a := fun p : (e : ℕ) × 𝒜 (e + 1) => (p.2 : A))
    (d := fun p => p.1 + 1) (fun p => p.2.2) (fun p => Nat.succ_pos p.1)
    (W := fun p => ψ.coveringOpen.ι ⁻¹ᵁ ψ.nonvanishingOpenAt (p.1 + 1) p.2)
    (fun p => hpre p.1 p.2)
    (fun p => ψ.preimage_basicOpen_glued p.2.2 (Nat.succ_pos p.1))
    ψ.iSup_preimage_nonvanishingOpenAt_eq_top
    fun p n x hx => happ p.1 p.2 n x hx

end Characterisation

end GradedSections

end Stacks.AlgebraicGeometry.ProjChartFullGraded

end
