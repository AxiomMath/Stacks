module

public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.BaseChangeFunctorial
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.ChartProjBaseChange
public import Mathlib.AlgebraicGeometry.Cover.Directed
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Relative `Proj` base change along a morphism of base schemes

Let `g : S' ⟶ S` be a morphism of schemes, let `s` and `s'` be relative `Proj` situations over
`S` and `S'`, and let `Φ` identify the graded algebra of `s'` with the pullback along `g` of the
graded algebra of `s`, isomorphically in every nonnegative degree. This file glues the chart
squares of `Stacks.RelativeProj.Situation.isPullback_projInclusionToOpen_gradedBaseChange` into a
single morphism `relativeProj s' ⟶ relativeProj s` and proves that

```
relativeProj s'  ⟶  relativeProj s
      |                   |
      v                   v
      S'       ⟶          S
```

is cartesian: `relativeProj s'` *is* the base change of `relativeProj s` along `g`.

The comparison morphism is glued along the cover of `relativeProj s'` indexed by the pairs
`(W', W)` of affine opens of `S'` and of `S` with `W' ⊆ g⁻¹W`, ordered componentwise.

## Main definitions

* `Stacks.RelativeProj.Cover.locallyDirectedOfOpensRange`: a `Cover.LocallyDirected` structure
  on an open cover whose index preorder refines inclusion of images and whose images are
  *pointwise* directed.
* `Stacks.RelativeProj.Situation.BaseChangeIndex`: the poset of pairs `W' ⊆ g⁻¹W` of affine
  opens.
* `Stacks.RelativeProj.Situation.baseChangeBaseCover` and `baseChangeCover`: the induced covers
  of `S'` and of `relativeProj s'`.
* `Stacks.RelativeProj.Situation.chartBaseChangeHom`: the comparison morphism attached to one
  pair.
* `Stacks.RelativeProj.Situation.relativeProjBaseChange`: the glued comparison morphism
  `relativeProj s' ⟶ relativeProj s`.
* `Stacks.RelativeProj.Situation.relativeProjBaseChangeIso`: the comparison with the fibre
  product, `relativeProj s' ≅ relativeProj s ×_S S'`.

## Main results

* `Stacks.RelativeProj.Situation.projInclusionMap_comp_chartBaseChangeHom`: the comparison
  morphisms of charts are compatible in both opens at once.
* `Stacks.RelativeProj.Situation.isPullback_relativeProjBaseChange`: the base-change square is
  cartesian.
* `Stacks.RelativeProj.Situation.relativeProjBaseChangeIso_hom_fst` and `_hom_snd`: the
  comparison isomorphism sits over `relativeProj s` and over `S'`.

## References

* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite HomogeneousIdeal

universe u

namespace Stacks.RelativeProj

/-! ### A locally directed cover from pointwise directedness of the ranges -/

/-- The locally directed structure on an open cover whose index preorder refines inclusion of the
images and whose images are pointwise directed: a point in the images of `i` and `j` lies in the
image of some `k` with `k ≤ i` and `k ≤ j`. -/
@[instance_reducible]
public def Cover.locallyDirectedOfOpensRange {X : Scheme.{u}} (𝒰 : X.OpenCover) [Preorder 𝒰.I₀]
    (hle : ∀ {i j : 𝒰.I₀}, i ≤ j → Set.range (𝒰.f i).base ⊆ Set.range (𝒰.f j).base)
    (hdir : ∀ (i j : 𝒰.I₀) (x : X), x ∈ (𝒰.f i).opensRange → x ∈ (𝒰.f j).opensRange →
      ∃ (k : 𝒰.I₀) (_ : k ≤ i) (_ : k ≤ j), x ∈ (𝒰.f k).opensRange) :
    𝒰.LocallyDirected where
  trans {i j} hij := IsOpenImmersion.lift (𝒰.f j) (𝒰.f i) (hle (leOfHom hij))
  trans_id i := by
    rw [← cancel_mono (𝒰.f i), Category.id_comp]
    exact IsOpenImmersion.lift_fac _ _ _
  trans_comp hij hjk := by
    rw [← cancel_mono (𝒰.f _), Category.assoc, IsOpenImmersion.lift_fac,
      IsOpenImmersion.lift_fac, IsOpenImmersion.lift_fac]
  w hij := IsOpenImmersion.lift_fac _ _ _
  directed {i j} x := by
    have hx : (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) x ∈ (𝒰.f i).opensRange :=
      ⟨pullback.fst (𝒰.f i) (𝒰.f j) x, (Scheme.Hom.comp_apply _ _ x).symm⟩
    have hx' : (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) x ∈ (𝒰.f j).opensRange := by
      rw [pullback.condition]
      exact ⟨pullback.snd (𝒰.f i) (𝒰.f j) x, (Scheme.Hom.comp_apply _ _ x).symm⟩
    obtain ⟨k, hki, hkj, y, hy⟩ := hdir i j _ hx hx'
    refine ⟨k, homOfLE hki, homOfLE hkj, y, ?_⟩
    apply (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i).isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst_assoc]
    exact ((Scheme.Hom.comp_apply _ _ y).symm.trans
      (congrArg (fun z => z y) (IsOpenImmersion.lift_fac (𝒰.f i) (𝒰.f k) _))).trans hy

/-- The transition map of a locally directed open cover is the unique morphism over the cover. -/
public theorem Cover.trans_eq_of_comp_f {X : Scheme.{u}} (𝒰 : X.OpenCover) [Preorder 𝒰.I₀]
    [𝒰.LocallyDirected] {i j : 𝒰.I₀} (hij : i ⟶ j) {t : 𝒰.X i ⟶ 𝒰.X j}
    (ht : t ≫ 𝒰.f j = 𝒰.f i) : 𝒰.trans hij = t := by
  rw [← cancel_mono (𝒰.f j), ht]
  exact 𝒰.trans_map hij

/-- Transport of a cartesian square along an equality of its upper horizontal morphism. -/
public theorem isPullback_of_fst_eq {C : Type*} [Category C] {P X Y Z : C} {fst fst' : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ Z} {h : Y ⟶ Z} (e : fst = fst') (hsq : IsPullback fst snd f h) :
    IsPullback fst' snd f h := e ▸ hsq

/-- If `α : A ⟶ X'` exhibits `A` as the part of `X'` over an open `V` of `S'`, and if `A` is the
base change of `X ⟶ S` along `V ⟶ S' ⟶ S`, then the canonical pullback `X' ×_{S'} V` is too. -/
public theorem isPullback_snd_fst_comp {X' X S' S A V : Scheme.{u}} (c : X' ⟶ X) (p' : X' ⟶ S')
    (pp : X ⟶ S) (gg : S' ⟶ S) (ι : V ⟶ S') (α : A ⟶ X') (a : A ⟶ V)
    (hchart : IsPullback α a p' ι)
    (htot : IsPullback (α ≫ c) a pp (ι ≫ gg)) :
    IsPullback (pullback.snd p' ι) (pullback.fst p' ι ≫ c) (ι ≫ gg) pp := by
  refine htot.flip.of_iso' hchart.isoPullback.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · rw [Iso.symm_hom, Iso.refl_hom, Category.comp_id, Iso.inv_comp_eq,
      hchart.isoPullback_hom_snd]
  · rw [Iso.symm_hom, Iso.refl_hom, Category.comp_id, Iso.inv_comp_eq, ← Category.assoc,
      hchart.isoPullback_hom_fst]
  · rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id]
  · rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id]


namespace Situation

variable {s s' : Situation.{u}} (g : s'.base ⟶ s.base)

/-! ### The index: pairs of affine opens `W' ⊆ g⁻¹W` -/

/-- Pairs of an affine open `W'` of `S'` and an affine open `W` of `S` with `W' ⊆ g⁻¹W`,
ordered componentwise. -/
public abbrev BaseChangeIndex (g : s'.base ⟶ s.base) : Type u :=
  {p : s'.base.affineOpens × s.base.affineOpens // p.1.1 ≤ g ⁻¹ᵁ p.2.1}

/-- A point of `S'` over a point of an open `V` of `S` has an affine neighbourhood `W'` inside a
prescribed open, with `W' ⊆ g⁻¹W` for an affine open `W ⊆ V`. -/
private theorem exists_baseChangeIndex_le (y : s'.base) (U : s'.base.Opens)
    (V : s.base.Opens) (hy : y ∈ U) (hgy : g.base y ∈ V) :
    ∃ p : BaseChangeIndex g, y ∈ p.1.1.1 ∧ p.1.1.1 ≤ U ∧ p.1.2.1 ≤ V := by
  obtain ⟨W, hW, hgyW, hWle⟩ := Opens.isBasis_iff_nbhd.mp s.base.isBasis_affineOpens hgy
  obtain ⟨W', hW', hyW', hle'⟩ := Opens.isBasis_iff_nbhd.mp s'.base.isBasis_affineOpens
    (show y ∈ U ⊓ g ⁻¹ᵁ W from ⟨hy, hgyW⟩)
  exact ⟨⟨(⟨W', hW'⟩, ⟨W, hW⟩), hle'.trans inf_le_right⟩, hyW', hle'.trans inf_le_left, hWle⟩

/-- Every point of `S'` has an affine open neighbourhood inside a prescribed open and inside the
preimage of an affine open of `S`. -/
public theorem exists_baseChangeIndex (y : s'.base) (U : s'.base.Opens) (hy : y ∈ U) :
    ∃ p : BaseChangeIndex g, y ∈ p.1.1.1 ∧ p.1.1.1 ≤ U :=
  let ⟨p, h₁, h₂, _⟩ := exists_baseChangeIndex_le g y U ⊤ hy trivial
  ⟨p, h₁, h₂⟩

/-! ### The two covers indexed by that poset -/

/-- The cover of `S'` by the affine opens that lie in the preimage of an affine open of `S`. -/
public def baseChangeBaseCover : s'.base.OpenCover :=
  Scheme.Cover.mkOfCovers (BaseChangeIndex g) (fun p => p.1.1.1.toScheme)
    (fun p => p.1.1.1.ι) (fun y => by
      obtain ⟨p, hy, -⟩ := exists_baseChangeIndex g y ⊤ trivial
      exact ⟨p, ⟨y, hy⟩, rfl⟩)

/-- The component of `baseChangeBaseCover` at a pair `(W', W)` is the inclusion of `W'`. -/
@[simp] public theorem baseChangeBaseCover_f (p : BaseChangeIndex g) :
    (baseChangeBaseCover g).f p = p.1.1.1.ι := rfl

/-- The chart of a relative `Proj` over an affine open of the base is an open immersion. -/
public instance isOpenImmersion_relativeProjChart (t : Situation.{u}) (W : t.base.affineOpens) :
    IsOpenImmersion (relativeProjChart t W) :=
  (chartData t).isOpenImmersion_chartι W

/-- The chart over an affine open of the base is the part of the relative `Proj` lying over it. -/
public theorem opensRange_relativeProjChart (t : Situation.{u}) (W : t.base.affineOpens) :
    (relativeProjChart t W).opensRange = relativeProjToBase t ⁻¹ᵁ W.1 :=
  ((chartData t).toBase_preimage_coe W).symm

/-- A point of the relative `Proj` lies in the chart over `W` exactly when it lies over `W`. -/
public theorem mem_opensRange_relativeProjChart (t : Situation.{u}) (W : t.base.affineOpens)
    (x : relativeProj t) :
    x ∈ (relativeProjChart t W).opensRange ↔ relativeProjToBase t x ∈ W.1 := by
  rw [opensRange_relativeProjChart]
  exact Iff.rfl

/-- The cover of `relativeProj s'` by the charts over the affine opens of `S'` that lie in the
preimage of an affine open of `S`. -/
public def baseChangeCover : (relativeProj s').OpenCover :=
  Scheme.Cover.mkOfCovers (BaseChangeIndex g)
    (fun p => Proj (s'.sectionRingGrading p.1.1.1)) (fun p => relativeProjChart s' p.1.1)
    (fun x => by
      obtain ⟨p, hy, -⟩ := exists_baseChangeIndex g (relativeProjToBase s' x) ⊤ trivial
      obtain ⟨y, hyx⟩ := (mem_opensRange_relativeProjChart s' p.1.1 x).mpr hy
      exact ⟨p, y, hyx⟩)

/-- The component of `baseChangeCover` at a pair `(W', W)` is the chart of `relativeProj s'`
over `W'`. -/
@[simp] public theorem baseChangeCover_f (p : BaseChangeIndex g) :
    (baseChangeCover g).f p = relativeProjChart s' p.1.1 := rfl

/-- The index of the chart cover, ordered componentwise. -/
public instance preorderBaseChangeCoverI₀ : Preorder (baseChangeCover g).I₀ :=
  inferInstanceAs (Preorder (BaseChangeIndex g))

/-- The images of the components of the chart cover increase with the index. -/
public theorem baseChangeCover_hle {p q : (baseChangeCover g).I₀} (hpq : p ≤ q) :
    Set.range ((baseChangeCover g).f p).base ⊆ Set.range ((baseChangeCover g).f q).base := by
  change (relativeProjChart s' p.1.1).opensRange ≤ (relativeProjChart s' q.1.1).opensRange
  rw [opensRange_relativeProjChart, opensRange_relativeProjChart]
  exact fun z hz => hpq.1 hz

/-- The images of the components of the chart cover are pointwise directed: a point in the
images of `p` and `q` lies in the image of some `r` with `r ≤ p` and `r ≤ q`. -/
public theorem baseChangeCover_hdir (p q : (baseChangeCover g).I₀) (x : relativeProj s')
    (hp : x ∈ ((baseChangeCover g).f p).opensRange)
    (hq : x ∈ ((baseChangeCover g).f q).opensRange) :
    ∃ (r : (baseChangeCover g).I₀) (_ : r ≤ p) (_ : r ≤ q),
      x ∈ ((baseChangeCover g).f r).opensRange := by
  have hp' := (mem_opensRange_relativeProjChart s' p.1.1 x).mp hp
  have hq' := (mem_opensRange_relativeProjChart s' q.1.1 x).mp hq
  obtain ⟨r, hyr, hrU, hrV⟩ := exists_baseChangeIndex_le g (relativeProjToBase s' x)
    (p.1.1.1 ⊓ q.1.1.1) (p.1.2.1 ⊓ q.1.2.1) ⟨hp', hq'⟩ ⟨p.2 hp', q.2 hq'⟩
  exact ⟨r, ⟨hrU.trans inf_le_left, hrV.trans inf_le_left⟩,
    ⟨hrU.trans inf_le_right, hrV.trans inf_le_right⟩,
    (mem_opensRange_relativeProjChart s' r.1.1 x).mpr hyr⟩

/-- The chart cover of `relativeProj s'` is locally directed. -/
public instance locallyDirectedBaseChangeCover : (baseChangeCover g).LocallyDirected :=
  Cover.locallyDirectedOfOpensRange _ (baseChangeCover_hle g) (baseChangeCover_hdir g)

/-- The transition maps of the chart cover are the chart comparison morphisms of `s'`. -/
public theorem baseChangeCover_trans {p q : (baseChangeCover g).I₀} (hpq : p ⟶ q) :
    (baseChangeCover g).trans hpq =
      projInclusionMap s' p.1.1.1 q.1.1.1 (leOfHom hpq).1 p.1.1.2 q.1.1.2 :=
  Cover.trans_eq_of_comp_f _ hpq (relativeProjChart_transition s' (leOfHom hpq).1)

/-! ### The glued comparison morphism -/

variable (Φ : SheafOfModules.GradedAlgebra.UnitalHom
    (Stacks.Conormal.gradedPullback g s.algebra) s'.algebra)
  (hΦ : ∀ m : ℕ, IsIso (Φ.app (m : ℤ)))

/-- The comparison morphism attached to a pair `W' ⊆ g⁻¹W` of affine opens: the chart base
change `Proj 𝒜'(W') ⟶ Proj 𝒜(W)` followed by the chart of `relativeProj s` over `W`. -/
public def chartBaseChangeHom (W : s.base.affineOpens) (W' : s'.base.affineOpens)
    (h : W'.1 ≤ g ⁻¹ᵁ W.1) : Proj (s'.sectionRingGrading W'.1) ⟶ relativeProj s :=
  AlgebraicGeometry.Proj.map (gradedBaseChange g Φ W.1 W'.1 h)
    (irrelevant_le_gradedBaseChange g Φ W W' h hΦ) ≫ relativeProjChart s W

/-- The comparison morphisms of charts are compatible in both opens at once: shrinking `W'` and
shrinking `W` give the same morphism into `relativeProj s`. -/
public theorem projInclusionMap_comp_chartBaseChangeHom {W₁ W₂ : s.base.affineOpens}
    {W₁' W₂' : s'.base.affineOpens} (hW : W₁ ≤ W₂) (hW' : W₁'.1 ≤ W₂'.1)
    (h₁ : W₁'.1 ≤ g ⁻¹ᵁ W₁.1) (h₂ : W₂'.1 ≤ g ⁻¹ᵁ W₂.1) :
    projInclusionMap s' W₁'.1 W₂'.1 hW' W₁'.2 W₂'.2 ≫ chartBaseChangeHom g Φ hΦ W₂ W₂' h₂ =
      chartBaseChangeHom g Φ hΦ W₁ W₁' h₁ := by
  have hirrW : (s.chartGrading W₁)₊ ≤ ((s.chartGrading W₂)₊).map (s.gradedRestrict hW) :=
    s.chartsCartesian.irrelevant_le hW
  have hirrW' : (s'.chartGrading W₁')₊ ≤ ((s'.chartGrading W₂')₊).map (s'.gradedRestrict hW') :=
    s'.chartsCartesian.irrelevant_le hW'
  have hle : W₁'.1 ≤ g ⁻¹ᵁ W₂.1 := h₁.trans fun z hz => hW hz
  rw [chartBaseChangeHom, chartBaseChangeHom,
    show projInclusionMap s' W₁'.1 W₂'.1 hW' W₁'.2 W₂'.2 =
      AlgebraicGeometry.Proj.map (s'.gradedRestrict hW') hirrW' from rfl,
    ← Category.assoc, ← AlgebraicGeometry.Proj.map_comp,
    AlgebraicGeometry.Proj.map_congr
      (gradedRestrict_comp_gradedBaseChange g Φ W₂.1 hW' h₂ hle) _
      (irrelevant_le_gradedBaseChange g Φ W₂ W₁' hle hΦ),
    ← relativeProjChart_transition s hW,
    show projInclusionMap s W₁.1 W₂.1 hW W₁.2 W₂.2 =
      AlgebraicGeometry.Proj.map (s.gradedRestrict hW) hirrW from rfl,
    ← Category.assoc, ← AlgebraicGeometry.Proj.map_comp,
    AlgebraicGeometry.Proj.map_congr
      (gradedBaseChange_comp_gradedRestrict g Φ hW W₁'.1 h₁ hle) _
      (irrelevant_le_gradedBaseChange g Φ W₂ W₁' hle hΦ)]

/-- The comparison morphism of charts, as a family indexed by the chart cover. -/
public def baseChangeChartHom (p : (baseChangeCover g).I₀) :
    (baseChangeCover g).X p ⟶ relativeProj s :=
  chartBaseChangeHom g Φ hΦ p.1.2 p.1.1 p.2

/-- The family of chart comparison morphisms is compatible with the chart transitions. -/
public theorem baseChangeChartHom_trans {p q : (baseChangeCover g).I₀} (hpq : p ⟶ q) :
    (baseChangeCover g).trans hpq ≫ baseChangeChartHom g Φ hΦ q =
      baseChangeChartHom g Φ hΦ p :=
  (congrArg (fun z => z ≫ baseChangeChartHom g Φ hΦ q) (baseChangeCover_trans g hpq)).trans
    (projInclusionMap_comp_chartBaseChangeHom g Φ hΦ (leOfHom hpq).2 (leOfHom hpq).1 p.2 q.2)

/-- The base-change comparison morphism `relativeProj s' ⟶ relativeProj s`, glued from the
comparison morphisms of charts. -/
public def relativeProjBaseChange : relativeProj s' ⟶ relativeProj s :=
  (baseChangeCover g).glueMorphismsOfLocallyDirected (baseChangeChartHom g Φ hΦ)
    (fun hij => baseChangeChartHom_trans g Φ hΦ hij)

/-- The comparison morphism restricts on each chart to the chart comparison morphism. -/
public theorem relativeProjChart_comp_relativeProjBaseChange (p : (baseChangeCover g).I₀) :
    relativeProjChart s' p.1.1 ≫ relativeProjBaseChange g Φ hΦ = baseChangeChartHom g Φ hΦ p :=
  (baseChangeCover g).map_glueMorphismsOfLocallyDirected (baseChangeChartHom g Φ hΦ)
    (fun hij => baseChangeChartHom_trans g Φ hΦ hij) p

/-! ### The base-change square -/

/-- The chart square of the comparison morphism: `Proj 𝒜'(W')` is the base change of
`relativeProj s` along `W' ⟶ S' ⟶ S`. -/
public theorem isPullback_chartBaseChangeHom (W : s.base.affineOpens)
    (W' : s'.base.affineOpens) (h : W'.1 ≤ g ⁻¹ᵁ W.1) :
    IsPullback (chartBaseChangeHom g Φ hΦ W W' h) (projInclusionToOpen s' W'.1 W'.2)
      (relativeProjToBase s) (W'.1.ι ≫ g) := by
  have key := (isPullback_projInclusionToOpen_gradedBaseChange g Φ W W' h hΦ).paste_horiz
    (relativeProjChart_isPullback s W)
  rwa [Scheme.Hom.resLE_comp_ι] at key

/-- The relative `Proj` of `s'` is the base change of the relative `Proj` of `s` along `g`. -/
public theorem isPullback_relativeProjBaseChange :
    IsPullback (relativeProjBaseChange g Φ hΦ) (relativeProjToBase s')
      (relativeProjToBase s) g :=
  (Scheme.isPullback_of_openCover (relativeProjToBase s') (relativeProjBaseChange g Φ hΦ) g
    (relativeProjToBase s) (baseChangeBaseCover g) (fun p =>
      Stacks.RelativeProj.isPullback_snd_fst_comp (relativeProjBaseChange g Φ hΦ)
        (relativeProjToBase s') (relativeProjToBase s) g p.1.1.1.ι
        (relativeProjChart s' p.1.1) (projInclusionToOpen s' p.1.1.1 p.1.1.2)
        (relativeProjChart_isPullback s' p.1.1)
        (isPullback_of_fst_eq
          (relativeProjChart_comp_relativeProjBaseChange g Φ hΦ p).symm
          (isPullback_chartBaseChangeHom g Φ hΦ p.1.2 p.1.1 p.2)))).flip

/-- The comparison isomorphism `relativeProj s' ≅ relativeProj s ×_S S'` with the fibre
product. -/
public def relativeProjBaseChangeIso :
    relativeProj s' ≅ pullback (relativeProjToBase s) g :=
  (isPullback_relativeProjBaseChange g Φ hΦ).isoPullback

/-- The comparison isomorphism composed with the projection to `relativeProj s` is the
comparison morphism. -/
@[simp] public theorem relativeProjBaseChangeIso_hom_fst :
    (relativeProjBaseChangeIso g Φ hΦ).hom ≫ pullback.fst (relativeProjToBase s) g =
      relativeProjBaseChange g Φ hΦ :=
  (isPullback_relativeProjBaseChange g Φ hΦ).isoPullback_hom_fst

/-- The comparison isomorphism is a morphism over `S'`. -/
@[simp] public theorem relativeProjBaseChangeIso_hom_snd :
    (relativeProjBaseChangeIso g Φ hΦ).hom ≫ pullback.snd (relativeProjToBase s) g =
      relativeProjToBase s' :=
  (isPullback_relativeProjBaseChange g Φ hΦ).isoPullback_hom_snd

/-- The comparison morphism is a morphism over `g`. -/
public theorem relativeProjBaseChange_comp_relativeProjToBase :
    relativeProjBaseChange g Φ hΦ ≫ relativeProjToBase s = relativeProjToBase s' ≫ g :=
  (isPullback_relativeProjBaseChange g Φ hΦ).w

end Situation

end Stacks.RelativeProj

end
