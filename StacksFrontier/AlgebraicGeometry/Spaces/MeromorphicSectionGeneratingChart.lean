module

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionHonestChart
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionRegularFreeGenerator

/-!
# A regular meromorphic section generates an invertible module on a nonempty chart

Let `X` be an algebraic space over a scheme `S` satisfying hypotheses (a) and (b) of
Stacks 0ENA, let `ℒ` be an *invertible* `𝒪_X`-module and let `s` be a **regular** meromorphic
section of `ℒ`.  Then over a suitable nonempty étale chart `s` is not merely an honest section
of `ℒ` — it is a *free generator*: `r ↦ r • s` is a bijection of the regular functions of the
chart onto the sections of `ℒ` there.

This is the first sentence of the proof of Stacks 0EPS in its *full* strength.
`AlgebraicGeometry.Space.exists_nonempty_chart_eval_eq_toMeromorphicSectionValue` gives only the
honest-section half of that sentence, which is all the subsequent argument of the source uses,
and it gives it without assuming regularity; the generating half genuinely needs regularity and
a further shrinking of the chart, so it is a separate statement rather than a strengthening of
that one.  A non-regular section cannot be made to generate: the zero section is honest
everywhere and generates nowhere, and more generally `f · e` for a regular function `f` which is
a nonunit nonzerodivisor is a regular section that generates exactly on `D(f)`.

## Main results

* `AlgebraicGeometry.Space.eq_zero_of_mul_eq_zero_of_eval_eq_tmul`: the coefficient of a regular
  meromorphic section on a section is a nonzerodivisor of the meromorphic functions.
* `AlgebraicGeometry.Space.mem_nonZeroDivisors_of_isRegularMeromorphicSection_of_eval_eq_smul`:
  over an *affine* chart it is a nonzerodivisor of the regular functions.
* `AlgebraicGeometry.Space.exists_nonempty_generating_chart_eval_eq_toMeromorphicSectionValue`:
  **a regular meromorphic section of an invertible module freely generates it over some nonempty
  chart**, which can be taken over any prescribed chart `C` of `X` with a point.

## Implementation notes

The chart is obtained from the honest one by two further refinements and one shrinking.

1. `AlgebraicGeometry.Space.exists_nonempty_chart_eval_eq_toMeromorphicSectionValue` presents `s`
   as an honest section `e₁` of `ℒ` over a nonempty chart `W₁` over `C`; a point of `W₁` is
   carried along.
2. Stacks 0B8Q on the small étale site, in the form
   `AlgebraicGeometry.Space.exists_generator_cover_smul_of_isInvertible` that trivialises `ℒ`
   over the *regular* functions, gives a chart through that point over which `ℒ` is free of rank
   one with generator `e₀`, and
   `AlgebraicGeometry.Space.openChart` cuts out an affine chart `W₂` inside it through the
   point.  Over `W₂` the honest section is `e₁ = r₀ • e₀` for a unique regular function `r₀`.
3. `r₀` is a **nonzerodivisor**.  This is where regularity enters: over `W₂` the section `s` is
   the image of `(algebraMap r₀) ⊗ e₀`, so multiplication by `s` factors through multiplication
   by `algebraMap r₀`, and Stacks 0ENB's injectivity forces that to be injective
   (`AlgebraicGeometry.Space.eq_zero_of_mul_eq_zero_of_eval_eq_tmul`); `W₂` being affine,
   Stacks 0EN6(2) makes the meromorphic functions there the total ring of fractions, whose
   structure map is injective, so `r₀` itself is a nonzerodivisor
   (`AlgebraicGeometry.Space.mem_nonZeroDivisors_of_isRegularMeromorphicSection_of_eval_eq_smul`).
4. On the basic open `D(r₀)` the function `r₀` becomes a unit
   (`AlgebraicGeometry.RingedSpace.isUnit_res_basicOpen`), and a unit multiple of a free
   generator is a free generator.  That basic open is nonempty because the generic points of the
   chart scheme are dense, so the affine open chosen in step 2 contains one, and
   `AlgebraicGeometry.mem_basicOpen_of_mem_nonZeroDivisors_of_mem_genericPoints` puts every
   generic point lying in an affine open into the basic open of a nonzerodivisor there.

This is the same shrinking the honest-section statement performs for the *denominator* of the
coefficient; the point of assuming regularity is that it may be performed for the *numerator*
as well.

## References

* [Stacks Project, Tag 0EPS](https://stacks.math.columbia.edu/tag/0EPS)
* [Stacks Project, Tag 0EN5](https://stacks.math.columbia.edu/tag/0EN5)
* [Stacks Project, Tag 0EN6](https://stacks.math.columbia.edu/tag/0EN6)
* [Stacks Project, Tag 0ENA](https://stacks.math.columbia.edu/tag/0ENA)
* [Stacks Project, Tag 0ENB](https://stacks.math.columbia.edu/tag/0ENB)
* [Stacks Project, Tag 0B8Q](https://stacks.math.columbia.edu/tag/0B8Q)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] chartMeromorphicAlgebra

/-- **A unit multiple of a free generator is a free generator.**  `r ↦ r • (ρ • m)` is
`IsUnit.smul_bijective` at `ρ` composed with `r ↦ r • m`, the two scalars commuting. -/
private theorem bijective_smul_isUnit_smul {R₀ : Type*} [CommRing R₀] {M : Type*}
    [AddCommGroup M] [Module R₀ M] {m : M} (h : Function.Bijective fun r : R₀ ↦ r • m)
    {ρ : R₀} (hρ : IsUnit ρ) : Function.Bijective fun r : R₀ ↦ r • (ρ • m) := by
  have hcomm : ∀ c : R₀, c • (ρ • m) = ρ • (c • m) := fun c => by
    rw [smul_smul, mul_comm, smul_smul]
  have hcomp := (hρ.smul_bijective (β := M)).comp h
  refine ⟨fun c c' hcc' => hcomp.1 ?_, fun t => ?_⟩
  · exact ((hcomm c).symm.trans hcc').trans (hcomm c')
  · obtain ⟨c, hc⟩ := hcomp.2 t
    exact ⟨c, (hcomm c).trans hc⟩

/-- **A unit multiple of a member of a compatible family of free generators generates freely over
every chart below.**  Let `e₀` be a family of sections of `L` over the charts over `V₀`,
compatible with restriction and generating `L` freely over each of them, and let a section `e₃`
over a chart `W₃` over `V₀` be a *unit* multiple of the member of the family at `W₃`.  Then
`r ↦ r • e₃|_{W'}` is a bijection of `𝒪_F(W')` onto `L(W')` for every chart `W'` over `W₃`.

Both the unit and the family restrict, so the same presentation holds over every chart below,
and `AlgebraicGeometry.Space.bijective_smul_isUnit_smul` applies there. -/
private theorem forall_bijective_smul_chartRestrictLinear_of_eq_smul
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
    (L : Modules.{u, u} B S hS X.1 X.2) {V₀ W₃ : SmallEtale B S hS X.1}
    (e₀ : (W : SmallEtale B S hS X.1) → (W ⟶ V₀) → L.val.obj (op W))
    (hcompat : ∀ (W W' : SmallEtale B S hS X.1) (k : W ⟶ V₀) (g : W' ⟶ W),
      (L.val.map g.op).hom (e₀ W k) = e₀ W' (g ≫ k))
    (hbij : ∀ (W : SmallEtale B S hS X.1) (k : W ⟶ V₀),
      Function.Bijective fun r : chartRing B S hS X.1 X.2 W ↦ r • e₀ W k)
    (p : W₃ ⟶ V₀) {ρ : chartRing B S hS X.1 X.2 W₃} (hunit : IsUnit ρ)
    {e₃ : L.val.obj (op W₃)} (hsplit : e₃ = ρ • e₀ W₃ p) :
    ∀ (W' : SmallEtale B S hS X.1) (κ : W' ⟶ W₃),
      Function.Bijective fun r : chartRing B S hS X.1 X.2 W' ↦
        r • chartRestrictLinear L κ e₃ := by
  intro W' κ
  have hrestrict : chartRestrictLinear L κ e₃ =
      chartRestrict (hF := X.2) κ ρ • e₀ W' (κ ≫ p) := by
    rw [hsplit, chartRestrictLinear_smul L κ ρ (e₀ W₃ p)]
    exact congrArg (fun z : L.val.obj (op W') ↦ chartRestrict (hF := X.2) κ ρ • z)
      (hcompat W₃ W' p κ)
  rw [hrestrict]
  exact bijective_smul_isUnit_smul (hbij W' (κ ≫ p)) (hunit.map (chartRestrict (hF := X.2) κ))

section Coefficient

attribute [local instance] meromorphicSectionModuleRingedSiteModule

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **A regular meromorphic section whose coefficient on a section kills a meromorphic function
kills that function.**  If a meromorphic section `s` of a sheaf of `𝒪_F`-modules `L` is over an
étale chart `W` the image of the pure meromorphic section `c ⊗ m`, and multiplication by `s` is
injective on the meromorphic functions over `W` — Stacks 0ENB's condition at `W` — then `c` is a
nonzerodivisor there: `z · c = 0` forces `z = 0`.

Multiplication by a meromorphic function `z` carries `s` to the image of `(z · c) ⊗ m`, because
the sheafification map of Stacks 0EN5 is linear and the meromorphic sections over a chart are an
extension of scalars.  So `z · c = 0` makes `z · s` vanish, and injectivity makes `z` vanish.

This is the converse direction of
`AlgebraicGeometry.Space.injective_smul_eval_of_tmul_isUnit`, and unlike it needs nothing of
`m`: no freeness and no compatibility with restriction.  The conclusion is spelled out rather
than stated as membership of `nonZeroDivisors`, because the meromorphic functions over a chart
carry no registered commutative-ring instance at the spelling through the ringed site that
Stacks 0ENB's injectivity uses. -/
theorem eq_zero_of_mul_eq_zero_of_eval_eq_tmul
    (L : Modules.{u, u} B S hS F hF) (s : MeromorphicSection.{u, u} B S hS F hF L)
    (hs : IsRegularMeromorphicSection.{u, u} B S hS F hF L s)
    (W : SmallEtale B S hS F) (m : L.val.obj (op W))
    (c : meromorphicChartRing B S hS F hF W)
    (hpres : s.eval (op W) = toMeromorphicSectionSheaf B S hS F hF L W
      (c ⊗ₜ[chartRing B S hS F hF W] m :
        (meromorphicSectionModule B S hS F hF L).obj (op W)))
    (z : meromorphicChartRing B S hS F hF W) (hz : z * c = 0) :
    z = 0 := by
  have key : ∀ w : meromorphicChartRing B S hS F hF W,
      w • s.eval (op W) = toMeromorphicSectionSheaf B S hS F hF L W
        ((w * c) ⊗ₜ[chartRing B S hS F hF W] m :
          (meromorphicSectionModule B S hS F hF L).obj (op W)) := by
    intro w
    rw [hpres]
    refine Eq.trans ?_ (congrArg (toMeromorphicSectionSheaf B S hS F hF L W)
      (meromorphicSectionModule_smul_tmul B S hS F hF L W _ w c m rfl))
    exact (toMeromorphicSectionSheaf_smul B S hS F hF L W w _).symm
  refine hs W ((key z).trans (Eq.trans ?_ (key 0).symm))
  rw [hz, zero_mul]

end Coefficient

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **The coefficient of a regular meromorphic section on a section over an affine chart is a
nonzerodivisor of the regular functions.**  Let `X` satisfy hypotheses (a) and (b) of
Stacks 0ENA, let `s` be a regular meromorphic section of a sheaf of `𝒪_X`-modules `L` and
suppose that over an *affine* étale chart `W` the section `s` is the image of `r · m` for a
regular function `r` and a section `m` of `L`.  Then `r` is a nonzerodivisor of `𝒪_X(W)`.

The image of `r · m` is the pure meromorphic section `(algebraMap r) ⊗ m`, so `algebraMap r`
kills no meromorphic function by
`AlgebraicGeometry.Space.eq_zero_of_mul_eq_zero_of_eval_eq_tmul`; the chart being affine,
Stacks 0EN6(2) makes `𝒦_X(W)` the total ring of fractions of `𝒪_X(W)`, whose structure map is
injective, so `r` kills no regular function either. -/
theorem mem_nonZeroDivisors_of_isRegularMeromorphicSection_of_eval_eq_smul
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    (L : Modules.{u, u} B S hS X.1 X.2) (s : MeromorphicSection.{u, u} B S hS X.1 X.2 L)
    (hs : IsRegularMeromorphicSection.{u, u} B S hS X.1 X.2 L s)
    (W : SmallEtale B S hS X.1) (hW : IsAffine (chartScheme W))
    (m : L.val.obj (op W)) (r : chartRing B S hS X.1 X.2 W)
    (he : s.eval (op W) = toMeromorphicSectionValue B S hS X.1 X.2 L W (r • m)) :
    r ∈ nonZeroDivisors (chartRing B S hS X.1 X.2 W) := by
  have hpres : s.eval (op W) = toMeromorphicSectionSheaf B S hS X.1 X.2 L W
      ((algebraMap (chartRing B S hS X.1 X.2 W)
          ((meromorphicChartSheaf B S hS X.1 X.2).obj.obj (op W)) r) ⊗ₜ[
        chartRing B S hS X.1 X.2 W] m :
          (meromorphicSectionModule B S hS X.1 X.2 L).obj (op W)) := by
    rw [he, toMeromorphicSectionValue_eq]
    exact congrArg (toMeromorphicSectionSheaf B S hS X.1 X.2 L W)
      (pureMeromorphicSection_smul_eq_algebraMap_tmul B S hS X.1 X.2 L W r m)
  let : Algebra ((structurePresheaf B S hS X.1).obj (op W))
      ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op W)) :=
    ((toMeromorphicFunctionSheaf B S hS X.1 X.2).hom.app (op W)).hom.toAlgebra
  have := isFractionRing_meromorphicFunctionSheaf_obj B S hS X hwa hfin W hW
  have hinj : Function.Injective (algebraMap (chartRing B S hS X.1 X.2 W)
      ((meromorphicChartSheaf B S hS X.1 X.2).obj.obj (op W))) :=
    IsFractionRing.injective ((structurePresheaf B S hS X.1).obj (op W))
      ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op W))
  refine mem_nonZeroDivisors_iff_right.mpr fun y hy => ?_
  have h1 : algebraMap (chartRing B S hS X.1 X.2 W)
        ((meromorphicChartSheaf B S hS X.1 X.2).obj.obj (op W)) y *
      algebraMap (chartRing B S hS X.1 X.2 W)
        ((meromorphicChartSheaf B S hS X.1 X.2).obj.obj (op W)) r = 0 := by
    rw [← map_mul, hy, map_zero]
  exact hinj ((eq_zero_of_mul_eq_zero_of_eval_eq_tmul B S hS X.1 X.2 L s hs W m _ hpres _ h1).trans
    (map_zero _).symm)

/-- **Steps 3 and 4 of the generating chart: shrinking an affine chart to where the coefficient
is a unit.**  Let `s` be a regular meromorphic section of `L`, let `V₁` be an étale chart of `X`
with an affine open `O` of its scheme through a point `x₂`, let `e₀` be a compatible family of
free generators of `L` over the charts over a chart `V₀` receiving `V₁`, and suppose `s` is over
the affine chart `O` of `V₁` the image of a section `m` which is the `r₀`-multiple of the member
of that family there.  Then there is a chart `W₃` over `O`, with a point, over which `s` is an
honest section freely generating `L` there and over every chart below.

`r₀` is a nonzerodivisor of the regular functions on `O` by
`AlgebraicGeometry.Space.mem_nonZeroDivisors_of_isRegularMeromorphicSection_of_eval_eq_smul`,
which is where regularity enters; `W₃` is the basic open of `r₀` inside `O`, where `r₀` becomes
a unit (`AlgebraicGeometry.RingedSpace.isUnit_res_basicOpen`), and it is nonempty because the
generic points of the chart scheme are dense, so `O` contains one, and every generic point of an
affine open lies in the basic open of a nonzerodivisor there.  Free generation over the charts
below is `AlgebraicGeometry.Space.forall_bijective_smul_chartRestrictLinear_of_eq_smul`. -/
private theorem exists_nonempty_generating_chart_over_openChart
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    (L : Modules.{u, u} B S hS X.1 X.2) (s : MeromorphicSection.{u, u} B S hS X.1 X.2 L)
    (hs : IsRegularMeromorphicSection.{u, u} B S hS X.1 X.2 L s)
    (V₁ : SmallEtale B S hS X.1) (O : (chartScheme V₁).Opens) (hOaff : IsAffineOpen O)
    (x₂ : chartScheme V₁) (hx₂O : x₂ ∈ O)
    (V₀ : SmallEtale B S hS X.1) (q : V₁ ⟶ V₀)
    (e₀ : (W : SmallEtale B S hS X.1) → (W ⟶ V₀) → L.val.obj (op W))
    (hcompat : ∀ (W W' : SmallEtale B S hS X.1) (k : W ⟶ V₀) (g : W' ⟶ W),
      (L.val.map g.op).hom (e₀ W k) = e₀ W' (g ≫ k))
    (hbij : ∀ (W : SmallEtale B S hS X.1) (k : W ⟶ V₀),
      Function.Bijective fun r : chartRing B S hS X.1 X.2 W ↦ r • e₀ W k)
    (m : L.val.obj (op (openChart B S hS X.1 V₁ O)))
    (hm : s.eval (op (openChart B S hS X.1 V₁ O)) =
      toMeromorphicSectionValue B S hS X.1 X.2 L (openChart B S hS X.1 V₁ O) m) :
    ∃ (W₃ : SmallEtale B S hS X.1) (_ : W₃ ⟶ openChart B S hS X.1 V₁ O)
      (e₃ : L.val.obj (op W₃)),
      Nonempty (chartScheme W₃) ∧
        s.eval (op W₃) = toMeromorphicSectionValue B S hS X.1 X.2 L W₃ e₃ ∧
        ∀ (W' : SmallEtale B S hS X.1) (κ : W' ⟶ W₃),
          Function.Bijective fun r : chartRing B S hS X.1 X.2 W' ↦
            r • chartRestrictLinear L κ e₃ := by
  classical
  have hW₂aff : IsAffine (chartScheme (openChart B S hS X.1 V₁ O)) := hOaff
  obtain ⟨r₀, hr₀raw⟩ :=
    (hbij (openChart B S hS X.1 V₁ O) (openChartInclusion B S hS X.1 V₁ O ≫ q)).2 m
  have hr₀ : r₀ • e₀ (openChart B S hS X.1 V₁ O)
      (openChartInclusion B S hS X.1 V₁ O ≫ q) = m := hr₀raw
  -- Step 3: regularity of `s` makes the coefficient `r₀` a nonzerodivisor.
  have hr₀nzd : r₀ ∈ nonZeroDivisors
      (chartRing B S hS X.1 X.2 (openChart B S hS X.1 V₁ O)) :=
    mem_nonZeroDivisors_of_isRegularMeromorphicSection_of_eval_eq_smul B S hS X hwa hfin L s hs
      (openChart B S hS X.1 V₁ O) hW₂aff
      (e₀ (openChart B S hS X.1 V₁ O) (openChartInclusion B S hS X.1 V₁ O ≫ q)) r₀
      (hm.trans (congrArg
        (toMeromorphicSectionValue B S hS X.1 X.2 L (openChart B S hS X.1 V₁ O)) hr₀.symm))
  -- Step 4: shrink to the basic open of `r₀`, which is nonempty and on which `r₀` is a unit.
  set σ := (openChartGlobalSectionsIso V₁ O).commRingCatIsoToRingEquiv with hσdef
  have hσnzd : σ r₀ ∈ nonZeroDivisors Γ(chartScheme V₁, O) := by
    rw [← MulEquivClass.map_nonZeroDivisors σ]
    exact ⟨r₀, hr₀nzd, rfl⟩
  have hDle : (chartScheme V₁).basicOpen (σ r₀) ≤ O := Scheme.basicOpen_le _ _
  set W₃ : SmallEtale B S hS X.1 :=
    openChart B S hS X.1 V₁ ((chartScheme V₁).basicOpen (σ r₀)) with hW₃def
  set j : W₃ ⟶ openChart B S hS X.1 V₁ O :=
    openChartHomOfLE B S hS X.1 V₁ hDle with hjdef
  obtain ⟨y, hyO, hygen⟩ :=
    (dense_iff_closure_eq.mpr genericPoints.closure :
      Dense (genericPoints (chartScheme V₁))).inter_open_nonempty _ O.isOpen ⟨x₂, hx₂O⟩
  have hyD : y ∈ (chartScheme V₁).basicOpen (σ r₀) :=
    mem_basicOpen_of_mem_nonZeroDivisors_of_mem_genericPoints
      (schemeWeaklyAssociatedPoints_chartScheme_subset_genericPoints B S hS X hwa V₁)
      (fun Wo hWo ↦ finite_irreducibleComponents_chartScheme B S hS hfin V₁ Wo hWo)
      hOaff hσnzd hygen hyO
  have hrj : σ.symm (σ r₀) = r₀ := σ.symm_apply_apply r₀
  set σ' := (openChartGlobalSectionsIso V₁
    ((chartScheme V₁).basicOpen (σ r₀))).commRingCatIsoToRingEquiv with hσ'def
  have hres : ((structurePresheaf B S hS X.1).map j.op).hom (σ.symm (σ r₀)) =
      σ'.symm (((chartScheme V₁).presheaf.map (homOfLE hDle).op).hom (σ r₀)) :=
    ConcreteCategory.congr_hom
      (openChartGlobalSectionsIso_inv_comp B S hS X.1 V₁ hDle) (σ r₀)
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : chartRing B S hS X.1 X.2 W₃,
      ρ = ((structurePresheaf B S hS X.1).map j.op).hom r₀ := ⟨_, rfl⟩
  have hunit : IsUnit ρ := by
    rw [hρdef, ← hrj, hres]
    exact ((chartScheme V₁).toRingedSpace.isUnit_res_basicOpen (σ r₀)).map σ'.symm
  -- Assembling.
  obtain ⟨e₃, he₃⟩ : ∃ e₃ : L.val.obj (op W₃), e₃ = (L.val.map j.op).hom m := ⟨_, rfl⟩
  have hsplit : e₃ = ρ • e₀ W₃ (j ≫ openChartInclusion B S hS X.1 V₁ O ≫ q) := by
    rw [he₃, ← hr₀, ← hcompat (openChart B S hS X.1 V₁ O) W₃
      (openChartInclusion B S hS X.1 V₁ O ≫ q) j, hρdef]
    exact (L.val.map j.op).hom.map_smul r₀
      (e₀ (openChart B S hS X.1 V₁ O) (openChartInclusion B S hS X.1 V₁ O ≫ q))
  exact ⟨W₃, j, e₃, ⟨⟨y, hyD⟩⟩,
    he₃ ▸ eval_eq_toMeromorphicSectionValue_of_hom B S hS X.1 X.2 L s j m hm,
    forall_bijective_smul_chartRestrictLinear_of_eq_smul L e₀ hcompat hbij
      (j ≫ openChartInclusion B S hS X.1 V₁ O ≫ q) hunit hsplit⟩

/-- **A regular meromorphic section of an invertible module freely generates it over some
nonempty chart.**  Let `X` be an algebraic space over `S` satisfying hypotheses (a) and (b) of
Stacks 0ENA, let `ℒ` be an invertible `𝒪_X`-module, let `s` be a *regular* meromorphic section
of `ℒ` and let `C` be an étale chart of `X` with a point.  Then there is an étale chart `W` of
`X` over `C`, with nonempty underlying scheme, over which `s` is the image under
`AlgebraicGeometry.Space.toMeromorphicSectionValue` of a section `e` of `ℒ` which *freely
generates* `ℒ` there and over every chart below: `r ↦ r • e|_{W'}` is a bijection of `𝒪_X(W')`
onto `ℒ(W')` for every `W' ⟶ W`.

This is the first sentence of the proof of Stacks 0EPS in full: the source says that a regular
`s` generates `ℒ` over a nonempty open subspace.  See the implementation notes of this module
for the four steps and for why regularity cannot be dropped.

Free generation is asserted over the charts *below* `W`, not only over `W` itself.  That is what
the proof produces — `e` is a unit multiple of a member of the compatible family of free
generators of `AlgebraicGeometry.Space.exists_generator_cover_smul_of_isInvertible`, and both
the unit and the family restrict — and freeness over one chart alone does not pass to the
charts below it.  Taking `W' = W` and the identity recovers the
statement over `W`. -/
theorem exists_nonempty_generating_chart_eval_eq_toMeromorphicSectionValue
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    (L : Modules.{u, u} B S hS X.1 X.2)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property L)
    (s : MeromorphicSection.{u, u} B S hS X.1 X.2 L)
    (hs : IsRegularMeromorphicSection.{u, u} B S hS X.1 X.2 L s)
    (C : SmallEtale B S hS X.1) (x : chartScheme C) :
    ∃ (W : SmallEtale B S hS X.1) (_ : W ⟶ C) (e : L.val.obj (op W)),
      Nonempty (chartScheme W) ∧
        s.eval (op W) = toMeromorphicSectionValue B S hS X.1 X.2 L W e ∧
        ∀ (W' : SmallEtale B S hS X.1) (κ : W' ⟶ W),
          Function.Bijective fun r : chartRing B S hS X.1 X.2 W' ↦
            r • chartRestrictLinear L κ e := by
  classical
  -- Step 1: an honest presentation on a nonempty chart over `C`.
  obtain ⟨W₁, k₁, e₁, hne₁, he₁⟩ :=
    exists_nonempty_chart_eval_eq_toMeromorphicSectionValue B S hS X hwa hfin L hL s C x
  obtain ⟨x₁⟩ := hne₁
  -- Step 2: a chart of `W₁` through `x₁` on which `ℒ` is free of rank one over the regular
  -- functions, and an affine open of its scheme through the point.
  obtain ⟨I, V, a, hcov, hfree⟩ := exists_generator_cover_smul_of_isInvertible B S hS X L hL W₁
  obtain ⟨V₁, g₁, hg₁, x₂, -⟩ :=
    (SmallEtale.mem_topology_iff_exists_mem_range B S hS X.1 (Sieve.ofArrows V a)).1 hcov x₁
  obtain ⟨i, b, rfl⟩ := (Sieve.mem_ofArrows_iff V a g₁).1 hg₁
  obtain ⟨e₀, hcompat, hbij⟩ := hfree i
  obtain ⟨O, hOaff, hx₂O⟩ : ∃ O : (chartScheme V₁).Opens, IsAffineOpen O ∧ x₂ ∈ O := by
    obtain ⟨O, hO⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (show x₂ ∈ ⨆ O : (chartScheme V₁).affineOpens, (O : (chartScheme V₁).Opens) from
        (iSup_affineOpens_eq_top (chartScheme V₁)).ge trivial)
    exact ⟨O.1, O.2, hO⟩
  -- Steps 3 and 4: regularity makes the coefficient a nonzerodivisor, and the chart is shrunk
  -- to the basic open where it becomes a unit.
  obtain ⟨W₃, j, e₃, hne₃, he₃, hfam⟩ :=
    exists_nonempty_generating_chart_over_openChart B S hS X hwa hfin L s hs V₁ O hOaff x₂
      hx₂O (V i) b e₀ hcompat hbij
      ((L.val.map (openChartInclusion B S hS X.1 V₁ O ≫ b ≫ a i).op).hom e₁)
      (eval_eq_toMeromorphicSectionValue_of_hom B S hS X.1 X.2 L s
        (openChartInclusion B S hS X.1 V₁ O ≫ b ≫ a i) e₁ he₁)
  exact ⟨W₃, j ≫ openChartInclusion B S hS X.1 V₁ O ≫ b ≫ a i ≫ k₁, e₃, hne₃, he₃, hfam⟩

end AlgebraicGeometry.Space

end
