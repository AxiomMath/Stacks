module

public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceTensorPullbackLocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramSieveRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatChartSectionOrderTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingGeneratorLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FreeGeneratorSieveDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineMemberThroughPoint

/-!
# Chart diagrams carrying a free generator of an invertible module and of its pullback

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` and `ℒ` an invertible
`𝒪_Y`-module. This file constructs diagrams of affine étale charts `U ⟶ V` over `f` over which `ℒ`
is free on a generator `e` and `f^*ℒ` is free on the pulled back generator `f^*e`, and compares
the readings of meromorphic functions at points of the two charts.

## Main results

* `AlgebraicGeometry.Space.bijective_smul_modulePullbackChartSectionRestrict`: the inverse image
  of a free generator is a free generator over every chart of the source chart.
* `AlgebraicGeometry.Space.exists_affine_chartDiagram_generator_through`: through every point of
  `X` there is a diagram of affine étale charts over `f` whose chart of `Y` carries a compatible
  family of free generators of `ℒ`.
* `AlgebraicGeometry.Space.chartPointMeromorphicMap_chartMeromorphicFunctionPullback_of_le`: the
  germ square for the chart pullback of meromorphic functions, for any chart diagram whose stalk
  map carries nonzerodivisors to nonzerodivisors.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 0B8P](https://stacks.math.columbia.edu/tag/0B8P)
* [Stacks Project, Tag 0ENC](https://stacks.math.columbia.edu/tag/0ENC)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-! ### The inverse image of a free generator generates freely everywhere -/

/-- **The inverse image of a free generator is a free generator over every chart of the source
chart.** Let `M` be an invertible `𝒪_Y`-module, `d` a commuting square of étale scheme charts
over `f`, and `e` a compatible family of free generators of `M` over the charts over `d.V`. Then
for every chart `W` over `d.U` the restriction of `f^*e` to `W` generates `f^*M` freely over
`W`. -/
theorem bijective_smul_modulePullbackChartSectionRestrict (f : X ⟶ Y)
    (M : Modules.{u, u} B S hS Y.1 Y.2)
    (hM : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS Y)
      (structureRingSheaf B S hS Y).property M)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (e : (W : SmallEtale B S hS Y.1) → (W ⟶ d.V) → M.val.obj (op W))
    (hcompat : ∀ (W W' : SmallEtale B S hS Y.1) (k : W ⟶ d.V) (g : W' ⟶ W),
      (M.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hbij : ∀ (W : SmallEtale B S hS Y.1) (k : W ⟶ d.V),
      Function.Bijective fun r : chartRing B S hS Y.1 Y.2 W ↦ r • e W k)
    (W : SmallEtale B S hS X.1) (k : W ⟶ d.U) :
    Function.Bijective fun r : chartRing B S hS X.1 X.2 W ↦
      r • modulePullbackChartSectionRestrict B S hS f M d (e d.V (𝟙 d.V)) k := by
  obtain ⟨T, hT, hTbij⟩ := exists_sieve_bijective_smul_modulePullbackChartSection B S hS f M
    hM d e hcompat hbij
  refine bijective_smul_of_sieve B S hS X ((modulePullback B S hS f).obj M) W
    (modulePullbackChartSectionRestrict B S hS f M d (e d.V (𝟙 d.V)) k) (T.pullback k)
    ((SmallEtale.topology B S hS X.1).pullback_stable k hT) fun W' k' hk' => ?_
  have hres : chartRestrictLinear ((modulePullback B S hS f).obj M) k'
      (modulePullbackChartSectionRestrict B S hS f M d (e d.V (𝟙 d.V)) k) =
      modulePullbackChartSectionRestrict B S hS f M d (e d.V (𝟙 d.V)) (𝟙 W' ≫ k' ≫ k) := by
    rw [Category.id_comp]
    exact modulePullbackChartSectionRestrict_map B S hS f M d (e d.V (𝟙 d.V)) k k'
  rw [hres]
  exact hTbij (k' ≫ k) hk' W' (𝟙 W')

/-- The pulled back generators over the charts over `d.U` form a compatible family. -/
theorem modulePullbackChartSectionRestrict_compat (f : X ⟶ Y)
    (M : Modules.{u, u} B S hS Y.1 Y.2) (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (s : M.val.obj (op d.V)) (W W' : SmallEtale B S hS X.1) (k : W ⟶ d.U) (g : W' ⟶ W) :
    (((modulePullback B S hS f).obj M).val.map g.op).hom
        (modulePullbackChartSectionRestrict B S hS f M d s k) =
      modulePullbackChartSectionRestrict B S hS f M d s (g ≫ k) :=
  modulePullbackChartSectionRestrict_map B S hS f M d s k g

/-- At the identity chart the pulled back generator is the chart component of the unit of the
pullback adjunction, applied to the generator. -/
theorem modulePullbackChartSectionRestrict_id (f : X ⟶ Y)
    (M : Modules.{u, u} B S hS Y.1 Y.2) (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (s : M.val.obj (op d.V)) :
    modulePullbackChartSectionRestrict B S hS f M d s (𝟙 d.U) =
      (modulePullbackChartFMap B S hS f M).app d s :=
  CategoryTheory.congr_fun
    (((modulePullback B S hS f).obj M).val.presheaf.map_id (op d.U))
    ((modulePullbackChartFMap B S hS f M).app d s)

/-! ### Diagrams of affine charts carrying a free generator -/

/-- **Through every point of `X` there is a diagram of affine étale charts over `f` whose chart of
`Y` carries a compatible family of free generators of an invertible `𝒪_Y`-module `ℒ`.** -/
theorem exists_affine_chartDiagram_generator_through (f : X ⟶ Y)
    (L : Modules.{u, u} B S hS Y.1 Y.2)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS Y)
      (structureRingSheaf B S hS Y).property L)
    (x : points B S hS X.1) :
    ∃ (d : ChartDiagram B S hS X.1 Y.1 f.hom) (u : chartScheme d.U),
      IsAffine (chartScheme d.U) ∧ IsAffine (chartScheme d.V) ∧
      chartSchemeToPoints B S hS X.1 d.U u = x ∧
      ∃ e : (W : SmallEtale B S hS Y.1) → (W ⟶ d.V) → L.val.obj (op W),
        (∀ (W W' : SmallEtale B S hS Y.1) (k : W ⟶ d.V) (g : W' ⟶ W),
          (L.val.map g.op).hom (e W k) = e W' (g ≫ k)) ∧
        ∀ (W : SmallEtale B S hS Y.1) (k : W ⟶ d.V),
          Function.Bijective fun r : chartRing B S hS Y.1 Y.2 W ↦ r • e W k := by
  obtain ⟨d₀, w, hw⟩ := exists_chartDiagram_chartSchemeToPoints_eq B S hS f x
  obtain ⟨d₁, k₁, z, hU₁, hV₁, hz⟩ := exists_affine_chartDiagram_at_chartPoint B S hS f d₀.U w
  have hz' : chartSchemeToPoints B S hS X.1 d₁.U z = x := by
    rw [← hw, ← hz]
    exact (chartSchemeToPoints_map B S hS X.1 k₁ z).symm
  obtain ⟨I, V, a, hcov, hgen⟩ := exists_generator_cover_smul_of_isInvertible B S hS Y L hL d₁.V
  obtain ⟨n, d', a', k', hU', hV', hT, -, hcovU⟩ :=
    exists_affine_chartDiagram_cover_of_sieve B S hS f d₁ hU₁ hV₁ hcov
  obtain ⟨Q, φ, hφ, -, z', hz'eq⟩ :=
    SmallEtale.exists_affine_mem_range_of_mem_topology B S hS X.1 hcovU z
  obtain ⟨i, h, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hφ
  obtain ⟨l, h', hkl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 (hT i)
  obtain ⟨e, hecompat, hebij⟩ := hgen l
  refine ⟨d' i, (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map h) z',
    hU' i, hV' i, ?_, fun W m => e W (m ≫ h'), fun W W' m g => ?_, fun W m => ?_⟩
  · rw [chartSchemeToPoints_map B S hS X.1 h z', ← hz', ← hz'eq]
    exact (chartSchemeToPoints_map B S hS X.1 (h ≫ a' i) z').symm
  · exact (hecompat W W' (m ≫ h') g).trans (congrArg (e W') (Category.assoc g m h').symm)
  · exact hebij W (m ≫ h')

/-! ### The germ square for the chart pullback of meromorphic functions -/

attribute [local instance] chartMeromorphicFunctionAlgebra

/-- **The reading of a meromorphic function at a chart point, pushed along the stalk map**, for
any diagram of affine étale charts over `f : X ⟶ Y` whose stalk map at the point carries
nonzerodivisors to nonzerodivisors. Reading a meromorphic function `c` of `d.V` at `g(u)` and
pushing it along the stalk map of `g` gives the same element of `Q(𝒪_{d.U, u})` as reading the
chart pullback of `c` at `u`. -/
theorem chartPointMeromorphicMap_chartMeromorphicFunctionPullback_of_le (f : X ⟶ Y)
    (hfm : PullbacksMeromorphicSections B S hS f.hom)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hU : IsAffine (chartScheme d.U)) (hV : IsAffine (chartScheme d.V))
    (hKU : IsFractionRing ((structurePresheaf B S hS X.1).obj (op d.U))
      ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op d.U)))
    (hKV : IsFractionRing ((structurePresheaf B S hS Y.1).obj (op d.V))
      ((meromorphicFunctionSheaf B S hS Y.1 Y.2).obj.obj (op d.V)))
    (u : chartScheme d.U)
    (hφ : ((chartScheme d.V).presheaf.stalk
        (((BigFppfOver.toScheme B S hS).map d.g).base u))⁰ ≤
      ((chartScheme d.U).presheaf.stalk u)⁰.comap
        (((BigFppfOver.toScheme B S hS).map d.g).stalkMap u).hom)
    (c : (meromorphicFunctionSheaf B S hS Y.1 Y.2).obj.obj (op d.V)) :
    IsLocalization.map (T := ((chartScheme d.U).presheaf.stalk u)⁰)
        (FractionRing ((chartScheme d.U).presheaf.stalk u))
        (((BigFppfOver.toScheme B S hS).map d.g).stalkMap u).hom hφ
        (chartPointMeromorphicMap B S hS Y d.V hV hKV
          (((BigFppfOver.toScheme B S hS).map d.g).base u) c) =
      chartPointMeromorphicMap B S hS X d.U hU hKU u
        (chartMeromorphicFunctionPullback B S hS f hfm d c) := by
  have := hKU
  have := hKV
  set g := (BigFppfOver.toScheme B S hS).map d.g with hg
  let ψ : FractionRing ((chartScheme d.V).presheaf.stalk (g.base u)) →+*
      FractionRing ((chartScheme d.U).presheaf.stalk u) :=
    IsLocalization.map (T := ((chartScheme d.U).presheaf.stalk u)⁰)
      (FractionRing ((chartScheme d.U).presheaf.stalk u)) (g.stalkMap u).hom hφ
  have key : ψ.comp (chartPointMeromorphicMap B S hS Y d.V hV hKV (g.base u)) =
      (chartPointMeromorphicMap B S hS X d.U hU hKU u).comp
        (chartMeromorphicFunctionPullback B S hS f hfm d) := by
    refine IsLocalization.ringHom_ext ((structurePresheaf B S hS Y.1).obj (op d.V))⁰
      (RingHom.ext fun a => ?_)
    have hpull : chartMeromorphicFunctionPullback B S hS f hfm d
          (algebraMap ((structurePresheaf B S hS Y.1).obj (op d.V))
            ((meromorphicFunctionSheaf B S hS Y.1 Y.2).obj.obj (op d.V)) a) =
        algebraMap ((structurePresheaf B S hS X.1).obj (op d.U))
          ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op d.U))
          (chartDiagramRestrict B S hS f d a) :=
      RingHom.congr_fun (chartMeromorphicFunctionPullback_algebraMap B S hS f hfm d) a
    have h1 := chartPointMeromorphicMap_algebraMap B S hS Y d.V hV hKV (g.base u) a
    have h2 := chartPointMeromorphicMap_algebraMap B S hS X d.U hU hKU u
      (chartDiagramRestrict B S hS f d a)
    have h4 : ψ (algebraMap ((chartScheme d.V).presheaf.stalk (g.base u))
          (FractionRing ((chartScheme d.V).presheaf.stalk (g.base u)))
          (((chartScheme d.V).presheaf.germ ⊤ (g.base u) trivial).hom a)) =
        algebraMap ((chartScheme d.U).presheaf.stalk u)
          (FractionRing ((chartScheme d.U).presheaf.stalk u))
          ((g.stalkMap u).hom
            (((chartScheme d.V).presheaf.germ ⊤ (g.base u) trivial).hom a)) :=
      IsLocalization.map_eq _ _
    refine (congrArg ψ h1).trans (h4.trans (Eq.trans ?_ ((congrArg
      (chartPointMeromorphicMap B S hS X d.U hU hKU u) hpull).trans h2).symm))
    exact congrArg (algebraMap _ _) (Scheme.Hom.germ_stalkMap_apply g ⊤ u trivial a)
  exact RingHom.congr_fun key c

end AlgebraicGeometry.Space

end
