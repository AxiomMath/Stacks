module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.EtaleLocalLift
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmoothSquares
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlasFormallySmooth
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AffineEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheaf

/-!
# Local existence of lifts: the sheaf of lifts of a smooth morphism is locally nonempty

Let `Z ⊂ X'` be a first-order thickening of algebraic spaces over `S`, let `p : X' ⟶ Bb` and
`q : Y ⟶ Bb` be morphisms of algebraic spaces and let `a : Z ⟶ Y` be a morphism with
`a ≫ q = Z.ι ≫ p`, so that extending `a` over `X'` is a lifting problem for `q` along the
thickening.  The sheaf of lifts of [Stacks Project, Tag 061D],
`AlgebraicGeometry.Space.liftsSubfunctor`, is then **locally nonempty on the small étale site of
`X'` as soon as `q` is smooth**.

Smoothness of `q` is not removable.  Without it the statement is false: the module docstring of
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftTorsorGlueing` records a counterexample
(`Bb = Spec k[s]`, `Y = Spec k` with `q` the origin, `X' = Spec k[ε]/(ε²)` over `Bb` by
`s ↦ ε`), and [Stacks Project, Tag 061C] correspondingly asserts only the *pseudo*-torsor
property, simple transitivity over the objects where a section happens to exist.  Local
nonemptiness is the content of [Stacks Project, Tag 04AM], and it is what this file supplies.

## Main results

* `AlgebraicGeometry.Space.exists_isChartLift_of_isAffine_at_point`: over an affine étale chart
  of `X'` and through every point of it, there is a smaller affine étale chart carrying a lift.
* `AlgebraicGeometry.Space.exists_isChartLift_at_point`: the same through every point of an
  arbitrary étale chart, by cutting the chart down to an affine open.

## Implementation notes

The lift is produced by [Stacks Project, Tag 04CY],
`AlgebraicGeometry.Space.exists_etale_affine_local_lift`, which solves the lifting problem on an
affine étale neighbourhood of one point at a time.  Its three inputs are supplied as follows.

* The square-zero closed immersion of affine objects of the site is the chart of the thickening,
  `AlgebraicGeometry.Space.exists_squareZeroChart_of_isFirstOrderThickening`.
* Its formal smoothness hypothesis is about the composite of `q` with a surjective étale atlas
  of `Y`, not about `q` itself, and that is exactly
  `AlgebraicGeometry.Space.exists_atlas_formallySmooth_comp_of_isSmooth`.  This is why no
  descent of formal smoothness along a chart — the undischarged step (II) of
  [Stacks Project, Tag 04AM] — is needed here.
* The point of the closed subscheme lying over the given point of the chart exists because a
  square-zero closed immersion is a thickening, hence surjective on points:
  `Stacks.Thickenings.IsFirstOrderThickening.isThickening`.

The compatibility clause of `AlgebraicGeometry.Space.IsChartLift` is read off the last clause of
`AlgebraicGeometry.Space.exists_etale_affine_local_lift`, which states agreement of the produced
section with the given one over every common refinement; the refinement is produced from the
chart of the thickening being a pullback square, and full faithfulness of Yoneda turns the
resulting morphism of presheaves into a morphism of the site.

## References

* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 04CY](https://stacks.math.columbia.edu/tag/04CY)
* [Stacks Project, Tag 061C](https://stacks.math.columbia.edu/tag/061C)
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
variable {Bb X' Y : AlgebraicSpaces C S hS}

/-- **Over an affine étale chart of `X'`, a lift exists on an affine étale neighbourhood of
every point**, granted that `q` is smooth.

The chart of the thickening on the given affine chart is a square-zero closed immersion of
affine objects of the site, so it is a thickening and in particular surjective on points: the
given point of the chart is the image of a point of the closed subscheme.  Over that point
[Stacks Project, Tag 04CY] produces an affine étale neighbourhood together with a section of `Y`
lifting the structure morphism to `Bb` and agreeing with `a` over every common refinement, which
is the lifting condition of `AlgebraicGeometry.Space.IsChartLift`. -/
theorem exists_isChartLift_of_isAffine_at_point (p : X' ⟶ Bb) (q : Y ⟶ Bb)
    {Z : Subfunctor X'.1} (a : Z.toFunctor ⟶ Y.1)
    (hX : IsFirstOrderThickening C S hS X' Z) (ha : a ≫ q.hom = Z.ι ≫ p.hom)
    (hq : IsSmooth C S hS q.hom) (U' : SmallEtale C S hS X'.1)
    (hU' : IsAffine
      ((BigFppfOver.toScheme C S hS).obj ((SmallEtale.toOver C S hS X'.1).obj U')))
    (x : (BigFppfOver.toScheme C S hS).obj ((SmallEtale.toOver C S hS X'.1).obj U')) :
    ∃ (V' : SmallEtale C S hS X'.1) (r : V' ⟶ U')
      (β : Y.1.obj (op ((SmallEtale.toOver C S hS X'.1).obj V'))),
      IsAffine ((BigFppfOver.toScheme C S hS).obj
          ((SmallEtale.toOver C S hS X'.1).obj V')) ∧
        IsChartLift C S hS p q a V' (yonedaEquiv.symm β) ∧
        x ∈ Set.range ((BigFppfOver.toScheme C S hS).map
          ((SmallEtale.toOver C S hS X'.1).map r)) := by
  classical
  -- An étale atlas of `Y` whose composite with `q` is formally smooth.
  obtain ⟨W, α, hαS, hαE, hsm⟩ :=
    exists_atlas_formallySmooth_comp_of_isSmooth C S hS Y.2 Bb.2 q.hom hq
  -- The chart of the thickening on `U'`: a square-zero closed immersion of affine objects.
  obtain ⟨T₀, i₀, u₀, hpb, hT₀aff, hu₀, hsz⟩ :=
    exists_squareZeroChart_of_isFirstOrderThickening C S hS hX
      ((SmallEtale.toOver C S hS X'.1).obj U') U'.1.hom
      ((isEtale_iff_presheaf_of_yoneda C S hS U'.1.hom).2 U'.property) hU'
  -- A square-zero closed immersion is a thickening, hence surjective on points.
  obtain ⟨t, ht⟩ :=
    (isFirstOrderThickening_of_isSquareZeroClosedImmersion hsz).isThickening.2 x
  -- The lifting problem over the chart, as a compatible pair of sections.
  have hxy : (q.hom).app (op T₀) (yonedaEquiv (u₀ ≫ a)) =
      Bb.1.map i₀.op (yonedaEquiv (U'.1.hom ≫ p.hom)) := by
    calc (q.hom).app (op T₀) (yonedaEquiv (u₀ ≫ a))
        = yonedaEquiv ((u₀ ≫ a) ≫ q.hom) := (yonedaEquiv_comp _ _).symm
      _ = yonedaEquiv (u₀ ≫ a ≫ q.hom) := by rw [Category.assoc]
      _ = yonedaEquiv (u₀ ≫ Z.ι ≫ p.hom) := by rw [ha]
      _ = yonedaEquiv ((yoneda.map i₀ ≫ U'.1.hom) ≫ p.hom) := by
            rw [hpb.w, Category.assoc]
      _ = yonedaEquiv (yoneda.map i₀ ≫ U'.1.hom ≫ p.hom) := by rw [Category.assoc]
      _ = Bb.1.map i₀.op (yonedaEquiv (U'.1.hom ≫ p.hom)) :=
            (yonedaEquiv_naturality _ _).symm
  -- The étale-local lift of Tag 04CY at the chosen point.
  obtain ⟨V, j, z, hVaff, hjet, ⟨w, hw⟩, hzy, hagree⟩ :=
    exists_etale_affine_local_lift
      { B := C, S := S, hS := hS, F := yoneda.obj W, G := Y.1, H := Bb.1
        a := α, b := q.hom
        representable_a := hαE.1, surjective_a := hαS, etale_a := hαE }
      T₀ ((SmallEtale.toOver C S hS X'.1).obj U') i₀ hU' hsz
      (yonedaEquiv (u₀ ≫ a)) (yonedaEquiv (U'.1.hom ≫ p.hom)) hxy hsm t
  -- The neighbourhood, read as an étale chart of `X'` over `U'`.
  refine ⟨⟨CostructuredArrow.mk (yoneda.map j ≫ U'.1.hom),
      etale_comp_of_scheme C S hS _ U'.1.hom hjet U'.property⟩,
    ObjectProperty.homMk (CostructuredArrow.homMk j rfl), z, hVaff, ⟨?_, ?_⟩, ⟨w, ?_⟩⟩
  · -- The lift lies over `Bb`.
    refine yonedaEquiv.injective ?_
    calc yonedaEquiv (yonedaEquiv.symm z ≫ q.hom)
        = (q.hom).app (op V) z := by
          rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
      _ = Bb.1.map j.op (yonedaEquiv (U'.1.hom ≫ p.hom)) := hzy
      _ = yonedaEquiv (yoneda.map j ≫ U'.1.hom ≫ p.hom) := yonedaEquiv_naturality _ _
  · -- The lift agrees with `a` on the preimage of `Z`.
    intro V₀ k s hks
    -- `V₀` factors through the chart of the thickening.
    obtain ⟨f, hf₁, hf₂⟩ : ∃ f : V₀ ⟶ T₀,
        f ≫ i₀ = k ≫ j ∧ yoneda.map f ≫ u₀ = s := by
      refine ⟨Yoneda.fullyFaithful.preimage
        (hpb.lift (yoneda.map (k ≫ j)) s ?_), ?_, ?_⟩
      · rw [Functor.map_comp, Category.assoc]
        exact hks
      · refine Yoneda.fullyFaithful.map_injective ?_
        rw [Functor.map_comp, Yoneda.fullyFaithful.map_preimage]
        exact hpb.lift_fst _ _ _
      · rw [Yoneda.fullyFaithful.map_preimage]
        exact hpb.lift_snd _ _ _
    refine yonedaEquiv.injective ?_
    calc yonedaEquiv (yoneda.map k ≫ yonedaEquiv.symm z)
        = Y.1.map k.op z := by rw [← yonedaEquiv_naturality, Equiv.apply_symm_apply]
      _ = Y.1.map f.op (yonedaEquiv (u₀ ≫ a)) := (hagree V₀ f k hf₁).symm
      _ = yonedaEquiv (yoneda.map f ≫ u₀ ≫ a) := yonedaEquiv_naturality _ _
      _ = yonedaEquiv (s ≫ a) := by rw [← Category.assoc, hf₂]
  · -- The neighbourhood meets the given point.
    exact hw.trans ht

/-- **Through every point of an arbitrary étale chart of `X'` there is a smaller affine étale
chart carrying a lift**, granted that `q` is smooth.

The chart is cut down to an affine open neighbourhood of the point, which is again an étale
chart of `X'` by `AlgebraicGeometry.Space.openChart`, and
`AlgebraicGeometry.Space.exists_isChartLift_of_isAffine_at_point` applies there.  Being a lift
is a condition on the chart and the section alone, so it is unaffected by remembering the
larger chart. -/
theorem exists_isChartLift_at_point (p : X' ⟶ Bb) (q : Y ⟶ Bb)
    {Z : Subfunctor X'.1} (a : Z.toFunctor ⟶ Y.1)
    (hX : IsFirstOrderThickening C S hS X' Z) (ha : a ≫ q.hom = Z.ι ≫ p.hom)
    (hq : IsSmooth C S hS q.hom) (U' : SmallEtale C S hS X'.1)
    (x : (BigFppfOver.toScheme C S hS).obj ((SmallEtale.toOver C S hS X'.1).obj U')) :
    ∃ (V' : SmallEtale C S hS X'.1) (r : V' ⟶ U')
      (β : Y.1.obj (op ((SmallEtale.toOver C S hS X'.1).obj V'))),
      IsChartLift C S hS p q a V' (yonedaEquiv.symm β) ∧
        x ∈ Set.range ((BigFppfOver.toScheme C S hS).map
          ((SmallEtale.toOver C S hS X'.1).map r)) := by
  classical
  -- An affine open neighbourhood of the point in the chart.
  obtain ⟨O, hO, hxO, -⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      (Scheme.isBasis_affineOpens ((BigFppfOver.toScheme C S hS).obj
        ((SmallEtale.toOver C S hS X'.1).obj U')))
      (show x ∈ (⊤ : ((BigFppfOver.toScheme C S hS).obj
        ((SmallEtale.toOver C S hS X'.1).obj U')).Opens) from trivial)
  obtain ⟨x₀, hx₀⟩ := (Scheme.Opens.range_ι O).ge hxO
  obtain ⟨V', r₀, β, -, hlift, hmem⟩ :=
    exists_isChartLift_of_isAffine_at_point C S hS p q a hX ha hq
      (openChart C S hS X'.1 U' O) hO x₀
  refine ⟨V', r₀ ≫ openChartInclusion C S hS X'.1 U' O, β, hlift, ?_⟩
  obtain ⟨y₀, hy₀⟩ := hmem
  refine ⟨y₀, ?_⟩
  rw [Functor.map_comp, Functor.map_comp,
    toScheme_map_toOver_map_openChartInclusion C S hS X'.1 U' O]
  change (Scheme.Opens.ι O) ((BigFppfOver.toScheme C S hS).map
    ((SmallEtale.toOver C S hS X'.1).map r₀) y₀) = x
  rw [hy₀, hx₀]

/-! ### The covering family of charts carrying a lift -/

/-- **Every étale chart of `X'` is covered by affine étale charts carrying a lift**, granted
that `q` is smooth: this is the local nonemptiness of the sheaf of lifts of
[Stacks Project, Tag 061D].

The family is indexed by the points of the chart, one member through each by
`AlgebraicGeometry.Space.exists_isChartLift_at_point`; it is jointly surjective by
construction, and a jointly surjective family of étale charts generates a covering sieve of the
small étale site by `AlgebraicGeometry.Space.SmallEtale.ofArrows_mem_topology`. -/
theorem exists_isChartLift_ofArrows (p : X' ⟶ Bb) (q : Y ⟶ Bb)
    {Z : Subfunctor X'.1} (a : Z.toFunctor ⟶ Y.1)
    (hX : IsFirstOrderThickening C S hS X' Z) (ha : a ≫ q.hom = Z.ι ≫ p.hom)
    (hq : IsSmooth C S hS q.hom) (U' : SmallEtale C S hS X'.1) :
    ∃ (I : Type u) (V : I → SmallEtale C S hS X'.1) (r : ∀ i, V i ⟶ U')
      (β : ∀ i, Y.1.obj (op ((SmallEtale.toOver C S hS X'.1).obj (V i)))),
      (∀ i, IsChartLift C S hS p q a (V i) (yonedaEquiv.symm (β i))) ∧
        Sieve.ofArrows V r ∈ SmallEtale.topology C S hS X'.1 U' := by
  classical
  choose V r β hlift hmem using
    exists_isChartLift_at_point C S hS p q a hX ha hq U'
  refine ⟨(BigFppfOver.toScheme C S hS).obj ((SmallEtale.toOver C S hS X'.1).obj U'),
    V, r, β, hlift, ?_⟩
  refine SmallEtale.ofArrows_mem_topology C S hS X'.1 V r ?_
  rw [Scheme.ofArrows_mem_etalePrecoverage_iff]
  exact ⟨fun x => ⟨x, hmem x⟩, fun i => etale_toScheme_toOver_map C S hS X'.1 (r i)⟩

end AlgebraicGeometry.Space

end
