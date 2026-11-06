module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolutionExample
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleBaseChange
public import StacksFrontier.Examples.Spaces.AffineLineInvolutionNotLocallySeparated
public import StacksFrontier.Examples.Spaces.DoubledLineEtaleCovering

/-!
# The squaring map on the involution quotient: Stacks 05ZI

Let `k` be a field in which `2` is invertible and let `X = 𝐀¹_k/\{x ∼ -x ∣ x ≠ 0\}` be the
algebraic space of Stacks 05Z6, with its chart `𝐀¹_k ⟶ X` and the universal homeomorphism
`X ⟶ 𝐀¹_k` descended from squaring the coordinate. The remark Stacks 05ZI asserts:

* (a) a universal homeomorphism of algebraic spaces need not be representable, the example
  being `X ⟶ 𝐀¹_k`;
* (b) Theorem 05ZH fails for universal homeomorphisms: base change `V ↦ V ×_{𝐀¹_k} X` from the
  spaces-étale site of `𝐀¹_k` to that of `X` is not an equivalence.

This file proves both.

## Main results

* `AlgebraicGeometry.AffineLineInvolution.not_relativelyRepresentable_squaringMap`: the
  squaring map `X ⟶ 𝐀¹_k` is not representable.
* `AlgebraicGeometry.AffineLineInvolution.not_essSurj_spacesBaseChange_squaringMap`: the base
  change functor of Stacks 05ZH along it, `AlgebraicGeometry.Space.spacesBaseChange`, is not
  essentially surjective. The doubled-origin covering `Y ⟶ X` of the remark is not in its
  essential image.
* `squaringMap_universalHomeomorphism_not_representable_not_isEquivalence`:
  **Stacks 05ZI**, both assertions together, under the remark's hypotheses.

## Implementation notes

*(a).* If `X ⟶ 𝐀¹_k` were representable it would be locally separated, by Stacks 03KY, and
`𝐀¹_k` is locally separated over `k`. Then `X` would be locally separated over `k`. It is not:
its chart has the relation of Stacks 02Z1 as kernel pair, and that relation is not an
immersion (`AlgebraicGeometry.AffineLineInvolution.not_isLocallySeparatedOver_quotientSpace`).

*(b).* The source argues that `𝐀¹_k` has no nontrivial connected finite étale covering in
characteristic zero ("details omitted") and that `Y ⟶ X` is one. The proof here does not use
that fact. It works directly with an arbitrary `V` étale over `𝐀¹_k` and an isomorphism
`Y ≅ V ×_{𝐀¹_k} X` over `X`, and derives a contradiction. Let `g_b : 𝐀¹_k ⟶ V` be the two
charts of `Y` followed by `Y ≅ V ×_{𝐀¹_k} X ⟶ V`. Then `g_0 ∘ (−1)` lies over the squaring map,
so it lifts, with the chart `𝐀¹_k ⟶ X`, to a section of the right edge `Y₁ ⨿ Y₂ ⟶ 𝐀¹_k` of
the cartesian square of the remark. Since `𝐀¹_k` is irreducible, that section is the twisted
inclusion of one copy of the line (`exists_eq_chartTwist_comp_chartPairIncl`). So
`g_0 ∘ (−1) = g_0` or `g_0 ∘ (−1) = g_1 ∘ (−1)`.

* In the first case the first chart of `Y` is unchanged by negation on the punctured line, in
  the sense of `not_exists_section_chartPairToAffineLine`, which rules that out.
* In the second case `g_0 = g_1`. Negation fixes the origin, so the two origins of `Y` have the
  same image in `V` and in `X`, hence they are equal. They are not.

Only `2 ≠ 0` in `k` is used.

## References

* [Stacks Project, Tag 05ZI](https://stacks.math.columbia.edu/tag/05ZI)
* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 05Z6](https://stacks.math.columbia.edu/tag/05Z6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Examples Stacks.Examples.AffineOverAlgebraicSpace

universe u

namespace AlgebraicGeometry.AffineLineInvolution

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))

/-! ### Sections of the right edge of the square -/

/-- **A section of the right edge `Y₁ ⨿ Y₂ ⟶ 𝐀¹_k` of the square of Stacks 05ZI is the twisted
inclusion of a single copy of the line.** The decomposition of `𝐀¹_k` along the section has
two open pieces with disjoint images, by
`AlgebraicGeometry.AffineLineInvolution.isEmpty_of_comp_chartTwist_eq`. The affine line is
irreducible, so one piece is empty and the section factors through one copy everywhere. -/
theorem exists_eq_chartTwist_comp_chartPairIncl (hchar : (2 : k) ≠ 0)
    (u : affineLineChart k B hk ⟶ chartPair k B hk)
    (hu : u ≫ chartPairToAffineLine k B hk = 𝟙 (affineLineChart k B hk)) :
    ∃ b : Bool, u = chartTwist k B hk b ≫ chartPairIncl k B hk b := by
  classical
  obtain ⟨W, p, c, hoi, hcov, hfac⟩ := exists_chartPair_decomposition k B hk u
  have hc : ∀ (b : Bool) {T : _} (f : _ ⟶ T) (g : chartPair k B hk ⟶ T),
      chartPairIncl k B hk b ≫ g = f → c b ≫ f = p b ≫ u ≫ g := fun b _ f g h => by
    rw [← h, ← Category.assoc, hfac b, Category.assoc]
  have hcA : ∀ b, c b ≫ chartTwist k B hk b = p b := fun b => by
    rw [hc b _ _ (chartPairIncl_comp_chartPairToAffineLine k B hk b), hu, Category.comp_id]
  have hcD : ∀ b, c b ≫ doubledChartHom k B hk b =
      p b ≫ u ≫ chartPairToDoubledLine k B hk := fun b =>
    hc b _ _ (chartPairIncl_comp_chartPairToDoubledLine k B hk b)
  -- the two pieces have disjoint images
  have hdisj : ∀ x : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj (affineLineChart k B hk),
      x ∈ Set.range ((BigFppfOver.toScheme B (Spec (.of k)) hk).map (p false)) →
      x ∉ Set.range ((BigFppfOver.toScheme B (Spec (.of k)) hk).map (p true)) := by
    rintro x ⟨y, hy⟩ ⟨y', hy'⟩
    have hD : (Limits.pullback.fst (p false) (p true) ≫ c false) ≫
          doubledChartHom k B hk false =
        (Limits.pullback.snd (p false) (p true) ≫ c true) ≫ doubledChartHom k B hk true := by
      simp only [Category.assoc, hcD]
      rw [← Category.assoc, ← Category.assoc, Limits.pullback.condition]
      simp only [Category.assoc]
    have hA : (Limits.pullback.fst (p false) (p true) ≫ c false) ≫ chartTwist k B hk false =
        (Limits.pullback.snd (p false) (p true) ≫ c true) ≫ chartTwist k B hk true := by
      rw [Category.assoc, Category.assoc, hcA false, hcA true, Limits.pullback.condition]
    obtain ⟨z, -, -⟩ := Scheme.exists_preimage_of_isPullback
      ((IsPullback.of_hasPullback (p false) (p true)).map
        (BigFppfOver.toScheme B (Spec (.of k)) hk)) y y' (by rw [hy, hy'])
    exact (isEmpty_of_comp_chartTwist_eq k B hk hchar (by decide) _ _ hD hA).false z
  -- the affine line is irreducible, so one piece is empty
  have _hirr : IrreducibleSpace
      ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj (affineLineChart k B hk)) := by
    show IrreducibleSpace (affineLine k).left
    exact irreducibleSpace_affineLine k
  have hopen : ∀ b, IsOpen (Set.range
      ((BigFppfOver.toScheme B (Spec (.of k)) hk).map (p b))) := fun b =>
    have := hoi b
    (BigFppfOver.toScheme B (Spec (.of k)) hk).map (p b) |>.isOpenEmbedding.isOpen_range
  have hsome : (∀ x, x ∉ Set.range
        ((BigFppfOver.toScheme B (Spec (.of k)) hk).map (p false))) ∨
      ∀ x, x ∉ Set.range ((BigFppfOver.toScheme B (Spec (.of k)) hk).map (p true)) := by
    rcases Set.eq_empty_or_nonempty (Set.range
      ((BigFppfOver.toScheme B (Spec (.of k)) hk).map (p false))) with h0 | ⟨x₀, hx₀⟩
    · exact Or.inl fun x hx => by rw [h0] at hx; exact hx
    rcases Set.eq_empty_or_nonempty (Set.range
      ((BigFppfOver.toScheme B (Spec (.of k)) hk).map (p true))) with h1 | ⟨x₁, hx₁⟩
    · exact Or.inr fun x hx => by rw [h1] at hx; exact hx
    obtain ⟨z, -, hz₀, hz₁⟩ := (IrreducibleSpace.isIrreducible_univ
        ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj (affineLineChart k B hk))).2
      _ _ (hopen false) (hopen true) ⟨x₀, trivial, hx₀⟩ ⟨x₁, trivial, hx₁⟩
    exact absurd hz₁ (hdisj z hz₀)
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : Bool, ∀ x, x ∉ Set.range
      ((BigFppfOver.toScheme B (Spec (.of k)) hk).map (p b₀)) :=
    hsome.elim (fun h => ⟨false, h⟩) fun h => ⟨true, h⟩
  -- glue: on the empty piece there is nothing to check, on the other the section is twisted
  refine ⟨!b₀, yoneda.map_injective (Space.hom_ext_of_mem_topology
    (BigFppfOver.topology B (Spec (.of k)) hk)
    (BigFppfOver.isSheaf_yoneda_obj B (Spec (.of k)) hk (chartPair k B hk))
    (Sieve.ofArrows W p)
    (BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B (Spec (.of k)) hk p hoi hcov)
    fun {Z} e he => ?_)⟩
  obtain ⟨b, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ e).1 he
  rw [← Functor.map_comp, ← Functor.map_comp]
  refine congrArg yoneda.map ?_
  by_cases hb : b = b₀
  · subst hb
    have hZ : IsEmpty ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj Z) :=
      ⟨fun z => hb₀ _ ⟨(BigFppfOver.toScheme B (Spec (.of k)) hk).map a z, rfl⟩⟩
    exact (Over.isInitialOfIsInitialLeft (Y := Z)
      (isInitial_schemeBelow B (isInitial_iff_isEmpty.mpr hZ).some)).hom_ext _ _
  · have hb' : b = !b₀ := by cases b <;> cases b₀ <;> simp_all
    subst hb'
    calc (a ≫ p (!b₀)) ≫ u = a ≫ c (!b₀) ≫ chartPairIncl k B hk (!b₀) := by
          rw [Category.assoc, ← hfac]
      _ = a ≫ (c (!b₀) ≫ chartTwist k B hk (!b₀) ≫ chartTwist k B hk (!b₀)) ≫
            chartPairIncl k B hk (!b₀) := by
          rw [chartTwist_comp_self, Category.comp_id]
      _ = (a ≫ p (!b₀)) ≫ chartTwist k B hk (!b₀) ≫ chartPairIncl k B hk (!b₀) := by
          rw [← hcA]; simp only [Category.assoc]

/-- Negation of the coordinate does not change its square, read on the morphisms of the
site. -/
theorem chartNeg_comp_affineLineSquareChart :
    chartNeg k B hk ≫ affineLineSquareChart k B hk = affineLineSquareChart k B hk := by
  refine (Over.post (X := B.obj hk) B.inclusion).map_injective ?_
  rw [Functor.map_comp, post_chartNeg]
  show affineLineNeg k ≫ affineLineSquareOver k B hk = affineLineSquareOver k B hk
  rw [affineLineSquareOver_eq]
  exact affineLineNeg_comp_affineLineSquare k

variable [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)]

/-! ### (a): the squaring map is not representable -/

/-- If the squaring map `X ⟶ 𝐀¹_k` were representable, the involution quotient `X` would be
locally separated over `k`. A representable morphism of algebraic spaces is locally separated
(Stacks 03KY), and `𝐀¹_k` is locally separated over `k`. -/
theorem isLocallySeparatedOver_of_relativelyRepresentable_squaringMap (hchar : (2 : k) ≠ 0)
    (hf : yoneda.relativelyRepresentable (squaringMap k B hk)) :
    Space.IsLocallySeparatedOver B (Spec (.of k)) hk (involutionQuotient k B hk).obj := by
  have hX := isAlgebraicSpace_involutionQuotient_of_isAffineHom k B hk hchar
  have hA := Space.isAlgebraicSpace_points_affineLine B k hk
  have hterm : IsTerminal (yoneda.obj (Over.mk (𝟙 (B.obj hk)))) :=
    IsTerminal.isTerminalObj yoneda _ Over.mkIdTerminal
  refine (Space.isLocallySeparatedOver_iff_isLocallySeparated_of_isTerminal B (Spec (.of k)) hk
    hterm (squaringMap k B hk ≫ (affineLinePointsIso k B hk).hom ≫
      yoneda.map (Over.homMk (affineLineChart k B hk).hom (by simp) :
        affineLineChart k B hk ⟶ Over.mk (𝟙 (B.obj hk))))).2 ?_
  refine Space.isLocallySeparated_comp B (Spec (.of k)) hk _ _
    (Space.isLocallySeparated_of_relativelyRepresentable B (Spec (.of k)) hk _ hX hA hf) ?_
  exact Space.isLocallySeparated_comp B (Spec (.of k)) hk _ _
    (Space.isLocallySeparated_of_isIso B (Spec (.of k)) hk _)
    (Space.isLocallySeparated_yoneda_map B (Spec (.of k)) hk _)

/-- **Stacks 05ZI, (a).** Away from characteristic two the universal homeomorphism `X ⟶ 𝐀¹_k`
of Stacks 05Z6 is not representable. Otherwise `X` would be locally separated over `k`, and
it is not, because the relation of Stacks 02Z1 is not an immersion. -/
theorem not_relativelyRepresentable_squaringMap (hchar : (2 : k) ≠ 0) :
    ¬ yoneda.relativelyRepresentable (squaringMap k B hk) := by
  intro hf
  have : NeZero (2 : k) := ⟨hchar⟩
  refine not_isLocallySeparatedOver_quotientSpace k B hk ?_
  rw [quotientSpace_eq]
  exact isLocallySeparatedOver_of_relativelyRepresentable_squaringMap k B hk hchar hf

/-! ### (b): base change along the squaring map is not essentially surjective -/

/-- **No algebraic space étale over `𝐀¹_k` has the doubled-origin covering `Y ⟶ X` as its base
change along the squaring map.** Here `W` with projections `fst`, `snd` is a base change of
`π : V ⟶ 𝐀¹_k` along `X ⟶ 𝐀¹_k`, and `ψ` identifies `Y` with `W` over `X`. The proof is
outlined in the module docstring. -/
theorem false_of_isPullback_squaringMap_of_iso (hchar : (2 : k) ≠ 0)
    {V W : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    {π : V ⟶ Stacks.Groupoids.points (Over.post (X := B.obj hk) B.inclusion) (affineLine k)}
    {fst : W ⟶ V} {snd : W ⟶ (involutionQuotient k B hk).obj}
    (hpb : IsPullback fst snd π (squaringMap k B hk))
    (ψ : yoneda.obj (doubledLineSite k B hk) ≅ W)
    (hψ : ψ.hom ≫ snd = coveringMorphism k B hk) : False := by
  -- the two charts of `Y`, read in `V`
  set g : Bool → (yoneda.obj (affineLineChart k B hk) ⟶ V) :=
    fun b => yoneda.map (doubledChartHom k B hk b) ≫ ψ.hom ≫ fst with hg
  -- a morphism into `Y` is determined by its images in `V` and in `X`
  have hext : ∀ {Z : BigFppfOver B (Spec (.of k)) hk} (m m' : Z ⟶ doubledLineSite k B hk),
      yoneda.map m ≫ ψ.hom ≫ fst = yoneda.map m' ≫ ψ.hom ≫ fst →
      yoneda.map m ≫ coveringMorphism k B hk = yoneda.map m' ≫ coveringMorphism k B hk →
      m = m' := by
    intro Z m m' h₁ h₂
    refine yoneda.map_injective ((@cancel_mono _ _ _ _ _ ψ.hom (IsIso.mono_of_iso _)).mp
      (hpb.hom_ext ?_ ?_))
    · simpa only [Category.assoc] using h₁
    · simpa only [Category.assoc, hψ] using h₂
  -- `g false` precomposed with negation lies over the squaring map
  have hw : (yoneda.map (chartNeg k B hk) ≫ g false) ≫ π =
      quotientChart k B hk ≫ squaringMap k B hk := by
    have h₁ : ψ.hom ≫ fst ≫ π = coveringMorphism k B hk ≫ squaringMap k B hk := by
      rw [hpb.w, ← Category.assoc, hψ]
    simp only [hg, Category.assoc, h₁]
    rw [← Category.assoc (yoneda.map (doubledChartHom k B hk false)),
      doubledChartHom_comp_coveringMorphism, doubledChartQuotientMap_false,
      quotientChart_comp_squaringMap, ← Category.assoc, ← Functor.map_comp,
      chartNeg_comp_affineLineSquareChart]
  set ℓ := hpb.lift (yoneda.map (chartNeg k B hk) ≫ g false) (quotientChart k B hk) hw with hℓ
  have hψinv : ψ.inv ≫ coveringMorphism k B hk = snd := by
    rw [← hψ, Iso.inv_hom_id_assoc]
  have hℓY : (ℓ ≫ ψ.inv) ≫ coveringMorphism k B hk = 𝟙 _ ≫ quotientChart k B hk := by
    rw [Category.assoc, hψinv, hpb.lift_snd, Category.id_comp]
  -- it lifts to a section of the right edge of the square of the remark
  have hsq := isPullback_chartPairToDoubledLine k B hk hchar
  set u₀ := hsq.lift (ℓ ≫ ψ.inv) (𝟙 _) hℓY with hu₀
  obtain ⟨u, hu⟩ := yoneda.map_surjective u₀
  have huA : u ≫ chartPairToAffineLine k B hk = 𝟙 _ := by
    refine yoneda.map_injective ?_
    rw [Functor.map_comp, hu, hsq.lift_snd, CategoryTheory.Functor.map_id]
  have huD : yoneda.map (u ≫ chartPairToDoubledLine k B hk) = ℓ ≫ ψ.inv := by
    rw [Functor.map_comp, hu, hsq.lift_fst]
  obtain ⟨b, rfl⟩ := exists_eq_chartTwist_comp_chartPairIncl k B hk hchar u huA
  -- so `g false` precomposed with negation is `g b` precomposed with the `b`-th twist
  have hkey : yoneda.map (chartNeg k B hk) ≫ g false =
      yoneda.map (chartTwist k B hk b) ≫ g b := by
    have h₁ : yoneda.map (chartNeg k B hk) ≫ g false = (ℓ ≫ ψ.inv) ≫ ψ.hom ≫ fst := by
      rw [Category.assoc, Iso.inv_hom_id_assoc, hpb.lift_fst]
    rw [h₁, ← huD, Category.assoc, chartPairIncl_comp_chartPairToDoubledLine, Functor.map_comp,
      Category.assoc]
  cases b with
  | false =>
    -- the first chart of `Y` is unchanged by negation on the punctured line: impossible
    rw [chartTwist_false, CategoryTheory.Functor.map_id, Category.id_comp] at hkey
    refine not_exists_section_chartPairToAffineLine k B hk hchar
      ⟨chartPairIncl k B hk false, ?_, ?_⟩
    · rw [chartPairIncl_comp_chartPairToAffineLine, chartTwist_false]
    · rw [chartPairIncl_comp_chartPairToDoubledLine]
      refine hext _ _ ?_ ?_
      · have h₁ : yoneda.map (puncturedChartInclusion k B hk ≫ doubledChartHom k B hk false) ≫
            ψ.hom ≫ fst = yoneda.map (puncturedChartInclusion k B hk) ≫ g false := by
          rw [Functor.map_comp, Category.assoc]
        have h₂ : yoneda.map ((puncturedChartInclusion k B hk ≫ chartNeg k B hk) ≫
              doubledChartHom k B hk false) ≫ ψ.hom ≫ fst =
            yoneda.map (puncturedChartInclusion k B hk) ≫
              (yoneda.map (chartNeg k B hk) ≫ g false) := by
          simp only [hg, Functor.map_comp, Category.assoc]
        rw [h₁, h₂, hkey]
      · rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
          doubledChartHom_comp_coveringMorphism, doubledChartQuotientMap_false,
          ← puncturedChartNeg_eq_comp]
        exact yoneda_puncturedChart_comp_quotientChart k B hk
  | true =>
    -- the two charts of `Y` have the same image in `V`, so the two origins coincide
    rw [chartTwist_true] at hkey
    have hg01 : g false = g true := by
      have h := congrArg (yoneda.map (chartNeg k B hk) ≫ ·) hkey
      simpa only [← Category.assoc, ← Functor.map_comp, chartNeg_comp_chartNeg,
        CategoryTheory.Functor.map_id, Category.id_comp] using h
    have hD : chartOrigin k B hk ≫ doubledChartHom k B hk false =
        chartOrigin k B hk ≫ doubledChartHom k B hk true := by
      refine hext _ _ ?_ ?_
      · have h := congrArg (yoneda.map (chartOrigin k B hk) ≫ ·) hg01
        simpa only [hg, Functor.map_comp, Category.assoc] using h
      · rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
          doubledChartHom_comp_coveringMorphism, doubledChartHom_comp_coveringMorphism,
          doubledChartQuotientMap_false, doubledChartQuotientMap_true, ← Category.assoc,
          ← Functor.map_comp, chartOrigin_comp_chartNeg]
    have hA : chartOrigin k B hk ≫ chartTwist k B hk false =
        chartOrigin k B hk ≫ chartTwist k B hk true := by
      rw [chartTwist_false, chartTwist_true, chartOrigin_comp_chartNeg, Category.comp_id]
    have hempty := isEmpty_of_comp_chartTwist_eq k B hk hchar (b := false) (b' := true)
      (by decide) _ _ hD hA
    obtain ⟨x₀⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of k)))
    exact hempty.false x₀

/-- The involution quotient `X` of Stacks 05Z6, as an object of the category of algebraic
spaces over `k`. -/
noncomputable abbrev involutionQuotientSpace (hchar : (2 : k) ≠ 0) :
    AlgebraicSpaces B (Spec (.of k)) hk :=
  ⟨(involutionQuotient k B hk).obj, isAlgebraicSpace_involutionQuotient_of_isAffineHom k B hk hchar⟩

/-- The affine line `𝐀¹_k`, as an object of the category of algebraic spaces over `k`. -/
noncomputable abbrev affineLineSpace : AlgebraicSpaces B (Spec (.of k)) hk :=
  ⟨Stacks.Groupoids.points (Over.post (X := B.obj hk) B.inclusion) (affineLine k),
    Space.isAlgebraicSpace_points_affineLine B k hk⟩

/-- The squaring map `X ⟶ 𝐀¹_k` of Stacks 05Z6, as a morphism of algebraic spaces over `k`. -/
noncomputable abbrev squaringSpaceHom (hchar : (2 : k) ≠ 0) :
    involutionQuotientSpace k B hk hchar ⟶ affineLineSpace k B hk :=
  ObjectProperty.homMk (squaringMap k B hk)

/-- The doubled-origin covering `Y ⟶ X` of Stacks 05ZI, as an object of the spaces-étale site
of `X`. -/
noncomputable def doubledLineEtale (hchar : (2 : k) ≠ 0) :
    Space.SpacesEtale B (Spec (.of k)) hk (involutionQuotientSpace k B hk hchar) :=
  ⟨Over.mk (ObjectProperty.homMk (coveringMorphism k B hk) :
      Space.representedAlgebraicSpace B (Spec (.of k)) hk (doubledLineSite k B hk) ⟶
        involutionQuotientSpace k B hk hchar),
    Space.isEtale_of_presheaf_etale B (Spec (.of k)) hk
      (presheaf_etale_coveringMorphism k B hk hchar)⟩

/-- **Stacks 05ZI, (b).** Away from characteristic two, base change `V ↦ V ×_{𝐀¹_k} X` along
the universal homeomorphism `X ⟶ 𝐀¹_k` of Stacks 05Z6 is not essentially surjective from the
spaces-étale site of `𝐀¹_k` to that of `X`. The functor is the one of Stacks 05ZH,
`AlgebraicGeometry.Space.spacesBaseChange`. The doubled-origin covering `Y ⟶ X` is not in its
essential image, by `false_of_isPullback_squaringMap_of_iso`. -/
theorem not_essSurj_spacesBaseChange_squaringMap (hchar : (2 : k) ≠ 0) :
    ¬ (Space.spacesBaseChange B (Spec (.of k)) hk (squaringSpaceHom k B hk hchar)).functor.EssSurj
    := by
  intro hes
  obtain ⟨V, ⟨e⟩⟩ := hes.mem_essImage (doubledLineEtale k B hk hchar)
  set F := Space.spacesBaseChange B (Spec (.of k)) hk (squaringSpaceHom k B hk hchar)
  have hpb := AlgebraicSpaces.isPullback_hom B (Spec (.of k)) hk (F.isPullback V)
  let e₁ : (F.functor.obj V).1 ≅ (doubledLineEtale k B hk hchar).1 :=
    (Space.SpacesEtale.inclusion B (Spec (.of k)) hk _).mapIso e
  let e₂ := (Over.forget _).mapIso e₁
  refine false_of_isPullback_squaringMap_of_iso k B hk hchar hpb
    ((ObjectProperty.ι _).mapIso e₂.symm) ?_
  exact congrArg (fun m => m.hom) (Over.w e₁.inv)

/-- **Stacks 05ZI.** Let `k` be an algebraically closed field of characteristic zero and let
`𝐀¹_k ⟶ X ⟶ 𝐀¹_k` be as in Stacks 05Z6, with `X ⟶ 𝐀¹_k` the morphism descended from squaring
the coordinate. Then:

1. `X` and `𝐀¹_k` are algebraic spaces and `X ⟶ 𝐀¹_k` is a universal homeomorphism;
2. it is not representable: a universal homeomorphism of algebraic spaces need not be
   representable;
3. base change `V ↦ V ×_{𝐀¹_k} X` from the spaces-étale site of `𝐀¹_k` to that of `X` is not
   essentially surjective;
4. hence it is not an equivalence, so Theorem 05ZH fails for universal homeomorphisms.

The functor is `AlgebraicGeometry.Space.spacesBaseChange`, the one Stacks 05ZH is stated for.
Only `2 ≠ 0` in `k` is used. The general statements are
`AlgebraicGeometry.AffineLineInvolution.not_relativelyRepresentable_squaringMap` and
`AlgebraicGeometry.AffineLineInvolution.not_essSurj_spacesBaseChange_squaringMap`. The proof of
(3) does not use that `𝐀¹_k` has no nontrivial connected finite étale covering. It shows
directly that the doubled-origin covering of the remark is not a base change. -/
@[stacks 05ZI "the remark's two assertions: X ⟶ 𝐀¹_k is a universal homeomorphism which is not \
representable, and base change along it is not an equivalence of spaces-étale sites (it is not \
essentially surjective), so Theorem 05ZH fails for universal homeomorphisms"]
theorem squaringMap_universalHomeomorphism_not_representable_not_isEquivalence
    [IsAlgClosed k] [CharZero k] :
    IsAlgebraicSpace B (Spec (.of k)) hk (involutionQuotient k B hk).obj ∧
      IsAlgebraicSpace B (Spec (.of k)) hk
        (Stacks.Groupoids.points (Over.post (X := B.obj hk) B.inclusion) (affineLine k)) ∧
      Space.UniversalHomeomorphism B (Spec (.of k)) hk (squaringMap k B hk) ∧
      ¬ yoneda.relativelyRepresentable (squaringMap k B hk) ∧
      ¬ (Space.spacesBaseChange B (Spec (.of k)) hk
          (squaringSpaceHom k B hk two_ne_zero)).functor.EssSurj ∧
      ¬ (Space.spacesBaseChange B (Spec (.of k)) hk
          (squaringSpaceHom k B hk two_ne_zero)).functor.IsEquivalence := by
  have hchar : (2 : k) ≠ 0 := two_ne_zero
  refine ⟨isAlgebraicSpace_involutionQuotient_of_isAffineHom k B hk hchar,
    Space.isAlgebraicSpace_points_affineLine B k hk,
    universalHomeomorphism_squaringMap k B hk hchar,
    not_relativelyRepresentable_squaringMap k B hk hchar,
    not_essSurj_spacesBaseChange_squaringMap k B hk hchar, fun h => ?_⟩
  exact not_essSurj_spacesBaseChange_squaringMap k B hk hchar inferInstance

end AlgebraicGeometry.AffineLineInvolution

end
