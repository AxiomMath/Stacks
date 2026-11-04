module

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionGeneratingLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalIntegralEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ModuleFilteredColimitSections

/-!
# A covering family of integral affine charts trivializing an invertible module

Let `X` be a normal integral algebraic space over a scheme `S` and let `ℒ` be an invertible
`𝒪_X`-module. The proof of Stacks 0EPX works over an étale chart which is **affine and
integral** and over which `ℒ` is **free**, and it needs such charts to cover `X` — in the
precise sense of `CategoryTheory.GrothendieckTopology.CoversTop`, which is what
`AlgebraicGeometry.Space.picardClass_eq_zero_of_generatesOnChart_coversTop` consumes.

This file produces that family. The only `CoversTop` families the development had were
`AlgebraicGeometry.Space.SmallEtale.coversTop_affineCharts` and
`AlgebraicGeometry.Space.SmallEtale.coversTop_of_isSurjective`, neither of which can be cut out
by a property of the module; what is produced here is the two-step refinement of the first.

## Main results

* `AlgebraicGeometry.Space.exists_isAffine_isIntegral_chart_mem_range`: every point of the
  scheme of an étale chart of a normal integral algebraic space is in the image of an étale
  chart over it whose scheme is affine and integral. This is the pointwise statement
  `AlgebraicGeometry.Space.exists_isAffine_isIntegral_ofArrows` turns into a covering family.
* `AlgebraicGeometry.Space.exists_isAffine_isIntegral_ofArrows`: every étale chart of a normal
  integral algebraic space carries a covering family by charts with affine integral scheme.
* `AlgebraicGeometry.Space.exists_coversTop_isAffine_isIntegral_generator`: the family itself —
  étale charts with affine integral scheme, over each of which the invertible module is free on
  a compatible family of generators, covering the final object of the small étale site.

## Implementation notes

**The order of the two refinements is forced.** Integrality of a scheme is not étale-local — an
étale scheme over an integral scheme need not be integral — so refining an integral chart by
charts over which `ℒ` is free destroys integrality and nothing re-establishes it. The source
does it the other way round, trivializing first and arranging the chart integral afterwards (its
appeal to Properties of Spaces, Lemma 28.7.5 comes *after* the choice of the trivializing `U`),
and that order works because an integral affine open of a chart carrying a free generator
carries one again by restriction. So
`AlgebraicGeometry.Space.exists_isAffine_isIntegral_ofArrows` is applied to the members of the
trivializing family and not conversely, and the free generator over the trivializing chart is
restricted along the inclusion, the compatible family `e` becoming `fun W k ↦ e W (k ≫ j)` —
the same reindexing as in `AlgebraicGeometry.Space.chartRatio_restrict`.

**Normality and local Noetherianness are not in the conclusion** because they are free: every
étale chart of a normal algebraic space is a normal scheme
(`AlgebraicGeometry.Space.isNormal_iff_forall_etale`) and every étale chart of a locally
Noetherian one is locally Noetherian
(`AlgebraicGeometry.Space.isLocallyNoetherian_chartScheme`), with no hypothesis on the chart.
Affineness and integrality are the two that have to be arranged.

**The pointwise step** is the shrinking step of Stacks 0AYH,
`AlgebraicGeometry.Space.exists_isAffineOpen_isNormal_isIntegral_of_isAffine_etaleChart`,
applied to an affine *open* of the given chart rather than to
the chart itself: that lemma wants an affine chart, and a general chart is only covered by
affine opens, each of which is again an étale chart
(`AlgebraicGeometry.Space.openChart`).

## References

* [Stacks Project, Tag 0AYH](https://stacks.math.columbia.edu/tag/0AYH)
* [Stacks Project, Tag 0EPX](https://stacks.math.columbia.edu/tag/0EPX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
variable (hnormal : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsNormal Y))
variable (hintegral : IsIntegralSpace B S hS X)

include hX hnormal hintegral in
/-- **Every point of an étale chart of a normal integral algebraic space is in the image of an
affine integral étale chart over it.** This is the shrinking step of Stacks 0AYH
(`AlgebraicGeometry.Space.exists_isAffineOpen_isNormal_isIntegral_of_isAffine_etaleChart`) made
applicable to a chart that is not itself affine: an affine open of the chart through the point is
again an étale chart (`AlgebraicGeometry.Space.openChart`), the shrinking step applies to it, and
the integral affine open it returns is an étale chart over the first one. -/
theorem exists_isAffine_isIntegral_chart_mem_range (W : SmallEtale B S hS X)
    (x : chartScheme W) :
    ∃ (Q : SmallEtale B S hS X) (b : Q ⟶ W), IsAffine (chartScheme Q) ∧
      IsIntegral (chartScheme Q) ∧
      x ∈ Set.range ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS X).map b)) := by
  obtain ⟨-, ⟨O, hOaff, rfl⟩, hxO, -⟩ :=
    (chartScheme W).isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : IsAffine (chartScheme (openChart B S hS X W O)) := hOaff
  obtain ⟨O', hxO', hO'aff, -, hO'int⟩ :=
    exists_isAffineOpen_isNormal_isIntegral_of_isAffine_etaleChart B S hS hX hnormal hintegral
      ((SmallEtale.toOver B S hS X).obj (openChart B S hS X W O)) inferInstance
      (openChart B S hS X W O).1.hom (openChart B S hS X W O).property ⟨x, hxO⟩
  refine ⟨openChart B S hS X (openChart B S hS X W O) O',
    openChartInclusion B S hS X (openChart B S hS X W O) O' ≫
      openChartInclusion B S hS X W O, hO'aff, hO'int, ⟨⟨x, hxO⟩, hxO'⟩, ?_⟩
  rw [Functor.map_comp, Functor.map_comp,
    toScheme_map_toOver_map_openChartInclusion B S hS X (openChart B S hS X W O) O',
    toScheme_map_toOver_map_openChartInclusion B S hS X W O]
  rfl

include hX hnormal hintegral in
/-- **Every étale chart of a normal integral algebraic space carries a covering family by charts
with affine integral scheme.** The family is indexed by the points of the scheme of the chart,
one affine integral chart through each
(`AlgebraicGeometry.Space.exists_isAffine_isIntegral_chart_mem_range`); it is jointly surjective
by construction and étale because every morphism of étale charts is, so the sieve it generates is
covering by `AlgebraicGeometry.Space.SmallEtale.ofArrows_mem_topology`. -/
theorem exists_isAffine_isIntegral_ofArrows (W : SmallEtale B S hS X) :
    ∃ (I : Type u) (Y : I → SmallEtale B S hS X) (a : ∀ j, Y j ⟶ W),
      (∀ j, IsAffine (chartScheme (Y j))) ∧ (∀ j, IsIntegral (chartScheme (Y j))) ∧
        Sieve.ofArrows Y a ∈ SmallEtale.topology B S hS X W := by
  choose Y a hYaff hYint hYmem using
    exists_isAffine_isIntegral_chart_mem_range B S hS hX hnormal hintegral W
  refine ⟨chartScheme W, Y, a, hYaff, hYint, SmallEtale.ofArrows_mem_topology B S hS X Y a ?_⟩
  rw [Scheme.ofArrows_mem_etalePrecoverage_iff]
  exact ⟨fun z ↦ ⟨z, hYmem z⟩, fun j ↦ etale_toScheme_toOver_map B S hS X (a j)⟩

include hX hnormal hintegral in
/-- **The charts the proof of Stacks 0EPX works over cover the final object of the small étale
site.** On a normal integral algebraic space `X`, for every invertible `𝒪_X`-module `ℒ` there is
a family of étale charts covering the final object of the small étale site, each of which has
affine integral scheme and over each of which `ℒ` is free on a compatible family of generators.

This is the producer
`AlgebraicGeometry.Space.picardClass_eq_zero_of_generatesOnChart_coversTop` needs.
The affine charts cover
(`AlgebraicGeometry.Space.SmallEtale.coversTop_affineCharts`), each of them is covered by
charts trivializing `ℒ`
(`AlgebraicGeometry.Space.exists_generator_cover_smul_of_isInvertible`), and each of *those* is
covered by charts with affine integral scheme
(`AlgebraicGeometry.Space.exists_isAffine_isIntegral_ofArrows`), the free generator restricting
along the inclusion; `Stacks.Sites.coversTop_bind` assembles the three layers. Trivializing
before arranging integrality is the order the source uses and the only one available: see the
implementation notes of this file. -/
theorem exists_coversTop_isAffine_isIntegral_generator (L : Modules.{u, u} B S hS X hX)
    (hL : IsInvertibleModule (⟨X, hX⟩ : AlgebraicSpaces B S hS) L) :
    ∃ (I : Type (u + 1)) (Y : I → SmallEtale B S hS X),
      (SmallEtale.topology B S hS X).CoversTop Y ∧
        ∀ i, IsAffine (chartScheme (Y i)) ∧ IsIntegral (chartScheme (Y i)) ∧
          ∃ e : (W : SmallEtale B S hS X) → (W ⟶ Y i) → L.val.obj (op W),
            (∀ (W W' : SmallEtale B S hS X) (k : W ⟶ Y i) (g : W' ⟶ W),
                (L.val.map g.op).hom (e W k) = e W' (g ≫ k)) ∧
              ∀ (W : SmallEtale B S hS X) (k : W ⟶ Y i),
                Function.Bijective fun r : chartRing B S hS X hX W ↦ r • e W k := by
  classical
  choose I V a htcov htgen using fun U : {U : SmallEtale B S hS X // IsAffine (chartScheme U)} ↦
    exists_generator_cover_smul_of_isInvertible B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS) L hL U.1
  have h₁ := Stacks.Sites.coversTop_bind (SmallEtale.coversTop_affineCharts B S hS X) a htcov
  choose κ Q b hQaff hQint hQcov using fun p : Σ U, I U ↦
    exists_isAffine_isIntegral_ofArrows B S hS hX hnormal hintegral (V p.1 p.2)
  refine ⟨Σ p : Σ U, I U, κ p, fun q ↦ Q q.1 q.2,
    Stacks.Sites.coversTop_bind h₁ b hQcov, fun q ↦ ⟨hQaff q.1 q.2, hQint q.1 q.2, ?_⟩⟩
  obtain ⟨e, hcompat, hfree⟩ := htgen q.1.1 q.1.2
  exact ⟨fun W k ↦ e W (k ≫ b q.1 q.2),
    fun W W' k g ↦ (hcompat W W' (k ≫ b q.1 q.2) g).trans
      (congrArg (e W') (Category.assoc g k (b q.1 q.2)).symm),
    fun W k ↦ hfree W (k ≫ b q.1 q.2)⟩

end AlgebraicGeometry.Space

end
