module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionValueDescent

/-!
# Free generation of a module by a section is local on the small étale site

Let `F` be an algebraic space over a scheme `S` of a big fppf site `B`, let `M` be a sheaf of
`𝒪_F`-modules and let `n` be a section of `M` over an étale chart `V`.  **Being a free generator
is a local condition on `n`**: if the restrictions of `n` along the members of a covering sieve
of `V` are free generators, then `n` is a free generator over `V`.

## Main results

* `AlgebraicGeometry.Space.exists_chartRestrict_eq_of_sieve`: regular functions glue on the
  small étale site, stated at `AlgebraicGeometry.Space.chartRing` and
  `AlgebraicGeometry.Space.chartRestrict`.
* `AlgebraicGeometry.Space.bijective_smul_of_sieve`: **the descent of free generation.**
* `AlgebraicGeometry.Space.honestFreeSieve` is the sieve of charts over which a *meromorphic*
  section of `M` is the image of a free generator of `M`, there and below, and
  `AlgebraicGeometry.Space.exists_bijective_smul_eval_eq_of_honestFreeSieve_mem` descends that
  condition along it when `M` is invertible — the shape the second collection of Stacks 0EPS
  consumes.

## Implementation notes

The statement is the sheaf condition for `𝒪_F` and the separatedness of `M`, and nothing else —
no invertibility, no local freeness.  Injectivity of `r ↦ r • n` descends because two regular
functions agreeing on a covering sieve are equal; surjectivity descends because the local
coefficients are *unique* — each one is the preimage of a restriction of the target section under
an injective map — so they form a compatible family and glue.

The gluing is separated off into `…exists_chartRestrict_eq_of_sieve` because the sheaf condition
`AlgebraicGeometry.Space.isSheaf_globalSections` is phrased at the composite
`structurePresheaf ⋙ forget CommRingCat`, whose sections over a chart are the same type as
`AlgebraicGeometry.Space.chartRing` but are not seen as such by instance search: a scalar
multiplication by an element of the composite's value does not elaborate.  That statement is the
only place where the two spellings meet.

Invertibility of `M` enters only in the *meromorphic* statement, where it is what makes
`AlgebraicGeometry.Space.toMeromorphicSectionValue` injective, so that the section the honesty
descent produces is identified with the local free generators.

## References

* [Stacks Project, Tag 0EN5](https://stacks.math.columbia.edu/tag/0EN5)
* [Stacks Project, Tag 03G6](https://stacks.math.columbia.edu/tag/03G6)
* [Stacks Project, Tag 0EPS](https://stacks.math.columbia.edu/tag/0EPS)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS)

/-- **Regular functions glue on the small étale site.**  A family of regular functions on the
charts of a covering sieve of `V`, compatible under restriction, is the family of restrictions of
a single regular function on `V`.

This is `AlgebraicGeometry.Space.isSheaf_globalSections`, Stacks 03G6, with the sections and the
restrictions spelled as `AlgebraicGeometry.Space.chartRing` and
`AlgebraicGeometry.Space.chartRestrict`. -/
theorem exists_chartRestrict_eq_of_sieve (V : SmallEtale B S hS X.1) (T : Sieve V)
    (hT : T ∈ SmallEtale.topology B S hS X.1 V)
    (c : ∀ ⦃W : SmallEtale B S hS X.1⦄ (k : W ⟶ V), T.arrows k → chartRing B S hS X.1 X.2 W)
    (hc : ∀ ⦃W W' : SmallEtale B S hS X.1⦄ (k : W ⟶ V) (g : W' ⟶ W) (hk : T.arrows k),
      c (g ≫ k) (T.downward_closed hk g) = chartRestrict (hF := X.2) g (c k hk)) :
    ∃ r : chartRing B S hS X.1 X.2 V,
      ∀ ⦃W : SmallEtale B S hS X.1⦄ (k : W ⟶ V) (hk : T.arrows k),
        chartRestrict (hF := X.2) k r = c k hk := by
  obtain ⟨r, hr, -⟩ := isSheaf_globalSections B S hS X.1 T hT (fun _ k hk ↦ c k hk)
    ((Presieve.compatible_iff_sieveCompatible _).2 fun _ _ k g hk ↦ hc k g hk)
  exact ⟨r, fun _ k hk ↦ hr k hk⟩

/-- **The descent of free generation.**  Let `M` be a sheaf of `𝒪_F`-modules, let `n` be a
section of `M` over an étale chart `V` and let `T` be a covering sieve of `V` such that for every
member `k : W ⟶ V` of `T` the map `r ↦ r • n|_W` is a bijection of `𝒪_F(W)` onto `M(W)`.  Then
`r ↦ r • n` is a bijection of `𝒪_F(V)` onto `M(V)`.

Injectivity: if `r • n = r' • n` then `r|_W = r'|_W` for every member of `T`, because
`r|_W • n|_W = r'|_W • n|_W` and multiplication by `n|_W` is injective, and the structure sheaf
is separated.  Surjectivity: the local coefficients of a section `m` of `M` over `V` are unique,
hence form a compatible family, hence glue to a regular function `r` over `V`; and `r • n = m`
because the two agree on `T` and `M` is separated. -/
theorem bijective_smul_of_sieve (M : Modules.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS X.1) (n : M.val.obj (op V)) (T : Sieve V)
    (hT : T ∈ SmallEtale.topology B S hS X.1 V)
    (hloc : ∀ ⦃W : SmallEtale B S hS X.1⦄ (k : W ⟶ V), T.arrows k →
      Function.Bijective fun r : chartRing B S hS X.1 X.2 W ↦
        r • chartRestrictLinear M k n) :
    Function.Bijective fun r : chartRing B S hS X.1 X.2 V ↦ r • n := by
  classical
  have uniq : ∀ ⦃W : SmallEtale B S hS X.1⦄ (k : W ⟶ V), T.arrows k →
      ∀ (a b : chartRing B S hS X.1 X.2 W) (m' : M.val.obj (op V)),
        a • chartRestrictLinear M k n = chartRestrictLinear M k m' →
        b • chartRestrictLinear M k n = chartRestrictLinear M k m' → a = b :=
    fun _ k hk _ _ _ h₁ h₂ ↦ (hloc k hk).1 (h₁.trans h₂.symm)
  refine ⟨fun r r' hrr ↦ ?_, fun m ↦ ?_⟩
  · have hrr : r • n = r' • n := hrr
    exact (isSheaf_globalSections B S hS X.1 T hT).isSeparatedFor.ext fun _ k hk ↦
      uniq k hk _ _ (r • n) (chartRestrictLinear_smul M k r n).symm
        ((chartRestrictLinear_smul M k r' n).symm.trans (congrArg _ hrr.symm))
  · obtain ⟨c, hcspec⟩ :
        ∃ c : ∀ ⦃W : SmallEtale B S hS X.1⦄ (k : W ⟶ V), T.arrows k →
            chartRing B S hS X.1 X.2 W,
          ∀ ⦃W : SmallEtale B S hS X.1⦄ (k : W ⟶ V) (hk : T.arrows k),
            c k hk • chartRestrictLinear M k n = chartRestrictLinear M k m :=
      ⟨fun _ k hk ↦ ((hloc k hk).2 (chartRestrictLinear M k m)).choose,
        fun _ k hk ↦ ((hloc k hk).2 (chartRestrictLinear M k m)).choose_spec⟩
    have hc : ∀ ⦃W W' : SmallEtale B S hS X.1⦄ (k : W ⟶ V) (g : W' ⟶ W) (hk : T.arrows k),
        c (g ≫ k) (T.downward_closed hk g) = chartRestrict (hF := X.2) g (c k hk) := by
      intro W W' k g hk
      refine uniq (g ≫ k) (T.downward_closed hk g) _ _ m (hcspec _ _) ?_
      rw [chartRestrictLinear_comp M k g n, chartRestrictLinear_comp M k g m, ← hcspec k hk,
        chartRestrictLinear_smul M g (c k hk) (chartRestrictLinear M k n)]
    obtain ⟨r, hr⟩ := exists_chartRestrict_eq_of_sieve B S hS X V T hT c hc
    refine ⟨r, eq_of_modules_map_eq_of_sieve B S hS X M V T hT (r • n) m fun {W} k hk ↦ ?_⟩
    change chartRestrictLinear M k (r • n) = chartRestrictLinear M k m
    rw [chartRestrictLinear_smul M k r n, hr k hk, hcspec k hk]

/-! ### The sieve of charts over which a meromorphic section is an honest free generator -/

/-- **The sieve of charts over which a meromorphic section of `M` is an honest free generator.**
A morphism `k : Q ⟶ C₀` of charts belongs to it when the value of `σ` over `Q` is the image under
`AlgebraicGeometry.Space.toMeromorphicSectionValue` of a section `n` of `M` which generates `M`
freely over *every* chart over `Q`.

Freeness is asked over the charts below `Q` and not only over `Q`, which is what makes the family
of arrows downward closed, and it is the form the two statements below both produce and
consume. -/
def honestFreeSieve (M : Modules.{u, u} B S hS X.1 X.2)
    (σ : MeromorphicSection.{u, u} B S hS X.1 X.2 M) (C₀ : SmallEtale B S hS X.1) :
    Sieve C₀ where
  arrows Q _ := ∃ n : M.val.obj (op Q),
    σ.eval (op Q) = toMeromorphicSectionValue B S hS X.1 X.2 M Q n ∧
      ∀ (Q' : SmallEtale B S hS X.1) (h : Q' ⟶ Q),
        Function.Bijective fun r : chartRing B S hS X.1 X.2 Q' ↦
          r • chartRestrictLinear M h n
  downward_closed := by
    rintro Q Q' k ⟨n, hn, hfree⟩ g
    refine ⟨chartRestrictLinear M g n,
      eval_eq_toMeromorphicSectionValue_of_hom B S hS X.1 X.2 M σ g n hn, fun Q'' h ↦ ?_⟩
    rw [← chartRestrictLinear_comp M g h n]
    exact hfree Q'' (h ≫ g)

/-- **A meromorphic section of an invertible module which is an honest free generator on a
covering sieve of a chart is an honest free generator over that chart.**

Honesty descends by `AlgebraicGeometry.Space.exists_eval_eq_toMeromorphicSectionValue_of_sieve`,
which produces the section `n` over the chart; over each member of the sieve `n` restricts to the
local witness, because `AlgebraicGeometry.Space.toMeromorphicSectionValue` is injective for an
invertible module and the two have the same image; and free generation then descends by
`AlgebraicGeometry.Space.bijective_smul_of_sieve`. -/
theorem exists_bijective_smul_eval_eq_of_honestFreeSieve_mem (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property M)
    (σ : MeromorphicSection.{u, u} B S hS X.1 X.2 M) (C₀ : SmallEtale B S hS X.1)
    (hT : honestFreeSieve B S hS X M σ C₀ ∈ SmallEtale.topology B S hS X.1 C₀) :
    ∃ n : M.val.obj (op C₀),
      σ.eval (op C₀) = toMeromorphicSectionValue B S hS X.1 X.2 M C₀ n ∧
        Function.Bijective fun r : chartRing B S hS X.1 X.2 C₀ ↦ r • n := by
  obtain ⟨n, hn⟩ := exists_eval_eq_toMeromorphicSectionValue_of_sieve B S hS X M hM σ C₀ _ hT
    fun {_} _ hk ↦ ⟨hk.choose, hk.choose_spec.1⟩
  refine ⟨n, hn, bijective_smul_of_sieve B S hS X M C₀ n _ hT fun {Q} k hk ↦ ?_⟩
  obtain ⟨m, hm, hmfree⟩ := hk
  have hrestrict : chartRestrictLinear M k n = m :=
    injective_toMeromorphicSectionValue B S hS X M hM Q
      ((eval_eq_toMeromorphicSectionValue_of_hom B S hS X.1 X.2 M σ k n hn).symm.trans hm)
  rw [hrestrict]
  simpa only [chartRestrictLinear_id M Q m] using hmfree Q (𝟙 Q)

end AlgebraicGeometry.Space

end
