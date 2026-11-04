module

public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeStratificationGerbes
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeStratificationMinimal
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeStratificationQuotientStack

/-!
# An algebraic stack stratified by gerbes, with no coarser such stratification (Stacks 06RE)

Let `k` be a field and `p` a prime. The multiplicative group acts on
`U = Spec(k[x_0, x_1, x_2, …])` by `t · (x_0, x_1, x_2, …) = (t x_0, t^p x_1, t^{p^2} x_2, …)`, and
`𝒳 = [U/𝐆_m]`. **Stacks 06RE** asserts:

1. `𝒳` is an algebraic stack;
2. `𝒳` is stratified by strata `𝒳_i`, where `x_0 = ⋯ = x_{i-1} = 0` and `x_i ≠ 0`, and `𝒳_∞`,
   where all `x_i` vanish;
3. each stratum is a gerbe over a scheme, with group `μ_{p^i}` for `𝒳_i` and `𝐆_m` for `𝒳_∞`;
4. the strata are reduced locally closed substacks;
5. there is no coarser stratification with the same properties.

This module states each assertion as one theorem, for the algebraic stack
`AlgebraicGeometry.PPowerWeighted.weightedQuotientStack`, the quotient stack
`AlgebraicGeometry.PPowerWeighted.quotientStack` of
`StacksFrontier.AlgebraicGeometry.Stacks.GerbeStratificationQuotientStack` read as an object of the
2-category of algebraic stacks through its small model.

## Main results

* `AlgebraicGeometry.PPowerWeighted.weightedQuotientStack_presentation`: assertion (1): `𝒳` is an
  algebraic stack presented by the action groupoid of `𝐆_m` on `U` (its quotient stack is
      `[U/𝐆_m]`).
* `AlgebraicGeometry.PPowerWeighted.stratumProperty_chart_iff`: assertion (2), the strata: a
  `W`-valued point of `U` lands in `𝒳_i` exactly when `x_0, …, x_{i-1}` vanish on `W` and `x_i` is
  invertible on `W`, and in `𝒳_∞` exactly when all `x_j` vanish on `W`.
* `AlgebraicGeometry.PPowerWeighted.isAlgebraicStack_stratum`: each stratum is an algebraic
  stack, being a locally closed substack of `𝒳`; assertions (2)–(4) are stated for this algebraic
  stack structure on the strata.
* `AlgebraicGeometry.PPowerWeighted.exists_stratification`: assertion (2), the stratification: the
  point sets of the strata form a stratification of `|𝒳|` in the sense of Stacks 09Y1.
* `AlgebraicGeometry.PPowerWeighted.isGerbeOverSchemeWithGroup_algebraicStratum`: assertion (3),
  from `AlgebraicGeometry.PPowerWeighted.isGerbeOverSchemeWithGroup_stratum` of
  `StacksFrontier.AlgebraicGeometry.Stacks.GerbeStratificationGerbes`.
* `AlgebraicGeometry.PPowerWeighted.isReduced_isLocallyClosedSubstack_stratum`: assertion (4).
* `AlgebraicGeometry.PPowerWeighted.stratification_minimal`: assertion (5).

## Implementation notes

The ambient site is the big fppf site over `Spec ℤ`, which is the whole big fppf site, and it is
assumed to contain `U`; see
`StacksFrontier.AlgebraicGeometry.Stacks.GerbeStratificationQuotientStack`. The strata are indexed by
`WithTop ℕ`, `⊤` being `∞`; the closure order is the reverse order, so the stratification is
indexed by `(WithTop ℕ)ᵒᵈ`.

## References

* [Stacks Project, Tag 06RE](https://stacks.math.columbia.edu/tag/06RE)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.PPowerWeighted

local macro "𝒵" : term => `(Spec (CommRingCat.of (ULift ℤ)))

variable (𝒞 : BigFppfSite.{u}) (k : Type u) [Field k] (p : ℕ) [hp : Fact p.Prime]
  (hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k))))

omit hp in
/-- **Stacks 06RE**, assertion (1): `𝒳 = [U/𝐆_m]` is an algebraic stack. The algebraic stack
`weightedQuotientStack` is presented, in the sense of Stacks 04TI, by the action groupoid of `𝐆_m`
on `U`, whose quotient stack is the `[U/𝐆_m]` of `quotientStack`. -/
@[stacks 06RE "X = [U/G_m] is an algebraic stack: the object of the 2-category of algebraic \
stacks presented by the action groupoid"]
theorem weightedQuotientStack_presentation :
    ∃ P : Stack.GroupoidPresentation 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
        (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val,
      Stack.quotientStack P.groupoid = quotientStack 𝒞 k p hU :=
  ⟨weightedQuotientPresentation.{u, w} 𝒞 k p hU, rfl⟩

omit hp in
/-- **Stacks 06RE**, assertion (2), the strata: the stratum of index `i` is the locus where
`x_0, …, x_{i-1}` vanish and `x_i` does not, and the stratum of index `∞` the locus where all
`x_j` vanish. Precisely, a point `h : W ⟶ U` with values in any scheme `W` of the site lands in
`𝒳_i` if and only if `x_0, …, x_{i-1}` pull back to `0` and `x_i` to a unit of `Γ(W, 𝒪_W)`, and in
`𝒳_∞` if and only if every `x_j` pulls back to `0`. -/
@[stacks 06RE "the strata X_i (x_0 = ... = x_{i-1} = 0, x_i invertible) and X_infinity \
(all x_j = 0)"]
theorem stratumProperty_chart_iff {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (h : W ⟶ totalSiteObject 𝒞 k hU) :
    (∀ i : ℕ, stratumProperty.{u, w} 𝒞 k p hU i (chartObj.{u, w} p h) ↔
      (∀ j < i, coord h j = 0) ∧ IsUnit (coord h i)) ∧
    (stratumProperty.{u, w} 𝒞 k p hU ⊤ (chartObj.{u, w} p h) ↔ ∀ j, coord h j = 0) :=
  ⟨fun i => (chartObj_mem_stratumProperty_iff (𝒞 := 𝒞) (k := k) (p := p) (hU := hU) (a := i)
      (h := h)).trans (mem_stratumSubfunctor_coe_iff i h),
    (chartObj_mem_stratumProperty_iff (𝒞 := 𝒞) (k := k) (p := p) (hU := hU) (a := ⊤)
      (h := h)).trans (mem_stratumSubfunctor_top_iff h)⟩

omit hp in
/-- **Stacks 06RE: each stratum is an algebraic stack.** The full subcategory of `𝒳` on the
objects of the stratum `𝒳_a` is an algebraic stack, being a locally closed substack of `𝒳`: this
is the algebraicity component of `isLocallyClosedSubstack_stratumProperty`. It is the algebraic
stack structure on `𝒳_a` that assertions (2), (3) and (4) below are stated for. -/
@[stacks 06RE "each stratum is an algebraic stack (locally closed substack)"]
theorem isAlgebraicStack_stratum (a : WithTop ℕ) :
    Stack.IsAlgebraicStack.{u, w} 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (Stack.fullSubcategoryBased (weightedQuotientStack.{u, w} 𝒞 k p hU)
        (stratumProperty.{u, w} 𝒞 k p hU a)) := by
  obtain ⟨-, hP, -⟩ :=
    isLocallyClosedSubstack_stratumProperty (𝒞 := 𝒞) (k := k) (p := p) (hU := hU) (a := a)
  exact hP

omit hp in
/-- **Stacks 06RE**, assertion (2), the stratification: the point sets `|𝒳_a|` of the strata form a
stratification of `|𝒳|` (Stacks 09Y1) indexed by `ℕ ∪ {∞}` with the reverse order: they are
pairwise disjoint, cover `|𝒳|`, and the closure of `|𝒳_i|` lies in
`|𝒳_i| ∪ |𝒳_{i+1}| ∪ ⋯ ∪ |𝒳_∞|`. -/
@[stacks 06RE "the strata form a stratification of |X|"]
theorem exists_stratification :
    letI := Stack.pointTopology 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (weightedQuotientStack.{u, w} 𝒞 k p hU).val
    ∃ σ : Stratification (Stack.AlgebraicStacks.points 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
        (weightedQuotientStack.{u, w} 𝒞 k p hU)) (WithTop ℕ)ᵒᵈ,
      ∀ a : WithTop ℕ,
        σ.strata (OrderDual.toDual a) =
          Set.range (Stack.AlgebraicStacks.pointsMap 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
            (Stack.fullSubcategoryInclusion (weightedQuotientStack.{u, w} 𝒞 k p hU)
              (stratumProperty.{u, w} 𝒞 k p hU a)
              (isAlgebraicStack_stratum.{u, w} 𝒞 k p hU a))) :=
  ⟨stratification.{u, w} (𝒞 := 𝒞) (k := k) (p := p) (hU := hU), fun a =>
    (stratification_strata.{u, w} (𝒞 := 𝒞) (k := k) (p := p) (hU := hU) (a := a)).trans
      (range_pointsMap_stratumProperty (𝒞 := 𝒞) (k := k) (p := p) (hU := hU) (a := a) (hP :=
          isAlgebraicStack_stratum.{u, w} 𝒞 k p hU a)).symm⟩

omit hp in
/-- **Stacks 06RE**, assertion (4): every stratum is a reduced locally closed substack of `𝒳`. -/
@[stacks 06RE "the strata are reduced locally closed substacks"]
theorem isReduced_isLocallyClosedSubstack_stratum (a : WithTop ℕ) :
    Stack.IsLocallyClosedSubstack (weightedQuotientStack.{u, w} 𝒞 k p hU)
        (stratumProperty.{u, w} 𝒞 k p hU a) ∧
      Stack.IsReducedStack 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
        (Stack.fullSubcategoryAlgebraicStack (weightedQuotientStack.{u, w} 𝒞 k p hU)
          (stratumProperty.{u, w} 𝒞 k p hU a) (isAlgebraicStack_stratum.{u, w} 𝒞 k p hU a)) :=
  ⟨isLocallyClosedSubstack_stratumProperty (𝒞 := 𝒞) (k := k) (p := p) (hU := hU) (a := a),
    isReducedStack_stratumProperty (𝒞 := 𝒞) (k := k) (p := p) (hU := hU) (a := a) (hP :=
      isAlgebraicStack_stratum.{u, w} 𝒞 k p hU a)⟩

/-- **Stacks 06RE**, assertion (3): each stratum is a gerbe over a scheme, with group `μ_{p^i}`
for `𝒳_i` and `𝐆_m` for `𝒳_∞`. -/
@[stacks 06RE "each stratum is a gerbe over a scheme with group mu_{p^i} for X_i and G_m for \
X_infinity"]
theorem isGerbeOverSchemeWithGroup_algebraicStratum (a : WithTop ℕ) :
    haveI : NeZero p := ⟨hp.out.ne_zero⟩
    Stack.AlgebraicStacks.IsGerbeOverSchemeWithGroup 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (Stack.fullSubcategoryAlgebraicStack (weightedQuotientStack.{u, w} 𝒞 k p hU)
        (stratumProperty.{u, w} 𝒞 k p hU a) (isAlgebraicStack_stratum.{u, w} 𝒞 k p hU a))
      (stratumGroup.{u} p a) :=
  have : NeZero p := ⟨hp.out.ne_zero⟩
  isGerbeOverSchemeWithGroup_stratum a (isAlgebraicStack_stratum.{u, w} 𝒞 k p hU a)

/-- **Stacks 06RE**, assertion (5): there is no coarser stratification with the same properties.
If a topological partition of `|𝒳|` (Stacks 09XZ) consists of the point sets of reduced locally
closed substacks of `𝒳` each of which is a gerbe over a scheme, and the strata `|𝒳_a|` refine it,
then it is the partition by the strata. -/
@[stacks 06RE "there is no coarser stratification by reduced locally closed gerbes over schemes"]
theorem stratification_minimal :
    letI := Stack.pointTopology 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (weightedQuotientStack.{u, w} 𝒞 k p hU).val
    ∀ Qs : Set (Set (Stack.AlgebraicStacks.points 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
        (weightedQuotientStack.{u, w} 𝒞 k p hU))),
      IsTopologicalPartition Qs →
      (∀ s ∈ Qs, ∃ (W : ObjectProperty (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj)
          (_ : Stack.IsLocallyClosedSubstack (weightedQuotientStack.{u, w} 𝒞 k p hU) W),
        (∀ hA, Stack.IsReducedStack 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
            (Stack.fullSubcategoryAlgebraicStack (weightedQuotientStack.{u, w} 𝒞 k p hU) W hA) ∧
          Stack.AlgebraicStacks.IsGerbeOverScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
            (Stack.fullSubcategoryAlgebraicStack (weightedQuotientStack.{u, w} 𝒞 k p hU) W hA)) ∧
        ∀ hA, Set.range (Stack.AlgebraicStacks.pointsMap 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
          (Stack.fullSubcategoryInclusion (weightedQuotientStack.{u, w} 𝒞 k p hU) W hA)) = s) →
      local_Refines (Set.range (stratumPoints.{u, w} 𝒞 k p hU)) Qs →
      Qs = Set.range (stratumPoints.{u, w} 𝒞 k p hU) :=
  eq_range_stratumPoints_of_refines p hp.out.one_lt

end AlgebraicGeometry.PPowerWeighted

end
