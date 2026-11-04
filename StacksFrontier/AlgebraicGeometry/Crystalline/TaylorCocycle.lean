module

public import StacksFrontier.AlgebraicGeometry.Crystalline.TwistedTaylorComparison
public import StacksFrontier.RingTheory.DividedPowers.MultiIndexBinomial

/-!
# The cocycle identity of the Taylor comparison of [Stacks, Tag 07JH]

For three divided power maps `f, g, h : D → B` agreeing with each other modulo the divided power
ideal `J_B`, the comparisons of
`StacksFrontier/AlgebraicGeometry/Crystalline/TwistedTaylorComparison.lean` compose:

`c_{g,h} ∘ c_{f,g} = c_{f,h}`.

Since `ξ_{f,g} + ξ_{g,h} = ξ_{f,h}` (`Crystalline.SecondDividedPowerMap.diff_add_diff`), this is
the statement that the composite of the series of `ξ` and the series of `η` is the series of
`ξ + η`. The `(K', K'')` term of the composite is `ξ^{[K']} η^{[K'']} ⊗ θ_{K''}(θ_{K'}(m))`, which
by `Crystalline.IsThetaMonomialFamily.add` is `ξ^{[K']} η^{[K'']} ⊗ θ_{K' + K''}(m)`, and
collecting the terms with `K' + K'' = K` uses the multi-index binomial formula for divided powers

`∑_{K' + K'' = K} ξ^{[K']} η^{[K'']} = ∏_i (ξ_i + η_i)^{[k_i]}`,

which is `DividedPowers.prod_dpow_add_support`.

## Main definitions

* `Crystalline.SecondDividedPowerMap.diff`: the family `ξ_{f,g} = f(x_i) - g(x_i)` for two data.
* `Crystalline.taylorComposite`: the term-by-term composite
  `∑_{(K', K'')} ξ^{[K']} η^{[K'']} ⊗ θ_{K''}(θ_{K'}(m))`, that is `c_{g,h} ∘ c_{f,g}` evaluated on
  the generator `1 ⊗ m`, summed over a finite set of pairs of multi-indices.

## Main results

* `Crystalline.taylorMonomial_add`: the multi-index binomial formula for the divided power
  monomials of the Taylor series: `(ξ + η)^{[K]} = ∑_{K' + K'' = K} ξ^{[K']} η^{[K'']}`.
* `Crystalline.taylorComposite_eq`: the cocycle identity: the term-by-term composite of the
  `ξ`-series and the `η`-series is the `(ξ + η)`-series.
* `Crystalline.hasTaylorSum_taylorComposite`: the composite is a sum of the `(ξ + η)`-series in
  the sense of `Crystalline.HasTaylorSum`.
* `Crystalline.hasTaylorSum_taylorComposite_diff`: the same for three data `f, g, h`, with
  coefficient families `ξ_{f,g}`, `ξ_{g,h}` and `ξ_{f,h}`.
* `Crystalline.taylorComposite_prod_eq`: the identity with the composite summed over the iterated
  sum `∑_{K' ∈ s} ∑_{K'' ∈ s}`, for a downward closed set `s`.
* `Crystalline.taylorComposite_prod_Iic_eq`: the same at a `Finset.Iic`.

## Implementation notes

`Crystalline.TaylorCocycle` is not proved here: it concludes an equality of `B`-linear
endomorphisms from convergence of the three series, which needs uniqueness of the sum of a Taylor
series (Hausdorffness of the `p`-adic topology of `B ⊗_D M`) and continuity of the comparison.

## References

* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Tag 07JD](https://stacks.math.columbia.edu/tag/07JD)
* [Stacks Project, Tag 07JE](https://stacks.math.columbia.edu/tag/07JE)
* [Stacks Project, Tag 07HM](https://stacks.math.columbia.edu/tag/07HM)
-/

@[expose] public section

open scoped TensorProduct

-- `antidiagonal` below is `Finset.HasAntidiagonal.antidiagonal`, not the additive form of
-- `Finset.mulAntidiagonal`.
open Finset.HasAntidiagonal

universe u uI

namespace Crystalline

/-! ### The difference family of two data -/

section Diff

variable {D : DividedPowerRing.{u}} {B : DividedPowerRing.{u}}
  [Algebra (D : Type u) (B : Type u)] {ι : Type uI}

namespace SecondDividedPowerMap

/-- **The family `ξ_{f,g} = f(x_i) - g(x_i)` of two divided power maps `f, g`.**
`Crystalline.SecondDividedPowerMap.diffFamily` is the case `g = algebraMap D B`. -/
def diff (f g : SecondDividedPowerMap D B) (x : ι → (D : Type u)) : ι → (B : Type u) :=
  fun i ↦ f.hom (x i) - g.hom (x i)

/-- **The differences of two data lie in the divided power ideal of `B`.** -/
theorem diff_mem (f g : SecondDividedPowerMap D B) (x : ι → (D : Type u)) (i : ι) :
    f.diff g x i ∈ B.ideal := by
  simpa only [diff, sub_sub_sub_cancel_right] using
    sub_mem (f.sub_algebraMap_mem (x i)) (g.sub_algebraMap_mem (x i))

/-- **The difference families of three data add up**: `ξ_{f,g} + ξ_{g,h} = ξ_{f,h}`. -/
theorem diff_add_diff (f g h : SecondDividedPowerMap D B) (x : ι → (D : Type u)) :
    f.diff g x + g.diff h x = f.diff h x :=
  funext fun _ ↦ sub_add_sub_cancel _ _ _

/-- The difference of a datum with itself is zero. -/
@[simp] theorem diff_self (f : SecondDividedPowerMap D B) (x : ι → (D : Type u)) :
    f.diff f x = 0 :=
  funext fun _ ↦ sub_self _

end SecondDividedPowerMap

end Diff

/-! ### The multi-index binomial formula for the divided power monomials -/

section Binomial

variable (B : DividedPowerRing.{u}) {ι : Type uI} [DecidableEq ι]

/-- **The multi-index binomial formula for the divided power monomials of the Taylor series of
[Stacks, Tag 07JH]**: for families `ξ`, `η` in the divided power ideal,

`(ξ + η)^{[K]} = ∑_{K' + K'' = K} ξ^{[K']} η^{[K'']}`,

the sum being over the antidiagonal of `K` in `ι →₀ ℕ`. -/
theorem taylorMonomial_add (xi eta : ι → (B : Type u)) (hxi : ∀ i, xi i ∈ B.ideal)
    (heta : ∀ i, eta i ∈ B.ideal) (K : ι →₀ ℕ) :
    taylorMonomial B (xi + eta) K =
      ∑ L ∈ antidiagonal K, taylorMonomial B xi L.1 * taylorMonomial B eta L.2 := by
  simpa only [taylorMonomial, Pi.add_apply] using
    B.dividedPowers.prod_dpow_add_support hxi heta K

end Binomial

/-! ### The cocycle identity -/

section Cocycle

variable (p : ℕ) (D : DividedPowerRing.{u}) (B : DividedPowerRing.{u})
  [Algebra (D : Type u) (B : Type u)] (M : Type u) [AddCommGroup M] [Module (D : Type u) M]
  {ι : Type uI} [DecidableEq ι] {theta : ι → (M → M)} (thetaPow : (ι →₀ ℕ) → (M → M))

/-- **The term-by-term composite of two Taylor series of [Stacks, Tag 07JH]**, that is
`c_{g,h} ∘ c_{f,g}` evaluated on the generator `1 ⊗ m`:

`∑_{(K', K'')} ξ^{[K']} η^{[K'']} ⊗ θ_{K''}(θ_{K'}(m))`,

summed over a finite set `t` of pairs of multi-indices. -/
noncomputable def taylorComposite (xi eta : ι → (B : Type u)) (m : M)
    (t : Finset ((ι →₀ ℕ) × (ι →₀ ℕ))) : (B : Type u) ⊗[(D : Type u)] M :=
  ∑ L ∈ t, (taylorMonomial B xi L.1 * taylorMonomial B eta L.2) ⊗ₜ[(D : Type u)]
    thetaPow L.2 (thetaPow L.1 m)

variable {p D B M thetaPow}

/-- A pair `L` lies in the union of the antidiagonals of `K ∈ s` iff `L.1 + L.2 ∈ s`. -/
private theorem mem_biUnion_antidiagonal_iff (s : Finset (ι →₀ ℕ))
    (L : (ι →₀ ℕ) × (ι →₀ ℕ)) : L ∈ s.biUnion (fun K ↦ antidiagonal K) ↔ L.1 + L.2 ∈ s := by
  rw [Finset.mem_biUnion]
  exact ⟨fun ⟨K, hK, hLK⟩ ↦ (mem_antidiagonal.mp hLK) ▸ hK,
    fun h ↦ ⟨L.1 + L.2, h, mem_antidiagonal.mpr rfl⟩⟩

omit [DecidableEq ι] in
/-- **The cocycle identity of [Stacks, Tag 07JH]**: the term-by-term composite of the `ξ`-series
and the `η`-series is the `(ξ + η)`-series, when the index set `t` of the composite is the set of
pairs `(K', K'')` with `K' + K'' ∈ s`. -/
theorem taylorComposite_eq (hfam : IsThetaMonomialFamily M theta thetaPow)
    {xi eta : ι → (B : Type u)} (hxi : ∀ i, xi i ∈ B.ideal) (heta : ∀ i, eta i ∈ B.ideal) (m : M)
    (s : Finset (ι →₀ ℕ)) (t : Finset ((ι →₀ ℕ) × (ι →₀ ℕ)))
    (ht : ∀ L : (ι →₀ ℕ) × (ι →₀ ℕ), L ∈ t ↔ L.1 + L.2 ∈ s) :
    taylorComposite D B M thetaPow xi eta m t =
      ∑ K ∈ s, taylorMonomial B (xi + eta) K ⊗ₜ[(D : Type u)] thetaPow K m := by
  classical
  have htb : t = s.biUnion fun K ↦ antidiagonal K :=
    Finset.ext fun L ↦ (ht L).trans (mem_biUnion_antidiagonal_iff s L).symm
  have hdisj : (s : Set (ι →₀ ℕ)).PairwiseDisjoint fun K : ι →₀ ℕ ↦ antidiagonal K := by
    intro K _ K' _ hKK'
    simp only [Function.onFun, Finset.disjoint_left]
    intro L hL hL'
    exact hKK' ((mem_antidiagonal.mp hL).symm.trans (mem_antidiagonal.mp hL'))
  rw [taylorComposite, htb, Finset.sum_biUnion hdisj]
  refine Finset.sum_congr rfl fun K _ ↦ ?_
  rw [taylorMonomial_add B xi eta hxi heta K, TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun L hL ↦ ?_
  rw [← mem_antidiagonal.mp hL, hfam.add L.1 L.2]
  rfl

/-- **The cocycle identity with the index set written out**: `Crystalline.taylorComposite_eq`
with `t` the union over `K ∈ s` of the antidiagonals of `K`. -/
theorem taylorComposite_biUnion_eq (hfam : IsThetaMonomialFamily M theta thetaPow)
    {xi eta : ι → (B : Type u)} (hxi : ∀ i, xi i ∈ B.ideal) (heta : ∀ i, eta i ∈ B.ideal) (m : M)
    (s : Finset (ι →₀ ℕ)) :
    taylorComposite D B M thetaPow xi eta m (s.biUnion fun K ↦ antidiagonal K) =
      ∑ K ∈ s, taylorMonomial B (xi + eta) K ⊗ₜ[(D : Type u)] thetaPow K m := by
  classical
  exact taylorComposite_eq hfam hxi heta m s _ (mem_biUnion_antidiagonal_iff s)

/-- **A tensor `b ⊗ y` with `y ∈ p^N M` vanishes** when `p^N = 0` in `B`, for every `b` in `B`. -/
theorem tmul_eq_zero_of_mem_pPowSmul {N : ℕ} (hpB : ((p : (B : Type u))) ^ N = 0)
    (b : (B : Type u)) {y : M} (hy : y ∈ pPowSmul p (D : Type u) M N) :
    b ⊗ₜ[(D : Type u)] y = 0 := by
  obtain ⟨z, hz⟩ := (mem_pPowSmul_iff p (D : Type u) M).mp hy
  have hzero : ((p : (D : Type u)) ^ N) • b = 0 := by
    rw [Algebra.smul_def, map_pow, map_natCast, hpB, zero_mul]
  rw [← hz, TensorProduct.tmul_smul, TensorProduct.smul_tmul', hzero, TensorProduct.zero_tmul]

omit [DecidableEq ι] in
/-- **The composite of the two Taylor comparisons is a sum of the series of the sum of the
coefficient families**, when `p^N = 0` in `B` and `θ_K m ∈ p^N M` for every `K ∉ s`. -/
theorem hasTaylorSum_taylorComposite (hfam : IsThetaMonomialFamily M theta thetaPow)
    {xi eta : ι → (B : Type u)} (hxi : ∀ i, xi i ∈ B.ideal) (heta : ∀ i, eta i ∈ B.ideal)
    {N : ℕ} (hpB : ((p : (B : Type u))) ^ N = 0) (m : M) (s : Finset (ι →₀ ℕ))
    (t : Finset ((ι →₀ ℕ) × (ι →₀ ℕ))) (ht : ∀ L : (ι →₀ ℕ) × (ι →₀ ℕ), L ∈ t ↔ L.1 + L.2 ∈ s)
    (hvanish : ∀ K ∉ s, thetaPow K m ∈ pPowSmul p (D : Type u) M N) :
    HasTaylorSum p D B M thetaPow (xi + eta) m
      (taylorComposite D B M thetaPow xi eta m t) := by
  rw [taylorComposite_eq hfam hxi heta m s t ht]
  exact hasTaylorSum_of_eq_zero p D B M thetaPow (xi + eta) m s fun K hK ↦
    tmul_eq_zero_of_mem_pPowSmul hpB _ (hvanish K hK)

omit [DecidableEq ι] in
/-- **The cocycle identity for three data `f, g, h`**: the composite of the comparison of
`ξ_{f,g}` with the comparison of `ξ_{g,h}` is a sum of the series of `ξ_{f,h}`, that is
`c_{g,h} ∘ c_{f,g} = c_{f,h}`. -/
theorem hasTaylorSum_taylorComposite_diff (hfam : IsThetaMonomialFamily M theta thetaPow)
    (f g h : SecondDividedPowerMap D B) (x : ι → (D : Type u)) {N : ℕ}
    (hpB : ((p : (B : Type u))) ^ N = 0) (m : M) (s : Finset (ι →₀ ℕ))
    (t : Finset ((ι →₀ ℕ) × (ι →₀ ℕ))) (ht : ∀ L : (ι →₀ ℕ) × (ι →₀ ℕ), L ∈ t ↔ L.1 + L.2 ∈ s)
    (hvanish : ∀ K ∉ s, thetaPow K m ∈ pPowSmul p (D : Type u) M N) :
    HasTaylorSum p D B M thetaPow (f.diff h x) m
      (taylorComposite D B M thetaPow (f.diff g x) (g.diff h x) m t) := by
  have hsum := hasTaylorSum_taylorComposite hfam (f.diff_mem g x) (g.diff_mem h x) hpB m s t ht
    hvanish
  rwa [SecondDividedPowerMap.diff_add_diff] at hsum

/-! ### The composite over a downward closed box -/

omit [DecidableEq ι] in
/-- **The cocycle identity over a downward closed box, modulo a submodule.** For `s` downward
closed with `θ_K m ∈ p^N M` for every `K ∉ s`, the iterated sum

`∑_{K' ∈ s} ∑_{K'' ∈ s} ξ^{[K']} η^{[K'']} ⊗ θ_{K''}(θ_{K'}(m))`

is congruent to the `(ξ + η)`-series over `s` modulo every submodule `Filt` of `B ⊗_D M`
containing each `b ⊗ y` with `y ∈ p^N M`. -/
theorem taylorComposite_prod_mem (hfam : IsThetaMonomialFamily M theta thetaPow)
    {xi eta : ι → (B : Type u)} (hxi : ∀ i, xi i ∈ B.ideal) (heta : ∀ i, eta i ∈ B.ideal)
    {N : ℕ} (Filt : Submodule (B : Type u) ((B : Type u) ⊗[(D : Type u)] M))
    (hdrop : ∀ (b : (B : Type u)) {y : M}, y ∈ pPowSmul p (D : Type u) M N →
      b ⊗ₜ[(D : Type u)] y ∈ Filt)
    (m : M) (s : Finset (ι →₀ ℕ))
    (hdown : ∀ K ∈ s, ∀ L ≤ K, L ∈ s)
    (hvanish : ∀ K ∉ s, thetaPow K m ∈ pPowSmul p (D : Type u) M N) :
    ∑ K' ∈ s, ∑ K'' ∈ s, (taylorMonomial B xi K' * taylorMonomial B eta K'') ⊗ₜ[(D : Type u)]
        thetaPow K'' (thetaPow K' m) -
      ∑ Q ∈ s, taylorMonomial B (xi + eta) Q ⊗ₜ[(D : Type u)] thetaPow Q m ∈ Filt := by
  classical
  rw [← Finset.sum_product', ← Finset.sum_filter_add_sum_filter_not (s ×ˢ s)
    fun L : (ι →₀ ℕ) × (ι →₀ ℕ) ↦ L.1 + L.2 ∈ s]
  have hzero : ∑ L ∈ (s ×ˢ s).filter fun L : (ι →₀ ℕ) × (ι →₀ ℕ) ↦ L.1 + L.2 ∉ s,
      (taylorMonomial B xi L.1 * taylorMonomial B eta L.2) ⊗ₜ[(D : Type u)]
        thetaPow L.2 (thetaPow L.1 m) ∈ Filt := by
    refine Submodule.sum_mem _ fun L hL ↦ ?_
    simpa only [hfam.add, Function.comp_apply] using
      hdrop _ (hvanish _ (Finset.mem_filter.mp hL).2)
  have hiff : ∀ L : (ι →₀ ℕ) × (ι →₀ ℕ),
      L ∈ (s ×ˢ s).filter (fun L : (ι →₀ ℕ) × (ι →₀ ℕ) ↦ L.1 + L.2 ∈ s) ↔ L.1 + L.2 ∈ s := by
    intro L
    rw [Finset.mem_filter, Finset.mem_product]
    exact ⟨fun hL ↦ hL.2,
      fun hL ↦ ⟨⟨hdown _ hL _ le_self_add, hdown _ hL _ le_add_self⟩, hL⟩⟩
  have hcomp := taylorComposite_eq (D := D) hfam hxi heta m s _ hiff
  rw [taylorComposite] at hcomp
  rwa [hcomp, add_sub_cancel_left]

omit [DecidableEq ι] in
/-- **The cocycle identity of [Stacks, Tag 07JH] summed over a downward closed box**: the case
`Filt = ⊥` of `Crystalline.taylorComposite_prod_mem`, when `p^N = 0` in `B`. -/
theorem taylorComposite_prod_eq (hfam : IsThetaMonomialFamily M theta thetaPow)
    {xi eta : ι → (B : Type u)} (hxi : ∀ i, xi i ∈ B.ideal) (heta : ∀ i, eta i ∈ B.ideal)
    {N : ℕ} (hpB : ((p : (B : Type u))) ^ N = 0) (m : M) (s : Finset (ι →₀ ℕ))
    (hdown : ∀ K ∈ s, ∀ L ≤ K, L ∈ s)
    (hvanish : ∀ K ∉ s, thetaPow K m ∈ pPowSmul p (D : Type u) M N) :
    ∑ K' ∈ s, ∑ K'' ∈ s, (taylorMonomial B xi K' * taylorMonomial B eta K'') ⊗ₜ[(D : Type u)]
        thetaPow K'' (thetaPow K' m) =
      ∑ Q ∈ s, taylorMonomial B (xi + eta) Q ⊗ₜ[(D : Type u)] thetaPow Q m := by
  have hmem := taylorComposite_prod_mem hfam hxi heta ⊥
    (fun b _ hy ↦ (Submodule.mem_bot _).mpr (tmul_eq_zero_of_mem_pPowSmul hpB b hy)) m s hdown
    hvanish
  rwa [Submodule.mem_bot, sub_eq_zero] at hmem

/-- **The cocycle identity over the box `Finset.Iic L`**: `Crystalline.taylorComposite_prod_eq`
at the downward closed set `Finset.Iic L`. -/
theorem taylorComposite_prod_Iic_eq (hfam : IsThetaMonomialFamily M theta thetaPow)
    {xi eta : ι → (B : Type u)} (hxi : ∀ i, xi i ∈ B.ideal) (heta : ∀ i, eta i ∈ B.ideal)
    {N : ℕ} (hpB : ((p : (B : Type u))) ^ N = 0) (m : M) (L : ι →₀ ℕ)
    (hvanish : ∀ K ∉ Finset.Iic L, thetaPow K m ∈ pPowSmul p (D : Type u) M N) :
    ∑ K' ∈ Finset.Iic L, ∑ K'' ∈ Finset.Iic L,
        (taylorMonomial B xi K' * taylorMonomial B eta K'') ⊗ₜ[(D : Type u)]
          thetaPow K'' (thetaPow K' m) =
      ∑ Q ∈ Finset.Iic L, taylorMonomial B (xi + eta) Q ⊗ₜ[(D : Type u)] thetaPow Q m :=
  taylorComposite_prod_eq hfam hxi heta hpB m (Finset.Iic L)
    (fun _ hK _ hLK ↦ Finset.mem_Iic.mpr (hLK.trans (Finset.mem_Iic.mp hK))) hvanish

end Cocycle

end Crystalline

end
