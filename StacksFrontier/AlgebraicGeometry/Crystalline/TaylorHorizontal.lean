module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials
public import StacksFrontier.AlgebraicGeometry.Crystalline.TaylorConvergence

/-!
# Horizontality of the Taylor comparison

The proof of [Stacks, Lemma 60.17.5, Tag 07L5] reduces the second assertion of that lemma to the
statement that the round-trip comparison

`c_{id_D, b ∘ a} : M ⊗_{D, id_D} D ⟶ M ⊗_{D, b ∘ a} D`

of the proof of [Stacks, Proposition 60.17.4, Tag 07JH] is a morphism of *pairs*, and then stops:
"It remains to prove that this map is horizontal, i.e., compatible with connections, which we
omit."  This module proves it.

## The identity, and why it is the whole of the step

Write `g` for the second divided power map, `ξ_i = f(x_i) - g(x_i)` for the coordinate differences,
and `c(m) = ∑_K ξ^{[K]} ⊗ θ_K(m)` for the comparison.  Expanding the base-changed connection on
the generator `ξ^{[K]} ⊗ θ_K(m) = ξ^{[K]} • (1 ⊗ θ_K(m))` gives two terms: the Leibniz correction
`(1 ⊗ θ_K m) ⊗ d(ξ^{[K]})` of the coefficient, and `ξ^{[K]} • ∑_i (1 ⊗ θ_i θ_K m) ⊗ d(g(x_i))`.
The comparison is horizontal exactly when their sum is `∑_i c(θ_i m) ⊗ d(f(x_i))`, and since
`θ_i θ_K = θ_{K + e_i}` the second term already accounts for `∑_i c(θ_i m) ⊗ d(g(x_i))`.  So
horizontality is precisely

`∑_K (1 ⊗ θ_K m) ⊗ d(ξ^{[K]}) = ∑_i (∑_K ξ^{[K]} ⊗ θ_{K + e_i} m) ⊗ d(ξ_i)`,

because `d(f(x_i)) - d(g(x_i)) = d(ξ_i)`.  That identity is
`Crystalline.taylorDeriv_eq_sum`, and `Crystalline.nabla_taylorSum_eq` is the horizontality it
amounts to, written out with both terms of the connection in place.

Its proof is the divided power chain rule and one reindexing.  Differentiating a divided power
monomial gives `d(ξ^{[K]}) = ∑_i ξ^{[K - e_i]} d(ξ_i)`, which is
`Crystalline.dividedPowerDerivation_taylorMonomial`; so the left-hand side is the double sum over
the pairs `(K, i)` with `K` below the bound and `k_i ≥ 1`, with coefficient `ξ^{[K - e_i]}` and
operator `θ_K`.  Substituting `K = K' + e_i` turns that term into the `K'`-term of the right-hand
side, and the bijection `K' ↦ K' + e_i` between the two index sets is where the quasi-nilpotence
of the connection is used: the multi-indices `K` with `K + e_i` outside the bound are exactly the
ones whose operator kills `m`, so they contribute nothing.

## Why the finite-sum form is the whole statement over the completion

The series is summed over `Finset.Iic L` for a multi-index `L` bounding the surviving operators of
`m`.  That is what the route through the finite levels of the `p`-adic tower supplies: at a level
`D ⧸ (p)^e` the element `p` is nilpotent, so `Crystalline.finite_thetaPow_notMem_pPowSmul` and
`Crystalline.exists_Iic_thetaPow_mem_pPowSmul` of
`StacksFrontier/AlgebraicGeometry/Crystalline/PointedTaylorComparison.lean` leave only finitely many
terms, bounded by a `Finset.Iic`; and over the completion `D̂` the connection, the comparison and
the forms are all limits of their levels.  So the identity below is stated and proved at exactly
the generality the levels have: a sum over a downward closed finite set of multi-indices, with the
operators outside it killing `m`, and with no nilpotence of `p` assumed anywhere — none is needed,
because nothing here is a convergence statement.

## Main results

* `Crystalline.derivation_prod_eq` — the Leibniz rule for a finite product.
* `Crystalline.dividedPowerDerivation_taylorMonomial` — **the divided power derivative of a
  divided power monomial**, `d(ξ^{[K]}) = ∑_i ξ^{[K - e_i]} d(ξ_i)`.
* `Crystalline.taylorDeriv_eq_sum` — **the differentiated Taylor series is the coordinate-shifted
  Taylor series**, which is the identity horizontality reduces to.
* `Crystalline.nabla_taylorSum_eq` — **horizontality of the Taylor comparison**: the two terms the
  base-changed connection produces on the comparison add up to the comparison applied to the
  connection.

## What carries which tag

No `@[stacks 07L5]` attribute is placed in this module: [Stacks, Lemma 60.17.5, Tag 07L5] has two
assertions, a retract and an equivalence of categories of pairs, and a tag belongs on a
declaration stating the whole of what it claims.  The retract is
`Crystalline.exists_completedEnvelopeRetract` of
`StacksFrontier/AlgebraicGeometry/Crystalline/EnvelopeRetract.lean`; the direction `F ∘ G ≅ id` of
the second assertion is `Crystalline.CompletedConnection.exists_horizontalEquiv_of_retract` of
`StacksFrontier/AlgebraicGeometry/Crystalline/BaseChangeRetractPair.lean` on the pairs themselves,
and `Crystalline.CompletedDeRham.isIso_baseChangeComplexHom_comp_of_retract` of
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedConnectionBaseChangeComposite.lean` on the
completed de Rham complexes; and what is here is the step of the direction `G ∘ F ≅ id` that the
source omits, as an algebraic identity of finite sums.  Over the completed envelope that step is
`Crystalline.coordOp_taylorRoundTrip` of
`StacksFrontier/AlgebraicGeometry/Crystalline/TaylorRoundTrip.lean`, and the whole lemma is
`Crystalline.exists_presentation_retract_pairEquivalence` of
`StacksFrontier/AlgebraicGeometry/Crystalline/EnvelopeRetractEquivalence.lean`, which carries the
tag.

No `@[stacks 07JH]` attribute is placed here either: nothing in this module is about crystals, and
the subject is one comparison map for one module.

## References

* [Stacks Project, Lemma 60.17.5, Tag 07L5](https://stacks.math.columbia.edu/tag/07L5)
* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Tag 07HR](https://stacks.math.columbia.edu/tag/07HR)
* [Stacks Project, Tag 07JE](https://stacks.math.columbia.edu/tag/07JE)
-/

@[expose] public section

open scoped TensorProduct

universe u uI v uA

namespace Crystalline

/-! ### Multi-index arithmetic -/

section Index

variable {ι : Type uI} [DecidableEq ι]

omit [DecidableEq ι] in
/-- A single divided power monomial exponent vanishes away from its index. -/
private theorem single_one_apply_of_ne {i j : ι} (h : j ≠ i) :
    (Finsupp.single i 1 : ι →₀ ℕ) j = 0 := by
  classical
  simp [h]

omit [DecidableEq ι] in
/-- Subtracting one from a positive entry and adding it back is the identity. -/
theorem finsupp_sub_single_add_single {K : ι →₀ ℕ} {i : ι} (hi : 1 ≤ K i) :
    K - Finsupp.single i 1 + Finsupp.single i 1 = K := by
  exact tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hi)

omit [DecidableEq ι] in
/-- Adding one to an entry and subtracting it again is the identity. -/
theorem finsupp_add_single_sub_single (K : ι →₀ ℕ) (i : ι) :
    K + Finsupp.single i 1 - Finsupp.single i 1 = K := by
  exact add_tsub_cancel_right K _

omit [DecidableEq ι] in
/-- A multi-index decreases when one is subtracted from an entry. -/
theorem finsupp_sub_single_le (K : ι →₀ ℕ) (i : ι) : K - Finsupp.single i 1 ≤ K := by
  exact tsub_le_self

omit [DecidableEq ι] in
/-- The entry of `K + e_i` at `i` is positive. -/
theorem finsupp_one_le_add_single (K : ι →₀ ℕ) (i : ι) :
    1 ≤ (K + Finsupp.single i 1 : ι →₀ ℕ) i := by
  rw [Finsupp.add_apply, Finsupp.single_eq_same]
  omega

end Index

/-! ### The Leibniz rule for a finite product -/

section Prod

variable {B : Type u} [CommRing B] {Om : Type v} [AddCommGroup Om] [Module B Om]

/-- **The Leibniz rule for a finite product**: differentiating `∏_{i ∈ s} g i` differentiates one
factor at a time and carries the others along.  Mathlib has this for a power
(`Derivation.leibniz_pow`) but not for a `Finset.prod`; it is what turns the divided power chain
rule for a single `ξ_i^{[k_i]}` into the derivative of a divided power monomial. -/
theorem derivation_prod_eq (Dr : Derivation ℤ B Om) {ι : Type uI} [DecidableEq ι]
    (g : ι → B) (s : Finset ι) :
    Dr (∏ i ∈ s, g i) = ∑ i ∈ s, (∏ j ∈ s.erase i, g j) • Dr (g i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
      have key : ∀ i ∈ s, (∏ j ∈ (insert a s).erase i, g j) • Dr (g i) =
          g a • ((∏ j ∈ s.erase i, g j) • Dr (g i)) := by
        intro i hi
        have hne : a ≠ i := fun h ↦ ha (h ▸ hi)
        rw [Finset.erase_insert_of_ne hne,
          Finset.prod_insert (fun h ↦ ha (Finset.mem_of_mem_erase h)), smul_smul]
      rw [Finset.prod_insert ha, Dr.leibniz, Finset.sum_insert ha, Finset.erase_insert ha, ih,
        Finset.sum_congr rfl key, ← Finset.smul_sum]
      exact add_comm _ _

end Prod

/-! ### The divided power derivative of a divided power monomial -/

section Monomial

variable {B : DividedPowerRing.{u}} {ι : Type uI} [DecidableEq ι] {xi : ι → (B : Type u)}

omit [DecidableEq ι] in
/-- A divided power monomial may be written as a product over any finite set of indices
containing the support of its multi-index: the extra factors are `ξ_i^{[0]} = 1`. -/
theorem taylorMonomial_eq_prod (hxi : ∀ i, xi i ∈ B.ideal) (K : ι →₀ ℕ) (s : Finset ι)
    (hs : K.support ⊆ s) :
    taylorMonomial B xi K = ∏ i ∈ s, B.dividedPowers.dpow (K i) (xi i) := by
  rw [taylorMonomial]
  exact Finset.prod_subset hs fun i _ hi ↦ by
    rw [Finsupp.notMem_support_iff.mp hi, B.dividedPowers.dpow_zero (hxi i)]

/-- **The monomial of `K - e_i` is the monomial of `K` with one divided power removed from the
`i`-th factor.** -/
theorem taylorMonomial_sub_single (hxi : ∀ i, xi i ∈ B.ideal) {K : ι →₀ ℕ} {i : ι}
    (hi : i ∈ K.support) :
    taylorMonomial B xi (K - Finsupp.single i 1) =
      B.dividedPowers.dpow (K i - 1) (xi i) *
        ∏ j ∈ K.support.erase i, B.dividedPowers.dpow (K j) (xi j) := by
  rw [taylorMonomial_eq_prod hxi _ K.support
      (Finsupp.support_mono (finsupp_sub_single_le K i)),
    ← Finset.mul_prod_erase _ _ hi]
  refine congrArg₂ _ ?_ (Finset.prod_congr rfl fun j hj ↦ ?_)
  · rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
  · rw [Finsupp.tsub_apply, single_one_apply_of_ne (Finset.ne_of_mem_erase hj), Nat.sub_zero]

variable {A : Type uA} [CommRing A] {fB : A →+* (B : Type u)} {Om : Type v} [AddCommGroup Om]
  [Module (B : Type u) Om]

omit [DecidableEq ι] in
/-- **The divided power derivative of a divided power monomial**:

`d(ξ^{[K]}) = ∑_i ξ^{[K - e_i]} d(ξ_i)`,

the sum being over the support of `K`.  This is the divided power chain rule
`Crystalline.DividedPowerDerivation.map_dpow` of [Stacks, Tag 07HR] applied in each factor of
`ξ^{[K]} = ∏_i ξ_i^{[k_i]}`, the remaining factors being carried along by
`Crystalline.derivation_prod_eq`.

It is the coefficient identity horizontality of the Taylor comparison runs on: differentiating the
series term by term produces the terms of the series shifted by one coordinate, which is why the
Leibniz correction of the comparison cancels against the correction coming from the change of
coordinates. -/
theorem dividedPowerDerivation_taylorMonomial (Dr : DividedPowerDerivation A B fB Om)
    (hxi : ∀ i, xi i ∈ B.ideal) (K : ι →₀ ℕ) :
    Dr (taylorMonomial B xi K) =
      ∑ i ∈ K.support, taylorMonomial B xi (K - Finsupp.single i 1) • Dr (xi i) := by
  classical
  rw [taylorMonomial, derivation_prod_eq Dr.toDerivation]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hmd : Dr.toDerivation (B.dividedPowers.dpow (K i) (xi i)) =
      B.dividedPowers.dpow (K i - 1) (xi i) • Dr.toDerivation (xi i) :=
    Dr.map_dpow (K i) (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)) (xi i) (hxi i)
  rw [hmd, smul_smul, taylorMonomial_sub_single hxi hi, mul_comm]

end Monomial

/-! ### The differentiated Taylor series -/

section Horizontal

variable {D B : DividedPowerRing.{u}} [Algebra (D : Type u) (B : Type u)]
  {M : Type u} [AddCommGroup M] [Module (D : Type u) M]
  {ι : Type uI} [DecidableEq ι] {theta : ι → (M → M)} {thetaPow : (ι →₀ ℕ) → (M → M)}
  {xi : ι → (B : Type u)}
  {A : Type uA} [CommRing A] {fB : A →+* (B : Type u)} {Om : Type v} [AddCommGroup Om]
  [Module (B : Type u) Om]

omit [AddCommGroup M] [DecidableEq ι] in
/-- **Raising the `i`-th entry of a multi-index is applying one more `θ_i` first**, so the
`K`-th term of the Taylor series of `θ_i m` is the `(K + e_i)`-th coefficient family of `m`.  This
is `Crystalline.IsThetaMonomialFamily.add` at a one-point multi-index, and it is what makes the
inner sums of `Crystalline.nabla_taylorSum_eq` the values of the comparison on `θ_i m`. -/
theorem thetaPow_add_single_apply (hfam : IsThetaMonomialFamily M theta thetaPow) (K : ι →₀ ℕ)
    (i : ι) (m : M) : thetaPow (K + Finsupp.single i 1) m = thetaPow K (theta i m) := by
  have h1 := hfam.add (Finsupp.single i 1) K
  rw [hfam.single i 1, Function.iterate_one] at h1
  rw [add_comm K (Finsupp.single i 1), h1]
  rfl

/-- Moving a scalar of `B` from the differential to the coefficient of a Taylor term. -/
private theorem one_tmul_tmul_smul (c : (B : Type u)) (m' : M) (om : Om) :
    (((1 : (B : Type u)) ⊗ₜ[(D : Type u)] m') ⊗ₜ[(B : Type u)] (c • om)) =
      ((c ⊗ₜ[(D : Type u)] m') ⊗ₜ[(B : Type u)] om) := by
  have h1 : c • ((1 : (B : Type u)) ⊗ₜ[(D : Type u)] m') = c ⊗ₜ[(D : Type u)] m' := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul' (R := (B : Type u)), h1]

omit [DecidableEq ι] in
/-- A Taylor term indexed by a multi-index whose operator kills `m` contributes nothing. -/
private theorem tmul_thetaPow_eq_zero_of_not_le
    {m : M} {L : ι →₀ ℕ} (hvan : ∀ K, ¬ K ≤ L → thetaPow K m = 0) {K : ι →₀ ℕ} (hK : ¬ K ≤ L)
    (b : (B : Type u)) : b ⊗ₜ[(D : Type u)] thetaPow K m = 0 := by
  rw [hvan K hK, TensorProduct.tmul_zero]

/-- **The differentiated Taylor series is the coordinate-shifted Taylor series.**

For a Taylor series `∑_K ξ^{[K]} ⊗ θ_K(m)` whose surviving multi-indices are bounded by `L`,

`∑_K (1 ⊗ θ_K m) ⊗ d(ξ^{[K]}) = ∑_i (∑_K ξ^{[K]} ⊗ θ_{K + e_i} m) ⊗ d(ξ_i)`,

the outer sum on the right running over any finite set `t` of coordinates containing the support of
`L`.

**This is the step the proof of [Stacks, Lemma 60.17.5, Tag 07L5] leaves to the reader.**  Its
left-hand side is the Leibniz correction produced by differentiating the divided power coefficients
of the series, its right-hand side the correction produced by the change of coordinates
`ξ_i = f(x_i) - g(x_i)` in the base-changed connection, and
`Crystalline.nabla_taylorSum_eq` is the two put together — the horizontality the source states and
omits the verification of.

The proof is `Crystalline.dividedPowerDerivation_taylorMonomial` term by term, then the reindexing
`K = K' + e_i`: the `K`-term of the differentiated series in the direction `i` has coefficient
`ξ^{[K - e_i]}` and operator `θ_K = θ_{(K - e_i) + e_i}`, which is the `(K - e_i)`-term of the
right-hand side.  The multi-indices `K` with `K + e_i` not below `L` contribute nothing, by
`hvan`; that is where the quasi-nilpotence of the connection enters, in the form
`Crystalline.exists_Iic_thetaPow_mem_pPowSmul` gives it at a finite level of the `p`-adic tower.

Nothing here assumes `p` nilpotent, or indeed mentions `p`: both sides are finite sums, so the
identity is an algebraic one and holds at every level of the tower and hence in the limit. -/
theorem taylorDeriv_eq_sum (Dr : DividedPowerDerivation A B fB Om)
    (_hfam : IsThetaMonomialFamily M theta thetaPow) (hxi : ∀ i, xi i ∈ B.ideal) (m : M)
    (L : ι →₀ ℕ) (hvan : ∀ K, ¬ K ≤ L → thetaPow K m = 0) (t : Finset ι)
    (ht : L.support ⊆ t) :
    ∑ K ∈ Finset.Iic L,
        (((1 : (B : Type u)) ⊗ₜ[(D : Type u)] thetaPow K m) ⊗ₜ[(B : Type u)]
          Dr (taylorMonomial B xi K)) =
      ∑ i ∈ t, (∑ K ∈ Finset.Iic L,
            taylorMonomial B xi K ⊗ₜ[(D : Type u)] thetaPow (K + Finsupp.single i 1) m)
          ⊗ₜ[(B : Type u)] Dr (xi i) := by
  classical
  -- Each term of the left-hand side is a sum over the coordinates in `t`.
  have hterm : ∀ K ∈ Finset.Iic L,
      (((1 : (B : Type u)) ⊗ₜ[(D : Type u)] thetaPow K m) ⊗ₜ[(B : Type u)]
          Dr (taylorMonomial B xi K)) =
        ∑ i ∈ t, if 1 ≤ K i then
          ((taylorMonomial B xi (K - Finsupp.single i 1) ⊗ₜ[(D : Type u)] thetaPow K m)
            ⊗ₜ[(B : Type u)] Dr (xi i))
        else 0 := by
    intro K hK
    have hsub : K.support ⊆ t := fun i hi ↦ ht (Finsupp.support_mono (Finset.mem_Iic.mp hK) hi)
    rw [← Finset.sum_subset hsub (fun i _ hi ↦ by
        rw [ite_eq_right (by rw [Finsupp.notMem_support_iff.mp hi]; omega)]),
      dividedPowerDerivation_taylorMonomial Dr hxi K, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [ite_eq_left (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)),
      one_tmul_tmul_smul]
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [TensorProduct.sum_tmul, ← Finset.sum_filter]
  -- On the right, the multi-indices `K` with `K + e_i` not below `L` contribute nothing.
  rw [(Finset.sum_subset
    (Finset.filter_subset (fun K ↦ K + Finsupp.single i 1 ≤ L) (Finset.Iic L))
    (fun K hK hKn ↦ by
      rw [Finset.mem_filter] at hKn
      rw [tmul_thetaPow_eq_zero_of_not_le (D := D) hvan (fun h ↦ hKn ⟨hK, h⟩),
        TensorProduct.zero_tmul])).symm]
  -- The two index sets correspond under `K ↦ K + e_i`.
  have hmap : (Finset.Iic L).filter (fun K ↦ 1 ≤ K i) =
      Finset.map ⟨fun K ↦ K + Finsupp.single i 1, add_left_injective _⟩
        ((Finset.Iic L).filter (fun K ↦ K + Finsupp.single i 1 ≤ L)) := by
    ext K
    simp only [Finset.mem_filter, Finset.mem_Iic, Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨hKL, hKi⟩
      have hadd : K - Finsupp.single i 1 + Finsupp.single i 1 = K :=
        finsupp_sub_single_add_single hKi
      exact ⟨K - Finsupp.single i 1,
        ⟨le_trans (finsupp_sub_single_le K i) hKL, by rwa [hadd]⟩, hadd⟩
    · rintro ⟨K', ⟨-, hK'⟩, rfl⟩
      exact ⟨hK', finsupp_one_le_add_single K' i⟩
  rw [hmap, Finset.sum_map]
  refine Finset.sum_congr rfl fun K hK ↦ ?_
  simp only [Function.Embedding.coeFn_mk]
  rw [finsupp_add_single_sub_single K i]

/-- **Horizontality of the Taylor comparison of the proof of [Stacks, Proposition 60.17.4,
Tag 07JH]**, which is the step the proof of [Stacks, Lemma 60.17.5, Tag 07L5] omits.

Let `g = algebraMap D B` and `f : D → B` be the two divided power maps, `ξ_i = f(x_i) - g(x_i)`
their coordinate differences, and `c(m) = ∑_K ξ^{[K]} ⊗ θ_K(m)` the comparison.  Applying the
base-changed connection to `c(m)` produces two terms:

* the Leibniz correction `∑_K (1 ⊗ θ_K m) ⊗ d(ξ^{[K]})` of the divided power coefficients, and
* the connection term `∑_i (1 ⊗ θ_i θ_K m) ⊗ d(g(x_i))` summed against `ξ^{[K]}`, whose inner
  sums are the values `c(θ_i m)` because `θ_{K + e_i} = θ_K θ_i`
  (`Crystalline.thetaPow_add_single_apply`), and which is how they are written below;

and the conclusion says that their sum is `∑_i c(θ_i m) ⊗ d(f(x_i))`, which is the comparison
applied to `∇ m = ∑_i θ_i m ⊗ d x_i`.  So the displayed identity *is* `∇' ∘ c = (c ⊗ 1) ∘ ∇`,
written with the two terms of `∇'` in place rather than through a definition of the base-changed
connection, so that nothing about the comparison or the connection is assumed beyond what the
source gives.

The proof is `Crystalline.taylorDeriv_eq_sum` together with `d(ξ_i) = d(f(x_i)) - d(g(x_i))`,
which is additivity of the derivation.  As there, both sides are finite sums over the multi-indices
below `L`, which is what a finite level of the `p`-adic tower supplies, and no nilpotence of `p` is
assumed. -/
theorem nabla_taylorSum_eq (Dr : DividedPowerDerivation A B fB Om)
    (hfam : IsThetaMonomialFamily M theta thetaPow) (hxi : ∀ i, xi i ∈ B.ideal)
    (f : (D : Type u) →+* (B : Type u)) (x : ι → (D : Type u))
    (hxidef : ∀ i, xi i = f (x i) - algebraMap (D : Type u) (B : Type u) (x i))
    (m : M) (L : ι →₀ ℕ) (hvan : ∀ K, ¬ K ≤ L → thetaPow K m = 0) (t : Finset ι)
    (ht : L.support ⊆ t) :
    (∑ K ∈ Finset.Iic L,
          (((1 : (B : Type u)) ⊗ₜ[(D : Type u)] thetaPow K m) ⊗ₜ[(B : Type u)]
            Dr (taylorMonomial B xi K))) +
        ∑ i ∈ t, (∑ K ∈ Finset.Iic L,
              taylorMonomial B xi K ⊗ₜ[(D : Type u)] thetaPow K (theta i m))
            ⊗ₜ[(B : Type u)] Dr (algebraMap (D : Type u) (B : Type u) (x i)) =
      ∑ i ∈ t, (∑ K ∈ Finset.Iic L,
            taylorMonomial B xi K ⊗ₜ[(D : Type u)] thetaPow K (theta i m))
          ⊗ₜ[(B : Type u)] Dr (f (x i)) := by
  have hshift : ∀ (i : ι) (K : ι →₀ ℕ),
      taylorMonomial B xi K ⊗ₜ[(D : Type u)] thetaPow K (theta i m) =
        taylorMonomial B xi K ⊗ₜ[(D : Type u)] thetaPow (K + Finsupp.single i 1) m :=
    fun i K ↦ by rw [thetaPow_add_single_apply hfam K i m]
  simp only [hshift]
  rw [taylorDeriv_eq_sum Dr hfam hxi m L hvan t ht, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← TensorProduct.tmul_add]
  have hsub : Dr (xi i) + Dr (algebraMap (D : Type u) (B : Type u) (x i)) = Dr (f (x i)) := by
    rw [hxidef i]
    have : Dr.toDerivation (f (x i) - algebraMap (D : Type u) (B : Type u) (x i)) =
        Dr.toDerivation (f (x i)) - Dr.toDerivation (algebraMap (D : Type u) (B : Type u) (x i)) :=
      map_sub Dr.toDerivation _ _
    rw [show Dr (f (x i) - algebraMap (D : Type u) (B : Type u) (x i)) =
      Dr.toDerivation (f (x i) - algebraMap (D : Type u) (B : Type u) (x i)) from rfl, this]
    abel
  rw [hsub]

end Horizontal

end Crystalline

end
