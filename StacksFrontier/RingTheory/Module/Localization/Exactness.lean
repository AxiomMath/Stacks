module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.Order.Filter.AtTopBot.Finite
public import Mathlib.RingTheory.Ideal.Operations
import StacksCore.Tactic.StacksAttribute

@[expose] public section

/-!
# Exactness of the sheaf sequence of a standard cover

Proof of `IsLocalizedModule.Away.injective_pi_and_exact_of_span_range_eq_top`: for a family
`f : ι → R` generating the unit ideal and an `R`-module `M`, the sequence
`0 → M → ∏ i, M_{f i} → ∏ (i, j), M_{f i * f j}`
is exact, the first map being `m ↦ (m / 1)ᵢ` and the second `(mᵢ) ↦ (mᵢ / 1 - mⱼ / 1)`.

The mathematical content is the gluing lemma `exists_forall_map_eq_of_finite`: over a *finite*
family generating the unit ideal, a compatible family of sections is the restriction of a global
one. It is proved by the classical partition of unity computation: choose a single exponent `K`
and lifts `B i ∈ M` with `f i ^ K • x i = g i (B i)`, a single exponent `P` with
`(f i * f j) ^ P • (f j ^ K • B i) = (f i * f j) ^ P • (f i ^ K • B j)` for all `i, j`, and a
partition of unity `1 = ∑ i, d i * f i ^ (P + K)`; then `m = ∑ i, (d i * f i ^ P) • B i`
satisfies `f j ^ (P + K) • m = f j ^ P • B j` (`pow_smul_sum_smul_eq`), hence `g j m = x j`.

## Implementation notes

The source reduces to the case `f 1 = 1` by localizing at a maximal ideal, which needs the index
set to be finite (localization commutes with finite products only). The proof given here is the
same mathematics carried out directly, and works for an arbitrary index type: writing
`1 = ∑ i ∈ t, c i * f i` for a finite `t ⊆ ι`, the family `(f i)_{i ∈ t}` still generates the
unit ideal, so a compatible family is glued over `t` alone, and for an index `j` outside `t` the
difference `g j m - x j` dies in every `M_{f i * f j}` with `i ∈ t`, hence is zero
(`eq_zero_of_forall_map_eq_zero`). So no finiteness is imposed on `ι`, and no localization at a
maximal ideal is needed. That last step rests on two elementary observations:

* an element of an `R`-module killed by a power of every member of a family generating the unit
  ideal is zero (`eq_zero_of_forall_exists_pow_smul_eq_zero`), because the annihilator of the
  element is then an ideal whose radical is the unit ideal;
* an element of `M_b` dying in `M_{a * b}` is killed by a power of `a`
  (`exists_pow_smul_eq_zero_of_map_eq_zero`).

## References

* [Stacks Project, Tag 00EK](https://stacks.math.columbia.edu/tag/00EK)
-/

namespace IsLocalizedModule.Away

section Uniform

/-- If a predicate on exponents persists when the exponent is increased, and holds at some
exponent for each member of a finite family, then one exponent works for the whole family. -/
private lemma exists_forall_of_forall_exists {ι : Type*} [Finite ι] {p : ι → ℕ → Prop}
    (hmono : ∀ i n, p i n → p i (n + 1)) (h : ∀ i, ∃ n, p i n) : ∃ n, ∀ i, p i n := by
  have key : ∀ i, ∀ᶠ n in Filter.atTop, p i n := fun i ↦ by
    obtain ⟨n, hn⟩ := h i
    exact Filter.eventually_atTop.2
      ⟨n, fun m hm ↦ Nat.le_induction hn (fun k _ ih ↦ hmono i k ih) m hm⟩
  exact (Filter.eventually_atTop.1 (Filter.eventually_all.2 key)).imp fun n hn ↦ hn n le_rfl

end Uniform

section Annihilator

variable {R N : Type*} [CommSemiring R] [AddCommGroup N] [Module R N]

/-- If a set of elements of `R` generates the unit ideal and each of them kills `y` after being
raised to some power, then `y = 0`: the annihilator of `y` has radical the unit ideal. -/
private lemma eq_zero_of_forall_exists_pow_smul_eq_zero {s : Set R}
    (hs : Ideal.span s = ⊤) {y : N} (h : ∀ a ∈ s, ∃ n : ℕ, a ^ n • y = 0) : y = 0 := by
  set J : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R N y) with hJ
  have hle : Ideal.span s ≤ J.radical := Ideal.span_le.2 fun a ha ↦
    Ideal.mem_radical_iff.2 <| (h a ha).imp fun n hn ↦ by
      simpa [hJ, LinearMap.toSpanSingleton_apply] using hn
  rw [hs] at hle
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.1 (hle Submodule.mem_top : (1 : R) ∈ J.radical)
  simpa [hJ, LinearMap.toSpanSingleton_apply] using hn

end Annihilator

section Away

variable {R M Mb Mab : Type*} [CommSemiring R] [AddCommGroup M] [Module R M]
  [AddCommGroup Mb] [Module R Mb] [AddCommGroup Mab] [Module R Mab]

/-- An element of `M` dying in the localization of `M` away from `b` is killed by a power
of `b`. -/
private lemma exists_pow_smul_eq_zero (b : R) (gb : M →ₗ[R] Mb) [IsLocalizedModule.Away b gb]
    {y : M} (hy : gb y = 0) : ∃ n : ℕ, b ^ n • y = 0 :=
  (IsLocalizedModule.Away.exists_of_eq b (hy.trans (map_zero gb).symm)).imp fun n hn ↦ by
    simpa using hn

/-- Multiplication by a power of `b` is injective on a localization of a module away from `b`. -/
private lemma pow_smul_left_cancel (b : R) (gb : M →ₗ[R] Mb) [IsLocalizedModule.Away b gb]
    (n : ℕ) {y z : Mb} (h : b ^ n • y = b ^ n • z) : y = z :=
  IsLocalizedModule.smul_injective (S := Submonoid.powers b) gb ⟨b ^ n, n, rfl⟩ h

/-- If `z`, an element of the localization of `M` away from `b`, is killed by the map to the
localization of `M` away from `a * b`, then some power of `a` kills `z`. -/
private lemma exists_pow_smul_eq_zero_of_map_eq_zero (a b : R) (gb : M →ₗ[R] Mb)
    [IsLocalizedModule.Away b gb] (ρ : Mb →ₗ[R] Mab)
    [IsLocalizedModule.Away (a * b) (ρ.comp gb)] {z : Mb} (hz : ρ z = 0) :
    ∃ n : ℕ, a ^ n • z = 0 := by
  obtain ⟨e, w, hw⟩ := IsLocalizedModule.Away.surj gb b z
  obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero (a * b) (ρ.comp gb)
    (show (ρ.comp gb) w = 0 by rw [LinearMap.comp_apply, ← hw, map_smul, hz, smul_zero])
  refine ⟨n, pow_smul_left_cancel b gb (n + e) ?_⟩
  rw [smul_zero, smul_smul, show b ^ (n + e) * a ^ n = (a * b) ^ n * b ^ e by ring, ← smul_smul,
    hw, ← map_smul, hn, map_zero]

/-- An element of the localization of `M` away from `b` that dies in the localization away from
`f i * b` for every member of a family `f` generating the unit ideal is zero. -/
private lemma eq_zero_of_forall_map_eq_zero {ι : Type*} {f : ι → R} (b : R) (gb : M →ₗ[R] Mb)
    [IsLocalizedModule.Away b gb] {Mfb : ι → Type*} [∀ i, AddCommGroup (Mfb i)]
    [∀ i, Module R (Mfb i)] (ρ : ∀ i, Mb →ₗ[R] Mfb i)
    [∀ i, IsLocalizedModule.Away (f i * b) ((ρ i).comp gb)]
    (hf : Ideal.span (Set.range f) = ⊤) {z : Mb} (hz : ∀ i, ρ i z = 0) : z = 0 :=
  eq_zero_of_forall_exists_pow_smul_eq_zero hf <| by
    rintro a ⟨i, rfl⟩
    exact exists_pow_smul_eq_zero_of_map_eq_zero (f i) b gb (ρ i) (hz i)

end Away

section Pair

variable {R M Mi Mj Mij : Type*} [CommSemiring R] [AddCommGroup M] [Module R M]
  [AddCommGroup Mi] [Module R Mi] [AddCommGroup Mj] [Module R Mj]
  [AddCommGroup Mij] [Module R Mij]

/-- Applying `l ∘ g` to `d ^ K • B`, where `c ^ K • x = g B`, gives `d ^ K • c ^ K • l x`. -/
private lemma map_pow_smul_eq {Mx Mij : Type*} [AddCommGroup Mx] [Module R Mx]
    [AddCommGroup Mij] [Module R Mij] (g : M →ₗ[R] Mx) (l : Mx →ₗ[R] Mij) {c d : R} {K : ℕ}
    {x : Mx} {B : M} (h : c ^ K • x = g B) : l (g (d ^ K • B)) = d ^ K • c ^ K • l x := by
  rw [map_smul, ← h, map_smul, map_smul]

/-- Two elements `xi`, `xj` of the localizations of `M` away from `a`, `b` with the same image in
the localization away from `a * b` have local lifts `Bi`, `Bj` — witnesses of
`a ^ K • xi = gi Bi` and `b ^ K • xj = gj Bj` — which agree in `M` after multiplication by a
power of `a * b`. -/
private lemma exists_pow_smul_smul_eq {a b : R} (gi : M →ₗ[R] Mi) (gj : M →ₗ[R] Mj)
    (lij : Mi →ₗ[R] Mij) (rij : Mj →ₗ[R] Mij) [IsLocalizedModule.Away (a * b) (lij.comp gi)]
    (hlr : lij.comp gi = rij.comp gj) {K : ℕ} {xi : Mi} {xj : Mj} {Bi Bj : M}
    (hi : a ^ K • xi = gi Bi) (hj : b ^ K • xj = gj Bj) (h : lij xi = rij xj) :
    ∃ n : ℕ, (a * b) ^ n • (b ^ K • Bi) = (a * b) ^ n • (a ^ K • Bj) := by
  have key : (lij.comp gi) (b ^ K • Bi) = (lij.comp gi) (a ^ K • Bj) := by
    rw [LinearMap.comp_apply, map_pow_smul_eq gi lij hi, h, hlr, LinearMap.comp_apply,
      map_pow_smul_eq gj rij hj, smul_comm]
  exact IsLocalizedModule.Away.exists_of_eq (f := lij.comp gi) (a * b) key

end Pair

section Glue

variable {R M : Type*} [CommSemiring R] [AddCommGroup M] [Module R M]
  {ι : Type*} {f : ι → R}
  {Mf : ι → Type*} [∀ i, AddCommGroup (Mf i)] [∀ i, Module R (Mf i)]
  {Mff : ι → ι → Type*} [∀ i j, AddCommGroup (Mff i j)] [∀ i j, Module R (Mff i j)]

/-- The partition of unity computation behind the gluing: if `1 = ∑ i, d i * f i ^ (P + K)` and
the lifts `B i` agree pairwise after multiplication by `(f i * f j) ^ P`, then
`m = ∑ i, (d i * f i ^ P) • B i` satisfies `f j ^ (P + K) • m = f j ^ P • B j` for every `j`. -/
private lemma pow_smul_sum_smul_eq [Fintype ι] {B : ι → M} {d : ι → R} {P K : ℕ}
    (hd : ∑ i, d i * f i ^ (P + K) = 1)
    (hB : ∀ i j, ((f i * f j) ^ P * f j ^ K) • B i = ((f i * f j) ^ P * f i ^ K) • B j) (j : ι) :
    f j ^ (P + K) • ∑ i, (d i * f i ^ P) • B i = f j ^ P • B j := by
  rw [Finset.smul_sum]
  calc ∑ i, f j ^ (P + K) • (d i * f i ^ P) • B i
      = ∑ i, (d i * f i ^ (P + K)) • (f j ^ P • B j) := Finset.sum_congr rfl fun i _ ↦ by
        rw [smul_smul, smul_smul,
          show f j ^ (P + K) * (d i * f i ^ P) = d i * ((f i * f j) ^ P * f j ^ K) by ring,
          show d i * f i ^ (P + K) * f j ^ P = d i * ((f i * f j) ^ P * f i ^ K) by ring,
          mul_smul (d i) _ (B i), mul_smul (d i) _ (B j), hB i j]
    _ = (∑ i, d i * f i ^ (P + K)) • (f j ^ P • B j) := by rw [← Finset.sum_smul]
    _ = f j ^ P • B j := by rw [hd, one_smul]

/-- Gluing over a finite cover: if the `f i`, for `i` in a finite index type, generate the unit
ideal, then a family of sections `x i` of the localizations away from the `f i` agreeing pairwise
in the localizations away from the `f i * f j` is the family of images of a single element
of `M`. -/
private lemma exists_forall_map_eq_of_finite [Finite ι] (g : ∀ i, M →ₗ[R] Mf i)
    [∀ i, IsLocalizedModule.Away (f i) (g i)]
    (l : ∀ i j, Mf i →ₗ[R] Mff i j) (r : ∀ i j, Mf j →ₗ[R] Mff i j)
    [∀ i j, IsLocalizedModule.Away (f i * f j) ((l i j).comp (g i))]
    (hf : Ideal.span (Set.range f) = ⊤)
    (hlr : ∀ i j, (l i j).comp (g i) = (r i j).comp (g j))
    {x : ∀ i, Mf i} (hx : ∀ i j, l i j (x i) = r i j (x j)) :
    ∃ m : M, ∀ i, g i m = x i := by
  cases nonempty_fintype ι
  obtain ⟨K, hK⟩ := exists_forall_of_forall_exists
    (p := fun i n ↦ ∃ y : M, f i ^ n • x i = g i y)
    (fun i n ⟨y, hy⟩ ↦ ⟨f i • y, by rw [pow_succ', mul_smul, hy, map_smul]⟩)
    (fun i ↦ IsLocalizedModule.Away.surj (g i) (f i) (x i))
  choose B hB using hK
  obtain ⟨P, hP⟩ := exists_forall_of_forall_exists
    (p := fun p : ι × ι ↦ fun n ↦
      (f p.1 * f p.2) ^ n • (f p.2 ^ K • B p.1) = (f p.1 * f p.2) ^ n • (f p.1 ^ K • B p.2))
    (fun p n hn ↦ by rw [pow_succ', mul_smul, hn, mul_smul (f p.1 * f p.2) _ (f p.1 ^ K • B p.2)])
    (fun p ↦ exists_pow_smul_smul_eq (g p.1) (g p.2) (l p.1 p.2) (r p.1 p.2) (hlr p.1 p.2)
      (hB p.1) (hB p.2) (hx p.1 p.2))
  have hspan : Ideal.span (Set.range fun i ↦ f i ^ (P + K)) = ⊤ := by
    have h := Ideal.span_pow_eq_top _ hf (P + K)
    rwa [← Set.range_comp] at h
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 ((Ideal.eq_top_iff_one _).1 hspan)
  refine ⟨∑ i, (d i * f i ^ P) • B i, fun j ↦ pow_smul_left_cancel (f j) (g j) (P + K) ?_⟩
  rw [← map_smul, pow_smul_sum_smul_eq (by simpa using hd)
      (fun i j ↦ by simpa [smul_smul] using hP (i, j)) j, map_smul,
    ← hB j, smul_smul, ← pow_add]

end Glue

end IsLocalizedModule.Away

/-!
# The sheaf sequence of a standard cover of an affine scheme

Let `R` be a commutative ring, let `f : ι → R` be a family of elements generating the unit
ideal, so that the standard opens `D(f i)` cover `Spec R`, and let `M` be an `R`-module. Then
the sequence of `R`-modules
`0 → M → ∏ i, M_{f i} → ∏ (i, j), M_{f i * f j}`,
whose first map sends `m` to the family of its images `m / 1`, and whose second map sends a
family `(m i)` to the family of differences `m i / 1 - m j / 1` computed in `M_{f i * f j}`, is
exact. Equivalently: an element of `M` is determined by its images in the `M_{f i}`, and a
family of elements `m i ∈ M_{f i}` agreeing pairwise in the `M_{f i * f j}` comes from an
element of `M`. This is the sheaf condition for the quasi-coherent module `M` on the standard
opens of `Spec R`.

## Main results

* `IsLocalizedModule.Away.injective_pi_and_exact_of_span_range_eq_top`: for a family generating
  the unit ideal, the map `M → ∏ i, M_{f i}` is injective and the sequence above is exact at
  `∏ i, M_{f i}`.

## Implementation notes

The localizations are taken abstractly: `Mf i` is any `R`-module with an `R`-linear
`g i : M →ₗ[R] Mf i` making it a localization of `M` away from `f i`, and `Mff i j` is any
`R`-module receiving `l i j : Mf i →ₗ[R] Mff i j` and `r i j : Mf j →ₗ[R] Mff i j` such that
the composite `l i j ∘ g i : M →ₗ[R] Mff i j` is a localization of `M` away from `f i * f j`.
This is the shape of the localization results in `Mathlib.RingTheory.LocalProperties.Exactness`,
and it frees each application from transporting along an isomorphism onto a chosen model such
as `LocalizedModule.Away (f i) M`.

The source's direct sums are products, over an arbitrary index type. Both are genuine
generalizations of the source's finite `f 1, …, f n`, for which the two agree: exactness of the
sequence needs no finiteness, because a family generating the unit ideal contains a finite
subfamily that does, and a section over the whole family is pinned by its restrictions to that
subfamily. Mathlib phrases the ring-level injectivity the same way, over a product indexed by
an arbitrary set (`Localization.algebraMap_injective_of_span_eq_top`).

Exactness of a four-term sequence `0 → M → N → P` is stated as injectivity of `M → N`
together with `Function.Exact` for the pair `M → N → P`; the first conjunct is exactness at
`M` and the second exactness at `N`.

Faithfulness. (1) Both hypotheses are used: `hf` is what makes the standard opens `D(f i)`
cover `Spec R`, and `hlr` — that the two composites `M → Mf i → Mff i j` and
`M → Mf j → Mff i j` agree — is what makes the composite of the two maps of the sequence
vanish. (2) The scalars are the source's: this is a sequence of `R`-modules and `R`-linear
maps, not of modules over any localization of `R`. (3) The canonical maps of the source are
pinned, not merely assumed to exist: `g i` is pinned as the localization map `m ↦ m / 1` by
`IsLocalizedModule.Away (f i)`, and `l i j`, `r i j` are then the unique `R`-linear maps out of
the localizations `Mf i`, `Mf j` whose composites with `g i`, `g j` are the localization map
`M → Mff i j` away from `f i * f j`, which is exactly what is required of them; so all three
families are the maps `m / f i ^ e ↦ m / f i ^ e` of the source, and no choice is left.
(4) The instantiation is not degenerate: `R = ℤ`, `ι = Fin 2`, `f = ![2, 3]`, `M = ℤ`,
`Mf i = LocalizedModule.Away (f i) ℤ` and `Mff i j = LocalizedModule.Away (f i * f j) ℤ`
satisfy the hypotheses, and there `M → ∏ i, M_{f i}` is far from surjective.

## References

* [Stacks Project, Tag 00EK](https://stacks.math.columbia.edu/tag/00EK)
-/

namespace IsLocalizedModule.Away

variable {R : Type*} [CommSemiring R] {M : Type*} [AddCommGroup M] [Module R M]
  {ι : Type*} {f : ι → R}
  {Mf : ι → Type*} [∀ i, AddCommGroup (Mf i)] [∀ i, Module R (Mf i)]
  {Mff : ι → ι → Type*} [∀ i j, AddCommGroup (Mff i j)] [∀ i j, Module R (Mff i j)]
  (g : ∀ i, M →ₗ[R] Mf i) [∀ i, IsLocalizedModule.Away (f i) (g i)]
  (l : ∀ i j, Mf i →ₗ[R] Mff i j) (r : ∀ i j, Mf j →ₗ[R] Mff i j)
  [∀ i j, IsLocalizedModule.Away (f i * f j) ((l i j).comp (g i))]

/-- Let `R` be a commutative semiring, let `f : ι → R` be a family of elements generating the unit
ideal and let `M` be an `R`-module. Let `Mf i` be the localization of `M` away from `f i`, with
localization map `g i`, and let `Mff i j` be the localization of `M` away from `f i * f j`,
reached from `Mf i` by `l i j` and from `Mf j` by `r i j`. Then the sequence
`0 → M → ∏ i, Mf i → ∏ (i, j), Mff i j`
is exact, the first map being `m ↦ (g i m)` and the second
`(m i) ↦ (l i j (m i) - r i j (m j))`. -/
@[stacks 00EK]
public theorem injective_pi_and_exact_of_span_range_eq_top
    (hf : Ideal.span (Set.range f) = ⊤)
    (hlr : ∀ i j, (l i j).comp (g i) = (r i j).comp (g j)) :
    Function.Injective (LinearMap.pi g) ∧
      Function.Exact (LinearMap.pi g) (LinearMap.pi fun p : ι × ι ↦
        (l p.1 p.2).comp (LinearMap.proj p.1) - (r p.1 p.2).comp (LinearMap.proj p.2)) := by
  classical
  constructor
  · rw [injective_iff_map_eq_zero]
    refine fun m hm ↦ eq_zero_of_forall_exists_pow_smul_eq_zero hf ?_
    rintro a ⟨i, rfl⟩
    exact exists_pow_smul_eq_zero (f i) (g i) (by simpa using congrFun hm i)
  · intro x
    constructor
    · intro hx
      have hcompat : ∀ i j, l i j (x i) = r i j (x j) := fun i j ↦ by
        simpa [sub_eq_zero] using congrFun hx (i, j)
      obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1
        ((Ideal.eq_top_iff_one _).1 hf)
      have hspan : Ideal.span (Set.range fun i : (c.support : Set ι) ↦ f i) = ⊤ := by
        rw [Ideal.eq_top_iff_one, ← hc, Finsupp.sum]
        exact Submodule.sum_mem _ fun i hi ↦
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)
      obtain ⟨m, hm⟩ := exists_forall_map_eq_of_finite (f := fun i : (c.support : Set ι) ↦ f i)
        (fun i ↦ g i) (fun i j ↦ l i j) (fun i j ↦ r i j) hspan (fun i j ↦ hlr i j)
        (x := fun i ↦ x i) (fun i j ↦ hcompat i j)
      refine ⟨m, funext fun j ↦ ?_⟩
      have : ∀ i : (c.support : Set ι),
          IsLocalizedModule.Away (f i * f j) ((r i j).comp (g j)) := fun i ↦ by
        rw [← hlr i j]
        infer_instance
      have hzero : g j m - x j = 0 :=
        eq_zero_of_forall_map_eq_zero (f j) (g j) (fun i : (c.support : Set ι) ↦ r i j) hspan
          fun i ↦ by
          rw [map_sub, ← LinearMap.comp_apply, ← hlr i j, LinearMap.comp_apply, hm i,
            hcompat i j, sub_self]
      simpa using sub_eq_zero.1 hzero
    · rintro ⟨m, rfl⟩
      funext p
      simp only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply,
        LinearMap.proj_apply, Pi.zero_apply]
      rw [sub_eq_zero, ← LinearMap.comp_apply, ← LinearMap.comp_apply, hlr]

end IsLocalizedModule.Away
