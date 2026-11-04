module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Int.Star
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.GradedAlgebra.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Veronese subrings of a finitely generated graded ring are generated in degree one

Throughout, fix a graded ring `S`. Following the Stacks Project (Tag 00JL), this
means a commutative ring `S` together with a direct sum decomposition of its
underlying additive group `S = ⨁_{d ≥ 0} S_d` indexed by the non-negative
integers `d ≥ 0`, such that `1 ∈ S_0` and `S_d · S_e ⊆ S_{d+e}` for all
`d, e ≥ 0`. In particular each `S_d` is an `S_0`-module, `S_0` is a subring of
`S`, and there are no nonzero elements in negative degrees.

We model such an `S` as a commutative ring `A` together with a family
`𝒜 : ℕ → σ` of additive subgroups (a `SetLike` family) such that `[GradedRing 𝒜]`
holds. In this version of Mathlib the class `GradedRing 𝒜` bundles together:
* `SetLike.GradedMonoid 𝒜`, i.e. `1 ∈ 𝒜 0` and `𝒜 i · 𝒜 j ⊆ 𝒜 (i + j)`; and
* `DirectSum.Decomposition 𝒜`, i.e. the additive group of `A` is the *direct sum*
  `⨁_{d} 𝒜 d` (every element decomposes uniquely into finitely many homogeneous
  pieces).
Thus `[GradedRing 𝒜]` is exactly the genuine graded-ring decomposition required
by the problem; in particular the exhaustiveness and uniqueness of the
homogeneous decomposition are part of the hypothesis (they are recorded by
`GradedRing.toDecomposition : DirectSum.Decomposition 𝒜`). Since the index type
is `ℕ`, the "no nonzero elements in negative degrees" condition is built in. The
degree-zero part `S_0` is the subring `SetLike.GradeZero.subring 𝒜`, over which
`A` is an algebra.

If `A` is finitely generated as an `S_0`-algebra, then for all
sufficiently divisible `d` the Veronese subring `S^{(d)} = ⨁_{n} S_{nd}` is
generated in degree `1` over `S_0`, i.e. for every `n ≥ 1` the `S_0`-module
`S_{nd}` is spanned by the `n`-fold products `g_1 ⋯ g_n` with each `g_i ∈ S_d`.
-/

@[expose] public section

namespace Stacks.Veronese

variable {A : Type*} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The degree-zero part `S_0` of the graded ring, as a subring. This is the base
ring over which we form modules and algebras. -/
abbrev gradeZero : Subring A := SetLike.GradeZero.subring 𝒜

/-- The Veronese subring's degree-`n` component: the degree-`n`
homogeneous component of the Veronese subring `S^{(d)}` is `S_{nd}`. By
construction `(S^{(d)})_0 = S_0 = 𝒜 0` and `(S^{(d)})_1 = S_d = 𝒜 d`. -/
@[ega "II 2.1.1"]
def veroneseComponent (d n : ℕ) : σ := 𝒜 (n * d)

/-- The reindexed family of components `n ↦ S_{nd}` is again a graded monoid: it
contains `1` in degree `0` and is closed under multiplication of degrees. This is
the multiplicative skeleton of the Veronese subring `S^{(d)}` viewed as a graded
ring with `(S^{(d)})_n = S_{nd}`. -/
@[ega "II 2.1.1" "partial"]
instance veroneseGradedMonoid (d : ℕ) :
    SetLike.GradedMonoid (fun n => 𝒜 (n * d)) where
  one_mem := by simpa using SetLike.GradedOne.one_mem (A := 𝒜)
  mul_mem := by
    intro i j gi gj hi hj
    rw [add_mul]
    exact SetLike.GradedMul.mul_mem hi hj

/-- The Veronese subring as a genuine subring of `S`: the Veronese
subring `S^{(d)} = ⨁_{n ≥ 0} S_{nd}` is realized as the subring of `A` generated
by the homogeneous elements whose degree is a multiple of `d`. Its homogeneous
components are exactly the `S_{nd}` (see `veroneseComponent`); the ring operations
and the `S_0`-action are inherited from `A`. -/
def veroneseSet (d : ℕ) : Set A := ⋃ n : ℕ, (𝒜 (n * d) : Set A)

/-- The Veronese subring `S^{(d)}` as a `Subring A` (the additive/subring closure
of all homogeneous pieces in degrees divisible by `d`). Since `veroneseSet` is
closed under multiplication and contains `1`, this subring consists exactly of the
finite sums of homogeneous elements of degrees divisible by `d`, i.e. of
`⨁_{n} S_{nd}` inside `A`. -/
@[ega "II 2.1.1" "underlying ring of S^(d)"]
noncomputable def veroneseSubring (d : ℕ) : Subring A :=
  Subring.closure (veroneseSet 𝒜 d)

/-- The set of `n`-fold products `g_1 g_2 ⋯ g_n` of
elements `g_i ∈ S_d`. For `n = 0` this is the singleton `{1}` (empty product). -/
def degOneProducts (d n : ℕ) : Set A :=
  {x : A | ∃ g : Fin n → A, (∀ i, g i ∈ 𝒜 d) ∧ x = ∏ i, g i}

/-- Generated in degree `1` over `S_0`, applied to the Veronese
subring `S^{(d)}`). The Veronese subring `S^{(d)}` is generated in degree `1`
over `S_0` if for every `n ≥ 1` the `S_0`-module `S_{nd}` *equals* the
`S_0`-submodule of `A` spanned by all `n`-fold products `g_1 ⋯ g_n` with each
`g_i ∈ S_d`. We state this as an equality of subsets of `A`: the homogeneous
component `S_{nd} = 𝒜 (n*d)` coincides with the `S_0`-span of `degOneProducts`.
(The reverse inclusion ⊇ is automatic since such products are themselves
homogeneous of degree `nd` and `S_0 = 𝒜 0` preserves degrees; we nonetheless
require full equality to match the problem statement.) -/
def VeroneseGeneratedInDegOne (d : ℕ) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (𝒜 (n * d) : Set A) =
      (Submodule.span (gradeZero 𝒜) (degOneProducts 𝒜 d n) : Set A)

/-- `S` is finitely generated over
`S_0` if it is finitely generated as an `S_0`-algebra. We use Mathlib's
`Algebra.FiniteType`, where the base ring is the grade-zero subring. -/
def FinitelyGeneratedOverGradeZero : Prop :=
  Algebra.FiniteType (gradeZero 𝒜) A

/-- "For all sufficiently divisible `d`": a predicate `P` on
positive integers holds for all sufficiently divisible `d` if there is a
`d₀ ≥ 1` such that `P d` holds for every positive multiple `d` of `d₀`. -/
@[sga "3 XI 4.5"]
def ForAllSufficientlyDivisible (P : ℕ → Prop) : Prop :=
  ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, 1 ≤ d → d₀ ∣ d → P d

/-- Reduce finite generation to a finite set of positive-degree homogeneous
generators. From `Algebra.FiniteType (S_0) A` extract a finite family `f : Fin r → A`
with degrees `deg : Fin r → ℕ`, each `deg i ≥ 1` and `f i ∈ 𝒜 (deg i)`, such that
`A = S_0[f_1,...,f_r]` as an `S_0`-algebra. (Degree-0 generators may be dropped since
they live in `S_0`; each generator can be replaced by its finitely many homogeneous
components — this uses `DirectSum.Decomposition`.)

STRATEGY: `Algebra.FiniteType` gives a finite `s : Finset A` with `adjoin S_0 s = ⊤`.
For each generator `a ∈ s`, decompose `a = ∑_d (DirectSum.decompose 𝒜 a) d` into its
finitely many nonzero homogeneous components (`DirectSum.Decomposition`/`decompose`);
the support is finite. Collect ALL the positive-degree components of ALL generators into
one finite family `f`, with `deg` its degree. Dropping the degree-0 components is fine:
they live in `𝒜 0 = S_0` (the base ring), so `adjoin` is unchanged
(`Algebra.adjoin_insert_adjoin` / `adjoin` of base-ring elements is `⊤`-neutral). The
original generators are recovered as `S_0`-combinations of the `f i` plus a base element,
so `adjoin S_0 (range f) = ⊤`. **Likely the hardest lemma.** -/
theorem homogeneous_generators_of_finiteType
    (h : FinitelyGeneratedOverGradeZero 𝒜) :
    ∃ (r : ℕ) (f : Fin r → A) (deg : Fin r → ℕ),
      (∀ i, 1 ≤ deg i) ∧ (∀ i, f i ∈ 𝒜 (deg i)) ∧
      Algebra.adjoin (gradeZero 𝒜) (Set.range f) = ⊤ := by
  classical
  obtain ⟨s, hs⟩ := h.out
  set t : Finset (A × ℕ) :=
    s.biUnion fun a =>
      ((DirectSum.decompose 𝒜 a).support.filter (fun i => 1 ≤ i)).image fun i => (a, i) with ht
  have htmem : ∀ p : A × ℕ, p ∈ t ↔
      p.fst ∈ s ∧ 1 ≤ p.snd ∧ (DirectSum.decompose 𝒜 p.fst p.snd : A) ≠ 0 := by
    intro p
    rw [ht]
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter, DFinsupp.mem_support_toFun]
    constructor
    · rintro ⟨a, ha, i, ⟨hi1, hi2⟩, heq⟩
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp heq.symm
      refine ⟨ha, hi2, fun hcontra => hi1 ?_⟩
      ext
      simp [hcontra]
    · rintro ⟨h1, h2, h3⟩
      exact ⟨p.fst, h1, p.snd, ⟨fun hcontra => h3 (by simp [hcontra]), h2⟩, rfl⟩
  set ev : Fin t.card ≃ t := t.equivFin.symm
  set f : Fin t.card → A := fun j =>
    (DirectSum.decompose 𝒜 (ev j : A × ℕ).fst (ev j : A × ℕ).snd : A) with hf
  refine ⟨t.card, f, fun j => (ev j : A × ℕ).snd,
    fun j => ((htmem _).mp (ev j).property).right.left, fun j => SetLike.coe_mem _, ?_⟩
  -- key: components in t are in range f
  have hrange : ∀ p : A × ℕ, p ∈ t → (DirectSum.decompose 𝒜 p.fst p.snd : A) ∈ Set.range f :=
    fun p hp => ⟨ev.symm ⟨p, hp⟩, by
      simp only [hf]
      rw [show (↑(ev (ev.symm ⟨p, hp⟩)) : A × ℕ) = p by rw [Equiv.apply_symm_apply]]⟩
  rw [eq_top_iff, ← hs]
  apply Algebra.adjoin_le
  intro a ha
  -- a = ∑ i ∈ support, component i, each in adjoin
  rw [SetLike.mem_coe, ← DirectSum.sum_support_decompose 𝒜 a]
  refine Subalgebra.sum_mem _ fun i hi => ?_
  obtain rfl | hipos := Nat.eq_zero_or_pos i
  · exact Subalgebra.algebraMap_mem _ (⟨_, (SetLike.coe_mem _ : _ ∈ 𝒜 0)⟩ : gradeZero 𝒜)
  · exact Algebra.subset_adjoin (hrange (a, i) ((htmem _).mpr ⟨ha, hipos, by simpa using hi⟩))

/-- A `k`-th power of an element of `𝒜 d` lies in `𝒜 (k * d)`. -/
private theorem pow_mem_grade_mul {a : A} {d : ℕ} (ha : a ∈ 𝒜 d) (k : ℕ) :
    a ^ k ∈ 𝒜 (k * d) := by
  simpa only [smul_eq_mul] using SetLike.pow_mem_graded k ha

/-- A monomial in homogeneous elements `f i ∈ 𝒜 (deg i)` is homogeneous of the total degree. -/
private theorem prod_pow_mem_grade_sum {r : ℕ} (f : Fin r → A) (deg : Fin r → ℕ)
    (hfdeg : ∀ i, f i ∈ 𝒜 (deg i)) (e : Fin r → ℕ) :
    (∏ i, f i ^ e i) ∈ 𝒜 (∑ i, e i * deg i) :=
  SetLike.prod_mem_graded 𝒜 _ _ fun i _ => pow_mem_grade_mul 𝒜 (hfdeg i) (e i)

/-- Step B (monomial spanning): every homogeneous element of degree `n` is an
`S_0`-linear combination of monomials `∏ f_i^{e_i}` whose total degree
`∑ e_i * deg i = n`. We phrase it as: `𝒜 n` (as a set) is contained in the
`S_0`-span of the set of such monomials.

STRATEGY: Since `adjoin S_0 (range f) = ⊤`, every `x ∈ A` is an `S_0`-polynomial in the
`f i` (`Algebra.adjoin_eq_top`/`mem_adjoin` → `MvPolynomial` aeval surjectivity), i.e. an
`S_0`-linear combination of monomials `∏ f_i^{e_i}`. Each monomial is homogeneous of
degree `∑ e_i * deg i` (by Step E `pow_mem_grade` + graded mul). Apply the degree-`n`
homogeneous projection `GradedRing.proj 𝒜 n` (an `S_0`-linear map fixing `𝒜 n`): it kills
the monomials of degree `≠ n` and keeps exactly the degree-`n` ones, exhibiting `x ∈ 𝒜 n`
in the span of degree-`n` monomials. -/
theorem mem_span_monomials
    {r : ℕ} (f : Fin r → A) (deg : Fin r → ℕ)
    (hdeg : ∀ i, f i ∈ 𝒜 (deg i))
    (hgen : Algebra.adjoin (gradeZero 𝒜) (Set.range f) = ⊤)
    (n : ℕ) :
    (𝒜 n : Set A) ⊆
      (Submodule.span (gradeZero 𝒜)
        {x : A | ∃ e : Fin r → ℕ, (∑ i, e i * deg i = n) ∧ x = ∏ i, f i ^ e i} : Set A) := by
  classical
  set S₀ := SetLike.GradeZero.subring 𝒜
  set Mon : Set A := {x : A | ∃ e : Fin r → ℕ, (∑ i, e i * deg i = n) ∧ x = ∏ i, f i ^ e i}
  have hmono : ∀ y ∈ Submonoid.closure (Set.range f), ∃ e : Fin r → ℕ, y = ∏ i, f i ^ e i := by
    intro y hy
    induction hy using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      refine ⟨Pi.single i 1, ?_⟩
      rw [Finset.prod_eq_single i]
      · rw [Pi.single_eq_same, pow_one]
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj, pow_zero]
      · exact fun h => (h (Finset.mem_univ i)).elim
    | one => exact ⟨0, by simp⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨ex, rfl⟩ := ihx
      obtain ⟨ey, rfl⟩ := ihy
      exact ⟨ex + ey, by simp [pow_add, Finset.prod_mul_distrib]⟩
  have hkey : ∀ y ∈ Submodule.span S₀ (Submonoid.closure (Set.range f) : Set A),
      (GradedRing.proj 𝒜 n) y ∈ Submodule.span S₀ Mon := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨e, rfl⟩ := hmono z hz
      have hzmem := prod_pow_mem_grade_sum 𝒜 f deg hdeg e
      by_cases hD : (∑ i, e i * deg i) = n
      · rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_same 𝒜 (hD ▸ hzmem)]
        exact Submodule.subset_span ⟨e, hD, rfl⟩
      · rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_ne 𝒜 hzmem hD]
        simp
    | zero => simp
    | add x y hx hy ihx ihy =>
      rw [map_add]
      exact Submodule.add_mem _ ihx ihy
    | smul a x hx ih =>
      rw [show (a • x : A) = (a : A) * x from rfl, GradedRing.proj_apply,
        DirectSum.coe_decompose_mul_of_left_mem_zero 𝒜 a.property, ← GradedRing.proj_apply,
        show (a : A) * GradedRing.proj 𝒜 n x = a • GradedRing.proj 𝒜 n x from rfl]
      exact Submodule.smul_mem _ a ih
  intro x hx
  have := hkey x (by rw [← Algebra.adjoin_eq_span, hgen]; trivial)
  rwa [GradedRing.proj_apply, DirectSum.decompose_of_mem_same 𝒜 hx] at this

/-- Step C (peeling, arithmetic core): if `m` is a positive common multiple of all
`deg i` and the exponent vector `e` has total degree `∑ e i * deg i = N * m` with
`N ≥ r ≥ 1`, then some coordinate `i` satisfies `e i * deg i ≥ m`.

STRATEGY: Pure `ℕ` pigeonhole. By contradiction, if `e i * deg i < m` (i.e. `≤ m-1`) for
all `i`, then `∑ e i * deg i ≤ r * (m-1) < r * m ≤ N * m`, contradicting `hsum`. Use
`Finset.sum_le_sum` / `Finset.sum_lt_sum_of_nonempty` and `Finset.card_fin`. (Equivalently
`Finset.exists_le_of_sum_le` after dividing.) -/
theorem exists_large_exponent
    {r : ℕ} (deg : Fin r → ℕ)
    (m : ℕ)
    (N : ℕ) (hN : r ≤ N) (hr : 1 ≤ r)
    (e : Fin r → ℕ) (hsum : ∑ i, e i * deg i = N * m) :
    ∃ i, m ≤ e i * deg i := by
  by_contra hcon
  push Not at hcon
  have hne : (Finset.univ : Finset (Fin r)).Nonempty := ⟨⟨0, hr⟩, Finset.mem_univ _⟩
  have hlt : ∑ i, e i * deg i < ∑ _i : Fin r, m :=
    Finset.sum_lt_sum_of_nonempty hne (fun i _ => hcon i)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, hsum] at hlt
  nlinarith [hN]

/-- Step D (degree-`(r*m)` monomial factorization): every monomial `∏ f_i^{e_i}` of
total degree `K * (r*m)` (with `K ≥ 1`, `m` a positive common multiple of the `deg i`)
is a `K`-fold product of degree-`(r*m)` elements of `𝒜 (r*m)`, i.e. lies in
`degOneProducts 𝒜 (r*m) K`. **The combinatorial heart of the Stacks proof.**

STRATEGY: Induction on `K`. Base `K = 1`: the monomial itself is a single factor of
degree `r*m` (homogeneous by Step E + graded mul, since `∑ e_i deg_i = r*m`), so it is in
`degOneProducts 𝒜 (r*m) 1`. Inductive step `K+1`: total degree `(K+1)*(r*m)`. Peel off a
degree-`(r*m)` block: apply Step C with `N := r` (note total degree `≥ r*m`) to find a
coordinate `i₁` with `e i₁ * deg i₁ ≥ m`, i.e. `e i₁ ≥ m / deg i₁`; extract the factor
`f i₁ ^ (m / deg i₁)` of degree exactly `m` (Step E + `(m/deg i)*deg i = m` from
`deg i ∣ m`). Repeating this `r` times peels `r` factors of total degree `r*m`; their
product is a single degree-`(r*m)` element of `𝒜 (r*m)`, and the remaining monomial has
degree `K*(r*m)`, handled by the induction hypothesis. Concatenate the one new factor with
the `K` factors from IH (`Fin.cons` / `degOneProducts` membership). -/
theorem monomial_isProduct_of_degM
    {r : ℕ} (f : Fin r → A) (deg : Fin r → ℕ)
    (hdeg : ∀ i, 1 ≤ deg i) (hfdeg : ∀ i, f i ∈ 𝒜 (deg i))
    (m : ℕ) (hdvd : ∀ i, deg i ∣ m) (hr : 1 ≤ r)
    (K : ℕ) (hK : 1 ≤ K)
    (e : Fin r → ℕ) (hsum : ∑ i, e i * deg i = K * (r * m)) :
    (∏ i, f i ^ e i) ∈ degOneProducts 𝒜 (r * m) K := by
  classical
  have inner_peel : ∀ (s : ℕ) (e₀ : Fin r → ℕ) (Nn : ℕ),
      r + s ≤ Nn → (∑ i, e₀ i * deg i = Nn * m) →
      ∃ (e'' : Fin r → ℕ) (c : A), c ∈ 𝒜 (s * m) ∧
        (∑ i, e'' i * deg i = (Nn - s) * m) ∧
        (∏ i, f i ^ e₀ i) = c * (∏ i, f i ^ e'' i) := by
    intro s
    induction s with
    | zero =>
      intro e₀ Nn _ hN0
      refine ⟨e₀, 1, ?_, ?_, ?_⟩
      · simpa using (SetLike.GradedOne.one_mem (A := 𝒜))
      · simpa using hN0
      · simp
    | succ s ih =>
      intro e₀ Nn hfeas hN0
      obtain ⟨i₀, hi₀⟩ := exists_large_exponent deg m Nn (by omega) hr e₀ hN0
      set q : ℕ := m / deg i₀
      have hqdeg : q * deg i₀ = m := Nat.div_mul_cancel (hdvd i₀)
      have hqle : q ≤ e₀ i₀ := Nat.le_of_mul_le_mul_right (by rwa [hqdeg]) (hdeg i₀)
      set e₁ : Fin r → ℕ := Function.update e₀ i₀ (e₀ i₀ - q) with he1
      have herase : ∀ i ∈ (Finset.univ.erase i₀), e₁ i = e₀ i := fun i hi => by
        rw [he1, Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      have he1i0 : e₁ i₀ = e₀ i₀ - q := by rw [he1, Function.update_self]
      have hsumrel : (∑ i, e₁ i * deg i) + m = ∑ i, e₀ i * deg i := by
        have hcong : ∑ i ∈ Finset.univ.erase i₀, e₁ i * deg i
            = ∑ i ∈ Finset.univ.erase i₀, e₀ i * deg i :=
          Finset.sum_congr rfl fun i hi => by rw [herase i hi]
        rw [← Finset.add_sum_erase Finset.univ (fun i => e₀ i * deg i) (Finset.mem_univ i₀),
          ← Finset.add_sum_erase Finset.univ (fun i => e₁ i * deg i) (Finset.mem_univ i₀),
          hcong, he1i0, Nat.sub_mul, hqdeg]
        omega
      have he1sum : ∑ i, e₁ i * deg i = (Nn - 1) * m := by
        have : m ≤ Nn * m := Nat.le_mul_of_pos_left m (by omega)
        rw [Nat.sub_one_mul]
        omega
      have hprodrel : (∏ i, f i ^ e₀ i) = f i₀ ^ q * (∏ i, f i ^ e₁ i) := by
        have hcong : ∏ i ∈ Finset.univ.erase i₀, f i ^ e₁ i
            = ∏ i ∈ Finset.univ.erase i₀, f i ^ e₀ i :=
          Finset.prod_congr rfl fun i hi => by rw [herase i hi]
        rw [← Finset.mul_prod_erase Finset.univ (fun i => f i ^ e₀ i) (Finset.mem_univ i₀),
          ← Finset.mul_prod_erase Finset.univ (fun i => f i ^ e₁ i) (Finset.mem_univ i₀),
          hcong, he1i0, ← mul_assoc, ← pow_add, Nat.add_sub_of_le hqle]
      obtain ⟨e'', c', hc', hsum'', hfact''⟩ := ih e₁ (Nn - 1) (by omega) he1sum
      refine ⟨e'', f i₀ ^ q * c', ?_, ?_, ?_⟩
      · have hfq := pow_mem_grade_mul 𝒜 (hfdeg i₀) q
        rw [hqdeg] at hfq
        have : f i₀ ^ q * c' ∈ 𝒜 (m + s * m) := SetLike.GradedMul.mul_mem hfq hc'
        rwa [show m + s * m = (s + 1) * m by ring] at this
      · rwa [show Nn - 1 - s = Nn - (s + 1) by omega] at hsum''
      · rw [hprodrel, hfact'', mul_assoc]
  induction K, hK using Nat.le_induction generalizing e with
  | base =>
    refine ⟨fun _ => ∏ i, f i ^ e i, fun _ => ?_, by simp⟩
    have := prod_pow_mem_grade_sum 𝒜 f deg hfdeg e
    rwa [hsum, one_mul] at this
  | succ K hKge ihK =>
    obtain ⟨e'', c, hc, hsum'', hfact''⟩ :=
      inner_peel r e ((K + 1) * r) (by nlinarith [hKge]) (by rw [hsum]; ring)
    rw [show (K + 1) * r - r = K * r by rw [add_one_mul, Nat.add_sub_cancel]] at hsum''
    obtain ⟨g'', hg''mem, hg''eq⟩ := ihK e'' (by rw [hsum'']; ring)
    refine ⟨Fin.cons c g'', fun j => ?_, ?_⟩
    · exact Fin.cases (by simpa using hc) (fun i => by simpa using hg''mem i) j
    · simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      rw [← hg''eq, hfact'']

/-- Step E (powers are homogeneous): `f i ^ k ∈ 𝒜 (k * deg i)`.

STRATEGY: Elementary induction on `k`. Base `k = 0`: `f i ^ 0 = 1 ∈ 𝒜 0` by
`SetLike.GradedOne.one_mem` (and `0 * deg i = 0`). Step: `f i ^ (k+1) = f i ^ k * f i`,
with `f i ^ k ∈ 𝒜 (k * deg i)` (IH) and `f i ∈ 𝒜 (deg i)`, so the product is in
`𝒜 (k * deg i + deg i) = 𝒜 ((k+1) * deg i)` by `SetLike.GradedMul.mul_mem` and
`Nat.succ_mul`. -/
theorem pow_mem_grade
    {r : ℕ} (f : Fin r → A) (deg : Fin r → ℕ)
    (hfdeg : ∀ i, f i ∈ 𝒜 (deg i)) (i : Fin r) (k : ℕ) :
    f i ^ k ∈ 𝒜 (k * deg i) := by
  exact pow_mem_grade_mul 𝒜 (hfdeg i) k

/-- Step F (reverse inclusion, always true): the `S_0`-span of `degOneProducts 𝒜 d n`
is contained in `𝒜 (n*d)`.

STRATEGY: `Submodule.span_le`: suffices each generator `x ∈ degOneProducts 𝒜 d n` lies in
the submodule `𝒜 (n*d)` viewed as an `S_0`-submodule. Write `x = ∏ i : Fin n, g i` with
`g i ∈ 𝒜 d`; then `x ∈ 𝒜 (n*d)` because the `n`-fold product of degree-`d` elements has
degree `n*d` — use the `veroneseGradedMonoid`/`SetLike.GradedMonoid` structure, e.g.
`SetLike.prod_mem_graded` / fold `GradedMul.mul_mem` over `Finset.univ`, giving degree
`∑ i, d = n*d`. The `S_0 = 𝒜 0`-submodule property holds because `𝒜 0 • 𝒜 (n*d) ⊆ 𝒜 (n*d)`
(graded mul with degree 0); `𝒜 (n*d)` is already a `gradeZero`-submodule. -/
theorem span_degOneProducts_subset (d n : ℕ) :
    (Submodule.span (gradeZero 𝒜) (degOneProducts 𝒜 d n) : Set A) ⊆ (𝒜 (n * d) : Set A) := by
  intro x hx
  rw [SetLike.mem_coe] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨g, hg, rfl⟩ := hz
    have hprod : (∏ i, g i) ∈ 𝒜 (∑ _i : Fin n, d) :=
      SetLike.prod_mem_graded 𝒜 (fun _ => d) g fun i _ => hg i
    rwa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hprod
  | zero => exact zero_mem _
  | add y z _ _ hy hz => exact add_mem hy hz
  | smul a y _ hy =>
    have : (a • y : A) ∈ 𝒜 (0 + n * d) := SetLike.mul_mem_graded a.property hy
    rwa [zero_add] at this

/-- Step G (forward inclusion at `d = r*m`): combine Steps B and D.

STRATEGY: Given `n ≥ 1`. By Step B (`mem_span_monomials` with `n := n*(r*m)`),
`𝒜 (n*(r*m)) ⊆ span S_0 {monomials ∏ f_i^{e_i} of degree n*(r*m)}`. It suffices to show
that set of monomials is contained in `degOneProducts 𝒜 (r*m) n` (then `span_mono` +
`span` of a subset). Each such monomial has `∑ e_i deg_i = n*(r*m) = n*(r*m)`, so by Step D
(`monomial_isProduct_of_degM` with `K := n`, `K ≥ 1`) it lies in `degOneProducts 𝒜 (r*m) n`.
Chain the inclusions with `Set.Subset.trans` / `Submodule.span_mono`. -/
theorem grade_subset_span_degOneProducts
    {r : ℕ} (f : Fin r → A) (deg : Fin r → ℕ)
    (hdeg : ∀ i, 1 ≤ deg i) (hfdeg : ∀ i, f i ∈ 𝒜 (deg i))
    (hgen : Algebra.adjoin (gradeZero 𝒜) (Set.range f) = ⊤)
    (m : ℕ) (hdvd : ∀ i, deg i ∣ m) (hr : 1 ≤ r)
    (n : ℕ) (hn : 1 ≤ n) :
    (𝒜 (n * (r * m)) : Set A) ⊆
      (Submodule.span (gradeZero 𝒜) (degOneProducts 𝒜 (r * m) n) : Set A) := by
  refine (mem_span_monomials 𝒜 f deg hfdeg hgen _).trans (Submodule.span_mono ?_)
  rintro x ⟨e, hsum, rfl⟩
  exact monomial_isProduct_of_degM 𝒜 f deg hdeg hfdeg m hdvd hr n hn e hsum

/-- Step H (per-`d` conclusion): for any positive `d` that is a multiple of `r*L`
(where `L` is a positive common multiple of the `deg i`), `S^(d)` is generated in
degree `1`.

STRATEGY: Unfold `VeroneseGeneratedInDegOne`: fix `n ≥ 1`, show
`𝒜 (n*d) = span S_0 (degOneProducts 𝒜 d n)` by `Set.Subset.antisymm`. Write `d = (r*L)*t`
from `hdvd`, set `m := L*t`; then `m ≥ 1` (positivity of `L`,`t`), `deg i ∣ m` (since
`deg i ∣ L ∣ m`), and `r*m = r*(L*t) = (r*L)*t = d`. Rewrite `d` as `r*m` everywhere.
- ⊆ : Step G `grade_subset_span_degOneProducts` (with this `m`, `n`).
- ⊇ : Step F `span_degOneProducts_subset` (always true).
Note `t ≥ 1` because `d ≥ 1` and `d = (r*L)*t`. -/
@[ega "II 2.1.6"]
theorem veroneseGeneratedInDegOne_of_multiple
    {r : ℕ} (f : Fin r → A) (deg : Fin r → ℕ)
    (hdeg : ∀ i, 1 ≤ deg i) (hfdeg : ∀ i, f i ∈ 𝒜 (deg i))
    (hgen : Algebra.adjoin (gradeZero 𝒜) (Set.range f) = ⊤)
    (L : ℕ) (hLdvd : ∀ i, deg i ∣ L) (hr : 1 ≤ r)
    (d : ℕ) (hd : 1 ≤ d) (hdvd : (r * L) ∣ d) :
    VeroneseGeneratedInDegOne 𝒜 d := by
  obtain ⟨t, ht⟩ := hdvd
  have htpos : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h0 | h1
    · subst h0; simp at ht; omega
    · exact h1
  set m : ℕ := L * t with hm_def
  have hdivm : ∀ i, deg i ∣ m := fun i => (hLdvd i).mul_right t
  have hrm : r * m = d := by
    rw [hm_def, ht]
    ring
  intro n hn
  apply Set.Subset.antisymm
  · -- ⊆ : 𝒜 (n*d) ⊆ span (degOneProducts 𝒜 d n)
    have hG := grade_subset_span_degOneProducts 𝒜 f deg hdeg hfdeg hgen m hdivm hr n hn
    rwa [hrm] at hG
  · -- ⊇ : span (degOneProducts 𝒜 d n) ⊆ 𝒜 (n*d)
    exact span_degOneProducts_subset 𝒜 d n

/-- Degenerate case `r = 0` (i.e. `A = S_0`): the algebra is generated by the empty
set, so `A = 𝒜 0`. Witness `d₀ = 1`.

STRATEGY: `Algebra.adjoin S_0 ∅ = ⊥` and `= ⊤` (hgen) forces `(⊤ : Subalgebra) = ⊥`, so
every element of `A` is in `S_0 = 𝒜 0` (via `Algebra.adjoin_empty`/`Subalgebra.eq_bot_iff`
or `mem_bot`). Then for `n ≥ 1`: any `x ∈ 𝒜 (n*d)` is also in `𝒜 0`; by uniqueness of the
graded decomposition (`DirectSum.Decomposition`, `n*d ≠ 0` since `n,d ≥ 1`), an element in
both `𝒜 0` and `𝒜 (n*d)` is `0` (`DirectSum.decompose_of_mem` disjointness /
`GradedRing.proj` orthogonality). So `𝒜 (n*d) = {0}`, and the span side `degOneProducts`
also spans only `0` (or just show both sides equal `{0}`). Equality follows. -/
theorem veroneseGeneratedInDegOne_of_trivial
    (hgen : Algebra.adjoin (gradeZero 𝒜) (∅ : Set A) = ⊤)
    (d : ℕ) (hd : 1 ≤ d) :
    VeroneseGeneratedInDegOne 𝒜 d := by
  classical
  -- Step 1: every element of A lies in 𝒜 0.
  have hA0 : ∀ x : A, x ∈ 𝒜 0 := by
    intro x
    have hxtop : x ∈ (⊤ : Subalgebra (gradeZero 𝒜) A) := Algebra.mem_top
    rw [← hgen, Algebra.adjoin_empty, Algebra.mem_bot] at hxtop
    obtain ⟨y, rfl⟩ := hxtop
    exact y.property
  -- Step 2: orthogonality: an element of 𝒜 m with m ≠ 0 is zero.
  have hzero : ∀ (m : ℕ), m ≠ 0 → ∀ x ∈ 𝒜 m, x = 0 := by
    intro m hm x hx
    have := DirectSum.decompose_of_mem_ne 𝒜 (hA0 x) (Ne.symm hm)
    rwa [DirectSum.decompose_of_mem_same 𝒜 hx] at this
  intro n hn
  have hnd : n * d ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  -- Both sides equal {0}.
  have hLHS : (𝒜 (n * d) : Set A) = {(0 : A)} :=
    Set.eq_singleton_iff_unique_mem.mpr ⟨zero_mem (𝒜 (n * d)), fun x hx => hzero _ hnd x hx⟩
  have hRHS : (Submodule.span (gradeZero 𝒜) (degOneProducts 𝒜 d n) : Set A) = {(0 : A)} := by
    have hbot : Submodule.span (gradeZero 𝒜) (degOneProducts 𝒜 d n) = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro x ⟨g, hg, rfl⟩
      have hg0 : g ⟨0, by omega⟩ = 0 := hzero d (by omega) _ (hg _)
      exact Finset.prod_eq_zero (Finset.mem_univ (⟨0, by omega⟩ : Fin n)) hg0
    rw [hbot, Submodule.bot_coe]
  rw [hLHS, hRHS]

/-- **Theorem (Stacks Tag 0EGH, Lemma 10.56.2).** Let `S` be a graded ring that is
finitely generated over `S_0`. Then for all sufficiently divisible `d` the
algebra `S^{(d)}` is generated in degree `1` over `S_0`: there is a `d₀ ≥ 1` such
that for every positive multiple `d` of `d₀` and every `n ≥ 1`, the `S_0`-module
`S_{nd}` equals the `S_0`-span of the `n`-fold products of elements of `S_d`.

ASSEMBLY:
1. Get homogeneous positive-degree generators (Step A `homogeneous_generators_of_finiteType`).
2. Case split on `r = 0` (degenerate, use `veroneseGeneratedInDegOne_of_trivial`,
   witness `d₀ = 1`; `Set.range f = ∅` since `Fin 0` is empty) vs `r ≥ 1`.
3. For `r ≥ 1`: set `L := ∏ i, deg i` (positive common multiple of each `deg i`:
   `1 ≤ L` by `Finset.prod_pos`; `deg i ∣ L` by `Finset.dvd_prod_of_mem`), witness
   `d₀ := r * L ≥ 1`, and discharge each positive multiple via Step H
   (`veroneseGeneratedInDegOne_of_multiple`). -/
@[stacks 0EGH, ega "II 3.1.10" "affine case", ega "II 2.1.6"]
theorem veronese_generated_in_deg_one_of_finiteType
    (h : FinitelyGeneratedOverGradeZero 𝒜) :
    ForAllSufficientlyDivisible (fun d => VeroneseGeneratedInDegOne 𝒜 d) := by
  obtain ⟨r, f, deg, hdeg, hfdeg, hgen⟩ := homogeneous_generators_of_finiteType 𝒜 h
  obtain rfl | hr := Nat.eq_zero_or_pos r
  · refine ⟨1, le_rfl, fun d hd _ => ?_⟩
    rw [Set.range_eq_empty f] at hgen
    exact veroneseGeneratedInDegOne_of_trivial 𝒜 hgen d hd
  · exact ⟨r * ∏ i, deg i, Nat.mul_pos hr (Finset.prod_pos fun i _ => hdeg i),
      veroneseGeneratedInDegOne_of_multiple 𝒜 f deg hdeg hfdeg hgen _
        (fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) hr⟩

end Stacks.Veronese
