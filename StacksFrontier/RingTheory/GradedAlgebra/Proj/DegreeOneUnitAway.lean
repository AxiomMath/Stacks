module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.RingTheory.Flat.Basic
public import StacksFrontier.AlgebraicGeometry.GradedLocalization.ModuleMaps

/-!
# Localizing at a product whose factors have consecutive degrees

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring and let `c ∈ 𝒜 (m + 1)` and `b ∈ 𝒜 m` be homogeneous
of consecutive degrees. In the localization `A[1/cb]` both `c` and `b` become units, so

`u = c² / (cb)`

is a unit of `A[1/cb]` of degree `2(m + 1) - (2m + 1) = 1`, with inverse `b² / (cb)`. A unit of
degree one makes the localization a Laurent extension of its degree-zero part: the integer powers
`uʲ` form a basis of `A[1/cb]` over `A₍cb₎ = HomogeneousLocalization.Away 𝒜 (cb)`, and the same
holds for a graded module, `M[1/cb]` being the base change of its degree-zero part `M₍cb₎` along
`A₍cb₎ → A[1/cb]`.

On the punctured affine cone over a projective scheme `P = Proj(A)` this is the statement that the
cone is, over the chart `D₊(cb)`, the trivial `𝐆ₘ`-torsor `Spec A₍cb₎[u, u⁻¹]`: it is what makes
the cone a smooth morphism of relative dimension one onto `P` near every point at which a section
of degree `m + 1` and one of degree `m` both fail to vanish.

## Main definitions

* `Stacks.DegreeOneUnitAway.chartUnit`: the unit `u = c² / (cb)`.
* `Stacks.DegreeOneUnitAway.basisChartUnit`: the basis `j ↦ uʲ` of `A[1/cb]` over `A₍cb₎`.

## Main results

* `Stacks.DegreeOneUnitAway.mk_eq_chartUnit_zpow_mul`: a fraction `x / (cb)ᵏ` with `x` of degree
  `e` is `u^(e - k(2m+1))` times a degree-zero fraction.
* `Stacks.DegreeOneUnitAway.linearIndependent_chartUnit_zpow`: the powers of `u` are linearly
  independent over `A₍cb₎`.
* `Stacks.DegreeOneUnitAway.free_away` and `Stacks.DegreeOneUnitAway.flat_away`: `A[1/cb]` is free,
  hence flat, over `A₍cb₎`.

## Implementation notes

The argument is the one of `Stacks.GradedLaurent.laurentAwayEquiv`, which treats a localization at
an element of degree one; here the element inverted has degree `2m + 1`, and the role of its
powers is taken by the powers of `u`. Linear independence is reduced to the directness of the
grading of `A`: clearing denominators in a relation `∑ zⱼ uʲ = 0` leaves a relation among
homogeneous elements of `A` of pairwise distinct degrees, the degree of the `j`-th term being `j`
plus a constant.
-/

@[expose] public noncomputable section

namespace Stacks.DegreeOneUnitAway

open HomogeneousLocalization

universe u v

variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-! ### The unit of degree one -/

/-- The element `g` of the submonoid of its powers. -/
def gen (g : A) : Submonoid.powers g := ⟨g, 1, pow_one _⟩

/-- **The unit `u = c² / (cb)` of `A[1/cb]`**, with inverse `b² / (cb)`. -/
def chartUnit {c b g : A} (hcb : c * b = g) : (Localization.Away g)ˣ where
  val := Localization.mk (c ^ 2) (gen g)
  inv := Localization.mk (b ^ 2) (gen g)
  val_inv := by
    subst hcb
    rw [Localization.mk_mul, ← Localization.mk_one, Localization.mk_eq_mk_iff,
      Localization.r_iff_exists]
    exact ⟨1, by simp [gen]; ring⟩
  inv_val := by
    subst hcb
    rw [Localization.mk_mul, ← Localization.mk_one, Localization.mk_eq_mk_iff,
      Localization.r_iff_exists]
    exact ⟨1, by simp [gen]; ring⟩

/-- The unit `chartUnit hcb` is the fraction `c² / g`. -/
theorem coe_chartUnit {c b g : A} (hcb : c * b = g) :
    (chartUnit hcb : Localization.Away g) = Localization.mk (c ^ 2) (gen g) := rfl

/-- The inverse of `chartUnit hcb` is the fraction `b² / g`. -/
theorem coe_chartUnit_inv {c b g : A} (hcb : c * b = g) :
    ((chartUnit hcb)⁻¹ : (Localization.Away g)ˣ).val =
      Localization.mk (b ^ 2) (gen g) := rfl

/-- The `n`-th power of the denominator `g`, as an element of the submonoid of its powers. -/
def genPow (g : A) (n : ℕ) : Submonoid.powers g := ⟨g ^ n, n, rfl⟩

/-- The `n`-th power of `gen g` is `genPow g n`. -/
theorem gen_pow (g : A) (n : ℕ) : gen g ^ n = genPow g n := by
  apply Subtype.ext
  simp [gen, genPow]

/-- A nonnegative power of `u`, as a single fraction. -/
theorem coe_chartUnit_zpow_natCast {c b g : A} (hcb : c * b = g) (n : ℕ) :
    ((chartUnit hcb ^ (n : ℤ) : (Localization.Away g)ˣ) : Localization.Away g) =
      Localization.mk (c ^ (2 * n)) (genPow g n) := by
  subst hcb
  rw [zpow_natCast, Units.val_pow_eq_pow_val, coe_chartUnit, Localization.mk_pow, gen_pow,
    ← pow_mul]

/-- A finite set of integers is bounded below by `-N` for some natural number `N`. -/
private theorem exists_nat_add_nonneg (s : Finset ℤ) : ∃ N : ℕ, ∀ j ∈ s, (0 : ℤ) ≤ j + N :=
  ⟨s.sup fun j => (-j).toNat, fun j hj => by
    have h1 : ((-j).toNat : ℤ) ≤ (s.sup fun j => (-j).toNat : ℕ) :=
      Int.ofNat_le.mpr (Finset.le_sup (f := fun j : ℤ => (-j).toNat) hj)
    omega⟩

/-- `u ^ N * u ^ j` as a single fraction, when `N + j = a` is a natural number. -/
private theorem chartUnit_zpow_natCast_mul_zpow {c b g : A} (hcb : c * b = g) (N a : ℕ) (j : ℤ)
    (h : (N : ℤ) + j = a) :
    ((chartUnit hcb ^ (N : ℤ) : (Localization.Away g)ˣ) : Localization.Away g) *
      ((chartUnit hcb ^ j : (Localization.Away g)ˣ) : Localization.Away g) =
        Localization.mk (c ^ (2 * a)) (genPow g a) := by
  rw [← Units.val_mul, ← zpow_add, h, coe_chartUnit_zpow_natCast hcb]

/-- A nonpositive power of `u`, as a single fraction. -/
theorem coe_chartUnit_zpow_neg_natCast {c b g : A} (hcb : c * b = g) (n : ℕ) :
    ((chartUnit hcb ^ (-(n : ℤ)) : (Localization.Away g)ˣ) : Localization.Away g) =
      Localization.mk (b ^ (2 * n)) (genPow g n) := by
  subst hcb
  rw [zpow_neg, ← inv_zpow, zpow_natCast, Units.val_pow_eq_pow_val, coe_chartUnit_inv,
    Localization.mk_pow, gen_pow, ← pow_mul]

variable {𝒜} {c b g : A} {m : ℕ}

/-- The degree of `cb`. -/
theorem mul_mem (hc : c ∈ 𝒜 (m + 1)) (hb : b ∈ 𝒜 m) (hcb : c * b = g) :
    g ∈ 𝒜 (2 * m + 1) := by
  subst hcb
  have h := SetLike.mul_mem_graded hc hb
  rwa [show m + 1 + m = 2 * m + 1 by ring] at h

/-! ### Every fraction is a power of `u` times a degree-zero fraction -/

/-- **A fraction `x / (cb)ᵏ` with `x` homogeneous of degree `e` is `uʲ` times a degree-zero
fraction**, for `j = e - k(2m + 1)`. -/
theorem exists_mk_eq_chartUnit_zpow_mul (hc : c ∈ 𝒜 (m + 1)) (hb : b ∈ 𝒜 m) (hcb : c * b = g)
    {e : ℕ} {x : A} (hx : x ∈ 𝒜 e) (k : ℕ) :
    ∃ z : Away 𝒜 g,
      Localization.mk x (genPow g k) =
        ((chartUnit hcb ^ ((e : ℤ) - k * (2 * m + 1)) : (Localization.Away g)ˣ) :
          Localization.Away g) * z.val := by
  subst hcb
  have hg := mul_mem hc hb rfl
  rcases le_or_gt ((k : ℤ) * (2 * m + 1)) (e : ℤ) with hle | hlt
  · -- `j = n ≥ 0`: divide by `uⁿ`, that is multiply by `b²ⁿ / (cb)ⁿ`
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (e : ℤ) - k * (2 * m + 1) = n :=
      ⟨((e : ℤ) - k * (2 * m + 1)).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    have hdeg : b ^ (2 * n) * x ∈ 𝒜 ((n + k) • (2 * m + 1)) := by
      have h := SetLike.mul_mem_graded (SetLike.pow_mem_graded (2 * n) hb) hx
      convert h using 2
      simp only [smul_eq_mul]
      have : (e : ℤ) = n + k * (2 * m + 1) := by omega
      have he : e = n + k * (2 * m + 1) := by exact_mod_cast this
      rw [he]
      ring
    refine ⟨Away.mk 𝒜 hg (n + k) (b ^ (2 * n) * x) hdeg, ?_⟩
    rw [hn, Away.val_mk, coe_chartUnit_zpow_natCast, Localization.mk_mul,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [genPow, Submonoid.coe_mul, OneMemClass.coe_one, one_mul]
    ring
  · -- `j = -n < 0`: multiply by `uⁿ = c²ⁿ / (cb)ⁿ`
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (e : ℤ) - k * (2 * m + 1) = -(n : ℤ) :=
      ⟨((k : ℤ) * (2 * m + 1) - e).toNat, by rw [Int.toNat_of_nonneg (by omega)]; ring⟩
    have hdeg : c ^ (2 * n) * x ∈ 𝒜 ((n + k) • (2 * m + 1)) := by
      have h := SetLike.mul_mem_graded (SetLike.pow_mem_graded (2 * n) hc) hx
      convert h using 2
      simp only [smul_eq_mul]
      have : (e : ℤ) + n = k * (2 * m + 1) := by omega
      have he : e + n = k * (2 * m + 1) := by exact_mod_cast this
      nlinarith [he]
    refine ⟨Away.mk 𝒜 hg (n + k) (c ^ (2 * n) * x) hdeg, ?_⟩
    rw [hn, Away.val_mk, coe_chartUnit_zpow_neg_natCast, Localization.mk_mul,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [genPow, Submonoid.coe_mul, OneMemClass.coe_one, one_mul]
    ring


/-! ### The Laurent basis of the localization -/

/-- The action of the degree-zero localization on the full localization is multiplication by the
value of the fraction. -/
theorem away_smul_eq_val_mul {g : A} (z : Away 𝒜 g) (y : Localization.Away g) :
    z • y = z.val * y := rfl

/-- **The powers of `u` span `A[1/cb]` over `A₍cb₎`.** -/
theorem span_chartUnit_zpow_eq_top (hc : c ∈ 𝒜 (m + 1)) (hb : b ∈ 𝒜 m) (hcb : c * b = g) :
    Submodule.span (Away 𝒜 g) (Set.range fun j : ℤ =>
      ((chartUnit hcb ^ j : (Localization.Away g)ˣ) : Localization.Away g)) = ⊤ := by
  subst hcb
  classical
  rw [eq_top_iff]
  intro y _
  induction y using Localization.induction_on with
  | H y =>
    obtain ⟨x, s⟩ := y
    obtain ⟨k, hk⟩ := s.2
    have hs : s = genPow (c * b) k := Subtype.ext hk.symm
    subst hs
    rw [← DirectSum.sum_support_decompose 𝒜 x]
    rw [Localization.mk_sum]
    refine Submodule.sum_mem _ fun e _ => ?_
    obtain ⟨z, heq⟩ := exists_mk_eq_chartUnit_zpow_mul hc hb rfl (DirectSum.decompose 𝒜 x e).2 k
    rw [heq]
    have hcomm : ((chartUnit (rfl : c * b = c * b) ^ ((e : ℤ) - k * (2 * m + 1)) :
        (Localization.Away (c * b))ˣ) : Localization.Away (c * b)) * z.val =
        z • ((chartUnit (rfl : c * b = c * b) ^ ((e : ℤ) - k * (2 * m + 1)) :
          (Localization.Away (c * b))ˣ) : Localization.Away (c * b)) :=
      (mul_comm _ _).trans (away_smul_eq_val_mul _ _).symm
    rw [hcomm]
    exact Submodule.smul_mem _ z (Submodule.subset_span ⟨_, rfl⟩)

/-- A finite sum of homogeneous elements of `A` of pairwise distinct degrees vanishes only if every
summand vanishes. -/
theorem eq_zero_of_sum_eq_zero_of_injOn_ring {ι : Type*} {s : Finset ι} {deg : ι → ℕ}
    (hdeg : Set.InjOn deg s) {w : ι → A} (hw : ∀ n ∈ s, w n ∈ 𝒜 (deg n))
    (h : ∑ n ∈ s, w n = 0) {n₀ : ι} (hn₀ : n₀ ∈ s) : w n₀ = 0 := by
  classical
  have key : (DirectSum.decompose 𝒜 (∑ n ∈ s, w n) (deg n₀) : A) = w n₀ := by
    rw [DirectSum.decompose_sum, DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum]
    refine (Finset.sum_eq_single_of_mem n₀ hn₀ fun b hb hne => ?_).trans ?_
    · exact DirectSum.decompose_of_mem_ne 𝒜 (hw b hb) fun hcon => hne (hdeg hb hn₀ hcon)
    · exact DirectSum.decompose_of_mem_same 𝒜 (hw n₀ hn₀)
  rw [h, DirectSum.decompose_zero] at key
  exact key.symm

/-- **The powers of `u` are linearly independent over `A₍cb₎`.** -/
theorem linearIndependent_chartUnit_zpow (hc : c ∈ 𝒜 (m + 1)) (hb : b ∈ 𝒜 m) (hcb : c * b = g) :
    LinearIndependent (Away 𝒜 g) (fun j : ℤ =>
      ((chartUnit hcb ^ j : (Localization.Away g)ˣ) : Localization.Away g)) := by
  subst hcb
  classical
  have hg := mul_mem hc hb rfl
  rw [linearIndependent_iff']
  intro s z h j₀ hj₀
  choose n x hx hzx using fun j => HomogeneousLocalization.Away.mk_surjective 𝒜 hg (z j)
  obtain ⟨N, hjN⟩ := exists_nat_add_nonneg s
  set a : ℤ → ℕ := fun j => (j + N).toNat with hadef
  have ha : ∀ j ∈ s, (a j : ℤ) = j + N := fun j hj => Int.toNat_of_nonneg (hjN j hj)
  set J : ℕ := s.sup n with hJ
  set K : ℕ := s.sup a with hK
  have hnJ : ∀ j ∈ s, n j ≤ J := fun j hj => Finset.le_sup hj
  have haK : ∀ j ∈ s, a j ≤ K := fun j hj => Finset.le_sup hj
  set w : ℤ → A := fun j => (c * b) ^ ((J - n j) + (K - a j)) * c ^ (2 * a j) * x j with hw
  set t : Localization.Away (c * b) :=
    algebraMap A (Localization.Away (c * b)) ((c * b) ^ (J + K)) *
      ((chartUnit (rfl : c * b = c * b) ^ (N : ℤ) : (Localization.Away (c * b))ˣ) :
        Localization.Away (c * b))
    with ht
  have hterm : ∀ j ∈ s, t * (z j • ((chartUnit (rfl : c * b = c * b) ^ j :
      (Localization.Away (c * b))ˣ) : Localization.Away (c * b))) =
      algebraMap A (Localization.Away (c * b)) (w j) := by
    intro j hj
    have hu := chartUnit_zpow_natCast_mul_zpow (rfl : c * b = c * b) N (a j) j
      (by rw [ha j hj]; ring)
    rw [away_smul_eq_val_mul, ← hzx j, HomogeneousLocalization.Away.val_mk, ht,
      show ∀ p q r v : Localization.Away (c * b), p * q * (r * v) = p * (q * v) * r by
        intros; ring, hu, ← Localization.mk_one_eq_algebraMap, ← Localization.mk_one_eq_algebraMap,
      Localization.mk_mul, Localization.mk_mul, Localization.mk_eq_mk_iff,
      Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [genPow, Submonoid.coe_mul, OneMemClass.coe_one, one_mul, hw]
    have e1 : J = n j + (J - n j) := (Nat.add_sub_cancel' (hnJ j hj)).symm
    have e2 : K = a j + (K - a j) := (Nat.add_sub_cancel' (haK j hj)).symm
    conv_lhs => rw [e1, e2]
    ring
  have hsum : algebraMap A (Localization.Away (c * b)) (∑ j ∈ s, w j) = 0 := by
    rw [map_sum, ← Finset.sum_congr rfl hterm, ← Finset.mul_sum, h, mul_zero]
  rw [IsLocalization.map_eq_zero_iff (Submonoid.powers (c * b))] at hsum
  obtain ⟨⟨_, p, rfl⟩, hp⟩ := hsum
  rw [Finset.mul_sum] at hp
  have hdeg : ∀ j ∈ s, (c * b) ^ p * w j ∈ 𝒜 ((p + J + K) * (2 * m + 1) + a j) := by
    intro j hj
    have hmem := SetLike.mul_mem_graded (SetLike.pow_mem_graded p hg)
      (SetLike.mul_mem_graded (SetLike.mul_mem_graded
        (SetLike.pow_mem_graded ((J - n j) + (K - a j)) hg)
        (SetLike.pow_mem_graded (2 * a j) hc)) (hx j))
    convert hmem using 2
    simp only [smul_eq_mul]
    have e1 := hnJ j hj
    have e2 := haK j hj
    zify [e1, e2]
    ring
  have hinj : Set.InjOn (fun j => (p + J + K) * (2 * m + 1) + a j) s := by
    intro j hj j' hj' hjj
    simp only at hjj
    have := ha j hj
    have := ha j' hj'
    omega
  have hvan := eq_zero_of_sum_eq_zero_of_injOn_ring hinj hdeg hp hj₀
  rw [← hzx j₀]
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero,
    ← Localization.mk_zero (genPow (c * b) (n j₀)), Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨⟨(c * b) ^ (p + (J - n j₀) + (K - a j₀) + 2 * a j₀), _, rfl⟩, ?_⟩
  have := congrArg (fun y => (c * b) ^ n j₀ * (b ^ (2 * a j₀) * y)) hvan
  simp only [hw, mul_zero] at this
  simp only [genPow, mul_zero]
  rw [← this]
  rw [pow_add, pow_add, pow_add, mul_pow c b (2 * a j₀)]
  ring

/-- **The basis `j ↦ uʲ` of `A[1/cb]` over `A₍cb₎`.** -/
def basisChartUnit (hc : c ∈ 𝒜 (m + 1)) (hb : b ∈ 𝒜 m) (hcb : c * b = g) :
    Module.Basis ℤ (Away 𝒜 g) (Localization.Away g) :=
  Module.Basis.mk (linearIndependent_chartUnit_zpow hc hb hcb)
    (by rw [span_chartUnit_zpow_eq_top hc hb hcb])

/-- The `j`-th vector of `basisChartUnit` is `uʲ`. -/
theorem basisChartUnit_apply (hc : c ∈ 𝒜 (m + 1)) (hb : b ∈ 𝒜 m) (hcb : c * b = g) (j : ℤ) :
    basisChartUnit hc hb hcb j =
      ((chartUnit hcb ^ j : (Localization.Away g)ˣ) : Localization.Away g) := by
  subst hcb
  rw [basisChartUnit, Module.Basis.mk_apply]

/-- `A[1/cb]` is free over `A₍cb₎`. -/
theorem free_away (hc : c ∈ 𝒜 (m + 1)) (hb : b ∈ 𝒜 m) (hcb : c * b = g) :
    Module.Free (Away 𝒜 g) (Localization.Away g) :=
  Module.Free.of_basis (basisChartUnit hc hb hcb)

/-- `A[1/cb]` is flat over `A₍cb₎`. -/
theorem flat_away (hc : c ∈ 𝒜 (m + 1)) (hb : b ∈ 𝒜 m) (hcb : c * b = g) :
    Module.Flat (Away 𝒜 g) (Localization.Away g) :=
  have := free_away hc hb hcb
  inferInstance

/-! ### Graded modules -/

section Module

open Stacks.GradedLocalization

variable {M : Type v} [AddCommGroup M] [Module A M] {τ : Type*} [SetLike τ M]
  [AddSubgroupClass τ M] (𝓜 : ℤ → τ) [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul 𝒜 𝓜]

omit [AddSubgroupClass σ A] [GradedRing 𝒜] [AddSubgroupClass τ M] [DirectSum.Decomposition 𝓜] in
/-- The scalar action of a homogeneous element of the ring on a homogeneous element of the module,
with the degree of the product named by an equation. -/
theorem smul_mem_of_eq {i : ℕ} {j n : ℤ} {a : A} {x : M} (ha : a ∈ 𝒜 i) (hx : x ∈ 𝓜 j)
    (h : n = (i : ℤ) + j) : a • x ∈ 𝓜 n := by
  subst h
  exact SetLike.GradedSMul.smul_mem (A := 𝒜) (B := 𝓜) ha hx

/-- A finite sum of homogeneous elements of a graded module of pairwise distinct degrees vanishes
only if every summand vanishes. -/
theorem eq_zero_of_sum_eq_zero_of_injOn {ι : Type*} {s : Finset ι} {deg : ι → ℤ}
    (hdeg : Set.InjOn deg s) {w : ι → M} (hw : ∀ n ∈ s, w n ∈ 𝓜 (deg n))
    (h : ∑ n ∈ s, w n = 0) {n₀ : ι} (hn₀ : n₀ ∈ s) : w n₀ = 0 := by
  classical
  have key : (DirectSum.decompose 𝓜 (∑ n ∈ s, w n) (deg n₀) : M) = w n₀ := by
    rw [DirectSum.decompose_sum, DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum]
    refine (Finset.sum_eq_single_of_mem n₀ hn₀ fun b hb hne => ?_).trans ?_
    · exact DirectSum.decompose_of_mem_ne 𝓜 (hw b hb) fun hcon => hne (hdeg hb hn₀ hcon)
    · exact DirectSum.decompose_of_mem_same 𝓜 (hw n₀ hn₀)
  rw [h, DirectSum.decompose_zero] at key
  exact key.symm

variable {𝓜}

/-- `M[1/g]` as a module over `A₍g₎`, through the algebra map `A₍g₎ → A[1/g]`. -/
local instance moduleAway (g : A) : Module (Away 𝒜 g) (LocalizedModule.Away (R := A) g M) :=
  Module.compHom (R := Localization.Away g) (LocalizedModule.Away (R := A) g M)
    (algebraMap (Away 𝒜 g) (Localization.Away g))

omit [DirectSum.Decomposition 𝓜] in
/-- The action of the degree-zero localization on the localized module is the action of the
value of the fraction. -/
theorem away_smul_eq (g : A) (z : Away 𝒜 g) (y : LocalizedModule.Away (R := A) g M) :
    z • y = z.val • y := rfl

/-- **The degree-zero part consists of single fractions.** An element of `M₍g₎` is a fraction
`x / gⁿ` with `x` of degree `n • deg g`. -/
theorem exists_eq_mk_of_mem {g : A} {d : ℕ} (hg : g ∈ 𝒜 d) {y : LocalizedModule.Away (R := A) g M}
    (hy : y ∈ GradedModuleDegreeZeroLocalization 𝒜 𝓜 g) :
    ∃ (n : ℕ) (x : M), x ∈ 𝓜 (n • (d : ℤ)) ∧ y = LocalizedModule.mk x (genPow g n) := by
  classical
  induction hy using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨d', n, hg', x, hx, rfl⟩ := hy
      by_cases hgn : g ^ n = 0
      · have : Subsingleton (LocalizedModule.Away (R := A) g M) :=
          LocalizedModule.subsingleton (S := Submonoid.powers g) (M := M) (by
            rw [← hgn]; exact ⟨n, rfl⟩)
        exact ⟨0, 0, by simp, Subsingleton.elim _ _⟩
      · have hdeg : n • d' = n • d :=
          DirectSum.degree_eq_of_mem_mem 𝒜
            (SetLike.pow_mem_graded n hg') (SetLike.pow_mem_graded n hg) hgn
        have hdeg' : n • (d' : ℤ) = n • (d : ℤ) := by
          simpa [nsmul_eq_mul] using congrArg (fun k : ℕ => (k : ℤ)) hdeg
        exact ⟨n, x, hdeg' ▸ hx, rfl⟩
  | zero => exact ⟨0, 0, by simp, by simp⟩
  | add y z _ _ hy hz =>
      obtain ⟨n, x, hx, rfl⟩ := hy
      obtain ⟨l, z, hz, rfl⟩ := hz
      refine ⟨n + l, (g ^ l) • x + (g ^ n) • z, add_mem ?_ ?_, ?_⟩
      · exact smul_mem_of_eq 𝓜 (SetLike.pow_mem_graded l hg) hx (by
          simp only [nsmul_eq_mul, smul_eq_mul]
          push_cast
          ring)
      · exact smul_mem_of_eq 𝓜 (SetLike.pow_mem_graded n hg) hz (by
          simp only [nsmul_eq_mul, smul_eq_mul]
          push_cast
          ring)
      · rw [LocalizedModule.mk_add_mk]
        congr 1
        apply Subtype.ext
        simp [genPow, pow_add]
  | smul a y _ hy =>
      obtain ⟨n, x, hx, rfl⟩ := hy
      obtain ⟨l, a', ha', rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hg a
      refine ⟨l + n, a' • x, smul_mem_of_eq 𝓜 ha' hx (by
        simp only [nsmul_eq_mul, smul_eq_mul]
        push_cast
        ring), ?_⟩
      rw [away_smul_eq, HomogeneousLocalization.Away.val_mk, LocalizedModule.mk_smul_mk]
      congr 1
      apply Subtype.ext
      simp [genPow, pow_add]

/-- A single fraction with numerator of the right degree lies in the degree-zero part. -/
theorem mk_mem {g : A} {d : ℕ} (hg : g ∈ 𝒜 d) {n : ℕ} {x : M} (hx : x ∈ 𝓜 (n • (d : ℤ))) :
    LocalizedModule.mk x (genPow g n) ∈ GradedModuleDegreeZeroLocalization 𝒜 𝓜 g :=
  Submodule.subset_span ⟨d, n, hg, x, hx, rfl⟩

omit [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul 𝒜 𝓜] in
/-- Two fractions are equal once their cross products agree. -/
theorem mk_eq_mk_of_smul_eq {g : A} (x y : M) (s t : Submonoid.powers g)
    (h : (t : A) • x = (s : A) • y) : LocalizedModule.mk x s = LocalizedModule.mk y t :=
  LocalizedModule.mk_eq.mpr ⟨1, by simpa [Submonoid.smul_def] using h⟩

omit [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul 𝒜 𝓜] in
/-- Fractions with the same denominator add numerator-wise. -/
theorem mk_add_mk_same {g : A} (x y : M) (s : Submonoid.powers g) :
    LocalizedModule.mk (x + y) s = LocalizedModule.mk x s + LocalizedModule.mk y s := by
  rw [LocalizedModule.mk_add_mk]
  refine mk_eq_mk_of_smul_eq _ _ _ _ ?_
  simp only [Submonoid.coe_mul, smul_add, Submonoid.smul_def, smul_smul]

/-- Fractions with the same denominator add numerator-wise over finite sums. -/
private theorem mk_sum_same {g : A} {ι : Type*} (t : Finset ι) (w : ι → M)
    (s : Submonoid.powers g) :
    LocalizedModule.mk (∑ i ∈ t, w i) s = ∑ i ∈ t, LocalizedModule.mk (w i) s := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih, mk_add_mk_same]

/-- **A fraction `x / (cb)ᵏ` of the module with `x` of degree `e` is `uʲ` times a degree-zero
fraction**, for `j = e - k(2m + 1)`. -/
theorem exists_mk_eq_chartUnit_zpow_smul (hc : c ∈ 𝒜 (m + 1)) (hb : b ∈ 𝒜 m) (hcb : c * b = g)
    {e : ℤ} {x : M} (hx : x ∈ 𝓜 e) (k : ℕ) :
    ∃ z ∈ GradedModuleDegreeZeroLocalization 𝒜 𝓜 g,
      LocalizedModule.mk x (genPow g k) =
        ((chartUnit hcb ^ (e - k * (2 * m + 1)) : (Localization.Away g)ˣ) :
          Localization.Away g) • z := by
  subst hcb
  have hg := mul_mem hc hb rfl
  rcases le_or_gt ((k : ℤ) * (2 * m + 1)) e with hle | hlt
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, e - k * (2 * m + 1) = n :=
      ⟨(e - k * (2 * m + 1)).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    have hdeg : b ^ (2 * n) • x ∈ 𝓜 ((n + k) • ((2 * m + 1 : ℕ) : ℤ)) :=
      smul_mem_of_eq 𝓜 (SetLike.pow_mem_graded (2 * n) hb) hx (by
        simp only [nsmul_eq_mul, smul_eq_mul]
        push_cast
        linarith [hn])
    refine ⟨_, mk_mem hg hdeg, ?_⟩
    rw [hn, coe_chartUnit_zpow_natCast, LocalizedModule.mk_smul_mk]
    refine mk_eq_mk_of_smul_eq _ _ _ _ ?_
    simp only [genPow, Submonoid.coe_mul, smul_smul]
    congr 1
    ring
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, e - k * (2 * m + 1) = -(n : ℤ) :=
      ⟨((k : ℤ) * (2 * m + 1) - e).toNat, by rw [Int.toNat_of_nonneg (by omega)]; ring⟩
    have hdeg : c ^ (2 * n) • x ∈ 𝓜 ((n + k) • ((2 * m + 1 : ℕ) : ℤ)) :=
      smul_mem_of_eq 𝓜 (SetLike.pow_mem_graded (2 * n) hc) hx (by
        simp only [nsmul_eq_mul, smul_eq_mul]
        push_cast
        linarith [hn])
    refine ⟨_, mk_mem hg hdeg, ?_⟩
    rw [hn, coe_chartUnit_zpow_neg_natCast, LocalizedModule.mk_smul_mk]
    refine mk_eq_mk_of_smul_eq _ _ _ _ ?_
    simp only [genPow, Submonoid.coe_mul, smul_smul]
    congr 1
    ring

/-- **The degree-zero part spans the localized module** over `A[1/cb]`. -/
theorem span_degreeZero_eq_top (hc : c ∈ 𝒜 (m + 1)) (hb : b ∈ 𝒜 m) (hcb : c * b = g) :
    Submodule.span (Localization.Away g)
      (GradedModuleDegreeZeroLocalization 𝒜 𝓜 g : Set (LocalizedModule.Away g M)) =
      ⊤ := by
  subst hcb
  classical
  rw [eq_top_iff]
  intro y _
  induction y using LocalizedModule.induction_on with
  | h x s =>
    obtain ⟨k, hk⟩ := s.2
    have hs : s = genPow (c * b) k := Subtype.ext hk.symm
    subst hs
    rw [← DirectSum.sum_support_decompose 𝓜 x]
    rw [mk_sum_same]
    refine Submodule.sum_mem _ fun e _ => ?_
    obtain ⟨z, hz, heq⟩ := exists_mk_eq_chartUnit_zpow_smul (𝓜 := 𝓜) hc hb rfl
      (DirectSum.decompose 𝓜 x e).2 k
    rw [heq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hz)

/-- A fraction vanishes only if some power of the inverted element kills its numerator. -/
private theorem exists_pow_smul_eq_zero_of_mk_eq_zero_aux {g : A} (x : M)
    (s : Submonoid.powers g) (h : LocalizedModule.mk x s = 0) : ∃ p : ℕ, g ^ p • x = 0 := by
  rw [← LocalizedModule.zero_mk (1 : Submonoid.powers g)] at h
  obtain ⟨⟨_, p, rfl⟩, hu⟩ := LocalizedModule.mk_eq.mp h
  exact ⟨p, by simpa [Submonoid.smul_def] using hu⟩

omit [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul 𝒜 𝓜] in
/-- A fraction vanishes as soon as some power of the inverted element kills its numerator. -/
theorem mk_eq_zero_of_pow_smul_eq_zero {g : A} (x : M) (s : Submonoid.powers g) {p : ℕ}
    (h : g ^ p • x = 0) : LocalizedModule.mk x s = 0 := by
  rw [← LocalizedModule.zero_mk s]
  exact LocalizedModule.mk_eq.mpr ⟨⟨g ^ p, p, rfl⟩, by
    rw [Submonoid.smul_def, Submonoid.smul_def, smul_zero, smul_comm, Submonoid.smul_def, h,
      smul_zero, smul_zero]⟩

omit [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul 𝒜 𝓜] in
/-- A fraction with denominator one vanishes only if a power of the inverted element kills its
numerator. -/
theorem exists_pow_smul_eq_zero_of_mk_eq_zero {g : A} (x : M)
    (h : LocalizedModule.mk x (1 : Submonoid.powers g) = 0) : ∃ p : ℕ, g ^ p • x = 0 :=
  exists_pow_smul_eq_zero_of_mk_eq_zero_aux x 1 h

/-- **The powers of `u` are independent over the degree-zero part of the module**: a vanishing
finite sum `∑ uʲ zⱼ` with every `zⱼ` of degree zero has every `zⱼ = 0`. -/
theorem eq_zero_of_sum_chartUnit_zpow_smul_eq_zero (hc : c ∈ 𝒜 (m + 1)) (hb : b ∈ 𝒜 m)
    (hcb : c * b = g) (s : Finset ℤ) (z : ℤ → GradedModuleDegreeZeroLocalization 𝒜 𝓜 g)
    (h : ∑ j ∈ s, ((chartUnit hcb ^ j : (Localization.Away g)ˣ) :
      Localization.Away g) • (z j : LocalizedModule.Away g M) = 0)
    {j₀ : ℤ} (hj₀ : j₀ ∈ s) : z j₀ = 0 := by
  subst hcb
  classical
  have hg := mul_mem hc hb rfl
  choose n x hx hzx using fun j => exists_eq_mk_of_mem hg (z j).2
  obtain ⟨N, hjN⟩ := exists_nat_add_nonneg s
  set a : ℤ → ℕ := fun j => (j + N).toNat with hadef
  have ha : ∀ j ∈ s, (a j : ℤ) = j + N := fun j hj => Int.toNat_of_nonneg (hjN j hj)
  set J : ℕ := s.sup n with hJ
  set K : ℕ := s.sup a with hK
  have hnJ : ∀ j ∈ s, n j ≤ J := fun j hj => Finset.le_sup hj
  have haK : ∀ j ∈ s, a j ≤ K := fun j hj => Finset.le_sup hj
  set w : ℤ → M := fun j => ((c * b) ^ ((J - n j) + (K - a j)) * c ^ (2 * a j)) • x j with hw
  set t : Localization.Away (c * b) :=
    algebraMap A (Localization.Away (c * b)) ((c * b) ^ (J + K)) *
      ((chartUnit (rfl : c * b = c * b) ^ (N : ℤ) : (Localization.Away (c * b))ˣ) :
        Localization.Away (c * b))
    with ht
  have hterm : ∀ j ∈ s, t • (((chartUnit (rfl : c * b = c * b) ^ j : (Localization.Away (c * b))ˣ) :
      Localization.Away (c * b)) • (z j : LocalizedModule.Away (c * b) M)) =
      LocalizedModule.mk (w j) 1 := by
    intro j hj
    have hu := chartUnit_zpow_natCast_mul_zpow (rfl : c * b = c * b) N (a j) j
      (by rw [ha j hj]; ring)
    rw [smul_smul, ht, mul_assoc, hu, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul,
      hzx j, LocalizedModule.mk_smul_mk]
    refine mk_eq_mk_of_smul_eq _ _ _ _ ?_
    simp only [genPow, Submonoid.coe_mul, OneMemClass.coe_one, one_mul, hw, smul_smul]
    congr 1
    have e1 : J = n j + (J - n j) := (Nat.add_sub_cancel' (hnJ j hj)).symm
    have e2 : K = a j + (K - a j) := (Nat.add_sub_cancel' (haK j hj)).symm
    conv_lhs => rw [e1, e2]
    ring
  have hsum : LocalizedModule.mk (∑ j ∈ s, w j) (1 : Submonoid.powers (c * b)) = 0 := by
    rw [mk_sum_same, ← Finset.sum_congr rfl hterm, ← Finset.smul_sum, h, smul_zero]
  obtain ⟨p, hp⟩ := exists_pow_smul_eq_zero_of_mk_eq_zero _ hsum
  rw [Finset.smul_sum] at hp
  have hdeg : ∀ j ∈ s, (c * b) ^ p • w j ∈
      𝓜 (((p + J + K) * (2 * m + 1) : ℕ) + (a j : ℤ)) := by
    intro j hj
    simp only [hw, smul_smul]
    rw [show (c * b) ^ p * ((c * b) ^ ((J - n j) + (K - a j)) * c ^ (2 * a j)) =
      (c * b) ^ (p + (J - n j) + (K - a j)) * c ^ (2 * a j) by ring]
    refine smul_mem_of_eq 𝓜 (SetLike.mul_mem_graded
      (SetLike.pow_mem_graded (p + (J - n j) + (K - a j)) hg)
      (SetLike.pow_mem_graded (2 * a j) hc)) (hx j) ?_
    have e1 : (n j : ℤ) ≤ J := by exact_mod_cast hnJ j hj
    have e2 : (a j : ℤ) ≤ K := by exact_mod_cast haK j hj
    simp only [smul_eq_mul, nsmul_eq_mul]
    push_cast [Nat.cast_sub (hnJ j hj), Nat.cast_sub (haK j hj)]
    ring
  have hinj : Set.InjOn (fun j => (((p + J + K) * (2 * m + 1) : ℕ) : ℤ) + (a j : ℤ)) s := by
    intro j hj j' hj' hjj
    simp only at hjj
    have := ha j hj
    have := ha j' hj'
    omega
  have hvan := eq_zero_of_sum_eq_zero_of_injOn 𝓜 hinj hdeg hp hj₀
  apply Subtype.ext
  rw [hzx j₀, Submodule.coe_zero]
  refine mk_eq_zero_of_pow_smul_eq_zero (p := p + (J - n j₀) + (K - a j₀) + 2 * a j₀) _ _ ?_
  have := congrArg (fun y => b ^ (2 * a j₀) • y) hvan
  simp only [hw, smul_smul, smul_zero] at this
  rw [← this]
  congr 1
  rw [pow_add, pow_add, pow_add, mul_pow (c) b (2 * a j₀)]
  ring

/-! ### The chart ratio of a degree-one element -/

variable {f : A}

/-- The degree of `f b²`. -/
theorem mul_sq_mem (hb : b ∈ 𝒜 m) (hf : f ∈ 𝒜 1) : f * b ^ 2 ∈ 𝒜 (1 • (2 * m + 1)) := by
  have h := SetLike.mul_mem_graded hf (SetLike.pow_mem_graded 2 hb)
  convert h using 2
  simp only [smul_eq_mul]
  ring

/-- **The chart ratio `w = f b² / (cb)`** of a degree-one element `f`: the degree-zero fraction by
which `f` differs from the unit `u` of degree one, `f = w u`. On `D₊(cb)` it is the local equation
of the zero scheme of `f`. -/
def chartRatio (hc : c ∈ 𝒜 (m + 1)) (hb : b ∈ 𝒜 m) (hcb : c * b = g) (hf : f ∈ 𝒜 1) : Away 𝒜 g :=
  Away.mk 𝒜 (mul_mem hc hb hcb) 1 (f * b ^ 2) (mul_sq_mem hb hf)

/-- The chart ratio is the fraction `f b² / g`. -/
theorem val_chartRatio (hc : c ∈ 𝒜 (m + 1)) (hb : b ∈ 𝒜 m) (hcb : c * b = g) (hf : f ∈ 𝒜 1) :
    (chartRatio hc hb hcb hf).val = Localization.mk (f * b ^ 2) (gen g) := by
  subst hcb
  rw [chartRatio, Away.val_mk]
  congr 1
  apply Subtype.ext
  simp [gen]

/-- **`f = w u` in `A[1/cb]`.** -/
theorem algebraMap_eq_chartRatio_mul (hc : c ∈ 𝒜 (m + 1)) (hb : b ∈ 𝒜 m) (hcb : c * b = g)
    (hf : f ∈ 𝒜 1) :
    algebraMap A (Localization.Away g) f =
      (chartRatio hc hb hcb hf).val * (chartUnit hcb : Localization.Away g) := by
  subst hcb
  rw [val_chartRatio, coe_chartUnit, Localization.mk_mul, ← Localization.mk_one_eq_algebraMap,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp [gen]; ring⟩

omit [AddSubgroupClass τ M] [DirectSum.Decomposition 𝓜] in
/-- **A multiple of `fᵏ` of the right degree is a multiple of `wᵏ` in the degree-zero part.** If
`x = fᵏ y` has degree `n • (2m + 1)`, then `x / (cb)ⁿ = wᵏ · (c²ᵏ y / (cb)ⁿ⁺ᵏ)`. -/
theorem mk_pow_smul_eq_chartRatio_pow_smul (hc : c ∈ 𝒜 (m + 1)) (hb : b ∈ 𝒜 m) (hcb : c * b = g)
    (hf : f ∈ 𝒜 1) (k n : ℕ) {y : M} (hy : y ∈ 𝓜 (n • ((2 * m + 1 : ℕ) : ℤ) - k)) :
    c ^ (2 * k) • y ∈ 𝓜 ((n + k) • ((2 * m + 1 : ℕ) : ℤ)) ∧
      LocalizedModule.mk (f ^ k • y) (genPow g n) =
        (chartRatio hc hb hcb hf ^ k) •
          LocalizedModule.mk (c ^ (2 * k) • y) (genPow g (n + k)) := by
  subst hcb
  refine ⟨smul_mem_of_eq 𝓜 (SetLike.pow_mem_graded (2 * k) hc) hy (by
    simp only [nsmul_eq_mul, smul_eq_mul]
    push_cast
    ring), ?_⟩
  rw [away_smul_eq, HomogeneousLocalization.val_pow, val_chartRatio, Localization.mk_pow,
    LocalizedModule.mk_smul_mk]
  refine mk_eq_mk_of_smul_eq _ _ _ _ ?_
  simp only [genPow, gen, Submonoid.coe_mul, SubmonoidClass.coe_pow, smul_smul]
  congr 1
  ring

/-- **`wᵏ` times a degree-zero fraction is a fraction with numerator a multiple of `fᵏ`.** -/
theorem chartRatio_pow_smul_mk (hc : c ∈ 𝒜 (m + 1)) (hb : b ∈ 𝒜 m) (hcb : c * b = g) (hf : f ∈ 𝒜 1)
    (k n : ℕ) (y : M) :
    (chartRatio hc hb hcb hf ^ k) • LocalizedModule.mk y (genPow g n) =
      LocalizedModule.mk (f ^ k • (b ^ (2 * k) • y)) (genPow g (n + k)) := by
  subst hcb
  rw [away_smul_eq, HomogeneousLocalization.val_pow, val_chartRatio, Localization.mk_pow,
    LocalizedModule.mk_smul_mk]
  refine mk_eq_mk_of_smul_eq _ _ _ _ ?_
  simp only [genPow, gen, Submonoid.coe_mul, SubmonoidClass.coe_pow, smul_smul]
  congr 1
  ring

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- **A homogeneous multiple of a homogeneous element is a multiple of a homogeneous element.**
If `x = a y` has degree `e` and `a` has degree `i`, then `x = a y'` with `y'` the degree `e - i`
component of `y`. -/
theorem eq_smul_decompose_of_eq_smul {i : ℕ} {a : A} (ha : a ∈ 𝒜 i) {e : ℤ} {x y : M}
    (hx : x ∈ 𝓜 e) (h : x = a • y) :
    x = a • (DirectSum.decompose 𝓜 y (e - i) : M) := by
  classical
  have key : ∀ y : M, (DirectSum.decompose 𝓜 (a • y) e : M) =
      a • (DirectSum.decompose 𝓜 y (e - i) : M) := by
    intro y
    induction y using DirectSum.Decomposition.inductionOn 𝓜 with
    | zero => simp
    | homogeneous y =>
        rename_i j
        have hay : a • (y : M) ∈ 𝓜 ((i : ℤ) + j) := smul_mem_of_eq 𝓜 ha y.2 rfl
        by_cases hn : e = (i : ℤ) + j
        · subst hn
          rw [DirectSum.decompose_of_mem_same 𝓜 hay,
            show (i : ℤ) + j - (i : ℤ) = j by ring, DirectSum.decompose_of_mem_same 𝓜 y.2]
        · rw [DirectSum.decompose_of_mem_ne 𝓜 hay (Ne.symm hn),
            DirectSum.decompose_of_mem_ne 𝓜 y.2 (by omega), smul_zero]
    | add y y' hy hy' =>
        rw [smul_add, DirectSum.decompose_add, DirectSum.add_apply, AddMemClass.coe_add, hy, hy',
          DirectSum.decompose_add, DirectSum.add_apply, AddMemClass.coe_add, smul_add]
  rw [← key, ← h, DirectSum.decompose_of_mem_same 𝓜 hx]

omit [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul 𝒜 𝓜] in
/-- A fraction vanishes only if some power of the inverted element kills its numerator. -/
theorem exists_pow_smul_eq_zero_of_mk_eq_zero' {g : A} (x : M) (s : Submonoid.powers g)
    (h : LocalizedModule.mk x s = 0) : ∃ p : ℕ, g ^ p • x = 0 :=
  exists_pow_smul_eq_zero_of_mk_eq_zero_aux x s h

omit [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul 𝒜 𝓜] in
/-- The multiples of `fᵏ` are the elements of `(f)ᵏ M`. -/
theorem mem_span_pow_smul_top_iff (k : ℕ) (x : M) :
    x ∈ Ideal.span {f} ^ k • (⊤ : Submodule A M) ↔ ∃ y : M, f ^ k • y = x := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp

/-- **The kernel of `M₍g₎ → (M / fᵏM)₍g₎` is `wᵏ M₍g₎`.** A degree-zero fraction dies modulo `fᵏ`
exactly when it is `wᵏ` times a degree-zero fraction, `w = f b² / (cb)` the chart ratio. -/
theorem map_mkQ_eq_zero_iff (hc : c ∈ 𝒜 (m + 1)) (hb : b ∈ 𝒜 m) (hcb : c * b = g)
    (hf : f ∈ 𝒜 1) (k : ℕ) {z : LocalizedModule.Away g M}
    (hz : z ∈ GradedModuleDegreeZeroLocalization 𝒜 𝓜 g) :
    LocalizedModule.map (Submonoid.powers g)
        (Ideal.span {f} ^ k • (⊤ : Submodule A M)).mkQ z = 0 ↔
      ∃ z' ∈ GradedModuleDegreeZeroLocalization 𝒜 𝓜 g, z = chartRatio hc hb hcb hf ^ k • z' := by
  subst hcb
  have hg := mul_mem hc hb rfl
  constructor
  · intro h
    obtain ⟨n, x, hx, rfl⟩ := exists_eq_mk_of_mem hg hz
    rw [LocalizedModule.map_mk] at h
    obtain ⟨p, hp⟩ := exists_pow_smul_eq_zero_of_mk_eq_zero' _ _ h
    rw [← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hp
    obtain ⟨y, hy⟩ := (mem_span_pow_smul_top_iff k _).mp hp
    have hxp : (c * b) ^ p • x ∈ 𝓜 ((n + p) • ((2 * m + 1 : ℕ) : ℤ)) :=
      smul_mem_of_eq 𝓜 (SetLike.pow_mem_graded p hg) hx (by
        simp only [nsmul_eq_mul, smul_eq_mul]
        push_cast
        ring)
    have hdec := eq_smul_decompose_of_eq_smul (𝓜 := 𝓜) (SetLike.pow_mem_graded k hf) hxp hy.symm
    set y' := (DirectSum.decompose 𝓜 y ((n + p : ℕ) • ((2 * m + 1 : ℕ) : ℤ) - (k • 1 : ℕ)) : M)
    have hy'mem : y' ∈ 𝓜 ((n + p) • ((2 * m + 1 : ℕ) : ℤ) - k) := by
      convert (DirectSum.decompose 𝓜 y ((n + p : ℕ) • ((2 * m + 1 : ℕ) : ℤ) - (k • 1 : ℕ))).2
        using 2
      simp
    obtain ⟨hmem, heq⟩ := mk_pow_smul_eq_chartRatio_pow_smul (𝓜 := 𝓜) hc hb rfl hf k (n + p) hy'mem
    refine ⟨_, mk_mem hg hmem, ?_⟩
    rw [← heq, ← hdec]
    exact mk_eq_mk_of_smul_eq _ _ _ _ (by simp only [genPow, smul_smul, ← pow_add])
  · rintro ⟨z', hz', rfl⟩
    obtain ⟨n, y, hy, rfl⟩ := exists_eq_mk_of_mem hg hz'
    rw [chartRatio_pow_smul_mk, LocalizedModule.map_mk, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero _).mpr ((mem_span_pow_smul_top_iff k _).mpr ⟨_, rfl⟩),
      LocalizedModule.zero_mk]

end Module

end Stacks.DegreeOneUnitAway

end
