module

public import Mathlib.Data.ENat.BigOperators
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Tactic.FinCases
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.CalculationMultiplicities.TwoPeriodic
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesHerbrand.Defs
public import StacksFrontier.RingTheory.Lattice.Distance

/-!
# Vanishing of the periodic length of powers of a nilpotent endomorphism

For a nilpotent endomorphism of a module, the two-periodic complexes whose differentials are
complementary powers of that endomorphism have periodic length zero, provided the quotient of
the kernel by the penultimate image has finite length.

## Main results

* `AlgebraicGeometry.isFiniteLength_homology_and_periodicLength_powers_eq_zero_of_nilpotent`
  states that for all complementary powers of a nilpotent endomorphism the two-periodic complex
  has finite-length cohomology and periodic length zero (Stacks 0EAB).
* `AlgebraicGeometry.periodicLength_powers_eq_zero_of_nilpotent` states the vanishing of the
  periodic length alone.

## Implementation notes

The quotient `ker φ / range (φ ^ (n - 1))` is represented as the quotient of `ker φ` by the
comap of `range (φ ^ (n - 1))` along its inclusion into the ambient module. The nilpotence
hypothesis ensures that this comap is precisely the penultimate image viewed inside the kernel.

The proof filters the kernel of the `i`-th power by the kernels of the smaller powers and
compares its graded pieces with those of the filtration of `ker φ` by the images of the powers;
the resulting double sum is symmetric in the two exponents, which is the vanishing.

## References

* [Stacks Project, Tag 0EAB](https://stacks.math.columbia.edu/tag/0EAB)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

/-- The kernel of the `i`-th power of an endomorphism. -/
private def powerKer {R : Type u} [Ring R] {M : Type v}
    [AddCommGroup M] [Module R M] (φ : Module.End R M) (i : ℕ) :
    Submodule R M := LinearMap.ker (φ ^ i)

/-- The image of the `i`-th power of an endomorphism. -/
private def powerRange {R : Type u} [Ring R] {M : Type v}
    [AddCommGroup M] [Module R M] (φ : Module.End R M) (i : ℕ) :
    Submodule R M := LinearMap.range (φ ^ i)

/-- The part of the image of the `i`-th power of an endomorphism that is killed by
the endomorphism itself. -/
private def firstLayer {R : Type u} [Ring R] {M : Type v}
    [AddCommGroup M] [Module R M] (φ : Module.End R M) (i : ℕ) :
    Submodule R M := powerKer φ 1 ⊓ powerRange φ i

/-- Applying two powers of an endomorphism in succession is applying the power given
by the sum of the exponents. -/
private lemma power_apply_power {R : Type u} [Ring R] {M : Type v}
    [AddCommGroup M] [Module R M] (φ : Module.End R M) (a b : ℕ) (x : M) :
    (φ ^ a) ((φ ^ b) x) = (φ ^ (a + b)) x := by
  rw [← Module.End.mul_apply, ← pow_add]

/-- The kernels of the powers of an endomorphism increase with the exponent. -/
private lemma powerKer_mono {R : Type u} [Ring R] {M : Type v}
    [AddCommGroup M] [Module R M] (φ : Module.End R M) {a b : ℕ} (hab : a ≤ b) :
    powerKer φ a ≤ powerKer φ b := by
  intro x hx
  change (φ ^ b) x = 0
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [add_comm, ← power_apply_power]
  simp [LinearMap.mem_ker.mp hx]

/-- The images of the powers of an endomorphism decrease with the exponent. -/
private lemma powerRange_antitone {R : Type u} [Ring R] {M : Type v}
    [AddCommGroup M] [Module R M] (φ : Module.End R M) {a b : ℕ} (hab : a ≤ b) :
    powerRange φ b ≤ powerRange φ a := by
  rintro x ⟨y, rfl⟩
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  exact ⟨(φ ^ c) y, power_apply_power φ a c y⟩

/-- The graded piece of the kernel filtration at exponent `a` with offset `b` has the
same length as the corresponding graded piece of the first-layer filtration. -/
private lemma kernel_grade_length {R : Type u} [Ring R] {M : Type v}
    [AddCommGroup M] [Module R M] (φ : Module.End R M) (a b : ℕ) :
    Module.length R (↥(powerKer φ (a + 1)) ⧸
      (powerKer φ a ⊔ powerRange φ b).comap (powerKer φ (a + 1)).subtype) =
    Module.length R (↥(firstLayer φ a) ⧸
      (firstLayer φ (a + b)).comap (firstLayer φ a).subtype) := by
  let F : (powerKer φ (a + 1)) →ₗ[R] firstLayer φ a :=
    ((φ ^ a).comp (powerKer φ (a + 1)).subtype).codRestrict (firstLayer φ a)
      (fun x => by
        constructor
        · change φ ((φ ^ a) x.1) = 0
          rw [← Module.End.mul_apply, ← pow_succ']
          exact x.2
        · exact ⟨x.1, rfl⟩)
  have hF : Function.Surjective F := by
    intro y
    obtain ⟨x, hx⟩ := y.2.2
    have hk : x ∈ powerKer φ (a + 1) := by
      change (φ ^ (a + 1)) x = 0
      rw [← Nat.add_comm 1 a, ← power_apply_power φ 1 a, hx]
      exact y.2.1
    exact ⟨⟨x, hk⟩, Subtype.ext hx⟩
  have hpre : ((firstLayer φ (a + b)).comap (firstLayer φ a).subtype).comap F =
      (powerKer φ a ⊔ powerRange φ b).comap (powerKer φ (a + 1)).subtype := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ : (φ ^ a) x.1 ∈ powerRange φ (a + b) :=
        (show (F x).1 ∈ firstLayer φ (a + b) from hx).2
      let z := (φ ^ b) y
      have hz : z ∈ powerRange φ b := ⟨y, rfl⟩
      have hk : (x : M) - z ∈ powerKer φ a := by
        change (φ ^ a) ((x : M) - z) = 0
        rw [map_sub, power_apply_power φ a b, ← hy, sub_self]
      exact Submodule.mem_sup.mpr ⟨(x : M) - z, hk, z, hz, sub_add_cancel _ _⟩
    · intro hx
      obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hx
      obtain ⟨y, hy⟩ := hv
      change (φ ^ a) x.1 ∈ firstLayer φ (a + b)
      refine ⟨(F x).2.1, y, ?_⟩
      change (φ ^ (a + b)) y = (φ ^ a) x.1
      rw [← power_apply_power φ a b, hy]
      simpa [LinearMap.mem_ker.mp hu] using congrArg (φ ^ a) huv
  rw [← hpre]
  exact quotient_length_of_bijective_map F hF
    ((firstLayer φ (a + b)).comap (firstLayer φ a).subtype)

/-- The `k`-th step of the filtration of the kernel of a power by the kernels of the
smaller powers together with the image of the `b`-th power. -/
private def kernelFiltration {R : Type u} [Ring R] {M : Type v}
    [AddCommGroup M] [Module R M] (φ : Module.End R M) (b k : ℕ) :
    Submodule R M := powerKer φ k ⊔ powerRange φ b

/-- The kernel filtration is increasing. -/
private lemma kernelFiltration_mono {R : Type u} [Ring R] {M : Type v}
    [AddCommGroup M] [Module R M] (φ : Module.End R M) (b k : ℕ) :
    kernelFiltration φ b k ≤ kernelFiltration φ b (k + 1) :=
  sup_le_sup_right (powerKer_mono φ k.le_succ) _

/-- A graded piece of the kernel filtration has the same length as the corresponding
graded piece of the first-layer filtration. -/
private lemma kernelFiltration_grade_length {R : Type u} [Ring R] {M : Type v}
    [AddCommGroup M] [Module R M] (φ : Module.End R M) (b k : ℕ) :
    Module.length R (↥(kernelFiltration φ b (k + 1)) ⧸
      (kernelFiltration φ b k).submoduleOf (kernelFiltration φ b (k + 1))) =
    Module.length R (↥(firstLayer φ k) ⧸
      (firstLayer φ (k + b)).submoduleOf (firstLayer φ k)) := by
  have hsup : powerKer φ (k + 1) ⊔ kernelFiltration φ b k =
      kernelFiltration φ b (k + 1) := by
    unfold kernelFiltration
    rw [← sup_assoc, sup_of_le_left (powerKer_mono φ (Nat.le_succ k))]
  have h := (LinearMap.quotientInfEquivSupQuotient
    (powerKer φ (k + 1)) (kernelFiltration φ b k)).length_eq
  rw [Submodule.comap_subtype_self, top_inf_eq, hsup] at h
  have hh : Module.length R (↥(powerKer φ (k + 1)) ⧸
      (powerKer φ k ⊔ powerRange φ b).comap (powerKer φ (k + 1)).subtype) =
      Module.length R (↥(kernelFiltration φ b (k + 1)) ⧸
        (kernelFiltration φ b k).submoduleOf (kernelFiltration φ b (k + 1))) := by
    convert h using 1 <;> simp [kernelFiltration, Submodule.submoduleOf] <;> rfl
  exact (hh.symm.trans (kernel_grade_length φ k b)).trans (by rfl)

/-- The length of the `m`-th step of the kernel filtration over the image of the `b`-th
power is the sum of the lengths of its graded pieces. -/
private lemma kernelFiltration_length_sum {R : Type u} [Ring R] {M : Type v}
    [AddCommGroup M] [Module R M] (φ : Module.End R M) (b m : ℕ) :
    Module.length R (↥(kernelFiltration φ b m) ⧸
      (powerRange φ b).submoduleOf (kernelFiltration φ b m)) =
    ∑ k ∈ Finset.range m, Module.length R (↥(firstLayer φ k) ⧸
      (firstLayer φ (k + b)).submoduleOf (firstLayer φ k)) := by
  induction m with
  | zero =>
      have h0 : kernelFiltration φ b 0 = powerRange φ b := by
        have hk0 : powerKer φ 0 = ⊥ := by
          change LinearMap.ker (1 : Module.End R M) = ⊥
          exact LinearMap.ker_id
        simp [kernelFiltration, hk0]
      simp [h0]
  | succ m ih =>
      rw [Finset.sum_range_succ,
        Module.length_quotient_submoduleOf_eq_add le_sup_right (kernelFiltration_mono φ b m),
        ih, kernelFiltration_grade_length]

/-- The first layers decrease with the exponent. -/
private lemma firstLayer_antitone {R : Type u} [Ring R] {M : Type v}
    [AddCommGroup M] [Module R M] (φ : Module.End R M)
    {a b : ℕ} (hab : a ≤ b) : firstLayer φ b ≤ firstLayer φ a :=
  inf_le_inf le_rfl (powerRange_antitone φ hab)

/-- Each graded piece of the first-layer filtration below the nilpotency exponent has
finite length, computed as a difference of lengths measured from the bottom layer. -/
private lemma firstLayer_grade_toNat {R : Type u} [Ring R] {M : Type v}
    [AddCommGroup M] [Module R M] (φ : Module.End R M)
    (n : ℕ)
    (hbase : Module.length R (↥(firstLayer φ 0) ⧸
      (firstLayer φ n).submoduleOf (firstLayer φ 0)) ≠ ⊤)
    {p q : ℕ} (hpq : p ≤ q) (hqn : q ≤ n) :
    Module.length R (↥(firstLayer φ p) ⧸
      (firstLayer φ q).submoduleOf (firstLayer φ p)) ≠ ⊤ ∧
    ((Module.length R (↥(firstLayer φ p) ⧸
      (firstLayer φ q).submoduleOf (firstLayer φ p))).toNat : ℤ) =
      ((Module.length R (↥(firstLayer φ 0) ⧸
        (firstLayer φ q).submoduleOf (firstLayer φ 0))).toNat : ℤ) -
      ((Module.length R (↥(firstLayer φ 0) ⧸
        (firstLayer φ p).submoduleOf (firstLayer φ 0))).toNat : ℤ) := by
  have hq0 : firstLayer φ q ≤ firstLayer φ 0 := firstLayer_antitone φ (Nat.zero_le _)
  have hp0 : firstLayer φ p ≤ firstLayer φ 0 := firstLayer_antitone φ (Nat.zero_le _)
  have hqp : firstLayer φ q ≤ firstLayer φ p := firstLayer_antitone φ hpq
  have hnq : firstLayer φ n ≤ firstLayer φ q := firstLayer_antitone φ hqn
  have split {x y z : ℕ∞} (h : x = y + z) (hx : x ≠ ⊤) : y ≠ ⊤ ∧ z ≠ ⊤ := by
    simpa [h, not_or] using hx
  have hlen := Module.length_quotient_submoduleOf_eq_add hqp hp0
  have hq := (split (Module.length_quotient_submoduleOf_eq_add hnq hq0) hbase).2
  obtain ⟨hgrade, hp⟩ := split hlen hq
  have hnat := congrArg ENat.toNat hlen
  rw [ENat.toNat_add hgrade hp] at hnat
  exact ⟨hgrade, by omega⟩

/-- For a nilpotent endomorphism of order `n` and `a + b = n`, the image of the `b`-th
power lies in the kernel of the `a`-th power. -/
private lemma powerRange_le_powerKer {R : Type u} [Ring R] {M : Type v}
    [AddCommGroup M] [Module R M] (φ : Module.End R M)
    (n : ℕ) (hnil : φ ^ n = 0) (a b : ℕ) (hab : a + b = n) :
    powerRange φ b ≤ powerKer φ a := by
  rintro x ⟨y, rfl⟩
  change (φ ^ a) ((φ ^ b) y) = 0
  rw [power_apply_power, hab, hnil, LinearMap.zero_apply]

/-- The telescoping sum of successive differences of a sequence over the first `a`
indices with offset `b` is symmetric in `a` and `b`. -/
private lemma finite_layer_sum_symmetric (L : ℕ → ℤ) (a b : ℕ) :
    (∑ k ∈ Finset.range a, (L (k + b) - L k)) =
      ∑ k ∈ Finset.range b, (L (k + a) - L k) := by
  simp_rw [Finset.sum_sub_distrib]
  have h₁ : (∑ k ∈ Finset.range (a + b), L k) =
      (∑ k ∈ Finset.range b, L k) + (∑ k ∈ Finset.range a, L (k + b)) := by
    convert Finset.sum_range_add L b a using 1 <;> simp [add_comm]
  have h₂ : (∑ k ∈ Finset.range (a + b), L k) =
      (∑ k ∈ Finset.range a, L k) + (∑ k ∈ Finset.range b, L (k + a)) := by
    convert Finset.sum_range_add L a b using 1; simp [add_comm]
  omega

/-- For a nilpotent endomorphism of order `n` and `a + b = n`, the length of
`ker (φ ^ a) / range (φ ^ b)` is the sum of the lengths of the graded pieces of the
first-layer filtration with offset `b` below `a`. -/
private lemma powerKer_quotient_length_eq_sum {R : Type u} [Ring R] {M : Type v}
    [AddCommGroup M] [Module R M] (φ : Module.End R M)
    (n : ℕ) (hnil : φ ^ n = 0) (a b : ℕ) (hab : a + b = n) :
    Module.length R (↥(powerKer φ a) ⧸
      (powerRange φ b).submoduleOf (powerKer φ a)) =
    ∑ k ∈ Finset.range a, Module.length R (↥(firstLayer φ k) ⧸
      (firstLayer φ (k + b)).submoduleOf (firstLayer φ k)) := by
  have hfinal : kernelFiltration φ b a = powerKer φ a :=
    sup_of_le_left (powerRange_le_powerKer φ n hnil a b hab)
  have h := kernelFiltration_length_sum φ b a
  rwa [hfinal] at h

/-- For a nilpotent endomorphism of order `n` with `ker φ / range (φ ^ (n - 1))` of
finite length and `a + b = n`, every graded piece of the first-layer filtration with
offset `b` below `a` has finite length. -/
private lemma firstLayer_grade_ne_top {R : Type u} [Ring R] {M : Type v}
    [AddCommGroup M] [Module R M] (φ : Module.End R M) (n : ℕ)
    (hbase : Module.length R (↥(firstLayer φ 0) ⧸
      (firstLayer φ (n - 1)).submoduleOf (firstLayer φ 0)) ≠ ⊤)
    (a b : ℕ) (hab : a + b = n) :
    ∀ k ∈ Finset.range a,
      Module.length R (↥(firstLayer φ k) ⧸
        (firstLayer φ (k + b)).submoduleOf (firstLayer φ k)) ≠ ⊤ := by
  intro k hk
  rw [Finset.mem_range] at hk
  exact (firstLayer_grade_toNat φ (n - 1) hbase (Nat.le_add_right k b) (by omega)).1

/-- For a nilpotent endomorphism of order `n` with `ker φ / range (φ ^ (n - 1))` of
finite length and `a + b = n`, the quotient `ker (φ ^ a) / range (φ ^ b)` has finite
length. -/
private lemma powerKer_quotient_length_ne_top {R : Type u} [Ring R] {M : Type v}
    [AddCommGroup M] [Module R M] (φ : Module.End R M)
    (n : ℕ) (hnil : φ ^ n = 0)
    (hbase : Module.length R (↥(firstLayer φ 0) ⧸
      (firstLayer φ (n - 1)).submoduleOf (firstLayer φ 0)) ≠ ⊤)
    (a b : ℕ) (hab : a + b = n) :
    Module.length R (↥(powerKer φ a) ⧸
      (powerRange φ b).submoduleOf (powerKer φ a)) ≠ ⊤ := by
  rw [powerKer_quotient_length_eq_sum φ n hnil a b hab]
  exact ENat.sum_ne_top.mpr (firstLayer_grade_ne_top φ n hbase a b hab)

/-- Interchanging the two complementary powers of a nilpotent endomorphism does not
change the length of the relevant quotient. -/
private lemma kernel_quotient_length_symmetric {R : Type u} [Ring R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (φ : Module.End R M) (n : ℕ) (hnpos : 0 < n) (hnil : φ ^ n = 0)
    (hbase : Module.length R (↥(firstLayer φ 0) ⧸
      (firstLayer φ (n - 1)).submoduleOf (firstLayer φ 0)) ≠ ⊤)
    (i : ℕ) (hi : i ≤ n) :
    (Module.length R (↥(powerKer φ i) ⧸
      (powerRange φ (n - i)).submoduleOf (powerKer φ i))).toNat =
    (Module.length R (↥(powerKer φ (n - i)) ⧸
      (powerRange φ i).submoduleOf (powerKer φ (n - i)))).toNat := by
  let L : ℕ → ℤ := fun q =>
    ((Module.length R (↥(firstLayer φ 0) ⧸
      (firstLayer φ q).submoduleOf (firstLayer φ 0))).toNat : ℤ)
  have hsum := powerKer_quotient_length_eq_sum φ n hnil
  have hterms := firstLayer_grade_ne_top φ n hbase
  have hlen (a b : ℕ) (hab : a + b = n) :
      ((Module.length R (↥(powerKer φ a) ⧸
        (powerRange φ b).submoduleOf (powerKer φ a))).toNat : ℤ) =
      ∑ k ∈ Finset.range a, (L (k + b) - L k) := by
    have hnat := congrArg ENat.toNat (hsum a b hab)
    rw [ENat.toNat_sum (hterms a b hab)] at hnat
    have hint := congrArg (fun t : ℕ => (t : ℤ)) hnat
    rw [Nat.cast_sum] at hint
    rw [hint]
    apply Finset.sum_congr rfl
    intro k hk
    exact (firstLayer_grade_toNat φ (n - 1) hbase
      (Nat.le_add_right k b) (by have := Finset.mem_range.mp hk; omega)).2
  have h₁ := hlen i (n - i) (Nat.add_sub_of_le hi)
  have h₂ := hlen (n - i) i (Nat.sub_add_cancel hi)
  exact_mod_cast h₁.trans ((finite_layer_sum_symmetric L i (n - i)).trans h₂.symm)

/-- For a nilpotent endomorphism of order `n`, the finiteness of the length of
`ker φ / range (φ ^ (n - 1))` is the finiteness of the bottom graded piece of the
first-layer filtration. -/
private lemma firstLayer_base_ne_top {R : Type u} [Ring R] {M : Type v}
    [AddCommGroup M] [Module R M] (φ : Module.End R M) (n : ℕ) (hnpos : 0 < n)
    (hnil : φ ^ n = 0)
    (hfinite : IsFiniteLength R ((LinearMap.ker φ) ⧸
      (LinearMap.range (φ ^ (n - 1))).comap (LinearMap.ker φ).subtype)) :
    Module.length R (↥(firstLayer φ 0) ⧸
      (firstLayer φ (n - 1)).submoduleOf (firstLayer φ 0)) ≠ ⊤ := by
  have hfirst : firstLayer φ 0 = powerKer φ 1 := by
    have hr0 : powerRange φ 0 = ⊤ := by
      change LinearMap.range (1 : Module.End R M) = ⊤
      exact LinearMap.range_id
    unfold firstLayer
    rw [hr0, inf_top_eq]
  have hlast : firstLayer φ (n - 1) = powerRange φ (n - 1) :=
    inf_of_le_right (powerRange_le_powerKer φ n hnil 1 (n - 1) (by omega))
  rw [hfirst, hlast]
  change Module.length R (↥(LinearMap.ker φ) ⧸
    (LinearMap.range (φ ^ (n - 1))).comap (LinearMap.ker φ).subtype) ≠ ⊤
  exact Module.length_ne_top_iff.mpr hfinite

/-- The degree-zero cohomology of the two-periodic complex of complementary powers of a
nilpotent endomorphism has the length of `ker (φ ^ i) / range (φ ^ (n - i))`. -/
private lemma length_homology_zero_twoPeriodicComplex_pow {R : Type u} [Ring R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (φ : Module.End R M) (n : ℕ) (hnil : φ ^ n = 0) (i : ℕ) (hi : i ≤ n) :
    Module.length R
        ((twoPeriodicComplex (φ ^ i) (φ ^ (n - i))
          (by rw [← pow_add, Nat.add_sub_of_le hi, hnil])
          (by rw [← pow_add, Nat.sub_add_cancel hi, hnil])).homology (0 : ZMod 2)) =
      Module.length R (↥(powerKer φ i) ⧸
        (powerRange φ (n - i)).submoduleOf (powerKer φ i)) := by
  have htmp := homology_length_eq_ker_quotient (φ ^ i) (φ ^ (n - i))
    (by rw [← pow_add, Nat.add_sub_of_le hi, hnil])
    (by rw [← pow_add, Nat.sub_add_cancel hi, hnil]) 0 (Or.inl rfl)
  simp only at htmp
  convert htmp using 1; rfl

/-- The degree-one cohomology of the two-periodic complex of complementary powers of a
nilpotent endomorphism has the length of `ker (φ ^ (n - i)) / range (φ ^ i)`. -/
private lemma length_homology_one_twoPeriodicComplex_pow {R : Type u} [Ring R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (φ : Module.End R M) (n : ℕ) (hnil : φ ^ n = 0) (i : ℕ) (hi : i ≤ n) :
    Module.length R
        ((twoPeriodicComplex (φ ^ i) (φ ^ (n - i))
          (by rw [← pow_add, Nat.add_sub_of_le hi, hnil])
          (by rw [← pow_add, Nat.sub_add_cancel hi, hnil])).homology (1 : ZMod 2)) =
      Module.length R (↥(powerKer φ (n - i)) ⧸
        (powerRange φ i).submoduleOf (powerKer φ (n - i))) := by
  have htmp := homology_length_eq_ker_quotient (φ ^ i) (φ ^ (n - i))
    (by rw [← pow_add, Nat.add_sub_of_le hi, hnil])
    (by rw [← pow_add, Nat.sub_add_cancel hi, hnil]) 1 (Or.inr rfl)
  simp only [one_ne_zero, ite_false] at htmp
  convert htmp using 1; rfl

/-- If `φ` is nilpotent of order at most `n` and
`ker φ / range (φ ^ (n - 1))` has finite length, then the periodic length associated to
`φ ^ i` and `φ ^ (n - i)` vanishes for every `0 ≤ i ≤ n`.

Since `periodicLength` reads infinite lengths as zero, this alone does not say that the
multiplicity is defined; the full statement of Stacks 0EAB, including the finiteness of both
cohomology modules, is
`isFiniteLength_homology_and_periodicLength_powers_eq_zero_of_nilpotent`. -/
@[stacks 0EAB]
public lemma periodicLength_powers_eq_zero_of_nilpotent {R : Type u} [Ring R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (φ : Module.End R M) (n : ℕ) (hnpos : 0 < n) (hnil : φ ^ n = 0)
    (hfinite : IsFiniteLength R ((LinearMap.ker φ) ⧸
      (LinearMap.range (φ ^ (n - 1))).comap (LinearMap.ker φ).subtype)) :
    ∀ (i : ℕ) (hi : i ≤ n),
      periodicLength
        (twoPeriodicComplex (φ ^ i) (φ ^ (n - i))
          (by rw [← pow_add, Nat.add_sub_of_le hi, hnil])
          (by rw [← pow_add, Nat.sub_add_cancel hi, hnil])) = 0 := by
  intro i hi
  have hbase := firstLayer_base_ne_top φ n hnpos hnil hfinite
  have hsym := kernel_quotient_length_symmetric φ n hnpos hnil hbase i hi
  change ((Module.length R
    ((twoPeriodicComplex (φ ^ i) (φ ^ (n - i))
      (by rw [← pow_add, Nat.add_sub_of_le hi, hnil])
      (by rw [← pow_add, Nat.sub_add_cancel hi, hnil])).homology (0 : ZMod 2))).toNat : ℤ) -
    ((Module.length R
    ((twoPeriodicComplex (φ ^ i) (φ ^ (n - i))
      (by rw [← pow_add, Nat.add_sub_of_le hi, hnil])
      (by rw [← pow_add, Nat.sub_add_cancel hi, hnil])).homology (1 : ZMod 2))).toNat : ℤ) = 0
  rw [length_homology_zero_twoPeriodicComplex_pow φ n hnil i hi,
    length_homology_one_twoPeriodicComplex_pow φ n hnil i hi, hsym]
  ring

/-- **Stacks 0EAB.** Let `φ` be an endomorphism of an `R`-module `M` and `n > 0` with
`φ ^ n = 0` such that `ker φ / range (φ ^ (n - 1))` has finite length. Then for every
`0 ≤ i ≤ n` the multiplicity `e_R(M, φ ^ i, φ ^ (n - i))` is defined, that is, both
cohomology modules `ker (φ ^ i) / range (φ ^ (n - i))` and `ker (φ ^ (n - i)) / range (φ ^ i)`
of the two-periodic complex `(M, φ ^ i, φ ^ (n - i))` have finite length, and it vanishes. -/
@[stacks 0EAB]
public theorem isFiniteLength_homology_and_periodicLength_powers_eq_zero_of_nilpotent
    {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]
    (φ : Module.End R M) (n : ℕ) (hnpos : 0 < n) (hnil : φ ^ n = 0)
    (hfinite : IsFiniteLength R ((LinearMap.ker φ) ⧸
      (LinearMap.range (φ ^ (n - 1))).comap (LinearMap.ker φ).subtype)) :
    ∀ (i : ℕ) (hi : i ≤ n),
      IsFiniteLength R
        ((twoPeriodicComplex (φ ^ i) (φ ^ (n - i))
          (by rw [← pow_add, Nat.add_sub_of_le hi, hnil])
          (by rw [← pow_add, Nat.sub_add_cancel hi, hnil])).homology (0 : ZMod 2)) ∧
      IsFiniteLength R
        ((twoPeriodicComplex (φ ^ i) (φ ^ (n - i))
          (by rw [← pow_add, Nat.add_sub_of_le hi, hnil])
          (by rw [← pow_add, Nat.sub_add_cancel hi, hnil])).homology (1 : ZMod 2)) ∧
      periodicLength
        (twoPeriodicComplex (φ ^ i) (φ ^ (n - i))
          (by rw [← pow_add, Nat.add_sub_of_le hi, hnil])
          (by rw [← pow_add, Nat.sub_add_cancel hi, hnil])) = 0 := by
  intro i hi
  have hbase := firstLayer_base_ne_top φ n hnpos hnil hfinite
  refine ⟨?_, ?_, periodicLength_powers_eq_zero_of_nilpotent φ n hnpos hnil hfinite i hi⟩
  · rw [← Module.length_ne_top_iff, length_homology_zero_twoPeriodicComplex_pow φ n hnil i hi]
    exact powerKer_quotient_length_ne_top φ n hnil hbase i (n - i) (Nat.add_sub_of_le hi)
  · rw [← Module.length_ne_top_iff, length_homology_one_twoPeriodicComplex_pow φ n hnil i hi]
    exact powerKer_quotient_length_ne_top φ n hnil hbase (n - i) i (Nat.sub_add_cancel hi)

end AlgebraicGeometry
