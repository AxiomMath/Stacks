module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.DividedPowers.Basic
public import Mathlib.RingTheory.DividedPowers.SubDPIdeal
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Ideal.NatInt
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.EvalFactorPow
public import StacksFrontier.RingTheory.DividedPowers.Criteria
public import StacksFrontier.RingTheory.DividedPowers.Ring

/-!
# Extending divided powers along a ring map: uniqueness and existence

Let `γ` be a divided power structure on an ideal `I` of a commutative ring `A` and let
`f : A → B` be a ring homomorphism. One says that `γ` *extends* along `f` when the ideal
`I B = I.map f` carries a divided power structure for which `f` is a divided power morphism.
Such an extension is unique when it exists, because two divided power structures on `I B`
making `f` a divided power morphism agree on the image of `I`, which generates `I B`. It need
not exist in general, but it does in three cases: when `I B = 0`, when `I` is principal, and
when `f` is flat.

The flat case is the substantial one. The generating function
`exp_γ(x) = ∑ₙ γₙ(x) Tⁿ` turns the additivity of the divided powers into multiplicativity,
and the equational criterion for flatness says that every relation `∑ bᵢ f(xᵢ) = 0` in `B` is
trivial, i.e. pulled back from a relation over `A`. Multiplicativity then forces the
corresponding product of generating functions to be `1`, so the coefficient-wise definition of
the extended operations does not depend on how an element of `I B` is written as a
`B`-combination of elements of `I`.

## Main definitions

* `DividedPowers.Extends` — the predicate that a divided power structure extends along a ring
  homomorphism.
* `DividedPowers.DividedPowerRing.extendedDividedPowersOfMapEqBotOrIsPrincipalOrFlat` — a
  chosen extension in the three cases above.

## Main results

* `DividedPowers.existsUnique_extension` — an extension, if it exists, is unique.
* `DividedPowers.DividedPowerRing.dividedPowers_extends_of_map_eq_bot_or_isPrincipal_or_flat` —
  existence of an extension when the mapped ideal is zero, the source ideal is principal, or
  the ring map is flat.

## Implementation notes

The extended ideal `I B` is Mathlib's `Ideal.map f I`, and flatness of a ring map is
`RingHom.Flat`. The three-case existence statement is phrased for the bundled
`DividedPowerRing`, and an extension is also chosen noncomputably so that later constructions
can use the extended divided powers as data.

## References

* [Stacks Project, Tag 07H0](https://stacks.math.columbia.edu/tag/07H0)
* [Stacks Project, Tag 07H1](https://stacks.math.columbia.edu/tag/07H1)
-/

@[expose] public section

namespace DividedPowers


/-- A divided power structure `γ` on `I` extends along `f : A →+* B` if the extended ideal
`I.map f` admits a divided power structure making `f` a divided power morphism. -/
@[stacks 07H0]
public abbrev Extends
    {A B : Type*} [CommSemiring A] [CommSemiring B] {I : Ideal A}
    (γ : _root_.DividedPowers I) (f : A →+* B) : Prop :=
  ∃ δ : _root_.DividedPowers (I.map f), _root_.DividedPowers.IsDPMorphism γ δ f

/-- If a divided power structure extends along a ring homomorphism, the divided power structure
on the extended ideal making that homomorphism a divided power morphism is unique. -/
@[stacks 07H1 "uniqueness"]
public lemma existsUnique_extension {A B : Type*} [CommSemiring A] [CommSemiring B]
    {I : Ideal A} (γ : _root_.DividedPowers I) (f : A →+* B)
    (h : Extends γ f) :
    ∃! δ : _root_.DividedPowers (I.map f),
      _root_.DividedPowers.IsDPMorphism γ δ f := by
  rcases h with ⟨δ, hδ⟩
  exact ⟨δ, hδ, fun δ' hδ' ↦ _root_.DividedPowers.ext δ' δ (fun n x hx ↦
    ((_root_.DividedPowers.mem_dpEqualizer_iff δ' δ).mp
      (_root_.DividedPowers.le_equalizer_of_isDPMorphism γ f le_rfl δ' δ hδ' hδ hx)).2 n)⟩

section Existence

universe u v

/-- The image under a ring map of the product rule for divided powers. -/
private lemma map_dpow_mul_dpow {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S) {x : R} (hx : x ∈ I) (m n : ℕ) :
    f (γ.dpow m x) * f (γ.dpow n x) = (Nat.choose (m + n) m : S) * f (γ.dpow (m + n) x) := by
  rw [← f.map_mul, γ.mul_dpow hx, f.map_mul, map_natCast]

/-- The image under a ring map of the composition rule for divided powers. -/
private lemma map_dpow_comp {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S) {x : R} (hx : x ∈ I)
    {m n : ℕ} (hn : n ≠ 0) :
    f (γ.dpow m (γ.dpow n x)) = (Nat.uniformBell m n : S) * f (γ.dpow (m * n) x) := by
  rw [γ.dpow_comp hn hx, f.map_mul, map_natCast]

private lemma pow_mul_eq_of_mul_eq {R : Type*} [CommRing R] (a b x : R) (n : ℕ)
    (h : a * x = b * x) : a ^ n * x = b ^ n * x := by
  have hsub : (a - b) * x = 0 := by rw [sub_mul, h, sub_self]
  obtain ⟨d, hd⟩ := sub_dvd_pow_sub_pow a b n
  have hp : (a ^ n - b ^ n) * x = 0 := by
    rw [hd, mul_assoc, mul_comm d x, ← mul_assoc, hsub, zero_mul]
  rwa [sub_mul, sub_eq_zero] at hp

private lemma principal_dpow_coefficient_eq {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S)
    {x : R} (hI : I = Ideal.span {x}) (hx : x ∈ I)
    {b c : S} (h : b * f x = c * f x) (n : ℕ) :
    b ^ n * f (γ.dpow n x) = c ^ n * f (γ.dpow n x) := by
  by_cases hn : n = 0
  · simp [hn]
  · have hmem := γ.dpow_mem hn hx
    have hmem' : γ.dpow n x ∈ Ideal.span {x} := (le_of_eq hI) hmem
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hmem'
    rw [← hd, f.map_mul]
    calc
      b ^ n * (f d * f x) = f d * (b ^ n * f x) := by ring
      _ = f d * (c ^ n * f x) := by rw [pow_mul_eq_of_mul_eq b c (f x) n h]
      _ = c ^ n * (f d * f x) := by ring

private lemma map_principal_ideal {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {I : Ideal R} {x : R} (hI : I = Ideal.span {x}) :
    I.map f = Ideal.span {f x} := by
  rw [hI, Ideal.map_span]
  simp

/-- Every element of the extension of a principal ideal is a multiple of the image of the
generator. -/
private lemma exists_mul_generator_of_mem_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {I : Ideal R} {x : R} (hI : I = Ideal.span {x})
    {y : S} (hy : y ∈ I.map f) : ∃ b, b * f x = y :=
  Ideal.mem_span_singleton'.mp ((le_of_eq (map_principal_ideal f hI)) hy)

private noncomputable def principalCoefficient {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {I : Ideal R} {x : R} (hI : I = Ideal.span {x})
    (y : S) (hy : y ∈ I.map f) : S :=
  Classical.choose (exists_mul_generator_of_mem_map f hI hy)

private lemma principalCoefficient_mul {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {I : Ideal R} {x : R} (hI : I = Ideal.span {x})
    (y : S) (hy : y ∈ I.map f) :
    principalCoefficient f hI y hy * f x = y :=
  Classical.choose_spec (exists_mul_generator_of_mem_map f hI hy)

private noncomputable def principalDpow {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S)
    {x : R} (hI : I = Ideal.span {x}) (n : ℕ) (y : S) : S :=
  open scoped Classical in if hy : y ∈ I.map f then
    (principalCoefficient f hI y hy) ^ n * f (γ.dpow n x)
  else 0

private lemma principalDpow_mul_generator {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S)
    {x : R} (hI : I = Ideal.span {x}) (hx : x ∈ I)
    (n : ℕ) (b : S) :
    principalDpow γ f hI n (b * f x) = b ^ n * f (γ.dpow n x) := by
  have hy : b * f x ∈ I.map f := by
    rw [map_principal_ideal f hI]
    exact Ideal.mem_span_singleton'.mpr ⟨b, rfl⟩
  simp only [principalDpow, dite_eq_left hy]
  exact principal_dpow_coefficient_eq γ f hI hx
    (principalCoefficient_mul f hI (b * f x) hy) n

private lemma principalDpow_zero {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S)
    {x : R} (hI : I = Ideal.span {x}) (hx : x ∈ I)
    {y : S} (hy : y ∈ I.map f) : principalDpow γ f hI 0 y = 1 := by
  obtain ⟨b, rfl⟩ := exists_mul_generator_of_mem_map f hI hy
  simp [principalDpow_mul_generator γ f hI hx, γ.dpow_zero hx]

private lemma principalDpow_one {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S)
    {x : R} (hI : I = Ideal.span {x}) (hx : x ∈ I)
    {y : S} (hy : y ∈ I.map f) : principalDpow γ f hI 1 y = y := by
  obtain ⟨b, rfl⟩ := exists_mul_generator_of_mem_map f hI hy
  simp [principalDpow_mul_generator γ f hI hx, γ.dpow_one hx]

private lemma principalDpow_mul {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S)
    {x : R} (hI : I = Ideal.span {x}) (hx : x ∈ I)
    {y : S} (hy : y ∈ I.map f) (a : S) (n : ℕ) :
    principalDpow γ f hI n (a * y) = a ^ n * principalDpow γ f hI n y := by
  obtain ⟨b, rfl⟩ := exists_mul_generator_of_mem_map f hI hy
  rw [← mul_assoc, principalDpow_mul_generator γ f hI hx,
    principalDpow_mul_generator γ f hI hx, mul_pow]
  ring

private lemma principalDpow_mem {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S)
    {x : R} (hI : I = Ideal.span {x})
    {n : ℕ} (hn : n ≠ 0) {y : S} (hy : y ∈ I.map f) :
    principalDpow γ f hI n y ∈ I.map f := by
  simp only [principalDpow, dite_eq_left hy]
  exact (I.map f).mul_mem_left _ (Ideal.mem_map_of_mem f (γ.dpow_mem hn
    (hI ▸ Ideal.mem_span_singleton_self x)))

private noncomputable def flatTerm {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S)
    (x : R) (b : S) : PowerSeries S :=
  PowerSeries.rescale b ((γ.exp x).map f)

private lemma flatTerm_coeff {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S)
    (x : R) (b : S) (n : ℕ) :
    PowerSeries.coeff n (flatTerm γ f x b) = b ^ n * f (γ.dpow n x) := by
  simp [flatTerm, _root_.DividedPowers.exp]

private lemma flatTerm_add {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S)
    {x : R} (hx : x ∈ I) (b c : S) :
    flatTerm γ f x (b + c) = flatTerm γ f x b * flatTerm γ f x c := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_mul, flatTerm_coeff]
  simp_rw [flatTerm_coeff]
  calc
    (b + c) ^ n * f (γ.dpow n x) =
        ((Finset.antidiagonal n).sum fun k ↦
          Nat.choose n k.1 • (b ^ k.1 * c ^ k.2)) * f (γ.dpow n x) := by
      rw [(Commute.all b c).add_pow' n]
    _ = (Finset.antidiagonal n).sum (fun k ↦
        (b ^ k.1 * f (γ.dpow k.1 x)) * (c ^ k.2 * f (γ.dpow k.2 x))) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k.1 + k.2 = n := Finset.mem_antidiagonal.mp hk
      rw [← hk', nsmul_eq_mul]
      linear_combination (b ^ k.1 * c ^ k.2) * (map_dpow_mul_dpow γ f hx k.1 k.2).symm

private lemma principalDpow_add {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S)
    {x : R} (hI : I = Ideal.span {x}) (hx : x ∈ I)
    {n : ℕ} {y z : S} (hy : y ∈ I.map f) (hz : z ∈ I.map f) :
    principalDpow γ f hI n (y + z) =
      (Finset.antidiagonal n).sum fun k ↦
        principalDpow γ f hI k.1 y * principalDpow γ f hI k.2 z := by
  obtain ⟨b, rfl⟩ := exists_mul_generator_of_mem_map f hI hy
  obtain ⟨c, rfl⟩ := exists_mul_generator_of_mem_map f hI hz
  rw [← add_mul, principalDpow_mul_generator γ f hI hx]
  simp_rw [principalDpow_mul_generator γ f hI hx]
  have h := congrArg (PowerSeries.coeff n) (flatTerm_add γ f hx b c)
  rw [flatTerm_coeff, PowerSeries.coeff_mul] at h
  simpa only [flatTerm_coeff] using h

private lemma principalDpow_mul_dpow {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S)
    {x : R} (hI : I = Ideal.span {x}) (hx : x ∈ I)
    {m n : ℕ} {y : S} (hy : y ∈ I.map f) :
    principalDpow γ f hI m y * principalDpow γ f hI n y =
      (Nat.choose (m + n) m : S) * principalDpow γ f hI (m + n) y := by
  obtain ⟨b, rfl⟩ := exists_mul_generator_of_mem_map f hI hy
  simp only [principalDpow_mul_generator γ f hI hx]
  linear_combination b ^ m * b ^ n * map_dpow_mul_dpow γ f hx m n

private lemma principalDpow_comp {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S)
    {x : R} (hI : I = Ideal.span {x}) (hx : x ∈ I)
    {m n : ℕ} (hn : n ≠ 0) {y : S} (hy : y ∈ I.map f) :
    principalDpow γ f hI m (principalDpow γ f hI n y) =
      (Nat.uniformBell m n : S) * principalDpow γ f hI (m * n) y := by
  obtain ⟨b, rfl⟩ := exists_mul_generator_of_mem_map f hI hy
  have hmem : γ.dpow n x ∈ Ideal.span {x} := hI ▸ γ.dpow_mem hn hx
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hmem
  have htarget : (f d) ^ m * f (γ.dpow m x) =
      (Nat.uniformBell m n : S) * f (γ.dpow (m * n) x) := by
    rw [← map_dpow_comp γ f hx hn, ← hd, γ.dpow_mul hx, f.map_mul, f.map_pow]
  rw [principalDpow_mul_generator γ f hI hx n b, ← hd, f.map_mul]
  have hre : b ^ n * (f d * f x) = (b ^ n * f d) * f x := by ring
  rw [hre, principalDpow_mul_generator γ f hI hx,
    principalDpow_mul_generator γ f hI hx]
  calc
    (b ^ n * f d) ^ m * f (γ.dpow m x) =
        b ^ (m * n) * ((f d) ^ m * f (γ.dpow m x)) := by
      rw [mul_pow, ← pow_mul]
      ring
    _ = (Nat.uniformBell m n : S) *
        (b ^ (m * n) * f (γ.dpow (m * n) x)) := by rw [htarget]; ring

private noncomputable def principalDividedPowers {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S)
    {x : R} (hI : I = Ideal.span {x}) : _root_.DividedPowers (I.map f) :=
  have hx : x ∈ I := hI ▸ Ideal.mem_span_singleton_self x
  { dpow := principalDpow γ f hI
    dpow_null := fun hy ↦ by simp [principalDpow, hy]
    dpow_zero := principalDpow_zero γ f hI hx
    dpow_one := principalDpow_one γ f hI hx
    dpow_mem := fun hn hy ↦ principalDpow_mem γ f hI hn hy
    dpow_add := principalDpow_add γ f hI hx
    dpow_mul := fun hy ↦ principalDpow_mul γ f hI hx hy _ _
    mul_dpow := principalDpow_mul_dpow γ f hI hx
    dpow_comp := fun hn hy ↦ principalDpow_comp γ f hI hx hn hy }

private lemma flatTerm_smul {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S)
    {x : R} (hx : x ∈ I) (a : R) (b : S) :
    flatTerm γ f (a * x) b = flatTerm γ f x (f a * b) := by
  apply PowerSeries.ext
  intro n
  simp only [flatTerm_coeff, γ.dpow_mul hx, f.map_mul, f.map_pow, mul_pow]
  ring

private lemma flatTerm_zero {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S)
    {x : R} (hx : x ∈ I) : flatTerm γ f x 0 = 1 := by
  apply PowerSeries.ext
  intro n
  rw [flatTerm_coeff, PowerSeries.coeff_one]
  by_cases hn : n = 0
  · simp [hn, γ.dpow_zero hx]
  · simp [hn]

private lemma flatTerm_add_source {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S)
    {x y : R} (hx : x ∈ I) (hy : y ∈ I) (b : S) :
    flatTerm γ f (x + y) b = flatTerm γ f x b * flatTerm γ f y b := by
  simp only [flatTerm, γ.exp_add hx hy, map_mul, map_mul]

private lemma flatTerm_zero_source {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S) (b : S) :
    flatTerm γ f 0 b = 1 := by
  apply PowerSeries.ext
  intro n
  rw [flatTerm_coeff, PowerSeries.coeff_one]
  by_cases hn : n = 0
  · simp [hn, γ.dpow_zero I.zero_mem]
  · simp [hn, γ.dpow_eval_zero hn]

private lemma flatTerm_sum_coeff {R S ι : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S)
    {x : R} (hx : x ∈ I) (s : Finset ι) (c : ι → S) :
    flatTerm γ f x (∑ j ∈ s, c j) = ∏ j ∈ s, flatTerm γ f x (c j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [flatTerm_zero γ f hx]
  | @insert j s hjs ih =>
    rw [Finset.sum_insert hjs, Finset.prod_insert hjs, flatTerm_add γ f hx, ih]

private lemma flatTerm_sum_source {R S ι : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S)
    (s : Finset ι) (a : ι → R) (hx : ∀ i ∈ s, a i ∈ I) (b : S) :
    flatTerm γ f (∑ i ∈ s, a i) b = ∏ i ∈ s, flatTerm γ f (a i) b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [flatTerm_zero_source γ f b]
  | @insert i s his ih =>
    rw [Finset.sum_insert his, Finset.prod_insert his,
      flatTerm_add_source γ f (hx i (Finset.mem_insert_self ..))
        (I.sum_mem (fun j hj ↦ hx j (Finset.mem_insert_of_mem hj))) b]
    rw [ih (fun j hj ↦ hx j (Finset.mem_insert_of_mem hj))]

private lemma flatTerm_substitution {R S ι κ : Type*} [CommRing R] [CommRing S]
    [Fintype ι] [Fintype κ]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S)
    (x : ι → R) (hx : ∀ i, x i ∈ I) (a : ι → κ → R) (c : κ → S) :
    (∏ i, flatTerm γ f (x i) (∑ j, f (a i j) * c j)) =
      ∏ j, flatTerm γ f (∑ i, a i j * x i) (c j) := by
  classical
  simp_rw [flatTerm_sum_coeff γ f (hx _) Finset.univ]
  simp_rw [← flatTerm_smul γ f (hx _)]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro j hj
  rw [flatTerm_sum_source γ f Finset.univ (fun i ↦ a i j * x i)
    (fun i hi ↦ I.mul_mem_left _ (hx i))]

private lemma flatTerm_product_eq_one_of_relation
    {R S ι : Type*} [CommRing R] [CommRing S] [Fintype ι]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S) (hf : f.Flat)
    (x : ι → R) (hx : ∀ i, x i ∈ I) (b : ι → S)
    (hrel : ∑ i, b i * f (x i) = 0) :
    (∏ i, flatTerm γ f (x i) (b i)) = 1 := by
  let algS : Algebra R S := f.toAlgebra
  have : Module.Flat R S := hf
  have hrel' : ∑ i, x i • b i = 0 := by
    simpa only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_comm] using hrel
  obtain ⟨k, a, c, hb, ha⟩ :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R) (M := S) hrel'
  have hmat := flatTerm_substitution γ f x hx a c
  have hb' : ∀ i, b i = ∑ j, f (a i j) * c j := by
    intro i
    simpa only [Algebra.smul_def, RingHom.algebraMap_toAlgebra] using hb i
  simp_rw [← hb'] at hmat
  rw [hmat]
  have hy : ∀ j, (∑ i, a i j * x i) = 0 := by
    intro j
    simpa only [mul_comm] using ha j
  simp_rw [hy, flatTerm_zero_source γ f, Finset.prod_const_one]

private def flatEval {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (f : R →+* S) (p : I →₀ S) : S :=
  p.sum fun x b ↦ b * f x.1

private noncomputable def flatExp {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S)
    (p : I →₀ S) : PowerSeries S :=
  p.prod fun x b ↦ flatTerm γ f x.1 b

private lemma flatEval_add {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (f : R →+* S) (p q : I →₀ S) :
    flatEval f (p + q) = flatEval f p + flatEval f q := by
  simp only [flatEval]
  apply Finsupp.sum_add_index'
  · intro a
    simp
  · intro a b c
    ring

private lemma flatExp_add {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S)
    (p q : I →₀ S) : flatExp γ f (p + q) = flatExp γ f p * flatExp γ f q :=
  Finsupp.prod_add_index' (fun a ↦ flatTerm_zero γ f a.property)
    (fun a b c ↦ flatTerm_add γ f a.property b c)

private lemma flatEval_zero {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (f : R →+* S) : flatEval f (0 : I →₀ S) = 0 := by
  simp [flatEval]

private lemma flatExp_zero {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S) :
    flatExp γ f (0 : I →₀ S) = 1 := by
  simp [flatExp]

private lemma flatExp_eq_one_of_eval_eq_zero {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S) (hf : f.Flat)
    (p : I →₀ S) (hp : flatEval f p = 0) : flatExp γ f p = 1 := by
  classical
  let s := p.support
  have hrel : ∑ i : s, p i.1 * f i.1.1 = 0 := by
    change (∑ i ∈ p.support, p i * f i.1) = 0 at hp
    exact (Finset.sum_attach p.support (fun i : I ↦ p i * f i.1)).trans hp
  show (∏ i ∈ p.support, flatTerm γ f i.1 (p i)) = 1
  exact (Finset.prod_attach p.support (fun i : I ↦ flatTerm γ f i.1 (p i))).symm.trans
    (flatTerm_product_eq_one_of_relation γ f hf
      (fun i : s ↦ i.1.1) (fun i ↦ i.1.2) (fun i : s ↦ p i.1) hrel)

private lemma flatExp_eq_of_eval_eq {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S) (hf : f.Flat)
    (p q : I →₀ S) (hpq : flatEval f p = flatEval f q) :
    flatExp γ f p = flatExp γ f q := by
  have hzero : flatEval f (p - q) = 0 := by
    rw [sub_eq_add_neg, flatEval_add]
    have hneg : flatEval f (-q) = -flatEval f q := by
      have hh : flatEval f q + flatEval f (-q) = 0 := by
        simpa only [add_neg_cancel, flatEval_zero] using
          (flatEval_add f q (-q)).symm
      exact add_left_cancel (hh.trans (add_neg_cancel (flatEval f q)).symm)
    rw [hneg, hpq, add_neg_cancel]
  have hExp := flatExp_eq_one_of_eval_eq_zero γ f hf (p - q) hzero
  rw [sub_eq_add_neg, flatExp_add] at hExp
  have hq : flatExp γ f q * flatExp γ f (-q) = 1 := by
    simpa only [add_neg_cancel, flatExp_zero] using (flatExp_add γ f q (-q)).symm
  calc
    flatExp γ f p = flatExp γ f p * (flatExp γ f q * flatExp γ f (-q)) := by
      rw [hq, mul_one]
    _ = flatExp γ f q * (flatExp γ f p * flatExp γ f (-q)) := by ring
    _ = flatExp γ f q := by rw [hExp, mul_one]

private lemma map_eq_span_range {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (f : R →+* S) :
    I.map f = Ideal.span (Set.range (fun x : I ↦ f x.1)) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact Ideal.subset_span ⟨⟨x, hx⟩, rfl⟩
  · rw [Ideal.span_le]
    rintro y ⟨x, rfl⟩
    exact Ideal.mem_map_of_mem f x.property

private lemma flatEval_exists {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (f : R →+* S) {y : S} (hy : y ∈ I.map f) :
    ∃ p : I →₀ S, flatEval f p = y := by
  rw [map_eq_span_range f] at hy
  obtain ⟨p, hp⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hy
  refine ⟨p, ?_⟩
  simpa only [flatEval, smul_eq_mul] using hp

private noncomputable def flatChoice {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (f : R →+* S) (y : S) (hy : y ∈ I.map f) : I →₀ S :=
  Classical.choose (flatEval_exists f hy)

private lemma flatChoice_eval {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (f : R →+* S) (y : S) (hy : y ∈ I.map f) :
    flatEval f (flatChoice f y hy) = y :=
  Classical.choose_spec (flatEval_exists f hy)

private noncomputable def flatDpow {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S) (_hf : f.Flat)
    (n : ℕ) (y : S) : S :=
  open scoped Classical in if hy : y ∈ I.map f then
    PowerSeries.coeff n (flatExp γ f (flatChoice f y hy))
  else 0

private lemma flatDpow_eq_coeff {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S) (hf : f.Flat)
    (n : ℕ) {y : S} (hy : y ∈ I.map f) (p : I →₀ S)
    (hp : flatEval f p = y) :
    flatDpow γ f hf n y = PowerSeries.coeff n (flatExp γ f p) := by
  simp only [flatDpow, dite_eq_left hy]
  exact congrArg (PowerSeries.coeff n)
    (flatExp_eq_of_eval_eq γ f hf _ p ((flatChoice_eval f y hy).trans hp.symm))

private lemma flatExp_single {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S)
    (x : I) (b : S) :
    flatExp γ f (Finsupp.single x b) = flatTerm γ f x.1 b :=
  Finsupp.prod_single_index (flatTerm_zero γ f x.property)

private lemma flatEval_single {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (f : R →+* S) (x : I) (b : S) :
    flatEval f (Finsupp.single x b) = b * f x.1 := by
  simp [flatEval]

private lemma flatExp_coeff_zero {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S)
    (p : I →₀ S) : PowerSeries.coeff 0 (flatExp γ f p) = 1 := by
  induction p using Finsupp.induction_linear with
  | zero => simp [flatExp_zero]
  | add p q hp hq =>
      rw [flatExp_add, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hp, hq, one_mul]
  | single x b =>
      rw [flatExp_single, flatTerm_coeff]
      simp [γ.dpow_zero x.property]

private lemma flatExp_coeff_one {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S)
    (p : I →₀ S) : PowerSeries.coeff 1 (flatExp γ f p) = flatEval f p := by
  induction p using Finsupp.induction_linear with
  | zero => simp [flatExp_zero, flatEval_zero]
  | add p q hp hq =>
      rw [flatExp_add, PowerSeries.coeff_one_mul,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        flatExp_coeff_zero, flatExp_coeff_zero, hp, hq, mul_one, mul_one,
        flatEval_add]
  | single x b =>
      rw [flatExp_single, flatTerm_coeff, flatEval_single]
      simp [γ.dpow_one x.property]

private lemma flatDpow_on_image {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S) (hf : f.Flat)
    (n : ℕ) {x : R} (hx : x ∈ I) :
    flatDpow γ f hf n (f x) = f (γ.dpow n x) := by
  let xI : I := ⟨x, hx⟩
  have heval : flatEval f (Finsupp.single xI 1) = f x := by
    rw [flatEval_single, one_mul]
  rw [flatDpow_eq_coeff γ f hf n (Ideal.mem_map_of_mem f hx)
    (Finsupp.single xI 1) heval, flatExp_single, flatTerm_coeff]
  simp [xI]

private lemma flatTerm_rescale {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S)
    (x : R) (a b : S) :
    flatTerm γ f x (a * b) = PowerSeries.rescale a (flatTerm γ f x b) := by
  apply PowerSeries.ext
  intro n
  simp only [flatTerm_coeff, PowerSeries.coeff_rescale, mul_pow]
  ring

private lemma flatEval_smul {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (f : R →+* S) (a : S) (p : I →₀ S) :
    flatEval f (a • p) = a * flatEval f p := by
  induction p using Finsupp.induction_linear with
  | zero => simp [flatEval_zero]
  | add p q hp hq =>
      rw [smul_add, flatEval_add, hp, hq, flatEval_add, mul_add]
  | single x b =>
      rw [Finsupp.smul_single, flatEval_single, flatEval_single]
      simp [smul_eq_mul, mul_assoc]

private lemma flatExp_smul {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S)
    (a : S) (p : I →₀ S) :
    flatExp γ f (a • p) = PowerSeries.rescale a (flatExp γ f p) := by
  induction p using Finsupp.induction_linear with
  | zero => simp [flatExp_zero]
  | add p q hp hq =>
      rw [smul_add, flatExp_add, hp, hq, flatExp_add, map_mul]
  | single x b =>
      rw [Finsupp.smul_single, flatExp_single, flatExp_single]
      exact flatTerm_rescale γ f x.1 a b

private lemma flatExp_coeff_mem {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S)
    (p : I →₀ S) {n : ℕ} (hn : n ≠ 0) :
    PowerSeries.coeff n (flatExp γ f p) ∈ I.map f := by
  induction p using Finsupp.induction_linear generalizing n with
  | zero => simp [flatExp_zero, hn]
  | add p q hp hq =>
      rw [flatExp_add, PowerSeries.coeff_mul]
      apply (I.map f).sum_mem
      intro k hk
      have hk' : k.1 + k.2 = n := Finset.mem_antidiagonal.mp hk
      by_cases h₁ : k.1 = 0
      · have h₂ : k.2 ≠ 0 := by omega
        exact (I.map f).mul_mem_left _ (hq h₂)
      · exact (I.map f).mul_mem_right _ (hp h₁)
  | single x b =>
      rw [flatExp_single, flatTerm_coeff]
      exact (I.map f).mul_mem_left _ (Ideal.mem_map_of_mem f (γ.dpow_mem hn x.property))

private lemma flatDpow_zero {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S) (hf : f.Flat)
    {y : S} (hy : y ∈ I.map f) : flatDpow γ f hf 0 y = 1 := by
  simp only [flatDpow, dite_eq_left hy]
  exact flatExp_coeff_zero γ f _

private lemma flatDpow_one {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S) (hf : f.Flat)
    {y : S} (hy : y ∈ I.map f) : flatDpow γ f hf 1 y = y := by
  simp only [flatDpow, dite_eq_left hy]
  rw [flatExp_coeff_one, flatChoice_eval]

private lemma flatDpow_mem {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S) (hf : f.Flat)
    {n : ℕ} (hn : n ≠ 0) {y : S} (hy : y ∈ I.map f) :
    flatDpow γ f hf n y ∈ I.map f := by
  simp only [flatDpow, dite_eq_left hy]
  exact flatExp_coeff_mem γ f _ hn

private lemma flatDpow_add {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S) (hf : f.Flat)
    {n : ℕ} {y z : S} (hy : y ∈ I.map f) (hz : z ∈ I.map f) :
    flatDpow γ f hf n (y + z) =
      (Finset.antidiagonal n).sum fun k ↦
        flatDpow γ f hf k.1 y * flatDpow γ f hf k.2 z := by
  let p := flatChoice f y hy
  let q := flatChoice f z hz
  have hp : flatEval f p = y := flatChoice_eval f y hy
  have hq : flatEval f q = z := flatChoice_eval f z hz
  have hsum : flatEval f (p + q) = y + z := by rw [flatEval_add, hp, hq]
  rw [flatDpow_eq_coeff γ f hf n ((I.map f).add_mem hy hz) (p + q) hsum,
    flatExp_add, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [flatDpow_eq_coeff γ f hf k.1 hy p hp,
    flatDpow_eq_coeff γ f hf k.2 hz q hq]

private lemma flatDpow_mul {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S) (hf : f.Flat)
    {n : ℕ} {y : S} (hy : y ∈ I.map f) (a : S) :
    flatDpow γ f hf n (a * y) = a ^ n * flatDpow γ f hf n y := by
  let p := flatChoice f y hy
  have hp : flatEval f p = y := flatChoice_eval f y hy
  have hsmul : flatEval f (a • p) = a * y := by rw [flatEval_smul, hp]
  rw [flatDpow_eq_coeff γ f hf n ((I.map f).mul_mem_left a hy) (a • p) hsmul,
    flatExp_smul, PowerSeries.coeff_rescale,
    flatDpow_eq_coeff γ f hf n hy p hp]

private lemma flatDpow_mul_dpow_on_image {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S) (hf : f.Flat)
    {m n : ℕ} {x : R} (hx : x ∈ I) :
    flatDpow γ f hf m (f x) * flatDpow γ f hf n (f x) =
      (Nat.choose (m + n) m : S) * flatDpow γ f hf (m + n) (f x) := by
  rw [flatDpow_on_image γ f hf m hx, flatDpow_on_image γ f hf n hx,
    flatDpow_on_image γ f hf (m + n) hx]
  exact map_dpow_mul_dpow γ f hx m n

private lemma flatDpow_comp_on_image {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S) (hf : f.Flat)
    {m n : ℕ} (hn : n ≠ 0) {x : R} (hx : x ∈ I) :
    flatDpow γ f hf m (flatDpow γ f hf n (f x)) =
      (Nat.uniformBell m n : S) * flatDpow γ f hf (m * n) (f x) := by
  rw [flatDpow_on_image γ f hf n hx,
    flatDpow_on_image γ f hf m (γ.dpow_mem hn hx),
    flatDpow_on_image γ f hf (m * n) hx]
  exact map_dpow_comp γ f hx hn

private lemma flatDividedPowers_exists {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (γ : _root_.DividedPowers I) (f : R →+* S) (hf : f.Flat) :
    ∃ δ : _root_.DividedPowers (I.map f),
      ∀ (n : ℕ) {y : S}, y ∈ I.map f → δ.dpow n y = flatDpow γ f hf n y := by
  apply exists_dividedPowers_of_axioms_on_generators
    (I.map f) (flatDpow γ f hf) (Set.range (fun x : I ↦ f x.1)) (map_eq_span_range f)
  · intro y hy
    exact flatDpow_zero γ f hf hy
  · intro y hy
    exact flatDpow_one γ f hf hy
  · intro n y hn hy
    exact flatDpow_mem γ f hf hn hy
  · intro n y z hy hz
    exact flatDpow_add γ f hf hy hz
  · intro n a y hy
    exact flatDpow_mul γ f hf hy a
  · intro m n y hy
    obtain ⟨⟨x, hx⟩, rfl⟩ := hy
    exact flatDpow_mul_dpow_on_image γ f hf hx
  · intro m n y hn hy
    obtain ⟨⟨x, hx⟩, rfl⟩ := hy
    exact flatDpow_comp_on_image γ f hf hn hx

/-- Divided powers extend along a ring homomorphism if the mapped ideal is zero, the source
ideal is principal, or the homomorphism is flat. -/
@[stacks 07H1 "existence"]
public theorem DividedPowerRing.dividedPowers_extends_of_map_eq_bot_or_isPrincipal_or_flat
    (A : DividedPowerRing.{u}) {B : Type v} [CommRing B] (f : A →+* B)
    (h : (A.ideal.map f = ⊥) ∨ A.ideal.IsPrincipal ∨ f.Flat) :
    Extends A.dividedPowers f := by
  rcases h with hzero | hprincipal | hflat
  · show ∃ δ : _root_.DividedPowers (A.ideal.map f),
      _root_.DividedPowers.IsDPMorphism A.dividedPowers δ f
    rw [hzero]
    have hvanish {x : A} (hx : x ∈ A.ideal) : f x = 0 :=
      Ideal.mem_bot.mp (hzero ▸ Ideal.mem_map_of_mem f hx)
    refine ⟨dividedPowersBot B, ?_⟩
    refine ⟨?_, ?_⟩
    · simp [hzero]
    · intro n a ha
      by_cases hn : n = 0
      · rw [hn, A.dividedPowers.dpow_zero ha, hvanish ha]
        simp [dividedPowersBot]
      · rw [hvanish ha, (dividedPowersBot B).dpow_eval_zero hn,
          hvanish (A.dividedPowers.dpow_mem hn ha)]
  · let _ : A.ideal.IsPrincipal := hprincipal
    let x : A := Submodule.IsPrincipal.generator A.ideal
    have hI : A.ideal = Ideal.span {x} := (Ideal.span_singleton_generator A.ideal).symm
    have hx : x ∈ A.ideal := hI ▸ Ideal.mem_span_singleton_self x
    refine ⟨principalDividedPowers A.dividedPowers f hI, ?_⟩
    apply _root_.DividedPowers.IsDPMorphism.on_span A.dividedPowers
      (principalDividedPowers A.dividedPowers f hI) hI
    · intro s hs
      rcases Set.mem_singleton_iff.mp hs with rfl
      exact Ideal.mem_map_of_mem f hx
    · intro n s hs
      rcases Set.mem_singleton_iff.mp hs with rfl
      show f (A.dividedPowers.dpow n x) = principalDpow A.dividedPowers f hI n (f x)
      simpa using (principalDpow_mul_generator A.dividedPowers f hI hx n 1).symm
  · obtain ⟨δ, hδ⟩ := flatDividedPowers_exists A.dividedPowers f hflat
    refine ⟨δ, ⟨le_refl _, ?_⟩⟩
    intro n a ha
    rw [hδ n (Ideal.mem_map_of_mem f ha)]
    exact flatDpow_on_image A.dividedPowers f hflat n ha

/-- A chosen divided power structure extending the divided powers on `A` when the mapped ideal
is zero, the source ideal is principal, or the ring homomorphism is flat. -/
public noncomputable def DividedPowerRing.extendedDividedPowersOfMapEqBotOrIsPrincipalOrFlat
    (A : DividedPowerRing.{u}) {B : Type v} [CommRing B] (f : A →+* B)
    (h : (A.ideal.map f = ⊥) ∨ A.ideal.IsPrincipal ∨ f.Flat) :
    _root_.DividedPowers (A.ideal.map f) :=
  Classical.choose (dividedPowers_extends_of_map_eq_bot_or_isPrincipal_or_flat A f h)

/-- The chosen divided powers on the mapped ideal make the original ring homomorphism a divided
power morphism. -/
@[stacks 07H1 "existence"]
public theorem
    DividedPowerRing.isDPMorphism_extendedDividedPowersOfMapEqBotOrIsPrincipalOrFlat
    (A : DividedPowerRing.{u}) {B : Type v} [CommRing B] (f : A →+* B)
    (h : (A.ideal.map f = ⊥) ∨ A.ideal.IsPrincipal ∨ f.Flat) :
    _root_.DividedPowers.IsDPMorphism A.dividedPowers
      (DividedPowerRing.extendedDividedPowersOfMapEqBotOrIsPrincipalOrFlat A f h) f :=
  Classical.choose_spec
    (DividedPowerRing.dividedPowers_extends_of_map_eq_bot_or_isPrincipal_or_flat A f h)

end Existence

end DividedPowers
