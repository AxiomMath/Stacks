module

public import Mathlib.Algebra.MvPolynomial.Counit
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.DividedPowers.Basic
public import Mathlib.RingTheory.DividedPowers.SubDPIdeal
public import Mathlib.RingTheory.GradedAlgebra.TensorProduct
public import Mathlib.RingTheory.RingHom.Flat
public import StacksFrontier.RingTheory.DividedPowers.Extend
public import StacksFrontier.RingTheory.DividedPowers.Ring
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Basic
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.FlatTensor.EvenSubalgebra
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.FlatTensor.EvenDividedPowers
import all StacksFrontier.RingTheory.DividedPowers.TateResolution.FlatTensor.EvenSubalgebra
import all StacksFrontier.RingTheory.DividedPowers.TateResolution.FlatTensor.EvenDividedPowers

/-!
# The divided power structure on the base-changed algebra

Products of two odd elements have vanishing higher divided powers after base change. This
assembles the divided power structure on `P ⊗[R] A` with the base-changed grading, proves its
compatibility with the base-changed differential, and concludes
`DividedPowers.TateResolution.exists_dividedPowerStructure_baseChange` (Stacks, Tag 09PL).
-/

@[expose] public section

namespace DividedPowers.TateResolution

open TensorProduct

universe u v w x y

private theorem oddProduct_mem_positiveEvenPart
    {R : Type u} {A : Type w}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    {d e : ℕ} {x y : A}
    (hx : x ∈ 𝒜 (2 * d + 1)) (hy : y ∈ 𝒜 (2 * e + 1)) :
    x * y ∈ positiveEvenPart 𝒜 := by
  have hxy := SetLike.mul_mem_graded hx hy
  have hdegree : (2 * d + 1) + (2 * e + 1) = 2 * (d + e + 1) := by lia
  exact Submodule.mem_iSup_of_mem (d + e) (hdegree ▸ hxy)

private theorem dividedPowers_dpow_add_eq_zero_of_mul_eq_zero
    {B : Type*} [CommRing B] {I : Ideal B}
    (δ : _root_.DividedPowers I)
    {a b : B} (ha : a ∈ I) (hb : b ∈ I)
    (hpa : ∀ n : ℕ, 1 < n → δ.dpow n a = 0)
    (hpb : ∀ n : ℕ, 1 < n → δ.dpow n b = 0)
    (hab : a * b = 0) (n : ℕ) (hn : 1 < n) :
    δ.dpow n (a + b) = 0 := by
  rw [δ.dpow_add ha hb]
  apply Finset.sum_eq_zero
  intro ij hij
  have hsum := Finset.mem_antidiagonal.mp hij
  by_cases hi : ij.1 = 0
  · have hj : 1 < ij.2 := by lia
    simp [hi, δ.dpow_zero ha, hpb ij.2 hj]
  by_cases hj : ij.2 = 0
  · have hi' : 1 < ij.1 := by lia
    simp [hj, δ.dpow_zero hb, hpa ij.1 hi']
  by_cases hi' : ij.1 = 1
  · by_cases hj' : ij.2 = 1
    · simp [hi', hj', δ.dpow_one ha, δ.dpow_one hb, hab]
    · have hj'' : 1 < ij.2 := by lia
      simp [hpb ij.2 hj'']
  · have hi'' : 1 < ij.1 := by lia
    simp [hpa ij.1 hi'']

private def oddProductEven
    {R : Type u} {A : Type w}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜]
    {d e : ℕ} (x y : A)
    (hx : x ∈ 𝒜 (2 * d + 1)) (hy : y ∈ 𝒜 (2 * e + 1)) :
    evenSubalgebra 𝒜 :=
  ⟨x * y, positiveEvenPart_le_evenPart 𝒜
    (oddProduct_mem_positiveEvenPart 𝒜 hx hy)⟩

private theorem oddProductEven_mem
    {R : Type u} {A : Type w}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜]
    {d e : ℕ} (x y : A)
    (hx : x ∈ 𝒜 (2 * d + 1)) (hy : y ∈ 𝒜 (2 * e + 1)) :
    oddProductEven 𝒜 x y hx hy ∈ positiveEvenIdeal 𝒜 :=
  oddProduct_mem_positiveEvenPart 𝒜 hx hy

private theorem odd_mul_eq_neg_mul
    {R : Type u} {A : Type w}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜]
    {d e : ℕ} {x y : A}
    (hx : x ∈ 𝒜 (2 * d + 1)) (hy : y ∈ 𝒜 (2 * e + 1)) :
    x * y = -(y * x) := by
  have hodd : Odd ((2 * d + 1) * (2 * e + 1)) :=
    (odd_two_mul_add_one d).mul (odd_two_mul_add_one e)
  simpa only [hodd.neg_one_pow, neg_one_smul] using IsStrictlyGradedComm.graded_comm hx hy

/-- For `x ∈ positiveEvenPart 𝒜`, `1 ⊗ₜ x` lies in the base-changed positive even part. -/
private theorem one_tmul_mem_positiveEvenPart_baseChange
    {R : Type u} {A : Type w} {P : Type v}
    [CommRing R] [Ring A] [Algebra R A] [CommRing P] [Algebra R P]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] {x : A} (hx : x ∈ positiveEvenPart 𝒜) :
    (1 : P) ⊗ₜ[R] x ∈ positiveEvenPart (fun i => (𝒜 i).baseChange P) := by
  rw [positiveEvenPart_baseChange]
  exact Submodule.tmul_mem_baseChange_of_mem 1 hx

private theorem dividedPowersOnBaseChangedEven_dpow_oddProduct_tmul
    {R : Type u} {A : Type w} {P : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜]
    [CommRing P] [Algebra R P]
    (γ : DividedPowerStructure 𝒜)
    (d e n : ℕ) (hn : 1 < n)
    (a b : A) (ha : a ∈ 𝒜 (2 * d + 1)) (hb : b ∈ 𝒜 (2 * e + 1))
    (p q : P)
    (z : evenSubalgebra (R := P) (fun i => (𝒜 i).baseChange P))
    (hz : (z : P ⊗[R] A) = (p ⊗ₜ[R] a) * (q ⊗ₜ[R] b)) :
    let 𝒜' : ℕ → Submodule P (P ⊗[R] A) := fun i => (𝒜 i).baseChange P
    letI : IsStrictlyGradedComm 𝒜' := strictlyGradedComm_baseChange 𝒜
    (dividedPowersOnBaseChangedEven 𝒜 (dividedPowersOnEven 𝒜 γ)).dpow n z = 0 := by
  intro 𝒜'
  let : IsStrictlyGradedComm 𝒜' := strictlyGradedComm_baseChange 𝒜
  let c := oddProductEven 𝒜 a b ha hb
  have hc0 : (dividedPowersOnEven 𝒜 γ).dpow n c = 0 :=
    Subtype.ext (γ.dpow_mul_odd hn ha hb)
  let E := evenSubalgebraTensorEquiv (P := P) 𝒜
  have hz' : z = E (c ⊗ₜ[R] (p * q)) := by
    apply Subtype.ext
    calc
      (z : P ⊗[R] A) = (p ⊗ₜ[R] a) * (q ⊗ₜ[R] b) := hz
      _ = (p * q) ⊗ₜ[R] (a * b) := Algebra.TensorProduct.tmul_mul_tmul p q a b
      _ = ((E (c ⊗ₜ[R] (p * q)) : evenSubalgebra 𝒜') : P ⊗[R] A) := by
        show (p * q) ⊗ₜ[R] (c : A) =
          ((evenSubalgebraTensorHom 𝒜 (c ⊗ₜ[R] (p * q)) :
            evenSubalgebra 𝒜') : P ⊗[R] A)
        exact (evenSubalgebraTensorHom_tmul 𝒜 c (p * q)).symm
  rw [hz']
  exact dividedPowersOnBaseChangedEven_dpow_tmul_of_zero 𝒜
    (dividedPowersOnEven 𝒜 γ) n c (oddProductEven_mem 𝒜 a b ha hb) hc0 (p * q)

private theorem oddProductEven_mul_eq_zero_of_same_left
    {R : Type u} {A : Type w}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜]
    {d e : ℕ} {x y z : A}
    (hx : x ∈ 𝒜 (2 * d + 1))
    (hy : y ∈ 𝒜 (2 * e + 1)) (hz : z ∈ 𝒜 (2 * e + 1)) :
    oddProductEven 𝒜 x y hx hy * oddProductEven 𝒜 x z hx hz = 0 := by
  apply Subtype.ext
  show (x * y) * (x * z) = 0
  have hcomm : y * x = -(x * y) := odd_mul_eq_neg_mul 𝒜 hy hx
  have hx2 := IsStrictlyGradedComm.odd_sq_zero hx
  calc
    (x * y) * (x * z) = x * (y * x) * z := by simp only [mul_assoc]
    _ = -(x * x) * (y * z) := by rw [hcomm]; simp only [mul_neg, neg_mul, mul_assoc]
    _ = 0 := by rw [← pow_two, hx2]; simp

/-- Membership in the span of the image of `p` under `m ↦ 1 ⊗ₜ m` gives membership in
`p.baseChange P`. -/
private theorem mem_baseChange_of_mem_span
    {R : Type u} {M : Type w} {P : Type v}
    [CommRing R] [AddCommGroup M] [Module R M] [CommRing P] [Algebra R P]
    (p : Submodule R M) {y : P ⊗[R] M}
    (hy : y ∈ Submodule.span P ((p.map (TensorProduct.mk R P M 1) : Submodule R _) : Set _)) :
    y ∈ p.baseChange P := by
  rwa [Submodule.baseChange_eq_span]

private theorem dividedPowers_oddProduct_right_span
    {R : Type u} {A : Type w} {P : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜]
    [CommRing P] [Algebra R P]
    [IsStrictlyGradedComm (fun i => (𝒜 i).baseChange P)]
    (δ : _root_.DividedPowers
      (positiveEvenIdeal (R := P) (fun i => (𝒜 i).baseChange P)))
    (d e : ℕ) (x : P ⊗[R] A)
    (hx : x ∈ (𝒜 (2 * d + 1)).baseChange P)
    (hpure : ∀ (b : A) (hb : b ∈ 𝒜 (2 * e + 1)) (p : P)
        (n : ℕ) (_hn : 1 < n),
      δ.dpow n (oddProductEven (fun i => (𝒜 i).baseChange P)
        x (p ⊗ₜ[R] b) hx (Submodule.tmul_mem_baseChange_of_mem p hb)) = 0)
    (y : P ⊗[R] A) (hy : y ∈ (𝒜 (2 * e + 1)).baseChange P)
    (n : ℕ) (hn : 1 < n) :
    δ.dpow n (oddProductEven (fun i => (𝒜 i).baseChange P) x y hx hy) = 0 := by
  let 𝒜' : ℕ → Submodule P (P ⊗[R] A) := fun i => (𝒜 i).baseChange P
  let : IsStrictlyGradedComm 𝒜' := strictlyGradedComm_baseChange 𝒜
  have H : ∀ y : P ⊗[R] A, (hy' : y ∈ 𝒜' (2 * e + 1)) →
      ∀ m : ℕ, 1 < m →
        δ.dpow m (oddProductEven 𝒜' x y hx hy') = 0 := by
    intro y hy'
    change y ∈ (𝒜 (2 * e + 1)).baseChange P at hy'
    rw [Submodule.baseChange_eq_span] at hy'
    induction hy' using Submodule.span_induction with
    | mem y hygen =>
        rcases hygen with ⟨b, hb, rfl⟩
        intro m hm
        exact hpure b hb 1 m hm
    | zero =>
        intro m hm
        have hzero : oddProductEven 𝒜' x 0 hx (𝒜' (2 * e + 1)).zero_mem = 0 :=
          Subtype.ext (mul_zero x)
        rw [hzero, δ.dpow_eval_zero (by lia)]
    | add y z hy hz ihy ihz =>
        intro m hm
        have hy' : y ∈ 𝒜' (2 * e + 1) := mem_baseChange_of_mem_span _ hy
        have hz' : z ∈ 𝒜' (2 * e + 1) := mem_baseChange_of_mem_span _ hz
        have hadd : oddProductEven 𝒜' x (y + z) hx
            ((𝒜' (2 * e + 1)).add_mem hy' hz') =
              oddProductEven 𝒜' x y hx hy' + oddProductEven 𝒜' x z hx hz' :=
          Subtype.ext (mul_add x y z)
        rw [hadd]
        apply dividedPowers_dpow_add_eq_zero_of_mul_eq_zero δ
          (oddProductEven_mem 𝒜' x y hx hy')
          (oddProductEven_mem 𝒜' x z hx hz')
        · exact fun k hk => ihy hy' k hk
        · exact fun k hk => ihz hz' k hk
        · exact oddProductEven_mul_eq_zero_of_same_left 𝒜' hx hy' hz'
        · exact hm
    | smul p y hy ih =>
        intro m hm
        have hy' : y ∈ 𝒜' (2 * e + 1) := mem_baseChange_of_mem_span _ hy
        have hsmul : oddProductEven 𝒜' x (p • y) hx
            ((𝒜' (2 * e + 1)).smul_mem p hy') =
              p • oddProductEven 𝒜' x y hx hy' :=
          Subtype.ext (mul_smul_comm p x y)
        rw [hsmul, Algebra.smul_def,
          δ.dpow_mul (oddProductEven_mem 𝒜' x y hx hy'), ih hy' m hm]
        simp
  exact H y hy n hn

private theorem dividedPowers_oddProduct_swap_zero
    {R : Type u} {A : Type w}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜]
    (δ : _root_.DividedPowers (positiveEvenIdeal 𝒜))
    {d e n : ℕ} {x y : A}
    (hx : x ∈ 𝒜 (2 * d + 1)) (hy : y ∈ 𝒜 (2 * e + 1))
    (hzero : δ.dpow n (oddProductEven 𝒜 y x hy hx) = 0) :
    δ.dpow n (oddProductEven 𝒜 x y hx hy) = 0 := by
  have hswap : oddProductEven 𝒜 x y hx hy =
      -(oddProductEven 𝒜 y x hy hx) := Subtype.ext (odd_mul_eq_neg_mul 𝒜 hx hy)
  rw [hswap, show -(oddProductEven 𝒜 y x hy hx) =
      (-1 : evenSubalgebra 𝒜) * oddProductEven 𝒜 y x hy hx by ring,
    δ.dpow_mul (oddProductEven_mem 𝒜 y x hy hx), hzero]
  simp

private theorem dividedPowersOnBaseChangedEven_dpow_oddProduct
    {R : Type u} {A : Type w} {P : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜]
    [CommRing P] [Algebra R P]
    (γ : DividedPowerStructure 𝒜)
    (d e n : ℕ) (hn : 1 < n)
    (x y : P ⊗[R] A)
    (hx : x ∈ (𝒜 (2 * d + 1)).baseChange P)
    (hy : y ∈ (𝒜 (2 * e + 1)).baseChange P) :
    let 𝒜' : ℕ → Submodule P (P ⊗[R] A) := fun i => (𝒜 i).baseChange P
    letI : IsStrictlyGradedComm 𝒜' := strictlyGradedComm_baseChange 𝒜
    (dividedPowersOnBaseChangedEven 𝒜 (dividedPowersOnEven 𝒜 γ)).dpow n
      (oddProductEven 𝒜' x y hx hy) = 0 := by
  intro 𝒜'
  let : IsStrictlyGradedComm 𝒜' := strictlyGradedComm_baseChange 𝒜
  let δ := dividedPowersOnBaseChangedEven (P := P) 𝒜 (dividedPowersOnEven 𝒜 γ)
  have hpure : ∀ (b : A) (hb : b ∈ 𝒜 (2 * e + 1)) (q : P)
      (m : ℕ) (hm : 1 < m),
      δ.dpow m (oddProductEven 𝒜' x (q ⊗ₜ[R] b) hx
        (Submodule.tmul_mem_baseChange_of_mem q hb)) = 0 := by
    intro b hb q m hm
    let z := q ⊗ₜ[R] b
    have hz : z ∈ 𝒜' (2 * e + 1) :=
      Submodule.tmul_mem_baseChange_of_mem q hb
    have hgen : ∀ (a : A) (ha : a ∈ 𝒜 (2 * d + 1)) (p : P)
        (k : ℕ) (hk : 1 < k),
        δ.dpow k (oddProductEven 𝒜' z (p ⊗ₜ[R] a) hz
          (Submodule.tmul_mem_baseChange_of_mem p ha)) = 0 :=
      fun a ha p k hk ↦ dividedPowersOnBaseChangedEven_dpow_oddProduct_tmul 𝒜 γ
        e d k hk b a hb ha q p _ rfl
    have hright := dividedPowers_oddProduct_right_span 𝒜 δ e d z hz
      hgen x hx m hm
    exact dividedPowers_oddProduct_swap_zero 𝒜' δ hx hz hright
  exact dividedPowers_oddProduct_right_span 𝒜 δ d e x hx hpure y hy n hn

private noncomputable def baseChangedGradedDpow
    {R : Type u} {A : Type w} {P : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜]
    [CommRing P] [Algebra R P]
    (γ : DividedPowerStructure 𝒜) (n : ℕ) (x : P ⊗[R] A) : P ⊗[R] A := by
  let 𝒜' : ℕ → Submodule P (P ⊗[R] A) := fun i => (𝒜 i).baseChange P
  letI : IsStrictlyGradedComm 𝒜' := strictlyGradedComm_baseChange 𝒜
  let δ := dividedPowersOnBaseChangedEven (P := P) 𝒜 (dividedPowersOnEven 𝒜 γ)
  classical
  exact if hx : x ∈ positiveEvenPart 𝒜' then
    ((δ.dpow n (⟨x, positiveEvenPart_le_evenPart 𝒜' hx⟩ :
      evenSubalgebra 𝒜') : evenSubalgebra 𝒜') : P ⊗[R] A)
  else 0

private theorem baseChangedGradedDpow_of_mem
    {R : Type u} {A : Type w} {P : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜]
    [CommRing P] [Algebra R P]
    (γ : DividedPowerStructure 𝒜) (n : ℕ) (x : P ⊗[R] A)
    (hx : x ∈ positiveEvenPart (fun i => (𝒜 i).baseChange P)) :
    let 𝒜' : ℕ → Submodule P (P ⊗[R] A) := fun i => (𝒜 i).baseChange P
    letI : IsStrictlyGradedComm 𝒜' := strictlyGradedComm_baseChange 𝒜
    baseChangedGradedDpow 𝒜 γ n x =
      (((dividedPowersOnBaseChangedEven 𝒜 (dividedPowersOnEven 𝒜 γ)).dpow n
        (⟨x, positiveEvenPart_le_evenPart 𝒜' hx⟩ : evenSubalgebra 𝒜') :
        evenSubalgebra 𝒜') : P ⊗[R] A) := by
  intro 𝒜'
  let : IsStrictlyGradedComm 𝒜' := strictlyGradedComm_baseChange 𝒜
  simp only [baseChangedGradedDpow, dite_eq_left hx]

private theorem baseChangedGradedDpow_of_not_mem
    {R : Type u} {A : Type w} {P : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜]
    [CommRing P] [Algebra R P]
    (γ : DividedPowerStructure 𝒜) (n : ℕ) (x : P ⊗[R] A)
    (hx : x ∉ positiveEvenPart (fun i => (𝒜 i).baseChange P)) :
    baseChangedGradedDpow 𝒜 γ n x = 0 := by
  simp only [baseChangedGradedDpow, dite_eq_right hx]

private noncomputable def dividedPowerStructureOnBaseChange
    {R : Type u} {A : Type w} {P : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜]
    [CommRing P] [Algebra R P]
    (γ : DividedPowerStructure 𝒜) :
    let 𝒜' : ℕ → Submodule P (P ⊗[R] A) := fun i => (𝒜 i).baseChange P
    letI : IsStrictlyGradedComm 𝒜' := strictlyGradedComm_baseChange 𝒜
    DividedPowerStructure 𝒜' := by
  intro 𝒜'
  letI : IsStrictlyGradedComm 𝒜' := strictlyGradedComm_baseChange 𝒜
  let δ := dividedPowersOnBaseChangedEven (P := P) 𝒜 (dividedPowersOnEven 𝒜 γ)
  refine {
    dpow := baseChangedGradedDpow 𝒜 γ
    dpow_null := ?_
    dpow_zero := ?_
    dpow_one := ?_
    dpow_mem := ?_
    dpow_mem_grade := ?_
    dpow_mul := ?_
    dpow_mul_even := ?_
    dpow_mul_odd := ?_
    dpow_add := ?_
    dpow_dpow := ?_ }
  · intro n x hx
    exact baseChangedGradedDpow_of_not_mem 𝒜 γ n x hx
  · intro x hx
    rw [baseChangedGradedDpow_of_mem 𝒜 γ 0 x hx]
    exact congrArg Subtype.val (δ.dpow_zero hx)
  · intro x hx
    rw [baseChangedGradedDpow_of_mem 𝒜 γ 1 x hx]
    exact congrArg Subtype.val (δ.dpow_one hx)
  · intro n x hn hx
    rw [baseChangedGradedDpow_of_mem 𝒜 γ n x hx]
    exact δ.dpow_mem hn hx
  · intro n d x hn hx hxgrade
    rw [baseChangedGradedDpow_of_mem 𝒜 γ n x hx]
    exact dividedPowersOnBaseChangedEven_dpow_mem_grade 𝒜 γ n d hn
      ⟨x, positiveEvenPart_le_evenPart 𝒜' hx⟩ hx hxgrade
  · intro m n x hx
    rw [baseChangedGradedDpow_of_mem 𝒜 γ n x hx,
      baseChangedGradedDpow_of_mem 𝒜 γ m x hx,
      baseChangedGradedDpow_of_mem 𝒜 γ (n + m) x hx]
    exact congrArg Subtype.val (δ.mul_dpow hx)
  · intro n x y hn hx hy
    have hxy : x * y ∈ positiveEvenPart 𝒜' :=
      evenPart_mul_positiveEvenPart 𝒜' hx hy
    let a : evenSubalgebra 𝒜' := ⟨x, hx⟩
    let b : evenSubalgebra 𝒜' := ⟨y, positiveEvenPart_le_evenPart 𝒜' hy⟩
    rw [baseChangedGradedDpow_of_mem 𝒜 γ n (x * y) hxy,
      baseChangedGradedDpow_of_mem 𝒜 γ n y hy]
    change ((δ.dpow n (a * b) : evenSubalgebra 𝒜') : P ⊗[R] A) =
      x ^ n * ((δ.dpow n b : evenSubalgebra 𝒜') : P ⊗[R] A)
    simpa only [Subalgebra.coe_mul, Subalgebra.coe_pow] using
      congrArg Subtype.val (δ.dpow_mul hy)
  · intro n d e x y hn hx hy
    have hxy : x * y ∈ positiveEvenPart 𝒜' :=
      oddProduct_mem_positiveEvenPart 𝒜' hx hy
    rw [baseChangedGradedDpow_of_mem 𝒜 γ n (x * y) hxy]
    exact congrArg Subtype.val
      (dividedPowersOnBaseChangedEven_dpow_oddProduct 𝒜 γ d e n hn x y hx hy)
  · intro n x y hx hy
    have hxy : x + y ∈ positiveEvenPart 𝒜' :=
      (positiveEvenPart 𝒜').add_mem hx hy
    let a : evenSubalgebra 𝒜' := ⟨x, positiveEvenPart_le_evenPart 𝒜' hx⟩
    let b : evenSubalgebra 𝒜' := ⟨y, positiveEvenPart_le_evenPart 𝒜' hy⟩
    rw [baseChangedGradedDpow_of_mem 𝒜 γ n (x + y) hxy]
    change ((δ.dpow n (a + b) : evenSubalgebra 𝒜') : P ⊗[R] A) = _
    rw [δ.dpow_add hx hy]
    simp only [AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul]
    refine Finset.sum_congr rfl fun ij _ ↦ ?_
    rw [baseChangedGradedDpow_of_mem 𝒜 γ ij.1 x hx,
      baseChangedGradedDpow_of_mem 𝒜 γ ij.2 y hy]
  · intro m n x hm hn hx
    have hinner : baseChangedGradedDpow 𝒜 γ m x ∈ positiveEvenPart 𝒜' := by
      rw [baseChangedGradedDpow_of_mem 𝒜 γ m x hx]
      exact δ.dpow_mem hm hx
    rw [baseChangedGradedDpow_of_mem 𝒜 γ n
      (baseChangedGradedDpow 𝒜 γ m x) hinner,
      baseChangedGradedDpow_of_mem 𝒜 γ (n * m) x hx]
    have hinner_eq :
        (⟨baseChangedGradedDpow 𝒜 γ m x,
          positiveEvenPart_le_evenPart 𝒜' hinner⟩ : evenSubalgebra 𝒜') =
          δ.dpow m (⟨x, positiveEvenPart_le_evenPart 𝒜' hx⟩ : evenSubalgebra 𝒜') :=
      Subtype.ext (baseChangedGradedDpow_of_mem 𝒜 γ m x hx)
    rw [hinner_eq]
    have hbell : Nat.uniformBell n m =
        (n * m).factorial / (n.factorial * m.factorial ^ n) := by
      rw [Nat.uniformBell_eq_div n hm]
      congr 1
      ac_rfl
    simpa only [Subalgebra.coe_mul, SubringClass.coe_natCast, hbell] using
      congrArg Subtype.val (δ.dpow_comp
        (m := n) (n := m)
        (x := (⟨x, positiveEvenPart_le_evenPart 𝒜' hx⟩ : evenSubalgebra 𝒜')) hm hx)

private theorem dividedPowerStructureOnBaseChange_dpow_tmul
    {R : Type u} {A : Type w} {P : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜]
    [CommRing P] [Algebra R P]
    (γ : DividedPowerStructure 𝒜)
    (n : ℕ) (x : A) (hx : x ∈ positiveEvenPart 𝒜) :
    let 𝒜' : ℕ → Submodule P (P ⊗[R] A) := fun i => (𝒜 i).baseChange P
    letI : IsStrictlyGradedComm 𝒜' := strictlyGradedComm_baseChange 𝒜
    (dividedPowerStructureOnBaseChange (P := P) 𝒜 γ).dpow n (1 ⊗ₜ[R] x) =
      1 ⊗ₜ[R] γ.dpow n x := by
  intro 𝒜'
  let : IsStrictlyGradedComm 𝒜' := strictlyGradedComm_baseChange 𝒜
  have hx' : (1 : P) ⊗ₜ[R] x ∈ positiveEvenPart 𝒜' :=
    one_tmul_mem_positiveEvenPart_baseChange 𝒜 hx
  show baseChangedGradedDpow (P := P) 𝒜 γ n (1 ⊗ₜ[R] x) = _
  rw [baseChangedGradedDpow_of_mem 𝒜 γ n (1 ⊗ₜ[R] x) hx']
  let b : evenSubalgebra 𝒜 :=
    ⟨x, positiveEvenPart_le_evenPart 𝒜 hx⟩
  have hb : b ∈ positiveEvenIdeal 𝒜 := hx
  let E := evenSubalgebraTensorEquiv (P := P) 𝒜
  have hE : E (b ⊗ₜ[R] (1 : P)) =
      (⟨1 ⊗ₜ[R] x, positiveEvenPart_le_evenPart 𝒜' hx'⟩ :
        evenSubalgebra 𝒜') :=
    Subtype.ext (evenSubalgebraTensorHom_tmul 𝒜 b 1)
  rw [← hE, dividedPowersOnBaseChangedEven_dpow_tmul_one 𝒜
    (dividedPowersOnEven 𝒜 γ) n b hb]
  show ((evenSubalgebraTensorHom 𝒜
    ((dividedPowersOnEven 𝒜 γ).dpow n b ⊗ₜ[R] (1 : P)) :
    evenSubalgebra 𝒜') : P ⊗[R] A) = 1 ⊗ₜ[R] γ.dpow n x
  simpa only [dividedPowersOnEven, evenDpow_coe] using
    evenSubalgebraTensorHom_tmul 𝒜 ((dividedPowersOnEven 𝒜 γ).dpow n b) 1

private theorem differential_mul_evenPart
    {R : Type u} {A : Type w}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (d : A →ₗ[R] A)
    (hd : ∀ (i j : ℕ) (x y : A), x ∈ 𝒜 i → y ∈ 𝒜 j →
      d (x * y) = d x * y + (-1 : R) ^ i • (x * d y))
    {x y : A} (hx : x ∈ evenPart 𝒜) (hy : y ∈ evenPart 𝒜) :
    d (x * y) = d x * y + x * d y := by
  change x ∈ (⨆ i : ℕ, 𝒜 (2 * i)) at hx
  change y ∈ (⨆ j : ℕ, 𝒜 (2 * j)) at hy
  rw [Submodule.iSup_eq_span] at hx hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      induction hy using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy
          have heven : Even (2 * i) := ⟨i, by lia⟩
          simpa only [heven.neg_one_pow, one_smul] using
            hd (2 * i) (2 * j) x y hi hj
      | zero => simp
      | add y z hy hz ihy ihz =>
          simp only [mul_add, map_add, ihy, ihz]
          abel
      | smul r y hy ih =>
          calc
            d (x * (r • y)) = r • d (x * y) := by rw [mul_smul_comm, map_smul]
            _ = r • (d x * y + x * d y) := by rw [ih]
            _ = d x * (r • y) + x * d (r • y) := by
              simp only [smul_add, mul_smul_comm, map_smul]
  | zero => simp
  | add x z hx hz ihx ihz =>
      simp only [add_mul, map_add, ihx, ihz]
      abel
  | smul r x hx ih =>
      calc
        d ((r • x) * y) = r • d (x * y) := by rw [smul_mul_assoc, map_smul]
        _ = r • (d x * y + x * d y) := by rw [ih]
        _ = d (r • x) * y + (r • x) * d y := by
          simp only [smul_add, smul_mul_assoc, map_smul]

private theorem dividedPowers_differential_add
    {R : Type u} {A : Type w}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜]
    (δ : _root_.DividedPowers (positiveEvenIdeal 𝒜))
    (d : A →ₗ[R] A)
    (hone : d 1 = 0)
    (hmul : ∀ {a b : A}, a ∈ evenPart 𝒜 → b ∈ evenPart 𝒜 →
      d (a * b) = d a * b + a * d b)
    (x y : evenSubalgebra 𝒜)
    (hxI : x ∈ positiveEvenIdeal 𝒜) (hyI : y ∈ positiveEvenIdeal 𝒜)
    (hx : ∀ k : ℕ, k ≠ 0 →
      d ((δ.dpow k x : evenSubalgebra 𝒜) : A) =
        d (x : A) * ((δ.dpow (k - 1) x : evenSubalgebra 𝒜) : A))
    (hy : ∀ k : ℕ, k ≠ 0 →
      d ((δ.dpow k y : evenSubalgebra 𝒜) : A) =
        d (y : A) * ((δ.dpow (k - 1) y : evenSubalgebra 𝒜) : A))
    (n : ℕ) :
    d ((δ.dpow (n + 1) (x + y) : evenSubalgebra 𝒜) : A) =
      d ((x + y : evenSubalgebra 𝒜) : A) *
        ((δ.dpow n (x + y) : evenSubalgebra 𝒜) : A) := by
  let F : ℕ → A := fun i => ((δ.dpow i x : evenSubalgebra 𝒜) : A)
  let G : ℕ → A := fun j => ((δ.dpow j y : evenSubalgebra 𝒜) : A)
  let S : ℕ → A := fun k => ∑ ij ∈ Finset.antidiagonal k, F ij.1 * G ij.2
  have hS (k : ℕ) : S k = ((δ.dpow k (x + y) : evenSubalgebra 𝒜) : A) := by
    dsimp only [S, F, G]
    simpa only [AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul] using
      (congrArg Subtype.val (δ.dpow_add hxI hyI)).symm
  have hF0 : F 0 = 1 := congrArg Subtype.val (δ.dpow_zero hxI)
  have hG0 : G 0 = 1 := congrArg Subtype.val (δ.dpow_zero hyI)
  have hFsucc (k : ℕ) : d (F (k + 1)) = d (x : A) * F k := by
    simpa only [F, Nat.add_sub_cancel_right] using hx (k + 1) (by lia)
  have hGsucc (k : ℕ) : d (G (k + 1)) = d (y : A) * G k := by
    simpa only [G, Nat.add_sub_cancel_right] using hy (k + 1) (by lia)
  have hfirst :
      (∑ ij ∈ Finset.antidiagonal (n + 1), d (F ij.1) * G ij.2) =
        d (x : A) * S n := by
    rw [Finset.Nat.sum_antidiagonal_succ]
    simp only [hF0, hone, zero_mul, zero_add, hFsucc]
    simp only [S, Finset.mul_sum, mul_assoc]
  have hsecond :
      (∑ ij ∈ Finset.antidiagonal (n + 1), F ij.1 * d (G ij.2)) =
        d (y : A) * S n := by
    rw [Finset.Nat.sum_antidiagonal_succ']
    simp only [hG0, hone, mul_zero, zero_add, hGsucc]
    calc
      (∑ ij ∈ Finset.antidiagonal n, F ij.1 * (d (y : A) * G ij.2)) =
          ∑ ij ∈ Finset.antidiagonal n, d (y : A) * (F ij.1 * G ij.2) := by
            apply Finset.sum_congr rfl
            intro ij hij
            have hc := evenPart_mul_comm 𝒜
              ((δ.dpow ij.1 x : evenSubalgebra 𝒜).property) (d (y : A))
            rw [← mul_assoc, hc, mul_assoc]
      _ = d (y : A) * S n := by simp only [S, Finset.mul_sum]
  calc
    d ((δ.dpow (n + 1) (x + y) : evenSubalgebra 𝒜) : A) = d (S (n + 1)) := by rw [hS]
    _ = ∑ ij ∈ Finset.antidiagonal (n + 1), d (F ij.1 * G ij.2) := by
      simp only [S, map_sum]
    _ = ∑ ij ∈ Finset.antidiagonal (n + 1),
          (d (F ij.1) * G ij.2 + F ij.1 * d (G ij.2)) := by
      apply Finset.sum_congr rfl
      intro ij hij
      exact hmul ((δ.dpow ij.1 x : evenSubalgebra 𝒜).property)
        ((δ.dpow ij.2 y : evenSubalgebra 𝒜).property)
    _ = d (x : A) * S n + d (y : A) * S n := by
      rw [Finset.sum_add_distrib, hfirst, hsecond]
    _ = d ((x + y : evenSubalgebra 𝒜) : A) *
        ((δ.dpow n (x + y) : evenSubalgebra 𝒜) : A) := by
      rw [← add_mul, ← hS n]
      simp

private theorem dividedPowers_differential_smul
    {R : Type u} {A : Type w}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜]
    (δ : _root_.DividedPowers (positiveEvenIdeal 𝒜))
    (d : A →ₗ[R] A)
    (x : evenSubalgebra 𝒜) (hxI : x ∈ positiveEvenIdeal 𝒜)
    (hx : ∀ k : ℕ, k ≠ 0 →
      d ((δ.dpow k x : evenSubalgebra 𝒜) : A) =
        d (x : A) * ((δ.dpow (k - 1) x : evenSubalgebra 𝒜) : A))
    (r : R) (n : ℕ) :
    d ((δ.dpow (n + 1) (r • x) : evenSubalgebra 𝒜) : A) =
      d ((r • x : evenSubalgebra 𝒜) : A) *
        ((δ.dpow n (r • x) : evenSubalgebra 𝒜) : A) := by
  have hδ_smul (k : ℕ) : δ.dpow k (r • x) = r ^ k • δ.dpow k x := by
    rw [Algebra.smul_def, δ.dpow_mul hxI]
    rw [← map_pow]
    exact (Algebra.smul_def (r ^ k) (δ.dpow k x)).symm
  rw [hδ_smul (n + 1), hδ_smul n]
  simp only [Subalgebra.coe_smul, map_smul]
  rw [hx (n + 1) (by lia)]
  simp only [Nat.add_sub_cancel_right, pow_succ, smul_mul_smul_comm]
  rw [mul_comm (r ^ n) r]

private theorem dividedPowerStructureOnBaseChange_isCompatible
    {R : Type u} {A : Type w} {P : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜]
    [CommRing P] [Algebra R P]
    (γ : DividedPowerStructure 𝒜) (d : A →ₗ[R] A)
    [IsCompatibleWithDifferential γ d]
    (d_grade_zero : ∀ x : A, x ∈ 𝒜 0 → d x = 0)
    (d_mul : ∀ (i j : ℕ) (x y : A), x ∈ 𝒜 i → y ∈ 𝒜 j →
      d (x * y) = d x * y + (-1 : R) ^ i • (x * d y)) :
    let 𝒜' : ℕ → Submodule P (P ⊗[R] A) := fun i => (𝒜 i).baseChange P
    letI : IsStrictlyGradedComm 𝒜' := strictlyGradedComm_baseChange 𝒜
    IsCompatibleWithDifferential
      (dividedPowerStructureOnBaseChange (P := P) 𝒜 γ) (d.baseChange P) := by
  intro 𝒜'
  let : IsStrictlyGradedComm 𝒜' := strictlyGradedComm_baseChange 𝒜
  let γ' := dividedPowerStructureOnBaseChange (P := P) 𝒜 γ
  let δ := dividedPowersOnBaseChangedEven (P := P) 𝒜 (dividedPowersOnEven 𝒜 γ)
  let d' := d.baseChange P
  have hone : d' (1 : P ⊗[R] A) = 0 :=
    baseChange_zero_on d (𝒜 0) d_grade_zero 1 (SetLike.one_mem_graded 𝒜')
  have hmul : ∀ {a b : P ⊗[R] A}, a ∈ evenPart 𝒜' → b ∈ evenPart 𝒜' →
      d' (a * b) = d' a * b + a * d' b := fun ha hb ↦
    differential_mul_evenPart 𝒜' d'
      (fun i j x y hx hy ↦ differential_mul_baseChange 𝒜 d d_mul hx hy) ha hb
  have hγ : ∀ (k : ℕ) (a : A), a ∈ positiveEvenPart 𝒜 →
      γ'.dpow k (1 ⊗ₜ[R] a) = 1 ⊗ₜ[R] γ.dpow k a :=
    fun k a ha ↦ dividedPowerStructureOnBaseChange_dpow_tmul 𝒜 γ k a ha
  have hpos : ∀ {z : P ⊗[R] A}, z ∈ Submodule.span P
      ((((positiveEvenPart 𝒜).map (TensorProduct.mk R P A 1) : Submodule R _)) : Set _) →
        z ∈ positiveEvenPart 𝒜' := fun hz ↦ by
    rw [positiveEvenPart_baseChange]
    exact mem_baseChange_of_mem_span _ hz
  have H : ∀ z : P ⊗[R] A, z ∈ positiveEvenPart 𝒜' →
      ∀ b : evenSubalgebra 𝒜', (b : P ⊗[R] A) = z →
      ∀ k : ℕ, k ≠ 0 →
        d' ((δ.dpow k b : evenSubalgebra 𝒜') : P ⊗[R] A) =
          d' z * ((δ.dpow (k - 1) b : evenSubalgebra 𝒜') : P ⊗[R] A) := by
    intro z hz
    rw [positiveEvenPart_baseChange] at hz
    rw [Submodule.baseChange_eq_span] at hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
        rcases hz with ⟨a, ha, rfl⟩
        intro b hb k hk
        have ha' : (1 : P) ⊗ₜ[R] a ∈ positiveEvenPart 𝒜' :=
          one_tmul_mem_positiveEvenPart_baseChange 𝒜 ha
        obtain rfl : b = (⟨1 ⊗ₜ[R] a,
            positiveEvenPart_le_evenPart 𝒜' ha'⟩ : evenSubalgebra 𝒜') :=
          Subtype.ext hb
        have hpure := differential_dpow_baseChange_tmul 𝒜 γ d γ' hγ
          k hk a ha
        change d' (baseChangedGradedDpow 𝒜 γ k (1 ⊗ₜ[R] a)) =
          d' (1 ⊗ₜ[R] a) *
            baseChangedGradedDpow 𝒜 γ (k - 1) (1 ⊗ₜ[R] a) at hpure
        rw [baseChangedGradedDpow_of_mem 𝒜 γ k (1 ⊗ₜ[R] a) ha',
          baseChangedGradedDpow_of_mem 𝒜 γ (k - 1) (1 ⊗ₜ[R] a) ha'] at hpure
        exact hpure
    | zero =>
        intro b hb k hk
        obtain rfl : b = 0 := Subtype.ext hb
        rw [δ.dpow_eval_zero hk]
        simp
    | add z t hz ht ihz iht =>
        intro b hb k hk
        have hz' : z ∈ positiveEvenPart 𝒜' := hpos hz
        have ht' : t ∈ positiveEvenPart 𝒜' := hpos ht
        let bz : evenSubalgebra 𝒜' :=
          ⟨z, positiveEvenPart_le_evenPart 𝒜' hz'⟩
        let bt : evenSubalgebra 𝒜' :=
          ⟨t, positiveEvenPart_le_evenPart 𝒜' ht'⟩
        have hb' : b = bz + bt := Subtype.ext hb
        rw [hb']
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by lia⟩
        exact dividedPowers_differential_add 𝒜' δ d' hone hmul
          bz bt hz' ht' (ihz bz rfl) (iht bt rfl) j
    | smul p z hz ih =>
        intro b hb k hk
        have hz' : z ∈ positiveEvenPart 𝒜' := hpos hz
        let bz : evenSubalgebra 𝒜' :=
          ⟨z, positiveEvenPart_le_evenPart 𝒜' hz'⟩
        have hb' : b = p • bz := Subtype.ext hb
        rw [hb']
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by lia⟩
        exact dividedPowers_differential_smul 𝒜' δ d' bz hz' (ih bz rfl) p j
  constructor
  intro n x hn hx
  have hδ := H x hx
    (⟨x, positiveEvenPart_le_evenPart 𝒜' hx⟩ : evenSubalgebra 𝒜') rfl n hn
  show d' (baseChangedGradedDpow 𝒜 γ n x) =
    d' x * baseChangedGradedDpow 𝒜 γ (n - 1) x
  rwa [baseChangedGradedDpow_of_mem 𝒜 γ n x hx,
    baseChangedGradedDpow_of_mem 𝒜 γ (n - 1) x hx]

/-- Divided powers and their compatibility with the differential extend under arbitrary base
change: for a ring map `R → R'`, the differential graded algebra `R' ⊗[R] A` with grading
`(𝒜 i).baseChange R'` and differential `d.baseChange R'` carries divided powers `γ'` compatible
with that differential, and `γ'ₙ (1 ⊗ₜ x) = 1 ⊗ₜ γₙ x` for `x` in the positive even part. -/
@[stacks 09PL]
public theorem exists_dividedPowerStructure_baseChange
    {R : Type u} {R' : Type v} {A : Type w}
    [CommRing R] [CommRing R'] [Ring A] [Algebra R R'] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (γ : DividedPowerStructure 𝒜) (d : A →ₗ[R] A) [IsCompatibleWithDifferential γ d]
    (d_sq : d.comp d = 0)
    (d_grade_zero : ∀ x : A, x ∈ 𝒜 0 → d x = 0)
    (d_mem : ∀ (n : ℕ) (x : A), x ∈ 𝒜 (n + 1) → d x ∈ 𝒜 n)
    (d_mul : ∀ (i j : ℕ) (x y : A), x ∈ 𝒜 i → y ∈ 𝒜 j →
      d (x * y) = d x * y + (-1 : R) ^ i • (x * d y)) :
    let 𝒜' : ℕ → Submodule R' (R' ⊗[R] A) := fun i ↦ (𝒜 i).baseChange R'
    let d' := LinearMap.baseChange R' d
    ∃ hcomm : IsStrictlyGradedComm 𝒜',
      letI := hcomm
      ∃ γ' : DividedPowerStructure 𝒜',
        d'.comp d' = 0 ∧
          (∀ x : R' ⊗[R] A, x ∈ 𝒜' 0 → d' x = 0) ∧
          (∀ (n : ℕ) (x : R' ⊗[R] A), x ∈ 𝒜' (n + 1) → d' x ∈ 𝒜' n) ∧
          (∀ (i j : ℕ) (x y : R' ⊗[R] A), x ∈ 𝒜' i → y ∈ 𝒜' j →
            d' (x * y) = d' x * y + (-1 : R') ^ i • (x * d' y)) ∧
          IsCompatibleWithDifferential γ' d' ∧
          ∀ (n : ℕ) (x : A), x ∈ positiveEvenPart 𝒜 →
            γ'.dpow n (1 ⊗ₜ[R] x) = 1 ⊗ₜ[R] γ.dpow n x := by
  intro 𝒜' d'
  let hcomm : IsStrictlyGradedComm 𝒜' := strictlyGradedComm_baseChange 𝒜
  refine ⟨hcomm, ?_⟩
  let : IsStrictlyGradedComm 𝒜' := hcomm
  let γ' := dividedPowerStructureOnBaseChange (P := R') 𝒜 γ
  exact ⟨γ', (by rw [← LinearMap.baseChange_comp, d_sq, LinearMap.baseChange_zero]),
    baseChange_zero_on d (𝒜 0) d_grade_zero,
    fun n x hx ↦ baseChange_mapsTo d (𝒜 (n + 1)) (𝒜 n) (d_mem n) x hx,
    fun i j x y hx hy ↦ differential_mul_baseChange 𝒜 d d_mul hx hy,
    dividedPowerStructureOnBaseChange_isCompatible 𝒜 γ d d_grade_zero d_mul,
    fun n x hx ↦ dividedPowerStructureOnBaseChange_dpow_tmul 𝒜 γ n x hx⟩

end DividedPowers.TateResolution
