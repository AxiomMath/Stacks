module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.VariableDifferential.OddExtensionUnique

/-!
# Leibniz rule and divided powers for an odd-variable differential

For an odd variable `T`, this file proves that `oddExtensionDifferential` satisfies the graded
Leibniz rule, is square-zero when the prescribed value is a cycle, lowers degrees by one, and is
compatible with the divided powers of the extension `A⟨T⟩ = A ⊕ AT`.
-/

@[expose] public section

namespace DividedPowers.TateResolution

attribute [local implicit_reducible] TwistedModule

universe u v

private theorem signRingEquiv_eq_signRingHom
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (d : ℕ) (a : A) :
    signRingEquiv 𝒜 d a = signRingHom 𝒜 d a := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp [signRingEquiv]
  | homogeneous a =>
      rw [signRingEquiv_of_mem 𝒜 d _ a.property,
        signRingHom_of_mem 𝒜 d _ a.property]
  | add a b ha hb => simp [ha, hb]

private theorem odd_sign_pow_sub
    {R : Type u} [CommRing R] {d i : ℕ} (hd : Odd d) (hdi : d ≤ i) :
    (-1 : R) ^ (d * (i - d)) = -(-1 : R) ^ i := by
  rcases hd with ⟨q, hq⟩
  calc
    (-1 : R) ^ (d * (i - d)) = (-1 : R) ^ (i - d) := by
      rw [pow_mul, Odd.neg_one_pow ⟨q, hq⟩]
    _ = -(-1 : R) ^ i := by
      rw [show i = (i - d) + d by omega, pow_add,
        Odd.neg_one_pow ⟨q, hq⟩]
      simp

/-- `signRingHom 𝒜 1` fixes a homogeneous element of even degree and negates one of odd degree. -/
private theorem signRingHom_one_of_mem_ite
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] {i : ℕ} {a : A} (ha : a ∈ 𝒜 i) :
    signRingHom 𝒜 1 a = if Even i then a else -a := by
  rw [signRingHom_of_mem 𝒜 1 i ha, Nat.one_mul, neg_one_pow_eq_ite]
  split_ifs <;> simp

/-- Membership in `if p then S else ⊥` means `p` and membership in `S`, or vanishing. -/
private theorem mem_ite_bot_cases
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {p : Prop} [Decidable p] {S : Submodule R A} {b : A} (hb : b ∈ if p then S else ⊥) :
    (p ∧ b ∈ S) ∨ b = 0 := by
  split_ifs at hb with hp
  · exact Or.inl ⟨hp, hb⟩
  · exact Or.inr ((Submodule.mem_bot R).mp hb)

private theorem oddExtensionDifferential_fst
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (dA : A →ₗ[R] A)
    (d : ℕ) (f : A) (x : OddVariableExtension 𝒜 d) :
    (oddExtensionDifferential 𝒜 dA d f x).fst = dA x.fst + signRingHom 𝒜 d x.snd * f := by
  have h := oddExtensionDifferential_coefficients 𝒜 dA d f x
  exact congrArg Prod.fst h

private theorem oddExtensionDifferential_snd
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (dA : A →ₗ[R] A)
    (d : ℕ) (f : A) (x : OddVariableExtension 𝒜 d) :
    (oddExtensionDifferential 𝒜 dA d f x).snd = dA x.snd := by
  have h := oddExtensionDifferential_coefficients 𝒜 dA d f x
  exact congrArg Prod.snd h

private theorem differential_mul_even_odd
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (dA : A →ₗ[R] A)
    (hleibniz : ∀ {i j : ℕ} {x y : A}, x ∈ 𝒜 i → y ∈ 𝒜 j →
      dA (x * y) = dA x * y + (-1 : R) ^ i • (x * dA y))
    {x y : A} (hx : x ∈ evenPart 𝒜)
    (hy : y ∈ oddPart 𝒜) :
    dA (x * y) = dA x * y + x * dA y := by
  change x ∈ (⨆ i : ℕ, 𝒜 (2 * i)) at hx
  change y ∈ (⨆ j : ℕ, 𝒜 (2 * j + 1)) at hy
  rw [Submodule.iSup_eq_span] at hx hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      induction hy using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy
          have heven : Even (2 * i) := ⟨i, by omega⟩
          simpa only [heven.neg_one_pow, one_smul] using hleibniz hi hj
      | zero => simp
      | add y z hy hz ihy ihz =>
          simp only [mul_add, map_add, ihy, ihz]
          abel
      | smul r y hy ih =>
          calc
            dA (x * (r • y)) = r • dA (x * y) := by rw [mul_smul_comm, map_smul]
            _ = r • (dA x * y + x * dA y) := by rw [ih]
            _ = dA x * (r • y) + x * dA (r • y) := by
              simp only [smul_add, mul_smul_comm, map_smul]
  | zero => simp
  | add x z hx hz ihx ihz =>
      simp only [add_mul, map_add, ihx, ihz]
      abel
  | smul r x hx ih =>
      calc
        dA ((r • x) * y) = r • dA (x * y) := by rw [smul_mul_assoc, map_smul]
        _ = r • (dA x * y + x * dA y) := by rw [ih]
        _ = dA (r • x) * y + (r • x) * dA y := by
          simp only [smul_add, smul_mul_assoc, map_smul]

theorem oddExtensionDifferential_leibniz
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (dA : A →ₗ[R] A) [IsGradedDerivation 𝒜 dA]
    (d : ℕ) (hd_odd : Odd d) (f : A) (hf_grade : f ∈ 𝒜 (d - 1))
    {i j : ℕ} {x y : OddVariableExtension 𝒜 d}
    (hx : x ∈ OddVariableExtension.grade 𝒜 d i)
    (hy : y ∈ OddVariableExtension.grade 𝒜 d j) :
    oddExtensionDifferential 𝒜 dA d f (x * y) =
      oddExtensionDifferential 𝒜 dA d f x * y +
        (-1 : R) ^ i • (x * oddExtensionDifferential 𝒜 dA d f y) := by
  -- Work in the two coefficients of the square-zero extension.
  let a : A := x.fst
  let b : A := x.snd
  let c : A := y.fst
  let e : A := y.snd
  apply (OddVariableExtension.coefficients 𝒜 d).injective
  change
    (dA (a * c) + signRingHom 𝒜 d
        (a * e + b * signRingHom 𝒜 d c) * f,
      dA (a * e + b * signRingHom 𝒜 d c)) =
    ((dA a + signRingHom 𝒜 d b * f) * c +
        (-1 : R) ^ i • (a * (dA c + signRingHom 𝒜 d e * f)),
      (dA a + signRingHom 𝒜 d b * f) * e + dA b *
        signRingHom 𝒜 d c +
        (-1 : R) ^ i • (a * dA e + b *
          signRingHom 𝒜 d (dA c + signRingHom 𝒜 d e * f)))
  have hτ : signRingHom 𝒜 d = signRingHom 𝒜 1 :=
    RingHom.ext (gradingSign_eq_odd 𝒜 d hd_odd)
  have hx' := (OddVariableExtension.mem_grade_coefficients_iff 𝒜 d i x).mp hx
  have hy' := (OddVariableExtension.mem_grade_coefficients_iff 𝒜 d j y).mp hy
  have ha : a ∈ 𝒜 i := hx'.1
  have hc : c ∈ 𝒜 j := hy'.1
  have hf_even : Even (d - 1) := Nat.Odd.sub_odd hd_odd odd_one
  -- The second coefficient of an element of degree `k` is odd-shifted, and `f` commutes with it.
  have hsnd (k : ℕ) (z : A) (hz : z ∈ if d ≤ k then 𝒜 (k - d) else ⊥) :
      signRingHom 𝒜 1 z = (if Even k then -z else z) ∧ f * z = z * f := by
    rcases mem_ite_bot_cases hz with ⟨hdk, hmem⟩ | h0
    · refine ⟨?_, even_element_commute 𝒜 hf_grade hf_even z⟩
      have hde : ¬ Even d := Nat.not_even_iff_odd.mpr hd_odd
      rw [signRingHom_one_of_mem_ite 𝒜 hmem]
      by_cases hk : Even k <;> simp [hk, hde, Nat.even_sub hdk]
    · simp [h0]
  have hsigA : signRingHom 𝒜 1 a = if Even i then a else -a :=
    signRingHom_one_of_mem_ite 𝒜 ha
  have hsigC : signRingHom 𝒜 1 c = if Even j then c else -c :=
    signRingHom_one_of_mem_ite 𝒜 hc
  have hsigB : signRingHom 𝒜 1 b = if Even i then -b else b := (hsnd i b hx'.2).1
  have hsigE : signRingHom 𝒜 1 e = if Even j then -e else e := (hsnd j e hy'.2).1
  have hsigNegE : signRingHom 𝒜 1 (-e) = if Even j then e else -e := by
    rw [map_neg, hsigE]
    by_cases hj : Even j <;> simp [hj]
  have hsigF : signRingHom 𝒜 1 f = f := by
    simp [signRingHom_one_of_mem_ite 𝒜 hf_grade, hf_even]
  have hfc : f * c = c * f := even_element_commute 𝒜 hf_grade hf_even c
  have hfe : f * e = e * f := (hsnd j e hy'.2).2
  rw [hτ]
  rw [differential_mul_sign 𝒜 dA a c]
  rw [map_add dA (a * e) (b * signRingHom 𝒜 1 c)]
  rw [differential_mul_sign 𝒜 dA a e,
      differential_mul_sign 𝒜 dA b (signRingHom 𝒜 1 c)]
  rw [map_add (signRingHom 𝒜 1) (a * e) (b * signRingHom 𝒜 1 c)]
  rw [map_mul (signRingHom 𝒜 1) b (signRingHom 𝒜 1 c)]
  rw [map_mul (signRingHom 𝒜 1) a e]
  have hanti := gradingSign_anticommutes_differential 𝒜 dA c
  have hanti' : dA (signRingHom 𝒜 1 c) = -signRingHom 𝒜 1 (dA c) :=
    eq_neg_of_add_eq_zero_right hanti
  rw [hanti']
  simp only [map_add, map_mul]
  rw [signRingHom_involutive 𝒜 1 c]
  simp only [hsigA, hsigB, hsigC, hsigE, hsigF]
  -- The remaining signs are the four parity cases for the homogeneous degrees.
  rw [neg_one_pow_eq_ite]
  by_cases hiEven : Even i <;> by_cases hjEven : Even j <;>
    simp only [hiEven, hjEven, ↓reduceIte, one_smul, neg_one_smul]
  all_goals
    first | rw [hsigE] | rw [hsigNegE]
    simp only [hjEven, ↓reduceIte, neg_mul, mul_neg, neg_neg]
    simp only [add_mul, mul_add]
    try simp only [neg_mul, mul_neg]
    try simp only [mul_assoc]
    rw [hfc, hfe]
    abel_nf

theorem oddExtensionDifferential_sq_zero
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (dA : A →ₗ[R] A) [IsDifferentialGradedAlgebra 𝒜 dA]
    (d : ℕ) (hd_odd : Odd d) (f : A) (hf_grade : f ∈ 𝒜 (d - 1))
    (hf_cycle : dA f = 0) (x : OddVariableExtension 𝒜 d) :
    oddExtensionDifferential 𝒜 dA d f
      (oddExtensionDifferential 𝒜 dA d f x) = 0 := by
  apply (OddVariableExtension.coefficients 𝒜 d).injective
  rw [oddExtensionDifferential_coefficients, oddExtensionDifferential_coefficients]
  change (dA (dA x.fst + signRingHom 𝒜 d x.snd * f) +
      signRingHom 𝒜 d (dA (show A from x.snd)) * f,
    dA (dA (show A from x.snd))) = (0, 0)
  apply Prod.ext
  · have hanti := gradingSignOdd_anticommutes_differential 𝒜 dA d hd_odd
      (show A from x.snd)
    have hcycle := differential_mul_cycle 𝒜 dA hf_grade hf_cycle
      (signRingHom 𝒜 d (show A from x.snd))
    change dA (dA x.fst + signRingHom 𝒜 d x.snd * f) +
        signRingHom 𝒜 d (dA (show A from x.snd)) * f = 0
    rw [map_add]
    rw [IsDifferentialGradedAlgebra.d_sq_zero (𝒜 := 𝒜) (d := dA) x.fst, hcycle]
    have hanti' : dA (signRingHom 𝒜 d (show A from x.snd)) =
        -signRingHom 𝒜 d (dA (show A from x.snd)) :=
      eq_neg_of_add_eq_zero_right hanti
    rw [hanti']
    simp
  · change dA (dA (show A from x.snd)) = 0
    exact IsDifferentialGradedAlgebra.d_sq_zero (𝒜 := 𝒜) (d := dA)
      (show A from x.snd)

theorem oddExtensionDifferential_grade_zero
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (dA : A →ₗ[R] A) [IsGradedDerivation 𝒜 dA]
    (d : ℕ) (hd : 0 < d) (f : A) {x : OddVariableExtension 𝒜 d}
    (hx : x ∈ OddVariableExtension.grade 𝒜 d 0) :
    oddExtensionDifferential 𝒜 dA d f x = 0 := by
  have hx' := (OddVariableExtension.mem_grade_coefficients_iff 𝒜 d 0 x).mp hx
  have hfst : dA x.fst = 0 :=
    IsGradedDerivation.d_grade_zero hx'.1
  have hsnd : (show A from x.snd) = 0 :=
    (mem_ite_bot_cases hx'.2).resolve_left fun h => absurd h.1 (by omega)
  apply (OddVariableExtension.coefficients 𝒜 d).injective
  rw [oddExtensionDifferential_coefficients]
  apply Prod.ext
  · change dA x.fst + signRingHom 𝒜 d (show A from x.snd) * f = 0
    simp [hfst, hsnd]
  · change dA (show A from x.snd) = 0
    simp [hsnd]

theorem oddExtensionDifferential_mem
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (dA : A →ₗ[R] A) [IsGradedDerivation 𝒜 dA]
    (d : ℕ) (hd : 0 < d) (f : A) (hf_grade : f ∈ 𝒜 (d - 1))
    {n : ℕ} {x : OddVariableExtension 𝒜 d}
    (hx : x ∈ OddVariableExtension.grade 𝒜 d (n + 1)) :
    oddExtensionDifferential 𝒜 dA d f x ∈ OddVariableExtension.grade 𝒜 d n := by
  have hx' := (OddVariableExtension.mem_grade_coefficients_iff 𝒜 d (n + 1) x).mp hx
  let a : A := (OddVariableExtension.coefficients 𝒜 d x).1
  let b : A := (OddVariableExtension.coefficients 𝒜 d x).2
  have ha : a ∈ 𝒜 (n + 1) := hx'.1
  have hb : b ∈ (if d ≤ n + 1 then 𝒜 (n + 1 - d) else ⊥) := hx'.2
  have hda : dA a ∈ 𝒜 n := IsGradedDerivation.d_mem (𝒜 := 𝒜) (d := dA) ha
  rw [OddVariableExtension.mem_grade_coefficients_iff]
  rw [oddExtensionDifferential_coefficients]
  change dA a + signRingHom 𝒜 d b * f ∈ 𝒜 n ∧
    dA b ∈ (if d ≤ n then 𝒜 (n - d) else ⊥)
  rcases mem_ite_bot_cases hb with ⟨hdle, hsnd⟩ | hb0
  · refine ⟨Submodule.add_mem _ hda ?_, ?_⟩
    · have hsign : signRingHom 𝒜 d b ∈ 𝒜 (n + 1 - d) := by
        rw [signRingHom_of_mem 𝒜 d (n + 1 - d) hsnd]
        exact (𝒜 (n + 1 - d)).smul_mem _ hsnd
      simpa [show (n + 1 - d) + (d - 1) = n by omega] using
        SetLike.mul_mem_graded hsign hf_grade
    · by_cases hdle' : d ≤ n
      · rw [show n + 1 - d = (n - d) + 1 by omega] at hsnd
        simpa [hdle'] using IsGradedDerivation.d_mem (𝒜 := 𝒜) (d := dA) hsnd
      · have hb0 : b ∈ 𝒜 0 := by simpa [show n + 1 - d = 0 by omega] using hsnd
        simp [hdle', IsGradedDerivation.d_grade_zero (𝒜 := 𝒜) (d := dA) hb0]
  · simp [hb0, hda]

private theorem oddPositiveEven_coefficients
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜] (d : ℕ) (hd_odd : Odd d)
    (z : OddVariableExtension 𝒜 d)
    (hz : z ∈ positiveEvenPart (OddVariableExtension.grade 𝒜 d)) :
    z.fst ∈ positiveEvenPart 𝒜 ∧ z.snd ∈ oddPart 𝒜 := by
  classical
  rcases hd_odd with ⟨q, hq⟩
  rw [positiveEvenPart] at hz
  obtain ⟨g, hg, hgsum⟩ :=
    (Submodule.mem_iSup_iff_exists_finsupp
      (fun e : ℕ ↦ OddVariableExtension.grade 𝒜 d (2 * (e + 1))) z).mp hz
  have hfst : z.fst = g.sum (fun e x ↦ x.fst) := by
    rw [← hgsum]
    simp only [Finsupp.sum, TrivSqZeroExt.fst_sum]
  have hsnd : (show A from z.snd) = g.sum (fun e x ↦ (show A from x.snd)) := by
    rw [← hgsum]
    simp only [Finsupp.sum, TrivSqZeroExt.snd_sum]
    rfl
  constructor
  · rw [hfst, positiveEvenPart, Finsupp.sum]
    apply Submodule.sum_mem
    intro e he
    apply Submodule.mem_iSup_of_mem e
    exact (OddVariableExtension.mem_grade_iff 𝒜 d (2 * (e + 1)) (g e)).mp (hg e) |>.1
  · change (show A from z.snd) ∈ oddPart 𝒜
    rw [hsnd, oddPart, Finsupp.sum]
    apply Submodule.sum_mem
    intro e he
    have hmem := (OddVariableExtension.mem_grade_iff 𝒜 d
      (2 * (e + 1)) (g e)).mp (hg e)
    rcases mem_ite_bot_cases (b := (show A from (g e).snd)) hmem.2 with ⟨hle, hsecond⟩ | hzero
    · have hodd : 2 * (e + 1) - d = 2 * (e - q) + 1 := by omega
      apply Submodule.mem_iSup_of_mem (e - q)
      simpa [hodd] using hsecond
    · simp [hzero]

private theorem oddPart_anticomm
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜] {x y : A}
    (hx : x ∈ oddPart 𝒜) (hy : y ∈ oddPart 𝒜) :
    x * y = -(y * x) := by
  classical
  obtain ⟨f, hf, hfsum⟩ :=
    (Submodule.mem_iSup_iff_exists_finsupp
      (fun i : ℕ ↦ 𝒜 (2 * i + 1)) x).mp hx
  obtain ⟨g, hg, hgsum⟩ :=
    (Submodule.mem_iSup_iff_exists_finsupp
      (fun i : ℕ ↦ 𝒜 (2 * i + 1)) y).mp hy
  rw [← hfsum, ← hgsum, Finsupp.sum, Finsupp.sum,
    Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hcomm := IsStrictlyGradedComm.graded_comm (hf j) (hg i)
  have hodd₁ : Odd (2 * j + 1) := ⟨j, rfl⟩
  have hodd₂ : Odd (2 * i + 1) := ⟨i, rfl⟩
  have hpow : (-1 : R) ^ ((2 * j + 1) * (2 * i + 1)) = -1 :=
    Odd.neg_one_pow (hodd₁.mul hodd₂)
  simpa [hpow] using hcomm

private theorem oddPart_sq_zero
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜] {x : A}
    (hx : x ∈ oddPart 𝒜) : x * x = 0 := by
  change x ∈ (⨆ i : ℕ, 𝒜 (2 * i + 1)) at hx
  rw [Submodule.iSup_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      simpa [pow_two] using IsStrictlyGradedComm.odd_sq_zero hi
  | zero => simp
  | add x y hx hy ihx ihy =>
      calc
        (x + y) * (x + y) = x * x + x * y + y * x + y * y := by
          simp only [add_mul, mul_add]
          abel
        _ = 0 := by
          have hx' : x ∈ oddPart 𝒜 := by
            change x ∈ ⨆ i : ℕ, 𝒜 (2 * i + 1)
            rw [Submodule.iSup_eq_span]
            exact hx
          have hy' : y ∈ oddPart 𝒜 := by
            change y ∈ ⨆ i : ℕ, 𝒜 (2 * i + 1)
            rw [Submodule.iSup_eq_span]
            exact hy
          rw [ihx, ihy, oddPart_anticomm 𝒜 hx' hy']
          simp
  | smul r x hx ih =>
      rw [Algebra.smul_def]
      have hcomm : x * algebraMap R A r = algebraMap R A r * x :=
        (Algebra.commutes r x).symm
      calc
        (algebraMap R A r * x) * (algebraMap R A r * x) =
            algebraMap R A r * (x * algebraMap R A r) * x := by simp [mul_assoc]
        _ = algebraMap R A r * (algebraMap R A r * x) * x := by rw [hcomm]
        _ = algebraMap R A r * algebraMap R A r * (x * x) := by ac_rfl
        _ = 0 := by rw [ih]; simp

theorem signRingHom_eq_self_evenPart
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    {x : A} (hx : x ∈ evenPart 𝒜) :
    signRingHom 𝒜 1 x = x := by
  classical
  obtain ⟨f, hf, hfsum⟩ :=
    (Submodule.mem_iSup_iff_exists_finsupp (fun e : ℕ ↦ 𝒜 (2 * e)) x).mp hx
  rw [← hfsum, Finsupp.sum, map_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [signRingHom_of_mem 𝒜 1 (2 * e) (hf e)]
  simp

private theorem signRingHom_eq_neg_oddPart
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    {x : A} (hx : x ∈ oddPart 𝒜) :
    signRingHom 𝒜 1 x = -x := by
  classical
  obtain ⟨f, hf, hfsum⟩ :=
    (Submodule.mem_iSup_iff_exists_finsupp (fun e : ℕ ↦ 𝒜 (2 * e + 1)) x).mp hx
  rw [← hfsum, Finsupp.sum, map_sum]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro e he
  rw [signRingHom_of_mem 𝒜 1 (2 * e + 1) (hf e)]
  have hp : (-1 : R) ^ (1 * (2 * e + 1)) = -1 := by
    rw [Nat.one_mul]
    exact Odd.neg_one_pow ⟨e, rfl⟩
  rw [hp, neg_one_smul]

theorem evenPart_comm_oddPart
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    {x y : A} (hx : x ∈ evenPart 𝒜)
    (hy : y ∈ oddPart 𝒜) : x * y = y * x := by
  classical
  obtain ⟨f, hf, hfsum⟩ :=
    (Submodule.mem_iSup_iff_exists_finsupp (fun e : ℕ ↦ 𝒜 (2 * e)) x).mp hx
  obtain ⟨g, hg, hgsum⟩ :=
    (Submodule.mem_iSup_iff_exists_finsupp (fun e : ℕ ↦ 𝒜 (2 * e + 1)) y).mp hy
  rw [← hfsum, ← hgsum, Finsupp.sum, Finsupp.sum,
    Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hcomm := IsStrictlyGradedComm.graded_comm (hf j) (hg i)
  have hpow : (-1 : R) ^ ((2 * j) * (2 * i + 1)) = 1 := by
    have he : Even ((2 * j) * (2 * i + 1)) := ⟨j * (2 * i + 1), by ring⟩
    exact he.neg_one_pow
  simpa [hpow, smul_eq_mul] using hcomm

/-- A graded derivation maps `⨆ e, 𝒜 (g e)` into `⨆ e, 𝒜 (h e)` when `g e = h e + 1`. -/
private theorem differential_mem_iSup
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (dA : A →ₗ[R] A) [IsGradedDerivation 𝒜 dA] {g h : ℕ → ℕ} (hgh : ∀ e, g e = h e + 1)
    {x : A} (hx : x ∈ ⨆ e : ℕ, 𝒜 (g e)) : dA x ∈ ⨆ e : ℕ, 𝒜 (h e) := by
  refine (iSup_le (fun e a ha => ?_) : (⨆ e : ℕ, 𝒜 (g e)) ≤ (⨆ e : ℕ, 𝒜 (h e)).comap dA) hx
  rw [hgh e] at ha
  exact Submodule.mem_iSup_of_mem e (IsGradedDerivation.d_mem ha)

theorem differential_positiveEvenPart_oddPart
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (dA : A →ₗ[R] A) [IsGradedDerivation 𝒜 dA]
    {x : A} (hx : x ∈ positiveEvenPart 𝒜) :
    dA x ∈ oddPart 𝒜 :=
  differential_mem_iSup 𝒜 dA (g := fun e ↦ 2 * (e + 1)) (h := fun e ↦ 2 * e + 1)
    (fun e ↦ by omega) hx

private theorem differential_oddPart_evenPart
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (dA : A →ₗ[R] A) [IsGradedDerivation 𝒜 dA]
    {x : A} (hx : x ∈ oddPart 𝒜) :
    dA x ∈ evenPart 𝒜 :=
  differential_mem_iSup 𝒜 dA (g := fun e ↦ 2 * e + 1) (h := fun e ↦ 2 * e)
    (fun e ↦ by omega) hx

theorem oddExtensionDifferential_compatible
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (γ : DividedPowerStructure 𝒜) (dA : A →ₗ[R] A)
    [IsGradedDerivation 𝒜 dA] [IsCompatibleWithDifferential γ dA]
    (d : ℕ) (hd : 0 < d) (hd_odd : Odd d) (f : A)
    (hf_grade : f ∈ 𝒜 (d - 1)) :
    IsCompatibleWithDifferential
      (oddVariableDividedPowerStructure 𝒜 γ d hd hd_odd)
      (oddExtensionDifferential 𝒜 dA d f) := by
  constructor
  intro n x hn hx
  classical
  let a : A := x.fst
  let b : A := x.snd
  have hab := oddPositiveEven_coefficients 𝒜 d hd_odd x hx
  have ha : a ∈ positiveEvenPart 𝒜 := by simpa [a] using hab.1
  have hb : b ∈ oddPart 𝒜 := by simpa [b] using hab.2
  have hvar (z : A) : OddVariableExtension.inclusion 𝒜 d z *
      OddVariableExtension.generator 𝒜 d =
      TrivSqZeroExt.inr (show TwistedModule 𝒜 d from z) := by
    simp [OddVariableExtension.inclusion, OddVariableExtension.generator,
      TrivSqZeroExt.inl_mul_inr]
  have hrepr : x = OddVariableExtension.inclusion 𝒜 d a +
      OddVariableExtension.inclusion 𝒜 d b * OddVariableExtension.generator 𝒜 d := by
    rw [hvar]
    exact (TrivSqZeroExt.inl_fst_add_inr_snd_eq x).symm
  by_cases hn1 : n = 1
  · subst n
    rw [(oddVariableDividedPowerStructure 𝒜 γ d hd hd_odd).dpow_one hx,
      (oddVariableDividedPowerStructure 𝒜 γ d hd hd_odd).dpow_zero hx]
    simp
  · have hn0 : n ≠ 0 := hn
    have hkpos : 0 < n - 1 := by omega
    have hk0 : n - 1 ≠ 0 := by omega
    let gN := γ.dpow n a
    let gK := γ.dpow (n - 1) a
    let gKm := γ.dpow (n - 2) a
    let c := gK * b
    let cPrev := gKm * b
    have hgN : gN ∈ positiveEvenPart 𝒜 := γ.dpow_mem hn0 ha
    have hgK : gK ∈ positiveEvenPart 𝒜 := γ.dpow_mem hk0 ha
    have hgKmEven : gKm ∈ evenPart 𝒜 := by
      dsimp [gKm]
      by_cases hkm : n - 2 = 0
      · rw [hkm, γ.dpow_zero ha]
        change (1 : A) ∈ ⨆ i : ℕ, 𝒜 (2 * i)
        exact Submodule.mem_iSup_of_mem 0 (by simpa using SetLike.one_mem_graded 𝒜)
      · exact positiveEvenPart_le_evenPart 𝒜 (γ.dpow_mem hkm ha)
    have hgKEven : gK ∈ evenPart 𝒜 :=
      positiveEvenPart_le_evenPart 𝒜 hgK
    have hdaOdd : dA a ∈ oddPart 𝒜 :=
      differential_positiveEvenPart_oddPart 𝒜 dA ha
    have hdbEven : dA b ∈ evenPart 𝒜 :=
      differential_oddPart_evenPart 𝒜 dA hb
    have hcN : dA gN = dA a * gK := IsCompatibleWithDifferential.d_dpow hn0 ha
    have hcK : dA gK = dA a * gKm := IsCompatibleWithDifferential.d_dpow hk0 ha
    have hτ : signRingHom 𝒜 d = signRingHom 𝒜 1 :=
      RingHom.ext (gradingSign_eq_odd 𝒜 d hd_odd)
    have hsignB : signRingHom 𝒜 d b = -b := by
      rw [hτ]
      exact signRingHom_eq_neg_oddPart 𝒜 hb
    have hsignGk : signRingHom 𝒜 d gK = gK := by
      rw [hτ]
      exact signRingHom_eq_self_evenPart 𝒜 hgKEven
    have hsignC : signRingHom 𝒜 d c = -c := by
      dsimp [c]
      rw [map_mul, hτ]
      rw [signRingHom_eq_self_evenPart 𝒜 hgKEven,
        signRingHom_eq_neg_oddPart 𝒜 hb]
      simp
    have hcommGkB : gK * b = b * gK := evenPart_comm_oddPart 𝒜 hgKEven hb
    have hcommGkmB : gKm * b = b * gKm := evenPart_comm_oddPart 𝒜 hgKmEven hb
    have hcommDaGkm : dA a * gKm = gKm * dA a :=
      (evenPart_comm_oddPart 𝒜 hgKmEven hdaOdd).symm
    have hcommDbGk : dA b * gK = gK * dA b := evenPart_mul_comm 𝒜 hdbEven gK
    have hf_even : Even (d - 1) := Nat.Odd.sub_odd hd_odd odd_one
    have hcommFGk : f * gK = gK * f := even_element_commute 𝒜 hf_grade hf_even gK
    have hcommFGkm : f * gKm = gKm * f := even_element_commute 𝒜 hf_grade hf_even gKm
    have hcommFb : f * b = b * f := even_element_commute 𝒜 hf_grade hf_even b
    have hbb : b * b = 0 := oddPart_sq_zero 𝒜 hb
    have hdpN : (oddVariableDividedPowerStructure 𝒜 γ d hd hd_odd).dpow n x =
        OddVariableExtension.inclusion 𝒜 d gN +
          OddVariableExtension.inclusion 𝒜 d c * OddVariableExtension.generator 𝒜 d := by
      have h := oddVariableDividedPowerStructure_dpow 𝒜 γ d hd hd_odd
        n hn0 a b ha hb
      rw [← hrepr] at h
      simpa [gN, gK, c] using h
    have hdpK : (oddVariableDividedPowerStructure 𝒜 γ d hd hd_odd).dpow (n - 1) x =
        OddVariableExtension.inclusion 𝒜 d gK +
          OddVariableExtension.inclusion 𝒜 d cPrev * OddVariableExtension.generator 𝒜 d := by
      have h := oddVariableDividedPowerStructure_dpow 𝒜 γ d hd hd_odd
        (n - 1) hk0 a b ha hb
      rw [← hrepr] at h
      simpa [gK, gKm, cPrev, Nat.sub_sub] using h
    have hdx : oddExtensionDifferential 𝒜 dA d f x =
        OddVariableExtension.inclusion 𝒜 d (dA a) +
          OddVariableExtension.inclusion 𝒜 d (signRingHom 𝒜 d b * f) +
          OddVariableExtension.inclusion 𝒜 d (dA b) * OddVariableExtension.generator 𝒜 d := by
      rw [hrepr, map_add, oddExtensionDifferential_inclusion,
        oddExtensionDifferential_inclusion_mul_generator_any]
      simp only [add_assoc]
    have hdc : dA c = dA a * gKm * b + gK * dA b := by
      dsimp [c]
      rw [differential_mul_sign 𝒜 dA, hcK,
        signRingHom_eq_self_evenPart 𝒜 hgKEven]
    have hL : OddVariableExtension.coefficients 𝒜 d
        (oddExtensionDifferential 𝒜 dA d f
          ((oddVariableDividedPowerStructure 𝒜 γ d hd hd_odd).dpow n x)) =
        (dA a * gK + signRingHom 𝒜 d c * f, dA c) := by
      rw [hdpN, map_add, oddExtensionDifferential_inclusion,
        oddExtensionDifferential_inclusion_mul_generator_any]
      simp [hcN]
    have hR : OddVariableExtension.coefficients 𝒜 d
        (oddExtensionDifferential 𝒜 dA d f x *
          (oddVariableDividedPowerStructure 𝒜 γ d hd hd_odd).dpow (n - 1) x) =
        ((dA a + signRingHom 𝒜 d b * f) * gK,
          (dA a + signRingHom 𝒜 d b * f) * cPrev +
            dA b * signRingEquiv 𝒜 d gK) := by
      rw [hdx, hdpK]
      simp only [OddVariableExtension.coefficients_mul,
        OddVariableExtension.coefficients_inclusion,
        OddVariableExtension.coefficients_generator, map_add]
      simp
    have hvanish : b * f * gKm * b = 0 := by
      calc
        b * f * gKm * b = b * (f * gKm) * b := by ac_rfl
        _ = b * (gKm * f) * b := by rw [hcommFGkm]
        _ = (b * gKm) * (f * b) := by ac_rfl
        _ = (gKm * b) * (f * b) := by rw [hcommGkmB.symm]
        _ = (gKm * b) * (b * f) := by rw [hcommFb]
        _ = gKm * (b * b) * f := by ac_rfl
        _ = 0 := by rw [hbb]; simp
    have hfst : dA a * gK + signRingHom 𝒜 d c * f =
        (dA a + signRingHom 𝒜 d b * f) * gK := by
      rw [hsignC, hsignB]
      dsimp [c]
      have hterm : (gK * b) * f = (b * f) * gK := by
        calc
          (gK * b) * f = gK * (b * f) := by ac_rfl
          _ = gK * (f * b) := by rw [hcommFb]
          _ = (gK * f) * b := by ac_rfl
          _ = (f * gK) * b := by rw [hcommFGk]
          _ = f * (gK * b) := by ac_rfl
          _ = f * (b * gK) := by rw [hcommGkB]
          _ = (f * b) * gK := by ac_rfl
          _ = (b * f) * gK := by rw [hcommFb]
      rw [neg_mul, hterm]
      rw [← neg_mul]
      simp only [add_mul, neg_mul, mul_assoc]
    have hsnd : dA c =
        (dA a + signRingHom 𝒜 d b * f) * cPrev +
          dA b * signRingEquiv 𝒜 d gK := by
      rw [hdc, hsignB, signRingEquiv_eq_signRingHom, hsignGk, hcommDbGk]
      dsimp [cPrev]
      have hkill : (b * f) * (gKm * b) = 0 := by
        simpa only [mul_assoc] using hvanish
      simp only [add_mul, neg_mul, hkill, neg_zero, add_zero]
      rw [← mul_assoc (dA a) gKm b]
    apply (OddVariableExtension.coefficients 𝒜 d).injective
    rw [hL, hR]
    exact Prod.ext hfst hsnd

end DividedPowers.TateResolution
