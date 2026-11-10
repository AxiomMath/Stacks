module

public import Mathlib.Tactic.NoncommRing
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Basic
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.EvenVariable
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.UniversalProperty
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.VariableLift

/-!
# Mapping out of an even-variable divided-power extension

A graded ring homomorphism out of the coefficient algebra, together with a choice of image for
the adjoined divided-power variable, extends uniquely to the even-variable extension `A⟨T⟩`.
The image of the variable must be a homogeneous element of the same positive even degree, and
the target must carry a divided power structure: the extension sends the divided-power monomial
`a T⁽ⁿ⁾` to `g a · γₙ τ`.

Everything here is stated for ring homomorphisms rather than algebra homomorphisms, for the same
reason as in the odd-variable case: the consumer is the mapping property of an iterated
divided-power polynomial algebra, whose intermediate finite stages carry an `R`-algebra structure
supplied existentially, which therefore cannot be assumed compatible with the ambient one.

No sign ever appears, because the adjoined variable has even degree. The only commutation fact
needed is that an element of even degree is central, which is recorded here as
`mul_comm_of_mem_grade_even'`.

## Main definitions

* `DividedPowers.TateResolution.evenLift` — the ring homomorphism out of an even-variable
  divided-power extension determined by its restriction to the coefficients and the image of the
  adjoined variable.

## Main results

* `DividedPowers.TateResolution.mul_comm_of_mem_grade_even` and
  `DividedPowers.TateResolution.mul_comm_of_mem_grade_even'`: homogeneous elements of even degree
  are central in a strictly graded-commutative algebra.
* `DividedPowers.TateResolution.evenLift_monomial`,
  `DividedPowers.TateResolution.evenLift_coeffEmbedding` and
  `DividedPowers.TateResolution.evenLift_monomial_one` compute the extension on the generators.
* `DividedPowers.TateResolution.evenLift_mem_grade`: the extension is graded.
* `DividedPowers.TateResolution.evenLift_unique`: the extension is determined by the restriction
  to the coefficients together with the images of the divided-power monomials `T⁽ⁿ⁾`.

## References

* [Stacks Project, Tag 09PH](https://stacks.math.columbia.edu/tag/09PH)
* [Stacks Project, Tag 09PI](https://stacks.math.columbia.edu/tag/09PI)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w

section EvenTarget

variable {R : Type u} {D : Type w} [CommRing R] [Ring D] [Algebra R D]
variable (Dᵢ : ℕ → Submodule R D) [GradedAlgebra Dᵢ] [IsStrictlyGradedComm Dᵢ]

omit [GradedAlgebra Dᵢ] in
/-- A homogeneous element of even degree commutes with every homogeneous element. -/
public theorem mul_comm_of_mem_grade_even {k m : ℕ} {x y : D} (hx : x ∈ Dᵢ (2 * k))
    (hy : y ∈ Dᵢ m) : x * y = y * x := by
  have heven : Even (2 * k * m) := ⟨k * m, by ring⟩
  rw [IsStrictlyGradedComm.graded_comm (𝒜 := Dᵢ) hx hy,
    show ((-1 : R) ^ (2 * k * m)) = 1 from heven.neg_one_pow, one_smul]

/-- A homogeneous element of even degree is central. -/
public theorem mul_comm_of_mem_grade_even' {k : ℕ} {x : D} (hx : x ∈ Dᵢ (2 * k)) (y : D) :
    x * y = y * x := by
  induction y using DirectSum.Decomposition.inductionOn Dᵢ with
  | zero => rw [mul_zero, zero_mul]
  | @homogeneous m a => exact mul_comm_of_mem_grade_even Dᵢ hx a.property
  | add a b ha hb => rw [mul_add, ha, hb, add_mul]

omit [GradedAlgebra Dᵢ] [IsStrictlyGradedComm Dᵢ] in
/-- A homogeneous element of positive even degree lies in the positive even part. -/
public theorem mem_positiveEvenPart_of_even (d : ℕ) (hd : 0 < d) (hdeven : Even d) {τ : D}
    (hτ : τ ∈ Dᵢ d) : τ ∈ positiveEvenPart Dᵢ := by
  obtain ⟨k, hk⟩ := hdeven
  refine mem_positiveEvenPart_of_mem_grade Dᵢ (d := k) (by omega) ?_
  rwa [show 2 * k = d by omega]

/-- The `n`th divided power of a homogeneous element of positive even degree `d` has degree
`n * d`. -/
private theorem dpow_mem_grade_of_even (d : ℕ) (hd : 0 < d) (hdeven : Even d)
    (δ : DividedPowerStructure Dᵢ) (τ : D) (hτ : τ ∈ Dᵢ d) (n : ℕ) :
    δ.dpow n τ ∈ Dᵢ (n * d) := by
  obtain ⟨k, hk⟩ := id hdeven
  have h := dpow_mem_grade_mul_of_mem_positiveEvenPart Dᵢ δ n k
    (mem_positiveEvenPart_of_even Dᵢ d hd hdeven hτ) (by rwa [show 2 * k = d by omega])
  rwa [show 2 * k = d by omega] at h

end EvenTarget

section EvenLift

variable {R : Type u} {A : Type v} {D : Type w}
  [CommRing R] [Ring A] [Algebra R A] [Ring D] [Algebra R D]
variable (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
  (Dᵢ : ℕ → Submodule R D) [GradedAlgebra Dᵢ] [IsStrictlyGradedComm Dᵢ]

/-- The additive map sending `∑ aₙ T⁽ⁿ⁾` to `∑ g aₙ · γₙ τ`. -/
public noncomputable def evenLiftAddHom (g : A →+* D) (δ : DividedPowerStructure Dᵢ) (τ : D) :
    EvenVariableAlgebra A →+ D :=
  (Finsupp.liftAddHom fun n : ℕ =>
      (AddMonoidHom.mulRight (δ.dpow n τ)).comp g.toAddMonoidHom).comp
    { toFun := EvenVariableAlgebra.coeff
      map_zero' := EvenVariableAlgebra.coeff_zero
      map_add' := EvenVariableAlgebra.coeff_add }

omit [Algebra R A] in
/-- The additive extension sends the divided-power monomial `a T⁽ⁿ⁾` to `g a · γₙ τ`. -/
public theorem evenLiftAddHom_monomial (g : A →+* D) (δ : DividedPowerStructure Dᵢ) (τ : D)
    (n : ℕ) (a : A) :
    evenLiftAddHom Dᵢ g δ τ (EvenVariableAlgebra.monomial n a) = g a * δ.dpow n τ := by
  change (Finsupp.liftAddHom fun n : ℕ =>
      (AddMonoidHom.mulRight (δ.dpow n τ)).comp g.toAddMonoidHom) (Finsupp.single n a) = _
  rw [Finsupp.liftAddHom_apply_single]
  rfl

omit [Algebra R A] [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ] in
/-- The additive extension is multiplicative: this is the divided-power rule
`T⁽ⁿ⁾ T⁽ᵐ⁾ = (n + m).choose n · T⁽ⁿ⁺ᵐ⁾` matched against `γₙ τ · γₘ τ`. -/
public theorem evenLiftAddHom_mul (d : ℕ) (hd : 0 < d) (hdeven : Even d) (g : A →+* D)
    (δ : DividedPowerStructure Dᵢ) (τ : D) (hτ : τ ∈ Dᵢ d) (x y : EvenVariableAlgebra A) :
    evenLiftAddHom Dᵢ g δ τ (x * y) =
      evenLiftAddHom Dᵢ g δ τ x * evenLiftAddHom Dᵢ g δ τ y := by
  have hτ' : τ ∈ positiveEvenPart Dᵢ := mem_positiveEvenPart_of_even Dᵢ d hd hdeven hτ
  obtain ⟨k, hk⟩ := id hdeven
  have hmem : ∀ j : ℕ, δ.dpow j τ ∈ Dᵢ (2 * (j * k)) := fun j => by
    rw [show 2 * (j * k) = j * d by rw [hk]; ring]
    exact dpow_mem_grade_of_even Dᵢ d hd hdeven δ τ hτ j
  have key : ∀ (n m : ℕ) (a b : A),
      evenLiftAddHom Dᵢ g δ τ
          (EvenVariableAlgebra.monomial n a * EvenVariableAlgebra.monomial m b) =
        g a * δ.dpow n τ * (g b * δ.dpow m τ) := by
    intro n m a b
    rw [EvenVariableAlgebra.monomial_mul_monomial, evenLiftAddHom_monomial, map_nsmul, map_mul,
      nsmul_eq_mul, (Nat.cast_commute ((n + m).choose n) (g a * g b)).eq,
      mul_assoc (g a * g b), ← δ.dpow_mul hτ']
    calc g a * g b * (δ.dpow n τ * δ.dpow m τ)
        = g a * (g b * δ.dpow n τ) * δ.dpow m τ := by noncomm_ring
      _ = g a * (δ.dpow n τ * g b) * δ.dpow m τ := by
        rw [mul_comm_of_mem_grade_even' Dᵢ (hmem n) (g b)]
      _ = g a * δ.dpow n τ * (g b * δ.dpow m τ) := by noncomm_ring
  have keyL : ∀ (n : ℕ) (a : A) (z : EvenVariableAlgebra A),
      evenLiftAddHom Dᵢ g δ τ (EvenVariableAlgebra.monomial n a * z) =
        g a * δ.dpow n τ * evenLiftAddHom Dᵢ g δ τ z := by
    intro n a z
    induction z using EvenVariableAlgebra.induction_on with
    | zero => rw [mul_zero, map_zero, mul_zero]
    | add m b z hz =>
        simp only [mul_add, map_add]
        rw [key n m a b, hz, evenLiftAddHom_monomial]
  induction x using EvenVariableAlgebra.induction_on with
  | zero => rw [zero_mul, map_zero, zero_mul]
  | add n a x hx =>
      simp only [add_mul, map_add]
      rw [keyL n a y, hx, evenLiftAddHom_monomial]

/-- The ring homomorphism out of an even-variable divided-power extension determined by a graded
ring homomorphism on the coefficient algebra together with an image for the adjoined variable.

The adjoined variable of degree `d` is sent to `τ`, and its `n`th divided power to `γₙ τ`. -/
public noncomputable def evenLift (d : ℕ) (hd : 0 < d) (hdeven : Even d) (g : A →+* D)
    (_hg : ∀ (m : ℕ) (a : A), a ∈ Aᵢ m → g a ∈ Dᵢ m)
    (δ : DividedPowerStructure Dᵢ) (τ : D) (hτ : τ ∈ Dᵢ d) :
    EvenVariableAlgebra A →+* D where
  toFun := evenLiftAddHom Dᵢ g δ τ
  map_one' := by
    change evenLiftAddHom Dᵢ g δ τ (EvenVariableAlgebra.monomial 0 1) = 1
    rw [evenLiftAddHom_monomial, map_one,
      δ.dpow_zero (mem_positiveEvenPart_of_even Dᵢ d hd hdeven hτ), one_mul]
  map_mul' := evenLiftAddHom_mul Dᵢ d hd hdeven g δ τ hτ
  map_zero' := map_zero _
  map_add' := map_add _

omit [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ] in
/-- The extension sends the divided-power monomial `a T⁽ⁿ⁾` to `g a · γₙ τ`. -/
@[simp] public theorem evenLift_monomial (d : ℕ) (hd : 0 < d) (hdeven : Even d) (g : A →+* D)
    (hg : ∀ (m : ℕ) (a : A), a ∈ Aᵢ m → g a ∈ Dᵢ m)
    (δ : DividedPowerStructure Dᵢ) (τ : D) (hτ : τ ∈ Dᵢ d) (n : ℕ) (a : A) :
    evenLift Aᵢ Dᵢ d hd hdeven g hg δ τ hτ (EvenVariableAlgebra.monomial n a) =
      g a * δ.dpow n τ := by
  change evenLiftAddHom Dᵢ g δ τ (EvenVariableAlgebra.monomial n a) = _
  rw [evenLiftAddHom_monomial]

omit [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ] in
/-- The extension restricts to `g` on the coefficient algebra. -/
@[simp] public theorem evenLift_coeffEmbedding (d : ℕ) (hd : 0 < d) (hdeven : Even d)
    (g : A →+* D) (hg : ∀ (m : ℕ) (a : A), a ∈ Aᵢ m → g a ∈ Dᵢ m)
    (δ : DividedPowerStructure Dᵢ) (τ : D) (hτ : τ ∈ Dᵢ d) (a : A) :
    evenLift Aᵢ Dᵢ d hd hdeven g hg δ τ hτ (EvenVariableAlgebra.coeffEmbedding a) = g a := by
  rw [EvenVariableAlgebra.coeffEmbedding_apply, evenLift_monomial,
    δ.dpow_zero (mem_positiveEvenPart_of_even Dᵢ d hd hdeven hτ), mul_one]

omit [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ] in
/-- The extension sends the divided-power monomial `T⁽ⁿ⁾` to `γₙ τ`. -/
public theorem evenLift_monomial_one (d : ℕ) (hd : 0 < d) (hdeven : Even d) (g : A →+* D)
    (hg : ∀ (m : ℕ) (a : A), a ∈ Aᵢ m → g a ∈ Dᵢ m)
    (δ : DividedPowerStructure Dᵢ) (τ : D) (hτ : τ ∈ Dᵢ d) (n : ℕ) :
    evenLift Aᵢ Dᵢ d hd hdeven g hg δ τ hτ (EvenVariableAlgebra.monomial n 1) =
      δ.dpow n τ := by
  rw [evenLift_monomial, map_one, one_mul]

omit [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ] in
/-- The extension is graded when the adjoined variable is sent to a homogeneous element of the
same degree. -/
public theorem evenLift_mem_grade (d : ℕ) (hd : 0 < d) (hdeven : Even d) (g : A →+* D)
    (hg : ∀ (m : ℕ) (a : A), a ∈ Aᵢ m → g a ∈ Dᵢ m)
    (δ : DividedPowerStructure Dᵢ) (τ : D) (hτ : τ ∈ Dᵢ d) (m : ℕ)
    (x : EvenVariableAlgebra A) (hx : x ∈ EvenVariableAlgebra.grade Aᵢ d m) :
    evenLift Aᵢ Dᵢ d hd hdeven g hg δ τ hτ x ∈ Dᵢ m := by
  refine EvenVariableAlgebra.homogeneous_induction_on hx ?_ ?_ ?_
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro n a hn ha
    rw [evenLift_monomial]
    have hdpow := dpow_mem_grade_of_even Dᵢ d hd hdeven δ τ hτ n
    have h := SetLike.GradedMul.mul_mem (hg _ a ha) hdpow
    rwa [show m - n * d + n * d = m by omega] at h
  · intro y z hy hz hy' hz'
    rw [map_add]
    exact Submodule.add_mem _ hy' hz'

omit [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ] in
/-- A ring homomorphism out of an even-variable divided-power extension is determined by its
restriction to the coefficient algebra together with its values on the divided-power monomials
`T⁽ⁿ⁾`. -/
public theorem evenLift_unique (d : ℕ) (hd : 0 < d) (hdeven : Even d) (g : A →+* D)
    (hg : ∀ (m : ℕ) (a : A), a ∈ Aᵢ m → g a ∈ Dᵢ m)
    (δ : DividedPowerStructure Dᵢ) (τ : D) (hτ : τ ∈ Dᵢ d)
    (G : EvenVariableAlgebra A →+* D)
    (hGcoeff : ∀ a : A, G (EvenVariableAlgebra.coeffEmbedding a) = g a)
    (hGmon : ∀ n : ℕ, G (EvenVariableAlgebra.monomial n 1) = δ.dpow n τ) :
    G = evenLift Aᵢ Dᵢ d hd hdeven g hg δ τ hτ := by
  have hsplit : ∀ (n : ℕ) (a : A), EvenVariableAlgebra.monomial n a =
      EvenVariableAlgebra.coeffEmbedding a * EvenVariableAlgebra.monomial n 1 := by
    intro n a
    rw [EvenVariableAlgebra.coeffEmbedding_apply, EvenVariableAlgebra.monomial_mul_monomial]
    simp
  have hGmon' : ∀ (n : ℕ) (a : A),
      G (EvenVariableAlgebra.monomial n a) = g a * δ.dpow n τ := by
    intro n a
    rw [hsplit n a, map_mul, hGcoeff, hGmon]
  ext x
  induction x using EvenVariableAlgebra.induction_on with
  | zero => rw [map_zero, map_zero]
  | add n a y hy => rw [map_add, map_add, hy, hGmon' n a, evenLift_monomial]

end EvenLift

end DividedPowers.TateResolution

end
