module

public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.GaloisSide
public import StacksFrontier.NumberTheory.Drinfeld.BrauerNesbitt

/-!
# Conjugation invariance of the conclusion of Theorem 03VT

The conclusion of Stacks Theorem 03VT (Drinfeld) is a continuous, absolutely irreducible
`ρ : π₁(X) → GL₂(E)` compatible with the eigenvalues `t_v`, `u_v` of an eigenform. In Drinfeld's
construction `ρ` is only produced up to conjugation (as the `π`-isotypic part of a cohomology
group, with a basis chosen at the end), and it is identified with other constructions through
the Brauer–Nesbitt theorem, which also only gives conjugacy. This file records that every part of
the conclusion is invariant under conjugation by `P ∈ GL₂(E)`, and that two absolutely
irreducible representations with the same traces are conjugate.

## Main results

* `Stacks.Drinfeld.isFrobeniusCompatible_conj_iff`,
  `Stacks.Drinfeld.isAbsolutelyIrreducible_conj_iff`, `Stacks.Drinfeld.continuous_conj`:
  invariance under conjugation.
* `Stacks.Drinfeld.IsAbsolutelyIrreducible.isSemisimpleRepresentation`: absolutely
  irreducible (Burnside's form) implies semisimple.
* `Stacks.Drinfeld.exists_conj_of_isAbsolutelyIrreducible`: two absolutely irreducible
  `ρ, ρ' : G → GL₂(E)`, `E` of characteristic zero, with equal traces are conjugate.
-/

@[expose] public noncomputable section

open AlgebraicGeometry Stacks.Adeles Stacks.Adeles.GlobalFunctionField

namespace Stacks.Drinfeld

variable {G : Type*} [Group G] {E : Type*} [Field E]

/-- The conjugate `g ↦ P ρ(g) P⁻¹` of `ρ : G → GL₂(E)`. -/
def conjRep (P : Matrix.GeneralLinearGroup (Fin 2) E)
    (ρ : G →* Matrix.GeneralLinearGroup (Fin 2) E) : G →* Matrix.GeneralLinearGroup (Fin 2) E :=
  (MulAut.conj P).toMonoidHom.comp ρ

/-- The value of `conjRep P ρ` at `g` is `P * ρ g * P⁻¹`. -/
theorem conjRep_apply (P : Matrix.GeneralLinearGroup (Fin 2) E)
    (ρ : G →* Matrix.GeneralLinearGroup (Fin 2) E) (g : G) :
    conjRep P ρ g = P * ρ g * P⁻¹ := rfl

/-- The underlying matrix of `conjRep P ρ g` is the matrix product `P * ρ g * P⁻¹`. -/
theorem coe_conjRep_apply (P : Matrix.GeneralLinearGroup (Fin 2) E)
    (ρ : G →* Matrix.GeneralLinearGroup (Fin 2) E) (g : G) :
    (conjRep P ρ g : Matrix (Fin 2) (Fin 2) E) =
      (P : Matrix (Fin 2) (Fin 2) E) * (ρ g : Matrix (Fin 2) (Fin 2) E) *
        ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) := rfl

/-- Conjugating by `P` and then by `P⁻¹` recovers `ρ`. -/
theorem conjRep_inv_conjRep (P : Matrix.GeneralLinearGroup (Fin 2) E)
    (ρ : G →* Matrix.GeneralLinearGroup (Fin 2) E) : conjRep P⁻¹ (conjRep P ρ) = ρ := by
  ext g : 1
  rw [conjRep_apply, conjRep_apply, inv_inv]
  group

/-- Conjugation preserves traces. -/
theorem trace_conjRep (P : Matrix.GeneralLinearGroup (Fin 2) E)
    (ρ : G →* Matrix.GeneralLinearGroup (Fin 2) E) (g : G) :
    Matrix.trace (conjRep P ρ g : Matrix (Fin 2) (Fin 2) E) =
      Matrix.trace (ρ g : Matrix (Fin 2) (Fin 2) E) := by
  rw [coe_conjRep_apply, Matrix.trace_mul_cycle, Units.inv_mul, one_mul]

/-- Conjugation preserves determinants. -/
theorem det_conjRep (P : Matrix.GeneralLinearGroup (Fin 2) E)
    (ρ : G →* Matrix.GeneralLinearGroup (Fin 2) E) (g : G) :
    Matrix.det (conjRep P ρ g : Matrix (Fin 2) (Fin 2) E) =
      Matrix.det (ρ g : Matrix (Fin 2) (Fin 2) E) := by
  rw [coe_conjRep_apply, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul,
    Units.inv_mul, Matrix.det_one, one_mul]

/-- The span of the image of a conjugate is the conjugate of the span; in particular Burnside's
condition `span = M₂(E)` is preserved. -/
theorem isAbsolutelyIrreducible_conj (P : Matrix.GeneralLinearGroup (Fin 2) E)
    {ρ : G →* Matrix.GeneralLinearGroup (Fin 2) E} (h : IsAbsolutelyIrreducible ρ) :
    IsAbsolutelyIrreducible (conjRep P ρ) := by
  unfold IsAbsolutelyIrreducible at h ⊢
  set A := (P : Matrix (Fin 2) (Fin 2) E)
  set B := ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 2) E) : Matrix (Fin 2) (Fin 2) E)
  let c : Matrix (Fin 2) (Fin 2) E →ₗ[E] Matrix (Fin 2) (Fin 2) E :=
    (LinearMap.mulRight E B).comp (LinearMap.mulLeft E A)
  have hc : ∀ M, c M = A * M * B := fun M => rfl
  refine eq_top_iff.2 fun M _ => ?_
  have hM : B * M * A ∈ Submodule.span E (Set.range fun g => (ρ g : Matrix (Fin 2) (Fin 2) E)) :=
    h ▸ Submodule.mem_top
  have himg := Submodule.mem_map_of_mem (f := c) hM
  rw [Submodule.map_span, ← Set.range_comp] at himg
  have : c (B * M * A) = M := by
    rw [hc, ← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]
  rw [this] at himg
  convert himg using 3
  ext1 g
  simp only [Function.comp_apply, hc]
  rfl

/-- `conjRep P ρ` is absolutely irreducible if and only if `ρ` is. -/
theorem isAbsolutelyIrreducible_conj_iff (P : Matrix.GeneralLinearGroup (Fin 2) E)
    (ρ : G →* Matrix.GeneralLinearGroup (Fin 2) E) :
    IsAbsolutelyIrreducible (conjRep P ρ) ↔ IsAbsolutelyIrreducible ρ :=
  ⟨fun h => conjRep_inv_conjRep P ρ ▸ isAbsolutelyIrreducible_conj P⁻¹ h,
    isAbsolutelyIrreducible_conj P⟩

/-- Conjugation preserves continuity of the matrix coefficients. -/
theorem continuous_conj [TopologicalSpace G] [TopologicalSpace E] [IsTopologicalRing E]
    (P : Matrix.GeneralLinearGroup (Fin 2) E) {ρ : G →* Matrix.GeneralLinearGroup (Fin 2) E}
    (h : Continuous fun g => (ρ g : Matrix (Fin 2) (Fin 2) E)) :
    Continuous fun g => (conjRep P ρ g : Matrix (Fin 2) (Fin 2) E) := by
  simp only [coe_conjRep_apply]
  exact (continuous_const.matrix_mul h).matrix_mul continuous_const

section Frobenius

variable {X : Scheme} [IsIntegral X] (base : GeometricPoint X)
  {Ω : Type*} [Field Ω]

/-- **Frobenius compatibility is invariant under conjugation.** -/
theorem isFrobeniusCompatible_conj_iff (P : Matrix.GeneralLinearGroup (Fin 2) E)
    (ρ : EtaleFundamentalGroup X base →* Matrix.GeneralLinearGroup (Fin 2) E) (j : E →+* Ω)
    (t u : Place X.functionField → Ω) :
    IsFrobeniusCompatible base (conjRep P ρ) j t u ↔ IsFrobeniusCompatible base ρ j t u := by
  unfold IsFrobeniusCompatible
  simp only [trace_conjRep, det_conjRep]

end Frobenius

/-- An absolutely irreducible `ρ : G → GL₂(E)` (Burnside's form) is semisimple. -/
theorem IsAbsolutelyIrreducible.isSemisimpleRepresentation [CharZero E]
    {ρ : G →* Matrix.GeneralLinearGroup (Fin 2) E} (h : IsAbsolutelyIrreducible ρ) :
    (Stacks.EtaleCohomology.matrixRepresentation ρ).IsSemisimpleRepresentation :=
  isSemisimpleRepresentation_of_span_eq_top ρ h

/-- **Brauer–Nesbitt for absolutely irreducible two-dimensional representations.** Over a field of
characteristic zero, two absolutely irreducible `ρ, ρ' : G → GL₂(E)` with the same traces are
conjugate. -/
theorem exists_conj_of_isAbsolutelyIrreducible [CharZero E]
    {ρ ρ' : G →* Matrix.GeneralLinearGroup (Fin 2) E} (hρ : IsAbsolutelyIrreducible ρ)
    (hρ' : IsAbsolutelyIrreducible ρ')
    (htr : ∀ g, Matrix.trace (ρ g : Matrix (Fin 2) (Fin 2) E) =
      Matrix.trace (ρ' g : Matrix (Fin 2) (Fin 2) E)) :
    ∃ P : Matrix.GeneralLinearGroup (Fin 2) E, ρ' = conjRep P ρ := by
  obtain ⟨P, hP⟩ := exists_conj_of_trace_eq ρ ρ'
    (IsAbsolutelyIrreducible.isSemisimpleRepresentation hρ)
    (IsAbsolutelyIrreducible.isSemisimpleRepresentation hρ') htr
  exact ⟨P, MonoidHom.ext hP⟩

end Stacks.Drinfeld
