module

public import Mathlib.RingTheory.Discriminant
public import StacksCore.Algebra.QuotSq

/-! # Discriminant -/

@[expose] public section

open Matrix Module QuotSq

namespace Algebra

/-- **Stacks 0BIM**.
The discriminant of an `R`-algebra `S` as an element of `QuotSq R`: when `S` is finite free over
`R`, return the class of `discr R b` for any chosen basis `b` (the class is independent of the
basis); otherwise return `0`. -/
@[stacks 0BIM]
noncomputable def discr' (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] : QuotSq R :=
  open scoped Classical in
  if h : Free R S ∧ Module.Finite R S then
    have _ := h.1; have _ := h.2
    QuotSq.mk R (discr R (Free.chooseBasis R S))
  else 0

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- **Stacks 0BIM**.
For any `R`-basis `b` of `S`, the class of the basis-discriminant `discr R b` in `QuotSq R`
agrees with `discr' R S`, witnessing that the latter is well-defined independently of the
chosen basis. -/
@[stacks 0BIM]
theorem mk_discr_eq_discr' {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι R S) :
    .mk R (discr R b) = discr' R S := by
  nontriviality R
  have := Free.of_basis b
  have := Finite.of_basis b
  rw [discr', dite_eq_left ⟨‹_›, ‹_›⟩, mk_eq_iff_isUnit]
  generalize Free.chooseBasis R S = b'
  have e := b.indexEquiv b'
  simp_rw [← discr_reindex _ _ e.symm, ← b'.coe_reindex]
  generalize b'.reindex e.symm = b'
  have := b.invertibleToMatrix b'
  refine ⟨(b.toMatrix b').det, by simp [← isUnit_iff_isUnit_det, isUnit_of_invertible], ?_⟩
  nth_rw 2 [show ⇑b' = (b.toMatrix b')ᵀ.map (algebraMap R S) *ᵥ b by
    ext; simp [mulVec_eq_sum, mul_comm (b _), ← Algebra.smul_def]]
  rw [discr_of_matrix_mulVec, det_transpose]

/-- If `S` is not finite free over `R`, the discriminant `discr' R S` is `0`. -/
theorem discr'_eq_zero (h : ¬(Free R S ∧ Module.Finite R S)) : discr' R S = 0 := by simp [discr', h]

/-- The discriminant `discr' R S` is invariant under `R`-algebra isomorphisms. -/
theorem _root_.AlgEquiv.discr'_eq {A : Type*} [CommRing A] [Algebra R A] (e : S ≃ₐ[R] A) :
    discr' R S = discr' R A := by
  classical
  by_cases h : Free R S ∧ Module.Finite R S
  · obtain ⟨_, _⟩ := h
    rw [← mk_discr_eq_discr' (Free.chooseBasis R S), discr_eq_discr_of_algEquiv _ e,
      ← AlgEquiv.coe_toLinearEquiv e, ← Basis.coe_map, mk_discr_eq_discr']
  · have h' := by simpa only [Free.iff_of_equiv e.toLinearEquiv,
      Module.Finite.equiv_iff e.toLinearEquiv] using h
    rw [discr'_eq_zero h, discr'_eq_zero h']

end Algebra
