module

public import StacksCore.Algebra.Algebra.Subalgebra.DivisionRing
public import StacksCore.Tactic.StacksAttribute

/-!
# Maximal subfields of a central division algebra

A maximal subfield `K` of a finite-dimensional central division algebra `D` over a field `k`
satisfies `dim D = (dim K)^2` (`Subalgebra.finrank_eq_finrank_sq_of_maximal_isField`, Stacks
074W). The input is that a subalgebra of a finite-dimensional division algebra is a field
exactly when it is commutative (`Subalgebra.isField_iff_isMulCommutative`), so maximal
subfields are maximal commutative subalgebras, to which 074V applies.
-/

@[expose] public section

open scoped IsMulCommutative

variable {k D : Type*} [Field k] [DivisionRing D] [Algebra k D]

/-- A subalgebra of a finite-dimensional division algebra is a field if and only if it is
commutative. -/
theorem Subalgebra.isField_iff_isMulCommutative [FiniteDimensional k D] (L : Subalgebra k D) :
    IsField L ↔ IsMulCommutative L :=
  ⟨fun h ↦ ⟨⟨h.mul_comm⟩⟩, fun _ ↦ letI := L.fieldOfIsMulCommutative; Field.toIsField L⟩

/-- **Stacks 074W**: the dimension of a finite-dimensional central division algebra `D` over
`k` is the square of the dimension of any maximal subfield `K ⊆ D`.

A subfield is a subalgebra that is a field, and `K` is maximal among those. Every commutative
subalgebra of `D` is a field (`Subalgebra.isField_iff_isMulCommutative`), so `K` is a maximal
commutative subalgebra, hence self-centralizing (074V (iii) ⇒ (ii),
`Subalgebra.maximal_comm_iff_self_centralizer`), and 074V (ii) ⇒ (i)
(`Subalgebra.isMaximal_comm_iff_finrank`) gives the dimension count. -/
@[stacks 074W "maximal subfield: `K` maximal among subalgebras of `D` that are fields; \
the conclusion `[D : k] = [K : k]^2` as `finrank k D = finrank k K ^ 2`"]
theorem Subalgebra.finrank_eq_finrank_sq_of_maximal_isField [FiniteDimensional k D]
    [Algebra.IsCentral k D] (K : Subalgebra k D)
    (hK : Maximal (fun S : Subalgebra k D ↦ IsField S) K) :
    Module.finrank k D = Module.finrank k K ^ 2 := by
  have h : (fun S : Subalgebra k D ↦ IsField S) = fun S : Subalgebra k D ↦ IsMulCommutative S :=
    funext fun S ↦ propext S.isField_iff_isMulCommutative
  rw [h] at hK
  have := hK.prop
  let : Field ↥K := K.fieldOfIsMulCommutative
  rw [sq]
  exact K.isMaximal_comm_iff_finrank.1 ((Subalgebra.maximal_comm_iff_self_centralizer K).1 hK)
