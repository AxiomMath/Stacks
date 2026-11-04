module

public import Mathlib.Algebra.Central.Defs
public import Mathlib.Data.Matrix.Basic

/-!
# Centrality descends from matrix algebras

Mathlib's `Algebra.IsCentral.matrix` shows that a matrix algebra over a central algebra is
central. This file provides the reverse direction, `Algebra.IsCentral.of_matrix`: if
`Matrix n n D` is central over `K` then so is `D`. The proof reads off a diagonal entry of
the scalar matrix attached to a central element.

This is what lets centrality be transported along a Wedderburn decomposition
`A ≃ₐ[K] Matrix (Fin n) (Fin n) D`, which is how the division-algebra representative of a
Brauer class inherits centrality from the class.
-/

@[expose] public section

namespace Algebra.IsCentral

/-- If a matrix algebra `Matrix n n D` is central over `K`, then so is `D`: a central `d : D`
gives a central scalar matrix, which is therefore in the image of `K`, and comparing a
diagonal entry exhibits `d` in the image of `K`. -/
theorem of_matrix {K D : Type*} [CommSemiring K] [Semiring D] [Algebra K D]
    (n : Type*) [Fintype n] [DecidableEq n] [Nonempty n]
    [h : Algebra.IsCentral K (Matrix n n D)] : Algebra.IsCentral K D where
  out d hd := by
    obtain ⟨i⟩ := ‹Nonempty n›
    have hscalar : Matrix.scalar n d ∈ Subalgebra.center K (Matrix n n D) :=
      Subalgebra.mem_center_iff.mpr fun M =>
        (Matrix.scalar_commute d
          (fun r => (Subalgebra.mem_center_iff.mp hd r).symm) M).symm
    obtain ⟨c, hc⟩ := Algebra.mem_bot.mp (h.out hscalar)
    exact Algebra.mem_bot.mpr ⟨c, by
      simpa [Matrix.algebraMap_matrix_apply] using congrFun (congrFun hc i) i⟩

end Algebra.IsCentral
