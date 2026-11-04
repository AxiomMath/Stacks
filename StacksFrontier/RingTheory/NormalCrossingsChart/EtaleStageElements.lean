module

public import StacksFrontier.RingTheory.Etale.IndEtaleStageDescent

/-!
# Realizing finitely many elements of an ind-étale algebra on an étale stage

An ind-étale algebra is a filtered colimit of étale algebras, so finitely many of its elements
come from a single étale stage. This is the form in which the strict henselization of a ring at a
prime is used as a limit of étale neighbourhoods: a regular system of parameters of
`𝒪^{sh}_{X, p}` is realized by functions on an affine étale neighbourhood of `p`.

## Main results

* `StacksDraft.exists_etale_algHom_forall_eq`: a finite family of elements of an ind-étale
  algebra is the image of a family of elements of an étale stage.

## Implementation notes

The family of elements is packaged as the `C`-algebra map out of a polynomial ring in finitely
many variables that sends the variables to them; that map is of finite presentation, so
`StacksDraft.exists_etale_stage_of_indEtale` applies with `A = C`. Its statement is phrased with
the base change `A ⊗[C] Λ`, which for `A = C` is `C ⊗[C] Λ`; the two unitors
`Algebra.TensorProduct.lid` translate between that and `Λ` itself, and the only computation is
their naturality in the second variable, which is checked on pure tensors.

## References

* [Stacks Project, Tag 07C3](https://stacks.math.columbia.edu/tag/07C3)
* [Stacks Project, Tag 04GP](https://stacks.math.columbia.edu/tag/04GP)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace StacksDraft

/-- The unitor `C ⊗[C] D ≃ D` is natural in `D`. -/
private theorem lid_map_id {C D Λ : Type u} [CommRing C] [CommRing D] [CommRing Λ]
    [Algebra C D] [Algebra C Λ] (h : D →ₐ[C] Λ) (z : C ⊗[C] D) :
    Algebra.TensorProduct.lid C Λ (Algebra.TensorProduct.map (AlgHom.id C C) h z) =
      h (Algebra.TensorProduct.lid C D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul c d => simp
  | add z w hz hw => simp [hz, hw]

/-- **Finitely many elements of an ind-étale algebra come from an étale stage.** If `Λ` is a
filtered colimit of étale `C`-algebras and `x : Fin n → Λ`, then there is an étale `C`-algebra `B`
with a `C`-algebra map `h : B → Λ` and elements `y : Fin n → B` with `h (y i) = x i`. -/
public theorem exists_etale_algHom_forall_eq {C Λ : Type u} [CommRing C] [CommRing Λ]
    [Algebra C Λ] (hΛ : StacksDraft.IndEtale C Λ) {n : ℕ} (x : Fin n → Λ) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra C B), Algebra.Etale C B ∧
      ∃ (h : B →ₐ[C] Λ) (y : Fin n → B), ∀ i, h (y i) = x i := by
  set f : MvPolynomial (Fin n) C →ₐ[C] C ⊗[C] Λ :=
    (Algebra.TensorProduct.lid C Λ).symm.toAlgHom.comp (MvPolynomial.aeval x) with hf
  obtain ⟨B, _, _, hBet, h, g, hcomp⟩ :=
    StacksDraft.exists_etale_stage_of_indEtale (A := C) (A' := MvPolynomial (Fin n) C) hΛ
      inferInstance f
  refine ⟨B, inferInstance, inferInstance, hBet, h,
    fun i => Algebra.TensorProduct.lid C B (g (MvPolynomial.X i)), fun i => ?_⟩
  have hgi := congrArg (fun k : MvPolynomial (Fin n) C →ₐ[C] C ⊗[C] Λ => k (MvPolynomial.X i))
    hcomp
  simp only [AlgHom.coe_comp, Function.comp_apply] at hgi
  rw [← lid_map_id h (g (MvPolynomial.X i)), hgi, hf]
  simp

end StacksDraft

end
