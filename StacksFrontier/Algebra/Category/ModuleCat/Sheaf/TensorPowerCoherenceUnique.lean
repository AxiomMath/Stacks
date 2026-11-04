module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCommutativity
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerIntegerCoherence

/-!
# The coherent multiplication of the integral tensor powers is unique

Let `O` be a sheaf of commutative rings on a site and `L` an invertible sheaf of `O`-modules.
`Stacks.SheafOfModules.TensorPower.TensorPowerCoherence` is the structure bundling the
multiplication isomorphisms `L^{⊗ n} ⊗_O L^{⊗ m} ≅ L^{⊗ (n + m)}` of Tag 01CU with their unit,
associativity and commutativity normalisations. This file proves that its multiplication is
**unique**: any two coherence data on the same `L` have the same `mulIso` in every pair of degrees,
and in particular the same as `Stacks.SheafOfModules.TensorPower.coherentMulIso`.

## Main results

* `Stacks.SheafOfModules.TensorPower.TensorPowerCoherence.mulIso_eq`: two coherence data have the
  same multiplication, in every pair of degrees.
* `Stacks.SheafOfModules.TensorPower.coherentMulIso_eq`: the multiplication of any coherence datum
  is `Stacks.SheafOfModules.TensorPower.coherentMulIso`.
* `Stacks.SheafOfModules.TensorPower.tensorSheafMapIso_refl_right_eq_map`: the tensor product sheaf
  of an isomorphism with an identity is the image of the isomorphism under the right-tensor
  functor.

## Implementation notes

The proof is an induction on the right exponent, in both directions from `0`, using only the right
unit laws in degrees `0` and `1` and associativity. The descending step cancels a tensor product
with the identity of `L^{⊗ 1}`, which uses that the right-tensor functor by the invertible sheaf
`L^{⊗ 1}` is faithful.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v u w

namespace Stacks.SheafOfModules.TensorPower

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-! ### Cancellation of isomorphisms -/

section Cancel

variable {D : Type u} [Category.{v} D] {A B E : D}

/-- An isomorphism composed on the left may be cancelled. -/
theorem iso_cancel_left (a : A ≅ B) {u v : B ≅ E} (h : a ≪≫ u = a ≪≫ v) : u = v :=
  Iso.ext ((cancel_epi a.hom).mp (congrArg Iso.hom h))

/-- An isomorphism composed on the right may be cancelled. -/
theorem iso_cancel_right (r : B ≅ E) {u v : A ≅ B} (h : u ≪≫ r = v ≪≫ r) : u = v :=
  Iso.ext ((cancel_mono r.hom).mp (congrArg Iso.hom h))

end Cancel

/-! ### The tensor product sheaf of an isomorphism with an identity -/

/-- **The tensor product sheaf of an isomorphism with an identity is the image of the isomorphism
under the right-tensor functor.** For `i : M ≅ M'`, the tensor product sheaf of `i` with
`Iso.refl N` is the image of `i` under the functor
`(Stacks.SheafOfModules.Tensor.sheafTensor _).flip.obj N`. -/
theorem tensorSheafMapIso_refl_right_eq_map
    {M M' : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)} (i : M ≅ M')
    (N : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) :
    tensorSheafMapIso O hO i (Iso.refl N) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
          N).mapIso i := by
  apply Iso.ext
  simp only [tensorSheafMapIso]
  congr 1

/-- **An isomorphism is determined by its tensor product with an identity.** If the right-tensor
functor by `N` is an equivalence, then two isomorphisms `i i' : M ≅ M'` whose tensor products with
`Iso.refl N` agree are equal. -/
theorem iso_eq_of_tensorSheafMapIso_refl_right
    {M M' N : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)}
    [((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        N).IsEquivalence]
    {i i' : M ≅ M'}
    (h : tensorSheafMapIso O hO i (Iso.refl N) = tensorSheafMapIso O hO i' (Iso.refl N)) :
    i = i' := by
  rw [tensorSheafMapIso_refl_right_eq_map, tensorSheafMapIso_refl_right_eq_map] at h
  exact Iso.ext (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        N).map_injective
    (congrArg Iso.hom h))

/-! ### Uniqueness of the coherent multiplication -/

namespace TensorPowerCoherence

variable (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
  [IsInvertible O hO L] (c c' : TensorPowerCoherence O hO L)

/-- Two coherence data have the same multiplication in degree `(n, 0)`. -/
theorem mulIso_zero_right_eq (n : ℤ) : c.mulIso n 0 = c'.mulIso n 0 :=
  iso_cancel_right _ ((c.mul_zero_right n).trans (c'.mul_zero_right n).symm)

/-- Two coherence data have the same multiplication in degree `(n, 1)`. -/
theorem mulIso_one_right_eq (n : ℤ) : c.mulIso n 1 = c'.mulIso n 1 :=
  (c.mul_one_right n).trans (c'.mul_one_right n).symm

/-- If two coherence data have the same multiplication in every degree `(k, m)`, then they have the
same multiplication in every degree `(n, m + 1)`. -/
theorem mulIso_succ_right_eq (m : ℤ) (ih : ∀ k : ℤ, c.mulIso k m = c'.mulIso k m) (n : ℤ) :
    c.mulIso n (m + 1) = c'.mulIso n (m + 1) := by
  have h := c.mul_assoc n m 1
  rw [ih n, mulIso_one_right_eq O hO L c c' (n + m), mulIso_one_right_eq O hO L c c' m] at h
  exact iso_cancel_right _ (iso_cancel_left _ (iso_cancel_left _ (h.symm.trans
    (c'.mul_assoc n m 1))))

/-- If two coherence data on an invertible sheaf have the same multiplication in every degree
`(k, m + 1)`, then they have the same multiplication in every degree `(n, m)`. -/
theorem mulIso_pred_right_eq (m : ℤ) (ih : ∀ k : ℤ, c.mulIso k (m + 1) = c'.mulIso k (m + 1))
    (n : ℤ) : c.mulIso n m = c'.mulIso n m := by
  have := isInvertible_tensorPower O hO L 1
  have h := c.mul_assoc n m 1
  rw [ih n, mulIso_one_right_eq O hO L c c' m] at h
  have key := h.trans (c'.mul_assoc n m 1).symm
  rw [mulIso_one_right_eq O hO L c c' (n + m)] at key
  exact iso_eq_of_tensorSheafMapIso_refl_right O hO (iso_cancel_right _ key)

/-- **The multiplication of a coherence datum on the integral tensor powers of an invertible sheaf
of modules is unique.** Any two coherence data have the same multiplication isomorphism in every
pair of degrees. -/
theorem mulIso_eq (n m : ℤ) : c.mulIso n m = c'.mulIso n m := by
  suffices h : ∀ m : ℤ, ∀ n : ℤ, c.mulIso n m = c'.mulIso n m from h m n
  intro m
  induction m using Int.induction_on with
  | zero => exact mulIso_zero_right_eq O hO L c c'
  | succ k ih => exact mulIso_succ_right_eq O hO L c c' (k : ℤ) ih
  | pred k ih =>
      refine mulIso_pred_right_eq O hO L c c' (-(k : ℤ) - 1) ?_
      rw [show -(k : ℤ) - 1 + 1 = -(k : ℤ) from by ring]
      exact ih

end TensorPowerCoherence

/-- **The multiplication of any coherence datum is the coherent multiplication.** For every
coherence datum `c` on `L`, `c.mulIso n m` is
`Stacks.SheafOfModules.TensorPower.coherentMulIso O hO L n m`. -/
theorem coherentMulIso_eq
    (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) [IsInvertible O hO L]
    (c : TensorPowerCoherence O hO L) (n m : ℤ) : c.mulIso n m = coherentMulIso O hO L n m :=
  TensorPowerCoherence.mulIso_eq O hO L c (tensorPowerCoherence O hO L) n m

end Stacks.SheafOfModules.TensorPower

end
