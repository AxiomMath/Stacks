module

public import StacksCore.Algebra.BrauerGroup.Basic
public import StacksCore.RingTheory.MatrixAlgebra

/-!
## Base change of Brauer groups

For a field extension `L/K`, base change `A ↦ L ⊗[K] A` induces a monoid homomorphism
`BrauerGroup K →* BrauerGroup L`. It is the identity when `L = K` and is compatible with
towers of field extensions.
-/

@[expose] public section

namespace BrauerGroup

universe u u₂ u₃

open scoped TensorProduct

variable (K : Type u) (L : Type (max u u₂)) [Field K] [Field L] [Algebra K L]

open Algebra.TensorProduct in
/-- Base change along a field extension `L/K` as a monoid homomorphism
`BrauerGroup K →* BrauerGroup L`, sending the class of `A` to the class of `L ⊗[K] A`. -/
def baseChange : BrauerGroup K →* BrauerGroup L where
  toFun := BrauerGroup.map (k := K) L fun A B h ↦ by
    obtain ⟨n, m, hn, hm, ⟨e⟩⟩ := h
    simp only [IsBrauerEquivalent]
    refine ⟨n, m, hn, hm, ⟨?_⟩⟩
    exact (matrixBaseChange K L (Fin n) A).trans <|
      (congr AlgEquiv.refl e).trans <| (matrixBaseChange K L (Fin m) B).symm
  map_one' := by
    rw [← mk_self_eq_one, ← mk_self_eq_one, map_mk]
    exact mk_congr (Algebra.TensorProduct.rid _ _ _)
  map_mul' x y := by
    induction x using BrauerGroup.induction with | h A =>
    induction y using BrauerGroup.induction with | h B =>
    rw [map_mk, map_mk, mk_mul_mk, mk_mul_mk, map_mk]
    refine mk_congr <| ((Algebra.TensorProduct.assoc K K L L A B).symm.trans
      (congr (Algebra.TensorProduct.rid L L (L ⊗[K] A)).symm AlgEquiv.refl)).trans
      (Algebra.TensorProduct.assoc K L L (L ⊗[K] A) L B)

@[simp]
lemma baseChange_mk (A : Type u) [Ring A] [Algebra K A] [FiniteDimensional K A]
    [IsSimpleRing A] [Algebra.IsCentral K A] :
    baseChange K L (BrauerGroup.mk K A) = BrauerGroup.mk L (L ⊗[K] A) := rfl

lemma baseChange_self : baseChange K K = .id (BrauerGroup K) := by
  ext x
  induction x using BrauerGroup.induction with | h A =>
  simp only [baseChange_mk, MonoidHom.id_apply]
  exact mk_congr <| (Algebra.TensorProduct.lid ..)

@[simp]
lemma baseChange_self_apply (x : BrauerGroup K) :
    baseChange K K x = x := by
  simp [baseChange_self]

lemma baseChange_comp (M : Type (max u u₂ u₃)) [Field M] [Algebra L M]
    [Algebra K M] [IsScalarTower K L M] :
    (baseChange L M).comp (baseChange K L) = baseChange.{u, max u₂ u₃} K M := by
  ext x
  induction x using BrauerGroup.induction with | h A =>
  simp only [MonoidHom.comp_apply, baseChange_mk]
  exact mk_congr <| (Algebra.TensorProduct.assoc K L M M L A).symm.trans
    (Algebra.TensorProduct.congr (Algebra.TensorProduct.rid L M M) AlgEquiv.refl)

end BrauerGroup
