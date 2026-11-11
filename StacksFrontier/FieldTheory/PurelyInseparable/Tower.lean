module

public import Mathlib.FieldTheory.PurelyInseparable.Tower
public import StacksCore.FieldTheory.PurelyInseparable.PerfectClosure
import StacksCore.FieldTheory.PurelyInseparable.Basic
import StacksCore.FieldTheory.SeparableClosure
import StacksCore.Tactic.StacksAttribute

/-! # Separable and perfect closure of a normal extension

For a normal algebraic extension `E / F`, the separable closure `E_sep` and the relative perfect
closure `E_insep` of `F` in `E` satisfy `E = E_sep ⊗[F] E_insep`: the multiplication map
`E_sep ⊗[F] E_insep → E` is an isomorphism of `F`-algebras.

## Main results

* `separableClosure.linearDisjoint_perfectClosure`: `E_sep` and `E_insep` are linearly disjoint
  over `F`.
* `Normal.bijective_productMap_separableClosure_perfectClosure`: for normal `E / F`, the
  multiplication map `E_sep ⊗[F] E_insep → E` is bijective.
* `Normal.separableClosure_perfectClosure_tensorDecomposition`: Stacks 030M, all three parts.

## Partial facts registered in `StacksCore/`

The promoted library already registers single parts of 030M, which stay as they are:

* part 1: `separableClosure.isGalois` (`StacksCore/FieldTheory/SeparableClosure.lean`) and
  `separableClosure.isPurelyInseparable` (`StacksCore/FieldTheory/PurelyInseparable/Basic.lean`);
* part 2: `perfectClosure`, `perfectClosure.isPurelyInseparable` and `perfectClosure.isGalois`
  (`StacksCore/FieldTheory/PurelyInseparable/PerfectClosure.lean`);
* part 3: `separableClosure_inf_perfectClosure` and `separableClosure_sup_perfectClosure`
  (`StacksCore/FieldTheory/PurelyInseparable/PerfectClosure.lean`), which say that `E_sep ∩ E_insep = F`
  and `E_sep ⊔ E_insep = E`; the tensor product statement itself is proved here.
-/

@[expose] public section

open IntermediateField

variable (F E : Type*) [Field F] [Field E] [Algebra F E]

/-- The separable closure and the relative perfect closure of `F` in `E` are linearly disjoint
over `F`. -/
theorem separableClosure.linearDisjoint_perfectClosure :
    (separableClosure F E).LinearDisjoint (perfectClosure F E) :=
  linearDisjoint_of_isPurelyInseparable_of_isSeparable (perfectClosure F E) (separableClosure F E)

/-- For a normal extension `E / F`, the multiplication map
`separableClosure F E ⊗[F] perfectClosure F E → E` is bijective. -/
theorem Normal.bijective_productMap_separableClosure_perfectClosure [Normal F E] :
    Function.Bijective
      (Algebra.TensorProduct.productMap (separableClosure F E).val (perfectClosure F E).val) := by
  refine ⟨?_, ?_⟩
  · exact Subalgebra.linearDisjoint_iff_injective.mp
      (linearDisjoint_iff'.mp (separableClosure.linearDisjoint_perfectClosure F E))
  · rw [← AlgHom.range_eq_top, Algebra.TensorProduct.productMap_range]
    simp only [IntermediateField.range_val]
    rw [← sup_toSubalgebra_of_isAlgebraic _ _ (.inl inferInstance),
      separableClosure_sup_perfectClosure, top_toSubalgebra]

/-- **Stacks 030M.** Let `E / F` be a normal algebraic extension, and let `E_sep` and `E_insep` be
the separable closure and the relative perfect closure of `F` in `E`. Then
1. `E_sep / F` is Galois and `E / E_sep` is purely inseparable;
2. `E_insep / F` is purely inseparable and `E / E_insep` is Galois;
3. `E = E_sep ⊗[F] E_insep`: the multiplication map `E_sep ⊗[F] E_insep → E` is bijective, so it is
  an isomorphism of `F`-algebras. -/
@[stacks 030M "`E_sep` is `separableClosure F E`, `E_insep` is `perfectClosure F E`, which equals
  `E^Aut(E/F)` by `perfectClosure_eq_fixedField_top_of_normal`; part 3 is the bijectivity of the
  multiplication map `E_sep ⊗[F] E_insep → E`."]
theorem Normal.separableClosure_perfectClosure_tensorDecomposition [Normal F E] :
    (IsGalois F (separableClosure F E) ∧ IsPurelyInseparable (separableClosure F E) E) ∧
    (IsPurelyInseparable F (perfectClosure F E) ∧ IsGalois (perfectClosure F E) E) ∧
    Function.Bijective
      (Algebra.TensorProduct.productMap (separableClosure F E).val (perfectClosure F E).val) :=
  ⟨⟨inferInstance, inferInstance⟩, ⟨inferInstance, inferInstance⟩,
    Normal.bijective_productMap_separableClosure_perfectClosure F E⟩
