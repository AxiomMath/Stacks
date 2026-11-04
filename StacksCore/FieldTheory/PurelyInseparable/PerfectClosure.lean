module

import Mathlib.FieldTheory.Minpoly.IsConjRoot
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import StacksCore.Algebra.Algebra.Subalgebra.Basic
import StacksCore.Data.Finset.Card
import StacksCore.Tactic.StacksAttribute

/-! # Perfect closure -/

@[expose] public section

add_to_stacks 030M perfectClosure
add_to_stacks 09HE "1" perfectClosure
add_to_stacks 030M "First part of 2" perfectClosure.isPurelyInseparable
add_to_stacks 030M "First part of 3" separableClosure_inf_perfectClosure

open IntermediateField Polynomial Finset

variable (F E : Type*) [Field F] [Field E] [Algebra F E]

theorem perfectClosure_eq_fixedField_top_of_normal [Normal F E] :
    perfectClosure F E = fixedField ⊤ := by
  ext x
  have hx : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  classical
  rw [mem_fixedField_iff, mem_perfectClosure_iff_natSepDegree_eq_one,
    natSepDegree_eq_of_splits (E := E) _ (Normal.splits ‹_› _),
    card_eq_one_iff_of_mem (x := x) (by simp [minpoly.ne_zero hx])]
  simp_rw [Finset.ext_iff, Multiset.mem_toFinset, ← isConjRoot_iff_mem_minpoly_aroots hx,
    mem_singleton, IsConjRoot.comm (x := x), isConjRoot_iff_exists_algEquiv,
    Subgroup.mem_top, true_implies]
  exact ⟨fun h g ↦ (h _).mp ⟨g, rfl⟩, by aesop⟩

noncomputable instance (priority := high) perfectClosure.algebra
    (F E K : Type*) [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra E K] [Algebra F K] [IsScalarTower F E K] :
    Algebra (perfectClosure F E) (perfectClosure F K) :=
  Algebra.ofMapLE <| perfectClosure.map_le_of_algHom (Algebra.algHom F E K)

instance (F E K : Type*) [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra E K] [Algebra F K] [IsScalarTower F E K] :
    IsScalarTower (perfectClosure F E) (perfectClosure F K) K :=
  IsScalarTower.ofMapLE <| perfectClosure.map_le_of_algHom (Algebra.algHom F E K)

instance [Normal F E] : Algebra.IsSeparable (perfectClosure F E) E where
  isSeparable' x := by
    -- first reduce to the finite (normal) case
    let N := normalClosure F F⟮x⟯ E
    have := adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := F) x)
    suffices IsSeparable (perfectClosure F N) x from this.tower_top _
    have hxN : x ∈ N := le_normalClosure _ <| subset_adjoin _ _ (by simp)
    suffices Algebra.IsSeparable (perfectClosure F N) N from
      (Algebra.IsSeparable.isSeparable (perfectClosure F N) (⟨x, hxN⟩ : N)).map
        (Algebra.algHom _ _ E) (RingHom.injective _)
    -- then use finite Galois theory
    rw [perfectClosure_eq_fixedField_top_of_normal]
    exact FixedPoints.isSeparable _ _

/-- **Stacks 030N** (second part of 2).
For a normal field extension `E/F`, the extension `E` over the perfect closure of `F`
in `E` is Galois. -/
@[stacks 030M "Second part of 2"]
instance perfectClosure.isGalois [Normal F E] : IsGalois (perfectClosure F E) E where

theorem perfectClosure_le {F E : Type*} [Field F] [Field E] [Algebra F E]
    (L : IntermediateField F E) [Algebra.IsSeparable L E] : perfectClosure F E ≤ L := by
  rintro x ⟨n, y, hyx⟩
  have : x ∈ perfectClosure L E := ⟨n, algebraMap F L y, by
    simp [hyx, ringExpChar.eq L (ringExpChar F)]⟩
  rw [perfectClosure.eq_bot_of_isSeparable L E] at this
  simpa [mem_bot]

/-- This theorem requires the assumption `Algebra.IsSeparable (perfectClosure F E) E`, which is
true if `E/F` is separable, or if `E/F` is normal. It is not true in general. -/
theorem perfectClosure_le_iff
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsSeparable (perfectClosure F E) E]
    (L : IntermediateField F E) :
    perfectClosure F E ≤ L ↔ Algebra.IsSeparable L E := by
  refine ⟨fun h ↦ ?_, fun _ ↦ perfectClosure_le _⟩
  let := (Subalgebra.inclusion h).toAlgebra
  have : IsScalarTower (perfectClosure F E) L E := .of_algebraMap_eq fun _ ↦ rfl
  exact Algebra.isSeparable_tower_top_of_isSeparable (perfectClosure F E) _ _

/-- This theorem is the "uniqueness" part of a characterisation of `perfectClosure`. Note that
the "existence part" might not hold, i.e. in general we do not necessarily have
`Algebra.IsSeparable (perfectClosure F E) E`. -/
theorem eq_perfectClosure {F E : Type*} [Field F] [Field E] [Algebra F E]
    (L : IntermediateField F E) [IsPurelyInseparable F L] [Algebra.IsSeparable L E] :
    L = perfectClosure F E :=
  le_antisymm (le_perfectClosure F E L) (perfectClosure_le L)

/-- **Stacks 030N** (second part of 3).
For a normal field extension `E/F`, the separable closure and the perfect closure of
`F` in `E` together generate the whole extension `E`. -/
@[stacks 030M "Second part of 3"]
theorem separableClosure_sup_perfectClosure [Normal F E] :
    separableClosure F E ⊔ perfectClosure F E = ⊤ :=
  eq_top_iff.mpr fun x _ ↦
  let L := separableClosure F E ⊔ perfectClosure F E
  have : Algebra.IsSeparable L E := (perfectClosure_le_iff _).mp (by simp [L])
  have : IsPurelyInseparable L E := (separableClosure_le_iff _ _ _).mp (by simp [L])
  let ⟨x, hx⟩ := IsPurelyInseparable.surjective_algebraMap_of_isSeparable L E x
  hx ▸ x.2
