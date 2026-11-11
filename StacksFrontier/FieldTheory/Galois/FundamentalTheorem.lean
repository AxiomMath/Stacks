module

public import Mathlib.FieldTheory.Galois.Basic

import StacksCore.Tactic.StacksAttribute

/-!
# The fundamental theorem of Galois theory

Stacks 09DW: let `L/K` be a finite Galois extension with Galois group `G`. Then `K = L^G`, the
map `H ↦ L^H` from subgroups of `G` to subextensions `L/M/K` is a bijection whose inverse maps
`M` to `Gal(L/M)`, and the normal subgroups of `G` correspond exactly to the subextensions `M`
with `M/K` Galois.

Mathlib states the pieces separately: `IsGalois.fixedField_top`,
`IsGalois.intermediateFieldEquivSubgroup` (with `IsGalois.fixedField_fixingSubgroup` and
`IntermediateField.fixingSubgroup_fixedField`), `IsGalois.of_fixedField_normal_subgroup` and
`IsGalois.fixingSubgroup_normal_of_isGalois`. This file collects them into the single statement
of the theorem.

Here `Gal(L/M)` is the subgroup `M.fixingSubgroup` of `G = Gal(L/K)`, which
`IntermediateField.fixingSubgroupEquiv` identifies with the group `Gal(L/M)` of `M`-algebra
automorphisms of `L`, and `L^H` is `IntermediateField.fixedField H`.

## Main results

* `IsGalois.fixedField_bijective_and_isGalois_iff_normal`: the fundamental theorem of Galois
  theory (Stacks 09DW).
-/

@[expose] public section

open IntermediateField

namespace IsGalois

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **Fundamental theorem of Galois theory** (Stacks 09DW). Let `L/K` be a finite Galois
extension with Galois group `G = Gal(L/K)`. Then `K = L^G`; the map `H ↦ L^H` from subgroups of
`G` to intermediate fields `L/M/K` is a bijection whose inverse sends `M` to
`Gal(L/M) = M.fixingSubgroup`; and a subgroup `H` is normal exactly when `L^H/K` is Galois,
equivalently a subextension `M/K` is Galois exactly when `Gal(L/M)` is normal in `G`. -/
@[stacks 09DW "the full statement: K = L^G, the bijection H ↦ L^H with inverse M ↦ Gal(L/M),
and normal subgroups ↔ Galois subextensions"]
theorem fixedField_bijective_and_isGalois_iff_normal [FiniteDimensional K L] [IsGalois K L] :
    fixedField (⊤ : Subgroup Gal(L/K)) = ⊥ ∧
    Function.Bijective (fixedField : Subgroup Gal(L/K) → IntermediateField K L) ∧
    (∀ H : Subgroup Gal(L/K), (fixedField H).fixingSubgroup = H) ∧
    (∀ M : IntermediateField K L, fixedField M.fixingSubgroup = M) ∧
    (∀ H : Subgroup Gal(L/K), H.Normal ↔ IsGalois K (fixedField H)) ∧
    (∀ M : IntermediateField K L, M.fixingSubgroup.Normal ↔ IsGalois K M) := by
  have hleft : ∀ H : Subgroup Gal(L/K), (fixedField H).fixingSubgroup = H :=
    fun H ↦ fixingSubgroup_fixedField H
  have hright : ∀ M : IntermediateField K L, fixedField M.fixingSubgroup = M :=
    fun M ↦ fixedField_fixingSubgroup M
  have hnormal : ∀ H : Subgroup Gal(L/K), H.Normal ↔ IsGalois K (fixedField H) := by
    intro H
    refine ⟨fun _ ↦ inferInstance, fun _ ↦ ?_⟩
    rw [← hleft H]
    exact fixingSubgroup_normal_of_isGalois (fixedField H)
  refine ⟨fixedField_top, ⟨fun H₁ H₂ h ↦ ?_, fun M ↦ ⟨M.fixingSubgroup, hright M⟩⟩, hleft, hright,
    hnormal, fun M ↦ ?_⟩
  · rw [← hleft H₁, ← hleft H₂, h]
  · refine ⟨fun h ↦ ?_, fun _ ↦ fixingSubgroup_normal_of_isGalois M⟩
    have := (hnormal M.fixingSubgroup).1 h
    rwa [hright M] at this

end IsGalois
