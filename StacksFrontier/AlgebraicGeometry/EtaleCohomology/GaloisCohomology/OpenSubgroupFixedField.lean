module

public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# The fixed field of an open subgroup of an infinite Galois group

Let `Ω/K` be a Galois extension and let `U` be an open subgroup of `Gal(Ω/K)`.  The infinite
Galois correspondence identifies `U` with the Galois group of `Ω` over the fixed field
`L := IntermediateField.fixedField U`, which is a *finite* subextension of `Ω/K`. This file
gives that identification as a `ContinuousMulEquiv` `Gal(Ω/L) ≃ₜ* U` whose underlying map does
not change how an automorphism acts on `Ω`.

## Main results

* `Stacks.GaloisCohomology.finiteDimensional_fixedField_of_isOpen`: the fixed field of an open
  subgroup of `Gal(Ω/K)` is finite-dimensional over `K`.
* `Stacks.GaloisCohomology.fixingSubgroup_fixedField_of_isOpen`: an open subgroup is the fixing
  subgroup of its fixed field, i.e. the Galois correspondence is defined on it.
* `Stacks.GaloisCohomology.range_restrictScalarsHom`: the image of the
  restriction-of-scalars homomorphism `AlgEquiv.restrictScalarsHom K : Gal(Ω/L) →* Gal(Ω/K)` is
  `L.fixingSubgroup`, hence `Stacks.GaloisCohomology.range_restrictScalarsHom_fixedField`: it is
  `U` when `L` is the fixed field of an open `U`.
* `Stacks.GaloisCohomology.continuous_restrictScalarsHom`: that same homomorphism is continuous
  for the Krull topologies when `L/K` is finite.
* `Stacks.GaloisCohomology.fixedFieldContinuousMulEquiv`: the `ContinuousMulEquiv`
  `Gal(Ω/fixedField U) ≃ₜ* U` for `U` open, together with
  `fixedFieldContinuousMulEquiv_apply_apply` saying that it changes no value of an automorphism
  (and `coe_fixedFieldContinuousMulEquiv`, `fixedFieldContinuousMulEquiv_symm_apply_apply`),
  and the transfer of local constancy along it in one and in two variables
  (`isLocallyConstant_comp_fixedFieldContinuousMulEquiv_iff` and the primed version).
* `Stacks.GaloisCohomology.finiteDimensional_tower` and
  `Stacks.GaloisCohomology.finiteDimensional_restrictScalars`: a finite extension of a finite
  subextension of `Ω/K` is finite over `K`.

## References

* [Stacks Project, Tag 0BMJ](https://stacks.math.columbia.edu/tag/0BMJ), the Krull topology on an
  infinite Galois group.
* [Stacks Project, Tag 03QV](https://stacks.math.columbia.edu/tag/03QV)
-/

@[expose] public noncomputable section

open IntermediateField

namespace Stacks.GaloisCohomology

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

section RestrictScalars

variable (L : IntermediateField K Ω)

/-- The image of `AlgEquiv.restrictScalarsHom K : Gal(Ω/L) →* Gal(Ω/K)` is the subgroup fixing
`L`. -/
theorem range_restrictScalarsHom :
    (AlgEquiv.restrictScalarsHom K (S := ↥L) (A := Ω)).range = L.fixingSubgroup := by
  ext g
  refine ⟨?_, fun hg ↦ ⟨fixingSubgroupEquiv L ⟨g, hg⟩, ?_⟩⟩
  · rintro ⟨σ, rfl⟩
    exact (IntermediateField.mem_fixingSubgroup_iff L _).2 fun x hx ↦ σ.commutes ⟨x, hx⟩
  · exact AlgEquiv.ext fun _ ↦ rfl

/-- The restriction of scalars `AlgEquiv.restrictScalarsHom K : Gal(Ω/L) →* Gal(Ω/K)` is
continuous for the Krull topologies, when `L/K` is finite. -/
theorem continuous_restrictScalarsHom [FiniteDimensional K L] :
    Continuous (AlgEquiv.restrictScalarsHom K (S := ↥L) (A := Ω)) := by
  refine continuous_of_continuousAt_one _ (continuousAt_def.2 fun N hN ↦ ?_)
  rw [map_one, krullTopology_mem_nhds_one_iff] at hN
  obtain ⟨M, _, hM⟩ := hN
  rw [krullTopology_mem_nhds_one_iff]
  have hle : L ≤ M ⊔ L := le_sup_right
  have : FiniteDimensional K ↥(extendScalars hle) :=
    inferInstanceAs (FiniteDimensional K ↥(M ⊔ L))
  refine ⟨extendScalars hle, Module.Finite.right K ↥L _, fun σ hσ ↦ hM ?_⟩
  exact (IntermediateField.mem_fixingSubgroup_iff M _).2 fun x hx ↦
    (IntermediateField.mem_fixingSubgroup_iff (extendScalars hle) σ).1 hσ x
      ((mem_extendScalars hle).2 ((le_sup_left : M ≤ M ⊔ L) hx))

end RestrictScalars

section OpenSubgroup

variable [IsGalois K Ω] (U : Subgroup Gal(Ω/K)) (hU : IsOpen (U : Set Gal(Ω/K)))

include hU

/-- An open subgroup of `Gal(Ω/K)` is the fixing subgroup of its fixed field. -/
theorem fixingSubgroup_fixedField_of_isOpen : (fixedField U).fixingSubgroup = U :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨U, OpenSubgroup.isClosed ⟨U, hU⟩⟩

/-- The fixed field of an open subgroup of `Gal(Ω/K)` is a finite extension of `K`. -/
theorem finiteDimensional_fixedField_of_isOpen : FiniteDimensional K ↥(fixedField U) := by
  rwa [← InfiniteGalois.isOpen_iff_finite, fixingSubgroup_fixedField_of_isOpen U hU]

/-- The Galois correspondence at an open subgroup `U ≤ Gal(Ω/K)`, as a topological group
isomorphism `Gal(Ω/fixedField U) ≃ₜ* U`, whose underlying map is restriction of scalars. -/
def fixedFieldContinuousMulEquiv : Gal(Ω/↥(fixedField U)) ≃ₜ* ↥U :=
  have := finiteDimensional_fixedField_of_isOpen U hU
  let e : Gal(Ω/↥(fixedField U)) ≃* ↥U :=
    (fixingSubgroupEquiv (fixedField U)).symm.trans
      (MulEquiv.subgroupCongr (fixingSubgroup_fixedField_of_isOpen U hU))
  have he : Continuous e :=
    continuous_induced_rng.2 (continuous_restrictScalarsHom (fixedField U))
  { toMulEquiv := e
    continuous_toFun := he
    continuous_invFun :=
      (Continuous.homeoOfEquivCompactToT2 (f := e.toEquiv) he).continuous_invFun }

/-- The identification `Gal(Ω/fixedField U) ≃ₜ* U` changes no value of an automorphism of `Ω`. -/
@[simp]
theorem fixedFieldContinuousMulEquiv_apply_apply (σ : Gal(Ω/↥(fixedField U))) (x : Ω) :
    ((fixedFieldContinuousMulEquiv U hU σ : Gal(Ω/K)) : Ω → Ω) x = σ x := rfl

/-- The underlying map of `fixedFieldContinuousMulEquiv` is restriction of scalars. -/
@[simp]
theorem coe_fixedFieldContinuousMulEquiv (σ : Gal(Ω/↥(fixedField U))) :
    (fixedFieldContinuousMulEquiv U hU σ : Gal(Ω/K)) = AlgEquiv.restrictScalarsHom K σ := rfl

/-- The inverse of `fixedFieldContinuousMulEquiv` also changes no value of an automorphism. -/
@[simp]
theorem fixedFieldContinuousMulEquiv_symm_apply_apply (g : ↥U) (x : Ω) :
    (fixedFieldContinuousMulEquiv U hU).symm g x = (g : Gal(Ω/K)) x := rfl

/-- The image of `Gal(Ω/fixedField U) →* Gal(Ω/K)` is `U` itself, for `U` open. -/
theorem range_restrictScalarsHom_fixedField :
    (AlgEquiv.restrictScalarsHom K (S := ↥(fixedField U)) (A := Ω)).range = U :=
  (range_restrictScalarsHom (fixedField U)).trans (fixingSubgroup_fixedField_of_isOpen U hU)

/-- A function on an open subgroup `U ≤ Gal(Ω/K)` is locally constant if and only if the
corresponding function on `Gal(Ω/fixedField U)` is. -/
theorem isLocallyConstant_comp_fixedFieldContinuousMulEquiv_iff {α : Type*} (f : ↥U → α) :
    IsLocallyConstant f ↔ IsLocallyConstant (f ∘ fixedFieldContinuousMulEquiv U hU) :=
  forall_congr' fun s ↦ by
    rw [Set.preimage_comp]
    exact ((fixedFieldContinuousMulEquiv U hU).toHomeomorph.isOpen_preimage).symm

/-- The two-variable form of `isLocallyConstant_comp_fixedFieldContinuousMulEquiv_iff`, for
`2`-cochains. -/
theorem isLocallyConstant_comp_fixedFieldContinuousMulEquiv_iff' {α : Type*}
    (f : ↥U × ↥U → α) : IsLocallyConstant f ↔
      IsLocallyConstant fun στ : Gal(Ω/↥(fixedField U)) × Gal(Ω/↥(fixedField U)) ↦
        f (fixedFieldContinuousMulEquiv U hU στ.1, fixedFieldContinuousMulEquiv U hU στ.2) :=
  forall_congr' fun s ↦ (((fixedFieldContinuousMulEquiv U hU).toHomeomorph.prodCongr
    (fixedFieldContinuousMulEquiv U hU).toHomeomorph).isOpen_preimage (s := f ⁻¹' s)).symm

end OpenSubgroup

/-- Transitivity of finiteness for a tower of intermediate fields: if `L/K` is finite and `L'` is
a finite extension of `L` inside `Ω`, then `L'`, read as an intermediate field of `Ω/K`, is
finite over `K`. -/
theorem finiteDimensional_tower (L : IntermediateField K Ω) [FiniteDimensional K L]
    (L' : IntermediateField ↥L Ω) [FiniteDimensional ↥L L'] : FiniteDimensional K ↥L' :=
  have : IsScalarTower K ↥L ↥L' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  Module.Finite.trans ↥L ↥L'

/-- The form of `finiteDimensional_tower` that reads `L'` as an intermediate field of `Ω/K`
through `IntermediateField.restrictScalars`. -/
theorem finiteDimensional_restrictScalars (L : IntermediateField K Ω) [FiniteDimensional K L]
    (L' : IntermediateField ↥L Ω) [FiniteDimensional ↥L L'] :
    FiniteDimensional K ↥(L'.restrictScalars K) :=
  finiteDimensional_tower L L'

end Stacks.GaloisCohomology

end
