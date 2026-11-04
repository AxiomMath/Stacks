module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.ResidueField
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The normalization of a scheme in the spectrum of a field is normal

For a quasi-compact quasi-separated morphism `f : Spec L ⟶ X` with `L` a field, the relative
normalization of `X` in `Spec L` is normal. Over an affine open `U` of `X` it is the spectrum of
the integral closure of `Γ(X, U)` in `Γ(Spec L, f⁻¹U)`, a ring whose elements are all zero or
units, and such an integral closure is a normal ring
(`isNormalRing_integralClosure_of_isUnit_or_eq_zero`). This generalizes
`AlgebraicGeometry.isNormal_normalization_fromSpecResidueField` from residue fields to arbitrary
fields.

## Main results

* `AlgebraicGeometry.isNormal_normalization_of_spec_field`.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

private theorem isUnit_or_eq_zero_of_sections_spec_field (L : Type u) [Field L]
    (V : (Spec (.of L)).Opens) (x : Γ(Spec (.of L), V)) : x = 0 ∨ IsUnit x := by
  rcases eq_or_ne V ⊥ with rfl | hV
  · exact Or.inl (Subsingleton.elim _ _)
  · obtain ⟨z, hz⟩ : (V : Set (Spec (.of L))).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr fun h ↦ hV (Opens.coe_eq_empty.mp h)
    have hVtop : V = ⊤ :=
      Opens.ext (Set.eq_univ_of_forall fun y ↦ Subsingleton.elim y z ▸ hz)
    subst hVtop
    let e := (Scheme.ΓSpecIso (.of L)).commRingCatIsoToRingEquiv
    rcases eq_or_ne (e x) 0 with h | h
    · exact Or.inl (e.injective (by rw [h, map_zero]))
    · refine Or.inr ?_
      have hu : IsUnit (e.symm (e x)) := (isUnit_iff_ne_zero.mpr h).map e.symm.toRingHom
      rwa [e.symm_apply_apply] at hu

/-- **The normalization of a scheme in the spectrum of a field is normal.** Over an affine open
`U` of `X` it is the spectrum of the integral closure of `Γ(X, U)` in `Γ(Spec L, π⁻¹U)`, a ring
whose elements are all zero or units, so that integral closure is a normal ring. -/
@[ega "II 6.3.6" "partial"]
theorem isNormal_normalization_of_spec_field {X : Scheme.{u}} (L : Type u) [Field L]
    (f : Spec (.of L) ⟶ X) [QuasiCompact f] [QuasiSeparated f] :
    IsNormal f.normalization := by
  have h : IsNormal f.normalization ↔
      ∃ (I : Type u) (U : I → f.normalization.Opens),
        IsOpenCover U ∧ ∀ i, IsNormal (U i).toScheme :=
    (isNormal_tfae _).out 1 4
  refine h.mpr ⟨X.affineOpens, fun U ↦ f.fromNormalization ⁻¹ᵁ U.1, IsOpenCover.mk ?_, fun U ↦ ?_⟩
  · refine top_unique fun z _ ↦ ?_
    obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (f.fromNormalization z)) isOpen_univ
    exact Opens.mem_iSup.2 ⟨⟨U, hU⟩, hzU⟩
  · let : Algebra Γ(X, U.1) Γ(Spec (.of L), f ⁻¹ᵁ U.1) := (f.app U.1).hom.toAlgebra
    let := isNormal_spec_of_isNormalRing
      (isNormalRing_integralClosure_of_isUnit_or_eq_zero Γ(X, U.1)
        Γ(Spec (.of L), f ⁻¹ᵁ U.1)
        (isUnit_or_eq_zero_of_sections_spec_field L _))
    exact isNormal_of_iso (relativeNormalizationPreimageIso f U.1 U.2)

end AlgebraicGeometry

end
