module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# The homology of the mapping cone of a map out of a single complex

Let `φ : L ⟶ K` be a morphism of cochain complexes in an abelian category, where `L` has homology
only in degree `0` (for instance an object placed in degree `0`). The long exact homology sequence
of the mapping cone triangle `L ⟶ K ⟶ cone(φ) ⟶ L[1]` shows that the mapping cone has the
homology of `K` outside the degrees `-1` and `0`, and that it has no homology in degrees `-1` and
`0` exactly when `K` has none in degree `-1` and `φ` induces an isomorphism `H⁰(L) ≅ H⁰(K)`.

## Main results

* `Stacks.MappingConeSingle.isIso_homologyMap_inr`: `Hⁿ(K) ≅ Hⁿ(cone(φ))` for `n ≠ -1, 0`.
* `Stacks.MappingConeSingle.isZero_homology_of_isIso`: the cone has no homology in degrees
  `-1` and `0` when `H⁰(φ)` is an isomorphism and `H⁻¹(K) = 0`.
* `Stacks.MappingConeSingle.isIso_homologyMap_of_isZero`: conversely `H⁰(φ)` is an isomorphism
  when the cone has no homology in degrees `-1` and `0`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Stacks.MappingConeSingle

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

variable {L K : CochainComplex C ℤ} (φ : L ⟶ K) (hL : ∀ n : ℤ, n ≠ 0 → IsZero (L.homology n))
include hL

/-- The map `Hⁿ(K) ⟶ Hⁿ(cone(φ))` is epi when `Hⁿ⁺¹(L) = 0`. -/
private theorem epi_homologyMap_inr (n : ℤ) (h : n + 1 ≠ 0) :
    Epi (homologyMap (CochainComplex.mappingCone.triangle φ).mor₂ n) :=
  (CochainComplex.homologyMap_exact₃_of_distTriang _
    (DerivedCategory.mappingCone_triangle_distinguished φ) n (n + 1) rfl).epi_f
    ((hL (n + 1) h).eq_of_tgt _ _)

/-- **Outside the degrees `-1` and `0` the mapping cone of `φ` has the homology of
`K`**, through the inclusion `K ⟶ cone(φ)`. -/
theorem isIso_homologyMap_inr (n : ℤ) (h₀ : n ≠ 0) (h₁ : n ≠ -1) :
    IsIso (homologyMap (CochainComplex.mappingCone.inr φ) n) := by
  let T := CochainComplex.mappingCone.triangle φ
  have hT := DerivedCategory.mappingCone_triangle_distinguished φ
  have hmono : Mono (homologyMap T.mor₂ n) :=
    (CochainComplex.homologyMap_exact₂_of_distTriang T hT n).mono_g
      ((hL n h₀).eq_of_src _ _)
  have hepi := epi_homologyMap_inr φ hL n (by omega)
  exact isIso_of_mono_of_epi (homologyMap T.mor₂ n)

/-- **The mapping cone of `φ` has no homology in degrees `-1` and `0`** when
`H⁻¹(K) = 0` and `H⁰(φ)` is an isomorphism. -/
theorem isZero_homology_of_isIso (hK : IsZero (K.homology (-1)))
    (hφ : IsIso (homologyMap φ 0)) :
    IsZero ((CochainComplex.mappingCone φ).homology (-1)) ∧
      IsZero ((CochainComplex.mappingCone φ).homology 0) := by
  let T := CochainComplex.mappingCone.triangle φ
  have hT := DerivedCategory.mappingCone_triangle_distinguished φ
  constructor
  · have hmono : Mono (CochainComplex.homologyδOfTriangle T (-1) 0) :=
      (CochainComplex.homologyMap_exact₃_of_distTriang T hT (-1) 0).mono_g
        (hK.eq_of_src _ _)
    have hzero : CochainComplex.homologyδOfTriangle T (-1) 0 = 0 := by
      have hm : Mono (homologyMap T.mor₁ 0) := by
        change Mono (homologyMap φ 0)
        infer_instance
      exact (CochainComplex.homologyMap_exact₁_of_distTriang T hT (-1) 0).mono_g_iff.1 hm
    exact @IsZero.of_mono_eq_zero _ _ _ _ _ _ hmono hzero
  · have hepi := epi_homologyMap_inr φ hL 0 (by omega)
    have hzero : homologyMap T.mor₂ 0 = 0 := by
      have he : Epi (homologyMap T.mor₁ 0) := by
        change Epi (homologyMap φ 0)
        infer_instance
      exact (CochainComplex.homologyMap_exact₂_of_distTriang T hT 0).epi_f_iff.1 he
    exact @IsZero.of_epi_eq_zero _ _ _ _ _ _ hepi hzero

omit hL in
/-- **`H⁰(φ)` is an isomorphism** when the mapping cone of `φ` has no
homology in degrees `-1` and `0`. -/
theorem isIso_homologyMap_of_isZero (h₁ : IsZero ((CochainComplex.mappingCone φ).homology (-1)))
    (h₀ : IsZero ((CochainComplex.mappingCone φ).homology 0)) :
    IsIso (homologyMap φ 0) := by
  let T := CochainComplex.mappingCone.triangle φ
  have hT := DerivedCategory.mappingCone_triangle_distinguished φ
  have hmono : Mono (homologyMap T.mor₁ 0) :=
    (CochainComplex.homologyMap_exact₁_of_distTriang T hT (-1) 0).mono_g (h₁.eq_of_src _ _)
  have hepi : Epi (homologyMap T.mor₁ 0) :=
    (CochainComplex.homologyMap_exact₂_of_distTriang T hT 0).epi_f (h₀.eq_of_tgt _ _)
  exact @isIso_of_mono_of_epi _ _ _ _ _ (homologyMap T.mor₁ 0) hmono hepi

end Stacks.MappingConeSingle

end
