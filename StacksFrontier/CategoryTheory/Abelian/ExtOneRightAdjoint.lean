module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# `Ext¹` from an object killed by a left adjoint into the image of the right adjoint

Let `L ⊣ R` be an adjunction between abelian categories with `L` preserving monomorphisms and
enough injectives in the target of `L`. If `L P = 0`, then `Ext¹(P, R M) = 0` for every `M`: embed
`M ↪ J` with `J` injective, so that `R M ↪ R J ↠ Q` is short exact with `R J` injective, and every
class in `Ext¹(P, R M)` comes from a map `P ⟶ Q`; but `Q` embeds into `R(J/M)` because `R` is left
exact, and `Hom(P, R(J/M)) = Hom(L P, J/M) = 0`.

For the restriction `j⁻¹ ⊣ j_*` to an open subscheme this says: an extension of a sheaf supported
on the complement by a sheaf `F` with `F ≅ j_* j⁻¹ F` splits. This is the vanishing
`Ext¹(punctual, lisse) = 0` on a normal curve used in the proof that the Fourier transform of an
irreducible lisse sheaf is irreducible.

## Main results

* `CategoryTheory.Abelian.Ext.subsingleton_ext_one_rightAdjoint_obj`
* `CategoryTheory.Abelian.Ext.subsingleton_ext_one_of_isIso_unit_app`
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Abelian.Ext

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {D : Type u₂} [Category.{v₂} D] [Abelian D]
  [HasExt.{w} C] [EnoughInjectives D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  [L.PreservesMonomorphisms]

include adj in
/-- **`Ext¹(P, R M) = 0` when `L P = 0`**, for an adjunction `L ⊣ R` of abelian categories with
`L` preserving monomorphisms and enough injectives in the target of `L`. -/
theorem subsingleton_ext_one_rightAdjoint_obj (P : C) (hP : IsZero (L.obj P)) (M : D) :
    Subsingleton (Ext.{w} P (R.obj M) 1) := by
  have := adj.rightAdjoint_preservesLimits.{0, 0}
  have : R.IsRightAdjoint := adj.isRightAdjoint
  refine subsingleton_of_forall_eq 0 fun x => ?_
  let i : M ⟶ Injective.under M := Injective.ι M
  let f : R.obj M ⟶ R.obj (Injective.under M) := R.map i
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (S.exact_of_g_is_cokernel (cokernelIsCokernel f))
      inferInstance inferInstance
  have : Injective (R.obj (Injective.under M)) := Injective.injective_of_adjoint adj _
  have := subsingleton_of_injective.{w} P (R.obj (Injective.under M)) 0
  obtain ⟨x₃, hx₃⟩ := covariant_sequence_exact₁ P hS x (Subsingleton.elim _ _) (zero_add 1)
  obtain ⟨φ, rfl⟩ := (mk₀_bijective (X := P) (Y := S.X₃)).2 x₃
  obtain rfl : φ = 0 := by
    let S₀ := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
    have := ((S₀.map R).exact_of_f_is_kernel
      (isLimitForkMapOfIsLimit' R (cokernel.condition i)
        (Abelian.monoIsKernelOfCokernel (CokernelCofork.ofπ (cokernel.π i) (cokernel.condition i))
          (cokernelIsCokernel i)))).mono_cokernelDesc
    rw [← cancel_mono (cokernel.desc (S₀.map R).f (S₀.map R).g (S₀.map R).zero), Limits.zero_comp]
    exact (adj.homEquiv _ _).symm.injective (hP.eq_of_src _ _)
  rw [← hx₃, mk₀_zero, zero_comp]

include adj in
/-- **`Ext¹(P, F) = 0` when `L P = 0` and the unit is an isomorphism at `F`**, e.g. for a sheaf `F`
with `F ≅ j_* j⁻¹ F` and `P` supported on the complement of the open `j`. -/
theorem subsingleton_ext_one_of_isIso_unit_app (P : C) (hP : IsZero (L.obj P)) (F : C)
    [IsIso (adj.unit.app F)] : Subsingleton (Ext.{w} P F 1) := by
  have := subsingleton_ext_one_rightAdjoint_obj adj P hP (L.obj F)
  refine ⟨fun x y => ?_⟩
  have h : ∀ z : Ext.{w} P F 1, z = (z.comp (mk₀ (adj.unit.app F)) (add_zero 1)).comp
      (mk₀ (inv (adj.unit.app F))) (add_zero 1) := fun z => by
    rw [comp_assoc_of_third_deg_zero, mk₀_comp_mk₀, IsIso.hom_inv_id, comp_mk₀_id]
  rw [h x, h y]
  congr 1
  exact Subsingleton.elim (α := Ext.{w} P (R.obj (L.obj F)) 1) _ _

end CategoryTheory.Abelian.Ext

end
