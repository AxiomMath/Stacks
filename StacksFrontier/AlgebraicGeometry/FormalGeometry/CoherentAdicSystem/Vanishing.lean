module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Transition
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.AffineSections
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.TrivialDividedPowers
public import StacksFrontier.AlgebraicGeometry.GenericPointCoproduct.Basic

/-!
# Vanishing of a coherent adic system

Let `X` be a scheme, `ℐ ⊆ 𝒪_X` a quasi-coherent sheaf of ideals and `(F_n)` a coherent adic
system along `ℐ`. If `F_0 = 0` then `F_n = 0` for every `n`.

## Main results

* `Stacks.Coherent.isZero_of_affine_sections` — a sheaf of modules on a scheme whose module of
  sections over every affine open is a zero object is itself a zero object.
* `Stacks.Coherent.isZero_of_isZero_obj_zero` — every term of a coherent adic system whose
  zeroth term vanishes is a zero object.
* `Stacks.Coherent.isZero_functor_of_isZero_obj_zero` — the same statement packaged as the
  vanishing of the inverse system itself.

## References

* [Stacks Project, Tag 087Y](https://stacks.math.columbia.edu/tag/087Y)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Algebraization
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

variable {X : Scheme.{u}} {I : X.IdealSheafData} {F : ℕᵒᵖ ⥤ X.Modules}

/-- **Vanishing of a sheaf of modules is an affine-local condition.** An `𝒪_X`-module whose
module of sections over every affine open is a zero object is a zero object. -/
public theorem isZero_of_affine_sections (M : X.Modules)
    (hM : ∀ U : X.affineOpens, IsZero (ModuleCat.of Γ(X, U) Γ(M, U))) : IsZero M := by
  have haff : ∀ (U : X.affineOpens) (s : Γ(M, U)), s = 0 := fun U s =>
    (ModuleCat.isZero_iff_subsingleton.mp (hM U)).elim s 0
  have hsec : ∀ (U : X.Opens) (s : Γ(M, U)), s = 0 := by
    intro U s
    refine TopCat.Presheaf.section_ext ⟨M.presheaf, M.isSheaf⟩ U s 0 fun x hx => ?_
    obtain ⟨-, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
    have hgerm : M.presheaf.germ U x hx s =
        M.presheaf.germ V x hxV (M.presheaf.map (homOfLE hVU).op s) :=
      (M.presheaf.germ_res_apply (homOfLE hVU) x hxV s).symm
    change M.presheaf.germ U x hx s = M.presheaf.germ U x hx 0
    rw [hgerm, haff ⟨V, hV⟩ (M.presheaf.map (homOfLE hVU).op s)]
    simp
  exact Stacks.AlgebraicGeometry.GenericPointCoproduct.isZero_of_subsingleton_sections M
    fun U => subsingleton_of_forall_eq 0 (hsec U)

/-- **A coherent adic system with vanishing zeroth term vanishes.** If `F_0 = 0` then every term
`F_n` of the coherent adic system is a zero object. -/
public theorem isZero_of_isZero_obj_zero (hF : IsCoherentAdicSystem I F)
    (h0 : IsZero (F.obj (op 0))) (n : ℕ) : IsZero (F.obj (op n)) := by
  induction n with
  | zero => exact h0
  | succ n ih =>
      have hqc : (F.obj (op (n + 1))).IsQuasicoherent := hF.isQuasicoherent (n + 1)
      have hQ : IsZero (idealPowerQuotient I (n + 1) (F.obj (op (n + 1)))) :=
        (hF.quotientIso n).isZero_iff.mpr ih
      have hπ : cokernel.π (C := X.Modules)
          (idealPowerMultiple I (n + 1) (F.obj (op (n + 1)))).ι = 0 := hQ.eq_of_tgt _ _
      have hsections : ∀ (U : X.affineOpens) (s : Γ(F.obj (op (n + 1)), U)), s = 0 := by
        intro U s
        have htop : I.ideal U ^ (n + 1) •
            (⊤ : Submodule Γ(X, U) Γ(F.obj (op (n + 1)), U)) = ⊤ := by
          refine le_antisymm le_top fun y _ => ?_
          rw [← idealPowerMultiple_toSubmodule_obj_affine I (n + 1) (F.obj (op (n + 1))) U]
          refine (cokernel_π_app_eq_zero_iff (F.obj (op (n + 1)))
            (idealPowerMultiple I (n + 1) (F.obj (op (n + 1)))) U.1 y).mp ?_
          rw [hπ]
          rfl
        have hlarge : s ∈ I.ideal U ^ (2 * (n + 1)) •
            (⊤ : Submodule Γ(X, U) Γ(F.obj (op (n + 1)), U)) := by
          have hs : s ∈ I.ideal U ^ (n + 1) • (I.ideal U ^ (n + 1) •
              (⊤ : Submodule Γ(X, U) Γ(F.obj (op (n + 1)), U))) := by
            rw [htop, htop]; exact Submodule.mem_top
          simpa [← Submodule.mul_smul, ← pow_add, two_mul] using hs
        have hle : I.ideal U ^ (2 * (n + 1)) ≤ I.ideal U ^ (n + 1 + 1) :=
          Ideal.pow_le_pow_right (by omega)
        have hmem : s ∈ (⊥ : (F.obj (op (n + 1))).Submodule).toSubmodule.obj (op U.1) :=
          (idealPowerMultiple_le_iff I (n + 1 + 1) (F.obj (op (n + 1))) ⊥).mp
            (le_of_eq (hF.idealPowerMultiple_eq_bot (n + 1))) U
            (Submodule.smul_mono_left hle hlarge)
        have hbot : (⊥ : (F.obj (op (n + 1))).Submodule).toSubmodule.obj (op U.1) =
            (⊥ : Submodule Γ(X, U) Γ(F.obj (op (n + 1)), U)) :=
          SheafOfModules.Submodule.bot_obj (F.obj (op (n + 1))) (op U.1)
        have hs0 : s ∈ (⊥ : Submodule Γ(X, U) Γ(F.obj (op (n + 1)), U)) := hbot ▸ hmem
        simpa using hs0
      exact isZero_of_affine_sections (F.obj (op (n + 1))) fun U =>
        ModuleCat.isZero_iff_subsingleton.mpr (subsingleton_of_forall_eq 0 (hsections U))

/-- A coherent adic system whose zeroth term vanishes is a zero object of `ℕᵒᵖ ⥤ X.Modules`. -/
public theorem isZero_functor_of_isZero_obj_zero (hF : IsCoherentAdicSystem I F)
    (h0 : IsZero (F.obj (op 0))) : IsZero F :=
  F.isZero_iff.mpr fun ⟨n⟩ => isZero_of_isZero_obj_zero hF h0 n

end Stacks.Coherent

end
