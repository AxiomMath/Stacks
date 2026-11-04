module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LevelDevissage

/-!
# The `p`-torsion of the constant sheaf `ℤ/pᵐ` is the constant sheaf `ℤ/p`

For `N = d e`, the inclusion `ℤ/e_X ↪ ℤ/N_X`, `x ↦ d x`
(`Stacks.EtaleCohomology.LevelChange.inclusion`) is the `e`-torsion of `ℤ/N_X`: it is the kernel
of the reduction to `ℤ/d`, and multiplication by `e` is that reduction followed by the
monomorphism `ℤ/d_X ↪ ℤ/N_X`, `y ↦ e y`
(`Stacks.EtaleCohomology.LevelChange.isTorsionKernel_inclusion`). For `N = pᵐ` and `e = p`, the
`p`-torsion `ℤ/pᵐ_X[p]` is therefore the constant sheaf `ℤ/p_X`, restriction of scalars being
fully faithful (`Stacks.EtaleCohomology.LevelChange.unitSheafCoextendIso`).

## Main results

* `Stacks.EtaleCohomology.LevelChange.isTorsionKernel_inclusion`.
* `Stacks.EtaleCohomology.LevelChange.unitSheafCoextendIso`.
* `Stacks.EtaleCohomology.LevelChange.map_unitSheafCoextendIso_comp_torsionCounit`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology.LevelChange

open ExtensionTorsor

section Torsion

variable (X : Scheme.{u}) {N d e : ℕ} (hde : d * e = N)

/-- **`ℤ/e_X ↪ ℤ/N_X`, `x ↦ d x`, is the `e`-torsion of `ℤ/N_X`**, for `N = d e`. -/
theorem isTorsionKernel_inclusion [NeZero N] : IsTorsionKernel e (inclusion X hde) := by
  have hed : e * d = N := (mul_comm e d).trans hde
  have hS := inclusionShortComplex_shortExact X hde
  have hS' := inclusionShortComplex_shortExact X hed
  have := hS.mono_f
  have := hS'.mono_f
  refine ⟨hS.mono_f, ?_, fun T t ht => ?_⟩
  · rw [Preadditive.comp_nsmul, Category.comp_id, ← Category.id_comp (inclusion X hde),
      ← Preadditive.nsmul_comp, nsmul_id_restrict, zero_comp]
  · have h1 : e • 𝟙 (unitSheaf (X := X) N) =
        reduction X (dvd_of_mul_eq_left hed) ≫ inclusion X hed :=
      (reduction_comp_inclusion X hed).symm
    have h2 : t ≫ reduction X (Dvd.intro e hde) = 0 := by
      rw [← cancel_mono (inclusion X hed), zero_comp, Category.assoc]
      exact (congrArg (t ≫ ·) h1).symm.trans ht
    exact ⟨hS.exact.lift t h2, hS.exact.lift_f t h2⟩

end Torsion

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (m : ℕ) [NeZero m]

omit [Fact p.Prime] in
/-- For `m ≠ 0`, `p ^ (m - 1) * p = p ^ m`. -/
theorem pow_pred_mul_self : p ^ (m - 1) * p = p ^ m := by
  rw [← pow_succ, Nat.sub_add_cancel (NeZero.one_le)]

/-- For a prime `p`, the power `p ^ m` is nonzero. -/
instance neZero_pow_prime : NeZero (p ^ m) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩

/-- A morphism `R(ℤ/p_X) ⟶ R(ℤ/pᵐ_X[p])` over `ℤ/pᵐ_X`: both are the `p`-torsion of `ℤ/pᵐ_X`. -/
def unitSheafTorsionLift :
    (restrict X (dvd_pow_self_of_neZero (p := p) (m := m))).obj (unitSheaf p) ⟶
      (restrict X (dvd_pow_self_of_neZero (p := p) (m := m))).obj
        ((coextend X (dvd_pow_self_of_neZero (p := p) (m := m))).obj (unitSheaf (p ^ m))) :=
  ((isTorsionKernel_torsionCounit X (unitSheaf (p ^ m))).exists_lift
    (inclusion X (pow_pred_mul_self p m))
    (isTorsionKernel_inclusion X (pow_pred_mul_self p m)).comp_eq_zero).choose

/-- The composite of `unitSheafTorsionLift` with the torsion counit of `ℤ/pᵐ_X` is the inclusion
`ℤ/p_X ↪ ℤ/pᵐ_X`, `x ↦ p^{m-1} x`. -/
theorem unitSheafTorsionLift_comp :
    unitSheafTorsionLift X p m ≫ torsionCounit X (unitSheaf (p ^ m)) =
      inclusion X (pow_pred_mul_self p m) :=
  ((isTorsionKernel_torsionCounit X (unitSheaf (p ^ m))).exists_lift
    (inclusion X (pow_pred_mul_self p m))
    (isTorsionKernel_inclusion X (pow_pred_mul_self p m)).comp_eq_zero).choose_spec

/-- The morphism `unitSheafTorsionLift` is an isomorphism. -/
instance : IsIso (unitSheafTorsionLift X p m) :=
  (isTorsionKernel_inclusion X (pow_pred_mul_self p m)).isIso_of_comp
    (isTorsionKernel_torsionCounit X (unitSheaf (p ^ m))) _ (unitSheafTorsionLift_comp X p m)

/-- **`ℤ/p_X ≅ ℤ/pᵐ_X[p]`**: the `p`-torsion of the constant sheaf `ℤ/pᵐ` is the constant sheaf
`ℤ/p`, restriction of scalars being fully faithful. -/
def unitSheafCoextendIso :
    unitSheaf (X := X) p ≅
      (coextend X (dvd_pow_self_of_neZero (p := p) (m := m))).obj (unitSheaf (p ^ m)) :=
  (Functor.FullyFaithful.ofFullyFaithful
    (restrict X (dvd_pow_self_of_neZero (p := p) (m := m)))).preimageIso
      (asIso (unitSheafTorsionLift X p m))

/-- Under `ℤ/p_X ≅ ℤ/pᵐ_X[p]`, the inclusion of the `p`-torsion is `x ↦ p^{m-1} x`. -/
theorem map_unitSheafCoextendIso_comp_torsionCounit :
    (restrict X (dvd_pow_self_of_neZero (p := p) (m := m))).map
        (unitSheafCoextendIso X p m).hom ≫ torsionCounit X (unitSheaf (p ^ m)) =
      inclusion X (pow_pred_mul_self p m) := by
  rw [unitSheafCoextendIso, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage]
  exact unitSheafTorsionLift_comp X p m

end Stacks.EtaleCohomology.LevelChange

end
