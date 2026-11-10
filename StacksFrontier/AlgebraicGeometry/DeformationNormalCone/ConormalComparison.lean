module

public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.ReesPullback
public import StacksFrontier.AlgebraicGeometry.DeformationNormalCone.DeformationSpace
public import StacksFrontier.Topology.Sheaves.Basis.ModuleHomOnBasis

/-!
# The extended Rees algebra maps onto the conormal algebra

Let `g : Z ⟶ X` be a closed immersion with ideal sheaf `ℐ`. The conormal algebra of `g` is the
pullback `g^*(⨁ₙ ℐⁿ)` of the Rees algebra, whose degree-`n` piece is `ℐⁿ/ℐⁿ⁺¹`. This file
proves the vanishing that makes the extended Rees algebra map to it: a local section of `ℐⁿ⁺¹`,
read as a section of `ℐⁿ`, pulls back to zero in `g^*ℐⁿ`.

## Main results

* `Stacks.Deformation.reesPieceLower_comp_unit_eq_zero`: the composite
  `ℐⁿ⁺¹ ⟶ ℐⁿ ⟶ g_* g^* ℐⁿ` is zero.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.Deformation

open Stacks.Blowup

variable {Z X : Scheme.{u}} (g : Z ⟶ X) [IsClosedImmersion g]

/-- Over an affine open `V`, a section of `ℐⁿ` whose image in `Γ(X, V)` lies in `ℐ(V)ⁿ⁺¹` pulls
back to zero in `g^*ℐⁿ`: such a section is a sum of products `a • b` with `a ∈ ℐ(V)`, and
`g` kills `a`. -/
theorem pullbackSection_eq_zero_of_mem (m : ℕ) (V : X.affineOpens)
    (z : (reesPiece g.ker (m : ℤ)).val.obj (op V.1))
    (hz : reesPieceAmbient g.ker (m : ℤ) V.1 z ∈ g.ker.ideal V ^ (m + 1)) :
    Scheme.Modules.pullbackSection g (reesPiece g.ker (m : ℤ)) V.1 (g ⁻¹ᵁ V.1) le_rfl z = 0 := by
  have hinj : Function.Injective (reesPieceAmbient g.ker (m : ℤ) V.1) :=
    reesPieceAmbient_injective g.ker (m : ℤ) (Int.natCast_nonneg m) V.1
  have hmk : ∀ x ∈ g.ker.ideal V ^ m, ∃ w, reesPieceAmbient g.ker (m : ℤ) V.1 w = x := fun x hx =>
    ⟨(reesPieceAffineEquiv g.ker (m : ℤ) (Int.natCast_nonneg m) V).symm ⟨x, by simpa using hx⟩,
      by rw [← reesPieceAffineEquiv_coe g.ker (m : ℤ) (Int.natCast_nonneg m) V,
        AddEquiv.apply_symm_apply]⟩
  rw [pow_succ'] at hz
  refine Submodule.mul_induction_on'
    (C := fun x _ => ∀ w, reesPieceAmbient g.ker (m : ℤ) V.1 w = x →
      Scheme.Modules.pullbackSection g (reesPiece g.ker (m : ℤ)) V.1 (g ⁻¹ᵁ V.1) le_rfl w = 0)
    ?_ ?_ hz z rfl
  · intro a ha b hb w hw
    obtain ⟨b', hb'⟩ := hmk b hb
    have hw' : w = (show X.ringCatSheaf.obj.obj (op V.1) from a) • b' := by
      apply hinj
      rw [hw, reesPieceAmbient_smul g.ker (m : ℤ) V.1, hb']
      rfl
    have ha0 : (g.app V.1).hom a = 0 := by rwa [g.ker_apply V] at ha
    rw [hw', Stacks.Conormal.pullbackSection_smul g (reesPiece g.ker (m : ℤ)) V.1 a b']
    change (show Z.ringCatSheaf.obj.obj (op (g ⁻¹ᵁ V.1)) from (g.app V.1).hom a) • _ = 0
    rw [ha0]
    exact zero_smul _ _
  · intro x hx y hy ihx ihy w hw
    have hle : g.ker.ideal V * g.ker.ideal V ^ m ≤ g.ker.ideal V ^ m := Ideal.mul_le_right
    obtain ⟨wx, hwx⟩ := hmk x (hle hx)
    obtain ⟨wy, hwy⟩ := hmk y (hle hy)
    have hw' : w = wx + wy := by
      apply hinj
      rw [hw, reesPieceAmbient_add, hwx, hwy]
    have hadd : ∀ a b : (reesPiece g.ker (m : ℤ)).val.obj (op V.1),
        Scheme.Modules.pullbackSection g (reesPiece g.ker (m : ℤ)) V.1 (g ⁻¹ᵁ V.1) le_rfl (a + b) =
          Scheme.Modules.pullbackSection g (reesPiece g.ker (m : ℤ)) V.1 (g ⁻¹ᵁ V.1) le_rfl a +
          Scheme.Modules.pullbackSection g (reesPiece g.ker (m : ℤ)) V.1 (g ⁻¹ᵁ V.1) le_rfl b := by
      intro a b
      unfold Scheme.Modules.pullbackSection
      rw [map_add]
      exact map_add _ _ _
    rw [hw', hadd, ihx wx hwx, ihy wy hwy, add_zero]

/-- **The composite `ℐⁿ⁺¹ ⟶ ℐⁿ ⟶ g_* g^* ℐⁿ` is zero.** It is checked on the basis of affine
opens, where it is `Stacks.Deformation.pullbackSection_eq_zero_of_mem`. -/
theorem reesPieceLower_comp_unit_eq_zero (m : ℕ) :
    reesPieceLower g.ker (Nat.le_succ m) ≫
      (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app (reesPiece g.ker (m : ℤ)) = 0 := by
  refine Stacks.BasisRestriction.moduleSheafHom_ext_onBasis _ _ (fun V : X.affineOpens => V.1)
    (by rw [Subtype.range_coe]; exact X.isBasis_affineOpens) _ _ fun V => ?_
  ext y
  change ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
      (reesPiece g.ker (m : ℤ))).val.app (op V.1) ((reesPieceLower g.ker (Nat.le_succ m)).val.app
        (op V.1) y) = 0
  refine (Stacks.Conormal.pullbackSection_self g (reesPiece g.ker (m : ℤ)) V.1 _).symm.trans
    (pullbackSection_eq_zero_of_mem g m V _ ?_)
  change idealPowerKernelAmbient g.ker m V.1 _ ∈ _
  rw [reesPieceAmbient_reesPieceLower g.ker (Nat.le_succ m) V.1 y]
  have h := reesPieceAmbient_mem_affine g.ker ((m + 1 : ℕ) : ℤ) (Int.natCast_nonneg _) V y
  rwa [Int.toNat_natCast] at h

/-- **A local section of `ℐⁿ⁺¹`, read in `ℐⁿ`, pulls back to zero in `g^*ℐⁿ`.** -/
theorem pullbackSection_reesPieceLower_eq_zero (m : ℕ) (W : X.Opens)
    (y : (reesPiece g.ker ((m + 1 : ℕ) : ℤ)).val.obj (op W)) :
    Scheme.Modules.pullbackSection g (reesPiece g.ker (m : ℤ)) W (g ⁻¹ᵁ W) le_rfl
      ((reesPieceLower g.ker (Nat.le_succ m)).val.app (op W) y) = 0 :=
  (Stacks.Conormal.pullbackSection_self g (reesPiece g.ker (m : ℤ)) W _).trans
    (congrArg (fun φ => φ.val.app (op W) y) (reesPieceLower_comp_unit_eq_zero g m))

end Stacks.Deformation

end
