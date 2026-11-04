module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.Laurent
public import StacksFrontier.AlgebraicGeometry.QcohRestrictEquiv.IsoLocality
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullback

/-!
# A trivializing global section of degree one is a unit of the Laurent sections

Let `L` be an invertible module on a scheme and `u` a global section of `L^{⊗ 1}` such that
multiplication by `u` is bijective on the sections over every open — that is, `u` trivializes
`L`. Then `u`, placed in degree one, is a **unit** of the ring `⨁_{n ∈ ℤ} Γ(⊤, L^{⊗ n})` of global
Laurent sections, with inverse homogeneous of degree `-1`.

## Main definitions

* `mulBy`: multiplication by a global section of `L^{⊗ m}`, as a morphism from `L^{⊗ -m}` to
  the structure sheaf.

## Main results

* `isIso_mulBy`: if multiplication by `x` is an isomorphism, then so is `mulBy m x`.
* `exists_unit_of_isIso_secHom`: a trivializing global section of degree one is a unit of the
  global Laurent sections, with inverse homogeneous of degree `-1`.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry MonoidalCategory
open Stacks.RingedSpace Stacks.PullbackTensorCoherence

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentSections

attribute [local instance] gcommRing

variable {T : Scheme.{u}} {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]

/-- Multiplication by a global section of `L^{⊗ m}`, into degree zero. -/
def mulBy (m : ℤ) (x : ((laurent L).piece m).val.obj (op ⊤)) :
    (laurent L).piece (-m) ⟶ 𝟙_ (SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)) :=
  (λ_ _).inv ≫ (secHom ((laurent L).piece m) x ▷ (laurent L).piece (-m)) ≫
    Stacks.PullbackTensorCoherence.mulHom (laurent L) m (-m) ≫
      eqToHom (congrArg (laurent L).piece (add_neg_cancel m))

/-- On sections over `V`, `mulBy m x` sends `y` to the product of the restriction of `x` to `V`
with `y`, transported to degree zero. -/
theorem mulBy_app (m : ℤ) (x : ((laurent L).piece m).val.obj (op ⊤)) (V : (Opens T.carrier)ᵒᵖ)
    (y : ((laurent L).piece (-m)).val.obj V) :
    (mulBy m x).val.app V y =
      (eqToHom (congrArg (laurent L).piece (add_neg_cancel m))).val.app V
        (((laurent L).mul m (-m)).app V
          (((laurent L).piece m).val.restrictₛₗ (topRes T V) x) y) := by
  have e1 := leftUnitor_inv_app ((laurent L).piece (-m)) V y
  have e2 := whiskerRight_tmul (secHom ((laurent L).piece m) x) V (oneSec T.toRingedSpace V) y
  have e3 : (secHom ((laurent L).piece m) x).val.app V (oneSec T.toRingedSpace V) =
      ((laurent L).piece m).val.restrictₛₗ (topRes T V) x :=
    (secHom_app _ _ V 1).trans (one_smul _ _)
  have e4 :=
    mulHom_tmul (laurent L) m (-m) V (((laurent L).piece m).val.restrictₛₗ (topRes T V) x) y
  show (eqToHom (congrArg (laurent L).piece (add_neg_cancel m))).val.app V
    ((mulHom (laurent L) m (-m)).val.app V
      ((secHom ((laurent L).piece m) x ▷ (laurent L).piece (-m)).val.app V
        ((λ_ ((laurent L).piece (-m))).inv.val.app V y))) = _
  rw [e1, e2, e3, e4]

/-- If multiplication by the global section `x` of `L^{⊗ m}` is an isomorphism, then so is
`mulBy m x`. -/
instance isIso_mulBy (m : ℤ) (x : ((laurent L).piece m).val.obj (op ⊤))
    [IsIso (secHom ((laurent L).piece m) x)] : IsIso (mulBy m x) := by
  have : IsIso (Stacks.PullbackTensorCoherence.mulHom (laurent L) m (-m)) := by
    rw [show Stacks.PullbackTensorCoherence.mulHom (laurent L) m (-m) =
      (LaurentPullback.mulIso L m (-m)).hom from LaurentPullback.mulHom_laurent L m (-m)]
    infer_instance
  have : IsIso (eqToHom (congrArg (laurent L).piece (add_neg_cancel m))) :=
    (eqToIso (congrArg (laurent L).piece (add_neg_cancel m))).isIso_hom
  have h2 : IsIso (secHom ((laurent L).piece m) x ▷ (laurent L).piece (-m)) := inferInstance
  have h1 : IsIso (λ_ ((laurent L).piece (-m))).inv := inferInstance
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1
    (@IsIso.comp_isIso _ _ _ _ _ _ _ h2 (@IsIso.comp_isIso _ _ _ _ _ _ _ ‹_› ‹_›))

/-- **A trivializing global section of degree one is a unit of the Laurent sections**, with
inverse homogeneous of degree `-1`. -/
theorem exists_unit_of_isIso_secHom (x : ((laurent L).piece 1).val.obj (op ⊤))
    [IsIso (secHom ((laurent L).piece 1) x)] :
    ∃ w : (Ring L (op ⊤))ˣ, (w : Ring L (op ⊤)) = DirectSum.of _ 1 x ∧
      ∃ τ, ((w⁻¹ : (Ring L (op ⊤))ˣ) : Ring L (op ⊤)) = DirectSum.of _ (-1) τ := by
  set τ : ((laurent L).piece (-1)).val.obj (op ⊤) :=
    (inv (mulBy 1 x)).val.app (op ⊤) (oneSec T.toRingedSpace (op ⊤)) with hτ
  have hm : (mulBy 1 x).val.app (op ⊤) τ = oneSec T.toRingedSpace (op ⊤) := by
    show ((inv (mulBy 1 x)) ≫ mulBy 1 x).val.app (op ⊤) _ = _
    rw [IsIso.inv_hom_id]
    rfl
  have htop : ((laurent L).piece 1).val.restrictₛₗ (topRes T (op ⊤)) x = x := by
    have h1 : topRes T (op ⊤) = 𝟙 _ := Subsingleton.elim _ _
    show ((laurent L).piece 1).val.map (topRes T (op ⊤)) x = x
    rw [h1, PresheafOfModules.map_id]
    rfl
  rw [mulBy_app, htop] at hm
  have hmul : DirectSum.of ((laurent L).sectionsPiece (op ⊤)) 1 x *
      DirectSum.of _ (-1) τ = 1 := by
    rw [of_mul_of, ← of_eqToHom (add_neg_cancel (1 : ℤ)), hm]
    rfl
  refine ⟨⟨DirectSum.of _ 1 x, DirectSum.of _ (-1) τ, hmul, (mul_comm _ _).trans hmul⟩, rfl,
    τ, rfl⟩

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentSections

end
