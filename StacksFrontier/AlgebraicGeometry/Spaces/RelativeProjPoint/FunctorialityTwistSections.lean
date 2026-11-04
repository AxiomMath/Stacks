module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.FunctorialityTwistLegs
public import StacksFrontier.AlgebraicGeometry.Morphism.TwistTransportBaseChange

/-!
# The comparisons of twists of Situation 0849 on homogeneous sections

The comparison `congrBaseChangeTwistIso` of the twists of Tag 01NR along a restriction
`Proj(A₁) ≅ Proj(hs^*A)` followed by the base change `Proj(hs^*A) ⟶ Proj(A)` carries the inverse
image of `ψ_A(a)` to `ψ_{A₁}` of the section of `A₁` corresponding to `hs^*a`.

## Main results

* `RelativeProjQcohSheaf.congrTwistIsoApp_pullbackSection_psiU`: the restriction factor, on
  pulled-back sections.
* `RelativeProjBaseChangeTwist.congrBaseChangeTwistIso_hom_app_pullbackSection_psiU`: the whole
  comparison, on pulled-back sections.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj (relativeProj)
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap (psiU)
open Stacks.AlgebraicGeometry.Tag07ZGTwist (relativeTwist)

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {Y : Scheme.{u}} {A₁ A₂ : SheafGradedAlgebra Y}
  (Φ : SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra A₁) (situationAlgebra A₂))
  (hΦ : ∀ n : ℤ, IsIso (Φ.app n))

/-- The degree-`n` component of `congrTwistIso`, typed as a map of modules of the scheme. -/
def congrTwistIsoApp (n : ℤ) :
    (Scheme.Modules.pullback (relativeProjCongr Φ hΦ).hom).obj (relativeTwist A₂ n) ⟶
      (Tag07ZGTwist.twistAlgebra A₁).piece n :=
  (congrTwistIso Φ hΦ).hom.app n

/-- **`congrTwistIso` on a pulled-back homogeneous section**: it carries the inverse image along
`relativeProjCongr Φ` of `ψ_{A₂}(Φ(a))` to `ψ_{A₁}(a)`. -/
theorem congrTwistIsoApp_pullbackSection_psiU (n : ℕ) (V : Y.Opens)
    (a : Γ(A₁.piece (n : ℤ), V)) (b : Γ(A₂.piece (n : ℤ), V))
    (hb : ((congrHom Φ).app (n : ℤ)).val.app (op V) a = b)
    (hW : (relativeProj A₁).toBase ⁻¹ᵁ V ≤
      (relativeProjCongr Φ hΦ).hom ⁻¹ᵁ ((relativeProj A₂).toBase ⁻¹ᵁ V)) :
    (congrTwistIsoApp Φ hΦ n).val.app (op ((relativeProj A₁).toBase ⁻¹ᵁ V))
        (Scheme.Modules.pullbackSection (relativeProjCongr Φ hΦ).hom (relativeTwist A₂ n) _ _ hW
          (psiU A₂ n V b)) = psiU A₁ n V a := by
  subst hb
  refine Eq.trans ?_ (congrTwistIso_app_congrPsi_app Φ hΦ n V a)
  rw [congrPsi_app Φ hΦ n V a hW]
  rfl

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

namespace Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {Y Y' : Scheme.{u}} (A : SheafGradedAlgebra Y) (hs : Y' ⟶ Y) {A₁ : SheafGradedAlgebra Y'}
  (Φ : SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra A₁)
    (situationAlgebra (A.pullback hs)))
  (hΦ : ∀ n : ℤ, IsIso (Φ.app n))
  (pc : (relativeProj A₁).scheme ⟶ (relativeProj A).scheme)
  (hpc : pc = (relativeProjCongr Φ hΦ).hom ≫ baseChangeHom A hs)

/-- The value of `κ⁻¹ ≫ e^*P ≫ C` on a section pulled back along `e ≫ b`, from the values of `P`
and `C` on pulled-back sections. -/
private theorem comp_val_app_pullbackSection {X Y Z : Scheme.{u}} (e : X ⟶ Y) (b : Y ⟶ Z)
    (M : Z.Modules) {M₂ : Y.Modules} {M₁ : X.Modules} (P : (Scheme.Modules.pullback b).obj M ⟶ M₂)
    (C : (Scheme.Modules.pullback e).obj M₂ ⟶ M₁) (U : Z.Opens) (W : Y.Opens) (V' : X.Opens)
    (hg : W ≤ b ⁻¹ᵁ U) (hf : V' ≤ e ⁻¹ᵁ W) (h : V' ≤ (e ≫ b) ⁻¹ᵁ U) (m : M.val.obj (op U))
    (t : M₂.val.obj (op W)) (c : M₁.val.obj (op V'))
    (hP : P.val.app (op W) (Scheme.Modules.pullbackSection b M U W hg m) = t)
    (hC : C.val.app (op V') (Scheme.Modules.pullbackSection e M₂ W V' hf t) = c) :
    ((Scheme.Modules.pullbackComp e b).inv.app M ≫ (Scheme.Modules.pullback e).map P ≫ C).val.app
        (op V') (Scheme.Modules.pullbackSection (e ≫ b) M U V' h m) = c := by
  rw [Tag07ZGTwist.val_app_comp_apply, Tag07ZGTwist.val_app_comp_apply,
    Tag07ZGTwist.pullbackComp_inv_pullbackSection e b M U W V' hg hf h m,
    Scheme.Modules.pullbackSection_naturality, hP, hC]

/-- The degree-`d` component of `congrBaseChangeTwistIso` at `pc = e ≫ bc`, written out in modules
of the scheme. -/
theorem congrBaseChangeTwistIso_hom_app_eq (d : ℤ) :
    (congrBaseChangeTwistIso A hs Φ hΦ ((relativeProjCongr Φ hΦ).hom ≫
      baseChangeHom A hs) rfl).hom.app d =
      ((Scheme.Modules.pullbackComp (relativeProjCongr Φ hΦ).hom (baseChangeHom A hs)).inv.app
          (relativeTwist A d) ≫
        (Scheme.Modules.pullback (relativeProjCongr Φ hΦ).hom).map
          ((pulledTwistIso A hs).hom.app d) ≫ congrTwistIsoApp Φ hΦ d :
        (Scheme.Modules.pullback ((relativeProjCongr Φ hΦ).hom ≫ baseChangeHom A hs)).obj
          (relativeTwist A d) ⟶ (Tag07ZGTwist.twistAlgebra A₁).piece d) := by
  simp only [congrBaseChangeTwistIso]
  exact Category.id_comp _

/-- The composite of `congrBaseChangeTwistIso_hom_app_eq` on the homogeneous sections. -/
private theorem congrBaseChangeTwistIso_comp_pullbackSection_psiU
    (εA : ∀ d : ℕ, (Scheme.Modules.pullback hs).obj (A.piece (d : ℤ)) ≅ A₁.piece (d : ℤ))
    (hε : ∀ d : ℕ, (εA d).inv = (congrHom Φ).app (d : ℤ)) (d : ℕ) (V : Y.Opens)
    (a : Γ(A.piece (d : ℤ), V))
    (hV : (relativeProj A₁).toBase ⁻¹ᵁ (hs ⁻¹ᵁ V) ≤
      ((relativeProjCongr Φ hΦ).hom ≫ baseChangeHom A hs) ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V)) :
    ((Scheme.Modules.pullbackComp (relativeProjCongr Φ hΦ).hom (baseChangeHom A hs)).inv.app
          (relativeTwist A d) ≫
        (Scheme.Modules.pullback (relativeProjCongr Φ hΦ).hom).map
          ((pulledTwistIso A hs).hom.app d) ≫ congrTwistIsoApp Φ hΦ d :
        (Scheme.Modules.pullback ((relativeProjCongr Φ hΦ).hom ≫ baseChangeHom A hs)).obj
          (relativeTwist A d) ⟶ (Tag07ZGTwist.twistAlgebra A₁).piece d).val.app
        (op ((relativeProj A₁).toBase ⁻¹ᵁ (hs ⁻¹ᵁ V)))
        (Scheme.Modules.pullbackSection _ (relativeTwist A d) _ _ hV (psiU A d V a)) =
      psiU A₁ d (hs ⁻¹ᵁ V) ((εA d).hom.val.app (op (hs ⁻¹ᵁ V))
        (Scheme.Modules.pullbackSection hs (A.piece (d : ℤ)) V _ le_rfl a)) := by
  have hg : (relativeProj (A.pullback hs)).toBase ⁻¹ᵁ (hs ⁻¹ᵁ V) ≤
      baseChangeHom A hs ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V) :=
    (baseChangeHom_preimage_toBase A hs V).ge
  have hf : (relativeProj A₁).toBase ⁻¹ᵁ (hs ⁻¹ᵁ V) ≤ (relativeProjCongr Φ hΦ).hom ⁻¹ᵁ
      ((relativeProj (A.pullback hs)).toBase ⁻¹ᵁ (hs ⁻¹ᵁ V)) := by
    rw [← Scheme.Hom.comp_preimage (relativeProjCongr Φ hΦ).hom, relativeProjCongr_hom_comp_toBase]
  have hεy : ((congrHom Φ).app (d : ℤ)).val.app (op (hs ⁻¹ᵁ V)) ((εA d).hom.val.app
      (op (hs ⁻¹ᵁ V)) (Scheme.Modules.pullbackSection hs (A.piece (d : ℤ)) V _ le_rfl a)) =
        Scheme.Modules.pullbackSection hs (A.piece (d : ℤ)) V _ le_rfl a := by
    rw [← hε d]
    exact congrArg (fun φ => SheafOfModules.Hom.val φ |>.app (op (hs ⁻¹ᵁ V))
      (Scheme.Modules.pullbackSection hs (A.piece (d : ℤ)) V _ le_rfl a)) (εA d).hom_inv_id
  refine comp_val_app_pullbackSection _ _ _ _ _ _ _ _ hg hf hV _
    (psiU (A.pullback hs) d (hs ⁻¹ᵁ V)
      (Scheme.Modules.pullbackSection hs (A.piece (d : ℤ)) V _ le_rfl a)) _ ?_ ?_
  · exact (Tag07ZGTwist.chi_psiU_of_unitApp _ _ _ _ (pulledTwistIso_hom_unitApp_psiU A hs d V a)
      hg).trans (congrArg (psiU (A.pullback hs) d (hs ⁻¹ᵁ V))
        (PresheafOfModules.map_id_apply ((Scheme.Modules.pullback hs).obj (A.piece (d : ℤ))).val
          (op (hs ⁻¹ᵁ V)) _).symm)
  · convert congrTwistIsoApp_pullbackSection_psiU Φ hΦ d (hs ⁻¹ᵁ V) _ _ hεy hf using 2

/-- **`congrBaseChangeTwistIso` on the homogeneous sections**: it carries the inverse image along
`pc` of `ψ_A(a)` to `ψ_{A₁}` of the section `Φ⁻¹(hs^*a)`, for any identification `ε` of
`hs^*A_d` with `A₁_d` inverse to `Φ`. -/
theorem congrBaseChangeTwistIso_hom_app_pullbackSection_psiU
    (εA : ∀ d : ℕ, (Scheme.Modules.pullback hs).obj (A.piece (d : ℤ)) ≅ A₁.piece (d : ℤ))
    (hε : ∀ d : ℕ, (εA d).inv = (congrHom Φ).app (d : ℤ)) (d : ℕ) (V : Y.Opens)
    (a : Γ(A.piece (d : ℤ), V))
    (hV : (relativeProj A₁).toBase ⁻¹ᵁ (hs ⁻¹ᵁ V) ≤ pc ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V)) :
    ((congrBaseChangeTwistIso A hs Φ hΦ pc hpc).hom.app (d : ℤ)).val.app
        (op ((relativeProj A₁).toBase ⁻¹ᵁ (hs ⁻¹ᵁ V)))
        (Scheme.Modules.pullbackSection pc (relativeTwist A d) _ _ hV (psiU A d V a)) =
      psiU A₁ d (hs ⁻¹ᵁ V) ((εA d).hom.val.app (op (hs ⁻¹ᵁ V))
        (Scheme.Modules.pullbackSection hs (A.piece (d : ℤ)) V _ le_rfl a)) := by
  subst hpc
  rw [congrBaseChangeTwistIso_hom_app_eq A hs Φ hΦ d]
  exact congrBaseChangeTwistIso_comp_pullbackSection_psiU A hs Φ hΦ εA hε d V a hV

/-- **A comparison of twists with the components of `congrBaseChangeTwistIso`, on the homogeneous
sections**: `congrBaseChangeTwistIso`, as an isomorphism of sheaves of graded algebras on the
structure sheaf, carries the inverse image of `ψ_A(a)` to `ψ_{A₁}` of `ε(hs^*a)`. -/
theorem hom_app_pullbackSection_psiU_of_app_eq
    {χ : Stacks.RingedSpace.pullbackGradedAlgebra pc.toLRSHom.toShHom
        (Tag07ZGTwist.twistAlgebra A) ≅ Tag07ZGTwist.twistAlgebra A₁}
    (hχ : χ = congrBaseChangeTwistIso A hs Φ hΦ pc hpc)
    {εA : ∀ d : ℕ, (Scheme.Modules.pullback hs).obj (A.piece (d : ℤ)) ≅ A₁.piece (d : ℤ)}
    (hε : ∀ d : ℕ, (εA d).inv = (congrHom Φ).app (d : ℤ)) (d : ℕ) (V : Y.Opens)
    (a : Γ(A.piece (d : ℤ), V))
    (hV : (relativeProj A₁).toBase ⁻¹ᵁ (hs ⁻¹ᵁ V) ≤ pc ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V)) :
    (χ.hom.app (d : ℤ)).val.app (op ((relativeProj A₁).toBase ⁻¹ᵁ (hs ⁻¹ᵁ V)))
        (Scheme.Modules.pullbackSection pc (relativeTwist A d) _ _ hV (psiU A d V a)) =
      psiU A₁ d (hs ⁻¹ᵁ V) ((εA d).hom.val.app (op (hs ⁻¹ᵁ V))
        (Scheme.Modules.pullbackSection hs (A.piece (d : ℤ)) V _ le_rfl a)) := by
  subst hχ hpc
  exact congrBaseChangeTwistIso_hom_app_pullbackSection_psiU A hs Φ hΦ _ rfl εA hε d V a hV

end Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist

end
