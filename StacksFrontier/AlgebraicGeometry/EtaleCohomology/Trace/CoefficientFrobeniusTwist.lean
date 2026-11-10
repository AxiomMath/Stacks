module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalCompactSupportFrobenius
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoefficientMateLimit

/-!
# The Frobenius base change twist and a change of coefficients

Let `Γ : Mod(R) ⥤ Mod(S)` be any functor of module categories which preserves the sheaf
condition (for instance a right adjoint), applied sectionwise to sheaves on small étale sites.
The base change twist `g^{-1} ⟶ a_* ∘ g^{-1}` of
`Stacks.EtaleCohomology.etaleModuleBaseChangeTwist` commutes with `Γ`, through the comparison
`g^{-1}(Γ L) ⟶ Γ(g^{-1} L)` of `Stacks.EtaleCohomology.sheafComposeCoefficientMate`. Nothing is
asked of `Γ` beyond preserving sheaves: the comparison need not be invertible.

This generalizes `Stacks.EtaleCohomology.etaleModuleBaseChangeTwist_restrictScalars` from
restriction of scalars to an arbitrary change of coefficients.

## Main results

* `Stacks.EtaleCohomology.etaleModuleBaseChangeTwist_sheafCompose`: the base change twist
  commutes with `Γ`.
* `Stacks.EtaleCohomology.frobeniusBaseChangeTwist_sheafCompose`: the same for the Frobenius base
  change twist.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

section Twist

variable {R S : Type} [Ring R] [Ring S] (Gf : ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} S)
  [∀ X : Scheme.{u}, X.smallEtaleTopology.HasSheafCompose Gf]
  {Y' Y : Scheme.{u}} (g : Y' ⟶ Y) (a : Y' ⟶ Y') (b : Y ⟶ Y) (w : a ≫ g = g ≫ b)

/-- The component at `L` of the comparison `g^{-1}(Γ L) ⟶ Γ(g^{-1} L)`. -/
abbrev inverseImageCoefficientMateApp (L : EtaleModules.{u, 0} R Y) :
    (etaleModuleInverseImage.{u, 0} S g).obj ((sheafCompose Y.smallEtaleTopology Gf).obj L) ⟶
      (sheafCompose Y'.smallEtaleTopology Gf).obj ((etaleModuleInverseImage.{u, 0} R g).obj L) :=
  (sheafComposeCoefficientMate (smallEtaleBaseChange g) Y.smallEtaleTopology Y'.smallEtaleTopology
    (etaleModuleInverseImageAdj.{u, 0} R g) (etaleModuleInverseImageAdj.{u, 0} S g)
    Gf).app L

/-- `Γ` applied to the unit of `g^{-1} ⊣ g_*` is the unit at `Γ L` followed by direct
image of the inverse-image comparison. -/
theorem sheafCompose_map_inverseImageAdj_unit (L : EtaleModules.{u, 0} R Y) :
    (sheafCompose Y.smallEtaleTopology Gf).map
        ((etaleModuleInverseImageAdj.{u, 0} R g).unit.app L) =
      (etaleModuleInverseImageAdj.{u, 0} S g).unit.app
          ((sheafCompose Y.smallEtaleTopology Gf).obj L) ≫
        (etaleModuleDirectImage.{u, 0} S g).map
          (inverseImageCoefficientMateApp Gf g L) :=
  coefficientMate_unit _ _ _ _ _ Gf L

/-- The composition isomorphism of direct images commutes with `Γ`. -/
theorem sheafCompose_mapIso_directImageComp_app {X Z : Scheme.{u}} (f : X ⟶ Y) (h : Y ⟶ Z)
    (fh : X ⟶ Z) (hfh : fh = f ≫ h) (F : EtaleModules.{u, 0} R X) :
    (sheafCompose Z.smallEtaleTopology Gf).mapIso
        ((etaleModuleDirectImageComp.{u, 0} R f h fh hfh).app F) =
      (etaleModuleDirectImageComp.{u, 0} S f h fh hfh).app
        ((sheafCompose X.smallEtaleTopology Gf).obj F) := by
  ext : 1
  apply Sheaf.hom_ext
  ext : 1
  rfl

variable (ψ' : 𝟭 (EtaleModules.{u, 0} R Y) ⟶ etaleModuleDirectImage.{u, 0} R b)
  (ψ : 𝟭 (EtaleModules.{u, 0} S Y) ⟶ etaleModuleDirectImage.{u, 0} S b)
  (hψ : ∀ L, (sheafCompose Y.smallEtaleTopology Gf).map (ψ'.app L) =
    ψ.app ((sheafCompose Y.smallEtaleTopology Gf).obj L))

include hψ in
/-- The adjoint form of the base change twist commutes with `Γ`. -/
theorem etaleModuleBaseChangeTwistAdj_sheafCompose (L : EtaleModules.{u, 0} R Y) :
    (sheafCompose Y.smallEtaleTopology Gf).map
        ((etaleModuleBaseChangeTwistAdj R g a b w ψ').app L) =
      (etaleModuleBaseChangeTwistAdj S g a b w ψ).app
          ((sheafCompose Y.smallEtaleTopology Gf).obj L) ≫
        (etaleModuleDirectImage.{u, 0} S g).map ((etaleModuleDirectImage.{u, 0} S a).map
          (inverseImageCoefficientMateApp Gf g L)) := by
  simp only [etaleModuleBaseChangeTwistAdj, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Category.id_comp, Category.comp_id, Functor.map_comp,
    Category.assoc]
  have e1 : (sheafCompose Y.smallEtaleTopology Gf).map
      ((etaleModuleDirectImage.{u, 0} R b).map
        ((etaleModuleInverseImageAdj.{u, 0} R g).unit.app L)) =
      (etaleModuleDirectImage.{u, 0} S b).map
        ((etaleModuleInverseImageAdj.{u, 0} S g).unit.app
            ((sheafCompose Y.smallEtaleTopology Gf).obj L) ≫
          (etaleModuleDirectImage.{u, 0} S g).map
            (inverseImageCoefficientMateApp Gf g L)) :=
    congrArg (etaleModuleDirectImage.{u, 0} S b).map
      (sheafCompose_map_inverseImageAdj_unit Gf g L)
  have e2 := congrArg Iso.hom (sheafCompose_mapIso_directImageComp_app Gf g b (a ≫ g) w
    ((etaleModuleInverseImage.{u, 0} R g).obj L))
  have e3 := congrArg Iso.inv (sheafCompose_mapIso_directImageComp_app Gf a g (a ≫ g) rfl
    ((etaleModuleInverseImage.{u, 0} R g).obj L))
  simp only [Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv] at e2 e3
  rw [e1, e2, e3, Functor.map_comp]
  have n1 := (etaleModuleDirectImageComp.{u, 0} S g b (a ≫ g) w).hom.naturality
    (inverseImageCoefficientMateApp Gf g L)
  have n2 := (etaleModuleDirectImageComp.{u, 0} S a g (a ≫ g) rfl).inv.naturality
    (inverseImageCoefficientMateApp Gf g L)
  refine (congrArg (· ≫ _) (hψ L)).trans (congrArg (ψ.app _ ≫ ·) ?_)
  refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_)
  exact ((reassoc_of% n1) _).trans (congrArg (_ ≫ ·) n2)

include hψ in
/-- **The base change twist commutes with a change of coefficients `Γ`.** -/
theorem etaleModuleBaseChangeTwist_sheafCompose (L : EtaleModules.{u, 0} R Y) :
    (etaleModuleBaseChangeTwist S g a b w ψ).app ((sheafCompose Y.smallEtaleTopology Gf).obj L) ≫
        (etaleModuleDirectImage.{u, 0} S a).map
          (inverseImageCoefficientMateApp Gf g L) =
      inverseImageCoefficientMateApp Gf g L ≫
        (sheafCompose Y'.smallEtaleTopology Gf).map
          ((etaleModuleBaseChangeTwist R g a b w ψ').app L) := by
  have hT : ∀ (Λ₀ : Type) [Ring Λ₀] (ψ₀ : 𝟭 (EtaleModules.{u, 0} Λ₀ Y) ⟶
      etaleModuleDirectImage.{u, 0} Λ₀ b) (M : EtaleModules.{u, 0} Λ₀ Y),
      (etaleModuleInverseImageAdj.{u, 0} Λ₀ g).unit.app M ≫
        (etaleModuleDirectImage.{u, 0} Λ₀ g).map
          ((etaleModuleBaseChangeTwist Λ₀ g a b w ψ₀).app M) =
        (etaleModuleBaseChangeTwistAdj Λ₀ g a b w ψ₀).app M := by
    intro Λ₀ _ ψ₀ M
    rw [etaleModuleBaseChangeTwist_app]
    exact (Adjunction.homEquiv_unit _ _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  apply ((etaleModuleInverseImageAdj.{u, 0} S g).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  rw [Functor.map_comp,
    reassoc_of% (hT S ψ ((sheafCompose Y.smallEtaleTopology Gf).obj L)),
    ← etaleModuleBaseChangeTwistAdj_sheafCompose Gf g a b w ψ' ψ hψ L, ← hT R ψ' L,
    Functor.map_comp]
  refine Eq.trans ?_ (Adjunction.homEquiv_unit _ _ _ _).symm
  exact (congrArg (· ≫ _) (sheafCompose_map_inverseImageAdj_unit Gf g L)).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
      ((etaleModuleDirectImage.{u, 0} S g).map_comp (inverseImageCoefficientMateApp Gf g L)
        ((sheafCompose Y'.smallEtaleTopology Gf).map
          ((etaleModuleBaseChangeTwist R g a b w ψ').app L))).symm))

end Twist

section Frobenius

open Stacks.Frobenius

variable {R S : Type} [Ring R] [Ring S] (Gf : ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} S)
  [∀ X : Scheme.{u}, X.smallEtaleTopology.HasSheafCompose Gf]
  {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k)))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- The Frobenius descent isomorphism of [Tag 03SR] commutes with any change of coefficients:
on sections it is a restriction map of the sheaf. -/
theorem sheafCompose_map_geometricFrobeniusPushforwardIso (L : EtaleModules.{u, 0} R Y.left) :
    (sheafCompose Y.left.smallEtaleTopology Gf).map
        ((geometricFrobeniusPushforwardIso Y p q hcard (ModuleCat.{u + 1} R)).hom.app L) =
      (geometricFrobeniusPushforwardIso Y p q hcard (ModuleCat.{u + 1} S)).hom.app
        ((sheafCompose Y.left.smallEtaleTopology Gf).obj L) := by
  apply Sheaf.hom_ext
  ext U : 2
  exact (congrArg Gf.map
    (geometricFrobeniusPushforwardIso_hom_app_hom_app Y p q hcard (ModuleCat.{u + 1} R) L
      U.unop)).trans
    (geometricFrobeniusPushforwardIso_hom_app_hom_app Y p q hcard (ModuleCat.{u + 1} S)
      ((sheafCompose Y.left.smallEtaleTopology Gf).obj L) U.unop).symm

/-- **The Frobenius base change twist commutes with a change of coefficients.** -/
theorem frobeniusBaseChangeTwist_sheafCompose (L : EtaleModules.{u, 0} R Y.left) :
    (frobeniusBaseChangeTwist.{u, 0} S Y kbar p q hcard).app
        ((sheafCompose Y.left.smallEtaleTopology Gf).obj L) ≫
        (etaleModuleDirectImage.{u, 0} S (geometricFrobeniusBaseChange Y kbar p q hcard)).map
          (inverseImageCoefficientMateApp Gf (fieldBaseChangeProj Y kbar) L) =
      inverseImageCoefficientMateApp Gf (fieldBaseChangeProj Y kbar) L ≫
        (sheafCompose (fieldBaseChange Y kbar).smallEtaleTopology Gf).map
          ((frobeniusBaseChangeTwist.{u, 0} R Y kbar p q hcard).app L) :=
  etaleModuleBaseChangeTwist_sheafCompose Gf _ _ _ _ _ _
    (sheafCompose_map_geometricFrobeniusPushforwardIso Gf Y p q hcard) L

end Frobenius

end Stacks.EtaleCohomology

end
