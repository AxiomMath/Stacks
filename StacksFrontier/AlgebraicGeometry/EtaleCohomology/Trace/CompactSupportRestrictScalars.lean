module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalarsDerived
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalCompactSupportFrobeniusNatTrans

/-!
# Compactly supported cohomology of the geometric fibre and restriction of scalars

Let `ρ : Λ →+* Λ'` be a morphism of rings and `res_ρ` the restriction of scalars of sheaves of
modules on the small étale site along `ρ`. The base change twist
`Stacks.EtaleCohomology.etaleModuleBaseChangeTwist`, out of which the action of the geometric
Frobenius on `RΓ_c(X_k̄, K)` (`Stacks.EtaleCohomology.compactSupportFrobeniusFunctor`) is built,
commutes with `res_ρ`, and so does its Frobenius instance
`Stacks.EtaleCohomology.frobeniusBaseChangeTwist`.

## Main results

* `Stacks.EtaleCohomology.etaleModuleBaseChangeTwist_restrictScalars`: the base change twist
  commutes with `res_ρ`.
* `Stacks.EtaleCohomology.frobeniusBaseChangeTwist_restrictScalars`: the Frobenius base change
  twist commutes with `res_ρ`.

## References

* [Stacks Project, Tag 03V2](https://stacks.math.columbia.edu/tag/03V2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

variable {Λ Λ' : Type} [Ring Λ] [Ring Λ'] (ρ : Λ →+* Λ')

/-! ### The base change twist and restriction of scalars -/

section Twist

variable {Y' Y : Scheme.{u}} (g : Y' ⟶ Y) (a : Y' ⟶ Y') (b : Y ⟶ Y) (w : a ≫ g = g ≫ b)

/-- The comparison `g^{-1} ∘ res_ρ ⟶ res_ρ ∘ g^{-1}` of inverse images. -/
abbrev inverseImageRestrictScalarsTwoSquare :=
  coefficientSheafPullbackTwoSquare (smallEtaleBaseChange g) Y.smallEtaleTopology
    Y'.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} ρ)

/-- The component at `L` of the comparison `g^{-1} ∘ res_ρ ⟶ res_ρ ∘ g^{-1}`. -/
abbrev inverseImageRestrictScalarsApp (L : EtaleModules.{u, 0} Λ' Y) :
    (etaleModuleInverseImage.{u, 0} Λ g).obj ((etaleModuleRestrictScalars ρ Y).obj L) ⟶
      (etaleModuleRestrictScalars ρ Y').obj ((etaleModuleInverseImage.{u, 0} Λ' g).obj L) :=
  (inverseImageRestrictScalarsTwoSquare ρ g).natTrans.app L

/-- `res_ρ` applied to the unit of `g^{-1} ⊣ g_*` is the unit at `res_ρ L` followed by direct
image of the inverse-image comparison. -/
theorem restrictScalars_map_inverseImageAdj_unit (L : EtaleModules.{u, 0} Λ' Y) :
    (etaleModuleRestrictScalars ρ Y).map ((etaleModuleInverseImageAdj.{u, 0} Λ' g).unit.app L) =
      (etaleModuleInverseImageAdj.{u, 0} Λ g).unit.app ((etaleModuleRestrictScalars ρ Y).obj L) ≫
        (etaleModuleDirectImage.{u, 0} Λ g).map
          (inverseImageRestrictScalarsApp ρ g L) :=
  coefficientSheafPullbackTwoSquare_unit _ _ _ _ L

/-- The composition isomorphism of direct images commutes with `res_ρ`. -/
theorem restrictScalars_mapIso_directImageComp_app {X Z : Scheme.{u}} (f : X ⟶ Y) (h : Y ⟶ Z)
    (fh : X ⟶ Z) (hfh : fh = f ≫ h) (F : EtaleModules.{u, 0} Λ' X) :
    (etaleModuleRestrictScalars ρ Z).mapIso
        ((etaleModuleDirectImageComp.{u, 0} Λ' f h fh hfh).app F) =
      (etaleModuleDirectImageComp.{u, 0} Λ f h fh hfh).app
        ((etaleModuleRestrictScalars ρ X).obj F) := by
  ext : 1
  apply Sheaf.hom_ext
  ext : 1
  rfl

variable (ψ' : 𝟭 (EtaleModules.{u, 0} Λ' Y) ⟶ etaleModuleDirectImage.{u, 0} Λ' b)
  (ψ : 𝟭 (EtaleModules.{u, 0} Λ Y) ⟶ etaleModuleDirectImage.{u, 0} Λ b)
  (hψ : ∀ L, (etaleModuleRestrictScalars ρ Y).map (ψ'.app L) =
    ψ.app ((etaleModuleRestrictScalars ρ Y).obj L))

include hψ in
/-- The adjoint form of the base change twist commutes with `res_ρ`. -/
theorem etaleModuleBaseChangeTwistAdj_restrictScalars (L : EtaleModules.{u, 0} Λ' Y) :
    (etaleModuleRestrictScalars ρ Y).map ((etaleModuleBaseChangeTwistAdj Λ' g a b w ψ').app L) =
      (etaleModuleBaseChangeTwistAdj Λ g a b w ψ).app ((etaleModuleRestrictScalars ρ Y).obj L) ≫
        (etaleModuleDirectImage.{u, 0} Λ g).map ((etaleModuleDirectImage.{u, 0} Λ a).map
          (inverseImageRestrictScalarsApp ρ g L)) := by
  simp only [etaleModuleBaseChangeTwistAdj, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Category.id_comp, Category.comp_id, Functor.map_comp,
    Category.assoc]
  have e1 : (etaleModuleRestrictScalars ρ Y).map
      ((etaleModuleDirectImage.{u, 0} Λ' b).map
        ((etaleModuleInverseImageAdj.{u, 0} Λ' g).unit.app L)) =
      (etaleModuleDirectImage.{u, 0} Λ b).map
        ((etaleModuleInverseImageAdj.{u, 0} Λ g).unit.app ((etaleModuleRestrictScalars ρ Y).obj L) ≫
          (etaleModuleDirectImage.{u, 0} Λ g).map
            (inverseImageRestrictScalarsApp ρ g L)) :=
    congrArg (etaleModuleDirectImage.{u, 0} Λ b).map
      (restrictScalars_map_inverseImageAdj_unit ρ g L)
  have e2 := congrArg Iso.hom (restrictScalars_mapIso_directImageComp_app ρ g b (a ≫ g) w
    ((etaleModuleInverseImage.{u, 0} Λ' g).obj L))
  have e3 := congrArg Iso.inv (restrictScalars_mapIso_directImageComp_app ρ a g (a ≫ g) rfl
    ((etaleModuleInverseImage.{u, 0} Λ' g).obj L))
  simp only [Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv] at e2 e3
  rw [e1, e2, e3, Functor.map_comp]
  refine (congrArg (· ≫ _) (hψ L)).trans (congrArg (ψ.app _ ≫ ·) ?_)
  have n1 := (etaleModuleDirectImageComp.{u, 0} Λ g b (a ≫ g) w).hom.naturality
    (inverseImageRestrictScalarsApp ρ g L)
  have n2 := (etaleModuleDirectImageComp.{u, 0} Λ a g (a ≫ g) rfl).inv.naturality
    (inverseImageRestrictScalarsApp ρ g L)
  refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_)
  erw [reassoc_of% n1, n2]
  rfl

include hψ in
/-- **The base change twist commutes with restriction of scalars.** -/
theorem etaleModuleBaseChangeTwist_restrictScalars (L : EtaleModules.{u, 0} Λ' Y) :
    (etaleModuleBaseChangeTwist Λ g a b w ψ).app ((etaleModuleRestrictScalars ρ Y).obj L) ≫
        (etaleModuleDirectImage.{u, 0} Λ a).map
          (inverseImageRestrictScalarsApp ρ g L) =
      inverseImageRestrictScalarsApp ρ g L ≫
        (etaleModuleRestrictScalars ρ Y').map
          ((etaleModuleBaseChangeTwist Λ' g a b w ψ').app L) := by
  have hT : ∀ (Λ₀ : Type) [Ring Λ₀] (ψ₀ : 𝟭 (EtaleModules.{u, 0} Λ₀ Y) ⟶
      etaleModuleDirectImage.{u, 0} Λ₀ b) (M : EtaleModules.{u, 0} Λ₀ Y),
      (etaleModuleInverseImageAdj.{u, 0} Λ₀ g).unit.app M ≫
        (etaleModuleDirectImage.{u, 0} Λ₀ g).map
          ((etaleModuleBaseChangeTwist Λ₀ g a b w ψ₀).app M) =
        (etaleModuleBaseChangeTwistAdj Λ₀ g a b w ψ₀).app M := by
    intro Λ₀ _ ψ₀ M
    rw [etaleModuleBaseChangeTwist_app]
    exact (Adjunction.homEquiv_unit _ _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  apply ((etaleModuleInverseImageAdj.{u, 0} Λ g).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  rw [Functor.map_comp,
    reassoc_of% (hT Λ ψ ((etaleModuleRestrictScalars ρ Y).obj L)),
    ← etaleModuleBaseChangeTwistAdj_restrictScalars ρ g a b w ψ' ψ hψ L, ← hT Λ' ψ' L,
    Functor.map_comp]
  refine Eq.trans ?_ (Adjunction.homEquiv_unit _ _ _ _).symm
  exact (congrArg (· ≫ _) (restrictScalars_map_inverseImageAdj_unit ρ g L)).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
      ((etaleModuleDirectImage.{u, 0} Λ g).map_comp (inverseImageRestrictScalarsApp ρ g L)
        ((etaleModuleRestrictScalars ρ Y').map
          ((etaleModuleBaseChangeTwist Λ' g a b w ψ').app L))).symm))

end Twist

/-! ### The Frobenius twist -/

section Frobenius

variable {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k)))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- The Frobenius descent isomorphism of [Tag 03SR] commutes with restriction of scalars. -/
theorem restrictScalars_map_geometricFrobeniusPushforwardIso (L : EtaleModules.{u, 0} Λ' Y.left) :
    (etaleModuleRestrictScalars ρ Y.left).map
        ((geometricFrobeniusPushforwardIso Y p q hcard (ModuleCat.{u + 1} Λ')).hom.app L) =
      (geometricFrobeniusPushforwardIso Y p q hcard (ModuleCat.{u + 1} Λ)).hom.app
        ((etaleModuleRestrictScalars ρ Y.left).obj L) := by
  apply Sheaf.hom_ext
  ext U : 2
  refine (congrArg (ModuleCat.restrictScalars.{u + 1} ρ).map
    (geometricFrobeniusPushforwardIso_hom_app_hom_app Y p q hcard (ModuleCat.{u + 1} Λ') L
      U.unop)).trans ?_
  exact (geometricFrobeniusPushforwardIso_hom_app_hom_app Y p q hcard (ModuleCat.{u + 1} Λ)
    ((etaleModuleRestrictScalars ρ Y.left).obj L) U.unop).symm

/-- **The Frobenius base change twist commutes with restriction of scalars.** -/
theorem frobeniusBaseChangeTwist_restrictScalars (L : EtaleModules.{u, 0} Λ' Y.left) :
    (frobeniusBaseChangeTwist.{u, 0} Λ Y kbar p q hcard).app
        ((etaleModuleRestrictScalars ρ Y.left).obj L) ≫
        (etaleModuleDirectImage.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar p q hcard)).map
          (inverseImageRestrictScalarsApp ρ (fieldBaseChangeProj Y kbar) L) =
      inverseImageRestrictScalarsApp ρ (fieldBaseChangeProj Y kbar) L ≫
        (etaleModuleRestrictScalars ρ (fieldBaseChange Y kbar)).map
          ((frobeniusBaseChangeTwist.{u, 0} Λ' Y kbar p q hcard).app L) :=
  etaleModuleBaseChangeTwist_restrictScalars ρ _ _ _ _ _ _
    (restrictScalars_map_geometricFrobeniusPushforwardIso ρ Y p q hcard) L

end Frobenius

end Stacks.EtaleCohomology

end
