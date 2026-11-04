module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ExtensionByZeroSelfMapTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantTwistedFrobeniusFix

/-!
# The restriction of the canonical twist of a constant sheaf to a stable open

Let `j : V ⟶ V̄` be an open immersion, `σ : V̄ ⟶ V̄` an integral morphism and `a : V ⟶ V` with
`V = σ^{-1}(V)` (`IsPullback a j j σ`). Through `j^{-1} M_{V̄} ≅ M_V`, the restriction to `V` of
the canonical map `M_{V̄} ⟶ σ_* M_{V̄}`, followed by `j^{-1} σ_* ≅ a_* j^{-1}`, is the canonical
map `M_V ⟶ a_* M_V`.

## Main results

* `Stacks.EtaleCohomology.restrictionConstantIso`: `j^{-1} M_{V̄} ≅ M_V`, through restriction.
* `Stacks.EtaleCohomology.restrictionConstantIso_hom_comp_constantSelfMapTwist`: the restriction
  of the canonical twist of `M_{V̄}` is the canonical twist of `M_V`.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Steps 8 and 9.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable (Λ : Type) [CommRing Λ] (M : ModuleCat.{u + 1} Λ) {V Vb : Scheme.{u}} (j : V ⟶ Vb)
  [Etale j] [Mono j] (a : V ⟶ V) (σ : Vb ⟶ Vb) [IsIntegralHom σ] (sq : IsPullback a j j σ)

/-- The inverse of a composite `e₁ ≪≫ (asIso b)⁻¹ ≪≫ e₃` of natural isomorphisms, on an object. -/
private lemma trans_asIso_symm_trans_inv_app {C D : Type*} [Category* C] [Category* D]
    {P Q R S : C ⥤ D} (e₁ : P ≅ Q) (b : R ⟶ Q) [IsIso b] (e₃ : R ≅ S) (X : C) :
    (e₁ ≪≫ (asIso b).symm ≪≫ e₃).inv.app X = e₃.inv.app X ≫ b.app X ≫ e₁.inv.app X := by
  simp

/-- The inverse of `restrictionDirectImageIso` on an object: restriction is inverse image, followed
by the base change map. -/
lemma restrictionDirectImageIso_inv_app {U Ub V' Vb' : Scheme.{u}} (j₀ : U ⟶ Ub) [Etale j₀]
    [Mono j₀] (j₀' : V' ⟶ Vb') [Etale j₀'] [Mono j₀'] (f₀ : V' ⟶ U) (fb₀ : Vb' ⟶ Ub)
    [IsIntegralHom fb₀] (sq₀ : IsPullback f₀ j₀' j₀ fb₀) (G : EtaleModules.{u, 0} Λ Vb') :
    (restrictionDirectImageIso Λ j₀ j₀' f₀ fb₀ sq₀).inv.app G =
      (etaleModuleInverseImageRestrictionIso.{u, 0} Λ j₀).inv.app
          ((etaleModuleDirectImage.{u, 0} Λ fb₀).obj G) ≫
        (etaleModuleBaseChange Λ fb₀ f₀ j₀ j₀' sq₀.w).app G ≫
        (etaleModuleDirectImage.{u, 0} Λ f₀).map
          ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ j₀').hom.app G) := by
  have := isIso_etaleModuleBaseChange_of_isIntegralHom Λ fb₀ f₀ j₀ j₀' sq₀
  have e : restrictionDirectImageIso Λ j₀ j₀' f₀ fb₀ sq₀ =
      Functor.isoWhiskerRight (etaleModuleInverseImageRestrictionIso.{u, 0} Λ j₀').symm _ ≪≫
        (asIso (etaleModuleBaseChange Λ fb₀ f₀ j₀ j₀' sq₀.w)).symm ≪≫
        Functor.isoWhiskerLeft _ (etaleModuleInverseImageRestrictionIso.{u, 0} Λ j₀) := rfl
  rw [e, trans_asIso_symm_trans_inv_app]
  rfl

/-- **`j^{-1} M_{V̄} ≅ M_V`**, with `j^{-1}` read as restriction. -/
abbrev restrictionConstantIso :
    (etaleModuleRestriction.{u, 0} Λ j).obj (etaleModuleConstantSheaf Λ M Vb) ≅
      etaleModuleConstantSheaf Λ M V :=
  (etaleModuleInverseImageRestrictionIso.{u, 0} Λ j).symm.app _ ≪≫
    inverseImageEtaleModuleConstantSheafIso.{u, 0} Λ M j

include sq in
/-- **The restricted canonical twist is the canonical twist of `M_V`.** -/
theorem restrictionConstantIso_hom_comp_constantSelfMapTwist :
    (restrictionConstantIso Λ M j).hom ≫ constantSelfMapTwist Λ M a =
      ((etaleModuleRestriction.{u, 0} Λ j).map (constantSelfMapTwist Λ M σ) ≫
          (restrictionDirectImageIso Λ j j a σ sq).inv.app (etaleModuleConstantSheaf Λ M Vb)) ≫
        (etaleModuleDirectImage.{u, 0} Λ a).map (restrictionConstantIso Λ M j).hom := by
  set τ := (etaleModuleInverseImage.{u, 0} Λ j).map (constantSelfMapTwist Λ M σ) ≫
    (etaleModuleBaseChange Λ σ a j j sq.w).app (etaleModuleConstantSheaf Λ M Vb) with hτ
  have hfix : transportedConstantTwist.{u, 0} Λ M j a τ = constantSelfMapTwist Λ M a := by
    apply constantSheaf_hom_ext Λ M
    obtain ⟨ρ₂, hρ⟩ := exists_pulledBackConstantSection_comp_etaleModuleBaseChange Λ M σ a j sq.w
    rw [constantSheafSection_comp_transportedConstantTwist Λ M j a τ ρ₂ (by
      simpa only [hτ, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, Category.assoc]
        using hρ), constantSheafSection_comp_constantSelfMapTwist]
  have hn := (etaleModuleInverseImageRestrictionIso.{u, 0} Λ j).inv.naturality
    (constantSelfMapTwist Λ M σ)
  rw [← hfix, restrictionDirectImageIso_inv_app]
  simp only [restrictionConstantIso, transportedConstantTwist, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, inverseImageEtaleModuleConstantSheafIso, Category.assoc,
    Functor.map_comp]
  rw [reassoc_of% hn, hτ]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]

end Stacks.EtaleCohomology

end
