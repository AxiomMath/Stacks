module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ExtensionByZeroIntegralTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantTwistedFrobeniusFix

/-!
# The restriction of the canonical twist of a constant sheaf to a stable open, any ring

Let `Λ` be a ring, `j : V ⟶ V̄` an open immersion, `σ : V̄ ⟶ V̄` an integral morphism and
`a : V ⟶ V` with `V = σ^{-1}(V)` (`IsPullback a j j σ`). Through `j^{-1} M_{V̄} ≅ M_V`, the
restriction to `V` of the canonical map `M_{V̄} ⟶ σ_* M_{V̄}`, followed by
`j^{-1} σ_* ≅ a_* j^{-1}` (`Stacks.EtaleCohomology.restrictionIntegralDirectImageIso`), is the
canonical map `M_V ⟶ a_* M_V`.

This is the noncommutative-coefficient form of the statement used in Step 9 of the proof of
[Stacks, Tag 03UG]; the proof does not use commutativity of `Λ`. In [Stacks, Tag 03VK] it
identifies the Galois action on `H²(C, j_!(E_U))`, `C` the smooth projective model of the curve
`U`, with the Galois action on `H²(C, E_C)`.

## Main results

* `Stacks.EtaleCohomology.restrictionIntegralDirectImageIso_inv_app`.
* `Stacks.EtaleCohomology.restrictionInverseImageConstantIso_hom_comp_constantSelfMapTwist`.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Steps 8 and 9.
* [Stacks Project, Tag 03VK](https://stacks.math.columbia.edu/tag/03VK).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable (Λ : Type) [Ring Λ]

/-- The inverse of `restrictionIntegralDirectImageIso` on an object: restriction is inverse
image, followed by the base change map. -/
lemma restrictionIntegralDirectImageIso_inv_app {U Ub V' Vb' : Scheme.{u}} (j₀ : U ⟶ Ub)
    [Etale j₀] [Mono j₀] (j₀' : V' ⟶ Vb') [Etale j₀'] [Mono j₀'] (f₀ : V' ⟶ U) (fb₀ : Vb' ⟶ Ub)
    [IsIntegralHom fb₀] (sq₀ : IsPullback f₀ j₀' j₀ fb₀) (G : EtaleModules.{u, 0} Λ Vb') :
    (restrictionIntegralDirectImageIso Λ j₀ j₀' f₀ fb₀ sq₀).inv.app G =
      (etaleModuleInverseImageRestrictionIso.{u, 0} Λ j₀).inv.app
          ((etaleModuleDirectImage.{u, 0} Λ fb₀).obj G) ≫
        (etaleModuleBaseChange Λ fb₀ f₀ j₀ j₀' sq₀.w).app G ≫
        (etaleModuleDirectImage.{u, 0} Λ f₀).map
          ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ j₀').hom.app G) := by
  have : ∀ M, IsIso ((etaleModuleBaseChange Λ fb₀ f₀ j₀ j₀' sq₀.w).app M) :=
    isIso_etaleModuleBaseChange_app_of_isIntegralHom Λ fb₀ f₀ j₀ j₀' sq₀
  have := NatIso.isIso_of_isIso_app (etaleModuleBaseChange Λ fb₀ f₀ j₀ j₀' sq₀.w)
  have e : restrictionIntegralDirectImageIso Λ j₀ j₀' f₀ fb₀ sq₀ =
      Functor.isoWhiskerRight (etaleModuleInverseImageRestrictionIso.{u, 0} Λ j₀').symm _ ≪≫
        (asIso (etaleModuleBaseChange Λ fb₀ f₀ j₀ j₀' sq₀.w)).symm ≪≫
        Functor.isoWhiskerLeft _ (etaleModuleInverseImageRestrictionIso.{u, 0} Λ j₀) := rfl
  have hinv : ∀ {C D : Type _} [Category C] [Category D] {P Q R S : C ⥤ D} (e₁ : P ≅ Q)
      (b : R ⟶ Q) [IsIso b] (e₃ : R ≅ S) (X : C),
      (e₁ ≪≫ (asIso b).symm ≪≫ e₃).inv.app X = e₃.inv.app X ≫ b.app X ≫ e₁.inv.app X := by
    intros; simp
  rw [e, hinv]
  rfl

variable (M : ModuleCat.{u + 1} Λ) {V Vb : Scheme.{u}} (j : V ⟶ Vb) [Etale j] [Mono j]
  (a : V ⟶ V) (σ : Vb ⟶ Vb) [IsIntegralHom σ] (sq : IsPullback a j j σ)

include sq in
/-- **The restricted canonical twist is the canonical twist of `M_V`**, `Λ` any ring: through
`j^{-1} M_{V̄} ≅ M_V`, the restriction of `M_{V̄} ⟶ σ_* M_{V̄}` followed by
`j^{-1} σ_* ≅ a_* j^{-1}` is `M_V ⟶ a_* M_V`. -/
theorem restrictionInverseImageConstantIso_hom_comp_constantSelfMapTwist :
    ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ j).symm.app _ ≪≫
        inverseImageEtaleModuleConstantSheafIso.{u, 0} Λ M j).hom ≫ constantSelfMapTwist Λ M a =
      ((etaleModuleRestriction.{u, 0} Λ j).map (constantSelfMapTwist Λ M σ) ≫
          (restrictionIntegralDirectImageIso Λ j j a σ sq).inv.app
            (etaleModuleConstantSheaf Λ M Vb)) ≫
        (etaleModuleDirectImage.{u, 0} Λ a).map
          ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ j).symm.app _ ≪≫
            inverseImageEtaleModuleConstantSheafIso.{u, 0} Λ M j).hom := by
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
  rw [← hfix, restrictionIntegralDirectImageIso_inv_app]
  simp only [transportedConstantTwist, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, inverseImageEtaleModuleConstantSheafIso, Category.assoc,
    Functor.map_comp]
  rw [reassoc_of% hn, hτ]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]

include sq in
/-- `Stacks.EtaleCohomology.restrictionInverseImageConstantIso_hom_comp_constantSelfMapTwist`
with the identification `M_V ≅ j^{-1} M_{V̄}` moved across. -/
theorem constantSelfMapTwist_comp_map_restrictionInverseImageConstantIso_inv :
    constantSelfMapTwist Λ M a ≫ (etaleModuleDirectImage.{u, 0} Λ a).map
      ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ j).symm.app _ ≪≫
        inverseImageEtaleModuleConstantSheafIso.{u, 0} Λ M j).inv =
      ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ j).symm.app _ ≪≫
        inverseImageEtaleModuleConstantSheafIso.{u, 0} Λ M j).inv ≫
        ((etaleModuleRestriction.{u, 0} Λ j).map (constantSelfMapTwist Λ M σ) ≫
          (restrictionIntegralDirectImageIso Λ j j a σ sq).inv.app
            (etaleModuleConstantSheaf Λ M Vb)) := by
  have hγ := restrictionInverseImageConstantIso_hom_comp_constantSelfMapTwist Λ M j a σ sq
  rw [Iso.eq_inv_comp, ← Category.assoc, hγ, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id]
  exact Category.comp_id _

include sq in
/-- **Extension by zero of the canonical twist of `M_V`, compared with `M_{V̄}`.** The map
`ι : j_! M_V ≅ j_! j^{-1} M_{V̄} ⟶ M_{V̄}` (the counit) intertwines the twist
`j_!(M_V ⟶ a_* M_V) ≫ (j_! a_* ⟶ σ_* j_!)` of `j_! M_V` with the canonical twist
`M_{V̄} ⟶ σ_* M_{V̄}`. -/
theorem extensionByZeroConstantSelfMapTwist_comp_counit :
    ((etaleModuleExtensionByZero.{u, 0} Λ j).map (constantSelfMapTwist Λ M a) ≫
        extensionByZeroIntegralDirectImageMap Λ j j a σ sq (etaleModuleConstantSheaf Λ M V)) ≫
      (etaleModuleDirectImage.{u, 0} Λ σ).map
        ((etaleModuleExtensionByZero.{u, 0} Λ j).map
            (((etaleModuleInverseImageConstantIso.{u, 0} Λ j).app M).symm ≪≫
              (etaleModuleInverseImageRestrictionIso.{u, 0} Λ j).app _).hom ≫
          (etaleModuleExtensionByZeroAdj.{u, 0} Λ j).counit.app
            (etaleModuleConstantSheaf Λ M Vb)) =
      ((etaleModuleExtensionByZero.{u, 0} Λ j).map
            (((etaleModuleInverseImageConstantIso.{u, 0} Λ j).app M).symm ≪≫
              (etaleModuleInverseImageRestrictionIso.{u, 0} Λ j).app _).hom ≫
          (etaleModuleExtensionByZeroAdj.{u, 0} Λ j).counit.app
            (etaleModuleConstantSheaf Λ M Vb)) ≫ constantSelfMapTwist Λ M σ := by
  have hR : (((etaleModuleInverseImageConstantIso.{u, 0} Λ j).app M).symm ≪≫
      (etaleModuleInverseImageRestrictionIso.{u, 0} Λ j).app
        (etaleModuleConstantSheaf Λ M Vb)).hom =
      ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ j).symm.app _ ≪≫
        inverseImageEtaleModuleConstantSheafIso.{u, 0} Λ M j).inv := by
    simp [inverseImageEtaleModuleConstantSheafIso]
  rw [hR]
  have h1 := constantSelfMapTwist_comp_map_restrictionInverseImageConstantIso_inv Λ M j a σ sq
  have hn := extensionByZeroIntegralDirectImageMap_naturality Λ j j a σ sq
    ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ j).symm.app _ ≪≫
        inverseImageEtaleModuleConstantSheafIso.{u, 0} Λ M j).inv
  have hc := extensionByZeroIntegralTwist_comp_counit Λ j a σ sq
    (etaleModuleConstantSheaf Λ M Vb) (constantSelfMapTwist Λ M σ)
  rw [extensionByZeroIntegralTwist] at hc
  have hc' := hc
  simp only [Category.assoc] at hc'
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% hn, ← Functor.map_comp_assoc, h1, Functor.map_comp_assoc, hc']

end Stacks.EtaleCohomology

end
