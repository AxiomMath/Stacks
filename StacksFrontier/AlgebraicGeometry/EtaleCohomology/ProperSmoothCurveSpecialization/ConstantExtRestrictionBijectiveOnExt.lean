module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CupProductRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedSectionsRestrictionOfExt

/-!
# Restriction of `H^*(-, Λ)` is bijective iff the inverse image is bijective on `Ext(ℤ, U Λ)`

Let `g : Y ⟶ X` be a morphism of schemes and `Λ` a commutative ring. Restriction
`g^* : Hⁱ(X, Λ) → Hⁱ(Y, Λ)` of étale cohomology with coefficients in the constant sheaf `Λ`,
computed as `Ext^i_Λ(Λ_X, Λ_X)` (`Stacks.EtaleCohomology.constantExtRestriction`), is bijective
in degree `i` exactly when the inverse image `g⁻¹` of abelian sheaves is bijective on
`Ext^i(ℤ_X, U Λ_X)`, `U` forgetting the `Λ`-module structure. This is the form in which the
derived restriction of global sections is controlled
(`isIso_smallEtaleDerivedGlobalSectionsRestriction_single_of_isBijectiveOnExt`).

The two groups are identified by `Ext^i_Λ(Λ, M) ≃+ Hⁱ(U M)`
(`Stacks.EtaleCohomology.extForgetSheafH`), compatibly with restriction
(`Stacks.EtaleCohomology.extForgetSheafH_etaleModuleExtRestriction`), and `Hⁱ(X, F)` with
`Ext^i(ℤ_X, F)` (`etaleCohomologyRestrictionMap_bijective_iff_isBijectiveOnExt`).

## Main results

* `Stacks.EtaleCohomology.bijective_constantExtRestriction_iff_isBijectiveOnExt`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- **Postcomposition with an isomorphism of degree zero is bijective on `Ext`.** -/
theorem bijective_comp_mk₀_of_iso {𝒞 : Type*} [Category* 𝒞] [Abelian 𝒞] [HasExt.{u + 1} 𝒞]
    {A B B' : 𝒞} (e : B ≅ B') (q : ℕ) :
    Function.Bijective (fun x : Ext.{u + 1} A B q => x.comp (Ext.mk₀ e.hom) (add_zero q)) := by
  have key : ∀ {C D : 𝒞} (e : C ≅ D) (x : Ext.{u + 1} A C q),
      (x.comp (Ext.mk₀ e.hom) (add_zero q)).comp (Ext.mk₀ e.inv) (add_zero q) = x := fun e x => by
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, e.hom_inv_id, Ext.comp_mk₀_id]
  exact Function.bijective_iff_has_inverse.2
    ⟨fun y => y.comp (Ext.mk₀ e.inv) (add_zero q), key e, key e.symm⟩

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type) [CommRing Λ] {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- **Restriction of `H^*(-, Λ)` along `g` is bijective in degree `q` iff `g⁻¹` is bijective on
`Ext^q(ℤ_X, U Λ_X)`.** -/
theorem bijective_constantExtRestriction_iff_isBijectiveOnExt (q : ℕ) :
    Function.Bijective (constantExtRestriction Λ g q) ↔
      IsBijectiveOnExt (smallEtalePullbackAb g) (smallEtaleConstantInt X)
        ((etaleModuleUnderlyingAbelian X Λ).obj
          (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology)) q := by
  set M := Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology
  -- `g^*` is `etaleModuleExtRestriction` followed by a bijection
  have h1 : Function.Bijective (constantExtRestriction Λ g q) ↔
      Function.Bijective (etaleModuleExtRestriction Λ g M q) := by
    have hfun : (constantExtRestriction Λ g q : _ → _) =
        (fun x => x.comp (Ext.mk₀ (constantInverseImageIso Λ g).symm.hom) (add_zero q)) ∘
          etaleModuleExtRestriction Λ g M q := by
      funext a
      exact constantExtRestriction_eq Λ g a
    rw [hfun]
    exact Function.Bijective.of_comp_iff' (bijective_comp_mk₀_of_iso _ q) _
  -- through `Ext^q_Λ(Λ, -) ≃+ Hᵠ(U -)`, `etaleModuleExtRestriction` is the restriction map
  have h2 : Function.Bijective (etaleModuleExtRestriction Λ g M q) ↔
      Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1} g
        ((etaleModuleUnderlyingAbelian X Λ).obj M) q) := by
    have hX := extForgetSheafH_bijective Λ X q M
    have hY := extForgetSheafH_bijective Λ Y q ((etaleModuleInverseImage.{u, 0} Λ g).obj M)
    have hfun : (extForgetSheafH Λ Y _ q : _ → _) ∘ etaleModuleExtRestriction Λ g M q =
        (fun z => z.comp (Ext.mk₀ ((etaleModuleUnderlyingAbelianInverseImageIso Λ g).app M).hom)
          (add_zero q)) ∘
          etaleCohomologyRestrictionMap.{u, 0, u + 1} g
            ((etaleModuleUnderlyingAbelian X Λ).obj M) q ∘ extForgetSheafH Λ X M q := by
      funext a
      exact extForgetSheafH_etaleModuleExtRestriction Λ g M a
    rw [← Function.Bijective.of_comp_iff' hY, hfun,
      Function.Bijective.of_comp_iff' (bijective_comp_mk₀_of_iso _ q),
      Function.Bijective.of_comp_iff _ hX]
  -- and bijectivity of the restriction map is bijectivity of `g⁻¹` on `Ext(ℤ, -)`
  rw [h1, h2, etaleCohomologyRestrictionMap_bijective_iff_isBijectiveOnExt.{u, 0, u + 1}]
  exact (isBijectiveOnExt_congr (smallEtalePullbackAbIsoInverseImage g) _ _ q).symm

end Stacks.EtaleCohomology

end
