module

public import StacksFrontier.Deformation.ToposThickening.Helpers.PushforwardModuleTensorIsoPairing

/-!
# Pairing identities for the descended obstruction classes along a morphism of thickenings

Generic identities used to compare the actions on two thickenings related by a morphism of their
targets, on the universal pairings:

* a morphism out of a tensor product given by a bilinear pairing has that pairing
  (`Stacks.SheafOfModules.tensorSectionPairing_comp_bilinearEquivTensorHom`);
* a natural isomorphism `θ : Φ ≅ Ψ` of finite-product-preserving functors is compatible with
  the comparisons `Φ(A × B) ≅ ΦA × ΦB`
  (`Stacks.SheafOfModules.preservesLimitPair_iso_inv_comp_app`);
* the comparison of a composite of finite-product-preserving functors is the composite of the
  comparisons (`Stacks.SheafOfModules.preservesLimitPair_iso_inv_comp_functor`);
* the resulting identity of pushed pairings
  (`Stacks.SheafOfModules.prodMap_comp_pushPairing_eq_of_natIso`).

This module is a helper and carries no `@[stacks]` attribute.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf MonoidalCategory

universe v u w

namespace Stacks.SheafOfModules

section Bilinear

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {O : Sheaf J CommRingCat.{w}} {A B N : _root_.SheafOfModules.{w} (Tensor.ringSheaf O)}

/-- **The pairing of the morphism out of a tensor product determined by a bilinear pairing** is
that pairing. -/
theorem tensorSectionPairing_comp_bilinearEquivTensorHom
    (q : moduleSheaf (Tensor.ringSheaf O) A ⨯ moduleSheaf (Tensor.ringSheaf O) B ⟶
      moduleSheaf (Tensor.ringSheaf O) N) (hq : IsBilinearPairing (Tensor.ringSheaf O) q) :
    tensorSectionPairing A B ≫ (moduleSheafFunctor (Tensor.ringSheaf O)).map
      (bilinearEquivTensorHom ⟨q, hq⟩) = q := by
  refine pairing_ext _ fun U a b => ?_
  refine (pairingApp_comp _ _ U a b).trans ?_
  refine (congrArg _ (pairingApp_tensorSectionPairing A B U a b)).trans ?_
  exact (congrArg (fun t => t.app U (a ⊗ₜ[O.obj.obj U] b))
    (tensorHomEquivPresheafTensorHom.apply_symm_apply (tensorHomOfPairing hq))).trans
      (tensorHomOfPairing_app_tmul hq U a b)

end Bilinear

section Products

variable {𝒞 𝒟 ℰ : Type*} [Category* 𝒞] [Category* 𝒟] [Category* ℰ] [HasBinaryProducts 𝒞]
  [HasBinaryProducts 𝒟] [HasBinaryProducts ℰ]

omit [HasBinaryProducts 𝒟] in
/-- **A natural isomorphism of finite-product-preserving functors is compatible with the
comparisons of products.** -/
theorem preservesLimitPair_iso_inv_comp_app (Φ Ψ : 𝒞 ⥤ 𝒟) [PreservesFiniteProducts Φ]
    [PreservesFiniteProducts Ψ] (θ : Φ ⟶ Ψ) (A B : 𝒞) :
    (PreservesLimitPair.iso Φ A B).inv ≫ θ.app (A ⨯ B) =
      prod.map (θ.app A) (θ.app B) ≫ (PreservesLimitPair.iso Ψ A B).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  apply prod.hom_ext <;>
    simp only [Category.assoc, PreservesLimitPair.iso_hom, prodComparison_fst, prod.map_fst,
      prodComparison_fst_assoc, prodComparison_snd, prod.map_snd, prodComparison_snd_assoc] <;>
    exact (θ.naturality _).symm

omit [HasBinaryProducts 𝒟] [HasBinaryProducts ℰ] in
/-- **The comparison of products of a composite of finite-product-preserving functors** is the
composite of the comparisons. -/
theorem preservesLimitPair_iso_inv_comp_functor (Φ : 𝒞 ⥤ 𝒟) (Ψ : 𝒟 ⥤ ℰ)
    [PreservesFiniteProducts Φ] [PreservesFiniteProducts Ψ] (A B : 𝒞) :
    (PreservesLimitPair.iso (Φ ⋙ Ψ) A B).inv =
      (PreservesLimitPair.iso Ψ (Φ.obj A) (Φ.obj B)).inv ≫
        Ψ.map (PreservesLimitPair.iso Φ A B).inv := by
  refine Iso.inv_ext ?_
  rw [PreservesLimitPair.iso_hom, prodComparison_comp, Category.assoc,
    ← PreservesLimitPair.iso_hom Ψ (Φ.obj A) (Φ.obj B), Iso.hom_inv_id_assoc,
    ← CategoryTheory.Functor.map_comp, ← PreservesLimitPair.iso_hom Φ A B, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id]
  rfl

/-- **Pushing pairings along a natural isomorphism `θ : Φ ⋙ Ψ ≅ Φ'`**: the pairing
`(μ, θ⁻¹)` followed by `Ψ` of the pushed pairing `(ε, 1)` of `τ` and by `θ`, is the pushed
pairing `(μ ∘ Ψε ∘ θ, 1)` of `τ` along `Φ'`. -/
theorem prodMap_comp_pushPairing_eq_of_natIso (Φ : 𝒞 ⥤ 𝒟) (Ψ : 𝒟 ⥤ ℰ) (Φ' : 𝒞 ⥤ ℰ)
    [PreservesFiniteProducts Φ] [PreservesFiniteProducts Ψ] [PreservesFiniteProducts Φ']
    (θ : Φ ⋙ Ψ ≅ Φ') {A B N : 𝒞} (τ : A ⨯ B ⟶ N) {I₁ : ℰ} {I₂ : 𝒟} (μ : I₁ ⟶ Ψ.obj I₂)
    (ε₂ : I₂ ⟶ Φ.obj A) (ε₁ : I₁ ⟶ Φ'.obj A) (hH : ε₁ = μ ≫ Ψ.map ε₂ ≫ θ.hom.app A) :
    prod.map ε₁ (𝟙 _) ≫ (PreservesLimitPair.iso Φ' A B).inv ≫ Φ'.map τ =
      prod.map μ (θ.inv.app B) ≫ (PreservesLimitPair.iso Ψ I₂ (Φ.obj B)).inv ≫
        Ψ.map (prod.map ε₂ (𝟙 _) ≫ (PreservesLimitPair.iso Φ A B).inv ≫ Φ.map τ) ≫
          θ.hom.app N := by
  have hθ := preservesLimitPair_iso_inv_comp_app (Φ ⋙ Ψ) Φ' θ.hom A B
  have hc := preservesLimitPair_iso_inv_comp_functor Φ Ψ A B
  have hn := θ.hom.naturality τ
  simp only [Functor.comp_map] at hn
  rw [hH]
  simp only [Functor.map_comp, Category.assoc]
  rw [hn, ← Category.assoc (PreservesLimitPair.iso Ψ I₂ (Φ.obj B)).inv,
    preservesLimitPair_iso_inv_naturality Ψ ε₂ (𝟙 _), Category.assoc,
    ← Category.assoc (PreservesLimitPair.iso Ψ (Φ.obj A) (Φ.obj B)).inv, ← hc,
    ← Category.assoc (PreservesLimitPair.iso (Φ ⋙ Ψ) A B).inv, hθ]
  simp only [← Category.assoc, prod.map_map, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id_app, Functor.comp_obj]

end Products

end Stacks.SheafOfModules

end
