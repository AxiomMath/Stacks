module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModuleTensor.InverseImageModuleSheafHomComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.TwistNegOneModuleInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.KummerClassMapLevel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.TwistNegOneInverseImageInput
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.EtaleLevelInverseImage

/-!
# The Tate twist commutes with inverse image, on towers

Let `g : Y ⟶ X` be a morphism of Noetherian schemes of a big étale site, `X` over a field in
which `ℓ` is invertible, and `F` an ℓ-adic sheaf on `X`. Level by level,
`g⁻¹ 𝓗om(μ_{ℓⁿ⁺¹}, Fₙ) ≅ 𝓗om(g⁻¹ μ_{ℓⁿ⁺¹}, g⁻¹ Fₙ) ≅ 𝓗om(μ_{ℓⁿ⁺¹}, (g⁻¹F)ₙ)`: the comparison
`Stacks.EtaleCohomology.etaleModuleInverseImageModuleSheafHomComparison` (an isomorphism, `μ` being
dualizable), followed by `g⁻¹ μ ≅ μ` and `g⁻¹ Fₙ ≅ (g⁻¹ F)ₙ`. These isomorphisms commute with the
transitions of the two twisted towers, which change the level `ℤ/ℓⁿ⁺² → ℤ/ℓⁿ⁺¹`
(`Stacks.EtaleCohomology.inverseImageRestrictScalars_comp_map_comparison_comp_homPrecomp`), so they
form an isomorphism of towers of sheaves of `ℤ_ℓ`-modules. This proves
`Stacks.EtaleCohomology.Purity.TwistNegOneTowerInverseImageInput`, the step
`i⁻¹ (G(-1)) ≅ (i⁻¹ G)(-1)` of the tower form of cohomological purity along a divisor
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main results

* `Stacks.EtaleCohomology.etaleModuleUnderlyingAbelianInverseImageIso_restrictScalars`.
* `Stacks.Kummer.rootsOfUnityModuleInverseImageIso_powMap`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open Functor.LaxMonoidal Functor.OplaxMonoidal Stacks.ConstantSheaf

universe u

namespace Stacks.EtaleCohomology

/-- **Forgetting the module structure after inverse image commutes with restriction of
scalars**: the identification `g⁻¹(U M) ≅ U(g⁻¹ M)` for `res_ρ M` is the one for `M` read through
`κ : g⁻¹ ∘ res_ρ ≅ res_ρ ∘ g⁻¹`. -/
theorem etaleModuleUnderlyingAbelianInverseImageIso_restrictScalars {Λ Λ' : Type} [CommRing Λ]
    [CommRing Λ'] (ρ : Λ →+* Λ') {X Y : Scheme.{u}} (g : Y ⟶ X) (M : EtaleModules.{u, 0} Λ' X) :
    (etaleModuleUnderlyingAbelianInverseImageIso Λ g).hom.app
        ((etaleModuleRestrictScalars ρ X).obj M) ≫
      (etaleModuleUnderlyingAbelian Y Λ).map
        ((etaleModuleInverseImageRestrictScalars ρ g).hom.app M) =
    (etaleModuleUnderlyingAbelianInverseImageIso Λ' g).hom.app M := by
  apply ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (smallEtaleBaseChange g)
    AddCommGrpCat.{u + 1} X.smallEtaleTopology Y.smallEtaleTopology).homEquiv _ _).injective
  refine ((Adjunction.homEquiv_unit _ _ _ _).trans ?_).trans (Adjunction.homEquiv_unit _ _ _ _).symm
  rw [Functor.map_comp, ← Category.assoc, ← etaleModuleUnderlyingAbelianInverseImageIso_unit]
  exact (((etaleModuleUnderlyingAbelian X Λ).map_comp _ _).symm.trans
    (congrArg (etaleModuleUnderlyingAbelian X Λ).map
      (etaleModuleInverseImageRestrictScalars_unit ρ g M))).trans
    (etaleModuleUnderlyingAbelianInverseImageIso_unit (g := g) (M := M))

end Stacks.EtaleCohomology

namespace Stacks.Kummer

open Stacks.EtaleCohomology

/-- A square of isomorphisms and morphisms, at variable objects: the shape of the compatibility
of `π⁻¹ μ ≅ μ` with the power maps after forgetting to abelian sheaves. -/
theorem comp_comp_eq_of_conj {C : Type*} [Category C] {P₁ P₂ P₃ P₄ P₅ Q₁ Q₂ : C}
    (x₁ : P₁ ⟶ P₂) (x₂ : P₂ ⟶ P₃) (x₃ : P₃ ⟶ P₄) (y₁ : P₁ ⟶ P₅) (y₂ : P₅ ⟶ P₄)
    (a : Q₁ ≅ P₁) (b : Q₂ ≅ P₂) (c : Q₂ ≅ P₃) (g : Q₁ ⟶ Q₂) (ι : Q₂ ⟶ P₄) (ι' : Q₁ ⟶ P₅)
    (hU : g ≫ b.hom = a.hom ≫ x₁) (hK : b.hom ≫ x₂ = c.hom) (h₃ : x₃ = c.inv ≫ ι)
    (h₄ : y₁ = a.inv ≫ ι') (hp : g ≫ ι = ι' ≫ y₂) : x₁ ≫ x₂ ≫ x₃ = y₁ ≫ y₂ := by
  rw [← cancel_epi a.hom, ← reassoc_of% hU, reassoc_of% hK, h₃, Iso.hom_inv_id_assoc, hp, h₄,
    Category.assoc, Iso.hom_inv_id_assoc]

/-- The underlying abelian morphism of the identification `π⁻¹ μ_{N,Y} ≅ μ_{N,X}` is the
comparison of abelian sheaves, read through `π⁻¹(U μ) ≅ U(π⁻¹ μ)`. -/
theorem etaleModuleForgetAb_map_rootsOfUnityModuleInverseImageIso_hom {X Y : Scheme.{u}}
    (π : X ⟶ Y) (N : ℕ) [NeZero N] (hN : IsUnit ((N : ℕ) : Γ(Y, ⊤))) :
    (etaleModuleForgetAb.{u, 0} (ZMod N) X).map (rootsOfUnityModuleInverseImageIso π N hN).hom =
      (etaleModuleUnderlyingAbelianInverseImageIso (ZMod N) π).inv.app
          (rootsOfUnityModule.{u, 0} Y N) ≫
        rootsOfUnityInverseImageComparison.{u, 0} π N := by
  rw [rootsOfUnityModuleInverseImageIso, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage]
  change _ ≫ (etaleAbelianInverseImage.{u, 0} π).map (𝟙 _) ≫ _ ≫ 𝟙 _ = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [Iso.symm_hom, Iso.app_inv, rootsOfUnityInverseImageIso_hom]
  exact congrArg (_ ≫ ·) (Category.comp_id _)

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **The identification `π⁻¹ μ ≅ μ` commutes with the `ℓ`-th power maps**, as morphisms of
sheaves of `ℤ/ℓN`-modules `π⁻¹ μ_{ℓN,Y} ⟶ res μ_{N,X}`. -/
theorem rootsOfUnityModuleInverseImageIso_powMap {X Y : Scheme.{u}} (π : X ⟶ Y) (ℓ N N' : ℕ)
    (hN : ℓ * N = N') [NeZero N] [NeZero N'] (hNY : IsUnit ((N : ℕ) : Γ(Y, ⊤)))
    (hN'Y : IsUnit ((N' : ℕ) : Γ(Y, ⊤))) :
    (etaleModuleInverseImage.{u, 0} (ZMod N') π).map (rootsOfUnityModulePowMap.{u, 0} Y ℓ N N' hN) ≫
        (etaleModuleInverseImageRestrictScalars
          (ZMod.castHom (dvd_of_mul_eq hN) (ZMod N)) π).hom.app
          (rootsOfUnityModule.{u, 0} Y N) ≫
        (etaleModuleRestrictScalars (ZMod.castHom (dvd_of_mul_eq hN) (ZMod N)) X).map
          (rootsOfUnityModuleInverseImageIso π N hNY).hom =
      (rootsOfUnityModuleInverseImageIso π N' hN'Y).hom ≫
        rootsOfUnityModulePowMap.{u, 0} X ℓ N N' hN := by
  apply (ArtinSchreier.etaleModuleForgetZModFullyFaithful X N').map_injective
  have hU := (etaleModuleUnderlyingAbelianInverseImageIso (ZMod N') π).hom.naturality
    (rootsOfUnityModulePowMap.{u, 0} Y ℓ N N' hN)
  have hK := etaleModuleUnderlyingAbelianInverseImageIso_restrictScalars
    (ZMod.castHom (dvd_of_mul_eq hN) (ZMod N)) π (rootsOfUnityModule.{u, 0} Y N)
  have hr := etaleModuleForgetAb_map_rootsOfUnityModuleInverseImageIso_hom π N hNY
  have hr' := etaleModuleForgetAb_map_rootsOfUnityModuleInverseImageIso_hom π N' hN'Y
  have hp := Purity.rootsOfUnityInverseImageComparison_comp_rootsOfUnityPowMap π ℓ N N' hN
  have hΦY : (etaleModuleUnderlyingAbelian Y (ZMod N')).map
      (rootsOfUnityModulePowMap.{u, 0} Y ℓ N N' hN) = rootsOfUnityPowMap.{u, 0} Y ℓ N N' hN := by
    apply Sheaf.hom_ext
    rfl
  have hΦX : (etaleModuleForgetAb.{u, 0} (ZMod N') X).map
      (rootsOfUnityModulePowMap.{u, 0} X ℓ N N' hN) = rootsOfUnityPowMap.{u, 0} X ℓ N N' hN := by
    apply Sheaf.hom_ext
    rfl
  have hp2 := (congrArg (fun t => (etaleAbelianInverseImage.{u, 0} π).map t ≫
    rootsOfUnityInverseImageComparison.{u, 0} π N) hΦY).trans
      (hp.trans (congrArg (rootsOfUnityInverseImageComparison.{u, 0} π N' ≫ ·) hΦX.symm))
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp]
  exact comp_comp_eq_of_conj _ _ _ _ _
    ((etaleModuleUnderlyingAbelianInverseImageIso (ZMod N') π).app (rootsOfUnityModule.{u, 0} Y N'))
    ((etaleModuleUnderlyingAbelianInverseImageIso (ZMod N') π).app
      ((etaleModuleRestrictScalars (ZMod.castHom (dvd_of_mul_eq hN) (ZMod N)) Y).obj
        (rootsOfUnityModule.{u, 0} Y N)))
    ((etaleModuleUnderlyingAbelianInverseImageIso (ZMod N) π).app (rootsOfUnityModule.{u, 0} Y N))
    _ _ _ hU hK hr hr' hp2

end Stacks.Kummer

end
