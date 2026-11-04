module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LaumonFourierLevelIsogenyCoreProof
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierTransformCoefficientExtension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.PadicIntegerRingExtensionLattice

/-!
# The level isogeny of Laumon's comparison over the integers of a finite extension of `E`

`Stacks.EtaleCohomology.LaumonFourierLevelIsogenyInput` asks, for every finite extension `E''` of
`E` inside `Ē` with integers `O''` and all `O''`-models `σ_O` of `σ' = σ₁ ⊗ L_{ψ'}(a xⁿ)` and `τ_O`
of `τ`, for an `ℓᶜ`-isogeny, `c` independent of the level `N'`, between
`jV'⁻¹ H¹(Φ(ℱ_{σ_O mod ℓ^{N'+1}}))` and `ℱ_{τ_O mod ℓ^{N'+1}}` over `Λ'' = O''/ℓ^{N'+1}`. This
file deduces it from its core case `E'' = E`
(`Stacks.EtaleCohomology.LaumonFourierLevelIsogenyCoreInput`), step R3 of the proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH):

1. choose `O_E`-models `σ_E`, `τ_E` (`Stacks.EtaleCohomology.exists_padicIntegerRing_model`) and
   take the core isogeny over `Λ = O_E/ℓ^{N'+1}`, exponent `c_E`;
2. `O''` is free of finite rank over `O_E`
   (`Stacks.EtaleCohomology.free_padicIntegerRing_extension`); an `O_E`-basis of `O''` gives a
   basis of `Λ''` over `Λ` with coordinates
   (`Stacks.EtaleCohomology.exists_quotient_coordinates`), and the core isogeny extends to an
   `ℓ^{c_E}`-isogeny over `Λ''` between the objects of `σ_E ⊗ O''` and `τ_E ⊗ O''` with the
   character `ψ'' = ρ ∘ ψ_E`
   (`Stacks.EtaleCohomology.exists_fourierTransform_isogeny_coefficientExtension`);
3. `σ_O` and `σ_E ⊗ O''` are models over `O''` of conjugates of `σ'`, hence commensurable with an
   exponent `a_σ` independent of the level
   (`Stacks.EtaleCohomology.exists_intertwiner_pow_of_conj`), likewise `τ_O` and `τ_E ⊗ O''` with
   `a_τ`, and the lattice changes give `ℓ^{a_σ}`- and `ℓ^{a_τ}`-isogenies
   (`Stacks.EtaleCohomology.exists_fourierTransform_isogeny_of_intertwiners`,
   `Stacks.EtaleCohomology.exists_lisseEtaleSheaf_isogeny_of_intertwiners`);
4. compose: `c = a_σ + c_E + a_τ`.

## Main results

* `Stacks.EtaleCohomology.exists_uniform_fourierTransform_isogeny_quotient_of_intertwiners`.
* `Stacks.EtaleCohomology.laumonFourierLevelIsogenyInput_of_core`.
* `Stacks.EtaleCohomology.laumonFourierLevelIsogenyInput`: the level isogeny holds.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale Matrix
  Polynomial Stacks.GroupCohomology

universe u

namespace Stacks.EtaleCohomology

/-- **Composition of isogenies**: if `f₀ ≫ g₀ = n₀` and `f₁ ≫ g₁ = n₁`, then
`(f₀ ≫ f₁) ≫ (g₁ ≫ g₀) = n₁ n₀`. -/
theorem comp_comp_eq_mul_nsmul_of_isogeny {C : Type*} [Category* C] [Preadditive C] {X Y Z : C}
    (f₀ : X ⟶ Y) (g₀ : Y ⟶ X) (f₁ : Y ⟶ Z) (g₁ : Z ⟶ Y) {n₀ n₁ : ℕ} (h₀ : f₀ ≫ g₀ = n₀ • 𝟙 X)
    (h₁ : f₁ ≫ g₁ = n₁ • 𝟙 Y) : (f₀ ≫ f₁) ≫ (g₁ ≫ g₀) = (n₁ * n₀) • 𝟙 X := by
  rw [Category.assoc, ← Category.assoc f₁, h₁, Preadditive.nsmul_comp, Category.id_comp,
    Preadditive.comp_nsmul, h₀, smul_smul]

section Level

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable (k' : Type u) [Field k'] [Fintype k'] (B : BigEtaleSite.{u})
  (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
  (hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k'))))
  (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
  (V' : B.Scheme) [ConnectedSpace V'.1]
  (jV' : V' ⟶ Stacks.ArtinSchreier.specObject (Polynomial k') B hL) (xV : GeometricPoint V'.1)

include hS in
/-- **One level of step R3**: a level isogeny over `Λ` for models `σ_E`, `τ_E`, a basis of `Λ''`
over `Λ` with its coordinates, and integral intertwiners between `ρ ∘ σ_E`, `ρ ∘ τ_E` and other
models `σ_O`, `τ_O` over `Λ''` give a level isogeny over `Λ''` for `σ_O`, `τ_O` and the character
`ρ ∘ ψ`, with exponent the product of the three. -/
theorem exists_fourierTransform_isogeny_of_coefficientExtension_of_intertwiners {Λ Λ'' : Type}
    [CommRing Λ] [CommRing Λ''] [Finite Λ] [Finite Λ''] (ρ : Λ →+* Λ'') {e : ℕ}
    (β : Fin e → Λ'') (π : Fin e → Λ'' →+ Λ) (h₁ : ∀ i (c : Λ) (x : Λ''), π i (ρ c * x) = c * π i x)
    (h₂ : ∀ i j, π j (β i) = if i = j then 1 else 0) (h₃ : ∀ x : Λ'', ∑ i, ρ (π i x) * β i = x)
    (ψ : AddChar k' Λ) (hψ : ∑ x, ψ x = 0)
    (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k')).obj
      (Stacks.ArtinSchreier.cover k' (Polynomial k') Polynomial.X))
    (j : CompactificationOf (Over.mk (Stacks.ArtinSchreier.affineLineStructureMap k')))
    {m mτ : ℕ}
    {σ : EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')) →*
      GL (Fin m) Λ}
    (hσ : IsOpen (σ.ker : Set (EtaleFundamentalGroup (Spec (.of (Polynomial k')))
      (z.map (laumonFamilyPr₁ k')))))
    {σO : EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')) →*
      GL (Fin m) Λ''}
    (hσO : IsOpen (σO.ker : Set (EtaleFundamentalGroup (Spec (.of (Polynomial k')))
      (z.map (laumonFamilyPr₁ k')))))
    {τ : EtaleFundamentalGroup V'.1 xV →* GL (Fin mτ) Λ}
    (hτ : IsOpen (τ.ker : Set (EtaleFundamentalGroup V'.1 xV)))
    {τO : EtaleFundamentalGroup V'.1 xV →* GL (Fin mτ) Λ''}
    (hτO : IsOpen (τO.ker : Set (EtaleFundamentalGroup V'.1 xV)))
    (A A' : Matrix (Fin m) (Fin m) Λ'')
    (hA : ∀ g, A * (σO g).val = ((σ g).val.map ρ) * A)
    (hA' : ∀ g, A' * ((σ g).val.map ρ) = (σO g).val * A') {nσ : ℕ}
    (hAA' : A' * A = (nσ : Λ'') • 1) (hA'A : A * A' = (nσ : Λ'') • 1)
    (C C' : Matrix (Fin mτ) (Fin mτ) Λ'')
    (hC : ∀ g, C * ((τ g).val.map ρ) = (τO g).val * C)
    (hC' : ∀ g, C' * (τO g).val = ((τ g).val.map ρ) * C') {nτ : ℕ}
    (hCC' : C' * C = (nτ : Λ'') • 1) (hC'C : C * C' = (nτ : Λ'') • 1)
    (f : (etaleModuleInverseImage.{u, 0} Λ (B.inclusion.map jV')).obj
        ((DerivedCategory.Plus.homologyFunctor _ 1).obj ((fourierTransform k' Λ ψ B p₀ j).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((lisseEtaleSheaf B (Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
              (z.map (laumonFamilyPr₁ k')) Λ).obj
                (matrixContinuousModule.{u + 1, u + 1} Λ σ hσ))))) ⟶
      (lisseEtaleSheaf B V' xV Λ).obj (matrixContinuousModule.{u + 1, u + 1} Λ τ hτ))
    (g : (lisseEtaleSheaf B V' xV Λ).obj (matrixContinuousModule.{u + 1, u + 1} Λ τ hτ) ⟶
      (etaleModuleInverseImage.{u, 0} Λ (B.inclusion.map jV')).obj
        ((DerivedCategory.Plus.homologyFunctor _ 1).obj ((fourierTransform k' Λ ψ B p₀ j).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((lisseEtaleSheaf B (Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
              (z.map (laumonFamilyPr₁ k')) Λ).obj
                (matrixContinuousModule.{u + 1, u + 1} Λ σ hσ))))))
    {nE : ℕ} (hfg : f ≫ g = nE • 𝟙 _) (hgf : g ≫ f = nE • 𝟙 _) :
    ∃ (ψ'' : AddChar k' Λ'') (_ : ∑ x, ψ'' x = 0)
      (f'' : (etaleModuleInverseImage.{u, 0} Λ'' (B.inclusion.map jV')).obj
        ((DerivedCategory.Plus.homologyFunctor _ 1).obj ((fourierTransform k' Λ'' ψ'' B p₀ j).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((lisseEtaleSheaf B (Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
              (z.map (laumonFamilyPr₁ k')) Λ'').obj
                (matrixContinuousModule.{u + 1, u + 1} Λ'' σO hσO))))) ⟶
        (lisseEtaleSheaf B V' xV Λ'').obj (matrixContinuousModule.{u + 1, u + 1} Λ'' τO hτO))
      (g'' : (lisseEtaleSheaf B V' xV Λ'').obj (matrixContinuousModule.{u + 1, u + 1} Λ'' τO hτO) ⟶
        (etaleModuleInverseImage.{u, 0} Λ'' (B.inclusion.map jV')).obj
          ((DerivedCategory.Plus.homologyFunctor _ 1).obj ((fourierTransform k' Λ'' ψ'' B p₀ j).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj
              ((lisseEtaleSheaf B (Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
                (z.map (laumonFamilyPr₁ k')) Λ'').obj
                  (matrixContinuousModule.{u + 1, u + 1} Λ'' σO hσO)))))),
      f'' ≫ g'' = (nτ * (nE * nσ)) • 𝟙 _ ∧ g'' ≫ f'' = (nσ * nE * nτ) • 𝟙 _ := by
  have hσ'' := isOpen_ker_generalLinearGroupMap_comp ρ σ hσ
  have hτ'' := isOpen_ker_generalLinearGroupMap_comp ρ τ hτ
  obtain ⟨f₁, g₁, hfg₁, hgf₁⟩ := exists_fourierTransform_isogeny_coefficientExtension k' B p₀ j
    hS hL z V' jV' xV ρ β π h₁ h₂ h₃ ψ σ hσ hσ'' τ hτ hτ'' f g hfg hgf
  obtain ⟨f₀, g₀, hfg₀, hgf₀⟩ := exists_fourierTransform_isogeny_of_intertwiners k' B p₀ j hL z V'
    jV' Λ'' (ρ.toMonoidHom.compAddChar ψ) hσO hσ'' A A' hA hA' hAA' hA'A
  obtain ⟨f₂, g₂, hfg₂, hgf₂⟩ := exists_lisseEtaleSheaf_isogeny_of_intertwiners B V' xV Λ'' hτ''
    hτO C C' hC hC' hCC' hC'C
  refine ⟨ρ.toMonoidHom.compAddChar ψ, ?_, (f₀ ≫ f₁) ≫ f₂, g₂ ≫ (g₁ ≫ g₀),
    comp_comp_eq_mul_nsmul_of_isogeny _ _ _ _
      (comp_comp_eq_mul_nsmul_of_isogeny _ _ _ _ hfg₀ hfg₁) hfg₂,
    comp_comp_eq_mul_nsmul_of_isogeny _ _ _ _ hgf₂
      (comp_comp_eq_mul_nsmul_of_isogeny _ _ _ _ hgf₁ hgf₀)⟩
  show ∑ x, ρ (ψ x) = 0
  rw [← map_sum, hψ, map_zero]

include hS in
/-- **One level of step R3 over quotient rings**: for `ι : R →+* S` and ideals `J ⊆ ι⁻¹(I)` with
finite quotients, a basis of `S/I` over `R/J` with its coordinates, a level isogeny over `R/J`
(exponent `n_E`) for `σ_E mod J`, `τ_E mod J`, and integral intertwiners over `S` between
`ι ∘ σ_E`, `ι ∘ τ_E` and `σ_O`, `τ_O` with products `n_σ`, `n_τ` give a level isogeny over `S/I`
for `σ_O mod I`, `τ_O mod I`, with exponent `n_τ n_E n_σ`. -/
theorem exists_fourierTransform_isogeny_quotient_of_intertwiners {R S : Type} [CommRing R]
    [CommRing S] (ι : R →+* S) (I : Ideal S) (J : Ideal R) [Finite (R ⧸ J)] [Finite (S ⧸ I)]
    (hJI : J ≤ I.comap ι) {e : ℕ} (β : Fin e → S ⧸ I) (π : Fin e → (S ⧸ I) →+ (R ⧸ J))
    (h₁ : ∀ i (c : R ⧸ J) (x : S ⧸ I), π i (Ideal.quotientMap I ι hJI c * x) = c * π i x)
    (h₂ : ∀ i j, π j (β i) = if i = j then 1 else 0)
    (h₃ : ∀ x : S ⧸ I, ∑ i, Ideal.quotientMap I ι hJI (π i x) * β i = x)
    (ψ : AddChar k' (R ⧸ J)) (hψ : ∑ x, ψ x = 0)
    (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k')).obj
      (Stacks.ArtinSchreier.cover k' (Polynomial k') Polynomial.X))
    (j : CompactificationOf (Over.mk (Stacks.ArtinSchreier.affineLineStructureMap k')))
    {m mτ : ℕ} {σE : EtaleFundamentalGroup (Spec (.of (Polynomial k')))
      (z.map (laumonFamilyPr₁ k')) →* GL (Fin m) R}
    (hσE : IsOpen (((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk J)).comp σE).ker :
      Set (EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')))))
    {σO : EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')) →*
      GL (Fin m) S}
    (hσO : IsOpen (((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I)).comp σO).ker :
      Set (EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')))))
    {τE : EtaleFundamentalGroup V'.1 xV →* GL (Fin mτ) R}
    (hτE : IsOpen (((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk J)).comp τE).ker :
      Set (EtaleFundamentalGroup V'.1 xV)))
    {τO : EtaleFundamentalGroup V'.1 xV →* GL (Fin mτ) S}
    (hτO : IsOpen (((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I)).comp τO).ker :
      Set (EtaleFundamentalGroup V'.1 xV)))
    (A A' : Matrix (Fin m) (Fin m) S) (hA : ∀ g, A * (σO g).val = (σE g).val.map ι * A)
    (hA' : ∀ g, A' * (σE g).val.map ι = (σO g).val * A') (nσ : ℕ)
    (hAA' : A' * A = (nσ : S) • 1) (hA'A : A * A' = (nσ : S) • 1)
    (C C' : Matrix (Fin mτ) (Fin mτ) S) (hC : ∀ g, C * (τO g).val = (τE g).val.map ι * C)
    (hC' : ∀ g, C' * (τE g).val.map ι = (τO g).val * C') (nτ : ℕ)
    (hCC' : C' * C = (nτ : S) • 1) (hC'C : C * C' = (nτ : S) • 1)
    (f : (etaleModuleInverseImage.{u, 0} (R ⧸ J) (B.inclusion.map jV')).obj
          ((DerivedCategory.Plus.homologyFunctor _ 1).obj
            ((fourierTransform k' (R ⧸ J) ψ B p₀ j).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj
              ((lisseEtaleSheaf B (Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
                (z.map (laumonFamilyPr₁ k')) (R ⧸ J)).obj
                  (matrixContinuousModule.{u + 1, u + 1} (R ⧸ J)
                    ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk J)).comp σE) hσE))))) ⟶
      (lisseEtaleSheaf B V' xV (R ⧸ J)).obj (matrixContinuousModule.{u + 1, u + 1} (R ⧸ J)
          ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk J)).comp τE) hτE))
    (g : (lisseEtaleSheaf B V' xV (R ⧸ J)).obj (matrixContinuousModule.{u + 1, u + 1} (R ⧸ J)
          ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk J)).comp τE) hτE) ⟶
      (etaleModuleInverseImage.{u, 0} (R ⧸ J) (B.inclusion.map jV')).obj
          ((DerivedCategory.Plus.homologyFunctor _ 1).obj
            ((fourierTransform k' (R ⧸ J) ψ B p₀ j).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj
              ((lisseEtaleSheaf B (Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
                (z.map (laumonFamilyPr₁ k')) (R ⧸ J)).obj
                  (matrixContinuousModule.{u + 1, u + 1} (R ⧸ J)
                    ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk J)).comp σE) hσE))))))
    {nE : ℕ} (hfg : f ≫ g = nE • 𝟙 _) (hgf : g ≫ f = nE • 𝟙 _) :
    ∃ (ψ'' : AddChar k' (S ⧸ I)) (_ : ∑ x, ψ'' x = 0)
      (f'' : (etaleModuleInverseImage.{u, 0} (S ⧸ I) (B.inclusion.map jV')).obj
          ((DerivedCategory.Plus.homologyFunctor _ 1).obj
            ((fourierTransform k' (S ⧸ I) ψ'' B p₀ j).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj
              ((lisseEtaleSheaf B (Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
                (z.map (laumonFamilyPr₁ k')) (S ⧸ I)).obj
                  (matrixContinuousModule.{u + 1, u + 1} (S ⧸ I)
                    ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I)).comp σO) hσO))))) ⟶
        (lisseEtaleSheaf B V' xV (S ⧸ I)).obj (matrixContinuousModule.{u + 1, u + 1} (S ⧸ I)
          ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I)).comp τO) hτO))
      (g'' : (lisseEtaleSheaf B V' xV (S ⧸ I)).obj (matrixContinuousModule.{u + 1, u + 1} (S ⧸ I)
          ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I)).comp τO) hτO) ⟶
        (etaleModuleInverseImage.{u, 0} (S ⧸ I) (B.inclusion.map jV')).obj
          ((DerivedCategory.Plus.homologyFunctor _ 1).obj
            ((fourierTransform k' (S ⧸ I) ψ'' B p₀ j).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj
              ((lisseEtaleSheaf B (Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
                (z.map (laumonFamilyPr₁ k')) (S ⧸ I)).obj
                  (matrixContinuousModule.{u + 1, u + 1} (S ⧸ I)
                    ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I)).comp σO) hσO)))))),
      f'' ≫ g'' = (nτ * (nE * nσ)) • 𝟙 _ ∧ g'' ≫ f'' = (nσ * nE * nτ) • 𝟙 _ := by
  have hrσ := intertwiners_quotient ι I J hJI σE σO A A' hA hA' nσ hAA' hA'A
  obtain ⟨hσ₁, hσ₂, hσ₃, hσ₄⟩ := hrσ
  have hrτ := intertwiners_quotient ι I J hJI τE τO C C' hC hC' nτ hCC' hC'C
  obtain ⟨hτ₁, hτ₂, hτ₃, hτ₄⟩ := hrτ
  exact exists_fourierTransform_isogeny_of_coefficientExtension_of_intertwiners k' B hS hL z V' jV'
    xV (Ideal.quotientMap I ι hJI) β π h₁ h₂ h₃ ψ hψ p₀ j hσE hσO hτE hτO _ _ hσ₁ hσ₂ hσ₃ hσ₄ _ _
    hτ₂ hτ₁ hτ₄ hτ₃ f g hfg hgf

end Level

section Extension

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable (k' : Type u) [Field k'] [Fintype k'] (B : BigEtaleSite.{u})
  (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
  (hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k'))))
  (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
  (V' : B.Scheme) [ConnectedSpace V'.1]
  (jV' : V' ⟶ Stacks.ArtinSchreier.specObject (Polynomial k') B hL) (xV : GeometricPoint V'.1)

include hS in
/-- **Step R3 over towers of quotient rings**: for `ι : R →+* S`, ideals `J k ⊆ ι⁻¹(I k)` with
finite quotients and bases of `S/I k` over `R/J k` with coordinates, a level isogeny over the
`R/J (N'+1)`, uniform in `N'`, for models `σ_E`, `τ_E` over `R` gives one over the `S/I (N'+1)`
for models `σ_O`, `τ_O` over `S` commensurable with `ι ∘ σ_E`, `ι ∘ τ_E`. -/
theorem exists_uniform_fourierTransform_isogeny_quotient_of_intertwiners {R S : Type}
    [CommRing R] [CommRing S] (ι : R →+* S) (I : ℕ → Ideal S) (J : ℕ → Ideal R)
    [∀ k, Finite (R ⧸ J k)] [∀ k, Finite (S ⧸ I k)] (hJI : ∀ k, J k ≤ (I k).comap ι)
    (hcoord : ∀ k, ∃ (e : ℕ) (β : Fin e → S ⧸ I k) (π : Fin e → (S ⧸ I k) →+ (R ⧸ J k)),
      (∀ i c x, π i (Ideal.quotientMap (I k) ι (hJI k) c * x) = c * π i x) ∧
      (∀ i j, π j (β i) = if i = j then 1 else 0) ∧
      ∀ x, ∑ i, Ideal.quotientMap (I k) ι (hJI k) (π i x) * β i = x) (ℓ : ℕ)
    {m mτ : ℕ} {σE : EtaleFundamentalGroup (Spec (.of (Polynomial k')))
      (z.map (laumonFamilyPr₁ k')) →* GL (Fin m) R}
    (hσE : ∀ k, IsOpen (((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (J k))).comp σE).ker :
      Set (EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')))))
    {σO : EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')) →*
      GL (Fin m) S}
    (hσO : ∀ k, IsOpen (((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (I k))).comp σO).ker :
      Set (EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')))))
    {τE : EtaleFundamentalGroup V'.1 xV →* GL (Fin mτ) R}
    (hτE : ∀ k, IsOpen (((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (J k))).comp τE).ker :
      Set (EtaleFundamentalGroup V'.1 xV)))
    {τO : EtaleFundamentalGroup V'.1 xV →* GL (Fin mτ) S}
    (hτO : ∀ k, IsOpen (((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (I k))).comp τO).ker :
      Set (EtaleFundamentalGroup V'.1 xV)))
    (aσ : ℕ) (A A' : Matrix (Fin m) (Fin m) S) (hA : ∀ g, A * (σO g).val = (σE g).val.map ι * A)
    (hA' : ∀ g, A' * (σE g).val.map ι = (σO g).val * A')
    (hAA' : A' * A = ((ℓ : S) ^ aσ) • 1) (hA'A : A * A' = ((ℓ : S) ^ aσ) • 1)
    (aτ : ℕ) (C C' : Matrix (Fin mτ) (Fin mτ) S) (hC : ∀ g, C * (τO g).val = (τE g).val.map ι * C)
    (hC' : ∀ g, C' * (τE g).val.map ι = (τO g).val * C')
    (hCC' : C' * C = ((ℓ : S) ^ aτ) • 1) (hC'C : C * C' = ((ℓ : S) ^ aτ) • 1)
    (hcE : ∃ c : ℕ, ∀ N' : ℕ,
      ∃ (ψN : AddChar k' (R ⧸ J (N' + 1))) (_ : ∑ x, ψN x = 0)
        (p₀' : (finiteEtaleFiberFunctor (affineLineOrigin k')).obj
          (Stacks.ArtinSchreier.cover k' (Polynomial k') Polynomial.X))
        (j : CompactificationOf (Over.mk (Stacks.ArtinSchreier.affineLineStructureMap k')))
        (f : (etaleModuleInverseImage.{u, 0} (R ⧸ J (N' + 1)) (B.inclusion.map jV')).obj
            ((DerivedCategory.Plus.homologyFunctor _ 1).obj
              ((fourierTransform k' (R ⧸ J (N' + 1)) ψN B p₀' j).obj
              ((DerivedCategory.Plus.singleFunctor _ 0).obj
                ((lisseEtaleSheaf B (Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
                  (z.map (laumonFamilyPr₁ k')) (R ⧸ J (N' + 1))).obj
                    (matrixContinuousModule.{u + 1, u + 1} (R ⧸ J (N' + 1))
                      ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (J (N' + 1)))).comp σE)
                        (hσE (N' + 1))))))) ⟶
          (lisseEtaleSheaf B V' xV (R ⧸ J (N' + 1))).obj
            (matrixContinuousModule.{u + 1, u + 1} (R ⧸ J (N' + 1))
            ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (J (N' + 1)))).comp τE)
              (hτE (N' + 1))))
        (g : (lisseEtaleSheaf B V' xV (R ⧸ J (N' + 1))).obj
          (matrixContinuousModule.{u + 1, u + 1} (R ⧸ J (N' + 1))
            ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (J (N' + 1)))).comp τE)
              (hτE (N' + 1))) ⟶
          (etaleModuleInverseImage.{u, 0} (R ⧸ J (N' + 1)) (B.inclusion.map jV')).obj
            ((DerivedCategory.Plus.homologyFunctor _ 1).obj
              ((fourierTransform k' (R ⧸ J (N' + 1)) ψN B p₀' j).obj
              ((DerivedCategory.Plus.singleFunctor _ 0).obj
                ((lisseEtaleSheaf B (Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
                  (z.map (laumonFamilyPr₁ k')) (R ⧸ J (N' + 1))).obj
                    (matrixContinuousModule.{u + 1, u + 1} (R ⧸ J (N' + 1))
                      ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (J (N' + 1)))).comp σE)
                        (hσE (N' + 1)))))))),
        f ≫ g = ℓ ^ c • 𝟙 _ ∧ g ≫ f = ℓ ^ c • 𝟙 _) :
    ∃ c : ℕ, ∀ N' : ℕ,
      ∃ (ψN : AddChar k' (S ⧸ I (N' + 1))) (_ : ∑ x, ψN x = 0)
        (p₀' : (finiteEtaleFiberFunctor (affineLineOrigin k')).obj
          (Stacks.ArtinSchreier.cover k' (Polynomial k') Polynomial.X))
        (j : CompactificationOf (Over.mk (Stacks.ArtinSchreier.affineLineStructureMap k')))
        (f : (etaleModuleInverseImage.{u, 0} (S ⧸ I (N' + 1)) (B.inclusion.map jV')).obj
            ((DerivedCategory.Plus.homologyFunctor _ 1).obj
              ((fourierTransform k' (S ⧸ I (N' + 1)) ψN B p₀' j).obj
              ((DerivedCategory.Plus.singleFunctor _ 0).obj
                ((lisseEtaleSheaf B (Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
                  (z.map (laumonFamilyPr₁ k')) (S ⧸ I (N' + 1))).obj
                    (matrixContinuousModule.{u + 1, u + 1} (S ⧸ I (N' + 1))
                      ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (I (N' + 1)))).comp σO)
                        (hσO (N' + 1))))))) ⟶
          (lisseEtaleSheaf B V' xV (S ⧸ I (N' + 1))).obj
            (matrixContinuousModule.{u + 1, u + 1} (S ⧸ I (N' + 1))
            ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (I (N' + 1)))).comp τO)
              (hτO (N' + 1))))
        (g : (lisseEtaleSheaf B V' xV (S ⧸ I (N' + 1))).obj
          (matrixContinuousModule.{u + 1, u + 1} (S ⧸ I (N' + 1))
            ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (I (N' + 1)))).comp τO)
              (hτO (N' + 1))) ⟶
          (etaleModuleInverseImage.{u, 0} (S ⧸ I (N' + 1)) (B.inclusion.map jV')).obj
            ((DerivedCategory.Plus.homologyFunctor _ 1).obj
              ((fourierTransform k' (S ⧸ I (N' + 1)) ψN B p₀' j).obj
              ((DerivedCategory.Plus.singleFunctor _ 0).obj
                ((lisseEtaleSheaf B (Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
                  (z.map (laumonFamilyPr₁ k')) (S ⧸ I (N' + 1))).obj
                    (matrixContinuousModule.{u + 1, u + 1} (S ⧸ I (N' + 1))
                      ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (I (N' + 1)))).comp σO)
                        (hσO (N' + 1)))))))),
        f ≫ g = ℓ ^ c • 𝟙 _ ∧ g ≫ f = ℓ ^ c • 𝟙 _ := by
  obtain ⟨cE, hcE⟩ := hcE
  refine ⟨aσ + cE + aτ, fun N' => ?_⟩
  have hcN := hcE N'
  obtain ⟨ψE, hψE, p₀', j, fE, gE, hfgE, hgfE⟩ := hcN
  have hco := hcoord (N' + 1)
  obtain ⟨e, β, π, h₁, h₂, h₃⟩ := hco
  rw [← Nat.cast_pow] at hAA' hA'A hCC' hC'C
  have hlev := exists_fourierTransform_isogeny_quotient_of_intertwiners k' B hS hL z V' jV' xV ι
    (I (N' + 1)) (J (N' + 1)) (hJI (N' + 1)) β π h₁ h₂ h₃ ψE hψE p₀' j (hσE (N' + 1))
    (hσO (N' + 1)) (hτE (N' + 1)) (hτO (N' + 1)) A A' hA hA' _ hAA' hA'A C C' hC hC' _ hCC' hC'C
    fE gE hfgE hgfE
  obtain ⟨ψN, hψN, f, g, hfg, hgf⟩ := hlev
  have e₁ : ℓ ^ aτ * (ℓ ^ cE * ℓ ^ aσ) = ℓ ^ (aσ + cE + aτ) := by ring
  have e₂ : ℓ ^ aσ * ℓ ^ cE * ℓ ^ aτ = ℓ ^ (aσ + cE + aτ) := by ring
  rw [e₁] at hfg
  rw [e₂] at hgf
  exact ⟨ψN, hψN, p₀', j, f, g, hfg, hgf⟩

end Extension

section Assembly

attribute [local instance] padicIntAlgebraOfRat HasDerivedCategory.standard
  moduleCat_hasLimitsOfSize

/-- **The level isogeny over the integers of a finite extension of `E` from the core case over the
integers of `E`** (step R3 of the comparison in Laumon's proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)). -/
theorem laumonFourierLevelIsogenyInput_of_core (hcore : LaumonFourierLevelIsogenyCoreInput.{u}) :
    LaumonFourierLevelIsogenyInput.{u} := by
  intro B ℓ _ _ _ _ k' _ _ p _ _ hℓp E _ _ _ d b ψ' hψ' hζ n a hS hL z p₀ m σ₁ hσ₁ p₁ V' U' _ _ _
    jV' jU g' _ _ _ jg' hjV hpb xV r ρ hρ φ ψ₀ N hφψ hψφ mτ τ P Q hPQ hα hτ hQP E'' hE'' σO T₁
    hT₁ hσO τO T hT hτO
  have : FiniteDimensional E E'' := hE''
  have := compactSpace_etaleFundamentalGroup V'.1 xV
  have := compactSpace_etaleFundamentalGroup (Spec (.of (Polynomial k')))
    (z.map (laumonFamilyPr₁ k'))
  -- the models over `O_E` and the core isogeny
  have hσ' := continuous_restrictScalarsRep_characterTwist_artinSchreierCharacter k'
    (Polynomial k') (Polynomial.C a * Polynomial.X ^ n) b ψ' (z.map (laumonFamilyPr₁ k')) p₁ σ₁ hσ₁
  have hτc : Continuous (restrictScalarsRep b τ) := by
    refine continuous_restrictScalarsRep b τ ?_
    have : (fun g => restrictScalarsMatrix b (τ g).val) = fun g => Q *
        (Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := ℓ))
          (integralModel ρ hρ g)).val * P := funext fun g => by
      rw [hτ g, restrictScalarsRep_val]
    rw [this]
    exact (continuous_const.matrix_mul ((Units.continuous_val.comp
      (continuous_integralModel ρ hρ)).matrix_map continuous_subtype_val)).matrix_mul
        continuous_const
  let σ' := characterTwist σ₁ (Stacks.ArtinSchreier.artinSchreierCharacter k' (Polynomial k')
    (Polynomial.C a * Polynomial.X ^ n) ψ' (z.map (laumonFamilyPr₁ k')) p₁)
  have hmσ := exists_padicIntegerRing_model b E σ' hσ'
  obtain ⟨σE, T₁E, hT₁E, hσE⟩ := hmσ
  have hmτ := exists_padicIntegerRing_model b E τ hτc
  obtain ⟨τE, TE, hTE, hτE⟩ := hmτ
  have hmapE : ∀ {k : ℕ} (M : Matrix (Fin k) (Fin k) E), M.map (algebraMap E E) = M := fun M => by
    ext i j
    rfl
  have hcE₀ := hcore B ℓ k' p hℓp E b ψ' hψ' hζ n a hS hL z p₀ σ₁ hσ₁ p₁ V' U' jV' jU g'
    jg' hjV hpb xV ρ hρ φ ψ₀ N hφψ hψφ τ P Q hPQ hα hτ hQP σE T₁E
    (fun g => by rw [hT₁E g, hmapE]) hσE τE TE (fun g => by rw [hTE g, hmapE]) hτE
  obtain ⟨cE, hcE⟩ := hcE₀
  -- `O_E → O''` and the commensurability of the models
  let ι := padicIntegerRingMap ℓ E E''
  have hinj : Function.Injective (algebraMap (integralClosure ℤ_[ℓ] E'') E'') :=
    Subtype.val_injective
  have hden : ∀ x : E'', ∃ (c : ℕ) (y : integralClosure ℤ_[ℓ] E''),
      algebraMap (integralClosure ℤ_[ℓ] E'') E'' y = (ℓ : E'') ^ c * x :=
    exists_natCast_pow_mul_mem_padicIntegerRing ℓ
  have hιmap : ∀ {k : ℕ} (M : Matrix (Fin k) (Fin k) (integralClosure ℤ_[ℓ] E)),
      (M.map ι).map (algebraMap (integralClosure ℤ_[ℓ] E'') E'') =
        (M.map (algebraMap (integralClosure ℤ_[ℓ] E) E)).map (algebraMap E E'') := fun M => by
    ext i j
    rfl
  have hGLmap : ∀ {k : ℕ} (T' : GL (Fin k) E) (M : Matrix (Fin k) (Fin k) E),
      (((T'⁻¹ : GL (Fin k) E).val * M * T'.val)).map (algebraMap E E'') =
        ((Matrix.GeneralLinearGroup.map (algebraMap E E'') T')⁻¹ : GL (Fin k) E'').val *
          M.map (algebraMap E E'') *
            (Matrix.GeneralLinearGroup.map (algebraMap E E'') T').val := fun T' M => by
    rw [Matrix.map_mul, Matrix.map_mul, ← map_inv]
    rfl
  have hcσ := exists_intertwiner_pow_of_conj ℓ hinj hden
    (fun g => (σO g).val) (fun g => (σE g).val.map ι) (fun g => (σ' g).val.map (algebraMap E E''))
    T₁ (Matrix.GeneralLinearGroup.map (algebraMap E E'') T₁E) hT₁ fun g => by
      rw [hιmap, hT₁E g, hmapE, hGLmap]
  obtain ⟨aσ, Aσ, Aσ', hAσ, hAσ', hAσAσ', hAσ'Aσ⟩ := hcσ
  have hcτ := exists_intertwiner_pow_of_conj ℓ hinj hden
    (fun g => (τO g).val) (fun g => (τE g).val.map ι) (fun g => (τ g).val.map (algebraMap E E''))
    T (Matrix.GeneralLinearGroup.map (algebraMap E E'') TE) hT fun g => by
      rw [hιmap, hTE g, hmapE, hGLmap]
  obtain ⟨aτ, Aτ, Aτ', hAτ, hAτ', hAτAτ', hAτ'Aτ⟩ := hcτ
  exact exists_uniform_fourierTransform_isogeny_quotient_of_intertwiners k' B hS hL z V' jV' xV ι
    (fun k => Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E'') ^ k})
    (fun k => Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ k})
    (fun k => span_natCast_pow_le_comap_padicIntegerRingMap ℓ E E'' k)
    (fun k => exists_padicIntegerRing_quotient_coordinates ℓ E E'' k
      (span_natCast_pow_le_comap_padicIntegerRingMap ℓ E E'' k)) ℓ hσE hσO hτE hτO
    aσ Aσ Aσ' hAσ hAσ' hAσAσ' hAσ'Aσ aτ Aτ Aτ' hAτ hAτ' hAτAτ' hAτ'Aτ ⟨cE, hcE⟩

/-- **The level isogeny of Laumon's comparison holds** over the integers of every finite extension
`E''` of `E` (`Stacks.EtaleCohomology.LaumonFourierLevelIsogenyInput`): its core case over `O_E`
is `Stacks.EtaleCohomology.laumonFourierLevelIsogenyCoreInput`. -/
theorem laumonFourierLevelIsogenyInput : LaumonFourierLevelIsogenyInput.{u} :=
  laumonFourierLevelIsogenyInput_of_core laumonFourierLevelIsogenyCoreInput

end Assembly

end Stacks.EtaleCohomology

end
