module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LisseEtaleSheafScalarSplitting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LaumonFourierTransformComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LaumonFourierKernelTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.ArtinSchreierKernelProduct
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LaumonFourierKernelTwistModel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierInversionExact

/-!
# Level isogenies with `H¹Φ` after a finite free extension of the coefficients

Let `k'` be a finite field, `ρ : Λ →+* Λ''` a homomorphism of finite commutative rings with a
basis `β` of `Λ''` over `Λ` and its coordinate maps `π` (as in
`Stacks.EtaleCohomology.EtaleModuleScalarSplitting`), `ψ : k' → Λ` an additive character and
`ψ'' = ρ ∘ ψ`. Let `σ` be a representation of `π₁(𝔸¹_x)` on `Λ^m` and `τ` a representation of
`π₁(V')` on `Λ^{m_τ}`, for a scheme `V'` over `𝔸¹_t` through `jV'`, both with open kernels.

**Theorem** (`Stacks.EtaleCohomology.exists_fourierTransform_isogeny_coefficientExtension`). If
`jV'⁻¹ H¹(Φ_ψ(ℱ_σ))` and `ℱ_τ` are `n`-isogenous as sheaves of `Λ`-modules, then
`jV'⁻¹ H¹(Φ_{ψ''}(ℱ_{ρ ∘ σ}))` and `ℱ_{ρ ∘ τ}` are `n`-isogenous as sheaves of `Λ''`-modules.

Through `H¹(Φ_ψ(ℱ_σ)) ≅ R¹pr₂!(pr₁⁻¹ ℱ_σ ⊗ L_ψ(x t)) ≅ R¹pr₂!(ℱ_{pr₁^* σ ⊗ ψ(-χ_{x t})})`
(`Stacks.EtaleCohomology.nonempty_homology_fourierTransform_iso_laumonFamily` and
`Stacks.EtaleCohomology.nonempty_inverseImage_lisseEtaleSheaf_tensor_artinSchreierLevelSheaf_iso`,
over `Λ` and over `Λ''`, where the twist over `Λ''` is `ρ` of the twist over `Λ`), both sides
carry scalar splittings with the same matrices: the lisse sheaves by
`Stacks.EtaleCohomology.etaleModuleScalarSplitting_lisseEtaleSheaf`, carried through `R¹pr₂!` and
`jV'⁻¹`, which commute with restriction of scalars
(`Stacks.EtaleCohomology.lowerShriekHomologyRestrictScalarsIso`,
`Stacks.EtaleCohomology.etaleModuleInverseImageRestrictScalars`) and with the scalars; then
`Stacks.EtaleCohomology.exists_isogeny_of_etaleModuleScalarSplitting` applies.

**Theorem** (`Stacks.EtaleCohomology.exists_fourierTransform_isogeny_of_intertwiners`). Integral
intertwiners `A`, `A'` of `σ₁, σ₂` with `A' A = A A' = n` give an `n`-isogeny between
`jV'⁻¹ H¹(Φ_ψ(ℱ_{σ₁}))` and `jV'⁻¹ H¹(Φ_ψ(ℱ_{σ₂}))` (and
`Stacks.EtaleCohomology.exists_lisseEtaleSheaf_isogeny_of_intertwiners` for the lisse sheaves).

These are the sheaf steps of the extension of the level isogeny of Laumon's comparison from the
integers of `E` to the integers of a finite extension (step R3 of the proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main results

* `Stacks.EtaleCohomology.exists_fourierTransform_isogeny_coefficientExtension`.
* `Stacks.EtaleCohomology.exists_fourierTransform_isogeny_of_intertwiners`.
* `Stacks.EtaleCohomology.exists_lisseEtaleSheaf_isogeny_of_intertwiners`.

## Implementation notes

The Fourier transform and `R^q f_!` live in the standard model `HasDerivedCategory.standard`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.GroupCohomology Matrix

universe u

namespace Stacks.EtaleCohomology

section Kernel

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A representation followed by a ring homomorphism has open kernel if the representation
does. -/
theorem isOpen_ker_generalLinearGroupMap_comp {O O' : Type*} [CommRing O] [CommRing O']
    (ρ : O →+* O') {n : ℕ} (σ : G →* GL (Fin n) O) (hσ : IsOpen (σ.ker : Set G)) :
    IsOpen (((Matrix.GeneralLinearGroup.map ρ).comp σ).ker : Set G) := by
  refine Subgroup.isOpen_mono (fun g hg => ?_) hσ
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker.mp hg, map_one]

end Kernel

section Isogeny

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  Sheaf.monoidalCategory isMonoidal_W_etaleModules

variable (k' : Type u) [Field k'] [Fintype k'] (B : BigEtaleSite.{u})
  (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k')).obj
    (Stacks.ArtinSchreier.cover k' (Polynomial k') Polynomial.X))
  (j : CompactificationOf (Over.mk (Stacks.ArtinSchreier.affineLineStructureMap k')))
  (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
  (hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k'))))
  (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
  (V' : B.Scheme) [ConnectedSpace V'.1]
  (jV' : V' ⟶ Stacks.ArtinSchreier.specObject (Polynomial k') B hL) (xV : GeometricPoint V'.1)

omit [ConnectedSpace V'.1] in
/-- **Lattice change for `H¹Φ`**: integral intertwiners `A : σ₁ → σ₂` and `A' : σ₂ → σ₁` with
`A' A = A A' = n` give an `n`-isogeny between `jV'⁻¹ H¹(Φ_ψ(ℱ_{σ₁}))` and
`jV'⁻¹ H¹(Φ_ψ(ℱ_{σ₂}))`: the functor `ℱ ↦ jV'⁻¹ H¹(Φ_ψ(ℱ[0]))` is additive and `ℱ_{n • 1}` is
multiplication by `n`. -/
theorem exists_fourierTransform_isogeny_of_intertwiners (Λ : Type) [CommRing Λ] [Finite Λ]
    (ψ : AddChar k' Λ) {m : ℕ}
    {σ₁ σ₂ : EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')) →*
      GL (Fin m) Λ}
    (hσ₁ : IsOpen (σ₁.ker : Set (EtaleFundamentalGroup (Spec (.of (Polynomial k')))
      (z.map (laumonFamilyPr₁ k')))))
    (hσ₂ : IsOpen (σ₂.ker : Set (EtaleFundamentalGroup (Spec (.of (Polynomial k')))
      (z.map (laumonFamilyPr₁ k')))))
    (A A' : Matrix (Fin m) (Fin m) Λ) (hA : ∀ g, A * (σ₁ g).val = (σ₂ g).val * A)
    (hA' : ∀ g, A' * (σ₂ g).val = (σ₁ g).val * A') {n : ℕ} (hAA' : A' * A = (n : Λ) • 1)
    (hA'A : A * A' = (n : Λ) • 1) :
    ∃ (f : (etaleModuleInverseImage.{u, 0} Λ (B.inclusion.map jV')).obj
        ((DerivedCategory.Plus.homologyFunctor _ 1).obj ((fourierTransform k' Λ ψ B p₀ j).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((lisseEtaleSheaf B (Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
              (z.map (laumonFamilyPr₁ k')) Λ).obj
                (matrixContinuousModule.{u + 1, u + 1} Λ σ₁ hσ₁))))) ⟶
        (etaleModuleInverseImage.{u, 0} Λ (B.inclusion.map jV')).obj
          ((DerivedCategory.Plus.homologyFunctor _ 1).obj ((fourierTransform k' Λ ψ B p₀ j).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj
              ((lisseEtaleSheaf B (Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
                (z.map (laumonFamilyPr₁ k')) Λ).obj
                  (matrixContinuousModule.{u + 1, u + 1} Λ σ₂ hσ₂))))))
      (g : (etaleModuleInverseImage.{u, 0} Λ (B.inclusion.map jV')).obj
          ((DerivedCategory.Plus.homologyFunctor _ 1).obj ((fourierTransform k' Λ ψ B p₀ j).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj
              ((lisseEtaleSheaf B (Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
                (z.map (laumonFamilyPr₁ k')) Λ).obj
                  (matrixContinuousModule.{u + 1, u + 1} Λ σ₂ hσ₂))))) ⟶
        (etaleModuleInverseImage.{u, 0} Λ (B.inclusion.map jV')).obj
          ((DerivedCategory.Plus.homologyFunctor _ 1).obj ((fourierTransform k' Λ ψ B p₀ j).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj
              ((lisseEtaleSheaf B (Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
                (z.map (laumonFamilyPr₁ k')) Λ).obj
                  (matrixContinuousModule.{u + 1, u + 1} Λ σ₁ hσ₁)))))),
      f ≫ g = n • 𝟙 _ ∧ g ≫ f = n • 𝟙 _ := by
  let X₁ := Stacks.ArtinSchreier.specObject (Polynomial k') B hL
  have : ConnectedSpace X₁.1 := inferInstanceAs (ConnectedSpace (Spec (.of (Polynomial k'))))
  have := additive_lisseEtaleSheaf B X₁ (z.map (laumonFamilyPr₁ k')) Λ
  let F := lisseEtaleSheaf B X₁ (z.map (laumonFamilyPr₁ k')) Λ ⋙
    DerivedCategory.Plus.singleFunctor _ 0 ⋙ fourierTransform k' Λ ψ B p₀ j ⋙
      DerivedCategory.Plus.homologyFunctor _ 1 ⋙
        etaleModuleInverseImage.{u, 0} Λ (B.inclusion.map jV')
  let := fourierTransformCommShift k' Λ ψ B p₀ j
  have := isTriangulated_fourierTransform k' Λ ψ B p₀ j
  have : (fourierTransform k' Λ ψ B p₀ j).Additive := inferInstance
  have : F.Additive := by
    dsimp only [F]
    infer_instance
  have hn : ∀ {σ : EtaleFundamentalGroup (Spec (.of (Polynomial k')))
      (z.map (laumonFamilyPr₁ k')) →* GL (Fin m) Λ}
      (hσ : IsOpen (σ.ker : Set (EtaleFundamentalGroup (Spec (.of (Polynomial k')))
        (z.map (laumonFamilyPr₁ k')))))
      (h : ∀ g, ((n : Λ) • 1 : Matrix (Fin m) (Fin m) Λ) * (σ g).val =
        (σ g).val * ((n : Λ) • 1)),
      F.map (matrixContinuousModuleHom Λ hσ hσ ((n : Λ) • 1) h) = n • 𝟙 _ := by
    intro σ hσ h
    rw [matrixContinuousModuleHom_smul_one, Functor.comp_map,
      ← etaleModuleSMul_app_lisseEtaleSheaf, etaleModuleSMul_app_eq_smul_id,
      Nat.cast_smul_eq_nsmul]
    simp only [Functor.comp_map, Functor.map_nsmul, CategoryTheory.Functor.map_id]
    rfl
  refine ⟨F.map (matrixContinuousModuleHom Λ hσ₁ hσ₂ A hA),
    F.map (matrixContinuousModuleHom Λ hσ₂ hσ₁ A' hA'), ?_, ?_⟩
  · rw [← F.map_comp, matrixContinuousModuleHom_comp]
    simp only [hAA']
    exact hn hσ₁ _
  · rw [← F.map_comp, matrixContinuousModuleHom_comp]
    simp only [hA'A]
    exact hn hσ₂ _

/-- **Lattice change for lisse sheaves**: integral intertwiners `A : τ₁ → τ₂` and `A' : τ₂ → τ₁`
with `A' A = A A' = n` give an `n`-isogeny between `ℱ_{τ₁}` and `ℱ_{τ₂}`. -/
theorem exists_lisseEtaleSheaf_isogeny_of_intertwiners (Λ : Type) [CommRing Λ] [Finite Λ]
    {m : ℕ} {τ₁ τ₂ : EtaleFundamentalGroup V'.1 xV →* GL (Fin m) Λ}
    (hτ₁ : IsOpen (τ₁.ker : Set (EtaleFundamentalGroup V'.1 xV)))
    (hτ₂ : IsOpen (τ₂.ker : Set (EtaleFundamentalGroup V'.1 xV)))
    (A A' : Matrix (Fin m) (Fin m) Λ) (hA : ∀ g, A * (τ₁ g).val = (τ₂ g).val * A)
    (hA' : ∀ g, A' * (τ₂ g).val = (τ₁ g).val * A') {n : ℕ} (hAA' : A' * A = (n : Λ) • 1)
    (hA'A : A * A' = (n : Λ) • 1) :
    ∃ (f : (lisseEtaleSheaf B V' xV Λ).obj (matrixContinuousModule.{u + 1, u + 1} Λ τ₁ hτ₁) ⟶
        (lisseEtaleSheaf B V' xV Λ).obj (matrixContinuousModule.{u + 1, u + 1} Λ τ₂ hτ₂))
      (g : (lisseEtaleSheaf B V' xV Λ).obj (matrixContinuousModule.{u + 1, u + 1} Λ τ₂ hτ₂) ⟶
        (lisseEtaleSheaf B V' xV Λ).obj (matrixContinuousModule.{u + 1, u + 1} Λ τ₁ hτ₁)),
      f ≫ g = n • 𝟙 _ ∧ g ≫ f = n • 𝟙 _ := by
  let F := lisseEtaleSheaf B V' xV Λ
  have hn : ∀ {τ : EtaleFundamentalGroup V'.1 xV →* GL (Fin m) Λ}
      (hτ : IsOpen (τ.ker : Set (EtaleFundamentalGroup V'.1 xV)))
      (h : ∀ g, ((n : Λ) • 1 : Matrix (Fin m) (Fin m) Λ) * (τ g).val =
        (τ g).val * ((n : Λ) • 1)),
      F.map (matrixContinuousModuleHom Λ hτ hτ ((n : Λ) • 1) h) = n • 𝟙 _ := by
    intro τ hτ h
    rw [matrixContinuousModuleHom_smul_one, ← etaleModuleSMul_app_lisseEtaleSheaf,
      etaleModuleSMul_app_eq_smul_id, Nat.cast_smul_eq_nsmul]
  refine ⟨F.map (matrixContinuousModuleHom Λ hτ₁ hτ₂ A hA),
    F.map (matrixContinuousModuleHom Λ hτ₂ hτ₁ A' hA'), ?_, ?_⟩
  · rw [← F.map_comp, matrixContinuousModuleHom_comp]
    simp only [hAA']
    exact hn hτ₁ _
  · rw [← F.map_comp, matrixContinuousModuleHom_comp]
    simp only [hA'A]
    exact hn hτ₂ _

omit [ConnectedSpace V'.1] in
attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **`jV'⁻¹ H¹(Φ_ψ(ℱ_σ)) ≅ jV'⁻¹ R¹pr₂!(ℱ_{pr₁^* σ ⊗ ψ(-χ_{x t})})`**, from
`Stacks.EtaleCohomology.nonempty_homology_fourierTransform_iso_laumonFamily` and
`Stacks.EtaleCohomology.nonempty_inverseImage_lisseEtaleSheaf_tensor_artinSchreierLevelSheaf_iso`.
-/
theorem nonempty_inverseImage_homology_fourierTransform_lisse_iso (Λ : Type) [CommRing Λ]
    [Finite Λ] (ψ : AddChar k' Λ) {m : ℕ}
    (σ : EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')) →*
      GL (Fin m) Λ)
    (hσ : IsOpen (σ.ker : Set (EtaleFundamentalGroup (Spec (.of (Polynomial k')))
      (z.map (laumonFamilyPr₁ k')))))
    (jg : CompactificationOf (Over.mk (B.inclusion.map (laumonFamilyProjection k' B hS hL))))
    (pK : (finiteEtaleFiberFunctor z).obj (Stacks.ArtinSchreier.cover k'
      (Polynomial (Polynomial k')) (Polynomial.C Polynomial.X * Polynomial.X)))
    (hY : IsOpen ((characterTwist
      (σ.comp (etaleFundamentalGroupMap (laumonFamilyPr₁ k') z).toMonoidHom)
      (Stacks.ArtinSchreier.artinSchreierCharacter k' (Polynomial (Polynomial k'))
        (Polynomial.C Polynomial.X * Polynomial.X) ψ z pK)).ker :
          Set (EtaleFundamentalGroup (Spec (.of (Polynomial (Polynomial k')))) z))) :
    Nonempty ((etaleModuleInverseImage.{u, 0} Λ (B.inclusion.map jV')).obj
        ((DerivedCategory.Plus.homologyFunctor _ 1).obj ((fourierTransform k' Λ ψ B p₀ j).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((lisseEtaleSheaf B (Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
              (z.map (laumonFamilyPr₁ k')) Λ).obj
                (matrixContinuousModule.{u + 1, u + 1} Λ σ hσ))))) ≅
      (etaleModuleInverseImage.{u, 0} Λ (B.inclusion.map jV')).obj
        ((lowerShriekHomology Λ (B.inclusion.map (laumonFamilyProjection k' B hS hL)) jg 1).obj
          ((lisseEtaleSheaf B (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS)
            z Λ).obj (matrixContinuousModule.{u + 1, u + 1} Λ _ hY)))) := by
  obtain ⟨e₁⟩ := nonempty_homology_fourierTransform_iso_laumonFamily k' Λ ψ B p₀ j hS hL jg z pK
    ((lisseEtaleSheaf B (Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
      (z.map (laumonFamilyPr₁ k')) Λ).obj (matrixContinuousModule.{u + 1, u + 1} Λ σ hσ))
  obtain ⟨e₂⟩ := nonempty_inverseImage_lisseEtaleSheaf_tensor_artinSchreierLevelSheaf_iso k' Λ ψ
    B hS hL z pK σ hσ hY
  exact ⟨(etaleModuleInverseImage.{u, 0} Λ (B.inclusion.map jV')).mapIso
    (e₁ ≪≫ (lowerShriekHomology Λ (B.inclusion.map (laumonFamilyProjection k' B hS hL)) jg 1).mapIso
      e₂)⟩

omit [Fintype k'] [ConnectedSpace V'.1] in
attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **The scalar splitting of `jV'⁻¹ R¹pr₂!(ℱ_{ρ ∘ Y})` over `jV'⁻¹ R¹pr₂!(ℱ_Y)`**, from that of
the lisse sheaves (`Stacks.EtaleCohomology.etaleModuleScalarSplitting_lisseEtaleSheaf`), carried
by `R¹pr₂!` and `jV'⁻¹`. -/
theorem exists_etaleModuleScalarSplitting_inverseImage_lowerShriekHomology_lisse {Λ Λ'' : Type}
    [CommRing Λ] [CommRing Λ''] [Finite Λ] [Finite Λ''] (ρ : Λ →+* Λ'') {e : ℕ}
    (β : Fin e → Λ'') (π : Fin e → Λ'' →+ Λ) (h₁ : ∀ i (c : Λ) (x : Λ''), π i (ρ c * x) = c * π i x)
    (h₂ : ∀ i j, π j (β i) = if i = j then 1 else 0) (h₃ : ∀ x : Λ'', ∑ i, ρ (π i x) * β i = x)
    (jg : CompactificationOf (Over.mk (B.inclusion.map (laumonFamilyProjection k' B hS hL))))
    {m : ℕ} (Y : EtaleFundamentalGroup (Spec (.of (Polynomial (Polynomial k')))) z →* GL (Fin m) Λ)
    (hY : IsOpen (Y.ker : Set (EtaleFundamentalGroup (Spec (.of (Polynomial (Polynomial k')))) z)))
    (hY'' : IsOpen (((Matrix.GeneralLinearGroup.map ρ).comp Y).ker :
      Set (EtaleFundamentalGroup (Spec (.of (Polynomial (Polynomial k')))) z))) :
    ∃ π' ι', EtaleModuleScalarSplitting ρ (fun o k i => π k (o * β i))
      ((etaleModuleInverseImage.{u, 0} Λ'' (B.inclusion.map jV')).obj
        ((lowerShriekHomology Λ'' (B.inclusion.map (laumonFamilyProjection k' B hS hL)) jg 1).obj
          ((lisseEtaleSheaf B (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS)
            z Λ'').obj (matrixContinuousModule.{u + 1, u + 1} Λ''
              ((Matrix.GeneralLinearGroup.map ρ).comp Y) hY''))))
      ((etaleModuleInverseImage.{u, 0} Λ (B.inclusion.map jV')).obj
        ((lowerShriekHomology Λ (B.inclusion.map (laumonFamilyProjection k' B hS hL)) jg 1).obj
          ((lisseEtaleSheaf B (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS)
            z Λ).obj (matrixContinuousModule.{u + 1, u + 1} Λ Y hY)))) π' ι' := by
  let Xp := Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS
  have : ConnectedSpace Xp.1 :=
    inferInstanceAs (ConnectedSpace (Spec (.of (Polynomial (Polynomial k')))))
  let pr := B.inclusion.map (laumonFamilyProjection k' B hS hL)
  exact ⟨_, _, ((etaleModuleScalarSplitting_lisseEtaleSheaf B Xp z ρ β π h₁ h₂ h₃ hY hY'').map
    (lowerShriekHomology Λ'' pr jg 1) (lowerShriekHomology Λ pr jg 1)
    (lowerShriekHomologyRestrictScalarsIso ρ pr jg 1)
    (fun a G => lowerShriekHomology_map_etaleModuleSMul pr jg 1 a G)
    (fun a G => lowerShriekHomology_map_etaleModuleSMul pr jg 1 a G)).map
    (etaleModuleInverseImage.{u, 0} Λ'' (B.inclusion.map jV'))
    (etaleModuleInverseImage.{u, 0} Λ (B.inclusion.map jV'))
    (etaleModuleInverseImageRestrictScalars ρ (B.inclusion.map jV'))
    (fun a G => etaleModuleInverseImage_map_etaleModuleSMul _ a G)
    (fun a G => etaleModuleInverseImage_map_etaleModuleSMul _ a G)⟩

include hS in
attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **Level isogenies with `H¹Φ` after a finite free extension of the coefficients**: an
`n`-isogeny of sheaves of `Λ`-modules between `jV'⁻¹ H¹(Φ_ψ(ℱ_σ))` and `ℱ_τ` gives an
`n`-isogeny of sheaves of `Λ''`-modules between `jV'⁻¹ H¹(Φ_{ρ ∘ ψ}(ℱ_{ρ ∘ σ}))` and
`ℱ_{ρ ∘ τ}`, for `Λ''` free over `Λ` with basis `β` and coordinates `π`. -/
theorem exists_fourierTransform_isogeny_coefficientExtension {Λ Λ'' : Type} [CommRing Λ]
    [CommRing Λ''] [Finite Λ] [Finite Λ''] (ρ : Λ →+* Λ'') {e : ℕ} (β : Fin e → Λ'')
    (π : Fin e → Λ'' →+ Λ) (h₁ : ∀ i (c : Λ) (x : Λ''), π i (ρ c * x) = c * π i x)
    (h₂ : ∀ i j, π j (β i) = if i = j then 1 else 0) (h₃ : ∀ x : Λ'', ∑ i, ρ (π i x) * β i = x)
    (ψ : AddChar k' Λ) {m mτ : ℕ}
    (σ : EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')) →*
      GL (Fin m) Λ)
    (hσ : IsOpen (σ.ker : Set (EtaleFundamentalGroup (Spec (.of (Polynomial k')))
      (z.map (laumonFamilyPr₁ k')))))
    (hσ'' : IsOpen (((Matrix.GeneralLinearGroup.map ρ).comp σ).ker :
      Set (EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')))))
    (τ : EtaleFundamentalGroup V'.1 xV →* GL (Fin mτ) Λ)
    (hτ : IsOpen (τ.ker : Set (EtaleFundamentalGroup V'.1 xV)))
    (hτ'' : IsOpen (((Matrix.GeneralLinearGroup.map ρ).comp τ).ker :
      Set (EtaleFundamentalGroup V'.1 xV)))
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
    {n : ℕ} (hfg : f ≫ g = n • 𝟙 _) (hgf : g ≫ f = n • 𝟙 _) :
    ∃ (f'' : (etaleModuleInverseImage.{u, 0} Λ'' (B.inclusion.map jV')).obj
        ((DerivedCategory.Plus.homologyFunctor _ 1).obj
          ((fourierTransform k' Λ'' (ρ.toMonoidHom.compAddChar ψ) B p₀ j).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj
              ((lisseEtaleSheaf B (Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
                (z.map (laumonFamilyPr₁ k')) Λ'').obj
                  (matrixContinuousModule.{u + 1, u + 1} Λ''
                    ((Matrix.GeneralLinearGroup.map ρ).comp σ) hσ''))))) ⟶
        (lisseEtaleSheaf B V' xV Λ'').obj (matrixContinuousModule.{u + 1, u + 1} Λ''
          ((Matrix.GeneralLinearGroup.map ρ).comp τ) hτ''))
      (g'' : (lisseEtaleSheaf B V' xV Λ'').obj (matrixContinuousModule.{u + 1, u + 1} Λ''
          ((Matrix.GeneralLinearGroup.map ρ).comp τ) hτ'') ⟶
        (etaleModuleInverseImage.{u, 0} Λ'' (B.inclusion.map jV')).obj
          ((DerivedCategory.Plus.homologyFunctor _ 1).obj
            ((fourierTransform k' Λ'' (ρ.toMonoidHom.compAddChar ψ) B p₀ j).obj
              ((DerivedCategory.Plus.singleFunctor _ 0).obj
                ((lisseEtaleSheaf B (Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
                  (z.map (laumonFamilyPr₁ k')) Λ'').obj
                    (matrixContinuousModule.{u + 1, u + 1} Λ''
                      ((Matrix.GeneralLinearGroup.map ρ).comp σ) hσ'')))))),
      f'' ≫ g'' = n • 𝟙 _ ∧ g'' ≫ f'' = n • 𝟙 _ := by
  let Xp := Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS
  have : ConnectedSpace Xp.1 :=
    inferInstanceAs (ConnectedSpace (Spec (.of (Polynomial (Polynomial k')))))
  let pr := B.inclusion.map (laumonFamilyProjection k' B hS hL)
  have : CompactSpace (B.inclusion.obj (Stacks.ArtinSchreier.specObject (Polynomial k') B hL)) :=
    inferInstanceAs (CompactSpace (Spec (.of (Polynomial k'))))
  have : QuasiSeparatedSpace
      (B.inclusion.obj (Stacks.ArtinSchreier.specObject (Polynomial k') B hL)) :=
    inferInstanceAs (QuasiSeparatedSpace (Spec (.of (Polynomial k'))))
  obtain ⟨jg⟩ : Nonempty (CompactificationOf (Over.mk pr)) := IsCofiltered.nonempty
  obtain ⟨pK⟩ := Stacks.ArtinSchreier.nonempty_finiteEtaleFiber_cover k'
    (Polynomial.C Polynomial.X * Polynomial.X : Polynomial (Polynomial k')) z
  let φ := etaleFundamentalGroupMap (laumonFamilyPr₁ k') z
  let ψ'' := ρ.toMonoidHom.compAddChar ψ
  let χ := Stacks.ArtinSchreier.artinSchreierCharacter k' (Polynomial (Polynomial k'))
    (Polynomial.C Polynomial.X * Polynomial.X) ψ z pK
  let χ'' := Stacks.ArtinSchreier.artinSchreierCharacter k' (Polynomial (Polynomial k'))
    (Polynomial.C Polynomial.X * Polynomial.X) ψ'' z pK
  -- the twist over `Λ` and its image over `Λ''`
  let Y := characterTwist (σ.comp φ.toMonoidHom) χ
  have hY : IsOpen (Y.ker : Set (EtaleFundamentalGroup Xp.1 z)) :=
    isOpen_ker_characterTwist _ _ (hσ.preimage φ.continuous)
      (Stacks.ArtinSchreier.isOpen_ker_artinSchreierCharacter k' _ _ Λ ψ z pK)
  have hY'' : IsOpen (((Matrix.GeneralLinearGroup.map ρ).comp Y).ker :
      Set (EtaleFundamentalGroup Xp.1 z)) := isOpen_ker_generalLinearGroupMap_comp ρ Y hY
  let Y₂ := characterTwist (((Matrix.GeneralLinearGroup.map ρ).comp σ).comp φ.toMonoidHom) χ''
  have hY₂ : IsOpen (Y₂.ker : Set (EtaleFundamentalGroup Xp.1 z)) :=
    isOpen_ker_characterTwist _ _ (hσ''.preimage φ.continuous)
      (Stacks.ArtinSchreier.isOpen_ker_artinSchreierCharacter k' _ _ Λ'' ψ'' z pK)
  let mY := matrixContinuousModuleIsoOfEq Λ'' hY₂ hY'' fun g => by
    change Y₂ g = ((Matrix.GeneralLinearGroup.map ρ).comp
      (characterTwist (σ.comp φ.toMonoidHom) χ)) g
    rw [map_comp_characterTwist]
    rfl
  -- `H¹Φ` as `R¹pr₂!` of a lisse sheaf, over `Λ` and over `Λ''`
  obtain ⟨eΛ⟩ := nonempty_inverseImage_homology_fourierTransform_lisse_iso k' B p₀ j hS hL z V'
    jV' Λ ψ σ hσ jg pK hY
  obtain ⟨e''⟩ := nonempty_inverseImage_homology_fourierTransform_lisse_iso k' B p₀ j hS hL z V'
    jV' Λ'' ψ'' ((Matrix.GeneralLinearGroup.map ρ).comp σ) hσ'' jg pK hY₂
  let eΛ'' := e'' ≪≫ (etaleModuleInverseImage.{u, 0} Λ'' (B.inclusion.map jV')).mapIso
    ((lowerShriekHomology Λ'' pr jg 1).mapIso ((lisseEtaleSheaf B Xp z Λ'').mapIso mY))
  -- the scalar splittings
  obtain ⟨πA, ιA, hA⟩ := exists_etaleModuleScalarSplitting_inverseImage_lowerShriekHomology_lisse
    k' B hS hL z V' jV' ρ β π h₁ h₂ h₃ jg Y hY hY''
  obtain ⟨f₀, g₀, hfg₀, hgf₀⟩ := exists_isogeny_of_etaleModuleScalarSplitting hA
    (etaleModuleScalarSplitting_lisseEtaleSheaf B V' xV ρ β π h₁ h₂ h₃ hτ hτ'')
    (eΛ.inv ≫ f) (g ≫ eΛ.hom) (by
      rw [Category.assoc, ← Category.assoc f, hfg, Preadditive.nsmul_comp, Category.id_comp,
        Preadditive.comp_nsmul, Iso.inv_hom_id]) (by
      rw [Category.assoc, Iso.hom_inv_id_assoc, hgf])
  refine ⟨eΛ''.hom ≫ f₀, g₀ ≫ eΛ''.inv, ?_, ?_⟩
  · rw [Category.assoc, ← Category.assoc f₀, hfg₀, Preadditive.nsmul_comp, Category.id_comp,
      Preadditive.comp_nsmul, Iso.hom_inv_id]
  · rw [Category.assoc, Iso.inv_hom_id_assoc, hgf₀]

end Isogeny

end Stacks.EtaleCohomology

end
