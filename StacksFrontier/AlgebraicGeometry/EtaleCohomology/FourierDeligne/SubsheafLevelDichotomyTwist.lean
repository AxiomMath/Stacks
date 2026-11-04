module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LisseSubsheafMonodromyDichotomy
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.InvertibleTwistNonzero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierKernelInverse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LocallyConstantTensor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.InverseImageNoPunctualSections

/-!
# The level dichotomy for subsheaves, and its invariance under an invertible twist

Let `X` be a scheme and `Λ` a commutative ring. A sheaf `F` of `Λ`-modules on `X_étale`
satisfies the *subsheaf level dichotomy* at the exponents `N, c₀` of an integer `ℓ`
(`Stacks.EtaleCohomology.SubsheafLevelDichotomy`) if for every subsheaf `κ : K ↪ F` which is
locally constant of finite type on a nonempty open `U` and has `ℓ^N • κ ≠ 0`, the endomorphism
`ℓ^{c₀}` of `F|_U` factors through `κ|_U`: generically `ℓ^{c₀} F ⊆ K`.

For a locally constant `F` on an integral normal scheme this follows from the level dichotomy of
its monodromy modules (`Stacks.EtaleCohomology.subsheafLevelDichotomy_of_monodromy`). It is
invariant under isomorphism (`Stacks.EtaleCohomology.SubsheafLevelDichotomy.of_iso`) and under
the twist by an invertible étale-locally free sheaf `T` with étale-locally free inverse `T'`
(`Stacks.EtaleCohomology.SubsheafLevelDichotomy.tensor`): a subsheaf `κ : K ↪ M ⊗ T` gives the
subsheaf `K ⊗ T' ↪ M ⊗ T ⊗ T' ≅ M` (tensoring with `T'` is exact), which is still nonzero after
`ℓ^N` (tensoring with `T'` is faithful, `T' ⊗ T ≅ 𝟙`); a factorization `r₁` of `ℓ^{c₀}` through
it on `U` twists back to a factorization through `κ|_U`
(`Stacks.EtaleCohomology.exists_comp_eq_nsmul_of_whiskerRight`, a formal computation in a
monoidal preadditive category).

This is how the rank-one twist in `F' = H²(Φ(Φ F)) ≅ 𝔸f⁻¹ H²(R f_! Λ) ⊗ ν⁻¹ F` is removed from
the level dichotomy of step (d) of the single-level argument for the irreducibility of the
Fourier transform in Laumon's proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main definitions

* `Stacks.EtaleCohomology.SubsheafLevelDichotomy`.

## Main results

* `Stacks.EtaleCohomology.exists_comp_eq_nsmul_of_whiskerRight`.
* `Stacks.EtaleCohomology.subsheafLevelDichotomy_of_monodromy`.
* `Stacks.EtaleCohomology.SubsheafLevelDichotomy.of_iso`.
* `Stacks.EtaleCohomology.SubsheafLevelDichotomy.tensor`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

section Monoidal

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C]

/-- **Untwisting a factorization through a twisted morphism.** In a monoidal preadditive category,
let `κ : A ⟶ B`, `χ : B ⊗ S' ≅ M`, `e : S' ⊗ S ≅ 𝟙` with tensoring by `S` additive, and
`r₁ : M ⟶ A ⊗ S'` with `r₁ ≫ (κ ▷ S') ≫ χ = n • 𝟙`. Then `n • 𝟙 B` factors through `κ`:
`B ≅ B ⊗ S' ⊗ S ≅ M ⊗ S ⟶ A ⊗ S' ⊗ S ≅ A`. -/
theorem exists_comp_eq_nsmul_of_whiskerRight {A B M S S' : C}
    [(MonoidalCategory.tensorRight S).Additive]
    (κ : A ⟶ B) (χ : B ⊗ S' ≅ M) (e : S' ⊗ S ≅ 𝟙_ C) (r₁ : M ⟶ A ⊗ S') (n : ℕ)
    (h : r₁ ≫ κ ▷ S' ≫ χ.hom = n • 𝟙 M) :
    ∃ r : B ⟶ A, r ≫ κ = n • 𝟙 B := by
  refine ⟨(ρ_ B).inv ≫ B ◁ e.inv ≫ (α_ B S' S).inv ≫ χ.hom ▷ S ≫ r₁ ▷ S ≫
    (α_ A S' S).hom ≫ A ◁ e.hom ≫ (ρ_ A).hom, ?_⟩
  have h₁ : χ.hom ≫ r₁ ≫ κ ▷ S' = n • 𝟙 _ := by
    rw [← cancel_mono χ.hom, Category.assoc, Category.assoc, h, Preadditive.comp_nsmul,
      Category.comp_id, Preadditive.nsmul_comp, Category.id_comp]
  have h₂ : χ.hom ▷ S ≫ r₁ ▷ S ≫ (κ ▷ S') ▷ S = n • 𝟙 _ := by
    rw [← comp_whiskerRight, ← comp_whiskerRight, h₁]
    show (MonoidalCategory.tensorRight S).map (n • 𝟙 _) = _
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
    rfl
  have key : (α_ A S' S).hom ≫ A ◁ e.hom ≫ (ρ_ A).hom ≫ κ =
      (κ ▷ S') ▷ S ≫ (α_ B S' S).hom ≫ B ◁ e.hom ≫ (ρ_ B).hom := by
    rw [← rightUnitor_naturality, whisker_exchange_assoc, ← associator_naturality_left_assoc]
  calc _ = (ρ_ B).inv ≫ B ◁ e.inv ≫ (α_ B S' S).inv ≫ χ.hom ▷ S ≫ r₁ ▷ S ≫
        ((α_ A S' S).hom ≫ A ◁ e.hom ≫ (ρ_ A).hom ≫ κ) := by
          simp only [Category.assoc]
    _ = (ρ_ B).inv ≫ B ◁ e.inv ≫ (α_ B S' S).inv ≫ (χ.hom ▷ S ≫ r₁ ▷ S ≫ (κ ▷ S') ▷ S) ≫
        (α_ B S' S).hom ≫ B ◁ e.hom ≫ (ρ_ B).hom := by
          rw [key]
          simp only [Category.assoc]
    _ = n • 𝟙 B := by
          rw [h₂]
          simp

end Monoidal

section Sheaf

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  etaleModuleInverseImageSheafPullbackMonoidal hasSheafify_etaleModules_fourierKernel
  moduleCat_hasLimitsOfSize etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable {Λ : Type} [CommRing Λ]

/-- **The subsheaf level dichotomy** of a sheaf `F` of `Λ`-modules at the exponents `N, c₀` of
`ℓ`: for every subsheaf `κ : K ↪ F` which is locally constant of finite type on a nonempty open
`U` and is not killed by `ℓ^N`, the endomorphism `ℓ^{c₀}` of `F|_U` factors through `κ|_U`. -/
def SubsheafLevelDichotomy {X : Scheme.{u}} (F : EtaleModules.{u, 0} Λ X) (ℓ N c₀ : ℕ) :
    Prop :=
  ∀ ⦃K : EtaleModules.{u, 0} Λ X⦄ (κ : K ⟶ F), Mono κ → ∀ (U : X.Opens), Nonempty U →
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ U.toScheme.smallEtaleTopology
      ((etaleModuleInverseImage.{u, 0} Λ U.ι).obj K) → ℓ ^ N • κ ≠ 0 →
    ∃ r : (etaleModuleInverseImage.{u, 0} Λ U.ι).obj F ⟶
        (etaleModuleInverseImage.{u, 0} Λ U.ι).obj K,
      r ≫ (etaleModuleInverseImage.{u, 0} Λ U.ι).map κ = ℓ ^ c₀ • 𝟙 _

/-- **The subsheaf level dichotomy from the monodromy**: on an integral normal scheme, a locally
constant sheaf of finite type whose monodromy modules satisfy the level dichotomy at every
geometric point satisfies the subsheaf level dichotomy. -/
theorem subsheafLevelDichotomy_of_monodromy [Finite Λ] (B : BigEtaleSite.{u}) {X : Scheme.{u}}
    (hXB : B.Contains X) [IsIntegral X] [IsNormal X] {F : EtaleModules.{u, 0} Λ X}
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ X.smallEtaleTopology F)
    (ℓ N c₀ : ℕ)
    (hdich : ∀ x : GeometricPoint X, ContinuousModuleLevelDichotomy
      ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B (B.obj X hXB) x Λ).functor.obj
        ⟨F, hF⟩) ℓ N c₀) :
    SubsheafLevelDichotomy F ℓ N c₀ := fun _ κ _ U _ hK hκ =>
  exists_inverseImage_comp_eq_nsmul_of_monodromy B hXB κ hF U hK ℓ N c₀ hdich hκ

/-- Composing with a monomorphism preserves a morphism not killed by a natural number. -/
private theorem nsmul_comp_ne_zero {X : Scheme.{u}} {Y Z W : EtaleModules.{u, 0} Λ X}
    (f : Y ⟶ W) (m : W ⟶ Z) [Mono m] {n : ℕ} (h : n • f ≠ 0) : n • (f ≫ m) ≠ 0 := by
  rw [← Preadditive.nsmul_comp]
  exact fun h0 => h ((cancel_mono m).1 (h0.trans zero_comp.symm))

/-- **The subsheaf level dichotomy is invariant under isomorphism.** -/
theorem SubsheafLevelDichotomy.of_iso {X : Scheme.{u}} {F F' : EtaleModules.{u, 0} Λ X}
    (e : F ≅ F') {ℓ N c₀ : ℕ} (h : SubsheafLevelDichotomy F ℓ N c₀) :
    SubsheafLevelDichotomy F' ℓ N c₀ := by
  intro K κ _ U hU hK hκ
  obtain ⟨r, hr⟩ := h (κ ≫ e.inv) inferInstance U hU hK (nsmul_comp_ne_zero _ _ hκ)
  let L := etaleModuleInverseImage.{u, 0} Λ U.ι
  refine ⟨L.map e.inv ≫ r, ?_⟩
  have h₁ : r ≫ L.map κ = ℓ ^ c₀ • L.map e.hom := by
    rw [← cancel_mono (L.map e.inv), Category.assoc, ← L.map_comp, hr, Preadditive.nsmul_comp,
      ← L.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id]
  rw [Category.assoc, h₁, Preadditive.comp_nsmul, ← L.map_comp, e.inv_hom_id,
    CategoryTheory.Functor.map_id]

/-- Twisting a sheaf which is locally constant of finite type on `U` by an étale-locally free
sheaf keeps it locally constant of finite type on `U`. -/
private theorem isFiniteTypeLocallyConstant_inverseImage_tensor {X : Scheme.{u}}
    {K T' : EtaleModules.{u, 0} Λ X} (hT' : IsLocallyFreeEtaleModule Λ T') (U : X.Opens)
    (hK : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ U.toScheme.smallEtaleTopology
      ((etaleModuleInverseImage.{u, 0} Λ U.ι).obj K)) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ U.toScheme.smallEtaleTopology
      ((etaleModuleInverseImage.{u, 0} Λ U.ι).obj (K ⊗ T')) := by
  have h₁ := isLocallyConstantWith_tensor Λ (ModuleCat.isFG Λ)
    (fun E => Module.Free Λ E ∧ Module.Finite Λ E) hK
    (isLocallyConstantWith_inverseImage Λ _ U.ι hT')
  have h₂ := isLocallyConstantWith_of_iso Λ _
    (Functor.Monoidal.μIso (etaleModuleInverseImage.{u, 0} Λ U.ι) K T') h₁
  intro V
  obtain ⟨I, W, f, hcov, htriv⟩ := h₂ V
  refine ⟨I, W, f, hcov, fun i => ?_⟩
  obtain ⟨E, ⟨E₁, E₂, hE₁, hE₂, rfl⟩, he⟩ := htriv i
  have : Module.Finite Λ E₁ := (ModuleCat.isFG_iff E₁).1 hE₁
  have : Module.Finite Λ E₂ := hE₂.2
  exact ⟨_, (ModuleCat.isFG_iff _).2
    (inferInstanceAs (Module.Finite Λ (TensorProduct Λ E₁ E₂))), he⟩

/-- **The subsheaf level dichotomy survives an invertible twist**: if `M` satisfies it and `T`,
`T'` are étale-locally free with `T ⊗ T' ≅ 𝟙` and `T' ⊗ T ≅ 𝟙`, then `M ⊗ T` satisfies it. -/
theorem SubsheafLevelDichotomy.tensor {X : Scheme.{u}} {M T T' : EtaleModules.{u, 0} Λ X}
    (hT : IsLocallyFreeEtaleModule Λ T) (hT' : IsLocallyFreeEtaleModule Λ T')
    (e : T ⊗ T' ≅ 𝟙_ (EtaleModules.{u, 0} Λ X)) (e' : T' ⊗ T ≅ 𝟙_ (EtaleModules.{u, 0} Λ X))
    {ℓ N c₀ : ℕ} (h : SubsheafLevelDichotomy M ℓ N c₀) :
    SubsheafLevelDichotomy (M ⊗ T) ℓ N c₀ := by
  intro K κ _ U hU hK hκ
  obtain ⟨hadd', hlim', -⟩ :=
    additive_preservesFiniteLimits_preservesFiniteColimits_tensorRight_of_isLocallyConstantWith
      T' hT'
  let φ : (M ⊗ T) ⊗ T' ≅ M := α_ M T T' ≪≫ whiskerLeftIso M e ≪≫ ρ_ M
  let κ₁ : K ⊗ T' ⟶ M := κ ▷ T' ≫ φ.hom
  have : Mono (κ ▷ T') := (MonoidalCategory.tensorRight T').map_mono κ
  have : Mono κ₁ := mono_comp _ _
  have hκ₁ : ℓ ^ N • κ₁ ≠ 0 := by
    refine nsmul_comp_ne_zero _ _ fun h0 => hκ ?_
    refine eq_zero_of_whiskerRight_eq_zero_of_tensor_iso Λ hT e' _ ?_
    exact (Functor.map_nsmul (MonoidalCategory.tensorRight T') (n := ℓ ^ N) (f := κ)).trans h0
  obtain ⟨r₁, hr₁⟩ :=
    h κ₁ inferInstance U hU (isFiniteTypeLocallyConstant_inverseImage_tensor hT' U hK) hκ₁
  let L := etaleModuleInverseImage.{u, 0} Λ U.ι
  have :=
    (additive_preservesFiniteLimits_preservesFiniteColimits_tensorRight_of_isLocallyConstantWith
      (L.obj T) (isLocallyConstantWith_inverseImage Λ _ U.ι hT)).1
  let eU : L.obj T' ⊗ L.obj T ≅ 𝟙_ _ :=
    Functor.Monoidal.μIso L T' T ≪≫ L.mapIso e' ≪≫ (Functor.Monoidal.εIso L).symm
  let χ : L.obj (M ⊗ T) ⊗ L.obj T' ≅ L.obj M := Functor.Monoidal.μIso L (M ⊗ T) T' ≪≫ L.mapIso φ
  refine exists_comp_eq_nsmul_of_whiskerRight (L.map κ) χ eU
    (r₁ ≫ (Functor.Monoidal.μIso L K T').inv) (ℓ ^ c₀) ?_
  have hμ : (Functor.Monoidal.μIso L K T').inv ≫ L.map κ ▷ L.obj T' ≫
      (Functor.Monoidal.μIso L (M ⊗ T) T').hom = L.map (κ ▷ T') :=
    (Iso.inv_comp_eq _).2 (Functor.LaxMonoidal.μ_natural_left L κ T')
  calc _ = r₁ ≫ ((Functor.Monoidal.μIso L K T').inv ≫ L.map κ ▷ L.obj T' ≫
        (Functor.Monoidal.μIso L (M ⊗ T) T').hom) ≫ L.map φ.hom := by
          simp only [χ, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
    _ = ℓ ^ c₀ • 𝟙 _ := by
          rwa [hμ, ← L.map_comp]

end Sheaf

end Stacks.EtaleCohomology

end
