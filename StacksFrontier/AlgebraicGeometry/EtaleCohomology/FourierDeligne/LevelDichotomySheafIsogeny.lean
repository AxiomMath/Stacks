module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LevelDichotomyInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LevelDichotomyBasePoint

/-!
# The level dichotomy through isogenies of locally constant sheaves

Let `M`, `M'` be finite continuous `Λ`-`H`-modules and `f : M ⟶ M'`, `g : M' ⟶ M` with
`g ∘ f = ℓᶜ` and `f ∘ g = ℓᶜ`. If every `H`-stable submodule of `M'` not killed by `ℓᴺ` contains
`ℓ^{c₀} M'`, then every `H`-stable submodule of `M` not killed by `ℓ^{N+c}` contains
`ℓ^{c₀+c} M` (`Stacks.EtaleCohomology.ContinuousModuleLevelDichotomy.of_isogeny`): the image of a
stable `W ⊆ M` under `f` is stable and not killed by `ℓᴺ`, so it contains `ℓ^{c₀} f(x)` and
`ℓ^{c₀+c} x = g(ℓ^{c₀} f(x)) ∈ g(f(W)) = ℓᶜ W`. Read through the equivalence of Tag 0DV5 (3),
this is the same statement for an `ℓᶜ`-isogeny of locally constant sheaves of finite type on a
connected scheme (`Stacks.EtaleCohomology.continuousModuleLevelDichotomy_of_isogeny`).

Conversely to `Stacks.EtaleCohomology.ContinuousModuleLevelDichotomy.res`, the dichotomy of the
restriction of `M` along any continuous homomorphism `G ⟶ H` gives it for `M`, the `H`-stable
submodules being `G`-stable (`Stacks.EtaleCohomology.ContinuousModuleLevelDichotomy.of_res`); for
an open immersion `U ⟶ X` of connected schemes this gives the dichotomy for `F` on `X` from that of
`F|_U` (`Stacks.EtaleCohomology.continuousModuleLevelDichotomy_of_inverseImage`).

These are steps M1 and M2 of the comparison of the levels of the Fourier family with the
dichotomy for the Fourier transform, in Laumon's proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.ContinuousModuleLevelDichotomy.of_isogeny`.
* `Stacks.EtaleCohomology.ContinuousModuleLevelDichotomy.of_res`.
* `Stacks.EtaleCohomology.continuousModuleLevelDichotomy_of_isogeny`.
* `Stacks.EtaleCohomology.continuousModuleLevelDichotomy_of_inverseImage`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.GroupCohomology

universe u v w

namespace Stacks.EtaleCohomology

section Module

variable {Λ : Type} [CommRing Λ] [Finite Λ] {G H : Type v} [Group G] [TopologicalSpace G]
  [Group H] [TopologicalSpace H]

omit [Finite Λ] in
/-- **The level dichotomy from that of a restriction**: an `H`-stable submodule is stable under
the image of `G`. -/
theorem ContinuousModuleLevelDichotomy.of_res (φ : G →ₜ* H)
    {M : FiniteTypeContinuousModule.{0, v, w} Λ H} {ℓ N c₀ : ℕ}
    (h : ContinuousModuleLevelDichotomy ((finiteTypeContinuousModuleRes Λ φ).obj M) ℓ N c₀) :
    ContinuousModuleLevelDichotomy M ℓ N c₀ :=
  fun W hW hne => h W (fun g x hx => hW (φ g) x hx) hne

/-- An additive functor preserves the relation `a ≫ b = n • 𝟙 X`. -/
private theorem functor_map_comp_eq_nsmul_id {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive] {X Y : C} {a : X ⟶ Y} {b : Y ⟶ X}
    {n : ℕ} (h : a ≫ b = n • 𝟙 X) : F.map a ≫ F.map b = n • 𝟙 (F.obj X) := by
  rw [← F.map_comp, h, F.map_nsmul, F.map_id]

omit [Finite Λ] in
/-- **The level dichotomy through an isogeny** of finite continuous modules: if `g ∘ f = ℓᶜ`,
`f ∘ g = ℓᶜ` and `M'` satisfies the dichotomy at `N, c₀`, then `M` satisfies it at
`N + c, c₀ + c`. -/
theorem ContinuousModuleLevelDichotomy.of_isogeny
    {M M' : FiniteTypeContinuousModule.{0, v, w} Λ H} (f : M ⟶ M') (g : M' ⟶ M) {ℓ c : ℕ}
    (hgf : f ≫ g = ℓ ^ c • 𝟙 M) (hfg : g ≫ f = ℓ ^ c • 𝟙 M') {N c₀ : ℕ}
    (h : ContinuousModuleLevelDichotomy M' ℓ N c₀) :
    ContinuousModuleLevelDichotomy M ℓ (N + c) (c₀ + c) := by
  let Uf : FiniteTypeContinuousModule.{0, v, w} Λ H ⥤ ModuleCat.{w} Λ :=
    finiteTypeContinuousModuleι Λ H ⋙ Stacks.Injectives.continuousModuleUnderlying Λ H
  have : (finiteTypeContinuousModuleι.{0, v, w} Λ H).Additive := ⟨fun {_ _ _ _} => rfl⟩
  have := additive_continuousModuleToModuleCat.{0, v, w} Λ H
  have : Uf.Additive := inferInstance
  let f' : M.obj.obj.obj.V →ₗ[Λ] M'.obj.obj.obj.V := (Uf.map f).hom
  let g' : M'.obj.obj.obj.V →ₗ[Λ] M.obj.obj.obj.V := (Uf.map g).hom
  have hgf' : ∀ x, g' (f' x) = ℓ ^ c • x := fun x =>
    LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (functor_map_comp_eq_nsmul_id Uf hgf)) x
  have hfg' : ∀ y, f' (g' y) = ℓ ^ c • y := fun y =>
    LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (functor_map_comp_eq_nsmul_id Uf hfg)) y
  have hf : ∀ h x, f' ((M.obj.obj.obj.ρ h).hom x) = (M'.obj.obj.obj.ρ h).hom (f' x) :=
    fun h x => LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (f.hom.hom.hom.comm h)) x
  intro W hW hne x
  have hmapW : ∀ h, ∀ y ∈ W.map f', (M'.obj.obj.obj.ρ h).hom y ∈ W.map f' := by
    rintro h _ ⟨x, hx, rfl⟩
    exact ⟨_, hW h x hx, hf h x⟩
  obtain ⟨x₀, hx₀, hx₀N⟩ := hne
  have hne' : ∃ y ∈ W.map f', ℓ ^ N • y ≠ 0 := by
    refine ⟨f' x₀, ⟨x₀, hx₀, rfl⟩, fun h0 => hx₀N ?_⟩
    rw [pow_add, mul_smul, ← hgf', ← map_nsmul, h0, map_zero]
  obtain ⟨s, hs, hsx⟩ := h _ hmapW hne' (f' x)
  rw [show ℓ ^ (c₀ + c) • x = ℓ ^ c • s by
    rw [pow_add, mul_smul, ← hgf', ← map_nsmul, ← hsx, hgf']]
  exact nsmul_mem hs _

end Module

section Sheaf

attribute [local instance] moduleCat_hasLimitsOfSize

variable {Λ : Type} [CommRing Λ] [Finite Λ]

/-- **The level dichotomy through an isogeny of locally constant sheaves**: for `A`, `A'`
locally constant of finite type on a connected `X` and `f : A ⟶ A'`, `g : A' ⟶ A` with
`g ∘ f = ℓᶜ` and `f ∘ g = ℓᶜ`, the dichotomy at `N, c₀` of the monodromy of `A'` at `x̄` gives the
dichotomy at `N + c, c₀ + c` of the monodromy of `A` at `x̄`. -/
theorem continuousModuleLevelDichotomy_of_isogeny (B : BigEtaleSite.{u}) (X : B.Scheme)
    [ConnectedSpace X.1] (x : GeometricPoint X.1) {A A' : EtaleModules.{u, 0} Λ X.1}
    (hA : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ X.1.smallEtaleTopology A)
    (hA' : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ X.1.smallEtaleTopology A')
    (f : A ⟶ A') (g : A' ⟶ A) {ℓ c : ℕ} (hgf : f ≫ g = ℓ ^ c • 𝟙 A)
    (hfg : g ≫ f = ℓ ^ c • 𝟙 A') {N c₀ : ℕ}
    (h : ContinuousModuleLevelDichotomy
      ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X x Λ).functor.obj ⟨A', hA'⟩)
      ℓ N c₀) :
    ContinuousModuleLevelDichotomy
      ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X x Λ).functor.obj ⟨A, hA⟩)
      ℓ (N + c) (c₀ + c) := by
  let E := finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X x Λ
  have : E.functor.Additive := (additive_of_equivalence_finiteTypeContinuousModule E).2
  let f₁ : (⟨A, hA⟩ : ObjectProperty.FullSubcategory
      (fun F => Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ X.1.smallEtaleTopology F)) ⟶
      ⟨A', hA'⟩ := ObjectProperty.homMk f
  let g₁ : (⟨A', hA'⟩ : ObjectProperty.FullSubcategory
      (fun F => Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ X.1.smallEtaleTopology F)) ⟶
      ⟨A, hA⟩ := ObjectProperty.homMk g
  have hgf₁ : f₁ ≫ g₁ = ℓ ^ c • 𝟙 _ :=
    (ObjectProperty.fullyFaithfulι _).map_injective (by
      rwa [Functor.map_comp, Functor.map_nsmul, CategoryTheory.Functor.map_id])
  have hfg₁ : g₁ ≫ f₁ = ℓ ^ c • 𝟙 _ :=
    (ObjectProperty.fullyFaithfulι _).map_injective (by
      rwa [Functor.map_comp, Functor.map_nsmul, CategoryTheory.Functor.map_id])
  refine ContinuousModuleLevelDichotomy.of_isogeny (E.functor.map f₁) (E.functor.map g₁) ?_ ?_ h
  · simpa using functor_map_comp_eq_nsmul_id E.functor hgf₁
  · simpa using functor_map_comp_eq_nsmul_id E.functor hfg₁

/-- **The level dichotomy of `F` from that of an inverse image**: for `f : Y ⟶ X` a morphism of
connected schemes of `B` and `F` locally constant of finite type on `X`, the dichotomy at `N, c₀`
of the monodromy of `f⁻¹ F` at `ȳ` gives the dichotomy of the monodromy of `F` at every geometric
point of `X`. -/
theorem continuousModuleLevelDichotomy_of_inverseImage (B : BigEtaleSite.{u}) {X Y : B.Scheme}
    [ConnectedSpace X.1] [ConnectedSpace Y.1] (f : Y ⟶ X) {F : EtaleModules.{u, 0} Λ X.1}
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ X.1.smallEtaleTopology F)
    (hF' : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ Y.1.smallEtaleTopology
      ((etaleModuleInverseImage.{u, 0} Λ f.hom).obj F)) {ℓ N c₀ : ℕ} (y : GeometricPoint Y.1)
    (hdich : ContinuousModuleLevelDichotomy
      ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B Y y Λ).functor.obj ⟨_, hF'⟩)
      ℓ N c₀) (x : GeometricPoint X.1) :
    ContinuousModuleLevelDichotomy
      ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X x Λ).functor.obj ⟨F, hF⟩)
      ℓ N c₀ := by
  obtain ⟨α⟩ := nonempty_finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite_pullbackIso
    B f Λ y
  let EY := finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B Y y Λ
  let FX : ObjectProperty.FullSubcategory
      (fun F => Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ X.obj.smallEtaleTopology F) :=
    ⟨F, hF⟩
  let e : (etaleModuleInverseImage.{u, 0} Λ f.hom).obj F ≅
      (etaleSiteSheafPullbackModule B f Λ).obj F :=
    ((etaleModuleInverseImageAdj.{u, 0} Λ f.hom).leftAdjointUniq
      (etaleSiteSheafPullbackModuleAdjunction B f Λ)).app F
  let e' : (etaleModuleInverseImage.{u, 0} Λ f.hom).obj F ≅
      ((etaleSiteFiniteTypeLocallyConstantModuleSheafPullback B f Λ).obj FX).obj :=
    e ≪≫ eqToIso (Functor.congr_obj
      (etaleSiteFiniteTypeLocallyConstantModuleSheafPullback_comp_ι B f Λ) FX).symm
  let e'' : (⟨_, hF'⟩ : ObjectProperty.FullSubcategory
      (fun F => Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ Y.obj.smallEtaleTopology F)) ≅
      (etaleSiteFiniteTypeLocallyConstantModuleSheafPullback B f Λ).obj FX :=
    (ObjectProperty.fullyFaithfulι _).preimageIso e'
  exact continuousModuleLevelDichotomy_of_basePoint B X (y.map f.hom) x hF
    ((hdich.of_iso (EY.functor.mapIso e'' ≪≫ (α.app FX).symm)).of_res _)

end Sheaf

end Stacks.EtaleCohomology

end
