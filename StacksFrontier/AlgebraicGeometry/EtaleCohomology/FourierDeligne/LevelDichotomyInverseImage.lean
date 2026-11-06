module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LisseSubsheafMonodromyDichotomy
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LisseExtVanishing

/-!
# The level dichotomy of monodromy modules along inverse images

Let `Λ` be a finite commutative ring. The level dichotomy of a finite continuous `Λ`-module
(`Stacks.EtaleCohomology.ContinuousModuleLevelDichotomy`: every stable submodule `W` with
`ℓ^N W ≠ 0` contains `ℓ^{c₀}` times the module) is invariant under isomorphism
(`Stacks.EtaleCohomology.ContinuousModuleLevelDichotomy.of_iso`) and under restriction along a
surjective continuous homomorphism, which has the same stable submodules
(`Stacks.EtaleCohomology.ContinuousModuleLevelDichotomy.res`).

Hence, for a morphism `f : Y ⟶ X` of connected schemes inducing surjections on étale fundamental
groups and a locally constant sheaf `F` of finite type on `X_étale` whose monodromy modules
(Tag 0DV5 on Mathlib's small étale site) satisfy the dichotomy at every geometric point, the
monodromy modules of `f⁻¹ F` satisfy it at every geometric point: by Tag 0DV6 the monodromy
module of `f⁻¹ F` at `y` is that of `F` at `f(y)` restricted along `π₁(Y, y) ⟶ π₁(X, f(y))`
(`Stacks.EtaleCohomology.continuousModuleLevelDichotomy_inverseImage`).

This carries the dichotomy from `F` to `ν⁻¹ F`, `ν = -1` on `𝔸¹_k`, in the level dichotomy of
step (d) of the single-level argument for the irreducibility of the Fourier transform in Laumon's
proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.ContinuousModuleLevelDichotomy.of_iso`.
* `Stacks.EtaleCohomology.ContinuousModuleLevelDichotomy.res`.
* `Stacks.EtaleCohomology.continuousModuleLevelDichotomy_inverseImage`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.GroupCohomology

universe u v w

namespace Stacks.EtaleCohomology

section Module

variable {Λ : Type} [CommRing Λ] [Finite Λ] {G H : Type v} [Group G] [TopologicalSpace G]
  [Group H] [TopologicalSpace H]

omit [Finite Λ] in
/-- **The level dichotomy is invariant under isomorphism** of finite continuous modules. -/
theorem ContinuousModuleLevelDichotomy.of_iso {M M' : FiniteTypeContinuousModule.{0, v, w} Λ H}
    (e : M ≅ M') {ℓ N c₀ : ℕ} (h : ContinuousModuleLevelDichotomy M ℓ N c₀) :
    ContinuousModuleLevelDichotomy M' ℓ N c₀ := by
  let f := e.hom.hom.hom.hom.hom.hom
  let g := e.inv.hom.hom.hom.hom.hom
  have hfg : ∀ x, f (g x) = x := fun x =>
    LinearMap.congr_fun (congrArg (fun φ : M' ⟶ M' => φ.hom.hom.hom.hom.hom) e.inv_hom_id) x
  have hcomm : ∀ h x, f ((M.obj.obj.obj.ρ h).asHom.hom x) = (M'.obj.obj.obj.ρ h).asHom.hom (f x) :=
    fun h x => LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (e.hom.hom.hom.hom.comm h)) x
  intro W' hW' hne y
  have hstab : ∀ h, ∀ x ∈ W'.comap f, (M.obj.obj.obj.ρ h).asHom.hom x ∈ W'.comap f := by
    intro h x hx
    rw [Submodule.mem_comap, hcomm]
    exact hW' h _ hx
  have hne' : ∃ x ∈ W'.comap f, ℓ ^ N • x ≠ 0 := by
    obtain ⟨x, hx, hx0⟩ := hne
    refine ⟨g x, by rwa [Submodule.mem_comap, hfg], fun h0 => hx0 ?_⟩
    calc ℓ ^ N • x = f (ℓ ^ N • g x) := by rw [map_nsmul, hfg]
      _ = 0 := by rw [h0, map_zero]
  have hy := h _ hstab hne' (g y)
  rwa [Submodule.mem_comap, map_nsmul, hfg] at hy

omit [Finite Λ] in
/-- **The level dichotomy survives restriction along a surjective homomorphism**: the stable
submodules are the same. -/
theorem ContinuousModuleLevelDichotomy.res (φ : G →ₜ* H) (hφ : Function.Surjective φ)
    {M : FiniteTypeContinuousModule.{0, v, w} Λ H} {ℓ N c₀ : ℕ}
    (h : ContinuousModuleLevelDichotomy M ℓ N c₀) :
    ContinuousModuleLevelDichotomy ((finiteTypeContinuousModuleRes Λ φ).obj M) ℓ N c₀ := by
  intro W hW hne
  refine h W (fun h' x hx => ?_) hne
  obtain ⟨g, rfl⟩ := hφ h'
  exact hW g x hx

end Module

section Sheaf

attribute [local instance] moduleCat_hasLimitsOfSize

variable {Λ : Type} [CommRing Λ] [Finite Λ]

/-- **The level dichotomy of the monodromy modules of an inverse image**: for `f : Y ⟶ X` a
morphism of connected schemes of `B` inducing surjections `π₁(Y, y) ⟶ π₁(X, f(y))`, and `F`
locally constant of finite type on `X_étale` whose monodromy modules satisfy the dichotomy at
every geometric point, so do those of `f⁻¹ F` (Tag 0DV6). -/
theorem continuousModuleLevelDichotomy_inverseImage (B : BigEtaleSite.{u}) {X Y : B.Scheme}
    [ConnectedSpace X.1] [ConnectedSpace Y.1] (f : Y ⟶ X)
    (hf : ∀ y : GeometricPoint Y.1, Function.Surjective (etaleFundamentalGroupMap f.hom y))
    {F : EtaleModules.{u, 0} Λ X.1}
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ X.1.smallEtaleTopology F)
    (hF' : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ Y.1.smallEtaleTopology
      ((etaleModuleInverseImage.{u, 0} Λ f.hom).obj F)) {ℓ N c₀ : ℕ}
    (hdich : ∀ x : GeometricPoint X.1, ContinuousModuleLevelDichotomy
      ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X x Λ).functor.obj ⟨F, hF⟩)
      ℓ N c₀) (y : GeometricPoint Y.1) :
    ContinuousModuleLevelDichotomy
      ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B Y y Λ).functor.obj
        ⟨_, hF'⟩) ℓ N c₀ := by
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
  exact ((hdich (y.map f.hom)).res _ (hf y)).of_iso (α.app FX ≪≫ EY.functor.mapIso e''.symm)

end Sheaf

end Stacks.EtaleCohomology

end
