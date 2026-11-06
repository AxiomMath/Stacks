module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.BaseChangeEtaleSite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteTypeContinuousModuleAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.GeometricallyUnibranch
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.PunctualEtaleModule

/-!
# The level dichotomy for a subsheaf of a lisse sheaf, from its monodromy

Let `X` be an integral normal scheme, `Λ` a finite commutative ring, `F'` a finite type locally
constant sheaf of `Λ`-modules on `X_étale` and `κ : K ↪ F'` a subsheaf which is locally constant
of finite type on a nonempty open `U` of `X`. Suppose that the monodromy module `M'` of `F'`
(Stacks Tag 0DV5 on Mathlib's small étale site) satisfies the *level dichotomy* at the exponents
`N, c₀` of an integer `ℓ`: every `π₁(X)`-stable submodule `W` of `M'` with `ℓ^N W ≠ 0` contains
`ℓ^{c₀} M'`. If `ℓ^N • κ ≠ 0`, then `ℓ^{c₀} F'|_U ⊆ K|_U`: there is `r : F'|_U ⟶ K|_U` with
`r ≫ κ|_U = ℓ^{c₀} • 𝟙`.

The proof reads `κ|_U` through the dictionary on `U` and its compatibility with restriction
(Tag 0DV6): the monodromy module of `K|_U` is a `π₁(U)`-stable submodule `W` of `M'`, which is
`π₁(X)`-stable since `π₁(U) ⟶ π₁(X)` is surjective (Tag 0BQI). If `ℓ^N W = 0` then `ℓ^N` kills
`K|_U`, so `ℓ^N • κ` vanishes on `U` and hence, `F'` being locally constant on the normal integral
`X`, vanishes. Otherwise the dichotomy gives `ℓ^{c₀} M' ⊆ W`, a factorization of `ℓ^{c₀}` through
`W` in the category of finite continuous `π₁(U)`-modules, which the dictionary carries back.

This is the monodromy input of step (d) of the single-level argument for the irreducibility of
the Fourier transform in Laumon's proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.ContinuousModuleLevelDichotomy`: the dichotomy for a module.
* `Stacks.EtaleCohomology.exists_comp_eq_nsmul_of_forall_submodule`: the module form.
* `Stacks.EtaleCohomology.exists_inverseImage_comp_eq_nsmul_of_monodromy`: the sheaf form.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.GroupCohomology

universe u v w

namespace Stacks.EtaleCohomology

section Module

variable {Λ : Type} [CommRing Λ] [Finite Λ] {G H : Type v} [Group G] [TopologicalSpace G]
  [Group H] [TopologicalSpace H]

/-- **The level dichotomy** of a finite continuous `Λ`-`H`-module `M` at the exponents `N, c₀` of
`ℓ`: every `H`-stable submodule `W` of `M` with `ℓ^N W ≠ 0` contains `ℓ^{c₀} M`. -/
def ContinuousModuleLevelDichotomy (M : FiniteTypeContinuousModule.{0, v, w} Λ H)
    (ℓ N c₀ : ℕ) : Prop :=
  ∀ W : Submodule Λ M.obj.obj.obj.V,
    (∀ h, ∀ x ∈ W, (M.obj.obj.obj.ρ h).asHom.hom x ∈ W) → (∃ x ∈ W, ℓ ^ N • x ≠ 0) →
      ∀ x, ℓ ^ c₀ • x ∈ W

/-- **The level dichotomy, read on a finite continuous module.** Let `φ : G ⟶ H` be a surjective
continuous homomorphism, `M` a finite continuous `Λ`-`H`-module satisfying the dichotomy at
`ℓ, N, c₀` (every `H`-stable submodule `W` with `ℓ^N W ≠ 0` contains `ℓ^{c₀} M`), and
`ι : M₁ ↪ M|_G` a monomorphism of finite continuous `Λ`-`G`-modules with `ℓ^N • 𝟙 M₁ ≠ 0`. Then
`ℓ^{c₀}` on `M|_G` factors through `ι`. -/
theorem exists_comp_eq_nsmul_of_forall_submodule (φ : G →ₜ* H) (hφ : Function.Surjective φ)
    {M₁ : FiniteTypeContinuousModule.{0, v, w} Λ G} {M : FiniteTypeContinuousModule.{0, v, w} Λ H}
    (ι : M₁ ⟶ (finiteTypeContinuousModuleRes Λ φ).obj M) [Mono ι] (ℓ N c₀ : ℕ)
    (hdich : ContinuousModuleLevelDichotomy M ℓ N c₀) (h : ℓ ^ N • 𝟙 M₁ ≠ 0) :
    ∃ r : (finiteTypeContinuousModuleRes Λ φ).obj M ⟶ M₁, r ≫ ι = ℓ ^ c₀ • 𝟙 _ := by
  have : IsNoetherianRing Λ := inferInstance
  let Uf : FiniteTypeContinuousModule.{0, v, w} Λ G ⥤ ModuleCat.{w} Λ :=
    finiteTypeContinuousModuleι Λ G ⋙ Stacks.Injectives.continuousModuleUnderlying Λ G
  have : (finiteTypeContinuousModuleι.{0, v, w} Λ G).Additive := ⟨fun {_ _ _ _} => rfl⟩
  have := additive_continuousModuleToModuleCat.{0, v, w} Λ G
  have := preservesFiniteLimits_finiteTypeContinuousModuleι.{0, v, w} Λ G
  have := preservesMonomorphisms_continuousModuleToModuleCat.{0, v, w} Λ G
  have : Uf.Additive := inferInstance
  have : Uf.PreservesMonomorphisms := inferInstance
  have hext : ∀ {A B : FiniteTypeContinuousModule.{0, v, w} Λ G} (f g : A ⟶ B),
      Uf.map f = Uf.map g → f = g := fun f g hfg => by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact Action.hom_ext _ _ hfg
  let ιl := (Uf.map ι).hom
  have hinj : Function.Injective ιl :=
    (ModuleCat.mono_iff_injective (Uf.map ι)).1 inferInstance
  have hcomm : ∀ g x,
      ιl ((M₁.obj.obj.obj.ρ g).asHom.hom x) = (M.obj.obj.obj.ρ (φ g)).asHom.hom (ιl x) :=
    fun g x => LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (ι.hom.hom.hom.comm g)) x
  let W := LinearMap.range ιl
  have hstab : ∀ h, ∀ x ∈ W, (M.obj.obj.obj.ρ h).asHom.hom x ∈ W := by
    rintro h _ ⟨y, rfl⟩
    obtain ⟨g, rfl⟩ := hφ h
    exact ⟨_, hcomm g y⟩
  have hW : ∃ x ∈ W, ℓ ^ N • x ≠ 0 := by
    by_contra! hne
    refine h (hext _ _ ?_)
    rw [Functor.map_nsmul, Functor.map_zero, CategoryTheory.Functor.map_id]
    ext x
    show ℓ ^ N • x = 0
    apply hinj
    rw [map_nsmul, map_zero]
    exact hne _ ⟨x, rfl⟩
  let r₀ : M.obj.obj.obj.V →ₗ[Λ] M₁.obj.obj.obj.V :=
    (LinearEquiv.ofInjective ιl hinj).symm.toLinearMap ∘ₗ
      LinearMap.codRestrict W (ℓ ^ c₀ • LinearMap.id) (hdich W hstab hW)
  have hr₀ : ∀ x, ιl (r₀ x) = ℓ ^ c₀ • x := fun x =>
    (LinearEquiv.ofInjective_apply ιl (h := hinj) _).symm.trans
      (congrArg Subtype.val ((LinearEquiv.ofInjective ιl hinj).apply_symm_apply _))
  have hequiv : ∀ g x,
      r₀ ((M.obj.obj.obj.ρ (φ g)).asHom.hom x) = (M₁.obj.obj.obj.ρ g).asHom.hom (r₀ x) := by
    intro g x
    apply hinj
    rw [hr₀, hcomm, hr₀, map_nsmul]
  let r : (finiteTypeContinuousModuleRes Λ φ).obj M ⟶ M₁ :=
    ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk
      ⟨ModuleCat.ofHom r₀, fun g => ModuleCat.hom_ext (LinearMap.ext fun x => hequiv g x)⟩))
  refine ⟨r, hext _ _ ?_⟩
  rw [Functor.map_comp, Functor.map_nsmul, CategoryTheory.Functor.map_id]
  ext x
  exact hr₀ x

end Module

section Sheaf

attribute [local instance] moduleCat_hasLimitsOfSize etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable {Λ : Type} [CommRing Λ] [Finite Λ]

/-- **The level dichotomy for a subsheaf of a lisse sheaf, from the monodromy.** Let `X` be an
integral normal scheme in a big étale site `B`, `F'` locally constant of finite type on
`X_étale`, `κ : K ↪ F'` with `K` locally constant of finite type on a nonempty open `U`, and
suppose that at every geometric point the monodromy module of `F'` satisfies the dichotomy at
`ℓ, N, c₀`: every `π₁`-stable submodule `W` with `ℓ^N W ≠ 0` contains `ℓ^{c₀}` times the
module. If `ℓ^N • κ ≠ 0`, then `ℓ^{c₀} • 𝟙` on `F'|_U` factors through `κ|_U`. -/
theorem exists_inverseImage_comp_eq_nsmul_of_monodromy (B : BigEtaleSite.{u}) {X : Scheme.{u}}
    (hXB : B.Contains X) [IsIntegral X] [IsNormal X] {K F' : EtaleModules.{u, 0} Λ X}
    (κ : K ⟶ F') [Mono κ]
    (hF' : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ X.smallEtaleTopology F')
    (U : X.Opens) [Nonempty U]
    (hK : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ U.toScheme.smallEtaleTopology
      ((etaleModuleInverseImage.{u, 0} Λ U.ι).obj K)) (ℓ N c₀ : ℕ)
    (hdich : ∀ x : GeometricPoint X, ContinuousModuleLevelDichotomy
      ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B (B.obj X hXB) x Λ).functor.obj
        ⟨F', hF'⟩) ℓ N c₀)
    (hκ : ℓ ^ N • κ ≠ 0) :
    ∃ r : (etaleModuleInverseImage.{u, 0} Λ U.ι).obj F' ⟶
        (etaleModuleInverseImage.{u, 0} Λ U.ι).obj K,
      r ≫ (etaleModuleInverseImage.{u, 0} Λ U.ι).map κ = ℓ ^ c₀ • 𝟙 _ := by
  let XB := B.obj X hXB
  let UB := B.obj U.toScheme (Scheme.size_lt_of_isOpenImmersion U.ι hXB)
  let f : UB ⟶ XB := ObjectProperty.homMk U.ι
  have : ConnectedSpace XB.1 := (inferInstance : ConnectedSpace X)
  have : ConnectedSpace UB.1 := (inferInstance : ConnectedSpace U.toScheme)
  let y : GeometricPoint U.toScheme := GeometricPoint.ofPoint U.toScheme (Classical.arbitrary U)
  let EU := finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B UB y Λ
  obtain ⟨α⟩ := nonempty_finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite_pullbackIso
    B f Λ y
  let L := etaleModuleInverseImage.{u, 0} Λ U.ι
  have : L.Additive := Functor.additive_of_preserves_binary_products _
  let e : L.obj F' ≅ (etaleSiteSheafPullbackModule B f Λ).obj F' :=
    ((etaleModuleInverseImageAdj.{u, 0} Λ U.ι).leftAdjointUniq
      (etaleSiteSheafPullbackModuleAdjunction B f Λ)).app F'
  let F'X : ObjectProperty.FullSubcategory
      (fun F => Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ XB.obj.smallEtaleTopology F) :=
    ⟨F', hF'⟩
  let F'U := (etaleSiteFiniteTypeLocallyConstantModuleSheafPullback B f Λ).obj F'X
  let KU : ObjectProperty.FullSubcategory
      (fun F => Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ UB.obj.smallEtaleTopology F) :=
    ⟨L.obj K, hK⟩
  let e' : L.obj F' ≅ F'U.obj := e ≪≫ eqToIso (Functor.congr_obj
    (etaleSiteFiniteTypeLocallyConstantModuleSheafPullback_comp_ι B f Λ) F'X).symm
  let κU : KU ⟶ F'U := ObjectProperty.homMk (L.map κ ≫ e'.hom)
  have : Mono κU := (ObjectProperty.ι _).mono_of_mono_map (mono_comp (L.map κ) e'.hom)
  let ι := EU.functor.map κU ≫ (α.app F'X).inv
  have : EU.functor.PreservesMonomorphisms :=
    Functor.preservesMonomorphisms_of_adjunction EU.symm.toAdjunction
  have := EU.toAdjunction.rightAdjoint_preservesLimits.{0, 0}
  have : EU.inverse.IsLeftAdjoint := ⟨_, ⟨EU.symm.toAdjunction⟩⟩
  have : EU.inverse.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  have : EU.symm.functor.Additive := additive_of_preservesBinaryProducts (F := EU.inverse)
  have : EU.functor.Additive := Equivalence.inverse_additive EU.symm
  by_cases h1 : ℓ ^ N • 𝟙 (EU.functor.obj KU) = 0
  · exfalso
    apply hκ
    have h2 : ℓ ^ N • 𝟙 KU = 0 := EU.functor.map_injective (by
      rwa [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero])
    have h4 : ℓ ^ N • 𝟙 (L.obj K) = 0 := congrArg (fun g => g.hom) h2
    have h3 : L.map (ℓ ^ N • κ) = 0 := by
      rw [Functor.map_nsmul, ← Category.id_comp (L.map κ), ← Preadditive.nsmul_comp, h4, zero_comp]
    have hI := lisseOpenUnitIsoInput.{u} U.ι Λ (ModuleCat.isFG Λ) F' hF'
    have : Mono ((etaleModuleInverseImageAdj.{u, 0} Λ U.ι).unit.app F') :=
      @IsIso.mono_of_iso _ _ _ _ _ hI
    rw [← cancel_mono ((etaleModuleInverseImageAdj.{u, 0} Λ U.ι).unit.app F'), zero_comp]
    refine ((etaleModuleInverseImageAdj.{u, 0} Λ U.ι).unit_naturality (ℓ ^ N • κ)).symm.trans ?_
    rw [show (etaleModuleInverseImage.{u, 0} Λ U.ι).map (ℓ ^ N • κ) = 0 from h3,
      Functor.map_zero, comp_zero]
  · obtain ⟨r₀, hr₀⟩ := exists_comp_eq_nsmul_of_forall_submodule (etaleFundamentalGroupMap f.hom y)
      (surjective_etaleFundamentalGroupMap_opensι_of_isGeometricallyUnibranch X
        isGeometricallyUnibranch_of_isNormal U y) ι ℓ N c₀ (hdich (y.map f.hom)) h1
    let s := (α.app F'X).inv ≫ r₀
    have hs : s ≫ EU.functor.map κU = ℓ ^ c₀ • 𝟙 _ := by
      have h5 : r₀ ≫ EU.functor.map κU = ℓ ^ c₀ • (α.app F'X).hom := by
        rw [← cancel_mono (α.app F'X).inv, Category.assoc]
        show r₀ ≫ ι = _
        rw [hr₀, Preadditive.nsmul_comp, Iso.hom_inv_id]
      show ((α.app F'X).inv ≫ r₀) ≫ _ = _
      rw [Category.assoc, h5, Preadditive.comp_nsmul, Iso.inv_hom_id]
    let rU : F'U ⟶ KU := EU.functor.preimage s
    have hrU : rU ≫ κU = ℓ ^ c₀ • 𝟙 _ := by
      apply EU.functor.map_injective
      rw [Functor.map_comp, Functor.map_preimage, hs, Functor.map_nsmul,
        CategoryTheory.Functor.map_id]
      rfl
    have hrU' : rU.hom ≫ L.map κ ≫ e'.hom = ℓ ^ c₀ • 𝟙 _ := congrArg (fun g => g.hom) hrU
    refine ⟨e'.hom ≫ rU.hom, ?_⟩
    rw [← cancel_mono e'.hom, Category.assoc, Category.assoc, hrU', Preadditive.comp_nsmul,
      Category.comp_id, Preadditive.nsmul_comp, Category.id_comp]

end Sheaf

end Stacks.EtaleCohomology

end
