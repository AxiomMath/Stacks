module
public import StacksCore.Algebra.Homology.SpectralSequence.Tower
public import StacksCore.FieldTheory.Separable
public import StacksFrontier.AlgebraicGeometry.AffineVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLimitsSets
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.IteratedRefinement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleEmbedding.LocallyConstantPushforward
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleEmbedding.ResidueFieldSeparability
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.LimitPresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExamplesSheaves.ConstantModuleSheafSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SeparablyClosedFieldSheaves
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.IntegralApproximation.AlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksFrontier.AlgebraicGeometry.Topologies.V.FppfFiniteDomination
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.Sites
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Normal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TrivialityAndGlobalSections
public import StacksFrontier.RingTheory.FinitePresentation.ModuleDescent
public import StacksFrontier.Topology.Dimension.DimensionFunctionObstruction

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleEmbedding.GenericPointLocallyConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleEmbedding.SeparablyClosedNormalCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleEmbedding.StageFactorization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompactSupportFiniteness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.FiniteCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ConstructiblePresentation
public import StacksFrontier.AlgebraicGeometry.PartTwoResidue.Complete
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LowerShriekAffineLine.RelativeCurveConstructibility
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleEmbedding.GenericEtale
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullbackCycles.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.IrreducibleCriterion

/-!
# A map out of a constructible sheaf which is injective at a given point

Let `X` be a quasi-compact and quasi-separated scheme, `Λ` a Noetherian ring and `ℱ` a
constructible sheaf of `Λ`-modules on `X_étale`. For every point `x` of `X` this file produces a
finite morphism of finite presentation `f : Y ⟶ X`, a finite `Λ`-module `M` and a map
`φ : ℱ ⟶ f_* M̲` whose kernel vanishes at a geometric point over `x`. This is the main step of the
proof of Stacks 09Z6.

The construction is that of the source. Let `π : Ỹ ⟶ X` be an integral morphism from an integral
normal scheme with separably closed function field `Ω` whose generic point lies over `x`
(`AlgebraicGeometry.exists_isIntegralHom_isNormal_isSepClosed_functionField`), and
`g : Spec Ω ⟶ Ỹ` the inclusion of the generic point. On `Spec Ω` every sheaf is constant, so
`g⁻¹ π⁻¹ ℱ` is the constant sheaf on its module of global sections `M`, which is finite because the
sheaf is constructible. Adjunction gives `ℱ ⟶ π_* g_* M̲`, and `g_* M̲ = M̲` on the normal scheme
`Ỹ` (Stacks 09Z5,
`Stacks.EtaleCohomology.isIso_locallyConstantToDirectImage_genericPointInclusion`).
Finally `π` is the limit of finite morphisms of finite presentation (Stacks 09YZ), and the map
`ℱ ⟶ π_* M̲` factors through one of them because `ℱ` is finitely presented
(`Stacks.EtaleCohomology.IntegralLimitPresentation.exists_comp_stageMap_eq`). Its kernel is killed
by `g⁻¹ π⁻¹`, through which the adjoint of the map is the identification of `g⁻¹ π⁻¹ ℱ` with
`M̲`.

## Main results

* `Stacks.EtaleCohomology.module_finite_etaleModuleGlobalSections_of_isSepClosed` — the global
  sections of a constructible sheaf on the spectrum of a separably closed field are finite.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

attribute [-instance] Stacks.EtaleCohomology.TorsionModules.hasSheafify_smallEtaleTopology_moduleCat
attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace Stacks.EtaleCohomology

attribute [local instance] SmallEtale.isRightAdjointPushforward_moduleCat
  SmallEtale.hasWeakSheafifyOver_moduleCat moduleCat_hasLimitsOfSize

variable (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]

/-- **A constructible sheaf on the spectrum of a separably closed field has finite global
sections.** Over an algebraic closure `Ω̄` of `Ω` the inverse image is constructible, hence has
finite global sections, and it is the constant sheaf on the same module, since every sheaf on
`Spec Ω` is constant. -/
theorem module_finite_etaleModuleGlobalSections_of_isSepClosed (Ω : Type u) [Field Ω]
    [IsSepClosed Ω] (G : EtaleModules.{u, u + 1} Λ (Spec (.of Ω)))
    (hG : IsConstructibleEtaleModule Λ G) :
    Module.Finite Λ ((etaleModuleGlobalSections.{u, u + 1} Λ (Spec (.of Ω))).obj G) := by
  let Ω' := AlgebraicClosure Ω
  let π : Spec (.of Ω') ⟶ Spec (.of Ω) := Spec.map (CommRingCat.ofHom (algebraMap Ω Ω'))
  have hfin := module_finite_etaleModuleGlobalSections_of_isConstructibleEtaleModule Λ Ω'
    ((etaleModuleInverseImage.{u, u + 1} Λ π).obj G)
    (isConstructibleEtaleModule_etaleModuleInverseImage Λ π G hG)
  have h₁ := isEquivalence_globalSections_of_isSepClosed Ω (ModuleCat.{u + 1} Λ)
  have h₂ := isEquivalence_globalSections_of_isSepClosed Ω' (ModuleCat.{u + 1} Λ)
  let adj₁ := constantSheafΓAdj (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let adj₂ := constantSheafΓAdj (Spec (.of Ω')).smallEtaleTopology (ModuleCat.{u + 1} Λ)
  have : (constantSheaf (Spec (.of Ω')).smallEtaleTopology (ModuleCat.{u + 1} Λ)).IsEquivalence :=
    adj₂.isEquivalence_left_of_isEquivalence_right
  let eG : (constantSheaf _ (ModuleCat.{u + 1} Λ)).obj
      ((etaleModuleGlobalSections.{u, u + 1} Λ (Spec (.of Ω))).obj G) ≅ G :=
    asIso (adj₁.counit.app G)
  let e : (etaleModuleGlobalSections.{u, u + 1} Λ (Spec (.of Ω'))).obj
      ((etaleModuleInverseImage.{u, u + 1} Λ π).obj G) ≅
      (etaleModuleGlobalSections.{u, u + 1} Λ (Spec (.of Ω))).obj G :=
    (etaleModuleGlobalSections.{u, u + 1} Λ (Spec (.of Ω'))).mapIso
      ((etaleModuleInverseImage.{u, u + 1} Λ π).mapIso eG.symm ≪≫
        (TorsionModules.etaleModuleInverseImageConstantIso.{u, u + 1} Λ π).app _) ≪≫
      (asIso (adj₂.unit.app _)).symm
  exact Module.Finite.equiv e.toLinearEquiv

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts

/-- **A finite presentation of a constructible sheaf by the sheaves `j_! Λ`.** On a Noetherian
scheme a constructible sheaf of `Λ`-modules is a quotient of a finite direct sum of the sheaves
`j_! Λ` at affine étale `X`-schemes, whose kernel is again such a quotient: the kernel of a map
between constructible sheaves is constructible (Stacks 03RZ). -/
theorem exists_finitePresentation_extensionByZeroConstant {X : Scheme.{u}} [IsNoetherian X]
    (F : EtaleModules.{u, u + 1} Λ X) (hF : IsConstructibleEtaleModule Λ F) :
    ∃ (n : ℕ) (W : Fin n → Scheme.{u}) (e : ∀ k, W k ⟶ X) (_ : ∀ k, Etale (e k))
      (_ : ∀ k, IsAffine (W k)) (p : (∐ fun k => extensionByZeroConstant Λ (e k)) ⟶ F) (_ : Epi p)
      (m : ℕ) (W' : Fin m → Scheme.{u}) (e' : ∀ l, W' l ⟶ X) (_ : ∀ l, Etale (e' l))
      (_ : ∀ l, IsAffine (W' l))
      (q : (∐ fun l => extensionByZeroConstant Λ (e' l)) ⟶ kernel p), Epi q := by
  obtain ⟨n, W, e, he, hW, p, hp⟩ :=
    exists_epi_sigma_etaleModuleExtensionByZero_of_isConstructibleEtaleModule Λ F hF
  have hP : IsConstructibleEtaleModule Λ (∐ fun k => extensionByZeroConstant Λ (e k)) :=
    isConstructibleEtaleModule_sigma Λ _ fun k =>
      isConstructibleEtaleModule_etaleModuleExtensionByZero_of_etale Λ (e k) _
        (isConstructibleEtaleModule_constantSheaf Λ (W k) (ModuleCat.of Λ Λ))
  obtain ⟨m, W', e', he', hW', q, hq⟩ :=
    exists_epi_sigma_etaleModuleExtensionByZero_of_isConstructibleEtaleModule Λ _
      ((IsConstructibleEtaleModule Λ).prop_kernel p hP hF)
  exact ⟨n, W, e, he, hW, p, hp, m, W', e', he', hW', q, hq⟩

omit [IsNoetherianRing Λ] in
/-- The double adjoint of a monomorphism `g⁻¹ f⁻¹ ℱ ⟶ ℋ` becomes a monomorphism after applying
`g⁻¹ f⁻¹`: composed with the counits it is the original monomorphism. -/
theorem mono_map_map_homEquiv_homEquiv {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    {F : EtaleModules.{u, u + 1} Λ X} {H : EtaleModules.{u, u + 1} Λ Z}
    (a : (etaleModuleInverseImage.{u, u + 1} Λ g).obj
      ((etaleModuleInverseImage.{u, u + 1} Λ f).obj F) ⟶ H) [Mono a] :
    Mono ((etaleModuleInverseImage.{u, u + 1} Λ g).map ((etaleModuleInverseImage.{u, u + 1} Λ f).map
      ((etaleModuleInverseImageAdj.{u, u + 1} Λ f).homEquiv _ _
        ((etaleModuleInverseImageAdj.{u, u + 1} Λ g).homEquiv _ _ a)))) := by
  set ψ := (etaleModuleInverseImageAdj.{u, u + 1} Λ g).homEquiv _ _ a
  set φ := (etaleModuleInverseImageAdj.{u, u + 1} Λ f).homEquiv _ _ ψ
  have h₁ : a = (etaleModuleInverseImage.{u, u + 1} Λ g).map ψ ≫
      (etaleModuleInverseImageAdj.{u, u + 1} Λ g).counit.app H := by
    simp [ψ, ← Adjunction.homEquiv_counit]
  have h₂ : ψ = (etaleModuleInverseImage.{u, u + 1} Λ f).map φ ≫
      (etaleModuleInverseImageAdj.{u, u + 1} Λ f).counit.app _ := by
    simp [φ, ← Adjunction.homEquiv_counit]
  rw [h₂, Functor.map_comp, Category.assoc] at h₁
  have : Mono ((etaleModuleInverseImage.{u, u + 1} Λ g).map
      ((etaleModuleInverseImage.{u, u + 1} Λ f).map φ) ≫
      (etaleModuleInverseImage.{u, u + 1} Λ g).map
        ((etaleModuleInverseImageAdj.{u, u + 1} Λ f).counit.app _) ≫
      (etaleModuleInverseImageAdj.{u, u + 1} Λ g).counit.app H) := by
    rw [← h₁]
    infer_instance
  exact mono_of_mono _ ((etaleModuleInverseImage.{u, u + 1} Λ g).map
        ((etaleModuleInverseImageAdj.{u, u + 1} Λ f).counit.app _) ≫
      (etaleModuleInverseImageAdj.{u, u + 1} Λ g).counit.app H)

attribute [local instance] AlgebraicGeometry.IntegralLimitPresentation.indexPreorder
  AlgebraicGeometry.IntegralLimitPresentation.indexNonempty
  AlgebraicGeometry.IntegralLimitPresentation.indexDirected

/-- If `c : Y ⟶ Z` is universally closed with integral image, `s : Z ⟶ X` is finite and the
residue field extension of `π = c ≫ s` at the generic point of `Y` is separable, then the image
of `Y` in `Z` is generically finite étale onto its image in `X`. -/
theorem isGenericallyFiniteEtaleOntoImage_imageι_comp {X Y Z : Scheme.{u}} [IsNoetherian X]
    [IsIntegral Y] (c : Y ⟶ Z) (s : Z ⟶ X) [IsFinite s] [UniversallyClosed c]
    [IsIntegral c.image] {π : Y ⟶ X} (hcs : c ≫ s = π)
    (hsep : letI := (π.residueFieldMap (genericPoint Y)).hom.toAlgebra
      Algebra.IsSeparable (X.residueField (π (genericPoint Y))) (Y.residueField (genericPoint Y))) :
    IsGenericallyFiniteEtaleOntoImage (c.imageι ≫ s) := by
  let f₁ := c.imageι ≫ s
  have htf : c.toImage ≫ f₁ = π := by
    rwa [← Category.assoc, Scheme.Hom.toImage_imageι]
  have : IsIntegral f₁.image := Stacks.Chow.isIntegral_image f₁
  have : Surjective c.toImage := Surjective.of_universallyClosed_of_isDominant c.toImage
  have : Surjective f₁.toImage := Surjective.of_universallyClosed_of_isDominant f₁.toImage
  have : IsFinite (f₁.toImage ≫ f₁.imageι) := by
    rw [Scheme.Hom.toImage_imageι]
    infer_instance
  have : IsFinite f₁.toImage := IsFinite.of_comp f₁.toImage f₁.imageι
  have : IsNoetherian f₁.image := isNoetherian_of_isClosedImmersion f₁.imageι
  have : LocallyOfFinitePresentation f₁.toImage :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance
  have h₁ := Scheme.Hom.isSeparable_residueFieldMap_of_comp_right (c.toImage ≫ f₁.toImage)
    f₁.imageι (p := π) (by rw [Category.assoc, Scheme.Hom.toImage_imageι, htf])
    (genericPoint Y) hsep
  have h₂ := Scheme.Hom.isSeparable_residueFieldMap_of_comp_left c.toImage f₁.toImage rfl
    (genericPoint Y) h₁
  have key : ∀ y : c.image, y = genericPoint c.image →
      (let := (f₁.toImage.residueFieldMap y).hom.toAlgebra;
        Algebra.IsSeparable (f₁.image.residueField (f₁.toImage y)) (c.image.residueField y)) →
      ∃ U : f₁.image.Opens, (U : Set f₁.image).Nonempty ∧ Etale (f₁.toImage ∣_ U) := by
    rintro y rfl h
    exact exists_nonempty_open_etale_restrict_of_isSeparable f₁.toImage
      (genericPoint_eq_of_surjective f₁.toImage) h
  obtain ⟨U, hU, hEt⟩ := key _ (genericPoint_eq_of_surjective c.toImage) h₂
  exact ⟨inferInstance, f₁.image, f₁.imageι, f₁.toImage, inferInstance, inferInstance,
    inferInstance, Scheme.Hom.toImage_imageι f₁, U, hU, inferInstance, hEt⟩

/-- An additive functor sends an identity killed by `n` to an identity killed by `n`. -/
private theorem nsmul_id_eq_zero_of_map {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] (T : C ⥤ D) [T.Additive] {A : C} {n : ℕ} (h : n • 𝟙 A = 0) :
    n • 𝟙 (T.obj A) = 0 := by
  rw [← T.map_id, ← Functor.map_nsmul, h, T.map_zero]

/-- **The map at the generic point.** Let `Y` be an integral normal scheme with separably closed
function field and `ℱ` a constructible sheaf of `Λ`-modules on `X_étale`. For any `π : Y ⟶ X`
there are a finite `Λ`-module `M` and a map `φ : ℱ ⟶ π_* 𝓛_Y(M)` such that the kernel of every
first factor of `φ` vanishes after inverse image to the generic point of `Y`. If `ℱ` is killed
by an integer `n`, so is `M`. -/
theorem exists_genericPoint_embedding {X Y : Scheme.{u}} [IsIntegral Y] [IsNormal Y]
    [IsSepClosed Y.functionField] (π : Y ⟶ X) (F : EtaleModules.{u, u + 1} Λ X)
    (hF : IsConstructibleEtaleModule Λ F) :
    ∃ (M : ModuleCat.{u + 1} Λ) (_ : Module.Finite Λ M)
      (φ : F ⟶ (etaleModuleDirectImage.{u, u + 1} Λ π).obj
        (smallEtaleLocallyConstantMapsModuleSheaf.{u, u + 1} Λ Y M)),
      (∀ (B : EtaleModules.{u, u + 1} Λ X) (ψ : F ⟶ B)
        (h : B ⟶ (etaleModuleDirectImage.{u, u + 1} Λ π).obj
          (smallEtaleLocallyConstantMapsModuleSheaf.{u, u + 1} Λ Y M)), ψ ≫ h = φ →
        IsZero ((etaleModuleInverseImage.{u, u + 1} Λ (genericPointInclusion Y ≫ π)).obj
          (kernel ψ))) ∧
      ∀ n : ℕ, n • 𝟙 F = 0 → ∀ m : M, n • m = 0 := by
  let Ω : Type u := Y.functionField
  let g : Spec (.of Ω) ⟶ Y := genericPointInclusion Y
  let T := etaleModuleInverseImage.{u, u + 1} Λ π ⋙ etaleModuleInverseImage.{u, u + 1} Λ g
  let G := T.obj F
  have hG : IsConstructibleEtaleModule Λ G :=
    isConstructibleEtaleModule_etaleModuleInverseImage Λ g _
      (isConstructibleEtaleModule_etaleModuleInverseImage Λ π F hF)
  let M := (etaleModuleGlobalSections.{u, u + 1} Λ (Spec (.of Ω))).obj G
  have hM : Module.Finite Λ M := module_finite_etaleModuleGlobalSections_of_isSepClosed Λ Ω G hG
  have := isEquivalence_globalSections_of_isSepClosed Ω (ModuleCat.{u + 1} Λ)
  let α : (constantSheaf _ (ModuleCat.{u + 1} Λ)).obj M ≅ G :=
    asIso ((constantSheafΓAdj (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.app G)
  let β : smallEtaleLocallyConstantMapsModuleSheaf.{u, u + 1} Λ (Spec (.of Ω)) M ≅ G :=
    (smallEtaleConstantSheafIsoLocallyConstantMapsModule.{u, u + 1} Λ _ M).symm ≪≫ α
  let ψ₀ := (etaleModuleInverseImageAdj.{u, u + 1} Λ g).homEquiv _ _ β.inv
  let φ₀ := (etaleModuleInverseImageAdj.{u, u + 1} Λ π).homEquiv _ _ ψ₀
  let θ := locallyConstantToDirectImage.{u, u + 1} Λ M g
  have : IsIso θ := isIso_locallyConstantToDirectImage_genericPointInclusion Λ M Y
  refine ⟨M, hM, φ₀ ≫ (etaleModuleDirectImage.{u, u + 1} Λ π).map (inv θ),
    fun B ψ h hψ => ?_, fun n hn m => ?_⟩
  · refine IsZero.of_iso ?_ ((etaleModuleInverseImageCompIso.{u, u + 1} Λ g π).app (kernel ψ))
    have hT : Mono (T.map φ₀) := mono_map_map_homEquiv_homEquiv Λ π g β.inv
    have hφ₀ : φ₀ = ψ ≫ h ≫ (etaleModuleDirectImage.{u, u + 1} Λ π).map θ := by
      rw [← Category.assoc, hψ, Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id,
        CategoryTheory.Functor.map_id, Category.comp_id]
    have hk : kernel.ι ψ ≫ φ₀ = 0 := by
      rw [hφ₀, kernel.condition_assoc, zero_comp]
    have hk' : T.map (kernel.ι ψ) = 0 := by
      rw [← cancel_mono (T.map φ₀), ← T.map_comp, hk, T.map_zero, zero_comp]
    exact IsZero.of_mono_eq_zero _ hk'
  · have hG : n • 𝟙 G = 0 := nsmul_id_eq_zero_of_map T hn
    have hM : n • 𝟙 M = 0 :=
      nsmul_id_eq_zero_of_map (etaleModuleGlobalSections.{u, u + 1} Λ (Spec (.of Ω))) hG
    simpa using congrArg (fun t => t.hom m) hM

/-- **The main step of Stacks 09Z6.** Let `X` be a Noetherian scheme, `Λ` a Noetherian ring and
`ℱ` a constructible sheaf of `Λ`-modules on `X_étale`. For every point `x` of `X` there are a
finite morphism of finite presentation `f : Y ⟶ X`, a finite `Λ`-module `M` and a map
`φ : ℱ ⟶ f_* 𝓛_Y(M)` into the direct image of the sheaf of locally constant `M`-valued maps (the
constant sheaf `M̲`) whose kernel vanishes after inverse image to a geometric point `s` over `x`.
If `ℱ` is killed by an integer `n`, so is `M`. Moreover `Y` is integral and maps onto an integral
closed subscheme `Z` of `X`, finite étale over a nonempty open of `Z`. -/
theorem exists_point_embedding {X : Scheme.{u}} [IsNoetherian X]
    (F : EtaleModules.{u, u + 1} Λ X) (hF : IsConstructibleEtaleModule Λ F) (x : X) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X) (_ : IsFinite f) (_ : FinitePresentation f)
      (M : ModuleCat.{u + 1} Λ) (_ : Module.Finite Λ M)
      (φ : F ⟶ (etaleModuleDirectImage.{u, u + 1} Λ f).obj
        (smallEtaleLocallyConstantMapsModuleSheaf.{u, u + 1} Λ Y M))
      (Ω : Type u) (_ : Field Ω) (_ : IsSepClosed Ω) (s : Spec (.of Ω) ⟶ X),
      (∀ y : Spec (.of Ω), s y = x) ∧
        IsZero ((etaleModuleInverseImage.{u, u + 1} Λ s).obj (kernel φ)) ∧
        (∀ n : ℕ, n • 𝟙 F = 0 → ∀ m : M, n • m = 0) ∧ IsGenericallyFiniteEtaleOntoImage f := by
  obtain ⟨Y', hY', π, hπ, hN, hS, hx, hsep⟩ :=
    exists_isIntegralHom_isNormal_isSepClosed_functionField x
  obtain ⟨M, hM, φ', hker, htors⟩ := exists_genericPoint_embedding Λ π F hF
  let P := (Stacks.AlgebraicGeometry.Tag0817PartTwo.nonempty_integralLimitPresentation π).some
  obtain ⟨n, W, e, he, hW, p, hp, m, W', e', he', hW', q, hq⟩ :=
    exists_finitePresentation_extensionByZeroConstant Λ F hF
  obtain ⟨i, φ, hφ⟩ := IntegralLimitPresentation.exists_comp_stageMap_eq Λ M P e p e' q φ'
  let c : Y' ⟶ P.diagram.obj i := P.limitCone.app i
  let si := IntegralLimitPresentation.stage P i
  have hcs : c ≫ si = π := (P.compatible i).symm
  have : IsFinite si := P.stageFinite i
  have : UniversallyClosed (c ≫ si) := by
    rw [hcs]
    infer_instance
  have : UniversallyClosed c := UniversallyClosed.of_comp_of_isSeparated c si
  have : IsIntegral c.image := Stacks.Chow.isIntegral_image c
  let f₁ := c.imageι ≫ si
  have hf₁ : FinitePresentation f₁ :=
    ⟨LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance, inferInstance,
      inferInstance⟩
  have htf : c.toImage ≫ f₁ = π := by
    rwa [← Category.assoc, Scheme.Hom.toImage_imageι]
  let r := locallyConstantPushforwardMap.{u, u + 1} Λ M si f₁ c.imageι rfl
  have hr : r ≫ locallyConstantPushforwardMap.{u, u + 1} Λ M f₁ π c.toImage htf =
      IntegralLimitPresentation.stageMap Λ M P i := by
    rw [locallyConstantPushforwardMap_comp, IntegralLimitPresentation.stageMap]
    congr 1
    exact Scheme.Hom.toImage_imageι c
  refine ⟨c.image, f₁, inferInstance, hf₁, M, hM, φ ≫ r, Y'.functionField, inferInstance, hS,
    genericPointInclusion Y' ≫ π, fun y => ?_,
    hker _ (φ ≫ r) (locallyConstantPushforwardMap.{u, u + 1} Λ M f₁ π c.toImage htf)
      (by rw [Category.assoc, hr, hφ]),
    htors, isGenericallyFiniteEtaleOntoImage_imageι_comp c si hcs hsep⟩
  have : Subsingleton ↥(Spec (CommRingCat.of Y'.functionField)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum Y'.functionField))
  rw [Scheme.Hom.comp_apply, Subsingleton.elim y (IsLocalRing.closedPoint Y'.functionField),
    genericPointInclusion_closedPoint, hx]

end Stacks.EtaleCohomology

end
