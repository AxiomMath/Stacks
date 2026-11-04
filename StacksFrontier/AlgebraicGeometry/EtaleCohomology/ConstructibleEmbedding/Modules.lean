module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModulesConstantRing
public import StacksCore.FieldTheory.Separable
public import StacksFrontier.Algebra.Homology.Resolution.NatIntBridge
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExamplesSheaves.ConstantModuleSheafSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointDomination
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointFiber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Specialization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Support.AffineLifting
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.GeometricPoints
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Normal

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleEmbedding.PointEmbedding
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StalkLocus
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StageFaithfulnessModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModelBridges.Stalks
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.IntegralSurjectiveCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothProperLocallyConstant.Locality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LowerShriekAffineLine.ConstructibleDescent
public import StacksFrontier.Topology.Spectral.ConstructibleTopology
public import StacksFrontier.Topology.Spectral.ConstructibleTopologyUnconditional

/-!
# Supports of kernels, and the embedding of a constructible sheaf of modules

For a sheaf `𝒦` of `Λ`-modules on `X_étale` let `T(𝒦) ⊆ X` be the set of points over which `𝒦`
has a nonzero geometric stalk. For constructible `𝒦` it is constructible (Stacks 09YS (3)); it
misses a point `x` as soon as `𝒦` vanishes after inverse image to a geometric point over `x`; and
outside `T(𝒦)` the geometric stalks of the underlying abelian sheaf vanish.

These are the three facts which turn the pointwise embeddings of
`Stacks.EtaleCohomology.exists_point_embedding` into the embedding of Stacks 09Z6: the supports
of their kernels are constructible and avoid the chosen points, the constructible topology of a
Noetherian scheme is quasi-compact, so finitely many of the embeddings already have kernels with
no common point of support, and their product is injective on every geometric stalk.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Topology

universe u

attribute [-instance] Stacks.EtaleCohomology.TorsionModules.hasSheafify_smallEtaleTopology_moduleCat
attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace Stacks.EtaleCohomology

variable (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]

/-- The support of a sheaf of `Λ`-modules on `X_étale`: the points of `X` over which some geometric
stalk is nonzero, the stalks being those of the small étale site of Tag 021B of the big étale site
`AlgebraicGeometry.BigEtaleSite.containing X`. -/
def etaleModuleSupport {X : Scheme.{u}} (K : EtaleModules.{u, u + 1} Λ X) : Set X :=
  {x | ∃ t : GeometricPoint X, t.LiesOver x ∧
    ¬ IsZero (etaleStalk (BigEtaleSite.containing X) X (BigEtaleSite.contains_containing X) t
      ((etaleModuleToBoundedSite Λ (BigEtaleSite.containing X)
        (BigEtaleSite.contains_containing X)).obj K).obj)}

/-- **The support of a constructible sheaf is constructible** (Stacks 09YS (3)). -/
theorem isConstructible_etaleModuleSupport {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (K : EtaleModules.{u, u + 1} Λ X)
    (hK : IsConstructibleEtaleModule Λ K) :
    Topology.IsConstructible (etaleModuleSupport Λ K) := by
  let B := BigEtaleSite.containing X
  have hX : B.Contains X := BigEtaleSite.contains_containing X
  have : CompactSpace (B.obj X hX).obj := ‹CompactSpace X›
  have : QuasiSeparatedSpace (B.obj X hX).obj := ‹QuasiSeparatedSpace X›
  exact isConstructible_support_moduleSheaf.{u + 1, u, u + 1} B (B.obj X hX) Λ _ hK

omit [IsNoetherianRing Λ] in
/-- A module whose underlying abelian group is zero is zero. -/
private theorem isZero_of_isZero_forget₂ {M : ModuleCat.{u + 1} Λ}
    (h : IsZero ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj M)) : IsZero M := by
  have : Subsingleton M := AddCommGrpCat.subsingleton_of_isZero h
  exact ModuleCat.isZero_of_subsingleton M

omit [IsNoetherianRing Λ] in
/-- **The support misses a point at which the sheaf vanishes after inverse image to a geometric
point.** If `s⁻¹ 𝒦 = 0` for a morphism `s : Spec Ω ⟶ X` from a separably closed field onto `x`,
then every geometric stalk of `𝒦` over `x` vanishes. -/
theorem notMem_etaleModuleSupport {X : Scheme.{u}} (K : EtaleModules.{u, u + 1} Λ X)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) {x : X}
    (hs : ∀ y, s y = x) (hK : IsZero ((etaleModuleInverseImage.{u, u + 1} Λ s).obj K)) :
    x ∉ etaleModuleSupport Λ K := by
  rintro ⟨t, ht, hne⟩
  apply hne
  let B := BigEtaleSite.containing X
  have hX : B.Contains X := BigEtaleSite.contains_containing X
  let Ω' := AlgebraicClosure Ω
  let ι : Spec (.of Ω') ⟶ Spec (.of Ω) := Spec.map (CommRingCat.ofHom (algebraMap Ω Ω'))
  let c : GeometricPoint (Spec (.of Ω')) := { residueField := Ω', hom := 𝟙 _ }
  let q : GeometricPoint X := c.map (ι ≫ s)
  have hq : t.hom default = q.hom default := by
    show t.hom default = (𝟙 _ ≫ ι ≫ s) default
    rw [ht]
    exact (hs _).symm
  refine IsZero.of_iso ?_ ((etaleStalkPresheafFunctorIsoOfEqBase B X hX hq
    (ModuleCat.{u + 1} Λ)).app ((etaleModuleToBoundedSite Λ B hX).obj K).obj)
  refine isZero_of_isZero_forget₂ Λ
    (IsZero.of_iso ?_ (etaleStalkForgetIsoSmallEtaleStalkAb Λ B hX q K))
  refine IsZero.of_iso ?_ (smallEtaleStalkAbEtaleModuleInverseImageIso Λ (ι ≫ s) c K).symm
  refine Functor.map_isZero _ (Functor.map_isZero _ ?_)
  refine IsZero.of_iso ?_ ((etaleModuleInverseImageCompIso.{u, u + 1} Λ ι s).app K)
  exact Functor.map_isZero (etaleModuleInverseImage.{u, u + 1} Λ ι) hK

omit [IsNoetherianRing Λ] in
/-- **Outside the support the geometric stalks of the underlying abelian sheaf vanish.** -/
theorem isZero_smallEtaleStalkAb_of_notMem_etaleModuleSupport {X : Scheme.{u}}
    (K : EtaleModules.{u, u + 1} Λ X) {x : X} (h : x ∉ etaleModuleSupport Λ K) :
    IsZero ((smallEtaleStalkAb (GeometricPoint.ofPoint X x).hom).obj
      ((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, u + 1} Λ X).obj K)) := by
  by_contra hne
  refine h ⟨GeometricPoint.ofPoint X x, GeometricPoint.ofPoint_liesOver X x, fun hz => hne ?_⟩
  exact IsZero.of_iso (Functor.map_isZero (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) hz)
    (etaleStalkForgetIsoSmallEtaleStalkAb Λ (BigEtaleSite.containing X)
      (BigEtaleSite.contains_containing X) (GeometricPoint.ofPoint X x) K).symm

attribute [local instance 3000] Abelian.hasFiniteBiproducts

omit [IsNoetherianRing Λ] in
/-- **A family of maps whose kernels have no common point of support is jointly injective.** -/
theorem mono_biproduct_lift_of_forall_exists_notMem_etaleModuleSupport {X : Scheme.{u}}
    {F : EtaleModules.{u, u + 1} Λ X} {n : ℕ} {G : Fin n → EtaleModules.{u, u + 1} Λ X}
    (φ : ∀ k, F ⟶ G k) (h : ∀ x : X, ∃ k, x ∉ etaleModuleSupport Λ (kernel (φ k))) :
    Mono (biproduct.lift φ) := by
  let Fo := _root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, u + 1} Λ X
  refine Fo.mono_of_mono_map ?_
  refine mono_of_geometricStalkAb_family (ι := X)
    (Ω := fun x => (GeometricPoint.ofPoint X x).residueField)
    (fun x => (GeometricPoint.ofPoint X x).hom) ?_ _ fun x => ?_
  · exact Set.eq_univ_of_forall fun y =>
      Set.mem_iUnion.2 ⟨y, ⟨default, GeometricPoint.ofPoint_liesOver X y⟩⟩
  · obtain ⟨k, hk⟩ := h x
    let S := smallEtaleStalkAb (GeometricPoint.ofPoint X x).hom
    have : Mono (S.map (Fo.map (biproduct.lift φ)) ≫ S.map (Fo.map (biproduct.π G k))) := by
      rw [← S.map_comp, ← Fo.map_comp, biproduct.lift_π, Preadditive.mono_iff_isZero_kernel]
      exact IsZero.of_iso (isZero_smallEtaleStalkAb_of_notMem_etaleModuleSupport Λ _ hk)
        (PreservesKernel.iso (Fo ⋙ S) (φ k)).symm
    exact mono_of_mono _ (S.map (Fo.map (biproduct.π G k)))

/-- The direct image of the sheaf of locally constant maps into a finite module along a finite
morphism of finite presentation is constructible (Stacks 095R). -/
theorem isConstructibleEtaleModule_etaleModuleDirectImage_locallyConstant {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsFinite f] (hfp : FinitePresentation f) (M : ModuleCat.{u + 1} Λ)
    [Module.Finite Λ M] :
    IsConstructibleEtaleModule Λ ((etaleModuleDirectImage.{u, u + 1} Λ f).obj
      (smallEtaleLocallyConstantMapsModuleSheaf.{u, u + 1} Λ Y M)) :=
  (IsConstructibleEtaleModule Λ).prop_of_iso
    ((etaleModuleDirectImage.{u, u + 1} Λ f).mapIso
      (smallEtaleConstantSheafIsoLocallyConstantMapsModule.{u, u + 1} Λ Y M))
    (isConstructibleEtaleModule_etaleModuleDirectImage_of_isFinite Λ f hfp _
      (isConstructibleEtaleModule_constantSheaf Λ Y M))

/-- A family of constructible subsets `T x` of a Noetherian scheme with `x ∉ T x` has a finite
subfamily with no common point. -/
private theorem exists_finset_forall_exists_notMem_of_isConstructible {X : Scheme.{u}}
    [IsNoetherian X] (T : X → Set X) (hT : ∀ x, Topology.IsConstructible (T x))
    (hxT : ∀ x, x ∉ T x) :
    ∃ S : Finset X, ∀ y, ∃ x ∈ S, y ∉ T x := by
  have hcl : ∀ x, IsClosed (WithConstructibleTopology.ofConstructible ⁻¹' T x :
      Set (WithConstructibleTopology X)) := fun x =>
    WithConstructibleTopology.isClosed_preimage_ofConstructible_of_isConstructible (hT x)
  have hempty : (⋂ x, (WithConstructibleTopology.ofConstructible ⁻¹' T x :
      Set (WithConstructibleTopology X))) = ∅ :=
    Set.eq_empty_iff_forall_notMem.2 fun y hy =>
      hxT (WithConstructibleTopology.ofConstructible y) (Set.mem_iInter.1 hy _)
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subfamily_closed _ hcl (by simp [hempty])
  refine ⟨S, fun y => ?_⟩
  by_contra! hcon
  exact Set.disjoint_left.1 hS (Set.mem_univ (WithConstructibleTopology.toConstructible y))
    (Set.mem_iInter₂.2 fun x hx => hcon x hx)

/-- **Stacks 09Z6 for sheaves of modules, in the form of locally constant maps.** Let `X` be a
Noetherian scheme, `Λ` a Noetherian ring and `ℱ` a constructible sheaf of `Λ`-modules on
`X_étale`. There is an injective map `ℱ ⟶ ⨁ᵢ fᵢ_* 𝓛_{Yᵢ}(Mᵢ)` into a finite direct sum, with the
`fᵢ` finite of finite presentation and the `Mᵢ` finite `Λ`-modules; if `ℱ` is killed by an
integer `N`, so are the `Mᵢ`. Each `Yᵢ` is integral and maps onto an integral closed subscheme
`Zᵢ` of `X`, finite étale over a nonempty open of `Zᵢ`. -/
theorem exists_mono_biproduct_lift_locallyConstant {X : Scheme.{u}} [IsNoetherian X]
    (F : EtaleModules.{u, u + 1} Λ X) (hF : IsConstructibleEtaleModule Λ F) :
    ∃ (n : ℕ) (Y : Fin n → Scheme.{u}) (f : ∀ k, Y k ⟶ X) (_ : ∀ k, IsFinite (f k))
      (_ : ∀ k, FinitePresentation (f k)) (M : Fin n → ModuleCat.{u + 1} Λ)
      (_ : ∀ k, Module.Finite Λ (M k))
      (φ : ∀ k, F ⟶ (etaleModuleDirectImage.{u, u + 1} Λ (f k)).obj
        (smallEtaleLocallyConstantMapsModuleSheaf.{u, u + 1} Λ (Y k) (M k))),
      Mono (biproduct.lift φ) ∧ (∀ N : ℕ, N • 𝟙 F = 0 → ∀ k (m : M k), N • m = 0) ∧
        ∀ k, IsGenericallyFiniteEtaleOntoImage (f k) := by
  classical
  choose Y f hf hfp M hM φ Ω hΩ hsep s hs hz htor hgen using
    fun x => exists_point_embedding Λ F hF x
  let T : X → Set X := fun x => etaleModuleSupport Λ (kernel (φ x))
  have hT : ∀ x, Topology.IsConstructible (T x) := fun x => by
    have := hf x
    have := hM x
    exact isConstructible_etaleModuleSupport Λ _ ((IsConstructibleEtaleModule Λ).prop_kernel (φ x)
      hF (isConstructibleEtaleModule_etaleModuleDirectImage_locallyConstant Λ (f x) (hfp x) (M x)))
  have hxT : ∀ x, x ∉ T x := fun x => by
    let := hΩ x
    have := hsep x
    exact notMem_etaleModuleSupport Λ _ (s x) (hs x) (hz x)
  obtain ⟨S, hS⟩ := exists_finset_forall_exists_notMem_of_isConstructible T hT hxT
  let e : Fin S.card ≃ S := S.equivFin.symm
  let c : Fin S.card → X := fun k => (e k).1
  refine ⟨S.card, fun k => Y (c k), fun k => f (c k), fun k => hf (c k), fun k => hfp (c k),
    fun k => M (c k), fun k => hM (c k), fun k => φ (c k),
    mono_biproduct_lift_of_forall_exists_notMem_etaleModuleSupport Λ _ fun y => ?_,
    fun N hN k m => htor (c k) N hN m, fun k => hgen (c k)⟩
  obtain ⟨x, hx, hy⟩ := hS y
  refine ⟨e.symm ⟨x, hx⟩, ?_⟩
  show y ∉ T (c (e.symm ⟨x, hx⟩))
  rwa [show c (e.symm ⟨x, hx⟩) = x by simp [c]]

end Stacks.EtaleCohomology

end
