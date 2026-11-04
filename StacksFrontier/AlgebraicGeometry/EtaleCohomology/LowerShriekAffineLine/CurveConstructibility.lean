module
public import StacksFrontier.AlgebraicGeometry.Limits.StageBaseChangeOpens
public import StacksCore.Algebra.Homology.SpectralSequence.Tower
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowCoreflection
public import StacksFrontier.Algebra.Homology.Resolution.NatIntBridge
public import StacksFrontier.AlgebraicGeometry.AffineVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnboundedExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.IteratedRefinement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InducedCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeCommutation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import StacksFrontier.AlgebraicGeometry.EventualLimitProperties.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.Compactification.ConstructibleCompactImage
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.Compactifications
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Normal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverRepresentable
public import StacksFrontier.Topology.Dimension.CounterexampleCodimension

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LowerShriekAffineLine.QuasiFiniteLowerShriek
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LowerShriekAffineLine.FibreFiniteness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.OpenClosedTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.FiniteCohomology
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeDimensionOne.CurveDiagram
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeDimensionOne.FibreDensity
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeDimensionOne.StageDiagram
public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafComplexLocalHom
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.Constructibility
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperSmoothCurveConstructibility.BaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperSmoothCurveConstructibility.FiniteCoefficients.ConstantCoefficients

/-!
# Compactly supported cohomology of a smooth family of curves with constant coefficients

This file proves Tag 0GKX: for a Noetherian scheme `S`, a separated, quasi-compact morphism
`f : X ⟶ S` which is smooth of relative dimension one, a Noetherian torsion ring `Λ` and a finite
`Λ`-module `M`, the derived lower shriek `Rf_! M̲` has constructible cohomology sheaves, granted
the proper base change theorem (Tag 095T) and Tag 0GKV, which enter as the named arguments
`h095T` and `h0GKV` (Tag 0GKW is proved from Tag 0GKV in
`Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedDirectImage_constant`).

## Main results

* `Stacks.EtaleCohomology.isConstructibleEtaleComplex_derivedLowerShriekUnbounded_constantSheaf`
  — Tag 0GKX.
* `exists_mem_isConstructibleEtaleComplex_derivedLowerShriekUnbounded_of_mem_genericPoints`
  — its generic step: constructibility over a neighbourhood of a generic point of `S`.
* `Stacks.EtaleCohomology.isConstructibleEtaleComplex_derivedLowerShriekUnbounded_of_curveDiagram`
  — the computation on the curve diagram of Tag 0GK7.
* `isConstructibleEtaleComplex_derivedLowerShriekUnbounded_restrictOpen_ofIsProper`
  — the smooth proper part of that diagram, from Tag 0GKW.

## Implementation notes

The source proves the tag by induction on `dim S`, with a base case `dim S = 0` from Tags 0GK0
and 0GKR. Here the induction is Noetherian induction on closed subsets of `S`, whose inductive
step is the source's generic step; that step needs no hypothesis on the dimension, so neither the
finite dimensionality of `S` nor the base case is needed. The source's hypotheses that `S` and
`f` are affine are not used either; see the docstring of the main theorem.

The coefficient ring lives in `Type (u + 1)`: the descent of constructibility (Tag 095Q) and the
finite étale direct image (Tag 095H) are available in the library for sheaves of modules at that
universe.

## References

* [Stacks Project, Tag 0GKX](https://stacks.math.columbia.edu/tag/0GKX)
* [Stacks Project, Tag 0GK7](https://stacks.math.columbia.edu/tag/0GK7)
* [Stacks Project, Tag 0GKW](https://stacks.math.columbia.edu/tag/0GKW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u

attribute [-instance] Stacks.EtaleCohomology.TorsionModules.hasSheafify_smallEtaleTopology_moduleCat
attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace Stacks.EtaleCohomology

variable (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ] (M : ModuleCat.{u + 1} Λ)

/-- The constant sheaf `M̲` placed in degree zero of `D(X_étale, Λ)`. -/
abbrev constantEtaleComplex (X : Scheme.{u}) : DerivedCategory (EtaleModules.{u, u + 1} Λ X) :=
  (DerivedCategory.singleFunctor (EtaleModules.{u, u + 1} Λ X) 0).obj
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)

/-- The restriction of `M̲` along an étale morphism is `M̲`. -/
def constantEtaleComplexRestrictionIso {X U : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    (etaleModuleRestriction.{u, u + 1} Λ j).mapDerivedCategory.obj (constantEtaleComplex Λ M X) ≅
      constantEtaleComplex Λ M U :=
  ((etaleModuleRestriction.{u, u + 1} Λ j).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (((etaleModuleInverseImageRestrictionIso.{u, u + 1} Λ j).app _).symm ≪≫
        (TorsionModules.etaleModuleInverseImageConstantIso.{u, u + 1} Λ j).app M)

variable [Module.Finite Λ M]

/-- `M̲` placed in degree zero lies in `D_c`. -/
theorem isConstructibleEtaleComplex_constantEtaleComplex (X : Scheme.{u}) :
    IsConstructibleEtaleComplex Λ (constantEtaleComplex Λ M X) :=
  isConstructibleEtaleComplex_singleFunctor_obj Λ _
    (isConstructibleEtaleModule_constantSheaf Λ X M)

omit [IsNoetherianRing Λ] in
/-- A sheaf of `Λ`-modules killed by an integer `n > 0` is torsion. -/
theorem isTorsionEtaleModule_of_nsmul_id_eq_zero {X : Scheme.{u}} {F : EtaleModules.{u, u + 1} Λ X}
    {n : ℕ} (hn0 : 0 < n) (h : n • 𝟙 F = 0) : IsTorsionEtaleModule Λ X F := by
  intro V x
  refine ⟨⊤, X.smallEtaleTopology.top_mem V, fun W g _ ↦ ⟨n, hn0, ?_⟩⟩
  have h2 : (sheafToPresheaf _ _).map (n • 𝟙 F) = 0 := by rw [h, Functor.map_zero]
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id] at h2
  have h' := congrArg (fun φ : F.obj ⟶ F.obj ↦ (φ.app (Opposite.op W)).hom (F.obj.map g.op x)) h2
  simpa using h'

omit [IsNoetherianRing Λ] [Module.Finite Λ M] in
/-- A constant sheaf on a module killed by `n > 0` is torsion. -/
theorem isTorsionEtaleModule_constantSheaf {n : ℕ} (hn0 : 0 < n) (hM : ∀ m : M, n • m = 0)
    (X : Scheme.{u}) :
    IsTorsionEtaleModule Λ X
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) := by
  refine isTorsionEtaleModule_of_nsmul_id_eq_zero Λ hn0 ?_
  have hM' : n • 𝟙 M = 0 := by ext m; simpa using hM m
  have := (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map_nsmul (f := 𝟙 M) (n := n)
  rw [CategoryTheory.Functor.map_id, hM', Functor.map_zero] at this
  exact this.symm

omit [IsNoetherianRing Λ] [Module.Finite Λ M] in
/-- `M̲` placed in degree zero has torsion cohomology sheaves, for `M` killed by `n > 0`. -/
theorem torsionCohomologyProperty_constantEtaleComplex {n : ℕ} (hn0 : 0 < n)
    (hM : ∀ m : M, n • m = 0) (X : Scheme.{u}) :
    Stacks.Torsion.torsionCohomologyProperty.{u + 1} X.smallEtaleTopology
      ((etaleModuleForgetDerived.{u, u + 1} Λ X).obj (constantEtaleComplex Λ M X)) :=
  torsionCohomologyProperty_etaleModuleForgetDerived_single Λ _
    (isTorsionEtaleModule_constantSheaf Λ M hn0 hM X)

/-- **`D_c` is closed under the first object of a distinguished triangle**: in a distinguished
triangle whose second and third objects have constructible cohomology sheaves, so does the
first. -/
theorem isConstructibleEtaleComplex_obj₁_of_distinguished {X : Scheme.{u}}
    (T : Pretriangulated.Triangle (DerivedCategory (EtaleModules.{u, u + 1} Λ X)))
    (hT : T ∈ distTriang _) (h₂ : IsConstructibleEtaleComplex Λ T.obj₂)
    (h₃ : IsConstructibleEtaleComplex Λ T.obj₃) : IsConstructibleEtaleComplex Λ T.obj₁ := by
  refine isConstructibleEtaleComplex_obj₂_of_distinguished Λ _
    (Pretriangulated.inv_rot_of_distTriang _ hT)
    (fun i ↦ ?_) h₂
  exact (IsConstructibleEtaleModule Λ).prop_of_iso
    (((DerivedCategory.homologyFunctor (EtaleModules.{u, u + 1} Λ X) 0).shiftIso (-1) i
      (-1 + i) rfl).app T.obj₃).symm (h₃ (-1 + i))

/-- Extension by zero along the identity is the identity: both are left adjoint to restriction
along the identity, which is the identity. -/
def etaleModuleExtensionByZeroIdIsoUnconditional (X : Scheme.{u}) :
    etaleModuleExtensionByZero.{u, u + 1} Λ (𝟙 X) ≅ 𝟭 _ :=
  Adjunction.leftAdjointUniq (etaleModuleExtensionByZeroAdj.{u, u + 1} Λ (𝟙 X))
    (Adjunction.id.ofNatIsoRight
      ((etaleModuleInverseImageRestrictionIso.{u, u + 1} Λ (𝟙 X)).symm ≪≫
        etaleModuleInverseImageIdIso.{u, u + 1} Λ X).symm)

/-- The closed complement of the image of an open immersion, with its reduced structure. -/
abbrev complementClosedImmersion {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (Scheme.IdealSheafData.vanishingIdeal
      (⟨(Set.range j.base)ᶜ, j.isOpenEmbedding.isOpen_range.isClosed_compl⟩ :
        TopologicalSpace.Closeds X)).subscheme ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal _).subschemeι

/-- The range of `complementClosedImmersion j` is the complement of the range of `j`. -/
theorem range_complementClosedImmersion {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Set.range (complementClosedImmersion j).base = (Set.range j.base)ᶜ :=
  (Scheme.IdealSheafData.range_subschemeι _).trans
    (Scheme.IdealSheafData.coe_support_vanishingIdeal _)

/-- `R(Z ⟶ V)_! M̲|_Z` is constructible for a closed immersion `iZ : Z ⟶ X` whose composite with
`p : X ⟶ V` is quasi-finite, granted Tag 095T. -/
private theorem isConstructibleEtaleComplex_derivedLowerShriekUnbounded_complement
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, u + 1} p)
    {n : ℕ} (hn0 : 0 < n) (hM : ∀ m : M, n • m = 0) {Z X V : Scheme.{u}} [IsNoetherian V]
    (iZ : Z ⟶ X) (p : X ⟶ V) [IsSeparated (iZ ≫ p)] [QuasiCompact (iZ ≫ p)]
    [LocallyQuasiFinite (iZ ≫ p)] [LocallyOfFiniteType (iZ ≫ p)]
    (J : CompactificationOf (Over.mk (iZ ≫ p))) :
    IsConstructibleEtaleComplex Λ ((derivedLowerShriekUnbounded.{u, u + 1} (iZ ≫ p) J Λ).obj
      ((etaleModuleDerivedInverseImageGeneral.{u, u + 1} Λ iZ).obj
        (constantEtaleComplex Λ M X))) := by
  have : LocallyOfFinitePresentation (iZ ≫ p) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance
  have := Functor.isGE_obj_mapDerivedCategory (etaleModuleInverseImage.{u, u + 1} Λ iZ)
    (constantEtaleComplex Λ M X) 0 inferInstance
  exact isConstructibleEtaleComplex_derivedLowerShriekUnbounded_of_locallyQuasiFinite Λ h095T
    (iZ ≫ p) _ _ 0
    (torsionCohomologyProperty_etaleModuleForgetDerived_inverseImage.{u, u + 1} Λ iZ _
      (torsionCohomologyProperty_constantEtaleComplex Λ M hn0 hM X))
    (isConstructibleEtaleComplex_etaleModuleDerivedInverseImage Λ iZ _
      (isConstructibleEtaleComplex_constantEtaleComplex Λ M X))

/-- **The smooth proper part of the curve diagram of Tag 0GK7**, granted Tags 095T and 0GKV. Let
`q̄ : Ȳ ⟶ T` be proper and smooth with geometrically connected fibres of dimension at most one,
let `t : T ⟶ V` be finite étale over a Noetherian scheme, and let `j : U ⟶ Ȳ` be an open
immersion meeting every fibre of `q̄`. For a Noetherian ring `Λ` with `n · 1 = 0` and a finite
`Λ`-module `M`, `R(U ⟶ V)_! M̲` has constructible cohomology sheaves, computed through the
compactification `Ȳ` of `U` over `V`.

As in the source: the distinguished triangle of Tag 0GKP for `U ⊆ Ȳ` and the complement `Z`
reduces this to `R(Ȳ ⟶ V)_! M̲ = t_* Rq̄_* M̲`, which is constructible by Tag 0GKW and Tag 095H,
and to `R(Z ⟶ V)_! M̲`, where `Z ⟶ V` is quasi-finite because `U` is dense in the fibres of `q̄`.

Hypotheses: `h095T` is Stacks Tag 095T; `h0GKV` is Stacks Tag 0GKV (Tag 0GKW is
`isConstructibleEtaleModule_homology_derivedDirectImage_constant` from it). -/
theorem isConstructibleEtaleComplex_derivedLowerShriekUnbounded_restrictOpen_ofIsProper
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, u + 1} p)
    (h0GKV : ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f],
      (∀ s : S, topologicalKrullDim (f.fiber s) ≤ ((1 : ℕ) : WithBot ℕ∞)) →
      ∀ (ℓ : ℕ) [Fact ℓ.Prime] (q : ℤ),
        Stacks.EtaleCohomology.IsConstructibleEtaleModule (ZMod ℓ)
          ((DerivedCategory.homologyFunctor
              (Stacks.EtaleCohomology.EtaleModules.{u, 0} (ZMod ℓ) S) q).obj
            ((Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnbounded.{u, 0} (ZMod ℓ) f).obj
              ((DerivedCategory.singleFunctor
                  (Stacks.EtaleCohomology.EtaleModules.{u, 0} (ZMod ℓ) X) 0).obj
                ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ))).obj
                  (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ))))))))
    {n : ℕ} (hn0 : 0 < n) (hM : ∀ m : M, n • m = 0)
    {Ybar T V U : Scheme.{u}} (qbar : Ybar ⟶ T) (t : T ⟶ V) [IsProper qbar] [Smooth qbar]
    [GeometricallyConnected qbar] (hqd : ∀ s, topologicalKrullDim (qbar.fiber s) ≤ 1)
    [IsFinite t] [Etale t] [IsNoetherian V] (jU : U ⟶ Ybar) [IsOpenImmersion jU]
    (hjU : ∀ s : T, ∃ y : U, qbar (jU y) = s) :
    IsConstructibleEtaleComplex Λ
      ((derivedLowerShriekUnbounded.{u, u + 1} (jU ≫ qbar ≫ t)
        ((CompactificationOf.ofIsProper (qbar ≫ t)).restrictOpen jU) Λ).obj
        (constantEtaleComplex Λ M U)) := by
  classical
  let Jbar := CompactificationOf.ofIsProper (qbar ≫ t)
  let iZ := complementClosedImmersion jU
  have hij : Set.range jU.base = (Set.range iZ.base)ᶜ := by
    rw [range_complementClosedImmersion, compl_compl]
  obtain ⟨a, b, c, hT⟩ := (exists_distTriang_derivedLowerShriek_openClosed.{u, u + 1} Λ Jbar jU iZ
    hij).2 (constantEtaleComplex Λ M Ybar)
  refine isConstructibleEtaleComplex_of_iso Λ
    ((derivedLowerShriekUnbounded.{u, u + 1} _ _ Λ).mapIso
      (constantEtaleComplexRestrictionIso Λ M jU))
    (isConstructibleEtaleComplex_obj₁_of_distinguished Λ _ hT ?_ ?_)
  · -- the middle term: `R(q̄ ≫ t)_* M̲ = t_* Rq̄_* M̲`
    show IsConstructibleEtaleComplex Λ ((etaleModuleDerivedDirectImageUnbounded.{u, u + 1} Λ
      (qbar ≫ t)).obj ((etaleModuleDerivedExtensionByZeroUnbounded.{u, u + 1} Λ (𝟙 Ybar)).obj
        (constantEtaleComplex Λ M Ybar)))
    let e₁ : (etaleModuleDerivedExtensionByZeroUnbounded.{u, u + 1} Λ (𝟙 Ybar)).obj
        (constantEtaleComplex Λ M Ybar) ≅ constantEtaleComplex Λ M Ybar :=
      (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, u + 1} Λ (𝟙 Ybar)).app _ ≪≫
        ((etaleModuleExtensionByZero.{u, u + 1} Λ (𝟙 Ybar)).mapDerivedCategorySingleFunctor
          0).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso
          ((etaleModuleExtensionByZeroIdIsoUnconditional Λ Ybar).app _)
    refine isConstructibleEtaleComplex_of_iso Λ
      ((etaleModuleDerivedDirectImageUnbounded.{u, u + 1} Λ (qbar ≫ t)).mapIso e₁).symm ?_
    refine isConstructibleEtaleComplex_of_iso Λ
      ((etaleModuleDerivedDirectImageUnboundedDerivedCompIso.{u, u + 1} Λ qbar t (qbar ≫ t)
        rfl).app _).symm fun q ↦ ?_
    refine (IsConstructibleEtaleModule Λ).prop_of_iso
      ((DerivedCategory.homologyFunctor _ q).mapIso
        ((etaleModuleDerivedDirectImageUnboundedIsoOfIsIntegralHom.{u, u + 1} Λ t).app _) ≪≫
        ((etaleModuleDirectImage.{u, u + 1} Λ t).mapDerivedCategoryHomologyIso q).app _).symm ?_
    exact isConstructibleEtaleModule_etaleModuleDirectImage_of_finite_of_etale Λ t _
      (isConstructibleEtaleModule_homology_derivedDirectImage_constant h0GKV qbar
        (fun s ↦ hqd s) Λ M n hn0 hM q)
  · -- the closed complement is quasi-finite over `V`
    have hdense : ∀ s, Dense ((qbar.fiberι s) ⁻¹' (jU.opensRange : Set Ybar)) := by
      intro s
      rw [dense_preimage_fiberι_iff]
      have :=
        isIrreducible_iff_irreducibleSpace.1 (isIrreducible_preimage_singleton_of_smooth qbar s)
      obtain ⟨y, hy⟩ := hjU s
      exact IsOpen.dense (jU.opensRange.isOpen.preimage continuous_subtype_val)
        ⟨⟨jU y, hy⟩, ⟨y, rfl⟩⟩
    have : LocallyQuasiFinite (iZ ≫ qbar) :=
      locallyQuasiFinite_comp_of_dense_fiber qbar hqd jU.opensRange hdense iZ (by
        rw [range_complementClosedImmersion]
        exact subset_rfl)
    have : LocallyQuasiFinite (iZ ≫ qbar ≫ t) := by
      rw [← Category.assoc]
      infer_instance
    exact isConstructibleEtaleComplex_derivedLowerShriekUnbounded_complement Λ M h095T hn0 hM iZ
      (qbar ≫ t) _

/-- **The induction step of the proof of Tag 0GKX on the curve diagram of Tag 0GK7**, granted
Tags 095T and 0GKV. Let `p_V : X_V ⟶ V` be separated, quasi-compact and locally of finite type
over a Noetherian scheme, with fibres of dimension at most one, and let `t : T ⟶ V`,
`q̄ : Ȳ ⟶ T`, `j : Y ⟶ Ȳ`, `ν : Y ⟶ X_V` and `W ⊆ X_V` be as in Tag 0GK7 (`t` finite étale,
`q̄` smooth proper with geometrically connected fibres of dimension at most one, `j` an open
immersion, `ν` finite surjective with `ν ≫ p_V = j ≫ q̄ ≫ t`, `ν⁻¹(W) ⟶ W` a closed immersion,
and `ν⁻¹(W)` meeting every fibre of `j ≫ q̄`). Then `R(p_V)_! M̲` has constructible cohomology
sheaves, for every compactification of `p_V`.

As in the source: the triangle of Tag 0GKP for `W ⊆ X_V` and its complement `Z`, quasi-finite over
`V` because `W` is dense in the fibres of `p_V`, reduces this to `R(W ⟶ V)_! M̲`; since
`ν⁻¹(W) ⟶ W` is a thickening, Tag 0GKQ identifies that with `R(ν⁻¹(W) ⟶ V)_! M̲`, which is computed
through the compactification `Ȳ` of `ν⁻¹(W)` (Tag 0F7I) and handled by
`isConstructibleEtaleComplex_derivedLowerShriekUnbounded_restrictOpen_ofIsProper`.

Hypotheses: `h095T` is Stacks Tag 095T; `h0GKV` is Stacks Tag 0GKV (Tag 0GKW is
`isConstructibleEtaleModule_homology_derivedDirectImage_constant` from it). -/
theorem isConstructibleEtaleComplex_derivedLowerShriekUnbounded_of_curveDiagram
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, u + 1} p)
    (h0GKV : ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f],
      (∀ s : S, topologicalKrullDim (f.fiber s) ≤ ((1 : ℕ) : WithBot ℕ∞)) →
      ∀ (ℓ : ℕ) [Fact ℓ.Prime] (q : ℤ),
        Stacks.EtaleCohomology.IsConstructibleEtaleModule (ZMod ℓ)
          ((DerivedCategory.homologyFunctor
              (Stacks.EtaleCohomology.EtaleModules.{u, 0} (ZMod ℓ) S) q).obj
            ((Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnbounded.{u, 0} (ZMod ℓ) f).obj
              ((DerivedCategory.singleFunctor
                  (Stacks.EtaleCohomology.EtaleModules.{u, 0} (ZMod ℓ) X) 0).obj
                ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ))).obj
                  (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ))))))))
    {n : ℕ} (hn0 : 0 < n) (hM : ∀ m : M, n • m = 0)
    {XV V T Ybar Y : Scheme.{u}} (pV : XV ⟶ V) [IsSeparated pV] [QuasiCompact pV]
    [LocallyOfFiniteType pV] [IsNoetherian V] (hpd : ∀ s, topologicalKrullDim (pV.fiber s) ≤ 1)
    (JV : CompactificationOf (Over.mk pV)) (t : T ⟶ V) (qbar : Ybar ⟶ T) (jY : Y ⟶ Ybar)
    (ν : Y ⟶ XV) (W : XV.Opens) (hcomm : ν ≫ pV = jY ≫ qbar ≫ t) [IsFinite t] [Etale t]
    [Smooth qbar] [IsProper qbar] [GeometricallyConnected qbar]
    (hqd : ∀ s, topologicalKrullDim (qbar.fiber s) ≤ 1) [IsOpenImmersion jY] [IsFinite ν]
    [Surjective ν] (hW : IsClosedImmersion (ν ∣_ W))
    (hWs : ∀ s : T, ∃ y : Y, ν y ∈ W ∧ qbar (jY y) = s) :
    IsConstructibleEtaleComplex Λ
      ((derivedLowerShriekUnbounded.{u, u + 1} pV JV Λ).obj (constantEtaleComplex Λ M XV)) := by
  classical
  have : IsNoetherian XV := isNoetherian_of_locallyOfFiniteType pV
  -- density of `W` in the fibres
  have hO : IsOpen (ν ⁻¹' (W : Set XV)) := W.isOpen.preimage ν.continuous
  have hdense₁ : ∀ s : T, Dense (((jY ≫ qbar).fiberι s) ⁻¹' (ν ⁻¹' (W : Set XV))) :=
    dense_preimage_fiberι_of_smooth qbar jY hO fun s ↦ by
      obtain ⟨y, hy, hys⟩ := hWs s
      exact ⟨y, hy, hys⟩
  have hdense : ∀ s : V, Dense ((pV.fiberι s) ⁻¹' (W : Set XV)) :=
    dense_preimage_fiberι_of_surjective pV t (jY ≫ qbar) ν (by rw [hcomm, Category.assoc]) _
      hdense₁
  -- the triangle of `W ⊆ X_V` and its complement
  let iZ := complementClosedImmersion W.ι
  have hij : Set.range W.ι.base = (Set.range iZ.base)ᶜ := by
    rw [range_complementClosedImmersion, compl_compl]
  obtain ⟨a, b, c, hT⟩ := (exists_distTriang_derivedLowerShriek_openClosed.{u, u + 1} Λ JV W.ι iZ
    hij).2 (constantEtaleComplex Λ M XV)
  refine isConstructibleEtaleComplex_obj₂_of_distinguished Λ _ hT ?_ ?_
  · -- the open part: through the thickening `ν⁻¹(W) ⟶ W` and the compactification `Ȳ`
    let τ := ν ∣_ W
    have hτs : Function.Surjective τ.base := fun w ↦ by
      obtain ⟨y, hy⟩ := ν.surjective w.1
      exact ⟨⟨y, show ν y ∈ W from hy ▸ w.2⟩, Subtype.ext
        ((morphismRestrict_base_coe ν W ⟨y, show ν y ∈ W from hy ▸ w.2⟩).trans hy)⟩
    let JW := JV.restrictOpen W.ι
    let jU := (ν ⁻¹ᵁ W).ι ≫ jY
    have hg : τ ≫ W.ι ≫ pV = jU ≫ qbar ≫ t := by
      simp only [τ, jU, morphismRestrict_ι_assoc, Category.assoc, hcomm]
    let J₂ := CompactificationOf.ofEq hg
      ((CompactificationOf.ofIsProper (qbar ≫ t)).restrictOpen jU)
    have h₂ : IsConstructibleEtaleComplex Λ
        ((derivedLowerShriekUnbounded.{u, u + 1} (τ ≫ W.ι ≫ pV) J₂ Λ).obj
          (constantEtaleComplex Λ M (ν ⁻¹ᵁ W))) :=
      isConstructibleEtaleComplex_derivedLowerShriekUnbounded_restrictOpen_ofIsProper Λ M h095T
        h0GKV hn0 hM qbar t hqd jU fun s ↦ by
          obtain ⟨y, hy, hys⟩ := hWs s
          exact ⟨⟨y, hy⟩, hys⟩
    let K₁ := (etaleModuleRestriction.{u, u + 1} Λ W.ι).mapDerivedCategory.obj
      (constantEtaleComplex Λ M XV)
    refine isConstructibleEtaleComplex_of_iso Λ
      ((derivedLowerShriekUnboundedThickeningIso.{u, u + 1} Λ JW τ hτs).app K₁) ?_
    let e : (etaleModuleDerivedInverseImageGeneral.{u, u + 1} Λ τ).obj K₁ ≅
        constantEtaleComplex Λ M (ν ⁻¹ᵁ W) :=
      (etaleModuleDerivedInverseImageGeneral.{u, u + 1} Λ τ).mapIso
          (constantEtaleComplexRestrictionIso Λ M W.ι) ≪≫
        etaleModuleDerivedInverseImageSingleConstantIso Λ τ M
    show IsConstructibleEtaleComplex Λ ((derivedLowerShriekUnbounded.{u, u + 1} (τ ≫ W.ι ≫ pV)
      (JW.restrictClosed τ) Λ).obj ((etaleModuleDerivedInverseImageGeneral.{u, u + 1} Λ τ).obj K₁))
    refine isConstructibleEtaleComplex_of_iso Λ
      ((derivedLowerShriekUnbounded.{u, u + 1} _ _ Λ).mapIso e).symm ?_
    exact isConstructibleEtaleComplex_of_iso Λ
      (derivedLowerShriekUnboundedCompactificationIsoUnconditional.{u, u + 1} Λ J₂
        (JW.restrictClosed τ) h095T
        (constantEtaleComplex Λ M (ν ⁻¹ᵁ W)) 0
        (torsionCohomologyProperty_constantEtaleComplex Λ M hn0 hM _)) h₂
  · -- the closed complement is quasi-finite over `V`
    have : LocallyQuasiFinite (iZ ≫ pV) :=
      locallyQuasiFinite_comp_of_dense_fiber pV hpd W hdense iZ (by
        rw [range_complementClosedImmersion, Scheme.Opens.range_ι])
    exact isConstructibleEtaleComplex_derivedLowerShriekUnbounded_complement Λ M h095T hn0 hM iZ
      pV _

/-- `Rf_! M̲` commutes with base change: for a cartesian square of `f` along `g`, the inverse
image of `Rf_! M̲` is `Rf'_! M̲`, computed through the base change of the compactification,
granted the proper base change theorem (Tag 0F7L). -/
def constantEtaleComplexDerivedLowerShriekBaseChangeIso
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, u + 1} p)
    {n : ℕ} (hn0 : 0 < n) (hM : ∀ m : M, n • m = 0)
    {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (sq : IsPullback g' f' f g) (J : CompactificationOf (Over.mk f)) :
    (etaleModuleDerivedInverseImageGeneral.{u, u + 1} Λ g).obj
        ((derivedLowerShriekUnbounded.{u, u + 1} f J Λ).obj (constantEtaleComplex Λ M X)) ≅
      (derivedLowerShriekUnbounded.{u, u + 1} f' (J.baseChange sq) Λ).obj
        (constantEtaleComplex Λ M X') :=
  haveI := isIso_derivedLowerShriekBaseChange_app_of_proper_base_change.{u, u + 1} Λ sq J h095T
    (constantEtaleComplex Λ M X) 0
    (torsionCohomologyProperty_constantEtaleComplex Λ M hn0 hM _)
  asIso ((derivedLowerShriekBaseChangeGeneral.{u, u + 1} Λ sq J).app
      (constantEtaleComplex Λ M X)) ≪≫
    (derivedLowerShriekUnbounded.{u, u + 1} f' (J.baseChange sq) Λ).mapIso
      (etaleModuleDerivedInverseImageSingleConstantIso Λ g' M)

/-- **The generic step of the proof of Tag 0GKX**, granted Tags 095T and 0GKV. Let `S` be a
Noetherian scheme, `f : X ⟶ S` separated, quasi-compact and smooth of relative dimension one, and
`η` a generic point of an irreducible component of `S`. Then `Rf_! M̲` has constructible cohomology
sheaves over an open neighbourhood of `η`.

As in the source: Tag 0GK7 gives an open `U ∋ η`, a finite surjective universally injective
`V ⟶ U` and the curve diagram over `V`; by Tag 095Q it suffices to show that the inverse image of
`Rf_! M̲` to `V` is constructible, and by Tag 0F7L this is `R(X_V ⟶ V)_! M̲`, which is
`Stacks.EtaleCohomology.isConstructibleEtaleComplex_derivedLowerShriekUnbounded_of_curveDiagram`.

Hypotheses: `h095T` is Stacks Tag 095T; `h0GKV` is Stacks Tag 0GKV (Tag 0GKW is
`isConstructibleEtaleModule_homology_derivedDirectImage_constant` from it). -/
theorem exists_mem_isConstructibleEtaleComplex_derivedLowerShriekUnbounded_of_mem_genericPoints
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, u + 1} p)
    (h0GKV : ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f],
      (∀ s : S, topologicalKrullDim (f.fiber s) ≤ ((1 : ℕ) : WithBot ℕ∞)) →
      ∀ (ℓ : ℕ) [Fact ℓ.Prime] (q : ℤ),
        Stacks.EtaleCohomology.IsConstructibleEtaleModule (ZMod ℓ)
          ((DerivedCategory.homologyFunctor
              (Stacks.EtaleCohomology.EtaleModules.{u, 0} (ZMod ℓ) S) q).obj
            ((Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnbounded.{u, 0} (ZMod ℓ) f).obj
              ((DerivedCategory.singleFunctor
                  (Stacks.EtaleCohomology.EtaleModules.{u, 0} (ZMod ℓ) X) 0).obj
                ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ))).obj
                  (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ))))))))
    {n : ℕ} (hn0 : 0 < n) (hM : ∀ m : M, n • m = 0)
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsSeparated f] [QuasiCompact f]
    [SmoothOfRelativeDimension 1 f] (J : CompactificationOf (Over.mk f)) (η : S)
    (hη : η ∈ genericPoints S) :
    ∃ U : S.Opens, η ∈ U ∧ IsConstructibleEtaleComplex Λ
      ((etaleModuleDerivedInverseImageGeneral.{u, u + 1} Λ U.ι).obj
        ((derivedLowerShriekUnbounded.{u, u + 1} f J Λ).obj (constantEtaleComplex Λ M X))) := by
  classical
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have hfp : FinitePresentation f := ⟨inferInstance, inferInstance, inferInstance⟩
  have hfd : ∀ s, topologicalKrullDim (f.fiber s) ≤ 1 := fun s ↦ by
    simpa using topologicalKrullDim_fiber_le_of_smoothOfRelativeDimension 1 f s
  obtain ⟨U, hηU, V, v, hvf, hvs, hvi, XV, a, pV, hsq, T, Ybar, Y, t, qbar, jY, ν, W, hcomm, htf,
    hte, hqs, hqp, hqc, hqd, hj, hνf, hνs, hW, hWs⟩ := exists_curveDiagram_single f hfp η hη (hfd η)
  refine ⟨U, hηU, ?_⟩
  have : CompactSpace U :=
    isCompact_iff_compactSpace.1 (TopologicalSpace.NoetherianSpace.isCompact _)
  have : IsNoetherian U := ⟨⟩
  have := hvf
  have := hvs
  have : IsNoetherian V := isNoetherian_of_locallyOfFiniteType v
  have := htf
  have := hte
  have := hqs
  have := hqp
  have := hqc
  have := hj
  have := hνf
  have := hνs
  refine isConstructibleEtaleComplex_of_inverseImage_of_surjective Λ v _ ?_
  rw [← isConstructibleEtaleComplex_inverseImage_comp_iff]
  have : IsSeparated pV := MorphismProperty.of_isPullback hsq ‹IsSeparated f›
  have : QuasiCompact pV := MorphismProperty.of_isPullback hsq ‹QuasiCompact f›
  have : LocallyOfFiniteType pV :=
    MorphismProperty.of_isPullback hsq (inferInstance : LocallyOfFiniteType f)
  refine isConstructibleEtaleComplex_of_iso Λ
    (constantEtaleComplexDerivedLowerShriekBaseChangeIso Λ M h095T hn0 hM hsq J).symm ?_
  exact isConstructibleEtaleComplex_derivedLowerShriekUnbounded_of_curveDiagram Λ M h095T h0GKV
    hn0 hM pV (forall_topologicalKrullDim_fiber_le_of_isPullback hsq hfd) _ t qbar jY ν W hcomm
    hqd hW hWs

/-- **Tag 0GKX for a module killed by an integer**, granted Tags 095T and 0GKV. Let `S` be a
Noetherian scheme, `f : X ⟶ S` separated, quasi-compact and smooth of relative dimension one, `Λ`
a Noetherian ring and `M` a finite `Λ`-module killed by an integer `n > 0`. Then `Rf_! M̲` has
constructible cohomology sheaves, for every compactification `j` of `f`.

This is the form of the tag that does not ask `Λ` to be torsion; Tag 0GKX
(`Stacks.EtaleCohomology.isConstructibleEtaleComplex_derivedLowerShriekUnbounded_constantSheaf`)
is the case `n = ` the additive order of `1 ∈ Λ`.

Hypotheses: `h095T` is Stacks Tag 095T; `h0GKV` is Stacks Tag 0GKV (Tag 0GKW is
`isConstructibleEtaleModule_homology_derivedDirectImage_constant` from it). -/
theorem isConstructibleEtaleComplex_derivedLowerShriekUnbounded_constantSheaf_of_nsmul
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, u + 1} p)
    (h0GKV : ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f],
      (∀ s : S, topologicalKrullDim (f.fiber s) ≤ ((1 : ℕ) : WithBot ℕ∞)) →
      ∀ (ℓ : ℕ) [Fact ℓ.Prime] (q : ℤ),
        Stacks.EtaleCohomology.IsConstructibleEtaleModule (ZMod ℓ)
          ((DerivedCategory.homologyFunctor
              (Stacks.EtaleCohomology.EtaleModules.{u, 0} (ZMod ℓ) S) q).obj
            ((Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnbounded.{u, 0} (ZMod ℓ) f).obj
              ((DerivedCategory.singleFunctor
                  (Stacks.EtaleCohomology.EtaleModules.{u, 0} (ZMod ℓ) X) 0).obj
                ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ))).obj
                  (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ))))))))
    {n : ℕ} (hn0 : 0 < n) (hM : ∀ m : M, n • m = 0)
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsSeparated f] [QuasiCompact f]
    [SmoothOfRelativeDimension 1 f] (j : CompactificationOf (Over.mk f)) :
    IsConstructibleEtaleComplex Λ ((derivedLowerShriekUnbounded.{u, u + 1} f j Λ).obj
      ((DerivedCategory.singleFunctor (EtaleModules.{u, u + 1} Λ X) 0).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))) := by
  classical
  refine isConstructibleEtaleComplex_of_forall_exists_opens Λ _ fun T i _ hT ↦ ?_
  have : IsNoetherian T := isNoetherian_of_isClosedImmersion i
  obtain ⟨x⟩ := hT
  obtain ⟨η, hη⟩ := genericPoints.ofComponent
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  have sq := IsPullback.of_hasPullback f i
  have : SmoothOfRelativeDimension 1 (pullback.snd f i) :=
    let _ := smoothOfRelativeDimension_isStableUnderBaseChange 1
    MorphismProperty.of_isPullback sq inferInstance
  obtain ⟨U, hηU, hU⟩ :=
    exists_mem_isConstructibleEtaleComplex_derivedLowerShriekUnbounded_of_mem_genericPoints Λ M
      h095T h0GKV hn0 hM (pullback.snd f i) (j.baseChange sq) η hη
  refine ⟨U, ⟨η, hηU⟩, ?_⟩
  rw [isConstructibleEtaleComplex_inverseImage_comp_iff]
  exact isConstructibleEtaleComplex_of_iso Λ
    ((etaleModuleDerivedInverseImageGeneral.{u, u + 1} Λ U.ι).mapIso
      (constantEtaleComplexDerivedLowerShriekBaseChangeIso Λ M h095T hn0 hM sq j).symm) hU

/-- **Stacks Project, Tag 0GKX**, granted Tags 095T and 0GKV. Let `S` be a Noetherian scheme, let
`f : X ⟶ S` be separated, quasi-compact and smooth of relative dimension one, let `Λ` be a
Noetherian ring which is torsion and let `M` be a finite `Λ`-module. Then `Rf_! M̲` has
constructible cohomology sheaves, for `Rf_!` computed through any compactification `j` of `f`.

The source assumes `S` affine of finite dimension and `f` affine. Neither is used: the induction on
`dim S` of the source is replaced by Noetherian induction on the closed subsets of `S`
(`Stacks.EtaleCohomology.isConstructibleEtaleComplex_of_forall_exists_opens`), whose step is the
source's (constructibility near a generic point,
`exists_mem_isConstructibleEtaleComplex_derivedLowerShriekUnbounded_of_mem_genericPoints`,
applied to the base change of `f` to a closed subscheme, Tag 0F7L), and the proof never uses
affineness of `f`, only its quasi-compactness. The generalization matters: the source's proof of
Tag 0GKY applies Tag 0GKX to a finite étale cover `U' ⟶ U` of an open `U ⊆ 𝔸¹_Y`, and `U' ⟶ Y`
need not be affine (for instance `𝔸²` minus a point over `𝔸¹`).

The coefficient ring lives in `Type (u + 1)`, the universe at which the library's Tags 095Q and
095H for sheaves of modules are stated.

Hypotheses: `h095T` is Stacks Tag 095T; `h0GKV` is Stacks Tag 0GKV (Tag 0GKW is
`isConstructibleEtaleModule_homology_derivedDirectImage_constant` from it). -/
theorem isConstructibleEtaleComplex_derivedLowerShriekUnbounded_constantSheaf
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, u + 1} p)
    (h0GKV : ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f],
      (∀ s : S, topologicalKrullDim (f.fiber s) ≤ ((1 : ℕ) : WithBot ℕ∞)) →
      ∀ (ℓ : ℕ) [Fact ℓ.Prime] (q : ℤ),
        Stacks.EtaleCohomology.IsConstructibleEtaleModule (ZMod ℓ)
          ((DerivedCategory.homologyFunctor
              (Stacks.EtaleCohomology.EtaleModules.{u, 0} (ZMod ℓ) S) q).obj
            ((Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnbounded.{u, 0} (ZMod ℓ) f).obj
              ((DerivedCategory.singleFunctor
                  (Stacks.EtaleCohomology.EtaleModules.{u, 0} (ZMod ℓ) X) 0).obj
                ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ))).obj
                  (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ))))))))
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsSeparated f] [QuasiCompact f]
    [SmoothOfRelativeDimension 1 f] (j : CompactificationOf (Over.mk f)) (hΛ : IsAddTorsion Λ) :
    IsConstructibleEtaleComplex Λ ((derivedLowerShriekUnbounded.{u, u + 1} f j Λ).obj
      ((DerivedCategory.singleFunctor (EtaleModules.{u, u + 1} Λ X) 0).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))) := by
  have hn0 : 0 < addOrderOf (1 : Λ) := (hΛ 1).addOrderOf_pos
  have hn : ((addOrderOf (1 : Λ) : ℕ) : Λ) = 0 := by rw [← nsmul_one, addOrderOf_nsmul_eq_zero]
  exact isConstructibleEtaleComplex_derivedLowerShriekUnbounded_constantSheaf_of_nsmul Λ M h095T
    h0GKV hn0 (fun m ↦ by rw [← Nat.cast_smul_eq_nsmul Λ, hn, zero_smul]) f j
end Stacks.EtaleCohomology

end
