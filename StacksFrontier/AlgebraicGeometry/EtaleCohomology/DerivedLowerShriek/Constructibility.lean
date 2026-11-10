module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModulesConstantRing
public import StacksCore.Algebra.Homology.SpectralSequence.Tower
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowCoreflection
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowTruncation
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedSerreInducedTStructure
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.Algebra.Homology.Resolution.NatIntBridge
public import StacksFrontier.AlgebraicGeometry.AffineVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnboundedExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.IteratedRefinement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InducedCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeCommutation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.Compactifications
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.CompactificationsUnconditional
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Bounded
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.Sites
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Normal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.TorsionCohomologySingle
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TrivialityAndGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverRepresentable
public import StacksFrontier.RingTheory.FinitePresentation.ModuleDescent
public import StacksFrontier.Topology.Dimension.CounterexampleCodimension

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CohomologicalBound
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.MayerVietoris
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.TorsionCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesAPI
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionInverseImage
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.AlgebraicGeometry.InductionPrinciple.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.Compactification.ConstructibleCompactImage
public import StacksFrontier.AlgebraicGeometry.Flatness.Compactification.QuasiAffineSource
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.PseudoCoherentFrom
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.PositiveRankSurjectivity
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeAtGenericPointsLocality
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived lower shriek preserves constructibility: the reductions

Let `f : X ⟶ Y` be a separated morphism of finite presentation of quasi-compact quasi-separated
schemes, `j` a compactification of `f` and `Λ` a Noetherian ring. [Stacks, Tag 0GL0] says that
`Rf_! = Rf̄_* ∘ Rj_!` (`Stacks.EtaleCohomology.derivedLowerShriekUnbounded`) carries
`D⁺_{tors, c}(X_étale, Λ)` into `D⁺_{tors, c}(Y_étale, Λ)`. This file proves the reductions of
the source's proof.

## Main definitions

All names below are in the namespace `Stacks.EtaleCohomology`.

* `LowerShriekConstructibleOnSheaves`: the sheaf form of the theorem for a morphism `f`: for
  every compactification and every constructible torsion sheaf `ℱ`, `Rf_!(ℱ[0])` has
  constructible cohomology sheaves.

## Main results

* `constructible_derivedLowerShriekUnbounded`: **[Stacks, Tag 0GL0]**, granted Tags 095T, 095U
  and 0GKZ (named arguments).
* `isTorsionEtaleModule_homology_derivedLowerShriekUnbounded_single`: `Rf_!` of a torsion sheaf
  has torsion cohomology sheaves.
* `isTorsionConstructibleEtaleComplexPlus_derivedLowerShriekUnbounded_of_sheaves`: it suffices to
  treat torsion constructible sheaves placed in degree `0`.
* The steps of the source's proof, each granted the proper base change theorem:
  `lowerShriekConstructibleOnSheaves_of_compactification` (independence of the compactification),
  `lowerShriekConstructibleOnSheaves_of_isAffineOpen_target` (locality on `Y`),
  `lowerShriekConstructibleOnSheaves_sup` and `lowerShriekConstructibleOnSheaves_of_isAffineOpen`
  (Mayer–Vietoris and the induction principle),
  `lowerShriekConstructibleOnSheaves_closedImmersion_comp` (a closed immersion),
  `lowerShriekConstructibleOnSheaves_comp` (composition),
  `lowerShriekConstructibleOnSheaves_affineSpace` (affine space from the affine line) and
  `lowerShriekConstructibleOnSheaves_of_isAffine` (the affine case).
* `lowerShriekConstructibleOnSheaves_iso_comp`: invariance under isomorphism of the source.

## References

* [Stacks Project, Tag 0GL0](https://stacks.math.columbia.edu/tag/0GL0)
* [Stacks Project, Tag 0DDD](https://stacks.math.columbia.edu/tag/0DDD)
* [Stacks Project, Tag 0GKZ](https://stacks.math.columbia.edu/tag/0GKZ)
* [Stacks Project, Tag 0GKN](https://stacks.math.columbia.edu/tag/0GKN)
* [Stacks Project, Tag 0F7J](https://stacks.math.columbia.edu/tag/0F7J)
* [Stacks Project, Tag 0G2A](https://stacks.math.columbia.edu/tag/0G2A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.CompactificationOf

attribute [local instance] HasDerivedCategory.standard

universe u r

attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace Stacks.EtaleCohomology

/-! ### Torsion -/

section Torsion

variable (Λ : Type r) [Ring Λ]

/-- **Higher direct images of a torsion sheaf of `Λ`-modules are torsion** ([Stacks, Tag 0DDD]
part (1), on `D(-_étale, Λ)`). For a quasi-compact quasi-separated morphism `p : S ⟶ T` and a
torsion sheaf `M` of `Λ`-modules on `S_étale`, every cohomology sheaf of `Rp_*(M[0])` is torsion.
-/
theorem isTorsionEtaleModule_homology_etaleModuleDerivedDirectImageUnbounded_single
    {S T : Scheme.{u}} (p : S ⟶ T) [QuasiCompact p] [QuasiSeparated p]
    (M : EtaleModules.{u, r} Λ S) (hM : IsTorsionEtaleModule Λ S M) (q : ℤ) :
    IsTorsionEtaleModule Λ T ((DerivedCategory.homologyFunctor _ q).obj
      ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ p).obj
        ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  rw [isTorsionEtaleModule_iff_torsionSheafProperty_unconditional]
  refine Stacks.Torsion.torsionSheafProperty_of_iso _
    (((etaleModuleForgetAb.{u, r} Λ T).mapDerivedCategoryHomologyIso q).app _) ?_
  rcases lt_or_ge q 0 with hq | hq
  · have : ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ p).obj
        ((DerivedCategory.singleFunctor _ 0).obj M)).IsGE 0 :=
      etaleModuleDerivedDirectImageUnbounded_obj_isGE.{u, r} Λ p _ 0
    have := Functor.isGE_obj_mapDerivedCategory (etaleModuleForgetAb.{u, r} Λ T)
      ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ p).obj
        ((DerivedCategory.singleFunctor _ 0).obj M)) 0 inferInstance
    exact ObjectProperty.prop_of_isZero _
      (DerivedCategory.isZero_of_isGE ((etaleModuleForgetAb.{u, r} Λ T).mapDerivedCategory.obj
        ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ p).obj
          ((DerivedCategory.singleFunctor _ 0).obj M))) 0 q hq)
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    refine Stacks.Torsion.torsionSheafProperty_of_iso _
      ((DerivedCategory.homologyFunctor _ (m : ℤ)).mapIso
          (((etaleModuleDerivedDirectImageForgetIsoUnconditional.{u, r} Λ p).app _) ≪≫
            (etaleAbelianDerivedDirectImage.{u, r} p).mapIso
              (((etaleModuleForgetAb.{u, r} Λ S).mapDerivedCategorySingleFunctor 0).app M)) ≪≫
        (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
          (etaleAbelianDirectImage.{u, r} p) (etaleAbelianDerivedDirectImage.{u, r} p)
          (etaleAbelianDerivedDirectImageUnit.{u, r} p)
          Stacks.DerivedFunctor.exists_quasiIso_isKInjective m).app
            ((etaleModuleForgetAb.{u, r} Λ S).obj M)).symm ?_
    exact torsionSheafProperty_rightDerived_smallEtaleDirectImageAb.{r} p m _
      ((isTorsionEtaleModule_iff_torsionSheafProperty_unconditional Λ M).1 hM)

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (j : CompactificationOf (Over.mk f))

/-- **`Rf_!` of a torsion sheaf has torsion cohomology sheaves.** For a compactification `j` of
`f` and a torsion sheaf `F` of `Λ`-modules on `X_étale`, every cohomology sheaf of `Rf_!(F[0])` is
torsion. -/
theorem isTorsionEtaleModule_homology_derivedLowerShriekUnbounded_single
    (F : EtaleModules.{u, r} Λ X) (hF : IsTorsionEtaleModule Λ X F) (q : ℤ) :
    IsTorsionEtaleModule Λ Y ((DerivedCategory.homologyFunctor _ q).obj
      ((derivedLowerShriekUnbounded.{u, r} f j Λ).obj
        ((DerivedCategory.singleFunctor _ 0).obj F))) := by
  have hF' :
      IsTorsionEtaleModule Λ j.space ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).obj F) :=
    (isTorsionEtaleModule_iff_torsionSheafProperty_unconditional Λ _).2
      (Stacks.Torsion.torsionSheafProperty_of_iso _
        (asIso ((etaleModuleExtensionByZeroForget.{u, r} Λ j.immersion).app F))
        (torsionSheafProperty_extensionByZero.{u, r} j.immersion
          ((etaleModuleForgetAb.{u, r} Λ X).obj F) hF))
  have h := isTorsionEtaleModule_homology_etaleModuleDerivedDirectImageUnbounded_single Λ
    j.toBase _ hF' q
  rw [isTorsionEtaleModule_iff_torsionSheafProperty_unconditional] at h ⊢
  refine Stacks.Torsion.torsionSheafProperty_of_iso _ ((etaleModuleForgetAb.{u, r} Λ Y).mapIso
    ((DerivedCategory.homologyFunctor _ q).mapIso
      (((derivedLowerShriekUnboundedIsoMapDerivedCategory.{u, r} Λ j).app _) ≪≫
        (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ j.toBase).mapIso
          (((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapDerivedCategorySingleFunctor
            0).app F)))).symm h

/-- **Inverse image preserves torsion sheaves of `Λ`-modules.** -/
@[sga "4 IX 1.2" "(iv)"]
theorem isTorsionEtaleModule_etaleModuleInverseImage {X' X : Scheme.{u}} (g : X' ⟶ X)
    (F : EtaleModules.{u, r} Λ X) (hF : IsTorsionEtaleModule Λ X F) :
    IsTorsionEtaleModule Λ X' ((etaleModuleInverseImage.{u, r} Λ g).obj F) :=
  (isTorsionEtaleModule_iff_torsionSheafProperty_unconditional Λ _).2
    (Stacks.Torsion.torsionSheafProperty_of_iso _
      (asIso ((etaleModuleInverseImageForget.{u, r} Λ g).app F))
      (torsionSheafProperty_etaleAbelianInverseImage.{u, r} g _
        ((isTorsionEtaleModule_iff_torsionSheafProperty_unconditional Λ F).1 hF)))

/-- **Restriction along an étale morphism preserves torsion sheaves of `Λ`-modules.** -/
theorem isTorsionEtaleModule_etaleModuleRestriction {U X : Scheme.{u}} (g : U ⟶ X) [Etale g]
    (F : EtaleModules.{u, r} Λ X) (hF : IsTorsionEtaleModule Λ X F) :
    IsTorsionEtaleModule Λ U ((etaleModuleRestriction.{u, r} Λ g).obj F) :=
  (isTorsionEtaleModule_iff_torsionSheafProperty_unconditional Λ _).2
    (Stacks.Torsion.torsionSheafProperty_of_iso _
      ((etaleModuleForgetAb.{u, r} Λ U).mapIso
        ((etaleModuleInverseImageRestrictionIso.{u, r} Λ g).app F))
      ((isTorsionEtaleModule_iff_torsionSheafProperty_unconditional Λ _).1
        (isTorsionEtaleModule_etaleModuleInverseImage Λ g F hF)))

/-- The underlying complex of abelian sheaves of a torsion sheaf of `Λ`-modules placed in degree
`0` has torsion cohomology sheaves. -/
theorem torsionCohomologyProperty_etaleModuleForgetDerived_single {X : Scheme.{u}}
    (F : EtaleModules.{u, r} Λ X) (hF : IsTorsionEtaleModule Λ X F) :
    Stacks.Torsion.torsionCohomologyProperty.{max (u + 1) r} X.smallEtaleTopology
      ((etaleModuleForgetDerived.{u, r} Λ X).obj ((DerivedCategory.singleFunctor _ 0).obj F)) :=
  fun q ↦ Stacks.Torsion.torsionSheafProperty_of_iso _
    ((DerivedCategory.homologyFunctor _ q).mapIso
      (((etaleModuleForgetAb.{u, r} Λ X).mapDerivedCategorySingleFunctor 0).app F).symm)
    (Stacks.Torsion.torsionCohomologyProperty_singleFunctor _ _
      ((isTorsionEtaleModule_iff_torsionSheafProperty_unconditional Λ F).1 hF) q)

/-- **Direct image along a quasi-compact quasi-separated morphism preserves torsion sheaves of
`Λ`-modules** ([Stacks, Tag 0DDD] part (1) in degree zero). -/
theorem isTorsionEtaleModule_etaleModuleDirectImage {X Y : Scheme.{u}} (p : X ⟶ Y) [QuasiCompact p]
    [QuasiSeparated p] (F : EtaleModules.{u, r} Λ X) (hF : IsTorsionEtaleModule Λ X F) :
    IsTorsionEtaleModule Λ Y ((etaleModuleDirectImage.{u, r} Λ p).obj F) :=
  (isTorsionEtaleModule_iff_torsionSheafProperty_unconditional Λ _).2
    (torsionSheafProperty_smallEtaleDirectImageAb.{r} p _
      ((isTorsionEtaleModule_iff_torsionSheafProperty_unconditional Λ F).1 hF))

end Torsion

/-! ### Reduction to sheaves -/

section Sheaves

variable (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]

/-- **The sheaf form of [Stacks, Tag 0GL0].** For every compactification `j` of `f` and every
constructible torsion sheaf `ℱ` of `Λ`-modules on `X_étale`, `Rf_!(ℱ[0])` has constructible
cohomology sheaves. -/
def LowerShriekConstructibleOnSheaves {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ (j : CompactificationOf (Over.mk f)) (F : EtaleModules.{u, r} Λ X),
    IsConstructibleEtaleModule Λ F → IsTorsionEtaleModule Λ X F →
      IsConstructibleEtaleComplex Λ ((derivedLowerShriekUnbounded.{u, r} f j Λ).obj
        ((DerivedCategory.singleFunctor (EtaleModules.{u, r} Λ X) 0).obj F))

/-- The torsion constructible sheaves of `Λ`-modules form a weak Serre subcategory in the sense of
Stacks 02MO. -/
theorem isWeakSerre_isTorsion_and_isConstructibleEtaleModule (X : Scheme.{u}) :
    WeakSerre.IsWeakSerre (fun F : EtaleModules.{u, r} Λ X ↦
      IsTorsionEtaleModule Λ X F ∧ IsConstructibleEtaleModule Λ F) :=
  WeakSerre.isWeakSerre_of_isWeakSerreClass _

/-- The constructible sheaves of `Λ`-modules form a weak Serre subcategory in the sense of
Stacks 02MO. -/
theorem isWeakSerre_isConstructibleEtaleModule (X : Scheme.{u}) :
    WeakSerre.IsWeakSerre (IsConstructibleEtaleModule.{u, r} Λ (X := X)) :=
  WeakSerre.isWeakSerre_of_isWeakSerreClass _

/-- Having constructible cohomology sheaves is invariant under isomorphism. -/
private theorem isConstructibleEtaleComplex_of_iso {X : Scheme.{u}}
    {K L : DerivedCategory (EtaleModules.{u, r} Λ X)} (e : K ≅ L)
    (h : IsConstructibleEtaleComplex Λ K) : IsConstructibleEtaleComplex Λ L :=
  (DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms _
    (isWeakSerre_isConstructibleEtaleModule Λ X)).of_iso e h

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (j : CompactificationOf (Over.mk f))

omit [IsNoetherianRing Λ] in
/-- `Rf_!` of a torsion sheaf whose image has constructible cohomology lies in
`D⁺_{tors, c}(Y_étale, Λ)`. -/
theorem isTorsionConstructibleEtaleComplexPlus_derivedLowerShriekUnbounded_single
    (F : EtaleModules.{u, r} Λ X) (hF : IsTorsionEtaleModule Λ X F)
    (hc : IsConstructibleEtaleComplex Λ ((derivedLowerShriekUnbounded.{u, r} f j Λ).obj
      ((DerivedCategory.singleFunctor (EtaleModules.{u, r} Λ X) 0).obj F))) :
    IsTorsionConstructibleEtaleComplexPlus Λ ((derivedLowerShriekUnbounded.{u, r} f j Λ).obj
      ((DerivedCategory.singleFunctor (EtaleModules.{u, r} Λ X) 0).obj F)) := by
  have : ((derivedLowerShriekUnbounded.{u, r} f j Λ).obj
      ((DerivedCategory.singleFunctor (EtaleModules.{u, r} Λ X) 0).obj F)).IsGE 0 :=
    isGE_derivedLowerShriekUnbounded_obj.{u, r} Λ j _ 0
  exact ⟨⟨0, fun n hn ↦ DerivedCategory.isZero_of_isGE _ 0 n hn⟩, fun n ↦
    ⟨isTorsionEtaleModule_homology_derivedLowerShriekUnbounded_single Λ j F hF n, hc n⟩⟩

/-- **Reduction of [Stacks, Tag 0GL0] to sheaves.** If `Rf_!(ℱ[0])` has constructible cohomology
for every constructible torsion sheaf `ℱ`, then `Rf_!` carries `D⁺_{tors, c}(X_étale, Λ)` into
`D⁺_{tors, c}(Y_étale, Λ)`. -/
@[sga "4½ Th_finitude 1.3" "clause b), special case"]
theorem isTorsionConstructibleEtaleComplexPlus_derivedLowerShriekUnbounded_of_sheaves
    (h : ∀ F : EtaleModules.{u, r} Λ X, IsConstructibleEtaleModule Λ F →
      IsTorsionEtaleModule Λ X F →
        IsConstructibleEtaleComplex Λ ((derivedLowerShriekUnbounded.{u, r} f j Λ).obj
          ((DerivedCategory.singleFunctor (EtaleModules.{u, r} Λ X) 0).obj F)))
    (K : DerivedCategory (EtaleModules.{u, r} Λ X))
    (hK : IsTorsionConstructibleEtaleComplexPlus Λ K) :
    IsTorsionConstructibleEtaleComplexPlus Λ
      ((derivedLowerShriekUnbounded.{u, r} f j Λ).obj K) := by
  let := etaleModuleDerivedDirectImageUnboundedCommShift.{u, r} Λ j.toBase
  have := etaleModuleDerivedDirectImageUnbounded_isTriangulated.{u, r} Λ j.toBase
  let G := (etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapDerivedCategory ⋙
    etaleModuleDerivedDirectImageUnbounded.{u, r} Λ j.toBase
  let e := derivedLowerShriekUnboundedIsoMapDerivedCategory.{u, r} Λ j
  have hB' := isWeakSerre_isTorsion_and_isConstructibleEtaleModule Λ Y
  have hcl := DerivedCategoryB.derivedCategoryBPlus_isClosedUnderIsomorphisms _ hB'
  obtain ⟨⟨a, ha⟩, hH⟩ := hK
  have hGE : K.IsGE a := (DerivedCategory.isGE_iff K a).2 ha
  have hR : ∀ (L : DerivedCategory (EtaleModules.{u, r} Λ X)) (m : ℤ), L.IsGE m →
      (G.obj L).IsGE m := fun L m hL ↦ by
    have : ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapDerivedCategory.obj L).IsGE m :=
      Functor.isGE_obj_mapDerivedCategory _ L m hL
    exact etaleModuleDerivedDirectImageUnbounded_obj_isGE.{u, r} Λ j.toBase _ m
  refine hcl.of_iso (e.app K).symm
    (DerivedCategoryB.derivedCategoryBPlus_map_obj_of_isGE G _ hB' hR K a hGE fun q ↦ ?_)
  exact hcl.of_iso (e.app _)
    (isTorsionConstructibleEtaleComplexPlus_derivedLowerShriekUnbounded_single Λ j _ (hH q).1
      (h _ (hH q).2 (hH q).1))

/-- **Independence of the compactification** ([Stacks, Tag 0F7I] objectwise), granted the proper
base change theorem: if `Rf_!(ℱ[0])` has constructible cohomology for one compactification of `f`
and every constructible torsion sheaf `ℱ`, then it has for every compactification. -/
theorem lowerShriekConstructibleOnSheaves_of_compactification [QuasiCompact f]
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, r} p)
    (j₀ : CompactificationOf (Over.mk f))
    (h : ∀ F : EtaleModules.{u, r} Λ X, IsConstructibleEtaleModule Λ F →
      IsTorsionEtaleModule Λ X F →
        IsConstructibleEtaleComplex Λ ((derivedLowerShriekUnbounded.{u, r} f j₀ Λ).obj
          ((DerivedCategory.singleFunctor (EtaleModules.{u, r} Λ X) 0).obj F))) :
    LowerShriekConstructibleOnSheaves Λ f := fun j F hc ht ↦
  isConstructibleEtaleComplex_of_iso Λ
    (derivedLowerShriekUnboundedCompactificationIsoUnconditional.{u, r} Λ j₀ j h095T _ 0
      (torsionCohomologyProperty_etaleModuleForgetDerived_single Λ F ht)) (h F hc ht)

omit [IsNoetherianRing Λ] in
/-- `LowerShriekConstructibleOnSheaves` only depends on the morphism. -/
theorem lowerShriekConstructibleOnSheaves_congr {f f' : X ⟶ Y} (hf : f = f')
    (h : LowerShriekConstructibleOnSheaves Λ f) : LowerShriekConstructibleOnSheaves Λ f' :=
  hf ▸ h

end Sheaves

/-! ### Isomorphisms of the source -/

section Isomorphism

variable (Λ : Type r) [Ring Λ]

attribute [local instance] moduleCat_hasLimitsOfSize in
/-- Along an isomorphism `e : U ⟶ X`, the counit `e_! e⁻¹ ℱ ⟶ ℱ` of extension by zero is an
isomorphism. -/
instance isIso_etaleModuleExtensionByZeroAdj_counit_app_of_isIso {U X : Scheme.{u}} (e : U ⟶ X)
    [IsIso e] (F : EtaleModules.{u, r} Λ X) :
    IsIso ((etaleModuleExtensionByZeroAdj.{u, r} Λ e).counit.app F) := by
  refine isIso_of_isIso_etaleModuleInverseImage_family.{u, r} Λ (ι := PUnit.{u + 1})
    (fun _ ↦ e) ?_ _ fun _ ↦ ?_
  · simp only [Set.iUnion_const]
    exact Set.range_eq_univ.2 e.surjective
  · refine (NatIso.isIso_map_iff (etaleModuleInverseImageRestrictionIso.{u, r} Λ e) _).2 ?_
    have h := (etaleModuleExtensionByZeroAdj.{u, r} Λ e).right_triangle_components F
    have : IsIso ((etaleModuleExtensionByZeroAdj.{u, r} Λ e).unit.app
        ((etaleModuleRestriction.{u, r} Λ e).obj F) ≫
      (etaleModuleRestriction.{u, r} Λ e).map
        ((etaleModuleExtensionByZeroAdj.{u, r} Λ e).counit.app F)) := by
      rw [h]; exact IsIso.id _
    exact IsIso.of_isIso_comp_left
      ((etaleModuleExtensionByZeroAdj.{u, r} Λ e).unit.app
        ((etaleModuleRestriction.{u, r} Λ e).obj F)) _

end Isomorphism

section IsoInvariance

variable (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]

/-- **The sheaf form of [Stacks, Tag 0GL0] is invariant under isomorphism of the source.** If it
holds for `f : X ⟶ Y`, it holds for `f ∘ e` for every isomorphism `e : X' ≅ X`. -/
theorem lowerShriekConstructibleOnSheaves_iso_comp {X' X Y : Scheme.{u}} (e : X' ≅ X)
    {f : X ⟶ Y} (hf : LowerShriekConstructibleOnSheaves Λ f) :
    LowerShriekConstructibleOnSheaves Λ (e.hom ≫ f) := by
  intro j' F hc ht
  have hf' : LowerShriekConstructibleOnSheaves Λ (e.inv ≫ e.hom ≫ f) :=
    lowerShriekConstructibleOnSheaves_congr Λ (by simp) hf
  let G := (etaleModuleRestriction.{u, r} Λ e.inv).obj F
  have h := hf' (j'.restrictOpen e.inv) G
    (isConstructibleEtaleModule_etaleModuleRestriction Λ e.inv F hc)
    (isTorsionEtaleModule_etaleModuleRestriction Λ e.inv F ht)
  refine isConstructibleEtaleComplex_of_iso Λ ?_ h
  exact (derivedLowerShriekUnboundedRestrictOpenIso.{u, r} Λ j' e.inv).app _ ≪≫
    (derivedLowerShriekUnbounded.{u, r} (e.hom ≫ f) j' Λ).mapIso
      ((etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ e.inv).app _ ≪≫
        ((etaleModuleExtensionByZero.{u, r} Λ e.inv).mapDerivedCategorySingleFunctor 0).app G ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso
          (asIso ((etaleModuleExtensionByZeroAdj.{u, r} Λ e.inv).counit.app F)))

/-- Two open immersions into `X` with the same image give the same sheaf form of
[Stacks, Tag 0GL0] after composing with `f`. -/
theorem lowerShriekConstructibleOnSheaves_of_range_eq {Z₁ Z₂ X Y : Scheme.{u}} (g₁ : Z₁ ⟶ X)
    (g₂ : Z₂ ⟶ X) [IsOpenImmersion g₁] [IsOpenImmersion g₂] (h : Set.range g₁ = Set.range g₂)
    {f : X ⟶ Y} (hf : LowerShriekConstructibleOnSheaves Λ (g₂ ≫ f)) :
    LowerShriekConstructibleOnSheaves Λ (g₁ ≫ f) :=
  lowerShriekConstructibleOnSheaves_congr Λ
    (by rw [← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac])
    (lowerShriekConstructibleOnSheaves_iso_comp Λ (IsOpenImmersion.isoOfRangeEq g₁ g₂ h) hf)

/-- An object whose cohomology objects lie in a weak Serre class `B` has the property for both
summands of a binary biproduct. -/
theorem derivedCategoryB_biprod {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (B : ObjectProperty A) (hB : WeakSerre.IsWeakSerre B) (K L : DerivedCategory A)
    (hK : DerivedCategoryB.derivedCategoryB B K) (hL : DerivedCategoryB.derivedCategoryB B L) :
    DerivedCategoryB.derivedCategoryB B (K ⊞ L) :=
  DerivedCategoryB.derivedCategoryB_mem_obj₂_of_distinguished B hB _
    (binaryBiproductTriangle_distinguished K L) hK hL

/-- In a distinguished triangle whose first two vertices have cohomology objects in a weak Serre
class `B`, so does the third. -/
theorem derivedCategoryB_obj₃_of_distinguished {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] (B : ObjectProperty A) (hB : WeakSerre.IsWeakSerre B)
    (T : Triangle (DerivedCategory A)) (hT : T ∈ distTriang _)
    (h₁ : DerivedCategoryB.derivedCategoryB B T.obj₁)
    (h₂ : DerivedCategoryB.derivedCategoryB B T.obj₂) :
    DerivedCategoryB.derivedCategoryB B T.obj₃ :=
  DerivedCategoryB.derivedCategoryB_mem_obj₂_of_distinguished B hB _ (rot_of_distTriang _ hT) h₂
    (DerivedCategoryB.derivedCategoryB_shift_mem B hB 1 h₁)

/-- **The Mayer–Vietoris step of [Stacks, Tag 0GL0]** ([Stacks, Tag 0GKN]), granted the proper
base change theorem. For opens `U`, `V` of `X`, if the sheaf form of the theorem holds for the
restrictions of `f` to `U`, `V` and `U ∩ V`, it holds for the restriction of `f` to `U ∪ V`. -/
theorem lowerShriekConstructibleOnSheaves_sup
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, r} p)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (j : CompactificationOf (Over.mk f)) (U V : X.Opens)
    [QuasiCompact ((U ⊔ V).ι ≫ f)]
    (hU : LowerShriekConstructibleOnSheaves Λ (U.ι ≫ f))
    (hV : LowerShriekConstructibleOnSheaves Λ (V.ι ≫ f))
    (hUV : LowerShriekConstructibleOnSheaves Λ ((U ⊓ V).ι ≫ f)) :
    LowerShriekConstructibleOnSheaves Λ ((U ⊔ V).ι ≫ f) := by
  let W := U ⊔ V
  let U' : W.toScheme.Opens := W.ι ⁻¹ᵁ U
  let V' : W.toScheme.Opens := W.ι ⁻¹ᵁ V
  have hcov : U' ⊔ V' = ⊤ := by
    change W.ι ⁻¹ᵁ U ⊔ W.ι ⁻¹ᵁ V = ⊤
    rw [← Scheme.Hom.preimage_sup]
    exact Scheme.Opens.ι_preimage_self W
  have hB := isWeakSerre_isConstructibleEtaleModule Λ Y
  have key : ∀ (A : X.Opens) (A' : W.toScheme.Opens),
      Set.range (A'.ι ≫ W.ι) = Set.range A.ι → LowerShriekConstructibleOnSheaves Λ (A.ι ≫ f) →
      ∀ (jA : CompactificationOf (Over.mk (A'.ι ≫ W.ι ≫ f))) (F : EtaleModules.{u, r} Λ W),
        IsConstructibleEtaleModule Λ F → IsTorsionEtaleModule Λ W F →
        IsConstructibleEtaleComplex Λ ((derivedLowerShriekUnbounded.{u, r} (A'.ι ≫ W.ι ≫ f) jA
          Λ).obj ((etaleModuleRestriction.{u, r} Λ A'.ι).mapDerivedCategory.obj
            ((DerivedCategory.singleFunctor _ 0).obj F))) := by
    intro A A' hA hfA jA F hc ht
    have h₁ : LowerShriekConstructibleOnSheaves Λ (A'.ι ≫ W.ι ≫ f) :=
      lowerShriekConstructibleOnSheaves_congr Λ (Category.assoc _ _ _)
        (lowerShriekConstructibleOnSheaves_of_range_eq Λ (A'.ι ≫ W.ι) A.ι hA hfA)
    exact isConstructibleEtaleComplex_of_iso Λ
      ((derivedLowerShriekUnbounded.{u, r} (A'.ι ≫ W.ι ≫ f) jA Λ).mapIso
        (((etaleModuleRestriction.{u, r} Λ A'.ι).mapDerivedCategorySingleFunctor 0).app F).symm)
      (h₁ jA _ (isConstructibleEtaleModule_etaleModuleRestriction Λ A'.ι F hc)
        (isTorsionEtaleModule_etaleModuleRestriction Λ A'.ι F ht))
  have hrange : ∀ (A : X.Opens), A ≤ W → Set.range ((W.ι ⁻¹ᵁ A).ι ≫ W.ι) = Set.range A.ι :=
    fun A hA ↦ Set.ext fun _ ↦
      ⟨fun ⟨y, hy⟩ ↦ ⟨⟨_, y.2⟩, hy⟩, fun ⟨y, hy⟩ ↦ ⟨⟨⟨y.1, hA y.2⟩, y.2⟩, hy⟩⟩
  refine lowerShriekConstructibleOnSheaves_of_compactification Λ h095T (j.restrictOpen W.ι)
    fun F hc ht ↦ ?_
  obtain ⟨α, β, γ, hT⟩ := exists_distTriang_derivedLowerShriekUnbounded_cover.{u, r} Λ
    (j.restrictOpen W.ι) U' V' hcov ((DerivedCategory.singleFunctor _ 0).obj F)
  refine derivedCategoryB_obj₃_of_distinguished _ hB _ hT ?_ ?_
  · refine key (U ⊓ V) (U' ⊓ V') ?_ hUV _ F hc ht
    have : U' ⊓ V' = W.ι ⁻¹ᵁ (U ⊓ V) := by ext; simp [U', V']
    rw [this]
    exact hrange _ (inf_le_left.trans le_sup_left)
  · exact derivedCategoryB_biprod _ hB _ _ (key U U' (hrange U le_sup_left) hU _ F hc ht)
      (key V V' (hrange V le_sup_right) hV _ F hc ht)

/-- **The induction principle step of [Stacks, Tag 0GL0]**: the reduction to an affine source,
granted the proper base change theorem. Let `X` be quasi-compact and quasi-separated and `Y`
quasi-separated. If the sheaf form of the theorem holds for the restriction of `f` to every affine
open of `X`, it holds for `f`. -/
theorem lowerShriekConstructibleOnSheaves_of_isAffineOpen
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, r} p)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (j : CompactificationOf (Over.mk f)) [CompactSpace X]
    [QuasiSeparatedSpace X] [QuasiSeparatedSpace Y]
    (h : ∀ W : X.Opens, IsAffineOpen W → LowerShriekConstructibleOnSheaves Λ (W.ι ≫ f)) :
    LowerShriekConstructibleOnSheaves Λ f := by
  have hQ : LowerShriekConstructibleOnSheaves Λ ((⊤ : X.Opens).ι ≫ f) := by
    refine Stacks.AlgebraicGeometry.InductionPrinciple.induction_top
      (fun W : X.Opens ↦ LowerShriekConstructibleOnSheaves Λ (W.ι ≫ f)) h ?_
    intro U V hU hV hPU hPV hPUV
    have : CompactSpace ↑(U ⊔ V) := isCompact_iff_compactSpace.1 (by
      rw [TopologicalSpace.Opens.coe_sup]
      exact hU.union hV.isCompact)
    exact lowerShriekConstructibleOnSheaves_sup Λ h095T j U V hPU hPV hPUV
  exact lowerShriekConstructibleOnSheaves_congr Λ (Category.id_comp f)
    (lowerShriekConstructibleOnSheaves_of_range_eq Λ (𝟙 X) (⊤ : X.Opens).ι (by simp) hQ)

/-- **Locality on the target of [Stacks, Tag 0GL0]**, granted the proper base change theorem. If
the sheaf form of the theorem holds for the restriction `f ∣_ V` of `f` over every affine open `V`
of `Y`, it holds for `f`. -/
theorem lowerShriekConstructibleOnSheaves_of_isAffineOpen_target
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, r} p)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ V : Y.Opens, IsAffineOpen V → LowerShriekConstructibleOnSheaves Λ (f ∣_ V)) :
    LowerShriekConstructibleOnSheaves Λ f := by
  intro j F hc ht n
  refine (isConstructibleEtaleModule_iff_forall_etaleModuleRestriction_opens Λ _
    (fun V : Y.affineOpens ↦ (V : Y.Opens)) (iSup_affineOpens_eq_top Y)).2 fun V ↦ ?_
  have sq := (isPullback_morphismRestrict f (V : Y.Opens)).flip
  have := isIso_derivedLowerShriekBaseChange_app_of_proper_base_change.{u, r} Λ sq j h095T
    ((DerivedCategory.singleFunctor _ 0).obj F) 0
    (torsionCohomologyProperty_etaleModuleForgetDerived_single Λ F ht)
  refine (IsConstructibleEtaleModule Λ).prop_of_iso ?_
    (h (V : Y.Opens) V.2 (j.baseChange sq) _
      (isConstructibleEtaleModule_etaleModuleInverseImage Λ (f ⁻¹ᵁ (V : Y.Opens)).ι F hc)
      (isTorsionEtaleModule_etaleModuleInverseImage Λ (f ⁻¹ᵁ (V : Y.Opens)).ι F ht) n)
  exact (DerivedCategory.homologyFunctor _ n).mapIso
      ((derivedLowerShriekUnbounded.{u, r} (f ∣_ (V : Y.Opens)) (j.baseChange sq) Λ).mapIso
        (((etaleModuleInverseImage.{u, r} Λ (f ⁻¹ᵁ (V : Y.Opens)).ι).mapDerivedCategorySingleFunctor
          0).app F).symm ≪≫
        (asIso ((derivedLowerShriekBaseChangeGeneral.{u, r} Λ sq j).app _)).symm) ≪≫
    ((etaleModuleInverseImage.{u, r} Λ (V : Y.Opens).ι).mapDerivedCategoryHomologyIso n).app _ ≪≫
    (etaleModuleInverseImageRestrictionIso.{u, r} Λ (V : Y.Opens).ι).app _

/-- **The closed immersion step of [Stacks, Tag 0GL0]**, granted the proper base change theorem.
For a closed immersion `i : X ⟶ P` with quasi-compact open complement and `p : P ⟶ Y` with a
compactification `J`, the sheaf form of the theorem passes from `p` to `i ≫ p`. -/
theorem lowerShriekConstructibleOnSheaves_closedImmersion_comp
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, r} p)
    {X P Y : Scheme.{u}} (i : X ⟶ P) [IsClosedImmersion i] (hi : IsCompact (Set.range i.base)ᶜ)
    {p : P ⟶ Y} [CompactSpace P] [QuasiSeparatedSpace P] [QuasiCompact p]
    (J : CompactificationOf (Over.mk p)) (hp : LowerShriekConstructibleOnSheaves Λ p) :
    LowerShriekConstructibleOnSheaves Λ (i ≫ p) := by
  refine lowerShriekConstructibleOnSheaves_of_compactification Λ h095T (J.restrictClosed i)
    fun F hc ht ↦ ?_
  refine isConstructibleEtaleComplex_of_iso Λ ?_
    (hp J _ (isConstructibleEtaleModule_etaleModuleDirectImage_of_isClosedImmersion Λ i hi F hc)
      (isTorsionEtaleModule_etaleModuleDirectImage Λ i F ht))
  exact (derivedLowerShriekUnbounded.{u, r} p J Λ).mapIso
      (((etaleModuleDirectImage.{u, r} Λ i).mapDerivedCategorySingleFunctor 0).app F).symm ≪≫
    ((derivedLowerShriekUnboundedRestrictClosedIso.{u, r} Λ J i).app _).symm

/-- **The composition step of [Stacks, Tag 0GL0]** ([Stacks, Tag 0F7J]), granted the proper base
change theorem. For `f : X ⟶ Y` and `g : Y ⟶ Z`, a compactification `jg` of `g` and a
compactification `J` of `X` over the ambient scheme of `jg`, the sheaf form of the theorem for `f`
and for `g` gives it for `g ∘ f`. -/
theorem lowerShriekConstructibleOnSheaves_comp
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, r} p)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} [QuasiCompact (f ≫ g)]
    (jg : CompactificationOf (Over.mk g)) (J : CompactificationOf (Over.mk (f ≫ jg.immersion)))
    (hf : LowerShriekConstructibleOnSheaves Λ f) (hg : LowerShriekConstructibleOnSheaves Λ g) :
    LowerShriekConstructibleOnSheaves Λ (f ≫ g) := by
  refine lowerShriekConstructibleOnSheaves_of_compactification Λ h095T
    (overCompactificationComp jg J) fun F hc ht ↦ ?_
  have := isIso_derivedLowerShriekUnboundedCompMap_app.{u, r} Λ jg J h095T
    ((DerivedCategory.singleFunctor _ 0).obj F) 0
    (torsionCohomologyProperty_etaleModuleForgetDerived_single Λ F ht)
  refine isConstructibleEtaleComplex_of_iso Λ
    (asIso ((derivedLowerShriekUnboundedCompMap.{u, r} Λ jg J).app _)) ?_
  exact fun n ↦ ((isTorsionConstructibleEtaleComplexPlus_derivedLowerShriekUnbounded_of_sheaves Λ
    jg (hg jg) _ (isTorsionConstructibleEtaleComplexPlus_derivedLowerShriekUnbounded_single Λ _ F
      ht (hf (overCompactificationRestrict jg J) F hc ht))).2 n).2

/-- **The peeling step of [Stacks, Tag 0GL0]**, granted the proper base change theorem: if the
sheaf form of the theorem holds for the affine line over every affine scheme, it holds for affine
`(d + 1)`-space `𝔸^{d + 1}_Y ⟶ Y` over every affine `Y`. -/
theorem lowerShriekConstructibleOnSheaves_affineSpace
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, r} p)
    (hA1 : ∀ (Y : Scheme.{u}) [IsAffine Y],
      LowerShriekConstructibleOnSheaves Λ (AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y))
    (d : ℕ) (Y : Scheme.{u}) [IsAffine Y] :
    LowerShriekConstructibleOnSheaves Λ (AffineSpace (ULift.{u} (Fin (d + 1))) Y ↘ Y) := by
  induction d generalizing Y with
  | zero => exact hA1 Y
  | succ d ih =>
    let A := AffineSpace (ULift.{u} (Fin 1)) Y
    let g : A ⟶ Y := A ↘ Y
    let f : AffineSpace (ULift.{u} (Fin (d + 1 + 1))) Y ⟶ A :=
      (Stacks.Chow.affineSpaceSuccIso Y (d + 1)).hom ≫
        (AffineSpace (ULift.{u} (Fin (d + 1))) A ↘ A)
    have hf : LowerShriekConstructibleOnSheaves Λ f :=
      lowerShriekConstructibleOnSheaves_iso_comp Λ (Stacks.Chow.affineSpaceSuccIso Y (d + 1))
        (ih A)
    obtain ⟨jg, -⟩ := exists_quasiCompact_compactificationOf_of_isQuasiAffine g
    have : IsSeparated (f ≫ jg.immersion) :=
      have : IsSeparated ((f ≫ jg.immersion) ≫ jg.toBase) := by
        rw [Category.assoc, jg.immersion_toBase_general]; infer_instance
      IsSeparated.of_comp _ jg.toBase
    have : LocallyOfFiniteType (f ≫ jg.immersion) :=
      have : LocallyOfFiniteType ((f ≫ jg.immersion) ≫ jg.toBase) := by
        rw [Category.assoc, jg.immersion_toBase_general]; infer_instance
      locallyOfFiniteType_of_comp _ jg.toBase
    have : CompactSpace jg.space := QuasiCompact.compactSpace_of_compactSpace jg.toBase
    have : QuasiSeparatedSpace jg.space := quasiSeparatedSpace_of_quasiSeparated jg.toBase
    obtain ⟨J, -⟩ := exists_quasiCompact_compactificationOf_of_isQuasiAffine (f ≫ jg.immersion)
    have hfg := lowerShriekConstructibleOnSheaves_comp Λ h095T jg J hf (hA1 Y)
    refine lowerShriekConstructibleOnSheaves_congr Λ ?_ hfg
    simpa [f, g, Category.assoc] using Stacks.Chow.affineSpaceSuccIso_hom_over Y (d + 1)

/-- A morphism of finite type of affine schemes is a closed immersion into some affine space
`𝔸^{d + 1}` of positive dimension over the target, followed by the projection. -/
theorem exists_isClosedImmersion_affineSpace_succ {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    (f : X ⟶ S) [LocallyOfFiniteType f] :
    ∃ (d : ℕ) (i : X ⟶ AffineSpace (ULift.{u} (Fin (d + 1))) S),
      IsClosedImmersion i ∧ i ≫ (AffineSpace (ULift.{u} (Fin (d + 1))) S ↘ S) = f := by
  obtain ⟨n, i, hi, hif⟩ := exists_isClosedImmersion_affineSpace f
  rcases n with _ | d
  · have : IsClosedImmersion f := by
      have : IsClosedImmersion (AffineSpace (ULift.{u} (Fin 0)) S ↘ S) := inferInstance
      rw [← hif]
      exact @IsClosedImmersion.comp _ _ _ i _ hi this
    let s : S ⟶ AffineSpace (ULift.{u} (Fin 1)) S := AffineSpace.homOfVector (𝟙 S) fun _ ↦ 0
    have hs : s ≫ (AffineSpace (ULift.{u} (Fin 1)) S ↘ S) = 𝟙 S := AffineSpace.homOfVector_over _ _
    have : IsClosedImmersion (s ≫ (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)) := by
      rw [hs]; infer_instance
    have : IsClosedImmersion s :=
      IsClosedImmersion.of_comp s (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
    exact ⟨0, f ≫ s, inferInstance, by rw [Category.assoc, hs, Category.comp_id]⟩
  · exact ⟨d, i, hi, hif⟩

/-- **The affine case of [Stacks, Tag 0GL0]**, granted the proper base change theorem and the
case of the affine line (Tag 0GKZ): the sheaf form of the theorem holds for every morphism locally
of finite presentation of affine schemes. -/
theorem lowerShriekConstructibleOnSheaves_of_isAffine
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, r} p)
    (hA1 : ∀ (Y : Scheme.{u}) [IsAffine Y],
      LowerShriekConstructibleOnSheaves Λ (AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y))
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) [LocallyOfFinitePresentation f] :
    LowerShriekConstructibleOnSheaves Λ f := by
  obtain ⟨d, i, hi, hif⟩ := exists_isClosedImmersion_affineSpace_succ f
  let p := AffineSpace (ULift.{u} (Fin (d + 1))) Y ↘ Y
  have : LocallyOfFinitePresentation (i ≫ p) := by rw [hif]; infer_instance
  have : LocallyOfFinitePresentation i := locallyOfFinitePresentation_of_comp i p
  obtain ⟨J, -⟩ := exists_quasiCompact_compactificationOf_of_isQuasiAffine p
  have h := lowerShriekConstructibleOnSheaves_closedImmersion_comp Λ h095T i
    (AlgebraicGeometry.isCompact_compl_range_of_isClosedImmersion i) J
    (lowerShriekConstructibleOnSheaves_affineSpace Λ h095T hA1 d Y)
  exact lowerShriekConstructibleOnSheaves_congr Λ hif h

end IsoInvariance

/-! ### Bounded below complexes -/

section Plus

variable (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]

/-- **[Stacks, Tag 0GL0] for `D⁺_{tors, c}`, granted the proper base change theorem and the case
of the affine line.** Let `f : X ⟶ Y` be a morphism locally of finite presentation and
quasi-compact, with `X` quasi-compact and quasi-separated and `Y` quasi-separated, let `j` be a
compactification of `f` and let `Λ` be a Noetherian ring. If, for every affine scheme `S`, every
compactification of `𝔸¹_S ⟶ S` and every constructible torsion sheaf `ℱ` on `𝔸¹_S`,
`R(𝔸¹_S ⟶ S)_!(ℱ[0])` has constructible cohomology (Tag 0GKZ, `hA1`), then `Rf_!` carries
`D⁺_{tors, c}(X_étale, Λ)` into `D⁺_{tors, c}(Y_étale, Λ)`. -/
theorem isTorsionConstructibleEtaleComplexPlus_derivedLowerShriekUnbounded_of_affineLine
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, r} p)
    (hA1 : ∀ (S : Scheme.{u}) [IsAffine S],
      LowerShriekConstructibleOnSheaves Λ (AffineSpace (ULift.{u} (Fin 1)) S ↘ S))
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f] [QuasiCompact f]
    [CompactSpace X] [QuasiSeparatedSpace X] [QuasiSeparatedSpace Y]
    (j : CompactificationOf (Over.mk f)) (K : DerivedCategory (EtaleModules.{u, r} Λ X))
    (hK : IsTorsionConstructibleEtaleComplexPlus Λ K) :
    IsTorsionConstructibleEtaleComplexPlus Λ
      ((derivedLowerShriekUnbounded.{u, r} f j Λ).obj K) := by
  suffices h : LowerShriekConstructibleOnSheaves Λ f from
    isTorsionConstructibleEtaleComplexPlus_derivedLowerShriekUnbounded_of_sheaves Λ j (h j) K hK
  refine lowerShriekConstructibleOnSheaves_of_isAffineOpen_target Λ h095T f fun V hV ↦ ?_
  have : IsAffine V := hV
  have : CompactSpace (f ⁻¹ᵁ V) := isCompact_iff_compactSpace.1 (f.isCompact_preimage hV.isCompact)
  have : QuasiSeparatedSpace (f ⁻¹ᵁ V) := quasiSeparatedSpace_of_quasiSeparated (f ⁻¹ᵁ V).ι
  refine lowerShriekConstructibleOnSheaves_of_isAffineOpen Λ h095T
    (j.baseChange (isPullback_morphismRestrict f V).flip) fun W hW ↦ ?_
  have : IsAffine W := hW
  exact lowerShriekConstructibleOnSheaves_of_isAffine Λ h095T hA1 (W.ι ≫ f ∣_ V)

end Plus

/-! ### Unbounded complexes over a torsion ring -/

section Unbounded

variable (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]

/-- **[Stacks, Tag 0GL0] for `D_c` over a torsion ring, granted the proper base change theorem,
Tag 095U and the case of the affine line.** Let `f : X ⟶ Y` be locally of finite presentation and
quasi-compact, with `X` and `Y` quasi-compact and quasi-separated, let `j` be a compactification
of `f` and let `Λ` be a Noetherian torsion ring. Then `Rf_!` carries `D_c(X_étale, Λ)` into
`D_c(Y_étale, Λ)`. -/
theorem isConstructibleEtaleComplex_derivedLowerShriekUnbounded_of_affineLine
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, r} p)
    (h095U : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p] (N : ℕ),
      (∀ t : T, topologicalKrullDim (p.fiber t) ≤ N) →
        ∀ F : Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) r},
          Stacks.Torsion.torsionSheafProperty S.smallEtaleTopology F → ∀ q : ℕ, 2 * N < q →
            IsZero (((etaleAbelianDirectImage.{u, r} p).rightDerived q).obj F))
    (hA1 : ∀ (S : Scheme.{u}) [IsAffine S],
      LowerShriekConstructibleOnSheaves Λ (AffineSpace (ULift.{u} (Fin 1)) S ↘ S))
    (hΛ : IsAddTorsion Λ) {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    [QuasiCompact f] [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
    [QuasiSeparatedSpace Y] (j : CompactificationOf (Over.mk f))
    (K : DerivedCategory (EtaleModules.{u, r} Λ X)) (hK : IsConstructibleEtaleComplex Λ K) :
    IsConstructibleEtaleComplex Λ ((derivedLowerShriekUnbounded.{u, r} f j Λ).obj K) := by
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_fiber_le j.toBase
  intro i
  let K' := (DerivedCategory.TStructure.t.truncGE (i - 2 * d)).obj K
  have hK' : IsTorsionConstructibleEtaleComplexPlus Λ K' :=
    ⟨⟨i - 2 * d, fun n hn ↦ DerivedCategory.isZero_of_isGE K' (i - 2 * d) n hn⟩, fun n ↦
      ⟨isTorsionEtaleModule_of_isAddTorsion Λ hΛ _,
        DerivedCategoryB.derivedCategoryB_truncGE_obj _
          (isWeakSerre_isConstructibleEtaleModule Λ X) _ K hK n⟩⟩
  have := isIso_homologyMap_derivedLowerShriekUnbounded_map_truncGEπ_of_isAddTorsion Λ j h095U hΛ
    d hd K i i le_rfl
  exact (IsConstructibleEtaleModule Λ).prop_of_iso
    (asIso ((DerivedCategory.homologyFunctor _ i).map
      ((derivedLowerShriekUnbounded.{u, r} f j Λ).map
        ((DerivedCategory.TStructure.t.truncGEπ (i - 2 * d)).app K)))).symm
    ((isTorsionConstructibleEtaleComplexPlus_derivedLowerShriekUnbounded_of_affineLine Λ h095T hA1 f
      j K' hK').2 i).2

end Unbounded

/-! ### The theorem -/

section Theorem

variable (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]

/-- **[Stacks, Tag 0GL0], granted the proper base change theorem, Tag 095U and Tag 0GKZ.** Let
`f : X ⟶ Y` be a separated morphism of finite presentation of quasi-compact and quasi-separated
schemes, `j` a compactification of `f` (so that `Rf_! = Rf̄_* ∘ Rj_!` is defined, Tag 0F7H) and
`Λ` a Noetherian ring. If `K` is in `D⁺_{tors, c}(X_étale, Λ)`, then `Rf_! K` is in
`D⁺_{tors, c}(Y_étale, Λ)`; if `Λ` is torsion and `K` is in `D_c(X_étale, Λ)`, then `Rf_! K` is in
`D_c(Y_étale, Λ)`. The statement holds for every compactification `j` of `f`.

Named arguments:
* `h095T` is Stacks Tag 095T, the proper base change theorem;
* `h095U` is Stacks Tag 095U, the vanishing `R^q f_* F = 0` for `q > 2N`;
* `h0GKZ` is Stacks Tag 0GKZ, the case of the affine line. -/
theorem constructible_derivedLowerShriekUnbounded
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, u + 1} p)
    (h095U : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p] (N : ℕ),
      (∀ t : T, topologicalKrullDim (p.fiber t) ≤ N) →
        ∀ F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1},
          Stacks.Torsion.torsionSheafProperty S.smallEtaleTopology F → ∀ q : ℕ, 2 * N < q →
            IsZero (((etaleAbelianDirectImage.{u, u + 1} p).rightDerived q).obj F))
    (h0GKZ : ∀ (Y : Scheme.{u}) [IsAffine Y]
      (j : CompactificationOf (Over.mk (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)))
      (F : EtaleModules.{u, u + 1} Λ 𝔸(ULift.{u} (Fin 1); Y)),
      IsConstructibleEtaleModule Λ F → IsTorsionEtaleModule Λ 𝔸(ULift.{u} (Fin 1); Y) F →
      IsConstructibleEtaleComplex Λ
        ((derivedLowerShriekUnbounded.{u, u + 1} (𝔸(ULift.{u} (Fin 1); Y) ↘ Y) j Λ).obj
          ((DerivedCategory.singleFunctor (EtaleModules.{u, u + 1} Λ 𝔸(ULift.{u} (Fin 1); Y)) 0).obj
            F)))
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [LocallyOfFinitePresentation f]
    [QuasiCompact f] [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
    [QuasiSeparatedSpace Y] (j : CompactificationOf (Over.mk f)) :
    (∀ K : DerivedCategory (EtaleModules.{u, u + 1} Λ X),
      IsTorsionConstructibleEtaleComplexPlus Λ K →
        IsTorsionConstructibleEtaleComplexPlus Λ
          ((derivedLowerShriekUnbounded.{u, u + 1} f j Λ).obj K)) ∧
    (IsAddTorsion Λ → ∀ K : DerivedCategory (EtaleModules.{u, u + 1} Λ X),
      IsConstructibleEtaleComplex Λ K →
        IsConstructibleEtaleComplex Λ ((derivedLowerShriekUnbounded.{u, u + 1} f j Λ).obj K)) :=
  ⟨isTorsionConstructibleEtaleComplexPlus_derivedLowerShriekUnbounded_of_affineLine Λ h095T
      (fun S _ ↦ h0GKZ S) f j,
    fun hΛ ↦ isConstructibleEtaleComplex_derivedLowerShriekUnbounded_of_affineLine Λ h095T h095U
      (fun S _ ↦ h0GKZ S) hΛ f j⟩

end Theorem

end Stacks.EtaleCohomology

end
