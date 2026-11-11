module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantPerfectComplexEtale
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.CanonicalFiniteTorDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFiniteTorRepresentation
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.FiniteTorCohomologyBound
public import StacksFrontier.CategoryTheory.Sites.Point.LocalizedPoint

/-!
# Tag 09BI for an object of `D_{ctf}(X_{étale}, Λ)`

Let `X` be a connected scheme in a big étale site, `Λ` a Noetherian ring and `K` an object of
`D_{ctf}(X_{étale}, Λ)` (Tag 03TQ) whose cohomology sheaves are locally constant. Then there are
a finite complex `M` of finite projective `Λ`-modules and an étale covering `{U_i → X}` with
`K|_{U_i} ≅ \underline{M}|_{U_i}` for every `i`.

## Main results

* `AlgebraicGeometry.isFiniteTypeLocallyConstantModuleSheaf_of_isLocallyConstant`: a locally
  constant sheaf of `Λ`-modules whose stalks are finite is locally constant of finite type; in
  particular a constructible locally constant sheaf is.
* `AlgebraicGeometry.exists_isGE_isLE_of_isLocallyConstant_homology`: an object of `D_{ctf}`
  with locally constant cohomology sheaves on a connected scheme is bounded.
* `AlgebraicGeometry.exists_hasFlatRepresentative_sheafFiber_of_locallyHasFiniteTorDimension`:
  the derived fibre at a point of the site of an object of `D_{ctf}` has a bounded flat
  representative over `Λ` (Tag 03TR).
* `AlgebraicGeometry.exists_etaleCover_constantFiniteProjectiveComplex_of_constructibleFiniteTor`
  and its instance at the canonical derived tensor products,
  `AlgebraicGeometry.exists_etaleCover_constantFiniteProjectiveComplex_of_canonicalCtf`:
  **Tag 09BI.**

## Implementation notes

The trivialization itself — local constant models (Tag 094G), one model on a connected base,
perfection of the model by Tag 0658 — is
`AlgebraicGeometry.exists_etaleCover_constantFiniteProjectiveComplex`. The source justifies its
inputs by restricting to affine étale neighbourhoods (Tags 0962, 03TT, 03TR); here the same
inputs are read off membership of `D_{ctf}` directly, over objects of the site and at its points.

* *Local boundedness.* Locally finite Tor dimension gives an object `V` of the site, with
  nonempty image in `X`, over which the image of `K` over the constant coefficient ring sheaf
  has Tor amplitude in some `[a, b]`, so its cohomology vanishes over `V` outside `[a, b]`. The
  cohomology sheaves of `K` are locally constant and `X` is connected, so a cohomology sheaf of
  `K` vanishing over `V` vanishes
  (`isZero_of_isZero_over_moduleSheafOverConstantCoefficients_of_connectedSpace`): `K` is
  bounded. Over a quasi-compact `X` this is Tag 03TQ's remark `D_{ctf} ⊂ D^b`; here it is
  connectedness and local constancy that spread the local bound.
* *Finite type.* The cohomology sheaves of `K` are constructible, so their stalks at geometric
  points are finite `Λ`-modules; the value of a locally constant sheaf over a member of a
  trivializing covering with a geometric point is such a stalk, so the cohomology sheaves are
  locally constant of finite type, which is what Tag 094G asks.
* *Perfection of the stalks (Tag 03TR).* At a point of the site, Tor amplitude in `[a, b]` over
  an object to which the point lifts gives, by the stalk comparison of Tor amplitude
  (`Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitudeCanonical_derivedModuleFiber`), a
  flat representative in `[a, b]` of the derived stalk over the stalk of the constant
  coefficient ring sheaf, which is `Λ`; restricting scalars along that identification it is a
  flat representative over `Λ` of the derived fibre of `K`.

## References

* [Stacks Project, Tag 09BI](https://stacks.math.columbia.edu/tag/09BI)
* [Stacks Project, Tag 03TQ](https://stacks.math.columbia.edu/tag/03TQ)
* [Stacks Project, Tag 03TR](https://stacks.math.columbia.edu/tag/03TR)
* [Stacks Project, Tag 094G](https://stacks.math.columbia.edu/tag/094G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.EtaleCohomology

universe u d

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard
  GrothendieckTopology.hasSheafify_addCommGrpCat
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type u) [CommRing Λ]

/-- Modules over a ring in `Type u` have all limits at the carrier universe `u + 1`. -/
local instance hasLimitsOfSize_moduleCat_succ' :
    HasLimitsOfSize.{u + 1, u + 1} (ModuleCat.{u + 1} Λ) :=
  hasLimits_moduleCat.{u, u + 1} Λ

/-- Sheaves of modules at the module universe `u + 1` of the small étale site form an abelian
category. The global instance `Stacks.Cohomology.SiteModules.moduleSheavesAbelian` is stated at
`SheafOfModules.{max u v r w}` with a free universe `w`, which the unifier cannot solve against
`u + 1`; this seats it with `w = 0`. -/
local instance (priority := high) abelianSheafOfModulesSucc {C : Type (u + 1)} [Category.{u} C]
    {J : GrothendieckTopology C} (O : Sheaf J RingCat.{u + 1}) :
    Abelian (SheafOfModules.{u + 1} O) :=
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian.{u + 1, u, u + 1, 0} O

/-! ### Finite type of a locally constant sheaf with finite stalks -/

/-- The fibre at a point of a site of the constant sheaf with value `M` is `M`: the
neighbourhoods of a point are cofiltered, so the colimit of the constant presheaf is `M`, and the
fibre functor does not distinguish a presheaf from its sheafification. -/
def constantSheafFiberIsoOfPoint {C : Type*} [Category C] {J : GrothendieckTopology C}
    (p : J.Point.{u + 1}) (M : ModuleCat.{u + 1} Λ) [HasWeakSheafify J (ModuleCat.{u + 1} Λ)] :
    p.sheafFiber.obj ((constantSheaf J (ModuleCat.{u + 1} Λ)).obj M) ≅ M := by
  have : IsConnected p.fiber.Elementsᵒᵖ := IsFiltered.isConnected _
  exact (p.presheafToSheafCompSheafFiberIso (ModuleCat.{u + 1} Λ)).app ((Functor.const _).obj M) ≪≫
    ((isColimitConstCocone p.fiber.Elementsᵒᵖ M).coconePointUniqueUpToIso
      (p.isColimitPresheafFiberCocone ((Functor.const _).obj M))).symm

/-- **A locally constant sheaf of `Λ`-modules on the small étale site whose stalks at the
geometric points are finite is locally constant of finite type.** The value of the sheaf over a
member of a trivializing covering which carries a geometric point is the stalk there; the
members carrying no geometric point are empty and may be dropped from the covering. -/
theorem isFiniteTypeLocallyConstantModuleSheaf_of_isLocallyConstant
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ))
    (hF : Stacks.ConstantSheaf.IsLocallyConstant (SmallEtale.topology B X.obj X.property) F)
    (hfin : ∀ s : GeometricPoint X.obj,
      Module.Finite Λ ((etaleModuleStalkFunctor.{u, u + 1, u} B X Λ s).obj F)) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, u, u}
      (SmallEtale.topology B X.obj X.property) Λ F := by
  intro U
  obtain ⟨I, V, f, hcov, hconst⟩ := hF.exists_cover U
  let I' := {i : I // Nonempty ((SmallEtale.toScheme B X.obj X.property).obj (V i))}
  refine ⟨I', fun i => V i.1, fun i => f i.1, ?_, fun i => ?_⟩
  · rw [SmallEtale.ofArrows_mem_topology_iff] at hcov ⊢
    intro x
    obtain ⟨i, y, hy⟩ := hcov x
    exact ⟨⟨i, ⟨y⟩⟩, y, hy⟩
  · obtain ⟨E, ⟨e⟩⟩ := (hconst i.1).mem_essImage
    refine ⟨E, ?_, ⟨e⟩⟩
    obtain ⟨y⟩ := i.2
    let t := GeometricPoint.ofPoint ((SmallEtale.toScheme B X.obj X.property).obj (V i.1)) y
    let s := t.map (B.inclusion.map (V i.1).obj.hom)
    let Ψ := (geometricSitePoint B X s).ulift.{u + 1}
    let z : Ψ.fiber.obj (V i.1) := ULift.up ⟨t.hom, rfl⟩
    let eE : E ≅ (etaleModuleStalkFunctor.{u, u + 1, u} B X Λ s).obj F :=
      (constantSheafFiberIsoOfPoint Λ (Ψ.over z) E).symm ≪≫
        (Ψ.over z).sheafFiber.mapIso e ≪≫
        (GrothendieckTopology.Point.sheafFiberOverIso Ψ z (ModuleCat.{u + 1} Λ)).app F ≪≫
        uliftGeometricSitePointFiberIso B X Λ s F
    have := hfin s
    rw [ModuleCat.isFG_iff]
    exact Module.Finite.equiv eE.symm.toLinearEquiv

/-! ### Boundedness, finite type and perfect stalks of an object of `D_{ctf}` -/

section Ctf

variable
  [HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, u + 1}
    (constantCoefficientRingedSite.{u, u + 1, u} B X Λ))]
  [hSliceDerived : ∀ U : (constantCoefficientRingedSite.{u, u + 1, u} B X Λ).C,
    HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, u + 1}
      ((constantCoefficientRingedSite.{u, u + 1, u} B X Λ).over U))]
  [∀ U : (constantCoefficientRingedSite.{u, u + 1, u} B X Λ).C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u + 1, u + 1, u + 1}
      ((constantCoefficientRingedSite.{u, u + 1, u} B X Λ).over U).O).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, u + 1, u} B X Λ).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u + 1, u + 1, u + 1}
      ((constantCoefficientRingedSite.{u, u + 1, u} B X Λ).over U).O).obj M).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, u + 1, u} B X Λ).C)
    (K L : CochainComplex (RingedSite.Modules.{u + 1, u, u + 1}
      ((constantCoefficientRingedSite.{u, u + 1, u} B X Λ).over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor
        ((constantCoefficientRingedSite.{u, u + 1, u} B X Λ).over U).O) (ComplexShape.up ℤ)]

attribute [local instance] Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory

open Stacks.SheafOfModules.DerivedTensorProduct in
/-- **An object of `D(X_étale, Λ)` of locally finite Tor dimension with locally constant
cohomology sheaves on a connected scheme is bounded.** Locally finite Tor dimension gives an
object `V` with nonempty image over which the image of `K` over the constant coefficient ring
sheaf has Tor amplitude in some `[a, b]`; outside `[a, b]` its cohomology vanishes over `V`, hence
so does the restriction to `V` of the cohomology sheaf of `K`, which is locally constant on a
connected scheme and therefore zero. -/
theorem exists_isGE_isLE_of_isLocallyConstant_homology [ConnectedSpace X.obj]
    [∀ U : SmallEtale B X.obj X.property,
      HasSheafify ((SmallEtale.topology B X.obj X.property).over U) (ModuleCat.{u + 1} Λ)]
    (T : ∀ U : (constantCoefficientRingedSite.{u, u + 1, u} B X Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u + 1, d}
        ((constantCoefficientRingedSite.{u, u + 1, u} B X Λ).over U))
    (K : DerivedCategory
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)))
    (hloc : LocallyHasFiniteTorDimension
      (X := constantCoefficientRingedSite.{u, u + 1, u} B X Λ) T
      ((moduleSheafOverConstantCoefficientsFunctor.{u, u + 1, u} B X Λ).mapDerivedCategory.obj K))
    (hK : ∀ n : ℤ, Stacks.ConstantSheaf.IsLocallyConstant
      (SmallEtale.topology B X.obj X.property)
      ((DerivedCategory.homologyFunctor
        (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)) n).obj K)) :
    ∃ a b : ℤ, K.IsGE a ∧ K.IsLE b := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X.obj)
  let Ψ := (geometricSitePoint B X (GeometricPoint.ofPoint X.obj x₀)).ulift.{u + 1}
  obtain ⟨@⟨U, x⟩⟩ := IsCofiltered.nonempty (C := Ψ.fiber.Elements)
  obtain ⟨V, -, y, a, b, -, hab⟩ :=
    exists_hasTorAmplitude_derivedRestriction_of_point T _ hloc Ψ x
  have hz : B.inclusion.map V.obj.hom (y.down.1 default) ∈
      (siteEtaleImageOpen B X.obj X.property V : Set X.obj) := ⟨_, rfl⟩
  have hvan : ∀ n : ℤ, n < a ∨ b < n →
      IsZero ((DerivedCategory.homologyFunctor
        (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)) n).obj K) := by
    intro n hn
    set E := (moduleSheafOverConstantCoefficientsFunctor.{u, u + 1, u} B X Λ).mapDerivedCategory.obj
      K
    let : HasDerivedCategory.{d}
        (SheafOfModules.{u + 1}
          ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1}
            (constantCoefficientRingedSite.{u, u + 1, u} B X Λ).O).over V)) := hSliceDerived V
    let ρ := SheafOfModules.overFunctor.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1}
        (constantCoefficientRingedSite.{u, u + 1, u} B X Λ).O) V
    have h1 : IsZero (ρ.obj ((DerivedCategory.homologyFunctor
        (RingedSite.Modules.{u + 1, u, u + 1}
          (constantCoefficientRingedSite.{u, u + 1, u} B X Λ)) n).obj E)) :=
      IsZero.of_iso (isZero_homology_of_hasTorAmplitude (T V) _ hab
          (by simp only [Set.mem_Icc, not_and_or, not_le]; omega))
        ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso.{_, _,
          _, _, d, d} ρ n).app E).symm
    refine isZero_of_isZero_over_moduleSheafOverConstantCoefficients_of_connectedSpace.{u, u + 1,
      u + 1, u} B X Λ _ (hK n) V _ hz (h1.of_iso ?_)
    exact ρ.mapIso ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso.{_, _,
      _, _, _, d} (moduleSheafOverConstantCoefficientsFunctor.{u, u + 1, u} B X Λ) n).app K).symm
  refine ⟨a, b, ?_, ?_⟩
  · rw [DerivedCategory.isGE_iff]
    exact fun i hi => hvan i (.inl hi)
  · rw [DerivedCategory.isLE_iff]
    exact fun i hi => hvan i (.inr hi)

open Stacks.SheafOfModules.DerivedTensorProduct in
/-- **Tag 03TR at a point of the site.** Let `K` be an object of `D(X_étale, Λ)` whose image over
the constant coefficient ring sheaf has locally finite Tor dimension, represented by a complex
`C`. At every point `Ψ` of the small étale site the complex of fibres of `C` has a bounded flat
representative over `Λ`: over an object to which `Ψ` lifts the image of `K` has Tor amplitude in
some `[a, b]`, its derived stalk has a flat representative in `[a, b]` over the stalk of the
constant coefficient ring sheaf, and that stalk is `Λ`. -/
theorem exists_hasFlatRepresentative_sheafFiber_of_locallyHasFiniteTorDimension
    (T : ∀ U : (constantCoefficientRingedSite.{u, u + 1, u} B X Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u + 1, d}
        ((constantCoefficientRingedSite.{u, u + 1, u} B X Λ).over U))
    (K : DerivedCategory
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)))
    (hloc : LocallyHasFiniteTorDimension
      (X := constantCoefficientRingedSite.{u, u + 1, u} B X Λ) T
      ((moduleSheafOverConstantCoefficientsFunctor.{u, u + 1, u} B X Λ).mapDerivedCategory.obj K))
    (C : CochainComplex
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)) ℤ)
    (eC : DerivedCategory.Q.obj C ≅ K)
    (Ψ : (SmallEtale.topology B X.obj X.property).Point.{u + 1}) :
    ∃ a b : ℤ, StacksDraft.Perfect.HasFlatRepresentative.{u, u + 1}
      (DerivedCategory.Q.obj (((Ψ.sheafFiber (A := ModuleCat.{u + 1} Λ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C)) a b := by
  obtain ⟨@⟨U, x⟩⟩ := IsCofiltered.nonempty (C := Ψ.fiber.Elements)
  obtain ⟨V, -, y, a, b, -, hamp⟩ :=
    exists_hasTorAmplitude_derivedRestriction_of_point T _ hloc Ψ x
  refine ⟨a, b, ?_⟩
  let : HasDerivedCategory.{d} (SheafOfModules.{u + 1}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (constantCoefficientRingedSite.{u, u + 1, u} B X Λ).O).over V)) :=
    hSliceDerived V
  let hd : HasDerivedCategory.{d} (SheafOfModules.{u + 1}
      (Stacks.commRingSheafToRingSheaf.{u, u + 1, u + 1}
        ((constantCoefficientRingedSite.{u, u + 1, u} B X Λ).over V).O)) :=
    hSliceDerived V
  let Φ := moduleSheafOverConstantCoefficientsFunctor.{u, u + 1, u} B X Λ
  let ρ := SheafOfModules.overFunctor
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (constantCoefficientRingedSite.{u, u + 1, u} B X Λ).O) V
  let G : SheafOfModules.{u + 1} (Stacks.commRingSheafToRingSheaf.{u, u + 1, u + 1}
        ((constantCoefficientRingedSite.{u, u + 1, u} B X Λ).over V).O) ⥤
      ModuleCat.{u + 1} (sliceStalkRing B X Λ Ψ y) :=
    Stacks.sheafModuleFiberOfCommRing (Ψ.over y)
      ((constantCoefficientRingedSite.{u, u + 1, u} B X Λ).over V).O
  have : (Φ ⋙ ρ ⋙ G).PreservesZeroMorphisms := ⟨fun _ _ => by
    change G.map (ρ.map (Φ.map 0)) = 0
    rw [Φ.map_zero, ρ.map_zero]
    exact G.map_zero _ _⟩
  let D := ((Φ ⋙ ρ ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ)).obj C
  have h0 := hasTorAmplitudeCanonical_derivedModuleFiber
    (Y := (constantCoefficientRingedSite.{u, u + 1, u} B X Λ).over V)
    (T V) _ a b hamp (Ψ.over y)
  have h1 := (StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_hasFlatRepresentative
    _ _ a b).1 h0
  have h2 : StacksDraft.TorAmplitude.HasFlatRepresentative (DerivedCategory.Q.obj D) a b :=
    StacksDraft.TorAmplitude.hasFlatRepresentative_of_iso
      ((Functor.mapDerivedCategory.{d} G).mapIso
        (((Functor.mapDerivedCategoryFactors.{d, d} ρ).app _).symm ≪≫
          (RingedSite.derivedRestriction.{u + 1, u, u + 1, d}
            (constantCoefficientRingedSite.{u, u + 1, u} B X Λ) V).mapIso
            (((Functor.mapDerivedCategoryFactors.{_, d} Φ).app C).symm ≪≫
              Φ.mapDerivedCategory.mapIso eC)).symm ≪≫
        (Functor.mapDerivedCategoryFactors.{d, _} G).app _) h1
  obtain ⟨E, hflat, hGE, hLE, ⟨g⟩⟩ := hasFlatRepresentative_restrictScalars
    (constantCoefficientRingOverFiberEquiv.{u, u + 1, u} B X Λ Ψ y) _ a b h2
  refine ⟨E, hflat, hGE, hLE, ⟨?_ ≪≫ g⟩⟩
  exact DerivedCategory.Q.mapIso
      ((moduleSheafOverConstantCoefficientsSheafFiberComplexIso B X Λ Ψ y).app C) ≪≫
    ((ModuleCat.restrictScalars.{u + 1}
      (constantCoefficientRingOverFiberEquiv.{u, u + 1, u} B X Λ Ψ
        y).toRingHom).mapDerivedCategoryFactors.app D).symm

end Ctf

/-! ### Tag 09BI -/

section Main

variable [IsNoetherianRing Λ] [ConnectedSpace X.obj]
  [HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)]
  [∀ U : SmallEtale B X.obj X.property,
    HasSheafify ((SmallEtale.topology B X.obj X.property).over U) (ModuleCat.{u + 1} Λ)]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, u + 1}
    (constantCoefficientRingedSite.{u, u + 1, u} B X Λ))]
  [hSliceDerived : ∀ U : (constantCoefficientRingedSite.{u, u + 1, u} B X Λ).C,
    HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, u + 1}
      ((constantCoefficientRingedSite.{u, u + 1, u} B X Λ).over U))]
  [∀ U : (constantCoefficientRingedSite.{u, u + 1, u} B X Λ).C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u + 1, u + 1, u + 1}
      ((constantCoefficientRingedSite.{u, u + 1, u} B X Λ).over U).O).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, u + 1, u} B X Λ).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u + 1, u + 1, u + 1}
      ((constantCoefficientRingedSite.{u, u + 1, u} B X Λ).over U).O).obj M).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, u + 1, u} B X Λ).C)
    (K L : CochainComplex (RingedSite.Modules.{u + 1, u, u + 1}
      ((constantCoefficientRingedSite.{u, u + 1, u} B X Λ).over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor
        ((constantCoefficientRingedSite.{u, u + 1, u} B X Λ).over U).O) (ComplexShape.up ℤ)]

/-- **Tag 09BI, with `D_{ctf}` measured against given derived tensor products.** Let `X` be a
connected scheme in a big étale site, `Λ` a Noetherian ring and `K` an object of
`D_{ctf}(X_{étale}, Λ)` (Tag 03TQ, Tor dimension measured against the derived tensor products
`T` on the slices of the constant coefficient ringed site) whose cohomology sheaves are locally
constant. Then there are a finite complex `E` of finite projective `Λ`-modules and an étale
covering of `X` over every member `U i` of which `K` is isomorphic, in `D(U_{i, étale}, Λ)`, to the
constant complex attached to `E`.

Boundedness of `K`, finite type of its cohomology sheaves and the bounded flat representatives
of its derived fibres are derived from membership of `D_{ctf}`
(`AlgebraicGeometry.exists_isGE_isLE_of_isLocallyConstant_homology`,
`AlgebraicGeometry.isFiniteTypeLocallyConstantModuleSheaf_of_isLocallyConstant`,
`AlgebraicGeometry.exists_hasFlatRepresentative_sheafFiber_of_locallyHasFiniteTorDimension`) and
fed to `AlgebraicGeometry.exists_etaleCover_constantFiniteProjectiveComplex`. -/
theorem exists_etaleCover_constantFiniteProjectiveComplex_of_constructibleFiniteTor
    (T : ∀ U : (constantCoefficientRingedSite.{u, u + 1, u} B X Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u + 1, d}
        ((constantCoefficientRingedSite.{u, u + 1, u} B X Λ).over U))
    (K : ConstructibleFiniteTorDerivedCategory.{u, u + 1, u, d} B X Λ T)
    (hK : ∀ n : ℤ, Stacks.ConstantSheaf.IsLocallyConstant
      (SmallEtale.topology B X.obj X.property)
      ((DerivedCategory.homologyFunctor
        (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)) n).obj K.obj.obj)) :
    ∃ (E : CochainComplex (ModuleCat.{u + 1} Λ) ℤ) (a b : ℤ)
      (C : CochainComplex
        (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)) ℤ)
      (_e : K.obj.obj ≅ DerivedCategory.Q.obj C),
      E.IsStrictlyGE a ∧ E.IsStrictlyLE b ∧
      (∀ n : ℤ, Module.Finite Λ (E.X n)) ∧ (∀ n : ℤ, Module.Projective Λ (E.X n)) ∧
      ∃ (I : Type (u + 1)) (U : I → SmallEtale B X.obj X.property)
        (f : ∀ i, U i ⟶ SmallEtale.final B X.obj X.property),
        Sieve.ofArrows U f ∈ SmallEtale.topology B X.obj X.property
          (SmallEtale.final B X.obj X.property) ∧
        ∀ i, Nonempty (DerivedCategory.Q.obj
            ((((SmallEtale.topology B X.obj X.property).overPullback
              (ModuleCat.{u + 1} Λ) (U i)).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) ≅
          DerivedCategory.Q.obj
            (((constantSheaf ((SmallEtale.topology B X.obj X.property).over (U i))
              (ModuleCat.{u + 1} Λ)).mapHomologicalComplex (ComplexShape.up ℤ)).obj E)) := by
  obtain ⟨a, b, hGE, hLE⟩ :=
    exists_isGE_isLE_of_isLocallyConstant_homology B X Λ T K.obj.obj K.property hK
  let Kb : DerivedCategory.Bounded
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)) :=
    ⟨K.obj.obj, ⟨⟨a, hGE⟩, ⟨b, hLE⟩⟩⟩
  refine exists_etaleCover_constantFiniteProjectiveComplex B X Λ Kb
    (fun n => isFiniteTypeLocallyConstantModuleSheaf_of_isLocallyConstant B X Λ _ (hK n)
      (fun s => ?_))
    (fun C V q z e => ?_)
  · have h := stalk_prop_of_isStratifiedLocallyConstantWith B X Λ (ModuleCat.isFG Λ)
      (fun {_ _} e hE => by
        rw [ModuleCat.isFG_iff] at hE ⊢
        have := hE
        exact Module.Finite.equiv e.toLinearEquiv)
      (fun _ hE => by
        rw [ModuleCat.isFG_iff]
        have := hE
        infer_instance)
      _ (K.obj.property n) s
    rwa [ModuleCat.isFG_iff] at h
  · obtain ⟨c, d', ⟨F, hflat, hFGE, hFLE, ⟨g⟩⟩⟩ :=
      exists_hasFlatRepresentative_sheafFiber_of_locallyHasFiniteTorDimension B X Λ T K.obj.obj
        K.property C e.symm q
    have := sheafFiber_preservesZeroMorphisms B X Λ q
    have : (((SmallEtale.topology B X.obj X.property).overPullback (ModuleCat.{u + 1} Λ) V) ⋙
        (q.over z).sheafFiber (A := ModuleCat.{u + 1} Λ)).PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_iso
        (GrothendieckTopology.Point.sheafFiberOverIso q z (ModuleCat.{u + 1} Λ)).symm
    refine ⟨c, d', F, hflat, hFGE, hFLE, ⟨?_ ≪≫ g⟩⟩
    exact ((q.over z).sheafFiber (A := ModuleCat.{u + 1} Λ)).mapDerivedCategoryFactors.app _ ≪≫
      DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex
        (GrothendieckTopology.Point.sheafFiberOverIso q z (ModuleCat.{u + 1} Λ))
        (ComplexShape.up ℤ)).app C)

/-- **Tag 09BI.** Let `X` be a connected scheme in a big étale site and `Λ` a Noetherian ring.
Let `K` be an object of `D_{ctf}(X_{étale}, Λ)` (Tag 03TQ, with the derived tensor products of
Stacks 06YU on the slices of the constant coefficient ringed site) whose cohomology sheaves are
locally constant. Then there are a finite complex `E` of finite projective `Λ`-modules and an
étale covering `{U i → X}` such that, for every `i`, the restriction of `K` to `U i` is
isomorphic in `D(U_{i, étale}, Λ)` to the constant complex attached to `E`. -/
@[stacks 09BI]
theorem exists_etaleCover_constantFiniteProjectiveComplex_of_canonicalCtf
    (K : CanonicalConstructibleFiniteTorDerivedCategory.{u, u + 1, u, d} B X Λ)
    (hK : ∀ n : ℤ, Stacks.ConstantSheaf.IsLocallyConstant
      (SmallEtale.topology B X.obj X.property)
      ((DerivedCategory.homologyFunctor
        (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)) n).obj K.obj.obj)) :
    ∃ (E : CochainComplex (ModuleCat.{u + 1} Λ) ℤ) (a b : ℤ)
      (C : CochainComplex
        (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)) ℤ)
      (_e : K.obj.obj ≅ DerivedCategory.Q.obj C),
      E.IsStrictlyGE a ∧ E.IsStrictlyLE b ∧
      (∀ n : ℤ, Module.Finite Λ (E.X n)) ∧ (∀ n : ℤ, Module.Projective Λ (E.X n)) ∧
      ∃ (I : Type (u + 1)) (U : I → SmallEtale B X.obj X.property)
        (f : ∀ i, U i ⟶ SmallEtale.final B X.obj X.property),
        Sieve.ofArrows U f ∈ SmallEtale.topology B X.obj X.property
          (SmallEtale.final B X.obj X.property) ∧
        ∀ i, Nonempty (DerivedCategory.Q.obj
            ((((SmallEtale.topology B X.obj X.property).overPullback
              (ModuleCat.{u + 1} Λ) (U i)).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) ≅
          DerivedCategory.Q.obj
            (((constantSheaf ((SmallEtale.topology B X.obj X.property).over (U i))
              (ModuleCat.{u + 1} Λ)).mapHomologicalComplex (ComplexShape.up ℤ)).obj E)) :=
  exists_etaleCover_constantFiniteProjectiveComplex_of_constructibleFiniteTor B X Λ
    (canonicalSliceDerivedTensorProduct.{u, u + 1, u, d} B X Λ) K hK

end Main

end AlgebraicGeometry

end
