module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.PullbackFiniteTor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.StalkwiseFiniteTor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.BaseChangeFiber
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Derived inverse image preserves locally finite Tor dimension

Let `Λ` be a Noetherian ring and `f : X ⟶ Y` a morphism of schemes. Tag 0963 says that derived
inverse image carries `D_{ctf}(Y_étale, Λ)` into `D_{ctf}(X_étale, Λ)`, and part (1) of Tag 0962
is the same statement for an étale `f`, where the inverse image is the restriction `K|_U`.

Membership of `D_{ctf}` is the conjunction of two conditions: constructibility of the cohomology
sheaves, and locally finite Tor dimension of the image of the complex in the derived category of
modules over the constant coefficient ring sheaf. Both are carried by derived inverse image: the
first is Tag 095Y, and the second is
`Stacks.EtaleCohomology.pullbackPreservesLocallyFiniteTorDimension`, proved below at an
arbitrary morphism. Tag 0963 is therefore unconditional here.

## Main results

* `Stacks.EtaleCohomology.pullbackPreservesLocallyFiniteTorDimension`: **the
  finite-Tor-dimension half of Tag 0963**, at an arbitrary morphism of schemes.
* `Stacks.EtaleCohomology.isConstructible_and_locallyHasFiniteTorDimension_derivedPullback`:
  **Tag 0963**, derived inverse image `Lf^*` carries an object of `D_{ctf}(Y_étale, Λ)` to one
  of `D_{ctf}(X_étale, Λ)`.
* `Stacks.EtaleCohomology.constructibleFiniteTorDerivedCategoryPullback_unconditional`: the
  same as a map of full subcategories, whose underlying object is `Lf^*K` by
  `Stacks.EtaleCohomology.constructibleFiniteTorDerivedCategoryPullback_unconditional_obj`.
* `Stacks.EtaleCohomology.constructibleFiniteTorDerivedCategoryEtalePullback_unconditional`: the
  same at an étale morphism, which is part (1) of Tag 0962 with the restriction spelled as the
  inverse image. The tag itself is registered on
  `Stacks.EtaleCohomology.constructibleFiniteTorDerivedCategoryEtale` of
  `StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ShriekFiniteTor`, which
  states both of its parts; this statement is one of the two the covering declaration is built
  from, so it carries no tag of its own.

The predicate `Stacks.EtaleCohomology.PullbackPreservesLocallyFiniteTorDimension` and the two
statements `Stacks.EtaleCohomology.constructibleFiniteTorDerivedCategoryPullback` and
`Stacks.EtaleCohomology.constructibleFiniteTorDerivedCategoryEtalePullback` taking it as an
argument are in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.PullbackFiniteTor`;
`Stacks.EtaleCohomology.pullbackPreservesLocallyFiniteTorDimension` proves that predicate for
every morphism.

## Implementation notes

`D_{ctf}(X_étale, Λ)` is `Stacks.EtaleCohomology.ConstructibleFiniteTorDerivedCategory`, the full
subcategory of the constructible derived category of Tag 095W cut out by locally finite Tor
dimension in the sense of Tag 08FZ, read on the image of the complex under the exact functor
`AlgebraicGeometry.moduleSheafOverConstantCoefficientsFunctor` to modules over the constant
coefficient ring sheaf of Tag 03TR. As there, Tor amplitude is measured against a *given* family
of derived tensor products on the slices, so the subcategories over the source and over the
target are indexed by two independent such families, `T` for `Y` and `T'` for `X`.

The coefficient universe is the one at which Tag 095Y is available, `max (u + 1) w`: that is the
universe in which the coefficient category receives the colimits computing the inverse image of
module sheaves, and the exactness instances for the inverse image are stated there. The universe
of the scheme and the universe of the coefficient ring stay independent.

Restriction along an étale morphism `j` is spelled as the inverse image along `j`. The two agree:
`AlgebraicGeometry.smallInverseImageIsoPostcomposePushforward` identifies the inverse image along
an étale morphism of a big étale site with the direct image of composition with it, which is the
restriction functor `AlgebraicGeometry.moduleRestriction` of Tag 03S3 part (3).

*How the finite-Tor-dimension half is proved.* Both the hypothesis and the conclusion are the
local condition of Tag 08FZ (3), read on the slices of the two constant coefficient ringed sites,
so the transport is a comparison of *stalks* rather than of a functor on modules. An earlier
version of this paragraph named two things as missing: a comparison functor
`P : Mod(O_Y) ⥤ Mod(O_X)` between the modules over the two constant coefficient ring sheaves,
exact and flat-preserving, feeding
`Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_mapDerivedCategory` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/TorAmplitude/ExactModulePullback.lean`; and, after
it, the local-to-global passage
`Stacks.SheafOfModules.DerivedTensorProduct.hasFiniteTorDimension_of_locallyHasFiniteTorDimension`
of `StacksFrontier/CategoryTheory/Sites/Cohomology/TorAmplitude/IntervalDescent.lean`. **Neither is
needed**: that route would transport a *global* Tor-amplitude interval.

Finite Tor dimension on one slice is a stalkwise condition, by Tag 0DJJ, which is available in
this tree with all four of its universes free:
`Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitudeCanonical_derivedModuleFiber` and
`Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_of_forall_derivedModuleFiber` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/TorAmplitude/Stalks.lean`. The proof assembles three
statements of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.StalkwiseFiniteTor`:

* the consuming half, on `X`:
  `Stacks.SheafOfModules.DerivedTensorProduct.locallyHasFiniteTorDimension_of_stalkwise_family`
  establishes the local condition from a covering of each object together with one interval per
  member bounding the Tor amplitude of the derived stalk at each member of a *given* conservative
  family of points of that member's slice. The family is
  `AlgebraicGeometry.isConservativeFamilyOfPoints_uliftGeometricSitePoint_over`, the universe
  lifts of the geometric points of Tag 06VX passed to the slices: the points at which Tag 0DJJ
  is read live in the universe `max (u + 1) w r` of the module sections and not in the universe
  `u` of the scheme where the geometric points live;
* the covering it asks for: `AlgebraicGeometry.exists_covering_factors_smallEtaleBaseChange`
  produces one on an arbitrary object of the small étale site of `X` by base change along `f` of
  the covering the hypothesis supplies at the final object of the small étale site of `Y`;
* the comparison of the stalks that joins the two sides:
  `AlgebraicGeometry.smallEtalePullbackUpliftedEtaleFiberNatIso`, Tag 03Q1 for the ulifted fibre
  functor, between the two slice comparisons
  `AlgebraicGeometry.moduleSheafOverConstantCoefficientsOverFiberNatIso` of
  `StacksFrontier/AlgebraicGeometry/EtaleCohomology/ConstantCoefficientStalk.lean`, lifted factor by
  factor to the derived categories through
  `Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso` and
  `Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso`. The two sides state the
  stalk over the two fibres of the structure sheaves, identified only through `Λ`, so the bound
  crosses that identification by
  `StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_of_restrictScalars_iso`.

The producing half needs no statement of its own: it is Tag 0DJJ (1) on the slice over a member
of the covering, applied to the interval the hypothesis supplies there.

The source's own proof of Tag 0963 goes through Tag 03TT instead, reducing to finite complexes of
flat constructible sheaves; that route is not the one taken here. The direction (2) ⟹ (1) of
03TT is available, as
`Stacks.EtaleCohomology.constructibleFiniteTorDerivedCategoryOfConstructibleFlatComplex` of
`ConstructibleFlatFiniteTor.lean` in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/ConstructibleComplexes/`,
and taking the source's route would want two further things: the direction (1) ⟹ (2) of 03TT on
`Y`, and the stability of `AlgebraicGeometry.IsConstructibleFlatModuleSheaf` under inverse
image.

Only part (1) of Tag 0962 is treated here; part (2), for extension by zero along a quasi-compact
quasi-separated étale morphism, is in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ShriekFiniteTor`, together
with `Stacks.EtaleCohomology.constructibleFiniteTorDerivedCategoryEtale`, which states both
parts.

## References

* [Stacks Project, Tag 0962](https://stacks.math.columbia.edu/tag/0962)
* [Stacks Project, Tag 0963](https://stacks.math.columbia.edu/tag/0963)
* [Stacks Project, Tag 095Y](https://stacks.math.columbia.edu/tag/095Y)
* [Stacks Project, Tag 03TQ](https://stacks.math.columbia.edu/tag/03TQ)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 08H5](https://stacks.math.columbia.edu/tag/08H5)
* [Stacks Project, Tag 0DJJ](https://stacks.math.columbia.edu/tag/0DJJ)
* [Stacks Project, Tag 06VX](https://stacks.math.columbia.edu/tag/06VX)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u w r d

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
  GrothendieckTopology.hasSheafify_addCommGrpCat
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  AlgebraicGeometry.preservesFiniteLimits_smallEtaleSheafPullback_moduleCat
  AlgebraicGeometry.preservesFiniteColimits_smallEtaleSheafPullback_moduleCat
  AlgebraicGeometry.additive_smallEtaleSheafPullback_moduleCat


variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) (Λ : Type r) [CommRing Λ]
  [IsNoetherianRing Λ]
  [HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ)]
  [HasSheafify (SmallEtale.topology B Y.obj Y.property) (ModuleCat.{max (u + 1) w} Λ)]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{max (u + 1) w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{max (u + 1) w} Λ)]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, max (u + 1) w r}
    (constantCoefficientRingedSite.{u, max (u + 1) w, r} B X Λ))]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, max (u + 1) w r}
    (constantCoefficientRingedSite.{u, max (u + 1) w, r} B Y Λ))]
  [hSliceDerivedX : ∀ U : (constantCoefficientRingedSite.{u, max (u + 1) w, r} B X Λ).C,
    HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, max (u + 1) w r}
      ((constantCoefficientRingedSite.{u, max (u + 1) w, r} B X Λ).over U))]
  [hSliceDerivedY : ∀ U : (constantCoefficientRingedSite.{u, max (u + 1) w, r} B Y Λ).C,
    HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, max (u + 1) w r}
      ((constantCoefficientRingedSite.{u, max (u + 1) w, r} B Y Λ).over U))]
  [∀ U : (constantCoefficientRingedSite.{u, max (u + 1) w, r} B X Λ).C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) w r, max (u + 1) w r,
        max (u + 1) w r}
      ((constantCoefficientRingedSite.{u, max (u + 1) w, r} B X Λ).over U).O).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, max (u + 1) w, r} B X Λ).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) w r, max (u + 1) w r,
        max (u + 1) w r}
      ((constantCoefficientRingedSite.{u, max (u + 1) w, r} B X Λ).over U).O).obj M).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, max (u + 1) w, r} B X Λ).C)
    (K L : CochainComplex (RingedSite.Modules.{u + 1, u, max (u + 1) w r}
      ((constantCoefficientRingedSite.{u, max (u + 1) w, r} B X Λ).over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor
        ((constantCoefficientRingedSite.{u, max (u + 1) w, r} B X Λ).over U).O)
      (ComplexShape.up ℤ)]
  [∀ U : (constantCoefficientRingedSite.{u, max (u + 1) w, r} B Y Λ).C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) w r, max (u + 1) w r,
        max (u + 1) w r}
      ((constantCoefficientRingedSite.{u, max (u + 1) w, r} B Y Λ).over U).O).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, max (u + 1) w, r} B Y Λ).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) w r, max (u + 1) w r,
        max (u + 1) w r}
      ((constantCoefficientRingedSite.{u, max (u + 1) w, r} B Y Λ).over U).O).obj M).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, max (u + 1) w, r} B Y Λ).C)
    (K L : CochainComplex (RingedSite.Modules.{u + 1, u, max (u + 1) w r}
      ((constantCoefficientRingedSite.{u, max (u + 1) w, r} B Y Λ).over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor
        ((constantCoefficientRingedSite.{u, max (u + 1) w, r} B Y Λ).over U).O)
      (ComplexShape.up ℤ)]


attribute [local instance] Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory

attribute [local instance] AlgebraicGeometry.SheafOfModules.hasSheafify_commRingCat
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_commRingCat
  CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived

open Stacks.DerivedCategoryComparisons in
omit [IsNoetherianRing Λ] [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{max (u + 1) w} Λ)] in
/-- **The finite-Tor-dimension half of Stacks 0963**, at an arbitrary morphism `f : X ⟶ Y` of
`B.Scheme`. If the image under the change of coefficients of Tag 03TR of an object `K` of
`D(Y_étale, Λ)` locally has finite Tor dimension against the family `T` of derived tensor
products on the slices over `Y`, then the image of its derived inverse image `Lf^*K` locally has
finite Tor dimension against the family `T'` on the slices over `X`.

Both the hypothesis and the conclusion are the *local* condition of Tag 08FZ (3), so the
transport is a comparison of stalks on the slices and not a functor on modules. The covering of
an object `U'` of the small étale site of `X` that the conclusion asks for is the base change
along `f` of the covering the hypothesis supplies at the final object of the small étale site of
`Y`, by `AlgebraicGeometry.exists_covering_factors_smallEtaleBaseChange`; on each member it is
`Stacks.SheafOfModules.DerivedTensorProduct.locallyHasFiniteTorDimension_of_stalkwise_family`,
Tag 0DJJ (2) tested on the conservative family
`AlgebraicGeometry.isConservativeFamilyOfPoints_uliftGeometricSitePoint_over` of lifts to the
slice of the universe lifts of the geometric points of Tag 06VX, that establishes the local
condition, and the bound it asks for at such a point comes from Tag 0DJJ (1),
`Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitudeCanonical_derivedModuleFiber`, read on
the `Y` side at the image geometric point.

What carries the bound from the one side to the other is the comparison of the two derived
stalks: the slice comparison
`AlgebraicGeometry.moduleSheafOverConstantCoefficientsOverFiberNatIso` on both sides with
`AlgebraicGeometry.smallEtalePullbackUpliftedEtaleFiberNatIso` — Tag 03Q1 for the ulifted fibre
functor — in between, lifted factor by factor to the derived categories through
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso` and
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso`. The two sides state the stalk
over the two fibres of the structure sheaves, which are identified only through `Λ`, so the bound
crosses that identification by
`StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_of_restrictScalars_iso`.

Étaleness of `f` is nowhere used, which is what makes part (1) of Tag 0962 an instance of this
statement, at `f := U.obj.hom` for an object `U` of the small étale site. -/
@[sga "4½ Th_finitude 1.7" "Clause", sga "5 III 1.2" "partial", sga "5 IIIB 6.2" "partial"]
public theorem pullbackPreservesLocallyFiniteTorDimension
    (T : ∀ U : (constantCoefficientRingedSite.{u, max (u + 1) w, r} B Y Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) w r, d}
        ((constantCoefficientRingedSite.{u, max (u + 1) w, r} B Y Λ).over U))
    (T' : ∀ U : (constantCoefficientRingedSite.{u, max (u + 1) w, r} B X Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) w r, d}
        ((constantCoefficientRingedSite.{u, max (u + 1) w, r} B X Λ).over U)) :
    PullbackPreservesLocallyFiniteTorDimension.{u, w, r, d} B f Λ T T' := by
  let : HasProducts.{u} (ModuleCat.{max (u + 1) w} Λ) := fun _ => ModuleCat.hasLimitsOfShape
  let : LocallySmall.{max (u + 1) w r} (SmallEtale B X.obj X.property) :=
    ⟨fun _ _ => small_max.{max (u + 1) w r} _⟩
  let : LocallySmall.{max (u + 1) w r} (SmallEtale B Y.obj Y.property) :=
    ⟨fun _ _ => small_max.{max (u + 1) w r} _⟩
  intro K hK
  refine Stacks.SheafOfModules.DerivedTensorProduct.locallyHasFiniteTorDimension_of_stalkwise_family
    (Z := constantCoefficientRingedSite.{u, max (u + 1) w, r} B X Λ) T' _
    (t := fun V => Σ Φ : (ObjectProperty.ofObj (fun z : ↥X.obj =>
        (geometricSitePoint B X (.ofPoint X.obj z)).ulift.{max (u + 1) w r})).FullSubcategory,
      Φ.obj.fiber.obj V)
    (fun V ψ => ψ.1.obj.over ψ.2)
    (fun V => isConservativeFamilyOfPoints_uliftGeometricSitePoint_over.{u, max (u + 1) w, r}
      B X V) ?_
  intro U'
  obtain ⟨S₀, hS₀, hbound⟩ := hK (SmallEtale.final B Y.obj Y.property)
  obtain ⟨R, hR, hfac⟩ := exists_covering_factors_smallEtaleBaseChange B f
    (Sieve.generate S₀) hS₀ U'
  refine ⟨R.arrows, by rwa [Sieve.generate_sieve], ?_⟩
  intro V' g hg
  obtain ⟨V, q, hq, ⟨c⟩⟩ := hfac g hg
  obtain ⟨W, hVW, p, hp, -⟩ := hq
  obtain ⟨a, b, hab⟩ := hbound p hp
  refine ⟨a, b, ?_⟩
  rintro ⟨⟨Φ, hΦ⟩, x⟩
  obtain ⟨z, rfl⟩ := (ObjectProperty.ofObj_iff _ _).1 hΦ
  have y : ((geometricSitePoint B Y
      ((GeometricPoint.ofPoint X.obj z).map (B.inclusion.map f))).ulift.{max (u + 1) w
        r}).fiber.obj W :=
    ULift.up ((geometricPointFiberBaseChangeIso B f (GeometricPoint.ofPoint X.obj z)).inv.app W
      ((geometricPointFiber B X.obj X.property (GeometricPoint.ofPoint X.obj z)).map
        (c ≫ (smallEtaleBaseChange B f).map hVW) x.down))
  refine StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_of_restrictScalars_iso
    (constantCoefficientRingOverFiberEquiv.{u, max (u + 1) w, r} B X Λ
      ((geometricSitePoint B X (GeometricPoint.ofPoint X.obj z)).ulift.{max (u + 1) w r}) x)
    (constantCoefficientRingOverFiberEquiv.{u, max (u + 1) w, r} B Y Λ
      ((geometricSitePoint B Y
        ((GeometricPoint.ofPoint X.obj z).map (B.inclusion.map f))).ulift.{max (u + 1) w r}) y)
    ?_ a b
    (Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitudeCanonical_derivedModuleFiber
      (T W) _ a b hab _)
  haveI hFXa : (Stacks.sheafModuleFiberOfCommRing
      (((geometricSitePoint B X (GeometricPoint.ofPoint X.obj z)).ulift.{max (u + 1) w
        r}).over x)
      ((constantCoefficientRingedSite.{u, max (u + 1) w, r} B X Λ).over V').O).Additive :=
    inferInstance
  haveI hRXa : (ModuleCat.restrictScalars
      (constantCoefficientRingOverFiberEquiv.{u, max (u + 1) w, r} B X Λ
        ((geometricSitePoint B X (GeometricPoint.ofPoint X.obj z)).ulift.{max (u + 1) w r})
        x).toRingHom).Additive := inferInstance
  haveI hFYa : (Stacks.sheafModuleFiberOfCommRing
      (((geometricSitePoint B Y
          ((GeometricPoint.ofPoint X.obj z).map (B.inclusion.map f))).ulift.{max (u + 1) w
        r}).over y)
      ((constantCoefficientRingedSite.{u, max (u + 1) w, r} B Y Λ).over W).O).Additive :=
    inferInstance
  haveI hRYa : (ModuleCat.restrictScalars
      (constantCoefficientRingOverFiberEquiv.{u, max (u + 1) w, r} B Y Λ
        ((geometricSitePoint B Y
          ((GeometricPoint.ofPoint X.obj z).map (B.inclusion.map f))).ulift.{max (u + 1) w r})
        y).toRingHom).Additive := inferInstance
  haveI hlFXa : PreservesFiniteLimits (Stacks.sheafModuleFiberOfCommRing
      (((geometricSitePoint B X (GeometricPoint.ofPoint X.obj z)).ulift.{max (u + 1) w
        r}).over x)
      ((constantCoefficientRingedSite.{u, max (u + 1) w, r} B X Λ).over V').O) :=
    Stacks.preservesFiniteLimits_sheafModuleFiberOfCommRing
      (((geometricSitePoint B X (GeometricPoint.ofPoint X.obj z)).ulift.{max (u + 1) w
        r}).over x)
      ((constantCoefficientRingedSite.{u, max (u + 1) w, r} B X Λ).over V').O
  haveI hcFXa : PreservesFiniteColimits (Stacks.sheafModuleFiberOfCommRing
      (((geometricSitePoint B X (GeometricPoint.ofPoint X.obj z)).ulift.{max (u + 1) w
        r}).over x)
      ((constantCoefficientRingedSite.{u, max (u + 1) w, r} B X Λ).over V').O) :=
    Stacks.instPreservesFiniteColimitsSheafModuleFiberOfCommRing
      (((geometricSitePoint B X (GeometricPoint.ofPoint X.obj z)).ulift.{max (u + 1) w
        r}).over x)
      ((constantCoefficientRingedSite.{u, max (u + 1) w, r} B X Λ).over V').O
  haveI hlFYa : PreservesFiniteLimits (Stacks.sheafModuleFiberOfCommRing
      (((geometricSitePoint B Y
          ((GeometricPoint.ofPoint X.obj z).map (B.inclusion.map f))).ulift.{max (u + 1) w
        r}).over y)
      ((constantCoefficientRingedSite.{u, max (u + 1) w, r} B Y Λ).over W).O) :=
    Stacks.preservesFiniteLimits_sheafModuleFiberOfCommRing
      (((geometricSitePoint B Y
          ((GeometricPoint.ofPoint X.obj z).map (B.inclusion.map f))).ulift.{max (u + 1) w
        r}).over y)
      ((constantCoefficientRingedSite.{u, max (u + 1) w, r} B Y Λ).over W).O
  haveI hcFYa : PreservesFiniteColimits (Stacks.sheafModuleFiberOfCommRing
      (((geometricSitePoint B Y
          ((GeometricPoint.ofPoint X.obj z).map (B.inclusion.map f))).ulift.{max (u + 1) w
        r}).over y)
      ((constantCoefficientRingedSite.{u, max (u + 1) w, r} B Y Λ).over W).O) :=
    Stacks.instPreservesFiniteColimitsSheafModuleFiberOfCommRing
      (((geometricSitePoint B Y
          ((GeometricPoint.ofPoint X.obj z).map (B.inclusion.map f))).ulift.{max (u + 1) w
        r}).over y)
      ((constantCoefficientRingedSite.{u, max (u + 1) w, r} B Y Λ).over W).O
  letI : HasDerivedCategory.{d} (SheafOfModules.{max (u + 1) w r}
      ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, max (u + 1) w r}
        (constantCoefficientRingedSite.{u, max (u + 1) w, r} B X Λ).O).over V')) :=
    hSliceDerivedX V'
  letI : HasDerivedCategory.{d} (SheafOfModules.{max (u + 1) w r}
      ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, max (u + 1) w r}
        (constantCoefficientRingedSite.{u, max (u + 1) w, r} B Y Λ).O).over W)) :=
    hSliceDerivedY W
  exact mapDerivedCategoryCompIso₅₄
    ((smallEtaleBaseChange B f).sheafPullback (ModuleCat.{max (u + 1) w} Λ)
      (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property))
    (moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) w, r} B X Λ)
    (SheafOfModules.overFunctor.{max (u + 1) w r}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (constantCoefficientRingedSite.{u, max (u + 1) w, r} B X Λ).O) V')
    (Stacks.sheafModuleFiberOfCommRing
      (((geometricSitePoint B X (GeometricPoint.ofPoint X.obj z)).ulift.{max (u + 1) w
        r}).over x)
      ((constantCoefficientRingedSite.{u, max (u + 1) w, r} B X Λ).over V').O)
    (ModuleCat.restrictScalars
      (constantCoefficientRingOverFiberEquiv.{u, max (u + 1) w, r} B X Λ
        ((geometricSitePoint B X (GeometricPoint.ofPoint X.obj z)).ulift.{max (u + 1) w r})
        x).toRingHom)
    (moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) w, r} B Y Λ)
    (SheafOfModules.overFunctor.{max (u + 1) w r}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (constantCoefficientRingedSite.{u, max (u + 1) w, r} B Y Λ).O) W)
    (Stacks.sheafModuleFiberOfCommRing
      (((geometricSitePoint B Y
          ((GeometricPoint.ofPoint X.obj z).map (B.inclusion.map f))).ulift.{max (u + 1) w
        r}).over y)
      ((constantCoefficientRingedSite.{u, max (u + 1) w, r} B Y Λ).over W).O)
    (ModuleCat.restrictScalars
      (constantCoefficientRingOverFiberEquiv.{u, max (u + 1) w, r} B Y Λ
        ((geometricSitePoint B Y
          ((GeometricPoint.ofPoint X.obj z).map (B.inclusion.map f))).ulift.{max (u + 1) w r})
        y).toRingHom)
    (hF₄ := hFXa) (hF₅ := hRXa)
    (hG₃ := hFYa) (hG₄ := hRYa)
    (hlF₄ := hlFXa) (hcF₄ := hcFXa) (hlG₃ := hlFYa) (hcG₃ := hcFYa)
    ((Functor.isoWhiskerLeft
        ((smallEtaleBaseChange B f).sheafPullback (ModuleCat.{max (u + 1) w} Λ)
          (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property))
        (moduleSheafOverConstantCoefficientsOverFiberNatIso.{u, max (u + 1) w, r} B X Λ
          ((geometricSitePoint B X (GeometricPoint.ofPoint X.obj z)).ulift.{max (u + 1) w r})
          x)).symm ≪≫
      smallEtalePullbackUpliftedEtaleFiberNatIso.{u, max (u + 1) w, r} B Λ f
        (GeometricPoint.ofPoint X.obj z) ≪≫
      moduleSheafOverConstantCoefficientsOverFiberNatIso.{u, max (u + 1) w, r} B Y Λ
        ((geometricSitePoint B Y
          ((GeometricPoint.ofPoint X.obj z).map (B.inclusion.map f))).ulift.{max (u + 1) w r})
        y)
    K

/-- **Stacks 0963.** Let `Λ` be a Noetherian ring and `f : X ⟶ Y` a morphism of schemes. Then
`Lf^*` maps `D_{ctf}(Y_étale, Λ)` into `D_{ctf}(X_étale, Λ)`: if an object `K` of the derived
category of étale sheaves of `Λ`-modules on `Y` has constructible cohomology sheaves and its image
under the change of coefficients of Tag 03TR locally has finite Tor dimension against `T`, then
its derived inverse image `Lf^*K` has constructible cohomology sheaves and its image locally has
finite Tor dimension against `T'`.

The membership condition is that of Tag 03TQ,
`Stacks.EtaleCohomology.ConstructibleFiniteTorDerivedCategory`. Constructibility of the
cohomology sheaves of `Lf^*K` is Tag 095Y,
`Stacks.EtaleCohomology.isConstructible_derivedPullback`; locally finite Tor dimension of its
image is
`Stacks.EtaleCohomology.pullbackPreservesLocallyFiniteTorDimension`. -/
@[stacks 0963 "the constructible-cohomology half by Tag 095Y, the finite-Tor-dimension half by \
Tag 0DJJ read at the stalks on the slices of the constant coefficient ringed sites",
  sga "5 III 1.2" "more general",
  sga "5 IIIB 6.2" "special case"]
public theorem isConstructible_and_locallyHasFiniteTorDimension_derivedPullback
    (T : ∀ U : (constantCoefficientRingedSite.{u, max (u + 1) w, r} B Y Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) w r, d}
        ((constantCoefficientRingedSite.{u, max (u + 1) w, r} B Y Λ).over U))
    (T' : ∀ U : (constantCoefficientRingedSite.{u, max (u + 1) w, r} B X Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) w r, d}
        ((constantCoefficientRingedSite.{u, max (u + 1) w, r} B X Λ).over U))
    (K : DerivedCategory (Sheaf (SmallEtale.topology B Y.obj Y.property)
      (ModuleCat.{max (u + 1) w} Λ)))
    (hK : IsConstructible B Y Λ K ∧
      Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension
        (X := constantCoefficientRingedSite.{u, max (u + 1) w, r} B Y Λ) T
        ((moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) w, r} B Y
          Λ).mapDerivedCategory.obj K)) :
    IsConstructible B X Λ
        (((smallEtaleBaseChange B f).sheafPullback (ModuleCat.{max (u + 1) w} Λ)
          (SmallEtale.topology B Y.obj Y.property)
          (SmallEtale.topology B X.obj X.property)).mapDerivedCategory.obj K) ∧
      Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension
        (X := constantCoefficientRingedSite.{u, max (u + 1) w, r} B X Λ) T'
        ((moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) w, r} B X
          Λ).mapDerivedCategory.obj
          (((smallEtaleBaseChange B f).sheafPullback (ModuleCat.{max (u + 1) w} Λ)
            (SmallEtale.topology B Y.obj Y.property)
            (SmallEtale.topology B X.obj X.property)).mapDerivedCategory.obj K)) :=
  ⟨isConstructible_derivedPullback B Λ f K hK.1,
    pullbackPreservesLocallyFiniteTorDimension.{u, w, r, d} B f Λ T T' K hK.2⟩

/-- **Stacks 0963, for the full subcategory.** Derived inverse image along a morphism
`f : X ⟶ Y` of schemes, as a map from `D_{ctf}(Y_étale, Λ)` to `D_{ctf}(X_étale, Λ)`: the
underlying object of the image of `K` is `Lf^*K`, by
`Stacks.EtaleCohomology.constructibleFiniteTorDerivedCategoryPullback_unconditional_obj`, and its
membership is
`Stacks.EtaleCohomology.isConstructible_and_locallyHasFiniteTorDimension_derivedPullback`, where
Tag 0963 is registered.

`Stacks.EtaleCohomology.constructibleFiniteTorDerivedCategoryPullback` is the same map taking the
finite-Tor-dimension half as a hypothesis, which this one discharges. -/
@[sga "5 III 1.2" "more general",
  sga "5 IIIB 6.2" "special case"]
public def constructibleFiniteTorDerivedCategoryPullback_unconditional
    (T : ∀ U : (constantCoefficientRingedSite.{u, max (u + 1) w, r} B Y Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) w r, d}
        ((constantCoefficientRingedSite.{u, max (u + 1) w, r} B Y Λ).over U))
    (T' : ∀ U : (constantCoefficientRingedSite.{u, max (u + 1) w, r} B X Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) w r, d}
        ((constantCoefficientRingedSite.{u, max (u + 1) w, r} B X Λ).over U))
    (K : ConstructibleFiniteTorDerivedCategory.{u, max (u + 1) w, r, d} B Y Λ T) :
    ConstructibleFiniteTorDerivedCategory.{u, max (u + 1) w, r, d} B X Λ T' :=
  ⟨constructibleDerivedCategoryPullback B Λ f K.obj,
    pullbackPreservesLocallyFiniteTorDimension.{u, w, r, d} B f Λ T T' K.obj.obj K.property⟩

/-- The underlying object of
`Stacks.EtaleCohomology.constructibleFiniteTorDerivedCategoryPullback_unconditional` at `K` is
the derived inverse image `Lf^*K` of the underlying object of `K`. -/
public theorem constructibleFiniteTorDerivedCategoryPullback_unconditional_obj
    (T : ∀ U : (constantCoefficientRingedSite.{u, max (u + 1) w, r} B Y Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) w r, d}
        ((constantCoefficientRingedSite.{u, max (u + 1) w, r} B Y Λ).over U))
    (T' : ∀ U : (constantCoefficientRingedSite.{u, max (u + 1) w, r} B X Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) w r, d}
        ((constantCoefficientRingedSite.{u, max (u + 1) w, r} B X Λ).over U))
    (K : ConstructibleFiniteTorDerivedCategory.{u, max (u + 1) w, r, d} B Y Λ T) :
    (constructibleFiniteTorDerivedCategoryPullback_unconditional.{u, w, r, d} B f Λ T T'
        K).obj.obj =
      ((smallEtaleBaseChange B f).sheafPullback (ModuleCat.{max (u + 1) w} Λ)
        (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B X.obj X.property)).mapDerivedCategory.obj K.obj.obj :=
  rfl

/-- **Part (1) of Stacks 0962.** Let `Λ` be a Noetherian ring and `f : X ⟶ Y` an étale morphism
of schemes — the source's `j : U ⟶ X`, with `X` here in the rôle of its `U` and `Y` in the rôle
of its `X`. The restriction along `f` of an object of `D_{ctf}(Y_étale, Λ)` is an object of
`D_{ctf}(X_étale, Λ)`.

Restriction along `f` is the inverse image along `f`: the two are identified by
`AlgebraicGeometry.smallInverseImageIsoPostcomposePushforward`, both being left adjoint to base
change along `f`. The statement is therefore the one of
`Stacks.EtaleCohomology.constructibleFiniteTorDerivedCategoryPullback_unconditional` at an étale
morphism, and the étaleness of `f` is not used: both halves hold along an arbitrary morphism, the
first by Tag 095Y and the second by
`Stacks.EtaleCohomology.pullbackPreservesLocallyFiniteTorDimension`.

No tag is attached: this is one of the two parts of Tag 0962, and the tag is registered on
`Stacks.EtaleCohomology.constructibleFiniteTorDerivedCategoryEtale` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ShriekFiniteTor`, whose
statement has both parts and whose first part is this one with the restriction spelled as the
restriction functor of Tag 03S3 rather than as the inverse image. -/
@[sga "5 III 1.2" "partial", sga "5 IIIB 6.2" "special case"]
public def constructibleFiniteTorDerivedCategoryEtalePullback_unconditional
    [Etale (B.inclusion.map f)]
    (T : ∀ U : (constantCoefficientRingedSite.{u, max (u + 1) w, r} B Y Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) w r, d}
        ((constantCoefficientRingedSite.{u, max (u + 1) w, r} B Y Λ).over U))
    (T' : ∀ U : (constantCoefficientRingedSite.{u, max (u + 1) w, r} B X Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) w r, d}
        ((constantCoefficientRingedSite.{u, max (u + 1) w, r} B X Λ).over U))
    (K : ConstructibleFiniteTorDerivedCategory.{u, max (u + 1) w, r, d} B Y Λ T) :
    ConstructibleFiniteTorDerivedCategory.{u, max (u + 1) w, r, d} B X Λ T' :=
  constructibleFiniteTorDerivedCategoryPullback_unconditional.{u, w, r, d} B f Λ T T' K


end Stacks.EtaleCohomology

end
