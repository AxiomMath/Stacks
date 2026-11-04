module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFullyFaithful
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.PullbackFiniteTorStalkwise
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.RestrictionExtensionByZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ShriekBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModuleExtensionByZeroStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleEnoughAffineObjects
public import StacksFrontier.Homology.TorAmplitude.FlatRepresentativeCoproduct
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Restriction and extension by zero of constructible complexes of finite Tor dimension

Let `Λ` be a Noetherian ring, let `X` be a scheme and let `U` be an object of the small étale
site of `X`, that is an étale morphism `j : U ⟶ X`. Tag 0962 asserts two things: that `K|_U`
lies in `D_ctf(U_étale, Λ)` when `K` lies in `D_ctf(X_étale, Λ)`, and that `j_! M` lies in
`D_ctf(X_étale, Λ)` when `M` lies in `D_ctf(U_étale, Λ)` and `j` is quasi-compact and
quasi-separated.

Membership of `D_ctf` is the conjunction of two conditions: constructibility of the cohomology
sheaves, and locally finite Tor dimension of the image of the complex in the derived category of
modules over the constant coefficient ring sheaf. The constructibility halves are the two parts
of Tag 095X. The finite-Tor-dimension half of part (1) is that of Tag 0963, which holds along an
arbitrary morphism of schemes and is instantiated at the structure morphism of `U`.

The finite-Tor-dimension half of part (2) is read at the stalks. On the slice over an object
`V'` of the small étale site of `X`, finite Tor dimension is a bound on the Tor amplitude of the
derived stalks, by Tag 0DJJ; and the stalk of `j_! M` at a geometric point `x` of `V'` is the
direct sum of the stalks of `M` at the lifts of `x` to `U`, by Tag 03S5. A direct sum of
complexes of Tor amplitude in `[a, b]` has Tor amplitude in `[a, b]`, so what is needed is one
interval bounding the stalks of `M` at all the points of `U` over `V'`. Those points are the
points of `W = U ×_X V'`, and when `V'` is affine and `j` quasi-compact, `W` is quasi-compact:
the covering of `W` on whose members `M` has finite Tor dimension then has a finite refinement,
and the largest of the finitely many intervals bounds every stalk.

## Main definitions

* `Stacks.EtaleCohomology.ExtensionByZeroPreservesLocallyFiniteTorDimension`: the
  finite-Tor-dimension half of Tag 0962 part (2) for a fixed étale object.

## Main results

* `Stacks.EtaleCohomology.extensionByZeroPreservesLocallyFiniteTorDimension`: **the
  finite-Tor-dimension half of Tag 0962, part (2)**, for a quasi-compact `j`.
* `Stacks.EtaleCohomology.constructibleFiniteTorDerivedCategoryRestriction`: **Tag 0962, part
  (1)**, with `K|_U` spelled as the restriction functor of Tag 03S3.
* `Stacks.EtaleCohomology.constructibleFiniteTorDerivedCategoryExtensionByZero`: **Tag 0962,
  part (2)**.
* `Stacks.EtaleCohomology.constructibleFiniteTorDerivedCategoryEtale`: **Tag 0962**, both parts
  in one declaration.

## Implementation notes

`D_ctf(X_étale, Λ)` is `Stacks.EtaleCohomology.ConstructibleFiniteTorDerivedCategory`, as in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.PullbackFiniteTor`; Tor
amplitude is measured against a *given* family of derived tensor products on the slices, so the
subcategories over `X` and over `U` are indexed by two independent such families, `T` over `X`
and `T'` over `U`.

The étale morphism is presented as an object `U` of the small étale site of `X` rather than as a
morphism of schemes with an `AlgebraicGeometry.Etale` instance, because that is the shape
`AlgebraicGeometry.moduleExtensionByZero` of Tag 03S3 is defined at; its étaleness is `U.property`
and the two presentations are interchangeable. The coefficient universe is the one extension by
zero forces, `ModuleCat.{max (u + 1) r} Λ`, the universe in which the coproducts defining the
presheaf extension by zero exist. That is the universe `max (u + 1) w` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.PullbackFiniteTor` at
`w = r`, so the statements of that file are available here.

Part (1) is proved in the restriction spelling: the restriction functor and the inverse image
along `j` are isomorphic by `AlgebraicGeometry.moduleRestrictionIsoSmallInverseImage`, which is
Tag 03S3 part (3), and `Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso` carries
that isomorphism to the unbounded derived categories, along which locally finite Tor dimension
transports by `Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension.of_iso`.

The points at which the stalks are read in part (2) are the universe lifts of the points of the
small étale sites attached to the geometric points, as in part (1): Tag 0DJJ is read at points
whose fibres live in the universe `max (u + 1) r` of the module sections. The stalk formula at
those points is `AlgebraicGeometry.moduleExtensionByZeroSheafFiberIso`; the passage from the
stalk of the sheaf of `Λ`-modules to the stalk of the associated sheaf of modules over the
constant coefficient ring sheaf is
`AlgebraicGeometry.moduleSheafOverConstantCoefficientsOverFiberNatIso` on both sides; and the
direct sum is handled by
`StacksDraft.TorAmplitude.hasFlatRepresentative_mapDerivedCategory_of_iso_sigma`, through flat
representatives (Tag 0654). The source's own proof reduces to an affine base and uses Tag 03TT
to pass to finite complexes of flat constructible sheaves; the stalkwise route is taken here
instead, and only the quasi-compactness of `j` is used in the finite-Tor-dimension half, its
quasi-separatedness entering through the constructibility half.

## References

* [Stacks Project, Tag 0962](https://stacks.math.columbia.edu/tag/0962)
* [Stacks Project, Tag 095X](https://stacks.math.columbia.edu/tag/095X)
* [Stacks Project, Tag 0963](https://stacks.math.columbia.edu/tag/0963)
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
* [Stacks Project, Tag 03S5](https://stacks.math.columbia.edu/tag/03S5)
* [Stacks Project, Tag 03TQ](https://stacks.math.columbia.edu/tag/03TQ)
* [Stacks Project, Tag 0DJJ](https://stacks.math.columbia.edu/tag/0DJJ)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u r d

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

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (U : SmallEtale B X.obj X.property)
  (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]
  [HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)]
  [HasSheafify (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
    (ModuleCat.{max (u + 1) r} Λ)]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{max (u + 1) r} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{max (u + 1) r} Λ)]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, max (u + 1) r}
    (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ))]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, max (u + 1) r}
    (constantCoefficientRingedSite.{u, max (u + 1) r, r} B U.obj.left Λ))]
  [hSliceDerivedX : ∀ V : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C,
    HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over V))]
  [hSliceDerivedU : ∀ V : (constantCoefficientRingedSite.{u, max (u + 1) r, r}
      B U.obj.left Λ).C,
    HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B U.obj.left Λ).over V))]
  [∀ V : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r, max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over V).O).Additive]
  [∀ (V : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r, max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over V).O).obj M).Additive]
  [∀ (V : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C)
    (K L : CochainComplex (RingedSite.Modules.{u + 1, u, max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over V)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over V).O)
      (ComplexShape.up ℤ)]
  [∀ V : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B U.obj.left Λ).C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r, max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B U.obj.left Λ).over V).O).Additive]
  [∀ (V : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B U.obj.left Λ).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r, max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B U.obj.left Λ).over V).O).obj
        M).Additive]
  [∀ (V : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B U.obj.left Λ).C)
    (K L : CochainComplex (RingedSite.Modules.{u + 1, u, max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B U.obj.left Λ).over V)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B U.obj.left Λ).over V).O)
      (ComplexShape.up ℤ)]

attribute [local instance] Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory

/-- **The finite-Tor-dimension half of Tag 0962, part (2)** for the étale object `U` of the
small étale site of `X`: whenever the image of an object of `D(U_étale, Λ)` under the change of
coefficients of Tag 03TR locally has finite Tor dimension against the family `T'` of derived
tensor products on the slices over `U`, so does the image of its extension by zero against the
family `T` on the slices over `X`.

`Stacks.EtaleCohomology.extensionByZeroPreservesLocallyFiniteTorDimension` proves it whenever
`j` is quasi-compact. -/
public def ExtensionByZeroPreservesLocallyFiniteTorDimension
    (T : ∀ V : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) r, d}
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over V))
    (T' : ∀ V : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B U.obj.left Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) r, d}
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B U.obj.left Λ).over V)) : Prop :=
  ∀ M : DerivedCategory (Sheaf (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
      (ModuleCat.{max (u + 1) r} Λ)),
    Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension
        (X := constantCoefficientRingedSite.{u, max (u + 1) r, r} B U.obj.left Λ) T'
        ((moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) r, r} B U.obj.left
          Λ).mapDerivedCategory.obj M) →
      Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension
        (X := constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ) T
        ((moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) r, r} B X
          Λ).mapDerivedCategory.obj
          ((moduleExtensionByZero.{u, r} B X.obj X.property U Λ).mapDerivedCategory.obj M))

attribute [local instance] AlgebraicGeometry.SheafOfModules.hasSheafify_commRingCat
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_commRingCat
  CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

open Stacks.DerivedCategoryComparisons StacksDraft.TorAmplitude in
/-- **The finite-Tor-dimension half of Stacks 0962, part (2).** Let `j : U ⟶ X` be étale and
quasi-compact. If the image under the change of coefficients of Tag 03TR of an object `M` of
`D(U_étale, Λ)` locally has finite Tor dimension against the family `T'` of derived tensor
products on the slices over `U`, then the image of its extension by zero `j_! M` locally has
finite Tor dimension against the family `T` on the slices over `X`.

The covering of an object `U'` of the small étale site of `X` is a covering by affine objects
`V'`, by `AlgebraicGeometry.SmallEtale.hasEnoughObjects_isAffine`. Over such a `V'` the base
change `W = U ×_X V'` is quasi-compact, `j` being quasi-compact; so the covering of `W` which the
hypothesis on `M` supplies has a finite refinement, by
`AlgebraicGeometry.SmallEtale.isQuasiCompactObject_of_compactSpace`, and one interval `[a, b]`
contains the Tor amplitudes of `M` on all of its members. Every point of the small étale site of
`U` attached to a lift of a geometric point of `V'` lies over `W`, hence over one of those
members, where Tag 0DJJ (1) bounds the derived stalk of `M` by `[a, b]`. By Tag 03S5 for sheaves
of modules, `AlgebraicGeometry.moduleExtensionByZeroSheafFiberIso`, the derived stalk of `j_! M`
at a geometric point of `V'` is the direct sum of the derived stalks of `M` at the lifts of that
point to `U`, so it has a flat representative in `[a, b]` by
`StacksDraft.TorAmplitude.hasFlatRepresentative_mapDerivedCategory_of_iso_sigma`; Tag 0DJJ (2),
read on the slice over `V'` through
`Stacks.SheafOfModules.DerivedTensorProduct.locallyHasFiniteTorDimension_of_stalkwise_family`,
concludes. -/
@[sga "4½ Th_finitude 1.7" "Clause, special case", sga "5 IIIB 6.2" "partial"]
public theorem extensionByZeroPreservesLocallyFiniteTorDimension
    (hqc : QuasiCompact (B.inclusion.map U.obj.hom))
    (T : ∀ V : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) r, d}
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over V))
    (T' : ∀ V : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B U.obj.left Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) r, d}
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B U.obj.left Λ).over V)) :
    ExtensionByZeroPreservesLocallyFiniteTorDimension.{u, r, d} B X U Λ T T' := by
  letI : LocallySmall.{max (u + 1) r} (SmallEtale B X.obj X.property) :=
    ⟨fun _ _ => small_max.{max (u + 1) r} _⟩
  letI : LocallySmall.{max (u + 1) r} (SmallEtale B U.obj.left.obj U.obj.left.property) :=
    ⟨fun _ _ => small_max.{max (u + 1) r} _⟩
  haveI : AB5OfSize.{max (u + 1) r, max (u + 1) r} (ModuleCat.{max (u + 1) r} Λ) :=
    ⟨fun J _ _ => HasExactColimitsOfShape.domain_of_functor J
      (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r})⟩
  intro M hM
  refine Stacks.SheafOfModules.DerivedTensorProduct.locallyHasFiniteTorDimension_of_stalkwise_family
    (Z := constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ) T _
    (t := fun V => Σ Φ : (ObjectProperty.ofObj (fun z : ↥X.obj =>
        (geometricSitePoint B X (.ofPoint X.obj z)).ulift.{max (u + 1) r})).FullSubcategory,
      Φ.obj.fiber.obj V)
    (fun V ψ => ψ.1.obj.over ψ.2)
    (fun V => isConservativeFamilyOfPoints_uliftGeometricSitePoint_over.{u, max (u + 1) r, r}
      B X V) ?_
  intro U'
  obtain ⟨I, Yc, fc, hcov, haff⟩ := SmallEtale.hasEnoughObjects_isAffine B X.obj X.property U'
  refine ⟨Presieve.ofArrows Yc fc, hcov, ?_⟩
  rintro _ _ ⟨i⟩
  -- the base change `W = V' ×_X U`, an object of the small étale site of `U`
  have hP := isPullback_smallEtaleBaseChange B U.obj.hom (Yc i)
  set W := (smallEtaleBaseChange B U.obj.hom).obj (Yc i) with hWdef
  have hWc : CompactSpace ((SmallEtale.toScheme B U.obj.left.obj U.obj.left.property).obj W) := by
    haveI : IsAffine (B.inclusion.obj (Yc i).obj.left) := haff i
    have hq : QuasiCompact (B.inclusion.map (Limits.pullback.fst (Yc i).obj.hom U.obj.hom)) :=
      MorphismProperty.of_isPullback hP.flip hqc
    exact @QuasiCompact.compactSpace_of_compactSpace _ _ _ hq _
  obtain ⟨S, hS, hbound⟩ := hM W
  let 𝒰 : PreZeroHypercover.{u + 1} W :=
    { I₀ := Σ Z : SmallEtale B U.obj.left.obj U.obj.left.property, {g : Z ⟶ W // S g}
      X := fun k => k.1
      f := fun k => k.2.1 }
  have h𝒰 : 𝒰.sieve₀ ∈ SmallEtale.topology B U.obj.left.obj U.obj.left.property W := by
    refine GrothendieckTopology.superset_covering _ ?_ hS
    rw [Sieve.generate_le_iff]
    intro Z g hg
    exact Sieve.ofArrows_mk 𝒰.X 𝒰.f (⟨Z, g, hg⟩ : 𝒰.I₀)
  obtain ⟨𝒱, φ, h𝒱, hfin⟩ := SmallEtale.isQuasiCompactObject_of_compactSpace B
    U.obj.left.obj U.obj.left.property W hWc 𝒰 h𝒰
  choose aI bI hI using fun k : 𝒰.I₀ => hbound k.2.1 k.2.2
  obtain ⟨a, ha⟩ := (hfin.image aI).bddBelow
  obtain ⟨b, hb⟩ := (hfin.image bI).bddAbove
  refine ⟨a, b, ?_⟩
  rintro ⟨⟨Φ, hΦ⟩, x⟩
  obtain ⟨z, rfl⟩ := (ObjectProperty.ofObj_iff _ _).1 hΦ
  refine hasTorAmplitudeCanonical_of_hasFlatRepresentative_restrictScalars.{r, max (u + 1) r}
    (constantCoefficientRingOverFiberEquiv.{u, max (u + 1) r, r} B X Λ
      ((geometricSitePoint B X (GeometricPoint.ofPoint X.obj z)).ulift.{max (u + 1) r}) x) ?_
  haveI hFXa : (Stacks.sheafModuleFiberOfCommRing
      (((geometricSitePoint B X (GeometricPoint.ofPoint X.obj z)).ulift.{max (u + 1) r}).over x)
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over (Yc i)).O).Additive :=
    inferInstance
  haveI hlFXa : PreservesFiniteLimits (Stacks.sheafModuleFiberOfCommRing
      (((geometricSitePoint B X (GeometricPoint.ofPoint X.obj z)).ulift.{max (u + 1) r}).over x)
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over (Yc i)).O) :=
    Stacks.preservesFiniteLimits_sheafModuleFiberOfCommRing
      (((geometricSitePoint B X (GeometricPoint.ofPoint X.obj z)).ulift.{max (u + 1) r}).over x)
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over (Yc i)).O
  haveI hcFXa : PreservesFiniteColimits (Stacks.sheafModuleFiberOfCommRing
      (((geometricSitePoint B X (GeometricPoint.ofPoint X.obj z)).ulift.{max (u + 1) r}).over x)
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over (Yc i)).O) :=
    Stacks.instPreservesFiniteColimitsSheafModuleFiberOfCommRing
      (((geometricSitePoint B X (GeometricPoint.ofPoint X.obj z)).ulift.{max (u + 1) r}).over x)
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over (Yc i)).O
  letI : HasDerivedCategory.{d} (SheafOfModules.{max (u + 1) r}
      ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, max (u + 1) r}
        (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).O).over (Yc i))) :=
    hSliceDerivedX (Yc i)
  haveI hGa : ∀ p : ULift.{max (u + 1) r}
      (geometricPointLifts B X.obj X.property U (GeometricPoint.ofPoint X.obj z)),
      ((uliftLiftedSitePoint.{u, r} B X U (GeometricPoint.ofPoint X.obj z) p.down).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).Additive :=
    fun _ => Functor.additive_of_preserves_binary_products _
  haveI hΦa : (((geometricSitePoint B X (GeometricPoint.ofPoint X.obj z)).ulift.{max (u + 1) r}
      ).sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)).Additive :=
    Functor.additive_of_preserves_binary_products _
  refine hasFlatRepresentative_of_iso
    (mapDerivedCategoryCompIso₅₂
      (moduleExtensionByZero.{u, r} B X.obj X.property U Λ)
      (moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) r, r} B X Λ)
      (SheafOfModules.overFunctor.{max (u + 1) r}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).O) (Yc i))
      (Stacks.sheafModuleFiberOfCommRing
        (((geometricSitePoint B X (GeometricPoint.ofPoint X.obj z)).ulift.{max (u + 1) r}).over x)
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over (Yc i)).O)
      (ModuleCat.restrictScalars
        (constantCoefficientRingOverFiberEquiv.{u, max (u + 1) r, r} B X Λ
          ((geometricSitePoint B X (GeometricPoint.ofPoint X.obj z)).ulift.{max (u + 1) r})
          x).toRingHom)
      (moduleExtensionByZero.{u, r} B X.obj X.property U Λ)
      (((geometricSitePoint B X (GeometricPoint.ofPoint X.obj z)).ulift.{max (u + 1) r}
        ).sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)) (hF₄ := hFXa)
      (hlF₄ := hlFXa) (hcF₄ := hcFXa) (hG₂ := hΦa)
      ((Functor.isoWhiskerLeft (moduleExtensionByZero.{u, r} B X.obj X.property U Λ)
        (moduleSheafOverConstantCoefficientsOverFiberNatIso.{u, max (u + 1) r, r} B X Λ
          ((geometricSitePoint B X (GeometricPoint.ofPoint X.obj z)).ulift.{max (u + 1) r})
          x)).symm ≪≫
        Functor.isoWhiskerLeft (moduleExtensionByZero.{u, r} B X.obj X.property U Λ)
          (upliftedEtaleFiberFunctorIso.{u, r} B X Λ
            ((geometricSitePoint B X (GeometricPoint.ofPoint X.obj z)).ulift.{max (u + 1) r})))
      M).symm ?_
  refine hasFlatRepresentative_mapDerivedCategory_of_iso_sigma
    (fun p : ULift.{max (u + 1) r}
        (geometricPointLifts B X.obj X.property U (GeometricPoint.ofPoint X.obj z)) =>
      (uliftLiftedSitePoint.{u, r} B X U (GeometricPoint.ofPoint X.obj z) p.down).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)) _
    (moduleExtensionByZeroSheafFiberIso.{u, r} B X U (GeometricPoint.ofPoint X.obj z) Λ) M ?_
  intro p
  -- a lift of the geometric point to the base change `W`, from the lifts to `Yc i` and to `U`
  let q : (geometricPointFiber B U.obj.left.obj U.obj.left.property
      (geometricPointOfLift B X.obj X.property U (GeometricPoint.ofPoint X.obj z) p.down)).obj W :=
    ⟨hP.lift x.down.1 p.down.1 (x.down.2.trans p.down.2.symm), hP.lift_snd _ _ _⟩
  obtain ⟨Z, g, hg, y₁, -⟩ :=
    (uliftLiftedSitePoint.{u, r} B X U (GeometricPoint.ofPoint X.obj z) p.down).jointly_surjective
      _ h𝒱 (ULift.up q)
  obtain ⟨m, c, -⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
  set Ψ := uliftLiftedSitePoint.{u, r} B X U (GeometricPoint.ofPoint X.obj z) p.down with hΨ
  set k := φ.s₀ m with hk
  let y : Ψ.fiber.obj k.1 := Ψ.fiber.map (φ.h₀ m) (Ψ.fiber.map c y₁)
  have hab := (hI k).mono (ha ⟨k, ⟨m, rfl⟩, rfl⟩) (hb ⟨k, ⟨m, rfl⟩, rfl⟩)
  have hcan := Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitudeCanonical_derivedModuleFiber
    (T' k.1) _ a b hab (Ψ.over y)
  have hflat := hasFlatRepresentative_restrictScalars_of_ringEquiv
    (constantCoefficientRingOverFiberEquiv.{u, max (u + 1) r, r} B U.obj.left Λ Ψ y) _ a b
    ((hasTorAmplitudeCanonical_iff_hasFlatRepresentative _ _ a b).1 hcan)
  haveI hFUa : (Stacks.sheafModuleFiberOfCommRing (Ψ.over y)
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B U.obj.left Λ).over k.1).O).Additive :=
    inferInstance
  haveI hlFUa : PreservesFiniteLimits (Stacks.sheafModuleFiberOfCommRing (Ψ.over y)
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B U.obj.left Λ).over k.1).O) :=
    Stacks.preservesFiniteLimits_sheafModuleFiberOfCommRing (Ψ.over y)
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B U.obj.left Λ).over k.1).O
  haveI hcFUa : PreservesFiniteColimits (Stacks.sheafModuleFiberOfCommRing (Ψ.over y)
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B U.obj.left Λ).over k.1).O) :=
    Stacks.instPreservesFiniteColimitsSheafModuleFiberOfCommRing (Ψ.over y)
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B U.obj.left Λ).over k.1).O
  letI : HasDerivedCategory.{d} (SheafOfModules.{max (u + 1) r}
      ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, max (u + 1) r}
        (constantCoefficientRingedSite.{u, max (u + 1) r, r} B U.obj.left Λ).O).over k.1)) :=
    hSliceDerivedU k.1
  exact hasFlatRepresentative_of_iso
    (mapDerivedCategoryCompIso₄₁
      (moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) r, r} B U.obj.left Λ)
      (SheafOfModules.overFunctor.{max (u + 1) r}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (constantCoefficientRingedSite.{u, max (u + 1) r, r} B U.obj.left Λ).O) k.1)
      (Stacks.sheafModuleFiberOfCommRing (Ψ.over y)
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B U.obj.left Λ).over k.1).O)
      (ModuleCat.restrictScalars
        (constantCoefficientRingOverFiberEquiv.{u, max (u + 1) r, r} B U.obj.left Λ Ψ
          y).toRingHom)
      (Ψ.sheafFiber (A := ModuleCat.{max (u + 1) r} Λ))
      (hF₃ := hFUa) (hlF₃ := hlFUa) (hcF₃ := hcFUa)
      ((moduleSheafOverConstantCoefficientsOverFiberNatIso.{u, max (u + 1) r, r} B U.obj.left Λ
          Ψ y).symm ≪≫
        upliftedEtaleFiberFunctorIso.{u, r} B U.obj.left Λ Ψ) M) hflat

/-- **Stacks 0962, part (1)**, with `K|_U` spelled as the restriction functor of Tag 03S3. The
restriction of an object of `D_ctf(X_étale, Λ)` is an object of `D_ctf(U_étale, Λ)`.

Constructibility of the cohomology sheaves of `K|_U` is Tag 095X part (1),
`Stacks.EtaleCohomology.isConstructible_derivedRestriction`. Locally finite Tor dimension is
`Stacks.EtaleCohomology.pullbackPreservesLocallyFiniteTorDimension`, the finite-Tor-dimension
half of Tag 0963 — which holds along an arbitrary morphism of `B.Scheme` and is used here at
`f := U.obj.hom` — read on the inverse image along `j` and transported to the restriction along
the isomorphism of Tag 03S3 part (3). Nothing is assumed. -/
@[sga "5 III 1.2" "special case", sga "5 IIIB 6.2" "special case"]
public def constructibleFiniteTorDerivedCategoryRestriction
    (T : ∀ V : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) r, d}
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over V))
    (T' : ∀ V : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B U.obj.left Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) r, d}
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B U.obj.left Λ).over V))
    (K : ConstructibleFiniteTorDerivedCategory.{u, max (u + 1) r, r, d} B X Λ T) :
    ConstructibleFiniteTorDerivedCategory.{u, max (u + 1) r, r, d} B U.obj.left Λ T' :=
  ⟨⟨(moduleRestriction.{u, r, max (u + 1) r} B X.obj X.property U Λ).mapDerivedCategory.obj
      K.obj.obj,
    isConstructible_derivedRestriction B Λ X U K.obj.obj K.obj.property⟩,
    Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension.of_iso T'
      ((moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) r, r} B U.obj.left
        Λ).mapDerivedCategory.mapIso
        ((Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso
          (smallEtaleModuleInverseImage B Λ X U)
          (moduleRestriction.{u, r, max (u + 1) r} B X.obj X.property U Λ)
          (moduleRestrictionIsoSmallInverseImage B Λ X U)).app K.obj.obj))
      (pullbackPreservesLocallyFiniteTorDimension.{u, r, r, d} B U.obj.hom Λ T T'
        K.obj.obj K.property)⟩

/-- **Stacks 0962, part (2).** Let `j : U ⟶ X` be quasi-compact and quasi-separated. The
extension by zero of an object of `D_ctf(U_étale, Λ)` is an object of `D_ctf(X_étale, Λ)`.

Constructibility of the cohomology sheaves of `j_! M` is Tag 095X part (2),
`Stacks.EtaleCohomology.isConstructible_derivedModuleExtensionByZero`, which rests on Tag 03S5
and on Tag 03S8 for an arbitrary constructible sheaf of modules. Locally finite Tor dimension of
its image under the change of coefficients is
`Stacks.EtaleCohomology.extensionByZeroPreservesLocallyFiniteTorDimension`, which uses the
quasi-compactness of `j`. -/
public def constructibleFiniteTorDerivedCategoryExtensionByZero
    (hqc : QuasiCompact (B.inclusion.map U.obj.hom))
    (hqs : QuasiSeparated (B.inclusion.map U.obj.hom))
    (T : ∀ V : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) r, d}
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over V))
    (T' : ∀ V : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B U.obj.left Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) r, d}
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B U.obj.left Λ).over V))
    (M : ConstructibleFiniteTorDerivedCategory.{u, max (u + 1) r, r, d} B U.obj.left Λ T') :
    ConstructibleFiniteTorDerivedCategory.{u, max (u + 1) r, r, d} B X Λ T :=
  ⟨⟨(moduleExtensionByZero.{u, r} B X.obj X.property U Λ).mapDerivedCategory.obj M.obj.obj,
    isConstructible_derivedModuleExtensionByZero B Λ X U hqc hqs M.obj.obj M.obj.property⟩,
    extensionByZeroPreservesLocallyFiniteTorDimension.{u, r, d} B X U Λ hqc T T' M.obj.obj
      M.property⟩

/-- **Stacks 0962.** Let `Λ` be a Noetherian ring and let `j : U ⟶ X` be an étale morphism of
schemes, that is an object `U` of the small étale site of `X`. Then

1. the restriction `K|_U` of an object `K` of `D_ctf(X_étale, Λ)` is an object of
   `D_ctf(U_étale, Λ)`, and
2. the extension by zero `j_! M` of an object `M` of `D_ctf(U_étale, Λ)` is an object of
   `D_ctf(X_étale, Λ)`, when `j` is quasi-compact and quasi-separated.

The two clauses are the two components of the pair; the quasi-compactness and
quasi-separatedness of `j`, which the source asks for in part (2) only, are hypotheses of the
second component alone. The first component is
`Stacks.EtaleCohomology.constructibleFiniteTorDerivedCategoryRestriction` and the second
`Stacks.EtaleCohomology.constructibleFiniteTorDerivedCategoryExtensionByZero`. -/
@[stacks 0962 "both parts, in the two components of the pair: part (1) with `K|_U` the \
restriction of Tag 03S3, part (2) with the quasi-compactness and quasi-separatedness of `j` as \
the premises of that component. The constructible-cohomology halves are the two parts of Tag \
095X; the finite-Tor-dimension half of part (1) is that of Tag 0963 at the structure morphism \
of `U`, and that of part (2) is read at the stalks, by Tag 03S5 for sheaves of modules and Tag \
0DJJ on the slices over affine objects, over which `U ×_X V'` is quasi-compact"]
public def constructibleFiniteTorDerivedCategoryEtale
    (T : ∀ V : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) r, d}
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over V))
    (T' : ∀ V : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B U.obj.left Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) r, d}
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B U.obj.left Λ).over V)) :
    (ConstructibleFiniteTorDerivedCategory.{u, max (u + 1) r, r, d} B X Λ T →
        ConstructibleFiniteTorDerivedCategory.{u, max (u + 1) r, r, d} B U.obj.left Λ T') ×
      (QuasiCompact (B.inclusion.map U.obj.hom) →
        QuasiSeparated (B.inclusion.map U.obj.hom) →
        ConstructibleFiniteTorDerivedCategory.{u, max (u + 1) r, r, d} B U.obj.left Λ T' →
        ConstructibleFiniteTorDerivedCategory.{u, max (u + 1) r, r, d} B X Λ T) :=
  ⟨constructibleFiniteTorDerivedCategoryRestriction.{u, r, d} B X U Λ T T',
    fun hqc hqs => constructibleFiniteTorDerivedCategoryExtensionByZero.{u, r, d} B X U Λ hqc hqs
      T T'⟩

end Stacks.EtaleCohomology

end
