module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLimitsSets
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlat
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlatIsFlat
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.FiniteTorDimension
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.RestrictionFreeModuleUniverse

/-!
# A constructible flat complex has locally finite Tor dimension

Let `Λ` be a Noetherian ring and `X` a scheme. Tag 03TT says that an object of
`D(X_étale, Λ)` lies in `D_{ctf}(X_étale, Λ)` exactly when it is represented by a bounded
complex of constructible flat sheaves of `Λ`-modules. This file proves the **finite-Tor-dimension
half of the direction (2) ⟹ (1)**: such a complex has locally finite Tor dimension in the sense
of Tag 08FZ over the constant coefficient ringed site of Tag 03TR. Together with
`Stacks.EtaleCohomology.isConstructible_of_isRepresentedByConstructibleFlatComplex`, the
constructible-cohomology half, it gives the direction (2) ⟹ (1) in full.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.FreeModuleUniverse.locallyHasFiniteTorDimension_of_flatRepresentative`
  : on a ringed site at a free module universe, an object represented by a complex of flat
  modules concentrated in `[a, b]` locally has finite Tor dimension.
* `Stacks.EtaleCohomology.locallyHasFiniteTorDimension_of_isRepresentedByConstructibleFlatComplex`
  : **Tag 03TT, the finite-Tor-dimension half of (2) ⟹ (1)**.
* `Stacks.EtaleCohomology.constructibleFiniteTorDerivedCategoryOfConstructibleFlatComplex`
  : **Tag 03TT, the direction (2) ⟹ (1)** in full, as membership of
  `D_{ctf}(X_étale, Λ)`, with no hypothesis carried.

## Implementation notes

The argument is one application of Stacks 08G1 per slice. A term of the complex is a
constructible flat sheaf of `Λ`-modules, so its image under the change of coefficients of
Tag 03TR is a *flat* module over the constant coefficient ring sheaf, by
`AlgebraicGeometry.isFlat_moduleSheafOverConstantCoefficients_of_isConstructibleFlatModuleSheaf`;
the restriction of a flat module to a slice is flat, by Stacks 0E8J at a free module universe
(`Stacks.SheafOfModules.FlatRestriction.FreeModuleUniverse.isFlat_over`); and a complex of flat
modules concentrated in `[a, b]` has Tor amplitude in `[a, b]`, by the direction of Stacks 08G1
that needs no input. Reading that on every slice is more than locally finite Tor dimension asks
for, so the maximal covering of each object witnesses the condition and
`Stacks.SheafOfModules.DerivedTensorProduct.locallyHasFiniteTorDimension_of_forall` concludes.
Exactness of the change of coefficients is what lets it be applied degreewise and commute with
the passage to the derived category, through `CategoryTheory.Functor.mapDerivedCategoryFactors`.

*What used to block this.* The module documentation of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/ConstructibleComplexes/ConstructibleFlat.lean`
recorded this half as missing for want of the *slicewise* form, on the ground that
`Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_derivedRestriction` "is available
only when the objects, morphisms and sections of the ringed site share one universe". That is no
longer so: the restriction statements of
`StacksFrontier/CategoryTheory/Sites/Cohomology/TorAmplitude/RestrictionFreeModuleUniverse.lean`
hold on a `RingedSite.{u, v, max v w}`, of which the constant coefficient ringed site, a
`AlgebraicGeometry.RingedSite.{u + 1, u, max (u + 1) w r}`, is the case `v := u` and
`w := max (u + 1) w r`. No per-slice flat representative has to be produced either: the
degreewise restriction of the one flat complex on the site is already flat on the slice, so this
file goes through `Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_of_flatRepresentative`
directly rather than through the Tor-amplitude transport.

The general statement carries no `@[stacks]` attribute, for the reason
`Stacks.SheafOfModules.DerivedTensorProduct.FreeModuleUniverse.hasTorAmplitude_derivedRestriction`
carries none: it is 08G1 and 0E8J assembled over the replacement of `C` by `C/U`, and those two
tags are registered where they are proved. It is stated here, next to its only consumer, rather
than in the Tor-amplitude tree, where the restriction statements it is built from are stated.

*What remains of Tag 03TT.* The converse direction (1) ⟹ (2) is still missing, and so is the
sharpened form bounding the length of the representative by the Tor amplitude. Its proof is an
induction on the length of the Tor window, and in this development's vocabulary it needs one
input that does not exist: the passage from locally finite Tor dimension to a single global
Tor-amplitude interval, which is
`Stacks.SheafOfModules.DerivedTensorProduct.hasFiniteTorDimension_of_locallyHasFiniteTorDimension`
of `StacksFrontier/CategoryTheory/Sites/Cohomology/TorAmplitude/IntervalDescent.lean`, stated at a
`RingedSite.{c, u, u}` with `C` essentially `u`-small and therefore not instantiable at the
constant coefficient ringed site. That pin is inherited from Stacks 0E8K through
`Stacks.SheafOfModules.DerivedTensorProduct.OfEssentiallySmall.isZero_homology_derivedRestriction_tensorModule`,
and a free-module-universe counterpart of 0E8K has no declaration in this tree. The resolution
itself is not an obstacle:
`Stacks.EtaleCohomology.isRepresentedByBoundedAboveConstructibleFlatComplex_of_isConstructible`
is unconditional.

The universes of the scheme, of the module sections and of the coefficient ring are independent
in the first two statements. The third fixes the module sections at `max (u + 1) r`, the
universe at which the weak Serre property of the constructible sheaves of modules —
`AlgebraicGeometry.SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf`, Tag 03RZ (3) — is
available, so that the constructibility half needs no hypothesis.

## References

* [Stacks Project, Tag 03TT](https://stacks.math.columbia.edu/tag/03TT)
* [Stacks Project, Tag 03TQ](https://stacks.math.columbia.edu/tag/03TQ)
* [Stacks Project, Tag 03TR](https://stacks.math.columbia.edu/tag/03TR)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 08G1](https://stacks.math.columbia.edu/tag/08G1)
* [Stacks Project, Tag 0E8J](https://stacks.math.columbia.edu/tag/0E8J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w r d

namespace Stacks.SheafOfModules.DerivedTensorProduct.FreeModuleUniverse

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {Z : RingedSite.{u, v, max v w}}
  [HasSheafify Z.J AddCommGrpCat.{max v w}]
  [Z.J.WEqualsLocallyBijective AddCommGrpCat.{max v w}]
  [∀ U : Z.C, HasSheafify (Z.J.over U) AddCommGrpCat.{max v w}]
  [∀ U : Z.C, (Z.J.over U).WEqualsLocallyBijective AddCommGrpCat.{max v w}]

attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits

variable [HasDerivedCategory.{d} (RingedSite.Modules.{u, v, max v w} Z)]
  [hSliceDerived : ∀ U : Z.C,
    HasDerivedCategory.{d} (RingedSite.Modules.{max u v, v, max v w} (Z.over U))]

attribute [local instance] RingedSite.sliceHasDerivedCategory sliceDerived

variable
  [∀ U : Z.C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{max u v, v, max v w, max v w, max v w} (Z.over U).O).Additive]
  [∀ (U : Z.C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{max u v, v, max v w, max v w, max v w} (Z.over U).O).obj M).Additive]
  [∀ (U : Z.C) (K L : CochainComplex (RingedSite.Modules.{max u v, v, max v w} (Z.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{max u v, v, max v w, max v w, max v w}
        (Z.over U).O) (ComplexShape.up ℤ)]

attribute [local instance] sliceTensorAdditive sliceTensorObjAdditive sliceHasMapBifunctor

/-- **An object represented by a bounded complex of flat modules locally has finite Tor
dimension**, at a free module universe.

The degreewise restriction of `K` to the slice over `V` has flat terms, by Stacks 0E8J at a free
module universe; it is still concentrated in `[a, b]`, restriction being additive; and it still
represents the restriction of `E`, restriction being exact. So the restriction of `E` to *every*
slice has Tor amplitude in `[a, b]` by the direction of Stacks 08G1 which needs no input, and the
maximal covering of each object witnesses the local condition.

This carries no attribute of its own, for the reason
`Stacks.SheafOfModules.DerivedTensorProduct.FreeModuleUniverse.hasTorAmplitude_derivedRestriction`
carries none: it is Stacks 08G1 and Stacks 0E8J assembled over the replacement of `C` by `C/U`
which Stacks 08FZ performs without comment, and both tags are registered where they are
proved. -/
theorem locallyHasFiniteTorDimension_of_flatRepresentative
    (T : ∀ U : Z.C, DerivedTensorProduct.{max u v, v, max v w, d} (Z.over U))
    (E : RingedSite.DerivedModules.{u, v, max v w, d} Z) (a b : ℤ)
    (K : CochainComplex (RingedSite.Modules.{u, v, max v w} Z) ℤ)
    (hflat : ∀ i : ℤ,
      AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, max v w, max v w} (O := Z.O) (K.X i))
    (hzero : ∀ i : ℤ, i ∉ Set.Icc a b → IsZero (K.X i))
    (e : DerivedCategory.Q.obj K ≅ E) :
    LocallyHasFiniteTorDimension T E := by
  refine locallyHasFiniteTorDimension_of_forall T E fun V => ⟨a, b, ?_⟩
  let KV : CochainComplex (RingedSite.Modules.{max u v, v, max v w} (Z.over V)) ℤ :=
    Z.restrictComplex K V
  refine hasTorAmplitude_of_flatRepresentative (T V) _ a b KV
    (fun i => ?_) (fun i hi => ?_) ?_
  · exact Stacks.SheafOfModules.FlatRestriction.FreeModuleUniverse.isFlat_over.{w, max v w, v, u}
      Z V (K.X i) (hflat i)
  · exact (SheafOfModules.overFunctor.{max v w} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) V).map_isZero (hzero i hi)
  · exact ((SheafOfModules.overFunctor.{max v w} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) V).mapDerivedCategoryFactors.app
        K).symm ≪≫
      (SheafOfModules.overFunctor.{max v w} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) V).mapDerivedCategory.mapIso e

end Stacks.SheafOfModules.DerivedTensorProduct.FreeModuleUniverse

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
  GrothendieckTopology.hasSheafify_addCommGrpCat
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits

section General

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]
  [HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} Λ)]
  [HasColimitsOfSize.{u, u} (ModuleCat.{w} Λ)]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, max (u + 1) w r}
    (constantCoefficientRingedSite.{u, w, r} B X Λ))]
  [hSliceDerived : ∀ U : (constantCoefficientRingedSite.{u, w, r} B X Λ).C,
    HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, max (u + 1) w r}
      ((constantCoefficientRingedSite.{u, w, r} B X Λ).over U))]
  [∀ U : (constantCoefficientRingedSite.{u, w, r} B X Λ).C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) w r, max (u + 1) w r, max (u + 1) w r}
      ((constantCoefficientRingedSite.{u, w, r} B X Λ).over U).O).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, w, r} B X Λ).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) w r, max (u + 1) w r, max (u + 1) w r}
      ((constantCoefficientRingedSite.{u, w, r} B X Λ).over U).O).obj M).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, w, r} B X Λ).C)
    (K L : CochainComplex (RingedSite.Modules.{u + 1, u, max (u + 1) w r}
      ((constantCoefficientRingedSite.{u, w, r} B X Λ).over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor
        ((constantCoefficientRingedSite.{u, w, r} B X Λ).over U).O) (ComplexShape.up ℤ)]

attribute [local instance] Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory

open _root_.Stacks.SheafOfModules.DerivedTensorProduct.FreeModuleUniverse in
/-- **Tag 03TT, the finite-Tor-dimension half of the direction (2) ⟹ (1).** An object of
`D(X_étale, Λ)` represented by a bounded complex of constructible flat sheaves of `Λ`-modules
has locally finite Tor dimension in the sense of Tag 08FZ, read on its image under the change of
coefficients of Tag 03TR and measured against the derived tensor products `T` on the slices of
the constant coefficient ringed site.

Each term of the complex becomes a flat module over the constant coefficient ring sheaf, by
`AlgebraicGeometry.isFlat_moduleSheafOverConstantCoefficients_of_isConstructibleFlatModuleSheaf`;
the change of coefficients is exact, so applied degreewise it carries the complex to a
representative of the image of `K`; and
`Stacks.SheafOfModules.DerivedTensorProduct.FreeModuleUniverse.locallyHasFiniteTorDimension_of_flatRepresentative`
reads Stacks 08G1 on every slice. -/
@[stacks 03TT "the finite-tor-dimension half of the direction (2) => (1), at a free coefficient \
universe; the constructible-cohomology half of that direction is \
`Stacks.EtaleCohomology.isConstructible_of_isRepresentedByConstructibleFlatComplex` and the two \
are combined in \
`Stacks.EtaleCohomology.constructibleFiniteTorDerivedCategoryOfConstructibleFlatComplex`",
  sga "4½ Rapport 4.6" "partial"]
theorem locallyHasFiniteTorDimension_of_isRepresentedByConstructibleFlatComplex
    (T : ∀ U : (constantCoefficientRingedSite.{u, w, r} B X Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) w r, d}
        ((constantCoefficientRingedSite.{u, w, r} B X Λ).over U))
    (K : DerivedCategory
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)))
    (hK : IsRepresentedByConstructibleFlatComplex.{u, w, r} B X Λ K) :
    Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension
      (X := constantCoefficientRingedSite.{u, w, r} B X Λ) T
      ((moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).mapDerivedCategory.obj K) := by
  obtain ⟨C, a, b, hGE, hLE, hflat, ⟨eC⟩⟩ := hK
  haveI := hGE
  haveI := hLE
  refine locallyHasFiniteTorDimension_of_flatRepresentative.{u + 1, u, max (u + 1) w r, d}
    T _ a b
    (((moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj C) (fun i => ?_) (fun i hi => ?_) ?_
  · exact isFlat_moduleSheafOverConstantCoefficients_of_isConstructibleFlatModuleSheaf
      B X Λ (C.X i) (hflat i)
  · refine (moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).map_isZero ?_
    simp only [Set.mem_Icc, not_and_or, not_le] at hi
    rcases hi with hi | hi
    · exact C.isZero_of_isStrictlyGE a i hi
    · exact C.isZero_of_isStrictlyLE b i hi
  · exact (Iso.app (Functor.mapDerivedCategoryFactors
        (moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ)) C).symm ≪≫
      (moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).mapDerivedCategory.mapIso eC

end General

section SerreUniverse

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]
  [HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{max (u + 1) r} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{max (u + 1) r} Λ)]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, max (u + 1) r}
    (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ))]
  [hSliceDerived : ∀ U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C,
    HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U))]
  [∀ U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r, max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U).O).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r, max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U).O).obj M).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C)
    (K L : CochainComplex (RingedSite.Modules.{u + 1, u, max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U).O)
      (ComplexShape.up ℤ)]

attribute [local instance] Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory

/-- **Tag 03TT, the direction (2) ⟹ (1).** An object of `D(X_étale, Λ)` represented by a bounded
complex of constructible flat sheaves of `Λ`-modules is an object of `D_{ctf}(X_étale, Λ)`: its
cohomology sheaves are constructible and its image under the change of coefficients of Tag 03TR
has locally finite Tor dimension.

The two halves are
`Stacks.EtaleCohomology.isConstructible_of_isRepresentedByConstructibleFlatComplex` and
`Stacks.EtaleCohomology.locallyHasFiniteTorDimension_of_isRepresentedByConstructibleFlatComplex`.
The weak Serre property of the constructible sheaves of modules, which the first of them asks
for, is Tag 03RZ (3) at the coefficient universe `max (u + 1) r`; that is why the module sections
are fixed there rather than left free, and it is why nothing is carried as a hypothesis. -/
@[stacks 03TT "the direction (2) => (1), both halves, with the weak Serre property of the \
constructible sheaves of modules discharged by Tag 03RZ (3) at the coefficient universe \
max (u + 1) r. The direction (1) => (2) and the sharpened bound on the length of the \
representative are not proved", sga "4½ Rapport 4.6" "partial"]
def constructibleFiniteTorDerivedCategoryOfConstructibleFlatComplex
    (T : ∀ U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) r, d}
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U))
    (K : DerivedCategory
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)))
    (hK : IsRepresentedByConstructibleFlatComplex.{u, max (u + 1) r, r} B X Λ K) :
    ConstructibleFiniteTorDerivedCategory.{u, max (u + 1) r, r, d} B X Λ T :=
  ⟨⟨K, isConstructible_of_isRepresentedByConstructibleFlatComplex B X Λ
      (SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf.{u, r, r} B X Λ) K hK⟩,
    locallyHasFiniteTorDimension_of_isRepresentedByConstructibleFlatComplex B X Λ T K hK⟩

end SerreUniverse

end Stacks.EtaleCohomology

end
