module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.FiniteTorDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.InverseImage

/-!
# Derived inverse image of a constructible complex of finite Tor dimension

Let `Λ` be a Noetherian ring and `f : X ⟶ Y` a morphism of schemes. Tag 0963 says that derived
inverse image carries `D_{ctf}(Y_étale, Λ)` into `D_{ctf}(X_étale, Λ)`, and part (1) of Tag 0962
is the same statement for an étale `f`, where the inverse image is the restriction `K|_U`.

Membership of `D_{ctf}` is the conjunction of two conditions: constructibility of the cohomology
sheaves, and locally finite Tor dimension of the image of the complex in the derived category of
modules over the constant coefficient ring sheaf. The first condition is carried by derived
inverse image, which is Tag 095Y; the second is the predicate
`Stacks.EtaleCohomology.PullbackPreservesLocallyFiniteTorDimension`, taken below as a hypothesis.
It is proved for every morphism by
`Stacks.EtaleCohomology.pullbackPreservesLocallyFiniteTorDimension` of
the sibling module `ConstructibleComplexes.PullbackFiniteTorStalkwise`,
where Tag 0963 is registered on
`Stacks.EtaleCohomology.constructibleFiniteTorDerivedCategoryPullback_unconditional`.

## Main definitions

* `Stacks.EtaleCohomology.PullbackPreservesLocallyFiniteTorDimension`: the finite-Tor-dimension
  half of Tag 0963 for a fixed morphism.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension.of_iso`: locally
  finite Tor dimension on a ringed site transports along an isomorphism of the unbounded derived
  category of modules.
* `Stacks.EtaleCohomology.constructibleFiniteTorDerivedCategoryPullback`: the statement of
  Tag 0963 with its finite-Tor-dimension half taken as a hypothesis; the tag itself is registered
  on `Stacks.EtaleCohomology.constructibleFiniteTorDerivedCategoryPullback_unconditional`.

Part (1) of Tag 0962 is the same statement at an étale morphism; it is
`Stacks.EtaleCohomology.constructibleFiniteTorDerivedCategoryEtalePullback_unconditional` of
the sibling module `ConstructibleComplexes.PullbackFiniteTorStalkwise`,
and the tag is registered on `Stacks.EtaleCohomology.constructibleFiniteTorDerivedCategoryEtale`
of `StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ShriekFiniteTor`.

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

The finite-Tor-dimension half is not obtained here from Tag 08H5, derived inverse image
preserves Tor amplitude, applied on the constant coefficient ringed sites:
`Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_derivedPullback` is stated for a
morphism of `AlgebraicGeometry.RingedTopos.{u, u, u}`, whose three universes coincide, whereas
`AlgebraicGeometry.constantCoefficientRingedSite` is a `AlgebraicGeometry.RingedSite.{u + 1, u,
max (u + 1) w r}`, whose objects and morphisms live in different universes. Even at matching
universes the argument would need the comparison identifying the change of coefficients composed
with the inverse image of module sheaves with the derived inverse image along the induced
morphism of constant coefficient ringed sites. It is proved stalkwise instead, in
the sibling module `ConstructibleComplexes.PullbackFiniteTorStalkwise`.

## References

* [Stacks Project, Tag 0962](https://stacks.math.columbia.edu/tag/0962)
* [Stacks Project, Tag 0963](https://stacks.math.columbia.edu/tag/0963)
* [Stacks Project, Tag 095Y](https://stacks.math.columbia.edu/tag/095Y)
* [Stacks Project, Tag 03TQ](https://stacks.math.columbia.edu/tag/03TQ)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 08H5](https://stacks.math.columbia.edu/tag/08H5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w r d

namespace Stacks.SheafOfModules.DerivedTensorProduct

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

section Iso

variable {Z : RingedSite.{u, v, w}}
  [HasSheafify Z.J AddCommGrpCat.{w}]
  [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : Z.C, HasSheafify (Z.J.over U) AddCommGrpCat.{w}]
  [∀ U : Z.C, (Z.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits

variable [HasDerivedCategory.{d} (RingedSite.Modules.{u, v, w} Z)]
  [hSliceDerived : ∀ U : Z.C,
    HasDerivedCategory.{d} (RingedSite.Modules.{max u v, v, w} (Z.over U))]

attribute [local instance] RingedSite.sliceHasDerivedCategory sliceDerived

variable
  [∀ U : Z.C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{max u v, v, w, w, w} (Z.over U).O).Additive]
  [∀ (U : Z.C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{max u v, v, w, w, w} (Z.over U).O).obj M).Additive]
  [∀ (U : Z.C) (K L : CochainComplex (RingedSite.Modules.{max u v, v, w} (Z.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (Z.over U).O) (ComplexShape.up ℤ)]

attribute [local instance] sliceTensorAdditive sliceTensorObjAdditive sliceHasMapBifunctor

/-- **Locally finite Tor dimension transports along an isomorphism** of `D(O)`: the same
covering of each object works, and on each member of it the restriction to the slice of the
isomorphism is an isomorphism, along which Tor amplitude in an interval transports. -/
theorem LocallyHasFiniteTorDimension.of_iso
    (T : ∀ U : Z.C, DerivedTensorProduct.{max u v, v, w, d} (Z.over U))
    {E E' : RingedSite.DerivedModules.{u, v, w, d} Z} (e : E ≅ E')
    (h : LocallyHasFiniteTorDimension T E) : LocallyHasFiniteTorDimension T E' := by
  intro U
  obtain ⟨S, hS, hdata⟩ := h U
  refine ⟨S, hS, fun {V} g hg => ?_⟩
  obtain ⟨a, b, hab⟩ := hdata g hg
  exact ⟨a, b, hab.of_iso ((RingedSite.derivedRestriction.{u, v, w, d} Z V).mapIso e)⟩

end Iso

end Stacks.SheafOfModules.DerivedTensorProduct

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

/-- **The finite-Tor-dimension half of Tag 0963** for the morphism `f : X ⟶ Y`: whenever the
image of an object of `D(Y_étale, Λ)` under the change of coefficients of Tag 03TR locally has
finite Tor dimension against the family `T` of derived tensor products on the slices over `Y`,
so does the image of its derived inverse image against the family `T'` on the slices over `X`.

It holds for every morphism, by
`Stacks.EtaleCohomology.pullbackPreservesLocallyFiniteTorDimension`, proved in a module importing
this one. -/
public def PullbackPreservesLocallyFiniteTorDimension
    (T : ∀ U : (constantCoefficientRingedSite.{u, max (u + 1) w, r} B Y Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) w r, d}
        ((constantCoefficientRingedSite.{u, max (u + 1) w, r} B Y Λ).over U))
    (T' : ∀ U : (constantCoefficientRingedSite.{u, max (u + 1) w, r} B X Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) w r, d}
        ((constantCoefficientRingedSite.{u, max (u + 1) w, r} B X Λ).over U)) : Prop :=
  ∀ K : DerivedCategory (Sheaf (SmallEtale.topology B Y.obj Y.property)
      (ModuleCat.{max (u + 1) w} Λ)),
    Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension
        (X := constantCoefficientRingedSite.{u, max (u + 1) w, r} B Y Λ) T
        ((moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) w, r} B Y
          Λ).mapDerivedCategory.obj K) →
      Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension
        (X := constantCoefficientRingedSite.{u, max (u + 1) w, r} B X Λ) T'
        ((moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) w, r} B X
          Λ).mapDerivedCategory.obj
          (((smallEtaleBaseChange B f).sheafPullback (ModuleCat.{max (u + 1) w} Λ)
            (SmallEtale.topology B Y.obj Y.property)
            (SmallEtale.topology B X.obj X.property)).mapDerivedCategory.obj K))

/-- **The statement of Stacks 0963 with its finite-Tor-dimension half as a hypothesis.** Let `Λ`
be a Noetherian ring and `f : X ⟶ Y` a morphism of schemes. The derived inverse image of an
object of `D_{ctf}(Y_étale, Λ)` is an object of `D_{ctf}(X_étale, Λ)`, given `hTor`.

Constructibility of the cohomology sheaves of `Lf^*K` is Tag 095Y, which is
`Stacks.EtaleCohomology.constructibleDerivedCategoryPullback`. Locally finite Tor dimension of
its image under the change of coefficients is the hypothesis `hTor`.

No tag is attached: Tag 0963 is registered on
`Stacks.EtaleCohomology.constructibleFiniteTorDerivedCategoryPullback_unconditional` of
the sibling module `ConstructibleComplexes.PullbackFiniteTorStalkwise`,
which discharges `hTor`. -/
public def constructibleFiniteTorDerivedCategoryPullback
    (T : ∀ U : (constantCoefficientRingedSite.{u, max (u + 1) w, r} B Y Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) w r, d}
        ((constantCoefficientRingedSite.{u, max (u + 1) w, r} B Y Λ).over U))
    (T' : ∀ U : (constantCoefficientRingedSite.{u, max (u + 1) w, r} B X Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) w r, d}
        ((constantCoefficientRingedSite.{u, max (u + 1) w, r} B X Λ).over U))
    (hTor : PullbackPreservesLocallyFiniteTorDimension.{u, w, r, d} B f Λ T T')
    (K : ConstructibleFiniteTorDerivedCategory.{u, max (u + 1) w, r, d} B Y Λ T) :
    ConstructibleFiniteTorDerivedCategory.{u, max (u + 1) w, r, d} B X Λ T' :=
  ⟨constructibleDerivedCategoryPullback B Λ f K.obj, hTor K.obj.obj K.property⟩

end Stacks.EtaleCohomology

end
