module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantCoefficientsExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.LocallyFiniteTorDimension
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExistenceFreeSections

/-!
# `D_{ctf}(X_étale, Λ)` with its derived tensor products constructed

For a scheme `X` and a Noetherian coefficient ring `Λ`, the category `D_{ctf}(X_étale, Λ)` of
Stacks 03TQ is the full subcategory of the constructible derived category `D_c(X_étale, Λ)` of
Stacks 095W consisting of the objects of locally finite Tor dimension in the sense of
Stacks 08FZ.

## Main definitions

* `Stacks.EtaleCohomology.canonicalSliceDerivedTensorProduct`: the derived tensor product on a
  slice of the constant-coefficient étale ringed site.
* `Stacks.EtaleCohomology.CanonicalConstructibleFiniteTorDerivedCategory`: the full subcategory
  `D_{ctf}(X_étale, Λ)`.

## Implementation notes

Constructibility is formulated for `ModuleCat`-valued sheaves on the small étale site, whereas
Tor amplitude is formulated for sheaves of modules on a ringed site. The bridge is the exact
functor `AlgebraicGeometry.moduleSheafOverConstantCoefficientsFunctor` to modules over the
constant coefficient ring sheaf of Stacks 03TR, which descends to unbounded derived categories;
membership is the predicate of Stacks 08FZ applied to the image of an object under that derived
functor.

Locally finite Tor dimension is measured against a family of derived tensor products on the
slices of the ringed site, one for each object of the site, because a slice has its own module
category and a datum on the site cannot measure Tor amplitude on a slice. That family is
`Stacks.SheafOfModules.FreeSections.derivedTensorProduct` of Stacks 06YU at each slice, so the
subcategory below depends on no choice.

`Stacks.SheafOfModules.FreeSections.derivedTensorProduct` is Stacks 06YU with the universe of the
module sections free of the morphism universe of the site. The small étale site of `X` ringed by
the constant coefficient sheaf is an `AlgebraicGeometry.RingedSite.{u + 1, u, max (u + 1) w r}`
— objects in `Type (u + 1)`, morphisms in `Type u`, sections in `Type (max (u + 1) w r)` — and so
is each of its slices, since a slice of a `RingedSite.{u, v, w}` is a
`RingedSite.{max u v, v, w}`; the sections universe is therefore not the morphism universe.

The universes of the scheme, of the module sections and of the coefficient ring are
independent, the comparison functor lifting the first two into a universe containing all three.

## References

* [Stacks Project, Tag 03TQ](https://stacks.math.columbia.edu/tag/03TQ)
* [Stacks Project, Tag 095W](https://stacks.math.columbia.edu/tag/095W)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
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

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]
  [HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} Λ)]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, max (u + 1) w r}
    (constantCoefficientRingedSite.{u, w, r} B X Λ))]
  [hSliceDerived : ∀ U : (constantCoefficientRingedSite.{u, w, r} B X Λ).C,
    HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, max (u + 1) w r}
      ((constantCoefficientRingedSite.{u, w, r} B X Λ).over U))]
  [∀ U : (constantCoefficientRingedSite.{u, w, r} B X Λ).C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) w r, max (u + 1) w r,
        max (u + 1) w r}
      ((constantCoefficientRingedSite.{u, w, r} B X Λ).over U).O).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, w, r} B X Λ).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) w r, max (u + 1) w r,
        max (u + 1) w r}
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

/-- The derived tensor product on the slice over `U` of the small étale site of `X` ringed by
the constant coefficient sheaf of Stacks 03TR: the canonical one of Stacks 06YU, with its
natural map to the ordinary total tensor product, its two one-sided K-flat comparisons and its
exactness in each variable. -/
def canonicalSliceDerivedTensorProduct
    (U : (constantCoefficientRingedSite.{u, w, r} B X Λ).C) :
    Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) w r, d}
      ((constantCoefficientRingedSite.{u, w, r} B X Λ).over U) :=
  Stacks.SheafOfModules.FreeSections.derivedTensorProduct
    ((constantCoefficientRingedSite.{u, w, r} B X Λ).over U)

/-- **Stacks 03TQ.** The category `D_{ctf}(X_étale, Λ)`: the full subcategory of the
constructible derived category of Stacks 095W consisting of the objects whose image in the
derived category of modules over the constant coefficient ring sheaf has locally finite Tor
dimension in the sense of Stacks 08FZ.

Tor dimension is measured against the derived tensor products
`Stacks.EtaleCohomology.canonicalSliceDerivedTensorProduct` of Stacks 06YU on the slices of that
ringed site. -/
@[stacks 03TQ "the derived tensor products on the slices of the constant-coefficient étale \
ringed site are constructed here, by Stacks 06YU at free universes, so no derived tensor \
product is assumed",
  sga "5 III 1.1" "D_ctf(X) definition",
  sga "4½ Rapport 4.6" "ii)",
  sga "5 IIIB 6.1" "D_ctf(-)", sga "4½ Th_finitude 1.7"]
abbrev CanonicalConstructibleFiniteTorDerivedCategory :=
  ObjectProperty.FullSubcategory
    (fun K : ConstructibleDerivedCategory.{u, w, r} B X Λ =>
      Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension
        (X := constantCoefficientRingedSite.{u, w, r} B X Λ)
        (canonicalSliceDerivedTensorProduct.{u, w, r, d} B X Λ)
        ((moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).mapDerivedCategory.obj
          K.obj))

end Stacks.EtaleCohomology

end
