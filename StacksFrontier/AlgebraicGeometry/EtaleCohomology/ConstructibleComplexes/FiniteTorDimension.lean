module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantCoefficientsExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.LocallyFiniteTorDimension
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# Constructible complexes of finite Tor dimension

For a scheme `X` and a Noetherian coefficient ring `Λ`, the category `D_{ctf}(X_étale, Λ)` is
the full subcategory of the constructible derived category `D_c(X_étale, Λ)` of Stacks 095W
consisting of the objects of locally finite Tor dimension in the sense of Stacks 08FZ.

## Main definitions

* `Stacks.EtaleCohomology.ConstructibleFiniteTorDerivedCategory`: the full subcategory
  `D_{ctf}(X_étale, Λ)`.

## Implementation notes

Constructibility is formulated for `ModuleCat`-valued sheaves on the small étale site, whereas
Tor amplitude is formulated for sheaves of modules on a ringed site. The bridge is the exact
functor `AlgebraicGeometry.moduleSheafOverConstantCoefficientsFunctor` to modules over the
constant coefficient ring sheaf of Stacks 03TR, which descends to unbounded derived categories;
membership is the predicate of Stacks 08FZ applied to the image of an object under that derived
functor.

Locally finite Tor dimension is measured, as everywhere in this development, against a given
family of derived tensor products on the slices of the ringed site rather than against a
canonical choice: `Stacks.SheafOfModules.DerivedTensorProduct` is universe-polymorphic while
the construction of an inhabitant of it is available only on a diagonal, and instantiating the
family specialises the subcategory.

The universes of the scheme, of the module sections and of the coefficient ring are
independent, the comparison functor lifting the first two into a universe containing all three.

## References

* [Stacks Project, Tag 03TQ](https://stacks.math.columbia.edu/tag/03TQ)
* [Stacks Project, Tag 095W](https://stacks.math.columbia.edu/tag/095W)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
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
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) w r,
        max (u + 1) w r, max (u + 1) w r}
      ((constantCoefficientRingedSite.{u, w, r} B X Λ).over U).O).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, w, r} B X Λ).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) w r,
        max (u + 1) w r, max (u + 1) w r}
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

/-- **Stacks 03TQ.** The category `D_{ctf}(X_étale, Λ)`: the full subcategory of the
constructible derived category of Stacks 095W consisting of the objects whose image in the
derived category of modules over the constant coefficient ring sheaf has locally finite Tor
dimension in the sense of Stacks 08FZ, measured against the derived tensor products `T` on the
slices of that ringed site. -/
@[stacks 03TQ,
  sga "5 III 1.1" "D_ctf(X) definition",
  sga "4½ Rapport 4.6" "ii)",
  sga "5 IIIB 6.1" "D_ctf(-)"]
abbrev ConstructibleFiniteTorDerivedCategory
    (T : ∀ U : (constantCoefficientRingedSite.{u, w, r} B X Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) w r, d}
        ((constantCoefficientRingedSite.{u, w, r} B X Λ).over U)) :=
  ObjectProperty.FullSubcategory
    (fun K : ConstructibleDerivedCategory.{u, w, r} B X Λ =>
      Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension
        (X := constantCoefficientRingedSite.{u, w, r} B X Λ) T
        ((moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).mapDerivedCategory.obj
          K.obj))

end Stacks.EtaleCohomology

end
