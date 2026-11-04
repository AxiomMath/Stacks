module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.FlatRepresentative
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.LocallyFiniteTorDimension
public import StacksFrontier.CategoryTheory.Sites.Modules.Gate18b.FlatRestrictionFreeModuleUniverse

/-!
# Tor amplitude is inherited by the restriction to a slice, at a free module universe

Let `(C, O)` be a ringed site whose objects lie in `Type u`, whose morphisms lie in `v` and
whose structure sheaf and modules have sections in `max v w`, let `U` be an object of `C` and
let `E` be an object of `D(O)` of Tor amplitude in `[a, b]`. Then the restriction of `E` to the
localized ringed site `(C/U, O|_U)` again has Tor amplitude in `[a, b]`.

## Main results

* `FreeModuleUniverse.hasTorAmplitude_derivedRestriction`: Tor amplitude in `[a, b]` is
  inherited by the restriction to a slice.
* `FreeModuleUniverse.hasFiniteTorDimension_derivedRestriction`: the same for finite Tor
  dimension.
* `FreeModuleUniverse.locallyHasFiniteTorDimension_of_hasFiniteTorDimension`: an object of
  finite Tor dimension locally has finite Tor dimension.

## Universes

`StacksFrontier/CategoryTheory/Sites/Cohomology/TorAmplitude/Restriction.lean` states the same
three results at `RingedSite.{u, u, u}`, and gives two reasons for the collapse. **Both are
false**, and the record of why is the point of this file.

* "Stacks 08G1 produces its representative only when the sections of the structure sheaf live
  in `max u v`." Both halves of 08G1 — `hasTorAmplitude_of_flatRepresentative` and
  `exists_flatRepresentative_of_hasTorAmplitude`, in
  `StacksFrontier/CategoryTheory/Sites/Cohomology/TorAmplitude/FlatRepresentative.lean` — are
  stated for `X : RingedSite.{u, v, w}` with the four universes unrelated; that file's own
  implementation notes say so, and say which unit law is used to avoid the monoidal structure
  that would need `w = max u v`.
* "Stacks 0E8J is available only when the objects, the morphisms and the sections all live in
  one universe." It is now also available at
  `Stacks.SheafOfModules.FlatRestriction.FreeModuleUniverse.isFlat_over`, for objects in
  `Type u`, morphisms in `v`, ring sections in `w` and modules in `max v a`, with no smallness
  assumption on the site.

Everything else the argument runs through was already universe-free: the slice instances, the
derived restriction functor `AlgebraicGeometry.RingedSite.derivedRestriction`, the degreewise
restriction `AlgebraicGeometry.RingedSite.restrictComplex` and the predicates
`HasTorAmplitude`, `HasFiniteTorDimension` and `LocallyHasFiniteTorDimension` are all stated at
`RingedSite.{u, v, w}` with four free universes.

The one bound that remains is that the sections dominate the morphisms: the ringed site is a
`RingedSite.{u, v, max v w}` rather than a `RingedSite.{u, v, w}`. It is inherited from 0E8J,
where it is spent on Grothendieck's AB4 for the direct sum over a hom-set of `C` that computes
the sections of an extension by zero; see the implementation notes of
`StacksFrontier/CategoryTheory/Sites/Modules/ExtensionByZeroExactnessFreeModuleUniverse.lean`. It
is no restriction for the sites this is wanted for, whose objects are at least as large as
their morphisms and whose sections are at least as large as their objects. In particular the
small-étale constant-coefficient site of Stacks 03TR, a
`RingedSite.{u + 1, u, max (u + 1) w r}`, is the case `v := u` and `w := max (u + 1) w r`.

A slice of a `RingedSite.{u, v, max v w}` is a `RingedSite.{max u v, v, max v w}`, which is
again of that shape, so the statement is closed under the operation it is about — as it has to
be, since `LocallyHasFiniteTorDimension` quantifies over the slices.

## Implementation notes

The proof is the proof of the single-universe statement, with the free-universe 0E8J in place
of the diagonal one. The earlier statement is not replaced and its consumers are untouched.

A second generalization of the same three results exists,
`StacksFrontier/CategoryTheory/Sites/Cohomology/TorAmplitude/RestrictionOfEssentiallySmall.lean`,
which frees the universe of the *objects* while keeping morphisms, ring and modules in one
universe `u`, and asks `C` to be essentially `u`-small. It avoids 08G1 and 0E8J altogether,
going through a K-flat representative and Stacks 0E8K, because neither was available at its
shape when it was written. Neither statement subsumes the other: that one allows modules in
the universe of the morphisms only, this one requires no smallness.

## References

* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 08G1](https://stacks.math.columbia.edu/tag/08G1)
* [Stacks Project, Tag 0E8J](https://stacks.math.columbia.edu/tag/0E8J)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w d

namespace Stacks.SheafOfModules.DerivedTensorProduct.FreeModuleUniverse

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {X : RingedSite.{u, v, max v w}}
  [HasSheafify X.J AddCommGrpCat.{max v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max v w}]
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{max v w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{max v w}]

attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits

variable [HasDerivedCategory.{d} (RingedSite.Modules.{u, v, max v w} X)]
  [hSliceDerived : ∀ U : X.C,
    HasDerivedCategory.{d} (RingedSite.Modules.{max u v, v, max v w} (X.over U))]

attribute [local instance] RingedSite.sliceHasDerivedCategory sliceDerived

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max v w, max v w, max v w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max v w, max v w, max v w}
      X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, v, max v w} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [∀ U : X.C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{max u v, v, max v w, max v w, max v w}
      (X.over U).O).Additive]
  [∀ (U : X.C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{max u v, v, max v w, max v w, max v w}
      (X.over U).O).obj M).Additive]
  [∀ (U : X.C) (K L : CochainComplex (RingedSite.Modules.{max u v, v, max v w} (X.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (X.over U).O) (ComplexShape.up ℤ)]

attribute [local instance] sliceTensorAdditive sliceTensorObjAdditive sliceHasMapBifunctor

/-- **Tor amplitude restricts to a slice, at a free module universe.** If an object `E` of
`D(O)` has Tor amplitude in `[a, b]` for a derived tensor product `T` on `D(O)`, then its
restriction to the ringed site localized at an object `U` has Tor amplitude in `[a, b]` for
*any* derived tensor product `T'` on that slice.

Stacks 08G1 represents `E` by a complex of flat `O`-modules concentrated in `[a, b]`;
restriction to the slice keeps the terms flat, by Stacks 0E8J at a free module universe, and
keeps the complex concentrated in `[a, b]`, restriction being additive; and a complex of that
shape has Tor amplitude in `[a, b]` by the direction of Stacks 08G1 which needs no input.

Like the single-universe
`Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_derivedRestriction` this carries no
attribute of its own. The assertion is the stability of the hypothesis of Stacks 08FZ under the
replacement of `C` by `C/U` that the source performs without comment, not a numbered result;
the two tags it is assembled from, 08G1 and 0E8J, are registered where they are proved. -/
theorem hasTorAmplitude_derivedRestriction
    (T : DerivedTensorProduct.{u, v, max v w, d} X) (U : X.C)
    (T' : DerivedTensorProduct.{max u v, v, max v w, d} (X.over U))
    (E : RingedSite.DerivedModules.{u, v, max v w, d} X) (a b : ℤ) (hab : a ≤ b)
    (hamp : HasTorAmplitude T E a b) :
    HasTorAmplitude T' ((RingedSite.derivedRestriction.{u, v, max v w, d} X U).obj E) a b := by
  obtain ⟨K, hflat, hzero, ⟨e⟩⟩ := exists_flatRepresentative_of_hasTorAmplitude T E a b hab hamp
  let KU : CochainComplex (RingedSite.Modules.{max u v, v, max v w} (X.over U)) ℤ :=
    X.restrictComplex K U
  let F := SheafOfModules.overFunctor.{max v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U
  refine hasTorAmplitude_of_flatRepresentative T' _ a b KU (fun i => ?_) (fun i hi => ?_) ?_
  · exact Stacks.SheafOfModules.FlatRestriction.FreeModuleUniverse.isFlat_over X U (K.X i)
      (hflat i)
  · exact F.map_isZero (hzero i hi)
  · exact (F.mapDerivedCategoryFactors.app K).symm ≪≫ F.mapDerivedCategory.mapIso e

/-- **Finite Tor dimension restricts to a slice, at a free module universe.** An interval
containing the Tor amplitude of `E` contains that of every restriction of `E`; the interval may
be taken nonempty by `hasFiniteTorDimension_iff`. -/
theorem hasFiniteTorDimension_derivedRestriction
    (T : DerivedTensorProduct.{u, v, max v w, d} X) (U : X.C)
    (T' : DerivedTensorProduct.{max u v, v, max v w, d} (X.over U))
    (E : RingedSite.DerivedModules.{u, v, max v w, d} X) (h : HasFiniteTorDimension T E) :
    HasFiniteTorDimension T'
      ((RingedSite.derivedRestriction.{u, v, max v w, d} X U).obj E) := by
  obtain ⟨a, b, hab, hamp⟩ := (hasFiniteTorDimension_iff T E).1 h
  exact ⟨a, b, hasTorAmplitude_derivedRestriction T U T' E a b hab hamp⟩

/-- **An object of finite Tor dimension locally has finite Tor dimension**, Stacks 08FZ (3), at
a free module universe: the restriction of `E` to *every* slice has finite Tor dimension, so the
maximal covering of each object witnesses the local condition.

This is what establishes `LocallyHasFiniteTorDimension` on a site whose module sections do not
lie in the universe of its morphisms — in particular on the small-étale constant-coefficient
site of Stacks 03TR, a `RingedSite.{u + 1, u, max (u + 1) w r}`. -/
theorem locallyHasFiniteTorDimension_of_hasFiniteTorDimension
    (T : DerivedTensorProduct.{u, v, max v w, d} X)
    (T' : ∀ U : X.C, DerivedTensorProduct.{max u v, v, max v w, d} (X.over U))
    (E : RingedSite.DerivedModules.{u, v, max v w, d} X) (h : HasFiniteTorDimension T E) :
    LocallyHasFiniteTorDimension T' E :=
  locallyHasFiniteTorDimension_of_forall T' E fun V =>
    hasFiniteTorDimension_derivedRestriction T V (T' V) E h

section Instantiations

universe r

/-- **The shape this exists for.** The small-étale constant-coefficient ringed site of
Stacks 03TR, `AlgebraicGeometry.constantCoefficientRingedSite`, is an
`AlgebraicGeometry.RingedSite.{u + 1, u, max (u + 1) w r}`: its module sections lie in
`max (u + 1) w r` while its morphisms lie in `u`. Neither
`Stacks.SheafOfModules.DerivedTensorProduct.locallyHasFiniteTorDimension_of_hasFiniteTorDimension`,
which collapses all three to one universe, nor the essentially-small statement, which asks the
modules to lie in the universe of the morphisms, can be instantiated there. This is the case
`v := u` and `w := max (u + 1) w r` of the statement above, so finite Tor dimension does
establish `LocallyHasFiniteTorDimension` on that site. The universes have to be named: the
module universe `max (u + 1) w r` has to be presented as a `max` over the morphism universe `u`,
and unification will not guess the decomposition. -/
example (Y : RingedSite.{u + 1, u, max (u + 1) w r})
    [HasSheafify Y.J AddCommGrpCat.{max (u + 1) w r}]
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{max (u + 1) w r}]
    [∀ U : Y.C, HasSheafify (Y.J.over U) AddCommGrpCat.{max (u + 1) w r}]
    [∀ U : Y.C, (Y.J.over U).WEqualsLocallyBijective AddCommGrpCat.{max (u + 1) w r}]
    [HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, max (u + 1) w r} Y)]
    [∀ U : Y.C,
      HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, max (u + 1) w r} (Y.over U))]
    [(Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) w r, max (u + 1) w r,
        max (u + 1) w r} Y.O).Additive]
    [∀ M,
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) w r, max (u + 1) w r,
        max (u + 1) w r} Y.O).obj M).Additive]
    [∀ (K L : CochainComplex (RingedSite.Modules.{u + 1, u, max (u + 1) w r} Y) ℤ),
      HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
        (ComplexShape.up ℤ)]
    [∀ U : Y.C,
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) w r, max (u + 1) w r,
        max (u + 1) w r} (Y.over U).O).Additive]
    [∀ (U : Y.C) M,
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) w r, max (u + 1) w r,
        max (u + 1) w r} (Y.over U).O).obj M).Additive]
    [∀ (U : Y.C) (K L : CochainComplex
        (RingedSite.Modules.{u + 1, u, max (u + 1) w r} (Y.over U)) ℤ),
      HomologicalComplex.HasMapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor (Y.over U).O) (ComplexShape.up ℤ)]
    (T : DerivedTensorProduct.{u + 1, u, max (u + 1) w r, d} Y)
    (T' : ∀ U : Y.C, DerivedTensorProduct.{u + 1, u, max (u + 1) w r, d} (Y.over U))
    (E : RingedSite.DerivedModules.{u + 1, u, max (u + 1) w r, d} Y)
    (h : HasFiniteTorDimension T E) :
    LocallyHasFiniteTorDimension T' E :=
  locallyHasFiniteTorDimension_of_hasFiniteTorDimension.{u + 1, u, max (u + 1) w r, d} T T' E h

end Instantiations

end Stacks.SheafOfModules.DerivedTensorProduct.FreeModuleUniverse

end
