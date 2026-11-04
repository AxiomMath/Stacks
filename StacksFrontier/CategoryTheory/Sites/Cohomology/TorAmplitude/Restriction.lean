module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.FlatRepresentative
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.LocallyFiniteTorDimension
public import StacksFrontier.CategoryTheory.Sites.Modules.Gate18b.FlatRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# Tor amplitude is inherited by the restriction to a slice

Let `(C, O)` be a ringed site, let `U` be an object of `C` and let `E` be an object of `D(O)`
of Tor amplitude in `[a, b]`. Then the restriction of `E` to the localized ringed site
`(C/U, O|_U)` again has Tor amplitude in `[a, b]`.

This is the step every local argument about Tor amplitude begins with: the source phrases it as
"after replacing `U` by the members of a covering and `C` by the localization `C/U`", which is
legitimate only because the hypothesis survives the replacement.

## Main results

All in the namespace `Stacks.SheafOfModules.DerivedTensorProduct`:

* `hasTorAmplitude_derivedRestriction`: Tor amplitude in `[a, b]` on a ringed site is inherited
  by the restriction to the site localized at an object.
* `hasFiniteTorDimension_derivedRestriction`: the same for finite Tor dimension.
* `locallyHasFiniteTorDimension_of_hasFiniteTorDimension`: an object of finite Tor dimension
  locally has finite Tor dimension.

## Implementation notes

The proof goes through the bounded flat representative of Stacks 08G1 rather than through the
definition. Tor amplitude on a slice is measured against a derived tensor product datum on that
slice, and no datum on `C` measures anything on `C/U` — see the implementation notes of
`StacksFrontier/CategoryTheory/Sites/Cohomology/TorAmplitude/LocallyFiniteTorDimension.lean` — so a
proof that unfolded the definition would have to compare the two data. There is nothing to
compare if the representative is produced first: Stacks 08G1 turns Tor amplitude in `[a, b]` into
a complex of flat `O`-modules concentrated in `[a, b]` representing `E`; restriction to a slice is
exact, preserves flatness by Stacks 0E8J, and carries a zero module to a zero module, so the
restricted complex is again flat and concentrated in `[a, b]`; and the easy direction of Stacks
08G1 on the slice, which needs no comparison of data, concludes. The datum on the slice is
therefore entirely arbitrary, as it is in
`Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension`.

The universes collapse to one. Stacks 08G1 produces its representative only when the sections of
the structure sheaf live in `max u v`, and Stacks 0E8J — whose proof runs through the reflection
of exactness by extension by zero — is available only when the objects, the morphisms and the
sections all live in one universe. A slice of a `RingedSite.{u, u, u}` is again a
`RingedSite.{u, u, u}`, so the statement is closed under the operation it is about.

## References

* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 08G1](https://stacks.math.columbia.edu/tag/08G1)
* [Stacks Project, Tag 0E8J](https://stacks.math.columbia.edu/tag/0E8J)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u d

namespace Stacks.SheafOfModules.DerivedTensorProduct

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {X : RingedSite.{u, u, u}}
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits

variable [HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} X)]
  [hSliceDerived : ∀ U : X.C,
    HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} (X.over U))]

attribute [local instance] RingedSite.sliceHasDerivedCategory sliceDerived

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, u, u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [∀ U : X.C, (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (X.over U).O).Additive]
  [∀ (U : X.C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (X.over U).O).obj M).Additive]
  [∀ (U : X.C) (K L : CochainComplex (RingedSite.Modules.{u, u, u} (X.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (X.over U).O) (ComplexShape.up ℤ)]

attribute [local instance] sliceTensorAdditive sliceTensorObjAdditive sliceHasMapBifunctor

/-- **Tor amplitude restricts to a slice.** If an object `E` of `D(O)` has Tor amplitude in
`[a, b]` for a derived tensor product `T` on `D(O)`, then its restriction to the ringed site
localized at an object `U` has Tor amplitude in `[a, b]` for *any* derived tensor product `T'` on
that slice.

Stacks 08G1 represents `E` by a complex of flat `O`-modules concentrated in `[a, b]`; restriction
to the slice keeps the terms flat, by Stacks 0E8J, and keeps the complex concentrated in
`[a, b]`, restriction being additive; and a complex of that shape has Tor amplitude in `[a, b]`
by the direction of Stacks 08G1 which needs no input. -/
theorem hasTorAmplitude_derivedRestriction (T : DerivedTensorProduct.{u, u, u, d} X) (U : X.C)
    (T' : DerivedTensorProduct.{u, u, u, d} (X.over U))
    (E : RingedSite.DerivedModules.{u, u, u, d} X) (a b : ℤ) (hab : a ≤ b)
    (hamp : HasTorAmplitude T E a b) :
    HasTorAmplitude T' ((RingedSite.derivedRestriction.{u, u, u, d} X U).obj E) a b := by
  obtain ⟨K, hflat, hzero, ⟨e⟩⟩ := exists_flatRepresentative_of_hasTorAmplitude T E a b hab hamp
  let KU : CochainComplex (RingedSite.Modules.{u, u, u} (X.over U)) ℤ := X.restrictComplex K U
  refine hasTorAmplitude_of_flatRepresentative T' _ a b KU (fun i => ?_) (fun i hi => ?_) ?_
  · exact Stacks.SheafOfModules.FlatRestriction.isFlat_over X U (K.X i) (hflat i)
  · exact (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      U).map_isZero (hzero i hi)
  · exact ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      U).mapDerivedCategoryFactors.app K).symm ≪≫
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        U).mapDerivedCategory.mapIso e

/-- **Finite Tor dimension restricts to a slice.** An interval containing the Tor amplitude of
`E` contains that of every restriction of `E`; the interval may be taken nonempty by
`hasFiniteTorDimension_iff`. -/
theorem hasFiniteTorDimension_derivedRestriction (T : DerivedTensorProduct.{u, u, u, d} X)
    (U : X.C) (T' : DerivedTensorProduct.{u, u, u, d} (X.over U))
    (E : RingedSite.DerivedModules.{u, u, u, d} X) (h : HasFiniteTorDimension T E) :
    HasFiniteTorDimension T' ((RingedSite.derivedRestriction.{u, u, u, d} X U).obj E) := by
  obtain ⟨a, b, hab, hamp⟩ := (hasFiniteTorDimension_iff T E).1 h
  exact ⟨a, b, hasTorAmplitude_derivedRestriction T U T' E a b hab hamp⟩

/-- **An object of finite Tor dimension locally has finite Tor dimension**, Stacks 08FZ (3): the
restriction of `E` to *every* slice has finite Tor dimension, so the maximal covering of each
object witnesses the local condition. -/
theorem locallyHasFiniteTorDimension_of_hasFiniteTorDimension
    (T : DerivedTensorProduct.{u, u, u, d} X)
    (T' : ∀ U : X.C, DerivedTensorProduct.{u, u, u, d} (X.over U))
    (E : RingedSite.DerivedModules.{u, u, u, d} X) (h : HasFiniteTorDimension T E) :
    LocallyHasFiniteTorDimension T' E :=
  locallyHasFiniteTorDimension_of_forall T' E fun V =>
    hasFiniteTorDimension_derivedRestriction T V (T' V) E h

end Stacks.SheafOfModules.DerivedTensorProduct

end
