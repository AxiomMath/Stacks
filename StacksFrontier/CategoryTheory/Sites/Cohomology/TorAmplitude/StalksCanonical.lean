module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.Stalks
import StacksCore.Tactic.StacksAttribute

/-!
# Tor amplitude is computed at the stalks, for the derived tensor product of a ringed site

Let `(C, O)` be a ringed site, `E` an object of `D(O)` and `a, b` integers.

1. If `E` has Tor amplitude in `[a, b]`, then for every point `Φ` of `C` the derived stalk `E_Φ`
   has Tor amplitude in `[a, b]` as an object of `D(O_Φ)`.
2. If `C` has enough points, the converse holds.

Tor amplitude is measured on the sheaf side against the derived tensor product
`Stacks.SheafOfModules.canonicalDerivedTensorProduct`, and on the stalk side against the canonical
derived tensor product of modules over the commutative ring `O_Φ`
(`StacksDraft.TorAmplitude.HasTorAmplitudeCanonical`). The morphisms of the site, the sections of
its structure sheaf and the sections of its modules lie in one universe `w`, the objects of the
site in a universe `u`, and `d` is the hom universe of `D(O)`.

## Main results

Both of the results below are in the namespace `Stacks.SheafOfModules.DerivedTensorProduct`.

* `hasTorAmplitudeCanonical_derivedModuleFiber_canonical`: Tor amplitude in `[a, b]` of `E`
  implies Tor amplitude in `[a, b]` of `E_Φ` over the stalk ring `O_Φ`, for every point `Φ`.
* `hasTorAmplitude_canonical_of_forall_derivedModuleFiber`: the converse on a site with a
  conservative family of points.

## References

* [Stacks Project, Tag 0DJJ](https://stacks.math.columbia.edu/tag/0DJJ)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u w d

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

namespace Stacks.SheafOfModules.DerivedTensorProduct

variable {Y : RingedSite.{u, w, w}} [LocallySmall.{w} Y.C]
  [HasSheafify Y.J AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [hd : HasDerivedCategory.{d} (RingedSite.Modules.{u, w, w} Y)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, w, w, w, w} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, w, w, w, w} Y.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, w, w} Y) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]

/-- If an object `E` of `D(O)` has Tor amplitude in `[a, b]` for the derived tensor product of the
ringed site, then for every point `Φ` of the site its derived stalk `E_Φ` has Tor amplitude in
`[a, b]` as an object of `D(O_Φ)`. -/
@[stacks 0DJJ "part (1)",
  sga "6 I 5.6.2" "fiber direction",
  sga "6 III 3.3" "(i)=>(ii), f=id",
  sga "4 XVII 4.2.8" "(iii) f=id, forward"]
theorem hasTorAmplitudeCanonical_derivedModuleFiber_canonical
    (E : RingedSite.DerivedModules.{u, w, w, d} Y) (a b : ℤ)
    (hamp : HasTorAmplitude
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u, w, d} Y) E a b)
    (Φ : Y.J.Point.{w}) :
    letI : HasDerivedCategory.{d}
        (SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf.{w, u, w} Y.O)) := hd
    StacksDraft.TorAmplitude.HasTorAmplitudeCanonical
      ((Φ.presheafFiber (A := CommRingCat.{w})).obj Y.O.obj)
      ((Stacks.derivedModuleFiber Φ Y.O).obj E) a b :=
  hasTorAmplitudeCanonical_derivedModuleFiber _ E a b hamp Φ

/-- On a ringed site whose underlying site has a conservative family of points, an object `E`
of `D(O)` has Tor amplitude in `[a, b]` for the derived tensor product of the site as soon as its
derived stalk at every point of the site does. -/
@[stacks 0DJJ "part (2)",
  sga "6 I 5.6.2" "converse, enough points",
  sga "6 III 3.3" "(ii)=>(i), f=id", sga "4 XVII 4.2.8" "(iii) f=id, converse"]
theorem hasTorAmplitude_canonical_of_forall_derivedModuleFiber
    (E : RingedSite.DerivedModules.{u, w, w, d} Y) (a b : ℤ)
    (hY : Y.J.HasConservativeFamily.{w})
    (hE : ∀ Φ : Y.J.Point.{w},
      letI : HasDerivedCategory.{d}
          (SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf.{w, u, w} Y.O)) := hd
      StacksDraft.TorAmplitude.HasTorAmplitudeCanonical
        ((Φ.presheafFiber (A := CommRingCat.{w})).obj Y.O.obj)
        ((Stacks.derivedModuleFiber Φ Y.O).obj E) a b) :
    HasTorAmplitude (Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u, w, d} Y) E a b :=
  hasTorAmplitude_of_forall_derivedModuleFiber _ E a b hY hE

end Stacks.SheafOfModules.DerivedTensorProduct

end
