module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.Defs
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.DirectSummands
import StacksCore.Tactic.StacksAttribute

/-!
# Tor amplitude passes to direct summands

Let `(C, O)` be a ringed site and let `T` be a derived tensor product on `D(O)`. If a direct sum
`K ⊕ L` of objects of `D(O)` has Tor amplitude in `[a, b]`, then so do `K` and `L`. The same
argument, unchanged, gives Tor amplitude to an arbitrary retract.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_of_retract`: Tor amplitude passes
  to a retract.
* `Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_of_biprod`: Tor amplitude of a
  biproduct passes to each of its two summands.

## Implementation notes

The argument needs no additivity of the derived tensor product, only its functoriality: for each
`O`-module `F` and each degree `i` the composite `E ↦ H^i(E ⊗^L_O F[0])` is a functor, and a
functor carries a retract of an object with zero image to an object whose identity factors
through zero. Both summands are retracts of the biproduct, via `biprod.inl`/`biprod.fst` and
`biprod.inr`/`biprod.snd`, so neither summand needs the braiding either: Stacks 08G3 is the
retract statement read at those two retractions.

The retract statement is what the direct-summand step of the proof of the first assertion of
Stacks 0FPV consumes, where `M` is exhibited as a retract of a bounded complex of flat modules
and its Tor amplitude is read off `Stacks.SheafOfModules.DerivedTensorProduct`
`.hasTorAmplitude_of_flatRepresentative`. Going through
`CategoryTheory.Pretriangulated.exists_iso_biprod_of_retraction` first, as
`Stacks.SheafOfModules.DerivedTensorProduct.isPerfect_of_retract` does at the perfectness level,
is unnecessary here — Tor amplitude is a vanishing statement about the image of a functor, and
that is inherited by a retract directly.

## References

* [Stacks Project, Tag 08G3](https://stacks.math.columbia.edu/tag/08G3)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w d

namespace Stacks.SheafOfModules.DerivedTensorProduct

variable {X : RingedSite.{u, v, w}}
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u, v, w} X)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, v, w} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

variable (T : DerivedTensorProduct.{u, v, w, d} X)

/-- **Tor amplitude passes to a retract.** If `M` is a retract of an object `K` of `D(O)` with
Tor amplitude in `[a, b]`, then `M` has Tor amplitude in `[a, b]`: in each degree `i` and against
each `O`-module `F`, the identity of `H^i(M ⊗^L_O F[0])` factors through `H^i(K ⊗^L_O F[0])`,
which is zero. -/
theorem hasTorAmplitude_of_retract {M K : RingedSite.DerivedModules.{u, v, w, d} X}
    (i : M ⟶ K) (r : K ⟶ M) (hir : i ≫ r = 𝟙 M) (a b : ℤ)
    (h : HasTorAmplitude T K a b) : HasTorAmplitude T M a b := fun F j hj =>
  Stacks.Cohomology.TorAmplitude.isZero_obj_of_retract
    (T.tensorModule F ⋙ DerivedCategory.homologyFunctor (RingedSite.Modules.{u, v, w} X) j)
    i r hir (h F j hj)

/-- **Stacks 08G3.** If the direct sum `K ⊕ L` of two objects of `D(O)` has Tor amplitude in
`[a, b]`, then both `K` and `L` have Tor amplitude in `[a, b]`. -/
@[stacks 08G3]
theorem hasTorAmplitude_of_biprod (K L : RingedSite.DerivedModules.{u, v, w, d} X) (a b : ℤ)
    (h : HasTorAmplitude T (K ⊞ L) a b) :
    HasTorAmplitude T K a b ∧ HasTorAmplitude T L a b :=
  ⟨hasTorAmplitude_of_retract T biprod.inl biprod.fst biprod.inl_fst a b h,
    hasTorAmplitude_of_retract T biprod.inr biprod.snd biprod.inr_snd a b h⟩

end Stacks.SheafOfModules.DerivedTensorProduct

end
