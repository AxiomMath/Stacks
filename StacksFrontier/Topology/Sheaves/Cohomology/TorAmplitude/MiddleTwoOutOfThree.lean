module

public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.FlatOpcycles
import StacksCore.Tactic.StacksAttribute

/-!
# The middle clause of the two-out-of-three property of Tor amplitude

[Stacks, Tag 08CJ] is the two-out-of-three property of Tor amplitude in a distinguished triangle.
Clause (1) is available at the Tor-amplitude predicate of
`Stacks.Cohomology.TorAmplitude.HasTorAmplitude`, as
`Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_obj₃`, and clause (3) as
`Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_obj₁`. This file adds clause (2),
the only one of the three that was missing there.

## Main results

* `Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_obj₂`: **[Stacks, Tag 08CJ] (2)**
  at the Tor-amplitude predicate of the ringed space. In a distinguished triangle
  `K ⟶ L ⟶ M ⟶ K[1]`, if `K` and `M` have Tor amplitude in `[a, b]` then so does `L`.

## Implementation notes

Clause (2) is obtained exactly as clause (3) is in
`StacksFrontier/Topology/Sheaves/Cohomology/TorAmplitude/FlatOpcycles.lean`: the abstract form
`TorAmplitude.hasTorAmplitude_obj₂`, which is stated for a bare family of triangulated
endofunctors, is read through
`Stacks.Cohomology.TorAmplitude.FlatOpcycles.tensorSingleFunctor`, the second variable of the
derived tensor product of [Stacks, Tag 06YU] fixed at a module placed in degree zero; the only
work is the translation between the two encodings of "outside `[a, b]`", `i ∉ Set.Icc a b` on the
ringed-space side and `i < a ∨ b < i` on the abstract side.

The consequence of this clause for a direct sum — [Stacks, Tag 08CK] from the summands to the
sum, through the split triangle `K ⟶ K ⊞ L ⟶ L ⟶ K[1]` — is not stated here: the biproduct in
`D(𝒪_X)` is only writable once a `HasBinaryBiproducts` instance has been seated at the spelling
of the category of modules that `Stacks.Cohomology.TorAmplitude.derTensor` is stated at, which is
a choice belonging to the file that needs the sum rather than to this one. The opposite direction
of Tag 08CK is already in this tree as
`Stacks.Cohomology.TorAmplitude.hasTorAmplitude_of_biprod`, proved from the retract property.

## References

* [Stacks Project, Tag 08CJ](https://stacks.math.columbia.edu/tag/08CJ)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open StrictlyPerfect AlgebraicGeometry.RingedSpace.KFlatDerivedPullback

namespace Stacks.Cohomology.TorAmplitude.FlatOpcycles

universe u d

variable {X : RingedSpace.{u, u}} [HasDerivedCategory.{d} (OXMod.{u} X)]

attribute [local instance] _root_.Stacks.Cohomology.TorAmplitude.hasDerivedCategoryModules

/-- **[Stacks, Tag 08CJ] (2) at the ringed-space Tor-amplitude predicate.** In a distinguished
triangle `K ⟶ L ⟶ M ⟶ K[1]` of `D(O_X)`, if `K` has Tor amplitude in `[a, b]` and `M` has Tor
amplitude in `[a, b]`, then `L` has Tor amplitude in `[a, b]`.

This is `TorAmplitude.hasTorAmplitude_obj₂` read through `tensorSingleFunctor`; the only content
is the translation between the two encodings of "outside `[a, b]`". -/
@[stacks 08CJ "(2), at the ringed-space Tor-amplitude predicate"]
theorem hasTorAmplitude_obj₂ (T : Triangle (DerivedCategory (Modules X)))
    (hT : T ∈ distinguishedTriangles) (a b : ℤ)
    (hK : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X T.obj₁ a b)
    (hM : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X T.obj₃ a b) :
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude X T.obj₂ a b := by
  have h := @TorAmplitude.hasTorAmplitude_obj₂ (Modules X) _ _ _ (tensorSingleFunctor X)
    (fun F => (Stacks.Cohomology.TorAmplitude.derTensor X).commShift_left
      ((DerivedCategory.singleFunctor (Modules X) 0).obj F))
    (fun F => (Stacks.Cohomology.TorAmplitude.derTensor X).exact_left
      ((DerivedCategory.singleFunctor (Modules X) 0).obj F))
    T hT a b
    (fun F i hi => hK F i (by simp only [Set.mem_Icc, not_and_or, not_le]; omega))
    (fun F i hi => hM F i (by simp only [Set.mem_Icc, not_and_or, not_le]; omega))
  exact fun F i hi => h F i (by simp only [Set.mem_Icc, not_and_or, not_le] at hi; omega)

end Stacks.Cohomology.TorAmplitude.FlatOpcycles

end
