module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatOpenRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.BoundedFlatRepresentative
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.FlatRepresentative

/-!
# Tor amplitude is inherited by the restriction to an open subspace

Let `(X, O_X)` be a ringed space, `U ⊆ X` open and `E` an object of `D(O_X)` of Tor amplitude in
`[a, b]`. Then the restriction of `E` to the open subspace `(U, O_X|_U)` again has Tor amplitude
in `[a, b]`.

This is the step every local argument about Tor amplitude begins with: the source phrases it as
"after replacing `X` by a member of a covering", which is legitimate only because the hypothesis
survives the replacement. It is what lets the local data coming from pseudo-coherence and the
local data coming from finite Tor dimension be used on a common open.

## Main results

* `Stacks.Cohomology.TorAmplitude.isFlat_restrictModules`: **restriction to an open subspace
  preserves flatness of a sheaf of modules**, at the spelling of restriction that the
  pseudo-coherence development uses.
* `Stacks.Cohomology.TorAmplitude.hasTorAmplitude_restrictModules`: **Tor amplitude in `[a, b]`
  is inherited by the restriction to an open subspace.**

## Implementation notes

The proof goes through the bounded flat representative of Stacks 08CI rather than through the
definition, exactly as the ringed-site analogue
`Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_derivedRestriction` does. Tor
amplitude on the subspace is measured against the derived tensor product of the subspace, and no
datum on `X` measures anything on `X|_U`, so a proof that unfolded the definition would have to
compare the two operations. There is nothing to compare if the representative is produced first:
Stacks 08CI turns Tor amplitude in `[a, b]` into a complex of flat `O_X`-modules concentrated in
`[a, b]` representing `E`; restriction to an open subspace is exact, preserves flatness by
`AlgebraicGeometry.SheafOfModules.isFlat_restrictMod`, and carries a zero module to a zero
module, so the restricted complex is again flat and concentrated in `[a, b]`; and the easy
direction of Stacks 08CI on the subspace, which needs no comparison, concludes.

Flatness is *not* transported here across the slice-to-subspace equivalence of module categories
from Stacks 0E8J, whose conclusion is flatness over the slice sheaf of rings `O_X|_U` on
`Over U`: an equivalence of categories of modules need not carry one tensor product to the
other, so that route would owe a comparison of tensor products. The route taken instead is the
stalkwise criterion of Stacks 05NE; see
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FlatOpenRestriction.lean`.

The universes of the space, its structure sheaf and its modules all coincide, as they already
must for `StrictlyPerfect.OXMod` and for Stacks 08CI; the derived category's hom universe is
taken to be the same for `X` and for its open subspaces, because the representative is carried
from one to the other by a single functor on derived categories.

## References

* [Stacks Project, Tag 08CG](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Tag 08CI](https://stacks.math.columbia.edu/tag/08CI)
* [Stacks Project, Tag 0E8J](https://stacks.math.columbia.edu/tag/0E8J)
* [Stacks Project, Tag 05NE](https://stacks.math.columbia.edu/tag/05NE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open StrictlyPerfect AlgebraicGeometry.RingedSpace.PseudoCoherence

namespace Stacks.Cohomology.TorAmplitude

universe u d

/-- **Restriction to an open subspace preserves flatness**, at the spelling of restriction that
the pseudo-coherence development of Tag 08CB uses.

This is `AlgebraicGeometry.SheafOfModules.isFlat_restrictMod`: restriction of modules to an open
subspace is the pushforward along the inclusion of the opens of the subspace, and the structure
sheaf of the subspace is the restriction of the structure sheaf, so the two statements are the
same one. -/
theorem isFlat_restrictModules (X : RingedSpace.{u, u}) (U : Opens X.carrier) (M : OXMod.{u} X)
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) M) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (X.restrict U.isOpenEmbedding).sheaf)
      ((restrictModules.{u} X U).obj M) :=
  AlgebraicGeometry.SheafOfModules.isFlat_restrictMod U X.sheaf M hM

variable {X : RingedSpace.{u, u}} [HasDerivedCategory.{d} (OXMod.{u} X)]
variable [∀ U : Opens X.carrier,
  HasDerivedCategory.{d} (OXMod.{u} (X.restrict U.isOpenEmbedding))]

attribute [local instance] restrictModules_preservesFiniteLimits
  restrictModules_preservesFiniteColimits

/-- **Tor amplitude restricts to an open subspace.** If an object `E` of `D(O_X)` has Tor
amplitude in `[a, b]`, then so does its restriction to the open subspace `X|_U`.

Stacks 08CI represents `E` by a complex of flat `O_X`-modules concentrated in `[a, b]`;
restriction keeps the terms flat, by `isFlat_restrictModules`, and keeps the complex
concentrated in `[a, b]`, restriction preserving zero objects; and a complex of that shape has
Tor amplitude in `[a, b]` by the direction of Stacks 08CI which needs no input. -/
theorem hasTorAmplitude_restrictModules (U : Opens X.carrier)
    (E : DerivedCategory (OXMod.{u} X)) (a b : ℤ) (hab : a ≤ b)
    (hamp : HasTorAmplitude X E a b) :
    HasTorAmplitude (X.restrict U.isOpenEmbedding)
      ((restrictModules.{u} X U).mapDerivedCategory.obj E) a b := by
  obtain ⟨K, hflat, hzero, ⟨e⟩⟩ :=
    BoundedFlatRepresentative.exists_flat_representative_of_hasTorAmplitude E a b hab hamp
  refine Stacks.TorAmplitude.FlatRepresentative.hasTorAmplitude_of_flat_representative
    _ a b (restrictComplex K U) (fun i => ?_) (fun i hi => ?_) ?_
  · exact isFlat_restrictModules X U (K.X i) (hflat i)
  · exact (restrictModules.{u} X U).map_isZero (hzero i hi)
  · exact ((restrictModules.{u} X U).mapDerivedCategoryFactors.app K).symm ≪≫
      (restrictModules.{u} X U).mapDerivedCategory.mapIso e

/-- **Finite Tor dimension restricts to an open subspace.** An interval containing the Tor
amplitude of `E` contains that of every restriction of `E`; the interval may be taken nonempty
by widening it. -/
theorem hasFiniteTorDimension_restrictModules (U : Opens X.carrier)
    (E : DerivedCategory (OXMod.{u} X)) (h : HasFiniteTorDimension X E) :
    HasFiniteTorDimension (X.restrict U.isOpenEmbedding)
      ((restrictModules.{u} X U).mapDerivedCategory.obj E) := by
  obtain ⟨a, b, hamp⟩ := h
  exact ⟨min a b, max a b, hasTorAmplitude_restrictModules U E (min a b) (max a b) min_le_max
    (fun F i hi => hamp F i (fun hmem => hi ⟨(min_le_left a b).trans hmem.1,
      hmem.2.trans (le_max_right a b)⟩))⟩

end Stacks.Cohomology.TorAmplitude

end
