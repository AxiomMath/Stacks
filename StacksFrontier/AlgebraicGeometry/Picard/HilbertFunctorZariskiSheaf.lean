module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorFpqcGluing
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcQuasicoherentReduction

/-!
# The Hilbert functor of points is a Zariski sheaf

Let `X` be a scheme over `S` and let `d` be a natural number. The degree-`d` Hilbert functor of
points satisfies the sheaf property for the fpqc topology on the schemes over `S`, which is
Stacks Tag 0B95. The Zariski topology is coarser than the fpqc topology, so the Hilbert functor
is a fortiori a sheaf for the Zariski topology on the schemes over `S`, and its total presheaf
on the category of all schemes is a sheaf for the Zariski topology on that category.

## Main results

* `CategoryTheory.GrothendieckTopology.over_le_over` — localizing two comparable Grothendieck
  topologies at an object preserves the comparison.
* `Stacks.Hilbert.isSheaf_zariskiTopology_hilbertFunctorOfRank` — the degree-`d` Hilbert functor
  is a sheaf for the Zariski topology on the schemes over `S`.
* `Stacks.Hilbert.isSheaf_zariskiTopology_totalPresheaf_hilbertFunctorOfRank` — the same
  statement for the total presheaf on the category of all schemes.

## References

* [Stacks Project, Tag 0B9A](https://stacks.math.columbia.edu/tag/0B9A)
* [Stacks Project, Tag 0B95](https://stacks.math.columbia.edu/tag/0B95)
* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

universe v u

namespace CategoryTheory.GrothendieckTopology

/-- Localizing two comparable Grothendieck topologies at an object preserves the comparison: a
sieve of `Over X` is covering for the localization of `J` exactly when the sieve of `X` it
corresponds to is covering for `J`. -/
theorem over_le_over {C : Type u} [Category.{v} C] {J K : GrothendieckTopology C} (h : J ≤ K)
    (X : C) : J.over X ≤ K.over X :=
  fun _ _ hS ↦ h _ hS

end CategoryTheory.GrothendieckTopology

namespace Stacks.Hilbert

/-- **The degree-`d` Hilbert functor of points of `X` over `S` satisfies the sheaf property for
the Zariski topology on the schemes over `S`.** -/
theorem isSheaf_zariskiTopology_hilbertFunctorOfRank {S : Scheme.{u}} (X : Over S) (d : ℕ) :
    Presheaf.IsSheaf (Scheme.zariskiTopology.{u}.over S) (hilbertFunctorOfRank X d) :=
  (isSheaf_fpqcTopology_hilbertFunctorOfRank X d).of_le
    (GrothendieckTopology.over_le_over Scheme.zariskiTopology_le_fpqcTopology S)

/-- **The total presheaf of the Hilbert functor is a Zariski sheaf.** The total presheaf of the
degree-`d` Hilbert functor — the presheaf on the category of all schemes sending `T` to the pairs
consisting of a morphism `T ⟶ S` and a degree-`d` Hilbert family in `X` over it — is a sheaf for
the Zariski topology on the category of all schemes. -/
theorem isSheaf_zariskiTopology_totalPresheaf_hilbertFunctorOfRank {S : Scheme.{u}} (X : Over S)
    (d : ℕ) :
    Presieve.IsSheaf Scheme.zariskiTopology.{u}
      (Stacks.Sites.totalPresheaf (hilbertFunctorOfRank X d)) :=
  (Stacks.Sites.isSheaf_over_iff_isSheaf_totalPresheaf Scheme.zariskiTopology.{u} _
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)).1
    ((isSheaf_iff_isSheaf_of_type _ _).1 (isSheaf_zariskiTopology_hilbertFunctorOfRank X d))

end Stacks.Hilbert

end
