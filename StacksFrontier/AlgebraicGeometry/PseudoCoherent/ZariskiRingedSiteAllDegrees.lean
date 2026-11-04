module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineCrossing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.Summands
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.SiteComparison

/-!
# Pseudo-coherence in all degrees on the small Zariski site of a scheme

Stacks 08FT part (3) is stated on a ringed site and Stacks 08CB part (3) on a ringed space, and
on the small Zariski site of a scheme the two agree.  In a fixed degree that is
`AlgebraicGeometry.Scheme.isPseudoCoherentFrom_zariskiRingedSite_iff`; this file adds the
all-degrees companion, which the two clauses state separately.

## Main results

* `AlgebraicGeometry.Scheme.isPseudoCoherent_zariskiRingedSite_iff`: an object of the derived
  category of `𝒪_S`-modules is pseudo-coherent on `AlgebraicGeometry.Scheme.zariskiRingedSite`
  exactly when it is pseudo-coherent on `AlgebraicGeometry.Scheme.toRingedSpace`.

## Implementation notes

The all-degrees clause of Stacks 08FT (3) and of Stacks 08CB (3) is not the conjunction over all
degrees of the fixed-degree clause on the nose: each asks for a *single* complex representing the
object which is `m`-pseudo-coherent for every `m`, and a family of degreewise statements supplies a
different representative in each degree.  Both predicates do nevertheless collapse to that
conjunction, on the site side by
`AlgebraicGeometry.RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom` (the forward
direction of Stacks 08FU (2)) and on the space side by
`AlgebraicGeometry.RingedSpace.isPseudoCoherent_iff_forall` (Stacks 08CC (2)), so the fixed-degree
comparison can be read under the quantifier.  Those two collapses are the whole content of the
proof; no new mathematics is involved.

The proof is in term mode and not by `rw`.  `AlgebraicGeometry.RingedSpace.IsPseudoCoherent` is an
`abbrev`, so by the time the statement is elaborated the right-hand side is already its unfolded
existential and there is no occurrence of the predicate's head for `rw` to find; `Iff.trans`
against the collapse lemma unifies up to that unfolding and goes through.

The derived-category instance has to be restated at the ringed-space spelling of the sheaf of
rings.  `AlgebraicGeometry.Scheme.zariskiRingedSite_ringSheaf` and
`Stacks.DerivedQCoh.oxMod_eq_sheafOfModules` make the two categories equal by `rfl`, but instance
search does not cross between them, so the hypothesis is taken at the site spelling and carried
over by `inferInstanceAs`.

## References

* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 08FU](https://stacks.math.columbia.edu/tag/08FU)
* [Stacks Project, Tag 08CB](https://stacks.math.columbia.edu/tag/08CB)
* [Stacks Project, Tag 08CC](https://stacks.math.columbia.edu/tag/08CC)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u d

namespace AlgebraicGeometry.Scheme

-- The derived category of `𝒪_S`-modules read at the underlying ringed space is the same
-- instance found at the other spelling of the sheaf of rings, which instance search does not
-- cross.  `StacksFrontier/Topology/Sheaves/Cohomology/StrictlyPerfect/SiteComparison.lean` already
-- declares it; only its instance attribute is file-local,
-- so it is re-enabled here rather than restated.
attribute [local instance] AlgebraicGeometry.Scheme.hasDerivedCategoryToRingedSpace

/-- **Pseudo-coherence on the small Zariski ringed site of a scheme is pseudo-coherence on its
underlying ringed space, in all degrees.**  The all-degrees companion of
`AlgebraicGeometry.Scheme.isPseudoCoherentFrom_zariskiRingedSite_iff`: Stacks 08FT (3) at
`AlgebraicGeometry.Scheme.zariskiRingedSite` and Stacks 08CB (3) at
`AlgebraicGeometry.Scheme.toRingedSpace` are the same condition.

Both predicates collapse to the conjunction over all degrees of their fixed-degree clause, by
`AlgebraicGeometry.RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom` and
`AlgebraicGeometry.RingedSpace.isPseudoCoherent_iff_forall`, under which quantifier the
fixed-degree comparison applies degree by degree. -/
public theorem isPseudoCoherent_zariskiRingedSite_iff (S : Scheme.{u})
    [HasDerivedCategory.{d}
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))]
    (E : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))) :
    S.zariskiRingedSite.IsPseudoCoherent E ↔
      AlgebraicGeometry.RingedSpace.IsPseudoCoherent (X := S.toRingedSpace) E :=
  (RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom S.zariskiRingedSite E).trans
    ((forall_congr' fun m => isPseudoCoherentFrom_zariskiRingedSite_iff S E m).trans
      (RingedSpace.isPseudoCoherent_iff_forall E).symm)

end AlgebraicGeometry.Scheme

end
