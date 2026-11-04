module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ColimitOfConstructibles
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleEnoughAffineObjects
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.EnoughObjects
public import StacksCore.Tactic.StacksAttribute

/-!
# The small étale site has enough affine objects

`CategoryTheory.GrothendieckTopology.HasEnoughObjects`, Stacks 090L (3), asks every object of a
site `C` to carry a covering family indexed in `Type v`, where `v` is the universe of the homs
of `C`. This is the form in which the consumers of Stacks 0BKZ -- notably
`Stacks.Cohomology.HypercohomologyEdge.isIso_hypercohomologyEdge_app_of_acyclic_cover` -- take
"the distinguished objects cover the site" as a hypothesis.

For the small étale site `AlgebraicGeometry.SmallEtale B S hS` of a scheme `S` the two universes
differ: its objects form a `Type (u + 1)`, being a full subcategory of a slice of
`AlgebraicGeometry.BigEtaleSite.Scheme`, while its homs are in `Type u`. So the index of a
covering family has to come down from `Type (u + 1)` to `Type u`, and the generic cut-down
`CategoryTheory.GrothendieckTopology.hasEnoughObjects_of_exists_preZeroHypercover` does not
apply: that one replaces the family by the family of all arrows it contains, which is a subtype
of `Σ V : C, V ⟶ U` and therefore needs `Small.{u} C`, and the small étale site is only
`EssentiallySmall.{u}` (`AlgebraicGeometry.SmallEtale.essentiallySmall`), not `Small.{u}`.

What does come down is one particular covering family. The covering of an object `T` by those of
its affine opens which lie over an affine open of `S`,
`AlgebraicGeometry.SmallEtale.affineSubordinateCover`, is indexed by

`ULift.{u + 1} (Σ V : affineOpens of T, {U : affineOpens of S // V ≤ T.hom ⁻¹ᵁ U})`,

a `ULift` of a type that is already in `Type u`: the opens of a scheme in `Scheme.{u}` form a
`Type u`. Reindexing it along `Equiv.ulift` therefore gives a `Type u`-indexed covering family
with the same generated sieve and the same members, which is exactly what Stacks 090L (3)
demands. So the étale side of the predicate needs no smallness hypothesis at all -- only this
site-specific cover.

## Main results

* `AlgebraicGeometry.SmallEtale.hasEnoughObjects_isQCQSEtaleObject`: it has enough quasi-compact
  quasi-separated objects, `AlgebraicGeometry.IsQCQSEtaleObject`. This is the object-property
  form of `AlgebraicGeometry.SmallEtale.hasEnoughObjects_quasiCompactObjectsSituation`, which is
  the same fact in the `PreZeroHypercover`-valued spelling of Stacks 0937 (1), and it is the
  property over whose members Stacks 0F1F supplies the acyclicity that Stacks 0BKZ consumes.

## Implementation notes

The affine form, `AlgebraicGeometry.SmallEtale.hasEnoughObjects_isAffine`, is in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleEnoughAffineObjects`, which imports
neither the constructible sheaves nor the cohomology of modules, so that it can be used where
the global module-sheaf instances of the latter would leave stuck universe constraints.

Nothing is assumed about `S`: every object of the small étale site has affine opens over affine
opens of `S` whatever `S` is.

The quasi-compact quasi-separated form is deduced from the affine one by
`CategoryTheory.GrothendieckTopology.HasEnoughObjects.mono`, an affine scheme being quasi-compact
and quasi-separated, rather than by rerunning the cut-down; so the one place where the index is
shrunk is `hasEnoughObjects_isAffine`.

## References

* [Stacks Project, Tag 090L](https://stacks.math.columbia.edu/tag/090L)
* [Stacks Project, Tag 0937](https://stacks.math.columbia.edu/tag/0937)
* [Stacks Project, Tag 0BKZ](https://stacks.math.columbia.edu/tag/0BKZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable (X : B.Scheme)

/-- **The small étale site has enough quasi-compact quasi-separated objects.** Every object of
the small étale site of `X` carries a covering family, indexed in the universe of the homs of the
site, by objects whose underlying scheme is quasi-compact and quasi-separated: the affine ones
already are, and `AlgebraicGeometry.SmallEtale.hasEnoughObjects_isAffine` supplies them.

This is the object-property form, Stacks 090L (3), of
`AlgebraicGeometry.SmallEtale.hasEnoughObjects_quasiCompactObjectsSituation`, which states the
same covering in the `PreZeroHypercover`-valued spelling of Stacks 0937 condition (1); the two
differ in the universe of the index, and that form cannot be converted to this one generically.
It is the hypothesis `hB` of
`Stacks.Cohomology.HypercohomologyEdge.isIso_hypercohomologyEdge_app_of_acyclic_cover`,
Stacks 0BKZ, at the object property over whose members Stacks 0F1F supplies acyclicity. -/
public theorem SmallEtale.hasEnoughObjects_isQCQSEtaleObject :
    (SmallEtale.topology B X.obj X.property).HasEnoughObjects (IsQCQSEtaleObject B X) :=
  (SmallEtale.hasEnoughObjects_isAffine B X.obj X.property).mono fun U hU =>
    have : _root_.AlgebraicGeometry.IsAffine
      ((SmallEtale.toScheme B X.obj X.property).obj U) := hU
    ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry

end
