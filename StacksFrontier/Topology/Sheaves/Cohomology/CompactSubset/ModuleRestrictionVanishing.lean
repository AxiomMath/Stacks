module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.InjectiveSheavesRestrictOnto
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.RestrictionVanishing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Vanishing of the higher cohomology of the restriction of an injective sheaf of modules

Let `X` be a topological space, let `R` be a sheaf of rings on `X`, and let `M` be an injective
sheaf of `R`-modules. This file proves

`H^p(Z, M|_Z) = 0` for every `p > 0`

for every quasi-compact `Z ⊆ X` any two distinct points of which have disjoint open
neighbourhoods in `X`, where the cohomology is that of the *underlying abelian sheaf* of `M`,
restricted to `Z`.

This is the form in which [Stacks, Tag 09V5] needs the vanishing of
`StacksFrontier/Topology/Sheaves/Cohomology/CompactSubset/RestrictionVanishing.lean`. That file
proves it for a sheaf which is injective *as an abelian sheaf*; the coefficient sheaf of Tag 09V5
is the underlying abelian
sheaf of an injective sheaf of modules, which is **not** injective as an abelian sheaf. The
bridge is flasqueness: an injective sheaf of modules has surjective restriction maps
([Stacks, Tag 01EA]), hence its underlying abelian sheaf is flasque, and the flasque form
`Stacks.Topology.isZero_cohomologyPresheaf_pullback_of_isFlasque` applies.

## Main results

* `Stacks.Topology.isFlasque_toSheaf_of_injective`: the underlying abelian sheaf of an injective
  sheaf of modules is flasque.
* `Stacks.Topology.isZero_cohomologyPresheaf_pullback_toSheaf_of_injective`: the vanishing.

## Implementation notes

The chosen derived categories are supplied by `HasDerivedCategory.standard`, which produces
`HasDerivedCategory.{max u v}`; for abelian sheaves on a space with coefficients in
`AddCommGrpCat.{u}` that is `HasDerivedCategory.{u + 1}`. Mathlib has no other constructor of
that class, so the two instances are introduced by hand at that universe rather than left to
instance search.

Existence of the right derived functor of sections is found only with
`HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso` given a raised priority;
with the default priority instance search times out.

## References

* [Stacks Project, Tag 01EA](https://stacks.math.columbia.edu/tag/01EA)
* [Stacks Project, Tag 09V3](https://stacks.math.columbia.edu/tag/09V3)
* [Stacks Project, Tag 09V5](https://stacks.math.columbia.edu/tag/09V5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat
open scoped AlgebraicGeometry

namespace Stacks.Topology

universe u

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X : TopCat.{u}}

/-- **The underlying abelian sheaf of an injective sheaf of modules is flasque.** This is
[Stacks, Tag 01EA] read as a statement about the underlying abelian sheaf: the restriction maps
of a sheaf of modules and of its underlying abelian sheaf are the same functions. -/
@[ega "0 12.2.1" "partial", sga "4 V 4.6" "special case"]
theorem isFlasque_toSheaf_of_injective
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (M : SheafOfModules.{u} R) [Injective M] :
    TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf R).obj M) := by
  constructor
  intro U V i
  exact (AddCommGrpCat.epi_iff_surjective _).2
    (Stacks.Cohomology.InjectiveRestriction.injective_restriction_surjective
      R M (leOfHom i.unop))

/-- **The higher cohomology of the restriction of an injective sheaf of modules to a
quasi-compact subset with separated points vanishes.** This is the vanishing
`H^p(Z, M|_Z) = 0` for `p > 0` that [Stacks, Tag 09V5] needs of the fibre of a separated
morphism of ringed spaces with quasi-compact fibre. -/
theorem isZero_cohomologyPresheaf_pullback_toSheaf_of_injective
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (M : SheafOfModules.{u} R) [Injective M] {Z : Set X}
    (hZ : IsCompact Z)
    (hSep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y →
      ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B)
    (p : ℕ) (hp : 0 < p) :
    IsZero ((((TopCat.Sheaf.pullback AddCommGrpCat.{u}
      (Stacks.subsetInclusion X Z)).obj
        ((SheafOfModules.toSheaf R).obj M)).cohomologyPresheaf p).obj (op ⊤)) := by
  let : HasDerivedCategory.{u + 1}
      (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u}) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory.{u + 1} AddCommGrpCat.{u} := HasDerivedCategory.standard _
  have := isFlasque_toSheaf_of_injective R M
  exact isZero_cohomologyPresheaf_pullback_of_isFlasque
    ((SheafOfModules.toSheaf R).obj M) hZ hSep p hp

end Stacks.Topology

end
