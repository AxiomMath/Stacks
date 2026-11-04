module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites

/-!
# The small and big étale topoi of a scheme

Let `B` be a big étale site containing a scheme `S`. The *small étale topos* of `S` is the
category of set-valued sheaves on the small étale site of `S`, and the *big étale topos* of
`S` is the category of set-valued sheaves on the big étale site over `S`.

## Main definitions

* `AlgebraicGeometry.smallEtaleTopos` — the small étale topos of `S`.
* `AlgebraicGeometry.bigEtaleTopos` — the big étale topos of `S`.

## Implementation notes

The two names give part (1) and the étale case of part (3) of the source definition; the
remaining cases concern the Zariski, smooth, syntomic and fppf topologies and are in
`StacksFrontier/AlgebraicGeometry/Topologies/Topoi.lean`, beside those sites. Each uses the
Grothendieck topology of the corresponding site. The universe of the values is left free.
These are abbreviations, so that the sheaf category's existing instances and API apply
directly.

## References

* [Stacks Project, Tag 04HQ](https://stacks.math.columbia.edu/tag/04HQ)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 04HQ, part (1).** The small étale topos of `S` is the category of set-valued
sheaves on the small étale site of `S`. -/
@[stacks 04HQ "part (1): the small étale topos"]
public abbrev smallEtaleTopos := Sheaf (SmallEtale.topology B S hS) (Type v)

/-- **Stacks 04HQ, part (3), the étale case.** The big étale topos of `S` is the category of
set-valued sheaves on the big étale site over `S`. -/
@[stacks 04HQ "part (3): the big étale topos"]
public abbrev bigEtaleTopos := Sheaf (BigEtaleOver.topology B S hS) (Type v)

end AlgebraicGeometry

end
