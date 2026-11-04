module

public import StacksFrontier.AlgebraicGeometry.Variety.Projective.LinesAvoidingSubvariety
public import StacksCore.Tactic.StacksAttribute

/-!
# Projections in the projective space of a vector space

Over an algebraically closed field the closed points of `𝐏(V) = Proj (Sym V)` are the
one-dimensional quotients `V → L_p` of `V`; the degree-one forms vanishing at such a point `p`
form the hyperplane `W_p = Ker(V → L_p)`, and the inclusion `W_p ⊆ V` induces the projection
away from `p`, the morphism `r_p : 𝐏(V) ∖ {p} → 𝐏(W_p)`.

## Main results

Those four conventions are the content of the section itself, and the declarations realizing
them are collected here as its covering set: the closed points are
`AlgebraicGeometry.ProjectiveSpaceOfModule.closedPointsEquivDual`, the hyperplane `W_p` is
`AlgebraicGeometry.ProjectiveSpaceOfModule.pointSubmodule`, and the projection and its domain
of definition are `AlgebraicGeometry.ProjectiveSpaceOfModule.projection` and
`AlgebraicGeometry.ProjectiveSpaceOfModule.coe_mapDomain_pointSubmodule`. The projective space
`𝐏(V)` is `AlgebraicGeometry.projectiveSpaceOfModule`, which the section takes from Tag 0FCY.

## Implementation notes

The library states each convention in the generality in which it is used: `pointSubmodule` is
the space of degree-one forms vanishing at an arbitrary point of `𝐏(V)`, a hyperplane exactly
for a closed point over an algebraically closed field
(`AlgebraicGeometry.ProjectiveSpaceOfModule.finrank_quotient_pointSubmodule`), and `projection`
is the linear projection away from the linear subspace cut out by an arbitrary submodule, which
is `r_p` for the submodule `W_p`.

The labelled items of the section are formalized elsewhere and carry their own tags: 0B1P, 0B1Q,
0B1R, 0B1S, 0B2T, 0B2U, 0B2V, 0B2W and 0H8A.

## References

* [Stacks Project, Tag 0B1N](https://stacks.math.columbia.edu/tag/0B1N)
-/

@[expose] public section

open AlgebraicGeometry.ProjectiveSpaceOfModule

-- Tag 0B1N is the section tag of `\section{Projections}`; these four declarations are its
-- covering set, one for each convention the section introduces.
add_to_stacks 0B1N "section tag; the closed points of 𝐏(V) are the one-dimensional quotients \
V → L_p of V" closedPointsEquivDual
add_to_stacks 0B1N "section tag; W_p = Ker(V → L_p), the degree-one forms vanishing at p"
  pointSubmodule
add_to_stacks 0B1N "section tag; the projection r_p away from p, for the submodule W_p"
  projection
add_to_stacks 0B1N "section tag; the domain of definition of r_p is 𝐏(V) ∖ {p}"
  coe_mapDomain_pointSubmodule
