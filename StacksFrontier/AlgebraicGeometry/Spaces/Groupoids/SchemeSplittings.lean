module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Pullback

/-!
# Splittings of a groupoid scheme at a point of its object scheme

An *open finite subgroupoid* of a groupoid scheme `(U, R, s, t, c)` is a groupoid scheme on the
same object scheme `U` whose arrow scheme is an open subscheme `P ⊆ R`, whose source and target
are the restrictions `s|_P`, `t|_P` of `s` and `t`, whose composition is the restriction of `c`,
and whose restricted source and target are finite.  Such a subgroupoid is a *quasi-splitting*
of `R` over a point `u` of `U` when it contains the identity arrow `e(u)`, and a *strong
splitting* of `R` over `u` when it contains every arrow from `u` to itself.

## Main definitions

* `Stacks.Groupoids.GroupoidScheme.OpenFiniteSubgroupoid`: conditions (a) and (b) of
  Tag 04RK, read for a groupoid scheme.
* `Stacks.Groupoids.GroupoidScheme.QuasiSplitting` and
  `Stacks.Groupoids.GroupoidScheme.IsQuasiSplitAt`: a quasi-splitting of a groupoid scheme over
  a point of its object scheme, and the assertion that one exists.
* `Stacks.Groupoids.GroupoidScheme.StrongSplitting` and
  `Stacks.Groupoids.GroupoidScheme.IsStronglySplitAt`: a strong splitting of a groupoid scheme
  over a point of its object scheme, and the assertion that one exists.

## Main results

* `Stacks.Groupoids.GroupoidScheme.OpenFiniteSubgroupoid.toQuasiSplitting` is the footnote to
  part (3) of Tag 04RK: condition (c) is implied by condition (a), so an open finite
  subgroupoid is a quasi-splitting over *every* point of the object scheme.
* `Stacks.Groupoids.GroupoidScheme.StrongSplitting.toQuasiSplitting` and
  `Stacks.Groupoids.GroupoidScheme.IsStronglySplitAt.isQuasiSplitAt`: a strong splitting is in
  particular a quasi-splitting, by the same footnote.

## Implementation notes

Tag 04RK is stated for a groupoid in algebraic spaces, and that reading is already available as
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.QuasiSplitting`.  What is defined here is the same
notion for a `Stacks.Groupoids.GroupoidScheme`, which is the form taken by the conclusions of
Tags 04RX, 04RZ, 0DTE and 04S0: there the étale neighbourhood is a *scheme*, affine in the last
two, and the restricted groupoid is a groupoid *scheme*.  An open subspace of a scheme is a
scheme, so the two readings agree on a groupoid scheme; identifying them requires realizing a
groupoid scheme as a groupoid in algebraic spaces, which is not available here, and no such
bridge is claimed.

Part (2) of the tag, a *splitting*, is not defined here.  Its condition (c) is membership of the
fibre of the stabilizer group scheme over `u`, so unlike parts (1) and (3) it is not a condition
on points of the arrow scheme alone; nothing in the étale-localization results that consume this
module — Tags 04RX, 04RY, 04RZ and 04S0 — uses it.

Two notes on the surrounding material, recorded here because they are easy to be misled by and
belong to no module of their own.  First, the module docstrings of
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeEtaleLocalization` and
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FinitePartSchemeLocalization` say that this
library proves only clauses (1) and (2) of Tag 04RU and not clause (3); that is out of date.
Clause (3) is proved, as
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.FinitePartGroupoid` together with
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.nonempty_finitePartGroupoid`.  What those two
modules actually assume is the *restriction-shaped* form of clause (3), namely an
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.OpenFiniteSubgroupoid` of the restriction, and the
four obstructions between the two shapes are the ones listed in the docstring of
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.SplittingSchemes`.  Second, three pieces of
infrastructure this neighbourhood uses are duplicated and should be unified rather than copied
again: the preservation of equivalence relations under restriction, in both
`StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionEquivalenceRelation` and
`StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatQuotient.RestrictionAffineQuotient`; the
invariant affine open of Tag 03JE, in both
`StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.InvariantAffineOpen` and
`StacksFrontier.AlgebraicGeometry.Groupoids.GroupSchemeProperties.InvariantAffineOpen`; and cases
(1) and (2) of Tag 01ZY, in both
`StacksFrontier.AlgebraicGeometry.AmpleCluster.QuasiAffineAndImmersion` and
`StacksFrontier.AlgebraicGeometry.Properties.FiniteSetInAffineOpen`.

Conditions (a) and (b) are carried by structure rather than by a predicate on a subset of the
arrow scheme: the subgroupoid is a groupoid scheme in its own right, together with a morphism
`Stacks.Groupoids.GroupoidScheme.Hom` into the ambient groupoid whose map on objects is the
identity of `U` and whose map on arrows is an open immersion.  That `Hom` carries exactly the
compatibilities `s|_P = s ∘ ι` and `t|_P = t ∘ ι` and the assertion that the composition of the
subgroupoid is the restriction of the ambient composition.  Bundling it this way is what makes a
splitting usable as an input to results about groupoid schemes — for instance the invariant
affine open of Tag 03JE, which is stated for a groupoid scheme with finite locally free source
and target.  The equality of object schemes is recorded as a field and transported with
`CategoryTheory.eqToHom`, following `AlgebraicGeometry.GroupoidScheme.Restriction`.

Finiteness is finiteness of the structure maps of the subgroupoid, whose target is its own
object scheme; by the recorded equality of object schemes this is finiteness of
`s|_P, t|_P : P → U`.

Condition (c) is membership of a point of the arrow scheme in the open subscheme `P`, which for
an open immersion is membership in the range of the inclusion: the point `e(u)` for part (3),
and every point with source and target `u` for part (1).

## References

* [Stacks Project, Tag 04RK](https://stacks.math.columbia.edu/tag/04RK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Groupoids.GroupoidScheme

variable {S : Scheme.{u}}

/-- Transporting a point of a scheme over `S` along an equality of objects of `Over S` and back
again returns the point. -/
theorem over_eqToHom_apply_symm {X Y : Over S} (h : X = Y) (y : Y.left) :
    (eqToHom h).left.base ((eqToHom h.symm).left.base y) = y := by
  cases h
  rfl

/-- An open subscheme of the arrow scheme of a groupoid scheme which is itself a groupoid scheme
on the ambient object scheme, with the restricted source and target morphisms finite and with
composition the restriction of the ambient composition.

This is conditions (a) and (b) shared by the three splittings of **Stacks 04RK**, read for a
groupoid scheme. -/
@[stacks 04RK "conditions (a) and (b) on the open subscheme, for a groupoid scheme"]
structure OpenFiniteSubgroupoid (G : GroupoidScheme S) where
  /-- The subgroupoid `(U, P, s|_P, t|_P, c|_{P ×_{s, U, t} P})`. -/
  subgroupoid : GroupoidScheme S
  /-- Its scheme of objects is the ambient scheme of objects. -/
  objects_eq : subgroupoid.objects = G.objects
  /-- The inclusion of the subgroupoid into the ambient groupoid.  Its two compatibilities say
  that the source and target of the subgroupoid are the restrictions of the ambient ones, and
  its compatibility with composition says that the composition of the subgroupoid is the
  restriction of the ambient composition. -/
  inclusion : Hom subgroupoid G
  /-- The inclusion is the identity on objects. -/
  mapObjects_eq : inclusion.mapObjects = eqToHom objects_eq
  /-- The scheme of arrows of the subgroupoid is an open subscheme of the ambient scheme of
  arrows. -/
  arrows_open : IsOpenImmersion inclusion.mapArrows.left
  /-- The restricted source morphism `s|_P` is finite. -/
  source_finite : IsFinite subgroupoid.source.left
  /-- The restricted target morphism `t|_P` is finite. -/
  target_finite : IsFinite subgroupoid.target.left

/-- A quasi-splitting of a groupoid scheme over a point `u` of its object scheme: an open finite
subgroupoid whose scheme of arrows contains the identity arrow `e(u)`. -/
@[stacks 04RK "part (3), for a groupoid scheme: a quasi-splitting of R over u"]
structure QuasiSplitting (G : GroupoidScheme S) (u : G.objects.left) extends
    OpenFiniteSubgroupoid G where
  /-- The identity arrow at `u` lies in the subgroupoid.  The source records that this condition
  is implied by the previous ones. -/
  contains_identity : ∃ p : subgroupoid.arrows.left,
    inclusion.mapArrows.left.base p = G.identity.left.base u

/-- A groupoid scheme is *quasi-split* over a point of its object scheme when a quasi-splitting
there exists. -/
@[stacks 04RK "part (3), for a groupoid scheme: R is quasi-split over u"]
abbrev IsQuasiSplitAt (G : GroupoidScheme S) (u : G.objects.left) : Prop :=
  Nonempty (QuasiSplitting G u)

/-- The footnote to part (3) of **Stacks 04RK**: condition (c) is implied by condition (a).
An open finite subgroupoid of a groupoid scheme contains the identity arrow at every point of
the object scheme, because the inclusion is a morphism of groupoid schemes which is the identity
on objects, and so carries the identity section of the subgroupoid to that of the ambient
groupoid. -/
@[stacks 04RK "the footnote to part (3): condition (c) follows from condition (a)"]
def OpenFiniteSubgroupoid.toQuasiSplitting {G : GroupoidScheme S} (P : OpenFiniteSubgroupoid G)
    (u : G.objects.left) : QuasiSplitting G u where
  toOpenFiniteSubgroupoid := P
  contains_identity := by
    refine ⟨P.subgroupoid.identity.left.base ((eqToHom P.objects_eq.symm).left.base u), ?_⟩
    have h := congrArg
      (fun f : P.subgroupoid.objects ⟶ G.arrows =>
        f.left.base ((eqToHom P.objects_eq.symm).left.base u))
      P.inclusion.map_identity
    simp only [Over.comp_left, Scheme.Hom.comp_apply, P.mapObjects_eq,
      over_eqToHom_apply_symm] at h
    exact h.symm

/-- A strong splitting of a groupoid scheme over a point `u` of its object scheme: an open
finite subgroupoid whose scheme of arrows contains every arrow of `R` whose source and target
are both `u`.

This is part (1) of **Stacks 04RK**, read for a groupoid scheme.  It is strictly stronger than
`Stacks.Groupoids.GroupoidScheme.QuasiSplitting`, whose condition (c) asks only for the identity
arrow `e(u)`; see `Stacks.Groupoids.GroupoidScheme.StrongSplitting.toQuasiSplitting`. -/
@[stacks 04RK "part (1), for a groupoid scheme: a strong splitting of R over u"]
structure StrongSplitting (G : GroupoidScheme S) (u : G.objects.left) extends
    OpenFiniteSubgroupoid G where
  /-- Every arrow whose source and whose target are both `u` lies in the subgroupoid. -/
  contains_stabilizer : ∀ r : G.arrows.left, G.source.left.base r = u →
    G.target.left.base r = u → ∃ p : subgroupoid.arrows.left,
      inclusion.mapArrows.left.base p = r

/-- A groupoid scheme is *strongly split* over a point of its object scheme when a strong
splitting there exists. -/
@[stacks 04RK "part (1), for a groupoid scheme: R is strongly split over u"]
abbrev IsStronglySplitAt (G : GroupoidScheme S) (u : G.objects.left) : Prop :=
  Nonempty (StrongSplitting G u)

/-- A strong splitting of a groupoid scheme over a point of its object scheme is in particular
a quasi-splitting there.  Condition (c) of part (3) of **Stacks 04RK** is not deduced from
condition (c) of part (1) — that would need the identity arrow to have source and target the
given point, which is true but is not what is recorded — but from condition (a), by the footnote
`Stacks.Groupoids.GroupoidScheme.OpenFiniteSubgroupoid.toQuasiSplitting`. -/
def StrongSplitting.toQuasiSplitting {G : GroupoidScheme S} {u : G.objects.left}
    (P : StrongSplitting G u) : QuasiSplitting G u :=
  P.toOpenFiniteSubgroupoid.toQuasiSplitting u

/-- A groupoid scheme which is strongly split over a point of its object scheme is quasi-split
there. -/
theorem IsStronglySplitAt.isQuasiSplitAt {G : GroupoidScheme S} {u : G.objects.left}
    (h : IsStronglySplitAt G u) : IsQuasiSplitAt G u :=
  h.elim fun P => ⟨P.toQuasiSplitting⟩

end Stacks.Groupoids.GroupoidScheme

end

