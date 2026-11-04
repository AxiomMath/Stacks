module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Size.BlowupContains
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupAtClosedPointExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupEquivalenceRelationTransitivity

/-!
# The blowing up of an algebraic space at a closed point exists, unconditionally

`AlgebraicGeometry.Space.exists_isBlowupAtClosedPoint` produces the blowing up of an algebraic
space `X` at a closed point `z ∈ |X|`, but takes three side conditions `hcU`, `hcR`, `hcRR`:
that the relative projective spectra of the Rees algebras on the presenting scheme, on the
relation scheme and on its double are schemes of the ambient big fppf site. This file
discharges all three and restates the existence with no hypothesis beyond `z` being closed.

Each of the three is the relative `Proj` of the Rees algebra of a quasi-coherent sheaf of
ideals on a scheme that is *already* an object of the site — the presenting scheme `U`, the
relation scheme `R = U ×_X U`, and `R ×_U R` — so each is an instance of
`AlgebraicGeometry.BigFppfSite.contains_relativeProj_reesSituation`, which bounds the size of
such a relative `Proj` by `Bound(size) = size ^ ℵ₀` and needs nothing of the ideal sheaf.

That last point is what makes this possible at all. The centre here is the reduced closed
subspace supported on `{z}` (`AlgebraicGeometry.Space.closedPointSubspace`), whose ideal is
not of finite type on a general algebraic space; so the route to the side conditions through
Stacks 000R (5) — `Stacks.RelativeProj.Situation.relativeProj_locallyOfFiniteType`, which
needs `Stacks.RelativeProj.Situation.IsFiniteType` — is unavailable, and the purely
cardinal-arithmetic bound is what discharges them.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  [HasSheafify (BigFppfOver.topology B S hS) (Type u)] {X : AlgebraicSpaces B S hS}

/-- **The blowing up of an algebraic space at a closed point exists** (Stacks 0BHE), with no
size side conditions.

The three conditions of `AlgebraicGeometry.Space.exists_isBlowupAtClosedPoint` are discharged
by `AlgebraicGeometry.BigFppfSite.contains_relativeProj_reesSituation`: each asks that the
relative `Proj` of the Rees algebra of a sheaf of ideals on an object of the site lie in the
site, and that holds for every quasi-coherent sheaf of ideals, the containment of the base
being supplied by the object itself. -/
theorem exists_isBlowupAtClosedPoint_unconditional (z : points B S hS X.obj)
    (hz : IsClosed ({z} : Set (points B S hS X.obj))) :
    ∃ (X' : AlgebraicSpaces B S hS) (b : X' ⟶ X), IsBlowupAtClosedPoint B S hS z hz b :=
  exists_isBlowupAtClosedPoint z hz
    (B.contains_relativeProj_reesSituation
      (presentationOfIsAlgebraicSpace B S hS X.obj X.property).U.left.2 _)
    (B.contains_relativeProj_reesSituation
      (presentationOfIsAlgebraicSpace B S hS X.obj X.property).R.left.2 _)
    (B.contains_relativeProj_reesSituation
      (presentationDouble
        (presentationOfIsAlgebraicSpace B S hS X.obj X.property)).left.2 _)

end AlgebraicGeometry.Space

end
