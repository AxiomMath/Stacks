module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHom

/-!
# The fpqc site of the test schemes over an algebraic space

Let `Y` be an algebraic space over a scheme `S` of a big fppf site.  The test schemes over `Y`
are the objects `AlgebraicGeometry.Space.SchemesOver Y` of the big fppf site equipped with a
morphism to `Y`; forgetting the structure morphism and passing to the underlying scheme gives a
functor to schemes, and comparing a family of test schemes with its underlying family of
morphisms of schemes gives the fpqc topology on them.

## Main definitions

* `AlgebraicGeometry.Space.testSchemeFunctor`: the underlying-scheme functor on the test
  schemes over an algebraic space.
* `AlgebraicGeometry.Space.fpqcTopology`: the fpqc topology on those test schemes, the topology
  whose covering sieves are the ones whose underlying families of scheme morphisms cover for
  the fpqc topology on schemes.

## References

* [Stacks Project, Tag 0CWW](https://stacks.math.columbia.edu/tag/0CWW)
* [Stacks Project, Tag 083H](https://stacks.math.columbia.edu/tag/083H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The underlying-scheme functor on the test schemes over an algebraic space: forget the
structure morphism to `Y`, then take the underlying scheme of the object of the big fppf
site. -/
def testSchemeFunctor (Y : AlgebraicSpaces B S hS) : SchemesOver Y ⥤ Scheme.{u} :=
  CostructuredArrow.proj (schemeSpaceFunctor B S hS) Y ⋙ BigFppfOver.toScheme B S hS

/-- The fpqc topology on the test schemes over an algebraic space: a sieve covers exactly when
the family of underlying morphisms of schemes it contains covers for the fpqc topology on
schemes. -/
def fpqcTopology (Y : AlgebraicSpaces B S hS) : GrothendieckTopology (SchemesOver Y) :=
  (Scheme.fpqcPrecoverage.comap (testSchemeFunctor Y)).toGrothendieck

end AlgebraicGeometry.Space

end
