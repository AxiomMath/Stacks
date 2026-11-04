module

public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.AlternatingComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.ComplexComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.OrderedComplex
import StacksCore.Tactic.StacksAttribute

/-!
# The ordered Čech complex is the alternating Čech complex

Let `X` be a topological space, let `U : I → Opens X` be a family of open subsets indexed by a
linearly ordered type and let `ℱ` be an abelian presheaf on `X`. Stacks 01FJ compares the
*ordered* Čech complex, whose degree-`p` term is indexed by the strictly increasing tuples
`i₀ < ⋯ < i_p`, with the *alternating* Čech complex, whose degree-`p` term is the subgroup of
all Čech cochains that vanish on degenerate tuples and change by the sign of a permutation.
The comparison `CechCochains.c` extends a cochain from the increasing tuples to all tuples by
sorting, and `CechCochains.cAddEquiv` is the resulting degreewise isomorphism.

This file assembles those degreewise isomorphisms into an isomorphism of cochain complexes.
The only thing to check is that `CechCochains.c` commutes with the two differentials, which is
`CechCochains.c_chainMap`; the isomorphism of complexes that the source asserts, and that
`CechCochains.cAddEquiv` on its own does not say, is `orderedIsoAlternatingCechComplex` below.

Composing with the comparison of the alternating Čech complex with Mathlib's
`CategoryTheory.cechComplexFunctor` gives the cohomology of the ordered Čech complex as Čech
cohomology in Mathlib's spelling, which is the form a client computing sheaf cohomology needs.

## Main definitions

* `Stacks.Cech.orderedIsoAlternatingCechComplex` — **the ordered Čech complex is the
  alternating Čech complex**, as cochain complexes.
* `Stacks.Cech.orderedCechHomologyIso` — in every degree the cohomology of the ordered Čech
  complex is the cohomology of Mathlib's Čech complex.

## Implementation notes

The degreewise isomorphism is `CechCochains.cAddEquiv` read as an isomorphism of
`AddCommGrpCat`-objects through `AddEquiv.toAddCommGrpIso`. The commutation square is checked on
elements: both composites send an ordered cochain `s` to the alternating cochain underlying
`CechCochains.cechD (CechCochains.c s) = CechCochains.c (CechCochains.ordD s)`, and membership of
  the
alternating subgroup is a proposition, so `Subtype.ext` finishes.

Both complexes are `ℕ`-indexed and `Mathlib`'s `HomologicalComplex.Hom.isoOfComponents` wants
the square for every related pair of degrees, which for `ComplexShape.up ℕ` means `j = i + 1`;
`orderedCechComplex_d` and `alternatingCechComplex_d` are stated in exactly that shape.

The coefficient universe is `max v w` rather than a free `w`, matching
`Stacks.Cech.alternatingCechHomologyIso`: the products in Mathlib's Čech complex are indexed by
tuples of indices, so the ambient universe of abelian groups must contain the indexing universe.

Stacks 01FJ asserts two things about `c`: that it is a morphism of complexes, and that it induces
an isomorphism of complexes `Č_ord^• → Č_alt^•`.  Its covering set is therefore three
declarations, and `orderedIsoAlternatingCechComplex` is the one that carries the second assertion:
`CechCochains.cAddEquiv` is only the degreewise group isomorphism, `CechCochains.c_chainMap` is
only the commutation with the differentials, and neither states that the two assemble into an
isomorphism of cochain complexes.  Stacks 01FI keeps its tag on
`Stacks.Cech.orderedCechComplex`, which is the complex itself.

## References

* [Stacks Project, Tag 01FI](https://stacks.math.columbia.edu/tag/01FI)
* [Stacks Project, Tag 01FJ](https://stacks.math.columbia.edu/tag/01FJ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u v w

namespace Stacks.Cech

variable {X : TopCat.{u}} {I : Type v} [LinearOrder I] (U : I → Opens X)
  (ℱ : TopCat.Presheaf Ab.{max v w} X)

/-- The degree-`p` comparison of the ordered with the alternating Čech cochains, as an
isomorphism of abelian groups: this is `CechCochains.cAddEquiv`, the extension of a cochain from
the strictly increasing tuples to all tuples by sorting. -/
def orderedAlternatingIsoX (p : ℕ) :
    (orderedCechComplex U ℱ).X p ≅ (alternatingCechComplex U ℱ).X p :=
  (CechCochains.cAddEquiv U ℱ p).toAddCommGrpIso

/-- **The ordered Čech complex is the alternating Čech complex.** The degreewise comparison of
Stacks 01FJ is an isomorphism of cochain complexes, because `CechCochains.c` is a chain map.

This is the second assertion of the source: the degreewise isomorphism `CechCochains.cAddEquiv`
and the chain-map property `CechCochains.c_chainMap` together induce an isomorphism of the
complexes themselves. -/
@[stacks 01FJ "the induced isomorphism of complexes"]
def orderedIsoAlternatingCechComplex :
    orderedCechComplex U ℱ ≅ alternatingCechComplex U ℱ :=
  HomologicalComplex.Hom.isoOfComponents (orderedAlternatingIsoX U ℱ) (fun {i j} hij => by
    obtain rfl : i + 1 = j := hij
    rw [orderedCechComplex_d, alternatingCechComplex_d]
    exact AddCommGrpCat.hom_ext <| AddMonoidHom.ext fun s =>
      Subtype.ext (CechCochains.c_chainMap U ℱ i s).symm)

/-- **The cohomology of the ordered Čech complex is Čech cohomology.** In every degree the
cohomology of the ordered Čech complex of Stacks 01FI agrees with the cohomology of Mathlib's
`CategoryTheory.cechComplexFunctor`, by the comparison with the alternating Čech complex and
`Stacks.Cech.alternatingCechHomologyIso`. -/
def orderedCechHomologyIso (n : ℕ) :
    (orderedCechComplex U ℱ).homology n ≅ ((cechComplexFunctor U).obj ℱ).homology n :=
  HomologicalComplex.homologyMapIso (orderedIsoAlternatingCechComplex U ℱ) n ≪≫
    alternatingCechHomologyIso U ℱ n

end Stacks.Cech

end
