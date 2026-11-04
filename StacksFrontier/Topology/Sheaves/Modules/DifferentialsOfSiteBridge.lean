module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PrincipalPartsUniversal
public import StacksFrontier.Topology.Sheaves.Modules.Differentials

/-!
# The two spellings of the sheaf of relative differentials agree

For a morphism `φ : O₁ ⟶ O₂` of sheaves of commutative rings on a topological space, the
repository names the sheaf of relative differentials twice: once over the open-cover site
spelled as `TopCat.Sheaf`, as `AlgebraicGeometry.SheafOfModules.moduleOfDifferentials`, and
once over a general site, as
`AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsOfSite`. Both are the representing
object `(derivationsFunctor O₁ O₂ φ).coreprX` of the derivations functor, so they are equal.

## Main results

* `AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsOfSite_eq_moduleOfDifferentials`:
  the site-level sheaf of relative differentials of a morphism of sheaves of commutative
  rings on a topological space is the open-cover-site one.

## Implementation notes

The statement is made at an arbitrary topological space and arbitrary sheaves of commutative
rings on it, where it holds by `rfl`: the two sides are the same application of
`CategoryTheory.Functor.coreprX`, and the two corepresentability instances involved are
proofs of one `Prop`.

The generality is what makes the statement usable. `TopCat.Sheaf` is a `def` rather than an
abbreviation, so at a *concrete* sheaf of rings — the structure sheaf of a scheme, say — the
elaborator does not join the two spellings of the category of sheaves within the heartbeat
budget, and the equation cannot be written down there at all. Applying this lemma, with its
arguments supplied, never asks it to: the sheaves and the morphism are checked against the
`TopCat.Sheaf` spelling only, and the site spelling in the conclusion arrives already
instantiated.

## References

* [Stacks Project, Tag 04BL](https://stacks.math.columbia.edu/tag/04BL)
* [Stacks Project, Tag 08RM](https://stacks.math.columbia.edu/tag/08RM)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u v w

namespace AlgebraicGeometry.SheafOfModules

/-- The sheaf of relative differentials of a morphism of sheaves of commutative rings on a
topological space, formed on a general site, is the one formed on the open-cover site. Both
corepresent the functor of relative derivations, and they are the same term. -/
theorem moduleOfDifferentialsOfSite_eq_moduleOfDifferentials {T : TopCat.{u}}
    (O₁ O₂ : TopCat.Sheaf CommRingCat.{max u v} T) (φ : O₁ ⟶ O₂) :
    moduleOfDifferentialsOfSite.{u, u, max u v, w} O₁ O₂ φ =
      moduleOfDifferentials.{u, v, w} φ :=
  rfl

end AlgebraicGeometry.SheafOfModules

end
