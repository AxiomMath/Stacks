module

public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Abelian
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finite
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.PrincipalIdealExtension

/-!
# Associated points of a coherent module on a quasi-compact scheme

Let `X` be a locally Noetherian scheme whose underlying topological space is quasi-compact, and
let `ℱ` be a coherent `𝒪_X`-module. Then the set `Ass(ℱ)` of points associated to `ℱ` is finite,
and so is the union of the associated points of finitely many coherent modules. A special case
is a module together with the quotient by a power of a global function: `f ∈ Γ(X, 𝒪_X)`
and `k : ℕ` give the endomorphism "multiplication by `fᵏ`" of `ℱ`, whose cokernel is `ℱ/fᵏℱ`, and
`Ass(ℱ) ∪ Ass(ℱ/fᵏℱ)` is finite.

## Main results

* `AlgebraicGeometry.associatedPoints_finite`: the associated points of a coherent module on a
  quasi-compact locally Noetherian scheme form a finite set.
* `AlgebraicGeometry.associatedPoints_union_finite`: the associated points of two coherent
  modules form a finite set together.
* `AlgebraicGeometry.associatedPoints_union_cokernel_smulPowHom_finite`: the instance
  `Ass(ℱ) ∪ Ass(ℱ/fᵏℱ)` of the previous statement, which for `k = 1` is `Ass(ℱ) ∪ Ass(ℱ/fℱ)`.

## Implementation notes

Quasi-compactness of the whole space is `CompactSpace`, and the first statement is the
quasi-compact-open finiteness of [Stacks, Tag 05AF] read on the open `⊤`. Multiplication by `fᵏ`
is `Stacks.AlgebraicGeometry.PrincipalIdealExtension.smulPowHom`, and its cokernel is coherent
by the cokernel clause of [Stacks, Tag 01Y0].

Tag 05AF is the statement for an arbitrary quasi-compact open,
`AlgebraicGeometry.associatedPoints_inter_finite`, and the results here are instances of it.

## References

* [Stacks Project, Tag 05AF](https://stacks.math.columbia.edu/tag/05AF)
* [Stacks Project, Tag 01Y0](https://stacks.math.columbia.edu/tag/01Y0)
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace
open Stacks.AlgebraicGeometry.PrincipalIdealExtension

universe u

namespace AlgebraicGeometry

/-- The associated points of a coherent module on a locally Noetherian scheme whose underlying
space is quasi-compact form a finite set. -/
theorem associatedPoints_finite {X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (F : X.Modules) [F.IsCoherent] : (Stacks.Divisors.associatedPoints F).Finite := by
  simpa using associatedPoints_inter_finite F ⊤ (by simpa using isCompact_univ (X := ↥X))

/-- The points associated to either of two coherent modules on a locally Noetherian scheme whose
underlying space is quasi-compact form a finite set. -/
theorem associatedPoints_union_finite {X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (F G : X.Modules) [F.IsCoherent] [G.IsCoherent] :
    (Stacks.Divisors.associatedPoints F ∪ Stacks.Divisors.associatedPoints G).Finite :=
  (associatedPoints_finite F).union (associatedPoints_finite G)

/-- For a coherent module `ℱ` on a locally Noetherian scheme whose underlying space is
quasi-compact, a global function `f` and an exponent `k`, the points associated to `ℱ` or to the
quotient `ℱ/fᵏℱ` form a finite set. -/
theorem associatedPoints_union_cokernel_smulPowHom_finite {X : Scheme.{u}}
    [IsLocallyNoetherian X] [CompactSpace X] (F : X.Modules) [F.IsCoherent] (f : Γ(X, ⊤))
    (k : ℕ) :
    (Stacks.Divisors.associatedPoints F ∪
      Stacks.Divisors.associatedPoints (cokernel (smulPowHom F f k))).Finite := by
  have := isCoherent_cokernel (smulPowHom F f k)
  exact associatedPoints_union_finite F _

end AlgebraicGeometry

end
