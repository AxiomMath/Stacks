module

public import StacksFrontier.AlgebraicGeometry.ComponentDegrees.Degree
public import StacksCore.Tactic.StacksAttribute

/-!
# The component formula of Stacks Tag 0AYW is a single equation

Let `f : X ⟶ Spec k` be proper with `topologicalKrullDim X ≤ 1` and let `ℰ` be a finite locally
free sheaf of rank `n` on `X`. Stacks Tag 0AYW asserts that there are proofs that each reduced
one-dimensional component of `X` is proper over `k`, has dimension at most one, and carries a
restriction of `ℰ` that is again finite locally free of rank `n`, and that with respect to those
proofs

`deg(ℰ) = ∑ᶠ ξ, m(ξ) * deg(ℰ|_{C(ξ)})`,

the sum running over the generic points of the one-dimensional components.

The three proofs the conclusion carries are already available:
`Stacks.AlgebraicGeometry.ComponentDegrees.isProper_reducedComponentι_comp`,
`topologicalKrullDim_reducedComponent_le` and
`isFiniteLocallyFreeOfRank_pullback_reducedComponentι`. This file records, as a theorem rather
than as a remark, that nothing else of Tag 0AYW is outstanding: the existentially quantified
statement is *equivalent* to the one equation

`curveDegree k f hX E rank =
  ∑ᶠ ξ, (componentMultiplicity X ξ : ℤ) * componentDegree k f hX E rank ξ`

in which no proof obligation appears, because
`Stacks.AlgebraicGeometry.ComponentDegrees.componentDegree` applies
`AlgebraicGeometry.curveDegree` to exactly those three proofs and all three are `Prop`-valued.

## Main results

* `Stacks.AlgebraicGeometry.ComponentDegrees.finite_genericPointsOne_of_isProper`: a scheme
  proper over a field has only finitely many one-dimensional components, so the sum above has
  finite support.
* `Stacks.AlgebraicGeometry.ComponentDegrees.exists_curveDegree_eq_finsum_iff`: the conclusion
  of Tag 0AYW is equivalent to that single equation.

## Implementation notes

`AlgebraicGeometry.IsProper`, `topologicalKrullDim _ ≤ 1` and
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank` are all `Prop`-valued, so the value
of `AlgebraicGeometry.curveDegree` does not depend on which proofs of them are supplied; the two
sides of the equivalence therefore differ by proof irrelevance alone. The point of stating it is
that the equation on the right is the whole of what remains, and that it is in a form a later
proof can rewrite with directly.

**What is not here, and where it is.** The equation itself is **not** proved in this file, and no
Stacks attribute for Tag 0AYW is attached anywhere in it. It is proved, with no hypothesis beyond
the source's, by
`Stacks.AlgebraicGeometry.ComponentDegreeDevissage.curveDegree_eq_finsum_componentDegree` of
`StacksFrontier/AlgebraicGeometry/ComponentDegreeDevissage/Basic.lean`, which carries the tag
together with the existential form; the equivalence recorded below is what that file rewrites
with to pass between the two.

The proof uses results of the chapter on cohomology of schemes, Tags 02O6, 01XJ, 01YF, 01YI,
089W, 02OH, 01Y9, 087T and 01E8, all of which are in the library; the route that uses them is
not the source's two paragraphs. The dévissage filtration of Tag 01YF
(`Stacks.AlgebraicGeometry.CoherentDevissage.hasIdealFiltration`) replaces both the reduction to
the irreducible case and the induction on the least `e` with `ℐ^{e+1} = 0`; what it is run
against is the quantity `χ(𝒫 ⊗ ℰ) − n·χ(𝒫)` of Tag 0AYU,
`AlgebraicGeometry.eulerCharacteristicTensorSheafSub`, whose additivity along a short exact
sequence is Tag 08AA in the unconditional form
`AlgebraicGeometry.eulerCharacteristic_add_of_shortExact`.

## References

* [Stacks Project, Tag 0AYW](https://stacks.math.columbia.edu/tag/0AYW)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Stacks.AlgebraicGeometry.ComponentDegrees

universe u

/-- A scheme proper over a field has only finitely many one-dimensional irreducible components,
so the sum of Stacks Tag 0AYW has finite support. -/
theorem finite_genericPointsOne_of_isProper (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] : (genericPointsOne X).Finite :=
  have := isNoetherian_of_isProper_over_field k f
  finite_genericPointsOne X

/-- **The conclusion of Stacks Tag 0AYW is equivalent to a single equation.** The tag asserts the
existence of proofs that each reduced one-dimensional component is proper over the base, has
dimension at most one and carries a restriction of `E` that is finite locally free of the same
rank, together with the component formula for the degree evaluated at those proofs. All three
are already proved and all three are `Prop`-valued, so the whole assertion is equivalent to the
component formula written with
`Stacks.AlgebraicGeometry.ComponentDegrees.componentDegree`, in which no proof obligation
appears. -/
theorem exists_curveDegree_eq_finsum_iff (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (hX : topologicalKrullDim X ≤ 1) (E : X.Modules)
    (rank : ℕ)
    [_root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E rank] :
    (∃ (hproper : ∀ ξ : genericPointsOne X, IsProper (reducedComponentι X ξ ≫ f))
        (hdimC : ∀ ξ : genericPointsOne X, topologicalKrullDim (reducedComponent X ξ) ≤ 1)
        (hrank : ∀ ξ : genericPointsOne X,
          _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
            ((Scheme.Modules.pullback (reducedComponentι X ξ)).obj E) rank),
        curveDegree k f hX E rank =
          ∑ᶠ ξ : genericPointsOne X,
            (componentMultiplicity X ξ : ℤ) *
              @curveDegree k _ (reducedComponent X ξ) (reducedComponentι X ξ ≫ f)
                (hproper ξ) (hdimC ξ)
                ((Scheme.Modules.pullback (reducedComponentι X ξ)).obj E) rank (hrank ξ)) ↔
      curveDegree k f hX E rank =
        ∑ᶠ ξ : genericPointsOne X,
          (componentMultiplicity X ξ : ℤ) * componentDegree k f hX E rank ξ :=
  ⟨fun ⟨_, _, _, h⟩ => h, fun h => ⟨isProper_reducedComponentι_comp k f,
    topologicalKrullDim_reducedComponent_le X hX,
    fun ξ => isFiniteLocallyFreeOfRank_pullback_reducedComponentι ξ E rank, h⟩⟩

end Stacks.AlgebraicGeometry.ComponentDegrees

end
