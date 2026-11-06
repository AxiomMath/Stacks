module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftLocalExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftTorsorGlueing

/-!
# The sheaf of lifts of a smooth morphism is a torsor, not merely a pseudo torsor

`AlgebraicGeometry.Space.liftPseudoTorsor` makes the sheaf of lifts of
[Stacks Project, Tag 061D] a pseudo torsor under the acting sheaf of that tag.  What that
structure does **not** carry is the local nonemptiness condition (T) of
`CategoryTheory.PseudoTorsor.IsTorsor`: that every object of the small étale site of `X'` is
covered by objects over which the sheaf of lifts has a section.

This file supplies it, from smoothness of `q`.  The hypothesis is not removable — the module
docstring of `StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftTorsorGlueing` records a
counterexample to local nonemptiness without it — and that is why
[Stacks Project, Tag 061C] claims only the pseudo-torsor property, with simple transitivity
restricted to the objects admitting a section.  Local nonemptiness belongs to
[Stacks Project, Tag 04AM], whose smoothness hypothesis this statement therefore carries.

With this, the sheaf of lifts is a torsor in the sense that the first-cohomology machinery of
`StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.FirstCohomology` consumes, which is what
turns a vanishing `H¹` into a global lift.

## Main results

* `AlgebraicGeometry.Space.nonempty_liftsSubfunctor_ofArrows`: the local nonemptiness of the
  sheaf of lifts, stated for the `ULift`ed sheaf that the pseudo torsor carries.
* `AlgebraicGeometry.Space.isTorsor_liftPseudoTorsor`: the pseudo torsor of lifts is a torsor.

## Implementation notes

The covering sieve is the one of `AlgebraicGeometry.Space.exists_isChartLift_ofArrows`, and an
arrow of it factors through a member of the generating family by
`CategoryTheory.Sieve.ofArrows.exists`; the section over that member restricts along the
factorisation, since the sheaf of lifts is a subfunctor and so has restriction maps, and
`ULift.up` puts it in the universe of the pseudo torsor's presheaf.

No `@[stacks]` attribute is claimed.  [Stacks Project, Tag 061C] is the pseudo-torsor
statement, already accounted for on `AlgebraicGeometry.Space.liftsSubfunctor` and
`AlgebraicGeometry.Space.liftActionSheaf`; the condition proved here is not part of it.

## References

* [Stacks Project, Tag 03AH](https://stacks.math.columbia.edu/tag/03AH)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 061C](https://stacks.math.columbia.edu/tag/061C)
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
variable {Bb X' Y : AlgebraicSpaces C S hS}

/-- **The sheaf of lifts is locally nonempty**, granted that `q` is smooth: every étale chart of
`X'` carries a covering sieve each of whose members has a section of the `ULift`ed sheaf of
lifts.

This is `AlgebraicGeometry.Space.exists_isChartLift_ofArrows` read at the sheaf
`AlgebraicGeometry.Space.liftsSubfunctorULift` that
`AlgebraicGeometry.Space.liftPseudoTorsor` carries: an arrow of the covering sieve factors
through a member of the generating family, and the section over that member restricts along the
factorisation. -/
theorem nonempty_liftsSubfunctor_ofArrows (p : X' ⟶ Bb) (q : Y ⟶ Bb)
    {Z : Subfunctor X'.1} (a : Z.toFunctor ⟶ Y.1)
    (hX : IsFirstOrderThickening C S hS X' Z) (ha : a ≫ q.hom = Z.ι ≫ p.hom)
    (hq : IsSmooth C S hS q.hom) (U' : SmallEtale C S hS X'.1) :
    ∃ R ∈ SmallEtale.topology C S hS X'.1 U',
      ∀ ⦃V' : SmallEtale C S hS X'.1⦄ ⦃g : V' ⟶ U'⦄, R g →
        Nonempty ((liftsSubfunctorULift C S hS p q a).obj.obj (op V')) := by
  obtain ⟨I, V, r, β, hlift, hcov⟩ :=
    exists_isChartLift_ofArrows C S hS p q a hX ha hq U'
  refine ⟨Sieve.ofArrows V r, hcov, ?_⟩
  intro V' g hg
  obtain ⟨i, k, -⟩ := Sieve.ofArrows.exists hg
  exact ⟨ULift.up ((liftsSubfunctor C S hS p q a).toFunctor.map k.op ⟨β i, hlift i⟩)⟩

/-- **[Stacks Project, Tag 04AM]'s local nonemptiness: the pseudo torsor of lifts of a smooth
morphism is a torsor.**

`AlgebraicGeometry.Space.liftPseudoTorsor` provides the action and its simple transitivity; what
is added here is condition (T), that every object of the site is covered by objects over which
the sheaf of lifts has a section.  That is
`AlgebraicGeometry.Space.nonempty_liftsSubfunctor_ofArrows`, and it is where smoothness of `q`
enters: without it the conclusion is false, and [Stacks Project, Tag 061C] accordingly asserts
only the pseudo-torsor property. -/
theorem isTorsor_liftPseudoTorsor {p : X' ⟶ Bb} {q : Y ⟶ Bb}
    {Z : ClosedSubspaces C S hS X'.1}
    {a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y}
    (hX : IsFirstOrderThickening C S hS X' Z.1)
    (hH : IsChartTranslationCompatible C S hS p Z hX.isThickening q a)
    (ha : a.hom ≫ q.hom = Z.1.ι ≫ p.hom) (hq : IsSmooth C S hS q.hom) :
    (liftPseudoTorsor C S hS hX hH).IsTorsor :=
  fun U' => nonempty_liftsSubfunctor_ofArrows C S hS p q a.hom hX ha hq U'

end AlgebraicGeometry.Space

end
