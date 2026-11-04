module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleGlobalSectionsFork

/-!
# The equalizer presentation of global sections is evaluation at the chart

`AlgebraicGeometry.Space.moduleSectionsEquivEqualizer` is the module-level reading of
Stacks 03M8: the global sections of an `𝒪_X`-module are in bijection with the sections over a
surjective étale scheme chart `U` which the two projections of `R = U ×_X U` equalize.  It is
assembled from four transports and a limiting fork, so nothing about its *value* is visible
from the construction.

This file computes that value: **the bijection is evaluation at the chart.**  A global section
of a sheaf on the small étale site is a compatible family of sections over the étale charts, and
the bijection sends it to its own member at `U`.

That is what makes the bijection usable in the proof of Stacks 07SI.  There the bijection has to
be compared, over a system of algebraic spaces, with the transition maps on global sections and
with restriction along a morphism of charts — the hypotheses `he` and `heT` of the theorem
`isSectionsColimit_of_equalizerPresentation_of_relationChart` in the namespace
`AlgebraicGeometry.Space.LimitSituation`.  Those comparisons are statements about the *value* of
the bijection, and are out of reach while it is only known to exist; evaluation at a chart, by
contrast, is natural for a formal reason.

## Main results

* `CategoryTheory.Functor.sectionsEquivOfIso_symm_apply_val`: the inverse transport of sections
  along an isomorphism of functors to types applies the inverse componentwise.
* `AlgebraicGeometry.Space.restrictSectionsToCharts_val`: restriction of a section over the
  terminal object of the spaces-étale site to the charts has, at a chart, the restriction of
  that section along the unique morphism out of the chart.
* `AlgebraicGeometry.Space.sectionsComparisonEquivEqualizer_apply_val`,
  `AlgebraicGeometry.Space.smallEtaleSectionsEquivEqualizer_apply_val` and
  `AlgebraicGeometry.Space.moduleSectionsEquivEqualizer_apply_val`: **each of the three
  equalizer presentations of global sections is evaluation at the chart `U`.**

## Implementation notes

*Why the three statements rather than only the last.*  The three bijections are defined in terms
of one another, and each step adds one transport whose effect on a section has to be unwound
separately: the comparison bijection of
`AlgebraicGeometry.Space.equivSectionsComparison` is `Equiv.ofBijective` of restriction to the
charts, so its inverse is only characterized by `Equiv.apply_symm_apply`; the small étale
bijection conjugates by the counit of the comparison equivalence of Stacks 03G1, which cancels
componentwise; and the module bijection adds nothing, the sheaf of sets underlying a module
being its own argument.

*The first statement is where the work is.*  The vertex of the limiting fork is the sections
over the terminal object, and the arrow of the fork is restriction along the unique morphism
`U ⟶ X`; so the composite bijection sends a compatible family to the restriction of the global
section it comes from.  That this is the family's own member at `U` is the defining property of
the comparison bijection, read through `Equiv.apply_symm_apply`.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v v' w u

namespace CategoryTheory.Functor

variable {J : Type v} [Category.{v'} J] {F G : J ⥤ Type w}

/-- **The inverse transport of sections along an isomorphism of functors to types applies the
inverse componentwise.**  This is the counterpart of
`CategoryTheory.Functor.sectionsEquivOfIso_apply_val` for the inverse of
`CategoryTheory.Functor.sectionsEquivOfIso`, and holds by definition. -/
@[simp]
lemma sectionsEquivOfIso_symm_apply_val (e : F ≅ G) (t : G.sections) (j : J) :
    ((sectionsEquivOfIso e).symm t).val j = e.inv.app j (t.val j) :=
  rfl

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : AlgebraicSpaces B S hS}

/-- **Restriction of a global section to the étale scheme charts, at one chart.**  The member at
a chart `V` of the compatible family `AlgebraicGeometry.Space.restrictSectionsToCharts` produces
from a section over the terminal object of the spaces-étale site is the restriction of that
section along the unique morphism of the site out of `V`. -/
theorem restrictSectionsToCharts_val (P : (SpacesEtale B S hS X)ᵒᵖ ⥤ Type u)
    (x : P.obj (op (SpacesEtale.idObj B S hS X))) (V : SmallEtale B S hS X.1) :
    (restrictSectionsToCharts B S hS P x).val (op V)
      = P.map ((SpacesEtale.isTerminal_idObj B S hS X).from
          ((comparisonFunctor B S hS X).obj V)).op x :=
  rfl

/-- **The equalizer presentation of the global sections computed over the small étale site is
evaluation at the chart.**  In the situation of
`AlgebraicGeometry.Space.sectionsComparisonEquivEqualizer`, the bijection sends a compatible
family of sections of `P` over the étale scheme charts to its own member at the chart `U`.

The bijection is the inverse of restriction to the charts followed by the arrow of the limiting
fork, which is restriction along the unique morphism `U ⟶ X`; so its value at a family is the
restriction, to `U`, of the global section the family comes from — and that is the family's
member at `U`, by the defining property of the comparison bijection. -/
theorem sectionsComparisonEquivEqualizer_apply_val (P : (SpacesEtale B S hS X)ᵒᵖ ⥤ Type u)
    (hP : Presheaf.IsSheaf (SpacesEtale.topology B S hS X) P)
    {U R : SmallEtale B S hS X.1} (hU : IsSurjective B S hS U.1.hom) {t s : R ⟶ U}
    (hR : IsPullback ((comparisonFunctor B S hS X).map t) ((comparisonFunctor B S hS X).map s)
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U))
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U)))
    (σ : ((comparisonFunctor B S hS X).op ⋙ P).sections) :
    (sectionsComparisonEquivEqualizer B S hS P hP hU hR σ).1 = σ.val (op U) := by
  conv_rhs => rw [← (equivSectionsComparison B S hS P hP hU).apply_symm_apply σ]
  rfl

/-- **The equalizer presentation of the global sections of a sheaf of sets on the small étale
site is evaluation at the chart.**  In the situation of
`AlgebraicGeometry.Space.smallEtaleSectionsEquivEqualizer`, the bijection sends a global section
of `G` — a compatible family of sections over the étale charts of `X` — to its own member at the
chart `U`.

The two transports along the counit of the comparison equivalence of Stacks 03G1 cancel: the
left one applies its inverse at every chart, and the right one applies the counit itself at `U`.
In between is
`AlgebraicGeometry.Space.sectionsComparisonEquivEqualizer_apply_val`. -/
theorem smallEtaleSectionsEquivEqualizer_apply_val
    (G : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    {U R : SmallEtale B S hS X.1} (hU : IsSurjective B S hS U.1.hom) {t s : R ⟶ U}
    (hR : IsPullback ((comparisonFunctor B S hS X).map t) ((comparisonFunctor B S hS X).map s)
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U))
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U)))
    (σ : G.obj.sections) :
    (smallEtaleSectionsEquivEqualizer B S hS G hU hR σ).1 = σ.val (op U) := by
  let P := (smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G
  let e : (comparisonFunctor B S hS X).op ⋙ P.obj ≅ G.obj :=
    (sheafToPresheaf (SmallEtale.topology B S hS X.1) (Type u)).mapIso
      ((smallEtaleComparisonRestriction B S hS X).asEquivalence.counitIso.app G)
  show (e.app (op U)).toEquiv
      (sectionsComparisonEquivEqualizer B S hS P.obj P.property hU hR
        ((Functor.sectionsEquivOfIso e).symm σ)).1 = σ.val (op U)
  rw [sectionsComparisonEquivEqualizer_apply_val,
    Functor.sectionsEquivOfIso_symm_apply_val]
  exact (e.app (op U)).toEquiv.apply_symm_apply (σ.val (op U))

/-- **The equalizer presentation of the global sections of an `𝒪`-module is evaluation at the
chart.**  In the situation of `AlgebraicGeometry.Space.moduleSectionsEquivEqualizer`, the
bijection sends a global section of the module `M` — a compatible family of sections over the
étale charts of `X` — to its own member at the chart `U`.

This is `AlgebraicGeometry.Space.smallEtaleSectionsEquivEqualizer_apply_val` at the sheaf of
sets underlying `M`; the module bijection adds no transport of its own. -/
theorem moduleSectionsEquivEqualizer_apply_val (M : Modules.{u, u} B S hS X.1 X.2)
    {U R : SmallEtale B S hS X.1} (hU : IsSurjective B S hS U.1.hom) {t s : R ⟶ U}
    (hR : IsPullback ((comparisonFunctor B S hS X).map t) ((comparisonFunctor B S hS X).map s)
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U))
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U)))
    (σ : (Sheaf.moduleSheaf.{u, u, u + 1}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
        M).obj.sections) :
    (moduleSectionsEquivEqualizer B S hS M hU hR σ).1 = σ.val (op U) :=
  smallEtaleSectionsEquivEqualizer_apply_val B S hS _ hU hR σ

end AlgebraicGeometry.Space

end
