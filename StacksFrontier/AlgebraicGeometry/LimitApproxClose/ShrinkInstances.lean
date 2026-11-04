module

public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.OverlapBridge

/-!
# The standing hypotheses of a diagram survive precomposition

Every reindexing in the one-affine-open step of Tag 07RN replaces a diagram `D` by `E ⋙ D` for
some functor `E` out of the new index: twice by shrinking the stages and once onto the pairs of a
stage and a distinguished subalgebra.  This file declares, for an arbitrary precomposition, the
three standing hypotheses that Mathlib's machinery on affine-transition limits
(`Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean`) and the results about the
compatible-opens diagram (`AlgebraicGeometry.compactSpace_compatibleOpensDiagram_obj`,
`AlgebraicGeometry.nonempty_isColimit_Γ_mapCocone_compatibleOpens`,
`AlgebraicGeometry.Scheme.exists_forall_isQuasiAffine_compatibleOpens`) assume of a diagram.

## Main results

* `AlgebraicGeometry.isAffineHom_comp_map`: affine transition morphisms survive precomposition.
* `AlgebraicGeometry.locallyOfFiniteType_terminal_from_comp_obj`: local finite type over the
  terminal scheme survives precomposition.
* `AlgebraicGeometry.quasiCompact_terminal_from_comp_obj`: quasi-compactness over the terminal
  scheme survives precomposition.

## Implementation notes

`AlgebraicGeometry.laterDiagram` is reducible, so a goal
`IsAffineHom ((laterDiagram D i₀).map f)` unfolds to `IsAffineHom ((E ⋙ D).map f)`; but
`CategoryTheory.Functor.comp` is a plain definition, so instance search stops there, while the
ambient hypothesis is about `D.map _`.  The instances are therefore stated about a
precomposition rather than about `AlgebraicGeometry.laterDiagram`, and each is `inferInstanceAs`
at the spelling with `CategoryTheory.Functor.comp` unfolded by hand.

No instance for `QuasiSeparatedSpace` is declared: it is derived from local finite type through
`AlgebraicGeometry.quasiSeparatedSpace_of_locallyOfFiniteType_terminal`, which needs only the
second instance.

The two index categories are free in their object and morphism universes; the schemes are in `u`.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ w₁ w₂ u

namespace AlgebraicGeometry

variable {J : Type w₁} [Category.{v₁} J] {K : Type w₂} [Category.{v₂} K] (E : J ⥤ K)
  (D : K ⥤ Scheme.{u})

/-- **Affine transition morphisms survive precomposition.**  The ambient hypothesis is about
`D.map`, and instance search will not unfold `CategoryTheory.Functor.comp` to reach it. -/
instance isAffineHom_comp_map [∀ {a b : K} (f : a ⟶ b), IsAffineHom (D.map f)] {a b : J}
    (f : a ⟶ b) : IsAffineHom ((E ⋙ D).map f) :=
  inferInstanceAs (IsAffineHom (D.map (E.map f)))

/-- **Local finite type over the terminal scheme survives precomposition.** -/
instance locallyOfFiniteType_terminal_from_comp_obj
    [∀ a, LocallyOfFiniteType (terminal.from (D.obj a))] (a : J) :
    LocallyOfFiniteType (terminal.from ((E ⋙ D).obj a)) :=
  inferInstanceAs (LocallyOfFiniteType (terminal.from (D.obj (E.obj a))))

/-- **Quasi-compactness over the terminal scheme survives precomposition.** -/
instance quasiCompact_terminal_from_comp_obj
    [∀ a, QuasiCompact (terminal.from (D.obj a))] (a : J) :
    QuasiCompact (terminal.from ((E ⋙ D).obj a)) :=
  inferInstanceAs (QuasiCompact (terminal.from (D.obj (E.obj a))))

end AlgebraicGeometry
