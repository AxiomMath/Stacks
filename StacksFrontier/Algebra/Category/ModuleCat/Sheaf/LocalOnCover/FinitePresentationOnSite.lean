module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteIff
import StacksCore.Tactic.StacksAttribute

/-!
# Finite presentation on a site is local on a covering family

Stacks 03DN(7): let `𝓕` be a sheaf of `𝒪`-modules on a site with a final object `X`.  The
following are equivalent:

* (a) `𝓕` is of finite presentation;
* (b) there is a covering `{Xᵢ ⟶ X}` such that each restriction `𝓕|_{𝒞/Xᵢ}` is of finite
  presentation;
* (c) there is a covering `{Xᵢ ⟶ X}` such that each restriction `𝓕|_{𝒞/Xᵢ}` has a finite
  global presentation.

"Of finite presentation" is Stacks 03DL(7): every object of the site has a covering on whose
members the restricted module has a finite global presentation.  This is
`SheafOfModules.IsFinitePresentationOnSite`, and it is the predicate used in (a) and (b) below.

## Main results

* `Stacks.SheafOfModules.isFinitePresentationOnSite_iff_exists_cover_isFinitePresentationOnSite`:
  (a) ⟺ (b).
* `Stacks.SheafOfModules.isFinitePresentationOnSite_iff_exists_cover_finite_presentations`:
  (a) ⟺ (c).

## Implementation notes

The proofs pass through Mathlib's `SheafOfModules.IsFinitePresentation`, which asks for one
family covering the final object with a finite presentation on each member.  The comparison with
`IsFinitePresentationOnSite` is
`SheafOfModules.isFinitePresentationOnSite_iff_isFinitePresentation`, whose direction from
Mathlib's predicate is the content of the proof of Stacks 03DN, restricting the presentations of
(c) along every object of the site.  The equivalences for Mathlib's
predicate are `Stacks.SheafOfModules.isFinitePresentation_iff_exists_cover_isFinitePresentation`
and `Stacks.SheafOfModules.isFinitePresentation_iff_exists_cover_finite_presentations`.

As there, the site need not have a final object: `GrothendieckTopology.CoversTop` expresses that a
family covers the final object without choosing one.

## References

* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory

namespace Stacks.SheafOfModules

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{w}} (M : SheafOfModules.{w} R)
  [∀ (U : C), HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
  [∀ (U : C), (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Stacks 03DN(7), (a) ⟺ (b).** A sheaf of modules is of finite presentation in the sense of
Stacks 03DL(7) if and only if there is a family covering the final object such that each
restriction to a member of it is of finite presentation in the same sense. -/
@[stacks 03DN "finite_presentation, (a) ⟺ (b)"]
theorem isFinitePresentationOnSite_iff_exists_cover_isFinitePresentationOnSite
    [∀ (U : C), ∀ (V : Over U),
      HasWeakSheafify ((J.over U).over V) AddCommGrpCat.{w}]
    [∀ (U : C), ∀ (V : Over U),
      ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{w}] :
    M.IsFinitePresentationOnSite ↔
      ∃ (I : Type u) (U : I → C), J.CoversTop U ∧
        ∀ i : I, (M.over (U i)).IsFinitePresentationOnSite := by
  refine (_root_.SheafOfModules.isFinitePresentationOnSite_iff_isFinitePresentation M).trans
    ((isFinitePresentation_iff_exists_cover_isFinitePresentation M).trans ?_)
  exact exists_congr fun I => exists_congr fun U => and_congr_right fun _ =>
    forall_congr' fun i =>
      (_root_.SheafOfModules.isFinitePresentationOnSite_iff_isFinitePresentation
        (M.over (U i))).symm

/-- **Stacks 03DN(7), (a) ⟺ (c).** A sheaf of modules is of finite presentation in the sense of
Stacks 03DL(7) if and only if there is a family covering the final object such that each
restriction to a member of it has a finite global presentation. -/
@[stacks 03DN "finite_presentation, (a) ⟺ (c)"]
theorem isFinitePresentationOnSite_iff_exists_cover_finite_presentations :
    M.IsFinitePresentationOnSite ↔
      ∃ (I : Type u) (U : I → C), J.CoversTop U ∧
        ∀ i : I, ∃ (p : (M.over (U i)).Presentation), p.IsFinite :=
  (_root_.SheafOfModules.isFinitePresentationOnSite_iff_isFinitePresentation M).trans
    (isFinitePresentation_iff_exists_cover_finite_presentations M)

end Stacks.SheafOfModules

end
