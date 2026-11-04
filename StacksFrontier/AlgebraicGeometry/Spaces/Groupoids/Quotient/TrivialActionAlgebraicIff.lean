module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.MorphismFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.TargetSheafSurjection
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientStackAlgebraicIffRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.TrivialActionAlgebraic
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatQuotientStackAlgebraic
public import StacksFrontier.CategoryTheory.Sites.LocallySurjectiveBaseChange

/-!
# A quotient stack by a trivial action is algebraic exactly when the group is flat and finitely
presented (Stacks 06PL)

Let `G` be a group algebraic space over an algebraic space `B` over a scheme `S` of a big fppf
site, and endow `B` with the trivial action of `G`. **Stacks 06PL** states that the quotient stack
`[B/G]` is an algebraic stack if and only if `G ⟶ B` is flat and locally of finite presentation.

`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.TrivialActionAlgebraic` reduces the
implication from flatness and local finite presentation to algebraicity to **Stacks 06FI**, and
this file supplies Stacks 06FI from
`AlgebraicGeometry.Stack.forall_isAlgebraicStack_quotientStack_of_flat`. It also proves the
converse implication: the two descent steps that follow the source's citation of **Stacks 06PK**,
and that citation itself, out of the converse of **Stacks 06PJ**.

## Main results

* `AlgebraicGeometry.Stack.source_eq_target_trivialActionGroupoid`: the action groupoid of a
  trivial action has equal source and target, the action map and the projection both being
  morphisms into a terminal object.
* `AlgebraicGeometry.Stack.isFlat_and_isLocallyOfFinitePresentation_of_trivialActionCriterion`:
  the converse half of Stacks 06PL downstream of its citation of Stacks 06PK.
* `isFlat_and_isLocallyOfFinitePresentation_of_isAlgebraicStack_trivialAction`: **the converse
  half of Stacks 06PL**.
* `AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_trivialAction_of_flat`: the
  implication from flatness and local finite presentation to algebraicity.
* `AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_trivialAction_iff`: **Stacks 06PL**.

## Implementation notes

The converse of Stacks 06PJ produces a morphism `g : U' ⟶ B` of algebraic spaces whose saturation
map `U' ×_{g, B, t} R ⟶ R ⟶ B` is a surjection of fppf sheaves and whose restricted source and
target are flat and locally of finite presentation. For the action groupoid of a trivial action the
source and the target coincide, so the saturation map is the first projection followed by `g`;
hence `g` is itself a surjection of fppf sheaves, and the restricted arrow space is
`U' ×_B G ×_B U'` with its two projections to `U'`. That is exactly the data Stacks 06PK is cited
for, and `isFlat_and_isLocallyOfFinitePresentation_of_trivialActionCriterion` consumes it.

The two cartesian squares it asks for are
`AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct` flipped and
`AlgebraicGeometry.Stack.isPullback_restrictionSource`, read in presheaves by
`AlgebraicGeometry.AlgebraicSpaces.isPullback_hom`; and the projection it asks to be flat and
locally of finite presentation is `AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictionTarget`,
which is that composite of projections on the nose. The passage from the source and target of the
action groupoid to `G ⟶ B` itself is
`AlgebraicGeometry.Stack.holdsOnEveryEtaleChart_trivialActionGroupoid_iff`.

## References

* [Stacks Project, Tag 041T](https://stacks.math.columbia.edu/tag/041T)
* [Stacks Project, Tag 041W](https://stacks.math.columbia.edu/tag/041W)
* [Stacks Project, Tag 0444](https://stacks.math.columbia.edu/tag/0444)
* [Stacks Project, Tag 044B](https://stacks.math.columbia.edu/tag/044B)
* [Stacks Project, Tag 06FI](https://stacks.math.columbia.edu/tag/06FI)
* [Stacks Project, Tag 06NR](https://stacks.math.columbia.edu/tag/06NR)
* [Stacks Project, Tag 06PJ](https://stacks.math.columbia.edu/tag/06PJ)
* [Stacks Project, Tag 06PK](https://stacks.math.columbia.edu/tag/06PK)
* [Stacks Project, Tag 06PL](https://stacks.math.columbia.edu/tag/06PL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u w

namespace AlgebraicGeometry.Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

/-- **The action groupoid of a trivial action has equal source and target.** The object space of
the action groupoid of **Stacks 0444** for the action of `G` on the monoidal unit of `Over B` is
that unit, which is a terminal object, and the source and target of the groupoid are the second
projection and the action map, both morphisms into it. -/
theorem source_eq_target_trivialActionGroupoid
    (B : AlgebraicSpaces C S hS) (G : Over B.obj) [GrpObj G]
    (hG : IsAlgebraicSpace C S hS G.left)
    (A : Space.ActionGroupoidConstruction B G (𝟙_ (Over B.obj)) hG B.property) :
    A.groupoid.source = A.groupoid.target := by
  have hst : snd G (𝟙_ (Over B.obj)) = γ[G, 𝟙_ (Over B.obj)] := toUnit_unique _ _
  apply ObjectProperty.hom_ext
  refine eq_of_heq (HEq.trans A.source_eq (HEq.symm ?_))
  rw [hst]
  exact A.target_eq

/-- **The converse half of Stacks 06PL, from the data that the source's proof extracts from
Stacks 06PK.** Let `G ⟶ B` be a morphism of algebraic spaces over `S` and let `B' ⟶ B` be a
morphism of algebraic spaces which is a surjection of fppf sheaves. Form the fibre products
`Q = G ×_B B'` and `P = Q ×_B B' = B' ×_B G ×_B B'`. If the projection `P ⟶ B'` which forgets
the `G` and the *first* `B'` is flat and locally of finite presentation, then so is `G ⟶ B`.

This is the whole of the converse half of Stacks 06PL after the citation of Stacks 06PK: that
lemma, applied to the trivial action of `G` on `B`, produces exactly a `B' ⟶ B` which is a
surjection of fppf sheaves and for which both projections `B' ×_B G ×_B B' ⟶ B'` are flat and
locally of finite presentation, and the source then runs the two descent steps below. The group
structure of `G` plays no part.

The first step is **Stacks 06NR**: `P ⟶ Q` is the base change of `B' ⟶ B` along `Q ⟶ B`, hence
again a surjection of fppf sheaves, and the composite `P ⟶ Q ⟶ B'` is the given flat, locally
finitely presented projection, so `Q ⟶ B'` is flat and locally of finite presentation. The second
is the descent at the target along a sheaf surjection of
`StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.TargetSheafSurjection`, which is where
the fppf covering of `B` refining `B' ⟶ B` is chosen and **Stacks 041W** and **Stacks 041T** are
applied: `Q ⟶ B'` is the base change of `G ⟶ B` along `B' ⟶ B`.

What this does not supply is the input: the existence of such a `B'` is the converse direction
of Stacks 06PK, hence of Stacks 06PJ. That input is
`AlgebraicGeometry.Stack.exists_restrictionAlong_of_isAlgebraicStack`, and the two are put
together in `isFlat_and_isLocallyOfFinitePresentation_of_isAlgebraicStack_trivialAction` below. -/
theorem isFlat_and_isLocallyOfFinitePresentation_of_trivialActionCriterion
    {Bs G B' Q P : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (hBs : IsAlgebraicSpace C S hS Bs) (hG : IsAlgebraicSpace C S hS G)
    (hB' : IsAlgebraicSpace C S hS B') (hQ : IsAlgebraicSpace C S hS Q)
    (hP : IsAlgebraicSpace C S hS P)
    {q : G ⟶ Bs} {ψ : B' ⟶ Bs} {pr₁ : Q ⟶ G} {pr₂ : Q ⟶ B'} {s : P ⟶ Q} {s' : P ⟶ B'}
    (hQsq : IsPullback pr₁ pr₂ q ψ) (hPsq : IsPullback s s' (pr₂ ≫ ψ) ψ)
    (hψ : Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS) ψ)
    (hflat : Space.IsFlat C S hS (s ≫ pr₂))
    (hlfp : Space.IsLocallyOfFinitePresentation C S hS (s ≫ pr₂)) :
    Space.IsFlat C S hS q ∧ Space.IsLocallyOfFinitePresentation C S hS q := by
  have hs : Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS) s :=
    Presheaf.isLocallySurjective_of_isPullback _ hPsq (hf := hψ)
  refine ⟨Space.isFlat_of_isPullback_of_locallySurjective C S hS hBs hG hB' hQ hQsq hψ
      (Space.isFlat_of_comp_of_locallySurjective C S hS hP hQ hB' s pr₂ hflat hs),
    Space.isLocallyOfFinitePresentation_of_isPullback_of_locallySurjective C S hS hBs hG hB' hQ
      hQsq hψ
      (Space.isLocallyOfFinitePresentation_of_comp_of_locallySurjective C S hS hP hQ hB' s pr₂
        hlfp hs)⟩

/-- **Stacks 06PL, the converse implication.** Let `G` be a group algebraic space over an
algebraic space `B` over `S`, endow `B` with the trivial action of `G`, and suppose the quotient
stack `[B/G]` is an algebraic stack. Then `G ⟶ B` is flat and locally of finite presentation.

The converse of **Stacks 06PJ**,
`AlgebraicGeometry.Stack.exists_restrictionAlong_of_isAlgebraicStack`, supplies the citation of
**Stacks 06PK** that the source's proof makes, and
`AlgebraicGeometry.Stack.isFlat_and_isLocallyOfFinitePresentation_of_trivialActionCriterion` is the
rest of the argument; see the module docstring. -/
@[stacks 06PL "the converse implication, from algebraicity to flat and locally of finite \
presentation, with nothing carried"]
theorem isFlat_and_isLocallyOfFinitePresentation_of_isAlgebraicStack_trivialAction
    (B : AlgebraicSpaces C S hS) (G : Over B.obj) [GrpObj G]
    (hG : IsAlgebraicSpace C S hS G.left)
    (A : Space.ActionGroupoidConstruction B G (𝟙_ (Over B.obj)) hG B.property)
    (h : IsAlgebraicStack.{u, w} C S hS (quotientStack A.groupoid)) :
    Space.IsFlat C S hS G.hom ∧ Space.IsLocallyOfFinitePresentation C S hS G.hom := by
  obtain ⟨U', g, hsat, _hsrcF, htgtF, _hsrcL, htgtL⟩ :=
    exists_restrictionAlong_of_isAlgebraicStack.{u, w} A.groupoid h
  have hsatEq : GroupoidInAlgebraicSpaces.fiberProductSnd g A.groupoid.target ≫
        A.groupoid.source =
      GroupoidInAlgebraicSpaces.fiberProductFst g A.groupoid.target ≫ g := by
    rw [source_eq_target_trivialActionGroupoid B G hG A]
    exact ((AlgebraicSpaces.isPullback_fiberProduct C S hS g A.groupoid.target).w).symm
  rw [hsatEq] at hsat
  have : Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS)
      ((GroupoidInAlgebraicSpaces.fiberProductFst g A.groupoid.target).hom ≫ g.hom) := hsat
  have hg : Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS) g.hom :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac
      (BigFppfOver.topology C S hS)
      (rfl : (GroupoidInAlgebraicSpaces.fiberProductFst g A.groupoid.target).hom ≫ g.hom =
        (GroupoidInAlgebraicSpaces.fiberProductFst g A.groupoid.target).hom ≫ g.hom)
  have hsq : IsPullback
      (GroupoidInAlgebraicSpaces.fiberProductFst
        (GroupoidInAlgebraicSpaces.fiberProductSnd g A.groupoid.target)
        (GroupoidInAlgebraicSpaces.fiberProductFst A.groupoid.source g))
      (GroupoidInAlgebraicSpaces.restrictionSource A.groupoid g)
      (GroupoidInAlgebraicSpaces.fiberProductFst g A.groupoid.target ≫ g) g := by
    rw [← hsatEq]
    exact isPullback_restrictionSource C S hS A.groupoid g
  have hres := isFlat_and_isLocallyOfFinitePresentation_of_trivialActionCriterion
    A.groupoid.objects.property A.groupoid.arrows.property U'.property
    (AlgebraicSpaces.fiberProduct C S hS g A.groupoid.target).property
    (GroupoidInAlgebraicSpaces.restrictionArrows A.groupoid g).property
    (AlgebraicSpaces.isPullback_hom C S hS
      ((AlgebraicSpaces.isPullback_fiberProduct C S hS g A.groupoid.target).flip))
    (AlgebraicSpaces.isPullback_hom C S hS hsq) hg htgtF htgtL
  exact ⟨(holdsOnEveryEtaleChart_trivialActionGroupoid_iff B G hG A
      (@AlgebraicGeometry.Flat.{u}) A.groupoid.target A.groupoid.target_over).1 hres.1,
    (holdsOnEveryEtaleChart_trivialActionGroupoid_iff B G hG A
      (@AlgebraicGeometry.LocallyOfFinitePresentation.{u}) A.groupoid.target
      A.groupoid.target_over).1 hres.2⟩

/-- **Stacks 06PL, the implication from flat and locally of finite presentation to algebraic.**
Let `G` be a group algebraic space over an algebraic space `B` over `S` and endow `B` with the
trivial action of `G`. If `G ⟶ B` is flat and locally of finite presentation, then the quotient
stack `[B/G]` is an algebraic stack.

This is `AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_trivialAction`, which applies
**Stacks 06FI** to the action groupoid, with that theorem supplied by
`AlgebraicGeometry.Stack.forall_isAlgebraicStack_quotientStack_of_flat`. -/
theorem isAlgebraicStack_quotientStack_trivialAction_of_flat
    (B : AlgebraicSpaces C S hS) (G : Over B.obj) [GrpObj G]
    (hG : IsAlgebraicSpace C S hS G.left)
    (A : Space.ActionGroupoidConstruction B G (𝟙_ (Over B.obj)) hG B.property)
    (hflat : Space.IsFlat C S hS G.hom)
    (hlfp : Space.IsLocallyOfFinitePresentation C S hS G.hom) :
    IsAlgebraicStack.{u, w} C S hS (quotientStack A.groupoid) :=
  isAlgebraicStack_quotientStack_trivialAction.{u, w} B G hG A
    (forall_isAlgebraicStack_quotientStack_of_flat.{u, w} B) hflat hlfp

/-- **Stacks 06PL.** Let `G` be a group algebraic space over an algebraic space `B` over `S` and
endow `B` with the trivial action of `G`. The quotient stack `[B/G]` is an algebraic stack if and
only if `G ⟶ B` is flat and locally of finite presentation. -/
@[stacks 06PL]
theorem isAlgebraicStack_quotientStack_trivialAction_iff
    (B : AlgebraicSpaces C S hS) (G : Over B.obj) [GrpObj G]
    (hG : IsAlgebraicSpace C S hS G.left)
    (A : Space.ActionGroupoidConstruction B G (𝟙_ (Over B.obj)) hG B.property) :
    IsAlgebraicStack.{u, w} C S hS (quotientStack A.groupoid) ↔
      (Space.IsFlat C S hS G.hom ∧
        Space.IsLocallyOfFinitePresentation C S hS G.hom) where
  mp h := isFlat_and_isLocallyOfFinitePresentation_of_isAlgebraicStack_trivialAction.{u, w}
    B G hG A h
  mpr h := isAlgebraicStack_quotientStack_trivialAction_of_flat.{u, w} B G hG A h.1 h.2

end AlgebraicGeometry.Stack

end
