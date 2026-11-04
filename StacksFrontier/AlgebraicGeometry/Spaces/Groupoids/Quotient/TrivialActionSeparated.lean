module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientStackSeparation
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.TrivialActionAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# Separatedness of the quotient by a trivial action

Let `G` be a group algebraic space over an algebraic space `B` over a scheme `S` of a big fppf
site, and endow `B` with the trivial action of `G`. The quotient stack `[B/G]` is then separated
as soon as `G ⟶ B` is proper, flat and locally of finite presentation.

This is Stacks 0DTY, part (6) read at the action groupoid of the trivial action. For that action
the object space of the groupoid of Stacks 0444 is `B` and its arrow space is `G ×_B B`, so both
the source and the target are the structural morphism of `G ×_B B`, which the right unitor
identifies with `G ⟶ B`; and the structure morphism of the object space is an isomorphism, hence
separated. The three hypotheses 0DTY part (6) makes on the groupoid are therefore exactly
properness, flatness and local finite presentation of `G ⟶ B`.

## Main results

* `AlgebraicGeometry.Stack.isProper_trivialActionGroupoid_iff`: a morphism from the arrow space
  to the object space of the action groupoid of the trivial action which commutes with the two
  structure morphisms to `B` is proper exactly when `G ⟶ B` is.
* `AlgebraicGeometry.Stack.isSeparated_objectsToBase_trivialActionGroupoid`: the structure
  morphism of the object space of that groupoid is separated, being an isomorphism.
* `AlgebraicGeometry.Stack.isSeparatedOver_quotientStack_trivialAction`: for a group algebraic
  space `G` over `S` itself, `[S/G]` is separated over the base scheme of the site when `G ⟶ S`
  is proper, flat and locally of finite presentation.
* `AlgebraicGeometry.Stack.isAbsolutelySeparated_quotientStack_trivialAction`: the same with the
  unqualified, absolute separatedness of Stacks 050D part (7) as the conclusion, on the further
  hypothesis that the algebraic stack of the base scheme is separated.

## Implementation notes

The identification of the groupoid's source and target with `G ⟶ B` is the one
`AlgebraicGeometry.Stack.holdsOnEveryEtaleChart_trivialActionGroupoid_iff` of Stacks 06PL makes,
and that lemma is reused verbatim for the flatness of Stacks 03ML and the local finite
presentation of Stacks 03XP, both of which are instances of
`AlgebraicGeometry.Space.HoldsOnEveryEtaleChart`. Properness is *not* such an instance — it is a
conjunction of separatedness, finite type and universal closedness, each quantified over
represented base changes — so the identification is redone for it here, from the same equalities
of algebraic spaces carried by `AlgebraicGeometry.Space.ActionGroupoidConstruction` and with the
same transport of heterogeneous equalities by `CategoryTheory.conj_eqToHom_iff_heq`. The
transport is then stripped off by the invariance of properness under composition with an
isomorphism on either side.

As in Stacks 0DTY, the algebraic stack whose separatedness is concluded is an argument tied to
the quotient stack by an equivalence over the site, because
`AlgebraicGeometry.Stack.quotientStack` is a based category whose morphisms live one universe up
from those of an `AlgebraicGeometry.Stack.AlgebraicStacks`. The two separatedness statements are
made for `B` the base scheme `S` itself, read as the final algebraic space
`AlgebraicGeometry.Space.terminalSpace`: Stacks 0DTY is a statement about groupoids in algebraic
spaces over `S`, its square `U × U` being taken over `S`.

## References

* [Stacks Project, Tag 0444](https://stacks.math.columbia.edu/tag/0444)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 06PL](https://stacks.math.columbia.edu/tag/06PL)
* [Stacks Project, Tag 0DTY](https://stacks.math.columbia.edu/tag/0DTY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u w

namespace AlgebraicGeometry.Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

section TrivialAction

variable (B : AlgebraicSpaces C S hS) (G : Over B.obj) [GrpObj G]
  (hG : IsAlgebraicSpace C S hS G.left)
  (A : Space.ActionGroupoidConstruction B G (𝟙_ (Over B.obj)) hG B.property)

/-- The object space of the action groupoid of the trivial action is `B` itself. -/
private theorem trivialActionGroupoid_objects_obj :
    A.groupoid.objects.obj = B.obj :=
  congrArg (fun z => z.obj) A.objects_eq

/-- The arrow space of the action groupoid of the trivial action is `G ×_B B`. -/
private theorem trivialActionGroupoid_arrows_obj :
    A.groupoid.arrows.obj = (G ⊗ 𝟙_ (Over B.obj)).left :=
  congrArg (fun z => z.obj) A.arrows_eq

/-- A morphism heterogeneously equal to `g` along an equality of sources is `g` precomposed with
the transport. -/
private theorem eq_eqToHom_comp_of_heq {D : Type*} [Category D] {W Y X : D} (f : W ⟶ X)
    (g : Y ⟶ X) (h : W = Y) (hfg : f ≍ g) : f = eqToHom h ≫ g := by
  subst h
  simpa using hfg

/-- The structure morphism of the object space of the action groupoid of the trivial action is
the transport along the identification of that space with `B`. -/
private theorem trivialActionGroupoid_objectsToBase_hom :
    A.groupoid.objectsToBase.hom =
      eqToHom (trivialActionGroupoid_objects_obj B G hG A) := by
  simpa using eq_eqToHom_comp_of_heq A.groupoid.objectsToBase.hom (𝟙 B.obj)
    (trivialActionGroupoid_objects_obj B G hG A) A.objectsToBase_eq

/-- A morphism from the arrow space to the object space of the action groupoid of the trivial
action which commutes with the two structure morphisms to `B` is, up to the two identifications,
the structural morphism of `G ×_B B`. -/
private theorem trivialActionGroupoid_hom_eq
    (m : A.groupoid.arrows ⟶ A.groupoid.objects)
    (hm : m ≫ A.groupoid.objectsToBase = A.groupoid.arrowsToBase) :
    m.hom = eqToHom (trivialActionGroupoid_arrows_obj B G hG A) ≫
      (G ⊗ 𝟙_ (Over B.obj)).hom ≫
        eqToHom (trivialActionGroupoid_objects_obj B G hG A).symm := by
  have harrsToBase : A.groupoid.arrowsToBase.hom =
      eqToHom (trivialActionGroupoid_arrows_obj B G hG A) ≫
        (G ⊗ 𝟙_ (Over B.obj)).hom := by
    exact eq_eqToHom_comp_of_heq _ _ (trivialActionGroupoid_arrows_obj B G hG A)
      A.arrowsToBase_eq
  have hmcomp : m.hom ≫ A.groupoid.objectsToBase.hom = A.groupoid.arrowsToBase.hom :=
    congrArg (fun g : A.groupoid.arrows ⟶ B => g.hom) hm
  have hmeq : m.hom ≫ eqToHom (trivialActionGroupoid_objects_obj B G hG A) =
      eqToHom (trivialActionGroupoid_arrows_obj B G hG A) ≫
        (G ⊗ 𝟙_ (Over B.obj)).hom := by
    rw [← trivialActionGroupoid_objectsToBase_hom, ← harrsToBase]
    exact hmcomp
  rw [← Category.assoc]
  exact (comp_eqToHom_iff (trivialActionGroupoid_objects_obj B G hG A) m.hom _).1 hmeq

/-- For the trivial action of a group algebraic space `G` on `B`, a morphism from the arrow
space to the object space of the action groupoid of Stacks 0444 which commutes with the two
structure morphisms to `B` is proper exactly when the structural morphism `G ⟶ B` is.

This is the analogue for properness of
`AlgebraicGeometry.Stack.holdsOnEveryEtaleChart_trivialActionGroupoid_iff`, which cannot be used
because properness is not a property tested on every commuting square of étale charts. -/
theorem isProper_trivialActionGroupoid_iff
    (m : A.groupoid.arrows ⟶ A.groupoid.objects)
    (hm : m ≫ A.groupoid.objectsToBase = A.groupoid.arrowsToBase) :
    Space.IsProper C S hS m.hom ↔ Space.IsProper C S hS G.hom := by
  have hunitor : ((Over.forget B.obj).mapIso (ρ_ G)).hom ≫ G.hom =
      (G ⊗ 𝟙_ (Over B.obj)).hom := Over.w (ρ_ G).hom
  rw [trivialActionGroupoid_hom_eq B G hG A m hm, ← hunitor,
    Space.isProper_isIso_comp_iff C S hS, Space.isProper_comp_isIso_iff C S hS,
    Space.isProper_isIso_comp_iff C S hS]
  exact Iff.rfl

/-- The structure morphism of the object space of the action groupoid of the trivial action is
separated: it is the transport along the identification of that space with `B`, hence an
isomorphism. -/
theorem isSeparated_objectsToBase_trivialActionGroupoid :
    Space.IsSeparated C S hS A.groupoid.objectsToBase.hom := by
  rw [trivialActionGroupoid_objectsToBase_hom B G hG A]
  exact Space.isSeparated_of_isIso C S hS _

/-- The source and the target of the action groupoid of the trivial action are flat when
`G ⟶ B` is. -/
private theorem isFlat_trivialActionGroupoid
    (hflat : Space.IsFlat C S hS G.hom)
    (m : A.groupoid.arrows ⟶ A.groupoid.objects)
    (hm : m ≫ A.groupoid.objectsToBase = A.groupoid.arrowsToBase) :
    Space.IsFlat C S hS m.hom :=
  (holdsOnEveryEtaleChart_trivialActionGroupoid_iff B G hG A
    (@AlgebraicGeometry.Flat.{u}) m hm).2 hflat

/-- The source and the target of the action groupoid of the trivial action are locally of finite
presentation when `G ⟶ B` is. -/
private theorem isLocallyOfFinitePresentation_trivialActionGroupoid
    (hlfp : Space.IsLocallyOfFinitePresentation C S hS G.hom)
    (m : A.groupoid.arrows ⟶ A.groupoid.objects)
    (hm : m ≫ A.groupoid.objectsToBase = A.groupoid.arrowsToBase) :
    Space.IsLocallyOfFinitePresentation C S hS m.hom :=
  (holdsOnEveryEtaleChart_trivialActionGroupoid_iff B G hG A
    (@AlgebraicGeometry.LocallyOfFinitePresentation.{u}) m hm).2 hlfp

end TrivialAction

section TrivialActionOverBase

variable (G : Over (Space.terminalSpace C S hS).obj) [GrpObj G]
  (hG : IsAlgebraicSpace C S hS G.left)
  (A : Space.ActionGroupoidConstruction (Space.terminalSpace C S hS) G
    (𝟙_ (Over (Space.terminalSpace C S hS).obj)) hG (Space.terminalSpace C S hS).property)

/-- **The quotient by a trivial action is separated over the base.** Let `G` be a group
algebraic space over `S`, endow `S` with the trivial action of `G` and let `𝒵` be an algebraic
stack equivalent over the site to the quotient stack `[S/G]`. If `G ⟶ S` is proper, flat and
locally of finite presentation, then `𝒵` is separated over the base scheme of the site.

This is Stacks 0DTY, part (6) at the action groupoid of the trivial action: the source and the
target of that groupoid are the structural morphism of `G ×_S S`, hence proper, flat and locally
of finite presentation with `G ⟶ S`, and the structure morphism of its object space is an
isomorphism, hence separated. -/
theorem isSeparatedOver_quotientStack_trivialAction
    (𝒵 : AlgebraicStacks.{u, w} C S hS)
    (hequiv : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (quotientStack A.groupoid).p 𝒵.val.val.p))
    (hproper : Space.IsProper C S hS G.hom)
    (hflat : Space.IsFlat C S hS G.hom)
    (hlfp : Space.IsLocallyOfFinitePresentation C S hS G.hom) :
    IsSeparatedOver.{u, w} C S hS 𝒵 :=
  isSeparatedOver_of_isProper_source_target.{u, w} A.groupoid 𝒵 hequiv
    (isFlat_trivialActionGroupoid _ G hG A hflat _ A.groupoid.source_over)
    (isFlat_trivialActionGroupoid _ G hG A hflat _ A.groupoid.target_over)
    (isLocallyOfFinitePresentation_trivialActionGroupoid _ G hG A hlfp _
      A.groupoid.source_over)
    (isLocallyOfFinitePresentation_trivialActionGroupoid _ G hG A hlfp _
      A.groupoid.target_over)
    ((isProper_trivialActionGroupoid_iff _ G hG A _ A.groupoid.source_over).2 hproper)
    ((isProper_trivialActionGroupoid_iff _ G hG A _ A.groupoid.target_over).2 hproper)
    (isSeparated_objectsToBase_trivialActionGroupoid _ G hG A)

/-- **The quotient by a trivial action is separated**, in the unqualified, absolute sense of
Stacks 050D part (7). Let `G` be a group algebraic space over `S`, endow `S` with the trivial
action of `G` and let `𝒵` be an algebraic stack equivalent over the site to the quotient stack
`[S/G]`. If `G ⟶ S` is proper, flat and locally of finite presentation and the algebraic stack of
the base scheme is separated, then `𝒵` is separated.

This is separatedness over the base scheme, which
`AlgebraicGeometry.Stack.isSeparatedOver_quotientStack_trivialAction` gives, strengthened by
Stacks 050L part (7) at the structure 1-morphism. The hypothesis `hBase` on the base is needed:
an algebraic stack separated over a base which is not itself separated need not be
separated. -/
theorem isAbsolutelySeparated_quotientStack_trivialAction
    (hZ : C.Contains (⊤_ Scheme.{u}))
    (hBase : AlgebraicStacks.IsAbsolutelySeparated.{u, w} C S hS hZ
      (schemeStack.{u, w} C S hS (Over.mk (𝟙 (C.obj hS)))))
    (𝒵 : AlgebraicStacks.{u, w} C S hS)
    (hequiv : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (quotientStack A.groupoid).p 𝒵.val.val.p))
    (hproper : Space.IsProper C S hS G.hom)
    (hflat : Space.IsFlat C S hS G.hom)
    (hlfp : Space.IsLocallyOfFinitePresentation C S hS G.hom) :
    AlgebraicStacks.IsAbsolutelySeparated.{u, w} C S hS hZ 𝒵 :=
  AlgebraicStacks.isAbsolutelySeparated_of_isSeparated.{u, w} C S hS hZ
    (structureMorphism.{u, w} C S hS 𝒵) hBase
    (isSeparatedOver_quotientStack_trivialAction.{u, w} G hG A 𝒵 hequiv hproper hflat hlfp)

end TrivialActionOverBase

end AlgebraicGeometry.Stack

end
