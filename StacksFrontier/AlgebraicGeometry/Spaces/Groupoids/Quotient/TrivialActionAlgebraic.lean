module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.TrivialActionGerbe
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStack
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.GroupSpaceTranslation
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack

/-!
# Algebraicity of the quotient by a trivial action (Stacks 06PL)

Let `G` be a group algebraic space over an algebraic space `B` over a scheme `S` of a big fppf
site, and endow `B` with the trivial action of `G`. The quotient stack `[B/G]` is an algebraic
stack as soon as `G` is flat and locally of finite presentation over `B`.

## Main results

* `AlgebraicGeometry.Stack.holdsOnEveryEtaleChart_trivialActionGroupoid_iff`: a property of
  scheme morphisms, tested on every commuting square of étale charts, holds on a structure
  morphism over `B` of the action groupoid of the trivial action exactly when it holds on the
  structural morphism `G ⟶ B`.
* `AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_trivialAction`: **Stacks 06PL**, the
  implication from flatness and local finite presentation of `G ⟶ B` to algebraicity of
  `[B/G]`.

## Implementation notes

For the trivial action the object space of the action groupoid of Stacks 0444 is `B` and its
arrow space is `G ×_B B`, so both the source and the target are morphisms `G ×_B B ⟶ B` over
`B`, hence equal to the structural morphism of `G ×_B B`; the right unitor identifies the
latter with `G ⟶ B`. That identification holds for an arbitrary morphism of the arrow space to
the object space which commutes with the two structure morphisms to `B`, which is what
`AlgebraicGeometry.Stack.holdsOnEveryEtaleChart_trivialActionGroupoid_iff` says, and it is
applied to the source and to the target in turn. Flatness of Stacks 03ML and local finite
presentation of Stacks 03XP are both instances of
`AlgebraicGeometry.Space.HoldsOnEveryEtaleChart`, so one lemma serves for both.

The identifications of the object and arrow spaces carried by
`AlgebraicGeometry.Space.ActionGroupoidConstruction` are equalities of algebraic spaces and the
identifications of the structure morphisms are heterogeneous, so the conjugation by the induced
`CategoryTheory.eqToHom` is transported by `CategoryTheory.conj_eqToHom_iff_heq`, exactly as in
`AlgebraicGeometry.Stack.isGerbeOver_quotientStackToBase_trivialAction` of Stacks 06PF.

Stacks 06FI — the quotient stack of a groupoid in algebraic spaces whose source and target are
flat and locally of finite presentation is an algebraic stack — is not in the library, so it is
carried as an explicit hypothesis, and the part string of the `@[stacks 06PL]` attribute records
this. Only the forward implication is proved: the converse rests on Stacks 06PK, which is not in
the library either, and on the descent arguments of Stacks 06NR, Stacks 041T and Stacks 041W.

## References

* [Stacks Project, Tag 0444](https://stacks.math.columbia.edu/tag/0444)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 06FI](https://stacks.math.columbia.edu/tag/06FI)
* [Stacks Project, Tag 06PF](https://stacks.math.columbia.edu/tag/06PF)
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

/-- Conjugating a morphism of presheaves by the transports attached to equalities of its source
and of its target does not change whether a property of scheme morphisms holds on every
commuting square of étale charts of it. -/
private theorem holdsOnEveryEtaleChart_eqToHom_conj_iff (P : MorphismProperty Scheme.{u})
    {F F' Y Y' : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ Y) (h₁ : F' = F) (h₂ : Y = Y') :
    Space.HoldsOnEveryEtaleChart C S hS P (eqToHom h₁ ≫ f ≫ eqToHom h₂) ↔
      Space.HoldsOnEveryEtaleChart C S hS P f := by
  subst h₁
  subst h₂
  rw [eqToHom_refl, eqToHom_refl, Category.comp_id, Category.id_comp]

/-- For the trivial action of a group algebraic space `G` on `B`, a morphism from the arrow
space to the object space of the action groupoid of Stacks 0444 which commutes with the two
structure morphisms to `B` has a property of scheme morphisms on every commuting square of
étale charts exactly when the structural morphism `G ⟶ B` does. -/
theorem holdsOnEveryEtaleChart_trivialActionGroupoid_iff
    (B : AlgebraicSpaces C S hS) (G : Over B.obj) [GrpObj G]
    (hG : IsAlgebraicSpace C S hS G.left)
    (A : Space.ActionGroupoidConstruction B G (𝟙_ (Over B.obj)) hG B.property)
    (P : MorphismProperty Scheme.{u}) (m : A.groupoid.arrows ⟶ A.groupoid.objects)
    (hm : m ≫ A.groupoid.objectsToBase = A.groupoid.arrowsToBase) :
    Space.HoldsOnEveryEtaleChart C S hS P m.hom ↔
      Space.HoldsOnEveryEtaleChart C S hS P G.hom := by
  have hobjs : A.groupoid.objects.obj = B.obj := congrArg (fun z => z.obj) A.objects_eq
  have harrs : A.groupoid.arrows.obj = (G ⊗ 𝟙_ (Over B.obj)).left :=
    congrArg (fun z => z.obj) A.arrows_eq
  have key : ∀ {X X'} (f : X ⟶ B.obj) (g : X' ⟶ B.obj) (h : X = X'), f ≍ g →
      f = eqToHom h ≫ g := fun f g h hfg => by
    simpa using (conj_eqToHom_iff_heq f g h rfl).2 hfg
  have hobjsToBase := key A.groupoid.objectsToBase.hom (𝟙 B.obj) hobjs A.objectsToBase_eq
  have harrsToBase := key A.groupoid.arrowsToBase.hom (G ⊗ 𝟙_ (Over B.obj)).hom harrs
    A.arrowsToBase_eq
  have hmcomp : m.hom ≫ A.groupoid.objectsToBase.hom = A.groupoid.arrowsToBase.hom :=
    congrArg (fun g : A.groupoid.arrows ⟶ B => g.hom) hm
  have hmeq : m.hom ≫ eqToHom hobjs = eqToHom harrs ≫ (G ⊗ 𝟙_ (Over B.obj)).hom := by
    simpa [hobjsToBase, harrsToBase] using hmcomp
  have hm' : m.hom =
      eqToHom harrs ≫ (G ⊗ 𝟙_ (Over B.obj)).hom ≫ eqToHom hobjs.symm := by
    rw [← Category.assoc]
    exact (comp_eqToHom_iff hobjs m.hom _).1 hmeq
  rw [hm', holdsOnEveryEtaleChart_eqToHom_conj_iff]
  have hunitor : ((Over.forget B.obj).mapIso (ρ_ G)).hom ≫ G.hom =
      (G ⊗ 𝟙_ (Over B.obj)).hom := Over.w (ρ_ G).hom
  rw [← hunitor]
  exact (Space.holdsOnEveryEtaleChart_precomp_iso C S hS P
    ((Over.forget B.obj).mapIso (ρ_ G)) G.hom).symm

/-- **Stacks 06PL**, the implication from flatness and local finite presentation to
algebraicity. Let `G` be a group algebraic space over an algebraic space `B` over `S` and endow
`B` with the trivial action of `G`. If `G` is flat and locally of finite presentation over `B`,
then the quotient stack `[B/G]` is an algebraic stack.

Stacks 06FI, which is not in the library, is carried as the hypothesis `h06FI`. -/
@[stacks 06PL "the implication from flat and locally of finite presentation to algebraic, with \
Stacks 06FI carried as a hypothesis; the converse, which rests on Stacks 06PK, is not proved"]
theorem isAlgebraicStack_quotientStack_trivialAction
    (B : AlgebraicSpaces C S hS) (G : Over B.obj) [GrpObj G]
    (hG : IsAlgebraicSpace C S hS G.left)
    (A : Space.ActionGroupoidConstruction B G (𝟙_ (Over B.obj)) hG B.property)
    (h06FI : ∀ H : GroupoidInAlgebraicSpaces C S hS B,
      Space.IsFlat C S hS H.source.hom → Space.IsFlat C S hS H.target.hom →
        Space.IsLocallyOfFinitePresentation C S hS H.source.hom →
          Space.IsLocallyOfFinitePresentation C S hS H.target.hom →
            IsAlgebraicStack.{u, w} C S hS (quotientStack H))
    (hflat : Space.IsFlat C S hS G.hom)
    (hlfp : Space.IsLocallyOfFinitePresentation C S hS G.hom) :
    IsAlgebraicStack.{u, w} C S hS (quotientStack A.groupoid) := by
  have h := holdsOnEveryEtaleChart_trivialActionGroupoid_iff B G hG A
  exact h06FI A.groupoid
    ((h (@AlgebraicGeometry.Flat.{u}) _ A.groupoid.source_over).2 hflat)
    ((h (@AlgebraicGeometry.Flat.{u}) _ A.groupoid.target_over).2 hflat)
    ((h (@AlgebraicGeometry.LocallyOfFinitePresentation.{u}) _ A.groupoid.source_over).2 hlfp)
    ((h (@AlgebraicGeometry.LocallyOfFinitePresentation.{u}) _ A.groupoid.target_over).2 hlfp)

end AlgebraicGeometry.Stack

end
