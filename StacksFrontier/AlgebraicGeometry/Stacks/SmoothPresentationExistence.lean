module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStack
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionSmoothPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionSmoothProjections

/-!
# Every algebraic stack has a presentation (Stacks 04T3)

Let `S` be a scheme of a big fppf site. A *presentation* of a category over `(Sch/S)_fppf` is a
smooth groupoid `(U, R, s, t, c)` in algebraic spaces over `S` together with an equivalence
`[U/R] ⟶ 𝒳` of categories over the site (Stacks 04TI). Section 94.16 of the source constructs
one for every algebraic stack: take the presentation `𝒮_U ⟶ 𝒳` by a scheme that algebraicity
provides, let `R` be the self-intersection `𝒮_U ×_𝒳 𝒮_U`, and read off the groupoid of
Stacks 04T4 (4) together with the canonical 1-morphism of Stacks 04T4 (5). Stacks 04T5 says that
the source and target of that groupoid are smooth and that the canonical 1-morphism is an
equivalence, which is exactly a presentation.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.changeBase`: a groupoid in algebraic spaces over
  one base, read over another base receiving it.

## Main results

* `AlgebraicGeometry.Stack.isTerminal_baseSpace`: the base `S`, read as an algebraic space over
  itself, is the final algebraic space over `S`.
* `AlgebraicGeometry.Stack.nonempty_groupoidPresentation`: **Stacks 04T3**, the existence of a
  presentation of an algebraic stack.

## Implementation notes

Nothing is proved here that the four results of Section 94.16 do not already give; the
content is that their hypotheses are met by the defining clauses of Stacks 026O with no further
input. The 1-morphism `f : 𝒮_U ⟶ 𝒳` and its representability by algebraic spaces come from the
presentation clause of `AlgebraicGeometry.Stack.IsAlgebraicStack`, whose surjectivity and
smoothness are stated in exactly the base-change form that
`AlgebraicGeometry.Stack.HasRelativeProperty` (Stacks 03YK) unfolds to, so smoothness of `f` in
the sense of Stacks 04XB is that clause's second conjunct and nothing has to be relocalized. The
algebraic space representing the source is `yoneda.obj U`, by
`CategoryTheory.PresheafOfCategories.sliceElementsEquivalenceOver`; the algebraic space
representing the self-intersection is the one Stacks 04T4 (1) produces from the representable
diagonal.

A groupoid in algebraic spaces "over `S`" is one over the final algebraic space over `S`, and the
library has two presentations of that object: `AlgebraicGeometry.Space.terminalSpace`, the
presheaf of the object `𝟙 : S ⟶ S` of the site, over which the groupoid of Stacks 04T4 (4) is
built, and `AlgebraicGeometry.Stack.baseSpace`, the presheaf of the chosen final object `⊤_` of
the site, which is the base of `AlgebraicGeometry.Stack.GroupoidPresentation`. The chosen final
object is picked by `Classical.choice`, so the two are not the same term; they are both final,
which is all that is needed, since the base of a groupoid in algebraic spaces enters only through
the two structure morphisms and the three equations saying the source, the target and the
composition are morphisms over it. `changeBase` moves the groupoid along the unique morphism
between the two, and leaves the underlying groupoid in presheaves — hence the quotient stack, and
hence the equivalence of Stacks 04T5 (2) — unchanged.

The conclusion is `Nonempty` of the presentation structure rather than a presentation: a choice
of the representing space of the self-intersection, of the equivalences presenting it and the
source, and of the quasi-inverse of the canonical 1-morphism all enter the data, and the source
asserts only that some presentation exists.

## References

* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 04T3](https://stacks.math.columbia.edu/tag/04T3)
* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 04T5](https://stacks.math.columbia.edu/tag/04T5)
* [Stacks Project, Tag 04TH](https://stacks.math.columbia.edu/tag/04TH)
* [Stacks Project, Tag 04TI](https://stacks.math.columbia.edu/tag/04TI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PresheafOfCategories

namespace AlgebraicGeometry

universe u w

namespace GroupoidInAlgebraicSpaces

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {Z Z' : AlgebraicSpaces B S hS}

/-- A groupoid in algebraic spaces over `Z`, read as a groupoid in algebraic spaces over an
algebraic space `Z'` receiving `Z`: the spaces of objects and of arrows, the source, the target
and the composition are unchanged, and the two structure morphisms to the new base are the old
ones followed by `i`. -/
noncomputable def changeBase (i : Z ⟶ Z') (G : GroupoidInAlgebraicSpaces B S hS Z) :
    GroupoidInAlgebraicSpaces B S hS Z' where
  objects := G.objects
  arrows := G.arrows
  objectsToBase := G.objectsToBase ≫ i
  arrowsToBase := G.arrowsToBase ≫ i
  source := G.source
  target := G.target
  source_over := by rw [← Category.assoc, G.source_over]
  target_over := by rw [← Category.assoc, G.target_over]
  comp := G.comp
  comp_over := by rw [← Category.assoc, G.comp_over, Category.assoc]
  pointwiseGroupoid := G.pointwiseGroupoid

/-- Changing the base leaves the source morphism unchanged. -/
theorem changeBase_source (i : Z ⟶ Z') (G : GroupoidInAlgebraicSpaces B S hS Z) :
    (changeBase i G).source = G.source :=
  rfl

/-- Changing the base leaves the target morphism unchanged. -/
theorem changeBase_target (i : Z ⟶ Z') (G : GroupoidInAlgebraicSpaces B S hS Z) :
    (changeBase i G).target = G.target :=
  rfl

/-- Changing the base leaves the underlying groupoid in presheaves unchanged. -/
theorem toGroupoidInFunctors_changeBase (i : Z ⟶ Z')
    (G : GroupoidInAlgebraicSpaces B S hS Z) :
    (changeBase i G).toGroupoidInFunctors = G.toGroupoidInFunctors :=
  rfl

/-- Changing the base leaves the quotient stack of Stacks 044Q unchanged. -/
theorem quotientStack_changeBase (i : Z ⟶ Z')
    (G : GroupoidInAlgebraicSpaces B S hS Z) :
    Stack.quotientStack (changeBase i G) = Stack.quotientStack G :=
  rfl

end GroupoidInAlgebraicSpaces

namespace Stack

/-- **The base `S`, read as an algebraic space over itself, is the final algebraic space over
`S`.** It is the algebraic space of the final object of the big fppf site of `S`, and `yoneda`
carries a final object to the final presheaf. -/
noncomputable def isTerminal_baseSpace (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : IsTerminal (baseSpace B S hS) :=
  have hT : IsTerminal (yoneda.obj (⊤_ (BigFppfOver B S hS))) :=
    terminalIsTerminal.isTerminalObj yoneda
  haveI : ∀ A : AlgebraicSpaces B S hS, Unique (A ⟶ baseSpace B S hS) := fun A =>
    { default := ObjectProperty.homMk (hT.from A.1)
      uniq := fun _ => ObjectProperty.hom_ext _ (hT.hom_ext _ _) }
  IsTerminal.ofUnique _

/-- **Stacks 04T3: every algebraic stack has a presentation.** Let `𝒳` be an algebraic stack
over `S`. Then there are a smooth groupoid `(U, R, s, t, c)` in algebraic spaces over `S` and an
equivalence over the big fppf site of `S` from its quotient stack `[U/R]` to `𝒳`.

The groupoid is the self-intersection groupoid of Stacks 04T4 (4) of the presentation of `𝒳` by
a scheme, which is smooth by Stacks 04T5 (1), and the equivalence is the canonical 1-morphism of
Stacks 04T4 (5), which is an equivalence by Stacks 04T5 (2). -/
@[stacks 04T3 "every algebraic stack has a presentation by a smooth groupoid in algebraic spaces"]
theorem nonempty_groupoidPresentation
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) :
    Nonempty (GroupoidPresentation B S hS 𝒳.val) := by
  obtain ⟨_hfib, ⟨⟨-, -⟩, -, W, f, hf, hfprop⟩⟩ := id h𝒳
  -- The presentation by a scheme, read as a 1-morphism of categories fibred in groupoids.
  let 𝒰 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
    schemeFibredCategory B S hS W
  let F : 𝒰 ⟶ 𝒳 := Bicategory.InducedBicategory.mkHom f
  -- Stacks 025Z: the slice of the site over `W` is the algebraic space `yoneda.obj W`.
  let U : AlgebraicSpaces B S hS := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩
  let eU : StacksRepresentableCFG.EquivalenceOver
      𝒰.val.p (presheafOfCategories (U.obj ⋙ typeToCat)).p :=
    sliceElementsEquivalenceOver W
  -- Stacks 04T4 (1): the self-intersection is representable by an algebraic space.
  obtain ⟨Robj, hRobj, ⟨eR₀⟩⟩ :=
    SelfIntersection.isRepresentableByAlgebraicSpace_relation_of_isAlgebraicStack
      B S hS 𝒰 𝒳 F.hom h𝒳 (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS W)
  let R : AlgebraicSpaces B S hS := ⟨Robj, hRobj⟩
  let eR : StacksRepresentableCFG.EquivalenceOver
      (SelfIntersection.relation B S hS 𝒰 𝒳 F.hom).val.p
      (presheafOfCategories (R.obj ⋙ typeToCat)).p := eR₀
  -- Smoothness of `f` in the sense of Stacks 04XB is the second conjunct of Stacks 026O.
  have hsmooth : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.smoothMorphismProperty B S hS) F hf :=
    fun V y hy G hG he => (hfprop V y hy G hG he).2
  -- Stacks 04T5 (1): the source and target of the groupoid are smooth.
  have hsrc := SelfIntersection.isSmooth_selfIntersectionPresentation_source
    (𝒰 := 𝒰) (𝒳 := 𝒳) (F := F) (U := U) (R := R) eU eR hf hsmooth h𝒳
  have htgt := SelfIntersection.isSmooth_selfIntersectionPresentation_target
    (𝒰 := 𝒰) (𝒳 := 𝒳) (F := F) (U := U) (R := R) eU eR hf hsmooth h𝒳
  -- Stacks 04T5 (2): the canonical 1-morphism out of the quotient stack is an equivalence.
  obtain ⟨e, -⟩ := SelfIntersection.exists_equivalenceOver_canonicalMap_of_isSmooth
    (𝒰 := 𝒰) (𝒳 := 𝒳) (f := F) (U := U) (R := R) eU eR h𝒳
    hsmooth (fun V y hy G hG he => (hfprop V y hy G hG he).1)
  refine ⟨{
    groupoid := GroupoidInAlgebraicSpaces.changeBase
      ((isTerminal_baseSpace B S hS).from
        (SelfIntersection.selfIntersectionPresentation eU eR h𝒳).base)
      (SelfIntersection.selfIntersectionPresentation eU eR h𝒳).groupoid
    smooth := ⟨hsrc, htgt⟩
    equivalence := ?_ }⟩
  rw [GroupoidInAlgebraicSpaces.quotientStack_changeBase]
  exact e

end Stack

end AlgebraicGeometry

end
