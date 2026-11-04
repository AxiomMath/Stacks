module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatLocusAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningFlatDeformation

/-!
# Base change of flatness at a point along a smooth chart of the target

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`, let `V` be an algebraic space over
`S` with a *smooth* 1-morphism `b : V ⟶ 𝒴`, and let `Q` be a 2-fibre product of the cospan
`(b, f)` whose apex is represented by an algebraic space `U`. Read through that representing
equivalence, the two projections of `Q` become a 1-morphism `U ⟶ 𝒳` and a morphism `h : U ⟶ V`
of algebraic spaces, and this file proves that for every point `u` of `|U|`

  `f` is flat at the image of `u` in `|𝒳|`  ↔  `h` is flat at `u`.

Both directions are base change and descent of flatness at a point (**Stacks 0CID**) along the
smooth chart `b`: left to right is base change, right to left is descent.

## Main results

* `isFlatAt_spacePointMap_iff_of_representedTwoFibreProduct`: the equivalence above.
* `isFlatAt_representingMap_of_isFlatAt` and `isFlatAt_of_isFlatAt_representingMap`: its two
  directions, the second stated at a prescribed point of `|𝒳|` carrying a lift to `|U|`.

## How it is proved

The square `Q`, read through the representing equivalence of its apex, *is* a diagram of
**Stacks 06FM** (2) over `f` whose comparison 1-morphisms are all smooth, so the statement is
`AlgebraicGeometry.Stack.AlgebraicStacks.isFlatAt_spacePointMap_iff_of_smoothDiagram` — itself
both directions of **Stacks 0CIC** — with that diagram substituted. Only the two hypotheses of
that lemma have to be produced.

* The left vertical 1-morphism is `cc ≫ Q.snd`, where `cc` is the backward 1-morphism
  `U ⟶ Q.pt` of the representing equivalence, and the top horizontal morphism of algebraic
  spaces is the one `Q.fst` induces through **Stacks 04SW**. The 2-cell filling the square is
  the filler of `Q` whiskered by `cc`, once the morphism of representing presheaves is
  identified with `cc ≫ Q.fst`: that identification is
  `AlgebraicGeometry.Stack.nonempty_twoIso_associatedMap_representingMap` applied to the
  composite, whose own morphism of representing presheaves is `h` because `cc` induces the
  identity (`AlgebraicGeometry.Stack.representingMap_equivalenceOverInvMap`) and
  **Stacks 04SW** is functorial (`AlgebraicGeometry.Stack.representingMap_comp`).
* The smoothness of *every* comparison 1-morphism from that diagram to *every* 2-fibre product
  of the cospan `(b, f)` is
  `AlgebraicGeometry.Stack.isRelativelySmooth_preHom_diagramCone_of_chart`, whose hypothesis is
  smoothness of `cc` — and `cc` is smooth because it induces the identity morphism of
  representing presheaves, which is
  `AlgebraicGeometry.Stack.isRelativelySmooth_equivalenceOverInvMap`.

So the apex being an *honest* 2-fibre product, rather than merely a square with a smooth
comparison, is what discharges the smoothness of the comparisons: there is nothing to check
about the chart beyond smoothness of `b` itself.

## Implementation notes

**Why this is not a weakening of the chart hypothesis of Stacks 0CIC.** The diagrams
**Stacks 0CIC** tests flatness on ask for the *comparison* 1-morphism `U ⟶ 𝒳 ×_𝒴 V` to be flat,
not for `U` to present that 2-fibre product. The statements here are the special case where the
comparison is an equivalence, which is the case every base change along a chart produces, and
they are stated because that case is the one a consumer can recognise: it needs no flat
comparison to be exhibited, only a representing algebraic space for the apex — which
**Stacks 0300** supplies, in the shape of
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_chartBaseChange`.

The chart `b` is taken as a 1-morphism out of `AlgebraicGeometry.Stack.fibredCategory`, not out
of an `AlgebraicGeometry.Stack.algebraicSpaceStack` or an
`AlgebraicGeometry.Stack.schemeStack`, because that is the shape
`AlgebraicGeometry.Stack.AlgebraicStacks.isFlatAt_spacePointMap_iff_of_smoothDiagram` and the
diagrams of **Stacks 06FM** are written in; a chart of an algebraic stack in that shape is
produced by
`AlgebraicGeometry.Stack.exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation`.
Smoothness is `AlgebraicGeometry.Stack.IsRelativelySmooth`, the relative property of
**Stacks 03YK** at smoothness of morphisms of algebraic spaces, which is what the diagrams of
Stacks 06FM ask of their right vertical 1-morphism.

No surjectivity of `b` is needed, and none is assumed: the equivalence is about one point `u` of
`|U|` and its image, and a point of `|𝒳|` outside the image of the chart is simply not spoken
about. The consumer which needs every point of `|𝒳|` to be reached adds surjectivity itself, as
`AlgebraicGeometry.Stack.AlgebraicStacks.exists_chart_setOf_isFlatAt` does.

No `@[stacks]` attribute is attached. **Stacks 0CID** is the definition of flatness at a point
and **Stacks 0CIC** its chart independence; both are formalized in
`StacksFrontier/AlgebraicGeometry/Stacks/FlatAtAPoint.lean`, and the chapter carries no separate
base-change or descent assertion for flatness at a point of a 1-morphism of algebraic stacks.
What is proved here is the reading of Stacks 0CIC on the particular diagrams a base change along
a chart produces.

## References

* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 0CIC](https://stacks.math.columbia.edu/tag/0CIC)
* [Stacks Project, Tag 0CID](https://stacks.math.columbia.edu/tag/0CID)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
  {U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (hU : IsAlgebraicSpace B S hS U) (hV : IsAlgebraicSpace B S hS V)
  {b : Stack.fibredCategory B S hS V ⟶ 𝒴.val}
  {Q : Bicategory.TwoCommSq b f.hom}
  (eU : StacksRepresentableCFG.EquivalenceOver Q.pt.val.p
    (presheafOfCategories (U ⋙ typeToCat)).p)

/-! ### The top horizontal morphism of a represented base change -/

/-- **The morphism of representing presheaves of the projection out of a represented 2-fibre
product is the one its composite with the representing equivalence induces.** Reading `Q.fst`
through the given equivalence of the apex and the identity of `V` gives the same morphism
`U ⟶ V` as reading the composite `U ⟶ Q.pt ⟶ V` through the identities on both sides:
**Stacks 04SW** is functorial, and the backward 1-morphism of a representing equivalence induces
the identity. -/
theorem representingMap_equivalenceOverInvMap_comp_fst :
    Stack.representingMap B S hS (Stack.fibredCategory B S hS U)
        (Stack.fibredCategory B S hS V) U V
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (Stack.equivalenceOverInvMap B S hS U eU ≫ Q.fst) =
      Stack.representingMap B S hS Q.pt (Stack.fibredCategory B S hS V) U V eU
        (StacksRepresentableCFG.EquivalenceOver.refl _) Q.fst := by
  rw [Stack.representingMap_comp B S hS U U V
      (StacksRepresentableCFG.EquivalenceOver.refl _) eU
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (Stack.equivalenceOverInvMap B S hS U eU) Q.fst,
    Stack.representingMap_equivalenceOverInvMap B S hS U eU, Category.id_comp]

/-- **The 2-cell of the diagram a represented 2-fibre product defines.** The morphism of
representing presheaves of `Q.fst` is 2-isomorphic, as a 1-morphism, to the composite of the
backward 1-morphism of the representing equivalence with `Q.fst`.

This is `AlgebraicGeometry.Stack.nonempty_twoIso_associatedMap_representingMap` for that
composite, whose morphism of representing presheaves is the one of `Q.fst` by
`AlgebraicGeometry.Stack.AlgebraicStacks.representingMap_equivalenceOverInvMap_comp_fst`. -/
theorem nonempty_twoIso_associatedMap_representingMap_fst :
    Nonempty ((Stack.associatedMap B S hS
          (Stack.representingMap B S hS Q.pt (Stack.fibredCategory B S hS V) U V eU
            (StacksRepresentableCFG.EquivalenceOver.refl _) Q.fst)).1 ≅
      Stack.equivalenceOverInvMap B S hS U eU ≫ Q.fst) := by
  obtain ⟨e⟩ := Stack.nonempty_twoIso_associatedMap_representingMap B S hS U V
    (Stack.equivalenceOverInvMap B S hS U eU ≫ Q.fst)
  refine ⟨Iso.trans (eqToIso ?_) e⟩
  exact congrArg (fun m : U ⟶ V => (Stack.associatedMap B S hS m).1)
    (representingMap_equivalenceOverInvMap_comp_fst B S hS f eU).symm

/-! ### Base change and descent of flatness at a point along a smooth chart -/

include hU hV in
/-- **Flatness at a point is base changed and descended along a smooth chart of the target.**
Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`, let `V` be an algebraic space over
`S` with a smooth 1-morphism `b : V ⟶ 𝒴`, and let `Q` be a 2-fibre product of the cospan
`(b, f)` whose apex is represented by an algebraic space `U`. Write `h : U ⟶ V` for the morphism
of algebraic spaces that `Q.fst` induces through **Stacks 04SW** and `cc ≫ Q.snd` for the
1-morphism `U ⟶ 𝒳` that `Q.snd` induces. Then `f` is flat at the image in `|𝒳|` of a point `u`
of `|U|`, in the sense of **Stacks 0CID**, exactly when `h` is flat at `u`.

The square read through the representing equivalence is a diagram of **Stacks 06FM** (2) whose
right vertical 1-morphism is `b` and whose comparison 1-morphisms are all smooth — the
comparison to `Q` itself being the backward 1-morphism of the representing equivalence, by
`AlgebraicGeometry.Stack.isRelativelySmooth_preHom_diagramCone_of_chart` — so this is
`AlgebraicGeometry.Stack.AlgebraicStacks.isFlatAt_spacePointMap_iff_of_smoothDiagram`, which is
both directions of **Stacks 0CIC**. -/
theorem isFlatAt_spacePointMap_iff_of_representedTwoFibreProduct
    (hbsm : Stack.IsRelativelySmooth B S hS b) (hQ : Bicategory.IsTwoFibreProduct Q)
    (u : Space.points B S hS U) :
    IsFlatAt B S hS f
        (Stack.spacePointMap B S hS U 𝒳.val
          (Stack.equivalenceOverInvMap B S hS U eU ≫ Q.snd).hom u) ↔
      Space.IsFlatAt B S hS
        (Stack.representingMap B S hS Q.pt (Stack.fibredCategory B S hS V) U V eU
          (StacksRepresentableCFG.EquivalenceOver.refl _) Q.fst) u := by
  obtain ⟨e⟩ := nonempty_twoIso_associatedMap_representingMap_fst B S hS f eU
  exact isFlatAt_spacePointMap_iff_of_smoothDiagram B S hS f hU hV
    (Stack.equivalenceOverInvMap B S hS U eU ≫ Q.snd) b
    (Stack.representingMap B S hS Q.pt (Stack.fibredCategory B S hS V) U V eU
      (StacksRepresentableCFG.EquivalenceOver.refl _) Q.fst)
    (Bicategory.whiskerRightIso e b ≪≫
      Bicategory.whiskerLeftIso (Stack.equivalenceOverInvMap B S hS U eU) Q.iso)
    hbsm
    (fun Q' hQ' k => Stack.isRelativelySmooth_preHom_diagramCone_of_chart B S hS f.hom b Q hQ
      (Stack.equivalenceOverInvMap B S hS U eU)
      (Stack.isRelativelySmooth_equivalenceOverInvMap B S hS U hU eU) _ e Q' hQ' k) u

include hU hV in
/-- **Base change of flatness at a point along a smooth chart of the target.** The forward
direction of
`AlgebraicGeometry.Stack.AlgebraicStacks.isFlatAt_spacePointMap_iff_of_representedTwoFibreProduct`:
if `f` is flat at a point of `|𝒳|`, then the base change of `f` along a smooth chart of `𝒴`,
read as a morphism of algebraic spaces, is flat at every point of `|U|` above it. -/
theorem isFlatAt_representingMap_of_isFlatAt
    (hbsm : Stack.IsRelativelySmooth B S hS b) (hQ : Bicategory.IsTwoFibreProduct Q)
    (u : Space.points B S hS U) (x : points B S hS 𝒳)
    (hx : Stack.spacePointMap B S hS U 𝒳.val
      (Stack.equivalenceOverInvMap B S hS U eU ≫ Q.snd).hom u = x)
    (hf : IsFlatAt B S hS f x) :
    Space.IsFlatAt B S hS
      (Stack.representingMap B S hS Q.pt (Stack.fibredCategory B S hS V) U V eU
        (StacksRepresentableCFG.EquivalenceOver.refl _) Q.fst) u :=
  (isFlatAt_spacePointMap_iff_of_representedTwoFibreProduct B S hS f hU hV eU hbsm hQ u).1
    (hx ▸ hf)

include hU hV in
/-- **Descent of flatness at a point along a smooth chart of the target.** The backward
direction of
`AlgebraicGeometry.Stack.AlgebraicStacks.isFlatAt_spacePointMap_iff_of_representedTwoFibreProduct`:
if the base change of `f` along a smooth chart of `𝒴`, read as a morphism of algebraic spaces,
is flat at a point `u` of `|U|`, then `f` is flat at the image of `u` in `|𝒳|`.

This is the statement that turns flatness produced *on a chart* into flatness at a point over
the stack itself. -/
theorem isFlatAt_of_isFlatAt_representingMap
    (hbsm : Stack.IsRelativelySmooth B S hS b) (hQ : Bicategory.IsTwoFibreProduct Q)
    (u : Space.points B S hS U) (x : points B S hS 𝒳)
    (hx : Stack.spacePointMap B S hS U 𝒳.val
      (Stack.equivalenceOverInvMap B S hS U eU ≫ Q.snd).hom u = x)
    (hh : Space.IsFlatAt B S hS
      (Stack.representingMap B S hS Q.pt (Stack.fibredCategory B S hS V) U V eU
        (StacksRepresentableCFG.EquivalenceOver.refl _) Q.fst) u) :
    IsFlatAt B S hS f x :=
  hx ▸ (isFlatAt_spacePointMap_iff_of_representedTwoFibreProduct B S hS f hU hV eU hbsm hQ u).2 hh

end AlgebraicGeometry.Stack.AlgebraicStacks

end
