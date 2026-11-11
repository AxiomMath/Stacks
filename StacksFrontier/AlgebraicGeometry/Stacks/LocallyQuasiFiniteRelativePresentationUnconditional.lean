module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordPresentationUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.FieldSpectrumCoverSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeFppfBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeFppfDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyQuasiFiniteOverField
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyQuasiFiniteRelativePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactFieldValuedPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactPointRepresentative
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionAtPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyOpenCriterion
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CospanReindex

/-!
# Stacks 06UF in full

`StacksFrontier.AlgebraicGeometry.Stacks.LocallyQuasiFiniteRelativePresentation` states the four
clauses of **Stacks 06UF** for a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` and
proves the chain (1) ⟹ (2) ⟹ (3) ⟹ (4), with (2) ⟹ (3) stated over the substantial direction of
**Stacks 06MF**, together with the quasi-DM conjunct of (4) ⟹ (1). This file discharges that
hypothesis and proves the remaining conjuncts of (4) ⟹ (1), so that the whole equivalence is the
theorem `isLocallyQuasiFinite_tfae`:

1. `f` is locally quasi-finite (**Stacks 06PU**);
2. `f` is quasi-DM (**Stacks 04YW**) and for every algebraic space `𝒱` over `𝒴` every locally
   quasi-finite 1-morphism `𝒰 ⟶ 𝒳 ×_𝒴 𝒱` out of an algebraic space has locally quasi-finite
   composite `𝒰 ⟶ 𝒱`;
3. for every algebraic space `𝒱` over `𝒴` there is a surjective, flat, locally finitely
   presented and locally quasi-finite 1-morphism `𝒰 ⟶ 𝒳 ×_𝒴 𝒱` out of an algebraic space whose
   composite `𝒰 ⟶ 𝒱` is locally quasi-finite;
4. one algebraic space `𝒱` surjective, flat and locally of finite presentation over `𝒴` carries
   such a cover of `𝒳 ×_𝒴 𝒱`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks`
  `.locallyQuasiFiniteCoverOnEverySpaceBaseChange_of_isQuasiDM_of_transfers_unconditional`:
  **Stacks 06UF**, (2) ⟹ (3), with the substantial direction of **Stacks 06MF** supplied by the
  theorem `AlgebraicGeometry.Stack.hasQuasiDMPresentation_of_isAbsolutelyQuasiDM`.
* `...discreteTopology_points_twoFibreProduct_of_hasLocallyQuasiFiniteFlatSpaceCoverOver`: the
  fibre of `f` over a field-valued point of `𝒴` which lifts to the chart has discrete space of
  points. This is the source's proof of the third conjunct of (4) ⟹ (1) after its reduction to
  such a point.
* `...isLocallyOfFiniteType_of_locallyQuasiFiniteCoverOnSomeFlatSpaceBaseChange`:
  **Stacks 06UF**, the local finite type conjunct of (4) ⟹ (1).
* `...exists_fieldSpectrumStack_hom_of_nonempty_points`: a point of an algebraic stack is hit by
  a 1-morphism from the algebraic stack of the spectrum of a field, presented in the shape the
  third clause of **Stacks 06PU** quantifies over.
* `...universallyOpen_to_fieldSpectrumStack`: a 1-morphism from the algebraic stack of an object
  of the site to the algebraic stack of the spectrum of a field is universally open in the sense
  of Properties of Stacks, Section 04XB. This is **Stacks 06DN** read on stacks.
* `...discreteTopology_points_of_locallyQuasiFiniteCoverOnSomeFlatSpaceBaseChange`:
  **Stacks 06UF**, the field-valued-fibre conjunct of (4) ⟹ (1).
* `...isLocallyQuasiFinite_of_locallyQuasiFiniteCoverOnSomeFlatSpaceBaseChange`:
  **Stacks 06UF**, (4) ⟹ (1).
* `...isLocallyQuasiFinite_tfae`: **Stacks 06UF**, the four-way equivalence.

## Implementation notes

Nothing is carried. The substantial direction of **Stacks 06MF**, which the statement of
`...AlgebraicStacks.locallyQuasiFiniteCoverOnEverySpaceBaseChange_of_isQuasiDM_of_transfers`
takes as its hypothesis `hPresentation`, is the theorem
`AlgebraicGeometry.Stack.hasQuasiDMPresentation_of_isAbsolutelyQuasiDM`, and the containment of
the terminal scheme in the site is `AlgebraicGeometry.BigFppfSite.contains_terminal`.

The field extension in the field-valued-fibre conjunct of (4) ⟹ (1) is *arbitrary*, where the
source takes a finite one. The source needs finiteness only to know that `Spec(k') ⟶ Spec(k)` is
flat and locally of finite presentation, and so open on points by **Stacks 06R7**; but every
1-morphism whose target is the algebraic stack of the spectrum of a field is already universally
open — that is **Stacks 06DN** on algebraic spaces, carried to stacks here through the
Section 04XB bridge for represented source and target
(`AlgebraicGeometry.Stack.hasRelativeProperty_iff_prop_representingMap`) — and **Stacks 06U1**
turns universal openness into openness on points of every stack base change. So the point of
`𝒱 ×_𝒴 Spec(k)` may be taken as it comes, with whatever residue field it has, and the source's
Nullstellensatz step — a nonempty algebraic space locally of finite type over `k` has a point
with residue field finite over `k` — is not needed.

Universal openness of morphisms of algebraic spaces carries the fpqc locality instance
(**Stacks 041P**) but not the base-change one, which the Section 04XB bridge also asks for;
`isStableUnderBaseChange_universallyOpenMorphismProperty` supplies it from **Stacks 03Z3** and
`AlgebraicGeometry.Stack.universallyOpenMorphismProperty_respectsIso`.

The 2-isomorphism `v ≫ g ≅ e ≫ y` produced by the filler of the chart's base-change square is
not an equality, so the two 2-fibre products it compares sit over cospans that agree only up to
an invertible 2-morphism. `CategoryTheory.Bicategory.TwoCommSq.reindexSnd` together with
`CategoryTheory.Bicategory.isTwoFibreProduct_reindexSnd` is what moves a 2-fibre product across
that, with the apex and both projections untouched.

## References

* [Stacks Project, Tag 02XD](https://stacks.math.columbia.edu/tag/02XD)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 03Z3](https://stacks.math.columbia.edu/tag/03Z3)
* [Stacks Project, Tag 041P](https://stacks.math.columbia.edu/tag/041P)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 06DN](https://stacks.math.columbia.edu/tag/06DN)
* [Stacks Project, Tag 06MF](https://stacks.math.columbia.edu/tag/06MF)
* [Stacks Project, Tag 06PU](https://stacks.math.columbia.edu/tag/06PU)
* [Stacks Project, Tag 06R7](https://stacks.math.columbia.edu/tag/06R7)
* [Stacks Project, Tag 06U1](https://stacks.math.columbia.edu/tag/06U1)
* [Stacks Project, Tag 06U7](https://stacks.math.columbia.edu/tag/06U7)
* [Stacks Project, Tag 06U8](https://stacks.math.columbia.edu/tag/06U8)
* [Stacks Project, Tag 06UB](https://stacks.math.columbia.edu/tag/06UB)
* [Stacks Project, Tag 06UE](https://stacks.math.columbia.edu/tag/06UE)
* [Stacks Project, Tag 06UF](https://stacks.math.columbia.edu/tag/06UF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

/-- **Discreteness descends along an open surjection.** If a discrete space maps onto a space by
a continuous open surjection, the target is discrete: the image of a singleton is an open
singleton. -/
private theorem discreteTopology_of_surjective_isOpenMap {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [DiscreteTopology X] {f : X → Y} (hsurj : Function.Surjective f)
    (hopen : IsOpenMap f) : DiscreteTopology Y := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  simpa only [Set.image_singleton] using hopen ({x} : Set X) (isOpen_discrete _)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- Discreteness of the points of a 2-fibre product of algebraic stacks transfers to any other
2-fibre product of the same cospan. -/
private theorem discreteTopology_points_congr_of_isTwoFibreProduct
    {𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴}
    (P Q : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (hQ : Bicategory.IsTwoFibreProduct Q)
    (h : @DiscreteTopology (Stack.points B S hS P.pt.val.val P.pt.val.property)
      (Stack.pointTopology B S hS P.pt.val)) :
    @DiscreteTopology (Stack.points B S hS Q.pt.val.val Q.pt.val.property)
      (Stack.pointTopology B S hS Q.pt.val) :=
  Stack.discreteTopology_points_congr B S hS P.underlying Q.underlying
    (Stack.isTwoFibreProduct_underlying_algebraicStacks B S hS P hP)
    (Stack.isTwoFibreProduct_underlying_algebraicStacks B S hS Q hQ) h

/-- **Stacks 06UF, (2) ⟹ (3).** If `f` is quasi-DM and transfers local quasi-finiteness to the
projections of its algebraic-space base changes, then each of those base changes has a
surjective, flat, locally finitely presented and locally quasi-finite cover by an algebraic
space which is locally quasi-finite over the base.

This is
`...AlgebraicStacks.locallyQuasiFiniteCoverOnEverySpaceBaseChange_of_isQuasiDM_of_transfers`
with its hypothesis, the substantial direction of **Stacks 06MF**, discharged by
`AlgebraicGeometry.Stack.hasQuasiDMPresentation_of_isAbsolutelyQuasiDM`. -/
theorem locallyQuasiFiniteCoverOnEverySpaceBaseChange_of_isQuasiDM_of_transfers_unconditional
    (f : 𝒳 ⟶ 𝒴) (hf : IsQuasiDM B S hS f)
    (htr : TransfersLocalQuasiFinitenessOnSpaceBaseChanges B S hS f) :
    LocallyQuasiFiniteCoverOnEverySpaceBaseChange B S hS f :=
  locallyQuasiFiniteCoverOnEverySpaceBaseChange_of_isQuasiDM_of_transfers B S hS
    (fun 𝒵 h𝒵 => Stack.hasQuasiDMPresentation_of_isAbsolutelyQuasiDM.{u, w} B S hS
      (BigFppfSite.contains_terminal B) 𝒵 h𝒵) f hf htr

/-- **The field-valued fibres of `f` over a field-valued point of `𝒴` which lifts to the chart
are discrete.** Let `𝒰 ⟶ 𝒳 ×_𝒴 𝒱` be a cover as in clauses (3) and (4) of **Stacks 06UF** and
let `v : Spec(k) ⟶ 𝒱` be a 1-morphism whose composite with `𝒱 ⟶ 𝒴` is the given field-valued
point `y` of `𝒴`. Then the fibre of `f` over `y` has discrete space of points.

This is the whole of the source's argument for the third condition in (4) ⟹ (1) *after* its
reduction to a field-valued point of `𝒴` which lifts to `𝒱`: pasting the canonical squares
(**Stacks 02XD**) identifies `𝒳 ×_𝒴 Spec(k)` with `(𝒳 ×_𝒴 𝒱) ×_𝒱 Spec(k)` and then
`𝒰 ×_{𝒳 ×_𝒴 𝒱} ((𝒳 ×_𝒴 𝒱) ×_𝒱 Spec(k))` with `𝒰 ×_𝒱 Spec(k)`. The latter is locally
quasi-finite over `Spec(k)` by **Stacks 06UB**, hence has discrete space of points, and it maps
to `𝒳 ×_𝒴 Spec(k)` by a base change of the cover, which is surjective, flat and locally of
finite presentation and therefore open and surjective on points by **Stacks 06R7**.

What the source puts in front of this is the production of the lift, which for a general
field-valued point `y` of `𝒴` is
`discreteTopology_points_of_locallyQuasiFiniteCoverOnSomeFlatSpaceBaseChange` below. -/
theorem discreteTopology_points_twoFibreProduct_of_hasLocallyQuasiFiniteFlatSpaceCoverOver
    (f : 𝒳 ⟶ 𝒴) {𝒱 : Stack.AlgebraicStacks.{u, w} B S hS} (g : 𝒱 ⟶ 𝒴)
    (hcover : HasLocallyQuasiFiniteFlatSpaceCoverOver B S hS f g)
    (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (toBase : Spec (.of k) ⟶ S)
    (v : Stack.schemeStack.{u, w} B S hS (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)) ⟶ 𝒱)
    (y : Stack.schemeStack.{u, w} B S hS (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)) ⟶ 𝒴)
    (hy : v ≫ g = y) :
    @DiscreteTopology
      (Stack.points B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS f y).pt.val.val
        (Stack.twoFibreProductSquareAlgebraicStacks B S hS f y).pt.val.property)
      (Stack.pointTopology B S hS
        (Stack.twoFibreProductSquareAlgebraicStacks B S hS f y).pt.val) := by
  subst hy
  set M := Stack.twoFibreProductSquareAlgebraicStacks B S hS f g with hMdef
  obtain ⟨𝒰, h𝒰, cov, hpS, hpF, hpL, hpQ, hcomp⟩ := hcover
  set N := Stack.twoFibreProductSquareAlgebraicStacks B S hS M.snd v with hNdef
  set R := Stack.twoFibreProductSquareAlgebraicStacks B S hS N.fst cov with hRdef
  set Q := Stack.twoFibreProductSquareAlgebraicStacks B S hS v (cov ≫ M.snd) with hQdef
  have hMfp : Bicategory.IsTwoFibreProduct M :=
    Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f g
  have hNfp : Bicategory.IsTwoFibreProduct N :=
    Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS M.snd v
  have hRfp : Bicategory.IsTwoFibreProduct R :=
    Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS N.fst cov
  have hQfp : Bicategory.IsTwoFibreProduct Q :=
    Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS v (cov ≫ M.snd)
  -- `𝒰 ×_𝒱 Spec(k)` is locally quasi-finite over `Spec(k)`, hence has discrete space of points
  have hQdisc := discreteTopology_points_of_isLocallyQuasiFinite B S hS k hk
    toBase Q.fst (isLocallyQuasiFinite_baseChange B S hS (cov ≫ M.snd) v Q hQfp hcomp)
  -- pasting identifies it with `𝒰 ×_{𝒳 ×_𝒴 𝒱} ((𝒳 ×_𝒴 𝒱) ×_𝒱 Spec(k))`
  have hRdisc := discreteTopology_points_congr_of_isTwoFibreProduct B S hS Q (N.swap.paste R)
    hQfp (Bicategory.isTwoFibreProduct_paste (Bicategory.isTwoFibreProduct_swap hNfp) hRfp)
    hQdisc
  -- that is a base change of the cover, so it is open and surjective on points
  have hNdisc := @discreteTopology_of_surjective_isOpenMap _ _
    (Stack.pointTopology B S hS R.pt.val) (Stack.pointTopology B S hS N.pt.val) hRdisc _
    (Stack.isSurjective_of_isTwoFibreProduct B S hS R.swap
      (Bicategory.isTwoFibreProduct_swap hRfp) hpS)
    (isOpenMap_pointsMap B S hS R.fst
      (isFlat_baseChange B S hS cov N.fst R hRfp hpF)
      (isLocallyOfFinitePresentation_baseChange B S hS cov N.fst R hRfp hpL))
  -- and pasting identifies `(𝒳 ×_𝒴 𝒱) ×_𝒱 Spec(k)` with the fibre of `f`
  exact discreteTopology_points_congr_of_isTwoFibreProduct B S hS (M.paste N)
    (Stack.twoFibreProductSquareAlgebraicStacks B S hS f (v ≫ g))
    (Bicategory.isTwoFibreProduct_paste hMfp hNfp)
    (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f (v ≫ g)) hNdisc

/-- **Stacks 06UF, the local finite type conjunct of (4) ⟹ (1).** A locally quasi-finite flat
cover of `𝒳 ×_𝒴 𝒱` by an algebraic space over one algebraic space `𝒱` surjective, flat and
locally of finite presentation over `𝒴` makes `f` locally of finite type.

The composite `𝒰 ⟶ 𝒱` is locally quasi-finite, hence locally of finite type, and `𝒰` covers
`𝒳 ×_𝒴 𝒱` by a surjective flat 1-morphism locally of finite presentation, so the projection
`𝒳 ×_𝒴 𝒱 ⟶ 𝒱` is locally of finite type by **Stacks 06U8**; that projection is the base change
of `f` along `𝒱 ⟶ 𝒴`, so **Stacks 06U7** descends local finite type to `f`. -/
theorem isLocallyOfFiniteType_of_locallyQuasiFiniteCoverOnSomeFlatSpaceBaseChange (f : 𝒳 ⟶ 𝒴)
    (hf : LocallyQuasiFiniteCoverOnSomeFlatSpaceBaseChange B S hS f) :
    IsLocallyOfFiniteType B S hS f := by
  obtain ⟨𝒱, h𝒱, g, hgS, hgF, hgL, 𝒰, h𝒰, p, hpS, hpF, hpL, -, hcomp⟩ := hf
  have hprep : Stack.IsRepresentableByAlgebraicSpaces B S hS p.hom.hom :=
    Stack.isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).pt.property h𝒰 p.hom
  exact isLocallyOfFiniteType_of_baseChange B S hS f g hgS hgF hgL
    (isLocallyOfFiniteType_of_comp_of_fppf B S hS p
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).snd hcomp.2.1 hprep hpS hpF hpL)

/-! ### The field-valued fibres of the implication (4) ⟹ (1) -/

/-- **Every point of an algebraic stack over `S` is hit by a 1-morphism from the algebraic stack
of the spectrum of a field, presented as the third clause of Stacks 06PU presents one.** A point
of **Stacks 04XG** *is* an equivalence class of field-valued points of **Stacks 04XF**, and a
field-valued point already carries a 1-morphism out of the algebraic stack of its base
(**Stacks 0DTK**). What is done here is the change of base object: a field-valued point presents
its base as an object of the site *together with* an isomorphism of the underlying scheme onto
the spectrum of a field, whereas the third clause of **Stacks 06PU** quantifies over objects of
the shape `Over.mk ⟨toBase⟩` whose underlying scheme *is* that spectrum. Transporting the
object of the fibre along `AlgebraicGeometry.Stack.spectrumSiteObjectIso`, the identification of
the two as objects of the site, produces a field-valued point over an object of the second
shape. -/
theorem exists_fieldSpectrumStack_hom_of_nonempty_points
    (𝒵 : Stack.AlgebraicStacks.{u, w} B S hS)
    (hne : Nonempty (Stack.points B S hS 𝒵.val.val 𝒵.val.property)) :
    ∃ (k : Type u) (_ : Field k) (hk : B.Contains (Spec (.of k)))
      (toBase : Spec (.of k) ⟶ S),
      Nonempty (Stack.schemeStack.{u, w} B S hS
        (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)) ⟶ 𝒵) := by
  classical
  obtain ⟨x⟩ := hne
  let p : Stack.FieldValuedPoint B S hS 𝒵.val.val := Quotient.out x
  obtain ⟨z, φ, hφ⟩ :=
    𝒵.val.property.exists_lift (Stack.spectrumSiteObjectIso B S hS p).hom p.obj p.over
  let _ := hφ
  let p' : Stack.FieldValuedPoint B S hS 𝒵.val.val :=
    ⟨p.carrier, Stack.spectrumSiteObject B S hS p, Iso.refl _, z,
      IsHomLift.domain_eq 𝒵.val.val.p (Stack.spectrumSiteObjectIso B S hS p).hom φ⟩
  exact ⟨p.carrier, p.field, Stack.contains_spectrum_fieldValuedPoint B S hS p,
    Stack.spectrumStructureMorphism B S hS p,
    ⟨Stack.fieldValuedPointStackMorphism.{u, w} B S hS 𝒵 p'⟩⟩

/-- **Universal openness of morphisms of algebraic spaces over `S` is stable under base
change.** The chosen fibre product of Stacks 02X2 realises one base change of each cospan, where
universal openness is **Stacks 03Z3**; the property respects isomorphisms, so it holds on every
other realisation. -/
private theorem isStableUnderBaseChange_universallyOpenMorphismProperty :
    (Space.universallyOpenMorphismProperty B S hS).IsStableUnderBaseChange := by
  have _ : (Space.universallyOpenMorphismProperty B S hS).RespectsIso :=
    Stack.universallyOpenMorphismProperty_respectsIso B S hS
  refine MorphismProperty.IsStableUnderBaseChange.of_forall_exists_isPullback ?_
  intro X Y Z f g _ hg
  exact ⟨AlgebraicSpaces.fiberProduct B S hS f g,
    ObjectProperty.homMk (Limits.pullback.fst f.hom g.hom),
    ObjectProperty.homMk (Limits.pullback.snd f.hom g.hom),
    AlgebraicSpaces.isPullback_fiberProduct B S hS f g,
    Space.universallyOpen_pullback B S hS Y.property Z.property X.property g.hom f.hom hg⟩

/-- **A 1-morphism from the algebraic stack of an object of the site to the algebraic stack of the
spectrum of a field is universally open in the sense of Stacks 04XB.** Source and target are both
represented by algebraic spaces, so the relative property of **Stacks 03YK** is the property of
the induced morphism of representing presheaves; universal openness is stable under base change
and local on the target, so that bridge applies to it, and the induced morphism is a morphism of
algebraic spaces to the spectrum of a field, hence universally open by **Stacks 06DN**. -/
@[sga "4 VIII 9.4.4" "special case"]
theorem universallyOpen_to_fieldSpectrumStack (F : Stack.FieldSpectrum B S hS)
    (V : BigFppfOver B S hS)
    (e : Stack.schemeStack.{u, w} B S hS V ⟶ Stack.schemeStack.{u, w} B S hS F.base) :
    Stack.UniversallyOpen B S hS e.hom := by
  have _ := isStableUnderBaseChange_universallyOpenMorphismProperty B S hS
  have _ : (Space.universallyOpenMorphismProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    MorphismProperty.IsLocalAtTarget.of_le
      (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  have hrep : Stack.IsRepresentableByAlgebraicSpaces B S hS e.hom.hom :=
    Stack.isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS
      (Stack.schemeStack.{u, w} B S hS F.base).property
      (Stack.isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS V) e.hom
  exact (Stack.hasRelativeProperty_iff_prop_representingMap B S hS
    (Space.universallyOpenMorphismProperty B S hS) e.hom hrep
    (yoneda.obj V) (yoneda.obj F.base)
    (isAlgebraicSpace_yoneda B S hS V) (isAlgebraicSpace_yoneda B S hS F.base)
    (PresheafOfCategories.sliceElementsEquivalenceOver V)
    (PresheafOfCategories.sliceElementsEquivalenceOver F.base)).2
    (Space.universallyOpen_to_field B S hS (isAlgebraicSpace_yoneda B S hS V) F.isSpec _)

/-- **Stacks 06UF, the field-valued-fibre conjunct of (4) ⟹ (1).** A locally quasi-finite flat
cover of `𝒳 ×_𝒴 𝒱` by an algebraic space over one algebraic space `𝒱` surjective, flat and
locally of finite presentation over `𝒴` makes the fibre of `f` over *every* field-valued point of
`𝒴` have discrete space of points.

This is the source's reduction of the third condition of **Stacks 06PU** to a field-valued point
which lifts to the chart. The chart being surjective, the fibre `𝒱 ×_𝒴 Spec(k)` has a point, and a
point of an algebraic stack is an equivalence class of field-valued points, so some field
extension `k'/k` carries `v : Spec(k') ⟶ 𝒱` and `e : Spec(k') ⟶ Spec(k)` with `v ≫ g`
2-isomorphic to `e ≫ y`. Over `v` the fibre is discrete, which is
`discreteTopology_points_twoFibreProduct_of_hasLocallyQuasiFiniteFlatSpaceCoverOver`; changing the
cospan leg by that 2-isomorphism (`CategoryTheory.Bicategory.isTwoFibreProduct_reindexSnd`) and
pasting (**Stacks 02XD**) identify the fibre over `v ≫ g` with `(𝒳 ×_𝒴 Spec(k)) ×_{Spec(k)}
Spec(k')`, and that maps onto `𝒳 ×_𝒴 Spec(k)` by a base change of `e`.

`e` is surjective by `AlgebraicGeometry.Stack.isSurjective_of_fieldSpectrum`, the spectrum of a
field having exactly one point, and it is universally open because its target is the algebraic
stack of the spectrum of a field (**Stacks 06DN** through
`universallyOpen_to_fieldSpectrumStack`), so its base change is open on points by **Stacks 06U1**.
No finiteness of `k'/k` is needed: the source gets openness from flatness and local finite
presentation of a *finite* extension, and universal openness over a field spectrum gives it for
an arbitrary one. -/
theorem discreteTopology_points_of_locallyQuasiFiniteCoverOnSomeFlatSpaceBaseChange (f : 𝒳 ⟶ 𝒴)
    (hf : LocallyQuasiFiniteCoverOnSomeFlatSpaceBaseChange B S hS f)
    (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (toBase : Spec (.of k) ⟶ S)
    (y : Stack.schemeStack.{u, w} B S hS (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)) ⟶ 𝒴) :
    @DiscreteTopology
      (Stack.points B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS f y).pt.val.val
        (Stack.twoFibreProductSquareAlgebraicStacks B S hS f y).pt.val.property)
      (Stack.pointTopology B S hS
        (Stack.twoFibreProductSquareAlgebraicStacks B S hS f y).pt.val) := by
  classical
  obtain ⟨𝒱, h𝒱, g, hgS, hgF, hgL, hcover⟩ := hf
  let K : BigFppfOver B S hS := Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)
  let Fk : Stack.FieldSpectrum B S hS := ⟨k, K, Iso.refl _⟩
  -- the chart is surjective, so the fibre `𝒱 ×_𝒴 Spec(k)` has a point
  let L := Stack.twoFibreProductSquareAlgebraicStacks B S hS g y
  have hLfp : Bicategory.IsTwoFibreProduct L :=
    Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g y
  obtain ⟨x⟩ := Stack.nonempty_points_fieldSpectrumStack.{u, w} B S hS Fk
  obtain ⟨q, -⟩ := Stack.isSurjective_of_isTwoFibreProduct B S hS L hLfp hgS x
  -- a point is an equivalence class of field-valued points, so it lifts to a field extension
  obtain ⟨k', instk', hk', toBase', ⟨a⟩⟩ :=
    exists_fieldSpectrumStack_hom_of_nonempty_points B S hS L.pt ⟨q⟩
  let _ := instk'
  let K' : BigFppfOver B S hS := Over.mk (⟨toBase'⟩ : B.obj hk' ⟶ B.obj hS)
  let Fk' : Stack.FieldSpectrum B S hS := ⟨k', K', Iso.refl _⟩
  let v : Stack.schemeStack.{u, w} B S hS K' ⟶ 𝒱 := a ≫ L.fst
  let e : Stack.schemeStack.{u, w} B S hS K' ⟶ Stack.schemeStack.{u, w} B S hS K := a ≫ L.snd
  let δ : v ≫ g ≅ e ≫ y :=
    Bicategory.associator a L.fst g ≪≫ Bicategory.whiskerLeftIso a L.iso ≪≫
      (Bicategory.associator a L.snd y).symm
  -- the fibre over the lifted point is discrete
  have h1 := discreteTopology_points_twoFibreProduct_of_hasLocallyQuasiFiniteFlatSpaceCoverOver
    B S hS f g hcover k' hk' toBase' v (v ≫ g) rfl
  -- reindexing and pasting identify it with `(𝒳 ×_𝒴 Spec k) ×_{Spec k} Spec k'`
  let P := Stack.twoFibreProductSquareAlgebraicStacks B S hS f (v ≫ g)
  have hPfp : Bicategory.IsTwoFibreProduct P :=
    Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f (v ≫ g)
  let M := Stack.twoFibreProductSquareAlgebraicStacks B S hS f y
  have hMfp : Bicategory.IsTwoFibreProduct M :=
    Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f y
  let Q := Stack.twoFibreProductSquareAlgebraicStacks B S hS M.snd e
  have hQfp : Bicategory.IsTwoFibreProduct Q :=
    Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS M.snd e
  have h2 := discreteTopology_points_congr_of_isTwoFibreProduct B S hS (P.reindexSnd δ)
    (M.paste Q) (Bicategory.isTwoFibreProduct_reindexSnd δ hPfp)
    (Bicategory.isTwoFibreProduct_paste hMfp hQfp) h1
  -- and `Q.fst` is a base change of `e`, hence surjective and open on points
  have herep : Stack.IsRepresentableByAlgebraicSpaces B S hS e.hom.hom :=
    Stack.isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS
      (Stack.schemeStack.{u, w} B S hS K).property
      (Stack.isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS K') e.hom
  exact @discreteTopology_of_surjective_isOpenMap _ _
    (Stack.pointTopology B S hS Q.pt.val) (Stack.pointTopology B S hS M.pt.val) h2 _
    (Stack.isSurjective_of_isTwoFibreProduct B S hS Q.swap
      (Bicategory.isTwoFibreProduct_swap hQfp)
      (Stack.isSurjective_of_fieldSpectrum.{u, w} B S hS Fk' Fk e))
    (Stack.isOpenMap_pointsMap_fst_of_universallyOpen B S hS e herep
      (universallyOpen_to_fieldSpectrumStack.{u, w} B S hS Fk K' e) M.pt M.snd)

/-! ### The four-way equivalence -/

/-- **Stacks 06UF, (4) ⟹ (1).** A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` admitting
one algebraic space `𝒱` surjective, flat and locally of finite presentation over `𝒴` whose base
change `𝒳 ×_𝒴 𝒱` has a surjective, flat, locally finitely presented and locally quasi-finite
cover by an algebraic space locally quasi-finite over `𝒱` is locally quasi-finite.

The three conjuncts of **Stacks 06PU** are the three preceding theorems. -/
theorem isLocallyQuasiFinite_of_locallyQuasiFiniteCoverOnSomeFlatSpaceBaseChange (f : 𝒳 ⟶ 𝒴)
    (hf : LocallyQuasiFiniteCoverOnSomeFlatSpaceBaseChange B S hS f) :
    IsLocallyQuasiFinite B S hS f :=
  ⟨(isQuasiDMWithRepresentableDiagonal_iff_isQuasiDM B S hS f).2
      (isQuasiDM_of_locallyQuasiFiniteCoverOnSomeFlatSpaceBaseChange B S hS f hf),
    isLocallyOfFiniteType_of_locallyQuasiFiniteCoverOnSomeFlatSpaceBaseChange B S hS f hf,
    fun k _ hk toBase y =>
      discreteTopology_points_of_locallyQuasiFiniteCoverOnSomeFlatSpaceBaseChange
        B S hS f hf k hk toBase y⟩

/-- **Stacks 06UF.** For a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` the following are
equivalent:

1. `f` is locally quasi-finite (**Stacks 06PU**);
2. `f` is quasi-DM (**Stacks 04YW**) and for every algebraic space `𝒱` over `𝒴` every locally
   quasi-finite 1-morphism `𝒰 ⟶ 𝒳 ×_𝒴 𝒱` out of an algebraic space has locally quasi-finite
   composite `𝒰 ⟶ 𝒱`;
3. for every algebraic space `𝒱` over `𝒴` there is a surjective, flat, locally finitely presented
   and locally quasi-finite 1-morphism `𝒰 ⟶ 𝒳 ×_𝒴 𝒱` out of an algebraic space whose composite
   `𝒰 ⟶ 𝒱` is locally quasi-finite;
4. there are algebraic spaces `𝒰` and `𝒱`, a surjective, flat and locally finitely presented
   1-morphism `𝒱 ⟶ 𝒴`, and a surjective, flat, locally finitely presented and locally
   quasi-finite 1-morphism `𝒰 ⟶ 𝒳 ×_𝒴 𝒱` whose composite `𝒰 ⟶ 𝒱` is locally quasi-finite. -/
@[stacks 06UF]
theorem isLocallyQuasiFinite_tfae (f : 𝒳 ⟶ 𝒴) :
    List.TFAE
      [IsLocallyQuasiFinite B S hS f,
        IsQuasiDM B S hS f ∧ TransfersLocalQuasiFinitenessOnSpaceBaseChanges B S hS f,
        LocallyQuasiFiniteCoverOnEverySpaceBaseChange B S hS f,
        LocallyQuasiFiniteCoverOnSomeFlatSpaceBaseChange B S hS f] := by
  tfae_have 1 → 2 := isQuasiDM_and_transfersLocalQuasiFiniteness_of_isLocallyQuasiFinite B S hS f
  tfae_have 2 → 3 := fun h =>
    locallyQuasiFiniteCoverOnEverySpaceBaseChange_of_isQuasiDM_of_transfers_unconditional B S hS f
      h.1 h.2
  tfae_have 3 → 4 :=
    locallyQuasiFiniteCoverOnSomeFlatSpaceBaseChange_of_onEverySpaceBaseChange B S hS f
  tfae_have 4 → 1 :=
    isLocallyQuasiFinite_of_locallyQuasiFiniteCoverOnSomeFlatSpaceBaseChange B S hS f
  tfae_finish

end AlgebraicGeometry.Stack.AlgebraicStacks

end
