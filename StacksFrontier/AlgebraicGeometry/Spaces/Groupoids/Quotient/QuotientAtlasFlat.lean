module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFpqcLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackProjectionRelativeProperty

/-!
# The atlas of a quotient stack is flat, locally of finite presentation and surjective

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `B` over a
scheme `S` of a big fppf site, and let `π : S_U ⟶ [U/R]` be the canonical projection of
Stacks 044R. **Stacks 06FH** says that if `s` and `t` are flat and locally of finite presentation
then `π` is flat, locally of finite presentation and surjective, in the relative sense of
Stacks 03YK.

## Main definitions

* `AlgebraicGeometry.Stack.QuotientAtlas.Presentation`: the data **Stacks 04M9** provides for a
  groupoid in algebraic spaces — a 2-fibre product of `π` with itself whose first leg is, up to
  equivalence, a 1-morphism of categories fibred in groupoids represented by the arrow space and
  the object space, with induced morphism of representing presheaves the source map `s`.

## Main results

* `AlgebraicGeometry.Stack.QuotientAtlas.isSurjective_source`: the source map of a groupoid in
  algebraic spaces is surjective on points.
* `AlgebraicGeometry.Stack.QuotientAtlas.hasRelativeProperty`: every property of morphisms of
  algebraic spaces stable under base change and local at the target for the fppf topology passes
  from `s` to `π`.
* `AlgebraicGeometry.Stack.QuotientAtlas.isFlat`,
  `AlgebraicGeometry.Stack.QuotientAtlas.isLocallyOfFinitePresentation` and
  `AlgebraicGeometry.Stack.QuotientAtlas.isSurjective`: the three conclusions of **Stacks 06FH**.

## Implementation notes

The reduction of the three conclusions to a property of one morphism of algebraic spaces is
`AlgebraicGeometry.Stack.hasRelativeProperty_quotientStackProjectionHom_of_representingMap`: the
local essential surjectivity of `π` that Stacks 045D asks for holds with no hypothesis on the
groupoid, descent along `π` reduces each conclusion to the first leg of a 2-fibre product of `π`
with itself, and the Stacks 04XB bridge reads a relative property of a 1-morphism of represented
categories off the induced morphism of representing presheaves. What that reduction does not
supply is the identification of the 2-fibre product, which is Stacks 04M9; `Presentation` carries
it as data.

**Where Stacks 04M9 comes from.** The library's Stacks 04M9,
`AlgebraicGeometry.Stack.quotientStack_twoFibreProduct`, is terminality in the 2-category of
*stacks* in groupoids over the big fppf site, whereas the descent result above consumes
terminality in the 2-category of *categories* fibred in groupoids, and the first does not formally
give the second. `AlgebraicGeometry.Stack.QuotientAtlas.presentation`, in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/Quotient/QuotientAtlasPresentation.lean`, builds
a `Presentation` from that Stacks 04M9 and the representability of `π` alone. The statements
below take a `Presentation` as an argument, so
that what they assert is that **Stacks 04M9 together with the hypotheses of Stacks 06FH on `s` is
sufficient**, every other input being discharged.

**Representability of `π`** is likewise a field of `Presentation`. Stacks 06FH takes it from
Algebraic Stacks, Lemma 94.17.1; the form in this library,
`AlgebraicGeometry.Stack.representable_quotientStackProjection_of_hasRepresentableDiagonal`, is
hypothesis-borne on `[U/R]` having representable diagonal, which is not a hypothesis of
Stacks 06FH.

**Only the source map is constrained.** Groupoid inversion identifies `s` and `t`, so the
hypotheses of Stacks 06FH on `t` are not used; and the surjectivity conclusion needs no hypothesis
at all, because the identity arrow at a point of the object space is a preimage of it under `s` —
which is `AlgebraicGeometry.Stack.QuotientAtlas.isSurjective_source`, the formal counterpart of
the source's remark that `s` has the groupoid identity as a section.

The three morphism properties are spelled exactly as the locality and base-change results state
them, which is what instance search needs; the two instances of flatness are recorded here
because the corresponding results are theorems rather than instances in the tree, while a
relative property needs them in scope already when its statement is elaborated. Base-change
stability of local finite presentation is already an instance where it is proved, in
`StacksFrontier/AlgebraicGeometry/Spaces/CoveringComparison.lean`.

## References

* [Stacks Project, Tag 03ME](https://stacks.math.columbia.edu/tag/03ME)
* [Stacks Project, Tag 03MO](https://stacks.math.columbia.edu/tag/03MO)
* [Stacks Project, Tag 03XR](https://stacks.math.columbia.edu/tag/03XR)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 041Q](https://stacks.math.columbia.edu/tag/041Q)
* [Stacks Project, Tag 041T](https://stacks.math.columbia.edu/tag/041T)
* [Stacks Project, Tag 041W](https://stacks.math.columbia.edu/tag/041W)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 045D](https://stacks.math.columbia.edu/tag/045D)
* [Stacks Project, Tag 04M9](https://stacks.math.columbia.edu/tag/04M9)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 06FH](https://stacks.math.columbia.edu/tag/06FH)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack.QuotientAtlas

universe u t

section Properties

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)

/-- **Stacks 041W** at the fppf precoverage: flatness of morphisms of algebraic spaces over `S`
is local at the target for the fppf topology, the form in which the relative properties of
Stacks 03YK ask for it. -/
instance flatIsLocalAtTargetFppf :
    MorphismProperty.IsLocalAtTarget
      (fun ⦃X Y : AlgebraicSpaces C S hS⦄ (f : X ⟶ Y) => Space.IsFlat C S hS f.hom)
      (Space.Topology.fppf.precoverage.{u, t} C S hS) :=
  .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage C S hS)

/- **Stacks 03MO** as an instance: flatness of morphisms of algebraic spaces over `S` is stable
under base change. It is a theorem in the tree, and the relative properties of Stacks 03YK ask
for it as an instance already when their statements are elaborated. -/
attribute [instance] Space.isFlat_isStableUnderBaseChange

end Properties

section Surjectivity

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

/-- A morphism of presheaves on the big fppf site of `S` is surjective on points as soon as every
field-valued point of the target is the image of a section of the source over the same test
object. -/
theorem isSurjective_of_sectionwise_lift {X Y : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (lift : ∀ p : Space.FieldValuedPoint C S hS Y,
      ∃ a : X.obj (op p.siteObject), f.app (op p.siteObject) a = p.value) :
    Space.IsSurjective C S hS f := by
  intro x
  refine Quot.inductionOn x ?_
  intro p
  obtain ⟨a, ha⟩ := lift p
  let q : Space.FieldValuedPoint C S hS X :=
    { carrier := p.carrier
      field := p.field
      contained := p.contained
      toBase := p.toBase
      value := a }
  refine ⟨q.class C S hS X, ?_⟩
  change (Space.FieldValuedPoint.map C S hS X f q).class C S hS Y = p.class C S hS Y
  apply Quot.sound
  refine ⟨p, ⟨𝟙 p.siteObject, ?_⟩, Space.FieldValuedPoint.dominates_refl C S hS Y p⟩
  change Y.map (𝟙 p.siteObject).op (f.app (op p.siteObject) a) = p.value
  simpa only [op_id, Functor.map_id_apply] using ha

variable {B : AlgebraicSpaces C S hS}

/-- The identity arrow at a field-valued point of the object space of a groupoid in algebraic
spaces has that point as both its source and its target. -/
private theorem exists_identity_arrow (G : GroupoidInAlgebraicSpaces C S hS B)
    (p : Space.FieldValuedPoint C S hS G.objects.obj) :
    ∃ a : G.arrows.obj.obj (op p.siteObject), G.source.hom.app (op p.siteObject) a = p.value ∧
      G.target.hom.app (op p.siteObject) a = p.value := by
  let F := G.toGroupoidInFunctors
  let : Groupoid (F.Evaluation (op p.siteObject)) := F.evaluationGroupoid (op p.siteObject)
  let x₀ : F.Evaluation (op p.siteObject) := p.value
  exact ⟨(F.evaluationArrowEquiv (op p.siteObject) x₀ x₀ (𝟙 x₀)).1,
    (F.evaluationArrowEquiv (op p.siteObject) x₀ x₀ (𝟙 x₀)).2.1,
    (F.evaluationArrowEquiv (op p.siteObject) x₀ x₀ (𝟙 x₀)).2.2⟩

/-- **The source map of a groupoid in algebraic spaces is surjective** (Stacks 03ME at `s`):
every point of the object space is the source of the identity arrow at it. This is the formal
counterpart of the groupoid identity `e : U ⟶ R` being a section of `s`. -/
theorem isSurjective_source (G : GroupoidInAlgebraicSpaces C S hS B) :
    Space.IsSurjective C S hS G.source.hom := by
  refine isSurjective_of_sectionwise_lift G.source.hom fun p => ?_
  exact (exists_identity_arrow G p).imp fun _ h => h.1

/-- **The target map of a groupoid in algebraic spaces is surjective** (Stacks 03ME at `t`):
every point of the object space is the target of the identity arrow at it. -/
theorem isSurjective_target (G : GroupoidInAlgebraicSpaces C S hS B) :
    Space.IsSurjective C S hS G.target.hom := by
  refine isSurjective_of_sectionwise_lift G.target.hom fun p => ?_
  exact (exists_identity_arrow G p).imp fun _ h => h.2

end Surjectivity

section Presentation

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- **The data of Stacks 04M9 for the canonical projection `π : S_U ⟶ [U/R]` of Stacks 044R**,
together with the representability of `π` that Stacks 06FH takes from Algebraic Stacks,
Lemma 94.17.1.

A `Presentation` of a groupoid `G = (U, R, s, t, c)` in algebraic spaces consists of a 2-fibre
product of `π` with itself whose first leg is carried by a pair of equivalences onto a
1-morphism of categories fibred in groupoids represented by the arrow space `R` and the object
space `U`, and whose induced morphism of representing presheaves is the source map `s`. -/
structure Presentation (G : GroupoidInAlgebraicSpaces C S hS B) where
  /-- The projection `π` is representable by algebraic spaces. -/
  representable : IsRepresentableByAlgebraicSpaces C S hS (quotientStackProjectionHom G).hom
  /-- A 2-commutative square of `π` with itself. -/
  square : Bicategory.TwoCommSq (quotientStackProjectionHom G) (quotientStackProjectionHom G)
  /-- It is a 2-fibre product. -/
  isTwoFibreProduct : Bicategory.IsTwoFibreProduct square
  /-- Its first leg is representable by algebraic spaces. -/
  fstRepresentable : IsRepresentableByAlgebraicSpaces C S hS square.fst.hom
  /-- A category fibred in groupoids representable by the arrow space. -/
  arrowStack : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver C S hS)
  /-- A category fibred in groupoids representable by the object space. -/
  objectStack : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver C S hS)
  /-- The 1-morphism between them that the first leg is carried onto. -/
  leg : arrowStack ⟶ objectStack
  /-- It is representable by algebraic spaces. -/
  legRepresentable : IsRepresentableByAlgebraicSpaces C S hS leg.hom
  /-- The equivalence identifying the apex of the square with the arrow space. -/
  toArrowStack : square.pt.val ⥤ᵇ arrowStack.val
  /-- The equivalence identifying the source of `π` with the object space. -/
  toObjectStack : (liftedObjectSpace G).val ⥤ᵇ objectStack.val
  /-- The first is an equivalence of the underlying categories. -/
  isEquivalence_toArrowStack : Functor.IsEquivalence toArrowStack.toFunctor
  /-- The second is an equivalence of the underlying categories. -/
  isEquivalence_toObjectStack : Functor.IsEquivalence toObjectStack.toFunctor
  /-- The two equivalences carry the first leg onto `leg`. -/
  comm : BasedFunctor.comp toArrowStack leg.hom ≅ BasedFunctor.comp square.fst.hom toObjectStack
  /-- `arrowStack` is represented by the arrow space of the groupoid. -/
  arrowsEquivalence : StacksRepresentableCFG.EquivalenceOver
    arrowStack.val.p (presheafOfCategories (G.arrows.obj ⋙ typeToCat)).p
  /-- `objectStack` is represented by the object space of the groupoid. -/
  objectsEquivalence : StacksRepresentableCFG.EquivalenceOver
    objectStack.val.p (presheafOfCategories (G.objects.obj ⋙ typeToCat)).p
  /-- The morphism of representing presheaves induced by `leg` is the source map. -/
  leg_eq : (ObjectProperty.homMk (representingMap C S hS arrowStack objectStack
      G.arrows.obj G.objects.obj arrowsEquivalence objectsEquivalence leg) :
    G.arrows ⟶ G.objects) = G.source

/-- **Every relative property of the source map passes to the quotient-stack projection.** Let
`G = (U, R, s, t, c)` be a groupoid in algebraic spaces over `S` presented as in Stacks 04M9, and
let `P` be a property of morphisms of algebraic spaces over `S` stable under base change and
local at the target for the fppf topology. If `s` has `P`, then the canonical projection
`π : S_U ⟶ [U/R]` of Stacks 044R has `P` in the relative sense of Stacks 03YK.

This is `AlgebraicGeometry.Stack.hasRelativeProperty_quotientStackProjectionHom_of_representingMap`
with the Stacks 04M9 data read off the presentation and the hypothesis on the induced morphism of
representing presheaves rewritten into one on `s`. -/
theorem hasRelativeProperty {G : GroupoidInAlgebraicSpaces C S hS B} (A : Presentation G)
    (P : MorphismProperty (AlgebraicSpaces C S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, max u t} C S hS)]
    (hP : P G.source) :
    HasRelativeProperty C S hS P (quotientStackProjectionHom G) A.representable := by
  have h := A.isEquivalence_toArrowStack
  have h' := A.isEquivalence_toObjectStack
  refine hasRelativeProperty_quotientStackProjectionHom_of_representingMap.{u, t} C S hS G P
    A.representable A.square A.isTwoFibreProduct A.fstRepresentable A.leg A.legRepresentable
    A.toArrowStack A.toObjectStack A.comm G.arrows.obj G.objects.obj G.arrows.property
    G.objects.property A.arrowsEquivalence A.objectsEquivalence ?_
  rw [A.leg_eq]
  exact hP

/-- **Stacks 06FH, flatness.** Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over
`S` presented as in Stacks 04M9. If the source map `s` is flat, then the canonical projection
`π : S_U ⟶ [U/R]` of Stacks 044R is flat in the relative sense of Stacks 03YK. -/
@[stacks 06FH "flatness; Stacks 04M9 and the representability of the projection carried as the \
hypothesis `Presentation`, and only the source map constrained"]
theorem isFlat {G : GroupoidInAlgebraicSpaces C S hS B} (A : Presentation G)
    (hs : Space.IsFlat C S hS G.source.hom) :
    HasRelativeProperty.{u, u + 1, u + 1, max u t} C S hS
      (fun ⦃X Y : AlgebraicSpaces C S hS⦄ (f : X ⟶ Y) => Space.IsFlat C S hS f.hom)
      (quotientStackProjectionHom G) A.representable :=
  hasRelativeProperty.{u, t} A _ hs

/-- **Stacks 06FH, local finite presentation.** Let `G = (U, R, s, t, c)` be a groupoid in
algebraic spaces over `S` presented as in Stacks 04M9. If the source map `s` is locally of finite
presentation, then the canonical projection `π : S_U ⟶ [U/R]` of Stacks 044R is locally of finite
presentation in the relative sense of Stacks 03YK. -/
@[stacks 06FH "locally of finite presentation; Stacks 04M9 and the representability of the \
projection carried as the hypothesis `Presentation`, and only the source map constrained"]
theorem isLocallyOfFinitePresentation {G : GroupoidInAlgebraicSpaces C S hS B}
    (A : Presentation G) (hs : Space.IsLocallyOfFinitePresentation C S hS G.source.hom) :
    HasRelativeProperty.{u, u + 1, u + 1, max u t} C S hS
      (fun ⦃X Y : AlgebraicSpaces C S hS⦄ (f : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation C S hS f.hom)
      (quotientStackProjectionHom G) A.representable :=
  hasRelativeProperty.{u, t} A _ hs

/-- **Stacks 06FH, surjectivity.** Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces
over `S` presented as in Stacks 04M9. The canonical projection `π : S_U ⟶ [U/R]` of Stacks 044R
is surjective in the relative sense of Stacks 03YK, with no hypothesis on the groupoid: the
source map is surjective because the identity arrow at a point of the object space is a preimage
of it. -/
@[stacks 06FH "surjectivity; Stacks 04M9 and the representability of the projection carried as \
the hypothesis `Presentation`, and no hypothesis on the groupoid"]
theorem isSurjective {G : GroupoidInAlgebraicSpaces C S hS B} (A : Presentation G) :
    HasRelativeProperty.{u, u + 1, u + 1, max u t} C S hS
      (Space.surjectiveMorphismProperty C S hS)
      (quotientStackProjectionHom G) A.representable :=
  hasRelativeProperty.{u, t} A _ (isSurjective_source G)

end Presentation

end AlgebraicGeometry.Stack.QuotientAtlas

end
