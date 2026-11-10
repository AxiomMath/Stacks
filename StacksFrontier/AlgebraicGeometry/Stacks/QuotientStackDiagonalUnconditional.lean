module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.GroupoidPresentationQuotientAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientAtlasArrowSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientStackAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.TrivialActionAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Unconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# The bootstrap theorem discharges Stacks 04TB, and with it the 04TB half of Stacks 06FI

`StacksFrontier/AlgebraicGeometry/Spaces/Representable/Bootstrap/Unconditional.lean` proves part (3)
of **Stacks 04S6** in the spellings the Spaces and the Stacks chapters of this library carry it
in, among them `AlgebraicGeometry.Stack.bootstrap04S6`, the spelling Stacks 04TB consumes.

That makes **Stacks 04TB** unconditional, hence also **Stacks 04WZ** and the representability of
the projection of Stacks 044R. Together with **Stacks 06FH**, which is proved with nothing carried
in `StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/Quotient/QuotientAtlasArrowSquare.lean`, it
removes the Stacks 04TB and Stacks 06FH hypotheses from **Stacks 06FI** and from its consumers
**Stacks 06PJ** and **Stacks 06PL**. What is left standing in those three is Artin's theorem
**Stacks 06DC** alone.

## Main results

* `AlgebraicGeometry.Stack.lemma04TB`: **Stacks 04TB** for every groupoid in algebraic spaces
  over every algebraic space of the site, with nothing carried.
* `AlgebraicGeometry.Stack.lemma06FH`: **Stacks 06FH** in the form
  `AlgebraicGeometry.Stack.Lemma06FH` asks for it, with nothing carried.
* `AlgebraicGeometry.Stack.hasRepresentableDiagonal_quotientStack_unconditional` and
  `AlgebraicGeometry.Stack.representable_quotientStackProjectionHom_unconditional`:
  **Stacks 04WZ** and the representability of the projection of Stacks 044R, with nothing
  carried.
* `AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_of_theorem06DC` and
  `AlgebraicGeometry.Stack.forall_isAlgebraicStack_quotientStack_of_theorem06DC`:
  **Stacks 06FI**, for a single groupoid and quantified over the groupoids on a fixed base,
  carrying Artin's theorem Stacks 06DC alone.
* `AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_of_restrictionAlong_of_theorem06DC`
  and
  `AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_trivialAction_of_theorem06DC`: the
  implications towards algebraicity of **Stacks 06PJ** and **Stacks 06PL**, carrying Artin's
  theorem alone.

## Implementation notes

No declaration here registers Stacks 06FI. The two statements of it carrying Artin's theorem,
`isAlgebraicStack_quotientStack_of_theorem06DC` and
`forall_isAlgebraicStack_quotientStack_of_theorem06DC`, are kept for the consumers that
instantiate them; the unconditional statement, with Artin's theorem proved, is
`AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_of_flat` in
`StacksFrontier/AlgebraicGeometry/Stacks/FlatQuotientStackAlgebraic.lean`, which carries the
registration.

The four tags whose hypotheses are narrowed here — 04TB, 04WZ, 06PJ and 06PL — are
registered where they are stated, and the declarations narrowing them record no further part of
any of them: each is an existing statement with one of its hypotheses supplied.
The converse implications of Stacks 06PJ and Stacks 06PL are untouched here; they are not
blocked by Stacks 06FI at all. As the module docstring of the module
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.GroupoidPresentationQuotientAlgebraic`
records, they are proved, carrying nothing, as
`AlgebraicGeometry.Stack.exists_restrictionAlong_of_isAlgebraicStack` and
`AlgebraicGeometry.Stack.isFlat_and_isLocallyOfFinitePresentation_of_isAlgebraicStack_trivialAction`

## References

* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 04TB](https://stacks.math.columbia.edu/tag/04TB)
* [Stacks Project, Tag 04WZ](https://stacks.math.columbia.edu/tag/04WZ)
* [Stacks Project, Tag 06DC](https://stacks.math.columbia.edu/tag/06DC)
* [Stacks Project, Tag 06FI](https://stacks.math.columbia.edu/tag/06FI)
* [Stacks Project, Tag 06PJ](https://stacks.math.columbia.edu/tag/06PJ)
* [Stacks Project, Tag 06PL](https://stacks.math.columbia.edu/tag/06PL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Stack

universe u w

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

/-- **Stacks 04TB, with nothing carried.** Every isomorphism sheaf of a fibre of the quotient
stack of a groupoid in algebraic spaces over an algebraic space of the site is an algebraic
space over the scheme the fibre sits over.

This is `AlgebraicGeometry.Stack.isAlgebraicSpace_isomPresheaf`, which on the base carries no
Stacks 04S6 hypothesis any more. -/
theorem lemma04TB (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S) :
    Lemma04TB C S hS :=
  fun A G T x y => isAlgebraicSpace_isomPresheaf C S hS A G T x y

/-- **Stacks 06FH, with nothing carried**, in the form `AlgebraicGeometry.Stack.Lemma06FH` that
`AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack` takes it in: for every groupoid in
algebraic spaces whose source and target are flat and locally of finite presentation, the
canonical projection of Stacks 044R is surjective, flat and locally of finite presentation.

This is `AlgebraicGeometry.Stack.QuotientAtlas.surjective_flat_lfp_quotientStackProjectionHom`. -/
theorem lemma06FH (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S) :
    Lemma06FH C S hS :=
  fun _ G hsflat htflat hslfp htlfp hπ =>
    QuotientAtlas.surjective_flat_lfp_quotientStackProjectionHom G hsflat htflat hslfp htlfp hπ

/-- **Stacks 04WZ, with nothing carried.** The diagonal of the quotient stack of a groupoid in
algebraic spaces over a scheme of a big fppf site is representable by algebraic spaces. -/
theorem hasRepresentableDiagonal_quotientStack_unconditional {A : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS A) :
    HasRepresentableDiagonal C S hS
      (CatFiberedInGroupoids.mk (quotientStack G) (isFiberedInGroupoids_quotientStack G)) :=
  hasRepresentableDiagonal_quotientStack G

/-- **The canonical projection `S_U ⟶ [U/R]` of Stacks 044R is representable by algebraic
spaces**, with nothing carried. -/
theorem representable_quotientStackProjectionHom_unconditional {A : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS A) :
    IsRepresentableByAlgebraicSpaces C S hS (quotientStackProjectionHom G).hom :=
  representable_quotientStackProjectionHom G

/-- **Stacks 06FI, carrying Artin's theorem alone.** Let `G = (U, R, s, t, c)` be a groupoid in
algebraic spaces over an algebraic space `A` over a scheme `S` of a big fppf site. If the source
and the target of `G` are flat and locally of finite presentation, then the quotient stack
`[U/R]` is an algebraic stack over `S`, given Artin's theorem Stacks 06DC.

This is `AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack` with its Stacks 06FH and
Stacks 04TB hypotheses `h06FH` and `h04TB` supplied by `AlgebraicGeometry.Stack.lemma06FH` and
`AlgebraicGeometry.Stack.lemma04TB`. -/
theorem isAlgebraicStack_quotientStack_of_theorem06DC {A : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS A)
    (h06DC : Theorem06DC.{u, w} C S hS)
    (hsflat : Space.IsFlat C S hS G.source.hom)
    (htflat : Space.IsFlat C S hS G.target.hom)
    (hslfp : Space.IsLocallyOfFinitePresentation C S hS G.source.hom)
    (htlfp : Space.IsLocallyOfFinitePresentation C S hS G.target.hom) :
    IsAlgebraicStack.{u, w} C S hS (quotientStack G) :=
  isAlgebraicStack_quotientStack.{u, w} G h06DC (lemma06FH C S hS) (lemma04TB C S hS A G) hsflat
    htflat hslfp htlfp

/-- **Stacks 06FI quantified over the groupoids on a fixed base, carrying Artin's theorem
alone.** Every groupoid in algebraic spaces over `A` whose source and target are flat and
locally of finite presentation has an algebraic quotient stack, given Artin's theorem
Stacks 06DC.

This is `AlgebraicGeometry.Stack.forall_isAlgebraicStack_quotientStack` with its Stacks 06FH and
Stacks 04TB hypotheses supplied by `AlgebraicGeometry.Stack.lemma06FH` and
`AlgebraicGeometry.Stack.lemma04TB`. -/
theorem forall_isAlgebraicStack_quotientStack_of_theorem06DC (A : AlgebraicSpaces C S hS)
    (h06DC : Theorem06DC.{u, w} C S hS) :
    ∀ H : GroupoidInAlgebraicSpaces C S hS A,
      Space.IsFlat C S hS H.source.hom → Space.IsFlat C S hS H.target.hom →
        Space.IsLocallyOfFinitePresentation C S hS H.source.hom →
          Space.IsLocallyOfFinitePresentation C S hS H.target.hom →
            IsAlgebraicStack.{u, w} C S hS (quotientStack H) :=
  forall_isAlgebraicStack_quotientStack A h06DC (lemma06FH C S hS) (lemma04TB C S hS)

variable {B : AlgebraicSpaces C S hS}

/-- **Stacks 06PJ, the implication towards algebraicity, carrying Artin's theorem alone.** Let
`(U, R, s, t, c)` be a groupoid in algebraic spaces over `B` and let `g : U' ⟶ U` be a morphism
of algebraic spaces such that the saturation map `U' ×_{g, U, t} R ⟶ R ⟶ U` is a surjection of
fppf sheaves and the source and target of the restriction of `(U, R, s, t, c)` along `g` are
flat and locally of finite presentation. Then the quotient stack `[U/R]` is an algebraic stack,
given Artin's theorem Stacks 06DC.

This is `AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_of_restrictionAlong` with its
Stacks 06FI hypothesis supplied by
`AlgebraicGeometry.Stack.forall_isAlgebraicStack_quotientStack_of_theorem06DC`. -/
theorem isAlgebraicStack_quotientStack_of_restrictionAlong_of_theorem06DC
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects)
    (h06DC : Theorem06DC.{u, w} C S hS)
    (hsaturation : Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS)
      ((GroupoidInAlgebraicSpaces.fiberProductSnd g G.target ≫ G.source).hom))
    (hsource : Space.IsFlat C S hS
      (GroupoidInAlgebraicSpaces.restrictionSource G g).hom)
    (htarget : Space.IsFlat C S hS
      (GroupoidInAlgebraicSpaces.restrictionTarget G g).hom)
    (hsourceFP : Space.IsLocallyOfFinitePresentation C S hS
      (GroupoidInAlgebraicSpaces.restrictionSource G g).hom)
    (htargetFP : Space.IsLocallyOfFinitePresentation C S hS
      (GroupoidInAlgebraicSpaces.restrictionTarget G g).hom) :
    IsAlgebraicStack.{u, w} C S hS (quotientStack G) :=
  isAlgebraicStack_quotientStack_of_restrictionAlong G g
    (forall_isAlgebraicStack_quotientStack_of_theorem06DC.{u, w} B h06DC)
    hsaturation hsource htarget hsourceFP htargetFP

/-- **Stacks 06PL, the implication from flatness and local finite presentation to algebraicity,
carrying Artin's theorem alone.** Let `G` be a group algebraic space over an algebraic space `B`
over `S` and endow `B` with the trivial action of `G`. If `G` is flat and locally of finite
presentation over `B`, then the quotient stack `[B/G]` is an algebraic stack, given Artin's
theorem Stacks 06DC.

This is `AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_trivialAction` with its
Stacks 06FI hypothesis supplied by
`AlgebraicGeometry.Stack.forall_isAlgebraicStack_quotientStack_of_theorem06DC`. -/
theorem isAlgebraicStack_quotientStack_trivialAction_of_theorem06DC
    (B : AlgebraicSpaces C S hS) (G : Over B.obj) [GrpObj G]
    (hG : IsAlgebraicSpace C S hS G.left)
    (A : Space.ActionGroupoidConstruction B G (𝟙_ (Over B.obj)) hG B.property)
    (h06DC : Theorem06DC.{u, w} C S hS)
    (hflat : Space.IsFlat C S hS G.hom)
    (hlfp : Space.IsLocallyOfFinitePresentation C S hS G.hom) :
    IsAlgebraicStack.{u, w} C S hS (quotientStack A.groupoid) :=
  isAlgebraicStack_quotientStack_trivialAction B G hG A
    (forall_isAlgebraicStack_quotientStack_of_theorem06DC.{u, w} B h06DC) hflat hlfp

end AlgebraicGeometry.Stack

end
