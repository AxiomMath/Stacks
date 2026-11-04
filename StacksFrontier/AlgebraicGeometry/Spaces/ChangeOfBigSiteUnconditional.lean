module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineFlatChartDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteEssentialImage

/-!
# Enlarging the big fppf site of an algebraic space, unconditionally

`StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSite` and
`StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteEssentialImage` prove Stacks 03FP, part (2)
and Stacks 04W1 — enlarging a big fppf site carries algebraic spaces over `S` to algebraic spaces
over `S`, the induced functor is fully faithful, and its essential image is the algebraic spaces
admitting a presentation by two objects of the smaller site — conditional on

```
AlgebraicGeometry.DescentForQuotients B S hS
```

for the sites involved, and on nothing else. That proposition is a theorem: it is
`AlgebraicGeometry.Space.IsEffectiveDescentAlongCoveringSieve` at the monomorphisms locally of
finite type, which is
`AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft`. This file
substitutes it, which discharges the two tags.

## Main definitions

* `AlgebraicGeometry.changeBigSite` is inverse image along the inclusion of localized big fppf
  sites, as a functor on algebraic spaces over `S`, with no hypothesis.

## Main results

* `AlgebraicGeometry.descentForQuotients`: the descent hypothesis of the quotient theorem holds
  for every big fppf site, every base scheme of it and every containment witness.
* `AlgebraicGeometry.isAlgebraicSpace_sheafPullback`: **Stacks 03FP, part (2)**, unconditionally.
* `AlgebraicGeometry.relativelyRepresentable_diag_sheafPullback`: the diagonal of the inverse
  image of an algebraic space is relatively representable, unconditionally.
* `AlgebraicGeometry.changeBigSite_fullyFaithful`: **Stacks 04W1, full faithfulness**, for the
  functor valued in algebraic spaces over `S` rather than in sheaves.
* `AlgebraicGeometry.exists_small_presentation_of_mem_essentialImage_changeBigSite`,
  `AlgebraicGeometry.mem_essentialImage_changeBigSite_of_small_presentation` and
  `AlgebraicGeometry.mem_essentialImage_changeBigSite_iff`: **Stacks 04W1, the essential image**,
  unconditionally.

## Implementation notes

**Why the hypothesis is dischargeable, and where the discharge lives.** The chain that produces
the chart of a quotient sheaf consumes
`AlgebraicGeometry.Space.IsEffectiveDescentAlongCoveringSieve` at the monomorphisms locally of
finite type, which is a smaller property than the one Stacks 02W8 descends. The predicate
mentions its property both in its hypothesis and in its conclusion, so it is monotone in neither
direction and the two instances are independent statements; the smaller one lies below the
monomorphisms, where `AlgebraicGeometry.Scheme.size_le_of_mono` pays for the passage from an
affine base object to an arbitrary one, and there it is proved outright in
`StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineFlatChartDescent`. Nothing new is proved here:
every statement below is its conditional form with that theorem substituted for the hypothesis.

**Tag placement.** Stacks 03FP asserts two things, and part (1) — that the inverse image of a
representable sheaf is represented by the same scheme — is already recorded, on
`CategoryTheory.sheafPullback_sheafify_yoneda_natIso` by `add_to_stacks`. Part (2) is the
assertion of `AlgebraicGeometry.isAlgebraicSpace_sheafPullback`, which is the only declaration
here carrying `@[stacks 03FP]`.

Stacks 04W1 asserts that the construction of 03FP defines a fully faithful functor
`Spaces/S ⟶ Spaces'/S` and identifies its essential image. The covering set is therefore
`AlgebraicGeometry.changeBigSite` for the functor,
`AlgebraicGeometry.changeBigSite_fullyFaithful` for full faithfulness and
`AlgebraicGeometry.mem_essentialImage_changeBigSite_iff` for the essential image, and the tag
sits on each of those three. The two halves of the characterization are recorded untagged: they
are the two implications of the tagged equivalence, not separate assertions of the source.
`AlgebraicGeometry.changeBigSiteSheafPullback_fullyFaithful` keeps its own
`@[stacks 04W1 "full faithfulness, for the sheaf-valued inverse image"]`; that statement is about
a functor valued in sheaves, which is not the functor 04W1 speaks of, and is kept because it
needs none of the quotient theory.

**What this does not give.** Stacks 04WX, the comparison of quotient stacks under a change of big
site, is not reached: it needs the groupoid-level functor `changeBigSiteGroupoid` and the
quotient-stack construction, neither of which is a consequence of the statements below.

## References

* [Stacks Project, Tag 03FP](https://stacks.math.columbia.edu/tag/03FP)
* [Stacks Project, Tag 04W1](https://stacks.math.columbia.edu/tag/04W1)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S)

/-- **The descent hypothesis of the quotient theorem holds.** Effective descent along the
covering sieves of a big fppf site at the monomorphisms locally of finite type is available for
every big fppf site, every scheme contained in it and every containment witness.

This is `AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft`
read through the abbreviation `AlgebraicGeometry.DescentForQuotients`, and it is what makes the
statements below unconditional. -/
theorem descentForQuotients (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    DescentForQuotients B S hS :=
  Space.isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft B S hS

/-- **Stacks 03FP, part (2).** Enlarging the big fppf site preserves algebraic spaces over the
base scheme: the inverse image of an algebraic space over `S` on the smaller localized site is an
algebraic space over `S` on the larger one.

This is `AlgebraicGeometry.isAlgebraicSpace_sheafPullback_of_descent` with its descent hypothesis
discharged by `AlgebraicGeometry.descentForQuotients`. -/
@[stacks 03FP "part (2)"]
theorem isAlgebraicSpace_sheafPullback
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    letI J := overTopology .fppf B S hS
    letI K := overTopology .fppf B' S (largerContains h hS)
    letI i := inclusionOver h S hS
    letI : i.IsContinuous J K :=
      (inclusionOver_isMorphismOfSites (τ := .fppf) B B' h S hS).toIsContinuous
    letI : (i.sheafPushforwardContinuous (Type u) J K).IsRightAdjoint :=
      inclusionOver_sheafPushforwardContinuous_isRightAdjoint B B' h S hS
    IsAlgebraicSpace B' S (largerContains h hS)
      ((i.sheafPullback (Type u) J K).obj ⟨F, hF.isSheaf⟩).obj :=
  isAlgebraicSpace_sheafPullback_of_descent B B' h S hS F hF
    (descentForQuotients B' S (largerContains h hS))

/-- **The diagonal of the inverse image of an algebraic space is relatively representable**, with
no hypothesis.

This is the hypothesis of
`AlgebraicGeometry.isAlgebraicSpace_sheafPullback_of_relativelyRepresentable_diag`, which is
strictly less than the effective descent predicate the quotient route carries. It is recorded
here because that reduction is the shape in which Stacks 03FP, part (2) is cheapest to consume:
a single assertion about a single presheaf rather than a statement quantified over all morphisms
of sheaves, all represented points and all covering sieves of the larger site. It is
`AlgebraicGeometry.relativelyRepresentable_diag_sheafPullback_of_descent` with its hypothesis
discharged. -/
theorem relativelyRepresentable_diag_sheafPullback
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    letI J := overTopology .fppf B S hS
    letI K := overTopology .fppf B' S (largerContains h hS)
    letI i := inclusionOver h S hS
    letI : i.IsContinuous J K :=
      (inclusionOver_isMorphismOfSites (τ := .fppf) B B' h S hS).toIsContinuous
    letI : (i.sheafPushforwardContinuous (Type u) J K).IsRightAdjoint :=
      inclusionOver_sheafPushforwardContinuous_isRightAdjoint B B' h S hS
    yoneda.relativelyRepresentable
      (diag ((i.sheafPullback (Type u) J K).obj ⟨F, hF.isSheaf⟩).obj) :=
  relativelyRepresentable_diag_sheafPullback_of_descent B B' h S hS F hF
    (descentForQuotients B' S (largerContains h hS))

/-- **Stacks 04W1, the functor.** Inverse image along the inclusion of localized big fppf sites,
as a functor from the algebraic spaces over `S` defined using the smaller site to those defined
using the larger one, with no hypothesis.

This is `AlgebraicGeometry.changeBigSiteOfDescent` with its descent hypothesis discharged by
`AlgebraicGeometry.descentForQuotients`. -/
@[stacks 04W1 "the functor"]
def changeBigSite :
    AlgebraicSpaces B S hS ⥤ AlgebraicSpaces B' S (largerContains h hS) :=
  changeBigSiteOfDescent B B' h S hS (descentForQuotients B' S (largerContains h hS))

/-- **Stacks 04W1, full faithfulness.** Inverse image along the inclusion of localized big fppf
sites is fully faithful as a functor on the algebraic spaces over `S`.

This is `AlgebraicGeometry.changeBigSiteOfDescent_fullyFaithful` with its descent hypothesis
discharged. It is the statement of 04W1 proper, where
`AlgebraicGeometry.changeBigSiteSheafPullback_fullyFaithful` is the same conclusion for the
functor valued in sheaves on the larger site. -/
@[stacks 04W1 "full faithfulness"]
theorem changeBigSite_fullyFaithful :
    Nonempty (changeBigSite B B' h S hS).FullyFaithful :=
  changeBigSiteOfDescent_fullyFaithful B B' h S hS
    (descentForQuotients B' S (largerContains h hS))

/-- **Stacks 04W1, one half of the essential image**, with no hypothesis.

An algebraic space over `S` in the essential image of `AlgebraicGeometry.changeBigSite` receives
a locally surjective map from an object of the smaller site, and its kernel pair receives a
locally surjective map from an object of the smaller site. This is
`AlgebraicGeometry.exists_small_presentation_of_mem_essentialImage` with its descent hypothesis
discharged; it is untagged, being one implication of the tagged equivalence
`AlgebraicGeometry.mem_essentialImage_changeBigSite_iff`. -/
theorem exists_small_presentation_of_mem_essentialImage_changeBigSite
    (X : AlgebraicSpaces B S hS) (X' : AlgebraicSpaces B' S (largerContains h hS))
    (eX : (changeBigSite B B' h S hS).obj X ≅ X') :
    let K := BigFppfOver.topology B' S (largerContains h hS)
    let i := inclusionOver h S hS
    ∃ (U R : BigFppfOver B S hS) (f : yoneda.obj (i.obj U) ⟶ X'.obj)
      (g : yoneda.obj (i.obj R) ⟶ pullback f f),
      Presheaf.IsLocallySurjective K f ∧ Presheaf.IsLocallySurjective K g :=
  exists_small_presentation_of_mem_essentialImage B B' h S hS
    (descentForQuotients B' S (largerContains h hS)) X X' eX

/-- **Stacks 04W1, the other half of the essential image**, with no hypothesis.

An algebraic space over `S` on the larger site which receives a locally surjective map from an
object of the smaller site, and whose kernel pair receives a locally surjective map from an
object of the smaller site, lies in the essential image of `AlgebraicGeometry.changeBigSite`.
This is `AlgebraicGeometry.mem_essentialImage_of_small_presentation` with its two descent
hypotheses discharged; it is untagged, being one implication of the tagged equivalence
`AlgebraicGeometry.mem_essentialImage_changeBigSite_iff`. -/
theorem mem_essentialImage_changeBigSite_of_small_presentation
    (X' : AlgebraicSpaces B' S (largerContains h hS)) (U R : BigFppfOver B S hS)
    (f : yoneda.obj ((inclusionOver h S hS).obj U) ⟶ X'.obj)
    (g : yoneda.obj ((inclusionOver h S hS).obj R) ⟶ pullback f f)
    (hf : Presheaf.IsLocallySurjective
      (BigFppfOver.topology B' S (largerContains h hS)) f)
    (hg : Presheaf.IsLocallySurjective
      (BigFppfOver.topology B' S (largerContains h hS)) g) :
    ∃ X : AlgebraicSpaces B S hS,
      Nonempty ((changeBigSite B B' h S hS).obj X ≅ X') :=
  mem_essentialImage_of_small_presentation B B' h S hS (descentForQuotients B S hS)
    (descentForQuotients B' S (largerContains h hS)) X' U R f g hf hg

/-- **Stacks 04W1, the essential image.** An algebraic space on the enlarged big fppf site
descends precisely when an object of the smaller site surjects onto it as a map of sheaves and
another object of the smaller site surjects onto the kernel pair of that surjection.

This is `AlgebraicGeometry.mem_essentialImage_changeBigSiteOfDescent_iff` with both descent
hypotheses discharged. -/
@[stacks 04W1 "the essential image"]
theorem mem_essentialImage_changeBigSite_iff
    (X' : AlgebraicSpaces B' S (largerContains h hS)) :
    (∃ X : AlgebraicSpaces B S hS,
      Nonempty ((changeBigSite B B' h S hS).obj X ≅ X')) ↔
      (letI K := BigFppfOver.topology B' S (largerContains h hS)
       let i := inclusionOver h S hS
       ∃ (U R : BigFppfOver B S hS) (f : yoneda.obj (i.obj U) ⟶ X'.obj)
         (g : yoneda.obj (i.obj R) ⟶ pullback f f),
         Presheaf.IsLocallySurjective K f ∧ Presheaf.IsLocallySurjective K g) :=
  mem_essentialImage_changeBigSiteOfDescent_iff B B' h S hS (descentForQuotients B S hS)
    (descentForQuotients B' S (largerContains h hS)) X'

end AlgebraicGeometry

end
