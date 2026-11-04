module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GenericFlatness.MorphismFlatStratificationQcqs
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.Flattening
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.FlatteningApproximation
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.AlmostBlowUpDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.SheafCriterion

/-!
# The almost blowup conditions for sheaves on the h site

Stacks 0EVF characterizes the sheaves on the big h site over a scheme `S` by three conditions on
a presheaf `F`:

1. `F` is a sheaf for the Zariski topology;
2. for every morphism `f : X ⟶ Y` of the site with `Y` affine and `f` surjective, flat, proper
   and of finite presentation, `F(Y)` is the equalizer of the two maps `F(X) ⟶ F(X ×_Y X)`;
3. for every almost blowup square of the site whose base `X` is affine, the square
   `F(E) ← F(X')`, `F(Z) ← F(X)` is cartesian in sets.

Condition (1) is condition (1) of Stacks 0EU5 and is reused verbatim from
`StacksFrontier.AlgebraicGeometry.Topologies.HTopology.SheafCriterion`.  Condition (2) is condition
(2′) of Stacks 0EU5 with flatness added, so it is *weaker* than the condition 0EU5 asks for, and
condition (3) is what Stacks 0EVD provides for a sheaf.

This file states conditions (2) and (3) and proves the necessity direction: a sheaf satisfies all
three.  The sufficiency direction, and hence the characterization itself, is proved in
`StacksFrontier.AlgebraicGeometry.Topologies.HTopology.AlmostBlowUpSheafInduction`, which imports
this module for the two conditions; see "The sufficiency direction" below.

## Main definitions

* `AlgebraicGeometry.BigHOver.IsAffineFlatProperFinitePresentationSheaf`: condition (2), in the
  form of the sheaf condition for the one-element family `{f}`.
* `AlgebraicGeometry.BigHOver.IsAffineAlmostBlowUpSheaf`: condition (3).
* `AlgebraicGeometry.FinitePresentationHasAlmostBlowUpFlattening`: the affine-base case of Stacks
  0EVC, in the shape the sufficiency direction consumes it.

Condition (1) is `AlgebraicGeometry.BigHOver.IsZariskiSheaf`, defined with Stacks 0EU5.

## Main results

* `AlgebraicGeometry.BigHOver.zariski_and_affineFlatProperFP_and_affineAlmostBlowUp_of_isSheaf`:
  a sheaf satisfies the three conditions.
* `AlgebraicGeometry.BigHOver.isAffineFlatProperFinitePresentationSheaf_of_isSheaf`: a sheaf
  satisfies condition (2).
* `AlgebraicGeometry.BigHOver.IsAffineFlatProperFinitePresentationSheaf.bijective_mapToEqualizer`:
  condition (2) in the equalizer form in which the source states it.
* `AlgebraicGeometry.BigHOver.isAffineAlmostBlowUpSheaf_of_isSheaf`: a sheaf satisfies condition
  (3).
* `AlgebraicGeometry.finitePresentationHasAlmostBlowUpFlattening`: the affine-base case of Stacks
  0EVC, the geometric input of the sufficiency direction.

A sheaf satisfies condition (1) by `AlgebraicGeometry.BigHOver.isZariskiSheaf_of_isSheaf`.

## Implementation notes

**The necessity direction.**  Flatness is not used in condition (2): a flat proper surjective
morphism of finite presentation is an h covering all by itself, and so is every proper surjective
morphism of finite presentation, which is the content of condition (2) of Stacks 0EU5.  Likewise
affineness of the base is not used in condition (3): that is Stacks 0EVD for an arbitrary almost
blowup square of the site.

**The sufficiency direction.**  By Stacks 0EU5 it is enough to produce condition (2′) of that
tag — the sheaf condition for a proper surjective morphism of finite presentation with affine
target, with no flatness assumed — so the whole content of the sufficiency direction is the
removal of flatness from condition (2).  That is
`AlgebraicGeometry.BigHOver.isAffineProperFinitePresentationSheaf_of_conditions` in
`StacksFrontier.AlgebraicGeometry.Topologies.HTopology.AlmostBlowUpSheafInduction`, where the
characterization
`AlgebraicGeometry.BigHOver.isSheaf_iff_zariski_and_affineFlatProperFP_and_affineAlmostBlowUp` is
assembled from it and the necessity direction below.  It runs the
source's induction along the generic flatness stratification of the target supplied by Stacks
0H3Z, flattening the morphism over each stratum by the pair of almost blowup squares of Stacks
0EVC.  Its ingredients are the thickening results and Interlude A of
`StacksFrontier.AlgebraicGeometry.Topologies.HTopology.AlmostBlowUpSheafThickening`, Interlude B of
`StacksFrontier.AlgebraicGeometry.Topologies.HTopology.AlmostBlowUpSheafCartesian`, and the
flattening pair of
`StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.FlatteningApproximation` and
`StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.FlatteningSurjective`.

**Generic flatness.**  Stacks 0H3Z is
`AlgebraicGeometry.HasFlatStratification.of_finitePresentation` in
`StacksFrontier.AlgebraicGeometry.GenericFlatness.MorphismFlatStratificationQcqs`, with the
`Prop`-valued form `AlgebraicGeometry.finitePresentationHasFlatStratification` beside it.  It is
the case `ℱ = 𝒪_X` of Stacks 0ASY, which this development has in full quasi-compact
quasi-separated generality for a finitely presented module.

**Why the structure is used.**  The theorem `AlgebraicGeometry.isIso_restrict_compl_support`
also carries `@[stacks 0EV6]`.  Partially
applied to a centre and a modification, that theorem's type is the `Pi` type
`IsAlmostBlowUpSquare I b → IsIso (b ∣_ I.supportᶜ)`, which the theorem itself inhabits for every
`I` and `b` whatsoever; binding it where `AlgebraicGeometry.IsAlmostBlowUpSquare` belongs would
subject clause (3) to no almost blowup hypothesis at all, and would demand instead that the image
of *every* square of the site with affine base, closed-immersion centre and cartesian exceptional
corner be cartesian, which a sheaf need not satisfy.  The structure, not the theorem, is used
here.

## References

* [Stacks Project, Tag 0EVF](https://stacks.math.columbia.edu/tag/0EVF)
* [Stacks Project, Tag 0EVD](https://stacks.math.columbia.edu/tag/0EVD)
* [Stacks Project, Tag 0EVC](https://stacks.math.columbia.edu/tag/0EVC)
* [Stacks Project, Tag 0EU5](https://stacks.math.columbia.edu/tag/0EU5)
* [Stacks Project, Tag 0EWM](https://stacks.math.columbia.edu/tag/0EWM)
* [Stacks Project, Tag 0H3Z](https://stacks.math.columbia.edu/tag/0H3Z)
* [Stacks Project, Tag 0ASY](https://stacks.math.columbia.edu/tag/0ASY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

/-! ### The flattening input of the sufficiency direction -/

/-- **The affine-base case of Stacks 0EVC.** Every morphism of finite presentation to an affine
scheme admits, over every quasi-compact open of its target over which it is flat, the pair of
almost blowup squares of Stacks 0EVC: a centre on the target disjoint from that open, a centre on
the source, two modifications making both squares almost blowup squares, and a relative morphism
between the two modifications which is flat and of finite presentation.

This is the shape in which the sufficiency direction below consumes Stacks 0EVC, and it is stated
as a `Prop` in the style of `AlgebraicGeometry.UniversallySubmersiveHasPHRefinement`.  It is
proved by `AlgebraicGeometry.finitePresentationHasAlmostBlowUpFlattening` beside it, from
`AlgebraicGeometry.hasFlatAlmostBlowUpSquarePair_of_flat`, which is Stacks 0EVC over a
quasi-compact quasi-separated base.

It carries no `@[stacks 0EVC]` attribute, that tag being registered where the statement it names
is proved. -/
public def FinitePresentationHasAlmostBlowUpFlattening : Prop :=
  ∀ {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y), FinitePresentation f →
    ∀ V : Y.Opens, IsCompact (V : Set Y) → Flat (pullback.snd f V.ι) →
      HasFlatAlmostBlowUpSquarePair f V

/-- **The affine-base case of Stacks 0EVC.** An affine scheme is quasi-compact and
quasi-separated, so this is `AlgebraicGeometry.hasFlatAlmostBlowUpSquarePair_of_flat`. -/
public theorem finitePresentationHasAlmostBlowUpFlattening :
    FinitePresentationHasAlmostBlowUpFlattening.{u} :=
  fun f hf V hV hflat ↦ hasFlatAlmostBlowUpSquarePair_of_flat f hf V hV hflat

namespace BigHOver

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (F : (BigHOver B S hS)ᵒᵖ ⥤ Type v)

/-! ### The two conditions of Stacks 0EVF beyond the Zariski one -/

/-- **Condition (2) of Stacks 0EVF.** A presheaf on the big h category over `S` satisfies the
sheaf condition for the one-element family `{f}` attached to every morphism `f` of the site whose
target has affine underlying scheme and whose underlying morphism of schemes is flat, proper,
surjective and of finite presentation.

This is condition (2′) of Stacks 0EU5,
`AlgebraicGeometry.BigHOver.IsAffineProperFinitePresentationSheaf`, with flatness added, so it is
a weaker requirement.  By
`AlgebraicGeometry.isSheafFor_singleton_iff_bijective_mapToEqualizer` it is exactly the source's
requirement that the sections over the target map bijectively onto the equalizer of the two maps
from the sections over the source to the sections over `X ×_Y X`; that reading is
`AlgebraicGeometry.BigHOver.IsAffineFlatProperFinitePresentationSheaf.bijective_mapToEqualizer`
below. -/
public def IsAffineFlatProperFinitePresentationSheaf : Prop :=
  ∀ (X Y : BigHOver B S hS) (f : Y ⟶ X),
    IsAffine ((BigHOver.toScheme B S hS).obj X) →
    Flat ((BigHOver.toScheme B S hS).map f) →
    IsProper ((BigHOver.toScheme B S hS).map f) →
    Surjective ((BigHOver.toScheme B S hS).map f) →
    FinitePresentation ((BigHOver.toScheme B S hS).map f) →
    Presieve.IsSheafFor F (Presieve.singleton f)

/-- **Condition (3) of Stacks 0EVF.** A presheaf on the big h category over `S` sends every
almost blowup square of the site whose base has affine underlying scheme to a cartesian square of
sets.

The square is given by its base `X`, its modification `b : X' ⟶ X`, its centre `z : Z ⟶ X` and
its exceptional corner `p : E ⟶ X'`, `e : E ⟶ Z`, together with an ideal sheaf `I` on the
underlying scheme of `X` for which `b` is an almost blowup square with centre `I`, an
identification of `z` with the closed subscheme cut out by `I` over `X`, and the cartesianness of
the square underlying `(z, b, e, p)`.  This is the data and the hypotheses of Stacks 0EVD,
`AlgebraicGeometry.isPullback_of_almostBlowUpSquare_bigH`, together with affineness of the
underlying scheme of `X`. -/
public def IsAffineAlmostBlowUpSheaf : Prop :=
  ∀ (X X' Z E : BigHOver B S hS) (b : X' ⟶ X) (z : Z ⟶ X) (p : E ⟶ X') (e : E ⟶ Z)
      (I : ((BigHOver.toScheme B S hS).obj X).IdealSheafData),
    IsAffine ((BigHOver.toScheme B S hS).obj X) →
    IsAlmostBlowUpSquare I ((BigHOver.toScheme B S hS).map b) →
    Nonempty (Over.mk ((BigHOver.toScheme B S hS).map z) ≅ Over.mk I.subschemeι) →
    IsPullback
      ((BigHOver.toScheme B S hS).map e)
      ((BigHOver.toScheme B S hS).map p)
      ((BigHOver.toScheme B S hS).map z)
      ((BigHOver.toScheme B S hS).map b) →
    IsPullback (F.map z.op) (F.map b.op) (F.map e.op) (F.map p.op)

/-! ### A sheaf satisfies the three conditions -/

/-- **Stacks 0EVF, a sheaf satisfies condition (2).** A sheaf on the big h site over `S` satisfies
the sheaf condition for the one-element family attached to a morphism of the site with affine
target which is flat, proper, surjective and of finite presentation.

Flatness is not used: such a morphism is an h covering all by itself, and so is every proper
surjective morphism of finite presentation, which is the content of condition (2) of Stacks
0EU5. -/
@[stacks 0EVF "only if, condition (2)"]
public theorem isAffineFlatProperFinitePresentationSheaf_of_isSheaf
    (hF : Presheaf.IsSheaf (BigHOver.topology B S hS) F) :
    BigHOver.IsAffineFlatProperFinitePresentationSheaf B S hS F :=
  fun X Y f _ _ hproper hsurj hfp ↦
    isProperFinitePresentationSheaf_of_isSheaf B S hS F hF X Y f hproper hsurj hfp

/-- **Condition (2) of Stacks 0EVF in the source's equalizer form.** Let `f : V ⟶ U` be a
morphism of the big h category over `S` whose target has affine underlying scheme and whose
underlying morphism of schemes is flat, proper, surjective and of finite presentation, and let
`p₁, p₂ : W ⟶ V` complete `f` to a cartesian square, so that `W = V ×_U V`.  Then condition (2)
says exactly that `F(U)` maps bijectively onto the equalizer of the two maps `F(V) ⟶ F(W)`.

This is the form in which the source states the condition; the two are identified by
`AlgebraicGeometry.isSheafFor_singleton_iff_bijective_mapToEqualizer`. -/
@[stacks 0EVF "condition (2) in equalizer form"]
public theorem IsAffineFlatProperFinitePresentationSheaf.bijective_mapToEqualizer
    (hF : BigHOver.IsAffineFlatProperFinitePresentationSheaf B S hS F)
    {V U W : BigHOver B S hS} (f : V ⟶ U) (p₁ p₂ : W ⟶ V) (hW : IsPullback p₁ p₂ f f)
    (haffine : IsAffine ((BigHOver.toScheme B S hS).obj U))
    (hflat : Flat ((BigHOver.toScheme B S hS).map f))
    (hproper : IsProper ((BigHOver.toScheme B S hS).map f))
    (hsurj : Surjective ((BigHOver.toScheme B S hS).map f))
    (hfp : FinitePresentation ((BigHOver.toScheme B S hS).map f)) :
    Function.Bijective (regularTopology.mapToEqualizer F f p₁ p₂ hW.w) :=
  (isSheafFor_singleton_iff_bijective_mapToEqualizer f p₁ p₂ hW).1
    (hF U V f haffine hflat hproper hsurj hfp)

/-- **Stacks 0EVF, a sheaf satisfies condition (3).** A sheaf on the big h site over `S` sends an
almost blowup square of the site with affine base to a cartesian square of sets.

Affineness of the base is not used: this is Stacks 0EVD for an arbitrary almost blowup square of
the site. -/
@[stacks 0EVF "only if, condition (3)"]
public theorem isAffineAlmostBlowUpSheaf_of_isSheaf
    (hF : Presheaf.IsSheaf (BigHOver.topology B S hS) F) :
    BigHOver.IsAffineAlmostBlowUpSheaf B S hS F :=
  fun _ _ _ _ b z p e I _ hb hZ hSquare ↦
    isPullback_of_almostBlowUpSquare_bigH B S hS F hF b z p e I hb hZ hSquare

/-- **Stacks 0EVF, the three conditions are necessary.** A sheaf on the big h site over `S`
satisfies condition (1), the sheaf condition for Zariski coverings, condition (2), the sheaf
condition for every morphism of the site with affine target which is flat, proper, surjective and
of finite presentation, and condition (3), the cartesianness of the image of every almost blowup
square of the site with affine base.

The converse is
`AlgebraicGeometry.BigHOver.isSheaf_of_zariski_and_affineFlatProperFP_and_affineAlmostBlowUp`, and
the two together are
`AlgebraicGeometry.BigHOver.isSheaf_iff_zariski_and_affineFlatProperFP_and_affineAlmostBlowUp`,
both in `StacksFrontier.AlgebraicGeometry.Topologies.HTopology.AlmostBlowUpSheafInduction`. -/
@[stacks 0EVF "only if, all three conditions"]
public theorem zariski_and_affineFlatProperFP_and_affineAlmostBlowUp_of_isSheaf
    (hF : Presheaf.IsSheaf (BigHOver.topology B S hS) F) :
    BigHOver.IsZariskiSheaf B S hS F ∧
      BigHOver.IsAffineFlatProperFinitePresentationSheaf B S hS F ∧
      BigHOver.IsAffineAlmostBlowUpSheaf B S hS F :=
  ⟨isZariskiSheaf_of_isSheaf B S hS F hF,
    isAffineFlatProperFinitePresentationSheaf_of_isSheaf B S hS F hF,
    isAffineAlmostBlowUpSheaf_of_isSheaf B S hS F hF⟩

end BigHOver

end AlgebraicGeometry

end
