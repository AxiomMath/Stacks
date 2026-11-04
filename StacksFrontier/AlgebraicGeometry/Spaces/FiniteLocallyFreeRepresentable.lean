module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeOfRankEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreePushforwardComparison

/-!
# Finite local freeness of a representable morphism of algebraic spaces

Stacks 03ZU asserts, for a representable morphism `f : X ⟶ Y` of algebraic spaces over a
scheme `S`, that `f` is finite locally free in the sense of Section 03HA — every represented
base change of `f` is a finite locally free morphism of schemes — exactly when `f` is affine
and the direct image `f_*𝒪_X` of the structure sheaf of its source is a finite locally free
`𝒪_Y`-module.  The right-hand side is the definition of Stacks 03ZV, in this development
`AlgebraicGeometry.Space.IsFiniteLocallyFree`, and it is condition (2) of Stacks 03ZW.

Both sides of that equivalence are étale local on `Y`, and both localizations are available:
the left-hand side is tested on one surjective étale chart by
`AlgebraicGeometry.Space.isFiniteLocallyFree_presheaf_iff_of_etaleChart_surjectiveOnPoints`
(Stacks 03ZW, conditions (1) and (3)), the right-hand side by
`AlgebraicGeometry.Space.isFiniteLocallyFree_iff_over_of_isSurjective` (the step the source
performs with Modules on Sites, Lemma 03DN).  What separates them is a single comparison *at a
chart*, between the restriction of `f_*𝒪_X` to the slice of the small étale site of `Y` at the
chart and the scheme-level finite local freeness of the base change of `f` over that chart.
This file does not prove that comparison; it is proved, and the tag carried unconditionally, in
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRepresentableChart`.  See
`## Where Stacks 03ZU is delivered` below.

This file isolates that comparison as sharply as possible.  It carries it as a named hypothesis
at **one** chart and for **one** morphism — the weakest form the argument uses — in both
directions separately, and it proves, with no hypothesis at all, that the equivalence of
Stacks 03ZU for a given morphism is *equivalent* to that comparison.  So the comparison is not
merely sufficient for Stacks 03ZU: at a surjective chart it is necessary and sufficient.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isFiniteLocallyFree_of_presheaf_of_chartComparison_at` and
  `AlgebraicGeometry.Space.presheaf_of_isFiniteLocallyFree_of_chartComparison_at`: the two
  implications of Stacks 03ZU, each granted only the implication of the chart comparison that
  it uses, at one surjective étale chart of the target.
* `AlgebraicGeometry.Space.presheaf_iff_isFiniteLocallyFree_of_chartComparison_at`:
  **Stacks 03ZU, granted the chart comparison at one surjective étale chart.**
* `AlgebraicGeometry.Space.presheaf_iff_isFiniteLocallyFree_iff_chartComparison`: **the
  equivalence of Stacks 03ZU for a morphism is itself equivalent to the chart comparison for
  that morphism at a surjective étale chart.**  This carries no hypothesis, and it measures
  exactly what is missing.
* `AlgebraicGeometry.Space.presheaf_iff_isFiniteLocallyFreeOfRank_of_chartComparison_at` and
  `AlgebraicGeometry.Space.presheaf_iff_isFiniteLocallyFreeOfRank_iff_chartComparison`: the
  same two statements for the rank clause of Stacks 03ZV.

## Implementation notes

Condition (1) of Stacks 03ZW is read, as throughout these files, as
`CategoryTheory.MorphismProperty.presheaf` of the inverse image along
`AlgebraicGeometry.BigFppfOver.toScheme` of finite local freeness of morphisms of schemes:
that is "`f` is representable and every represented base change of `f` is finite locally
free", which is what finite local freeness in the sense of Section 03HA means.  The restriction
of `f_*𝒪_X` to a chart is restriction `SheafOfModules.over` to the slice of the small étale
site of `Y` at the chart, over the localized ringed site
`AlgebraicGeometry.RingedSite.over` of Stacks 04IX; it is **not** restriction to the Zariski
site of the chart scheme (`AlgebraicGeometry.Space.restrictToChart`).

The affineness conjunct of Stacks 03ZV is not an extra input in either direction.  From the
left it is `AlgebraicGeometry.Space.isAffineHom_of_presheaf_isFiniteLocallyFree`, which is
Stacks 03WG, (1) implies (2), applied after weakening along
`Stacks.Morphisms.IsFiniteLocallyFree.toIsAffineHom`; from the right it is the first conjunct
of `AlgebraicGeometry.Space.IsFiniteLocallyFree` itself.  That is why the chart comparison may
be stated for the module conjunct alone in the hypothesis-carrying statements, while the
unconditional measurement must carry affineness on its right-hand side: the module conjunct
does not by itself bound the morphism, as the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreePushforwardComparison` record with
`𝐏¹_k` over `Spec k`.

The chart hypothesis is never vacuous: every algebraic space has an étale chart whose structure
morphism is surjective on points, by
`AlgebraicGeometry.Space.exists_surjective_smallEtale_chart`.  So each statement here applies to
every representable morphism of algebraic spaces over `S`, and the equivalence proved
unconditionally is an equivalence between two statements both of which have content.

## Where Stacks 03ZU is delivered

No declaration *in this file* claims Stacks 03ZU in full.  The hypothesis `hcross` of the
statements below is part of the content of Stacks 03ZU itself — it is the comparison which the
source performs implicitly, as the abuse of notation of its Equation 03LW — so a statement
carrying it must not claim the tag, and the unconditional
`AlgebraicGeometry.Space.presheaf_iff_isFiniteLocallyFree_iff_chartComparison` states an
equivalence *between* Stacks 03ZU and that comparison rather than Stacks 03ZU.

That comparison is now proved, and the tag is carried unconditionally by
`AlgebraicGeometry.Space.presheaf_iff_isFiniteLocallyFree` in
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRepresentableChart`, which discharges it
as `AlgebraicGeometry.Space.isFiniteLocallyFree_baseChange_iff_chart`.  What the comparison asks
for is the identification of `(f_*𝒪_X)|_V`, a module on the slice of the small étale site of `Y`
at an étale scheme chart `V`, with `Stacks.Morphisms.pushforwardStructureSheaf` of the base
change `V ×_Y X ⟶ V` of `f`, which is a morphism of schemes because `f` is representable; that
identification is
`AlgebraicGeometry.Space.overPushforwardStructureModuleIsoSliceAssociatedModule`, and the
transport of finite local freeness across it is
`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_sliceAssociatedModule_iff`.  The module on the
slice is read not on the Zariski site of the scheme `V` but as the module `Mᵃ` of Stacks 03DU
there, where the clause 03DL (2) of Stacks 05VG — proved in both directions as
`AlgebraicGeometry.SmallEtale.isFiniteLocallyFreeOnSite_associatedModule_iff` — compares it with
the Zariski-level condition that `Stacks.Morphisms.IsFiniteLocallyFree` imposes.

The rank clause of Stacks 03ZV is **not** delivered by that route; see the implementation notes
of `StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRepresentableChart`.

Every result the source's own proof cites is available: Stacks 03LX as
`AlgebraicGeometry.Space.modulePushforwardEtaleBaseChangeIso`, Stacks 03DN as
`Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isFiniteLocallyFreeOnSite`,
Stacks 03I2 as
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isFiniteLocallyFree`, and the
descent and base-change inputs of Stacks 02KD, 02VO and 0245 through
`AlgebraicGeometry.Space.isFiniteLocallyFree_presheaf_iff_exists_etaleChart`.  The gap is the
identification the source leaves implicit, not one of its citations.

## References

* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
* [Stacks Project, Tag 03ZU](https://stacks.math.columbia.edu/tag/03ZU)
* [Stacks Project, Tag 03ZV](https://stacks.math.columbia.edu/tag/03ZV)
* [Stacks Project, Tag 03ZW](https://stacks.math.columbia.edu/tag/03ZW)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-! ### The two implications of Stacks 03ZU, each granted one half of the chart comparison -/

/-- **Stacks 03ZU, the "if" direction, granted one half of the chart comparison.** A
representable morphism of algebraic spaces over `S` which is finite locally free in the sense of
Section 03HA is affine with `f_*𝒪_X` a finite locally free `𝒪_Y`-module, provided that at one
étale chart `V` of `Y` whose structure morphism is surjective on points the scheme-level finite
local freeness of the base change of `f` over `V` implies finite local freeness of the
restriction of `f_*𝒪_X` to the slice at `V`.

Only that one implication of the chart comparison is used, and only at the chart `V` and the
morphism `f` given.  The affineness conjunct needs no hypothesis: it is Stacks 03WG, (1)
implies (2), as `AlgebraicGeometry.Space.isAffineHom_of_presheaf_isFiniteLocallyFree`. -/
theorem isFiniteLocallyFree_of_presheaf_of_chartComparison_at (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom)
    (V : (smallEtaleRingedSite B S hS Y.1 Y.2).C) (hV : IsSurjective B S hS V.1.hom)
    (hcross : Stacks.Morphisms.IsFiniteLocallyFree
        ((BigFppfOver.toScheme B S hS).map (hf.snd V.1.hom)) →
      SheafOfModules.IsFiniteLocallyFreeOnSite
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Y.1 Y.2).O).over V)
        ((pushforwardStructureModule B S hS f).over V))
    (h : (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f.hom) :
    IsFiniteLocallyFree B S hS f :=
  (isFiniteLocallyFree_iff_over_of_isSurjective B S hS f V hV).2
    ⟨isAffineHom_of_presheaf_isFiniteLocallyFree B S hS h,
      hcross ((isFiniteLocallyFree_presheaf_iff_of_etaleChart_surjectiveOnPoints
        B S hS X.2 Y.2 hf V.2 hV).1 h)⟩

/-- **Stacks 03ZU, the "only if" direction, granted one half of the chart comparison.** A
representable morphism of algebraic spaces over `S` which is affine with `f_*𝒪_X` a finite
locally free `𝒪_Y`-module is finite locally free in the sense of Section 03HA, provided that at
one étale chart `V` of `Y` whose structure morphism is surjective on points finite local
freeness of the restriction of `f_*𝒪_X` to the slice at `V` implies the scheme-level finite
local freeness of the base change of `f` over `V`.

Only that one implication of the chart comparison is used, and only at the chart `V` and the
morphism `f` given. -/
theorem presheaf_of_isFiniteLocallyFree_of_chartComparison_at (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom)
    (V : (smallEtaleRingedSite B S hS Y.1 Y.2).C) (hV : IsSurjective B S hS V.1.hom)
    (hcross : SheafOfModules.IsFiniteLocallyFreeOnSite
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Y.1 Y.2).O).over V)
        ((pushforwardStructureModule B S hS f).over V) →
      Stacks.Morphisms.IsFiniteLocallyFree
        ((BigFppfOver.toScheme B S hS).map (hf.snd V.1.hom)))
    (h : IsFiniteLocallyFree B S hS f) :
    (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f.hom :=
  (isFiniteLocallyFree_presheaf_iff_of_etaleChart_surjectiveOnPoints
      B S hS X.2 Y.2 hf V.2 hV).2
    (hcross ((isFiniteLocallyFree_iff_over_of_isSurjective B S hS f V hV).1 h).2)

/-! ### Stacks 03ZU granted the chart comparison -/

/-- **Stacks 03ZU, granted the chart comparison at one surjective étale chart.** For a
representable morphism `f : X ⟶ Y` of algebraic spaces over `S`, being finite locally free in
the sense of Section 03HA — every represented base change a finite locally free morphism of
schemes — is equivalent to being affine with `f_*𝒪_X` a finite locally free `𝒪_Y`-module, which
is the definition of Stacks 03ZV.

The one input that is **not** proved is `hcross`: that at an étale chart `V` of `Y` whose
structure morphism is surjective on points, finite local freeness of the restriction of
`f_*𝒪_X` to the slice at `V` agrees with the scheme-level finite local freeness of the base
change of `f` over `V`.  This is the unranked companion of
`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_iff_presheaf_of_chartComparison`, whose
hypothesis is quantified over every morphism and every chart; here it is required only for the
morphism and the chart at hand, which is all the argument uses.

It carries no attribute: `hcross` is part of the content of Stacks 03ZU, so a statement
carrying it must not claim the tag. -/
theorem presheaf_iff_isFiniteLocallyFree_of_chartComparison_at (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom)
    (V : (smallEtaleRingedSite B S hS Y.1 Y.2).C) (hV : IsSurjective B S hS V.1.hom)
    (hcross : SheafOfModules.IsFiniteLocallyFreeOnSite
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Y.1 Y.2).O).over V)
        ((pushforwardStructureModule B S hS f).over V) ↔
      Stacks.Morphisms.IsFiniteLocallyFree
        ((BigFppfOver.toScheme B S hS).map (hf.snd V.1.hom))) :
    (MorphismProperty.inverseImage
        (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf f.hom ↔
      IsFiniteLocallyFree B S hS f :=
  ⟨isFiniteLocallyFree_of_presheaf_of_chartComparison_at B S hS f hf V hV hcross.2,
    presheaf_of_isFiniteLocallyFree_of_chartComparison_at B S hS f hf V hV hcross.1⟩

/-! ### The chart comparison is necessary as well as sufficient -/

/-- **The equivalence of Stacks 03ZU for a morphism is equivalent to the chart comparison for
that morphism.** For a representable `f : X ⟶ Y` and an étale chart `V` of `Y` whose structure
morphism is surjective on points, the assertion of Stacks 03ZU for `f` holds exactly when the
scheme-level finite local freeness of the base change of `f` over `V` agrees with affineness of
`f` together with finite local freeness of the restriction of `f_*𝒪_X` to the slice at `V`.

This statement carries no hypothesis.  It says that the chart comparison is not merely one
sufficient input for Stacks 03ZU but is equivalent to it, so that nothing is lost by reducing
the tag to a statement at a single chart.  Affineness appears on the right-hand side because
the module conjunct alone does not bound the morphism; it cannot be dropped, as the
implementation notes record.

Its `@[stacks 03ZU]` attribute is clause-labelled for the reduction alone: it is an equivalence
between Stacks 03ZU and a chart statement, not Stacks 03ZU.  The chart statement is proved, and
with it the biconditional, in
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRepresentableChart`. -/
@[stacks 03ZU "the reduction of the biconditional to the chart comparison: proved \
unconditionally, that f is finite locally free in the sense of Section 03HA if and only if it is \
affine with finite locally free pushforward, holds exactly when the chart comparison holds at a \
surjective etale chart. The biconditional itself is AlgebraicGeometry.Space \
.presheaf_iff_isFiniteLocallyFree, which discharges that chart comparison"]
theorem presheaf_iff_isFiniteLocallyFree_iff_chartComparison (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom)
    (V : (smallEtaleRingedSite B S hS Y.1 Y.2).C) (hV : IsSurjective B S hS V.1.hom) :
    (((MorphismProperty.inverseImage
          (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf f.hom ↔
        IsFiniteLocallyFree B S hS f) ↔
      (Stacks.Morphisms.IsFiniteLocallyFree
          ((BigFppfOver.toScheme B S hS).map (hf.snd V.1.hom)) ↔
        (IsAffineHom B S hS f.hom ∧
          SheafOfModules.IsFiniteLocallyFreeOnSite
            (R := (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS Y.1 Y.2).O).over V)
            ((pushforwardStructureModule B S hS f).over V)))) :=
  iff_congr (isFiniteLocallyFree_presheaf_iff_of_etaleChart_surjectiveOnPoints
    B S hS X.2 Y.2 hf V.2 hV) (isFiniteLocallyFree_iff_over_of_isSurjective B S hS f V hV)

/-! ### The same for the rank clause of Stacks 03ZV -/

/-- **The rank form of Stacks 03ZU, granted the chart comparison at one surjective étale
chart.** For a representable `f : X ⟶ Y`, being finite locally free of rank `r` on every
represented base change is equivalent to being affine with `f_*𝒪_X` of rank `r`, which is the
rank clause of Stacks 03ZV.

Stacks 03ZU states no rank, so this carries no attribute for two reasons; the other is that
`hcross` is part of the content of the tag.  It is
`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_iff_presheaf_of_chartComparison` with the
hypothesis required only at the morphism and the chart at hand. -/
theorem presheaf_iff_isFiniteLocallyFreeOfRank_of_chartComparison_at (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (r : ℕ)
    (V : (smallEtaleRingedSite B S hS Y.1 Y.2).C) (hV : IsSurjective B S hS V.1.hom)
    (hcross : RingedSite.IsFiniteLocallyFreeOfRank
        ((smallEtaleRingedSite B S hS Y.1 Y.2).over V)
        ((pushforwardStructureModule B S hS f).over V) r ↔
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank
        ((BigFppfOver.toScheme B S hS).map (hf.snd V.1.hom)) r) :
    (MorphismProperty.inverseImage
        (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r)
        (BigFppfOver.toScheme B S hS)).presheaf f.hom ↔
      IsFiniteLocallyFreeOfRank B S hS f r := by
  have hB := isFiniteLocallyFreeOfRank_presheaf_iff_of_etaleChart_surjectiveOnPoints
    B S hS r X.2 Y.2 hf V.2 hV
  have hC := isFiniteLocallyFreeOfRank_iff_over_of_isSurjective B S hS f r V hV
  refine ⟨fun hL => hC.2 ⟨isAffineHom_of_presheaf_isFiniteLocallyFreeOfRank B S hS r hL,
    hcross.2 (hB.1 hL)⟩, fun hR => hB.2 (hcross.1 (hC.1 hR).2)⟩

/-- **The equivalence of the rank form of Stacks 03ZU for a morphism is equivalent to the rank
form of the chart comparison for that morphism.**  The rank analogue of
`AlgebraicGeometry.Space.presheaf_iff_isFiniteLocallyFree_iff_chartComparison`, and like it it
carries no hypothesis. -/
theorem presheaf_iff_isFiniteLocallyFreeOfRank_iff_chartComparison (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (r : ℕ)
    (V : (smallEtaleRingedSite B S hS Y.1 Y.2).C) (hV : IsSurjective B S hS V.1.hom) :
    (((MorphismProperty.inverseImage
          (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r)
          (BigFppfOver.toScheme B S hS)).presheaf f.hom ↔
        IsFiniteLocallyFreeOfRank B S hS f r) ↔
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank
          ((BigFppfOver.toScheme B S hS).map (hf.snd V.1.hom)) r ↔
        (IsAffineHom B S hS f.hom ∧
          RingedSite.IsFiniteLocallyFreeOfRank
            ((smallEtaleRingedSite B S hS Y.1 Y.2).over V)
            ((pushforwardStructureModule B S hS f).over V) r))) :=
  iff_congr (isFiniteLocallyFreeOfRank_presheaf_iff_of_etaleChart_surjectiveOnPoints
    B S hS r X.2 Y.2 hf V.2 hV) (isFiniteLocallyFreeOfRank_iff_over_of_isSurjective B S hS f r V hV)

end AlgebraicGeometry.Space

end
