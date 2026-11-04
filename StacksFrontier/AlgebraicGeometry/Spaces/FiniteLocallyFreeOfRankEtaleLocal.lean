module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleMorphism
public import StacksFrontier.CategoryTheory.Sites.Modules.FiniteLocallyFreeOfRankLocalOnCover

/-!
# The rank of a finite locally free morphism of algebraic spaces is étale local on the target

A morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` is finite locally free of rank `r`
when it is affine and the direct image `f_*𝒪_X` of the structure sheaf of its source has rank `r`
on the small étale ringed site of `Y`; that is Stacks 03ZV, and in this development it is
`AlgebraicGeometry.Space.IsFiniteLocallyFreeOfRank`.  This file records that the second clause
may be tested on the members of any family of étale charts covering the final object of that
site, and in particular on *one* étale chart whose structure morphism is surjective on points.

That reduction is the step which the proof of Stacks 03ZU performs with Modules on Sites,
Lemma 03DN: having chosen a surjective étale `V ⟶ Y`, the proof concludes finite local freeness
of `f_*𝒪_X` on `Y_{spaces,étale}` from finite local freeness of its restriction to `V` alone.
Here the same reduction is carried out for a fixed rank.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_iff_exists_cover_charts`: a morphism of
  algebraic spaces is finite locally free of rank `r` exactly when it is affine and the direct
  image of the structure sheaf of its source has rank `r` on each member of some family of étale
  charts covering the final object of the small étale site of the target.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_iff_over_of_isSurjective`: the same with the
  covering family a single étale chart whose structure morphism is surjective on points.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_iff_exists_surjective_chart`: the same with
  the chart existentially quantified, which is the form that cannot be vacuous.
* `AlgebraicGeometry.Space.isFiniteLocallyFree_iff_over_of_isSurjective`: the unranked companion
  of the two previous statements, which is the form Stacks 03ZU itself uses.
* `AlgebraicGeometry.Space.isAffineHom_of_presheaf_isFiniteLocallyFreeOfRank`: a representable
  morphism all of whose represented base changes are finite locally free of rank `r` is affine.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_iff_presheaf_of_chartComparison`: **the rank
  form of Stacks 03ZU, granted one explicitly named chart comparison** `hcross` — everything
  else it needs is proved.

## Implementation notes

Neither statement carries an attribute.  Stacks 03ZW states no rank, so the rank statements of
this cone are untagged, as they already are in
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeEtaleLocal`; and the locality used is the
rank clause of Stacks 0409, not one of the conditions of Stacks 03DL that Stacks 03DN is about.

The restriction of the direct image to a chart is restriction `SheafOfModules.over` to the slice
of the small étale site of `Y` at the chart, over the localized ringed site
`AlgebraicGeometry.RingedSite.over` of Stacks 04IX — the same reading of Stacks' Equation 03LW as
in `AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_over_of_isSurjective`, whose shape these
statements follow.  It is **not** the restriction to the Zariski site of the chart scheme
(`AlgebraicGeometry.Space.restrictToChart`), and no statement here compares the two.

*What the rank form of Stacks 03ZU still owes, after this file.*  Stacks 03ZU itself states no
rank, and the unranked statement is proved downstream of this file, as
`AlgebraicGeometry.Space.presheaf_iff_isFiniteLocallyFree` in
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRepresentableChart`; what follows concerns
the rank refinement of Stacks 03ZV, which that route does not reach.  Condition (1) of Stacks 03ZW
at rank `r` — `f` representable with every represented base change finite locally free of rank
`r` — is related to the base change over one surjective étale chart by
`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_presheaf_iff_of_etaleChart_surjectiveOnPoints`,
and the rank clause of condition (2) is related to the restriction of `f_*𝒪_X` over one surjective
étale chart by `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_iff_over_of_isSurjective` below.
What is missing between them is a single comparison at the chart: the identification of
`(f_*𝒪_X)|_V`, a module on the slice of the small étale site of `Y` at `V`, with the direct image
`Stacks.Morphisms.pushforwardStructureSheaf` of the structure sheaf along the base change
`V ×_Y X ⟶ V` of schemes — read on the small étale site of `V` through
`AlgebraicGeometry.SmallEtale.associatedModule` — *carrying the rank*.  Without the rank the
identification is `AlgebraicGeometry.Space.overPushforwardStructureModuleIsoSliceAssociatedModule`
and the transport of finite local freeness across it is
`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_sliceAssociatedModule_iff`, the clause 03DL (2)
of Stacks 05VG carried to the slice; so the structure sheaves on the two sides of the Stacks 04M0
site equivalence `AlgebraicGeometry.Space.smallEtaleEquivalenceOverChart` are matched after all,
and the obstruction the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart` record is not one.  With the rank
nothing in the tree states the comparison: rank is transported only along equivalences of ringed
sites (`AlgebraicGeometry.RingedSite.isFiniteLocallyFreeOfRank_reindex_iff`), which covers three
of the four links of the unranked comparison but not the passage across `𝓕 ↦ 𝓕ᵃ`, for which no
rank analogue of `AlgebraicGeometry.SmallEtale.isFiniteLocallyFreeOnSite_associatedModule_iff`
exists.  It is *not* the Stacks 03DX(2) essential surjectivity that other results here are
conditional on: only the module in the image of `(-)ᵃ` is involved, and the degree-zero flat base
change `Stacks.Sites.affineAssociatedBaseChangeIso` of Stacks 02KH is available.

That the rank comparison is the *only* thing still owed is not an estimate:
`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_iff_presheaf_of_chartComparison` carries it as
the named hypothesis `hcross`, in the usual style for a missing input, and derives the rank
form of Stacks 03ZU from it with nothing else unproved.  `hcross` relates the two predicates
directly, at a chart, with no reference to the associated module — that formulation is one way to
supply it and the paragraph above is another.  No attribute is carried there either: a
hypothesis-carrying form of a tag must not claim the tag.

The chart hypothesis is not vacuous: every algebraic space has an étale chart whose structure
morphism is surjective on points, by
`AlgebraicGeometry.Space.exists_surjective_smallEtale_chart`, which is what
`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_iff_exists_surjective_chart` uses.  The rank
condition itself is not vacuous either: the structure sheaf of a ringed site has rank `1`, by
`AlgebraicGeometry.RingedSite.isFiniteLocallyFreeOfRank_unit`.

## References

* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03ZU](https://stacks.math.columbia.edu/tag/03ZU)
* [Stacks Project, Tag 03ZV](https://stacks.math.columbia.edu/tag/03ZV)
* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- **The rank is étale local on the target.** A morphism of algebraic spaces over `S` is finite
locally free of rank `r` exactly when it is affine and the direct image of the structure sheaf of
its source has rank `r` over each member of some family of étale charts covering the final object
of the small étale site of the target. -/
theorem isFiniteLocallyFreeOfRank_iff_exists_cover_charts (f : X ⟶ Y) (r : ℕ) :
    IsFiniteLocallyFreeOfRank B S hS f r ↔
      IsAffineHom B S hS f.hom ∧
        ∃ (I : Type (u + 1)) (V : I → (smallEtaleRingedSite B S hS Y.1 Y.2).C),
          (smallEtaleRingedSite B S hS Y.1 Y.2).J.CoversTop V ∧
            ∀ i : I, RingedSite.IsFiniteLocallyFreeOfRank
              ((smallEtaleRingedSite B S hS Y.1 Y.2).over (V i))
              ((pushforwardStructureModule B S hS f).over (V i)) r := by
  rw [isFiniteLocallyFreeOfRank_iff]
  exact and_congr_right fun _ =>
    RingedSite.isFiniteLocallyFreeOfRank_iff_exists_cover _ _ r

/-- **The rank may be tested on one surjective étale chart.** A morphism of algebraic spaces
over `S` is finite locally free of rank `r` exactly when it is affine and the direct image of the
structure sheaf of its source has rank `r` over one étale chart of the target whose structure
morphism is surjective on points.

This is the shape in which the proof of Stacks 03ZU uses Modules on Sites, Lemma 03DN. -/
theorem isFiniteLocallyFreeOfRank_iff_over_of_isSurjective (f : X ⟶ Y) (r : ℕ)
    (V : (smallEtaleRingedSite B S hS Y.1 Y.2).C) (hsurj : IsSurjective B S hS V.1.hom) :
    IsFiniteLocallyFreeOfRank B S hS f r ↔
      IsAffineHom B S hS f.hom ∧
        RingedSite.IsFiniteLocallyFreeOfRank
          ((smallEtaleRingedSite B S hS Y.1 Y.2).over V)
          ((pushforwardStructureModule B S hS f).over V) r := by
  rw [isFiniteLocallyFreeOfRank_iff]
  refine and_congr_right fun _ => ⟨fun h =>
    RingedSite.IsFiniteLocallyFreeOfRank.over _ _ h V, fun h => ?_⟩
  exact (RingedSite.isFiniteLocallyFreeOfRank_iff_exists_cover _ _ r).2
    ⟨PUnit.{u + 2}, fun _ => V,
      SmallEtale.coversTop_of_isSurjective B S hS Y.1 Y.2 V hsurj, fun _ => h⟩

/-- **The rank may be tested on some surjective étale chart.** A morphism of algebraic spaces
over `S` is finite locally free of rank `r` exactly when it is affine and the direct image of the
structure sheaf of its source has rank `r` over *some* étale chart of the target whose structure
morphism is surjective on points.

The existential is not vacuous, and that is what this statement adds to
`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_iff_over_of_isSurjective`: every algebraic
space has such a chart, by `AlgebraicGeometry.Space.exists_surjective_smallEtale_chart`. -/
theorem isFiniteLocallyFreeOfRank_iff_exists_surjective_chart (f : X ⟶ Y) (r : ℕ) :
    IsFiniteLocallyFreeOfRank B S hS f r ↔
      IsAffineHom B S hS f.hom ∧
        ∃ V : (smallEtaleRingedSite B S hS Y.1 Y.2).C, IsSurjective B S hS V.1.hom ∧
          RingedSite.IsFiniteLocallyFreeOfRank
            ((smallEtaleRingedSite B S hS Y.1 Y.2).over V)
            ((pushforwardStructureModule B S hS f).over V) r := by
  obtain ⟨V₀, hV₀⟩ := exists_surjective_smallEtale_chart B S hS Y.1 Y.2
  refine ⟨fun h => ⟨h.1.1, V₀, hV₀, ?_⟩, fun h => ?_⟩
  · exact ((isFiniteLocallyFreeOfRank_iff_over_of_isSurjective B S hS f r V₀ hV₀).1 h).2
  · obtain ⟨haff, V, hV, hrank⟩ := h
    exact (isFiniteLocallyFreeOfRank_iff_over_of_isSurjective B S hS f r V hV).2 ⟨haff, hrank⟩

/-- **Finite local freeness may be tested on one surjective étale chart.** A morphism of
algebraic spaces over `S` is finite locally free exactly when it is affine and the direct image
of the structure sheaf of its source is finite locally free over one étale chart of the target
whose structure morphism is surjective on points.

This is the unranked companion of
`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_iff_over_of_isSurjective`, and it is the
shape in which the proof of Stacks 03ZU uses Modules on Sites, Lemma 03DN. -/
theorem isFiniteLocallyFree_iff_over_of_isSurjective (f : X ⟶ Y)
    (V : (smallEtaleRingedSite B S hS Y.1 Y.2).C) (hsurj : IsSurjective B S hS V.1.hom) :
    IsFiniteLocallyFree B S hS f ↔
      IsAffineHom B S hS f.hom ∧
        SheafOfModules.IsFiniteLocallyFreeOnSite
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS Y.1 Y.2).O).over V)
          ((pushforwardStructureModule B S hS f).over V) := by
  refine and_congr_right fun _ => ⟨fun h => h.over V, fun h => ?_⟩
  exact (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isFiniteLocallyFreeOnSite
    (smallEtaleRingedSite B S hS Y.1 Y.2) (pushforwardStructureModule B S hS f)).2
    ⟨PUnit.{u + 2}, fun _ => V,
      SmallEtale.coversTop_of_isSurjective B S hS Y.1 Y.2 V hsurj, fun _ => h⟩

/-- A representable morphism of algebraic spaces over `S` all of whose represented base changes
are finite locally free of rank `r` is affine.

This is Stacks 03WG, (1) implies (2), `AlgebraicGeometry.Space.isAffineHom_of_presheaf`, applied
after weakening the property along `Stacks.Morphisms.IsFiniteLocallyFreeOfRank.toIsAffineHom`. -/
theorem isAffineHom_of_presheaf_isFiniteLocallyFreeOfRank
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G} (r : ℕ)
    (h : (MorphismProperty.inverseImage
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r)
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    IsAffineHom B S hS f := by
  refine isAffineHom_of_presheaf ⟨h.rep, ?_⟩
  intro a b g fst snd sq
  have hq : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((BigFppfOver.toScheme B S hS).map snd) r := h.property g fst snd sq
  exact hq.toIsAffineHom

/-- **The rank form of Stacks 03ZU, granted the chart comparison.** For a representable morphism
`f : X ⟶ Y` of algebraic spaces over `S`, being finite locally free of rank `r` in the sense of
Stacks 03ZV — affine with `f_*𝒪_X` of rank `r` on the small étale ringed site of `Y` — is
equivalent to being representable with every represented base change finite locally free of
rank `r`, which is condition (1) of Stacks 03ZW.

The one input that is **not** proved is `hcross`: that at an étale chart `V` of `Y` the rank of
the restriction of `f_*𝒪_X` to the slice at `V` agrees with the rank of the base change of `f`
over `V` as a morphism of schemes.  Everything else is discharged —
`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_iff_over_of_isSurjective` on the left,
`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_presheaf_iff_of_etaleChart_surjectiveOnPoints`
on the right, `AlgebraicGeometry.Space.exists_surjective_smallEtale_chart` for the chart, and
`AlgebraicGeometry.Space.isAffineHom_of_presheaf_isFiniteLocallyFreeOfRank` for the affineness
conjunct — so this statement measures exactly what Stacks 03ZU still owes.

It carries no attribute: a universe-specialized, hypothesis-carrying form of a tag must not
claim the tag. -/
theorem isFiniteLocallyFreeOfRank_iff_presheaf_of_chartComparison
    (hcross : ∀ {X' Y' : AlgebraicSpaces B S hS} (g : X' ⟶ Y')
      (hg : yoneda.relativelyRepresentable g.hom) (r : ℕ)
      (V : (smallEtaleRingedSite B S hS Y'.1 Y'.2).C),
      (RingedSite.IsFiniteLocallyFreeOfRank
          ((smallEtaleRingedSite B S hS Y'.1 Y'.2).over V)
          ((pushforwardStructureModule B S hS g).over V) r ↔
        Stacks.Morphisms.IsFiniteLocallyFreeOfRank
          ((BigFppfOver.toScheme B S hS).map (hg.snd V.1.hom)) r))
    (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom) (r : ℕ) :
    IsFiniteLocallyFreeOfRank B S hS f r ↔
      (MorphismProperty.inverseImage
        (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r)
        (BigFppfOver.toScheme B S hS)).presheaf f.hom := by
  obtain ⟨V, hV⟩ := exists_surjective_smallEtale_chart B S hS Y.1 Y.2
  have hB := isFiniteLocallyFreeOfRank_presheaf_iff_of_etaleChart_surjectiveOnPoints
    B S hS r X.2 Y.2 hf V.2 hV
  have hC := isFiniteLocallyFreeOfRank_iff_over_of_isSurjective B S hS f r V hV
  refine ⟨fun hL => hB.2 ((hcross f hf r V).1 (hC.1 hL).2), fun hR => ?_⟩
  exact hC.2 ⟨isAffineHom_of_presheaf_isFiniteLocallyFreeOfRank B S hS r hR,
    (hcross f hf r V).2 (hB.1 hR)⟩

end AlgebraicGeometry.Space

end
