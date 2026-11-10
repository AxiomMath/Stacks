module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ConstructibleCoequalizerPresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ConstructibleQuasiCompact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.EtaleObjectStratification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.SetSheafPresentationColimits
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.JointlySurjectiveFamilyFaithful
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CompactConstructibleSets
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SurjectiveMorphismStalkDescent
public import StacksFrontier.CategoryTheory.Sites.CoequalizerOfEpi
import StacksCore.Tactic.StacksAttribute

/-!
# Constructibility of an étale sheaf descends along a surjective morphism

Let `f : X ⟶ Y` be a surjective morphism of quasi-compact and quasi-separated schemes and let
`ℱ` be a sheaf of sets on `Y_étale`. Then `ℱ` is constructible as soon as `f⁻¹ℱ` is; together
with Stacks 095G, which is the converse and needs neither surjectivity nor quasi-compactness,
this is part (1) of Stacks 095Q.

The argument is the source's. Write `ℱ = colim_i ℱ_i` as a filtered colimit of constructible
sheaves (Stacks 03SA (1)). Inverse image is a left adjoint, so `f⁻¹ℱ = colim_i f⁻¹ℱ_i`, and
`f⁻¹ℱ` is constructible by assumption, hence a compact object of the topos on `X` (Stacks 09Z4).
The identity of `f⁻¹ℱ` therefore factors through some `f⁻¹ℱ_i`, which makes the coprojection
`f⁻¹ℱ_i ⟶ f⁻¹ℱ` a split epimorphism; surjectivity of `f` carries that back to `Y`, by
`AlgebraicGeometry.epi_of_epi_smallEtalePullback`, so `ℱ_i ⟶ ℱ` is an epimorphism. Thus `ℱ` is a
quotient of a constructible sheaf.

Applying this twice finishes the proof: the kernel pair `𝒢 ×_ℱ 𝒢` of such a quotient
`p : 𝒢 ⟶ ℱ` has constructible inverse image, because inverse image is left exact and
constructible sheaves of sets are closed under finite limits (Stacks 03RZ (1)), so it is in turn
a quotient of a constructible `ℋ`. An epimorphism of sheaves of sets is a regular epimorphism,
so `ℱ` is the coequalizer of the two composites `ℋ ⟶ 𝒢 ×_ℱ 𝒢 ⇉ 𝒢`, and a finite colimit of
constructible sheaves is constructible by Stacks 03RZ (1) again.

## Hypotheses that are granted rather than proved

Of the two lemmas of the source that the argument cites, the library's Stacks 03SA (1),
`AlgebraicGeometry.exists_isFilteredColimit_isConstructibleSetSheaf`, is used here with **both**
of its hypotheses discharged: its Stacks 03S0 from
`AlgebraicGeometry.etaleFiniteStratificationExists`, and its Stacks 093C (1) in the coequalizer
spelling `AlgebraicGeometry.SetSheavesAreFilteredColimitsOfPresentations` from
`AlgebraicGeometry.setSheavesAreFilteredColimitsOfPresentations`, which proves that spelling for
the small étale site of any scheme whatsoever. One hypothesis of the other lemma remains:

* **Stacks 09Y9** for sheaves of sets, as `h09Y9`: the hypothesis of
  `AlgebraicGeometry.isFinitelyPresentable_of_isConstructibleSetSheaf`, the library's
  Stacks 09Z4. It is a statement about the source `X` of `f`. The main result
  `AlgebraicGeometry.isConstructibleSetSheaf_pullback_iff` does not grant it: it derives it from
  Stacks 0245, as its docstring records.

It does not mention `f`, so it cannot supply the content of the statements below: what is proved
here is the descent of constructibility along a surjection.

## Main results

* `AlgebraicGeometry.exists_epi_isConstructibleSetSheaf_of_pullback` — a sheaf of sets on
  `Y_étale` with constructible inverse image is a quotient of a constructible sheaf of sets.
* `AlgebraicGeometry.isConstructibleSetSheaf_of_isConstructibleSetSheaf_pullback` and
  `AlgebraicGeometry.isConstructibleSetSheaf_pullback_iff` — the converse implication and the
  resulting equivalence, the latter no longer taking Stacks 0245 as a hypothesis.
* `AlgebraicGeometry.isConstructibleSetSheaf_pullback_iff_unconditional` — **Stacks 095Q (1)**,
  the same equivalence with nothing assumed. Stacks 09Y9 is supplied there from
  `isConstructibleSetSheaf_iff_hasFiniteQCSRepresentableCoequalizerPresentation_unconditional`,
  which does not pass through Stacks 0245 at all.

## Implementation notes

Only part (1) of the tag is proved here; the two other parts need different inputs, for reasons
that have nothing to do with the argument above. Part (2) rests on Stacks 03SA (2), the
presentation of an arbitrary abelian sheaf as a filtered colimit of constructible ones, which is
not the part of Stacks 03SA that
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ColimitOfConstructibles` carries;
part (3) on the reflection of epimorphisms of sheaves of `Λ`-modules along a surjective
morphism, which is the module case of the inverse-image comparison of étale stalks, Stacks 03Q1.

## References

* [Stacks Project, Tag 095Q](https://stacks.math.columbia.edu/tag/095Q)
* [Stacks Project, Tag 095G](https://stacks.math.columbia.edu/tag/095G)
* [Stacks Project, Tag 03SA](https://stacks.math.columbia.edu/tag/03SA)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
* [Stacks Project, Tag 09Z4](https://stacks.math.columbia.edu/tag/09Z4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts
attribute [local instance 2000] Sheaf.instHasFiniteColimits
attribute [local instance] Cardinal.fact_isRegular_aleph0

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)

/-- **A sheaf of sets with constructible inverse image is a quotient of a constructible sheaf.**
Let `f : X ⟶ Y` be a surjective morphism of quasi-compact quasi-separated schemes and `ℱ` a
sheaf of sets on `Y_étale` whose inverse image along `f` is constructible. Then there is a
constructible sheaf of sets on `Y_étale` and an epimorphism from it onto `ℱ`.

This is the step of the proof of Stacks 095Q (1) at which surjectivity of `f` is used, and the
only one: `ℱ` is a filtered colimit of constructible sheaves, the inverse image of that colimit
is essentially constant because `f⁻¹ℱ` is a compact object, and surjectivity of `f` carries the
resulting epimorphism back to `Y`. -/
public theorem exists_epi_isConstructibleSetSheaf_of_pullback
    (hf : Function.Surjective (B.inclusion.map f).base)
    (hXc : CompactSpace X.obj) (hXq : QuasiSeparatedSpace X.obj)
    (hYc : CompactSpace Y.obj) (hYq : QuasiSeparatedSpace Y.obj)
    (h09Y9 : ∀ G : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)),
      IsConstructibleSetSheaf B X G → HasFiniteQCSRepresentableCoequalizerPresentation B X G)
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) (Type (u + 1)))
    (hF : IsConstructibleSetSheaf B X ((smallEtaleSetPullback B f).obj F)) :
    ∃ (G : Sheaf (SmallEtale.topology B Y.obj Y.property) (Type (u + 1))) (p : G ⟶ F),
      IsConstructibleSetSheaf B Y G ∧ Epi p := by
  have hadj := (smallEtaleBaseChange B f).sheafAdjunctionContinuous (Type (u + 1))
    (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property)
  have := hadj.leftAdjoint_preservesColimits
  have hxc : CompactSpace X.obj := hXc
  have hxq : QuasiSeparatedSpace X.obj := hXq
  obtain ⟨I, hI, hfilt, D, ι, ⟨hcolim⟩, hD⟩ :=
    exists_isFilteredColimit_isConstructibleSetSheaf B Y
      (setSheavesAreFilteredColimitsOfPresentations B Y)
      (etaleFiniteStratificationExists B) hYc hYq F
  have hpres : IsFinitelyPresentable.{u + 1} ((smallEtaleSetPullback B f).obj F) :=
    isFinitelyPresentable_of_isConstructibleSetSheaf B X h09Y9 _ hF
  have : IsCardinalPresentable
      ((smallEtaleSetPullback B f).mapCocone (Cocone.mk F ι)).pt Cardinal.aleph0.{u + 1} :=
    hpres
  have : IsCardinalFiltered I Cardinal.aleph0.{u + 1} :=
    (isCardinalFiltered_aleph0_iff I).2 hfilt
  obtain ⟨i, r, hr⟩ := IsCardinalPresentable.exists_hom_of_isColimit
    (κ := Cardinal.aleph0.{u + 1})
    (isColimitOfPreserves (smallEtaleSetPullback B f) hcolim) (𝟙 _)
  have hsplit : IsSplitEpi ((smallEtaleSetPullback B f).map (ι.app i)) := ⟨⟨r, hr⟩⟩
  exact ⟨D.obj i, ι.app i, hD i,
    epi_of_epi_smallEtalePullback B f hf (ι.app i) hsplit.epi⟩

/-- **Stacks 095Q, part (1), the converse implication.** Let `f : X ⟶ Y` be a surjective
morphism of quasi-compact quasi-separated schemes and `ℱ` a sheaf of sets on `Y_étale` whose
inverse image `f⁻¹ℱ` is constructible. Then `ℱ` is constructible.

`AlgebraicGeometry.exists_epi_isConstructibleSetSheaf_of_pullback` applied to `ℱ` produces a
constructible `𝒢` with an epimorphism `p : 𝒢 ⟶ ℱ`; applied to the kernel pair of `p`, whose
inverse image is a finite limit of constructible sheaves, it produces a constructible `ℋ`
surjecting onto that kernel pair. Then `ℱ` is the coequalizer of `ℋ ⇉ 𝒢` and so is
constructible. -/
public theorem isConstructibleSetSheaf_of_isConstructibleSetSheaf_pullback
    (hf : Function.Surjective (B.inclusion.map f).base)
    (hXc : CompactSpace X.obj) (hXq : QuasiSeparatedSpace X.obj)
    (hYc : CompactSpace Y.obj) (hYq : QuasiSeparatedSpace Y.obj)
    (h09Y9 : ∀ G : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)),
      IsConstructibleSetSheaf B X G → HasFiniteQCSRepresentableCoequalizerPresentation B X G)
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) (Type (u + 1)))
    (hF : IsConstructibleSetSheaf B X ((smallEtaleSetPullback B f).obj F)) :
    IsConstructibleSetSheaf B Y F := by
  obtain ⟨G, p, hG, hp⟩ := exists_epi_isConstructibleSetSheaf_of_pullback B f hf hXc hXq hYc hYq
    h09Y9 F hF
  have := hp
  -- The kernel pair of `p` has constructible inverse image: inverse image is left exact and
  -- constructible sheaves of sets are closed under finite limits.
  have hGpull : IsConstructibleSetSheaf B X ((smallEtaleSetPullback B f).obj G) :=
    isConstructibleFiniteSheaf_pullback B f G hG
  have hRpull : IsConstructibleSetSheaf B X
      ((smallEtaleSetPullback B f).obj (pullback p p)) := by
    refine isConstructibleSetSheaf_congr B X
      (preservesLimitIso (smallEtaleSetPullback B f) (cospan p p)).symm
      (isConstructibleSetSheaf_limit B X (cospan p p ⋙ smallEtaleSetPullback B f) ?_)
    rintro (_ | _ | _)
    exacts [hF, hGpull, hGpull]
  -- The surjection onto the kernel pair is produced with the vertex of the chosen pullback cone
  -- as its target, which is the shape the coequalizer presentation below consumes.
  obtain ⟨H, q, hH, hq⟩ := exists_epi_isConstructibleSetSheaf_of_pullback B f hf hXc hXq hYc hYq
    h09Y9 (PullbackCone.mk (pullback.fst p p) (pullback.snd p p) pullback.condition).pt hRpull
  have := hq
  -- An epimorphism of sheaves of sets is a regular epimorphism, so `F` is the coequalizer.
  obtain ⟨e⟩ := Sheaf.nonempty_coequalizer_iso_of_epi_of_epi p
    (PullbackCone.mk (pullback.fst p p) (pullback.snd p p) pullback.condition)
    (pullbackIsPullback p p) q
  refine isConstructibleSetSheaf_congr B Y e ?_
  refine isConstructibleSetSheaf_colimit B Y (parallelPair _ _) ?_
  rintro (_ | _)
  exacts [hH, hG]

/-- The equivalence of Stacks 095Q (1), shared by its two statements. -/
private theorem isConstructibleSetSheaf_pullback_iff_of_surjective
    (hf : Function.Surjective (B.inclusion.map f).base)
    (hXc : CompactSpace X.obj) (hXq : QuasiSeparatedSpace X.obj)
    (hYc : CompactSpace Y.obj) (hYq : QuasiSeparatedSpace Y.obj)
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) (Type (u + 1))) :
    IsConstructibleSetSheaf B Y F ↔
      IsConstructibleSetSheaf B X ((smallEtaleSetPullback B f).obj F) := by
  have hxc : CompactSpace X.obj := hXc
  have hxq : QuasiSeparatedSpace X.obj := hXq
  have h09Y9 : ∀ G : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)),
      IsConstructibleSetSheaf B X G →
        HasFiniteQCSRepresentableCoequalizerPresentation B X G := fun G =>
    (isConstructibleSetSheaf_iff_hasFiniteQCSRepresentableCoequalizerPresentation_unconditional
      B X G).1
  exact ⟨fun hF => isConstructibleFiniteSheaf_pullback B f F hF,
    isConstructibleSetSheaf_of_isConstructibleSetSheaf_pullback B f hf hXc hXq hYc hYq
      h09Y9 F⟩

/-- **Stacks 095Q, part (1).** Let `f : X ⟶ Y` be a surjective morphism of quasi-compact and
quasi-separated schemes and let `ℱ` be a sheaf of sets on `Y_étale`. Then `ℱ` is constructible
if and only if `f⁻¹ℱ` is constructible.

The forward implication is Stacks 095G, `AlgebraicGeometry.isConstructibleFiniteSheaf_pullback`,
and needs neither surjectivity of `f` nor quasi-compactness. The converse is
`AlgebraicGeometry.isConstructibleSetSheaf_of_isConstructibleSetSheaf_pullback`.

Stacks 0245, which does not mention `f`, was once a hypothesis `hdesc` here; the proof never
used it, and it has been removed.
Both hypotheses of the library's Stacks 03SA (1) are **discharged** here:
Stacks 03S0 by `AlgebraicGeometry.etaleFiniteStratificationExists` of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Constructible/EtaleObjectStratification.lean`,
and Stacks 093C (1), in the spelling
`AlgebraicGeometry.SetSheavesAreFilteredColimitsOfPresentations`, by
`AlgebraicGeometry.setSheavesAreFilteredColimitsOfPresentations` of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Constructible/SetSheafPresentationColimits.lean`,
which assumes nothing at all about the scheme.

Stacks 09Y9 for sheaves of sets, the hypothesis of the library's Stacks 09Z4, is **not** granted
here: it is the library's Stacks 09Y9,
`isConstructibleSetSheaf_iff_hasFiniteQCSRepresentableCoequalizerPresentation_unconditional`,
which assumes nothing beyond quasi-compactness and quasi-separatedness of `X`.

Stacks 0245 is the only granted hypothesis, and the proof below does not use it.

**Why it cannot be discharged from the library's Stacks 0245.** Stacks 0245 *is* carried, twice,
as `AlgebraicGeometry.DescentData.isFamilyEffective_of_isAffineHom` of
`StacksFrontier/AlgebraicGeometry/Descent/AffineFpqcFamilyEffective.lean` and
`AlgebraicGeometry.DescentData.isFamilyEffective_of_forall_isAffineHom` of
`StacksFrontier/AlgebraicGeometry/Descent/AffineHomFpqcDescent.lean`. Those are statements about
fpqc descent **data of schemes** being effective when the structure morphisms are affine, whereas
`EtaleDescentForFiniteEtaleRepresentability` is about **sheaves** on a small étale site being
representable by an object with finite structure morphism. Translating between the two is
Stacks 02W5 (2), and that is where the obstruction lies, on the category-theoretic and not the
geometric side.

Two inputs of the translation are available: an étale covering family is an fpqc covering family
by `AlgebraicGeometry.Scheme.etalePrecoverage_le_fpqcPrecoverage`, and a finite morphism is
affine by `AlgebraicGeometry.Space.isFinite_le_isAffineHom`. The index universes can also be
reconciled, by passing to the subfamily indexed by the points of `X`, whose carrier is a
`Type u`, rather than by refining the covering. What fails is Stacks 02W5 (2) itself:
`CategoryTheory.GrothendieckTopology.effectiveDescentData_toDescentData_iff` of
`StacksFrontier/CategoryTheory/Sites/Descent/LocallyRepresentableSheaves.lean` is stated for
`Sheaf (J.over S) (Type v)` with the plain Yoneda embedding and requires
`HasLimitsOfSize.{max u v, max u v} (Type v)`. The small étale site of a `BigEtaleSite` has its
objects in `Type (u + 1)` and its morphisms in `Type u`, so that instance specialises to
`HasLimitsOfSize.{u + 1, u + 1} (Type u)`, which is false; and the sheaves here are
`Type (u + 1)`-valued with representability through `Sheaf.sheafifiedYoneda`, the sheafified
`ULift` Yoneda embedding, not through plain Yoneda.

The failure is specific to the representability layer. The ambient glueing equivalence of
Stacks 04TS, `CategoryTheory.GrothendieckTopology.isEquivalence_toDescentData_pseudofunctorOver`
of `StacksFrontier/CategoryTheory/Sites/Glueing/GlueingSheaves.lean`, does apply at this site, since
its coefficient category is arbitrary and the instance it needs is
`HasLimitsOfSize.{u + 1, u + 1} (Type (u + 1))`. So descent data of sheaves can be glued here;
only the identification of a glued sheaf with a representable one is unavailable.

**That universe obstruction has since been removed.** Stacks 02W5 (2) is now also available for
`Type (max u v)`-valued sheaves and the sheafified `ULift` Yoneda embedding, as
`CategoryTheory.GrothendieckTopology.effectiveDescentDataSheafified_toDescentData_iff` of
`StacksFrontier/CategoryTheory/Sites/Descent/LocallyRepresentableSheavesSheafified.lean`, and it
carries **no** `HasLimitsOfSize` hypothesis at all — at that universe the instance is global. It
instantiates at the small étale site of a `BigEtaleSite` with `Type (u + 1)`-valued sheaves,
subcanonicality coming from `AlgebraicGeometry.SmallEtale.topology_subcanonical`. Only one step of
the original proof was universe-sensitive, the identification of the essential image of Yoneda
into sheaves with representability of the underlying presheaf, and
`Functor.RepresentableBy.equivUliftYonedaIso` replaces it; Stacks 04TS transfers verbatim.

So what remains between here and Stacks 0245 in the shape used above is no longer a false
instance, and it is no longer the transition data either.

**The transition isomorphisms are manufacturable.** The hypothesis of Stacks 0245 does not
merely supply an unrelated isomorphism over each member of the covering: the
sheaf `ℱ` compares them itself: its restriction to an overlap is canonically either iterated
pullback, and the pullback of a sheafified representable is the sheafified representable of the
base change. Two declarations already in the library suffice, and their composite elaborates —
`AlgebraicGeometry.smallEtaleSheafPullbackCompIso` of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/SmallEtalePullbackFunctoriality.lean` (Stacks
021J), which transports a presentation along `h ≫ g` to one along `h` of the presentation along
`g`, and `CategoryTheory.Sheaf.sheafifiedYonedaCompSheafPullbackIso` of
`StacksFrontier/CategoryTheory/Sites/Continuous/PullbackOfSheafifiedYoneda.lean` (Stacks 04D3 at the
sheafified `ULift` universe), which identifies the pullback of a sheafified representable with the
sheafified representable of the base change. Instantiated at the two projections of `Y i ×_X Y j`
that composite *is* the comparison over the overlap. The module documentation of
`EtaleLocalRepresentability.lean`, under
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/FiniteLocallyConstant/`, describes the same
mechanism.

What is actually missing is bookkeeping, in two steps, neither of which is mathematics. First, an
equivalence between sheaves on a site and sheaves on its slice over a terminal object, compatible
with `Sheaf.sheafifiedYoneda`; without it the sheaf `ℱ` of the statement above cannot even be
handed to Stacks 02W5 (2), whose argument is a `Sheaf ((SmallEtale.topology B X).over
(SmallEtale.final B X))`. The library carries no such equivalence for plain sheaves. Second, an
identification of the slice of the small étale site with the small étale site of the slice,
carrying `GrothendieckTopology.overMapPullback` to `smallEtaleBaseChange … |>.sheafPullback`; this
one is half-present, as `AlgebraicGeometry.smallEtaleEquivalenceOver` and
`AlgebraicGeometry.smallEtaleEquivalenceOver_topology`, but the comparison of the two pullbacks is
not, and it is what connects the hypothesis of Stacks 0245 to the componentwise representability
that Stacks 02W5 (2) consumes. Descent of finiteness along a covering sieve, Stacks 02L6, is then
needed to see that the glued object is finite. The ring-theoretic core of the affine case is in the
tree as `Stacks.AlgebraDescent.exists_finiteEtale_spec_of_sheafTransition`, which does **not** take
the transition as an input — it derives it, by exactly the mechanism above — but does take as
hypotheses the three functoriality-of-restriction equations `h₀₁`, `h₁₂`, `h₀₂`, which have no
producer.

There is also a second and probably cheaper route, which does not pass through Stacks 02W5 (2) at
all. `AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_isFinite_inf_etale` of
`StacksFrontier/AlgebraicGeometry/Descent/FiniteEtaleCoveringSieveDescent.lean` is *unconditional*
effective descent of representability by a finite étale morphism along the covering sieves of the
big fppf site — that is, Stacks 0245's content, already proved. It is stated on `BigFppfOver` with
`Type u`-valued presheaves and plain `yoneda`, so it is not usable here only because the library
carries no comparison between that site and the small étale site of a `BigEtaleSite`. Supplying
that one comparison would discharge the hypothesis outright, instead of re-deriving descent
through the two bridges above.

Parts (2) and (3) of the tag are not proved here.

The tag is registered on `AlgebraicGeometry.isConstructibleSetSheaf_pullback_iff_unconditional`
below, which states the same equivalence, not on this declaration. -/
public theorem isConstructibleSetSheaf_pullback_iff
    (hf : Function.Surjective (B.inclusion.map f).base)
    (hXc : CompactSpace X.obj) (hXq : QuasiSeparatedSpace X.obj)
    (hYc : CompactSpace Y.obj) (hYq : QuasiSeparatedSpace Y.obj)
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) (Type (u + 1))) :
    IsConstructibleSetSheaf B Y F ↔
      IsConstructibleSetSheaf B X ((smallEtaleSetPullback B f).obj F) := by
  exact isConstructibleSetSheaf_pullback_iff_of_surjective B f hf hXc hXq hYc hYq F

/-- **Stacks 095Q, part (1).** Let `f : X ⟶ Y` be a surjective morphism of quasi-compact and
quasi-separated schemes and let `ℱ` be a sheaf of sets on `Y_étale`. Then `ℱ` is constructible
if and only if `f⁻¹ℱ` is constructible.

Nothing is assumed. The forward implication is Stacks 095G,
`AlgebraicGeometry.isConstructibleFiniteSheaf_pullback`, and needs neither surjectivity of `f`
nor quasi-compactness. The converse is
`AlgebraicGeometry.isConstructibleSetSheaf_of_isConstructibleSetSheaf_pullback`, whose Stacks 09Y9
is supplied from
`isConstructibleSetSheaf_iff_hasFiniteQCSRepresentableCoequalizerPresentation_unconditional`,
which assumes nothing beyond quasi-compactness and quasi-separatedness of `X` and does not use
Stacks 0245. Both hypotheses of the library's Stacks 03SA (1) are discharged as described above.

Parts (2) and (3) of the tag are not proved here. -/
@[stacks 095Q "part (1), sheaves of sets"]
public theorem isConstructibleSetSheaf_pullback_iff_unconditional
    (hf : Function.Surjective (B.inclusion.map f).base)
    (hXc : CompactSpace X.obj) (hXq : QuasiSeparatedSpace X.obj)
    (hYc : CompactSpace Y.obj) (hYq : QuasiSeparatedSpace Y.obj)
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) (Type (u + 1))) :
    IsConstructibleSetSheaf B Y F ↔
      IsConstructibleSetSheaf B X ((smallEtaleSetPullback B f).obj F) := by
  exact isConstructibleSetSheaf_pullback_iff_of_surjective B f hf hXc hXq hYc hYq F

end AlgebraicGeometry

end
