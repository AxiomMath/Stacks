module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.CartesianColimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedSpectrum
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleRigidityOverColimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFullyFaithful
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautFromRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautRepresentability
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductCutoffSharp
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedSpectrumRefined

/-!
# Representability of the formal spectrum of a taut homomorphism

Let `φ : A ⟶ C` be a taut continuous homomorphism of weakly admissible topological rings over a
scheme `S`. This file proves the implication (3) ⟹ (2) of **Stacks 0AN5** — `Spf φ` is
representable by schemes — and with it the equivalence of the three conditions of the tag, in
two forms: for a target whose stages are uniformly bounded by the size cutoff of the site, and,
with no hypothesis on the rings beyond the ones Stacks 0AN5 states, over a site whose cutoff is
a regular cardinal.

## Main results

* `FormalSpace.relative_isAffineHom_formalSpectrumMap_of_isTaut_of_boundedStages`: `Spf φ` is
  representable by objects of the site, with affine projections, assuming
  `⨆ K, (Spec (C ⧸ K)).size < B.cutoff` over the weak ideals of definition `K` of `C`, or that
  `B.cutoff` is regular.
* `AlgebraicGeometry.FormalSpace.relativelyRepresentable_formalSpectrumMap_of_isTaut`: the
  same under the bound on the stages, stated as condition (2) of Stacks 0AN5.
* `AlgebraicGeometry.FormalSpace.relativelyRepresentable_formalSpectrumMap_of_cutoff_isRegular`:
  condition (2) for *every* taut homomorphism of weakly admissible topological rings, over a
  site whose cutoff is regular.
* `AlgebraicGeometry.BigFppfSite.isRegular_cutoff_iff_contains_of_openCover_affineOpens`: that
  hypothesis on the site is *necessary* for the route which proves the previous statement, and
  not merely sufficient for it. The containment that route consumes — a scheme covered by the
  images of open immersions from objects of the site, indexed by the affine opens of an object
  of the site, with no bound on their sizes — holds for every such covering if and only if the
  cutoff is a regular cardinal.
* `AlgebraicGeometry.FormalSpace.formalSpectrumMap_tfae_of_imp_relativelyRepresentable`: the
  three conditions of Stacks 0AN5 are equivalent as soon as (3) ⟹ (2) is available, the other
  two arrows being unconditional.
* `AlgebraicGeometry.FormalSpace.formalSpectrumMap_tfae_of_cutoff_isRegular`: the equivalence
  of (1), (2) and (3) at the hypotheses of Stacks 0AN5 on the rings, over a site whose cutoff
  is regular.
* `AlgebraicGeometry.FormalSpace.iSup_stageSize_lt_cutoff_of_cofinal_lt_cof` and
  `AlgebraicGeometry.FormalSpace.iSup_stageSize_lt_cutoff_of_isCountablyGenerated`: the bound
  on the stages holds whenever the weak ideals of definition of `C` have a downward cofinal
  family indexed below the cofinality of the cutoff, in particular whenever the neighbourhood
  filter of `0` in `C` is countably generated.
* `AlgebraicGeometry.FormalSpace.relativelyRepresentable_formalSpectrumMap_of_isCountablyGenerated`
  and `AlgebraicGeometry.FormalSpace.formalSpectrumMap_tfae_of_isCountablyGenerated`: for a
  countably indexed target the implication is unconditional, and the three conditions of
  Stacks 0AN5 are equivalent.

## Implementation notes

*What is reached.* Three arrows of Stacks 0AN5 are proved with no set-theoretic hypothesis:
(2) ⟹ (1) is
`AlgebraicGeometry.FormalSpace.isRepresentableByAlgebraicSpacesULift_formalSpectrumMap`
(`SpectrumFullyFaithful.lean:707`), and (2) ⟹ (3), (1) ⟹ (3) are
`AlgebraicGeometry.FormalSpace.isTaut_of_relativelyRepresentable_formalSpectrumMap` and
`AlgebraicGeometry.FormalSpace.isTaut_of_isRepresentableByAlgebraicSpaces_formalSpectrumMap`
(`TautFromRepresentable.lean:241` and `:266`). The fourth, (3) ⟹ (2), is the one that needs an
input, and the input is about the *site*, not about the mathematics of the tag.

*What the remaining arrow costs.* The base change of `Spf φ` along a point out of a
quasi-compact object is represented unconditionally
(`AlgebraicGeometry.FormalSpace.exists_isPullback_formalSpectrumMap_of_isQuasiCompactObject`,
`TautRepresentability.lean:317`); the charts so obtained over the affine opens of an arbitrary
test object `T` glue to a scheme on any route, and the whole question is whether that scheme lies
in the site. The library's discharges of such a containment are
`AlgebraicGeometry.BigFppfSite.contains_of_openCover`
(`Spaces/Representability.lean:158`), which asks the index type to be smaller than
`B.cutoff.ord.cof`, and
`AlgebraicGeometry.BigFppfSite.contains_of_openCover_of_size_le` (`:173`), which asks one
cardinal below the cutoff to bound every chart — equivalently
`AlgebraicGeometry.BigFppfSite.contains_of_openCover_of_iSup_size_lt`
(`Spaces/DenseSchematicLocus.lean:230`), which asks the index type to be merely below the
cutoff and the supremum of the sizes of the charts to be below it. The *index type is therefore
never the obstruction here*: the affine opens of a test object of the site are fewer than the
cutoff unconditionally. The obstruction is the supremum of the chart sizes alone. The discharges
are consumed here through
`AlgebraicGeometry.FormalSpace.CartesianColimit.relative_of_affineBaseChanges`
(`Affine/CartesianColimit.lean:367`). The chart over the affine open `O` is
`O ×_{Spec (A ⧸ I_O)} Spec (C ⧸ K(I_O))`, and the weak ideal `I_O` through which `O` factors
genuinely varies with `O`, so no discharge is free:
`AlgebraicGeometry.FormalSpace.QuotientSystem` (`FormalSpace/FormalSpectrum.lean:139`) asks
only that each stage lie in the site separately, and an affine morphism carries no size bound,
there being no counterpart for `AlgebraicGeometry.IsAffineHom` of
`AlgebraicGeometry.Scheme.size_le_of_locallyOfFiniteType` (`Size/FiniteType.lean:260`).

*The index-type route: a regular cutoff, and nothing less.* There are at most `size T` affine
opens (`AlgebraicGeometry.Scheme.mk_affineOpens_le_size`, `Size/Basic.lean:72`), so a cutoff
equal to its own cofinality discharges the containment outright, with no bound on the charts
(`AlgebraicGeometry.BigFppfSite.contains_of_openCover_affineOpens_of_isRegular`,
`Spaces/SchematicLocusRelative.lean:187`). This is
`relativelyRepresentable_formalSpectrumMap_of_cutoff_isRegular` and it delivers the tag for all
weakly admissible `A` and `C`. Regularity is not weakenable here — the containment that route
consumes, over all test objects, *implies* `B.cutoff.IsRegular` and so is equivalent to it
(`AlgebraicGeometry.BigFppfSite.isRegular_cutoff_iff_contains_of_openCover_affineOpens` below) —
and it is not available from the axioms: the cardinal axioms of `AlgebraicGeometry.BigFppfSite`
(`Topologies/Fppf.lean:115`) are `aleph0_lt_cutoff`, `cutoff_isStrongPrelimit` and
`aleph0_lt_cutoff_cof` (`:123`, `:126`, `:128`) — uncountable cofinality, not regularity — and
closure of the site under the coproducts of the families of its objects indexed below the cutoff
is *equivalent* to `B.cutoff.IsRegular`
(`AlgebraicGeometry.BigFppfSite.isRegular_cutoff_iff_contains_sigma`,
`Spaces/CoproductCutoffSharp.lean:181`), hence to an inaccessible cardinal
(`AlgebraicGeometry.BigFppfSite.isInaccessible_cutoff_of_contains_sigma`, `:195`). A site whose
cutoff is singular, with a family below the cutoff whose coproduct leaves it, is exhibited
(`AlgebraicGeometry.exists_bigFppfSite_family_not_contains_sigma`, `:210`, built from
`AlgebraicGeometry.exists_cutoff_isSingular`,
`Spaces/Descent/SpacesOverSpaces/CoproductUniformAtlasCutoff.lean:147`). So what would have to
change in the axiomatisation is one further field on `BigFppfSite`, `B.cutoff.ord.cof =
B.cutoff` — equivalently, by the displayed equivalence, closure under those coproducts — and
that field cannot be added without assuming an inaccessible cardinal. The source's toolkit is no
better off: the only clause of Stacks 000R about an arbitrary open covering is (6), carried as
`AlgebraicGeometry.Scheme.size_lt_of_openCover` (`Size/Cutoff.lean:239`), which likewise demands
one uniform bound.

*The chart-size route: a bound on the stages, over an arbitrary site.* The other discharge asks
`⨆ K, (Spec (C ⧸ K)).size < B.cutoff` over the weak ideals of definition of `C`, which is what
`relativelyRepresentable_formalSpectrumMap_of_isTaut` assumes. That supremum is not an
over-quantification of the proof's needs, for two reasons. The stage `Spec (A ⧸ I)` is itself an
affine object of the site, so the chart over it is the full stage `Spec (C ⧸ K(I))`; and
although the charts only ever involve the ideals `K(I) = closure (IC)` extended from the weak
ideals of definition `I` of `A`, restricting the supremum to those gains nothing, because for a
taut homomorphism they are a fundamental system of weak ideals of definition of `C` — the second
clause of `RingHom.IsTaut` (`Topology/Algebra/AdicTopology/Taut.lean:53`), read through
`RingHom.isTaut_iff_hasBasis_isWeakIdealOfDefinition` (`:70`) — so every weak ideal of
definition of `C` contains one of them and `C ⧸ K` is a quotient of the corresponding
`C ⧸ K(I)`, making the two suprema equal. Nor is the index type of the supremum of any help: it
is a type of ideals of `C`, with nothing bounding it against the cofinality of the cutoff, and
`QuotientSystem.inSite` bounds the stages one at a time. What does imply the bound is any
downward cofinal family of weak ideals of definition indexed below `B.cutoff.ord.cof`
(`iSup_stageSize_lt_cutoff_of_cofinal_lt_cof`), of which a countable fundamental system is the
only case the cutoff's axioms always allow — weak admissibility puts no bound on the character
of the topology of `C`, and the refuting model of
`StacksFrontier.AlgebraicGeometry.FormalSpace.TautRepresentability` is built with a fundamental
system of cardinality exactly `B.cutoff.ord.cof`, one step outside the hypothesis; and
`(Spec (.of C)).size < B.cutoff`, every stage being a quotient of `C`. That last one is not
equivalent to the bound — it constrains `#C`, while the supremum is already below the cutoff
for a `C` of any cardinality whose weak ideals of
definition have a smallest member with small quotient, by
`iSup_stageSize_lt_cutoff_of_cofinal_lt_cof` at a one-point index type. See
`StacksFrontier.AlgebraicGeometry.FormalSpace.TautRepresentability` for the full record of the
obstruction.

## References

* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Cardinal

namespace AlgebraicGeometry

universe u

/-- The ranges of the coprojections of a coproduct of nonempty affine schemes are pairwise
distinct affine opens of it. -/
lemma injective_affineOpens_opensRange_sigmaι {I : Type u} (W : I → Scheme.{u})
    [∀ i, IsAffine (W i)] [∀ i, Nonempty (W i)] :
    Function.Injective fun i : I =>
      (⟨(Sigma.ι W i).opensRange, isAffineOpen_opensRange (Sigma.ι W i)⟩ :
        (∐ W).affineOpens) := by
  intro i j hij
  by_contra hne
  obtain ⟨x⟩ : Nonempty (W i) := inferInstance
  replace hij : (Sigma.ι W i).opensRange = (Sigma.ι W j).opensRange :=
    congrArg Subtype.val hij
  have hd := disjoint_opensRange_sigmaι W i j hne
  rw [hij, disjoint_self] at hd
  have hmem : Sigma.ι W i x ∈ (Sigma.ι W i).opensRange := ⟨x, rfl⟩
  rw [hij, hd] at hmem
  simp at hmem

end AlgebraicGeometry

namespace AlgebraicGeometry.BigFppfSite

universe u

/-- **The containment that the glueing of Stacks 0AN5 consumes is exactly a regular cutoff.** A
big fppf site contains every scheme covered by the images of open immersions from objects of the
site *indexed by the affine opens of an object of the site* if and only if its size cutoff is a
regular cardinal.

This is the sharp form, at the index shape the proof of Stacks 0AN5 produces, of
`AlgebraicGeometry.BigFppfSite.isRegular_cutoff_iff_contains_sigma`, whose index type is an
arbitrary one of cardinality below the cutoff. The index type is never itself the obstruction —
there are at most `size T` affine opens
(`AlgebraicGeometry.Scheme.mk_affineOpens_le_size`), and
`AlgebraicGeometry.BigFppfSite.contains_of_openCover_of_iSup_size_lt` asks nothing more of it
than that — so the only question is whether the sizes of the members may be left unbounded, and
the answer is that they may precisely when the cutoff is regular.

Forwards this is `AlgebraicGeometry.BigFppfSite.contains_of_openCover_affineOpens_of_isRegular`:
a regular cutoff is its own cofinality, so the affine opens number fewer than
`B.cutoff.ord.cof` and `AlgebraicGeometry.BigFppfSite.contains_of_openCover` applies. For the
converse, a singular cutoff carries a family `Z` of objects of the site, indexed by a type `I`
of cardinality `B.cutoff.ord.cof`, whose coproduct is not an object of the site
(`AlgebraicGeometry.BigFppfSite.exists_family_not_contains_sigma_of_cof_lt`); the coproduct
`T` of `I` copies of `Spec ℤ` is an object of the site, its size being at most `max ℵ₀ #I`
(`AlgebraicGeometry.schemeSize_coproduct_le`), and the ranges of its coprojections are pairwise
distinct affine opens of it, so the affine opens of `T` surject onto `I` and the coprojections
of `∐ Z`, reindexed along that surjection, are a covering of the forbidden shape. -/
theorem isRegular_cutoff_iff_contains_of_openCover_affineOpens (B : BigFppfSite.{u}) :
    B.cutoff.IsRegular ↔ ∀ T : Scheme.{u}, B.Contains T →
      ∀ (X : T.affineOpens → Scheme.{u}) (Y : Scheme.{u}) (g : ∀ O, X O ⟶ Y),
        (∀ O, IsOpenImmersion (g O)) → (∀ y : Y, ∃ O, y ∈ Set.range (g O)) →
        (∀ O, B.Contains (X O)) → B.Contains Y := by
  classical
  constructor
  · intro hreg T hT X Y g hg hcov hX
    have : Nonempty T.affineOpens := ⟨⟨⊥, isAffineOpen_bot T⟩⟩
    exact B.contains_of_openCover (T.mk_affineOpens_le_size.trans_lt (hT.trans_le hreg.2)) g
      hcov hX
  · intro h
    refine ⟨B.aleph0_lt_cutoff.le, ?_⟩
    by_contra hle
    obtain ⟨I, Z, hIcof, hI, hZ, hnot⟩ :=
      B.exists_family_not_contains_sigma_of_cof_lt (not_le.1 hle)
    have : Nonempty I := Cardinal.mk_ne_zero_iff.1 (by
      rw [hIcof]
      exact (Cardinal.aleph0_pos.trans B.aleph0_lt_cutoff_cof).ne')
    set W : I → Scheme.{u} := fun _ => Spec (CommRingCat.of (ULift.{u} ℤ)) with hW
    have hT : B.Contains (∐ W) :=
      (schemeSize_coproduct_le W (max ℵ₀ #I) (le_max_left _ _) (le_max_right _ _) fun _ => by
        rw [hW, Scheme.size_Spec]
        exact (max_le le_rfl Cardinal.mk_le_aleph0).trans (le_max_left _ _)).trans_lt
        (max_lt B.aleph0_lt_cutoff hI)
    have : ∀ i, IsAffine (W i) := fun _ => inferInstanceAs (IsAffine (Spec _))
    have : ∀ i, Nonempty (W i) := fun _ => inferInstanceAs (Nonempty (Spec _))
    obtain ⟨σ, hσ⟩ : ∃ σ : (∐ W).affineOpens → I, Function.Surjective σ :=
      ⟨Function.invFun _, Function.invFun_surjective (injective_affineOpens_opensRange_sigmaι W)⟩
    refine hnot (h (∐ W) hT (fun O => Z (σ O)) (∐ Z) (fun O => Sigma.ι Z (σ O))
      (fun _ => inferInstance) (fun y => ?_) fun _ => hZ _)
    obtain ⟨i, x, hx⟩ := (sigmaOpenCover Z).exists_eq y
    obtain ⟨O, hO⟩ := hσ i
    exact ⟨O, hO ▸ ⟨x, hx⟩⟩

end AlgebraicGeometry.BigFppfSite

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
  [IsLinearTopology C C]

/-- **Stacks 0AN5, the implication (3) ⟹ (2), under a uniform bound on the stages of the target
or over a site with regular cutoff.** Let `φ : A ⟶ C` be a taut continuous homomorphism of
weakly admissible topological rings over `S` and suppose *either* that one cardinal below the
cutoff of the site bounds the sizes of all the stages `Spec (C ⧸ K)` of `Spf C`, `K` running
over the weak ideals of definition of `C`, *or* that the cutoff of the site is a regular
cardinal. Then `Spf φ` is representable by objects of the site and every represented base change
of it is an affine morphism of schemes.

Neither alternative is an artefact of the proof and neither follows from the axioms of
`AlgebraicGeometry.BigFppfSite`; see the module docstring. The first is the hypothesis of
`AlgebraicGeometry.FormalSpace.relativelyRepresentable_formalSpectrumMap_of_isTaut`, the second
that of
`AlgebraicGeometry.FormalSpace.relativelyRepresentable_formalSpectrumMap_of_cutoff_isRegular`,
which assumes nothing about the rings beyond what Stacks 0AN5 states.

Over a point out of an *affine* object `U` of the site the base change is already known: the
point factors through a stage `Spec (A ⧸ I)` because `U` is quasi-compact
(`AlgebraicGeometry.FormalSpace.exists_factorsThroughStage_of_isQuasiCompactObject`), tautness
identifies `Spf C ×_{Spf A} Spec (A ⧸ I)` with the stage `Spec (C ⧸ K)` for `K` the closure of
`IC` (`AlgebraicGeometry.FormalSpace.isPullback_formalSpectrumMap_stage_of_isTaut`), and the
fibre product `Spec (C ⧸ K) ×_{Spec (A ⧸ I)} U` formed in the site represents the base change.
That fibre product is bounded by `AlgebraicGeometry.Space.size_pullback_le` by the maximum of
that supremum and of `size U` — unconditionally, the supremum being an upper bound of the stage
sizes whether or not it is below the cutoff — which is exactly the input that
`AlgebraicGeometry.FormalSpace.CartesianColimit.relative_of_affineBaseChanges` needs in order to
glue the charts over the affine opens of an arbitrary test object, and that statement asks for
the disjunction offered here. The remaining input of it, pointwise `u`-smallness of the source,
is unconditional (`AlgebraicGeometry.FormalSpace.small_formalSpectrum_sections`). -/
theorem relative_isAffineHom_formalSpectrumMap_of_isTaut_of_boundedStages
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E)
    (hf : RingHom.IsTaut f.toRingHom)
    (hstages : (⨆ K : { K : Ideal C // TopologicalRing.IsWeakIdealOfDefinition K },
      (Spec (.of (C ⧸ K.1))).size) < B.cutoff ∨ B.cutoff.IsRegular) :
    (MorphismProperty.inverseImage (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) (formalSpectrumMap hA f) := by
  classical
  let G := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let T := BigFppfOver.toScheme B S hS
  let Inc := BigAffineFppf.inclusion B S hS
  let _ : PreservesLimitsOfShape WalkingCospan G :=
    preservesLimitsOfShape_walkingCospan_sheafifiedYoneda B S hS
  let _ : PreservesLimitsOfShape WalkingCospan T := by
    dsimp only [T, BigFppfOver.toScheme]
    infer_instance
  have hsmall : FunctorToTypes.Small.{u} (formalSpectrum E).obj := fun X =>
    small_formalSpectrum_sections B S hS hC E X.unop
  have hisoA : MorphismProperty.RespectsIso (@IsAffineHom.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine CartesianColimit.relative_of_affineBaseChanges' B S hS (@IsAffineHom.{u})
    (@HasAffineProperty.instIsZariskiLocalAtTarget _ _ instHasAffinePropertyIsAffineHomIsAffine)
    (formalSpectrumMap hA f) hstages ?_
  intro U hU ξ
  have _ : IsAffine (T.obj U) := hU
  obtain ⟨I, g, hg⟩ := exists_factorsThroughStage_of_isQuasiCompactObject B S hS hA D U
    (isQuasiCompactObject_over_of_compact_scheme B S hS U) ξ
  obtain ⟨K, -, hIK, hsq⟩ :=
    isPullback_formalSpectrumMap_stage_of_isTaut B S hS hA hC D E f hf I
  let a : Inc.obj (E.stage K) ⟶ Inc.obj (D.stage I) := Inc.map (f.stageMap I K hIK)
  have ha : IsAffineHom (T.map a) := by
    have _ : IsAffine (T.obj (Inc.obj (E.stage K))) :=
      BigAffineFppf.isAffine_toScheme_obj B S hS (E.stage K)
    have _ : IsAffine (T.obj (Inc.obj (D.stage I))) :=
      BigAffineFppf.isAffine_toScheme_obj B S hS (D.stage I)
    infer_instance
  refine ⟨pullback a g, G.map (pullback.fst a g) ≫ formalSpectrumInclusion E K, pullback.snd a g,
    ?_, MorphismProperty.of_isPullback ((IsPullback.of_hasPullback a g).map T) ha, ?_⟩
  · rw [← hg]
    exact ((IsPullback.of_hasPullback a g).map G).paste_horiz hsq
  · exact (Space.size_pullback_le B S hS a g).trans (max_le_max (le_ciSup
      (f := fun L : { K : Ideal C // TopologicalRing.IsWeakIdealOfDefinition K } =>
        (Spec (.of (C ⧸ L.1))).size) Cardinal.bddAbove_of_small K) le_rfl)

/-- **Stacks 0AN5, the implication (3) ⟹ (2), under a uniform bound on the stages of the
target.** The representability half of
`AlgebraicGeometry.FormalSpace.relative_isAffineHom_formalSpectrumMap_of_isTaut_of_boundedStages`:
for a taut `φ : A ⟶ C`, if one cardinal below the cutoff bounds the sizes of all the stages
`Spec (C ⧸ K)` of `Spf C`, then `Spf φ` is representable by schemes.

The named hypothesis is not a consequence of the axioms of `AlgebraicGeometry.BigFppfSite`; see
the module docstring. Sufficient forms of it are
`AlgebraicGeometry.FormalSpace.QuotientSystem.HasLargeSite` for the quotient system of `C`, the
side condition of `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_formalSpectrum`;
a fundamental system of weak ideals of definition of `C` indexed below the cofinality of the
cutoff (`AlgebraicGeometry.FormalSpace.iSup_stageSize_lt_cutoff_of_cofinal_lt_cof`), of which a
countable fundamental system is the case the cutoff's axioms always allow
(`AlgebraicGeometry.FormalSpace.iSup_stageSize_lt_cutoff_of_isCountablyGenerated`); and
`(Spec (.of C)).size < B.cutoff`, since every stage is a quotient of `C`. The last of these is
the hypothesis `AlgebraicGeometry.FormalSpace.hasLargeSite_of_mk_lt_cutoff` consumes and it
constrains `#C`, which the bound on the stages does not: if the weak ideals of definition of `C`
have a smallest member `K₀` then that supremum is `(Spec (.of (C ⧸ K₀))).size` whatever `#C` may
be, by `AlgebraicGeometry.FormalSpace.iSup_stageSize_lt_cutoff_of_cofinal_lt_cof` at a one-point
index type.

Dropping the hypothesis altogether is possible at the price of one on the site instead of on the
rings; see
`AlgebraicGeometry.FormalSpace.relativelyRepresentable_formalSpectrumMap_of_cutoff_isRegular`. -/
theorem relativelyRepresentable_formalSpectrumMap_of_isTaut
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E)
    (hf : RingHom.IsTaut f.toRingHom)
    (hstages : ⨆ K : { K : Ideal C // TopologicalRing.IsWeakIdealOfDefinition K },
      (Spec (.of (C ⧸ K.1))).size < B.cutoff) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable
      (formalSpectrumMap hA f) :=
  (relative_isAffineHom_formalSpectrumMap_of_isTaut_of_boundedStages B S hS hA hC D E f hf
    (Or.inl hstages)).rep

/-- **Stacks 0AN5, the implication (3) ⟹ (2), over a site whose cutoff is a regular cardinal.**
Let `φ : A ⟶ C` be a taut continuous homomorphism of weakly admissible topological rings over
`S`. If the size cutoff of the site is a regular cardinal then `Spf φ` is representable by
schemes, with no hypothesis on `A` or `C` beyond the ones Stacks 0AN5 states.

What the glueing of the charts over the affine opens of a test object `T` needs is that the
scheme they glue to lie in the site. There are at most `size T` affine opens
(`AlgebraicGeometry.Scheme.mk_affineOpens_le_size`), so a regular cutoff, being its own
cofinality, makes the cofinality hypothesis of
`AlgebraicGeometry.BigFppfSite.contains_of_openCover` automatic and asks nothing of the charts
beyond their lying in the site, which they do — this is
`AlgebraicGeometry.BigFppfSite.contains_of_openCover_affineOpens_of_isRegular`. So the stages of
`C` may be of unbounded size.

Regularity is exactly the containment at stake, not merely one sufficient condition for it, and
at the very index shape used here: the containment of every scheme covered by the images of open
immersions from objects of the site indexed by the affine opens of an object of the site holds
for all such coverings if and only if the cutoff is regular
(`AlgebraicGeometry.BigFppfSite.isRegular_cutoff_iff_contains_of_openCover_affineOpens`). The
same is true of the coproducts of the families of objects of the site indexed below the cutoff
(`AlgebraicGeometry.BigFppfSite.isRegular_cutoff_iff_contains_sigma`), and such a cutoff is
inaccessible (`AlgebraicGeometry.BigFppfSite.isInaccessible_cutoff_of_contains_sigma`). It is
therefore not available from the axioms of `AlgebraicGeometry.BigFppfSite`, which a singular
cutoff satisfies (`AlgebraicGeometry.exists_cutoff_isSingular`,
`AlgebraicGeometry.exists_bigFppfSite_family_not_contains_sigma`). -/
theorem relativelyRepresentable_formalSpectrumMap_of_cutoff_isRegular
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E)
    (hf : RingHom.IsTaut f.toRingHom) (hreg : B.cutoff.IsRegular) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable
      (formalSpectrumMap hA f) :=
  (relative_isAffineHom_formalSpectrumMap_of_isTaut_of_boundedStages B S hS hA hC D E f hf
    (Or.inr hreg)).rep

/-! ### The equivalence of the three conditions -/

/-- **Stacks 0AN5, conditions (1), (2) and (3) are equivalent as soon as (3) ⟹ (2) is
available.** Let `φ : A ⟶ C` be a continuous homomorphism of weakly admissible topological rings
over `S`. Granting the implication from tautness to representability by objects of the site, the
following are equivalent:

1. `Spf φ` is representable by algebraic spaces over `S`;
2. `Spf φ` is representable by objects of the site;
3. `φ` is taut.

The other two arrows of the cycle are unconditional: (1) ⟹ (3) is
`AlgebraicGeometry.FormalSpace.isTaut_of_isRepresentableByAlgebraicSpaces_formalSpectrumMap` and
(2) ⟹ (1) is
`AlgebraicGeometry.FormalSpace.isRepresentableByAlgebraicSpacesULift_formalSpectrumMap`. So the
set-theoretic input of Stacks 0AN5 in this library is confined to the hypothesis `h` here, and
this statement is what the forms of Stacks 0AN5 below differ only in. -/
theorem formalSpectrumMap_tfae_of_imp_relativelyRepresentable
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E)
    (h : RingHom.IsTaut f.toRingHom →
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable
        (formalSpectrumMap hA f)) :
    List.TFAE
      [Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (formalSpectrumMap hA f).hom,
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable
          (formalSpectrumMap hA f),
        RingHom.IsTaut f.toRingHom] := by
  tfae_have 1 → 3 := fun hr =>
    isTaut_of_isRepresentableByAlgebraicSpaces_formalSpectrumMap B S hS hA hC D E f hr
  tfae_have 3 → 2 := h
  tfae_have 2 → 1 := fun hr =>
    isRepresentableByAlgebraicSpacesULift_formalSpectrumMap hA f
      (relativelyRepresentable_uliftYoneda_of_sheafifiedYoneda B S hS _ hr)
  tfae_finish

/-- **Stacks 0AN5 over a site whose cutoff is a regular cardinal: conditions (1), (2) and (3)
are equivalent.** Let `φ : A ⟶ C` be a continuous homomorphism of weakly admissible topological
rings over `S` and suppose the size cutoff of the site is a regular cardinal. Then the following
are equivalent:

1. `Spf φ` is representable by algebraic spaces over `S`;
2. `Spf φ` is representable by objects of the site;
3. `φ` is taut.

This is Stacks 0AN5 at its own hypotheses on the rings — two weakly admissible topological rings
and a continuous homomorphism, no countability and no bound on the stages. The regularity of the
cutoff is a condition on the ambient site, which the tag does not speak of; it is the exact
containment the glueing of the charts of condition (2) needs
(`AlgebraicGeometry.BigFppfSite.isRegular_cutoff_iff_contains_of_openCover_affineOpens`) and it
is not implied by the axioms of `AlgebraicGeometry.BigFppfSite`. Only the step (3) ⟹ (2),
`AlgebraicGeometry.FormalSpace.relativelyRepresentable_formalSpectrumMap_of_cutoff_isRegular`,
uses it. -/
theorem formalSpectrumMap_tfae_of_cutoff_isRegular
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E)
    (hreg : B.cutoff.IsRegular) :
    List.TFAE
      [Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (formalSpectrumMap hA f).hom,
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable
          (formalSpectrumMap hA f),
        RingHom.IsTaut f.toRingHom] :=
  formalSpectrumMap_tfae_of_imp_relativelyRepresentable B S hS hA hC D E f fun hf =>
    relativelyRepresentable_formalSpectrumMap_of_cutoff_isRegular B S hS hA hC D E f hf hreg

/-! ### Sufficient conditions for the bound on the stages -/

/-- The spectrum of a quotient ring is no larger than the spectrum of the ring. -/
private theorem size_Spec_le_of_surjective {R R' : Type u} [CommRing R] [CommRing R']
    (f : R →+* R') (hf : Function.Surjective f) :
    (Spec (.of R')).size ≤ (Spec (.of R)).size := by
  simpa only [Scheme.size_Spec] using max_le_max le_rfl (Cardinal.mk_le_of_surjective hf)

omit [IsTopologicalRing C] [IsLinearTopology C C] in
/-- **A formal spectrum with few stages has uniformly bounded stages.** Let `L` be a family of
weak ideals of definition of `C` which is cofinal downwards — every weak ideal of definition of
`C` contains a member — and indexed by a type of cardinality below the cofinality of the cutoff.
Then one cardinal below the cutoff bounds every stage `Spec (C ⧸ K)` of `Spf C`.

A weak ideal of definition `K` containing `L i` makes `C ⧸ K` a quotient of `C ⧸ L i`, hence no
larger (`Ideal.Quotient.factor_surjective`), so the supremum over all weak ideals of definition
is the supremum over the family; each member of that one is below the cutoff because its stage
lies in the site, and `Cardinal.iSup_lt_of_lt_cof_ord` keeps the supremum below it.

This is the sharpest form of the cofinality argument: by
`AlgebraicGeometry.BigFppfSite.aleph0_lt_cutoff_cof` a countable fundamental system always
qualifies, and nothing beyond `ℵ₀ < B.cutoff.ord.cof` is known of the cofinality. -/
theorem iSup_stageSize_lt_cutoff_of_cofinal_lt_cof
    (E : QuotientSystem B S hS C) {ι : Type u} (hι : #ι < B.cutoff.ord.cof)
    (L : ι → { K : Ideal C // TopologicalRing.IsWeakIdealOfDefinition K })
    (hL : ∀ K : { K : Ideal C // TopologicalRing.IsWeakIdealOfDefinition K },
      ∃ i, (L i).1 ≤ K.1) :
    ⨆ K : { K : Ideal C // TopologicalRing.IsWeakIdealOfDefinition K },
      (Spec (.of (C ⧸ K.1))).size < B.cutoff := by
  refine lt_of_le_of_lt (ciSup_le' fun K => ?_)
    (Cardinal.iSup_lt_of_lt_cof_ord hι fun i => E.inSite (L i))
  obtain ⟨i, hi⟩ := hL K
  refine le_trans ?_ (le_ciSup (f := fun j : ι => (Spec (.of (C ⧸ (L j).1))).size)
    Cardinal.bddAbove_of_small i)
  exact size_Spec_le_of_surjective _ (Ideal.Quotient.factor_surjective hi)

/-! ### The countably indexed case -/

/-- **A countably indexed formal spectrum has uniformly bounded stages.** If the neighbourhood
filter of `0` in `C` is countably generated — `Spf C` is countably indexed in the sense of
Stacks 0AN0 — then one cardinal below the cutoff bounds every stage `Spec (C ⧸ K)`.

The bound is `max ℵ₀ #C`: the ring itself is smaller than the cutoff by
`AlgebraicGeometry.FormalSpace.mk_lt_cutoff_of_isCountablyGenerated`, every stage is the
spectrum of a quotient of `C`, and `AlgebraicGeometry.Scheme.size_Spec` computes the size of a
spectrum as `max ℵ₀` of the cardinality of its ring. So the side condition of
`AlgebraicGeometry.FormalSpace.relativelyRepresentable_formalSpectrumMap_of_isTaut` holds with
no hypothesis on the site. -/
theorem iSup_stageSize_lt_cutoff_of_isCountablyGenerated
    (hC : TopologicalRing.IsWeaklyAdmissible C) (E : QuotientSystem B S hS C)
    (hc : (nhds (0 : C)).IsCountablyGenerated) :
    ⨆ K : { K : Ideal C // TopologicalRing.IsWeakIdealOfDefinition K },
      (Spec (.of (C ⧸ K.1))).size < B.cutoff := by
  refine lt_of_le_of_lt (ciSup_le' fun K => size_Spec_le_of_surjective _
    Ideal.Quotient.mk_surjective) ?_
  simpa only [Scheme.size_Spec] using
    max_lt B.aleph0_lt_cutoff (mk_lt_cutoff_of_isCountablyGenerated B S hS E hC hc)

/-- **Stacks 0AN5, the implication (3) ⟹ (2) for a countably indexed target, with no side
condition.** If the neighbourhood filter of `0` in `C` is countably generated and
`φ : A ⟶ C` is taut, then `Spf φ` is representable by schemes.

The side condition of
`AlgebraicGeometry.FormalSpace.relativelyRepresentable_formalSpectrumMap_of_isTaut` is
discharged by `AlgebraicGeometry.FormalSpace.iSup_stageSize_lt_cutoff_of_isCountablyGenerated`.
Nothing is assumed about `A`, and nothing about the site. -/
theorem relativelyRepresentable_formalSpectrumMap_of_isCountablyGenerated
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E)
    (hf : RingHom.IsTaut f.toRingHom) (hc : (nhds (0 : C)).IsCountablyGenerated) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable
      (formalSpectrumMap hA f) :=
  relativelyRepresentable_formalSpectrumMap_of_isTaut B S hS hA hC D E f hf
    (iSup_stageSize_lt_cutoff_of_isCountablyGenerated B S hS hC E hc)

/-- **Stacks 0AN5 for a countably indexed target: conditions (1), (2) and (3) are equivalent.**
Let `φ : A ⟶ C` be a continuous homomorphism of weakly admissible topological rings over `S`
and suppose the neighbourhood filter of `0` in `C` is countably generated. Then the following
are equivalent:

1. `Spf φ` is representable by algebraic spaces over `S`;
2. `Spf φ` is representable by objects of the site;
3. `φ` is taut.

Only the step (3) ⟹ (2),
`AlgebraicGeometry.FormalSpace.relativelyRepresentable_formalSpectrumMap_of_isCountablyGenerated`,
uses the countability hypothesis; the other two arrows are the unconditional ones of
`AlgebraicGeometry.FormalSpace.formalSpectrumMap_tfae_of_imp_relativelyRepresentable`. -/
theorem formalSpectrumMap_tfae_of_isCountablyGenerated
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E)
    (hc : (nhds (0 : C)).IsCountablyGenerated) :
    List.TFAE
      [Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (formalSpectrumMap hA f).hom,
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable
          (formalSpectrumMap hA f),
        RingHom.IsTaut f.toRingHom] :=
  formalSpectrumMap_tfae_of_imp_relativelyRepresentable B S hS hA hC D E f fun hf =>
    relativelyRepresentable_formalSpectrumMap_of_isCountablyGenerated B S hS hA hC D E f hf hc

end AlgebraicGeometry.FormalSpace

end
