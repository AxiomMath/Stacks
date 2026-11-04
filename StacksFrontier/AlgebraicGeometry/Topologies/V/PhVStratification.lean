module

public import StacksFrontier.AlgebraicGeometry.AffineClosedUnion.CardForm
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImmersionImage
public import StacksFrontier.AlgebraicGeometry.Morphisms.ProperCoproduct
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasicoherentSubobjectGluing.FiniteTypeCover
public import StacksFrontier.AlgebraicGeometry.Scheme.Reduction
public import StacksFrontier.AlgebraicGeometry.Sheaves.SectionsWithSupport.QuasiCompactOpenIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.AlmostBlowUpSheafCriterion
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.CoveringsParts0DBI
public import StacksFrontier.AlgebraicGeometry.Topologies.V.FppfAffineDomination
public import StacksFrontier.AlgebraicGeometry.Topologies.V.FppfVComparison
public import StacksFrontier.AlgebraicGeometry.Topologies.V.PhVTfae

/-!
# The generic flatness step of Stacks 0ETR

Stacks 0ETR says that a family of morphisms locally of finite presentation is a ph covering if
and only if it is a V covering. The converse implication is reduced, in
`StacksFrontier.AlgebraicGeometry.Topologies.V.PhVTfae`, to the single predicate
`AlgebraicGeometry.StandardVCoveringHasPHRefinement`: every standard V covering of an affine
scheme by morphisms locally of finite presentation is refined by a standard ph covering.

This file carries out the two outer steps of that predicate — the generic flatness reduction
and the recognition of the flattened family as a ph covering — and isolates the inner one as
`AlgebraicGeometry.StandardVCoveringDenseFlatHasModification`: the flattening blowup of
Stacks 0815 and the valuative argument that its strict transforms are jointly surjective, and
nothing else. That one is carried out, and the predicate proved, in
`StacksFrontier/AlgebraicGeometry/Topologies/V/PhVFlatteningModification.lean`.

The first step is the last paragraph of the Stacks proof, which is now unconditional. A standard
V covering is jointly surjective, so if its members are flat it is an fppf covering, and an fppf
covering of an affine scheme is refined by a standard ph covering of it — this is the step the
source cites as More on Morphisms, Lemma 37.48.7, and this development has it with no hypothesis
as `AlgebraicGeometry.exists_standardPHCovering_refinement_of_mem_fppfPrecoverage_of_isAffine`.
So `AlgebraicGeometry.standardVCoveringHasPHRefinement_of_flat'` needs nothing carried, unlike
`AlgebraicGeometry.standardVCoveringHasPHRefinement_of_flat`, which predates the discharge of
`AlgebraicGeometry.FppfHasFiniteDomination` at an affine base.

The second step is the third paragraph of the Stacks proof: the reduction, by a generic flatness
stratification of the base, to a family which is already flat over a scheme-theoretically dense
open. That is
`AlgebraicGeometry.standardVCoveringHasPHRefinement_of_denseFlat`, and its input is Stacks 0H3Z,
available here in full quasi-compact quasi-separated generality as
`AlgebraicGeometry.finitePresentationHasFlatStratification`.

A third step is the other bracket. Once the family has been flattened, over a proper surjection
of the base, by steps 4 and 5 of the source — the output of those steps is recorded as
`AlgebraicGeometry.HasFlatFppfModification` — the refinement by a standard ph covering follows
from the previous paragraph applied over the modified base, the transitivity of ph coverings
(Stacks 0DBI part (2)) and the refinement of a ph covering of an affine scheme by a standard one.
That is `AlgebraicGeometry.exists_standardPHCovering_refinement_of_hasFlatFppfModification`, and
it needs nothing carried either.

## Main definitions

* `AlgebraicGeometry.HasFlatFppfModification`: the output of steps 4 and 5 of the Stacks proof —
  a proper surjection of the base over which the family becomes flat, locally of finite
  presentation and jointly surjective.
* `AlgebraicGeometry.StandardVCoveringDenseFlatHasPHRefinement`: Stacks 0ETR after the generic
  flatness reduction — the case of a standard V covering which is already flat over a
  quasi-compact scheme-theoretically dense open of the affine base.
* `AlgebraicGeometry.StandardVCoveringDenseFlatHasModification`: the same case, asking only for
  the flattening modification. This is the inner step, and it is discharged from the
  Raynaud–Gruson flattening theorem of Stacks 0815 in
  `StacksFrontier.AlgebraicGeometry.Topologies.V.PhVFlatteningModification` by
  `AlgebraicGeometry.standardVCoveringDenseFlatHasModification_of_flatteningBlowup`, and proved
  outright there as `AlgebraicGeometry.standardVCoveringDenseFlatHasModification`.

## Main results

* `AlgebraicGeometry.flat_pullback_snd_comp_iff`, `AlgebraicGeometry.flat_pullback_snd_comp` and
  `AlgebraicGeometry.flat_pullback_snd_of_comp_left`: flatness of a projection `X ×_Z Y ⟶ Y`
  under composition in either leg of the diagram.
* `AlgebraicGeometry.exists_standardPHCovering_refinement_of_hasFlatFppfModification`: steps 5
  and 6 — a family admitting a flattening modification of its affine base is refined by a
  standard ph covering.
* `AlgebraicGeometry.standardVCoveringHasPHRefinement_of_flat'`: the flat case of
  `AlgebraicGeometry.StandardVCoveringHasPHRefinement`, with no hypothesis carried.
* `AlgebraicGeometry.standardVCoveringDenseFlatHasPHRefinement_of_flat` and
  `AlgebraicGeometry.standardVCoveringDenseFlatHasModification_of_flat`: the same, in the shape
  of the two carried predicates.
* `AlgebraicGeometry.standardVCoveringHasPHRefinement_of_denseFlat`: the generic flatness step —
  granted `AlgebraicGeometry.StandardVCoveringDenseFlatHasPHRefinement`, the whole of
  `AlgebraicGeometry.StandardVCoveringHasPHRefinement`.
* `AlgebraicGeometry.standardVCoveringHasPHRefinement_of_modification`: the two steps combined,
  reducing `AlgebraicGeometry.StandardVCoveringHasPHRefinement` to
  `AlgebraicGeometry.StandardVCoveringDenseFlatHasModification`.

## Implementation notes

The stratification is applied to the single morphism `∐_κ A_κ ⟶ T` out of the coproduct of the
members, as the source does: a finite coproduct of affine schemes is affine, so that morphism is
of finite presentation as soon as each member is locally of finite presentation. Flatness is
transported back to the individual members by
`AlgebraicGeometry.flat_pullback_snd_of_comp_left`, the coproduct inclusions being open
immersions and hence flat.

Each stratum `S_i ∖ S_{i+1}` of the stratification is a quasi-compact open of the affine closed
subscheme `S_i` — the complement of the support of an ideal sheaf of finite type, by
`AlgebraicGeometry.isCompact_of_isFiniteType_of_support_eq_compl` — and is replaced by its
scheme-theoretic closure `Y_i` inside `S_i`. What makes this the right replacement is Stacks
01RG: a quasi-compact immersion is an open immersion onto a scheme-theoretically dominant open
of its scheme-theoretic image (`AlgebraicGeometry.isOpenImmersion_toImage` and
`AlgebraicGeometry.isSchemeTheoreticallyDominant_toImage_of_quasiCompact`). Density is therefore
recorded in `AlgebraicGeometry.StandardVCoveringDenseFlatHasPHRefinement` as
`AlgebraicGeometry.IsSchemeTheoreticallyDominant j` for the open immersion `j`, rather than as
`AlgebraicGeometry.Scheme.Opens.IsSchemeTheoreticallyDense` of a subobject of the base; for a
quasi-compact open immersion the two agree, by Stacks 01RD
(`AlgebraicGeometry.Scheme.Opens.isSchemeTheoreticallyDense_iff_isSchemeTheoreticallyDominant`),
and writing the open immersion as a morphism avoids transporting the family along the
isomorphism identifying the stratum with an open subobject of its closure.

The `Y_i` cover the base because the strata do, which is where the hypotheses of a flat
stratification that are not about flatness are used: `S_0 ⊆ T` is a thickening, so the support
of its ideal sheaf is everything, and `S_t` is empty. Walking down the chain from `S_t` to `S_0`
locates the step at which a given point is lost, and that step is the stratum containing it.

The two stages are composed by Stacks 0DBF part (2),
`AlgebraicGeometry.exists_standardPHCovering_refinement_bind`, which this development has
unconditionally: the Chow's lemma input it rests on is
`AlgebraicGeometry.hasChowModification_of_compactSpace_quasiSeparatedSpace`.

## References

* [Stacks Project, Tag 0ETR](https://stacks.math.columbia.edu/tag/0ETR)
* [Stacks Project, Tag 0H3Z](https://stacks.math.columbia.edu/tag/0H3Z)
* [Stacks Project, Tag 0DBF](https://stacks.math.columbia.edu/tag/0DBF)
* [Stacks Project, Tag 0DBT](https://stacks.math.columbia.edu/tag/0DBT)
* [Stacks Project, Tag 0DBI](https://stacks.math.columbia.edu/tag/0DBI)
* [Stacks Project, Tag 0DES](https://stacks.math.columbia.edu/tag/0DES)
* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
* [Stacks Project, Tag 081N](https://stacks.math.columbia.edu/tag/081N)
* [Stacks Project, Tag 02JQ](https://stacks.math.columbia.edu/tag/02JQ)
* [Stacks Project, Tag 01RD](https://stacks.math.columbia.edu/tag/01RD)
* [Stacks Project, Tag 01RG](https://stacks.math.columbia.edu/tag/01RG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v w

namespace AlgebraicGeometry

/-! ### Flatness of a projection under composition in the base -/

/-- Flatness of a morphism is unchanged by precomposing with an isomorphism. -/
private theorem flat_iso_hom_comp_iff {X Y W : Scheme.{u}} (e : X ≅ Y) (g : Y ⟶ W) :
    Flat (e.hom ≫ g) ↔ Flat g :=
  have : MorphismProperty.RespectsIso (@Flat.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  MorphismProperty.cancel_left_of_respectsIso @Flat e.hom g

/-- Base changing along a composite `g' ≫ g` is base changing along `g` and then along `g'`:
the projection of `X ×_Z W` to `W` is, up to the canonical isomorphism, the projection of
`(X ×_Z Y) ×_Y W` to `W`. So the two flatness assertions agree. -/
theorem flat_pullback_snd_comp_iff {X Y Z W : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) (g' : W ⟶ Y) :
    Flat (pullback.snd f (g' ≫ g)) ↔ Flat (pullback.snd (pullback.snd f g) g') := by
  rw [← flat_iso_hom_comp_iff (pullbackLeftPullbackSndIso f g g'),
    pullbackLeftPullbackSndIso_hom_snd]

/-- If the projection `X ×_Z Y ⟶ Y` is flat then so is `X ×_Z W ⟶ W` for any `W ⟶ Y`: the
latter is a base change of the former. -/
theorem flat_pullback_snd_comp {X Y Z W : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) (g' : W ⟶ Y)
    [Flat (pullback.snd f g)] : Flat (pullback.snd f (g' ≫ g)) :=
  (flat_pullback_snd_comp_iff f g g').mpr inferInstance

/-- If `p` is flat and the projection `X ×_Z Y ⟶ Y` is flat then so is the projection
`W ×_Z Y ⟶ Y` for `p : W ⟶ X`: the latter factors through the former by a base change of
`p`. -/
theorem flat_pullback_snd_of_comp_left {W X Y Z : Scheme.{u}} (p : W ⟶ X) (f : X ⟶ Z)
    (g : Y ⟶ Z) [Flat p] [Flat (pullback.snd f g)] : Flat (pullback.snd (p ≫ f) g) := by
  rw [← flat_iso_hom_comp_iff (pullbackRightPullbackFstIso f g p),
    pullbackRightPullbackFstIso_hom_snd]
  infer_instance

/-! ### Flattening after a proper modification of the base -/

/-- **The output of the flattening steps of Stacks 0ETR.** For a family `{a_κ : A_κ ⟶ T}` there
are a proper surjection `b : T' ⟶ T` and a family `{c_κ : X'_κ ⟶ T'}` of flat morphisms locally
of finite presentation which is jointly surjective and maps to the given family over `b`.

This is what the Stacks proof of 0ETR has after steps 4 and 5: `b` is the flattening blowup of
Stacks 0815, `c_κ` is the strict transform of `a_κ` along it — flat by that theorem, locally of
finite presentation by Stacks 081N — and joint surjectivity is the valuative argument of step 5,
which lifts a point of `T'` along a valuation ring to a member of the family (Stacks 02JQ). -/
def HasFlatFppfModification {T : Scheme.{u}} {K : Type v} {A : K → Scheme.{u}}
    (a : ∀ κ, A κ ⟶ T) : Prop :=
  ∃ (T' : Scheme.{u}) (b : T' ⟶ T) (_ : IsProper b) (_ : Surjective b) (X' : K → Scheme.{u})
    (c : ∀ κ, X' κ ⟶ T') (d : ∀ κ, X' κ ⟶ A κ),
    (∀ κ, Flat (c κ)) ∧ (∀ κ, LocallyOfFinitePresentation (c κ)) ∧
      (∀ κ, d κ ≫ a κ = c κ ≫ b) ∧ ∀ t : T', ∃ κ, t ∈ Set.range (c κ).base

/-- A family which is itself flat, locally of finite presentation and jointly surjective has the
identity of the base as a flattening modification. -/
theorem HasFlatFppfModification.of_flat {T : Scheme.{u}} {K : Type v} {A : K → Scheme.{u}}
    (a : ∀ κ, A κ ⟶ T) (hflat : ∀ κ, Flat (a κ))
    (hfp : ∀ κ, LocallyOfFinitePresentation (a κ))
    (hsurj : ∀ t : T, ∃ κ, t ∈ Set.range (a κ).base) : HasFlatFppfModification a :=
  ⟨T, 𝟙 T, inferInstance, inferInstance, A, a, fun κ ↦ 𝟙 _, hflat, hfp,
    fun κ ↦ by rw [Category.id_comp, Category.comp_id], hsurj⟩

/-- **The last two steps of Stacks 0ETR.** A family of morphisms to an affine scheme which
admits a flattening modification of the base is refined by a standard ph covering.

The proper surjection `b : T' ⟶ T` is a ph covering by itself (Stacks 0DES,
`AlgebraicGeometry.surjective_proper_isPHCovering`); the flattened family `{c_κ}` is flat,
locally of finite presentation and jointly surjective, hence an fppf covering of `T'`, hence a
ph covering by Stacks 0DBT (`AlgebraicGeometry.IsPHCovering.of_mem_fppfPrecoverage`); the two
compose to a ph covering of `T` by Stacks 0DBI part (2)
(`AlgebraicGeometry.isPHCovering_bind`); and over the affine `T` a ph covering is refined by a
standard ph covering (`AlgebraicGeometry.IsPHCovering.exists_standardPHCovering`). The
refinement of the original family is by the morphisms `d_κ`. -/
theorem exists_standardPHCovering_refinement_of_hasFlatFppfModification {T : Scheme.{u}}
    (hT : IsAffine T) {K : Type u} {A : K → Scheme.{u}} (a : ∀ κ, A κ ⟶ T)
    (h : HasFlatFppfModification a) :
    ∃ 𝒱 : PreZeroHypercover.{u} T, @StandardPHCovering 𝒱.I₀ T hT 𝒱.X 𝒱.f ∧
      Nonempty (𝒱.Hom ({ I₀ := K, X := A, f := a } : PreZeroHypercover.{u} T)) := by
  have _ : IsAffine T := hT
  obtain ⟨T', b, hbproper, hbsurj, X', c, d, hcflat, hcfp, hd, hcsurj⟩ := h
  have _ : IsProper b := hbproper
  have _ : Surjective b := hbsurj
  -- The modification is a ph covering of the base, and the flattened family one of `T'`.
  have hph1 : IsPHCovering (fun _ : Unit ↦ T') (fun _ ↦ b) := surjective_proper_isPHCovering b
  have hph2 : IsPHCovering X' c :=
    IsPHCovering.of_mem_fppfPrecoverage X' c
      ((Scheme.ofArrows_mem_precoverage_iff (P := @Flat ⊓ @LocallyOfFinitePresentation)).mpr
        ⟨hcsurj, fun κ ↦ ⟨hcflat κ, hcfp κ⟩⟩)
  -- Their composite is a ph covering of the base, refining the given family.
  have hbind := isPHCovering_bind
    ({ I₀ := Unit, X := fun _ ↦ T', f := fun _ ↦ b } : PreZeroHypercover.{0} T) hph1
    (fun _ ↦ ({ I₀ := K, X := X', f := c } : PreZeroHypercover.{u} T')) fun _ ↦ hph2
  obtain ⟨𝒱, h𝒱, ⟨ρ⟩⟩ := hbind.exists_standardPHCovering
  exact ⟨𝒱, h𝒱, ⟨ρ.comp ⟨fun s ↦ s.2, fun s ↦ d s.2, fun s ↦ hd s.2⟩⟩⟩

/-! ### The flat case, unconditionally -/

/-- **The flat case of `AlgebraicGeometry.StandardVCoveringHasPHRefinement`.** A standard V
covering of an affine scheme whose members are *flat* and locally of finite presentation is
refined by a standard ph covering.

This is the last paragraph of the Stacks proof of 0ETR: such a covering is jointly surjective
by `AlgebraicGeometry.IsStandardVCovering.exists_mem_range`, hence an fppf covering, and an
fppf covering of an affine scheme is refined by a standard ph covering of it by
`AlgebraicGeometry.exists_standardPHCovering_refinement_of_mem_fppfPrecoverage_of_isAffine`,
which is Stacks 0DBT's main step. Unlike
`AlgebraicGeometry.standardVCoveringHasPHRefinement_of_flat` this carries no hypothesis: that
declaration predates the discharge of `AlgebraicGeometry.FppfHasFiniteDomination` at an affine
base in `StacksFrontier.AlgebraicGeometry.Topologies.V.FppfAffineDomination`. -/
theorem standardVCoveringHasPHRefinement_of_flat' (T : Scheme.{u}) (hT : IsAffine T)
    (K : Type u) (hK : Finite K) (A : K → Scheme.{u}) (hA : ∀ κ, IsAffine (A κ))
    (a : ∀ κ, A κ ⟶ T) (hflat : ∀ κ, Flat (a κ))
    (hfp : ∀ κ, LocallyOfFinitePresentation (a κ))
    (hstd : @IsStandardVCovering T hT K hK A hA a) :
    ∃ 𝒱 : PreZeroHypercover.{u} T, @StandardPHCovering 𝒱.I₀ T hT 𝒱.X 𝒱.f ∧
      Nonempty (𝒱.Hom ({ I₀ := K, X := A, f := a } : PreZeroHypercover.{u} T)) := by
  have _ : IsAffine T := hT
  have _ : Finite K := hK
  have _ : ∀ κ, IsAffine (A κ) := hA
  exact exists_standardPHCovering_refinement_of_mem_fppfPrecoverage_of_isAffine A a
    (mem_fppfPrecoverage_of_isStandardVCovering A a hflat hfp hstd)

/-! ### The generic flatness step -/

/-- **Stacks 0ETR after the generic flatness reduction.** A standard V covering of an affine
scheme whose members are locally of finite presentation and become flat after base change to a
quasi-compact scheme-theoretically dominant open immersion `j : V ⟶ T` is refined by a standard
ph covering.

This is `AlgebraicGeometry.StandardVCoveringHasPHRefinement` with the extra datum of an open
over which the family is already flat, required to be dense in the scheme-theoretic sense; it is
what the Stacks proof of 0ETR has available after it has stratified the base by generic
flatness and replaced each stratum by its scheme-theoretic closure. Density is recorded as
`AlgebraicGeometry.IsSchemeTheoreticallyDominant j`, which for a quasi-compact open immersion is
scheme-theoretic density of its range by
`AlgebraicGeometry.Scheme.Opens.isSchemeTheoreticallyDense_iff_isSchemeTheoreticallyDominant`
(Stacks 01RD).

`AlgebraicGeometry.standardVCoveringHasPHRefinement_of_denseFlat` shows that this suffices for
the whole of `AlgebraicGeometry.StandardVCoveringHasPHRefinement`, and
`AlgebraicGeometry.standardVCoveringDenseFlatHasPHRefinement_of_flat` discharges it on the
region where the family is flat over the whole base. -/
def StandardVCoveringDenseFlatHasPHRefinement : Prop :=
  ∀ (T : Scheme.{u}) (hT : IsAffine T) (K : Type u) (hK : Finite K) (A : K → Scheme.{u})
    (hA : ∀ κ, IsAffine (A κ)) (a : ∀ κ, A κ ⟶ T), (∀ κ, LocallyOfFinitePresentation (a κ)) →
      @IsStandardVCovering T hT K hK A hA a →
      ∀ (V : Scheme.{u}) (j : V ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
        [IsSchemeTheoreticallyDominant j], (∀ κ, Flat (pullback.snd (a κ) j)) →
        ∃ 𝒱 : PreZeroHypercover.{u} T, @StandardPHCovering 𝒱.I₀ T hT 𝒱.X 𝒱.f ∧
          Nonempty (𝒱.Hom ({ I₀ := K, X := A, f := a } : PreZeroHypercover.{u} T))

/-- A family which is already flat over the whole base satisfies
`AlgebraicGeometry.StandardVCoveringDenseFlatHasPHRefinement`, by
`AlgebraicGeometry.standardVCoveringHasPHRefinement_of_flat'`: the flatness of each
`X_κ ×_T V ⟶ V` is not used, the flatness of `a κ` itself being enough. -/
theorem standardVCoveringDenseFlatHasPHRefinement_of_flat (T : Scheme.{u}) (hT : IsAffine T)
    (K : Type u) (hK : Finite K) (A : K → Scheme.{u}) (hA : ∀ κ, IsAffine (A κ))
    (a : ∀ κ, A κ ⟶ T) (hflat : ∀ κ, Flat (a κ))
    (hfp : ∀ κ, LocallyOfFinitePresentation (a κ))
    (hstd : @IsStandardVCovering T hT K hK A hA a) (V : Scheme.{u}) (j : V ⟶ T)
    [IsOpenImmersion j] [QuasiCompact j] [IsSchemeTheoreticallyDominant j]
    (_hflatV : ∀ κ, Flat (pullback.snd (a κ) j)) :
    ∃ 𝒱 : PreZeroHypercover.{u} T, @StandardPHCovering 𝒱.I₀ T hT 𝒱.X 𝒱.f ∧
      Nonempty (𝒱.Hom ({ I₀ := K, X := A, f := a } : PreZeroHypercover.{u} T)) :=
  standardVCoveringHasPHRefinement_of_flat' T hT K hK A hA a hflat hfp hstd

/-- **The generic flatness step of Stacks 0ETR.** Granted
`AlgebraicGeometry.StandardVCoveringDenseFlatHasPHRefinement` — the case in which the family is
already flat over a quasi-compact scheme-theoretically dense open of the base — every standard V
covering of an affine scheme by morphisms locally of finite presentation is refined by a standard
ph covering, which is `AlgebraicGeometry.StandardVCoveringHasPHRefinement`.

This is the third paragraph of the Stacks proof of 0ETR. The coproduct of the (finitely many,
affine) members of the covering is a morphism of finite presentation `∐ A_κ ⟶ T`, so Stacks 0H3Z
(`AlgebraicGeometry.finitePresentationHasFlatStratification`) stratifies `T` by closed
subschemes `T ⊇ S_0 ⊇ ⋯ ⊇ S_n = ∅` over whose locally closed strata `S_i ∖ S_{i+1}` the family
becomes flat. Replacing each stratum by its scheme-theoretic closure `Y_i` inside `S_i` turns it
into a quasi-compact scheme-theoretically dense open immersion `S_i ∖ S_{i+1} ⟶ Y_i`
(Stacks 01RG), and the `Y_i` are closed subschemes of `T` which cover it, because the strata do.
Hence `{Y_i ⟶ T}` is a standard ph covering of `T`, presented by the proper surjection
`∐ Y_i ⟶ T`; the hypothesis refines the base change of the family to each `Y_i` by a standard ph
covering of `Y_i`; and Stacks 0DBF part (2),
`AlgebraicGeometry.exists_standardPHCovering_refinement_bind`, collapses the two stages into a
single standard ph covering of `T`. -/
theorem standardVCoveringHasPHRefinement_of_denseFlat
    (H : StandardVCoveringDenseFlatHasPHRefinement.{u}) :
    StandardVCoveringHasPHRefinement.{u} := by
  intro T hT K hK A hA a hlfp hstd
  have _ : IsAffine T := hT
  have _ : Finite K := hK
  have _ : ∀ κ, IsAffine (A κ) := hA
  have _ : ∀ κ, LocallyOfFinitePresentation (a κ) := hlfp
  -- The coproduct of the family is a morphism of finite presentation between affine schemes.
  have _ : IsAffine (∐ A) := inferInstance
  have hfp : FinitePresentation (Sigma.desc a) :=
    ⟨HasRingHomProperty.instIsZariskiLocalAtSource.sigmaDesc fun κ ↦ hlfp κ,
      inferInstance, inferInstance⟩
  -- Stratify the base by generic flatness.
  obtain ⟨t, Idl, hthick, hft, hmono, hlast, hflatstr⟩ :=
    finitePresentationHasFlatStratification (Sigma.desc a) hfp
  -- Each stratum, replaced by its scheme-theoretic closure, is an affine closed subscheme of
  -- the base over which the hypothesis applies.
  have key : ∀ i : Fin t, ∃ (Yi : Scheme.{u}) (yi : Yi ⟶ T) (_ : IsClosedImmersion yi)
      (hai : IsAffine Yi),
      ((Idl i.castSucc).support : Set T) \ ((Idl i.succ).support : Set T) ⊆
          Set.range yi.base ∧
        ∃ 𝒲 : PreZeroHypercover.{u} Yi, @StandardPHCovering 𝒲.I₀ Yi hai 𝒲.X 𝒲.f ∧
          Nonempty (𝒲.Hom
            (({ I₀ := K, X := A, f := a } : PreZeroHypercover.{u} T).pullback₂ yi)) := by
    intro i
    have hZaff : IsAffine (Idl i.castSucc).subscheme :=
      isAffine_of_isAffineHom (Idl i.castSucc).subschemeι
    set ζ : (Idl i.castSucc).subscheme ⟶ T := (Idl i.castSucc).subschemeι with hζ
    set Wo : (Idl i.castSucc).subscheme.Opens := ζ ⁻¹ᵁ (Idl i.succ).support.compl with hWodef
    -- The stratum is a quasi-compact open: it is the complement of the support of a finite
    -- type ideal sheaf on an affine scheme.
    have hWcomp : IsCompact (Wo : Set (Idl i.castSucc).subscheme) := by
      refine isCompact_of_isFiniteType_of_support_eq_compl Wo ((Idl i.succ).comap ζ)
        ((hft i.succ).comap ζ) ?_
      rw [Scheme.IdealSheafData.support_comap]
      simp [hWodef, Set.preimage_compl]
    have _ : QuasiCompact Wo.ι := quasiCompact_ι_of_isCompact Wo hWcomp
    -- Its scheme-theoretic closure, a closed subscheme of the base.
    have _ : IsOpenImmersion Wo.ι.toImage := isOpenImmersion_toImage Wo.ι (Or.inl ‹_›)
    have _ : IsSchemeTheoreticallyDominant Wo.ι.toImage :=
      isSchemeTheoreticallyDominant_toImage_of_quasiCompact Wo.ι
    have hyci : IsClosedImmersion (Wo.ι.imageι ≫ ζ) := inferInstance
    have hyaff : IsAffine Wo.ι.image := isAffine_of_isAffineHom (Wo.ι.imageι ≫ ζ)
    have hjy : Wo.ι.toImage ≫ Wo.ι.imageι ≫ ζ = Wo.ι ≫ ζ := by
      rw [← Category.assoc, Scheme.Hom.toImage_imageι]
    refine ⟨Wo.ι.image, Wo.ι.imageι ≫ ζ, hyci, hyaff, ?_, ?_⟩
    · -- The range of the closure contains the stratum.
      have hsub : Set.range (Wo.ι ≫ ζ).base ⊆ Set.range (Wo.ι.imageι ≫ ζ).base := by
        rw [← hjy]
        rintro _ ⟨x, rfl⟩
        exact ⟨Wo.ι.toImage x, (Scheme.Hom.comp_apply _ _ _).symm⟩
      refine subset_trans (le_of_eq ?_) hsub
      have hrange : Set.range (Wo.ι ≫ ζ).base = ζ.base '' (Wo : Set _) := by
        rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
      have hWset : (Wo : Set (Idl i.castSucc).subscheme)
          = ζ.base ⁻¹' (((Idl i.succ).support : Set T)ᶜ) := rfl
      rw [hrange, hWset, Set.image_preimage_eq_inter_range, hζ,
        Scheme.IdealSheafData.range_subschemeι, Set.diff_eq, Set.inter_comm]
    · -- The hypothesis applies to the base change of the family to the closure.
      refine H Wo.ι.image hyaff K hK (fun κ ↦ pullback (a κ) (Wo.ι.imageι ≫ ζ))
        (fun κ ↦ inferInstance) (fun κ ↦ pullback.snd (a κ) (Wo.ι.imageι ≫ ζ))
        (fun κ ↦ inferInstance)
        (isStandardVCovering_pullback A a (Wo.ι.imageι ≫ ζ) hstd) Wo.toScheme Wo.ι.toImage
        fun κ ↦ ?_
      rw [← flat_pullback_snd_comp_iff, hjy]
      have h1 : Flat (pullback.snd (Sigma.desc a) (Wo.ι ≫ ζ)) := hflatstr i
      have h2 := flat_pullback_snd_of_comp_left (Sigma.ι A κ) (Sigma.desc a) (Wo.ι ≫ ζ)
      rwa [Sigma.ι_desc] at h2
  choose Y y hyci hyaff hyrange 𝒲 h𝒲 hhom using key
  have _ : ∀ i, IsClosedImmersion (y i) := hyci
  have _ : ∀ i, IsAffine (Y i) := hyaff
  -- The closures of the strata cover the base, so they form a standard ph covering of it.
  have hcover : ⋃ i, Set.range (y i).base = Set.univ := by
    refine Set.eq_univ_iff_forall.mpr fun x ↦ ?_
    -- The first stage of the stratification is a thickening, so its support is everything.
    have h0 : ∀ h : 0 < t + 1, x ∈ ((Idl ⟨0, h⟩).support : Set T) := by
      intro h
      have htop : (Idl 0).support = ⊤ :=
        (Scheme.IdealSheafData.isThickening_subschemeι_iff (Idl 0)).mp hthick
      rw [show (⟨0, h⟩ : Fin (t + 1)) = 0 from Fin.mk_zero, htop]
      trivial
    -- Walking down from a stage that misses `x`, one reaches the step at which it is lost.
    have main : ∀ (m : ℕ) (h : m < t + 1), x ∉ ((Idl ⟨m, h⟩).support : Set T) →
        ∃ i : Fin t, x ∈ ((Idl i.castSucc).support : Set T) ∧
          x ∉ ((Idl i.succ).support : Set T) := by
      intro m
      induction m with
      | zero => exact fun h hx ↦ absurd (h0 h) hx
      | succ m ih =>
        intro h hx
        by_cases hm : x ∈ ((Idl ⟨m, by omega⟩).support : Set T)
        · exact ⟨⟨m, by omega⟩, hm, hx⟩
        · exact ih (by omega) hm
    -- The last stage is the whole base, so it misses `x`.
    have hlastx : x ∉ ((Idl ⟨t, Nat.lt_succ_self t⟩).support : Set T) := by
      rw [show (⟨t, Nat.lt_succ_self t⟩ : Fin (t + 1)) = Fin.last t from rfl, hlast]
      simp
    obtain ⟨i, hi1, hi2⟩ := main t (Nat.lt_succ_self t) hlastx
    exact Set.mem_iUnion.mpr ⟨i, hyrange i ⟨hi1, hi2⟩⟩
  have _ : ∀ i, IsProper (y i) := fun i ↦ inferInstance
  have hE : StandardPHCovering y :=
    StandardPHCovering.of_presentation y (fun i ↦ hyaff i) (Sigma.desc y) (Sigma.ι Y)
      (isProper_sigmaDesc y)
      ((Stacks.AffineClosedUnion.surjective_sigmaDesc_iff y).mpr hcover)
      (fun i ↦ inferInstance) (sigmaOpenCover Y).iUnion_range fun i ↦ Sigma.ι_desc _ _
  -- Collapse the two stages by Stacks 0DBF part (2).
  obtain ⟨G, hG, ⟨δ⟩⟩ := exists_standardPHCovering_refinement_bind
    ({ I₀ := Fin t, X := Y, f := y } : PreZeroHypercover.{0} T) hE 𝒲 h𝒲
  -- The two-stage covering refines the given family, by the first projections.
  have hφ : ∀ i, (𝒲 i).Hom
      (({ I₀ := K, X := A, f := a } : PreZeroHypercover.{u} T).pullback₂ (y i)) :=
    fun i ↦ (hhom i).some
  have ψ : (({ I₀ := Fin t, X := Y, f := y } : PreZeroHypercover.{0} T).bind 𝒲).Hom
      ({ I₀ := K, X := A, f := a } : PreZeroHypercover.{u} T) := by
    refine ⟨fun s ↦ (hφ s.1).s₀ s.2,
      fun s ↦ (hφ s.1).h₀ s.2 ≫ pullback.fst (a ((hφ s.1).s₀ s.2)) (y s.1), fun s ↦ ?_⟩
    calc ((hφ s.1).h₀ s.2 ≫ pullback.fst (a ((hφ s.1).s₀ s.2)) (y s.1)) ≫
          a ((hφ s.1).s₀ s.2)
        = (hφ s.1).h₀ s.2 ≫ pullback.fst (a ((hφ s.1).s₀ s.2)) (y s.1) ≫
            a ((hφ s.1).s₀ s.2) := Category.assoc _ _ _
      _ = (hφ s.1).h₀ s.2 ≫ pullback.snd (a ((hφ s.1).s₀ s.2)) (y s.1) ≫ y s.1 :=
          congrArg (fun k ↦ (hφ s.1).h₀ s.2 ≫ k) pullback.condition
      _ = ((hφ s.1).h₀ s.2 ≫ pullback.snd (a ((hφ s.1).s₀ s.2)) (y s.1)) ≫ y s.1 :=
          (Category.assoc _ _ _).symm
      _ = (𝒲 s.1).f s.2 ≫ y s.1 := congrArg (fun k ↦ k ≫ y s.1) ((hφ s.1).w₀ s.2)
  exact ⟨G, hG, ⟨δ.comp ψ⟩⟩

/-! ### The inner step -/

/-- **The flattening step of Stacks 0ETR.** For a standard V covering of an affine scheme by
morphisms locally of finite presentation which is already flat over a quasi-compact
scheme-theoretically dense open of the base, there is a flattening modification of the base in
the sense of
`AlgebraicGeometry.HasFlatFppfModification`.

This is steps 4 and 5 of the Stacks proof and nothing else: the `U`-admissible blowup of Stacks
0815 over which the strict transforms become flat, with their local finite presentation supplied
by Stacks 081N and their joint surjectivity by the valuative argument of Stacks 02JQ. Steps 3
and 6, which bracket it, are
`AlgebraicGeometry.standardVCoveringHasPHRefinement_of_denseFlat` and
`AlgebraicGeometry.exists_standardPHCovering_refinement_of_hasFlatFppfModification`. -/
def StandardVCoveringDenseFlatHasModification : Prop :=
  ∀ (T : Scheme.{u}) (hT : IsAffine T) (K : Type u) (hK : Finite K) (A : K → Scheme.{u})
    (hA : ∀ κ, IsAffine (A κ)) (a : ∀ κ, A κ ⟶ T), (∀ κ, LocallyOfFinitePresentation (a κ)) →
      @IsStandardVCovering T hT K hK A hA a →
      ∀ (V : Scheme.{u}) (j : V ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
        [IsSchemeTheoreticallyDominant j], (∀ κ, Flat (pullback.snd (a κ) j)) →
        HasFlatFppfModification a

/-- A standard V covering which is already flat has a flattening modification, namely the
identity of the base: it is jointly surjective by
`AlgebraicGeometry.IsStandardVCovering.exists_mem_range`. So
`AlgebraicGeometry.StandardVCoveringDenseFlatHasModification` holds on the region where no
blowup is needed. -/
theorem standardVCoveringDenseFlatHasModification_of_flat (T : Scheme.{u}) (hT : IsAffine T)
    (K : Type u) (hK : Finite K) (A : K → Scheme.{u}) (hA : ∀ κ, IsAffine (A κ))
    (a : ∀ κ, A κ ⟶ T) (hflat : ∀ κ, Flat (a κ))
    (hfp : ∀ κ, LocallyOfFinitePresentation (a κ))
    (hstd : @IsStandardVCovering T hT K hK A hA a) : HasFlatFppfModification a :=
  have _ : IsAffine T := hT
  have _ : Finite K := hK
  have _ : ∀ κ, IsAffine (A κ) := hA
  HasFlatFppfModification.of_flat a hflat hfp fun t ↦ hstd.exists_mem_range t

/-- Steps 4 and 5 of the Stacks proof of 0ETR imply the case the generic flatness reduction
leaves, by step 6. -/
theorem standardVCoveringDenseFlatHasPHRefinement_of_modification
    (H : StandardVCoveringDenseFlatHasModification.{u}) :
    StandardVCoveringDenseFlatHasPHRefinement.{u} :=
  fun T hT K hK A hA a hlfp hstd V j _ _ _ hflat ↦
    exists_standardPHCovering_refinement_of_hasFlatFppfModification hT a
      (H T hT K hK A hA a hlfp hstd V j hflat)

/-- **Stacks 0ETR, reduced to steps 4 and 5 of its proof.** Granted
`AlgebraicGeometry.StandardVCoveringDenseFlatHasModification` — the flattening blowup of Stacks
0815 together with the valuative recognition of the flattened family as jointly surjective —
every standard V covering of an affine scheme by morphisms locally of finite presentation is
refined by a standard ph covering, so that
`AlgebraicGeometry.StandardVCoveringHasPHRefinement` holds. -/
theorem standardVCoveringHasPHRefinement_of_modification
    (H : StandardVCoveringDenseFlatHasModification.{u}) :
    StandardVCoveringHasPHRefinement.{u} :=
  standardVCoveringHasPHRefinement_of_denseFlat
    (standardVCoveringDenseFlatHasPHRefinement_of_modification H)

end AlgebraicGeometry

end
