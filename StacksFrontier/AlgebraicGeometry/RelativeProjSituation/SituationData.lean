module

public import StacksFrontier.AlgebraicGeometry.Blowup.RelativeProjGluing
public import StacksFrontier.AlgebraicGeometry.Constructions.RelativeProjSectionRings

/-!
# From the relative `Proj` situation to the relative `Proj` gluing datum

The input of relative `Proj` is a `Stacks.RelativeProj.Situation`: a scheme `S` together with a
quasi-coherent, commutative, nonnegatively graded `𝒪_S`-algebra `𝒜`. What the gluing
construction of `StacksFrontier/AlgebraicGeometry/Blowup/RelativeProjGluing.lean` consumes is a
`Stacks.RelativeProj.Data`: an honest graded ring for every affine open of `S`, with restriction
maps, a degree-zero identification, and the two topological conditions that make the charts fit
together.

This file builds the second from the first. The graded rings are the rings
`Stacks.RelativeProj.Situation.sectionRing` of homogeneous local sections, graded by
`Stacks.RelativeProj.Situation.sectionRingGrading`, with their restriction maps as homomorphisms
of graded rings, and with the degree-zero part identified with the sections of the structure
sheaf compatibly with restriction.

## Main definitions

* `Stacks.RelativeProj.Situation.gradedRestrict` is the restriction map of section rings along an
  inclusion of opens, as a homomorphism of graded rings.
* `Stacks.RelativeProj.Situation.baseHom` is the degree-zero identification
  `Γ(S, U) ⟶ 𝒜(U)₀`.
* `Stacks.RelativeProj.Situation.ChartsCartesian` is the condition that the comparison morphisms
  of charts are defined, are open immersions, and have image the preimage of the smaller open.
* `Stacks.RelativeProj.Situation.data` assembles a `Stacks.RelativeProj.Data` from a situation
  satisfying that condition.

## Main results

* `Stacks.RelativeProj.Situation.gradedRestrict_id` and
  `Stacks.RelativeProj.Situation.gradedRestrict_comp`: the graded restrictions are functorial.
* `Stacks.RelativeProj.Situation.baseHom_gradedRestrict`: the degree-zero identifications commute
  with restriction.
* `Stacks.RelativeProj.Situation.map_chartToOpen`: the chart morphisms of a situation are
  morphisms over the base.
* `Stacks.RelativeProj.Situation.ChartsCartesian.isPullback`: under
  `Stacks.RelativeProj.Situation.ChartsCartesian`, the square of charts over `U ≤ V` is
  cartesian.
* `Stacks.RelativeProj.Situation.data_relativeProj_isPullback`: for a situation, the chart over an
  affine open `U` is the preimage of `U` in the glued scheme, and
  `Stacks.RelativeProj.Situation.data_map_chartι`: the charts are compatible with the comparison
  morphisms.

## Implementation notes

The three fields of `Stacks.RelativeProj.Situation.ChartsCartesian` are: that the irrelevant
ideal of `𝒜(U)` is covered by that of `𝒜(V)`, so that the comparison morphism
`Proj 𝒜(U) ⟶ Proj 𝒜(V)` exists; that the comparison is an open immersion; and that its image is
the preimage of `U`. By `AlgebraicGeometry.IsOpenImmersion.isPullback` the last two say that the
square of charts is cartesian, and conversely a cartesian square over the open immersion
`U ⟶ V` has both of them.

The degree-zero identification is the composite of
`Stacks.RelativeProj.Situation.sectionRingBaseMap` with the degree-zero projection
`GradedRing.projZeroRingHom'`, so that `Stacks.RelativeProj.Situation.baseHom_gradedRestrict`
follows from `GradedRingHom.map_directSumDecompose`.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01NP](https://stacks.math.columbia.edu/tag/01NP)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite HomogeneousIdeal Graded

universe u

namespace Stacks.RelativeProj.Situation

variable (s : Situation.{u})

/-! ### The graded restriction maps -/

/-- Restriction of homogeneous local sections along an inclusion `U ≤ V` of opens, as a
homomorphism of graded rings: the ring homomorphism is
`Stacks.RelativeProj.Situation.sectionRingRestrict`, and it preserves degrees because on a
homogeneous section it is the restriction in that homogeneous piece. -/
public def gradedRestrict {U V : s.base.Opens} (h : U ≤ V) :
    s.sectionRingGrading V →+*ᵍ s.sectionRingGrading U where
  toRingHom := s.sectionRingRestrict U V h
  map_mem := by
    rintro n x ⟨a, rfl⟩
    exact ⟨_, ((sectionRingStructure s).restrict_of U V h n a).symm⟩

/-- The graded restriction map is `Stacks.RelativeProj.Situation.sectionRingRestrict` on
elements. -/
@[simp]
public theorem gradedRestrict_apply {U V : s.base.Opens} (h : U ≤ V) (x : s.sectionRing V) :
    s.gradedRestrict h x = s.sectionRingRestrict U V h x :=
  rfl

/-- Restricting along the identity is the identity. -/
public theorem gradedRestrict_id (U : s.base.Opens) :
    s.gradedRestrict (le_refl U) = GradedRingHom.id (s.sectionRingGrading U) := by
  refine GradedRingHom.ext fun x ↦ ?_
  rw [gradedRestrict_apply, GradedRingHom.id_apply, sectionRingRestrict,
    (sectionRingStructure s).restrict_id U]
  rfl

/-- The graded restrictions are functorial. -/
public theorem gradedRestrict_comp {U V W : s.base.Opens} (hUV : U ≤ V) (hVW : V ≤ W) :
    s.gradedRestrict (hUV.trans hVW) = (s.gradedRestrict hUV).comp (s.gradedRestrict hVW) := by
  refine GradedRingHom.ext fun x ↦ ?_
  rw [gradedRestrict_apply, GradedRingHom.comp_apply, gradedRestrict_apply, gradedRestrict_apply,
    sectionRingRestrict, sectionRingRestrict, sectionRingRestrict,
    (sectionRingStructure s).restrict_comp U V W hUV hVW]
  rfl

/-! ### The degree-zero identification -/

/-- The identification of the degree-zero part of the graded ring of sections over `U` with the
sections of the structure sheaf over `U`: the canonical map
`Stacks.RelativeProj.Situation.sectionRingBaseMap` followed by the projection to degree zero,
which is the identity on its image. -/
public def baseHom (U : s.base.Opens) :
    Γ(s.base, U) ⟶ CommRingCat.of (s.sectionRingGrading U 0) :=
  CommRingCat.ofHom
    ((GradedRing.projZeroRingHom' (s.sectionRingGrading U)).comp (s.sectionRingBaseMap U))

/-- The canonical map to the graded section ring lands in degree zero. -/
public theorem sectionRingBaseMap_mem (U : s.base.Opens) (r : Γ(s.base, U)) :
    s.sectionRingBaseMap U r ∈ s.sectionRingGrading U 0 := by
  change (sectionRingStructure s).baseMap U r ∈ _
  rw [(sectionRingStructure s).baseMap_apply U r]
  exact ⟨_, rfl⟩

/-- The degree-zero identification is the canonical map, read inside the section ring. -/
public theorem baseHom_apply_coe (U : s.base.Opens) (r : Γ(s.base, U)) :
    ((s.baseHom U) r : s.sectionRing U) = s.sectionRingBaseMap U r := by
  change (GradedRing.projZeroRingHom' (s.sectionRingGrading U)
    (s.sectionRingBaseMap U r) : s.sectionRing U) = _
  rw [GradedRing.projZeroRingHom'_apply_coe _
    (⟨s.sectionRingBaseMap U r, s.sectionRingBaseMap_mem U r⟩ : s.sectionRingGrading U 0)]

/-- The degree-zero identifications commute with restriction. -/
public theorem baseHom_gradedRestrict {U V : s.base.Opens} (h : U ≤ V) :
    s.base.presheaf.map (homOfLE h).op ≫ s.baseHom U =
      s.baseHom V ≫ CommRingCat.ofHom (s.gradedRestrict h).gradedZeroRingHom := by
  refine CommRingCat.hom_ext (RingHom.ext fun r ↦ Subtype.ext ?_)
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply, baseHom_apply_coe,
    CommRingCat.ofHom_apply]
  change _ = s.gradedRestrict h ((s.baseHom V) r : s.sectionRing V)
  rw [gradedRestrict_apply, baseHom_apply_coe]
  exact ((sectionRingStructure s).restrict_baseMap U V h r).symm

/-! ### The gluing datum -/

/-- The family of graded rings of a situation, indexed by the affine opens of the base: the
grading of `Stacks.RelativeProj.Situation.sectionRing` by its homogeneous summands. -/
public abbrev chartGrading (U : s.base.affineOpens) : ℕ → AddSubgroup (s.sectionRing U.1) :=
  s.sectionRingGrading U.1

/-- The comparison morphism of charts over affine opens `U ≤ V` commutes with the chart
morphisms to the base opens and the inclusion `U ⟶ V`. -/
public theorem map_chartToOpen {U V : s.base.affineOpens} (h : U ≤ V)
    (hirr : (s.chartGrading U)₊ ≤ ((s.chartGrading V)₊).map (s.gradedRestrict h)) :
    Proj.map (s.gradedRestrict h) hirr ≫ chartToOpen (s.chartGrading) V (s.baseHom V.1) =
      chartToOpen (s.chartGrading) U (s.baseHom U.1) ≫ s.base.homOfLE h := by
  rw [chartToOpen, chartToOpen, Proj.map_toSpecZero_assoc, Category.assoc, Category.assoc,
    isoSpec_inv_homOfLE (isAffineOpen U) (isAffineOpen V) h, ← Spec.map_comp_assoc,
    ← Spec.map_comp_assoc]
  exact congrArg
    (fun k ↦ Proj.toSpecZero (s.chartGrading U) ≫ Spec.map k ≫ (isAffineOpen V).isoSpec.inv)
    (s.baseHom_gradedRestrict h).symm

/-- For every inclusion `U ≤ V` of affine opens of the base, the irrelevant ideal of `𝒜(U)` is
covered by that of `𝒜(V)`, so that the comparison morphism `Proj 𝒜(U) ⟶ Proj 𝒜(V)` is defined,
and that comparison is an open immersion whose image is the preimage of `U`. -/
public structure ChartsCartesian : Prop where
  /-- The irrelevant ideal of `𝒜(U)` is covered by that of `𝒜(V)`. -/
  irrelevant_le : ∀ {U V : s.base.affineOpens} (h : U ≤ V),
    (s.chartGrading U)₊ ≤ ((s.chartGrading V)₊).map (s.gradedRestrict h)
  /-- The comparison morphism is an open immersion. -/
  isOpenImmersion_map : ∀ {U V : s.base.affineOpens} (h : U ≤ V),
    IsOpenImmersion (Proj.map (s.gradedRestrict h) (irrelevant_le h))
  /-- Its image is the preimage of `U`. -/
  opensRange_map : ∀ {U V : s.base.affineOpens} (h : U ≤ V),
    chartToOpen (s.chartGrading) V (s.baseHom V.1) ⁻¹ᵁ (s.base.homOfLE h).opensRange =
      (Proj.map (s.gradedRestrict h) (irrelevant_le h)).opensRange

/-- The relative `Proj` gluing datum of a situation satisfying
`Stacks.RelativeProj.Situation.ChartsCartesian`. -/
public def data (hs : s.ChartsCartesian) : Data (s.chartGrading) where
  base U := s.baseHom U.1
  restrict h := s.gradedRestrict h
  irrelevant_le h := hs.irrelevant_le h
  restrict_id U := s.gradedRestrict_id U.1
  restrict_comp hUV hVW := s.gradedRestrict_comp hUV hVW
  base_restrict h := s.baseHom_gradedRestrict h
  isOpenImmersion_map h := hs.isOpenImmersion_map h
  opensRange_map h := hs.opensRange_map h

variable {s} (hs : s.ChartsCartesian)

/-- For affine opens `U ≤ V` of the base, the chart over
`U` is the base change of the chart over `V` along the inclusion `U ⟶ V`. -/
public theorem ChartsCartesian.isPullback {U V : s.base.affineOpens} (h : U ≤ V) :
    IsPullback (Proj.map (s.gradedRestrict h) (hs.irrelevant_le h))
      (chartToOpen (s.chartGrading) U (s.baseHom U.1))
      (chartToOpen (s.chartGrading) V (s.baseHom V.1)) (s.base.homOfLE h) :=
  (s.data hs).isPullback h

/-- For every affine open `U` of the base, the chart
`Proj 𝒜(U)` is the preimage of `U` in the relative `Proj`. -/
public theorem data_relativeProj_isPullback (U : s.base.affineOpens) :
    IsPullback (chartToOpen (s.chartGrading) U (s.baseHom U.1))
      ((s.data hs).chartι U) U.1.ι (s.data hs).toBase :=
  (s.data hs).isPullback_chartι U

/-- For affine opens `U ≤ V` of the base, the comparison morphism `Proj 𝒜(U) ⟶ Proj 𝒜(V)`
followed by the inclusion of the chart of `V` is the inclusion of the chart of `U`. -/
public theorem data_map_chartι {U V : s.base.affineOpens} (h : U ≤ V) :
    Proj.map (s.gradedRestrict h) (hs.irrelevant_le h) ≫ (s.data hs).chartι V =
      (s.data hs).chartι U :=
  colimit.w (s.data hs).gluingData.functor (homOfLE h)

/-- The charts of the relative `Proj` of a situation cover it. -/
public theorem data_iSup_opensRange_chartι :
    ⨆ U : s.base.affineOpens, ((s.data hs).chartι U).opensRange = ⊤ :=
  (s.data hs).iSup_opensRange_chartι

end Stacks.RelativeProj.Situation

end
