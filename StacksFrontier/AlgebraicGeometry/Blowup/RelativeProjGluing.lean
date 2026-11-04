module

public import Mathlib.AlgebraicGeometry.RelativeGluing
public import StacksFrontier.AlgebraicGeometry.Blowup.RelativeProj

/-!
# Relative `Proj` by gluing the affine charts

Let `S` be a scheme and let `𝒜` be a family of graded rings indexed by the affine opens of `S`,
with a degree-zero identification `Γ(S, U) ⟶ 𝒜 U 0` and a restriction map `𝒜 V →+*ᵍ 𝒜 U` for
every inclusion `U ≤ V` of affine opens. Each chart `Proj (𝒜 U)` is then a scheme over `U`, and
the restrictions induce morphisms `Proj (𝒜 U) ⟶ Proj (𝒜 V)` over `U ⟶ V`. If those squares are
cartesian, the charts glue to a single scheme over `S`: the *relative `Proj`* of the family.

The gluing itself is Mathlib's `AlgebraicGeometry.Scheme.Cover.RelativeGluingData.glued`, which
is the relative gluing lemma of Stacks tag 01LH, applied to the locally directed cover of `S` by
all of its affine opens (`AlgebraicGeometry.Scheme.directedAffineCover`). What this file supplies
is the datum: the diagram of charts, the natural transformation to the cover, and the proof that
it is equifibered.

## Main definitions

* `Stacks.RelativeProj.chartToOpen` is the structure morphism `Proj (𝒜 U) ⟶ U` of a chart.
* `Stacks.RelativeProj.Data` is the local data a relative `Proj` is glued from.
* `Stacks.RelativeProj.Data.functor` is the diagram `U ↦ Proj (𝒜 U)` of charts.
* `Stacks.RelativeProj.Data.gluingData` is the induced relative gluing datum.
* `Stacks.RelativeProj.Data.relativeProj` is the glued scheme.
* `Stacks.RelativeProj.Data.toBase` is its structure morphism to `S`.
* `Stacks.RelativeProj.Data.chartι` is the open immersion of a chart into the glued scheme.

## Main results

* `Stacks.RelativeProj.isoSpec_inv_homOfLE`: the inclusion of one affine open into another is
  `Spec` of the restriction map, read through the two affine identifications.
* `Stacks.RelativeProj.Data.commSq`: the chart morphisms are morphisms over the base.
* `Stacks.RelativeProj.Data.isPullback`: the chart squares are cartesian.
* `Stacks.RelativeProj.Data.isPullback_chartι`: the chart over `U` is the preimage of `U` in the
  glued scheme. This is the defining property of a relative `Proj`.
* `Stacks.RelativeProj.Data.toBase_preimage_coe`: the same statement at the level of opens.
* `Stacks.RelativeProj.Data.iSup_opensRange_chartι`: the charts cover the glued scheme.

## Implementation notes

The cartesian condition is *not* a field of `Data`; what is asked for instead is that each
`Proj.map` be an open immersion and that its image be the preimage of the corresponding open of
the base. By `AlgebraicGeometry.IsOpenImmersion.isPullback` those two conditions are equivalent
to the square being cartesian, and they are what one actually checks: both are statements about
the topology of `Proj`, with no limits involved. The compatibility of the restriction maps with
the degree-zero identifications is asked for at the level of rings; it is turned into the
commuting square of schemes by `AlgebraicGeometry.Proj.map_toSpecZero` together with
`Stacks.RelativeProj.isoSpec_inv_homOfLE`.

For the blowup of a scheme `S` in a quasi-coherent ideal sheaf `ℐ`, the intended instance has
`A U := reesAlgebra (ℐ U)` with `𝒜 U := Stacks.Blowup.reesGrading (ℐ U)` from
`StacksFrontier/AlgebraicGeometry/Blowup/ReesGrading.lean`, and `base U` the degree-zero
identification `Stacks.Blowup.reesGradingZeroEquiv`; the charts `Proj (𝒜 U)` are then the affine
blowups `Stacks.Blowup.blowUpSpec (ℐ U)`. The computation of the left-hand side of
`opensRange_map` for such an instance is what
`AlgebraicGeometry.Proj.toSpecZero_preimage_basicOpen` is for.

No `@[stacks]` attribute is attached here. Tag 01NQ is the relative `Proj` of a quasi-coherent
graded `𝒪_S`-algebra, and the hypothesis `Data.opensRange_map` — that the comparison
`Proj (𝒜 U) ⟶ Proj (𝒜 V)` is an open immersion onto the preimage of `U`, i.e. tag 01NO — is
proved in `StacksFrontier/AlgebraicGeometry/RelativeProj/Charts/` by
`Situation.projInclusionDomain_eq_top` and `Situation.projInclusion_isPullback`, via a degreewise
graded localization rather than a base change. `Situation.chartData` is the resulting
unconditional `Data`, and tag 01NQ is attached to `relativeProj` and its companions in
`StacksFrontier/AlgebraicGeometry/RelativeProj/Charts/Descent.lean`.

This file holds the general gluing machinery and `Data`.

## References

* [Stacks Project, Tag 01LH](https://stacks.math.columbia.edu/tag/01LH)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry HomogeneousIdeal Graded

universe u

namespace Stacks.RelativeProj

variable {S : Scheme.{u}} {A σ : S.affineOpens → Type u} [∀ U, CommRing (A U)]
  [∀ U, SetLike (σ U) (A U)] [∀ U, AddSubgroupClass (σ U) (A U)]
  (𝒜 : ∀ U, ℕ → σ U) [∀ U, GradedRing (𝒜 U)]

/-- A member of `S.affineOpens` is an affine open. The membership proof and the predicate are the
same statement, but only this spelling has the predicate as its type, which is what the lemmas
about `IsAffineOpen.isoSpec` need in order to rewrite. -/
theorem isAffineOpen (U : S.affineOpens) : IsAffineOpen (U : S.Opens) := U.2

/-- The structure morphism `Proj (𝒜 U) ⟶ U` of the chart over an affine open `U`: the structure
morphism of `Proj` to `Spec` of its degree-zero part, followed by `Spec` of the identification
`b` of that degree-zero part with the sections over `U`, followed by the affine identification of
`U` with `Spec Γ(S, U)`. -/
def chartToOpen (U : S.affineOpens) (b : Γ(S, U.1) ⟶ CommRingCat.of (𝒜 U 0)) :
    Proj (𝒜 U) ⟶ U.1.toScheme :=
  Proj.toSpecZero (𝒜 U) ≫ Spec.map b ≫ (isAffineOpen U).isoSpec.inv

/-- For affine opens `U ≤ V` of a scheme, the inclusion `U ⟶ V` is `Spec` of the restriction map
`Γ(S, V) ⟶ Γ(S, U)` read through the identifications of `U` and `V` with the spectra of their
rings of sections. -/
theorem isoSpec_inv_homOfLE {U V : S.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : U ≤ V) :
    hU.isoSpec.inv ≫ S.homOfLE h = Spec.map (S.presheaf.map (homOfLE h).op) ≫ hV.isoSpec.inv := by
  rw [← cancel_mono V.ι, Category.assoc, Category.assoc, Scheme.homOfLE_ι,
    IsAffineOpen.isoSpec_inv_ι, IsAffineOpen.isoSpec_inv_ι,
    IsAffineOpen.map_fromSpec hV hU (homOfLE h).op]

/-- The local data a relative `Proj` is glued from: a graded ring for every affine open of the
base, an identification of its degree-zero part with the sections of the base, and restriction
maps along inclusions of affine opens which are open immersions on `Proj` with the expected
image.

The fields `restrict_id` and `restrict_comp` make the restrictions functorial, `base_restrict`
makes them compatible with the degree-zero identifications, and `isOpenImmersion_map` together
with `opensRange_map` say that `Proj (𝒜 U)` is the preimage of `U` in `Proj (𝒜 V)`. -/
structure Data where
  /-- The identification of the degree-zero part of `𝒜 U` with the sections of `S` over `U`. -/
  base (U : S.affineOpens) : Γ(S, U.1) ⟶ CommRingCat.of (𝒜 U 0)
  /-- The restriction map of graded rings along an inclusion of affine opens. -/
  restrict {U V : S.affineOpens} (h : U ≤ V) : 𝒜 V →+*ᵍ 𝒜 U
  /-- The irrelevant ideal of `𝒜 U` is covered by that of `𝒜 V`, so that `Proj.map` applies. -/
  irrelevant_le {U V : S.affineOpens} (h : U ≤ V) : (𝒜 U)₊ ≤ ((𝒜 V)₊).map (restrict h)
  /-- Restricting along the identity is the identity. -/
  restrict_id (U : S.affineOpens) : restrict (le_refl U) = GradedRingHom.id (𝒜 U)
  /-- Restriction is functorial. -/
  restrict_comp {U V W : S.affineOpens} (hUV : U ≤ V) (hVW : V ≤ W) :
    restrict (hUV.trans hVW) = (restrict hUV).comp (restrict hVW)
  /-- Restriction is compatible with the degree-zero identifications. -/
  base_restrict {U V : S.affineOpens} (h : U ≤ V) :
    S.presheaf.map (homOfLE h).op ≫ base U =
      base V ≫ CommRingCat.ofHom (restrict h).gradedZeroRingHom
  /-- `Proj (𝒜 U)` is an open subscheme of `Proj (𝒜 V)`. -/
  isOpenImmersion_map {U V : S.affineOpens} (h : U ≤ V) :
    IsOpenImmersion (Proj.map (restrict h) (irrelevant_le h))
  /-- That open subscheme is the preimage of `U`. -/
  opensRange_map {U V : S.affineOpens} (h : U ≤ V) :
    chartToOpen 𝒜 V (base V) ⁻¹ᵁ (S.homOfLE h).opensRange =
      (Proj.map (restrict h) (irrelevant_le h)).opensRange

namespace Data

variable {𝒜} (d : Data 𝒜)

/-- The comparison morphism `Proj (𝒜 U) ⟶ Proj (𝒜 V)` attached to an inclusion `U ≤ V` of affine
opens of the base. -/
abbrev map {U V : S.affineOpens} (h : U ≤ V) : Proj (𝒜 U) ⟶ Proj (𝒜 V) :=
  Proj.map (d.restrict h) (d.irrelevant_le h)

/-- **The chart morphisms are morphisms over the base.** -/
theorem commSq {U V : S.affineOpens} (h : U ≤ V) :
    d.map h ≫ chartToOpen 𝒜 V (d.base V) = chartToOpen 𝒜 U (d.base U) ≫ S.homOfLE h := by
  rw [chartToOpen, chartToOpen, Proj.map_toSpecZero_assoc, Category.assoc, Category.assoc,
    isoSpec_inv_homOfLE (isAffineOpen U) (isAffineOpen V) h, ← Spec.map_comp_assoc,
    ← Spec.map_comp_assoc]
  exact congrArg
    (fun k ↦ Proj.toSpecZero (𝒜 U) ≫ Spec.map k ≫ (isAffineOpen V).isoSpec.inv)
    (d.base_restrict h).symm

/-- **The chart squares are cartesian.** This is the equifibered condition that the relative
gluing lemma asks for; it follows from the two topological hypotheses of `Data` by
`AlgebraicGeometry.IsOpenImmersion.isPullback`. -/
theorem isPullback {U V : S.affineOpens} (h : U ≤ V) :
    IsPullback (d.map h) (chartToOpen 𝒜 U (d.base U)) (chartToOpen 𝒜 V (d.base V))
      (S.homOfLE h) :=
  have := d.isOpenImmersion_map h
  (IsOpenImmersion.isPullback (chartToOpen 𝒜 U (d.base U)) (d.map h) (S.homOfLE h)
    (chartToOpen 𝒜 V (d.base V)) (d.commSq h) (d.opensRange_map h)).flip

/-- The diagram of charts: the affine opens of `S`, ordered by inclusion, sent to the `Proj` of
the corresponding graded ring. -/
def functor : S.affineOpens ⥤ Scheme.{u} where
  obj U := Proj (𝒜 U)
  map {_ _} h := d.map (leOfHom h)
  map_id U := (Proj.map_congr (d.restrict_id U) (d.irrelevant_le _) (by simp)).trans Proj.map_id
  map_comp {_ _ _} f g :=
    (Proj.map_congr (d.restrict_comp (leOfHom f) (leOfHom g)) (d.irrelevant_le _)
        (irrelevant_le_map_comp (d.irrelevant_le (leOfHom g))
          (d.irrelevant_le (leOfHom f)))).trans (Proj.map_comp _ _ _ _)

/-- The chart structure morphisms, as a natural transformation from the diagram of charts to the
diagram of affine opens of the base. -/
def natTrans : d.functor ⟶ S.directedAffineCover.functorOfLocallyDirected where
  app U := chartToOpen 𝒜 U (d.base U)
  naturality _ _ h := d.commSq (leOfHom h)

/-- The relative gluing datum over the locally directed cover of `S` by all of its affine
opens. -/
def gluingData : Scheme.Cover.RelativeGluingData S.directedAffineCover where
  functor := d.functor
  natTrans := d.natTrans
  equifibered _ _ h := d.isPullback (leOfHom h)

/-- **The relative `Proj` of the family `𝒜`:** the scheme obtained by gluing the charts
`Proj (𝒜 U)` along the affine opens of `S`. -/
def relativeProj : Scheme.{u} := d.gluingData.glued

/-- The structure morphism of the relative `Proj` to its base. -/
def toBase : d.relativeProj ⟶ S := d.gluingData.toBase

/-- The chart over an affine open `U` of the base, as a morphism into the relative `Proj`. -/
def chartι (U : S.affineOpens) : Proj (𝒜 U) ⟶ d.relativeProj :=
  colimit.ι d.gluingData.functor U

/-- **The chart over `U` is the preimage of `U` in the relative `Proj`.** This is the defining
property of a relative `Proj`: it is a scheme over `S` whose restriction to each affine open `U`
of the base is `Proj (𝒜 U)`. -/
theorem isPullback_chartι (U : S.affineOpens) :
    IsPullback (chartToOpen 𝒜 U (d.base U)) (d.chartι U) U.1.ι d.toBase :=
  d.gluingData.isPullback_natTrans_ι_toBase U

/-- The chart over an affine open of the base is an open immersion into the relative `Proj`. -/
instance isOpenImmersion_chartι (U : S.affineOpens) : IsOpenImmersion (d.chartι U) :=
  MorphismProperty.of_isPullback (d.isPullback_chartι U) inferInstance

/-- The relative `Proj` is canonically a scheme over the base. -/
instance over : d.relativeProj.CanonicallyOver S where
  hom := d.toBase

/-- The chart over `U` is the preimage of `U`, as an open subset of the relative `Proj`. -/
theorem toBase_preimage_coe (U : S.affineOpens) :
    d.toBase ⁻¹ᵁ (U : S.Opens) = (d.chartι U).opensRange := by
  rw [← Scheme.Opens.opensRange_ι (U : S.Opens)]
  exact d.gluingData.toBase_preimage_eq_opensRange_ι U

/-- The charts cover the relative `Proj`. -/
theorem iSup_opensRange_chartι : ⨆ U : S.affineOpens, (d.chartι U).opensRange = ⊤ := by
  refine top_le_iff.mp fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ?_
  obtain ⟨U, y, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective d.gluingData.functor x
  exact ⟨U, y, rfl⟩

/-- The structure morphism of the relative `Proj` restricts on each chart to the chart's own
structure morphism. -/
@[reassoc]
theorem chartι_toBase (U : S.affineOpens) :
    d.chartι U ≫ d.toBase = chartToOpen 𝒜 U (d.base U) ≫ U.1.ι :=
  ((d.isPullback_chartι U).w).symm

end Data

end Stacks.RelativeProj

end
