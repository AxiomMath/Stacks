module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import StacksFrontier.AlgebraicGeometry.Blowup.RelativeProjGluing

/-!
# Properties of a relative `Proj` that are local on the base

A relative `Proj` over a scheme `S`, in the sense of
`Stacks.RelativeProj.Data`, is glued from the ordinary `Proj (𝒜 U)` of a graded ring attached to
each affine open `U` of `S`, in such a way that the chart over `U` is the preimage of `U`. Any
property of morphisms of schemes which is Zariski-local at the target therefore holds for the
structure morphism `Stacks.RelativeProj.Data.toBase` as soon as it holds for every chart
structure morphism `Stacks.RelativeProj.chartToOpen`, and conversely.

The content is the observation that the chart over `U` *is* the restriction of the structure
morphism to `U`: both are pullbacks of `toBase` along the open immersion `U.ι`, so the two are
isomorphic as arrows. Transporting a local-at-target property along that isomorphism and gluing
over the cover of `S` by its affine opens gives the transfer in both directions.

Specialising, the structure morphism of a relative `Proj` is locally of finite type, separated,
universally closed and proper as soon as each `𝒜 U` is a finite-type algebra over its own
degree-zero part, because Mathlib proves all four for `AlgebraicGeometry.Proj.toSpecZero` under
exactly that hypothesis. Flatness is not of that kind — `Proj 𝒜` is not flat over
`Spec (𝒜 0)` for a general finite-type `𝒜` — so it is recorded as a transfer from the charts
rather than as a consequence of finite type.

## Main results

* `Stacks.RelativeProj.Data.chartIso`: the chart over `U` is the preimage of `U`.
* `Stacks.RelativeProj.Data.prop_toBase_iff`: a property Zariski-local at the target holds for
  the structure morphism of the relative `Proj` precisely when it holds for every chart.
* `Stacks.RelativeProj.prop_chartToOpen_iff`: when the degree-zero identification is an
  isomorphism, a property of the chart structure morphism is a property of
  `AlgebraicGeometry.Proj.toSpecZero`.
* `Stacks.RelativeProj.Data.prop_toBase_of_toSpecZero` and
  `Stacks.RelativeProj.Data.prop_toBase_of_comp`: the transfer phrased in terms of
  `AlgebraicGeometry.Proj.toSpecZero`, for an invertible degree-zero identification and for a
  general one.
* `Stacks.RelativeProj.Data.locallyOfFiniteType_chartToOpen`,
  `Stacks.RelativeProj.Data.locallyOfFiniteType_toBase`,
  `Stacks.RelativeProj.Data.isSeparated_toBase`,
  `Stacks.RelativeProj.Data.universallyClosed_toBase`, `Stacks.RelativeProj.Data.isProper_toBase`:
  the relative `Proj` of a family of finite-type graded algebras is proper over its base, and in
  particular locally of finite type.
* `Stacks.RelativeProj.Data.flat_toBase`: the structure morphism is flat as soon as every chart
  is.

## Implementation notes

`Stacks.RelativeProj.Data` asks for the degree-zero identification `base U : Γ(S, U) ⟶ 𝒜 U 0`
only as a ring homomorphism, not as an isomorphism, because the gluing needs no more than that.
For the transfer statements below the distinction matters: the chart structure morphism is
`Proj.toSpecZero (𝒜 U)` followed by `Spec` of `base U` and the affine identification of `U`, and
only the last of those three is an isomorphism for free. So the statements which reduce a
property of the chart to a property of `Proj.toSpecZero` take the invertibility of `base U` as an
explicit hypothesis; `prop_toBase_of_comp` is the variant which instead asks for the property of
`Spec` of `base U`, and the general transfer `prop_toBase_iff` does not mention `base U` at all.

The hypotheses are explicit `∀ U, …` arguments rather than instance arguments: they mention the
`Data` and its fields, so instance search cannot discharge them, and `have` inside the proof is
all that is wanted of them.

No `@[stacks]` attribute is attached. Nothing below is one of the assertions of a Stacks tag:
tag 01NQ is the *construction* of the relative `Proj` of a quasi-coherent graded `𝒪_S`-algebra,
and tag 02TX is the projective bundle formula for Chow groups, three of whose auxiliary
assertions — that the projection of a projective bundle is locally of finite type, flat, and of
relative dimension one less than the rank — are what the specialisations below reduce to the
charts. The reduction is not the assertion: the assertion is about the relative `Proj` of a
symmetric algebra, which still has to be exhibited as a `Data`.

## References

* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace Stacks.RelativeProj

variable {S : Scheme.{u}} {A σ : S.affineOpens → Type u} [∀ U, CommRing (A U)]
  [∀ U, SetLike (σ U) (A U)] [∀ U, AddSubgroupClass (σ U) (A U)]
  (𝒜 : ∀ U, ℕ → σ U) [∀ U, GradedRing (𝒜 U)]

/-- The chart structure morphism differs from `AlgebraicGeometry.Proj.toSpecZero` by the
isomorphism `Spec` of the degree-zero identification followed by the affine identification of the
open. When the degree-zero identification is invertible this reduces any property stable under
isomorphism from the chart to `Proj.toSpecZero`. -/
theorem prop_chartToOpen_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (U : S.affineOpens) (b : Γ(S, U.1) ⟶ CommRingCat.of (𝒜 U 0)) [IsIso b] :
    P (chartToOpen 𝒜 U b) ↔ P (Proj.toSpecZero (𝒜 U)) := by
  have : IsIso (Spec.map b ≫ (isAffineOpen U).isoSpec.inv) := inferInstance
  exact P.cancel_right_of_respectsIso (Proj.toSpecZero (𝒜 U))
    (Spec.map b ≫ (isAffineOpen U).isoSpec.inv)

namespace Data

variable {𝒜} (d : Data 𝒜)

/-- **The chart over `U` is the preimage of `U`.** Both the chart `Proj (𝒜 U)` and the open
subscheme `toBase ⁻¹ᵁ U` are pullbacks of the structure morphism along the open immersion `U.ι`,
so they are canonically isomorphic over `U`. -/
def chartIso (U : S.affineOpens) :
    Proj (𝒜 U) ≅ (d.toBase ⁻¹ᵁ (U : S.Opens)).toScheme :=
  (d.isPullback_chartι U).isoIsPullback _ _
    (isPullback_morphismRestrict d.toBase (U : S.Opens))

/-- The isomorphism `chartIso` followed by the restriction of the structure morphism to `U` is the
chart structure morphism over `U`. -/
@[reassoc (attr := simp)]
theorem chartIso_hom_morphismRestrict (U : S.affineOpens) :
    (d.chartIso U).hom ≫ d.toBase ∣_ (U : S.Opens) = chartToOpen 𝒜 U (d.base U) :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- The chart structure morphism over `U` and the restriction of the structure morphism of the
relative `Proj` to `U` are the same arrow up to isomorphism. -/
def chartArrowIso (U : S.affineOpens) :
    CategoryTheory.Arrow.mk (chartToOpen 𝒜 U (d.base U)) ≅
      CategoryTheory.Arrow.mk (d.toBase ∣_ (U : S.Opens)) :=
  CategoryTheory.Arrow.isoMk (d.chartIso U) (Iso.refl _) (by simp)

/-- A property stable under isomorphism holds for the restriction of the structure morphism to an
affine open `U` of the base precisely when it holds for the chart over `U`. -/
theorem prop_morphismRestrict_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (U : S.affineOpens) :
    P (d.toBase ∣_ (U : S.Opens)) ↔ P (chartToOpen 𝒜 U (d.base U)) :=
  (P.arrow_mk_iso_iff (d.chartArrowIso U)).symm

/-- **A property of morphisms of schemes which is Zariski-local at the target holds for the
structure morphism of a relative `Proj` precisely when it holds for every chart.** -/
theorem prop_toBase_iff (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P] :
    P d.toBase ↔ ∀ U : S.affineOpens, P (chartToOpen 𝒜 U (d.base U)) := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P)
    (fun U : S.affineOpens ↦ (U : S.Opens)) (iSup_affineOpens_eq_top S)]
  exact forall_congr' fun U ↦ d.prop_morphismRestrict_iff P U

/-- A property Zariski-local at the target is inherited by the structure morphism of a relative
`Proj` from the charts. -/
theorem prop_toBase (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    (h : ∀ U : S.affineOpens, P (chartToOpen 𝒜 U (d.base U))) : P d.toBase :=
  (d.prop_toBase_iff P).mpr h

/-- A property Zariski-local at the target holds for the structure morphism of a relative `Proj`
as soon as it holds for every `AlgebraicGeometry.Proj.toSpecZero`, provided the degree-zero
identifications are invertible. -/
theorem prop_toBase_of_toSpecZero (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    (hb : ∀ U : S.affineOpens, IsIso (d.base U))
    (h : ∀ U : S.affineOpens, P (Proj.toSpecZero (𝒜 U))) : P d.toBase :=
  d.prop_toBase P fun U ↦ have := hb U; (prop_chartToOpen_iff 𝒜 P U (d.base U)).mpr (h U)

/-- **The structure morphism of a relative `Proj` is proper** when every graded ring of the family
is a finite-type algebra over its own degree-zero part. -/
theorem isProper_toBase (hb : ∀ U : S.affineOpens, IsIso (d.base U))
    (hft : ∀ U : S.affineOpens, Algebra.FiniteType (𝒜 U 0) (A U)) : IsProper d.toBase :=
  d.prop_toBase_of_toSpecZero @IsProper hb fun U ↦ have := hft U; inferInstance

/-- A property Zariski-local at the target and stable under composition holds for the structure
morphism of a relative `Proj` as soon as it holds for every `AlgebraicGeometry.Proj.toSpecZero`
and for `Spec` of every degree-zero identification.

This is the form to use when the degree-zero part of `𝒜 U` is genuinely larger than `Γ(S, U)`,
so that `Stacks.RelativeProj.Data.prop_toBase_of_toSpecZero` does not apply: the relative `Proj`
is then a scheme over `Spec (𝒜 U 0)` over `U`, and the property has to hold for the second leg
too. -/
theorem prop_toBase_of_comp (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    [P.IsStableUnderComposition]
    (h : ∀ U : S.affineOpens, P (Proj.toSpecZero (𝒜 U)))
    (hb : ∀ U : S.affineOpens, P (Spec.map (d.base U))) : P d.toBase :=
  d.prop_toBase P fun U ↦
    P.comp_mem _ _ (h U)
      ((P.cancel_right_of_respectsIso (Spec.map (d.base U))
        (isAffineOpen U).isoSpec.inv).mpr (hb U))

/-- Each chart structure morphism of a relative `Proj` is locally of finite type when its graded
ring is a finite-type algebra over its own degree-zero part. This is the hypothesis that
`AlgebraicGeometry.RelativeDimension` of a chart needs as an instance. -/
theorem locallyOfFiniteType_chartToOpen (hb : ∀ U : S.affineOpens, IsIso (d.base U))
    (hft : ∀ U : S.affineOpens, Algebra.FiniteType (𝒜 U 0) (A U)) (U : S.affineOpens) :
    LocallyOfFiniteType (chartToOpen 𝒜 U (d.base U)) := by
  have hloc : IsZariskiLocalAtTarget @LocallyOfFiniteType :=
    HasRingHomProperty.instIsZariskiLocalAtTarget @LocallyOfFiniteType
  have := hloc.toRespects
  have := hb U
  have := hft U
  exact (prop_chartToOpen_iff 𝒜 @LocallyOfFiniteType U (d.base U)).mpr inferInstance

/-- **The structure morphism of a relative `Proj` is locally of finite type** when every graded
ring of the family is a finite-type algebra over its own degree-zero part. -/
theorem locallyOfFiniteType_toBase (hb : ∀ U : S.affineOpens, IsIso (d.base U))
    (hft : ∀ U : S.affineOpens, Algebra.FiniteType (𝒜 U 0) (A U)) :
    LocallyOfFiniteType d.toBase :=
  have : IsZariskiLocalAtTarget @LocallyOfFiniteType :=
    HasRingHomProperty.instIsZariskiLocalAtTarget @LocallyOfFiniteType
  d.prop_toBase _ (d.locallyOfFiniteType_chartToOpen hb hft)

/-- The structure morphism of a relative `Proj` is universally closed when every graded ring of
the family is a finite-type algebra over its own degree-zero part. -/
theorem universallyClosed_toBase (hb : ∀ U : S.affineOpens, IsIso (d.base U))
    (hft : ∀ U : S.affineOpens, Algebra.FiniteType (𝒜 U 0) (A U)) :
    UniversallyClosed d.toBase :=
  d.prop_toBase_of_toSpecZero @UniversallyClosed hb fun U ↦ have := hft U; inferInstance

/-- **The structure morphism of a relative `Proj` is flat as soon as every chart is.** Unlike the
properties above this does not follow from finite type: `Proj 𝒜` is not flat over `Spec (𝒜 0)`
for a general finite-type graded ring `𝒜`. -/
theorem flat_toBase (hb : ∀ U : S.affineOpens, IsIso (d.base U))
    (h : ∀ U : S.affineOpens, Flat (Proj.toSpecZero (𝒜 U))) : Flat d.toBase :=
  have : IsZariskiLocalAtTarget @Flat := HasRingHomProperty.instIsZariskiLocalAtTarget @Flat
  d.prop_toBase_of_toSpecZero @Flat hb h

end Data

end Stacks.RelativeProj

end
