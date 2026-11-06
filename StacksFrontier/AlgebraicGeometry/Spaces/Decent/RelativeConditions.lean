module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductClopenSubspaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReasonablePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeDecency
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RepresentablePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.MonomorphicFieldRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.Reasonable

/-!
# Permanence of the relative conditions of Stacks 03KZ

Stacks 03KZ turns each of the conditions "property `(β)`", "decent" and "reasonable" of
Stacks 03JX into a condition on a *morphism* of algebraic spaces, by asking that every base
change of it along a morphism from a representable presheaf into its target have the
corresponding absolute condition. This file proves the three permanence statements about those
conditions: each of them is preserved by arbitrary base change (Stacks 03L0); a morphism whose
source has one of them has it (Stacks 0ABX); and when both a morphism and its target have one
of them, so does its source (Stacks 0ABY).

The base-change statements rest on the invariance of each absolute condition under an
isomorphism of presheaves, because the two iterated fibre products compared by Stacks 03L0 are
isomorphic and not equal; those invariance statements are proved first and are of independent
interest.

## Main results

* `AlgebraicGeometry.Space.isDecentSpace_of_iso`,
  `AlgebraicGeometry.Space.hasFiniteRelationFibersAtEveryPoint_of_iso` and
  `AlgebraicGeometry.Space.isReasonableSpace_of_iso`: decency, property `(β)` and
  reasonableness of an algebraic space are invariant under isomorphism.
* `AlgebraicGeometry.Space.hasPropertyBeta_baseChange`,
  `AlgebraicGeometry.Space.isDecent_baseChange` and
  `AlgebraicGeometry.Space.isReasonable_baseChange` are the three cases of Stacks 03L0.
* `AlgebraicGeometry.Space.hasPropertyBeta_of_hasFiniteRelationFibersAtEveryPoint` and
  `AlgebraicGeometry.Space.isReasonable_of_isReasonableSpace_source` are the cases `(β)` and
  "reasonable" of Stacks 0ABX; the decent case is
  `AlgebraicGeometry.Space.isDecent_of_isDecentSpace_source` in
  `StacksFrontier/AlgebraicGeometry/Spaces/Decent/FieldFibreTopologicalDimension.lean`.
  `AlgebraicGeometry.Space.hasPropertyBeta_of_hasMonomorphicFieldRepresentative` and
  `AlgebraicGeometry.Space.hasMonomorphicFieldRepresentative_pullback_of_source` are the same
  two cases read in condition (4) of Stacks 03JU.
* `AlgebraicGeometry.Space.hasMonomorphicFieldRepresentative_of_target_of_baseChange` is the
  case `(β)` of Stacks 0ABY, and
  `AlgebraicGeometry.Space.hasFiniteRelationFibersAtEveryPoint_of_hasPropertyBeta` is that case
  restated in condition (1) of Stacks 03JU, through
  `AlgebraicGeometry.Space.hasFiniteRelationFiberAt_iff_hasMonomorphicFieldRepresentative`.
* `AlgebraicGeometry.Space.hasPropertyBeta_comp` and
  `AlgebraicGeometry.Space.isDecent_comp` are the cases `(β)` and "decent" of Stacks 03L1:
  property `(β)` and decency of a morphism are preserved by composition. The remaining case
  "reasonable" is `AlgebraicGeometry.Space.isReasonable_comp` in
  `StacksFrontier/AlgebraicGeometry/Spaces/Decent/RelativeReasonablePermanence.lean`, which is
  where the case "reasonable" of Stacks 0ABY that it needs is proved.

## Implementation notes

Each case of Stacks 03L0 is stated for the predicate of Stacks 03KZ built from the absolute
condition it concerns, so each spells its source condition the way that absolute predicate
does: property `(β)` as condition (1) of Stacks 03JU, finiteness of one relation fibre in some
étale chart; decency as condition (4) of Stacks 03JV, a quasi-compact monomorphism from the
spectrum of a field; and reasonableness as condition (2) of Stacks 03JT, universally bounded
fibres of every étale chart by an affine scheme.

Stacks 0ABX and Stacks 0ABY are stated with **condition (4) of Stacks 03JU** — a monomorphism
from the spectrum of a field — in hypothesis and conclusion alike, rather than with condition
(1). That is the condition the source's own proof of the case `(β)` of Stacks 0ABY argues
with, and it is the condition in which Stacks 0ABT is available here, as
`AlgebraicGeometry.Space.hasMonomorphicFieldRepresentative_of_relativelyRepresentable`.
Stacks 03JU **is** now proved in this repository, as the three pairwise equivalences
`AlgebraicGeometry.Space.hasFiniteRelationFiberAt_iff_everyEtaleChart`,
`...hasFiniteRelationFiberAtEveryEtaleChart_iff_hasEtaleQuasiCompactFieldRepresentative` and
`...hasEtaleQuasiCompactFieldRepresentative_iff_hasMonomorphicFieldRepresentative`, so
condition (4) can now be read off condition (1). The case `(β)` of Stacks 0ABX is therefore
stated below with `AlgebraicGeometry.Space.HasFiniteRelationFibersAtEveryPoint` — property
`(β)` as Stacks 03JX spells it — as its hypothesis on the source, the condition-(4) form being
kept as the lemma it is proved from; the same restatement of the case `(β)` of Stacks 0ABY is
`AlgebraicGeometry.Space.hasFiniteRelationFibersAtEveryPoint_of_hasPropertyBeta`.
The conclusion of the condition-(4) form of the decent case of Stacks 0ABX is condition (4) of
Stacks 03JU
at every point of every represented base change, and not
`AlgebraicGeometry.Space.IsDecent`, which asks in addition that the monomorphism be
quasi-compact in the sense of Stacks 03HE. The equivalence of conditions (1) and (4) of
Stacks 03JV, which the source uses to recover that quasi-compactness, **is** available here,
as
`hasFiniteChartAndRelationFibersAt_iff_hasQuasiCompactMonomorphicFieldRepresentative`
in `StacksFrontier/AlgebraicGeometry/Spaces/Decent/QuasiCompactMonomorphicPoint.lean`. What the
hypothesis below does not supply is the other half of property `(γ)` that the equivalence
needs, finiteness of the chart fibres; with decency of the source as hypothesis instead,
`AlgebraicGeometry.Space.IsDecent` of the morphism does follow, by
`AlgebraicGeometry.Space.isDecentSpace_of_relativelyRepresentable` applied to the projection
to the source of each represented base change.

The reasonable case of Stacks 0ABX runs on the case `(δ)` of Stacks 03KF — reasonableness
passes to the source of a representable morphism —
`AlgebraicGeometry.Space.isReasonableSpace_of_relativelyRepresentable` in
`StacksFrontier/AlgebraicGeometry/Spaces/Decent/ReasonablePermanence.lean`, which is the
reasonable half of Stacks 0ABT.

Algebraicity of the presheaves is assumed only where it is used. Every case of Stacks 0ABX
asks the target to be an algebraic space, which is what makes a morphism into it from a
representable presheaf representable and so puts Stacks 0ABT at their disposal; the cases
`(β)` and "reasonable" ask it of the source as well, the first because it passes through the
equivalences of Stacks 03JU, which hold for an algebraic space, and the second because the
case `(δ)` of Stacks 03KF tests reasonableness on a family of étale charts. Stacks 0ABY and
the invariance statements assume nothing: the fibre product there is
the one of presheaves, and a point of it above a given point of the source is produced by
Stacks 03H4, which needs no algebraicity either.

## References

* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 03JT](https://stacks.math.columbia.edu/tag/03JT)
* [Stacks Project, Tag 03JU](https://stacks.math.columbia.edu/tag/03JU)
* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
* [Stacks Project, Tag 03KF](https://stacks.math.columbia.edu/tag/03KF)
* [Stacks Project, Tag 03KZ](https://stacks.math.columbia.edu/tag/03KZ)
* [Stacks Project, Tag 03L0](https://stacks.math.columbia.edu/tag/03L0)
* [Stacks Project, Tag 03L1](https://stacks.math.columbia.edu/tag/03L1)
* [Stacks Project, Tag 0ABT](https://stacks.math.columbia.edu/tag/0ABT)
* [Stacks Project, Tag 0ABX](https://stacks.math.columbia.edu/tag/0ABX)
* [Stacks Project, Tag 0ABY](https://stacks.math.columbia.edu/tag/0ABY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
private instance hasPullbacks_presheaf_decentRelativeConditions
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

private instance (priority := high) hasPullback_presheaf_decentRelativeConditions
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/- The private instances above are invisible to the public statements below (module system), where
`HasPullback` on presheaves times out at the default budget. -/
set_option synthInstance.maxHeartbeats 400000

/-! ### Invariance of the absolute conditions under an isomorphism -/

section Isomorphism

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Postcomposing a quasi-compact morphism with an isomorphism leaves it quasi-compact: the
composite is a base change of the morphism along the inverse isomorphism. -/
private theorem isQuasiCompact_comp_iso {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (e : Y ≅ Z) (hf : IsQuasiCompact B S hS f) : IsQuasiCompact B S hS (f ≫ e.hom) :=
  have sq : IsPullback (𝟙 X) (f ≫ e.hom) f e.inv := IsPullback.of_horiz_isIso ⟨by simp⟩
  isQuasiCompact_of_isPullback B S hS sq hf

/-- Condition (4) of Stacks 03JV travels along an isomorphism of presheaves: the image of a
quasi-compact monomorphic field-valued representative under an isomorphism is one. -/
private theorem hasQuasiCompactMonomorphicFieldRepresentative_pointsMap_of_iso (e : X ≅ Y)
    {x : points B S hS X}
    (h : HasQuasiCompactMonomorphicFieldRepresentative B S hS X x) :
    HasQuasiCompactMonomorphicFieldRepresentative B S hS Y
      (pointsMap B S hS X e.hom x) := by
  obtain ⟨p, hp, hmono, hqc⟩ := h
  refine ⟨FieldValuedPoint.map B S hS X e.hom p, ?_, ?_, ?_⟩
  · rw [← pointsMap_class, hp]
  · rw [fieldMorphism_map]
    exact mono_comp' hmono (IsIso.mono_of_iso e.hom)
  · rw [fieldMorphism_map]
    exact isQuasiCompact_comp_iso B S hS _ e hqc

/-- Decency of an algebraic space is invariant under isomorphism: every point of the target of
an isomorphism is the image of a point of its source, and a quasi-compact monomorphic
field-valued representative of the latter composes with the isomorphism to one of the
former. -/
theorem isDecentSpace_of_iso (e : X ≅ Y) (hX : IsDecentSpace B S hS X) :
    IsDecentSpace B S hS Y := by
  intro y
  obtain ⟨x, rfl⟩ := pointsMap_surjective_of_isIso B S hS e.hom y
  exact hasQuasiCompactMonomorphicFieldRepresentative_pointsMap_of_iso B S hS e (hX x)

/-- Finiteness of a relation fibre is unaffected by composing the chart with an isomorphism of
the ambient presheaf: the two self-intersections are identified by the induced isomorphism of
pullbacks, compatibly with both projections. -/
private theorem hasFiniteRelationFiber_comp_iso (e : X ≅ Y) (U : BigFppfOver B S hS)
    (φ : yoneda.obj U ⟶ X) (a b : points B S hS (yoneda.obj U))
    (h : HasFiniteRelationFiber B S hS X U φ a b) :
    HasFiniteRelationFiber B S hS Y U (φ ≫ e.hom) a b := by
  have : IsIso (pullback.mapDesc φ φ e.hom) := inferInstance
  have hmapfst : pullback.mapDesc φ φ e.hom ≫ pullback.fst (φ ≫ e.hom) (φ ≫ e.hom) =
      pullback.fst φ φ := by
    simp [pullback.mapDesc, pullback.map, pullback.lift_fst]
  have hmapsnd : pullback.mapDesc φ φ e.hom ≫ pullback.snd (φ ≫ e.hom) (φ ≫ e.hom) =
      pullback.snd φ φ := by
    simp [pullback.mapDesc, pullback.map, pullback.lift_snd]
  simp only [HasFiniteRelationFiber] at h ⊢
  refine Set.Finite.subset (h.image (pointsMap B S hS (pullback φ φ) (pullback.mapDesc φ φ e.hom)))
    fun z hz ↦ ?_
  obtain ⟨r, rfl⟩ := pointsMap_surjective_of_isIso B S hS (pullback.mapDesc φ φ e.hom) z
  simp only [Set.mem_ofPred_eq, ← pointsMap_comp_apply, hmapfst, hmapsnd] at hz
  exact ⟨r, hz, rfl⟩

/-- Condition (1) of Stacks 03JU travels along an isomorphism of presheaves: an étale chart
with a finite relation fibre above a point gives one above the image point, after composition
with the isomorphism. -/
private theorem hasFiniteRelationFiberAt_pointsMap_of_iso (e : X ≅ Y)
    {x : points B S hS X} (h : HasFiniteRelationFiberAt B S hS X x) :
    HasFiniteRelationFiberAt B S hS Y (pointsMap B S hS X e.hom x) := by
  obtain ⟨U, φ, a, b, hφ, ha, hb, hfin⟩ := h
  refine ⟨U, φ ≫ e.hom, a, b, isEtale_comp B S hS hφ (isEtale_of_isIso B S hS e.hom), ?_, ?_,
    hasFiniteRelationFiber_comp_iso B S hS e U φ a b hfin⟩
  · rw [pointsMap_comp_apply, ha]
  · rw [pointsMap_comp_apply, hb]

/-- Property `(β)` of Stacks 03JX is invariant under isomorphism: every point of the target of
an isomorphism is the image of a point of its source, and an étale chart with a finite relation
fibre above the latter gives one above the former. -/
theorem hasFiniteRelationFibersAtEveryPoint_of_iso (e : X ≅ Y)
    (hX : HasFiniteRelationFibersAtEveryPoint B S hS X) :
    HasFiniteRelationFibersAtEveryPoint B S hS Y := by
  intro y
  obtain ⟨x, rfl⟩ := pointsMap_surjective_of_isIso B S hS e.hom y
  exact hasFiniteRelationFiberAt_pointsMap_of_iso B S hS e (hX x)

/-- Postcomposing a chart with universally bounded fibres with an isomorphism of the ambient
presheaf leaves its fibres universally bounded, with the same bound: the field-valued points of
the two presheaves correspond, and so do the fibres above them. -/
private theorem hasUniversallyBoundedFibers_comp_iso (e : X ≅ Y) (U : BigFppfOver B S hS)
    (φ : yoneda.obj U ⟶ X) (hφ : HasUniversallyBoundedFibers B S hS U φ) :
    HasUniversallyBoundedFibers B S hS U (φ ≫ e.hom) := by
  obtain ⟨n, hn⟩ := hφ
  refine ⟨n, ?_⟩
  intro k hk T hT ξ
  obtain ⟨V, p, i, r, hr, hrank, hpb⟩ := hn k T hT (ξ ≫ e.inv)
  exact ⟨V, p, i, r, hr, hrank, hpb.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e
    (by simp) (by simp) (by simp) (by simp)⟩

/-- Reasonableness of an algebraic space is invariant under isomorphism: an affine étale chart
of the target of an isomorphism composes with the inverse isomorphism to one of its source,
with the same fibres. -/
theorem isReasonableSpace_of_iso (e : X ≅ Y) (hX : IsReasonableSpace B S hS X) :
    IsReasonableSpace B S hS Y := by
  intro U hU φ hφ
  have hsq : IsPullback (𝟙 (yoneda.obj U)) (φ ≫ e.inv) φ e.hom :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have hbound := hX U hU (φ ≫ e.inv) (presheaf_of_isPullback B S hS hsq hφ)
  have hcomp : (φ ≫ e.inv) ≫ e.hom = φ := by simp
  rw [← hcomp]
  exact hasUniversallyBoundedFibers_comp_iso B S hS e U (φ ≫ e.inv) hbound

end Isomorphism

/-! ### Base change -/

section BaseChange

variable {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 03L0, property `(β)`.** Property `(β)` of a morphism of algebraic spaces over `S`
is preserved by arbitrary base change: a base change of the base change of `f : X ⟶ Y` along
`g : Y' ⟶ Y` is a base change of `f`. -/
@[stacks 03L0 "property beta"]
theorem hasPropertyBeta_baseChange (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hf : HasPropertyBeta B S hS f) : HasPropertyBeta B S hS (pullback.fst g f) := fun T h =>
  hasFiniteRelationFibersAtEveryPoint_of_iso B S hS
    (pullbackRightPullbackFstIso g f h).symm (hf T (h ≫ g))

/-- **Stacks 03L0, decent.** Decency of a morphism of algebraic spaces over `S` is preserved
by arbitrary base change: a base change of the base change of `f : X ⟶ Y` along `g : Y' ⟶ Y`
is a base change of `f`. -/
@[stacks 03L0 "decent"]
theorem isDecent_baseChange (f : X ⟶ Y) (g : Y' ⟶ Y) (hf : IsDecent B S hS f) :
    IsDecent B S hS (pullback.fst g f) := fun T h =>
  isDecentSpace_of_iso B S hS (pullbackRightPullbackFstIso g f h).symm (hf T (h ≫ g))

/-- **Stacks 03L0, reasonable.** Reasonableness of a morphism of algebraic spaces over `S` is
preserved by arbitrary base change: a base change of the base change of `f : X ⟶ Y` along
`g : Y' ⟶ Y` is a base change of `f`. -/
@[stacks 03L0 "reasonable"]
theorem isReasonable_baseChange (f : X ⟶ Y) (g : Y' ⟶ Y) (hf : IsReasonable B S hS f) :
    IsReasonable B S hS (pullback.fst g f) := fun T h =>
  isReasonableSpace_of_iso B S hS (pullbackRightPullbackFstIso g f h).symm (hf T (h ≫ g))

end BaseChange

/-! ### From a morphism to its source, and back -/

section SourceAndTarget

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The projection to the source of a base change of a morphism of algebraic spaces over `S`
along a morphism from a representable presheaf is representable, because that morphism into an
algebraic space is. -/
private theorem relativelyRepresentable_pullback_snd_of_isAlgebraicSpace
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (T : BigFppfOver B S hS)
    (g : yoneda.obj T ⟶ Y) : yoneda.relativelyRepresentable (pullback.snd g f) := by
  have : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback g f)
    (Functor.relativelyRepresentable.of_diag hY.diagonal_representable g)

/-- A base change of a morphism of algebraic spaces along a morphism from a representable
presheaf is an algebraic space. -/
private theorem isAlgebraicSpace_pullback_yoneda {T : BigFppfOver B S hS}
    (g : yoneda.obj T ⟶ Y) (f : X ⟶ Y) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) : IsAlgebraicSpace B S hS (pullback g f) :=
  isAlgebraicSpace_pullback B S hS g f (isAlgebraicSpace_yoneda B S hS T) hX hY

/-- **Stacks 0ABX, the decent case in the form of condition (4) of Stacks 03JU.** Let
`f : X ⟶ Y` be a morphism of presheaves on the big fppf site over `S` with `Y` an algebraic
space. If every point of `X` is the class of a field-valued point presenting it by a
monomorphism, then so is every point of every base change of `f` along a morphism from a
representable presheaf into `Y`: that base change is representable over `X`. -/
@[stacks 0ABX "decent, as condition (4) of Stacks 03JU at every represented base change"]
theorem hasMonomorphicFieldRepresentative_pullback_of_source
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hmono : ∀ x : points B S hS X, HasMonomorphicFieldRepresentative B S hS X x)
    (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y)
    (w : points B S hS (pullback g f)) :
    HasMonomorphicFieldRepresentative B S hS (pullback g f) w :=
  hasMonomorphicFieldRepresentative_of_relativelyRepresentable B S hS (pullback.snd g f)
    (relativelyRepresentable_pullback_snd_of_isAlgebraicSpace B S hS hY f T g) hmono w

/-- **Stacks 0ABX, the case `(β)`.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over
`S`. If every point of `X` is the class of a field-valued point presenting it by a
monomorphism — condition (4) of Stacks 03JU — then `f` has property `(β)` of Stacks 03JX. -/
@[stacks 0ABX "property beta, from condition (4) of Stacks 03JU on the source"]
theorem hasPropertyBeta_of_hasMonomorphicFieldRepresentative
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hmono : ∀ x : points B S hS X, HasMonomorphicFieldRepresentative B S hS X x) :
    HasPropertyBeta B S hS f := fun T g =>
  hasFiniteRelationFibersAtEveryPoint_of_relativelyRepresentable B S hS
    (isAlgebraicSpace_pullback_yoneda B S hS g f hX hY)
    (pullback.snd g f)
    (relativelyRepresentable_pullback_snd_of_isAlgebraicSpace B S hS hY f T g) hmono

/-- **Stacks 03JU, conditions (1) and (4).** For a point of an algebraic space over `S`,
finiteness of one relation fibre in some étale chart is equivalent to having a monomorphic
field-valued representative. -/
theorem hasFiniteRelationFiberAt_iff_hasMonomorphicFieldRepresentative
    (hX : IsAlgebraicSpace B S hS X) (x : points B S hS X) :
    HasFiniteRelationFiberAt B S hS X x ↔ HasMonomorphicFieldRepresentative B S hS X x :=
  (hasFiniteRelationFiberAt_iff_everyEtaleChart B S hS X hX x).trans
    ((hasFiniteRelationFiberAtEveryEtaleChart_iff_hasEtaleQuasiCompactFieldRepresentative
        B S hS X hX x).trans
      (hasEtaleQuasiCompactFieldRepresentative_iff_hasMonomorphicFieldRepresentative
        B S hS hX x))

/-- **Stacks 0ABX, the case `(β)`.** A morphism of algebraic spaces over `S` whose source has
property `(β)` of Stacks 03JX has property `(β)`.

Property `(β)` of the source is condition (1) of Stacks 03JU at each of its points, which the
equivalences of that lemma turn into condition (4). -/
@[stacks 0ABX "property beta"]
theorem hasPropertyBeta_of_hasFiniteRelationFibersAtEveryPoint
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hXβ : HasFiniteRelationFibersAtEveryPoint B S hS X) :
    HasPropertyBeta B S hS f :=
  hasPropertyBeta_of_hasMonomorphicFieldRepresentative B S hS hX hY f fun x ↦
    (hasFiniteRelationFiberAt_iff_hasMonomorphicFieldRepresentative B S hS hX x).mp (hXβ x)

/-- **Stacks 0ABX, the reasonable case.** A morphism of algebraic spaces over `S` whose source
is a reasonable algebraic space is a reasonable morphism.

Each base change of `f` along a morphism from a representable presheaf into `Y` projects to
`X` by a representable morphism, because the diagonal of `Y` is representable, and
reasonableness passes to the source of a representable morphism by Stacks 0ABT. -/
@[stacks 0ABX "reasonable"]
theorem isReasonable_of_isReasonableSpace_source (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hXr : IsReasonableSpace B S hS X) :
    IsReasonable B S hS f := fun T g ↦
  isReasonableSpace_of_relativelyRepresentable B S hS
    (isAlgebraicSpace_pullback_yoneda B S hS g f hX hY) hX
    (pullback.snd g f)
    (relativelyRepresentable_pullback_snd_of_isAlgebraicSpace B S hS hY f T g) hXr

/-- **Stacks 0ABY, the case `(β)` in the form of condition (4) of Stacks 03JU.** Let
`f : X ⟶ Y` be a morphism of presheaves on the big fppf site over `S`. If every point of `Y`
is the class of a field-valued point presenting it by a monomorphism, and if the same holds at
every point of every base change of `f` along a morphism from a representable presheaf into
`Y`, then it holds at every point of `X`.

This is the source's argument: a monomorphic representative `Spec k ⟶ Y` of the image of `x`
is a morphism out of a representable presheaf, the point `x` lifts to the base change
`Spec k ×_Y X` by Stacks 03H4, and a monomorphic representative there composes with the
projection — a monomorphism, being a base change of one — to a monomorphic representative
of `x`. -/
@[stacks 0ABY "property beta, as condition (4) of Stacks 03JU at every point"]
theorem hasMonomorphicFieldRepresentative_of_target_of_baseChange (f : X ⟶ Y)
    (hY : ∀ y : points B S hS Y, HasMonomorphicFieldRepresentative B S hS Y y)
    (hf : ∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y)
      (w : points B S hS (pullback g f)),
      HasMonomorphicFieldRepresentative B S hS (pullback g f) w)
    (x : points B S hS X) :
    HasMonomorphicFieldRepresentative B S hS X x := by
  obtain ⟨p, hp, hpmono⟩ := hY (pointsMap B S hS X f x)
  -- A monomorphic representative `g : Spec k ⟶ Y` of the image of `x`.
  set g := fieldMorphism B S hS Y p with hgdef
  have hcomm : pointsMap B S hS (yoneda.obj (FieldValuedPoint.siteObject B S hS Y p)) g
      ((FieldValuedPoint.tautologicalPoint B S hS Y p).class B S hS
        (yoneda.obj (FieldValuedPoint.siteObject B S hS Y p))) =
      pointsMap B S hS X f x := by
    rw [hgdef, pointsMap_fieldMorphism_tautologicalPoint, hp]
  -- The point `x` lifts to a point of the base change of `f` along `g`.
  obtain ⟨w, -, hw⟩ :=
    exists_points_of_isPullback B S hS (IsPullback.of_hasPullback g f) _ x hcomm
  -- A monomorphic representative of that lift, and its projection to `X`.
  obtain ⟨q, hq, hqmono⟩ := hf (FieldValuedPoint.siteObject B S hS Y p) g w
  have : Mono g := hgdef ▸ hpmono
  have : Mono (pullback.snd g f) := (IsPullback.of_hasPullback g f).mono_snd_of_mono
  refine ⟨FieldValuedPoint.map B S hS (pullback g f) (pullback.snd g f) q, ?_, ?_⟩
  · rw [← pointsMap_class, hq]
    exact hw
  · rw [fieldMorphism_map]
    exact mono_comp' hqmono inferInstance

end SourceAndTarget

/-! ### Composition -/

section Composition

variable {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 0ABY, the case `(β)`.** If a morphism of algebraic spaces over `S` has property
`(β)` and its target has property `(β)`, then so does its source.

This is `AlgebraicGeometry.Space.hasMonomorphicFieldRepresentative_of_target_of_baseChange`
read through the equivalence of conditions (1) and (4) of Stacks 03JU on the source, on the
target and on each represented base change. -/
theorem hasFiniteRelationFibersAtEveryPoint_of_hasPropertyBeta
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hYbeta : HasFiniteRelationFibersAtEveryPoint B S hS Y)
    (hf : HasPropertyBeta B S hS f) :
    HasFiniteRelationFibersAtEveryPoint B S hS X := fun x ↦
  (hasFiniteRelationFiberAt_iff_hasMonomorphicFieldRepresentative B S hS hX x).mpr
    (hasMonomorphicFieldRepresentative_of_target_of_baseChange B S hS f
      (fun y ↦ (hasFiniteRelationFiberAt_iff_hasMonomorphicFieldRepresentative
        B S hS hY y).mp (hYbeta y))
      (fun T g w ↦ (hasFiniteRelationFiberAt_iff_hasMonomorphicFieldRepresentative B S hS
        (isAlgebraicSpace_pullback_yoneda B S hS g f hX hY)
        w).mp (hf T g w)) x)

/-- **Stacks 03L1, property `(β)`.** Property `(β)` of a morphism of algebraic spaces over `S`
is preserved by composition.

The base change of `f ≫ g` along `k : T ⟶ Z` is the base change of `f` along the projection
`T ×_Z Y ⟶ Y`, viewed over `T ×_Z Y`; that projection has property `(β)` by Stacks 03L0 and
`T ×_Z Y` has it because `g` does, so Stacks 0ABY applies. -/
@[stacks 03L1 "property beta"]
theorem hasPropertyBeta_comp (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : HasPropertyBeta B S hS f) (hg : HasPropertyBeta B S hS g) :
    HasPropertyBeta B S hS (f ≫ g) := by
  intro T k
  have hP := isAlgebraicSpace_pullback_yoneda B S hS k g hY hZ
  exact hasFiniteRelationFibersAtEveryPoint_of_iso B S hS (pullbackLeftPullbackSndIso k g f)
    (hasFiniteRelationFibersAtEveryPoint_of_hasPropertyBeta B S hS
      (isAlgebraicSpace_pullback B S hS (pullback.snd k g) f hP hX hY) hP
      (pullback.fst (pullback.snd k g) f) (hg T k)
      (hasPropertyBeta_baseChange B S hS f (pullback.snd k g) hf))

/-- **Stacks 03L1, decent.** Decency of a morphism of algebraic spaces over `S` is preserved by
composition.

The base change of `f ≫ g` along `k : T ⟶ Z` is the base change of `f` along the projection
`T ×_Z Y ⟶ Y`, viewed over `T ×_Z Y`; that projection is decent by Stacks 03L0 and `T ×_Z Y`
is decent because `g` is, so Stacks 0ABY applies. -/
@[stacks 03L1 "decent"]
theorem isDecent_comp (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsDecent B S hS f) (hg : IsDecent B S hS g) :
    IsDecent B S hS (f ≫ g) := by
  intro T k
  have hP := isAlgebraicSpace_pullback_yoneda B S hS k g hY hZ
  exact isDecentSpace_of_iso B S hS (pullbackLeftPullbackSndIso k g f)
    (isDecentSpace_of_isDecent B S hS
      (isAlgebraicSpace_pullback B S hS (pullback.snd k g) f hP hX hY) hP
      (pullback.fst (pullback.snd k g) f) (hg T k)
      (isDecent_baseChange B S hS f (pullback.snd k g) hf))

end Composition

end AlgebraicGeometry.Space

end
