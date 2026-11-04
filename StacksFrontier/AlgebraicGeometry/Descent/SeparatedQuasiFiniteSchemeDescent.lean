module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineBaseLocality
public import StacksFrontier.AlgebraicGeometry.Descent.DescendingTypesOfMorphismsGeneralBase
public import StacksFrontier.AlgebraicGeometry.Descent.DescentDataReindex
public import StacksFrontier.AlgebraicGeometry.Descent.IndQuasiAffineFpqcEffective
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.IndQuasiAffineSeparated
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Effective descent of separated locally quasi-finite morphisms of schemes

Let `S` be a scheme, let `{X i ⟶ S}` be an fppf covering family and let `(V i / X i, φ i j)` be a
descent datum relative to it, each of whose structure morphisms `V i ⟶ X i` is separated, locally
quasi-finite and locally of finite type. Then the datum is effective: it is isomorphic to the
canonical descent datum of a scheme over `S`. That is
[Stacks, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8) at its own generality, and it is
`AlgebraicGeometry.DescentData.isFamilyEffective_of_forall_isSeparated_of_locallyQuasiFinite`
below. The special case of a covering by a single quasi-compact chart is
`AlgebraicGeometry.DescentDatum.isEffective_of_isSeparated_of_locallyQuasiFinite`.

The statements carrying the tag elsewhere — the étale one in
`StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineEtaleDescent` and the flat one in
`StacksFrontier.AlgebraicGeometry.Descent.SurjectiveFlatDescent` — read the tag through
`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale` and its flat analogue, as a
statement about presheaves on a big site and about representability of a morphism of presheaves;
neither produces a scheme over `S` from a descent datum of schemes.

The route is the one of [Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK) rather than
the one of the source: a separated quasi-finite morphism of schemes is ind-quasi-affine by
[Stacks, Tag 0AP9](https://stacks.math.columbia.edu/tag/0AP9), so Gabber's effectivity for
ind-quasi-affine descent data applies. Over an affine base that effectivity is
`AlgebraicGeometry.DescentData.isFamilyEffective_of_forall_isIndQuasiAffineHom`, and the passage
to an arbitrary base is the general-base half of Stacks 02W3,
`AlgebraicGeometry.DescentData.isFamilyEffective_fpqc_of_affineSingleton_of_anyIndex`, whose three
hypotheses ind-quasi-affine morphisms satisfy: stability under base change (Stacks 0AP7), closure
under nonempty finite disjoint unions (`AlgebraicGeometry.isIndQuasiAffineHom_sigmaMap`) and the
affine-chart case (`AlgebraicGeometry.DescentDatum.isEffective_of_isIndQuasiAffineHom`).

## Main results

* `AlgebraicGeometry.DescentDatum.isEffective_of_affineBaseCase`: **effective descent along a
  single quasi-compact fpqc covering reduces to the case of an affine base**, for any property of
  the structure morphism which is stable under base change.
* `AlgebraicGeometry.DescentDatum.isEffective_of_isIndQuasiAffineHom_of_affineBase`:
  **[Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK) for a single chart over an
  affine base**, in the one-morphism shape.
* `AlgebraicGeometry.DescentDatum.isEffective_of_isIndQuasiAffineHom_of_quasiCompact`: Gabber's
  effectivity for an ind-quasi-affine descent datum along a single quasi-compact fpqc covering,
  over an arbitrary base.
* `AlgebraicGeometry.DescentDatum.isEffective_of_isSeparated_of_locallyQuasiFinite`: **Stacks
  02W8 in the scheme-descent-datum form**, for a single quasi-compact chart.
  (Gabber's theorem in full, [Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK) for an
  arbitrary fpqc covering family of an arbitrary base indexed in an arbitrary universe, is
  `AlgebraicGeometry.DescentData.isFamilyEffective_of_forall_isIndQuasiAffineHom_of_anyIndex` in
  the imported `StacksFrontier.AlgebraicGeometry.Descent.IndQuasiAffineFpqcEffective`, not here.)
* `AlgebraicGeometry.DescentData.isFamilyEffective_of_forall_isSeparated_of_locallyQuasiFinite`:
  **[Stacks, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8) at its own generality** — a
  descent datum relative to an arbitrary fppf covering family of an arbitrary base whose
  structure morphisms are separated and locally quasi-finite is effective.

## Implementation notes

*Why the single-chart statement asks the chart to be quasi-compact.* Its glueing step over an
arbitrary base is [Stacks, Tag 0AP4](https://stacks.math.columbia.edu/tag/0AP4),
`AlgebraicGeometry.DescentDatum.isEffective_of_forall_exists_restrictOpen`, which asks the chart
to be surjective, flat and quasi-compact: an invariant open of `V` descends to a unique open of
the base only along a morphism for which the fpqc topology sees the underlying space as a
quotient. A single fppf chart which is not quasi-compact is not covered by that route, but it is
covered by the covering-family statement, a one-member fppf covering family being an fppf
covering family; the family statement glues over the affine opens of the base instead, through
`AlgebraicGeometry.DescentData.nonempty_chart_of_restrictBase_isFamilyEffective`.

*The index type of the covering family is unrestricted.* The source indexes a covering by a set,
i.e. by a type in the universe of the schemes; the statements below allow an arbitrary universe,
which `AlgebraicGeometry.DescentData.isFamilyEffective_of_forall_reindex` reduces to the
`u`-small case inside Stacks 02W3.

## References

* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
* [Stacks Project, Tag 0AP9](https://stacks.math.columbia.edu/tag/0AP9)
* [Stacks Project, Tag 0AP7](https://stacks.math.columbia.edu/tag/0AP7)
* [Stacks Project, Tag 0AP4](https://stacks.math.columbia.edu/tag/0AP4)
* [Stacks Project, Tag 02W3](https://stacks.math.columbia.edu/tag/02W3)
* [Stacks Project, Tag 02NG](https://stacks.math.columbia.edu/tag/02NG)
* [Stacks Project, Tag 02LR](https://stacks.math.columbia.edu/tag/02LR)
* [Stacks Project, Tag 02VU](https://stacks.math.columbia.edu/tag/02VU)
* [Stacks Project, Tag 023W](https://stacks.math.columbia.edu/tag/023W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.DescentDatum

/-- **Effective descent along a single quasi-compact fpqc covering reduces to the case of an
affine base.** Let `P` be a property of morphisms of schemes stable under base change. If every
descent datum whose structure morphism has `P`, relative to a surjective, flat, quasi-compact
morphism onto an *affine* base, is effective, then so is every such datum over an arbitrary base.

This is `AlgebraicGeometry.DescentDatum.isEffective_of_isAffineHom_of_affineBaseCase` with
affineness of the structure morphism replaced by `P`: the only property of affine morphisms used
there is that the base change of the datum along an open immersion of the base keeps it. -/
theorem isEffective_of_affineBaseCase {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] {S X : Scheme.{u}} {f : X ⟶ S}
    [Surjective f] [Flat f] [QuasiCompact f]
    (H : ∀ (S' X' : Scheme.{u}) (f' : X' ⟶ S') [IsAffine S'] [Surjective f'] [Flat f']
      [QuasiCompact f'] (D' : DescentDatum f'), P D'.over.hom → DescentData.IsEffective D')
    (D : DescentDatum f) (hP : P D.over.hom) : DescentData.IsEffective D := by
  refine isEffective_of_forall_exists_restrictOpen D fun v ↦ ?_
  obtain ⟨U, hU, hvU, -⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
    (X := S) (x := (D.over.hom ≫ f).base v) (U := ⊤) trivial
  refine ⟨(D.over.hom ≫ f) ⁻¹ᵁ U, D.isTransitionInvariant_preimage_base U, hvU, ?_⟩
  have : IsAffine U.toScheme := hU
  have : Surjective (f ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f U).flip inferInstance
  have : Flat (f ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f U).flip inferInstance
  have : QuasiCompact (f ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f U).flip inferInstance
  obtain ⟨Q⟩ := nonempty_descended_of_isEffective
    (H U.toScheme (f ⁻¹ᵁ U).toScheme (f ∣_ U) (D.restrictBaseOpen U)
      (MorphismProperty.of_isPullback (D.isPullback_restrictBaseOpenProj U) hP))
  exact (Descended.ofRestrictBaseOpen D U Q).isEffective

/-- **[Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK) for a single chart over an
affine base.** Let `f : X ⟶ S` be a morphism onto an affine scheme which generates an fpqc
covering of `S` on its own. Then every descent datum relative to `X/S` whose structure morphism
is ind-quasi-affine is effective.

The hypothesis holds for `f` surjective and flat which is either quasi-compact or locally of
finite presentation, by `AlgebraicGeometry.Scheme.Hom.singleton_mem_fpqcPrecoverage` and by
`AlgebraicGeometry.Scheme.Hom.singleton_mem_fppfPrecoverage` with
`AlgebraicGeometry.Scheme.fppfPrecoverage_le_fpqcPrecoverage`. -/
@[sga "1 VIII 7.8" "partial",
  sga "1 VIII 7.9" "special case",
  sga "3 IX 2.3" "partial",
  sga "3 VIII 1.7.2" "(ii), special case",
  sga "3 X 5.4" "special case",
  sga "3 XXIV 3.11.2" "partial"]
theorem isEffective_of_isIndQuasiAffineHom_of_affineBase {S X : Scheme.{u}} [IsAffine S]
    {f : X ⟶ S} (hcov : Presieve.singleton f ∈ Scheme.fpqcPrecoverage S) (D : DescentDatum f)
    (hiqa : IsIndQuasiAffineHom D.over.hom) : DescentData.IsEffective D := by
  have hfam : Presieve.ofArrows (fun _ : ULift.{u} Unit ↦ X) (fun _ ↦ f) ∈
      Scheme.fpqcPrecoverage S := by
    rw [DescentData.ofArrows_const_eq_singleton]
    exact hcov
  exact DescentData.isEffective_of_isFamilyEffective
    (DescentData.isFamilyEffective_of_reindex (D := D) (Equiv.ulift (α := Unit))
      (DescentData.isFamilyEffective_of_forall_isIndQuasiAffineHom
        (fun _ : ULift.{u} Unit ↦ f) hfam (D.reindex (Equiv.ulift (α := Unit))) fun _ ↦ hiqa))

/-- **Gabber's effectivity for ind-quasi-affine descent data along a single quasi-compact fpqc
covering.** A descent datum relative to a surjective, flat, quasi-compact morphism `f : X ⟶ S`
whose structure morphism `V ⟶ X` is ind-quasi-affine is effective.

This is [Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK) for a one-member covering,
over an arbitrary base. -/
@[stacks 0APK "the case of a one-member covering by a surjective flat quasi-compact \
morphism, over an arbitrary base",
  sga "1 VIII 7.8" "partial",
  sga "1 VIII 7.9" "partial",
  sga "3 X 5.4" "special case",
  sga "3 XI 4.2" "more general"]
theorem isEffective_of_isIndQuasiAffineHom_of_quasiCompact {S X : Scheme.{u}} {f : X ⟶ S}
    [Surjective f] [Flat f] [QuasiCompact f] (D : DescentDatum f)
    (hiqa : IsIndQuasiAffineHom D.over.hom) : DescentData.IsEffective D :=
  isEffective_of_affineBaseCase (P := @IsIndQuasiAffineHom)
    (fun _ _ f' _ _ _ _ D' h' ↦
      isEffective_of_isIndQuasiAffineHom_of_affineBase f'.singleton_mem_fpqcPrecoverage D' h')
    D hiqa

/-- **[Stacks, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8) in the scheme-descent-datum
form, for a single quasi-compact chart.** Let `f : X ⟶ S` be a surjective, flat, quasi-compact
morphism of schemes and let `(V, φ)` be a descent datum relative to `X/S` whose structure
morphism `V ⟶ X` is separated, locally quasi-finite and locally of finite type. Then `(V, φ)` is
effective: it is isomorphic to the canonical descent datum of a scheme over `S`.

Such a structure morphism is ind-quasi-affine by Stacks 0AP9, so this is Gabber's effectivity
`AlgebraicGeometry.DescentDatum.isEffective_of_isIndQuasiAffineHom_of_quasiCompact`. -/
@[stacks 02W8 "the scheme-descent-datum form, for a single quasi-compact chart",
  sga "3 X 5.4" "special case"]
theorem isEffective_of_isSeparated_of_locallyQuasiFinite {S X : Scheme.{u}} {f : X ⟶ S}
    [Surjective f] [Flat f] [QuasiCompact f] (D : DescentDatum f)
    (hsep : IsSeparated D.over.hom) (hqf : LocallyQuasiFinite D.over.hom)
    (hft : LocallyOfFiniteType D.over.hom) : DescentData.IsEffective D :=
  have := hsep
  have := hqf
  have := hft
  isEffective_of_isIndQuasiAffineHom_of_quasiCompact D
    (isIndQuasiAffineHom_of_isSeparated_of_locallyQuasiFinite D.over.hom)

end AlgebraicGeometry.DescentDatum

namespace AlgebraicGeometry.DescentData

/-! Gabber's theorem in full, [Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK), is
`AlgebraicGeometry.DescentData.isFamilyEffective_of_forall_isIndQuasiAffineHom_of_anyIndex` in
`StacksFrontier.AlgebraicGeometry.Descent.IndQuasiAffineFpqcEffective`, which this module imports.
It was proved here too, independently and with the same statement and the same proof; the two
copies are merged onto that one, which is the earlier of the two and is where the ind-quasi-affine
fpqc material lives. Tag 0APK stays registered there. -/

/-- **[Stacks, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8).** Let `S` be a scheme, let
`{X i ⟶ S}` be an fppf covering family and let `D = (V i / X i, φ i j)` be a descent datum
relative to that family. If each morphism `V i ⟶ X i` is separated and locally quasi-finite, then
the descent datum is effective: it is isomorphic to the canonical descent datum of a scheme over
`S`.

Quasi-finiteness is Stacks 02NG — `AlgebraicGeometry.LocallyQuasiFinite` together with
`AlgebraicGeometry.LocallyOfFiniteType`, as in the formalization of Stacks 01TD, of Stacks 02LR
and of Stacks 0AP9, Mathlib's `LocallyQuasiFinite` not itself asking for local finite type.

Such a structure morphism is ind-quasi-affine by Stacks 0AP9,
`AlgebraicGeometry.isIndQuasiAffineHom_of_isSeparated_of_locallyQuasiFinite`, and an fppf
covering family is an fpqc covering family, so this is Gabber's effectivity
`AlgebraicGeometry.DescentData.isFamilyEffective_of_forall_isIndQuasiAffineHom_of_anyIndex`. -/
@[stacks 02W8, sga "3 X 5.4" "more general"]
theorem isFamilyEffective_of_forall_isSeparated_of_locallyQuasiFinite {ι : Type v}
    {S : Scheme.{u}} {X : ι → Scheme.{u}} (f : ∀ i, X i ⟶ S)
    (hf : Presieve.ofArrows X f ∈ Scheme.fppfPrecoverage S) (D : DescentData f)
    (hsep : ∀ i, IsSeparated (D.obj i).hom)
    (hqf : ∀ i, LocallyQuasiFinite (D.obj i).hom)
    (hft : ∀ i, LocallyOfFiniteType (D.obj i).hom) :
    D.IsFamilyEffective :=
  isFamilyEffective_of_forall_isIndQuasiAffineHom_of_anyIndex f
    (Scheme.fppfPrecoverage_le_fpqcPrecoverage S hf) D fun i ↦
      have := hsep i
      have := hqf i
      have := hft i
      isIndQuasiAffineHom_of_isSeparated_of_locallyQuasiFinite (D.obj i).hom

end AlgebraicGeometry.DescentData

end
