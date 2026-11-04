module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FromLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.LocalCompleteIntersectionEtale
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.RegularGerm
public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.Regular
public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.ReducedSmoothLocal
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Composition
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Syntomic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.UnramifiedConormal
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.EtaleNormalization
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.FibrePowerBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Etale
public import StacksFrontier.AlgebraicGeometry.Thickenings.ConormalRankBaseChange

/-!
# Condition (2) of Tag 0CBR is étale-local on the ambient scheme

Let `D` be a closed subscheme of a locally Noetherian scheme `X` which is reduced and whose
normalization is unramified. If every point of `D` admits an étale chart `f : U ⟶ X` of the
ambient scheme over which the pullback divisor satisfies condition (2) of Tag 0CBR, then `D`
itself satisfies condition (2).

The mechanism is a single cartesian square. Normalization commutes with étale localization of a
divisor, and fibre powers commute with base change, so the `n`-fold fibre power of the
normalization of the pullback divisor is the base change along `f` of the `n`-fold fibre power of
the normalization of `D`; the complement of the fat diagonal on the source is the preimage of the
complement of the fat diagonal on the target, so the square survives the restriction to those
opens and exhibits `Z_n(D|_U) ⟶ U` as a base change of `Z_n(D) ⟶ X`.

Each of the three clauses of condition (2) then descends along the resulting étale cover of
`Z_n(D)`: regularity because regularity of a local ring is unchanged along an étale morphism,
the Koszul property because it is local on the source for the étale topology, and the rank of the
conormal sheaf because it may be read after a flat base change.

The same square, read in the other direction, gives the ascent: condition (2) is inherited by the
pullback of the divisor along a single étale chart. There no cover is needed, since the three
clauses are then statements about the source of a base change of a morphism already known to
satisfy them.

## Main results

* `Stacks.Divisors.isPullback_normalizationDistinctToAmbient_comap`: for an étale chart
  `f : U ⟶ X` the morphism `Z_n(D|_U) ⟶ U` is a base change of `Z_n(D) ⟶ X`.
* `Stacks.Divisors.isNormalizationCrossingsDivisor_of_forall_etaleChart`: condition (2) of
  Tag 0CBR may be verified on étale charts covering the divisor.
* `Stacks.Divisors.isNormalizationCrossingsDivisor_comap`: condition (2) of Tag 0CBR is inherited
  by the pullback of the divisor along an étale chart.

## Implementation notes

The comparison morphism of the fibre powers is the one built by recursion in
`StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.FibrePowerBaseChange`; the
open of the fibre power over `U` cut out by the complement of the fat diagonal is *equal* to the
preimage of the corresponding open over `X`, not merely isomorphic to it, so the restricted
comparison morphism is an honest `AlgebraicGeometry.Scheme.Hom.resLE` and no transport of schemes
along an equality of opens is needed. The substitution is isolated in
a private lemma, which is `AlgebraicGeometry.isPullback_resLE_preimage` with the open on the
source given by an equation rather than as a preimage on the nose.

The cartesian square is exported in existential form: the comparison morphism itself is never
needed, only the fact that some morphism makes the square cartesian.

Condition (2) binds the unramifiedness of the normalization by an existential, and its conormal
clause is stated under a `letI` for that bound witness. Unramifiedness and formal unramifiedness
are propositions, so the conormal sheaves produced from the bound witness, from the hypothesis of
the theorem, and from base change along the square are all definitionally equal by proof
irrelevance, and the clauses transfer by `exact`.

## References

* [Stacks Project, Tag 0CBR](https://stacks.math.columbia.edu/tag/0CBR)
* [Stacks Project, Tag 0AH7](https://stacks.math.columbia.edu/tag/0AH7)
* [Stacks Project, Tag 069P](https://stacks.math.columbia.edu/tag/069P)
* [Stacks Project, Tag 04F9](https://stacks.math.columbia.edu/tag/04F9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Divisors

/-- A cartesian square restricts to a cartesian square over an open of the base of its right
column and any open of the source that is *equal* to the preimage of that open; this is
`AlgebraicGeometry.isPullback_resLE_preimage` with the source open given by an equation. -/
private theorem isPullback_resLE_of_eq {W W' T T' : Scheme.{u}} {p : W' ⟶ T'} {q : W' ⟶ W}
    {b : T' ⟶ T} {r : W ⟶ T} (h : IsPullback p q b r) (V : W.Opens) (V' : W'.Opens)
    (hV : V' = q ⁻¹ᵁ V) :
    IsPullback (V'.ι ≫ p) (q.resLE V V' hV.le) b (V.ι ≫ r) := by
  subst hV
  exact isPullback_resLE_preimage h V

/-- **The scheme `Z_n` of the pullback divisor along an étale chart is the base change of `Z_n`.**
The normalization of the pullback of `D` along `f` is the fibre product of the normalization of
`D` with the pullback subscheme, fibre powers commute with base change, and the complement of the
fat diagonal upstairs is the preimage of the complement of the fat diagonal downstairs; pasting
and restricting gives the square. -/
theorem isPullback_normalizationDistinctToAmbient_comap
    {X U : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian U] (f : U ⟶ X) [Etale f]
    (D : X.IdealSheafData) (n : ℕ) :
    ∃ Ψ : normalizationDistinct (D.comap f) n ⟶ normalizationDistinct D n,
      IsPullback (normalizationDistinctToAmbient (D.comap f) n) Ψ f
        (normalizationDistinctToAmbient D n) := by
  have h1 : IsPullback (divisorNormalization (D.comap f)) (comapNormalizationMap f D)
      (comapSubschemeMap f D) (divisorNormalization D) :=
    (isPullback_comapNormalizationMap f D).flip
  have hopen : normalizationDistinctOpens (D.comap f) n
      = fibrePowerBaseChangeMap h1 n ⁻¹ᵁ normalizationDistinctOpens D n :=
    TopologicalSpace.Opens.ext (fibrePowerDistinctLocus_eq_preimage h1 n)
  exact ⟨_, isPullback_resLE_of_eq
    ((isPullback_fibrePowerBaseChangeMap h1 n).paste_horiz (isPullback_comapSubschemeMap f D))
    (normalizationDistinctOpens D n) (normalizationDistinctOpens (D.comap f) n) hopen⟩

/-- The left column of a cartesian square is étale when the bottom row is. -/
private theorem etale_of_isPullback_of_etale {A B C D : Scheme.{u}} {p : A ⟶ B} {q : A ⟶ C}
    {b : B ⟶ D} {c : C ⟶ D} (h : IsPullback p q b c) [Etale b] : Etale q :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Etale.{u}) h inferInstance

/-- Once the normalization of the divisor is unramified, `Z_n` is locally Noetherian: it is
unramified, hence locally of finite type, over the locally Noetherian ambient scheme. -/
private theorem isLocallyNoetherian_normalizationDistinct {X : Scheme.{u}}
    [IsLocallyNoetherian X] (D : X.IdealSheafData) [Unramified (divisorNormalization D)] (n : ℕ) :
    IsLocallyNoetherian (normalizationDistinct D n) := by
  have := unramified_normalizationDistinctToAmbient D n
  have : LocallyOfFiniteType (normalizationDistinctToAmbient D n) :=
    ((unramified_iff_locallyOfFiniteType_and_formallyUnramified
      (normalizationDistinctToAmbient D n)).mp inferInstance).1
  exact LocallyOfFiniteType.isLocallyNoetherian (normalizationDistinctToAmbient D n)

/-- The two-member family consisting of a morphism and the identity of its target, as a family of
schemes over that target. -/
private def etaleChartWithIdFamily {V W : Scheme.{u}} (_a : V ⟶ W) : Bool → Scheme.{u}
  | true => V
  | false => W

/-- The two-member family consisting of a morphism and the identity of its target. -/
private def etaleChartWithIdMap {V W : Scheme.{u}} (a : V ⟶ W) :
    ∀ b, etaleChartWithIdFamily a b ⟶ W
  | true => a
  | false => 𝟙 W

/-- Adjoining the identity of the target to an étale morphism gives an étale covering of the
target of which that morphism is a member; the identity supplies the surjectivity. -/
private theorem etaleChartWithIdMap_mem {V W : Scheme.{u}} (a : V ⟶ W) [Etale a] :
    Presieve.ofArrows (etaleChartWithIdFamily a) (etaleChartWithIdMap a)
      ∈ Scheme.etalePrecoverage W :=
  ofArrows_mem_etalePrecoverage_iff.mpr
    ⟨fun x => ⟨false, show x ∈ Set.range (𝟙 W : W ⟶ W).base by simp⟩, by
      rintro (_ | _)
      · exact (inferInstance : Etale (𝟙 W))
      · exact (inferInstance : Etale a)⟩

/-- The point of the divisor subscheme below a point of `Z_n`: push the point into the fibre
power of the normalization and then down to the subscheme. -/
private def pointBelowOfNormalizationDistinct {X : Scheme.{u}} [IsLocallyNoetherian X]
    (D : X.IdealSheafData) (n : ℕ) (z : normalizationDistinct D n) : D.subscheme :=
  (fibrePowerProj (divisorNormalization D) n).base
    ((normalizationDistinctOpens D n).ι.base z)

/-- The morphism `Z_n ⟶ X` sends a point to the image in `X` of the point of the divisor
subscheme below it. -/
private theorem normalizationDistinctToAmbient_apply {X : Scheme.{u}} [IsLocallyNoetherian X]
    (D : X.IdealSheafData) (n : ℕ) (z : normalizationDistinct D n) :
    normalizationDistinctToAmbient D n z
      = D.subschemeι (pointBelowOfNormalizationDistinct D n z) := rfl

/-- **Condition (2) of Tag 0CBR may be verified on étale charts covering the divisor.** If `D` is
reduced, its normalization is unramified, and every point of the subscheme cut out by `D` has an
étale chart of the ambient scheme over which the pullback of `D` satisfies condition (2), then `D`
satisfies condition (2).

For each `n` the étale charts produce, by
`Stacks.Divisors.isPullback_normalizationDistinctToAmbient_comap`, a family of cartesian squares
whose source legs are étale and jointly surjective onto `Z_n`. Regularity of `Z_n` follows from
Tag 0AH7, since regularity of a local ring is unchanged along an étale morphism and `Z_n` is
locally Noetherian because it is unramified over `X`; the Koszul property follows from the étale
case of Tag 069P, the composite of each source leg with `Z_n ⟶ X` being the composite of a Koszul
morphism with an étale one; and the rank of the conormal sheaf follows from Tag 04F9, the base
morphisms of the squares being flat. -/
theorem isNormalizationCrossingsDivisor_of_forall_etaleChart
    {X : Scheme.{u}} [IsLocallyNoetherian X] (D : X.IdealSheafData)
    (hred : IsReduced D.subscheme)
    (hν : Unramified (divisorNormalization D))
    (H : ∀ y : D.subscheme, ∃ (U : Scheme.{u}) (f : U ⟶ X) (hU : IsLocallyNoetherian U)
            (_ : Etale f), (∃ q : U, f q = D.subschemeι y) ∧
              @IsNormalizationCrossingsDivisor U hU (D.comap f)) :
    IsNormalizationCrossingsDivisor D := by
  have := hν
  choose U f hU hf hq hNC using H
  choose q hq using hq
  refine ⟨hred, hν, fun n hn => ?_⟩
  -- the cartesian squares supplied by the charts
  have hsq : ∀ y : D.subscheme,
      ∃ Ψ : @normalizationDistinct (U y) (hU y) (D.comap (f y)) n ⟶ normalizationDistinct D n,
        IsPullback (@normalizationDistinctToAmbient (U y) (hU y) (D.comap (f y)) n) Ψ (f y)
          (normalizationDistinctToAmbient D n) := fun y =>
    @isPullback_normalizationDistinctToAmbient_comap X (U y) _ (hU y) (f y) (hf y) D n
  choose Ψ hΨ using hsq
  have hEt : ∀ y, Etale (Ψ y) := fun y => have := hf y; etale_of_isPullback_of_etale (hΨ y)
  have hFlat : ∀ y, Flat (f y) := fun y => by have := hf y; infer_instance
  -- every point of `Z_n` is in the image of the chart at the point of `D` below it
  have hrange : ∀ z : normalizationDistinct D n,
      z ∈ Set.range (Ψ (pointBelowOfNormalizationDistinct D n z)).base := by
    intro z
    rw [range_base_of_isPullback (hΨ (pointBelowOfNormalizationDistinct D n z)).flip]
    exact ⟨q (pointBelowOfNormalizationDistinct D n z),
      (hq (pointBelowOfNormalizationDistinct D n z)).trans
        (normalizationDistinctToAmbient_apply D n z).symm⟩
  -- `Z_n` is locally Noetherian, being unramified over `X`
  have hLN : IsLocallyNoetherian (normalizationDistinct D n) :=
    isLocallyNoetherian_normalizationDistinct D n
  -- (a) regularity of `Z_n`
  have hregular : AlgebraicGeometry.IsRegular (normalizationDistinct D n) := by
    refine (isRegular_iff_regular_stalks _).mpr ⟨hLN, fun z => ?_⟩
    set y := pointBelowOfNormalizationDistinct D n z with hy
    obtain ⟨z', hz'⟩ := hrange z
    have := hU y
    have := hEt y
    obtain ⟨_, _, hcl⟩ := hNC y
    have hz'reg := ((isRegular_iff_regular_stalks _).mp (hcl n hn).1).2 z'
    have hmain := (isRegularLocalRing_stalk_iff_of_etale (Ψ y) z').mp hz'reg
    rwa [hz'] at hmain
  -- (b) the Koszul property
  have hlci : IsLocalCompleteIntersectionMorphism (normalizationDistinctToAmbient D n) := by
    let := isLocalCompleteIntersectionMorphism_isLocalAtSource_etale
    have hcov : Presieve.ofArrows _ Ψ ∈ Scheme.etalePrecoverage (normalizationDistinct D n) :=
      ofArrows_mem_etalePrecoverage_iff.mpr
        ⟨fun z => ⟨pointBelowOfNormalizationDistinct D n z, hrange z⟩, hEt⟩
    refine MorphismProperty.IsLocalAtSource.of_forall_comp hcov ?_
    rintro W g ⟨y⟩
    rw [← (hΨ y).w]
    have := hU y
    have := hf y
    obtain ⟨_, _, hcl⟩ := hNC y
    exact isLocalCompleteIntersectionMorphism_comp _ _ (hcl n hn).2.1
      (isLocalCompleteIntersectionMorphism_of_syntomic (syntomic_of_etale (f y)))
  -- (c) the rank of the conormal sheaf
  have := formallyUnramified_normalizationDistinctToAmbient D n
  refine ⟨hregular, hlci, ?_⟩
  refine isFiniteLocallyFreeOfRank_universalConormalSheaf_of_forall_isPullback
    (normalizationDistinctToAmbient D n) n
    (isFiniteLocallyFree_universalConormalSheaf_of_isLocalCompleteIntersection _ hlci)
    fun z => ?_
  set y := pointBelowOfNormalizationDistinct D n z with hy
  obtain ⟨z', hz'⟩ := hrange z
  have := hU y
  obtain ⟨_, _, hcl⟩ := hNC y
  exact ⟨_, U y, _, Ψ y, f y, hΨ y, z', hFlat y, hz', (hcl n hn).2.2⟩

/-- **Condition (2) of Tag 0CBR is inherited by the pullback along an étale chart.** This is the
ascent companion of `Stacks.Divisors.isNormalizationCrossingsDivisor_of_forall_etaleChart`, read
off the same cartesian square in the other direction.

Reducedness ascends because the induced morphism of divisor subschemes is étale and reducedness
is local for the étale precoverage; unramifiedness of the normalization ascends because the
normalization of the pullback divisor is a base change of the normalization of `D`. For the
remaining clauses the comparison morphism `Ψ` of
`Stacks.Divisors.isPullback_normalizationDistinctToAmbient_comap` is étale, being a base change
of the chart, so regularity of the stalks of `Z_n(D|_U)` follows from Tag 0AH7 with no
surjectivity needed; the Koszul property is a flat base change by Tag 069I; and the conormal
sheaf of `Z_n(D|_U) ⟶ U` is the pullback along `Ψ` of the conormal sheaf of `Z_n(D) ⟶ X` by
Tag 04F9, so it keeps its rank. -/
theorem isNormalizationCrossingsDivisor_comap
    {X U : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian U] (f : U ⟶ X) [Etale f]
    (D : X.IdealSheafData) (h : IsNormalizationCrossingsDivisor D) :
    IsNormalizationCrossingsDivisor (D.comap f) := by
  obtain ⟨hred, hν, hcl⟩ := h
  have := hν
  have hνc : Unramified (divisorNormalization (D.comap f)) :=
    unramified_isStableUnderBaseChange.of_isPullback (isPullback_comapNormalizationMap f D) hν
  refine ⟨ObjectProperty.IsLocal.component (P := fun Y : Scheme.{u} => IsReduced Y)
      (etaleChartWithIdMap_mem (comapSubschemeMap f D)) (comapSubschemeMap f D) ⟨true⟩ hred,
    hνc, fun n hn => ?_⟩
  obtain ⟨Ψ, hsq⟩ := isPullback_normalizationDistinctToAmbient_comap f D n
  have := etale_of_isPullback_of_etale hsq
  obtain ⟨hreg, hlci, hconormal⟩ := hcl n hn
  refine ⟨?_, ?_, ?_⟩
  · refine (isRegular_iff_regular_stalks _).mpr
      ⟨isLocallyNoetherian_normalizationDistinct (D.comap f) n, fun z => ?_⟩
    exact (isRegularLocalRing_stalk_iff_of_etale Ψ z).mpr
      (((isRegular_iff_regular_stalks _).mp hreg).2 (Ψ z))
  · rw [← hsq.flip.isoPullback_hom_snd]
    exact isLocalCompleteIntersectionMorphism_comp _ _
      (isLocalCompleteIntersectionMorphism_of_isOpenImmersion hsq.flip.isoPullback.hom)
      (isLocalCompleteIntersectionMorphism_pullback_snd
        (normalizationDistinctToAmbient D n) f hlci)
  · have := formallyUnramified_normalizationDistinctToAmbient D n
    have := formallyUnramified_normalizationDistinctToAmbient (D.comap f) n
    exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      (universalConormalSheafFlatBaseChangeIso hsq)
      (Scheme.Modules.isFiniteLocallyFreeOfRank_pullback_obj Ψ _ n hconormal)

end Stacks.Divisors

end
