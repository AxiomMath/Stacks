module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksFrontier.AlgebraicGeometry.Descent.ProperFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.F6Rank89.CoheightOfSurface
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.LocalizationBaseChange
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.Properties.Serre
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ModifyingLocalRings.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ModifyingLocalRings.NormalizedPointBlowupSequence
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.LipmanEquivalence

/-!
# Globalizing resolutions of the local rings at the singular points

Let `N` be a normal Noetherian scheme of dimension at most two whose singular locus is finite.
Its singular points are then closed points, and the spectra of the local rings there, together
with the open complement of those points, cover `N` in the flat topology. This file assembles
sequences of normalized blowups over those spectra into a single sequence over `N`: one blows up
over `N` at the closed point lying under the centre of a local blowup, which changes the
localization at the chosen singular point as prescribed and leaves the localizations at the other
singular points and the restriction to the complement untouched. Running through the singular
points one at a time produces a sequence over `N` whose localizations are the given local ones.

Applied to the normalization `N = Y^ν` of a two-dimensional integral Noetherian scheme `Y`, this
turns resolutions by normalized blowups of the spectra of the local rings of `Y^ν` at its
singular points into a resolution of singularities of `Y` by normalized blowups: regularity of
the total space is itself checked on the same flat cover, the complement of the singular points
being regular by definition and the local pieces being regular by hypothesis.

## Main definitions

* `AlgebraicGeometry.IsNormalizedBlowUpOutside` is the one-step relation on schemes over a fixed
  base: the source of the second is the normalized blowing up of the source of the first at a
  closed point whose image in the base lies outside a given open. Its reflexive-transitive
  closure from the identity expresses a finite sequence of such blowups.
* `AlgebraicGeometry.IsProperNormalizedBlowUpOutside` adds properness over the base.

## Main results

* `AlgebraicGeometry.FinitePresentationAwayPointsSituation`
  `.exists_properNormalizedBlowUpSequence_of_local`: finitely many local sequences of normalized
  blowups, one over the spectrum of the local ring at each distinguished closed point, come from a
  single sequence over the base.
* `AlgebraicGeometry.exists_normalizedBlowUpChain_of_reflTransGen` turns such a sequence over the
  normalization of `Y` into a chain of normalized blowups of `Y` in the sense of
  [Stacks, Tag 0BGL].
* `AlgebraicGeometry.hasResolutionByNormalizedBlowUps_of_local`: a two-dimensional integral
  Noetherian scheme with finite normalization, whose normalization has finitely many singular
  points and whose local rings there have spectra admitting resolutions by normalized blowups,
  has a resolution of singularities by normalized blowups.
* `AlgebraicGeometry.ringKrullDim_stalk_eq_two_of_mem_singularLocus` and
  `AlgebraicGeometry.isClosed_singleton_of_mem_singularLocus`: on a normal locally Noetherian
  scheme of dimension at most two the local ring at a singular point has Krull dimension exactly
  two, and such a point is closed.

## Implementation notes

The sequence over the base is recorded as the reflexive-transitive closure of a one-step
relation between objects of `CategoryTheory.Over`, rather than as the inductive family
`AlgebraicGeometry.NormalizedBlowUpChain`, because the induction that lifts a local sequence must
transport each stage along an isomorphism over the base: a base change is only isomorphic to a
normalized blowing up, never equal to one. The one-step relation carries that isomorphism, and
`AlgebraicGeometry.exists_normalizedBlowUpChain_of_reflTransGen` converts the result into a chain
in the sense of [Stacks, Tag 0BGL] once the sequence is complete.

Lifting one local step uses that the centre of the local blowup lies over the distinguished point
and that the point of the base under it is closed; the normalized blowing up there pulls back to
the local normalized blowing up because the reduced closed subscheme of a point pulls back to the
reduced closed subscheme of the unique point above it along the projection to the local scheme,
and because blowing up and normalizing both commute with that flat preimmersive base change. For
a *different* distinguished point the global blowup disappears after localization: a normalized
blowing up of a normal scheme is an isomorphism over the complement of its centre, and the
spectrum of the local ring at a point maps into that complement, no point of it specializing to
another distinguished point.

Properness of each stage over the base, which the chain of [Stacks, Tag 0BGL] demands at every
step, is checked on the flat cover by the complement and the local spectra, properness being
local at the target for the fpqc topology.

The dimension hypothesis enters twice: it makes the singular points closed, the local ring at a
singular point of a normal scheme having dimension exactly two because a normal scheme is regular
in codimension one; and it is inherited by the normalization along an integral morphism.

Nothing here carries an attribute for [Stacks, Tag 0BGP]. What is proved is the step from local
resolutions by normalized blowups to a global one; the source obtains those local resolutions
from the normality of the completed local rings in condition (4) by way of
[Stacks, Tags 0BGN and 0BGM], and no statement in the library concludes either of those.

## References

* [Lipman, *Rational singularities*, Theorem on page 151]
* [Stacks Project, Tag 0BGP](https://stacks.math.columbia.edu/tag/0BGP)
* [Stacks Project, Tag 0BFU](https://stacks.math.columbia.edu/tag/0BFU)
* [Stacks Project, Tag 0BFZ](https://stacks.math.columbia.edu/tag/0BFZ)
* [Stacks Project, Tag 0BGL](https://stacks.math.columbia.edu/tag/0BGL)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### One normalized blowup at a closed point outside an open -/

/-- `B` is obtained from `A`, both schemes over `X`, by blowing up a closed point of `A` whose
image in `X` lies outside the open `U` and normalizing: the source of `B` is isomorphic over `X`
to that normalized blowing up. -/
def IsNormalizedBlowUpOutside {X : Scheme.{u}} (U : X.Opens) (A B : Over X) : Prop :=
  ∃ (hA : ∀ V : A.left.Opens, IsCompact (V : Set A.left) → (irreducibleComponents V).Finite)
    (x : A.left) (hx : IsClosed ({x} : Set A.left)), A.hom x ∉ (U : Set X) ∧
      ∃ e : B.left ≅ Stacks.Blowup.normalizedBlowUpScheme A.left hA x hx,
        e.hom ≫ Stacks.Blowup.normalizedBlowUp A.left hA x hx ≫ A.hom = B.hom

/-- One normalized blowup at a closed point outside `U` whose total space is moreover proper over
the base. This is the step of a sequence of normalized blowups in the sense of
[Stacks, Tag 0BGL], which requires properness over the base at every stage. -/
def IsProperNormalizedBlowUpOutside {X : Scheme.{u}} (U : X.Opens) (A B : Over X) : Prop :=
  IsNormalizedBlowUpOutside U A B ∧ IsProper B.hom

/-- Forgetting properness turns a sequence of proper steps into a sequence of steps. -/
theorem reflTransGen_isNormalizedBlowUpOutside_of_isProper {X : Scheme.{u}} {U : X.Opens}
    {A B : Over X} (h : Relation.ReflTransGen (IsProperNormalizedBlowUpOutside U) A B) :
    Relation.ReflTransGen (IsNormalizedBlowUpOutside U) A B := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail hstep.1

/-- Properness of the structure morphism depends only on the isomorphism class over the base. -/
private theorem isProper_of_overIso {S : Scheme.{u}} {A B : Over S} (e : A ≅ B)
    (hB : IsProper B.hom) : IsProper A.hom := by
  let : IsIso e.hom.left := by
    simpa only [Over.forget_map] using Functor.map_isIso (Over.forget S) e.hom
  let : IsProper B.hom := hB
  rw [← e.hom.w]
  infer_instance

/-- The source of a normalized blowup step over a normal base is normal, being a normalization. -/
private theorem isNormal_of_isNormalizedBlowUpOutside {X : Scheme.{u}} {U : X.Opens}
    {A B : Over X} (hAB : IsNormalizedBlowUpOutside U A B) : IsNormal B.left := by
  obtain ⟨hA, x, hx, -, e, -⟩ := hAB
  let : IsNormal (Stacks.Blowup.normalizedBlowUpScheme A.left hA x hx) :=
    Scheme.isNormal_normalizationScheme _ (Stacks.Blowup.finite_irreducibleComponents_blowUp _ hA)
  exact isNormal_of_flat_preimmersion e.hom

/-- Every stage of a sequence of normalized blowups over a normal base is normal. -/
private theorem isNormal_of_reflTransGen {X : Scheme.{u}} {U : X.Opens} {A B : Over X}
    (hA : IsNormal A.left)
    (hAB : Relation.ReflTransGen (IsNormalizedBlowUpOutside U) A B) : IsNormal B.left := by
  induction hAB with
  | refl => exact hA
  | tail _ hstep _ => exact isNormal_of_isNormalizedBlowUpOutside hstep

/-- Quasi-compact opens of the source of a normalized blowup step over a reduced base have
finitely many irreducible components: the blowup of a reduced scheme is reduced, so its
normalization is birational onto it, and that property ascends along the isomorphism to the
source of the step. -/
private theorem finite_irreducibleComponents_of_isNormalizedBlowUpOutside {X : Scheme.{u}}
    {U : X.Opens} {A B : Over X} [IsReduced A.left]
    (hAB : IsNormalizedBlowUpOutside U A B) :
    ∀ V : B.left.Opens, IsCompact (V : Set B.left) → (irreducibleComponents V).Finite := by
  obtain ⟨hA, x, hx, -, e, -⟩ := hAB
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds A.left)
  let hB := Stacks.Blowup.finite_irreducibleComponents_blowUp I hA
  let : IsReduced (blowUp I) := isReduced_blowUp I
  have hbij := (Scheme.isBirational_normalization (blowUp I) hB).bijOn
  exact finite_irreducibleComponents_of_flat_preimmersion e.hom
    (finite_irreducibleComponents_of_mapsTo_injOn_genericPoints
      (Scheme.normalization (blowUp I) hB) hbij.mapsTo hbij.injOn hB)

/-- Replacing the source of a normalized blowup step by an isomorphic object over the base: the
centre is carried along the isomorphism, and the normalized blowing up at the transported centre
is identified with the original one, the reduced closed subscheme of a point pulling back to the
reduced closed subscheme of its preimage along an isomorphism. -/
private theorem isNormalizedBlowUpOutside_of_source_iso {X : Scheme.{u}} (U : X.Opens)
    {A B C : Over X} (e : C ≅ A) (h : IsNormalizedBlowUpOutside U A B) :
    IsNormalizedBlowUpOutside U C B := by
  obtain ⟨hA, x, hx, hout, eB, heB⟩ := h
  let a : C.left ≅ A.left := (Over.forget X).mapIso e
  let y := a.inv x
  have hyx : a.hom y = x := by simp [y]
  have hCfin : ∀ V : C.left.Opens, IsCompact (V : Set C.left) →
      (irreducibleComponents V).Finite :=
    finite_irreducibleComponents_of_flat_preimmersion a.hom hA
  obtain ⟨hy, hideal⟩ := vanishingIdeal_singleton_comap_of_isIso a.hom x hx y hyx
  obtain ⟨g, hg⟩ :=
    exists_isPullback_normalizedBlowUp_comap a.hom hA hCfin x hx y hy hideal
  let : IsIso g := (MorphismProperty.IsStableUnderBaseChange.isomorphisms Scheme).of_isPullback
    hg.flip (show MorphismProperty.isomorphisms Scheme a.hom from inferInstance)
  refine ⟨hCfin, y, hy, ?_, eB ≪≫ (asIso g).symm, ?_⟩
  · have hw : C.hom y = A.hom x := by
      rw [← e.hom.w]
      change A.hom (a.hom y) = A.hom x
      rw [hyx]
    simpa only [hw] using hout
  · let νC := Stacks.Blowup.normalizedBlowUp C.left hCfin y hy
    let νA := Stacks.Blowup.normalizedBlowUp A.left hA x hx
    have hf : νC ≫ C.hom = g ≫ νA ≫ A.hom := by
      rw [← e.hom.w]
      change νC ≫ a.hom ≫ A.hom = g ≫ νA ≫ A.hom
      rw [← Category.assoc, ← hg.w, Category.assoc]
    have hi : inv g ≫ νC ≫ C.hom = νA ≫ A.hom := (IsIso.inv_comp_eq g).mpr hf
    change (eB.hom ≫ inv g) ≫ νC ≫ C.hom = B.hom
    rw [Category.assoc, hi, heB]

/-- Quasi-compact opens of every stage of a sequence of normalized blowups over a normal base
have finitely many irreducible components. -/
private theorem finite_irreducibleComponents_of_reflTransGen {X : Scheme.{u}} {U : X.Opens}
    {A B : Over X} (hAnormal : IsNormal A.left)
    (hA : ∀ V : A.left.Opens, IsCompact (V : Set A.left) → (irreducibleComponents V).Finite)
    (h : Relation.ReflTransGen (IsNormalizedBlowUpOutside U) A B) :
    ∀ V : B.left.Opens, IsCompact (V : Set B.left) → (irreducibleComponents V).Finite := by
  cases h with
  | refl => exact hA
  | @tail C B hAC hCB =>
    let : IsNormal C.left := isNormal_of_reflTransGen hAnormal hAC
    exact finite_irreducibleComponents_of_isNormalizedBlowUpOutside hCB

/-- The base change of the identity is the identity. -/
private def pullbackIdentityIso {S T : Scheme.{u}} (s : T ⟶ S) :
    ((Over.pullback s).obj (Over.mk (𝟙 S))) ≅ Over.mk (𝟙 T) :=
  Over.isoMk (asIso (Limits.pullback.snd (𝟙 S) s)) (by simp)

/-- A scheme is regular iff it is locally Noetherian with regular local rings. -/
private theorem isRegular_iff_isLocallyNoetherian_and_stalks (X : Scheme.{u}) :
    IsRegular X ↔ IsLocallyNoetherian X ∧ ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) := by
  simpa using (isRegular_tfae X).out 1 2 (by simp) (by simp)

/-- The two images of a point of a pullback have the same image in the base. -/
private theorem pullback_fst_apply_eq_snd_apply {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (z : (Limits.pullback f g : Scheme.{u})) :
    f (Limits.pullback.fst f g z) = g (Limits.pullback.snd f g z) := by
  rw [← Scheme.Hom.comp_apply, Limits.pullback.condition, Scheme.Hom.comp_apply]

/-- A point of the spectrum of a local ring maps to a point specializing to the base point. -/
private theorem fromSpecStalk_apply_specializes {S : Scheme.{u}} (s : S)
    (y : Spec (S.presheaf.stalk s)) : S.fromSpecStalk s y ⤳ s := by
  have hr : S.fromSpecStalk s y ∈ Set.range (S.fromSpecStalk s) := ⟨y, rfl⟩
  rwa [Scheme.range_fromSpecStalk] at hr

/-! ### The flat cover by the complement and the local spectra -/

namespace FinitePresentationAwayPointsSituation

variable (D : FinitePresentationAwayPointsSituation.{u})

/-- The family consisting of the open complement of the distinguished points and the spectra of
the local rings at them. -/
private abbrev localizationPrecover : PreZeroHypercover D.S where
  I₀ := Option (Fin D.n)
  X := fun i => match i with
    | none => D.complement.toScheme
    | some i => D.localScheme i
  f := fun i => match i with
    | none => D.complement.ι
    | some i => D.S.fromSpecStalk (D.points i)

private theorem flat_localizationPrecover (i : (localizationPrecover D).I₀) :
    Flat ((localizationPrecover D).f i) := by
  cases i with
  | none => exact inferInstanceAs (Flat D.complement.ι)
  | some i => exact flat_fromSpecStalk D.S (D.points i)

private theorem isPreimmersion_localizationPrecover (i : (localizationPrecover D).I₀) :
    IsPreimmersion ((localizationPrecover D).f i) := by
  cases i with
  | none => exact inferInstanceAs (IsPreimmersion D.complement.ι)
  | some i => exact inferInstanceAs (IsPreimmersion (D.S.fromSpecStalk (D.points i)))

/-- The family is jointly surjective: a point of the base is either in the complement of the
distinguished points or is one of them, and a distinguished point is the image of the closed
point of its own local spectrum. -/
private theorem exists_mem_range_localizationPrecover (x : D.S) :
    ∃ i : (localizationPrecover D).I₀, ∃ y, (localizationPrecover D).f i y = x := by
  by_cases hx : x ∈ D.complement
  · exact ⟨none, ⟨x, hx⟩, rfl⟩
  · obtain ⟨i, rfl⟩ : x ∈ Set.range D.points := not_not.mp hx
    exact ⟨some i, IsLocalRing.closedPoint _, Scheme.fromSpecStalk_closedPoint⟩

/-- The family is a quasi-compact cover: a quasi-compact open of the base is covered by its
inverse image in the complement, which is quasi-compact because the inclusion of the complement
is, together with the whole of the local spectrum at each distinguished point it contains. -/
private theorem quasiCompactCover_localizationPrecover :
    QuasiCompactCover (localizationPrecover D) := by
  classical
  let : QuasiCompact D.complement.ι := D.complement_quasiCompact
  refine ⟨fun {V} hV => ?_⟩
  let W : ∀ i : Option (Fin D.n), ((localizationPrecover D).X i).Opens
    | none => D.complement.ι ⁻¹ᵁ V
    | some i => if D.points i ∈ V then ⊤ else ⊥
  refine IsCompactOpenCovered.of_finite id W ?_ ?_
  · intro i
    cases i with
    | none => exact D.complement.ι.isCompact_preimage hV.isCompact
    | some i =>
      change IsCompact (↑(if D.points i ∈ V then ⊤ else ⊥ : (D.localScheme i).Opens) :
        Set (D.localScheme i))
      split_ifs
      · exact isCompact_univ
      · exact isCompact_empty
  · ext x
    simp only [Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨i, y, hy, rfl⟩
      cases i with
      | none => exact hy
      | some i =>
        change y ∈ (if D.points i ∈ V then ⊤ else ⊥ : (D.localScheme i).Opens) at hy
        split_ifs at hy with hi
        · exact (fromSpecStalk_apply_specializes (D.points i) y).mem_open V.2 hi
        · exact False.elim hy
    · intro hx
      by_cases hcomp : x ∈ D.complement
      · exact ⟨none, ⟨x, hcomp⟩, hx, rfl⟩
      · obtain ⟨i, rfl⟩ : x ∈ Set.range D.points := not_not.mp hcomp
        refine ⟨some i, IsLocalRing.closedPoint (D.S.presheaf.stalk (D.points i)), ?_,
          Scheme.fromSpecStalk_closedPoint⟩
        change IsLocalRing.closedPoint (D.S.presheaf.stalk (D.points i)) ∈
          (if D.points i ∈ V then ⊤ else ⊥ : (D.localScheme i).Opens)
        rw [ite_eq_left (show D.points i ∈ V from hx)]
        exact Set.mem_univ _

/-- The open complement of the distinguished points together with the spectra of the local rings
at them form a cover of the base in the flat topology. -/
private abbrev localizationCover : D.S.Cover Scheme.fpqcPrecoverage where
  __ := localizationPrecover D
  mem₀ :=
    ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.mpr (quasiCompactCover_localizationPrecover D),
      (Scheme.presieve₀_mem_precoverage_iff (P := @Flat) (localizationPrecover D)).mpr
        ⟨exists_mem_range_localizationPrecover D, flat_localizationPrecover D⟩⟩

/-- **Properness over the base is checked on the complement and on the local spectra.**
Properness is local at the target for the flat topology. -/
theorem isProper_of_localizations (A : Over D.S)
    (hU : IsProper ((Over.pullback D.complement.ι).obj A).hom)
    (hlocal : ∀ i, IsProper
      ((Over.pullback (D.S.fromSpecStalk (D.points i))).obj A).hom) :
    IsProper A.hom := by
  let : MorphismProperty.IsLocalAtTarget (@IsProper : MorphismProperty Scheme.{u})
    Scheme.fpqcPrecoverage := isProper_isLocalAtTarget_fpqc
  exact MorphismProperty.IsLocalAtTarget.of_zeroHypercover (localizationCover D) fun
    | none => hU
    | some i => hlocal i

/-- **Regularity of a scheme over the base is checked on the complement and on the local
spectra.** Each member of the flat cover pulls back to a flat preimmersion onto the given scheme,
and a flat preimmersion induces isomorphisms on local rings, so the local rings of the given
scheme are already local rings of the members. -/
theorem isRegular_of_localizations (A : Over D.S) [IsLocallyNoetherian A.left]
    (hU : IsRegular ((Over.pullback D.complement.ι).obj A).left)
    (hlocal : ∀ i, IsRegular
      ((Over.pullback (D.S.fromSpecStalk (D.points i))).obj A).left) :
    IsRegular A.left := by
  let E := (localizationCover D).pullback₁ A.hom
  have hregE : ∀ i : E.I₀, IsRegular (E.X i) := fun
    | none => hU
    | some i => hlocal i
  have hsurj : ∀ x : A.left, ∃ i : E.I₀, x ∈ Set.range (E.f i) :=
    ((Scheme.presieve₀_mem_precoverage_iff E.toPreZeroHypercover).mp E.mem₀.2).1
  have hstalk : ∀ x : A.left, IsRegularLocalRing (A.left.presheaf.stalk x) := by
    intro x
    obtain ⟨i, y, rfl⟩ := hsurj x
    let : Flat ((localizationPrecover D).f i) := flat_localizationPrecover D i
    let : IsPreimmersion ((localizationPrecover D).f i) :=
      isPreimmersion_localizationPrecover D i
    let : Flat (E.f i) := by
      change Flat (Limits.pullback.fst A.hom ((localizationPrecover D).f i))
      infer_instance
    let : IsPreimmersion (E.f i) := by
      change IsPreimmersion (Limits.pullback.fst A.hom ((localizationPrecover D).f i))
      infer_instance
    let : IsIso ((E.f i).stalkMap y) := isIso_stalkMap_of_flat_preimmersion (E.f i) y
    let : IsRegularLocalRing ((E.X i).presheaf.stalk y) :=
      ((isRegular_iff_isLocallyNoetherian_and_stalks (E.X i)).mp (hregE i)).2 y
    exact IsRegularLocalRing.of_ringEquiv
      (asIso ((E.f i).stalkMap y)).commRingCatIsoToRingEquiv.symm
  exact (isRegular_iff_isLocallyNoetherian_and_stalks A.left).mpr ⟨inferInstance, hstalk⟩

/-! ### Lifting one local normalized blowup to the base -/

/-- The image in the base of the closed point of the local spectrum at a distinguished point is
that distinguished point, so no point of the local spectrum at one distinguished point maps to
another: the points of the local spectrum all specialize to the distinguished point, and a
specialization of a closed point is that point. -/
private theorem fromSpecStalk_ne_other_point (i j : Fin D.n) (hij : i ≠ j)
    (y : D.localScheme i) : D.S.fromSpecStalk (D.points i) y ≠ D.points j := by
  intro hy
  have hspec' : D.points j ⤳ D.points i := by
    simpa [hy] using fromSpecStalk_apply_specializes (D.points i) y
  have hmem := (specializes_iff_forall_closed.mp hspec') _ (D.points_closed j) (by simp)
  exact hij (D.points_injective (Set.mem_singleton_iff.mp hmem))

end FinitePresentationAwayPointsSituation

/-- The image of a closed point of a base change to the spectrum of a local ring at a closed
point of the base is closed: a point of the source specializing to it also lies over the closed
point of the base, so it is the image of a point of the base change, which then specializes to
the given closed point and so equals it. -/
private theorem isClosed_image_closedPoint_pullback_fromSpecStalk {X S : Scheme.{u}} (f : X ⟶ S)
    (s : S) (hs : IsClosed ({s} : Set S))
    (y : (Limits.pullback f (S.fromSpecStalk s) : Scheme.{u}))
    (hy : IsClosed ({y} : Set (Limits.pullback f (S.fromSpecStalk s) : Scheme.{u})))
    (hys : Limits.pullback.snd f (S.fromSpecStalk s) y =
      IsLocalRing.closedPoint (S.presheaf.stalk s)) :
    IsClosed ({Limits.pullback.fst f (S.fromSpecStalk s) y} : Set X) := by
  let q := Limits.pullback.fst f (S.fromSpecStalk s)
  have hqy : f (q y) = s := by
    have h := pullback_fst_apply_eq_snd_apply f (S.fromSpecStalk s) y
    rwa [hys, Scheme.fromSpecStalk_closedPoint] at h
  rw [← closure_eq_iff_isClosed]
  refine Set.Subset.antisymm ?_ subset_closure
  intro z hz
  have hyz : q y ⤳ z := specializes_iff_mem_closure.mpr hz
  have hsz : s ⤳ f z := hqy ▸ hyz.map f.continuous
  have hzs : f z = s := Set.mem_singleton_iff.mp
    ((specializes_iff_forall_closed.mp hsz) {s} hs (Set.mem_singleton s))
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := f) (g := S.fromSpecStalk s) z (IsLocalRing.closedPoint (S.presheaf.stalk s))
    (hzs.trans Scheme.fromSpecStalk_closedPoint.symm)
  have hyw : y ⤳ w := (IsPreimmersion.isEmbedding q).isInducing.specializes_iff.mp
    (by simpa only [q, hw] using hyz)
  have hwy : w = y := Set.mem_singleton_iff.mp
    ((specializes_iff_forall_closed.mp hyw) {y} hy (Set.mem_singleton y))
  exact Set.mem_singleton_iff.mpr (hw.symm.trans (congrArg q hwy))

/-- **A normalized blowup disappears after a base change which misses its centre.** The
normalized blowing up of a normal scheme at a closed point is an isomorphism over the complement
of that point, and a base change landing in that complement stays an isomorphism. -/
private theorem nonempty_pullback_iso_of_ne_center {S : Scheme.{u}} (A : Over S)
    [IsNormal A.left]
    (hA : ∀ V : A.left.Opens, IsCompact (V : Set A.left) → (irreducibleComponents V).Finite)
    (x : A.left) (hx : IsClosed ({x} : Set A.left)) {T : Scheme.{u}} (s : T ⟶ S)
    (hs : ∀ t, s t ≠ A.hom x) :
    Nonempty (((Over.pullback s).obj
        (Over.mk (Stacks.Blowup.normalizedBlowUp A.left hA x hx ≫ A.hom))) ≅
      (Over.pullback s).obj A) := by
  let ν := Stacks.Blowup.normalizedBlowUp A.left hA x hx
  let q := Limits.pullback.fst A.hom s
  let U : A.left.Opens := ⟨({x} : Set A.left)ᶜ, hx.isOpen_compl⟩
  have hiso : IsIso (ν ∣_ U) := isIso_normalizedBlowUp_restrict_compl_singleton hA x hx
  have hq : ∀ z : (Limits.pullback A.hom s : Scheme.{u}), q z ∈ U := by
    intro z hz
    apply hs (Limits.pullback.snd A.hom s z)
    exact (pullback_fst_apply_eq_snd_apply A.hom s z).symm.trans
      (congrArg A.hom (Set.mem_singleton_iff.mp hz))
  let : IsIso (Limits.pullback.snd ν q) :=
    isIso_pullback_snd_of_isIso_morphismRestrict ν q U hiso hq
  have hsq := (IsPullback.of_hasPullback ν q).flip.paste_horiz
    (IsPullback.of_hasPullback A.hom s).flip
  let e : Over.mk (Limits.pullback.snd ν q ≫ Limits.pullback.snd A.hom s) ≅
      (Over.pullback s).obj (Over.mk (ν ≫ A.hom)) :=
    Over.isoMk hsq.flip.isoPullback hsq.flip.isoPullback_hom_snd
  exact ⟨e.symm ≪≫ Over.isoMk (asIso (Limits.pullback.snd ν q)) rfl⟩

namespace FinitePresentationAwayPointsSituation

variable (D : FinitePresentationAwayPointsSituation.{u})

/-- **One normalized blowup over the spectrum of a local ring at a distinguished point comes from
one over the base.** The centre of the local blowup lies over the closed point of the local
spectrum, hence over a closed point of the source of the given object which maps to the
distinguished point; blowing that point up and normalizing gives a step over the base whose
localization at the chosen distinguished point is the given local step, because the reduced
closed subscheme of the chosen centre pulls back to the reduced closed subscheme of the local one
and blowing up and normalizing commute with that base change. The localizations at the other
distinguished points and the restriction to the complement are unchanged, the global centre lying
over neither. -/
private theorem exists_isNormalizedBlowUpOutside_lift (i : Fin D.n) (A : Over D.S)
    [IsNormal A.left]
    (hA : ∀ V : A.left.Opens, IsCompact (V : Set A.left) → (irreducibleComponents V).Finite)
    {B : Over (D.localScheme i)}
    (h : IsNormalizedBlowUpOutside (D.puncturedLocalScheme i)
      ((Over.pullback (D.S.fromSpecStalk (D.points i))).obj A) B) :
    ∃ C : Over D.S, IsNormalizedBlowUpOutside D.complement A C ∧
      Nonempty (((Over.pullback (D.S.fromSpecStalk (D.points i))).obj C) ≅ B) ∧
      (∀ j, j ≠ i → Nonempty
        (((Over.pullback (D.S.fromSpecStalk (D.points j))).obj C) ≅
          ((Over.pullback (D.S.fromSpecStalk (D.points j))).obj A))) ∧
      Nonempty (((Over.pullback D.complement.ι).obj C) ≅
        ((Over.pullback D.complement.ι).obj A)) := by
  let s := D.S.fromSpecStalk (D.points i)
  let L := (Over.pullback s).obj A
  let q : L.left ⟶ A.left := Limits.pullback.fst A.hom s
  let : Flat s := flat_fromSpecStalk D.S (D.points i)
  obtain ⟨hL, y, hy, hout, eB, heB⟩ := h
  have hys : L.hom y = IsLocalRing.closedPoint (D.S.presheaf.stalk (D.points i)) := by
    change ¬ L.hom y ≠ IsLocalRing.closedPoint _ at hout
    exact not_not.mp hout
  let x := q y
  have hx : IsClosed ({x} : Set A.left) :=
    isClosed_image_closedPoint_pullback_fromSpecStalk A.hom (D.points i) (D.points_closed i)
      y hy hys
  have hxs : A.hom x = D.points i := by
    have hc : A.hom x = s (L.hom y) := pullback_fst_apply_eq_snd_apply A.hom s y
    rwa [hys, Scheme.fromSpecStalk_closedPoint] at hc
  let C : Over D.S := Over.mk (Stacks.Blowup.normalizedBlowUp A.left hA x hx ≫ A.hom)
  have hAC : IsNormalizedBlowUpOutside D.complement A C := by
    refine ⟨hA, x, hx, ?_, Iso.refl _, by simp [C]⟩
    change A.hom x ∉ (Set.range D.points)ᶜ
    exact fun hn => hn ⟨i, hxs.symm⟩
  refine ⟨C, hAC, ?_, ?_, ?_⟩
  · obtain ⟨hy', hideal⟩ := vanishingIdeal_singleton_comap_pullbackFst A.hom s x hx
      (pointToSpecStalk A.hom x hxs) (pointToSpecStalk_comp_fromSpecStalk A.hom x hxs) y rfl
    obtain ⟨m, hm⟩ := exists_isPullback_normalizedBlowUp_comap q hA hL x hx y hy hideal
    let ν := Stacks.Blowup.normalizedBlowUp L.left hL y hy
    let νA := Stacks.Blowup.normalizedBlowUp A.left hA x hx
    have hsq : IsPullback (ν ≫ L.hom) m s (νA ≫ A.hom) :=
      hm.flip.paste_horiz (IsPullback.of_hasPullback A.hom s).flip
    let e : Over.mk (ν ≫ L.hom) ≅ (Over.pullback s).obj C :=
      Over.isoMk hsq.flip.isoPullback hsq.flip.isoPullback_hom_snd
    exact ⟨e.symm ≪≫ (Over.isoMk eB heB).symm⟩
  · intro j hji
    exact nonempty_pullback_iso_of_ne_center A hA x hx (D.S.fromSpecStalk (D.points j))
      (fun t => hxs ▸ fromSpecStalk_ne_other_point D j i hji t)
  · exact nonempty_pullback_iso_of_ne_center A hA x hx D.complement.ι (fun t ht => by
      exact t.2 ⟨i, hxs.symm.trans ht.symm⟩)

/-- **A sequence of normalized blowups over the spectrum of a local ring at a distinguished point
comes from one over the base.** The local sequence is lifted one step at a time; at each step the
localizations at the other distinguished points and the restriction to the complement stay as
they were, so the composite isomorphisms are carried along. -/
private theorem exists_reflTransGen_lift (i : Fin D.n) [IsNormal D.S]
    (hS : ∀ V : D.S.Opens, IsCompact (V : Set D.S) → (irreducibleComponents V).Finite)
    (A : Over D.S) (hAproper : IsProper A.hom)
    (hA : Relation.ReflTransGen (IsProperNormalizedBlowUpOutside D.complement)
      (Over.mk (𝟙 D.S)) A)
    {L Z : Over (D.localScheme i)}
    (eA : ((Over.pullback (D.S.fromSpecStalk (D.points i))).obj A) ≅ L)
    (h : Relation.ReflTransGen
      (IsProperNormalizedBlowUpOutside (D.puncturedLocalScheme i)) L Z) :
    ∃ C : Over D.S,
      Relation.ReflTransGen (IsProperNormalizedBlowUpOutside D.complement) A C ∧
      IsProper C.hom ∧
      Nonempty (((Over.pullback (D.S.fromSpecStalk (D.points i))).obj C) ≅ Z) ∧
      (∀ j, j ≠ i → Nonempty
        (((Over.pullback (D.S.fromSpecStalk (D.points j))).obj C) ≅
          ((Over.pullback (D.S.fromSpecStalk (D.points j))).obj A))) ∧
      Nonempty (((Over.pullback D.complement.ι).obj C) ≅
        ((Over.pullback D.complement.ι).obj A)) := by
  induction h with
  | refl => exact ⟨A, .refl, hAproper, ⟨eA⟩, fun _ _ => ⟨Iso.refl _⟩, ⟨Iso.refl _⟩⟩
  | @tail Z W hZ hZW ih =>
    obtain ⟨C, hAC, hCproper, ⟨eC⟩, hCother, ⟨eCU⟩⟩ := ih
    have hC := (reflTransGen_isNormalizedBlowUpOutside_of_isProper hA).trans
      (reflTransGen_isNormalizedBlowUpOutside_of_isProper hAC)
    let : IsNormal C.left :=
      isNormal_of_reflTransGen (inferInstanceAs (IsNormal D.S)) hC
    let : Flat (D.S.fromSpecStalk (D.points i)) := flat_fromSpecStalk D.S (D.points i)
    let : IsNormal ((Over.pullback (D.S.fromSpecStalk (D.points i))).obj C).left :=
      isNormal_of_flat_preimmersion
        (Limits.pullback.fst C.hom (D.S.fromSpecStalk (D.points i)))
    let eZ : ((Over.pullback (D.S.fromSpecStalk (D.points i))).obj C).left ≅ Z.left :=
      (Over.forget _).mapIso eC
    let : IsNormal Z.left := isNormal_of_flat_preimmersion eZ.inv
    obtain ⟨B, hCB, ⟨eB⟩, hBother, ⟨eBU⟩⟩ := exists_isNormalizedBlowUpOutside_lift D i C
      (finite_irreducibleComponents_of_reflTransGen (inferInstanceAs (IsNormal D.S)) hS hC)
      (isNormalizedBlowUpOutside_of_source_iso _ eC hZW.1)
    let : IsProper C.hom := hCproper
    have hBproper : IsProper B.hom := by
      refine isProper_of_localizations D B ?_ ?_
      · exact isProper_of_overIso eBU (by
          change IsProper (Limits.pullback.snd C.hom D.complement.ι)
          infer_instance)
      · intro j
        by_cases hji : j = i
        · subst j
          exact isProper_of_overIso eB hZW.2
        · exact isProper_of_overIso (hBother j hji).some (by
            change IsProper (Limits.pullback.snd C.hom (D.S.fromSpecStalk (D.points j)))
            infer_instance)
    refine ⟨B, hAC.tail ⟨hCB, hBproper⟩, hBproper, ⟨eB⟩, ?_, ⟨eBU ≪≫ eCU⟩⟩
    intro j hji
    exact ⟨(hBother j hji).some ≪≫ (hCother j hji).some⟩

/-- **Local sequences of normalized blowups, one over the spectrum of the local ring at each
distinguished point, come from a single sequence over the base.** The distinguished points are
treated one at a time: lifting the sequence at one of them leaves the localizations at the others
and the restriction to the complement unchanged, so the ones already installed survive and the
ones still to come are still trivial. -/
theorem exists_properNormalizedBlowUpSequence_of_local [IsNormal D.S]
    (hS : ∀ V : D.S.Opens, IsCompact (V : Set D.S) → (irreducibleComponents V).Finite)
    (Z : ∀ i, Over (D.localScheme i))
    (hZ : ∀ i, Relation.ReflTransGen
      (IsProperNormalizedBlowUpOutside (D.puncturedLocalScheme i))
      (Over.mk (𝟙 (D.localScheme i))) (Z i)) :
    ∃ A : Over D.S,
      Relation.ReflTransGen (IsProperNormalizedBlowUpOutside D.complement)
        (Over.mk (𝟙 D.S)) A ∧
      IsProper A.hom ∧
      (∀ i, Nonempty (((Over.pullback (D.S.fromSpecStalk (D.points i))).obj A) ≅ Z i)) ∧
      Nonempty (((Over.pullback D.complement.ι).obj A) ≅
        Over.mk (𝟙 D.complement.toScheme)) := by
  classical
  have build (t : Finset (Fin D.n)) :
      ∃ A : Over D.S,
        Relation.ReflTransGen (IsProperNormalizedBlowUpOutside D.complement)
          (Over.mk (𝟙 D.S)) A ∧
        IsProper A.hom ∧
        (∀ i ∈ t, Nonempty (((Over.pullback (D.S.fromSpecStalk (D.points i))).obj A) ≅ Z i)) ∧
        (∀ i ∉ t, Nonempty (((Over.pullback (D.S.fromSpecStalk (D.points i))).obj A) ≅
          Over.mk (𝟙 (D.localScheme i)))) ∧
        Nonempty (((Over.pullback D.complement.ι).obj A) ≅
          Over.mk (𝟙 D.complement.toScheme)) := by
    induction t using Finset.induction_on with
    | empty =>
      exact ⟨Over.mk (𝟙 D.S), .refl, inferInstanceAs (IsProper (𝟙 D.S)), by simp,
        fun i _ => ⟨pullbackIdentityIso _⟩, ⟨pullbackIdentityIso _⟩⟩
    | @insert i t hi ih =>
      obtain ⟨A, hA, hAproper, hAdone, hAtodo, ⟨eAU⟩⟩ := ih
      obtain ⟨B, hAB, hBproper, ⟨eB⟩, hBother, ⟨eBU⟩⟩ :=
        exists_reflTransGen_lift D i hS A hAproper hA (hAtodo i hi).some (hZ i)
      refine ⟨B, hA.trans hAB, hBproper, ?_, ?_, ⟨eBU ≪≫ eAU⟩⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact ⟨eB⟩
        · have hji : j ≠ i := fun h => hi (h ▸ hj)
          exact ⟨(hBother j hji).some ≪≫ (hAdone j hj).some⟩
      · intro j hj
        have hji : j ≠ i := fun h => hj (h ▸ Finset.mem_insert_self _ _)
        exact ⟨(hBother j hji).some ≪≫
          (hAtodo j (fun h => hj (Finset.mem_insert_of_mem h))).some⟩
  obtain ⟨A, hA, hAproper, hAdone, -, hAU⟩ := build Finset.univ
  exact ⟨A, hA, hAproper, fun i => hAdone i (Finset.mem_univ _), hAU⟩

end FinitePresentationAwayPointsSituation

/-! ### From a sequence over the base to a chain of normalized blowups -/

/-- Every stage of a chain of normalized blowups is proper over the base. -/
theorem NormalizedBlowUpChain.isProper {Y : Scheme.{u}}
    {hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite}
    {X : Scheme.{u}} {f : X ⟶ Y} (h : NormalizedBlowUpChain Y hY X f) : IsProper f := by
  induction h with
  | normalization hproper => exact hproper
  | blowUp _ _ _ _ hproper _ => exact hproper

/-- **A sequence of proper normalized blowups over the normalization of `Y`, starting from the
identity, is a chain of normalized blowups of `Y`** in the sense of [Stacks, Tag 0BGL]: the
normalization of `Y` is the first stage of such a chain, and each further step blows up a closed
point of the previous stage, properness over `Y` following from properness over the
normalization. -/
theorem exists_normalizedBlowUpChain_of_reflTransGen (Y : Scheme.{u})
    (hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite)
    (hproperν : IsProper (Scheme.normalization Y hY)) (U : (Y.normalizationScheme hY).Opens)
    {Z : Over (Y.normalizationScheme hY)}
    (h : Relation.ReflTransGen (IsProperNormalizedBlowUpOutside U)
      (Over.mk (𝟙 (Y.normalizationScheme hY))) Z) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Y.normalizationScheme hY),
      NormalizedBlowUpChain Y hY X (f ≫ Scheme.normalization Y hY) ∧
        Nonempty (Over.mk f ≅ Z) := by
  induction h with
  | refl =>
    refine ⟨Y.normalizationScheme hY, 𝟙 _, ?_, ⟨Iso.refl _⟩⟩
    simpa only [Category.id_comp] using NormalizedBlowUpChain.normalization hproperν
  | @tail A B hA hAB ih =>
    obtain ⟨X, f, hchain, ⟨e⟩⟩ := ih
    obtain ⟨hX, x, hx, -, eB, heB⟩ := isNormalizedBlowUpOutside_of_source_iso U e hAB.1
    let b := Stacks.Blowup.normalizedBlowUp X hX x hx
    let eOver : B ≅ Over.mk (b ≫ f) := Over.isoMk eB heB
    let : IsProper (Scheme.normalization Y hY) := hproperν
    let : IsProper (b ≫ f) := isProper_of_overIso eOver.symm hAB.2
    have hproperY : IsProper (b ≫ f ≫ Scheme.normalization Y hY) := by
      rw [← Category.assoc]
      infer_instance
    refine ⟨Stacks.Blowup.normalizedBlowUpScheme X hX x hx, b ≫ f, ?_, ⟨eOver.symm⟩⟩
    rw [Category.assoc]
    exact NormalizedBlowUpChain.blowUp hchain hX x hx hproperY

/-! ### From a chain over the spectrum of a local ring to a sequence -/

/-- A closed point of the spectrum of a local ring is its closed point: a point is closed exactly
when its prime is maximal, and a local ring has only one maximal ideal. -/
private theorem eq_closedPoint_of_isClosed_singleton (R : Type u) [CommRing R] [IsLocalRing R]
    (x : Spec (.of R)) (hx : IsClosed ({x} : Set (Spec (.of R)))) :
    x = IsLocalRing.closedPoint R :=
  PrimeSpectrum.ext
    (IsLocalRing.eq_maximalIdeal ((PrimeSpectrum.isClosed_singleton_iff_isMaximal x).mp hx))

/-- **A resolution by normalized blowups of a normal base all of whose closed points lie outside
`U` is a sequence of proper normalized blowups at closed points outside `U`, with regular total
space.** Over a normal base the normalization step of the chain is an isomorphism, so the
sequence starts at the identity; the centre of each later step maps to a closed point of the base,
the stage it is taken on being proper over the base and hence a closed map. -/
private theorem exists_reflTransGen_of_hasResolutionByNormalizedBlowUps {S : Scheme.{u}}
    [IsNormal S] [IsLocallyNoetherian S] (U : S.Opens)
    (hU : ∀ z : S, IsClosed ({z} : Set S) → z ∉ (U : Set S))
    (hres : HasResolutionByNormalizedBlowUps S) :
    ∃ Z : Over S, Relation.ReflTransGen (IsProperNormalizedBlowUpOutside U)
        (Over.mk (𝟙 S)) Z ∧ IsProper Z.hom ∧ IsRegular Z.left := by
  obtain ⟨hS, X, f, hchain, hreg⟩ := hres
  have hseq : ∃ Z : Over S, Relation.ReflTransGen (IsProperNormalizedBlowUpOutside U)
      (Over.mk (𝟙 S)) Z ∧ Nonempty (Z ≅ Over.mk f) := by
    clear hreg
    induction hchain with
    | normalization hproper =>
      let : IsIso (Scheme.normalization S hS) :=
        (Scheme.isIso_normalization_iff_isNormal S hS).2 inferInstance
      exact ⟨Over.mk (𝟙 S), .refl,
        ⟨Over.isoMk (asIso (Scheme.normalization S hS)).symm (by simp)⟩⟩
    | @blowUp W g previous hW w hw hproper ih =>
      obtain ⟨Z, hZ, ⟨eZ⟩⟩ := ih
      let : IsProper g := previous.isProper
      have hwclosed : IsClosed ({g w} : Set S) := by
        simpa only [Set.image_singleton] using g.isClosedMap _ hw
      refine ⟨Over.mk (Stacks.Blowup.normalizedBlowUp W hW w hw ≫ g),
        hZ.tail ⟨isNormalizedBlowUpOutside_of_source_iso U eZ
          ⟨hW, w, hw, hU _ hwclosed, Iso.refl _, by simp⟩, hproper⟩, ⟨Iso.refl _⟩⟩
  obtain ⟨Z, hZ, ⟨eZ⟩⟩ := hseq
  have hproperZ : IsProper Z.hom := isProper_of_overIso eZ hchain.isProper
  let : IsProper Z.hom := hproperZ
  let : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  exact ⟨Z, hZ, hproperZ, isRegular_of_iso ((Over.forget S).mapIso eZ) hreg⟩

/-! ### The singular points of a normal surface -/

/-- The local ring at a singular point of a normal locally Noetherian scheme of dimension at most
two has Krull dimension exactly two: at most two by the bound on the dimension of the scheme, and
more than one because a normal scheme is regular in codimension one. -/
theorem ringKrullDim_stalk_eq_two_of_mem_singularLocus (N : Scheme.{u})
    [IsLocallyNoetherian N] [IsNormal N] (hdim : topologicalKrullDim N ≤ 2) (y : N)
    (hy : y ∈ singularLocus N) : ringKrullDim (N.presheaf.stalk y) = 2 := by
  have hle : ringKrullDim (N.presheaf.stalk y) ≤ 2 := by
    rw [ringKrullDim_stalk_eq_coheight]
    have h := Order.coheight_le_krullDim y
    rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := N))] at h
    exact h.trans hdim
  have hR1 : IsRegularInCodimension N 1 :=
    ((isNormal_iff_hasPropertySk_two_and_isRegularInCodimension_one N).mp inferInstance).2
  have hgt : 1 < ringKrullDim (N.presheaf.stalk y) := not_le.mp fun h => hy (hR1 y h)
  exact le_antisymm hle (ENat.WithBot.add_one_le_iff.mpr hgt)

/-- A singular point of a normal locally Noetherian scheme of dimension at most two is a closed
point: its local ring has dimension two, so its coheight is maximal. -/
theorem isClosed_singleton_of_mem_singularLocus (N : Scheme.{u})
    [IsLocallyNoetherian N] [IsNormal N] (hdim : topologicalKrullDim N ≤ 2) (y : N)
    (hy : y ∈ singularLocus N) : IsClosed ({y} : Set N) := by
  have h := ringKrullDim_stalk_eq_two_of_mem_singularLocus N hdim y hy
  rw [ringKrullDim_stalk_eq_coheight] at h
  refine isClosed_singleton_of_coheight_two hdim (WithBot.coe_injective ?_)
  rw [h]
  norm_num

/-- The finitely many singular points of a normal Noetherian scheme of dimension at most two,
packaged as the standing situation of [Stacks, Tag 0BFU]. -/
private def singularPointsSituation (N : Scheme.{u}) [IsNoetherian N] [IsNormal N]
    (hdim : topologicalKrullDim N ≤ 2) (hsing : (singularLocus N).Finite) :
    FinitePresentationAwayPointsSituation.{u} := by
  classical
  let T := {y : N // y ∈ singularLocus N}
  let : Fintype T := hsing.fintype
  let e : Fin (Fintype.card T) ≃ T := (Fintype.equivFin T).symm
  exact { S := N
          n := Fintype.card T
          points := fun i => (e i).1
          points_injective := fun i j h => e.injective (Subtype.ext h)
          points_closed := fun i =>
            isClosed_singleton_of_mem_singularLocus N hdim (e i).1 (e i).2
          complement_quasiCompact := inferInstance }

/-- The distinguished points of the situation attached to the singular locus are singular. -/
private theorem singularPointsSituation_points_mem (N : Scheme.{u}) [IsNoetherian N] [IsNormal N]
    (hdim : topologicalKrullDim N ≤ 2) (hsing : (singularLocus N).Finite)
    (i : Fin (singularPointsSituation N hdim hsing).n) :
    (singularPointsSituation N hdim hsing).points i ∈ singularLocus N := by
  classical
  let T := {y : N // y ∈ singularLocus N}
  let : Fintype T := hsing.fintype
  change ((Fintype.equivFin T).symm i).1 ∈ singularLocus N
  exact ((Fintype.equivFin T).symm i).2

/-- The distinguished points of the situation attached to the singular locus are exactly the
singular points. -/
private theorem singularPointsSituation_range (N : Scheme.{u}) [IsNoetherian N] [IsNormal N]
    (hdim : topologicalKrullDim N ≤ 2) (hsing : (singularLocus N).Finite) :
    Set.range (singularPointsSituation N hdim hsing).points = singularLocus N := by
  classical
  let T := {y : N // y ∈ singularLocus N}
  let : Fintype T := hsing.fintype
  let e : Fin (Fintype.card T) ≃ T := (Fintype.equivFin T).symm
  refine Set.Subset.antisymm ?_ ?_
  · rintro y ⟨i, rfl⟩
    exact singularPointsSituation_points_mem N hdim hsing i
  · intro y hy
    obtain ⟨i, hi⟩ := e.surjective ⟨y, hy⟩
    exact ⟨i, congrArg Subtype.val hi⟩

/-- The complement of the singular locus is regular: its local rings are the local rings of the
scheme at points where those are regular. -/
private theorem isRegular_complement_singularPointsSituation (N : Scheme.{u}) [IsNoetherian N]
    [IsNormal N] (hdim : topologicalKrullDim N ≤ 2) (hsing : (singularLocus N).Finite) :
    IsRegular (singularPointsSituation N hdim hsing).complement.toScheme := by
  let D := singularPointsSituation N hdim hsing
  let : IsLocallyNoetherian D.S := inferInstanceAs (IsLocallyNoetherian N)
  let : IsLocallyNoetherian D.complement.toScheme :=
    isLocallyNoetherian_of_isOpenImmersion D.complement.ι
  refine (isRegular_iff_isLocallyNoetherian_and_stalks _).mpr ⟨inferInstance, fun x => ?_⟩
  have hx : D.complement.ι x ∉ singularLocus N := by
    rw [← singularPointsSituation_range N hdim hsing]
    exact x.2
  let : IsRegularLocalRing (D.S.presheaf.stalk (D.complement.ι x)) := not_not.mp hx
  exact IsRegularLocalRing.of_ringEquiv
    (asIso (D.complement.ι.stalkMap x)).commRingCatIsoToRingEquiv

/-! ### The resolution of singularities by normalized blowups -/

/-- **A two-dimensional integral Noetherian scheme has a resolution of singularities by
normalized blowups as soon as its normalization is finite with finitely many singular points and
the spectrum of the local ring at each of those has a resolution by normalized blowups.**

The singular points of the normalization `N` are closed, the local ring at a singular point of a
normal surface having dimension two, so they and the open complement of them put `N` in the
situation of [Stacks, Tag 0BFU]. The given local sequences of normalized blowups then assemble
into a single sequence of normalized blowups over `N` whose localizations are the given ones and
which is an isomorphism over the complement; that sequence is a chain in the sense of
[Stacks, Tag 0BGL] over `Y`, and its total space is regular because regularity is checked on the
flat cover of `N` by the complement, which is regular as it misses the singular locus, and by the
local spectra, over which the given sequences end in regular schemes. -/
theorem hasResolutionByNormalizedBlowUps_of_local (Y : Scheme.{u}) [IsIntegral Y]
    [IsNoetherian Y]
    (hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite)
    (hdim : topologicalKrullDim Y = 2)
    (hfin : IsFinite (Scheme.normalization Y hY))
    (hsing : (singularLocus (Y.normalizationScheme hY)).Finite)
    (hloc : ∀ y : Y.normalizationScheme hY, y ∈ singularLocus (Y.normalizationScheme hY) →
      HasResolutionByNormalizedBlowUps
        (Spec (.of ((Y.normalizationScheme hY).presheaf.stalk y)))) :
    HasResolutionByNormalizedBlowUps Y := by
  classical
  let N := Y.normalizationScheme hY
  let ν := Scheme.normalization Y hY
  let : IsFinite ν := hfin
  let : IsNormal N := Scheme.isNormal_normalizationScheme Y hY
  let : IsLocallyNoetherian N := LocallyOfFiniteType.isLocallyNoetherian ν
  let : CompactSpace N := QuasiCompact.compactSpace_of_compactSpace ν
  let : IsNoetherian N := {}
  have hdimN : topologicalKrullDim N ≤ 2 :=
    (topologicalKrullDim_le_of_isIntegralHom ν).trans_eq hdim
  let D := singularPointsSituation N hdimN hsing
  let : IsLocallyNoetherian D.S := inferInstanceAs (IsLocallyNoetherian N)
  let : IsNormal D.S := inferInstanceAs (IsNormal N)
  have hcomponents : ∀ V : D.S.Opens, IsCompact (V : Set D.S) →
      (irreducibleComponents V).Finite := finite_irreducibleComponents_of_isCompact D.S
  have hlocal : ∀ i : Fin D.n, ∃ Z : Over (D.localScheme i),
      Relation.ReflTransGen (IsProperNormalizedBlowUpOutside (D.puncturedLocalScheme i))
        (Over.mk (𝟙 (D.localScheme i))) Z ∧ IsProper Z.hom ∧ IsRegular Z.left := by
    intro i
    let : Flat (D.S.fromSpecStalk (D.points i)) := flat_fromSpecStalk D.S (D.points i)
    let : IsNormal (D.localScheme i) :=
      isNormal_of_flat_preimmersion (D.S.fromSpecStalk (D.points i))
    let : IsLocallyNoetherian (D.localScheme i) := by
      change IsLocallyNoetherian (Spec (.of (D.S.presheaf.stalk (D.points i))))
      exact isLocallyNoetherian_Spec.mpr inferInstance
    refine exists_reflTransGen_of_hasResolutionByNormalizedBlowUps _ (fun z hz hzU => ?_) ?_
    · exact hzU (Set.mem_singleton_iff.mpr
        (eq_closedPoint_of_isClosed_singleton _ z hz))
    · exact hloc (D.points i) (singularPointsSituation_points_mem N hdimN hsing i)
  choose Z hZ hZproper hZreg using hlocal
  obtain ⟨A, hA, hAproper, hAlocal, ⟨eAU⟩⟩ :=
    D.exists_properNormalizedBlowUpSequence_of_local hcomponents Z hZ
  let : IsProper A.hom := hAproper
  let : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have hregU : IsRegular ((Over.pullback D.complement.ι).obj A).left := by
    let : IsLocallyNoetherian ((Over.pullback D.complement.ι).obj A).left :=
      isLocallyNoetherian_of_isOpenImmersion
        (Limits.pullback.fst A.hom D.complement.ι)
    exact isRegular_of_iso ((Over.forget _).mapIso eAU)
      (isRegular_complement_singularPointsSituation N hdimN hsing)
  have hregLocal : ∀ i, IsRegular
      ((Over.pullback (D.S.fromSpecStalk (D.points i))).obj A).left := by
    intro i
    let : IsProper ((Over.pullback (D.S.fromSpecStalk (D.points i))).obj A).hom := by
      change IsProper (Limits.pullback.snd A.hom (D.S.fromSpecStalk (D.points i)))
      infer_instance
    let : IsLocallyNoetherian ((Over.pullback (D.S.fromSpecStalk (D.points i))).obj A).left :=
      LocallyOfFiniteType.isLocallyNoetherian
        ((Over.pullback (D.S.fromSpecStalk (D.points i))).obj A).hom
    exact isRegular_of_iso ((Over.forget _).mapIso (hAlocal i).some) (hZreg i)
  have hregA : IsRegular A.left := D.isRegular_of_localizations A hregU hregLocal
  obtain ⟨X, f, hchain, ⟨eXA⟩⟩ :=
    exists_normalizedBlowUpChain_of_reflTransGen Y hY inferInstance D.complement hA
  let : IsProper (f ≫ ν) := hchain.isProper
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (f ≫ ν)
  exact ⟨hY, X, f ≫ ν, hchain, isRegular_of_iso ((Over.forget _).mapIso eXA) hregA⟩

end AlgebraicGeometry

end
