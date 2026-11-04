module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Blowup.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NormalMorphism.BaseFieldExtension
public import StacksFrontier.AlgebraicGeometry.Normalization.BaseChangeToCompletion
public import StacksFrontier.AlgebraicGeometry.Normalization.CompletionSpecialFibrePoints
public import StacksFrontier.AlgebraicGeometry.Normalization.NormalizedBlowUpSequence
public import StacksFrontier.AlgebraicGeometry.Normalization.PuncturedPreimageBlowUp
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.IntegralClosureBaseChange

/-!
# Descending a sequence of normalized blowups from the completion

Let `(A, m)` be a Noetherian local domain whose completion `A^` is normal. Every finite sequence
of normalized blowups `Yₙ → ⋯ → Y₁ → Spec A^` is the base change to `A^` of a sequence of
normalized blowups `Xₙ → ⋯ → X₁ → Spec A`, and the latter is proper over `Spec A`.

## Main definitions

* `AlgebraicGeometry.NormalizedBlowUpSeqDescent` is the predicate asserting that a sequence of
  normalized blowups over `Spec A` has a given sequence of normalized blowups over `Spec A^` as
  its base change, stage by stage.

## Main results

* `AlgebraicGeometry.exists_normalizedBlowUpSeqDescent_of_adicCompletion`: the descent
  statement, Tag 0BGA.
* `AlgebraicGeometry.NormalizedBlowUpSeqDescent.seq`,
  `AlgebraicGeometry.NormalizedBlowUpSeqDescent.seqCompletion` and
  `AlgebraicGeometry.NormalizedBlowUpSeqDescent.isPullback` read off from a descent the two
  sequences it compares and the cartesian square between their total spaces.

## Implementation notes

The comparison between the two sequences is recorded as a cartesian square
`IsPullback p g f i` with `i : Spec A^ ⟶ Spec A` the completion map, rather than as an
isomorphism onto `pullback f i`; this is the same information and it composes. One such square is
demanded at every stage, relative to the stage below, rather than one square for the top stages
only: that a tower upstairs is the base change of a tower downstairs is a statement about every
rung of the two towers and about the maps between the rungs, and the squares over `Spec A` are
recovered from the stagewise ones by pasting.

The induction is on the inductive predicate `NormalizedBlowUpSeq`, whose successor case supplies
the closed point `y` of the current stage `Y` that is blown up. Three things happen at each step.
First, `y` lies over the closed point of `Spec A^`, because the structure morphism of the stage is
proper; its image `x = p y` is then a closed point of the current stage `X` over `Spec A`, alone in
its fibre, and the reduced point at `y` is the inverse image of the reduced point at `x`
(`isClosed_singleton_and_comap_vanishingIdeal`, whose hypothesis on the fibres is supplied by
`isIso_fiberToSpecResidueField_of_isPullback_adicCompletion`). Second, blowing up commutes with the
flat base change `p`, so the blowup of `Y` at `y` is the base change of the blowup of `X` at `x`
(Tag 0805). Third, the complement of the special fibre upstairs is normal
(`isNormal_complementSpecialFiber_blowUpToBase_vanishingIdeal`), so Tag 0BG9 makes the
normalization of the blowup of `X` finite and identifies its base change with the normalization
of the blowup of `Y`; that is the next stage of both sequences.

Tag 0BG9 is stated for the canonical pullback `pullback F i`. It is restated here for an arbitrary
cartesian square, as `isPullback_normalization_of_isPullback_adicCompletion`, by transporting along
the canonical isomorphism: normalization is compared across the isomorphism with
`isPullback_normalizationSchemeMap_of_etale`, an isomorphism being étale.

Properness of the descended sequence is *not* obtained from `NormalizedBlowUpSeq.properties`,
which needs the base to be Nagata; `Spec A` is not known to be. It is carried through the
induction instead, each step being the composite of a blowup, which is proper, with a finite
normalization morphism, finiteness being the first half of Tag 0BG9.

## References

* [Stacks Project, Tag 0BGA](https://stacks.math.columbia.edu/tag/0BGA)
* [Stacks Project, Tag 0BG9](https://stacks.math.columbia.edu/tag/0BG9)
* [Stacks Project, Tag 0BBS](https://stacks.math.columbia.edu/tag/0BBS)
* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing
open AlgebraicGeometry.SemistableReduction

universe u

namespace AlgebraicGeometry

/-! ### Preliminaries -/

/-- The spectrum of the completion of a Noetherian local ring, mapping to the spectrum of the
ring itself. -/
public abbrev specMapAdicCompletion (A : Type u) [CommRing A] [IsLocalRing A] :
    Spec (.of (AdicCompletion (maximalIdeal A) A)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (AdicCompletion (maximalIdeal A) A)))


/-- The completion of a Noetherian local ring at its maximal ideal is faithfully flat over the
ring, the maximal ideal being contained in the Jacobson radical. -/
@[ega "IV 8.11.4" "partial", sga "1 IV 3.2" "special case"]
private instance faithfullyFlat_adicCompletion (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] : Module.FaithfullyFlat A (AdicCompletion (maximalIdeal A) A) :=
  AdicCompletion.faithfullyFlat_of_le_ringJacobson _
    (by rw [← Ideal.jacobson_bot]; exact IsLocalRing.maximalIdeal_le_jacobson ⊥)

/-- The morphism from the spectrum of the completion is flat. -/
private instance flat_specMapAdicCompletion (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] : Flat (specMapAdicCompletion A) :=
  Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)

/-- Normality of the complement of the special fibre only depends on the cartesian square: if the
complement of the special fibre of `s` is normal and `s` sits in a cartesian square over the
completion map, then the complement of the special fibre of the canonical projection is normal. -/
private theorem isNormal_complementSpecialFiber_pullback_snd
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {W V : Scheme.{u}} {F : W ⟶ Spec (.of A)}
    {r : V ⟶ W} {s : V ⟶ Spec (.of (AdicCompletion (maximalIdeal A) A))}
    (hsq : IsPullback r s F (specMapAdicCompletion A))
    (hnormal : IsNormal (complementSpecialFiber s)) :
    IsNormal (complementSpecialFiber (pullback.snd F (specMapAdicCompletion A))) := by
  let c := hsq.isoPullback
  let U : (pullback F (specMapAdicCompletion A)).Opens :=
    pullback.snd F (specMapAdicCompletion A) ⁻¹ᵁ
      Stacks.Divisors.puncturedSpectrum (AdicCompletion (maximalIdeal A) A)
  have hU : c.hom ⁻¹ᵁ U = s ⁻¹ᵁ
      Stacks.Divisors.puncturedSpectrum (AdicCompletion (maximalIdeal A) A) :=
    congrArg
      (fun m : V ⟶ Spec (.of (AdicCompletion (maximalIdeal A) A)) =>
        m ⁻¹ᵁ Stacks.Divisors.puncturedSpectrum (AdicCompletion (maximalIdeal A) A))
      hsq.isoPullback_hom_snd
  have hres : IsNormal (c.hom ⁻¹ᵁ U).toScheme := by
    rw [hU]
    exact hnormal
  exact isNormal_of_iso (asIso (c.hom ∣_ U)).symm

/-- **Tag 0BG9, restated for an arbitrary cartesian square.** Let `A` be a Noetherian local ring,
let `F : W ⟶ Spec A` be locally of finite type, and let `r : V ⟶ W`, `s : V ⟶ Spec A^` be a
cartesian square over the completion map. If the complement of the special fibre of `s` is normal,
then the normalization of `W` is finite and the normalization of `V` is the base change of the
normalization of `W` along `r`. -/
private theorem isPullback_normalization_of_isPullback_adicCompletion
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {W V : Scheme.{u}} (F : W ⟶ Spec (.of A)) [LocallyOfFiniteType F]
    {r : V ⟶ W} {s : V ⟶ Spec (.of (AdicCompletion (maximalIdeal A) A))}
    (hsq : IsPullback r s F (specMapAdicCompletion A))
    (hnormal : IsNormal (complementSpecialFiber s))
    (hW : ∀ U : W.Opens, IsCompact (U : Set W) → (irreducibleComponents U).Finite)
    (hV : ∀ U : V.Opens, IsCompact (U : Set V) → (irreducibleComponents U).Finite) :
    IsFinite (Scheme.normalization W hW) ∧
      ∃ t : Scheme.normalizationScheme V hV ⟶ Scheme.normalizationScheme W hW,
        IsPullback t (Scheme.normalization V hV) (Scheme.normalization W hW) r := by
  let i := specMapAdicCompletion A
  let : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian F
  have hq : IsNormal (complementSpecialFiber (pullback.snd F i)) :=
    isNormal_complementSpecialFiber_pullback_snd A hsq hnormal
  let P : Scheme.{u} := pullback F i
  let hP : ∀ U : P.Opens, IsCompact (U : Set P) → (irreducibleComponents U).Finite :=
    finite_irreducibleComponents_of_locallyNoetherian P
  let νW := Scheme.normalization W hW
  let p₀ : P ⟶ W := pullback.fst F i
  obtain ⟨e, he⟩ :=
    exists_iso_pullback_normalization_completion_of_isNormal_complementSpecialFiber A F hq
  have hsnd : e.inv ≫ pullback.snd νW p₀ = Scheme.normalization P hP := by
    rw [← he, Iso.inv_hom_id_assoc]
  have hcomm : CommSq (e.inv ≫ pullback.fst νW p₀) (Scheme.normalization P hP) νW p₀ :=
    ⟨by rw [Category.assoc, pullback.condition, ← Category.assoc, hsnd]⟩
  have hB : IsPullback (e.inv ≫ pullback.fst νW p₀) (Scheme.normalization P hP) νW p₀ :=
    IsPullback.of_iso_pullback hcomm e.symm rfl hsnd
  let c := hsq.isoPullback
  have hA : IsPullback (normalizationSchemeMap c.hom hV hP) (Scheme.normalization V hV)
      (Scheme.normalization P hP) c.hom :=
    isPullback_normalizationSchemeMap_of_etale c.hom hP
  have hpaste := hA.paste_horiz hB
  rw [hsq.isoPullback_hom_fst] at hpaste
  refine ⟨?_, ⟨_, hpaste⟩⟩
  exact isFinite_normalization_of_isNormal_complementSpecialFiber_completion A F hq

/-! ### Closed points over a local base -/

/-- A closed point of the spectrum of a local ring is its closed point. -/
private theorem eq_closedPoint_of_isClosed {B : Type u} [CommRing B] [IsLocalRing B]
    {q : Spec (.of B)} (hq : IsClosed ({q} : Set (Spec (.of B)))) : q = closedPoint B :=
  PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal
    ((PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mp hq))

/-- A proper morphism to the spectrum of a local ring sends a closed point to the closed point,
being a closed map. -/
private theorem apply_eq_closedPoint_of_isProper {B : Type u} [CommRing B] [IsLocalRing B]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of B)) [IsProper g] {y : Y}
    (hy : IsClosed ({y} : Set Y)) : g y = closedPoint B := by
  refine eq_closedPoint_of_isClosed ?_
  have h := g.isClosedMap _ hy
  rwa [Set.image_singleton] at h

/-- The completion map carries the closed point to the closed point. -/
private theorem specMapAdicCompletion_closedPoint (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] :
    specMapAdicCompletion A (closedPoint (AdicCompletion (maximalIdeal A) A)) = closedPoint A :=
  PrimeSpectrum.ext
    (IsLocalRing.maximalIdeal_comap (algebraMap A (AdicCompletion (maximalIdeal A) A)))

/-- Above the closure of the image of a closed point of the completed base change, the projection
has fibres which are spectra of residue fields: all those points lie over the closed point of the
base, where the completion does not change the residue field. -/
private theorem isIso_fiberToSpecResidueField_closure
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Spec (.of A)}
    {g : Y ⟶ Spec (.of (AdicCompletion (maximalIdeal A) A))} {p : Y ⟶ X}
    (hsq : IsPullback p g f (specMapAdicCompletion A)) (y : Y)
    (hgy : g y = closedPoint (AdicCompletion (maximalIdeal A) A)) :
    ∀ x' ∈ closure ({p y} : Set X), IsIso (p.fiberToSpecResidueField x') := by
  have hpy : f (p y) = closedPoint A := by
    have h := congrArg (fun m : Y ⟶ Spec (.of A) => m.base y) hsq.w
    simp only [Scheme.Hom.comp_apply] at h
    rw [h, hgy]
    exact specMapAdicCompletion_closedPoint A
  intro x' hx'
  refine isIso_fiberToSpecResidueField_of_isPullback_adicCompletion A hsq x' ?_
  have hsp : f.base (p y) ⤳ f.base x' :=
    (specializes_iff_mem_closure.mpr hx').map f.continuous
  rw [hpy] at hsp
  exact (PrimeSpectrum.asIdeal_le_asIdeal (closedPoint A) (f.base x')).mpr
    ((PrimeSpectrum.le_iff_specializes (closedPoint A) (f.base x')).mpr hsp)

/-! ### The inductive step -/

/-- Blowing up commutes with flat base change, in the form in which the inverse image ideal sheaf
has already been identified with another ideal sheaf. -/
private theorem exists_isPullback_blowUpToBase_of_comap_eq {X Y : Scheme.{u}} (p : Y ⟶ X)
    [Flat p] (I : X.IdealSheafData) (J : Y.IdealSheafData) (hJ : I.comap p = J) :
    ∃ h : blowUp J ⟶ blowUp I, IsPullback (blowUpToBase J) h p (blowUpToBase I) := by
  subst hJ
  exact AlgebraicGeometry.exists_isPullback_blowUpToBase_comap p I

/-- One step of the descent. Let `X` be proper over `Spec A` with completed base change `Y`, let
`y` be a closed point of `Y` over the closed point of `Spec A^`. Then the normalized blowup of `Y`
at `y` is the completed base change of the normalized blowup of `X` at the image of `y`, and the
latter is again proper over `Spec A`. -/
private theorem exists_normalizedBlowUp_isPullback_step
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Spec (.of A)} [IsProper f] [IsLocallyNoetherian X]
    {g : Y ⟶ Spec (.of (AdicCompletion (maximalIdeal A) A))} [IsNormal Y]
    {p : Y ⟶ X} (hsq : IsPullback p g f (specMapAdicCompletion A))
    (hXfin : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (hYfin : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite)
    (y : Y) (hy : IsClosed ({y} : Set Y))
    (hgy : g y = closedPoint (AdicCompletion (maximalIdeal A) A)) :
    ∃ (x : X) (hx : IsClosed ({x} : Set X))
      (t : Stacks.Blowup.normalizedBlowUpScheme Y hYfin y hy ⟶
            Stacks.Blowup.normalizedBlowUpScheme X hXfin x hx),
      IsProper (Stacks.Blowup.normalizedBlowUp X hXfin x hx ≫ f) ∧
        IsPullback t (Stacks.Blowup.normalizedBlowUp Y hYfin y hy)
          (Stacks.Blowup.normalizedBlowUp X hXfin x hx) p := by
  have : Flat p := MorphismProperty.of_isPullback hsq.flip inferInstance
  obtain ⟨hx, -, hcomap⟩ := isClosed_singleton_and_comap_vanishingIdeal p hy
    (isIso_fiberToSpecResidueField_closure A hsq y hgy)
  refine ⟨p y, hx, ?_⟩
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨{p y}, hx⟩ : Closeds X)
  let J := Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)
  obtain ⟨h, hsqB⟩ := exists_isPullback_blowUpToBase_of_comap_eq p I J hcomap
  have hsqC := hsqB.flip.paste_vert hsq
  obtain ⟨hfin, t, hsqD⟩ := isPullback_normalization_of_isPullback_adicCompletion A
    (blowUpToBase I ≫ f) hsqC
    (isNormal_complementSpecialFiber_blowUpToBase_vanishingIdeal g y hy hgy)
    (Stacks.Blowup.finite_irreducibleComponents_blowUp _ hXfin)
    (Stacks.Blowup.finite_irreducibleComponents_blowUp _ hYfin)
  refine ⟨t, ?_, hsqD.paste_vert hsqB.flip⟩
  let := hfin
  exact inferInstanceAs (IsProper ((Scheme.normalization (blowUp I)
    (Stacks.Blowup.finite_irreducibleComponents_blowUp _ hXfin) ≫ blowUpToBase I) ≫ f))

/-! ### The descent -/


/-- A sequence of normalized blowups over `Spec A` presented *together with* a sequence of
normalized blowups over `Spec A^` of which it is a model: `p` compares the two top stages, and
every stage of the upper tower is the base change along the comparison of the stage below it of
the corresponding stage of the lower tower.

The two towers and the comparison between them are the indices; the predicate carries no data
beyond the cartesian square at each step, which is what "the base change recovers the given
sequence" says. The underlying towers are recovered by `NormalizedBlowUpSeqDescent.seq` and
`NormalizedBlowUpSeqDescent.seqCompletion`, and the comparison of the total spaces over
`Spec A` by `NormalizedBlowUpSeqDescent.isPullback`. -/
public inductive NormalizedBlowUpSeqDescent (A : Type u) [CommRing A] [IsLocalRing A] :
    (X : Scheme.{u}) → (X ⟶ Spec (.of A)) → (Y : Scheme.{u}) →
      (Y ⟶ Spec (.of (AdicCompletion (maximalIdeal A) A))) → (Y ⟶ X) → Prop where
  | refl : NormalizedBlowUpSeqDescent A (Spec (.of A))
      (CategoryTheory.CategoryStruct.id (Spec (.of A)))
      (Spec (.of (AdicCompletion (maximalIdeal A) A)))
      (CategoryTheory.CategoryStruct.id (Spec (.of (AdicCompletion (maximalIdeal A) A))))
      (specMapAdicCompletion A)
  | blowUp {X : Scheme.{u}} {f : X ⟶ Spec (.of A)} {Y : Scheme.{u}}
      {g : Y ⟶ Spec (.of (AdicCompletion (maximalIdeal A) A))} {p : Y ⟶ X}
      (prev : NormalizedBlowUpSeqDescent A X f Y g p)
      (hXfin : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
      (hYfin : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite)
      (x : X) (hx : IsClosed ({x} : Set X)) (y : Y) (hy : IsClosed ({y} : Set Y))
      (t : Stacks.Blowup.normalizedBlowUpScheme Y hYfin y hy ⟶
            Stacks.Blowup.normalizedBlowUpScheme X hXfin x hx)
      (hcart : IsPullback t (Stacks.Blowup.normalizedBlowUp Y hYfin y hy)
        (Stacks.Blowup.normalizedBlowUp X hXfin x hx) p) :
      NormalizedBlowUpSeqDescent A
        (Stacks.Blowup.normalizedBlowUpScheme X hXfin x hx)
        (Stacks.Blowup.normalizedBlowUp X hXfin x hx ≫ f)
        (Stacks.Blowup.normalizedBlowUpScheme Y hYfin y hy)
        (Stacks.Blowup.normalizedBlowUp Y hYfin y hy ≫ g) t

/-- The sequence of normalized blowups over `Spec A` underlying a descent. -/
public theorem NormalizedBlowUpSeqDescent.seq {A : Type u} [CommRing A] [IsLocalRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Spec (.of A)}
    {g : Y ⟶ Spec (.of (AdicCompletion (maximalIdeal A) A))} {p : Y ⟶ X}
    (hdesc : NormalizedBlowUpSeqDescent A X f Y g p) :
    NormalizedBlowUpSeq (Spec (.of A)) X f := by
  induction hdesc with
  | refl => exact NormalizedBlowUpSeq.refl
  | blowUp prev hXfin hYfin x hx y hy t hcart ih => exact ih.blowUp hXfin x hx

/-- The sequence of normalized blowups over `Spec A^` that a descent descends. -/
public theorem NormalizedBlowUpSeqDescent.seqCompletion {A : Type u} [CommRing A] [IsLocalRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Spec (.of A)}
    {g : Y ⟶ Spec (.of (AdicCompletion (maximalIdeal A) A))} {p : Y ⟶ X}
    (hdesc : NormalizedBlowUpSeqDescent A X f Y g p) :
    NormalizedBlowUpSeq (Spec (.of (AdicCompletion (maximalIdeal A) A))) Y g := by
  induction hdesc with
  | refl => exact NormalizedBlowUpSeq.refl
  | blowUp prev hXfin hYfin x hx y hy t hcart ih => exact ih.blowUp hYfin y hy

/-- The top stage of the upper tower of a descent is the base change to `A^` of the top stage of
the lower tower: the stagewise cartesian squares compose. -/
public theorem NormalizedBlowUpSeqDescent.isPullback {A : Type u} [CommRing A] [IsLocalRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Spec (.of A)}
    {g : Y ⟶ Spec (.of (AdicCompletion (maximalIdeal A) A))} {p : Y ⟶ X}
    (hdesc : NormalizedBlowUpSeqDescent A X f Y g p) :
    IsPullback p g f (specMapAdicCompletion A) := by
  induction hdesc with
  | refl => exact IsPullback.of_id_snd
  | blowUp prev hXfin hYfin x hx y hy t hcart ih => exact hcart.paste_vert ih

/-- **Stacks Project, Tag 0BGA.** Let `A` be a Noetherian local domain whose completion `A^` is
normal. Every finite sequence of normalized blowups `Yₙ → ⋯ → Y₁ → Spec A^` is the base change
to `A^` of a finite sequence of normalized blowups `Xₙ → ⋯ → X₁ → Spec A`, stage by stage, and
the latter sequence is proper over `Spec A`.

The hypothesis that `A^` is a Nagata ring is Tag 0335 for a Noetherian complete local ring; it is
carried explicitly because that case of Tag 0335 is not available here. It is what makes every
stage of the given sequence normal and proper over `Spec A^`, hence makes the centre of each
normalized blowup lie over the closed point. -/
@[stacks 0BGA "the whole statement, under the additional hypothesis that the completion is a \
Nagata ring; that is Tag 0335 item (2) for a Noetherian complete local ring, which is not \
available here"]
public theorem exists_normalizedBlowUpSeqDescent_of_adicCompletion
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    (hnormal : IsNormalRing (AdicCompletion (maximalIdeal A) A))
    (hnagata : IsNagataRing (AdicCompletion (maximalIdeal A) A))
    {Y : Scheme.{u}} {g : Y ⟶ Spec (.of (AdicCompletion (maximalIdeal A) A))}
    (hseq : NormalizedBlowUpSeq (Spec (.of (AdicCompletion (maximalIdeal A) A))) Y g) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (p : Y ⟶ X),
      NormalizedBlowUpSeqDescent A X f Y g p ∧ IsProper f := by
  have hnagataScheme : IsNagataScheme (Spec (.of (AdicCompletion (maximalIdeal A) A))) :=
    isNagataScheme_spec_of_isNagataRing _ hnagata
  let : IsNormal (Spec (.of (AdicCompletion (maximalIdeal A) A))) :=
    isNormal_spec_of_isNormalRing hnormal
  let : IsLocallyNoetherian (Spec (.of (AdicCompletion (maximalIdeal A) A))) :=
    ((isNagataScheme_iff_isLocallyNoetherian_and_isUniversallyJapaneseScheme _).mp
      hnagataScheme).1
  induction hseq with
  | refl =>
    exact ⟨Spec (.of A), CategoryStruct.id _, specMapAdicCompletion A,
      NormalizedBlowUpSeqDescent.refl, inferInstance⟩
  | @blowUp Z h prev hZfin z hz ih =>
    obtain ⟨X, f, p, hdesc, hfproper⟩ := ih
    let := hfproper
    obtain ⟨-, -, hZnormal, hhproper⟩ := prev.properties hnagataScheme
    let := hZnormal
    let := hhproper
    let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    obtain ⟨x, hx, t, hproper, hsqstep⟩ :=
      exists_normalizedBlowUp_isPullback_step A hdesc.isPullback
        (finite_irreducibleComponents_of_locallyNoetherian X) hZfin z hz
        (apply_eq_closedPoint_of_isProper h hz)
    exact ⟨_, _, t, hdesc.blowUp _ hZfin x hx z hz t hsqstep, hproper⟩

end AlgebraicGeometry

end
