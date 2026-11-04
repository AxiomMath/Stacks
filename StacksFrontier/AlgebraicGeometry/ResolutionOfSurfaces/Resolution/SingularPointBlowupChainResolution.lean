module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.SingularPointBlowupChain
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.ExistenceByNormalizedBlowUps
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.LipmanEquivalence
public import StacksFrontier.AlgebraicGeometry.Blowup.NormalizedBlowUpNagataExtra

/-!
# Blowups at singular points with normal stages are normalized blowups

A finite sequence of blowups at closed points all of whose stages are normal is a sequence of
normalized blowups: the normalized blowup of a scheme at a closed point is the normalization of
the blowup, and the blowup is already normal. So such a sequence ending in a regular scheme is a
resolution of singularities by normalized blowups in the sense of [Stacks, Tag 0BGL], and its
composite morphism is a modification.

The sequences produced by [Stacks, Tag 0BBV] and [Stacks, Tag 0BGE] are of this kind: blowups at
singular closed points, every stage normal. This is how the proof of [Stacks, Tag 0BGM] reads
their outputs as resolutions by normalized blowups.

## Main results

* `AlgebraicGeometry.SingularPointBlowupChain.mono`: a chain for a property is a chain for any
  weaker property.
* `AlgebraicGeometry.exists_normalizedBlowUpSeq_of_singularPointBlowupChain`: a chain of blowups
  at singular closed points with normal stages is, up to an isomorphism of the total space, a
  sequence of normalized blowups.
* `AlgebraicGeometry.hasResolutionByNormalizedBlowUps_of_singularPointBlowupChain`: over a normal
  Nagata base such a chain ending in a regular scheme is a resolution by normalized blowups.
* `AlgebraicGeometry.isModification_of_singularPointBlowupChain`: over a normal Nagata integral
  base of dimension two the composite morphism of such a chain is a modification.

## References

* [Stacks Project, Tag 0BGL](https://stacks.math.columbia.edu/tag/0BGL)
* [Stacks Project, Tag 0BGM](https://stacks.math.columbia.edu/tag/0BGM)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A Nagata scheme is locally Noetherian. -/
private theorem isLocallyNoetherian_of_isNagataScheme {Y : Scheme.{u}} (h : IsNagataScheme Y) :
    IsLocallyNoetherian Y :=
  ((isNagataScheme_iff_isLocallyNoetherian_and_isUniversallyJapaneseScheme Y).mp h).1

/-- A chain of blowups at singular closed points whose stages satisfy `P` is a chain for any
property implied by `P`. -/
theorem SingularPointBlowupChain.mono {P Q : Scheme.{u} → Prop} (hPQ : ∀ W, P W → Q W)
    {X Y : Scheme.{u}} {f : Y ⟶ X} (h : SingularPointBlowupChain P X Y f) :
    SingularPointBlowupChain Q X Y f := by
  induction h with
  | refl hX => exact .refl (hPQ _ hX)
  | step _ w hw hsing hP ih => exact ih.step w hw hsing (hPQ _ hP)

/-- **A chain of blowups at singular closed points with normal stages is a sequence of
normalized blowups**, up to an isomorphism of the total space over the base, and its stages are
locally Noetherian when the base is. -/
theorem exists_normalizedBlowUpSeq_of_singularPointBlowupChain {P : Scheme.{u} → Prop}
    (hP : ∀ W, P W → IsNormal W) {Y : Scheme.{u}} [IsLocallyNoetherian Y] {Z : Scheme.{u}}
    {f : Z ⟶ Y} (h : SingularPointBlowupChain P Y Z f) :
    IsLocallyNoetherian Z ∧ ∃ (X : Scheme.{u}) (g : X ⟶ Y) (e : Z ≅ X),
      NormalizedBlowUpSeq Y X g ∧ e.hom ≫ g = f := by
  induction h with
  | refl _ => exact ⟨inferInstance, Y, 𝟙 Y, Iso.refl Y, .refl, by simp⟩
  | @step W h hh w hw hsing hPb ih =>
    obtain ⟨hWln, X', g', e, hseq, he⟩ := ih
    have := hWln
    set M := Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)
    have : IsLocallyNoetherian (blowUp M) := LocallyOfFiniteType.isLocallyNoetherian
      (blowUpToBase M)
    have : IsLocallyNoetherian X' := isLocallyNoetherian_of_isOpenImmersion e.inv
    have : IsNormal (blowUp M) := hP _ hPb
    have hW := SemistableReduction.finite_irreducibleComponents_of_locallyNoetherian W
    have hX' := SemistableReduction.finite_irreducibleComponents_of_locallyNoetherian X'
    have hz' : IsClosed ({e.hom w} : Set X') := by
      have hset : ({e.hom w} : Set X') = e.inv ⁻¹' ({w} : Set W) := by
        ext y
        simp only [Set.mem_singleton_iff, Set.mem_preimage]
        refine ⟨fun hy => by rw [hy]; simp, fun hy => ?_⟩
        rw [← hy]
        simp
      rw [hset]
      exact hw.preimage e.inv.continuous
    obtain ⟨m, hm⟩ := exists_normalizedBlowUpScheme_iso_of_iso e hW hX' w hw hz'
    refine ⟨inferInstance, _, _, (Stacks.Blowup.normalizedBlowUpSchemeIsoBlowUp hW w hw).symm ≪≫ m,
      hseq.blowUp hX' (e.hom w) hz', ?_⟩
    have hm' : m.hom ≫ Stacks.Blowup.normalizedBlowUp X' hX' (e.hom w) hz' ≫ g' =
        Stacks.Blowup.normalizedBlowUp W hW w hw ≫ e.hom ≫ g' := by
      rw [← Category.assoc, hm, Category.assoc]
    rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, hm', he, Iso.inv_comp_eq,
      ← Category.assoc, Stacks.Blowup.normalizedBlowUpSchemeIsoBlowUp_hom_blowUpToBase]

/-- **A chain of blowups at singular closed points with normal stages, ending in a regular
scheme, is a resolution by normalized blowups** of a normal Nagata base. -/
theorem hasResolutionByNormalizedBlowUps_of_singularPointBlowupChain {P : Scheme.{u} → Prop}
    (hP : ∀ W, P W → IsNormal W) {Y : Scheme.{u}} [IsNormal Y] (hNagata : IsNagataScheme Y)
    {Z : Scheme.{u}} {f : Z ⟶ Y} (h : SingularPointBlowupChain P Y Z f) (hreg : IsRegular Z) :
    HasResolutionByNormalizedBlowUps Y := by
  have := isLocallyNoetherian_of_isNagataScheme hNagata
  obtain ⟨hZln, X, g, e, hseq, -⟩ := exists_normalizedBlowUpSeq_of_singularPointBlowupChain hP h
  have := hZln
  have : IsLocallyNoetherian X := isLocallyNoetherian_of_isOpenImmersion e.inv
  exact hasResolutionByNormalizedBlowUps_of_normalizedBlowUpSeq hNagata hseq
    (isRegular_of_iso e.symm hreg)

/-- **The composite morphism of a chain of blowups at singular closed points with normal stages
is a modification**, over a normal Nagata integral base of dimension two. -/
theorem isModification_of_singularPointBlowupChain {P : Scheme.{u} → Prop}
    (hP : ∀ W, P W → IsNormal W) {Y : Scheme.{u}} [IsNormal Y] [IsIntegral Y]
    (hNagata : IsNagataScheme Y) (hdim : topologicalKrullDim Y = 2) {Z : Scheme.{u}}
    {f : Z ⟶ Y} (h : SingularPointBlowupChain P Y Z f) : IsModification f := by
  have := isLocallyNoetherian_of_isNagataScheme hNagata
  have hY := SemistableReduction.finite_irreducibleComponents_of_locallyNoetherian Y
  obtain ⟨-, X, g, e, hseq, he⟩ := exists_normalizedBlowUpSeq_of_singularPointBlowupChain hP h
  obtain ⟨W, k, e', hchain, he'⟩ :=
    exists_normalizedBlowUpChain_of_normalizedBlowUpSeq hNagata hY hseq
  have hk := isModification_of_normalizedBlowUpChain hdim hchain
  have hf : f = (e ≪≫ e').hom ≫ k := by rw [Iso.trans_hom, Category.assoc, he', he]
  rw [hf]
  have : IsProper k := hk.isProper
  have : IsIntegral W := hk.source_isIntegral
  exact ⟨(isBirational_of_iso (e ≪≫ e')).comp hk.isBirational, inferInstance,
    IsIntegral.of_isIso (e ≪≫ e').inv⟩

end AlgebraicGeometry

end
