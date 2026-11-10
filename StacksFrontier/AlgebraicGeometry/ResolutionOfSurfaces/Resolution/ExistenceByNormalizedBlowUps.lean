module

public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.RegularBaseChange
public import StacksFrontier.AlgebraicGeometry.Normalization.NormalizedBlowUpDescent
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedBlowUpReduction

/-!
# Resolutions by normalized blowups from sequences of normalized blowups

A chain of [Stacks, Tag 0BGL] begins with the normalization of its base, whereas a sequence
`AlgebraicGeometry.NormalizedBlowUpSeq` begins with the base itself. Over a normal base the two
agree up to an isomorphism of the total space, so a sequence of normalized blowups ending in a
regular scheme exhibits a resolution by normalized blowups.

Combined with the descent of such sequences from the completion, [Stacks, Tag 0BGA], and with
the comparison of regularity across that completion, [Stacks, Tag 0BG6], this reduces the
existence of a resolution by normalized blowups of the spectrum of a Noetherian local ring to
the same statement for the spectrum of its completion. That reduction is the first paragraph of
the proof of [Stacks, Tag 0BGM].

## Main results

* `AlgebraicGeometry.exists_normalizedBlowUpScheme_iso_of_iso`: the normalized blowing up at a
  closed point transports along an isomorphism of the blown-up scheme.
* `AlgebraicGeometry.exists_normalizedBlowUpChain_of_normalizedBlowUpSeq`: over a normal Nagata
  base, a sequence of normalized blowups is a chain of Tag 0BGL up to an isomorphism of the total
  space over the base.
* `AlgebraicGeometry.hasResolutionByNormalizedBlowUps_of_normalizedBlowUpSeq`: a sequence of
  normalized blowups ending in a regular scheme is a resolution by normalized blowups.

## Implementation notes

The chain of Tag 0BGL names the schemes it passes through, being indexed by the canonical
constructions `AlgebraicGeometry.Scheme.normalizationScheme` and
`Stacks.Blowup.normalizedBlowUpScheme`, so transporting a sequence into a chain produces a total
space isomorphic to, and not equal to, the one the sequence ends at. The isomorphism is built
step by step out of the one between the normalized blowing ups of two isomorphic schemes, which
in turn comes from the corresponding isomorphism of blowups and of normalizations.

Properness of each stage over the base, which the chain of Tag 0BGL requires, is what makes the
Nagata hypothesis necessary: it is the finiteness of the normalizations occurring in the
normalized blowing ups.

## References

* [Stacks Project, Tag 0BGL](https://stacks.math.columbia.edu/tag/0BGL)
* [Stacks Project, Tag 0BGA](https://stacks.math.columbia.edu/tag/0BGA)
* [Stacks Project, Tag 0BG6](https://stacks.math.columbia.edu/tag/0BG6)
* [Stacks Project, Tag 0BGM](https://stacks.math.columbia.edu/tag/0BGM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing
open AlgebraicGeometry.SemistableReduction

universe u

namespace AlgebraicGeometry

/-! ### Transporting a normalized blowing up along an isomorphism -/

/-- The normalized blowing up at a closed point transports along an isomorphism of the scheme
being blown up: the reduced closed subscheme at the point pulls back to the one at its image,
the blowups of the two are therefore isomorphic over the isomorphism, and so are their
normalizations. -/
theorem exists_normalizedBlowUpScheme_iso_of_iso {Z W : Scheme.{u}} (e : Z ≅ W)
    (hZ : ∀ U : Z.Opens, IsCompact (U : Set Z) → (irreducibleComponents U).Finite)
    (hW : ∀ U : W.Opens, IsCompact (U : Set W) → (irreducibleComponents U).Finite)
    (z : Z) (hz : IsClosed ({z} : Set Z)) (hz' : IsClosed ({e.hom z} : Set W)) :
    ∃ m : Stacks.Blowup.normalizedBlowUpScheme Z hZ z hz ≅
        Stacks.Blowup.normalizedBlowUpScheme W hW (e.hom z) hz',
      m.hom ≫ Stacks.Blowup.normalizedBlowUp W hW (e.hom z) hz' =
        Stacks.Blowup.normalizedBlowUp Z hZ z hz ≫ e.hom := by
  set J : W.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal (⟨{e.hom z}, hz'⟩ : Closeds W) with hJ
  obtain ⟨_, hideal⟩ :=
    AlgebraicGeometry.vanishingIdeal_singleton_comap_of_isIso e.hom (e.hom z) hz' z rfl
  have key : ∀ K : Z.IdealSheafData, K = J.comap e.hom →
      ∃ d : blowUp K ≅ blowUp J, d.hom ≫ blowUpToBase J = blowUpToBase K ≫ e.hom := by
    intro K hK
    cases hK
    exact AlgebraicGeometry.exists_blowUp_iso_comap_of_isIso e.hom J
  obtain ⟨d, hd⟩ := key (Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds Z))
    hideal.symm
  obtain ⟨m, hm⟩ := AlgebraicGeometry.exists_normalizationScheme_iso_of_iso d
    (Stacks.Blowup.finite_irreducibleComponents_blowUp _ hZ)
    (Stacks.Blowup.finite_irreducibleComponents_blowUp _ hW)
  refine ⟨m, ?_⟩
  change m.hom ≫ Scheme.normalization (blowUp J)
      (Stacks.Blowup.finite_irreducibleComponents_blowUp J hW) ≫ blowUpToBase J =
    (Scheme.normalization (blowUp (Scheme.IdealSheafData.vanishingIdeal
          (⟨{z}, hz⟩ : Closeds Z)))
        (Stacks.Blowup.finite_irreducibleComponents_blowUp _ hZ) ≫
      blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds Z))) ≫ e.hom
  rw [← Category.assoc, hm, Category.assoc, hd, Category.assoc]

/-- The image of a closed point under an isomorphism is a closed point. -/
private theorem isClosed_singleton_image_of_iso {Z W : Scheme.{u}} (e : Z ≅ W) (z : Z)
    (hz : IsClosed ({z} : Set Z)) : IsClosed ({e.hom z} : Set W) := by
  have hset : ({e.hom z} : Set W) = e.inv ⁻¹' ({z} : Set Z) := by
    ext y
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    refine ⟨fun hy => by subst hy; simp, fun hy => ?_⟩
    rw [← show e.hom (e.inv y) = y from by simp, hy]
  rw [hset]
  exact hz.preimage e.inv.continuous

/-! ### Sequences of normalized blowups as chains -/

/-- A Nagata scheme is locally Noetherian. -/
private theorem isLocallyNoetherian_of_isNagataScheme {Y : Scheme.{u}} (hY : IsNagataScheme Y) :
    IsLocallyNoetherian Y :=
  ((isNagataScheme_iff_isLocallyNoetherian_and_isUniversallyJapaneseScheme Y).mp hY).1

/-- If `f` is proper and `e.hom ≫ g = f` for an isomorphism `e`, then `g` is proper. -/
private theorem isProper_of_iso_hom_comp_eq {X W Y : Scheme.{u}} {f : X ⟶ Y} {g : W ⟶ Y}
    (e : X ≅ W) (he : e.hom ≫ g = f) (hf : IsProper f) : IsProper g := by
  have hg : e.inv ≫ f = g := by rw [← he, Iso.inv_hom_id_assoc]
  have := hf
  exact hg ▸ (inferInstance : IsProper (e.inv ≫ f))

/-- Over a normal Nagata base, a finite sequence of normalized blowups at closed points is a
chain of normalized blowups in the sense of [Stacks, Tag 0BGL], up to an isomorphism of the
total space commuting with the morphisms to the base: the normalization with which such a chain
begins is an isomorphism over a normal base. -/
theorem exists_normalizedBlowUpChain_of_normalizedBlowUpSeq {Y : Scheme.{u}} [IsNormal Y]
    (hNagata : IsNagataScheme Y)
    (hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite)
    {X : Scheme.{u}} {f : X ⟶ Y} (hseq : NormalizedBlowUpSeq Y X f) :
    ∃ (W : Scheme.{u}) (g : W ⟶ Y) (e : X ≅ W),
      NormalizedBlowUpChain Y hY W g ∧ e.hom ≫ g = f := by
  have := isLocallyNoetherian_of_isNagataScheme hNagata
  have hνfinite : IsFinite (Scheme.normalization Y hY) := Scheme.isFinite_normalization hNagata hY
  induction hseq with
  | refl =>
    have hiso : IsIso (Scheme.normalization Y hY) :=
      (Scheme.isIso_normalization_iff_isNormal Y hY).2 inferInstance
    exact ⟨_, _, (asIso (Scheme.normalization Y hY)).symm,
      NormalizedBlowUpChain.normalization inferInstance, by simp⟩
  | @blowUp X f prev hX x hx ih =>
    obtain ⟨W, g, e, hchain, he⟩ := ih
    obtain ⟨hXnagata, -, -, hfproper⟩ := prev.properties hNagata
    have hW : ∀ U : W.Opens, IsCompact (U : Set W) → (irreducibleComponents U).Finite :=
      finite_irreducibleComponents_of_smooth e.inv hX
    have hz' : IsClosed ({e.hom x} : Set W) := isClosed_singleton_image_of_iso e x hx
    have hWnagata : IsNagataScheme W := isNagataScheme_of_locallyOfFiniteType e.inv hXnagata
    have := isProper_of_iso_hom_comp_eq e he hfproper
    have := Stacks.Blowup.isProper_normalizedBlowUp hW (e.hom x) hz' hWnagata
    have hcomp : IsProper (Stacks.Blowup.normalizedBlowUp W hW (e.hom x) hz' ≫ g) :=
      inferInstance
    obtain ⟨m, hm⟩ := exists_normalizedBlowUpScheme_iso_of_iso e hX hW x hx hz'
    refine ⟨_, _, m, hchain.blowUp hW (e.hom x) hz' hcomp, ?_⟩
    rw [← Category.assoc, hm, Category.assoc, he]

/-- Over a normal Nagata base, a finite sequence of normalized blowups at closed points ending in
a regular scheme is a resolution of singularities by normalized blowups in the sense of
[Stacks, Tag 0BGL]. -/
theorem hasResolutionByNormalizedBlowUps_of_normalizedBlowUpSeq {Y : Scheme.{u}} [IsNormal Y]
    (hNagata : IsNagataScheme Y) {X : Scheme.{u}} {f : X ⟶ Y}
    (hseq : NormalizedBlowUpSeq Y X f) (hreg : IsRegular X) :
    HasResolutionByNormalizedBlowUps Y := by
  have := isLocallyNoetherian_of_isNagataScheme hNagata
  have hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite :=
    finite_irreducibleComponents_of_locallyNoetherian Y
  obtain ⟨W, g, e, hchain, he⟩ :=
    exists_normalizedBlowUpChain_of_normalizedBlowUpSeq hNagata hY hseq
  obtain ⟨-, -, -, hfproper⟩ := hseq.properties hNagata
  have := isProper_of_iso_hom_comp_eq e he hfproper
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian g
  exact ⟨hY, W, g, hchain, isRegular_of_iso e.symm hreg⟩

end AlgebraicGeometry

end
