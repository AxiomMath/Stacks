module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.LipmanEquivalencePort
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.ResolutionByNormalizedBlowUps

/-!
# Composing two chains of normalized blowups

A chain of normalized blowups over `Y` reaching a stage `X`, followed by a chain of normalized
blowups over `X`, is again a chain of normalized blowups over `Y`. This file proves that, and
deduces that a scheme has a resolution of singularities by normalized blowups as soon as some
stage of a chain of normalized blowups over it has one.

## Main results

* `AlgebraicGeometry.NormalizedBlowUpChain.isNormal`: every stage of a chain of normalized
  blowups is a normal scheme.
* `AlgebraicGeometry.exists_normalizedBlowUpChain_comp`: the composite of two chains is a chain.
* `AlgebraicGeometry.hasResolutionByNormalizedBlowUps_of_chain`: a resolution by normalized
  blowups of a stage of a chain over `Y` gives one of `Y`.

## Implementation notes

`AlgebraicGeometry.NormalizedBlowUpChain` is an inductive family indexed by the *canonical*
schemes `AlgebraicGeometry.Scheme.normalizationScheme` and
`Stacks.Blowup.normalizedBlowUpScheme`, so it is not closed under isomorphism of the total space
and the composite cannot be asserted on the nose. The conclusion is therefore existential, in the
same shape as `AlgebraicGeometry.exists_normalizedBlowUpChain_of_normalizedBlowUpSeqDescent`:
there is a chain over `Y` whose total space is isomorphic to the given one over `Y`.

Two facts drive the induction. First, the base case of the second chain is the normalization of
`X` rather than `X` itself; it is an isomorphism because a stage of a chain is normal, which is
`AlgebraicGeometry.NormalizedBlowUpChain.isNormal` — the first stage is a normalization and every
later one is a normalized blowup, and both constructions are normal by
[Stacks, Tag 0BFT]. Second, each later step blows up a closed point of a stage that the induction
hypothesis only knows up to an isomorphism `e`, so the step must be transported along `e`: the
centre moves to its image, the reduced point at a point pulls back to the reduced point at its
image along an isomorphism, and
`AlgebraicGeometry.exists_isPullback_normalizedBlowUp_comap` then presents the normalized blowup
at the moved centre as a base change of the given one, an isomorphism being flat and a
preimmersion. Properness over `Y` of the transported step follows from properness over `X` of the
given one together with properness of `X` over `Y`, which is
`AlgebraicGeometry.NormalizedBlowUpChain.isProper`.

## References

* [Stacks Project, Tag 0BGL](https://stacks.math.columbia.edu/tag/0BGL)
* [Stacks Project, Tag 0BFT](https://stacks.math.columbia.edu/tag/0BFT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Every stage of a chain of normalized blowups is a normal scheme: the first stage is the
normalization of the base and every later one is a normalized blowup, which is by construction
the normalization of a blowup. -/
theorem NormalizedBlowUpChain.isNormal {Y : Scheme.{u}}
    {hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite}
    {X : Scheme.{u}} {f : X ⟶ Y} (h : NormalizedBlowUpChain Y hY X f) : IsNormal X := by
  induction h with
  | normalization _ => exact Scheme.isNormal_normalizationScheme Y hY
  | blowUp _ hW w hw _ _ => exact Stacks.Blowup.isNormal_normalizedBlowUpScheme hW w hw

/-- **A chain of normalized blowups over a stage of a chain of normalized blowups is a chain of
normalized blowups over the base.** Given a chain over `Y` reaching `X ⟶ Y` and a chain over `X`
reaching `W ⟶ X`, there is a chain over `Y` whose total space is isomorphic to `W` compatibly
with the composite morphism to `Y`.

The induction is over the second chain. Its base case is the normalization of `X`, which is an
isomorphism because a stage of a chain is normal. Each later step blows up a closed point of a
stage known only up to an isomorphism, so it is transported along that isomorphism as a base
change. -/
theorem exists_normalizedBlowUpChain_comp {Y : Scheme.{u}}
    {hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite}
    {X : Scheme.{u}} {f : X ⟶ Y} (hf : NormalizedBlowUpChain Y hY X f)
    {hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite}
    {W : Scheme.{u}} {q : W ⟶ X} (hq : NormalizedBlowUpChain X hX W q) :
    ∃ (V : Scheme.{u}) (p : V ⟶ Y), NormalizedBlowUpChain Y hY V p ∧
      ∃ e : W ≅ V, e.hom ≫ p = q ≫ f := by
  induction hq with
  | normalization _ =>
    have : IsNormal X := hf.isNormal
    have : IsIso (Scheme.normalization X hX) :=
      (Scheme.isIso_normalization_iff_isNormal X hX).2 inferInstance
    exact ⟨X, f, hf, asIso (Scheme.normalization X hX), by simp⟩
  | @blowUp W q prev hW w hw hproper ih =>
    obtain ⟨V, p, hchain, e, he⟩ := ih
    have hVfin : ∀ U : V.Opens, IsCompact (U : Set V) → (irreducibleComponents U).Finite :=
      finite_irreducibleComponents_of_smooth e.inv hW
    have hv : IsClosed ({e.hom w} : Set V) := by
      have hset : ({e.hom w} : Set V) = e.inv ⁻¹' ({w} : Set W) := by
        ext z
        simp only [Set.mem_singleton_iff, Set.mem_preimage]
        refine ⟨fun hzw => by subst hzw; simp, fun hzw => ?_⟩
        rw [← show e.hom (e.inv z) = z from by simp, hzw]
      rw [hset]
      exact hw.preimage e.inv.continuous
    obtain ⟨_, hideal⟩ := vanishingIdeal_singleton_comap_of_isIso e.hom (e.hom w) hv w rfl
    obtain ⟨m, hm⟩ :=
      exists_isPullback_normalizedBlowUp_comap e.hom hVfin hW (e.hom w) hv w hw hideal
    have : IsIso m :=
      (MorphismProperty.IsStableUnderBaseChange.isomorphisms Scheme).of_isPullback hm.flip
        (show MorphismProperty.isomorphisms Scheme e.hom from inferInstance)
    have hmw : m ≫ (Stacks.Blowup.normalizedBlowUp V hVfin (e.hom w) hv ≫ p) =
        Stacks.Blowup.normalizedBlowUp W hW w hw ≫ q ≫ f := by
      rw [← Category.assoc, hm.w, Category.assoc, he]
    have hproperY : IsProper (Stacks.Blowup.normalizedBlowUp W hW w hw ≫ q ≫ f) := by
      let : IsProper (Stacks.Blowup.normalizedBlowUp W hW w hw ≫ q) := hproper
      let : IsProper f := hf.isProper
      rw [← Category.assoc]
      infer_instance
    exact ⟨_, _, hchain.blowUp hVfin (e.hom w) hv
      ((MorphismProperty.cancel_left_of_respectsIso (P := @IsProper) m _).mp (hmw ▸ hproperY)),
      asIso m, hmw⟩

/-- **A scheme has a resolution of singularities by normalized blowups as soon as some stage of a
chain of normalized blowups over it has one.** The chain over the stage is appended to the chain
reaching it, and regularity is transported along the comparison isomorphism. -/
theorem hasResolutionByNormalizedBlowUps_of_chain {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    {hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite}
    {X : Scheme.{u}} {f : X ⟶ Y} (hf : NormalizedBlowUpChain Y hY X f)
    (hres : HasResolutionByNormalizedBlowUps X) :
    HasResolutionByNormalizedBlowUps Y := by
  obtain ⟨hXfin, W, q, hq, hreg⟩ := hres
  obtain ⟨V, p, hchain, e, -⟩ := exists_normalizedBlowUpChain_comp hf hq
  refine ⟨hY, V, p, hchain, ?_⟩
  let : IsProper p := hchain.isProper
  let : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian p
  exact isRegular_of_iso e.symm hreg

end AlgebraicGeometry

end
