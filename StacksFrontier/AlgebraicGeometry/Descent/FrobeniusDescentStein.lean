module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitThickeningInvariance
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusDescentTransfer
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.Noetherian

/-!
# The Stein factorization step of the essential-image half of Stacks Tag 0EXH

Let `f : X ⟶ Y` be proper with geometrically connected fibres onto a locally Noetherian scheme,
with Stein factorization `X --f'--> S --π--> Y` (Stacks Tag 03H0). The proof of Stacks Tag 0EXH
observes that `π` is a universal homeomorphism and replaces `Y` by `S`.

Universal injectivity of `π` is proved on points with values in fields: two such points of `S`
over the same `K`-point `c` of `Y` are two sections of the finite `K`-scheme `S_K = S ×_Y Spec K`,
which is a single point, being discrete (finite over a field) and connected (the image of the
connected `X_K`); and two sections of a one-point scheme over `Spec K` agree, because both become
isomorphisms onto its reduction.

The replacement itself goes through the graph `Γ : X ⟶ X ×_Y S` of `f'`. It is a closed immersion
(`π` is separated) and surjective (the projection `X ×_Y S ⟶ X` is injective, `π` being universally
injective), so pullback along it is fully faithful on `colim_F Vect` (Stacks Tag 0EXH, part (1)).
Hence a descent of `ℰ` along `f'` gives a descent of the pullback of `ℰ` to `X ×_Y S` along the
projection to `S`, which is what the h-descent of Stacks Tag 0EXE takes as input.

## Main results

* `AlgebraicGeometry.universallyInjective_fromNormalization`.
* `AlgebraicGeometry.descendsAfterFrobenius_pullback_fromNormalization`.

## References

* [Stacks Project, Tag 0EXH](https://stacks.math.columbia.edu/tag/0EXH)
* [Stacks Project, Tag 03H0](https://stacks.math.columbia.edu/tag/03H0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Frobenius

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- **Two sections of a one-point scheme over the spectrum of a field agree.** -/
theorem eq_of_comp_eq_id_of_subsingleton {K : Type u} [Field K] {Z : Scheme.{u}}
    [Subsingleton Z] (q : Z ⟶ Spec (.of K)) (σ₁ σ₂ : Spec (.of K) ⟶ Z) (h₁ : σ₁ ≫ q = 𝟙 _)
    (h₂ : σ₂ ≫ q = 𝟙 _) : σ₁ = σ₂ := by
  have : Subsingleton Z.reduction := Z.reductionι.isEmbedding.injective.subsingleton
  let q' : Z.nilradical.subscheme ⟶ Spec (.of K) := Z.nilradical.subschemeι ≫ q
  have hsub : Subsingleton Z.nilradical.subscheme := ‹Subsingleton Z.reduction›
  have key : ∀ σ : Spec (.of K) ⟶ Z, σ ≫ q = 𝟙 _ →
      ∃ τ : Spec (.of K) ⟶ Z.nilradical.subscheme,
        τ ≫ Z.nilradical.subschemeι = σ ∧ τ ≫ q' = 𝟙 _ ∧ IsIso τ := by
    intro σ hσ
    obtain ⟨τ, hτ, -⟩ := Scheme.existsUnique_lift_nilradical_subschemeι σ
    have hq : τ ≫ q' = 𝟙 _ := by simp only [q', ← Category.assoc, hτ, hσ]
    have : IsClosedImmersion τ := isClosedImmersion_of_comp_eq_id q' τ hq
    have : Surjective τ := ⟨fun z ↦ ⟨IsLocalRing.closedPoint _, Subsingleton.elim _ _⟩⟩
    have : IsReduced Z.nilradical.subscheme := inferInstanceAs (IsReduced Z.reduction)
    exact ⟨τ, hτ, hq, isIso_of_isClosedImmersion_of_surjective τ⟩
  obtain ⟨τ₁, hτ₁, hq₁, _⟩ := key σ₁ h₁
  obtain ⟨τ₂, hτ₂, hq₂, _⟩ := key σ₂ h₂
  have : IsIso q' := by
    rw [IsIso.eq_inv_of_hom_inv_id hq₁]
    infer_instance
  rw [← hτ₁, ← hτ₂, (cancel_mono q').mp (hq₁.trans hq₂.symm)]

/-- **The second factor of the Stein factorization of a proper morphism with geometrically
connected fibres onto a locally Noetherian scheme is universally injective.** -/
theorem universallyInjective_fromNormalization (f : X ⟶ Y) [IsProper f] [IsLocallyNoetherian Y]
    [GeometricallyConnected f] : UniversallyInjective f.fromNormalization := by
  let π := f.fromNormalization
  let f' := f.toNormalization
  have hff : f' ≫ π = f := Scheme.Hom.toNormalization_fromNormalization f
  have : IsFinite π := Stacks.SteinFactorization.isFinite_fromNormalization f
  have : Surjective f' := Stacks.SteinFactorization.surjective_toNormalization f
  refine ((tfae_universallyInjective π).out 1 2).mpr ?_
  intro K _ a b hab
  let c := a ≫ π
  let Z := pullback π c
  -- `Z = S ×_Y Spec K` is discrete
  have : IsAffine Z := isAffine_of_isAffineHom (pullback.snd π c)
  let φK : K →+* Γ(Z, ⊤) := (pullback.snd π c).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  have hφK : φK.Finite := (pullback.snd π c).finite_appTop.comp (RingHom.Finite.of_surjective _
    (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm.surjective)
  let _ : Algebra K Γ(Z, ⊤) := φK.toAlgebra
  have : Module.Finite K Γ(Z, ⊤) := hφK
  have : IsArtinianRing Γ(Z, ⊤) := IsArtinianRing.of_finite K Γ(Z, ⊤)
  have : DiscreteTopology (Spec Γ(Z, ⊤)) := inferInstanceAs (DiscreteTopology (PrimeSpectrum _))
  have : DiscreteTopology Z := Z.isoSpec.hom.homeomorph.symm.discreteTopology
  -- `Z` is connected, the image of the connected `X ×_Y Spec K`
  have : ConnectedSpace ↑(pullback f c : Scheme.{u}) :=
    GeometricallyConnected.geometrically_connectedSpace (f := f) c (pullback.fst f c)
      (pullback.snd f c) (IsPullback.of_hasPullback f c)
  let h : pullback f c ⟶ Z := pullback.lift (pullback.fst f c ≫ f') (pullback.snd f c)
    (by rw [Category.assoc, hff, pullback.condition])
  have hsq : IsPullback (pullback.fst f c) h f' (pullback.fst π c) := by
    refine IsPullback.of_bot (h₃₁ := c) (v₂₁ := pullback.snd π c) (v₂₂ := π) ?_ ?_
      (IsPullback.of_hasPullback π c)
    · have e1 : h ≫ pullback.snd π c = pullback.snd f c := pullback.lift_snd _ _ _
      rw [e1, hff]
      exact IsPullback.of_hasPullback f c
    · exact (pullback.lift_fst _ _ _).symm
  have : Surjective h := MorphismProperty.of_isPullback (P := @Surjective) hsq ‹_›
  have : ConnectedSpace Z := h.surjective.connectedSpace h.continuous
  have : Subsingleton Z := Set.subsingleton_univ_iff.mp isPreconnected_univ.subsingleton
  -- the two sections agree
  let σa : Spec (.of K) ⟶ Z := pullback.lift a (𝟙 _) (by simp [c])
  let σb : Spec (.of K) ⟶ Z := pullback.lift b (𝟙 _) (by simp [c, hab])
  have hσ := eq_of_comp_eq_id_of_subsingleton (pullback.snd π c) σa σb
    (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _)
  have ha : σa ≫ pullback.fst π c = a := pullback.lift_fst _ _ _
  have hb : σb ≫ pullback.fst π c = b := pullback.lift_fst _ _ _
  rw [← ha, ← hb, hσ]

variable {p : ℕ} [Fact p.Prime]

/-- **A descent along the first factor of the Stein factorization gives a descent of the pullback
to `X ×_Y S` along the projection to `S`.** Here `f : X ⟶ Y` is proper with geometrically
connected fibres onto a locally Noetherian scheme and `X --f'--> S --π--> Y` is its Stein
factorization. The graph `X ⟶ X ×_Y S` of `f'` is a surjective closed immersion, along which
pullback is fully faithful on `colim_F Vect`. -/
theorem descendsAfterFrobenius_pullback_fromNormalization (f : X ⟶ Y) [IsProper f]
    [IsLocallyNoetherian Y] [GeometricallyConnected f] [CompactSpace X] [QuasiSeparatedSpace X]
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) (E : X.Vect)
    (h : Scheme.Vect.DescendsAfterFrobenius f.toNormalization p hX E) :
    Scheme.Vect.DescendsAfterFrobenius (pullback.snd f f.fromNormalization) p
      (isInCharacteristic_of_hom (pullback.fst f f.fromNormalization) p hX)
      ((Scheme.Vect.pullback (pullback.fst f f.fromNormalization)).obj E) := by
  let π := f.fromNormalization
  let f' := f.toNormalization
  have hff : f' ≫ π = f := Scheme.Hom.toNormalization_fromNormalization f
  have : IsFinite π := Stacks.SteinFactorization.isFinite_fromNormalization f
  have : UniversallyInjective π := universallyInjective_fromNormalization f
  let P := pullback f π
  have hP : IsInCharacteristic P p := isInCharacteristic_of_hom (pullback.fst f π) p hX
  have hS : IsInCharacteristic f.normalization p := isInCharacteristic_of_hom π p hY
  -- the graph of `f'`
  let Γ : X ⟶ P := pullback.lift (𝟙 X) f' (by rw [Category.id_comp, hff])
  have hΓ₁ : Γ ≫ pullback.fst f π = 𝟙 X := pullback.lift_fst _ _ _
  have hΓ₂ : Γ ≫ pullback.snd f π = f' := pullback.lift_snd _ _ _
  have : IsClosedImmersion (Γ ≫ pullback.fst f π) := by
    rw [hΓ₁]
    infer_instance
  have : IsClosedImmersion Γ := IsClosedImmersion.of_comp Γ (pullback.fst f π)
  have : UniversallyInjective (pullback.fst f π) :=
    MorphismProperty.of_isPullback (P := @UniversallyInjective)
      (IsPullback.of_hasPullback f π).flip ‹_›
  have : Surjective Γ := by
    refine ⟨fun w ↦ ⟨pullback.fst f π w, ?_⟩⟩
    apply (pullback.fst f π).injective
    rw [← Scheme.Hom.comp_apply, hΓ₁]
    rfl
  have : GeometricallyConnected Γ := geometricallyConnected_of_surjective_of_universallyInjective Γ
  have : CompactSpace ↑P := QuasiCompact.compactSpace_of_compactSpace (pullback.fst f π)
  have : QuasiSeparatedSpace ↑P := quasiSeparatedSpace_of_quasiSeparated (pullback.fst f π)
  -- transport the descent along `f'` to one along `Γ ≫ snd`
  have h' : Scheme.Vect.DescendsAfterFrobenius (Γ ≫ pullback.snd f π) p hX E := by
    rwa [hΓ₂]
  have h'' : Scheme.Vect.DescendsAfterFrobenius (Γ ≫ pullback.snd f π) p hX
      ((Scheme.Vect.pullback Γ).obj ((Scheme.Vect.pullback (pullback.fst f π)).obj E)) :=
    h'.of_iso hX (((Scheme.Vect.pullbackId X).app E).symm ≪≫
      ((Scheme.Vect.pullbackCongr hΓ₁).app E).symm ≪≫
        ((Scheme.Vect.pullbackComp Γ (pullback.fst f π)).app E).symm)
  exact Scheme.Vect.DescendsAfterFrobenius.of_comp (pullback.snd f π) Γ hP hX hS
    (frobeniusColimitVectModelPullback_full_faithful Γ p hX hP) h''

end AlgebraicGeometry

end
