module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.LocalRings
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.ProfiniteComponentRealization
public import StacksFrontier.AlgebraicGeometry.ProEtale.LocalIso.Flatness
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.Basic
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.StratificationColimitIndZariski
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.StratificationLimitClosedPoints
public import StacksFrontier.Topology.ExtremallyDisconnected.Characterization
public import StacksFrontier.Topology.ExtremallyDisconnected.Cover
public import StacksFrontier.Topology.Profinite.Defs
public import StacksFrontier.Topology.Spectral.ComponentSpace

/-!
# Extremal disconnectedness of the component space from ind-Zariski retractions

If every faithfully flat ind-Zariski algebra over `A` admits a retraction, then the space of
connected components of `Spec A` is extremally disconnected. This is the ind-Zariski half of the
w-local characterisations.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

universe u v

/-- If every faithfully flat ind-Zariski `A`-algebra admits a retraction, then `Spec A` is
w-local. -/
public theorem wLocalSpace_of_indZariski_faithfullyFlat_retracts (A : Type u) [CommRing A]
    (h : ∀ (B : Type (max u v)) [CommRing B] [Algebra A B], Module.FaithfullyFlat A B →
      IsIndZariski.{u, max u v, max u v} A B → Nonempty (B →ₐ[A] A)) :
    WLocalSpace (PrimeSpectrum A) := by
  have hmap : algebraMap A (stratificationColimitRing (A := A)) =
      stratificationColimitAlgebraMap (A := A) := RingHom.algebraMap_toAlgebra _
  have : Module.FaithfullyFlat A (stratificationColimitRing (A := A)) :=
    RingHom.faithfullyFlat_algebraMap_iff.mp
      (hmap ▸ stratificationColimit_faithfullyFlat (A := A))
  have hff : Module.FaithfullyFlat A (ULift.{v} (stratificationColimitRing (A := A))) :=
    Module.FaithfullyFlat.of_linearEquiv A (stratificationColimitRing (A := A))
      (ULift.algEquiv (R := A)).toLinearEquiv
  have hind : IsIndZariski.{u, max u v, max u v} A
      (ULift.{v} (stratificationColimitRing (A := A))) :=
    Algebra.IsIndZariski.of_equiv (RingEquiv.refl A) ULift.ringEquiv.symm (fun _ => rfl)
      stratificationColimit_isIndZariski
  obtain ⟨r⟩ := h _ hff hind
  let r₀ : stratificationColimitRing (A := A) →ₐ[A] A := r.comp ULift.algEquiv.symm.toAlgHom
  have hemb := PrimeSpectrum.isClosedEmbedding_comap_of_surjective A
    (r₀ : stratificationColimitRing (A := A) →+* A) fun a => ⟨algebraMap A _ a, r₀.commutes a⟩
  have : WLocalSpace (PrimeSpectrum (stratificationColimitRing (A := A))) :=
    stratificationLimitScheme_wLocal (A := A)
  have : WLocalSpace
      (Set.range (PrimeSpectrum.comap (r₀ : stratificationColimitRing (A := A) →+* A))) :=
    wLocalSpace_of_isClosed hemb.isClosed_range
  exact wLocalSpace_of_homeomorph hemb.toIsEmbedding.toHomeomorph

/-- If every faithfully flat ind-Zariski `A`-algebra admits a retraction, then every continuous
surjection onto `π₀(Spec A)` from a compact Hausdorff extremally disconnected space has a
continuous section. -/
public theorem exists_continuous_section_of_indZariski_faithfullyFlat_retracts
    (A : Type u) [CommRing A]
    (h : ∀ (B : Type (max u v)) [CommRing B] [Algebra A B], Module.FaithfullyFlat A B →
      IsIndZariski.{u, max u v, max u v} A B → Nonempty (B →ₐ[A] A))
    (T : Type u) [TopologicalSpace T] [CompactSpace T] [T2Space T] [ExtremallyDisconnected T]
    (π : T → ConnectedComponents (PrimeSpectrum A)) (hπ : Continuous π)
    (hπsurj : Function.Surjective π) :
    ∃ s : ConnectedComponents (PrimeSpectrum A) → T, Continuous s ∧ π ∘ s = id := by
  let eT : ULift.{v} T ≃ₜ T := Homeomorph.ulift
  have : CompactSpace (ULift.{v} T) := eT.symm.compactSpace
  have : ExtremallyDisconnected (ULift.{v} T) := extremallyDisconnected_of_homeo eT.symm
  have hprof : IsProfiniteStacks (ULift.{v} T) :=
    (isProfiniteStacks_iff_compact_t2_totallyDisconnected (ULift.{v} T)).2
      ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨B, hB, algB, hind, g, -, -, hpb⟩ := exists_indZariski_of_profinite_component_map
    A (ULift.{v} T) hprof ⟨fun t => π t.down, hπ.comp continuous_uliftDown⟩
  let : CommRing B := hB
  let : Algebra A B := algB
  have hcomp (q : PrimeSpectrum B) :
      ConnectedComponents.mk (PrimeSpectrum.comap (algebraMap A B) q) = π (g q).down := by
    simpa using congrArg ULift.down (ConcreteCategory.congr_hom hpb.w q)
  have hspec : Function.Surjective (PrimeSpectrum.comap (algebraMap A B)) := by
    intro p
    obtain ⟨t, ht⟩ := hπsurj (ConnectedComponents.mk p)
    let pA : TopCat.of PUnit ⟶ TopCat.of (ULift.{max u v} (PrimeSpectrum A)) :=
      TopCat.ofHom ⟨fun _ => ULift.up p, continuous_const⟩
    let pT : TopCat.of PUnit ⟶ TopCat.of (ULift.{u} (ULift.{v} T)) :=
      TopCat.ofHom ⟨fun _ => ULift.up (ULift.up t), continuous_const⟩
    obtain ⟨l, hl, -⟩ := hpb.exists_lift pA pT (by ext _; simpa [pA, pT] using ht.symm)
    exact ⟨l.hom PUnit.unit, congrArg ULift.down (ConcreteCategory.congr_hom hl PUnit.unit)⟩
  have hff : Module.FaithfullyFlat A B :=
    RingHom.faithfullyFlat_algebraMap_iff.mp
      (faithfullyFlat_of_comap_surjective_of_identifiesLocalRings A B
        (identifiesLocalRings_of_isIndZariski A B hind) hspec)
  obtain ⟨r⟩ := h B hff hind
  have hcont : Continuous fun p : PrimeSpectrum A =>
      (g (PrimeSpectrum.comap (r : B →+* A) p)).down :=
    continuous_uliftDown.comp (g.continuous.comp (PrimeSpectrum.continuous_comap _))
  refine ⟨hcont.connectedComponentsLift, hcont.connectedComponentsLift_continuous, funext ?_⟩
  intro x
  obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe x
  have hs : hcont.connectedComponentsLift (ConnectedComponents.mk p) =
      (g (PrimeSpectrum.comap (r : B →+* A) p)).down :=
    congrFun hcont.connectedComponentsLift_comp_coe p
  have hid : PrimeSpectrum.comap (algebraMap A B)
      (PrimeSpectrum.comap (r : B →+* A) p) = p := by
    rw [← PrimeSpectrum.comap_comp_apply]
    simp
  simp only [Function.comp_apply, id_eq, hs]
  rw [← hcomp, hid]

/-- If every faithfully flat ind-Zariski `A`-algebra admits a retraction, then `π₀(Spec A)` is
extremally disconnected. -/
public theorem extremallyDisconnected_of_indZariski_faithfullyFlat_retracts
    (A : Type u) [CommRing A]
    (h : ∀ (B : Type (max u v)) [CommRing B] [Algebra A B], Module.FaithfullyFlat A B →
      IsIndZariski.{u, max u v, max u v} A B → Nonempty (B →ₐ[A] A)) :
    ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum A)) := by
  have : T2Space (ConnectedComponents (PrimeSpectrum A)) :=
    (connectedComponents_isProfinite (PrimeSpectrum A)).1
  have hsec : HasContinuousSectionFromCompactT2 (ConnectedComponents (PrimeSpectrum A)) := by
    intro Y _ _ _ f hf hfsurj
    obtain ⟨Y', _, _, _, hED, π, hπ, hπsurj⟩ := exists_extremallyDisconnected_cover Y
    obtain ⟨s, hs, hcomp⟩ := exists_continuous_section_of_indZariski_faithfullyFlat_retracts A h Y'
      (f ∘ π) (hf.comp hπ) (hfsurj.comp hπsurj)
    exact ⟨π ∘ s, hπ.comp hs, by simpa [Function.comp_assoc] using hcomp⟩
  have hiff : ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum A)) ↔
      HasContinuousSectionFromCompactT2 (ConnectedComponents (PrimeSpectrum A)) :=
    (extremallyDisconnected_tfae (ConnectedComponents (PrimeSpectrum A))).out 1 2
  exact hiff.mpr hsec

end AlgebraicGeometry.ProEtale

end
