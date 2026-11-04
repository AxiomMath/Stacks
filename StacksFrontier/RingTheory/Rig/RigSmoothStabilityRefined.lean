module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Rig.AdicBasic
public import StacksFrontier.RingTheory.Rig.Reduction
public import StacksFrontier.RingTheory.Rig.RigEtaleBaseChange
public import StacksFrontier.RingTheory.Rig.RigSmooth
public import StacksFrontier.RingTheory.Rig.RigSmoothBaseChange
public import StacksFrontier.RingTheory.Rig.RigSmoothStability
public import StacksFrontier.Topology.Algebra.AdicTopology.AdicRingMapRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.Adic
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalPropertiesRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.TautIsLocalRefined
import all StacksFrontier.RingTheory.Rig.RigSmoothStability

/-!
# Stability of rig-smoothness and rig-étaleness under base change by adic morphisms

## Main results

* `TopologicalRing.rigSmooth_isStableUnderBaseChangeByAdic'`: if rig-smoothness is local, then
  rig-smoothness is stable under base change by adic morphisms, in the bundled form
  `TopologicalRing.IsStableUnderBaseChangeBy'`.
* `TopologicalRing.rigEtale_isStableUnderBaseChangeByAdic'`: if rig-étaleness is local, then
  rig-étaleness is stable under base change by adic morphisms, in the same bundled form.
-/

@[expose] public noncomputable section

namespace TopologicalRing

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

open Filter
open CategoryTheory
open Rig
open scoped Topology TensorProduct

/-- A Noetherian adic ring has a finitely generated ideal of definition. -/
private theorem exists_fg_isAdic_of_isAdic_noetherian {R : Type u} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] (h : TopologicalRing.IsAdic R ∧ IsNoetherianRing R) :
    ∃ I : Ideal R, I.FG ∧ _root_.IsAdic I := by
  obtain ⟨I, -, hI⟩ := h.1.1
  have := h.2
  exact ⟨I, Ideal.fg_of_isNoetherianRing I, hI⟩

/-- The completion over a countably weakly admissible ring is countably weakly admissible. -/
private theorem completionOver_isCountablyWeaklyAdmissible {B A : Type u} [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B] [CommRing A] (f : B →+* A)
    (hB : IsCountablyWeaklyAdmissible B) : IsCountablyWeaklyAdmissible (CompletionOver f) :=
  ⟨completionOver_isWeaklyAdmissible f hB.1,
    completionOver_isCountablyGenerated_nhds_zero f hB.1 hB.2⟩

private theorem isAdic_propertyIsLocalNoetherian' :
    TopologicalRing.PropertyIsLocalNoetherian'.{u}
      (fun {A B : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
        [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        (φ : A →+* B) => RingHom.IsAdic φ) := by
  show TopologicalRing.PropertyIsLocal'
    (fun {A B : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
      [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      (φ : A →+* B) => RingHom.IsAdic φ)
    (fun R => TopologicalRing.IsAdic R ∧ IsNoetherianRing R)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro B A B' A' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    intro eB eA heB heBs heA heAs f _ _ _ _ _
    exact RingHom.isAdic_comp_ringEquiv_iff eB eA heB heBs heA heAs f
  · intro A B A' B' _ _ _ _ _ _ _ _ _ _ D hA hB hA' hB' hMap
    let hAweak : TopologicalRing.IsCountablyWeaklyAdmissible A :=
      ⟨D.weaklyAdmissibleA, D.countableA⟩
    let hBweak : TopologicalRing.IsCountablyWeaklyAdmissible B :=
      ⟨D.weaklyAdmissibleB, D.countableB⟩
    let hA'weak := completionOver_isCountablyWeaklyAdmissible D.toA' hAweak
    let hB'weak := completionOver_isCountablyWeaklyAdmissible D.toB' hBweak
    have hBfg := exists_fg_isAdic_of_isAdic_noetherian hB
    have hInput := (adic_iff_taut_of_local_context D.map D.continuousMap hBfg
      hAweak.1.2.1 hAweak.1.2.2).mp hMap
    have hOutput := TopologicalRing.isTaut_localizationPreserves
      D hAweak hBweak hA'weak hB'weak hInput
    have hB'fg := exists_fg_isAdic_of_isAdic_noetherian hB'
    exact (adic_iff_taut_of_local_context D.completedMap D.continuousCompletedMap hB'fg
      hA'weak.1.2.1 hA'weak.1.2.2).mpr hOutput
  · intro A B A' B' _ _ _ _ _ _ _ _ _ _ D hA hB hA' hB' hFF hCompleted
    let hAweak : TopologicalRing.IsCountablyWeaklyAdmissible A :=
      ⟨D.weaklyAdmissibleA, D.countableA⟩
    let hBweak : TopologicalRing.IsCountablyWeaklyAdmissible B :=
      ⟨D.weaklyAdmissibleB, D.countableB⟩
    let hA'weak := completionOver_isCountablyWeaklyAdmissible D.toA' hAweak
    let hB'weak := completionOver_isCountablyWeaklyAdmissible D.toB' hBweak
    have hBfg := exists_fg_isAdic_of_isAdic_noetherian hB
    have hB'fg := exists_fg_isAdic_of_isAdic_noetherian hB'
    have hInput := (adic_iff_taut_of_local_context D.completedMap
      D.continuousCompletedMap hB'fg hA'weak.1.2.1 hA'weak.1.2.2).mp hCompleted
    have hOutput := TopologicalRing.isTaut_faithfullyFlatDescent
      D hAweak hBweak hA'weak hB'weak hFF hInput
    exact (adic_iff_taut_of_local_context D.map D.continuousMap hBfg
      hAweak.1.2.1 hAweak.1.2.2).mpr hOutput
  · intro B _ _ _ _ hB hBcount ι _ A _ _ _ _ hAweak hAcount f hf hBprop hAprop hMaps
    have hBfg := exists_fg_isAdic_of_isAdic_noetherian hBprop
    have hProdTaut := TopologicalRing.isTaut_finiteProductPreserves
      hB hBcount A hAweak hAcount f hf ⟨hB, hBcount⟩ (fun i => ⟨hAweak i, hAcount i⟩)
      fun i => (adic_iff_taut_of_local_context (f i) (hf i) hBfg
        (hAweak i).2.1 (hAweak i).2.2).mp (hMaps i)
    let : ∀ i, UniformSpace (A i) := fun i => IsTopologicalAddGroup.rightUniformSpace (A i)
    let : ∀ i, IsUniformAddGroup (A i) := fun i => isUniformAddGroup_of_addCommGroup
    let : ∀ i, CompleteSpace (A i) := fun i => (hAweak i).2.1
    let : ∀ i, T2Space (A i) := fun i => (hAweak i).2.2
    let : IsLinearTopology (∀ i, A i) (∀ i, A i) := pi_isLinearTopology
    let : UniformSpace (∀ i, A i) := Pi.uniformSpace A
    let : IsUniformAddGroup (∀ i, A i) := ⟨by
      rw [uniformContinuous_pi]
      intro i
      exact ((Pi.uniformContinuous_proj A i).comp uniformContinuous_fst).sub
        ((Pi.uniformContinuous_proj A i).comp uniformContinuous_snd)⟩
    have hPiComplete : @CompleteSpace (∀ i, A i)
        (IsTopologicalAddGroup.rightUniformSpace (∀ i, A i)) := by
      rw [IsUniformAddGroup.rightUniformSpace_eq]
      exact Pi.complete A
    let : UniformSpace (∀ i, A i) :=
      IsTopologicalAddGroup.rightUniformSpace (∀ i, A i)
    let : CompleteSpace (∀ i, A i) := hPiComplete
    let : T2Space (∀ i, A i) := inferInstance
    exact (adic_iff_taut_of_local_context (RingHom.pi f) (continuous_pi hf)
      hBfg (inferInstance : @CompleteSpace (∀ i, A i)
        (IsTopologicalAddGroup.rightUniformSpace (∀ i, A i))) inferInstance).mpr hProdTaut

/-- If rig-smoothness is local in the sense of `TopologicalRing.PropertyIsLocalNoetherian'`
(Tag 0GCK), then rig-smoothness is stable under base change by adic morphisms in the sense of
`TopologicalRing.IsStableUnderBaseChangeBy'`: rig-smoothness and the adic property are both local,
and the completed base change of a rig-smooth arrow along an adic arrow is rig-smooth
(Tag 0GCL). -/
public theorem rigSmooth_isStableUnderBaseChangeByAdic'
    (hlocal : TopologicalRing.PropertyIsLocalNoetherian'.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) =>
        RingHom.IsRigSmoothArrow φ)) :
    TopologicalRing.IsStableUnderBaseChangeBy'.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) =>
        RingHom.IsRigSmoothArrow φ)
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) =>
        RingHom.IsAdic φ) where
  isLocalP := hlocal
  isLocalQ := isAdic_propertyIsLocalNoetherian'
  baseChange hB hA hC hBA hBC hP hQ :=
    rigSmooth_completedTensorProduct_of_isAdic hB hA hC hBA hBC hP hQ

/-- If rig-étaleness is local in the sense of `TopologicalRing.PropertyIsLocalNoetherian'`
(Tag 0AQL), then rig-étaleness is stable under base change by adic morphisms in the sense of
`TopologicalRing.IsStableUnderBaseChangeBy'`: rig-étaleness and the adic property are both local,
and the completed base change of a rig-étale arrow along an adic arrow is rig-étale
(Tag 0GCW). -/
public theorem rigEtale_isStableUnderBaseChangeByAdic'
    (hlocal : TopologicalRing.PropertyIsLocalNoetherian'.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) =>
        RingHom.IsRigEtaleArrow φ)) :
    TopologicalRing.IsStableUnderBaseChangeBy'.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) =>
        RingHom.IsRigEtaleArrow φ)
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) =>
        RingHom.IsAdic φ) where
  isLocalP := hlocal
  isLocalQ := isAdic_propertyIsLocalNoetherian'
  baseChange hB hA hC hBA hBC hP hQ :=
    rigEtale_completedTensorProduct_of_isAdic hB hA hC hBA hBC hP hQ

end TopologicalRing

end
