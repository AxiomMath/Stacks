module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Rig.AdicBasic
public import StacksFrontier.RingTheory.Rig.Reduction
public import StacksFrontier.RingTheory.Rig.RigEtaleBaseChange
public import StacksFrontier.RingTheory.Rig.RigSmooth
public import StacksFrontier.RingTheory.Rig.RigSmoothBaseChange
public import StacksFrontier.Topology.Algebra.AdicTopology.AdicRingMap
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.Adic
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalProperties
public import StacksFrontier.Topology.Algebra.AdicTopology.TautIsLocal

/-!
# Rig-smoothness and rig-étaleness are stable under base change by adic morphisms

Let `B → A` be a rig-smooth morphism and `B → C` an adic morphism of Noetherian adic
topological rings.  Then the completed tensor product `A ⊗̂_B C` is again Noetherian adic and
rig-smooth over `C`.  The same holds with rig-smooth replaced by rig-étale throughout.

## Main results

* `TopologicalRing.rigSmooth_completedTensorProduct_of_isAdic`: the completed base change of a
  rig-smooth morphism by an adic morphism is Noetherian adic and rig-smooth.
* `TopologicalRing.rigEtale_completedTensorProduct_of_isAdic`: the completed base change of a
  rig-étale morphism by an adic morphism is Noetherian adic and rig-étale.
* `TopologicalRing.rigSmooth_isStableUnderBaseChangeByAdic`: rig-smoothness is stable under base
  change by adic morphisms in the bundled form of Remark 0GBG, given its locality.
* `TopologicalRing.rigEtale_isStableUnderBaseChangeByAdic`: rig-étaleness is stable under base
  change by adic morphisms in the bundled form of Remark 0GBG, given its locality.

## References

* [Stacks Project, Tag 0GCL](https://stacks.math.columbia.edu/tag/0GCL)
* [Stacks Project, Tag 0GCW](https://stacks.math.columbia.edu/tag/0GCW)
* [Stacks Project, Tag 0GBG](https://stacks.math.columbia.edu/tag/0GBG)
* [Stacks Project, Tag 0GAM](https://stacks.math.columbia.edu/tag/0GAM)
* [Stacks Project, Tag 0GB2](https://stacks.math.columbia.edu/tag/0GB2)
* [Stacks Project, Tag 0GCJ](https://stacks.math.columbia.edu/tag/0GCJ)
* [Stacks Project, Tag 0GCV](https://stacks.math.columbia.edu/tag/0GCV)
-/

@[expose] public noncomputable section

namespace TopologicalRing

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

open Filter
open CategoryTheory
open Rig
open scoped Topology TensorProduct

private theorem isAdic_map_of_idealOfDefinition
    {R S : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R]
    [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [IsLinearTopology S S]
    {f : R →+* S} {I : Ideal R}
    (hI : TopologicalRing.IsIdealOfDefinition I)
    (hf : RingHom.IsAdic f) : _root_.IsAdic (I.map f) := by
  obtain ⟨J, hJ, hJmap⟩ := hf
  have hJdef : TopologicalRing.IsIdealOfDefinition J :=
    ⟨by simpa using (isAdic_iff.mp hJ).1 1, (isAdic_iff.mp hJ).2⟩
  obtain ⟨a, ha⟩ := hI.2 (J : Set R) (hJdef.1.mem_nhds (zero_mem J))
  obtain ⟨b, hb⟩ := hJdef.2 (I : Set R) (hI.1.mem_nhds (zero_mem I))
  have hsmall : (I.map f) ^ a ≤ J.map f := by
    rw [← Ideal.map_pow]
    exact Ideal.map_mono (SetLike.coe_subset_coe.mp ha)
  have hlarge : (J.map f) ^ b ≤ I.map f := by
    rw [← Ideal.map_pow]
    exact Ideal.map_mono (SetLike.coe_subset_coe.mp hb)
  rw [isAdic_iff]
  constructor
  · intro n
    have hopen := (isAdic_iff.mp hJmap).1 (b * n)
    have hle : (J.map f) ^ (b * n) ≤ (I.map f) ^ n := by
      rw [pow_mul]
      exact Ideal.pow_right_mono hlarge n
    exact (I.map f ^ n).toAddSubgroup.isOpen_of_mem_nhds
      (Filter.mem_of_superset (hopen.mem_nhds (zero_mem _))
        (SetLike.coe_subset_coe.mpr hle))
  · intro U hU
    obtain ⟨n, hn⟩ := (isAdic_iff.mp hJmap).2 U hU
    refine ⟨a * n, ?_⟩
    have hle : (I.map f) ^ (a * n) ≤ (J.map f) ^ n := by
      rw [pow_mul]
      exact Ideal.pow_right_mono hsmall n
    exact (SetLike.coe_subset_coe.mpr hle).trans hn

/-- A product of linearly topologized commutative rings is linearly topologized. -/
theorem pi_isLinearTopology {ι : Type*} {A : ι → Type*}
    [∀ i, CommRing (A i)] [∀ i, TopologicalSpace (A i)]
    [∀ i, IsTopologicalRing (A i)] [∀ i, IsLinearTopology (A i) (A i)] :
    IsLinearTopology (∀ i, A i) (∀ i, A i) := by
  let piSubmodule (S : Set ι) (J : ∀ i, Submodule (A i) (A i)) :
      Submodule (∀ i, A i) (∀ i, A i) := {
    carrier := S.pi fun i => (J i : Set (A i))
    zero_mem' := by simp
    add_mem' := by
      intro x y hx hy i hi
      exact (J i).add_mem (hx i hi) (hy i hi)
    smul_mem' := by
      intro r x hx i hi
      exact (J i).smul_mem (r i) (hx i hi)
  }
  let hRect := Filter.hasBasis_pi fun i =>
    (isLinearTopology_iff_hasBasis_submodule (R := A i) (M := A i)).mp inferInstance
  have hBasis : (nhds (0 : ∀ i, A i)).HasBasis
      (fun N : Submodule (∀ i, A i) (∀ i, A i) => (N : Set (∀ i, A i)) ∈ 𝓝 0)
      (fun N => (N : Set (∀ i, A i))) := by
    rw [nhds_pi]
    exact hRect.to_hasBasis
      (fun idx hidx => ⟨piSubmodule idx.1 idx.2, hRect.mem_of_mem hidx, fun x hx => hx⟩)
      (fun N hN => hRect.mem_iff.mp hN)
  exact IsLinearTopology.mk_of_hasBasis' (R := ∀ i, A i) hBasis
    (fun (I : Submodule (∀ i, A i) (∀ i, A i)) r x hx => I.smul_mem r hx)

private theorem adic_iff_taut_of_local_context
    {A B : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B] (φ : A →+* B) (hφ : Continuous φ)
    (hA : ∃ I : Ideal A, I.FG ∧ _root_.IsAdic I)
    (hBcomplete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hBT2 : T2Space B) : RingHom.IsAdic φ ↔ RingHom.IsTaut φ := by
  let : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace B
  let : CompleteSpace B := hBcomplete
  let : T2Space B := hBT2
  exact RingHom.isAdic_iff_isTaut φ hφ hA

private theorem isAdic_propertyIsLocalNoetherian :
    TopologicalRing.PropertyIsLocalNoetherian.{u}
      (fun {A B : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
        [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        (φ : A →+* B) => RingHom.IsAdic φ) := by
  show TopologicalRing.PropertyIsLocal
    (fun {A B : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
      [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      (φ : A →+* B) => RingHom.IsAdic φ)
    (fun R => TopologicalRing.IsAdic R ∧ IsNoetherianRing R)
  refine ⟨?_, ?_, ?_⟩
  · intro A B A' B' _ _ _ _ _ _ _ _ _ _ D hA hB hA' hB' hMap
    let hAweak : TopologicalRing.IsCountablyWeaklyAdmissible A :=
      ⟨D.weaklyAdmissibleA, D.countableA⟩
    let hBweak : TopologicalRing.IsCountablyWeaklyAdmissible B :=
      ⟨D.weaklyAdmissibleB, D.countableB⟩
    let hA'weak : TopologicalRing.IsCountablyWeaklyAdmissible
        (TopologicalRing.CompletionOver D.toA') :=
      ⟨TopologicalRing.completionOver_isWeaklyAdmissible
          D.toA' D.weaklyAdmissibleA,
        TopologicalRing.completionOver_isCountablyGenerated_nhds_zero
          D.toA' D.weaklyAdmissibleA D.countableA⟩
    let hB'weak : TopologicalRing.IsCountablyWeaklyAdmissible
        (TopologicalRing.CompletionOver D.toB') :=
      ⟨TopologicalRing.completionOver_isWeaklyAdmissible
          D.toB' D.weaklyAdmissibleB,
        TopologicalRing.completionOver_isCountablyGenerated_nhds_zero
          D.toB' D.weaklyAdmissibleB D.countableB⟩
    obtain ⟨I, hIdef, hIadic⟩ := hB.1.1
    let : IsNoetherianRing B := hB.2
    have hBfg : ∃ I : Ideal B, I.FG ∧ _root_.IsAdic I :=
      ⟨I, Ideal.fg_of_isNoetherianRing I, hIadic⟩
    have hInput := (adic_iff_taut_of_local_context D.map D.continuousMap hBfg
      hAweak.1.2.1 hAweak.1.2.2).mp hMap
    have hOutput := TopologicalRing.isTaut_localizationPreserves
      D hAweak hBweak hA'weak hB'weak hInput
    obtain ⟨IB', hIB'def, hIB'adic⟩ := hB'.1.1
    let : IsNoetherianRing (TopologicalRing.CompletionOver D.toB') := hB'.2
    have hB'fg : ∃ I : Ideal (TopologicalRing.CompletionOver D.toB'),
        I.FG ∧ _root_.IsAdic I := ⟨IB', Ideal.fg_of_isNoetherianRing IB', hIB'adic⟩
    exact (adic_iff_taut_of_local_context D.completedMap D.continuousCompletedMap hB'fg
      hA'weak.1.2.1 hA'weak.1.2.2).mpr hOutput
  · intro A B A' B' _ _ _ _ _ _ _ _ _ _ D hA hB hA' hB' hFF hCompleted
    let hAweak : TopologicalRing.IsCountablyWeaklyAdmissible A :=
      ⟨D.weaklyAdmissibleA, D.countableA⟩
    let hBweak : TopologicalRing.IsCountablyWeaklyAdmissible B :=
      ⟨D.weaklyAdmissibleB, D.countableB⟩
    let hA'weak : TopologicalRing.IsCountablyWeaklyAdmissible
        (TopologicalRing.CompletionOver D.toA') :=
      ⟨TopologicalRing.completionOver_isWeaklyAdmissible
          D.toA' D.weaklyAdmissibleA,
        TopologicalRing.completionOver_isCountablyGenerated_nhds_zero
          D.toA' D.weaklyAdmissibleA D.countableA⟩
    let hB'weak : TopologicalRing.IsCountablyWeaklyAdmissible
        (TopologicalRing.CompletionOver D.toB') :=
      ⟨TopologicalRing.completionOver_isWeaklyAdmissible
          D.toB' D.weaklyAdmissibleB,
        TopologicalRing.completionOver_isCountablyGenerated_nhds_zero
          D.toB' D.weaklyAdmissibleB D.countableB⟩
    obtain ⟨I, hIdef, hIadic⟩ := hB.1.1
    let : IsNoetherianRing B := hB.2
    have hBfg : ∃ I : Ideal B, I.FG ∧ _root_.IsAdic I :=
      ⟨I, Ideal.fg_of_isNoetherianRing I, hIadic⟩
    obtain ⟨IB', hIB'def, hIB'adic⟩ := hB'.1.1
    let : IsNoetherianRing (TopologicalRing.CompletionOver D.toB') := hB'.2
    have hB'fg : ∃ I : Ideal (TopologicalRing.CompletionOver D.toB'),
        I.FG ∧ _root_.IsAdic I := ⟨IB', Ideal.fg_of_isNoetherianRing IB', hIB'adic⟩
    have hInput := (adic_iff_taut_of_local_context D.completedMap
      D.continuousCompletedMap hB'fg hA'weak.1.2.1 hA'weak.1.2.2).mp hCompleted
    have hOutput := TopologicalRing.isTaut_faithfullyFlatDescent
      D hAweak hBweak hA'weak hB'weak hFF hInput
    exact (adic_iff_taut_of_local_context D.map D.continuousMap hBfg
      hAweak.1.2.1 hAweak.1.2.2).mpr hOutput
  · intro B _ _ _ _ hB hBcount ι _ A _ _ _ _ hAweak hAcount f hf hBprop hAprop hMaps
    obtain ⟨I, hIdef, hIadic⟩ := hBprop.1.1
    let : IsNoetherianRing B := hBprop.2
    have hBfg : ∃ I : Ideal B, I.FG ∧ _root_.IsAdic I :=
      ⟨I, Ideal.fg_of_isNoetherianRing I, hIadic⟩
    let hBcountableWeak : TopologicalRing.IsCountablyWeaklyAdmissible B := ⟨hB, hBcount⟩
    let hAcountableWeak : ∀ i, TopologicalRing.IsCountablyWeaklyAdmissible (A i) :=
      fun i => ⟨hAweak i, hAcount i⟩
    have hTaut : ∀ i, RingHom.IsTaut (f i) := fun i =>
      (adic_iff_taut_of_local_context (f i) (hf i) hBfg
        (hAweak i).2.1 (hAweak i).2.2).mp (hMaps i)
    have hProdTaut := TopologicalRing.isTaut_finiteProductPreserves
      hB hBcount A hAweak hAcount f hf hBcountableWeak hAcountableWeak hTaut
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


private noncomputable def replaceObjectIso
    {C D : Type*} [Category C] [Category D]
    (F : CategoryTheory.Functor C D) (X : C) (Y : D)
    (e : CategoryTheory.Iso Y (F.obj X)) (Z : C) [Decidable (Z = X)] :
    (if _ : Z = X then Y else F.obj Z) ≅ F.obj Z := by
  classical
  by_cases h : Z = X
  · subst Z
    simpa using e
  · simpa [h] using Iso.refl (F.obj Z)

private noncomputable def completedTensorProduct_adicCompletionEquiv
    {B A C : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B] [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
    [IsLinearTopology C C] [Algebra B A] [Algebra B C] :
    letI : TopologicalSpace (A ⊗[B] C) :=
      TopologicalRing.tensorProductTopology (R := B) (M := A) (N := C)
    letI : UniformSpace (A ⊗[B] C) :=
      TopologicalRing.tensorProductUniformSpace (R := B) (M := A) (N := C)
    letI : IsUniformAddGroup (A ⊗[B] C) := TopologicalRing.tensorProduct_isUniformAddGroup
    letI : IsTopologicalRing (A ⊗[B] C) := TopologicalRing.tensorProduct_isTopologicalRing
    (J : Ideal (A ⊗[B] C)) → _root_.IsAdic J →
    TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C) ≃+*
      AdicCompletion J (A ⊗[B] C) := by
  intro J hJ
  let S := A ⊗[B] C
  letI : TopologicalSpace S := TopologicalRing.tensorProductTopology (R := B) (M := A) (N := C)
  letI : UniformSpace S := TopologicalRing.tensorProductUniformSpace (R := B) (M := A) (N := C)
  letI : IsUniformAddGroup S := TopologicalRing.tensorProduct_isUniformAddGroup
  letI : IsTopologicalRing S := TopologicalRing.tensorProduct_isTopologicalRing
  exact AdicCompletionBridge.adicCompletionRingEquiv J hJ

private theorem completedTensorProduct_rightMap_isTaut
    {B A C : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B] [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
    [IsLinearTopology C C] [Algebra B A] [Algebra B C]
    (hBA : RingHom.IsTaut (algebraMap B A))
    (hBC : Continuous (algebraMap B C)) :
    RingHom.IsTaut (algebraMap C
      (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C))) := by
  let S := A ⊗[B] C
  let T := TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C)
  let : TopologicalSpace S := TopologicalRing.tensorProductTopology (R := B) (M := A) (N := C)
  let : UniformSpace S := TopologicalRing.tensorProductUniformSpace (R := B) (M := A) (N := C)
  let : IsUniformAddGroup S := TopologicalRing.tensorProduct_isUniformAddGroup
  let : IsLinearTopology S S := TopologicalRing.tensorProduct_isLinearTopologyRing
  let : IsTopologicalRing S := TopologicalRing.tensorProduct_isTopologicalRing
  let left : A →+* T := (UniformSpace.Completion.coeRingHom : S →+* T).comp
    (Algebra.TensorProduct.includeLeft : A →ₐ[B] S).toRingHom
  let right : C →+* T := (UniformSpace.Completion.coeRingHom : S →+* T).comp
    (Algebra.TensorProduct.includeRight : C →ₐ[B] S).toRingHom
  have hleft : Continuous left := by
    show Continuous (fun a : A => (↑(a ⊗ₜ[B] (1 : C)) : T))
    exact (UniformSpace.Completion.continuous_coe S).comp
      (TopologicalRing.continuous_tmul_const (R := B) (1 : C))
  let OA := {I : Ideal A // IsOpen (I : Set A)}
  let OC := {J : Ideal C // IsOpen (J : Set C)}
  let bA : (nhds (0 : A)).HasBasis (fun _ : OA => True) (fun i => (i.1 : Set A)) :=
    (IsLinearTopology.hasBasis_open_ideal (R := A)).to_hasBasis
      (fun I hI => ⟨⟨I, hI⟩, trivial, Set.Subset.rfl⟩)
      (fun i _ => ⟨i.1, i.2, Set.Subset.rfl⟩)
  let bC : (nhds (0 : C)).HasBasis (fun _ : OC => True) (fun i => (i.1 : Set C)) :=
    (IsLinearTopology.hasBasis_open_ideal (R := C)).to_hasBasis
      (fun J hJ => ⟨⟨J, hJ⟩, trivial, Set.Subset.rfl⟩)
      (fun j _ => ⟨j.1, j.2, Set.Subset.rfl⟩)
  have hproj := TopologicalRing.hasBasis_projectionKernel
    (B := B) (A := A) (C := C) (fun i : OA => i.1) (fun j : OC => j.1) bA bC
  have hleft_comp_right : left.comp (algebraMap B A) =
      right.comp (algebraMap B C) := by
    ext b
    simp [left, right, RingHom.comp_apply]
  have closureMapBound (K : Ideal B) (J : Ideal C)
      (hKJ : K ≤ Ideal.comap (algebraMap B C) J) :
      let U : Ideal A := Ideal.closure (K.map (algebraMap B A))
      (U.map left) ≤ Ideal.closure (J.map right) := by
    dsimp only
    let Q : Ideal T := Ideal.closure (J.map right)
    have hQclosed : IsClosed (Q : Set T) := isClosed_closure
    have hpreclosed : IsClosed ((Q.comap left : Ideal A) : Set A) := by
      show IsClosed (left ⁻¹' (Q : Set T))
      exact hQclosed.preimage hleft
    have hKmap : K.map (algebraMap B A) ≤ Q.comap left := by
      apply Ideal.map_le_iff_le_comap.mpr
      intro b hb
      show left ((algebraMap B A) b) ∈ Q
      have hcompat : left (algebraMap B A b) = right (algebraMap B C b) := by
        simpa only [RingHom.comp_apply] using
          congrArg (fun f : B →+* T => f b) hleft_comp_right
      rw [hcompat]
      show right (algebraMap B C b) ∈ closure (J.map right : Set T)
      exact subset_closure (Ideal.mem_map_of_mem right (hKJ hb))
    have hU : Ideal.closure (K.map (algebraMap B A)) ≤ Q.comap left := by
      show closure (K.map (algebraMap B A) : Set A) ⊆ (Q.comap left : Set A)
      exact closure_minimal (fun a ha => hKmap ha) hpreclosed
    exact Ideal.map_le_iff_le_comap.mpr hU
  have hKernel (J : Ideal C) (hJ : IsOpen (J : Set C)) :
      ∃ U : OA, TopologicalRing.projectionKernel (B := B) (A := A) (C := C)
        (fun i : OA => i.1) (fun j : OC => j.1) bA bC
        U ⟨J, hJ⟩ = Ideal.closure (J.map right) := by
    obtain ⟨K, hK, hKJ⟩ :=
      (IsLinearTopology.hasBasis_open_ideal (R := B)).mem_iff.mp
        ((hJ.preimage hBC).mem_nhds (by simp))
    let U : Ideal A := Ideal.closure (K.map (algebraMap B A))
    have hU : IsOpen (U : Set A) := hBA.1 K hK
    have hbound := closureMapBound K J fun b hb => hKJ hb
    have hkernel :
        TopologicalRing.projectionKernel (B := B) (A := A) (C := C)
          (fun i : OA => i.1) (fun j : OC => j.1) bA bC
          ⟨U, hU⟩ ⟨J, hJ⟩ = Ideal.closure (J.map right) := by
      apply SetLike.ext'
      rw [TopologicalRing.projectionKernel_eq_closure]
      have hsum : Ideal.map left U + Ideal.map right J ≤ Ideal.closure (J.map right) :=
        sup_le hbound (fun x hx => subset_closure hx)
      have hfirst :
          (Ideal.closure (Ideal.map left U + Ideal.map right J) : Set T) ⊆
            (Ideal.closure (J.map right) : Set T) :=
        closure_minimal (SetLike.coe_subset_coe.mpr hsum) isClosed_closure
      have hsecond :
          (Ideal.closure (J.map right) : Set T) ⊆
            (Ideal.closure (Ideal.map left U + Ideal.map right J) : Set T) :=
        closure_mono (SetLike.coe_subset_coe.mpr le_sup_right)
      exact Set.Subset.antisymm hfirst hsecond
    exact ⟨⟨U, hU⟩, hkernel⟩
  show RingHom.IsTaut right
  constructor
  · intro J hJ
    obtain ⟨U, hkernel⟩ := hKernel J hJ
    simpa only [hkernel] using TopologicalRing.isOpen_projectionKernel
      (B := B) (A := A) (C := C) (fun i : OA => i.1) (fun j : OC => j.1)
      bA bC U ⟨J, hJ⟩
  · apply hproj.to_hasBasis
    · intro ij _
      refine ⟨ij.2.1, ij.2.2, ?_⟩
      rw [TopologicalRing.projectionKernel_eq_closure]
      show closure ((Ideal.map right ij.2.1 : Ideal T) : Set T) ⊆
        closure ((Ideal.map left ij.1.1 + Ideal.map right ij.2.1 : Ideal T) : Set T)
      exact closure_mono (SetLike.coe_subset_coe.mpr le_sup_right)
    · intro J hJ
      obtain ⟨U, hkernel⟩ := hKernel J hJ
      refine ⟨(U, ⟨J, hJ⟩), trivial, ?_⟩
      rw [hkernel]


/-- A continuous algebra isomorphism `M ≃ₐ[B] N` induces a continuous isomorphism
`M ⊗[B] C ≃ₐ[B] N ⊗[B] C` for the tensor product topologies. -/
private theorem continuous_tensorProduct_congr_left
    {B M N C : Type*} [CommRing B] [CommRing M] [CommRing N] [CommRing C]
    [Algebra B M] [Algebra B N] [Algebra B C] [TopologicalSpace M] [TopologicalSpace N]
    [TopologicalSpace C] (e : M ≃ₐ[B] N) (he : Continuous e) :
    @Continuous (M ⊗[B] C) (N ⊗[B] C) (TopologicalRing.tensorProductTopology (R := B))
      (TopologicalRing.tensorProductTopology (R := B))
      (Algebra.TensorProduct.congr e (AlgEquiv.refl : C ≃ₐ[B] C)) := by
  let : TopologicalSpace (M ⊗[B] C) := TopologicalRing.tensorProductTopology (R := B)
  let : TopologicalSpace (N ⊗[B] C) := TopologicalRing.tensorProductTopology (R := B)
  have : IsTopologicalAddGroup (M ⊗[B] C) :=
    (TopologicalRing.tensorProductAddGroupFilterBasis (R := B) (M := M)
      (N := C)).isTopologicalAddGroup
  have : IsTopologicalAddGroup (N ⊗[B] C) :=
    (TopologicalRing.tensorProductAddGroupFilterBasis (R := B) (M := N)
      (N := C)).isTopologicalAddGroup
  let eS := Algebra.TensorProduct.congr e (AlgEquiv.refl : C ≃ₐ[B] C)
  apply continuous_of_continuousAt_zero eS.toAddMonoidHom
  apply (TopologicalRing.hasBasis_tensorProductTopology
    (R := B) (M := N) (N := C)).tendsto_right_iff.mpr
  intro i hi
  let P : Submodule B M := i.1.1.comap e.toLinearMap
  have hPopen : IsOpen (P : Set M) := he.isOpen_preimage (i.1.1 : Set N) i.1.2
  let i₀ : TopologicalRing.TensorProductSubmoduleIndex (R := B) (M := M) (N := C) :=
    (⟨P, hPopen⟩, i.2)
  let fP : P →ₗ[B] i.1.1 := {
    toFun := fun x => ⟨e x.1, x.2⟩
    map_add' := by intro x y; ext; simp
    map_smul' := by intro r x; ext; simp }
  have hcompL :
      eS.toLinearEquiv.toLinearMap.comp (TensorProduct.map P.subtype LinearMap.id) =
        (TensorProduct.map i.1.1.subtype LinearMap.id).comp
          (TensorProduct.map fP LinearMap.id) := by
    ext x y
    simp [eS, fP]
  have hcompR :
      eS.toLinearEquiv.toLinearMap.comp (TensorProduct.map LinearMap.id i.2.1.subtype) =
        (TensorProduct.map LinearMap.id i.2.1.subtype).comp
          (TensorProduct.map e.toLinearMap LinearMap.id) := by
    ext x y
    simp [eS]
  have hsub : ∀ x : M ⊗[B] C,
      x ∈ TopologicalRing.tensorProductSubmodule P i.2.1 →
        eS x ∈ TopologicalRing.tensorProductSubmodule i.1.1 i.2.1 := by
    intro x hx
    change x ∈ LinearMap.range (TensorProduct.map P.subtype LinearMap.id) ⊔
        LinearMap.range (TensorProduct.map LinearMap.id i.2.1.subtype) at hx
    rcases Submodule.mem_sup.mp hx with ⟨x₁, hx₁, x₂, hx₂, hxsum⟩
    rw [← hxsum]
    change eS (x₁ + x₂) ∈
      LinearMap.range (TensorProduct.map i.1.1.subtype LinearMap.id) ⊔
        LinearMap.range (TensorProduct.map LinearMap.id i.2.1.subtype)
    rw [map_add]
    refine (LinearMap.range (TensorProduct.map i.1.1.subtype LinearMap.id) ⊔
      LinearMap.range (TensorProduct.map LinearMap.id i.2.1.subtype)).add_mem ?_ ?_
    · obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hx₁
      exact Submodule.mem_sup_left (LinearMap.mem_range.mpr
        ⟨TensorProduct.map fP LinearMap.id z, (LinearMap.congr_fun hcompL z).symm⟩)
    · obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hx₂
      exact Submodule.mem_sup_right (LinearMap.mem_range.mpr
        ⟨TensorProduct.map e.toLinearMap LinearMap.id z, (LinearMap.congr_fun hcompR z).symm⟩)
  filter_upwards [
    (TopologicalRing.hasBasis_tensorProductTopology
      (R := B) (M := M) (N := C)).mem_of_mem (i := i₀) trivial] with x hx
  exact hsub x hx

set_option synthInstance.maxHeartbeats 80000 in
/-- The common core of the completed base change statements: the completed tensor product
`A ⊗̂_B C` is adic Noetherian, and `C → A ⊗̂_B C` is a finite type adic algebra, whose rig
property `P` is transported from the base change of `adicFiniteTypeAlgebra` along any
completed base change functor. -/
private theorem completedTensorProduct_baseChange_core
    {B A C : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B] [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
    [IsLinearTopology C C] [Algebra B A] [Algebra B C] [IsNoetherianRing B]
    [IsNoetherianRing A] [IsNoetherianRing C]
    (hB : TopologicalRing.IsAdic B) (hA : TopologicalRing.IsAdic A)
    (hC : TopologicalRing.IsAdic C)
    (hBA : Continuous (algebraMap B A)) (hBC : Continuous (algebraMap B C))
    (hQ : RingHom.IsAdic (algebraMap B C))
    (hft : Rig.FiniteTypeAdicAlgebraForEveryIdeal (algebraMap B A))
    (I : Ideal B) (hI : TopologicalRing.IsIdealOfDefinition I)
    (P : AdicFiniteTypeAlgebra C (I.map (algebraMap B C)) → Prop)
    (hP : ∀ BC : Rig.CompletedBaseChange
      (A₁ := B) (A₂ := C) (I₁ := I) (I₂ := I.map (algebraMap B C)),
      P (BC.functor.obj (Rig.adicFiniteTypeAlgebra (algebraMap B A) hft I hI))) :
    TopologicalRing.IsAdic (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C)) ∧
      IsNoetherianRing (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C)) ∧
      ∃ _ : Continuous
        (algebraMap C (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C))),
      ∃ hftT : Rig.FiniteTypeAdicAlgebraForEveryIdeal
        (algebraMap C (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C))),
      ∃ hdef : TopologicalRing.IsIdealOfDefinition (I.map (algebraMap B C)),
        P (Rig.adicFiniteTypeAlgebra (algebraMap C
          (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C))) hftT _ hdef) := by
  classical
  let T := TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C)
  obtain ⟨IB, hIBdef, _⟩ := hB.1
  obtain ⟨IA, hIAdef, _⟩ := hA.1
  obtain ⟨IC, hICdef, hICadic⟩ := hC.1
  have hBfg : ∃ I : Ideal B, TopologicalRing.IsIdealOfDefinition I ∧ I.FG :=
    ⟨IB, hIBdef, Ideal.fg_of_isNoetherianRing IB⟩
  have hAfg : ∃ I : Ideal A, TopologicalRing.IsIdealOfDefinition I ∧ I.FG :=
    ⟨IA, hIAdef, Ideal.fg_of_isNoetherianRing IA⟩
  have hCfg : ∃ I : Ideal C, TopologicalRing.IsIdealOfDefinition I ∧ I.FG :=
    ⟨IC, hICdef, Ideal.fg_of_isNoetherianRing IC⟩
  have hTadic : TopologicalRing.IsAdic T :=
    TopologicalRing.completedTensorProduct_isAdic
      hBA hBC hA.1 hAfg hC.1 hCfg
  have hBW : TopologicalRing.IsWeaklyPreAdmissible B :=
    ⟨IB, hIBdef.1, fun _ hx => isTopologicallyNilpotent_of_mem_isIdealOfDefinition hIBdef hx⟩
  have hTFAE := Rig.adicFiniteType_tfae
    (algebraMap B A) hBA hB hA hBfg hAfg
  have hTautAndFT := (hTFAE.out 6 1).mp hft
  have hTaut := RingHom.isTaut_of_isAdic
    (algebraMap B A) hBA hTautAndFT.1
  have hRed := Rig.isFiniteTypeOnReductions_of_isTaut_of_isTopologicallyOfFiniteType
    (algebraMap B A) hBA hBW hTaut hTautAndFT.2
  have hFinite : ∃ h : topologicalNilradical B ≤
      (topologicalNilradical A).comap (algebraMap B A),
      (Ideal.quotientMap (topologicalNilradical A) (algebraMap B A) h).FiniteType :=
    ⟨_, hRed⟩
  let : IsNoetherianRing T :=
    TopologicalRing.completedTensorProduct_isNoetherianRing
      hBA hBC hA.1 hC.1 hFinite
  let I₂ : Ideal C := I.map (algebraMap B C)
  have hmap : (I ^ 1).map (algebraMap B C) ≤ I₂ := by
    simp [I₂]
  have hI₂fg : I₂.FG := Ideal.fg_of_isNoetherianRing I₂
  let BC : Rig.CompletedBaseChange
      (A₁ := B) (A₂ := C) (I₁ := I) (I₂ := I₂) :=
    Rig.completedBaseChange I I₂ 1 (by decide) hmap hI₂fg
  let B₁ := Rig.adicFiniteTypeAlgebra (algebraMap B A) hft I hI
  let eA : A ≃+* B₁.carrier := {
    toFun := fun x => x
    invFun := fun x => x
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl
  }
  let eAB : A ≃ₐ[B] B₁.carrier := {
    toRingEquiv := eA
    commutes' := fun _ => rfl
  }
  have hcarrier : B₁.carrier = A := rfl
  let : TopologicalSpace B₁.carrier := hcarrier.symm ▸
    (inferInstance : TopologicalSpace A)
  have heAcont : Continuous eA := by
    show Continuous (fun x : A => x)
    exact continuous_id
  have heABsymmcont : Continuous eAB.symm := by
    show Continuous (fun x : B₁.carrier => eA.symm x)
    exact continuous_id
  let eS : (A ⊗[B] C) ≃ₐ[B] (B₁.carrier ⊗[B] C) :=
    Algebra.TensorProduct.congr eAB (AlgEquiv.refl : C ≃ₐ[B] C)
  let : UniformSpace (A ⊗[B] C) :=
    TopologicalRing.tensorProductUniformSpace (R := B) (M := A) (N := C)
  let : UniformSpace (B₁.carrier ⊗[B] C) :=
    TopologicalRing.tensorProductUniformSpace (R := B) (M := B₁.carrier) (N := C)
  let : TopologicalSpace (A ⊗[B] C) :=
    (inferInstance : UniformSpace (A ⊗[B] C)).toTopologicalSpace
  let : TopologicalSpace (B₁.carrier ⊗[B] C) :=
    (inferInstance : UniformSpace (B₁.carrier ⊗[B] C)).toTopologicalSpace
  let : IsTopologicalRing B₁.carrier := by
    show IsTopologicalRing A
    exact inferInstance
  let : IsLinearTopology B₁.carrier B₁.carrier := by
    show IsLinearTopology A A
    exact inferInstance
  let : IsUniformAddGroup (A ⊗[B] C) := TopologicalRing.tensorProduct_isUniformAddGroup
  let : IsUniformAddGroup (B₁.carrier ⊗[B] C) := TopologicalRing.tensorProduct_isUniformAddGroup
  let : IsTopologicalRing (A ⊗[B] C) := TopologicalRing.tensorProduct_isTopologicalRing
  let : IsTopologicalRing (B₁.carrier ⊗[B] C) := TopologicalRing.tensorProduct_isTopologicalRing
  have heScont : Continuous eS := continuous_tensorProduct_congr_left eAB heAcont
  have heSsymmcont : Continuous eS.symm :=
    continuous_tensorProduct_congr_left eAB.symm heABsymmcont
  have hIAadic : _root_.IsAdic (I.map (algebraMap B A)) :=
    isAdic_map_of_idealOfDefinition hI hTautAndFT.1
  have hI₂adic : _root_.IsAdic I₂ := isAdic_map_of_idealOfDefinition hI hQ
  have hIAdef : TopologicalRing.IsIdealOfDefinition (I.map (algebraMap B A)) :=
    isIdealOfDefinition_of_isAdic hIAadic
  have hI₂def : TopologicalRing.IsIdealOfDefinition I₂ :=
    isIdealOfDefinition_of_isAdic hI₂adic
  let J₁ : Ideal (B₁.carrier ⊗[B] C) :=
    Ideal.map (Algebra.TensorProduct.includeRight : C →ₐ[B] B₁.carrier ⊗[B] C).toRingHom I₂
  have hleft :
      Ideal.map (Algebra.TensorProduct.includeLeft : B₁.carrier →ₐ[B]
        B₁.carrier ⊗[B] C).toRingHom (I.map (algebraMap B B₁.carrier)) = J₁ := by
    calc
      _ = Ideal.map
          ((Algebra.TensorProduct.includeLeft : B₁.carrier →ₐ[B]
            B₁.carrier ⊗[B] C).toRingHom.comp (algebraMap B B₁.carrier)) I := by
            rw [Ideal.map_map]
      _ = Ideal.map
          ((Algebra.TensorProduct.includeRight : C →ₐ[B] B₁.carrier ⊗[B] C).toRingHom.comp
            (algebraMap B C)) I := by
            congr 1
            ext b
            simp
      _ = J₁ := by rw [← Ideal.map_map]
  let K₁ : Ideal (B₁.carrier ⊗[B] C) :=
    Ideal.map (Algebra.TensorProduct.includeLeft : B₁.carrier →ₐ[B]
      B₁.carrier ⊗[B] C).toRingHom (I.map (algebraMap B B₁.carrier)) + J₁
  have hK₁eq : K₁ = J₁ := by
    show Ideal.map (Algebra.TensorProduct.includeLeft : B₁.carrier →ₐ[B]
      B₁.carrier ⊗[B] C).toRingHom (I.map (algebraMap B B₁.carrier)) + J₁ = J₁
    rw [hleft]
    simp
  have hK₁adic : _root_.IsAdic K₁ := tensorProduct_basis_is_adic
    (B := B)
    (I.map (algebraMap B B₁.carrier)) hIAdef (I.map (algebraMap B B₁.carrier)) hIAdef hIAadic
    I₂ hI₂def I₂ hI₂def hI₂adic
  have hJ₁adic : _root_.IsAdic J₁ := hK₁eq ▸ hK₁adic
  have heSringcont : Continuous eS.toRingEquiv := heScont
  have heSringSymmcont : Continuous eS.toRingEquiv.symm := heSsymmcont
  let eComp := UniformSpace.Completion.mapRingEquiv
    eS.toRingEquiv heSringcont heSringSymmcont
  let eAdic := completedTensorProduct_adicCompletionEquiv J₁ hJ₁adic
  let eT : T ≃+* (BC.functor.obj B₁).carrier :=
    (eComp.trans eAdic).trans
        (BC.completedTensorProductEquiv B₁).symm
  let : Algebra C T := (algebraMap C T).toAlgebra
  let eAlg : T ≃ₐ[C] (BC.functor.obj B₁).carrier := {
    toRingEquiv := eT
    commutes' := by
      intro c
      apply (BC.completedTensorProductEquiv B₁).injective
      rw [BC.algebraMap_completedTensorProductEquiv]
      show eAdic (eComp ((Algebra.TensorProduct.includeRight c : A ⊗[B] C) : T)) = _
      have hcomp :
          eComp ((Algebra.TensorProduct.includeRight c : A ⊗[B] C) : T) =
            ((Algebra.TensorProduct.includeRight c : B₁.carrier ⊗[B] C) :
              TopologicalRing.CompletedTensorProduct (R := B) (M := B₁.carrier) (N := C)) := by
        show UniformSpace.Completion.map eS.toRingEquiv
          (↑(Algebra.TensorProduct.includeRight c : A ⊗[B] C)) = _
        rw [UniformSpace.Completion.map_coe
          (uniformContinuous_addMonoidHom_of_continuous heSringcont)]
        simp [eS]
      rw [hcomp]
      exact AdicCompletionBridge.adicCompletionRingEquiv_coe J₁ hJ₁adic
        (Algebra.TensorProduct.includeRight c) }
  let J_T : Ideal T := I₂.map (algebraMap C T)
  let J_BC : Ideal (BC.functor.obj B₁).carrier :=
    I₂.map (algebraMap C (BC.functor.obj B₁).carrier)
  have hJmap : J_BC = J_T.map eT := by
    calc
      J_BC = I₂.map (algebraMap C (BC.functor.obj B₁).carrier) := rfl
      _ = I₂.map ((eT : T →+* (BC.functor.obj B₁).carrier).comp
          (algebraMap C T)) := by
            congr 1
            ext c
            exact (eAlg.commutes c).symm
      _ = J_T.map eT := by
        show I₂.map ((eT : T →+* (BC.functor.obj B₁).carrier).comp
          (algebraMap C T)) = (I₂.map (algebraMap C T)).map eT
        rw [← Ideal.map_map]
        rfl
  have hCompleteT : IsAdicComplete J_T T :=
    (IsAdicComplete.congr_ringEquiv J_T eT).mp (hJmap ▸ (BC.functor.obj B₁).property.1)
  have hFiniteT : Algebra.FiniteType (C ⧸ I₂) (T ⧸ J_T) := by
    let eQuotRing : (T ⧸ J_T) ≃+* ((BC.functor.obj B₁).carrier ⧸ J_BC) :=
      Ideal.quotientEquiv J_T J_BC eT hJmap
    let eQuot : (T ⧸ J_T) ≃ₐ[C ⧸ I₂]
        ((BC.functor.obj B₁).carrier ⧸ J_BC) := {
      toRingEquiv := eQuotRing
      commutes' := by
        intro c
        obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
        show Ideal.Quotient.mk J_BC (eT (algebraMap C T c)) =
          Ideal.Quotient.mk J_BC (algebraMap C (BC.functor.obj B₁).carrier c)
        exact congrArg (Ideal.Quotient.mk J_BC) (eAlg.commutes c) }
    exact Algebra.FiniteType.equiv (BC.functor.obj B₁).property.2 eQuot.symm
  obtain ⟨I_T, hI_Tdef, hI_Tadic⟩ := hTadic.1
  have hTfg : ∃ J : Ideal T, TopologicalRing.IsIdealOfDefinition J ∧ J.FG :=
    ⟨I_T, hI_Tdef, Ideal.fg_of_isNoetherianRing I_T⟩
  have hCT : Continuous (algebraMap C T) := by
    show Continuous ((UniformSpace.Completion.coeRingHom :
      (A ⊗[B] C) →+* T).comp
        (Algebra.TensorProduct.includeRight : C →ₐ[B] A ⊗[B] C).toRingHom)
    apply (UniformSpace.Completion.continuous_coe (A ⊗[B] C)).comp
    show Continuous (fun c : C => (1 : A) ⊗ₜ[B] c)
    exact TopologicalRing.continuous_const_tmul (R := B) (M := A) (N := C) 1
  have hCTtaut : RingHom.IsTaut (algebraMap C T) :=
    completedTensorProduct_rightMap_isTaut hTaut hBC
  let : T2Space T := hTadic.2.1
  let : @CompleteSpace T (IsTopologicalAddGroup.rightUniformSpace T) := hTadic.2.2
  have hCTadic : RingHom.IsAdic (algebraMap C T) :=
    RingHom.isAdic_of_isTaut (algebraMap C T) hCT hCTtaut
      ⟨IC, Ideal.fg_of_isNoetherianRing IC, hICadic⟩
  have hI₂mapadic : _root_.IsAdic (I₂.map (algebraMap C T)) :=
    isAdic_map_of_idealOfDefinition hI₂def hCTadic
  have hTFAE_C := Rig.adicFiniteType_tfae
    (algebraMap C T) hCT hC hTadic hCfg hTfg
  have hSome : Rig.FiniteTypeAdicAlgebraForSomeIdeal
      (algebraMap C T) := by
    refine ⟨I₂, hI₂def, hI₂mapadic, ?_⟩
    let : Algebra C T := (algebraMap C T).toAlgebra
    let : Algebra (C ⧸ I₂) (T ⧸ J_T) :=
      (Ideal.quotientMap J_T (algebraMap C T)
        (Ideal.map_le_iff_le_comap.mp (le_rfl : J_T ≤ J_T))).toAlgebra
    have hAlgEq :
        (Ideal.Quotient.algebraQuotientMapQuotient : Algebra (C ⧸ I₂) (T ⧸ J_T)) =
          (Ideal.quotientMap J_T (algebraMap C T)
            (Ideal.map_le_iff_le_comap.mp (le_rfl : J_T ≤ J_T))).toAlgebra := by
      apply Algebra.algebra_ext
      intro c
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
      rfl
    exact ⟨hCompleteT, hAlgEq ▸ hFiniteT⟩
  have hftT : Rig.FiniteTypeAdicAlgebraForEveryIdeal
      (algebraMap C T) := (hTFAE_C.out 5 6).mp hSome
  let D := Rig.adicFiniteTypeAlgebra (algebraMap C T) hftT I₂ hI₂def
  let eD : D ≅ BC.functor.obj B₁ :=
    ObjectProperty.isoMk _ (CommAlgCat.isoMk eAlg)
  let objIso := fun (Z : AdicFiniteTypeAlgebra B I) =>
    replaceObjectIso BC.functor B₁ D eD Z
  let Fnew : AdicFiniteTypeAlgebra B I ⥤ AdicFiniteTypeAlgebra C I₂ := {
    obj := fun Z => if h : Z = B₁ then D else BC.functor.obj Z
    map := fun {Z W} f => (objIso Z).hom ≫ BC.functor.map f ≫ (objIso W).inv
    map_id := by intro Z; simp
    map_comp := by intro Z W V f g; simp }
  let objAlgEquiv := fun (Z : AdicFiniteTypeAlgebra B I) =>
    CommAlgCat.algEquivOfIso (asIso (objIso Z).hom.hom)
  let newEquiv := fun (Z : AdicFiniteTypeAlgebra B I) =>
    (objAlgEquiv Z).toRingEquiv.trans (BC.completedTensorProductEquiv Z)
  let BCnew : Rig.CompletedBaseChange
      (A₁ := B) (A₂ := C) (I₁ := I) (I₂ := I₂) := {
    functor := Fnew
    completedTensorProductEquiv := newEquiv
    algebraMap_completedTensorProductEquiv := by
      intro Z c
      dsimp [newEquiv]
      rw [(objAlgEquiv Z).commutes c]
      exact BC.algebraMap_completedTensorProductEquiv Z c
    map_completedTensorProductEquiv := by
      intro Z W f x
      have hnatCat : (objIso Z).hom ≫ BC.functor.map f =
          Fnew.map f ≫ (objIso W).hom := by
        simp [Fnew, Category.assoc]
      have hnat (y : (Fnew.obj Z).carrier) :
          (objAlgEquiv W) ((AdicFiniteTypeAlgebra.hom (Fnew.map f)) y) =
            (AdicFiniteTypeAlgebra.hom (BC.functor.map f)) ((objAlgEquiv Z) y) := by
        show (CategoryTheory.ConcreteCategory.hom (objIso W).hom.hom)
            ((AdicFiniteTypeAlgebra.hom (Fnew.map f)) y) =
          (AdicFiniteTypeAlgebra.hom (BC.functor.map f))
            ((CategoryTheory.ConcreteCategory.hom (objIso Z).hom.hom) y)
        rw [← CategoryTheory.ConcreteCategory.comp_apply,
          ← CategoryTheory.ConcreteCategory.comp_apply]
        exact congrArg (fun g => (AdicFiniteTypeAlgebra.hom g) y) hnatCat.symm
      show ((objAlgEquiv W).toRingEquiv.trans (BC.completedTensorProductEquiv W))
        ((AdicFiniteTypeAlgebra.hom (Fnew.map f))
          (((objAlgEquiv Z).toRingEquiv.trans (BC.completedTensorProductEquiv Z)).symm
            (AdicCompletion.of (Rig.baseChangedIdeal Z)
              (Rig.baseChangedAlgebra Z) x))) = _
      rw [RingEquiv.trans_apply]
      show (BC.completedTensorProductEquiv W)
        ((objAlgEquiv W) ((AdicFiniteTypeAlgebra.hom (Fnew.map f))
          (((objAlgEquiv Z).toRingEquiv.trans (BC.completedTensorProductEquiv Z)).symm
            (AdicCompletion.of (Rig.baseChangedIdeal Z)
              (Rig.baseChangedAlgebra Z) x)))) = _
      rw [hnat, RingEquiv.symm_trans_apply]
      show (BC.completedTensorProductEquiv W)
        ((AdicFiniteTypeAlgebra.hom (BC.functor.map f))
          ((objAlgEquiv Z).toRingEquiv
            ((objAlgEquiv Z).toRingEquiv.symm
              ((BC.completedTensorProductEquiv Z).symm
                (AdicCompletion.of (Rig.baseChangedIdeal Z)
                  (Rig.baseChangedAlgebra Z) x))))) = _
      rw [RingEquiv.apply_symm_apply]
      exact BC.map_completedTensorProductEquiv f x }
  have hPD : P D := by
    have hobj : BCnew.functor.obj B₁ = D := by simp [BCnew, Fnew]
    exact hobj ▸ hP BCnew
  exact ⟨hTadic, inferInstance, hCT, hftT, hI₂def, hPD⟩


/-- Rig-smoothness (Tag 0GCJ) is stable under base change by adic morphisms (Tag 0GBR) in the
sense of Remark 0GBG: if `B → A` is rig-smooth and `B → C` is adic, both arrows of
`WAdm^{Noeth}`, then the completed tensor product `A ⊗̂_B C` is again Noetherian adic and
rig-smooth over `C`. -/
@[stacks 0GCL]
public theorem rigSmooth_completedTensorProduct_of_isAdic
    {B A C : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B] [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
    [IsLinearTopology C C] [Algebra B A] [Algebra B C] [IsNoetherianRing B]
    [IsNoetherianRing A] [IsNoetherianRing C]
    (hB : TopologicalRing.IsAdic B) (hA : TopologicalRing.IsAdic A)
    (hC : TopologicalRing.IsAdic C)
    (hBA : Continuous (algebraMap B A)) (hBC : Continuous (algebraMap B C))
    (hP : RingHom.IsRigSmoothArrow (algebraMap B A))
    (hQ : RingHom.IsAdic (algebraMap B C)) :
    TopologicalRing.IsAdic (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C)) ∧
      IsNoetherianRing (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C)) ∧
      RingHom.IsRigSmoothArrow
        (algebraMap C (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C))) := by
  obtain ⟨-, hft, I, hI, hSmooth⟩ : Continuous (algebraMap B A) ∧
      ∃ hft : Rig.FiniteTypeAdicAlgebraForEveryIdeal (algebraMap B A), ∃ I : Ideal B,
        ∃ hI : TopologicalRing.IsIdealOfDefinition I,
          Rig.IsRigSmooth (Rig.adicFiniteTypeAlgebra (algebraMap B A) hft I hI) := hP
  obtain ⟨hTadic, hNoeth, hCT, hftT, hdef, hD⟩ := completedTensorProduct_baseChange_core
    hB hA hC hBA hBC hQ hft I hI Rig.IsRigSmooth fun BC =>
      Rig.isRigSmooth_completedBaseChange rfl BC _ hSmooth
  exact ⟨hTadic, hNoeth, hCT, hftT, _, hdef, hD⟩


/-- Rig-étaleness (Tag 0GCV) is stable under base change by adic morphisms (Tag 0GBR) in the
sense of Remark 0GBG: if `B → A` is rig-étale and `B → C` is adic, both arrows of
`WAdm^{Noeth}`, then the completed tensor product `A ⊗̂_B C` is again Noetherian adic and
rig-étale over `C`. -/
@[stacks 0GCW]
public theorem rigEtale_completedTensorProduct_of_isAdic
    {B A C : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B] [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
    [IsLinearTopology C C] [Algebra B A] [Algebra B C] [IsNoetherianRing B]
    [IsNoetherianRing A] [IsNoetherianRing C]
    (hB : TopologicalRing.IsAdic B) (hA : TopologicalRing.IsAdic A)
    (hC : TopologicalRing.IsAdic C)
    (hBA : Continuous (algebraMap B A)) (hBC : Continuous (algebraMap B C))
    (hP : RingHom.IsRigEtaleArrow (algebraMap B A))
    (hQ : RingHom.IsAdic (algebraMap B C)) :
    TopologicalRing.IsAdic (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C)) ∧
      IsNoetherianRing (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C)) ∧
      RingHom.IsRigEtaleArrow
        (algebraMap C (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C))) := by
  obtain ⟨-, hft, I, hI, hcA', hfinA', hEtale⟩ : Continuous (algebraMap B A) ∧
      RingHom.IsRigEtale (algebraMap B A) := hP
  obtain ⟨hTadic, hNoeth, hCT, hftT, hdef, hD⟩ := completedTensorProduct_baseChange_core
    hB hA hC hBA hBC hQ hft I hI Rig.IsRigEtale fun BC =>
      Rig.isRigEtale_completedBaseChangeFunctor rfl BC _ hEtale
  have pD := Rig.isAdicFiniteType_of_finiteTypeAdicAlgebraForEveryIdeal
    (algebraMap C _) hftT _ hdef
  exact ⟨hTadic, hNoeth, hCT, hftT, _, hdef, pD.1, pD.2, hD⟩


/-- If rig-smoothness is local on Noetherian rings (Tag 0GCK), then it is stable under base
change by adic morphisms in the sense of `TopologicalRing.IsStableUnderBaseChangeBy`. -/
public theorem rigSmooth_isStableUnderBaseChangeByAdic
    (hlocal : TopologicalRing.PropertyIsLocalNoetherian.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) =>
        RingHom.IsRigSmoothArrow φ)) :
    TopologicalRing.IsStableUnderBaseChangeBy.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) =>
        RingHom.IsRigSmoothArrow φ)
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) =>
        RingHom.IsAdic φ) where
  isLocalP := hlocal
  isLocalQ := isAdic_propertyIsLocalNoetherian
  baseChange hB hA hC hBA hBC hP hQ :=
    rigSmooth_completedTensorProduct_of_isAdic hB hA hC hBA hBC hP hQ

/-- If rig-étaleness is local on Noetherian rings (Tag 0AQL), then it is stable under base
change by adic morphisms in the sense of `TopologicalRing.IsStableUnderBaseChangeBy`. -/
public theorem rigEtale_isStableUnderBaseChangeByAdic
    (hlocal : TopologicalRing.PropertyIsLocalNoetherian.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) =>
        RingHom.IsRigEtaleArrow φ)) :
    TopologicalRing.IsStableUnderBaseChangeBy.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) =>
        RingHom.IsRigEtaleArrow φ)
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) =>
        RingHom.IsAdic φ) where
  isLocalP := hlocal
  isLocalQ := isAdic_propertyIsLocalNoetherian
  baseChange hB hA hC hBA hBC hP hQ :=
    rigEtale_completedTensorProduct_of_isAdic hB hA hC hBA hBC hP hQ

end TopologicalRing

end
