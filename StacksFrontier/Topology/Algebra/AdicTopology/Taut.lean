module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.Algebra.UniformRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Algebra.AdicTopology.AdmissibleRings
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissible
public import StacksFrontier.Topology.Algebra.OpenMapping

/-!
# Taut ring maps

A continuous homomorphism `φ : A →+* B` of linearly topologized rings is *taut* when the
closure of the extension of every open ideal of `A` is open in `B` and these closed extended
ideals form a neighbourhood basis of zero.  This file defines tautness, characterises it
through weak ideals of definition, and establishes its permanence properties: composition,
cancellation, the completion map, and what tautness forces on the target (countably generated
topology, weak pre-admissibility, pre-admissibility).  The last group of lemmas treats a taut
map with dense range, which is automatically open and surjective with complete target.

## References

* [Stacks Project, Tag 0AMX](https://stacks.math.columbia.edu/tag/0AMX)
* [Stacks Project, Tag 0AMY](https://stacks.math.columbia.edu/tag/0AMY)
* [Stacks Project, Tag 0APT](https://stacks.math.columbia.edu/tag/0APT)
* [Stacks Project, Tag 0GX2](https://stacks.math.columbia.edu/tag/0GX2)
* [Stacks Project, Tag 0GX3](https://stacks.math.columbia.edu/tag/0GX3)
* [Stacks Project, Tag 0GX4](https://stacks.math.columbia.edu/tag/0GX4)
* [Stacks Project, Tag 0GX6](https://stacks.math.columbia.edu/tag/0GX6)
* [Stacks Project, Tag 0GX7](https://stacks.math.columbia.edu/tag/0GX7)
* [Stacks Project, Tag 0GX8](https://stacks.math.columbia.edu/tag/0GX8)
-/

@[expose] public section

namespace RingHom

section

/-- A ring homomorphism is *taut* if the closure of the extension of each open source ideal is
open, and the resulting closed extended ideals form a neighbourhood basis of zero in the target.

For the Stacks definition, the source and target are linearly topologized rings and the
homomorphism is continuous; those ambient hypotheses are imposed by statements using this
predicate. -/
@[stacks 0AMX]
public abbrev IsTaut {A B : Type*} [CommRing A] [TopologicalSpace A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] (φ : A →+* B) : Prop :=
  (∀ I : Ideal A, IsOpen (I : Set A) → IsOpen (Ideal.closure (I.map φ) : Set B)) ∧
    (nhds (0 : B)).HasBasis (fun I : Ideal A ↦ IsOpen (I : Set A))
      (fun I : Ideal A ↦ (Ideal.closure (I.map φ) : Set B))

end

section

open Filter

/-- A taut continuous homomorphism sends a weak ideal of definition to the closure of its
extension, which is again a weak ideal of definition. -/
private theorem isWeakIdealOfDefinition_closure_map {A B : Type*} [CommRing A]
    [TopologicalSpace A] [IsLinearTopology A A] [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] [IsLinearTopology B B] (φ : A →+* B) (hφ : Continuous φ)
    (hφ_taut : RingHom.IsTaut φ) {I : Ideal A} (hI : TopologicalRing.IsWeakIdealOfDefinition I) :
    TopologicalRing.IsWeakIdealOfDefinition (Ideal.closure (I.map φ)) :=
  ⟨hφ_taut.1 I hI.1, fun _ hx ↦ IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mp
    (TopologicalRing.closure_map_le_topologicalNilradical φ hφ I
      (fun _ hy ↦ IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mpr (hI.2 _ hy)) hx)⟩

/-- A continuous homomorphism of weakly admissible topological rings is taut exactly when the
closed extensions of the weak ideals of definition are weak ideals of definition and form a
neighbourhood basis of zero in the target. -/
@[stacks 0AMY]
public theorem isTaut_iff_hasBasis_isWeakIdealOfDefinition
    {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B] (φ : A →+* B) (hφ : Continuous φ)
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hB : TopologicalRing.IsWeaklyAdmissible B) :
    RingHom.IsTaut φ ↔
      (∀ I : Ideal A, TopologicalRing.IsWeakIdealOfDefinition I →
        TopologicalRing.IsWeakIdealOfDefinition (Ideal.closure (I.map φ))) ∧
      (nhds (0 : B)).HasBasis
        (fun I : Ideal A ↦ TopologicalRing.IsWeakIdealOfDefinition I)
        (fun I : Ideal A ↦ (Ideal.closure (I.map φ) : Set B)) := by
  let hweak := TopologicalRing.hasBasis_nhds_zero_isWeakIdealOfDefinition hA
  have hcofinal (I : Ideal A) (hI : IsOpen (I : Set A)) :
      ∃ J : Ideal A, TopologicalRing.IsWeakIdealOfDefinition J ∧
        (Ideal.closure (J.map φ) : Set B) ⊆ (Ideal.closure (I.map φ) : Set B) := by
    obtain ⟨J, hJ, hJI⟩ := hweak.mem_iff.mp (hI.mem_nhds (zero_mem I))
    refine ⟨J, hJ, ?_⟩
    simpa only [Ideal.coe_closure] using closure_mono (Ideal.map_mono hJI)
  constructor
  · intro htaut
    exact ⟨fun I hI => isWeakIdealOfDefinition_closure_map φ hφ htaut hI,
      htaut.2.to_hasBasis hcofinal (fun I hI => ⟨I, hI.1, subset_rfl⟩)⟩
  · rintro ⟨_, hbasis⟩
    exact ⟨fun I hI =>
      (Ideal.closure (I.map φ)).toAddSubgroup.isOpen_of_mem_nhds
        (hbasis.mem_iff.mpr (hcofinal I hI)),
      hbasis.to_hasBasis (fun I hI => ⟨I, hI.1, subset_rfl⟩) hcofinal⟩

end

section

open Filter
open scoped Uniformity


private lemma isGroupComplete_of_completeSpace {A : Type*} [AddCommGroup A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [T2Space A]
    (hA : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)) :
    IsGroupComplete A := by
  let : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  refine ⟨inferInstance, ?_⟩
  intro F hF
  have hC : Cauchy F := by
    show F.NeBot ∧ F ×ˢ F ≤
      comap (fun p : A × A => p.2 + (-p.1)) (nhds (0 : A))
    have ht : Tendsto (fun p : A × A => p.2 + (-p.1)) (F ×ˢ F) (nhds (0 : A)) := by
      simpa [IsGroupCauchy, sub_eq_add_neg] using hF.2
    exact ⟨hF.1, (tendsto_iff_comap).1 ht⟩
  exact hA.complete hC

/-- The closure of the image `φ '' I` of an ideal `I` of `A`, which is an ideal of `B` when `φ`
has dense range. -/
public def closureImageIdeal {A B : Type*} [CommRing A] [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] (φ : A →+* B)
    (I : Ideal A) (hdense : DenseRange φ) : Ideal B where
  __ := (I.toAddSubgroup.map φ.toAddMonoidHom).topologicalClosure
  smul_mem' := by
    intro b x hx
    change x ∈ closure (φ '' (I : Set A)) at hx
    change b * x ∈ closure (φ '' (I : Set A))
    apply map_mem_closure₂' (fun b => continuous_const_mul b) (fun x => continuous_mul_const x)
      (hdense b) hx
    intro a ha i hi
    rcases ha with ⟨a, rfl⟩
    rcases hi with ⟨i, hiI, rfl⟩
    exact ⟨a * i, I.mul_mem_left a hiI, by simp⟩

private theorem ideal_closure_map_eq_closure_image
    {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (f : A →+* B) (hf : DenseRange f) (I : Ideal A) :
    (Ideal.closure (I.map f) : Set B) = closure (f '' (I : Set A)) := by
  let C : Ideal B := {
    carrier := closure (f '' (I : Set A))
    zero_mem' := subset_closure ⟨0, I.zero_mem, map_zero f⟩
    add_mem' := by
      intro x y hx hy
      apply map_mem_closure₂ continuous_add hx hy
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact ⟨a + b, I.add_mem ha hb, map_add f a b⟩
    smul_mem' := by
      intro b x hx
      apply map_mem_closure₂ continuous_mul (by rw [hf.closure_range]; simp) hx
      rintro _ ⟨a, rfl⟩ _ ⟨c, hc, rfl⟩
      exact ⟨a * c, I.mul_mem_left a hc, map_mul f a c⟩
  }
  apply Set.Subset.antisymm
  · rw [Ideal.coe_closure]
    exact closure_minimal (show I.map f ≤ C from Ideal.map_le_iff_le_comap.mpr
      (fun a ha => subset_closure ⟨a, ha, rfl⟩)) isClosed_closure
  · rw [Ideal.coe_closure]
    exact closure_mono (by rintro b ⟨a, ha, rfl⟩; exact Ideal.mem_map_of_mem f ha)

private lemma openMap_of_taut_dense {A B : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [T2Space A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [T2Space B] (φ : A →+* B) (hφ : Continuous φ)
    (hA : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hcount : (nhds (0 : A)).IsCountablyGenerated) (htaut : RingHom.IsTaut φ)
    (hdense : DenseRange φ) : IsOpenMap φ := by
  have hgroup : IsGroupComplete A := isGroupComplete_of_completeSpace hA
  have hlin : IsLinearlyTopologized A := by
    show (nhds (0 : A)).HasBasis
      (fun U : AddSubgroup A => IsOpen (U : Set A)) (fun U => (U : Set A))
    refine IsLinearTopology.hasBasis_open_ideal.to_hasBasis ?_ ?_
    · intro I hI
      exact ⟨I.toAddSubgroup, hI, Set.Subset.rfl⟩
    · intro U hU
      obtain ⟨I, hI, hIU⟩ :=
        IsLinearTopology.hasBasis_open_ideal.mem_iff.mp (hU.mem_nhds (zero_mem _))
      exact ⟨I, hI, hIU⟩
  rcases open_mapping_lemma (u := φ.toAddMonoidHom) hφ hgroup hlin hcount with
    ⟨hopen, _⟩ | ⟨⟨U, hUopen, hnd⟩, _⟩
  · exact hopen
  · obtain ⟨I, hIopen, hIU⟩ :=
      IsLinearTopology.hasBasis_open_ideal.mem_iff.mp (hUopen.mem_nhds (zero_mem _))
    have hclosureOpen : IsOpen (closure (φ '' (I : Set A))) := by
      rw [← ideal_closure_map_eq_closure_image φ hdense I]
      exact htaut.1 I hIopen
    have hnonemptyInterior : (0 : B) ∈ interior (closure (φ '' (U : Set A))) :=
      interior_maximal (closure_mono (Set.image_mono hIU)) hclosureOpen
        (subset_closure ⟨0, I.zero_mem, map_zero φ⟩)
    change IsNowhereDense (φ '' (U : Set A)) at hnd
    rw [IsNowhereDense] at hnd
    rw [hnd] at hnonemptyInterior
    simp at hnonemptyInterior

private lemma firstCountable_of_countable_nhds {A : Type*} [AddGroup A]
    [TopologicalSpace A] [IsTopologicalAddGroup A]
    (hcount : (nhds (0 : A)).IsCountablyGenerated) : FirstCountableTopology A := by
  let : IsCountablyGenerated (nhds (0 : A)) := hcount
  refine FirstCountableTopology.mk ?_
  intro a
  have hmap : IsCountablyGenerated (Filter.map (Homeomorph.addLeft a) (nhds (0 : A))) :=
    inferInstance
  rw [Homeomorph.map_nhds_eq] at hmap
  have hpoint : Homeomorph.addLeft a (0 : A) = a := by
    show a + 0 = a
    exact add_zero a
  rw [hpoint] at hmap
  exact hmap

private lemma complete_quotient_kernel {A B : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [T2Space A] [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] (φ : A →+* B)
    (hA : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hcount : (nhds (0 : A)).IsCountablyGenerated) (hsurj : Function.Surjective φ)
    (he : IsHomeomorph (RingHom.quotientKerEquivOfSurjective hsurj)) :
    @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B) := by
  let Q := A ⧸ RingHom.ker φ
  let e := RingHom.quotientKerEquivOfSurjective hsurj
  let : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  let : IsRightUniformAddGroup A := { uniformity_eq := rfl }
  let : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  let : FirstCountableTopology A := firstCountable_of_countable_nhds hcount
  let : CompleteSpace A := hA
  let : UniformSpace Q := IsTopologicalAddGroup.rightUniformSpace Q
  let : IsRightUniformAddGroup Q := { uniformity_eq := rfl }
  let : IsUniformAddGroup Q := isUniformAddGroup_of_addCommGroup
  have hQ : @CompleteSpace Q (IsTopologicalAddGroup.rightUniformSpace Q) :=
    QuotientAddGroup.completeSpace_right A (RingHom.ker φ).toAddSubgroup
  let : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace B
  let : IsRightUniformAddGroup B := { uniformity_eq := rfl }
  let : IsUniformAddGroup B := isUniformAddGroup_of_addCommGroup
  let hhomeo : Q ≃ₜ B := he.homeomorph e
  have hsymm : (hhomeo.symm : B → Q) = e.symm := by
    funext b
    apply e.injective
    calc
      e (hhomeo.symm b) = b := hhomeo.apply_symm_apply b
      _ = e (e.symm b) := (e.apply_symm_apply b).symm
  let ue : Q ≃ᵤ B :=
    { toEquiv := e.toEquiv
      uniformContinuous_toFun := uniformContinuous_addMonoidHom_of_continuous
        (f := e.toRingHom.toAddMonoidHom) hhomeo.continuous
      uniformContinuous_invFun := uniformContinuous_addMonoidHom_of_continuous
        (f := e.symm.toRingHom.toAddMonoidHom) (hsymm ▸ hhomeo.continuous_symm) }
  exact ue.completeSpace_iff.mp hQ

private lemma quotientKerEquiv_isHomeomorph {A B : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] [T2Space A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [T2Space B] (φ : A →+* B) (hφ : Continuous φ) (hopen : IsOpenMap φ)
    (hsurj : Function.Surjective φ) :
    IsHomeomorph (RingHom.quotientKerEquivOfSurjective hsurj) := by
  let e := RingHom.quotientKerEquivOfSurjective hsurj
  have hcomp : e ∘ Ideal.Quotient.mk (RingHom.ker φ) = φ := by
    funext a
    exact RingHom.quotientKerEquivOfSurjective_apply_mk hsurj a
  have hcont : Continuous e := by
    apply (QuotientRing.isOpenQuotientMap_mk (RingHom.ker φ)).isQuotientMap.continuous_iff.mpr
    exact hcomp ▸ hφ
  have hopenE : IsOpenMap e := by
    apply (QuotientRing.isOpenQuotientMap_mk (RingHom.ker φ)).isOpenMap_iff.mpr
    exact hcomp ▸ hopen
  exact ⟨hcont, hopenE, e.bijective⟩

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
  [IsLinearTopology A A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [IsLinearTopology B B] [T2Space B]

/-- A continuous taut map with dense image from a complete countably based linearly
topologized ring to a separated linearly topologized ring is open. -/
@[stacks 0APT "openness"]
public lemma isOpenMap_of_isTaut_of_denseRange (φ : A →+* B) (hφ : Continuous φ)
    (hA : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hcount : (nhds (0 : A)).IsCountablyGenerated) (htaut : RingHom.IsTaut φ)
    (hdense : DenseRange φ) : IsOpenMap φ :=
  openMap_of_taut_dense φ hφ hA hcount htaut hdense

/-- A continuous taut map with dense image under the completeness and countability hypotheses
is surjective. -/
@[stacks 0APT "surjectivity"]
public lemma surjective_of_isTaut_of_denseRange (φ : A →+* B) (hφ : Continuous φ)
    (hA : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hcount : (nhds (0 : A)).IsCountablyGenerated) (htaut : RingHom.IsTaut φ)
    (hdense : DenseRange φ) : Function.Surjective φ := by
  let R : AddSubgroup B := φ.toAddMonoidHom.range
  have hRopen : IsOpen (R : Set B) := by
    simpa [R, Set.image_univ] using
      (isOpenMap_of_isTaut_of_denseRange φ hφ hA hcount htaut hdense) Set.univ isOpen_univ
  have hRuniv : (R : Set B) = Set.univ := by
    rw [← (R.isClosed_of_isOpen hRopen).closure_eq]
    exact hdense.closure_range
  simpa [R, Set.range_eq_univ] using hRuniv

/-- The separated target of a continuous taut dense map from a complete countably based
linearly topologized ring is complete. -/
@[stacks 0APT "completeness of the target"]
public lemma completeSpace_of_isTaut_of_denseRange (φ : A →+* B) (hφ : Continuous φ)
    (hA : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hcount : (nhds (0 : A)).IsCountablyGenerated) (htaut : RingHom.IsTaut φ)
    (hdense : DenseRange φ) :
    @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B) := by
  have hsurj : Function.Surjective φ :=
    surjective_of_isTaut_of_denseRange φ hφ hA hcount htaut hdense
  have hopen : IsOpenMap φ := isOpenMap_of_isTaut_of_denseRange φ hφ hA hcount htaut hdense
  have he : IsHomeomorph (RingHom.quotientKerEquivOfSurjective hsurj) :=
    quotientKerEquiv_isHomeomorph φ hφ hopen hsurj
  exact complete_quotient_kernel φ hA hcount hsurj he

/-- The kernel of a continuous ring homomorphism into a space with closed points is closed. -/
@[stacks 0APT "closed kernel"]
public lemma isClosed_ker_of_continuous {R S : Type*} [CommRing R] [TopologicalSpace R]
    [CommRing S] [TopologicalSpace S] [T1Space S] (φ : R →+* S) (hφ : Continuous φ) :
    IsClosed (RingHom.ker φ : Set R) := by
  rw [show (RingHom.ker φ : Set R) = φ ⁻¹' ({0} : Set S) by ext x; simp]
  exact isClosed_singleton.preimage hφ

/-- The canonical map from the quotient by the kernel to the target is a homeomorphic ring
equivalence. -/
@[stacks 0APT "quotient presentation"]
public lemma quotientKerEquiv_of_isTaut_of_denseRange (φ : A →+* B) (hφ : Continuous φ)
    (hA : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hcount : (nhds (0 : A)).IsCountablyGenerated) (htaut : RingHom.IsTaut φ)
    (hdense : DenseRange φ) :
    ∃ e : (A ⧸ RingHom.ker φ) ≃+* B,
      (∀ a : A, e (Ideal.Quotient.mk (RingHom.ker φ) a) = φ a) ∧ IsHomeomorph e := by
  have hsurj : Function.Surjective φ :=
    surjective_of_isTaut_of_denseRange φ hφ hA hcount htaut hdense
  have hopen : IsOpenMap φ := isOpenMap_of_isTaut_of_denseRange φ hφ hA hcount htaut hdense
  let e := RingHom.quotientKerEquivOfSurjective hsurj
  refine ⟨e, ?_, quotientKerEquiv_isHomeomorph φ hφ hopen hsurj⟩
  intro a
  simp [e]

end

section

/-- The canonical map from a linearly topologized ring to its completion is taut. -/
@[stacks 0GX2]
public theorem isTaut_completion {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] :
    letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
    letI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
    RingHom.IsTaut (UniformSpace.Completion.coeRingHom :
      A →+* UniformSpace.Completion A) := by
  let : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  let : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  let f : A →+* UniformSpace.Completion A := UniformSpace.Completion.coeRingHom
  have hd : IsDenseInducing (f : A → UniformSpace.Completion A) :=
    UniformSpace.Completion.isDenseInducing_coe
  have hBasisA : (nhds (0 : A)).HasBasis
      (fun I : Ideal A => IsOpen (I : Set A)) (fun I => (I : Set A)) :=
    IsLinearTopology.hasBasis_open_ideal
  have hBasisCompletion := hBasisA.hasBasis_of_isDenseInducing hd
  constructor
  · intro I hI
    apply (Ideal.closure (I.map f)).toAddSubgroup.isOpen_of_mem_nhds
    show (Ideal.closure (I.map f) : Set _) ∈ nhds (0 : UniformSpace.Completion A)
    rw [ideal_closure_map_eq_closure_image f hd.dense I]
    simpa only [map_zero] using hd.closure_image_mem_nhds (hI.mem_nhds I.zero_mem)
  · exact hBasisCompletion.congr (fun _ => Iff.rfl) fun I _ =>
      (ideal_closure_map_eq_closure_image f hd.dense I).symm

end

section

/-- Closing an ideal before extending it along a continuous homomorphism does not change the
closure of the extension. -/
public lemma closure_map_closure {B C : Type*}
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
    (ψ : B →+* C) (hψ : Continuous ψ) (K : Ideal B) :
    Ideal.closure ((Ideal.closure K).map ψ) = Ideal.closure (K.map ψ) := by
  apply SetLike.ext'
  simp only [Ideal.coe_closure]
  apply le_antisymm
  · apply closure_minimal ?_ isClosed_closure
    show (Ideal.closure K).map ψ ≤ Ideal.closure (K.map ψ)
    apply Ideal.map_le_iff_le_comap.mpr
    intro b hb
    exact map_mem_closure hψ hb (fun _ hx => Ideal.mem_map_of_mem ψ hx)
  · exact closure_mono (Ideal.map_mono (show K ≤ Ideal.closure K from
      fun _ hx => subset_closure hx))

/-- The composite of continuous taut homomorphisms of linearly topologized rings is taut. -/
@[stacks 0GX3]
public lemma isTaut_comp {A B C : Type*}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
    (φ : A →+* B) (ψ : B →+* C) (hφ : Continuous φ) (hψ : Continuous ψ)
    (hφ_taut : RingHom.IsTaut φ) (hψ_taut : RingHom.IsTaut ψ) :
    RingHom.IsTaut (ψ.comp φ) := by
  constructor
  · intro I hI
    simpa only [closure_map_closure ψ hψ (I.map φ), Ideal.map_map] using
      hψ_taut.1 _ (hφ_taut.1 I hI)
  · apply hψ_taut.2.to_hasBasis
    · intro J hJ
      obtain ⟨I, hI, hIJ⟩ := hφ_taut.2.mem_iff.mp (hJ.mem_nhds J.zero_mem)
      refine ⟨I, hI, ?_⟩
      simpa only [← Ideal.map_map, Ideal.coe_closure] using
        closure_mono (Ideal.map_mono (show I.map φ ≤ J from
          fun _ hx => hIJ (subset_closure hx)))
    · intro I hI
      refine ⟨Ideal.closure (I.map φ), hφ_taut.1 I hI, ?_⟩
      rw [closure_map_closure ψ hψ (I.map φ), Ideal.map_map]

end

section

private lemma map_comp_le {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) {I : Ideal A} {J : Ideal B}
    (h : I ≤ J.comap φ) : I.map (ψ.comp φ) ≤ J.map ψ := by
  rw [← Ideal.map_map]; exact Ideal.map_mono (Ideal.map_le_iff_le_comap.mpr h)

/-- If a composite of two continuous ring homomorphisms is taut, then its second
map is taut. -/
@[stacks 0GX4]
public lemma isTaut_of_comp {A B C : Type*}
    [CommRing A] [TopologicalSpace A]
    [CommRing B] [TopologicalSpace B]
    [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
    (φ : A →+* B) (ψ : B →+* C) (hφ : Continuous φ) (hψ : Continuous ψ)
    (hcomp : RingHom.IsTaut (ψ.comp φ)) : RingHom.IsTaut ψ := by
  rcases hcomp with ⟨hopen, hbasis⟩
  refine ⟨?_, hbasis.to_hasBasis ?_ ?_⟩
  · intro J hJ
    exact Ideal.isOpen_of_isOpen_subideal
      (closure_mono (fun _ hx => map_comp_le φ ψ (J := J) le_rfl hx))
      (hopen (J.comap φ) (hJ.preimage hφ))
  · intro I hI
    let K : Ideal C := (I.map (ψ.comp φ)).closure
    refine ⟨K.comap ψ, (hopen I hI).preimage hψ, ?_⟩
    calc
      ((K.comap ψ).map ψ).closure ≤ K.closure :=
        closure_mono (fun _ hx => (Ideal.map_le_iff_le_comap.mpr le_rfl) hx)
      _ = K := Ideal.closure_eq_of_isClosed K isClosed_closure
  · intro J hJ
    exact ⟨J.comap φ, hJ.preimage hφ,
      closure_mono (fun _ hx => map_comp_le φ ψ (J := J) le_rfl hx)⟩

end

section

open Filter


/-- The target of a taut continuous homomorphism of linearly topologized rings has a countable
fundamental system of open ideals if the source does. -/
@[stacks 0GX6]
public lemma isCountablyGenerated_nhds_zero_of_isTaut
    {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B] (φ : A →+* B) (hφ : Continuous φ)
    (hφ_taut : RingHom.IsTaut φ) (hA : (nhds (0 : A)).IsCountablyGenerated) :
    (nhds (0 : B)).IsCountablyGenerated := by
  let := hA
  obtain ⟨x, hx, hxb⟩ := (IsLinearTopology.hasBasis_open_ideal (R := A)).exists_antitone_subbasis
  refine (hφ_taut.2.to_hasBasis (p' := fun _ : ℕ => True)
    (s' := fun n => (Ideal.closure ((x n).map φ) : Set B)) ?_
    (fun n _ => ⟨x n, hx n, subset_rfl⟩)).isCountablyGenerated
  · intro I hI
    obtain ⟨n, hn⟩ := hxb.mem_iff.1 ((IsLinearTopology.hasBasis_open_ideal (R := A)).mem_of_mem hI)
    exact ⟨n, trivial, closure_mono (Ideal.map_mono hn)⟩

end

section

/-- Weak pre-admissibility ascends along a continuous taut homomorphism of
linearly topologized rings. -/
@[stacks 0GX7]
public lemma isWeaklyPreAdmissible_of_isTaut
    {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B] (φ : A →+* B) (hφ : Continuous φ)
    (hφ_taut : RingHom.IsTaut φ) (hA : TopologicalRing.IsWeaklyPreAdmissible A) :
    TopologicalRing.IsWeaklyPreAdmissible B := by
  rcases hA with ⟨I, hI⟩
  exact ⟨_, isWeakIdealOfDefinition_closure_map φ hφ hφ_taut hI⟩

end

section

universe u v


private lemma closure_map_pow_le {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] (φ : A →+* B) (I : Ideal A) (n : ℕ) :
    (Ideal.closure (I.map φ)) ^ n ≤ Ideal.closure ((I ^ n).map φ) := by
  induction n with
  | zero =>
    simp only [pow_zero, Ideal.one_eq_top, Ideal.map_top]
    rw [Ideal.closure_eq_of_isClosed ⊤ isClosed_univ]
  | succ n ih =>
    rw [pow_succ]
    refine Ideal.mul_le.mpr fun x hx y hy ↦ ?_
    show x * y ∈ closure ((I ^ (n + 1)).map φ : Set B)
    exact map_mem_closure₂ continuous_mul (ih hx) hy
      (fun a ha b hb ↦ by
        show a * b ∈ (I ^ (n + 1)).map φ
        rw [pow_succ, Ideal.map_mul]
        exact Ideal.mul_mem_mul ha hb)

/-- Pre-admissibility ascends along a continuous taut homomorphism of linearly topologized
rings. -/
@[stacks 0GX8]
public lemma isPreAdmissible_of_isTaut {A : Type u} {B : Type v} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] [IsLinearTopology B B] (φ : A →+* B) (hφ : Continuous φ)
    (hφ_taut : RingHom.IsTaut φ) (hA : TopologicalRing.IsPreAdmissible A) :
    TopologicalRing.IsPreAdmissible B :=
  by
    obtain ⟨I, hI⟩ := hA
    refine ⟨Ideal.closure (I.map φ), hφ_taut.1 I hI.1, ?_⟩
    intro U hU
    obtain ⟨K, hKopen, hKU⟩ := hφ_taut.2.mem_iff.mp hU
    obtain ⟨n, hn⟩ := hI.2 (K : Set A) (hKopen.mem_nhds K.zero_mem)
    exact ⟨n, fun x hx ↦ hKU ((closure_mono (Ideal.map_mono hn))
      (closure_map_pow_le φ I n hx))⟩

end

end RingHom

end
