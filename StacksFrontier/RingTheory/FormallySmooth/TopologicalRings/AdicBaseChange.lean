module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.LocalRing.Pullback
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.Tactic.Abel
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Algebra.Nonarchimedean.Completion
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.UniformSpace.AbstractCompletion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.FormallySmooth.AdicLifting
public import StacksFrontier.RingTheory.FormallySmooth.BaseChange
public import StacksFrontier.RingTheory.FormallySmooth.Topological
public import StacksFrontier.Topology.Algebra.AdicTopology.Continuous
public import StacksFrontier.RingTheory.FormallySmooth.TopologicalRings.AdicCriterion

@[expose] public section

/-!
# Formally smooth maps of topological rings: lifting, base change and descent

Stacks Project, Chapter 15 "More on Algebra". The tags treated here are

07NJ, 07EG, 07EH.

## Tag 07NJ — Lifting to adic topological rings

A formally smooth homomorphism for an adic topology admits continuous lifts from quotients by
closed ideals whose suitable power lies in an ideal of definition.

### Main definitions

No new definitions are introduced.

### Main results

* `exists_continuous_lift_of_isFormallySmooth_of_isAdic`: a continuous lifting theorem
  from a closed quotient of an adic ring.

### Implementation notes

An ideal defining an adic topology is expressed by `IsAdic`; completeness and separatedness are
expressed by `IsAdicComplete`. The quotient carries Mathlib's quotient topology.

### References

* [Stacks Project, Tag 07NJ](https://stacks.math.columbia.edu/tag/07NJ)

## Tag 07EG — Base change of adic formal smoothness

Formal smoothness for an adic topology is preserved by arbitrary base change.

### Main definitions

The existing predicate `RingHom.FormallySmoothNAdic` expresses formal smoothness for the topology
defined by the powers of an ideal.

### Main results

* `isFormallySmooth_iff_formallySmoothNAdic`: for a discrete source and an
  adic target, the topological predicate of Tag 07EB agrees with the algebraic
  power-kernel predicate.

### Implementation notes

The base change itself is `RingHom.FormallySmoothNAdic.baseChange`, proved in
`StacksFrontier.RingTheory.FormallySmooth.BaseChange`, which this file imports; the comparison above
transports it to the topological predicate.

### References

* Stacks Project, Tag 07EG.

## Tag 07EH — Descent of adic formal smoothness along a split extension

Formal smoothness for an adic topology descends after a base change along a ring
map whose underlying module map admits a retraction.

### Main definitions

No new definitions are introduced.

### Main results

* `isFormallySmooth_adic_of_split_baseChange`: descent of formal
  smoothness from `S ⊗[R] R'` to `S` when `R → R'` is split as an
  `R`-linear map.

### Implementation notes

Formal smoothness for the `n`-adic topology means formal smoothness from the
discrete topology on the base ring to the adic topology on the target. The
extended ideal is the image of `n` under the canonical map
`S → S ⊗[R] R'`.

### References

* Stacks Project, Tag 07EH.

-/

section

/-! ### Stacks Tag 07NJ -/

section

section

@[expose] public section

universe u v w

/-- A formally smooth homomorphism for the `n`-adic topology lifts continuously through a closed
quotient of an adic ring when a positive power of the quotient ideal lies in an ideal of
definition. -/
@[stacks 07NJ]
public theorem exists_continuous_lift_of_isFormallySmooth_of_isAdic
    {R : Type u} {S : Type v} {A : Type w}
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
    [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [IsLinearTopology S S]
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (f : R →+* S) (n : Ideal S) (hn : IsAdic n)
    (hf : IsFormallySmooth.{w} f)
    (I : Ideal A) (hI : IsAdic I) [IsAdicComplete I A]
    (J : Ideal A) (hJ : IsClosed (J : Set A))
    (t : ℕ) (ht : 1 ≤ t) (hJI : J ^ t ≤ I)
    (g : R →+* A) (hg : Continuous g)
    (ψ : S →+* A ⧸ J) (hψ : Continuous ψ)
    (hcomm : ψ.comp f = (Ideal.Quotient.mk J).comp g) :
    ∃ φ : S →+* A, Continuous φ ∧ φ.comp f = g ∧
      (Ideal.Quotient.mk J).comp φ = ψ := by
  rcases hf with ⟨_, hfs⟩
  exact RingHom.FormallySmoothTop.exists_continuous_lift_of_isAdic f n hn hfs I hI J hJ t ht hJI
    g hg ψ hψ hcomm

end

end

end

/-! ### Stacks Tag 07EG -/

section

section

@[expose] public section

/-- For a discrete source and an adic target, the continuous lifting property of
Tag 07EB is equivalent to the algebraic power-kernel lifting property. -/
theorem isFormallySmooth_iff_formallySmoothNAdic.{u, v, w}
    {R : Type v} {S : Type w} [CommRing R] [CommRing S]
    [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
    [DiscreteTopology R]
    [TopologicalSpace S] [IsTopologicalRing S] [IsLinearTopology S S]
    (φ : R →+* S) (n : Ideal S) (hn : IsAdic n) :
    IsFormallySmooth.{u} φ ↔ RingHom.FormallySmoothNAdic.{u, v, w} φ n := by
  constructor
  · intro h A _ J hJ f ψ hcomm ⟨k, hk1, hkle⟩
    let : TopologicalSpace A := ⊥
    let : DiscreteTopology A := ⟨rfl⟩
    have : DiscreteTopology (A ⧸ J) :=
      QuotientAddGroup.discreteTopology (N := J.toAddSubgroup) (isOpen_discrete _)
    have hbot : IsAdic (⊥ : Ideal (A ⧸ J)) := is_bot_adic_iff.mpr inferInstance
    have hψadic : @Continuous S (A ⧸ J) n.adicTopology
        (⊥ : Ideal (A ⧸ J)).adicTopology ψ :=
      (RingHom.continuous_adic_iff ψ n ⊥).mpr ⟨k, hk1, fun x hx => hkle hx⟩
    have hψ : Continuous ψ := by
      change (inferInstance : TopologicalSpace S) = n.adicTopology at hn
      change (inferInstance : TopologicalSpace (A ⧸ J)) =
        (⊥ : Ideal (A ⧸ J)).adicTopology at hbot
      rwa [← hn, ← hbot] at hψadic
    obtain ⟨g, _, hgf, hqg⟩ := h.2 A J hJ f continuous_of_discreteTopology ψ hψ hcomm
    exact ⟨g, hqg, hgf⟩
  · intro h
    constructor
    · exact continuous_of_discreteTopology
    · intro A _ _ _ J hJ f _ ψ hψ hcomm
      have : DiscreteTopology (A ⧸ J) :=
        QuotientAddGroup.discreteTopology (N := J.toAddSubgroup) (isOpen_discrete _)
      have hbot : IsAdic (⊥ : Ideal (A ⧸ J)) := is_bot_adic_iff.mpr inferInstance
      have hk : ∃ k : ℕ, 1 ≤ k ∧ n ^ k ≤ RingHom.ker ψ := by
        have hψadic : @Continuous S (A ⧸ J) n.adicTopology
            (⊥ : Ideal (A ⧸ J)).adicTopology ψ := by
          change (inferInstance : TopologicalSpace S) = n.adicTopology at hn
          change (inferInstance : TopologicalSpace (A ⧸ J)) =
            (⊥ : Ideal (A ⧸ J)).adicTopology at hbot
          rwa [← hn, ← hbot]
        obtain ⟨k, hk, hle⟩ :=
          (RingHom.continuous_adic_iff ψ n (⊥ : Ideal (A ⧸ J))).mp hψadic
        exact ⟨k, hk, fun x hx => hle x hx⟩
      obtain ⟨k, hk1, hkle⟩ := hk
      obtain ⟨g, hqg, hgf⟩ := h A J hJ f ψ hcomm ⟨k, hk1, hkle⟩
      have hJg : n ^ k ≤ J.comap g := by
        intro x hx
        have hψx : ψ x = 0 := hkle hx
        have hq' : Ideal.Quotient.mk J (g x) = ψ x :=
          congrArg (fun q : S →+* A ⧸ J => q x) hqg
        exact (Ideal.Quotient.eq_zero_iff_mem (I := J)).mp (hq'.trans hψx)
      have hmapJ : (n ^ k).map g ≤ J := (Ideal.map_le_iff_le_comap).mpr hJg
      have hzero : (n ^ (k * 2)).map g ≤ (⊥ : Ideal A) := by
        rw [pow_mul, Ideal.map_pow]
        exact (pow_le_pow_left' hmapJ 2).trans_eq hJ
      have hcont' : @Continuous S A n.adicTopology (⊥ : Ideal A).adicTopology g :=
        (RingHom.continuous_adic_iff g n ⊥).mpr ⟨k * 2, by omega,
          fun x hx => hzero (Ideal.mem_map_of_mem g hx)⟩
      have hA : IsAdic (⊥ : Ideal A) := is_bot_adic_iff.mpr inferInstance
      refine ⟨g, ?_, hgf, hqg⟩
      change (inferInstance : TopologicalSpace A) = (⊥ : Ideal A).adicTopology at hA
      change (inferInstance : TopologicalSpace S) = n.adicTopology at hn
      rwa [← hn, ← hA] at hcont'

end

end

end

/-! ### Stacks Tag 07EH -/

section

section

open scoped TensorProduct

@[expose] public section

section Bridge

variable {R A R' : Type*} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']

private noncomputable def tensorRetract (p : R' →ₗ[R] R) : A ⊗[R] R' →ₗ[R] A :=
  TensorProduct.lift (LinearMap.mk₂ R (fun a r' ↦ p r' • a)
    (fun _ _ _ ↦ by simp [smul_add])
    (fun _ _ _ ↦ by simp [smul_smul, mul_comm])
    (fun _ _ _ ↦ by simp [add_smul])
    (fun _ _ _ ↦ by simp [smul_smul]))

private lemma tensorRetract_tmul (p : R' →ₗ[R] R) (a : A) (r' : R') :
    tensorRetract p (a ⊗ₜ[R] r') = p r' • a := by
  simp [tensorRetract]

private lemma tensorRetract_includeLeft (p : R' →ₗ[R] R)
    (hp : p.comp (Algebra.linearMap R R') = LinearMap.id) (a : A) :
    tensorRetract p ((Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] R') a) = a := by
  have hp1 : p 1 = 1 := by simpa using LinearMap.congr_fun hp (1 : R)
  simp [Algebra.TensorProduct.includeLeft_apply, tensorRetract_tmul, hp1]

private lemma tensorRetract_includeLeft_mul (p : R' →ₗ[R] R) (a : A)
    (x : A ⊗[R] R') :
    tensorRetract p
        ((Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] R') a * x) =
      a * tensorRetract p x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b r' => simp [Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.tmul_mul_tmul, tensorRetract_tmul]
  | add x y hx hy => simp only [mul_add, map_add, hx, hy]

private lemma tensorRetract_map_mem (p : R' →ₗ[R] R) (J : Ideal A)
    {x : A ⊗[R] R'}
    (hx : x ∈ Ideal.map
      (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] R') J) :
    tensorRetract p x ∈ J := by
  let ι : A →+* A ⊗[R] R' :=
    (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] R').toRingHom
  change x ∈ Ideal.span (ι '' (J : Set A)) at hx
  have h := Submodule.span_induction (p := fun x _ ↦ ∀ y, tensorRetract p (y * x) ∈ J)
    (by
      rintro x ⟨j, hj, rfl⟩ y
      rw [mul_comm]
      show tensorRetract p
        ((Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] R') j * y) ∈ J
      rw [tensorRetract_includeLeft_mul]
      exact J.mul_mem_right _ hj)
    (by intro y; simp)
    (by intro x y _ _ hx hy z; simpa [mul_add] using J.add_mem (hx z) (hy z))
    (by intro a x _ hx y; simpa [smul_eq_mul, mul_assoc] using hx (y * a)) hx 1
  simpa only [one_mul] using h

private def goodSubring (J : Ideal A) : Subring (A ⊗[R] R') where
  carrier := {x | ∃ a : A,
    x - (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] R') a ∈
      Ideal.map (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] R') J}
  zero_mem' := ⟨0, by simp⟩
  one_mem' := ⟨1, by simp [Algebra.TensorProduct.one_def]⟩
  add_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    simpa [map_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (Ideal.add_mem _ ha hb)
  mul_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a * b, ?_⟩
    let ι : A →ₐ[R] A ⊗[R] R' := Algebra.TensorProduct.includeLeft
    have hx : x = ι a + (x - ι a) := by abel
    have hy : y = ι b + (y - ι b) := by abel
    have heq : x * y - ι (a * b) =
        ι a * (y - ι b) + ι b * (x - ι a) + (x - ι a) * (y - ι b) := by
      rw [hx, hy]
      simp only [add_sub_cancel_left]
      rw [map_mul]
      ring
    rw [heq]
    exact Ideal.add_mem _ (Ideal.add_mem _ ((Ideal.map ι J).mul_mem_left (ι a) hb)
      ((Ideal.map ι J).mul_mem_left (ι b) ha)) ((Ideal.map ι J).mul_mem_right (y - ι b) ha)
  neg_mem' := by
    rintro x ⟨a, ha⟩
    refine ⟨-a, ?_⟩
    convert (Submodule.neg_mem _ ha) using 1; simp [map_neg]; abel

private noncomputable def goodSubringRetract (p : R' →ₗ[R] R)
    (hp : p.comp (Algebra.linearMap R R') = LinearMap.id) (J : Ideal A)
    (hJ : J ^ 2 = 0) : goodSubring (R := R) (R' := R') J →+* A where
  toFun x := tensorRetract p x
  map_zero' := map_zero _
  map_one' := by
    change tensorRetract p
      ((Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] R') 1) = 1
    exact tensorRetract_includeLeft p hp (1 : A)
  map_add' x y := map_add _ _ _
  map_mul' := by
    rintro ⟨x, a, ha⟩ ⟨y, b, hb⟩
    let ι : A →ₐ[R] A ⊗[R] R' := Algebra.TensorProduct.includeLeft
    let j := x - ι a
    let k := y - ι b
    have hx : x = ι a + j := by simp [j]
    have hy : y = ι b + k := by simp [k]
    have hjq : tensorRetract p j ∈ J := tensorRetract_map_mem p J ha
    have hkq : tensorRetract p k ∈ J := tensorRetract_map_mem p J hb
    have hjk : j * k = 0 := by
      have hzero : Ideal.map ι J * Ideal.map ι J = 0 := by
        rw [← pow_two, ← Ideal.map_pow, hJ]
        simp
      simpa [hzero] using Submodule.mul_mem_mul (show j ∈ Ideal.map ι J from ha)
        (show k ∈ Ideal.map ι J from hb)
    change tensorRetract p (x * y) = tensorRetract p x * tensorRetract p y
    have : tensorRetract p j * tensorRetract p k = 0 := by
      have hz : J * J = 0 := by simpa [pow_two] using hJ
      simpa [hz] using Submodule.mul_mem_mul hjq hkq
    rw [hx, hy, add_mul, mul_add, mul_add, map_add, map_add, map_add, map_add,
      map_add, hjk, map_zero, show ι a * ι b = ι (a * b) by simp,
      tensorRetract_includeLeft p hp, tensorRetract_includeLeft p hp,
      tensorRetract_includeLeft p hp,
      tensorRetract_includeLeft_mul p a k,
      show j * ι b = ι b * j by ac_rfl,
      tensorRetract_includeLeft_mul p b j]
    calc
      _ = a * b + a * tensorRetract p k + b * tensorRetract p j := by ring
      _ = a * b + a * tensorRetract p k + b * tensorRetract p j +
          tensorRetract p j * tensorRetract p k := by rw [this, add_zero]
      _ = _ := by ring

end Bridge

/-- If `R → R'` admits an `R`-linear retraction and the base change
`R' → S ⊗[R] R'` is formally smooth for the topology defined by the
extension of `n`, then `R → S` is formally smooth for the `n`-adic topology. -/
@[stacks 07EH]
public theorem isFormallySmooth_adic_of_split_baseChange.{u, v, w, z}
    {R : Type v} {S : Type w} {R' : Type z}
    [CommRing R] [CommRing S] [CommRing R'] [Algebra R S] [Algebra R R']
    (n : Ideal S)
    (hsplit : ∃ p : R' →ₗ[R] R,
      p.comp (Algebra.linearMap R R') = LinearMap.id)
    (hsmooth :
      letI : Algebra R' (S ⊗[R] R') :=
        Algebra.TensorProduct.rightAlgebra (R := R) (A := S) (B := R')
      let n' : Ideal (S ⊗[R] R') :=
        Ideal.map (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] R') n
      letI : TopologicalSpace R' := ⊥
      letI : DiscreteTopology R' := ⟨rfl⟩
      letI : TopologicalSpace (S ⊗[R] R') := n'.adicTopology
      letI : IsTopologicalRing (S ⊗[R] R') := n'.ringFilterBasis.isTopologicalRing
      letI : IsLinearTopology (S ⊗[R] R') (S ⊗[R] R') := n'.isLinearTopology
      IsFormallySmooth.{max u z} (algebraMap R' (S ⊗[R] R'))) :
    letI : TopologicalSpace R := ⊥
    letI : DiscreteTopology R := ⟨rfl⟩
    letI : TopologicalSpace S := n.adicTopology
    letI : IsTopologicalRing S := n.ringFilterBasis.isTopologicalRing
    letI : IsLinearTopology S S := n.isLinearTopology
    IsFormallySmooth.{u} (algebraMap R S) := by
  let : TopologicalSpace R := ⊥
  let : DiscreteTopology R := ⟨rfl⟩
  let : TopologicalSpace S := n.adicTopology
  let : IsTopologicalRing S := n.ringFilterBasis.isTopologicalRing
  let : IsLinearTopology S S := n.isLinearTopology
  let ιS : S →ₐ[R] S ⊗[R] R' := Algebra.TensorProduct.includeLeft
  let n' : Ideal (S ⊗[R] R') := Ideal.map ιS n
  let : Algebra R' (S ⊗[R] R') :=
    Algebra.TensorProduct.rightAlgebra (R := R) (A := S) (B := R')
  let : TopologicalSpace R' := ⊥
  let : DiscreteTopology R' := ⟨rfl⟩
  let : TopologicalSpace (S ⊗[R] R') := n'.adicTopology
  let : IsTopologicalRing (S ⊗[R] R') := n'.ringFilterBasis.isTopologicalRing
  let : IsLinearTopology (S ⊗[R] R') (S ⊗[R] R') := n'.isLinearTopology
  rcases hsmooth with ⟨_, hsmooth⟩
  refine ⟨continuous_of_discreteTopology, ?_⟩
  intro A _ tA _ J hJ f _ gbar hgbarCont hcomm
  let : DiscreteTopology (A ⧸ J) :=
    QuotientAddGroup.discreteTopology (isOpen_discrete (J : Set A))
  rcases hsplit with ⟨p, hp⟩
  let : Algebra R A := f.toAlgebra
  let A' := A ⊗[R] R'
  let ιA : A →ₐ[R] A' := Algebra.TensorProduct.includeLeft
  let J' : Ideal A' := Ideal.map (algebraMap A A') J
  let qeq : (A ⧸ J) ⊗[R] R' ≃ₐ[R] A' ⧸ J' :=
    Algebra.TensorProduct.quotientTensorEquiv (R := R) R R' A J
  let gbarAlg : S →ₐ[R] A ⧸ J :=
    { gbar with
      commutes' := fun r ↦ by
        show gbar (algebraMap R S r) = Ideal.Quotient.mk J (f r)
        exact DFunLike.congr_fun hcomm r }
  let gbar' : S ⊗[R] R' →+* A' ⧸ J' :=
    qeq.toRingHom.comp
      (Algebra.TensorProduct.map gbarAlg (AlgHom.id R R')).toRingHom
  let : TopologicalSpace A' := ⊥
  let : DiscreteTopology A' := ⟨rfl⟩
  let : Algebra R' A' :=
    Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := R')
  let : DiscreteTopology (A' ⧸ J') :=
    QuotientAddGroup.discreteTopology (isOpen_discrete (J' : Set A'))
  have hJ' : J' ^ 2 = 0 := by
    rw [← Ideal.map_pow, hJ]
    simp
  have hgbar' : Continuous gbar' := by
    have hQ : (inferInstance : TopologicalSpace (A' ⧸ J')) =
        (⊥ : Ideal (A' ⧸ J')).adicTopology :=
      (is_bot_adic_iff (A := A' ⧸ J')).2 inferInstance
    show @Continuous (S ⊗[R] R') (A' ⧸ J') n'.adicTopology
      (inferInstance : TopologicalSpace (A' ⧸ J')) gbar'
    rw [hQ]
    apply (RingHom.continuous_adic_iff gbar' n' ⊥).2
    obtain ⟨k, hk, hkill⟩ :=
      (RingHom.continuous_adic_iff gbar n ⊥).1 (by
        have hQ0 : (inferInstance : TopologicalSpace (A ⧸ J)) =
            (⊥ : Ideal (A ⧸ J)).adicTopology :=
          (is_bot_adic_iff (A := A ⧸ J)).2 inferInstance
        rw [← hQ0]
        exact hgbarCont)
    refine ⟨k, hk, ?_⟩
    intro x hx
    rw [← Ideal.map_pow] at hx
    refine Submodule.span_induction (p := fun x _ ↦ gbar' x = 0) ?_ (map_zero _) ?_ ?_ hx
    · rintro _ ⟨s, hs, rfl⟩
      have hz : gbar s = 0 := hkill s hs
      dsimp [gbar', qeq, gbarAlg, J', ιA, A', ιS]
      rw [hz]
      simp
    · intro x y _ _ hx hy
      simp [hx, hy]
    · intro a x _ hx
      simp [hx]
  have hcomm' : gbar'.comp (algebraMap R' (S ⊗[R] R')) =
      (Ideal.Quotient.mk J').comp (algebraMap R' A') := by
    ext r'
    dsimp [gbar', qeq, J', ιA, A']
    rw [show (Algebra.TensorProduct.map gbarAlg (AlgHom.id R R'))
        ((algebraMap R' (S ⊗[R] R')) r') = (1 : A ⧸ J) ⊗ₜ[R] r' by
      show (Algebra.TensorProduct.map gbarAlg (AlgHom.id R R'))
        ((1 : S) ⊗ₜ[R] r') = _
      rw [Algebra.TensorProduct.map_tmul]
      simp]
    show (Algebra.TensorProduct.quotientTensorEquiv R R' A J)
      (Ideal.Quotient.mk J (1 : A) ⊗ₜ[R] r') =
      Ideal.Quotient.mk _ ((1 : A) ⊗ₜ[R] r')
    exact Algebra.TensorProduct.quotientTensorEquiv_apply_tmul R R' A J 1 r'
  obtain ⟨lift', _, hliftR', hliftq⟩ :=
    hsmooth A' J' hJ' (algebraMap R' A') continuous_of_discreteTopology
      gbar' hgbar' hcomm'
  have hmem (s : S) (a : A) (ha : Ideal.Quotient.mk J a = gbar s) :
      lift' (ιS s) - ιA a ∈ J' := by
    refine (Ideal.Quotient.eq_zero_iff_mem).mp ?_
    rw [map_sub]
    have hh := DFunLike.congr_fun hliftq (ιS s)
    change Ideal.Quotient.mk J' (lift' (ιS s)) = gbar' (ιS s) at hh
    rw [hh]
    show qeq (gbar s ⊗ₜ[R] 1) - Ideal.Quotient.mk J' (a ⊗ₜ[R] 1) = 0
    rw [← ha]
    dsimp [qeq, J', ιA, A']
    simp
  have hgood (s : S) : lift' (ιS s) ∈ goodSubring (R := R) (R' := R') J :=
    (Ideal.Quotient.mk_surjective (gbar s)).imp (hmem s)
  let intoGood : S →+* goodSubring (R := R) (R' := R') J :=
    lift'.comp ιS.toRingHom |>.codRestrict _ hgood
  let lift : S →+* A := (goodSubringRetract p hp J hJ).comp intoGood
  have hlq : (Ideal.Quotient.mk J).comp lift = gbar := by
    ext s
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (gbar s)
    rw [← ha]
    show Ideal.Quotient.mk J (lift s) = Ideal.Quotient.mk J a
    rw [← sub_eq_zero, ← map_sub]
    apply (Ideal.Quotient.eq_zero_iff_mem).2
    have hq := tensorRetract_map_mem p J (hmem s a ha)
    simpa [lift, intoGood, goodSubringRetract, map_sub, ιA, J', A',
      Algebra.TensorProduct.includeLeft_apply, tensorRetract_tmul,
      show p 1 = 1 by simpa using LinearMap.congr_fun hp (1 : R)] using hq
  have hliftCont : Continuous lift := by
    have hA : tA = (⊥ : Ideal A).adicTopology :=
      (is_bot_adic_iff (A := A)).2 inferInstance
    show @Continuous S A n.adicTopology tA lift
    rw [hA]
    apply (RingHom.continuous_adic_iff lift n ⊥).2
    obtain ⟨k, hk, hkill⟩ :=
      (RingHom.continuous_adic_iff gbar n ⊥).1 (by
        have hQ : (inferInstance : TopologicalSpace (A ⧸ J)) =
            (⊥ : Ideal (A ⧸ J)).adicTopology :=
          (is_bot_adic_iff (A := A ⧸ J)).2 inferInstance
        rw [← hQ]
        exact hgbarCont)
    refine ⟨k * 2, by omega, ?_⟩
    intro x hx
    have hmap : Ideal.map lift (n ^ k) ≤ J := by
      rw [Ideal.map_le_iff_le_comap]
      intro y hy
      show lift y ∈ J
      apply (Ideal.Quotient.eq_zero_iff_mem).mp
      show ((Ideal.Quotient.mk J).comp lift) y = 0
      rw [DFunLike.congr_fun hlq y]
      exact hkill y hy
    have hxmap : lift x ∈ Ideal.map lift (n ^ (k * 2)) :=
      Ideal.mem_map_of_mem lift hx
    rw [pow_mul, Ideal.map_pow] at hxmap
    have : lift x ∈ J ^ 2 := (Ideal.pow_right_mono hmap 2) hxmap
    simpa [hJ] using this
  refine ⟨lift, hliftCont, ?_, ?_⟩
  · ext r
    have hh := DFunLike.congr_fun hliftR' (algebraMap R R' r)
    have hh' : lift' (ιS (algebraMap R S r)) = ιA (f r) := by
      calc
        lift' (ιS (algebraMap R S r)) =
            lift' (algebraMap R' (S ⊗[R] R') (algebraMap R R' r)) := by
              congr 1
              exact Algebra.TensorProduct.tmul_one_eq_one_tmul r
        _ = algebraMap R' A' (algebraMap R R' r) := hh
        _ = ιA (f r) := by
          show 1 ⊗ₜ[R] algebraMap R R' r = f r ⊗ₜ[R] 1
          exact (Algebra.TensorProduct.tmul_one_eq_one_tmul r).symm
    show tensorRetract p (lift' (ιS (algebraMap R S r))) = f r
    rw [hh']
    exact tensorRetract_includeLeft p hp (f r)
  · exact hlq

end

end

end

end
