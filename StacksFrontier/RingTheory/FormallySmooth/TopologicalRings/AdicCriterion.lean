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

@[expose] public section

/-!
# Formally smooth maps of topological rings: definition and adic criterion

Stacks Project, Chapter 15 "More on Algebra". The tags treated here are

07EB, 07EC.

## Tag 07EB — Formal smoothness of topological ring homomorphisms

A homomorphism of topological rings is formally smooth when compatible maps into
square-zero quotients of discrete rings admit continuous lifts. The definition
is stated for linearly topologized rings and includes continuity of the original
ring homomorphism.

### Main definitions

* `IsFormallySmooth`: formal smoothness of a topological ring homomorphism.

### Implementation notes

`IsLinearTopology R R` expresses that the neighborhoods of zero in `R` have a
basis of ideals. The lifting condition is `RingHom.FormallySmoothTop`; the conjunction
with `Continuous φ` records that the original arrow is a homomorphism of
topological rings. Thus, under the two linear-topology assumptions,
`IsFormallySmooth φ` is equivalent to continuity of `φ` together with
`RingHom.FormallySmoothTop φ`.

### References

* Stacks Project, Tag 07EB.

## Tag 07EC — Formal smoothness and adic topologies

An algebraically formally smooth ring homomorphism is formally smooth for a
linear topology on its source and a pre-adic topology on its target, provided
it is continuous. For adic topologies, formal smoothness is independent of
whether the source carries its adic topology or the discrete topology.

### Main results

* `isFormallySmooth_of_formallySmooth_and_isAdic_and_iff_discrete`:
  algebraic formal smoothness implies topological formal smoothness for a
  pre-adic target, and formal smoothness for adic topologies is equivalent to
  formal smoothness with discrete source.

### Implementation notes

A pre-adic topology on `S` is expressed by the existence of an ideal `n` with
`IsAdic n`. The `letI` expressions install the topologies named in each part of
the result without imposing unrelated topology choices on the other part.

### References

* Stacks Project, Tag 07EC.

-/

/-! ### Stacks Tag 07EB -/

section

@[expose] public section

/-- A homomorphism between linearly topologized rings is formally smooth if it
is continuous and every compatible square-zero lifting problem with a discrete
target ring has a continuous lift. -/
@[stacks 07EB, ega "0 19.3.1" "linearly topologized"]
def IsFormallySmooth.{u, v, w} {R : Type v} {S : Type w}
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
    [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [IsLinearTopology S S]
    (φ : R →+* S) : Prop :=
  Continuous φ ∧ RingHom.FormallySmoothTop.{u, v, w} φ

end

/-! ### Stacks Tag 07EC -/

section

section

@[expose] public section

namespace Stacks.FormallySmooth.TopologicalRings

/-- A ring map from an `m`-adic ring to a discrete ring is continuous if some power of `m` is sent
into an ideal `J` with `J ^ 2 = ⊥`. -/
private theorem continuous_adic_of_map_pow_le {X A : Type*} [CommRing X] [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [DiscreteTopology A] (m : Ideal X) (g : X →+* A)
    (J : Ideal A) (hJ : J ^ 2 = ⊥) {k : ℕ} (hk : 1 ≤ k) (hmap : ∀ y ∈ m ^ k, g y ∈ J) :
    @Continuous X A m.adicTopology _ g := by
  rw [(is_bot_adic_iff (A := A)).2 ‹_›]
  refine (RingHom.continuous_adic_iff g m ⊥).2 ⟨k * 2, by omega, fun x hx => ?_⟩
  have hxmap : g x ∈ Ideal.map g (m ^ (k * 2)) := Ideal.mem_map_of_mem g hx
  rw [pow_mul, Ideal.map_pow] at hxmap
  have : g x ∈ J ^ 2 :=
    Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hmap) 2 hxmap
  simpa [hJ] using this

/-- A continuous ring map from an `n`-adic ring to a discrete ring kills some power of `n`. -/
private theorem exists_pow_map_eq_zero_of_continuous {S Q : Type*} [CommRing S] [CommRing Q]
    [TopologicalSpace Q] [IsTopologicalRing Q] [DiscreteTopology Q] (n : Ideal S) (g : S →+* Q)
    (hg : @Continuous S Q n.adicTopology _ g) : ∃ k : ℕ, 1 ≤ k ∧ ∀ y ∈ n ^ k, g y = 0 := by
  have hQ : ‹TopologicalSpace Q› = (⊥ : Ideal Q).adicTopology :=
    (is_bot_adic_iff (A := Q)).2 ‹_›
  obtain ⟨k, hk, h⟩ := (RingHom.continuous_adic_iff g n ⊥).1 (by rw [← hQ]; exact hg)
  exact ⟨k, hk, fun y hy => by simpa using h y hy⟩

/-- An algebraically formally smooth ring homomorphism into a ring with an `n`-adic topology
satisfies the continuous lifting property `RingHom.FormallySmoothTop`. -/
public theorem formallySmoothTop_of_formallySmooth_of_isAdic.{u, v, w}
    {R : Type v} {S : Type w} [CommRing R] [CommRing S]
    [TopologicalSpace R] [IsTopologicalRing R]
    [TopologicalSpace S] [IsTopologicalRing S]
    (φ : R →+* S) (n : Ideal S) (hn : IsAdic n)
    (hφ : @Algebra.FormallySmooth R S _ _ φ.toAlgebra) :
    RingHom.FormallySmoothTop.{u} φ := by
  intro A _ tA _ J hJ f _ gbar hgbarCont hcomm
  let : Algebra R S := φ.toAlgebra
  let : Algebra R A := f.toAlgebra
  let gbarAlg : S →ₐ[R] A ⧸ J :=
    { gbar with
      commutes' := fun r => by
        show gbar (φ r) = Ideal.Quotient.mk J (f r)
        exact DFunLike.congr_fun hcomm r }
  let : Algebra.FormallySmooth R S := hφ
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_lift J ⟨2, hJ⟩ gbarAlg
  have hgbarEq : (Ideal.Quotient.mk J).comp g.toRingHom = gbar :=
    congrArg AlgHom.toRingHom hg
  have hcont : Continuous g := by
    let : DiscreteTopology (A ⧸ J) :=
      QuotientAddGroup.discreteTopology (isOpen_discrete (J : Set A))
    obtain ⟨k, hk, hkmap⟩ :=
      exists_pow_map_eq_zero_of_continuous n gbar (by rw [← hn]; exact hgbarCont)
    rw [hn]
    exact continuous_adic_of_map_pow_le n g.toRingHom J hJ hk fun y hy =>
      (Ideal.Quotient.eq_zero_iff_mem (I := J)).mp
        ((DFunLike.congr_fun hgbarEq y).trans (hkmap y hy))
  refine ⟨g.toRingHom, hcont, ?_, hgbarEq⟩
  ext r
  exact g.commutes r

end Stacks.FormallySmooth.TopologicalRings

open Stacks.FormallySmooth.TopologicalRings

/-- Algebraic formal smoothness implies formal smoothness for any continuous
map from a linearly topologized ring to a pre-adic ring. Moreover, for ideals
`m ⊆ R` and `n ⊆ S`, a continuous map for the adic topologies is formally
smooth if and only if it is formally smooth with the discrete topology on
`R`. -/
@[stacks 07EC]
public theorem isFormallySmooth_of_formallySmooth_and_isAdic_and_iff_discrete.{u, v, w}
    {R : Type v} {S : Type w} [CommRing R] [CommRing S] (φ : R →+* S) :
    (∀ (tR : TopologicalSpace R) (tS : TopologicalSpace S),
      letI := tR
      letI := tS
      ∀ [IsTopologicalRing R] [IsLinearTopology R R]
        [IsTopologicalRing S] [IsLinearTopology S S],
        (∃ n : Ideal S, IsAdic n) →
          @Algebra.FormallySmooth R S _ _ φ.toAlgebra → Continuous φ →
            IsFormallySmooth.{u} φ) ∧
      ∀ (m : Ideal R) (n : Ideal S),
        (letI := m.adicTopology
         letI : IsTopologicalRing R := m.ringFilterBasis.isTopologicalRing
         letI := n.adicTopology
         letI : IsTopologicalRing S := n.ringFilterBasis.isTopologicalRing
         @Continuous R S m.adicTopology n.adicTopology φ) →
          ((letI := m.adicTopology
            letI : IsTopologicalRing R := m.ringFilterBasis.isTopologicalRing
            letI : IsLinearTopology R R := m.isLinearTopology
            letI := n.adicTopology
            letI : IsTopologicalRing S := n.ringFilterBasis.isTopologicalRing
            letI : IsLinearTopology S S := n.isLinearTopology
            IsFormallySmooth.{u} φ) ↔
           (letI : TopologicalSpace R := ⊥
            letI : DiscreteTopology R := ⟨rfl⟩
            letI := n.adicTopology
            letI : IsTopologicalRing S := n.ringFilterBasis.isTopologicalRing
            letI : IsLinearTopology S S := n.isLinearTopology
            IsFormallySmooth.{u} φ)) := by
  constructor
  · intro tR tS _ _ _ _ ⟨n, hn⟩ hfs hcont
    exact ⟨hcont, formallySmoothTop_of_formallySmooth_of_isAdic φ n hn hfs⟩
  · intro m n hφ
    let discrete : @DiscreteTopology R (⊥ : TopologicalSpace R) := by
      let : TopologicalSpace R := ⊥
      exact ⟨rfl⟩
    let discreteRing : @IsTopologicalRing R (⊥ : TopologicalSpace R) _ := by
      let : TopologicalSpace R := ⊥
      let : DiscreteTopology R := discrete
      infer_instance
    change
      (@Continuous R S m.adicTopology n.adicTopology φ ∧
        @RingHom.FormallySmoothTop R S _ m.adicTopology
        m.ringFilterBasis.isTopologicalRing _ n.adicTopology
        n.ringFilterBasis.isTopologicalRing φ) ↔
      (@Continuous R S ⊥ n.adicTopology φ ∧
        @RingHom.FormallySmoothTop R S _ ⊥ discreteRing _ n.adicTopology
          n.ringFilterBasis.isTopologicalRing φ)
    constructor
    · rintro ⟨_, hsmooth⟩
      refine ⟨@continuous_of_discreteTopology R (⊥ : TopologicalSpace R) discrete S
        n.adicTopology φ, ?_⟩
      intro A _ _ _ J hJ f _ gbar hgbar hcomm
      have hf : @Continuous R A m.adicTopology _ f := by
        obtain ⟨a, ha, haφ⟩ := (RingHom.continuous_adic_iff φ m n).1 hφ
        let : DiscreteTopology (A ⧸ J) :=
          QuotientAddGroup.discreteTopology (isOpen_discrete (J : Set A))
        obtain ⟨b, hb, hbg⟩ := exists_pow_map_eq_zero_of_continuous n gbar hgbar
        refine continuous_adic_of_map_pow_le m f J hJ (k := a * b) (Nat.mul_pos ha hb) ?_
        intro y hy
        have hφy : φ y ∈ n ^ b := by
          have : φ y ∈ Ideal.map φ (m ^ (a * b)) := Ideal.mem_map_of_mem φ hy
          rw [pow_mul, Ideal.map_pow] at this
          exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr haφ) b this
        exact (Ideal.Quotient.eq_zero_iff_mem (I := J)).mp
          ((DFunLike.congr_fun hcomm y).symm.trans (hbg (φ y) hφy))
      exact hsmooth A J hJ f hf gbar hgbar hcomm
    · rintro ⟨_, hsmooth⟩
      refine ⟨hφ, ?_⟩
      intro A _ _ _ J hJ f hf gbar hgbar hcomm
      exact hsmooth A J hJ f
        (@continuous_of_discreteTopology R (⊥ : TopologicalSpace R) discrete A _ f)
        gbar hgbar hcomm

end

end

end
