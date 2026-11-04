module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Algebra.Nonarchimedean.Completion
public import Mathlib.Topology.Algebra.Ring.Ideal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Algebra.AdicTopology.AdicRingMap
public import StacksFrontier.Topology.Algebra.AdicTopology.AdmissibleRingsRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.Continuous
public import StacksFrontier.Topology.Algebra.AdicTopology.Taut
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissible

/-!
# Adic ring maps: the refined forms

The strengthened forms of declarations of `StacksFrontier.Topology.Algebra.AdicTopology.AdicRingMap`.
A declaration of that module whose statement was strengthened keeps its original statement there;
its strengthened form lives here under a primed name.

Adicness of ideals and of continuous ring homomorphisms is invariant under ring isomorphisms
that are continuous in both directions.

## Main results

* `RingHom.isAdic_ideal_map_of_ringEquiv`: the image of an adic ideal under a ring isomorphism
  continuous in both directions is adic.
* `RingHom.isAdic_comp_ringEquiv_iff`: a ring homomorphism is adic if and only if its transport
  along ring isomorphisms of source and target, continuous in both directions, is adic.
-/

@[expose] public section

namespace RingHom

section

end

section

section

end

end

section

section

/-- The extension of an adic ideal along a ring isomorphism continuous in both directions is
adic: the isomorphism is a homeomorphism, and it carries the powers of the ideal onto the
powers of the extended ideal. -/
public theorem isAdic_ideal_map_of_ringEquiv
    {A C : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
    (e : A ≃+* C) (he : Continuous e) (hes : Continuous e.symm)
    (I : Ideal A) (hI : _root_.IsAdic I) : _root_.IsAdic (I.map e.toRingHom) := by
  let E : A ≃ₜ C :=
    { toEquiv := e.toEquiv
      continuous_toFun := he
      continuous_invFun := hes }
  have hI' := isAdic_iff.mp hI
  have hmap : ∀ n : ℕ,
      ((I.map e.toRingHom) ^ n : Ideal C) = e '' ((I ^ n : Ideal A) : Set A) := by
    intro n
    rw [← Ideal.map_pow, Ideal.map_eq_image_of_surjective e.toRingHom e.surjective]
    rfl
  refine isAdic_iff.mpr ⟨fun n ↦ ?_, fun U hU ↦ ?_⟩
  · rw [hmap n]
    exact E.isOpenMap _ (hI'.1 n)
  · obtain ⟨n, hn⟩ := hI'.2 (E ⁻¹' U)
      (E.continuous.continuousAt.preimage_mem_nhds (by simpa [E] using hU))
    refine ⟨n, ?_⟩
    rw [hmap n]
    rintro y ⟨x, hx, rfl⟩
    exact hn hx

private theorem isAdic_transport_ringEquiv {B A B' A' : Type*}
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B'] [TopologicalSpace B'] [IsTopologicalRing B']
    [CommRing A'] [TopologicalSpace A'] [IsTopologicalRing A']
    (eB : B ≃+* B') (eA : A ≃+* A')
    (heB : Continuous eB) (heBs : Continuous eB.symm)
    (heA : Continuous eA) (heAs : Continuous eA.symm)
    (f : B →+* A) (h : RingHom.IsAdic f) :
    RingHom.IsAdic ((eA.toRingHom.comp f).comp eB.symm.toRingHom) := by
  obtain ⟨I, hI, hIf⟩ := h
  refine ⟨I.map eB.toRingHom, isAdic_ideal_map_of_ringEquiv eB heB heBs I hI, ?_⟩
  convert isAdic_ideal_map_of_ringEquiv eA heA heAs (I.map f) hIf using 1
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  ext x
  simp

/-- Adicness of a continuous homomorphism is unchanged when its source and its target are
replaced by isomorphic topological rings, the isomorphisms being continuous in both
directions. -/
public theorem isAdic_comp_ringEquiv_iff {B A B' A' : Type*}
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B'] [TopologicalSpace B'] [IsTopologicalRing B']
    [CommRing A'] [TopologicalSpace A'] [IsTopologicalRing A']
    (eB : B ≃+* B') (eA : A ≃+* A')
    (heB : Continuous eB) (heBs : Continuous eB.symm)
    (heA : Continuous eA) (heAs : Continuous eA.symm) (f : B →+* A) :
    RingHom.IsAdic f ↔
      RingHom.IsAdic ((eA.toRingHom.comp f).comp eB.symm.toRingHom) := by
  refine ⟨isAdic_transport_ringEquiv eB eA heB heBs heA heAs f, fun h ↦ ?_⟩
  convert isAdic_transport_ringEquiv eB.symm eA.symm heBs heB heAs heA
    ((eA.toRingHom.comp f).comp eB.symm.toRingHom) h using 1
  ext x
  simp

end

end

section

section

end

end

section

section

add_to_stacks 0GBS "part (2)" RingHom.isAdic_of_isTaut

end

end

end RingHom

end
