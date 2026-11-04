module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.GroupWithZero.Pi
public import Mathlib.RingTheory.Ideal.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Flat.UniversallyInjective
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOver
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalPropertiesRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.Taut
public import StacksFrontier.Topology.Algebra.AdicTopology.TautIsLocal

/-!
# Tautness is a local property: the refined forms

We show that tautness of continuous ring homomorphisms between countably indexed weakly
admissible topological rings is invariant under bicontinuous ring isomorphisms of the source and
the target, and that it is a local property in the sense of `PropertyIsLocal'`.

## Main results

* `TopologicalRing.isTaut_isomorphismInvariant`: tautness does not depend on the presentations
  of the source and the target.
* `TopologicalRing.isTaut_propertyIsLocal'`: tautness is a local property.
-/

@[expose] public section

namespace TopologicalRing

open Filter

universe u

/-! ### Presentation independence of tautness -/

section Invariance

/-- The identity of a linearly topologized ring is taut: an open ideal is closed, hence equal
to the closure of its own extension. -/
private theorem isTaut_id {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R] :
    RingHom.IsTaut (RingHom.id R) := by
  have hc (I : Ideal R) (hI : IsOpen (I : Set R)) : Ideal.closure I = I :=
    Ideal.closure_eq_of_isClosed I (I.toAddSubgroup.isClosed_of_isOpen hI)
  constructor
  · intro I hI
    simpa only [Ideal.map_id, hc I hI] using hI
  · exact (IsLinearTopology.hasBasis_open_ideal (R := R)).congr
      (fun _ ↦ Iff.rfl) (fun I hI ↦ by simp only [Ideal.map_id, hc I hI])

/-- An isomorphism of linearly topologized rings which is continuous in both directions is
taut. -/
private theorem isTaut_ringEquiv {R S : Type*}
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
    [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [IsLinearTopology S S]
    (e : R ≃+* S) (he : Continuous e) (hes : Continuous e.symm) :
    RingHom.IsTaut e.toRingHom := by
  apply RingHom.isTaut_of_comp e.symm.toRingHom e.toRingHom hes he
  convert isTaut_id (R := S) using 1
  ext x
  simp

/-- Tautness does not depend on the chosen presentations of the source and the target of a
continuous homomorphism: pre- and post-composing with bicontinuous ring isomorphisms preserves
and reflects tautness. -/
@[stacks 0ANJ "taut_is_local_property"]
public theorem isTaut_isomorphismInvariant :
    IsomorphismInvariant.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
        (f : B →+* A) ↦ RingHom.IsTaut f)
      IsCountablyWeaklyAdmissible := by
  intro B A B' A' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eB eA heB heBs heA heAs f hf _ _ _ _
  constructor
  · intro h
    simpa only [RingHom.comp_assoc] using RingHom.isTaut_comp (f.comp eB.symm.toRingHom)
      eA.toRingHom (hf.comp heBs) heA
      (RingHom.isTaut_comp eB.symm.toRingHom f heBs hf (isTaut_ringEquiv eB.symm heBs heB) h)
      (isTaut_ringEquiv eA heA heAs)
  · intro h
    have hpre : RingHom.IsTaut (f.comp eB.symm.toRingHom) := by
      convert RingHom.isTaut_comp ((eA.toRingHom.comp f).comp eB.symm.toRingHom)
        eA.symm.toRingHom (heA.comp (hf.comp heBs)) heAs h
        (isTaut_ringEquiv eA.symm heAs heA) using 1
      ext x
      simp
    convert RingHom.isTaut_comp eB.toRingHom (f.comp eB.symm.toRingHom) heB (hf.comp heBs)
      (isTaut_ringEquiv eB heB heBs) hpre using 1
    ext x
    simp

end Invariance

/-! ### The three locality axioms for tautness -/

section Local

/-- Tautness is a local property of morphisms of countably indexed weakly admissible
topological rings: it is invariant under isomorphisms, preserved by localization and by finite
products, and descends along faithfully flat maps. -/
public theorem isTaut_propertyIsLocal' :
    PropertyIsLocal'.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
        (f : B →+* A) ↦ RingHom.IsTaut f) :=
  ⟨isTaut_isomorphismInvariant, isTaut_localizationPreserves, isTaut_faithfullyFlatDescent,
    isTaut_finiteProductPreserves⟩

end Local

end TopologicalRing

end
