module

public import StacksFrontier.Topology.Algebra.AdicTopology.Descent
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Descent

/-!
# Descent of Noetherianness for adic rings

Let `A` be an adic topological ring and `φ : A →+* B` a ring homomorphism to a Noetherian
topological ring such that for every open ideal `I` of `A` the induced map
`A ⧸ I →+* B ⧸ closure (I B)` is faithfully flat. Then `A` is Noetherian.

## Main results

* `TopologicalRing.isNoetherianRing_of_faithfullyFlat_quotient`: Noetherianness descends along
  such a homomorphism.
-/

@[expose] public section

namespace TopologicalRing

section

open Filter

universe u v

end

section

open Filter

universe u v

end

section

universe u v

end

section

universe u v

open Filter

open scoped Topology

end

section

open Filter

open scoped Topology

universe u

end

section

universe u v

/-- Noetherianness descends along a homomorphism out of an adic ring all of whose maps on
quotients by open ideals are faithfully flat.

For an open ideal `L` of `A` the ring `B ⧸ closure (L B)` is a quotient of the Noetherian ring
`B`, so Stacks 033E makes `A ⧸ L` Noetherian. Read at the closure of the square of an ideal of
definition `I` of `A`, which is open because `I ^ 2` is, this exhibits `I / closure (I ^ 2)` as
a finite `A`-module, so Stacks 0GXH produces a finitely generated ideal `J` defining the
topology of `A`. Then `A` is `J`-adically complete, being complete and separated, and `A ⧸ J`
is Noetherian by the same descent, so Stacks 05GH concludes. -/
public theorem isNoetherianRing_of_faithfullyFlat_quotient
    {A : Type u} {B : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (φ : A →+* B)
    (hquot : ∀ I : Ideal A, IsOpen (I : Set A) →
      (Ideal.quotientMap (I := I) (Ideal.closure (I.map φ)) φ
        (Ideal.map_le_iff_le_comap.mp
          (show I.map φ ≤ Ideal.closure (I.map φ) from
            fun _ hx ↦ subset_closure hx))).FaithfullyFlat)
    (hA : TopologicalRing.IsAdic A) (hB : IsNoetherianRing B) : IsNoetherianRing A := by
  have _ : IsNoetherianRing B := hB
  have hdescent : ∀ L : Ideal A, IsOpen (L : Set A) → IsNoetherianRing (A ⧸ L) := fun L hL ↦
    descent_noetherian _ (hquot L hL) (Ideal.Quotient.isNoetherianRing _)
  obtain ⟨⟨I, hIdef, hIadic⟩, hT2, hcomplete⟩ := hA
  have _ : T2Space A := hT2
  have _ : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A) := hcomplete
  have _ : TopologicalRing.IsWeaklyAdic A :=
    TopologicalRing.isWeaklyAdic_of_isAdic A ⟨⟨I, hIdef, hIadic⟩, hT2, hcomplete⟩
  have _ : Module.Finite A (↥I ⧸ Submodule.comap I.subtype (I ^ 2).topologicalClosure) :=
    Ideal.finite_quotient_comap_subtype I _ (hdescent _
      (Ideal.isOpen_of_isOpen_subideal (Submodule.le_topologicalClosure _)
        ((isAdic_iff.mp hIadic).1 2)))
  obtain ⟨J, hJfg, hJadic⟩ :=
    TopologicalRing.exists_fg_isAdic_of_quotient_closure_sq_finite I hIdef
  let : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  let : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  exact noetherian_of_isAdicComplete_fg A J hJfg
    (hJadic.isAdicComplete_iff.mpr ⟨hcomplete, hT2⟩)
    (hdescent J (by simpa using (isAdic_iff.mp hJadic).1 1))

end

end TopologicalRing

end
