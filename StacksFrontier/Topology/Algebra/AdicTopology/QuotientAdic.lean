module

public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Algebra.Ring.Ideal

/-!
# The adic topology of a quotient

The image of an ideal defining the topology of `R` defines the topology of `R ⧸ J`: if `IsAdic I`
then `IsAdic (I.map (Ideal.Quotient.mk J))`. Two modules proved this privately; it lives here once.

## Main results

* `isAdic_map_quotient_mk`
-/

@[expose] public section

open Topology

/-- If `I` defines the topology of `R`, its image defines the topology of `R ⧸ J`. -/
public theorem isAdic_map_quotient_mk {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (I J : Ideal R) (hI : IsAdic I) :
    IsAdic (I.map (Ideal.Quotient.mk J)) := by
  rw [isAdic_iff] at hI ⊢
  obtain ⟨hopen, hcofinal⟩ := hI
  refine ⟨fun n ↦ ?_, fun s hs ↦ ?_⟩
  · rw [← Ideal.map_pow, Ideal.map_eq_image_of_surjective _ Ideal.Quotient.mk_surjective]
    exact QuotientRing.isOpenMap_coe J _ (hopen n)
  · have hpre : (Ideal.Quotient.mk J) ⁻¹' s ∈ 𝓝 (0 : R) :=
      (QuotientRing.isOpenQuotientMap_mk J).isQuotientMap.continuous.continuousAt hs
    obtain ⟨n, hn⟩ := hcofinal _ hpre
    refine ⟨n, fun y hy ↦ ?_⟩
    rw [← Ideal.map_pow] at hy
    obtain ⟨x, hx, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective (I := I ^ n)).mp hy
    exact hn hx

end
