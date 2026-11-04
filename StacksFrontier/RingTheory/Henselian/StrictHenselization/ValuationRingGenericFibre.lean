module

public import StacksFrontier.RingTheory.Etale.IndEtaleUniverse
public import StacksFrontier.RingTheory.Henselian.StrictHenselization
public import StacksFrontier.RingTheory.Valuation.Extension.Etale
import all StacksFrontier.RingTheory.Valuation.Extension.Etale

/-!
# The generic fibre of the strict henselization of a valuation ring

Let `V` be a valuation ring with fraction field `K`, and let `V → V^{sh}` be a strict
henselization. Then `V^{sh}` is a valuation ring, `V → V^{sh}` is injective, and
`V^{sh} ⊗_V K` is the fraction field of `V^{sh}`. The first two statements are Stacks 0ASK
(`ValuationRing.isValuationRingExtension_of_ind_etale`), for any ind-étale local `V`-algebra. For
the third, `V^{sh} ⊗_V K` is the localization of `V^{sh}` at the image of `V ∖ {0}`, and every
nonzero `x ∈ V^{sh}` divides the image of a nonzero element of `V`: `a = v · x · c` with
`a, c ∈ V ∖ {0}` and `v` a unit (`ValuationRing.factor_of_ind_etale`, the value groups of `V` and
`V^{sh}` agreeing). This is the identification `Spec (V^{sh} ⊗_V K) = Spec (Frac V^{sh})` used in
Gabber's Zariski–Riemann argument for Travaux de Gabber, Exposé XVIII-A, Corollary 1.2.

## Main results

* `Stacks.StrictHenselization.isFractionRing_tensor_of_valuationRing`: for an ind-étale local
  algebra over a valuation ring.
* `Stacks.StrictHenselization.IsStrictHenselization.isFractionRing_tensor_of_valuationRing`: for
  the strict henselization.

## References

* [StacksProject 0ASK](https://stacks.math.columbia.edu/tag/0ASK)
* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped TensorProduct

universe u v

namespace Stacks.StrictHenselization

/-- **The generic fibre of an ind-étale local algebra over a valuation ring is its fraction
field.** Let `V` be a valuation ring with fraction field `K` and `S` a local `V`-algebra, ind-étale
over `V` with local structure map. Then `S` is a valuation ring, `V → S` is injective, and
`S ⊗_V K` is a fraction field of `S`. -/
theorem isFractionRing_tensor_of_valuationRing (V : Type u) [CommRing V] [IsDomain V]
    [ValuationRing V] (K : Type v) [CommRing K] [Algebra V K] [IsFractionRing V K]
    (S : Type u) [CommRing S] [IsLocalRing S] [Algebra V S] [IsLocalHom (algebraMap V S)]
    (hind : (CommAlgCat.etale.{u} V).ind.{u} (CommAlgCat.of V S)) :
    ∃ (_ : IsDomain S) (_ : ValuationRing S), Function.Injective (algebraMap V S) ∧
      IsFractionRing S (S ⊗[V] K) := by
  obtain ⟨hdom, hval, hext⟩ := ValuationRing.isValuationRingExtension_of_ind_etale V S hind
  refine ⟨hdom, hval, hext.1, ?_⟩
  have hM : Algebra.algebraMapSubmonoid S (nonZeroDivisors V) ≤ nonZeroDivisors S := by
    rintro _ ⟨a, ha, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h0 => nonZeroDivisors.ne_zero ha ?_
    exact hext.1 (by rw [h0, map_zero])
  refine IsLocalization.isLocalization_of_is_exists_mul_mem (S ⊗[V] K)
    (Algebra.algebraMapSubmonoid S (nonZeroDivisors V)) (nonZeroDivisors S) hM ?_
  rintro ⟨x, hx⟩
  obtain ⟨a, c, w, ha, -, hfac⟩ :=
    ValuationRing.factor_of_ind_etale V S hind x (nonZeroDivisors.ne_zero hx)
  refine ⟨(w : S) * algebraMap V S c, Submonoid.mem_map.mpr
    ⟨a, mem_nonZeroDivisors_of_ne_zero ha, ?_⟩⟩
  rw [hfac]
  ring

/-- **The generic fibre of the strict henselization of a valuation ring is its fraction field.**
If `V` is a valuation ring with fraction field `K` and `V → V^{sh}` is a strict henselization,
then `V^{sh}` is a valuation ring, `V → V^{sh}` is injective, and `V^{sh} ⊗_V K = Frac V^{sh}`. -/
theorem IsStrictHenselization.isFractionRing_tensor_of_valuationRing (V : Type u) [CommRing V]
    [IsDomain V] [ValuationRing V] (K : Type v) [CommRing K] [Algebra V K] [IsFractionRing V K]
    {κ : Type*} [Field κ] [Algebra (maximalIdeal V).ResidueField κ]
    [IsSepClosure (maximalIdeal V).ResidueField κ]
    (Vsh : Type u) [CommRing Vsh] [IsLocalRing Vsh] [Algebra V Vsh]
    (h : IsStrictHenselization V κ Vsh) :
    ∃ (_ : IsDomain Vsh) (_ : ValuationRing Vsh), Function.Injective (algebraMap V Vsh) ∧
      IsFractionRing Vsh (Vsh ⊗[V] K) := by
  have := h.isLocalHom
  exact Stacks.StrictHenselization.isFractionRing_tensor_of_valuationRing V K Vsh
    (StacksDraft.indEtale_iff.mp h.isFilteredColimitEtale)

end Stacks.StrictHenselization

end
