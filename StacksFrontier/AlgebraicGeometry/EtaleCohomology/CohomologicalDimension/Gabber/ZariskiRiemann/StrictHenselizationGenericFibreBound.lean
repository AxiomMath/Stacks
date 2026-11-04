module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.StrictlyHenselianValuationFractionField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.TorsionVanishingBoundTransport
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.ValuationRingGenericFibre
import all StacksFrontier.RingTheory.Valuation.Extension.Etale

/-!
# The generic fibre of a strict henselization of a valuation ring has `cd_n ≤` the rank

Let `V` be a valuation ring with fraction field `K`, value group `Γ_V` and `n` invertible in `V`,
and let `S` be a strictly henselian local `V`-algebra, ind-étale over `V` with local structure
map (for instance a strict henselization of `V`). Then `S` is a valuation ring with the value group
of `V` (Stacks 0ASK), `S ⊗_V K` is the fraction field of `S`, and so

`H^p(Spec (S ⊗_V K), 𝓖) = 0` for every `p > rat.rank Γ_V` and every sheaf `𝓖` killed by `n`

(`AlgebraicGeometry.Scheme.isTorsionVanishingBound_spec_fractionRing_of_valuationRing` for `S`).
This is the vanishing at the Zariski–Riemann point `V` in Gabber's proof of Travaux de Gabber,
Exposé XVIII-A, Corollary 1.2: the limit over the models of
`η ×_Y Spec 𝒪^{sh}_{Y, c_Y}` is `Spec (K ⊗_V V^{sh})`.

## Main definitions

* `ValuationRing.valueGroupCongr`: the value groups of a valuation ring computed in two fraction
  fields agree.

## Main results

* `ValuationRing.rank_valueGroup_eq_of_indEtale`: an ind-étale local algebra over a valuation ring
  has the same rational rank.
* `AlgebraicGeometry.Scheme.isTorsionVanishingBound_spec_tensor_of_indEtale_valuationRing`: the
  bound above.

## References

* [Stacks Project, Tag 0ASK](https://stacks.math.columbia.edu/tag/0ASK)
* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace ValuationRing

section Congr

variable (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
  (K : Type v) [Field K] [Algebra A K] (K' : Type w) [Field K'] [Algebra A K']

variable {A K K'} in
/-- **The value group along an `A`-algebra isomorphism of fraction fields**: `e : K ≃ₐ[A] K'`
induces `Γ_{A,K} ≃* Γ_{A,K'}`, `[x] ↦ [e x]`. -/
def valueGroupMulEquivOfAlgEquiv (e : K ≃ₐ[A] K') : ValueGroup A K ≃* ValueGroup A K' where
  toFun := Quotient.map' e fun a b ⟨c, hc⟩ => ⟨c, by
    obtain rfl : c • b = a := hc
    change c • e b = e (c • b)
    rw [Units.smul_def, Units.smul_def, map_smul]⟩
  invFun := Quotient.map' e.symm fun a b ⟨c, hc⟩ => ⟨c, by
    obtain rfl : c • b = a := hc
    change c • e.symm b = e.symm (c • b)
    rw [Units.smul_def, Units.smul_def, map_smul]⟩
  left_inv := by
    rintro ⟨a⟩
    change Quotient.mk'' (e.symm (e a)) = Quotient.mk'' a
    rw [AlgEquiv.symm_apply_apply]
  right_inv := by
    rintro ⟨a⟩
    change Quotient.mk'' (e (e.symm a)) = Quotient.mk'' a
    rw [AlgEquiv.apply_symm_apply]
  map_mul' := by
    rintro ⟨a⟩ ⟨b⟩
    change Quotient.mk'' (e (a * b)) = Quotient.mk'' (e a * e b)
    rw [map_mul]

/-- **The value group does not depend on the fraction field**: the identification
`K ≃ₐ[A] K'` of two fraction fields of the valuation ring `A` induces `Γ_{A,K} ≃* Γ_{A,K'}`. -/
def valueGroupCongr [IsFractionRing A K] [IsFractionRing A K'] :
    ValueGroup A K ≃* ValueGroup A K' :=
  valueGroupMulEquivOfAlgEquiv (IsLocalization.algEquiv (nonZeroDivisors A) K K')

/-- The rational ranks of the value group of `A` computed in two fraction fields agree. -/
theorem rank_valueGroup_congr [IsFractionRing A K] [IsFractionRing A K'] :
    Cardinal.lift.{w} (Module.rank ℤ (Additive (ValueGroup A K)ˣ)) =
      Cardinal.lift.{v} (Module.rank ℤ (Additive (ValueGroup A K')ˣ)) :=
  (MulEquiv.toAdditive (Units.mapEquiv (valueGroupCongr A K K'))).toIntLinearEquiv.lift_rank_eq

end Congr

/-- **An ind-étale local algebra over a valuation ring has the same rational rank** (Stacks 0ASK):
for `S` local, ind-étale over the valuation ring `R` with local structure map, the map on value
groups is bijective (`ValuationRing.isWeaklyUnramified_of_ind_etale`), so
`rank_ℤ Γ_S = rank_ℤ Γ_R`, the latter computed in any fraction field `K` of `R`. -/
theorem rank_valueGroup_eq_of_indEtale (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Type u) [CommRing S] [IsDomain S] [ValuationRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)]
    (hind : (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R S)) :
    Module.rank ℤ (Additive (ValueGroup S (FractionRing S))ˣ) =
      Module.rank ℤ (Additive (ValueGroup R K)ˣ) := by
  obtain ⟨_, _, hext, hweak⟩ := isWeaklyUnramified_of_ind_etale R S hind
  have h := rank_valueGroup_congr R K (FractionRing R)
  rw [Cardinal.lift_id, Cardinal.lift_id] at h
  rw [h]
  exact ((MulEquiv.ofBijective _ hweak).toAdditive.toIntLinearEquiv.rank_eq).symm

end ValuationRing

namespace AlgebraicGeometry.Scheme

/-- **The generic fibre of a strict henselization of a valuation ring has `cd_n ≤` the rank.** Let
`V` be a valuation ring with fraction field `K`, `n` invertible in `V` with
`rank_ℤ Γ_V ≤ r`, and `S` a strictly henselian local `V`-algebra, ind-étale over `V` with local
structure map. Then `H^p(Spec (S ⊗_V K), 𝓖) = 0` for `p > r` and `𝓖` killed by `n`: `S` is a
valuation ring with the value group of `V` and `S ⊗_V K = Frac S`
(`Stacks.StrictHenselization.isFractionRing_tensor_of_valuationRing`), and
`AlgebraicGeometry.Scheme.isTorsionVanishingBound_spec_fractionRing_of_valuationRing` applies to
`S`. -/
theorem isTorsionVanishingBound_spec_tensor_of_indEtale_valuationRing (V : Type u) [CommRing V]
    [IsDomain V] [ValuationRing V] (K : Type u) [Field K] [Algebra V K] [IsFractionRing V K]
    (S : Type u) [CommRing S] [StrictlyHenselianLocalRing S] [Algebra V S]
    [IsLocalHom (algebraMap V S)] (hind : StacksDraft.IndEtale V S) {n r : ℕ}
    (hn : IsUnit (n : V))
    (hrank : Module.rank ℤ (Additive (ValuationRing.ValueGroup V K)ˣ) ≤ r) :
    IsTorsionVanishingBound (Spec (.of (S ⊗[V] K))) n r := by
  have hind' := StacksDraft.indEtale_iff.mp hind
  obtain ⟨_, _, -, _⟩ := Stacks.StrictHenselization.isFractionRing_tensor_of_valuationRing V K S
    hind'
  let e : S ⊗[V] K ≃ₐ[S] FractionRing S :=
    IsLocalization.algEquiv (nonZeroDivisors S) _ _
  refine IsTorsionVanishingBound.of_iso
    (Scheme.Spec.mapIso e.toRingEquiv.symm.toCommRingCatIso.op) ?_
  refine isTorsionVanishingBound_spec_fractionRing_of_valuationRing S ?_ ?_
  · simpa only [map_natCast] using hn.map (algebraMap V S)
  · rw [ValuationRing.rank_valueGroup_eq_of_indEtale V K S hind']
    exact hrank

end AlgebraicGeometry.Scheme

end
