module

public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.Length
public import StacksFrontier.RingTheory.HilbertSamuel.Defs
public import StacksFrontier.RingTheory.Support.Basic
public import StacksFrontier.RingTheory.Support.Finite
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite-length conditions for a quotient module

Let `M` be a finite module over a Noetherian local ring and let `I` be an ideal. Provided
`M / IM` is nonzero, the usual ideal-of-definition, support, dimension, and finite-length
conditions on `I` and `M` are all equivalent. This is what makes the generalized
Hilbert–Samuel theory of Tag 0B00 available: it is exactly the setting in which the lengths
of all the quotients `M / I ^ n M` are finite.

## Main results

* `Ideal.idealOfDefinition_support_length_tfae` gives the five equivalent finite-length
  conditions.

## Implementation notes

The quotient `M / IM` is represented by `M ⧸ I • ⊤`. The image of `I` in the quotient by the
annihilator is expressed using `Ideal.map`. The five conditions are recorded with `List.TFAE`
in the order in which they occur in the source.

## References

* [Stacks Project, Tag 0B00](https://stacks.math.columbia.edu/tag/0B00)
-/

@[expose] public section

namespace Ideal

/-- Over a Noetherian local ring, a nonzero finite module has support in the closed point if and
only if its support has dimension at most zero. -/
private theorem support_subset_closedPoint_iff_supportDim_nonpos {R N : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] [AddCommGroup N] [Module R N] [Module.Finite R N]
    [Nontrivial N] :
    Module.support R N ⊆ {IsLocalRing.closedPoint R} ↔ Module.supportDim R N ≤ 0 := by
  have : Nonempty (Module.support R N) := Module.nonempty_support_of_nontrivial.to_subtype
  have hdim : Order.krullDim ({IsLocalRing.closedPoint R} : Set (PrimeSpectrum R)) = 0 :=
    Order.krullDim_eq_zero_of_unique
  refine ⟨fun h => ?_, fun h => ?_⟩
  · unfold Module.supportDim
    simpa [hdim] using
      Order.krullDim_le_of_strictMono (Set.inclusion h) (Subtype.strictMono_coe _)
  · rw [support_of_supportDim_eq_zero R N (le_antisymm h Order.krullDim_nonneg),
      PrimeSpectrum.zeroLocus_eq_singleton]
    rfl

/-- Over a Noetherian local ring, a nonzero finite module has support in the closed point if and
only if it has finite length. -/
private theorem support_subset_closedPoint_iff_length_lt_top {R N : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] [AddCommGroup N] [Module R N] [Module.Finite R N]
    [Nontrivial N] :
    Module.support R N ⊆ {IsLocalRing.closedPoint R} ↔ Module.length R N < ⊤ := by
  rw [lt_top_iff_ne_top, Module.length_ne_top_iff, ← support_point (R := R) (M := N)]
  simp only [Set.Subset.antisymm_iff]
  exact ⟨fun h => ⟨h, by simp [IsLocalRing.closedPoint_mem_support R N]⟩, And.left⟩

/-- For a proper ideal `K` of a Noetherian local ring, `I + K` is an ideal of definition if and
only if the image of `I` in `R ⧸ K` is one. -/
private theorem isIdealOfDefinition_add_iff_map {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (I : Ideal R) {K : Ideal R} (hK : K ≠ ⊤) [IsLocalRing (R ⧸ K)] :
    IsIdealOfDefinition (I + K) ↔ IsIdealOfDefinition (I.map (Ideal.Quotient.mk K)) := by
  let f := Ideal.Quotient.mk K
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective
  rw [isIdealOfDefinition_iff, isIdealOfDefinition_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hk : RingHom.ker f ≤ I + K := Ideal.mk_ker.trans_le le_sup_right
    have hmapJ : Ideal.map f (I + K) = Ideal.map f I := by
      rw [Submodule.add_eq_sup, Ideal.map_sup, Ideal.map_quotient_self, sup_bot_eq]
    have hmax : Ideal.map f (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal (R ⧸ K) :=
      IsLocalRing.eq_maximalIdeal <| Ideal.IsMaximal.map_of_surjective_of_ker_le hf <|
        Ideal.mk_ker.trans_le (IsLocalRing.le_maximalIdeal hK)
    rw [← hmapJ, ← Ideal.map_radical_of_surjective hf hk, h, hmax]
  · have hc := congr_arg (Ideal.comap f) h
    rw [Ideal.comap_radical, Ideal.comap_map_of_surjective f hf,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at hc
    have hcomax : Ideal.comap f (IsLocalRing.maximalIdeal (R ⧸ K)) =
        IsLocalRing.maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective f hf)
    exact hcomax ▸ hc

/-- **Stacks Project, Tag 0B00, finite-length conditions.** Let `M` be a finite module over a
Noetherian local ring and `I` an ideal. If `M / IM` is nonzero, then the following are
equivalent: `I + Ann(M)` is an ideal of definition; the image of `I` in `R / Ann(M)` is an
ideal of definition; the support of `M / IM` is contained in the closed point; that support
has dimension at most zero; and `M / IM` has finite length. -/
@[stacks 0B00 "finite_length_conditions"]
theorem idealOfDefinition_support_length_tfae
    {R M : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (I : Ideal R) (hMI : Nontrivial (M ⧸ I • (⊤ : Submodule R M))) :
    letI := hMI
    letI : Nontrivial M := (I • (⊤ : Submodule R M)).mkQ_surjective.nontrivial
    letI : Nontrivial (R ⧸ Module.annihilator R M) :=
      Ideal.Quotient.nontrivial_iff.mpr
        (mt Module.annihilator_eq_top_iff.mp (not_subsingleton M))
    letI : IsLocalRing (R ⧸ Module.annihilator R M) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk (Module.annihilator R M))
        Ideal.Quotient.mk_surjective
    List.TFAE [
      IsIdealOfDefinition (I + Module.annihilator R M),
      IsIdealOfDefinition
        (Ideal.map (Ideal.Quotient.mk (Module.annihilator R M)) I),
      Module.support R (M ⧸ I • (⊤ : Submodule R M)) ⊆ {IsLocalRing.closedPoint R},
      Module.supportDim R (M ⧸ I • (⊤ : Submodule R M)) ≤ 0,
      Module.length R (M ⧸ I • (⊤ : Submodule R M)) < ⊤] := by
  have : Nontrivial M := (I • (⊤ : Submodule R M)).mkQ_surjective.nontrivial
  have hann : Module.annihilator R M ≠ ⊤ :=
    mt Module.annihilator_eq_top_iff.mp (not_subsingleton M)
  have : Nontrivial (R ⧸ Module.annihilator R M) := Ideal.Quotient.nontrivial_iff.mpr hann
  have : IsLocalRing (R ⧸ Module.annihilator R M) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (Module.annihilator R M))
      Ideal.Quotient.mk_surjective
  let N := M ⧸ I • (⊤ : Submodule R M)
  let J : Ideal R := I + Module.annihilator R M
  have hsupp : Module.support R N = PrimeSpectrum.zeroLocus (J : Set R) := by
    rw [Module.support_quotient, Module.support_eq_zeroLocus,
      ← PrimeSpectrum.zeroLocus_sup]
    simp [J, sup_comm]
  have hclosed : Module.support R N ⊆ {IsLocalRing.closedPoint R} ↔
      IsIdealOfDefinition J := by
    rw [hsupp, ← zeroLocus_maximalIdeal, isIdealOfDefinition_iff]
    refine ⟨fun h => le_antisymm ?_ ?_, fun h => ?_⟩
    · have hmem : IsLocalRing.closedPoint R ∈ PrimeSpectrum.zeroLocus (J : Set R) :=
        hsupp ▸ IsLocalRing.closedPoint_mem_support R N
      exact (Ideal.IsMaximal.isPrime (IsLocalRing.maximalIdeal.isMaximal R)).radical_le_iff.mpr
        fun x hx => hmem hx
    · exact (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff J
        (IsLocalRing.maximalIdeal R)).mp (by simpa using h)
    · exact (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff J
        (IsLocalRing.maximalIdeal R)).mpr (by simp [h])
  tfae_have 1 ↔ 3 := hclosed.symm
  tfae_have 3 ↔ 4 := support_subset_closedPoint_iff_supportDim_nonpos
  tfae_have 3 ↔ 5 := support_subset_closedPoint_iff_length_lt_top
  tfae_have 1 ↔ 2 := isIdealOfDefinition_add_iff_map I hann
  tfae_finish

end Ideal
