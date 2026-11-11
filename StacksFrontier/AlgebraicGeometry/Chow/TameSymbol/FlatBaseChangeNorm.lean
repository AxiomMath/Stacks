module

public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.FlatBaseChange
public import StacksFrontier.RingTheory.Length.NormFlatBaseChangeSupport

/-!
# The norm identity (0GU1) for a localization of a finite algebra

Let `(A, 𝔪, κ) → (A', 𝔪', κ')` be a flat local homomorphism of one-dimensional Noetherian local
rings with `m = length_{A'}(A' / 𝔪A')`, let `B` be a finite `A`-algebra, `𝔪_j` a maximal ideal of
`B` and `B_j = B_{𝔪_j}`. For a nonzerodivisor `π_j` and a unit `u` of `B_j`, the identity (0GU1)
in the proof of Stacks 0EPG,

`(Norm_{κ_j/κ}(ū)^{m_j})^m = ∏_l Norm_{κ'_{j,l}/κ'}(ū)^{m'_{j,l}}`,

is `Stacks.Length.map_norm_pow_length_eq_prod_norm_pow_length_of_isFiniteLength` applied to
`A → A'` and `B_j`: the lengths `m` and `m_j` are finite.

## Main results

* `Stacks.Chow.map_norm_pow_length_eq_prod_norm_pow_length_localization` — the identity (0GU1).

## References

* [Stacks Project, Tag 0EPG](https://stacks.math.columbia.edu/tag/0EPG)
* [Stacks Project, Tag 0GU1](https://stacks.math.columbia.edu/tag/0GU1)
-/

@[expose] public section

open IsLocalRing

open scoped TensorProduct

universe u v w

namespace Stacks.Chow

section NormFibre

/-- The quotient of the localization `B_𝔮` of a finite algebra `B` over a one-dimensional
Noetherian local ring at a maximal ideal `𝔮` by a nonzerodivisor has finite length. -/
theorem isFiniteLength_quotient_localization_of_finite {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (hdim : ringKrullDim A = 1) {B : Type w} [CommRing B]
    [Algebra A B] [Module.Finite A B] (q : MaximalSpectrum B) {π : Localization.AtPrime q.asIdeal}
    (hπ : π ∈ nonZeroDivisors (Localization.AtPrime q.asIdeal)) :
    IsFiniteLength (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime q.asIdeal ⧸ Ideal.span {π}) := by
  have : Ring.KrullDimLE 1 A := krullDimLE_one_of_ringKrullDim_eq_one hdim
  have : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  have : Ring.KrullDimLE 1 B := krullDimLE_one_of_isIntegral A B
  have : IsNoetherianRing (Localization.AtPrime q.asIdeal) :=
    IsLocalization.isNoetherianRing q.asIdeal.primeCompl _ inferInstance
  have := Stacks.Localization.krullDimLE_one_localizationAtPrime q.asIdeal
  exact isFiniteLength_quotient_span_singleton _ hπ

/-- **The identity (0GU1) in the proof of Stacks 0EPG.** Let `(A, 𝔪, κ) → (A', 𝔪', κ')` be a flat
local homomorphism of one-dimensional Noetherian local rings and `m = length_{A'}(A' / 𝔪A')`. Let
`B` be a finite `A`-algebra, `𝔪_j` a maximal ideal of `B` with residue field `κ_j`,
`B_j = B_{𝔪_j}`, `π_j ∈ B_j` a nonzerodivisor and `m_j = length_{B_j}(B_j / π_j B_j)`. For every
unit `u` of `B_j`,

`(Norm_{κ_j/κ}(ū)^{m_j})^m = ∏_l Norm_{κ'_{j,l}/κ'}(ū)^{m'_{j,l}}`

in `κ'`, where `𝔪'_{j,l}` runs over the maximal ideals of `A' ⊗_A B_j` containing `π_j`,
`B'_{j,l}` is the local ring there, `κ'_{j,l}` its residue field and
`m'_{j,l} = length_{B'_{j,l}}(B'_{j,l} / π_j B'_{j,l})`. These maximal ideals are finite in number
and lie over `𝔪'`, the maps `A' → B'_{j,l}` are local and the extensions `κ'_{j,l} / κ'` are
finite (`Stacks.Length.finite_tensorSupport`,
`Stacks.Length.isLocalHom_algebraMap_tensorSupport`,
`Stacks.Length.finite_residueField_tensorSupport`); the length `m` is finite
(`Stacks.Chow.isFiniteLength_closedFibre`) and so is `m_j`
(`Stacks.Chow.isFiniteLength_quotient_localization_of_finite`). -/
@[stacks 0GU1 "with `B'_{j,l}` the local rings of `A' ⊗_A B_j` at its maximal ideals containing
`π_j`; at a maximal ideal of `B' = A' ⊗_A B` over `𝔪_j` not containing `π_j` the factor is `1`"]
theorem map_norm_pow_length_eq_prod_norm_pow_length_localization
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {A' : Type v} [CommRing A'] [IsNoetherianRing A'] [IsLocalRing A'] [Algebra A A']
    [IsLocalHom (algebraMap A A')] [Module.Flat A A']
    (hdim : ringKrullDim A = 1) (hdim' : ringKrullDim A' = 1)
    {B : Type w} [CommRing B] [Algebra A B] [Module.Finite A B] (q : MaximalSpectrum B)
    {π : Localization.AtPrime q.asIdeal}
    (hπ : π ∈ nonZeroDivisors (Localization.AtPrime q.asIdeal))
    (u : (Localization.AtPrime q.asIdeal)ˣ) :
    letI := Stacks.Length.isLocalHom_algebraMap_localization (A := A) q
    letI := Stacks.Length.finite_residueField A q
    letI := @Fintype.ofFinite _ (Stacks.Length.finite_tensorSupport (A := A) (S := A')
      (isFiniteLength_quotient_localization_of_finite hdim q hπ))
    ResidueField.map (algebraMap A A')
      ((Algebra.norm (ResidueField A)
          (residue (Localization.AtPrime q.asIdeal) (u : Localization.AtPrime q.asIdeal)) ^
        (Module.length (Localization.AtPrime q.asIdeal)
          (Localization.AtPrime q.asIdeal ⧸ Ideal.span {π})).toNat) ^
        (Module.length A' (A' ⧸ Ideal.map (algebraMap A A') (maximalIdeal A))).toNat) =
      ∏ r : Stacks.Length.tensorSupport A A' π,
        letI := Stacks.Length.isLocalHom_algebraMap_tensorSupport
          (isFiniteLength_quotient_localization_of_finite hdim q hπ) r
        Algebra.norm (ResidueField A') (residue (Localization.AtPrime r.1.asIdeal)
            (algebraMap (A' ⊗[A] Localization.AtPrime q.asIdeal) (Localization.AtPrime r.1.asIdeal)
              (Algebra.TensorProduct.includeRight (u : Localization.AtPrime q.asIdeal)))) ^
          (Module.length (Localization.AtPrime r.1.asIdeal) (Localization.AtPrime r.1.asIdeal ⧸
            Ideal.span {(algebraMap (A' ⊗[A] Localization.AtPrime q.asIdeal)
              (Localization.AtPrime r.1.asIdeal)
                (Algebra.TensorProduct.includeRight π))})).toNat := by
  have := Stacks.Length.isLocalHom_algebraMap_localization (A := A) q
  have := Stacks.Length.finite_residueField A q
  have hm : Module.length A' (A' ⧸ extendedMaximalIdeal A A') =
      (Module.length A' (A' ⧸ Ideal.map (algebraMap A A') (maximalIdeal A))).toNat :=
    (ENat.natCast_toNat (Module.length_ne_top_iff.mpr (isFiniteLength_closedFibre hdim hdim'))).symm
  exact Stacks.Length.map_norm_pow_length_eq_prod_norm_pow_length_of_isFiniteLength π
    (u : Localization.AtPrime q.asIdeal) (isFiniteLength_quotient_localization_of_finite hdim q hπ)
    hm

end NormFibre

end Stacks.Chow

end
