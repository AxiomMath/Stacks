module

public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.TorsionCommonRefinement
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.Refinement

/-!
# Stacks 0EAR: the formula of Stacks 0EAQ is independent of the auxiliary extension

Let `(A, 𝔪)` be a one-dimensional Noetherian local ring and let `a₁, a₂ ∈ A` be nonzerodivisors.
Stacks 0EAG produces a finite ring extension `A ⊆ B` with `B / A` annihilated by a power of `𝔪`,
a nonzerodivisor `π_𝔮 ∈ B_𝔮` at each maximal ideal of `B` and factorizations
`a_i = u_{i, 𝔮} π_𝔮^{e_{i, 𝔮}}` — an `AlgebraicGeometry.TameSymbolPreparation` — and the formula
Stacks 0EAQ reads

`∂_A(a₁, a₂) = ∏_𝔮 Norm_{κ(𝔮)/κ(𝔪)}((-1)^{e_{1,𝔮}e_{2,𝔮}} u_{1,𝔮}^{e_{2,𝔮}} u_{2,𝔮}^{-e_{1,𝔮}}
  mod 𝔮)^{m_𝔮}`,  `m_𝔮 = length_{B_𝔮}(B_𝔮 / π_𝔮 B_𝔮)`.

Stacks 0EAR asserts that the right-hand side — `Stacks.Chow.preparationSymbolValue` — depends
neither on the local factorizations nor on `B`. The first half is
`Stacks.Chow.preparationSymbolValue_eq_of_preparations`. This file proves the second half, which
completes Stacks 0EAR.

The argument is the source's. Two extensions `B`, `B'` of the above kind are compared through
the common refinement

`C = (B ⊗_A B') / (𝔪`-power torsion`)`,

which is `Stacks.Chow.TorsionCommonRefinement` and is an extension of the same kind refining
both. Over `C` the value of the formula can be computed from one fixed choice of local
factorizations at the
maximal ideals of `C`, by `Stacks.Chow.preparationSymbolValue_eq_prod_norm_factorizationValue`,
and that computation mentions neither `B` nor `B'`.

## Main results

* `Stacks.Chow.preparationSymbolValue_eq_of_extensions` — Stacks 0EAR for the choice of the
  auxiliary extension: two preparations of the same family over two finite extensions of the kind
  Stacks 0EAG produces give the same element of `κ(𝔪)^*`.

## Implementation notes

All the instance data that the tower `A ⊆ B ⊆ C` needs is derived here from the finiteness of
`A → B` and `A → B'` and from the two non-associated-prime hypotheses; nothing is assumed. The
`B'`-side fibre hypotheses come from the `_right` corollaries of
`StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.TorsionCommonRefinement` — reusing the `B`-side ones
with the roles of `B` and `B'` exchanged would name a different ring, namely
`TorsionCommonRefinement A B' B`.

## References

* [Stacks Project, Tag 0EAQ](https://stacks.math.columbia.edu/tag/0EAQ)
* [Stacks Project, Tag 0EAR](https://stacks.math.columbia.edu/tag/0EAR)
* [Stacks Project, Tag 0EAG](https://stacks.math.columbia.edu/tag/0EAG)
-/

@[expose] public section

open IsLocalRing AlgebraicGeometry Stacks.Localization

universe u v w

namespace Stacks.Chow

section Independence

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
  {B : Type v} [CommRing B] [Algebra A B] {B' : Type w} [CommRing B'] [Algebra A B']

/-- **Stacks 0EAR for the choice of the auxiliary extension.** Let `(A, 𝔪)` be a one-dimensional
Noetherian local ring and let `a` be a finite family in `A`. Let `A ⊆ B` and `A ⊆ B'` be two
finite extensions of the kind Stacks 0EAG produces — module finite, with `𝔪` not an associated
prime — each carrying a tame-symbol preparation of `a`. Then the two preparations give the same
value of the formula Stacks 0EAQ:

`∏_𝔮 Norm_{κ(𝔮)/κ(𝔪)}(factor at 𝔮) = ∏_{𝔮'} Norm_{κ(𝔮')/κ(𝔪)}(factor at 𝔮')`.

Together with `Stacks.Chow.preparationSymbolValue_eq_of_preparations`, which is the independence
of the local factorizations at a fixed extension, this is Stacks 0EAR: the right-hand side of
Stacks 0EAQ is a well-defined element of `κ(𝔪)^*`, a function of `A` and the family alone.

The proof is the source's. Both extensions map into the common refinement
`C = (B ⊗_A B') / (𝔪`-power torsion`)`, which is again module finite over `A` with `𝔪` not an
associated prime and with `𝔪`-power torsion cokernel, and into which both `B` and `B'` inject.
Fix any simultaneous power factorization of `a` at each maximal ideal of `C` — the preparation
over `B` pushes forward to one, so there is such a choice. By
`Stacks.Chow.preparationSymbolValue_eq_prod_norm_factorizationValue` each of the two values equals
the value computed from that fixed choice over `C`, which mentions neither `B` nor `B'`. -/
theorem preparationSymbolValue_eq_of_extensions
    [Fintype (MaximalSpectrum B)] [Fintype (MaximalSpectrum B')]
    [∀ q : MaximalSpectrum B, IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal))]
    [∀ q' : MaximalSpectrum B', IsLocalHom (algebraMap A (Localization.AtPrime q'.asIdeal))]
    {n : ℕ} {a : Fin n → A}
    (P : TameSymbolPreparation a B) (P' : TameSymbolPreparation a B')
    (hB : ¬ IsAssociatedPrime (maximalIdeal A) B)
    (hB' : ¬ IsAssociatedPrime (maximalIdeal A) B')
    (i j : Fin n) :
    preparationSymbolValue P i j = preparationSymbolValue P' i j := by
  let := P.finite
  let := P'.finite
  have hinj := P.algebraMap_injective
  have hinj' := P'.algebraMap_injective
  obtain ⟨N, hN⟩ := P.quotient_annihilated_by_maximalIdeal_power
  obtain ⟨N', hN'⟩ := P'.quotient_annihilated_by_maximalIdeal_power
  -- The two extensions, and the common refinement, are Noetherian of dimension at most one.
  have : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  have : IsNoetherianRing B' := IsNoetherianRing.of_finite A B'
  have : Ring.KrullDimLE 1 B := Stacks.Chow.krullDimLE_one_of_moduleFinite (A := A)
  have : Ring.KrullDimLE 1 B' := Stacks.Chow.krullDimLE_one_of_moduleFinite (A := A)
  have : IsNoetherianRing (TorsionCommonRefinement A B B') :=
    IsNoetherianRing.of_finite A (TorsionCommonRefinement A B B')
  have : Ring.KrullDimLE 1 (TorsionCommonRefinement A B B') :=
    Stacks.Chow.krullDimLE_one_of_moduleFinite (A := A)
  -- The maximal spectra are finite.
  let : Fintype (MaximalSpectrum (TorsionCommonRefinement A B B')) :=
    @Fintype.ofFinite _ (Stacks.Length.finite_maximalSpectrum (A := A)
      (B := TorsionCommonRefinement A B B'))
  let : ∀ q : MaximalSpectrum B, Fintype (MaximalSpectrum (Localization
      (Algebra.algebraMapSubmonoid (TorsionCommonRefinement A B B') q.asIdeal.primeCompl))) :=
    fun q => @Fintype.ofFinite _
      (finite_maximalSpectrum_semilocalization B (TorsionCommonRefinement A B B') q)
  let : ∀ q' : MaximalSpectrum B', Fintype (MaximalSpectrum (Localization
      (Algebra.algebraMapSubmonoid (TorsionCommonRefinement A B B') q'.asIdeal.primeCompl))) :=
    fun q' => @Fintype.ofFinite _
      (finite_maximalSpectrum_semilocalization B' (TorsionCommonRefinement A B B') q')
  -- The local rings along the two towers.
  have : ∀ r : MaximalSpectrum (TorsionCommonRefinement A B B'),
      Ring.KrullDimLE 1 (Localization.AtPrime r.asIdeal) := fun r =>
    krullDimLE_one_localizationAtPrime r.asIdeal
  have : ∀ r : MaximalSpectrum (TorsionCommonRefinement A B B'),
      IsLocalHom (algebraMap A (Localization.AtPrime r.asIdeal)) := fun r =>
    Stacks.Length.isLocalHom_algebraMap_localization r
  -- The local rings of `C` along a fibre are algebras over the local rings of `B`, resp. `B'`.
  let : ∀ (q : MaximalSpectrum B) (v : MaximalSpectrum (Localization
        (Algebra.algebraMapSubmonoid (TorsionCommonRefinement A B B') q.asIdeal.primeCompl))),
      Algebra (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime (v.asIdeal.under (TorsionCommonRefinement A B B'))) := fun q v =>
    Localization.AtPrime.algebraOfLiesOver q.asIdeal
      (v.asIdeal.under (TorsionCommonRefinement A B B'))
  have : ∀ (q : MaximalSpectrum B) (v : MaximalSpectrum (Localization
        (Algebra.algebraMapSubmonoid (TorsionCommonRefinement A B B') q.asIdeal.primeCompl))),
      Localization.AtPrime.IsLiesOverAlgebra q.asIdeal
        (v.asIdeal.under (TorsionCommonRefinement A B B')) := fun _ _ => ⟨rfl⟩
  let : ∀ (q' : MaximalSpectrum B') (v : MaximalSpectrum (Localization
        (Algebra.algebraMapSubmonoid (TorsionCommonRefinement A B B') q'.asIdeal.primeCompl))),
      Algebra (Localization.AtPrime q'.asIdeal)
        (Localization.AtPrime (v.asIdeal.under (TorsionCommonRefinement A B B'))) := fun q' v =>
    Localization.AtPrime.algebraOfLiesOver q'.asIdeal
      (v.asIdeal.under (TorsionCommonRefinement A B B'))
  have : ∀ (q' : MaximalSpectrum B') (v : MaximalSpectrum (Localization
        (Algebra.algebraMapSubmonoid (TorsionCommonRefinement A B B') q'.asIdeal.primeCompl))),
      Localization.AtPrime.IsLiesOverAlgebra q'.asIdeal
        (v.asIdeal.under (TorsionCommonRefinement A B B')) := fun _ _ => ⟨rfl⟩
  -- The fibre hypotheses, on the `B` side and on the `B'` side.
  have hfass : ∀ q : MaximalSpectrum B,
      ¬ IsAssociatedPrime (maximalIdeal (Localization.AtPrime q.asIdeal))
        (Localization (Algebra.algebraMapSubmonoid (TorsionCommonRefinement A B B')
          q.asIdeal.primeCompl)) := fun q =>
    not_isAssociatedPrime_semilocalization_commonRefinement q hinj hB
  have hfinj : ∀ q : MaximalSpectrum B, Function.Injective
      (algebraMap (Localization.AtPrime q.asIdeal)
        (Localization (Algebra.algebraMapSubmonoid (TorsionCommonRefinement A B B')
          q.asIdeal.primeCompl))) := fun q =>
    injective_algebraMap_semilocalization_commonRefinement q hinj' hB hN'
  have hfquot : ∀ q : MaximalSpectrum B, ∃ m : ℕ,
      maximalIdeal (Localization.AtPrime q.asIdeal) ^ m •
          (⊤ : Submodule (Localization.AtPrime q.asIdeal)
            (Localization (Algebra.algebraMapSubmonoid (TorsionCommonRefinement A B B')
              q.asIdeal.primeCompl))) ≤
        LinearMap.range (Algebra.linearMap (Localization.AtPrime q.asIdeal)
          (Localization (Algebra.algebraMapSubmonoid (TorsionCommonRefinement A B B')
            q.asIdeal.primeCompl))) := fun q =>
    exists_pow_smul_le_range_semilocalization_commonRefinement q hN hN'
  have hfass' : ∀ q' : MaximalSpectrum B',
      ¬ IsAssociatedPrime (maximalIdeal (Localization.AtPrime q'.asIdeal))
        (Localization (Algebra.algebraMapSubmonoid (TorsionCommonRefinement A B B')
          q'.asIdeal.primeCompl)) := fun q' =>
    not_isAssociatedPrime_semilocalization_commonRefinement_right (B := B) q' hinj' hB'
  have hfinj' : ∀ q' : MaximalSpectrum B', Function.Injective
      (algebraMap (Localization.AtPrime q'.asIdeal)
        (Localization (Algebra.algebraMapSubmonoid (TorsionCommonRefinement A B B')
          q'.asIdeal.primeCompl))) := fun q' =>
    injective_algebraMap_semilocalization_commonRefinement_right (B' := B') q' hinj hB' hN
  have hfquot' : ∀ q' : MaximalSpectrum B', ∃ m : ℕ,
      maximalIdeal (Localization.AtPrime q'.asIdeal) ^ m •
          (⊤ : Submodule (Localization.AtPrime q'.asIdeal)
            (Localization (Algebra.algebraMapSubmonoid (TorsionCommonRefinement A B B')
              q'.asIdeal.primeCompl))) ≤
        LinearMap.range (Algebra.linearMap (Localization.AtPrime q'.asIdeal)
          (Localization (Algebra.algebraMapSubmonoid (TorsionCommonRefinement A B B')
            q'.asIdeal.primeCompl))) := fun q' =>
    exists_pow_smul_le_range_semilocalization_commonRefinement_right q' hN hN'
  -- One fixed choice of local factorizations at the maximal ideals of the common refinement.
  choose π hπ w e hfac using exists_factorization_localizationAtPrime (B := B) hfass P
  rw [preparationSymbolValue_eq_prod_norm_factorizationValue (C := TorsionCommonRefinement A B B')
      hfass hfinj hfquot P π hπ w e hfac i j,
    preparationSymbolValue_eq_prod_norm_factorizationValue (C := TorsionCommonRefinement A B B')
      hfass' hfinj' hfquot' P' π hπ w e hfac i j]

end Independence

end Stacks.Chow

end
