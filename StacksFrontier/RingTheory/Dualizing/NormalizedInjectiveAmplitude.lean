module

public import StacksFrontier.Algebra.Homology.InjectiveDimension.Criteria
public import StacksFrontier.RingTheory.Dualizing.ExtDegreeBounds

/-!
# Injective amplitude of a normalized dualizing complex

Let `A` be a Noetherian local ring and let `K` be a normalized dualizing complex over `A`. Then
`K` has injective amplitude in `[-n, 0]` for every natural number `n` bounding the Krull
dimension of `A`, and in particular in `[-dim A, 0]`.

## Main results

* `Dualizing.hasInjectiveAmplitude_of_ringKrullDim_le` — injective amplitude in `[-n, 0]`
  whenever `dim A ≤ n`.
* `Dualizing.hasInjectiveAmplitude_neg_ringKrullDim` — injective amplitude in `[-dim A, 0]`.

## Implementation notes

Quotient modules are shrunk into the universe of the target complex, matching the criterion, and
`dim Supp M = d` is expressed as `Module.supportDim A M = (d : WithBot ℕ∞)`, matching the degree
bound.

## References

* [Stacks Project, Tag 0A7U](https://stacks.math.columbia.edu/tag/0A7U)
* [Stacks Project, Tag 0A5T](https://stacks.math.columbia.edu/tag/0A5T)
-/

@[expose] public section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

/-- The support of a non-zero finite module over a Noetherian local ring of dimension at most `n`
has dimension a natural number at most `n`. -/
private lemma exists_supportDim_eq_nat_le
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (M : Type (max v u)) [AddCommGroup M] [Module A M] [Nontrivial M]
    (n : ℕ) (hn : Module.supportDim A M ≤ (n : WithBot ℕ∞)) :
    ∃ d : ℕ, Module.supportDim A M = (d : WithBot ℕ∞) ∧ d ≤ n := by
  cases hdim : Module.supportDim A M with
  | bot => exact absurd hdim (Module.supportDim_ne_bot_of_nontrivial A M)
  | coe e =>
      rw [hdim] at hn
      have hen : e ≤ (n : ℕ∞) := by exact_mod_cast hn
      lift e to ℕ using ne_top_of_le_ne_top (by simp) hen
      exact ⟨e, rfl, by exact_mod_cast hen⟩

/-- Ext into a normalized dualizing complex from a cyclic quotient module `A/I` vanishes in every
degree outside `[-n, 0]`, for any `n` bounding the dimension of `A`. -/
private lemma subsingleton_ext_quotient_of_ringKrullDim_le
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex.{u, v} K)
    (n : ℕ) (hn : ringKrullDim A ≤ (n : WithBot ℕ∞))
    (I : Ideal A) (i : ℤ) (hi : i < -(n : ℤ) ∨ 0 < i) :
    Subsingleton (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
        (ModuleCat.of A (Shrink.{max v u} (A ⧸ I)))) K i) := by
  rcases subsingleton_or_nontrivial (A ⧸ I) with hsub | hnt
  · have hzero : Limits.IsZero (ModuleCat.of A (Shrink.{max v u} (A ⧸ I))) := by
      rw [ModuleCat.isZero_iff_subsingleton]
      exact (Shrink.linearEquiv A (A ⧸ I)).toEquiv.subsingleton
    exact ⟨fun f g =>
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).map_isZero hzero).eq_of_src f g⟩
  · have hfin : Module.Finite A (Shrink.{max v u} (A ⧸ I)) :=
      Module.Finite.equiv (Shrink.linearEquiv A (A ⧸ I)).symm
    have hle : Module.supportDim A (Shrink.{max v u} (A ⧸ I)) ≤ (n : WithBot ℕ∞) :=
      (Module.supportDim_le_ringKrullDim A _).trans hn
    obtain ⟨d, hd, hdn⟩ :=
      exists_supportDim_eq_nat_le.{u, v} (A := A) (Shrink.{max v u} (A ⧸ I)) n hle
    by_contra hcon
    have hmem := Set.mem_Icc.mp (ext_degree_mem_Icc_of_nontrivial.{u, v} K hK d hd i
      (not_subsingleton_iff_nontrivial.mp hcon))
    omega

/-- **The injective amplitude of a normalized dualizing complex.** Over a Noetherian local ring
`A` of dimension at most `n`, a normalized dualizing complex has injective amplitude in
`[-n, 0]`. -/
theorem hasInjectiveAmplitude_of_ringKrullDim_le
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex.{u, v} K)
    (n : ℕ) (hn : ringKrullDim A ≤ (n : WithBot ℕ∞)) :
    StacksDraft.InjectiveDimension.HasInjectiveAmplitude K (-(n : ℤ)) 0 := by
  have key :=
    StacksDraft.InjectiveDimension.hasInjectiveAmplitude_iff_ext_vanishing_iff_quotient_vanishing
      K (-(n : ℤ)) 0
  exact key.1.2 (key.2.2 fun I i hi =>
    subsingleton_ext_quotient_of_ringKrullDim_le.{u, v} K hK n hn I i hi)

/-- **The injective amplitude of a normalized dualizing complex, at the sharp bound.** Over a
Noetherian local ring `A` of dimension `d`, a normalized dualizing complex has injective
amplitude in `[-d, 0]`. -/
theorem hasInjectiveAmplitude_neg_ringKrullDim
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex.{u, v} K)
    (d : ℕ) (hd : ringKrullDim A = (d : WithBot ℕ∞)) :
    StacksDraft.InjectiveDimension.HasInjectiveAmplitude K (-(d : ℤ)) 0 :=
  hasInjectiveAmplitude_of_ringKrullDim_le.{u, v} K hK d hd.le

end Dualizing
