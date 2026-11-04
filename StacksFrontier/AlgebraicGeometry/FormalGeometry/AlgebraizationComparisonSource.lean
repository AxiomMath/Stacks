module

public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSectionsSerreOneAlternativeHypotheses

/-!
# Stacks 0EFL at the source's hypotheses

`Stacks.Algebraization.exists_isAlgebraizationIdeal` proves Stacks 0EFL from
`Stacks.Algebraization.AlgebraizationHypotheses`, which records the dimension function `δ`
together with its extreme values `δmax`, `δmin` on `V(J) ∩ V(I)`; those exist only when that set
is nonempty. `Stacks.Algebraization.isAlgebraizationIdeal_of_zeroLocus_inter_eq_empty` proves
the empty case. This file states the lemma once, at exactly the source's hypotheses:

1. `A` is `I`-adically complete and has a dualizing complex,
2. no condition,
3. `cd(A, I) ≤ d`,
4. the depth-or-dimension bound at primes outside `V(I) ∪ T`,
5. for some dimension function `δ`, with `δmax` and `δmin` its maximum and minimum on
   `V(J) ∩ V(I)`, the three alternatives at primes outside `V(I) ∪ T` with a specialization in
   `V(J) ∩ V(I)` and depth less than `s`.

Condition (5) is guarded by `V(𝔭) ∩ V(J) ∩ V(I) ≠ ∅`, so `δmax` and `δmin` are only ever
needed when `V(J) ∩ V(I)` is nonempty. There they exist, because a ring with a dualizing complex
has finite Krull dimension (Stacks 0A80), so a dimension function has finite range.

## Main results

* `Stacks.Algebraization.exists_isAlgebraizationIdeal_of_sourceHypotheses`: **Stacks 0EFL**.

## References

* [Stacks Project, Tag 0EFL](https://stacks.math.columbia.edu/tag/0EFL)
* [Stacks Project, Tag 0EFG](https://stacks.math.columbia.edu/tag/0EFG)
* [Stacks Project, Tag 0A80](https://stacks.math.columbia.edu/tag/0A80)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- **Stacks 0EFL.** Let `I, J` be ideals of a Noetherian ring `A`, let `M` be a finite
`A`-module, let `s, d` be integers, and let `T = {𝔭 : V(𝔭) ∩ V(I) ⊆ V(J) ∩ V(I)}`. Assume
1. `A` is `I`-adically complete and has a dualizing complex;
2. (no condition at primes of `V(I)`);
3. `cd(A, I) ≤ d`;
4. if `𝔭 ∉ V(I)`, `𝔭 ∉ T`, then `depth(M_𝔭) ≥ s` or `depth(M_𝔭) + dim((A/𝔭)_𝔮) > d + s` for
   all `𝔮 ∈ V(𝔭) ∩ V(J) ∩ V(I)`;
5. for a dimension function `δ`, with `δmax` and `δmin` the maximum and the minimum of `δ` on
   `V(J) ∩ V(I)`: if `𝔭 ∉ V(I)`, `𝔭 ∉ T`, `V(𝔭) ∩ V(J) ∩ V(I) ≠ ∅` and `depth(M_𝔭) < s`, then
   (a) `dim(Supp(M_𝔭)) < s + 2`, or (b) `δ(𝔭) > d + δmax - 1`, or
   (c) `depth(M_𝔭) + dim((A/𝔭)_𝔮) > d + s + δmax - δmin - 2` for all
   `𝔮 ∈ V(𝔭) ∩ V(J) ∩ V(I)`.

Then there is an ideal `J₀ ⊆ J` with `V(J₀) ∩ V(I) = V(J) ∩ V(I)` such that for every
`J' ⊆ J₀` with `V(J') ∩ V(I) = V(J) ∩ V(I)` the map `RΓ_{J'}(M) → RΓ_J(M)^∧` is an isomorphism
on cohomology in degrees `≤ s` (`Stacks.Algebraization.IsAlgebraizationIdeal`).

The proof is by cases. If `V(J) ∩ V(I)` is empty, `J₀ = J` serves
(`isAlgebraizationIdeal_of_zeroLocus_inter_eq_empty`). Otherwise the extreme values of `δ` on
`V(J) ∩ V(I)` exist (`exists_isGreatest_isLeast_image_dimensionFunction`, using that `A` has
finite Krull dimension by Stacks 0A80), and `exists_isAlgebraizationIdeal` applies. -/
@[stacks 0EFL]
public theorem exists_isAlgebraizationIdeal_of_sourceHypotheses (I J : Ideal A) (s d : ℤ)
    (hcomplete : IsAdicComplete I A)
    (hdual : ∃ ω : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex ω)
    (hcd : Stacks.LocalCohomology.cohomologicalDimension A I I.fg_of_isNoetherianRing ≤ d)
    (h4 : ∀ p : PrimeSpectrum A,
      p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
      p ∉ associatedSubset I J →
      ((enatToEInt
          (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl M)) ≥ (s : EInt)) ∨
        (∀ q : PrimeSpectrum A,
          q ∈ (PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
            PrimeSpectrum.zeroLocus (J : Set A)) ∩
            PrimeSpectrum.zeroLocus (I : Set A) →
          enatToEInt
              (Module.depth (Localization.AtPrime p.asIdeal)
                (maximalIdeal (Localization.AtPrime p.asIdeal))
                (LocalizedModule p.asIdeal.primeCompl M)) +
              krullDimToEInt
                (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
                  p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))) >
            ((d + s : ℤ) : EInt))))
    (h5 : ∃ δ : TopologicalSpace.DimensionFunction (PrimeSpectrum A),
      ∀ δmax δmin : ℤ,
      IsGreatest (δ.toFun '' (PrimeSpectrum.zeroLocus (J : Set A) ∩
        PrimeSpectrum.zeroLocus (I : Set A))) δmax →
      IsLeast (δ.toFun '' (PrimeSpectrum.zeroLocus (J : Set A) ∩
        PrimeSpectrum.zeroLocus (I : Set A))) δmin →
      ∀ p : PrimeSpectrum A,
      p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
      p ∉ associatedSubset I J →
      ((PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
        PrimeSpectrum.zeroLocus (J : Set A)) ∩
        PrimeSpectrum.zeroLocus (I : Set A)).Nonempty →
      enatToEInt
          (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl M)) < (s : EInt) →
      (krullDimToEInt (Module.supportDim (Localization.AtPrime p.asIdeal)
            (LocalizedModule p.asIdeal.primeCompl M)) < ((s + 2 : ℤ) : EInt) ∨
        (d + δmax - 1 < δ.toFun p) ∨
        (∀ q : PrimeSpectrum A,
          q ∈ (PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
            PrimeSpectrum.zeroLocus (J : Set A)) ∩
            PrimeSpectrum.zeroLocus (I : Set A) →
          enatToEInt
              (Module.depth (Localization.AtPrime p.asIdeal)
                (maximalIdeal (Localization.AtPrime p.asIdeal))
                (LocalizedModule p.asIdeal.primeCompl M)) +
              krullDimToEInt
                (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
                  p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))) >
            ((d + s + δmax - δmin - 2 : ℤ) : EInt)))) :
    ∃ J₀ : Ideal A, IsAlgebraizationIdeal (M := M) I J s J₀ := by
  by_cases hne : (PrimeSpectrum.zeroLocus (J : Set A) ∩
      PrimeSpectrum.zeroLocus (I : Set A)).Nonempty
  · obtain ⟨ω, hω⟩ := hdual
    obtain ⟨δ, h5⟩ := h5
    obtain ⟨⟨δmax, hmax⟩, ⟨δmin, hmin⟩⟩ := exists_isGreatest_isLeast_image_dimensionFunction
      (Dualizing.ringKrullDim_lt_top_of_isDualizingComplex hω) δ hne
    exact exists_isAlgebraizationIdeal (M := M) I J s d ω δ.toFun δmax δmin
      { adicComplete := hcomplete
        dualizing := hω
        cohomologicalDimension_le := hcd
        depthOrDimensionBound := h4
        isDimensionFunction := isDimensionFunctionProp_toFun δ
        isGreatest_δmax := hmax
        isLeast_δmin := hmin
        supplementaryBound := h5 δmax δmin hmax hmin }
  · exact ⟨J, isAlgebraizationIdeal_of_zeroLocus_inter_eq_empty (M := M) I J s hcomplete
      (Set.not_nonempty_iff_eq_empty.1 hne)⟩

end Stacks.Algebraization

end
