module

public import StacksFrontier.RingTheory.Dualizing.Gluing
public import StacksFrontier.RingTheory.Dualizing.NormalizedInjectiveAmplitude
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.Normalized

/-!
# The degrees in which a normalized dualizing complex has cohomology

Let `A` be a Noetherian local ring of dimension `d` and let `ω_A^•` be a normalized dualizing
complex. Then `H^i(ω_A^•)` can be nonzero only for `-d ≤ i ≤ 0`.

## Main results

* `Dualizing.isZero_homology_of_pos` — no cohomology in positive degrees.
* `Dualizing.mem_Icc_of_not_isZero_homology` — nonvanishing cohomology forces `i ∈ [-d, 0]`.
* `Dualizing.mem_Icc_of_nontrivial_homology` — the same with nonvanishing read as
  `Nontrivial` of the underlying module.

## References

* [Stacks Project, Tag 0A7U](https://stacks.math.columbia.edu/tag/0A7U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

/-- **A normalized dualizing complex has no cohomology in positive degrees.** -/
theorem isZero_homology_of_pos (K : DerivedCategory (ModuleCat.{u} A))
    (hK : IsNormalizedDualizingComplex.{u, u} K) (d : ℕ)
    (hd : ringKrullDim A = (d : WithBot ℕ∞)) (i : ℤ) (hi : 0 < i) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K) :=
  isZero_homology_of_hasInjectiveAmplitude
    (hasInjectiveAmplitude_neg_ringKrullDim K hK d hd) i (Or.inr hi)

/-- **The cohomology of a normalized dualizing complex lives in degrees `-d` through `0`.** Over
a Noetherian local ring of dimension `d`, if `H^i(ω_A^•) ≠ 0` then `-d ≤ i ≤ 0`. -/
theorem mem_Icc_of_not_isZero_homology (K : DerivedCategory (ModuleCat.{u} A))
    (hK : IsNormalizedDualizingComplex.{u, u} K) (d : ℕ)
    (hd : ringKrullDim A = (d : WithBot ℕ∞)) (i : ℤ)
    (hi : ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K)) :
    i ∈ Set.Icc (-(d : ℤ)) 0 := by
  refine ⟨?_, ?_⟩
  · by_contra hlow
    exact hi (isZero_homology_of_lt_neg_ringKrullDim K hK d hd i (by omega))
  · by_contra hhigh
    exact hi (isZero_homology_of_pos K hK d hd i (by omega))

/-- Over a Noetherian local ring of dimension `d`, if the underlying module of `H^i(ω_A^•)` is
nontrivial then `-d ≤ i ≤ 0`. -/
theorem mem_Icc_of_nontrivial_homology (K : DerivedCategory (ModuleCat.{u} A))
    (hK : IsNormalizedDualizingComplex.{u, u} K) (d : ℕ)
    (hd : ringKrullDim A = (d : WithBot ℕ∞)) (i : ℤ)
    (hi : Nontrivial ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K)) :
    i ∈ Set.Icc (-(d : ℤ)) 0 :=
  mem_Icc_of_not_isZero_homology K hK d hd i fun hzero =>
    (not_subsingleton_iff_nontrivial.mpr hi) (ModuleCat.isZero_iff_subsingleton.mp hzero)

end Dualizing

end
