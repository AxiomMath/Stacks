module

public import StacksFrontier.Homology.DerivedCategory.Monoidal.Invertible
public import StacksFrontier.Homology.Perfect.Local
public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped

/-!
# A pseudo-coherent complex whose derived fibres are a line in one degree

Let `R` be a ring and `K` a pseudo-coherent object of `D(R)` such that for every prime `𝔭` the
derived fibre `K ⊗ᴸ_R κ(𝔭)` has cohomology only in degree `n`, of dimension one there. Then `K`
is locally a shifted unit: every prime has a principal open `D(f)` on which `K_f ≅ R_f[-n]`.
By Stacks 068V the fibre condition makes `K` perfect (of Tor amplitude `[n, n]`), and a perfect
complex with such fibres at the maximal ideals is locally a shifted unit by the minimal
representative of Stacks 0BCD
(`DerivedCategory.Invertible.isLocallyShiftedUnit_of_isPerfect_of_maximalFibre_finrank`).

This is the commutative-algebra step of "a relatively perfect complex whose fibres are invertible
modules in one degree is an invertible module in that degree", used for the relative dualizing
sheaf of a family of nodal curves (Stacks 0E6P, 0E6R).

## Main results

* `StacksDraft.Perfect.isLocallyShiftedUnit_of_isPseudoCoherent_of_fibres`.

## References

* [Stacks Project, Tag 068V](https://stacks.math.columbia.edu/tag/068V)
* [Stacks Project, Tag 0BCD](https://stacks.math.columbia.edu/tag/0BCD)
* [Stacks Project, Tag 0E6R](https://stacks.math.columbia.edu/tag/0E6R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CochainComplex.DerivedExtensionScalars

universe u

namespace StacksDraft.Perfect

-- The fibre criteria are stated at the standard model of `D(R)`.
open scoped Stacks.StandardDerivedModel

variable {R : Type u} [CommRing R]

/-- **A pseudo-coherent complex whose derived fibres are a line in degree `n` is locally `R[-n]`.**
Let `K` be pseudo-coherent with `H^i(K ⊗ᴸ_R κ(𝔭)) = 0` for `i ≠ n` and
`dim_{κ(𝔭)} H^n(K ⊗ᴸ_R κ(𝔭)) = 1` at every prime `𝔭`. Then `K` is locally a shifted unit. -/
theorem isLocallyShiftedUnit_of_isPseudoCoherent_of_fibres
    (K : DerivedCategory (ModuleCat.{u} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (n : ℤ)
    (hzero : ∀ (p : PrimeSpectrum R) (i : ℤ), i ≠ n →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} p.asIdeal.ResidueField) i).obj
        ((totalDerivedExtensionScalars.{u, u, u}
          (algebraMap R p.asIdeal.ResidueField)).functor.obj K)))
    (hrank : ∀ p : PrimeSpectrum R,
      Module.finrank p.asIdeal.ResidueField
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} p.asIdeal.ResidueField) n).obj
          ((totalDerivedExtensionScalars.{u, u, u}
            (algebraMap R p.asIdeal.ResidueField)).functor.obj K)) = 1) :
    DerivedCategory.Invertible.IsLocallyShiftedUnit K := by
  have hvan : ∀ q : PrimeSpectrum R, ∀ i : ℤ, i < n ∨ n < i →
      FibreCohomologyVanishes.{u, u} q.asIdeal K i := fun q i hi =>
    (fibreCohomologyVanishes_iff_isZero_homology.{u, u} q.asIdeal K hK i).2
      (hzero q i (by omega))
  have hperf : IsPerfect K :=
    ((isPerfect_and_torAmplitude_iff_fibreCohomologyVanishes.{u, u} K hK n n).1.2 hvan).1
  refine DerivedCategory.Invertible.isLocallyShiftedUnit_of_isPerfect_of_maximalFibre_finrank K
    hperf fun m hm => ⟨n, fun i => ?_⟩
  let p : PrimeSpectrum R := ⟨m, hm.isPrime⟩
  split_ifs with hi
  · subst hi
    exact hrank p
  · have := ModuleCat.subsingleton_of_isZero (hzero p i hi)
    exact Module.finrank_zero_of_subsingleton

end StacksDraft.Perfect

end
