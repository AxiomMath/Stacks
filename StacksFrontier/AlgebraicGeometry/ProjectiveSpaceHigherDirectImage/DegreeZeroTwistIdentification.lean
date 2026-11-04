module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TwistCohomologyMonomial
public import StacksFrontier.LinearAlgebra.SymmetricPower.FreePresentation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The degree-zero identification for the twists on projective space

For a commutative ring `R`, for `n = m + 1 ≥ 1` and an integer `d ≥ 0`, Serre's computation
identifies the degree-zero cohomology of a twisting sheaf on `𝐏^n_R` with a symmetric power of
the free module of rank `n + 1`,

  `H^0(𝐏(E), 𝒪(d)) ≅ Sym^d(E)`,  `E = R^{⊕ n + 1}`,

which is the `q = 0` row of [Stacks, Tag 01XX] read on the cohomology module; for `d < 0` the
same row reads as a vanishing, the symmetric power of a negative degree being zero.

The companion module `StacksDraft.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage`
`.TopDegreeTwistIdentification` records the `q = n` row at the same model and the same level, and
the vanishing row `q ≠ 0, n` is `(Stacks.ProjectiveSpace.Cohomology.serreTwistCohomology R m d)`
`.vanishing`, in the `Hgroup` spelling
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.MiddleVanishing`
`.isZero_Hgroup_twistingSheaf_of_ne`.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveBundleVanishing.DegreeZero.degreeZeroTwistIsoSym`:
  `H^0(𝐏^n_R, 𝒪(d)) ≅ Sym^d(R^{n+1})` as `R`-modules, for `d ≥ 0` carried as a natural number.
* `Stacks.AlgebraicGeometry.ProjectiveBundleVanishing.DegreeZero.isZero_degreeZeroTwist_of_neg`:
  the complementary half of the same row, `H^0(𝐏^n_R, 𝒪(d)) = 0` for `d < 0`.
* `Stacks.AlgebraicGeometry.ProjectiveBundleVanishing.DegreeZero`
  `.not_isZero_degreeZeroTwist_of_nonneg`: for a nontrivial ring and `d ≥ 0` the cohomology is
  **nonzero**, so the first statement is not a comparison of two zero objects; with the second it
  pins the sign condition exactly.

## Implementation notes

The degree is carried as a natural number `k` with `(k : ℤ) = d`, rather than as `d.toNat`, so that
a consumer never has to transport along `Int.toNat_of_nonneg`.

## References

* [Stacks Project, Tag 01XX](https://stacks.math.columbia.edu/tag/01XX)
* [Stacks Project, Tag 01XU](https://stacks.math.columbia.edu/tag/01XU)
-/


open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveBundleVanishing.DegreeZero

@[expose] public noncomputable section

/-- **The `q = 0` row of [Stacks, Tag 01XX]**, for an affine base and a free module: for a
commutative ring `R`, for `n = m + 1 ≥ 1`, an integer `d` and a natural number `k` with
`(k : ℤ) = d`,

  `H^0(𝐏(E), 𝒪(d)) ≅ Sym^k(E)`,  `E = R^{⊕ n+1}`,

as `R`-modules. -/
public def degreeZeroTwistIsoSym (R : Type u) [CommRing R] (m : ℕ) (d : ℤ) (k : ℕ)
    (hk : (k : ℤ) = d) :
    Stacks.ProjectiveSpace.Cohomology.twistCohomology R (m + 1) d 0 ≅
      ModuleCat.of R (SymPow.symmetricPower k R (Fin (m + 1 + 1) → R)) := by
  have hd : 0 ≤ d := by omega
  have hk' : d.toNat = k := by omega
  refine (Stacks.ProjectiveSpace.Cohomology.serreTwistCohomology R m d).degreeZeroPolynomial hd
    ≪≫ ?_
  rw [hk']
  exact (SymPow.symmetricPowerEquivHomogeneousSubmodule
    (Pi.basisFun R (Fin (m + 1 + 1))) k).symm.toModuleIso

/-- **The negative-twist half of the `q = 0` row of [Stacks, Tag 01XX]**: for `n = m + 1 ≥ 1` and
`d < 0`, `H^0(𝐏^n_R, 𝒪(d)) = 0`, which is `Sym^d(R^{n+1})` read as zero in negative degrees. -/
@[sga "6 VI 2.8" "partial"]
public theorem isZero_degreeZeroTwist_of_neg (R : Type u) [CommRing R] (m : ℕ) {d : ℤ}
    (hd : d < 0) :
    IsZero (Stacks.ProjectiveSpace.Cohomology.twistCohomology R (m + 1) d 0) :=
  Stacks.ProjectiveSpace.Cohomology.isZero_twistCohomology R (m + 1) d 0 <| by
    rintro (⟨-, h⟩ | ⟨h, -⟩) <;> omega

/-- **The left side of `degreeZeroTwistIsoSym` is nonzero**: for a nontrivial ring, `n = m + 1 ≥ 1`
and `d ≥ 0`, `H^0(𝐏^n_R, 𝒪(d)) ≠ 0`. -/
public theorem not_isZero_degreeZeroTwist_of_nonneg (R : Type u) [CommRing R] [Nontrivial R]
    (m : ℕ) {d : ℤ} (hd : 0 ≤ d) :
    ¬ IsZero (Stacks.ProjectiveSpace.Cohomology.twistCohomology R (m + 1) d 0) := by
  intro h
  have h2 := h.of_iso
    (((Stacks.ProjectiveSpace.Cohomology.serreTwistCohomology R m d).degreeZeroPolynomial
      hd).symm)
  have hs : Subsingleton
      ↥(MvPolynomial.homogeneousSubmodule (Fin (m + 1 + 1)) R d.toNat) :=
    ModuleCat.subsingleton_of_isZero h2
  have hmem : (MvPolynomial.X 0 : MvPolynomial (Fin (m + 1 + 1)) R) ^ d.toNat ∈
      MvPolynomial.homogeneousSubmodule (Fin (m + 1 + 1)) R d.toNat := by
    simpa using (MvPolynomial.isHomogeneous_X R (0 : Fin (m + 1 + 1))).pow d.toNat
  have he : (⟨(MvPolynomial.X 0 : MvPolynomial (Fin (m + 1 + 1)) R) ^ d.toNat, hmem⟩ :
      ↥(MvPolynomial.homogeneousSubmodule (Fin (m + 1 + 1)) R d.toNat)) = 0 := hs.elim _ _
  have hz : (MvPolynomial.X 0 : MvPolynomial (Fin (m + 1 + 1)) R) ^ d.toNat = 0 := by
    simp at he
  simp [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_eq_zero] at hz

end

end Stacks.AlgebraicGeometry.ProjectiveBundleVanishing.DegreeZero
