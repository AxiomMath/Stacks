module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianTorsion.KernelPointCount
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVarietyTorsionStructure
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.CubeRelationSiblings.ZPowFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianTorsion.Cube.AssemblyCubeRelation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The prime-to-characteristic torsion of an abelian variety

Let `k` be an algebraically closed field, `A` an abelian variety over `k` of dimension `g` and
`n ≥ 1` invertible in `k`.  This file proves the two statements

* for every `d ∣ n`, exactly `d ^ (2 g)` of the `k`-points of `A` are killed by `d`, and
* `A(k)[n] ≃+ (ℤ/nℤ)^{2g}`,

part (7) of [Stacks, Tag 03RP](https://stacks.math.columbia.edu/tag/03RP), from the cube relation
for `A` (`Stacks.Groupoids.hasCubeRelation_of_isAlgClosed`, `Cube/AssemblyCubeRelation.lean`),
and records the forms which take the theorem of the cube for `A × A × A`
(`Stacks.Groupoids.HasTheoremOfTheCube A`) or the cube relation as an argument.

## Main results

* `Stacks.Groupoids.natCard_kernelPoints_dvd`: for every `d ∣ n`, exactly `d ^ (2 g)` of the
  `k`-points of `A` are killed by `d`.
* `Stacks.Groupoids.nonempty_torsionBy_addEquiv_pi_zmod` (also under the name
  `AlgebraicGeometry.IsAbelianVariety.nonempty_torsionBy_points_addEquiv_pi_zmod_of_isUnit`):
  `A(k)[n] ≃+ (ℤ/nℤ)^{2g}`.

* `Stacks.Groupoids.natCard_kernelPoints_dvd_of_hasTheoremOfTheCube`: the point count, for
  every divisor of `n`.
* `Stacks.Groupoids.nonempty_torsionBy_addEquiv_pi_zmod_of_hasTheoremOfTheCube`: the group
  structure of the `n`-torsion.
* `Stacks.Groupoids.natCard_kernelPoints_dvd_of_hasCubeRelation` and
  `Stacks.Groupoids.nonempty_torsionBy_addEquiv_pi_zmod_of_hasCubeRelation`: the same two
  statements from the cube relation (`Stacks.Groupoids.HasCubeRelation A`) alone.

## Implementation notes

Both pairs of statements are instances of
`Stacks.Groupoids.natCard_kernelPoints_dvd_of_isFiniteLocallyFreeOfRank`, whose input is the
degree of multiplication by a nonzero integer `d`: finite locally free of rank `|d| ^ (2 dim A)`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Groupoids

variable {k : Type u} [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
  [AlgebraicGeometry.IsAbelianVariety k A]

/-- A divisor `d` of `n ≥ 1` with `n` invertible in `R` is nonzero and invertible in `R`. -/
private theorem ne_zero_and_isUnit_of_dvd {R : Type*} [CommRing R] {n d : ℕ} (hn : 1 ≤ n)
    (hnk : IsUnit (n : R)) (hd : d ∣ n) : d ≠ 0 ∧ IsUnit (d : R) :=
  ⟨(Nat.pos_of_dvd_of_pos hd hn).ne', isUnit_of_dvd_unit (Nat.cast_dvd_cast hd) hnk⟩

/-- **The point count from the degree of `[d]`.** If multiplication by every nonzero integer `d` on
`A` is finite locally free of rank `|d| ^ (2 dim A)`, then for `n ≥ 1` invertible in `k` and every
divisor `d` of `n`, exactly `d ^ (2 dim A)` of the `k`-points of `A` are killed by `d`. -/
theorem natCard_kernelPoints_dvd_of_isFiniteLocallyFreeOfRank
    (hrank : ∀ d : ℤ, d ≠ 0 → Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((𝟙 A : A ⟶ A) ^ d).left (d.natAbs ^ (2 * abelianVarietyDimension A)))
    (n : ℕ) (hn : 1 ≤ n) (hnk : IsUnit (n : k)) (d : ℕ) (hd : d ∣ n) :
    Nat.card {p : 𝟙_ (Over (Spec (.of k))) ⟶ A // p ≫ (𝟙 A : A ⟶ A) ^ (d : ℤ) = η[A]} =
      d ^ (2 * abelianVarietyDimension A) := by
  obtain ⟨hd0, hdk⟩ := ne_zero_and_isUnit_of_dvd hn hnk hd
  have h := hrank (d : ℤ) (by exact_mod_cast hd0)
  rw [Int.natAbs_natCast] at h
  exact natCard_kernelPoints_eq_of_isFiniteLocallyFreeOfRank A (d : ℤ) (by simpa using hdk) _ h

/-- From the theorem of the cube for `A`: for `n ≥ 1` invertible in `k` and every divisor `d` of
`n`, exactly `d ^ (2 dim A)` of the `k`-points of `A` are killed by multiplication by `d`. -/
theorem natCard_kernelPoints_dvd_of_hasTheoremOfTheCube (hcube : HasTheoremOfTheCube A)
    (n : ℕ) (hn : 1 ≤ n) (hnk : IsUnit (n : k)) (d : ℕ) (hd : d ∣ n) :
    Nat.card {p : 𝟙_ (Over (Spec (.of k))) ⟶ A // p ≫ (𝟙 A : A ⟶ A) ^ (d : ℤ) = η[A]} =
      d ^ (2 * abelianVarietyDimension A) := by
  obtain ⟨hd0, hdk⟩ := ne_zero_and_isUnit_of_dvd hn hnk hd
  exact natCard_kernelPoints_of_hasTheoremOfTheCube A hcube d hd0 hdk

/-- From the theorem of the cube for `A`: for `n ≥ 1` invertible in `k`, the `n`-torsion of the
group of `k`-points of `A` is isomorphic to `(ℤ/nℤ)^{2 dim A}`. -/
theorem nonempty_torsionBy_addEquiv_pi_zmod_of_hasTheoremOfTheCube
    (hcube : HasTheoremOfTheCube A) (n : ℕ) (hn : 1 ≤ n) (hnk : IsUnit (n : k)) :
    letI : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
    Nonempty (Submodule.torsionBy ℤ (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) (n : ℤ) ≃+
      (Fin (2 * abelianVarietyDimension A) → ZMod n)) :=
  AlgebraicGeometry.IsAbelianVariety.nonempty_torsionBy_points_addEquiv_pi_zmod A n hn hnk
    (natCard_kernelPoints_dvd_of_hasTheoremOfTheCube A hcube n hn hnk)

/-- From the cube relation for `A`: for `n ≥ 1` invertible in `k` and every divisor `d` of `n`,
exactly `d ^ (2 dim A)` of the `k`-points of `A` are killed by multiplication by `d`. -/
theorem natCard_kernelPoints_dvd_of_hasCubeRelation (hcr : HasCubeRelation A)
    (n : ℕ) (hn : 1 ≤ n) (hnk : IsUnit (n : k)) (d : ℕ) (hd : d ∣ n) :
    Nat.card {p : 𝟙_ (Over (Spec (.of k))) ⟶ A // p ≫ (𝟙 A : A ⟶ A) ^ (d : ℤ) = η[A]} =
      d ^ (2 * abelianVarietyDimension A) :=
  natCard_kernelPoints_dvd_of_isFiniteLocallyFreeOfRank A
    (fun d hd => isFiniteLocallyFreeOfRank_zpow_id_left_of_hasCubeRelation A hcr d hd)
    n hn hnk d hd

/-- From the cube relation for `A`: for `n ≥ 1` invertible in `k`, the `n`-torsion of the group of
`k`-points of `A` is isomorphic to `(ℤ/nℤ)^{2 dim A}`. -/
theorem nonempty_torsionBy_addEquiv_pi_zmod_of_hasCubeRelation
    (hcr : HasCubeRelation A) (n : ℕ) (hn : 1 ≤ n) (hnk : IsUnit (n : k)) :
    letI : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
    Nonempty (Submodule.torsionBy ℤ (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) (n : ℤ) ≃+
      (Fin (2 * abelianVarietyDimension A) → ZMod n)) :=
  AlgebraicGeometry.IsAbelianVariety.nonempty_torsionBy_points_addEquiv_pi_zmod A n hn hnk
    (natCard_kernelPoints_dvd_of_hasCubeRelation A hcr n hn hnk)

/-- **The number of `k`-points of an abelian variety killed by `d`.** Let `k` be algebraically
closed, `A` an abelian variety over `k`, `n ≥ 1` invertible in `k` and `d` a divisor of `n`. Then
exactly `d ^ (2 dim A)` of the `k`-points of `A` are killed by multiplication by `d`. -/
theorem natCard_kernelPoints_dvd (n : ℕ) (hn : 1 ≤ n) (hnk : IsUnit (n : k)) (d : ℕ)
    (hd : d ∣ n) :
    Nat.card {p : 𝟙_ (Over (Spec (.of k))) ⟶ A // p ≫ (𝟙 A : A ⟶ A) ^ (d : ℤ) = η[A]} =
      d ^ (2 * abelianVarietyDimension A) :=
  natCard_kernelPoints_dvd_of_hasCubeRelation A (hasCubeRelation_of_isAlgClosed A) n hn hnk d hd

/-- **The `n`-torsion of an abelian variety, `n` invertible.** Let `k` be algebraically closed,
`A` an abelian variety over `k` and `n ≥ 1` invertible in `k`. Then the `n`-torsion of the group
of `k`-points of `A` is isomorphic to `(ℤ/nℤ)^{2 dim A}`; this is part (7) of
[Stacks, Tag 03RP](https://stacks.math.columbia.edu/tag/03RP). -/
theorem nonempty_torsionBy_addEquiv_pi_zmod (n : ℕ) (hn : 1 ≤ n) (hnk : IsUnit (n : k)) :
    letI : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
    Nonempty (Submodule.torsionBy ℤ (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) (n : ℤ) ≃+
      (Fin (2 * abelianVarietyDimension A) → ZMod n)) :=
  nonempty_torsionBy_addEquiv_pi_zmod_of_hasCubeRelation A (hasCubeRelation_of_isAlgClosed A)
    n hn hnk

end Stacks.Groupoids

namespace AlgebraicGeometry.IsAbelianVariety

/-- **The `n`-torsion of an abelian variety, `n` invertible**, in the namespace and spelling of
`AlgebraicGeometry.IsAbelianVariety.nonempty_torsionBy_points_addEquiv_pi_zmod`: for `k`
algebraically closed, `A` an abelian variety over `k` and `n ≥ 1` invertible in `k`,
`A(k)[n] ≃+ (ℤ/nℤ)^{2 dim A}`. This is `Stacks.Groupoids.nonempty_torsionBy_addEquiv_pi_zmod`. -/
@[sga "3 XVII 4.5"]
theorem nonempty_torsionBy_points_addEquiv_pi_zmod_of_isUnit
    {k : Type u} [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
    [IsAbelianVariety k A] (n : ℕ) (hn : 1 ≤ n) (hnk : IsUnit (n : k)) :
    letI : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
    Nonempty (Submodule.torsionBy ℤ (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) (n : ℤ) ≃+
      (Fin (2 * Stacks.Groupoids.abelianVarietyDimension A) → ZMod n)) :=
  Stacks.Groupoids.nonempty_torsionBy_addEquiv_pi_zmod A n hn hnk

end AlgebraicGeometry.IsAbelianVariety

end
