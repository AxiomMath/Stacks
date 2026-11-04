module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.RelativeSectorMap

/-!
# The contracting homotopy of a relative sector

Let `A` be a ring, let `(B, I, δ)` be a divided power ring which is an `A`-algebra, let `W`
index a family of divided power variables and let `P = B⟨x_w : w ∈ W⟩`.
`Crystalline.DividedPowerPolynomial.relativeSectorMap_dividedPowerDeRham` exhibits the divided
power de Rham differential of `P` on the `K`-sector as the total differential of the bicomplex
`Kos(supp K) ⊗_B Ω^*_{B/A,δ}`: the horizontal differential `1 ⊗ d_B` plus `(-1)^i` times
wedging the Koszul factor by `∑_{w ∈ supp K} e_w`.

This module contracts the Koszul direction.  For a nonempty `supp K` the functional dual to one
of its elements sends the Koszul vector to `1`, so the Koszul identity
`exteriorPower.contraction_comp_wedgeLeft_add_wedgeLeft_comp_contraction` applies; tensored on
the right by the coefficient module `Ωⁱ_{B/A,δ}` it still applies, which is
`exteriorPower.rTensor_contraction_rTensor_wedgeLeft_add_rTensor_wedgeLeft_rTensor_contraction`.

## The signs

The Koszul differential of the sector carries the sign `(-1)^i` of the coefficient degree, and
so does the homotopy: `κ = (-1)^i (1 ⊗ e ∧ ·)` and `h = (-1)^i (1 ⊗ ι_φ)`.  Both composites
`κ h` and `h κ` therefore carry `((-1)^i)^2 = 1`, the signs cancel, and `κ h + h κ = id`
survives verbatim from the unsigned Koszul identity.  Putting the sign into `κ` is what makes
the sector differential of
`Crystalline.DividedPowerPolynomial.relativeSectorMap_dividedPowerDeRham_total` a plain sum of
two maps, with no sign left outside.

## Main definitions

* `Crystalline.DividedPowerPolynomial.sectorFunctional` — the functional dual to a chosen
  variable of `supp K`.
* `Crystalline.DividedPowerPolynomial.relativeSectorKoszulDifferential` — `(-1)^i (1 ⊗ e ∧ ·)`,
  the Koszul direction of the sector differential with its sign.
* `Crystalline.DividedPowerPolynomial.relativeSectorHomotopy` — `(-1)^i (1 ⊗ ι_φ)`, the
  contracting homotopy.

## Main results

* `Crystalline.DividedPowerPolynomial.sectorFunctional_sectorVector` — the functional sends the
  Koszul vector to `1`.
* `Crystalline.DividedPowerPolynomial.relativeSectorMap_dividedPowerDeRham_total` — the sector
  differential as a plain sum of the horizontal and the Koszul differential.
* `Crystalline.DividedPowerPolynomial.relativeSectorKoszul_homotopy` — **`κ h + h κ = id`** on
  the Koszul direction of the sector.
* `Crystalline.DividedPowerPolynomial.relativeSectorKoszul_homotopy_zero` — the degree-zero
  case, `h κ = id` on bidegree `(i, 0)`.

## References

* [Stacks Project, Lemma 60.20.1, Tag 07LC](https://stacks.math.columbia.edu/tag/07LC)
* [Stacks Project, Lemma 60.20.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
-/

@[expose] public noncomputable section

open DividedPowers
open scoped TensorProduct

universe uA uB uW

namespace Crystalline

namespace DividedPowerPolynomial

section Homotopy

variable (A : Type uA) [CommRing A] (B : DividedPowerRing.{uB}) [Algebra A B] (W : Type uW)
  [LinearOrder W]

/-- **The functional dual to a chosen variable of `supp K`.**  Which variable is chosen does not
matter: all that is used is that the functional sends the Koszul vector
`Crystalline.DividedPowerPolynomial.sectorVector` to `1`, and every coordinate functional does.
For `K = 0` the support is empty, there is no choice and the functional is zero; the sector is
then the single bidegree `(i, 0)` and the Koszul direction is not contracted. -/
def sectorFunctional (K : W →₀ ℕ) :
    Module.Dual (B : Type uB) ((K.support : Type uW) →₀ (B : Type uB)) :=
  if h : K ≠ 0 then
    Finsupp.lapply
      (⟨_, (Finsupp.support_nonempty_iff.mpr h).choose_spec⟩ : (K.support : Type uW))
  else 0

/-- **The functional sends the Koszul vector to `1`**, which is the hypothesis of the Koszul
identity. -/
theorem sectorFunctional_sectorVector (K : W →₀ ℕ) (hK : K ≠ 0) :
    sectorFunctional B W K (sectorVector B W K) = 1 := by
  classical
  simp [sectorFunctional, hK, sectorVector, Finsupp.single_apply]

/-- **The Koszul direction of the sector differential**, `(-1)^i (1 ⊗ e ∧ ·)`: wedging the
Koszul factor by the Koszul vector, with the sign of the coefficient degree. -/
def relativeSectorKoszulDifferential (K : W →₀ ℕ) (i j : ℕ) :
    sectorModule A B W K i j →ₗ[(B : Type uB)] sectorModule A B W K i (j + 1) :=
  (-1 : (B : Type uB)) ^ i •
    LinearMap.rTensor (dividedPowerDifferentialForms (A := A) B.dividedPowers i)
      (exteriorPower.wedgeLeft (sectorVector B W K) j)

/-- **The contracting homotopy of the Koszul direction**, `(-1)^i (1 ⊗ ι_φ)`: contracting the
Koszul factor against `Crystalline.DividedPowerPolynomial.sectorFunctional`, with the same sign
as the Koszul differential.

This is `exteriorPower.contraction` tensored with the coefficient module; the Koszul identity it
satisfies there is
`exteriorPower.rTensor_contraction_rTensor_wedgeLeft_add_rTensor_wedgeLeft_rTensor_contraction`.
-/
def relativeSectorHomotopy (K : W →₀ ℕ) (i j : ℕ) :
    sectorModule A B W K i (j + 1) →ₗ[(B : Type uB)] sectorModule A B W K i j :=
  (-1 : (B : Type uB)) ^ i •
    LinearMap.rTensor (dividedPowerDifferentialForms (A := A) B.dividedPowers i)
      (exteriorPower.contraction (sectorFunctional B W K) j)

/-- **The de Rham differential on the `K`-sector, as a plain sum of two maps**: the horizontal
differential `1 ⊗ d_B` and the Koszul differential with its sign absorbed.  This is
`Crystalline.DividedPowerPolynomial.relativeSectorMap_dividedPowerDeRham` with the sign moved
from the ambient `P`-module into the sector, where it belongs. -/
theorem relativeSectorMap_dividedPowerDeRham_total (K : W →₀ ℕ) (i j : ℕ)
    (x : sectorModule A B W K i j) :
    dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) (i + j)
        (relativeSectorMap A B W K i j x) =
      exteriorPower.degCongr (Nat.succ_add i j)
          (relativeSectorMap A B W K (i + 1) j
            (relativeSectorCoefficientDifferential A B W K i j x)) +
        exteriorPower.degCongr (Nat.add_succ i j)
          (relativeSectorMap A B W K i (j + 1)
            (relativeSectorKoszulDifferential A B W K i j x)) := by
  refine Eq.trans (relativeSectorMap_dividedPowerDeRham A B W K i j x) ?_
  refine congrArg (fun z : dividedPowerPolynomialForms A B W (i + j + 1) ↦
    exteriorPower.degCongr (Nat.succ_add i j)
        (relativeSectorMap A B W K (i + 1) j
          (relativeSectorCoefficientDifferential A B W K i j x)) + z) ?_
  have hsign : (algebraMap (B : Type uB) (setIndexedDividedPowerPolynomialAlgebra B W))
      ((-1 : (B : Type uB)) ^ i) =
      (-1 : setIndexedDividedPowerPolynomialAlgebra B W) ^ i := by
    rw [map_pow, map_neg, map_one]
  have hsmul : ∀ y : dividedPowerPolynomialForms A B W (i + (j + 1)),
      ((-1 : (B : Type uB)) ^ i) • y =
        ((-1 : setIndexedDividedPowerPolynomialAlgebra B W) ^ i) • y := fun y ↦ by
    rw [← hsign, algebraMap_smul]
  refine Eq.symm (Eq.trans (congrArg (exteriorPower.degCongr (Nat.add_succ i j))
    (Eq.trans (map_smul (relativeSectorMap A B W K i (j + 1)) ((-1 : (B : Type uB)) ^ i)
        (LinearMap.rTensor (dividedPowerDifferentialForms (A := A) B.dividedPowers i)
          (exteriorPower.wedgeLeft (sectorVector B W K) j) x))
      (hsmul _))) ?_)
  exact map_smul (exteriorPower.degCongr (Nat.add_succ i j)) _ _

/-- The signed Koszul differential after the signed homotopy is the unsigned composite. -/
private theorem relativeSectorKoszulDifferential_relativeSectorHomotopy (K : W →₀ ℕ) (i j : ℕ)
    (x : sectorModule A B W K i (j + 1)) :
    relativeSectorKoszulDifferential A B W K i j (relativeSectorHomotopy A B W K i j x) =
      LinearMap.rTensor (dividedPowerDifferentialForms (A := A) B.dividedPowers i)
        (exteriorPower.wedgeLeft (sectorVector B W K) j)
        (LinearMap.rTensor (dividedPowerDifferentialForms (A := A) B.dividedPowers i)
          (exteriorPower.contraction (sectorFunctional B W K) j) x) := by
  simp [relativeSectorKoszulDifferential, relativeSectorHomotopy, smul_smul, ← mul_pow]

/-- The signed homotopy after the signed Koszul differential is the unsigned composite. -/
private theorem relativeSectorHomotopy_relativeSectorKoszulDifferential (K : W →₀ ℕ) (i j : ℕ)
    (x : sectorModule A B W K i j) :
    relativeSectorHomotopy A B W K i j (relativeSectorKoszulDifferential A B W K i j x) =
      LinearMap.rTensor (dividedPowerDifferentialForms (A := A) B.dividedPowers i)
        (exteriorPower.contraction (sectorFunctional B W K) j)
        (LinearMap.rTensor (dividedPowerDifferentialForms (A := A) B.dividedPowers i)
          (exteriorPower.wedgeLeft (sectorVector B W K) j) x) := by
  simp [relativeSectorKoszulDifferential, relativeSectorHomotopy, smul_smul, ← mul_pow]

/-- **The Koszul direction of the sector is contractible: `κ h + h κ = id`.**

The two signs cancel — each composite carries `((-1)^i)^2 = 1` — so this is the Koszul identity
`exteriorPower.contraction_comp_wedgeLeft_add_wedgeLeft_comp_contraction`, tensored by the
coefficient module `Ωⁱ_{B/A,δ}` and evaluated at `φ e = 1`.  Nothing about the coefficient module
is used: it is an arbitrary `B`-module, which is exactly why the argument survives a nontrivial
divided power ideal `I`. -/
theorem relativeSectorKoszul_homotopy (K : W →₀ ℕ) (hK : K ≠ 0) (i j : ℕ)
    (x : sectorModule A B W K i (j + 1)) :
    relativeSectorKoszulDifferential A B W K i j
          (relativeSectorHomotopy A B W K i j x) +
        relativeSectorHomotopy A B W K i (j + 1)
          (relativeSectorKoszulDifferential A B W K i (j + 1) x) = x := by
  rw [relativeSectorKoszulDifferential_relativeSectorHomotopy,
    relativeSectorHomotopy_relativeSectorKoszulDifferential]
  exact (add_comm _ _).trans
    (exteriorPower.rTensor_contraction_rTensor_wedgeLeft_add_rTensor_wedgeLeft_rTensor_contraction
      (sectorFunctional B W K) (sectorVector B W K)
      (sectorFunctional_sectorVector B W K hK) j x)

/-- **The degree-zero case**: on bidegree `(i, 0)` the homotopy after the Koszul differential is
the identity.  There is no incoming Koszul differential in that bidegree, so this is the whole
of the contraction there. -/
theorem relativeSectorKoszul_homotopy_zero (K : W →₀ ℕ) (hK : K ≠ 0) (i : ℕ)
    (x : sectorModule A B W K i 0) :
    relativeSectorHomotopy A B W K i 0
        (relativeSectorKoszulDifferential A B W K i 0 x) = x := by
  rw [relativeSectorHomotopy_relativeSectorKoszulDifferential]
  exact exteriorPower.rTensor_contraction_rTensor_wedgeLeft_zero
    (sectorFunctional B W K) (sectorVector B W K)
    (sectorFunctional_sectorVector B W K hK) x

end Homotopy

end DividedPowerPolynomial

end Crystalline

end
