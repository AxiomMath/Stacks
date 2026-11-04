module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerProdSheaf
public import StacksFrontier.LinearAlgebra.ExteriorPower.HomBaseChange

/-!
# The base-change identification of homomorphisms, on wedges

`exteriorPower.homFreeBaseChangeEquiv` identifies the `R`-linear maps `⋀ⁿ_R(Rⁱ) ⟶ S` with the
`S`-linear functionals on `⋀ⁿ_S(Sⁱ)`. It is built as a composite of three equivalences and is
opaque as it stands; this file evaluates it.

The value of the transported functional on a wedge of base-changed vectors is the value of the
original map on the wedge of those vectors — nothing is added, the identification merely moves the
scalars. In particular on a wedge of standard basis vectors of `Sⁱ` it is the value on the
corresponding wedge of standard basis vectors of `Rⁱ`, which is the form a computation over `R`
delivers and a computation over `S` consumes.

## Main results

* `exteriorPower.homFreeBaseChangeEquiv_apply_ιMulti_baseChange`: **the identification evaluated on
  a wedge of base-changed vectors.**
* `exteriorPower.piScalarRight_one_tmul_single`: the base change of a standard basis vector of
  `Rⁱ` is the standard basis vector of `Sⁱ`.
* `exteriorPower.homFreeBaseChangeEquiv_apply_ιMulti_single`: **the identification evaluated on a
  wedge of standard basis vectors.**

## Implementation notes

**Each of the three factors is inverted, and each inversion is `LinearEquiv.symm_apply_eq` applied
to the factor's own forward formula.** `exteriorPower.homFreeBaseChangeEquiv` postcomposes with two
`LinearEquiv.arrowCongr`s whose first arguments therefore appear inverted, so what is needed is the
value of `(exteriorPowerCongr n e).symm` and of `(exteriorPowerBaseChange R S M n).symm` on a
wedge. Neither needs a `symm` lemma of its own: `LinearEquiv.symm_apply_eq` turns each into the
forward statement, which is `Stacks.exteriorPowerCongr_ιMulti` and
`ExteriorAlgebra.exteriorPowerBaseChange_tmul_ιMulti` respectively. The same remark disposes of the
inverse of `Algebra.TensorProduct.piScalarRight`, whose forward value on a tensor is
`Algebra.TensorProduct.piScalarRight_tmul`.

**The third factor needs no inversion.** `LinearMap.liftBaseChangeEquiv` appears first in the
composite, so it is applied forward, and `LinearMap.liftBaseChange_one_tmul` is exactly its value
on `1 ⊗ₜ y`.

## References

* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
-/

@[expose] public noncomputable section

open scoped ExteriorAlgebra
open TensorProduct

namespace exteriorPower

variable (R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
  (ι : Type*) [Fintype ι] [DecidableEq ι] (n : ℕ)

/-- **The base-change identification evaluated on a wedge of base-changed vectors.** The functional
that `homFreeBaseChangeEquiv` attaches to an `R`-linear map `Ψ` takes the wedge of the images of
`v₁, …, vₙ` under the base change `Rⁱ ⟶ Sⁱ` to the value of `Ψ` on the wedge of the `vⱼ`
themselves. -/
theorem homFreeBaseChangeEquiv_apply_ιMulti_baseChange
    (Ψ : (⋀[R]^n (ι → R)) →ₗ[R] S) (v : Fin n → (ι → R)) :
    homFreeBaseChangeEquiv R S ι n Ψ
        (exteriorPower.ιMulti S n fun k =>
          Algebra.TensorProduct.piScalarRight R S S ι ((1 : S) ⊗ₜ[R] v k)) =
      Ψ (exteriorPower.ιMulti R n v) := by
  have hcongr : (_root_.exteriorPowerCongr n
        (Algebra.TensorProduct.piScalarRight R S S ι).toLinearEquiv).symm
      (exteriorPower.ιMulti S n fun k =>
        Algebra.TensorProduct.piScalarRight R S S ι ((1 : S) ⊗ₜ[R] v k)) =
      exteriorPower.ιMulti S n fun k => (1 : S) ⊗ₜ[R] v k := by
    rw [LinearEquiv.symm_apply_eq, Stacks.exteriorPowerCongr_ιMulti]
    rfl
  have hbc : (ExteriorAlgebra.exteriorPowerBaseChange R S (ι → R) n).symm
        (exteriorPower.ιMulti S n fun k => (1 : S) ⊗ₜ[R] v k) =
      (1 : S) ⊗ₜ[R] exteriorPower.ιMulti R n v := by
    rw [LinearEquiv.symm_apply_eq,
      ExteriorAlgebra.exteriorPowerBaseChange_tmul_ιMulti, one_smul]
  rw [homFreeBaseChangeEquiv]
  simp only [LinearEquiv.trans_apply, LinearEquiv.arrowCongr_apply, LinearEquiv.refl_apply]
  rw [hcongr, hbc]
  exact LinearMap.liftBaseChange_one_tmul (A := S) Ψ (exteriorPower.ιMulti R n v)

/-- **The base change of a standard basis vector of `Rⁱ` is the standard basis vector of `Sⁱ`.** -/
theorem piScalarRight_one_tmul_single (j : ι) :
    Algebra.TensorProduct.piScalarRight R S S ι ((1 : S) ⊗ₜ[R] Pi.single j (1 : R)) =
      Pi.single j (1 : S) := by
  rw [Algebra.TensorProduct.piScalarRight_tmul]
  funext i
  by_cases h : j = i <;> simp [h]

/-- **The base-change identification evaluated on a wedge of standard basis vectors.** This is the
form in which a computation performed over `R` — a determinant of coordinates, say — is read as a
functional over `S`. -/
theorem homFreeBaseChangeEquiv_apply_ιMulti_single
    (Ψ : (⋀[R]^n (ι → R)) →ₗ[R] S) (v : Fin n → ι) :
    homFreeBaseChangeEquiv R S ι n Ψ
        (exteriorPower.ιMulti S n fun k => Pi.single (v k) (1 : S)) =
      Ψ (exteriorPower.ιMulti R n fun k => Pi.single (v k) (1 : R)) := by
  refine Eq.trans (congrArg (homFreeBaseChangeEquiv R S ι n Ψ) ?_)
    (homFreeBaseChangeEquiv_apply_ιMulti_baseChange R S ι n Ψ
      (fun k => Pi.single (v k) (1 : R)))
  exact congrArg (exteriorPower.ιMulti S n)
    (funext fun k => (piScalarRight_one_tmul_single R S ι (v k)).symm)

end exteriorPower

end
