module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.PolynomialMonomialDifferential
public import StacksFrontier.LinearAlgebra.ExteriorPower.BasisConstr
public import StacksFrontier.LinearAlgebra.ExteriorPower.KoszulCoefficients

/-!
# The relative sector map of the divided power Poincaré lemma

Let `A` be a ring, let `(B, I, δ)` be a divided power ring which is an `A`-algebra, let `W`
index a family of divided power variables and let `P = B⟨x_w : w ∈ W⟩` carry the divided power
ideal `IP + P₊` of [Stacks, Tag 07H6].  This module builds the **sector map** of the proof of
[Stacks, Tag 07LC] with the divided power ideal `I` of the base left arbitrary.

The forms of `P` are spanned by the elements

`x^{[L]} · ψ(ω) ∧ d x_{w₁} ∧ ⋯ ∧ d x_{w_j}`,

where `L : W →₀ ℕ` is an exponent vector, `ω ∈ Ωⁱ_{B/A,δ}` is a form of the base and `ψ` is the
comparison of forms along the coefficient inclusion `B → P`.  Grouping them by the **total
multi-index** `K = L + 1_{\{w₁, …, w_j\}}`, which the divided power de Rham differential
preserves, splits `Ω^*_{P/A,δ'}` into sectors indexed by `K`.  The `K`-sector is

`⨁_{i + j = n} ⋀ʲ_B (supp K →₀ B) ⊗_B Ωⁱ_{B/A,δ}`,

the total complex of the bicomplex `Kos(supp K) ⊗_B Ω^*_{B/A,δ}`, and this module constructs
the map from it into the forms of `P` and computes the de Rham differential on it.

## Why this is not the absolute argument with `B` in place of `A`

With `I = ⊥` the module `Ω¹_{B/A,δ}` vanishes in the relevant range and the sector is a bare
Koszul complex over the coefficients; that is the case
`StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerPoincare` proves, and the whole of its
sector argument rests on the freeness of `Ωⁿ_{P/A,δ'}` over `P` on the `n`-element subsets of
`W`.  For a nontrivial `I` that freeness is false: only the direct sum decomposition
`Crystalline.DividedPowerPolynomial.dividedPowerPolynomialFormsEquiv` survives, the coefficient
factor `Ωⁱ_{B/A,δ}` is an arbitrary `B`-module, and the sector becomes the total complex of a
bicomplex rather than a Koszul complex.  Correspondingly the differential acquires a second
term, and the Koszul direction acquires the sign `(-1)^i`.

## Main definitions

* `Crystalline.DividedPowerPolynomial.coefficientFormsMap` — the comparison `ψ` of forms along
  the coefficient inclusion `B → P`, as a `B`-linear map.
* `Crystalline.DividedPowerPolynomial.variableDifferential` — the one-form `d x_w` of `P`.
* `Crystalline.DividedPowerPolynomial.sectorGenerator` — the element
  `x^{[L]} · ψ(ω) ∧ d x_{v₁} ∧ ⋯ ∧ d x_{v_j}` of `Ω^{i+j}_{P/A,δ'}`.
* `Crystalline.DividedPowerPolynomial.sectorModule` — the bidegree-`(i, j)` piece
  `⋀ʲ_B (supp K →₀ B) ⊗_B Ωⁱ_{B/A,δ}` of the `K`-sector.
* `Crystalline.DividedPowerPolynomial.relativeSectorMap` — **the sector map.**
* `Crystalline.DividedPowerPolynomial.relativeSectorCoefficientDifferential` — the horizontal
  differential of the sector, `1 ⊗ d_B`.
* `Crystalline.DividedPowerPolynomial.sectorVector` — the Koszul vector `∑_{w ∈ supp K} e_w`.

## Main results

* `Crystalline.DividedPowerPolynomial.sectorGenerator_dividedPowerDeRham` — **the bigraded
  Leibniz computation**

  `d (x^{[L]} · ψ(ω) ∧ dx_v) = x^{[L]} · ψ(dω) ∧ dx_v
      + (-1)^i ∑_{w ∈ supp L} x^{[L - e_w]} · ψ(ω) ∧ dx_w ∧ dx_v.`

* `Crystalline.DividedPowerPolynomial.relativeSectorMap_dividedPowerDeRham` — **the de Rham
  differential on the `K`-sector** is the total differential of the bicomplex: the horizontal
  differential `1 ⊗ d_B` plus `(-1)^i` times wedging by the Koszul vector.

## References

* [Stacks Project, Lemma 60.19.1, Tag 07LC](https://stacks.math.columbia.edu/tag/07LC)
* [Stacks Project, Lemma 60.19.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
* [Stacks Project, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
-/

@[expose] public noncomputable section

open DividedPowers
open scoped TensorProduct

universe uA uB uW

namespace Crystalline

/-! ### Two facts about the divided power de Rham differential -/

section Generic

variable {A : Type uA} {B : Type*} [CommRing A] [CommRing B] [Algebra A B] {J : Ideal B}
  (hJ : DividedPowers J)

/-- **A wedge of differentials is closed.**  `d (d b₁ ∧ ⋯ ∧ d b_j) = 0`.

This is `Crystalline.dividedPowerDeRham_generator` with the leading coefficient taken to be
`1`: the generator rule then produces a wedge whose first slot is `d 1 = 0`. -/
theorem dividedPowerDeRham_ιMulti_dividedPowerDifferential (j : ℕ) (b : Fin j → B) :
    dividedPowerDeRham hJ j
        (exteriorPower.ιMulti B j fun k ↦ dividedPowerDifferential (A := A) hJ (b k)) = 0 := by
  have hgen := dividedPowerDeRham_generator (A := A) hJ j (Fin.cons (1 : B) b)
  rw [Fin.cons_zero, one_smul] at hgen
  refine Eq.trans (Eq.trans (congrArg (dividedPowerDeRham hJ j)
    ((exteriorPower.ιMulti B j).congr_arg (funext fun k ↦ ?_))) hgen) ?_
  · rw [Fin.cons_succ]
  · refine (exteriorPower.ιMulti B (j + 1)).map_coord_zero (i := 0) ?_
    rw [Fin.cons_zero, dividedPowerDifferential_one]

/-- **The divided power de Rham differential as an `A`-linear map.**
`Crystalline.dividedPowerDeRham` is a bare function, and `Crystalline.dividedPowerDeRhamHom`
bundles it only additively; the `A`-linearity is recorded in the complex, on the
`RestrictScalars` synonyms.  This pays that crossing once. -/
def dividedPowerDeRhamLinearMap (i : ℕ) :
    dividedPowerDifferentialForms (A := A) hJ i →ₗ[A]
      dividedPowerDifferentialForms (A := A) hJ (i + 1) :=
  (dividedPowerDeRhamComplex (A := A) hJ).differential i

/-- The map `Crystalline.dividedPowerDeRhamLinearMap` sends a form `ω` to its divided power de
Rham differential. -/
@[simp] theorem dividedPowerDeRhamLinearMap_apply (i : ℕ)
    (omega : dividedPowerDifferentialForms (A := A) hJ i) :
    dividedPowerDeRhamLinearMap hJ i omega = dividedPowerDeRham hJ i omega :=
  rfl

/-- **Moving a one-form past a form of degree `i` across a bigraded wedge.**  Left exterior
multiplication by a one-form `x` on `ω ∧ η` is `(-1)^i` times `ω ∧ (x ∧ η)`, where `i` is the
degree of `ω`.

This is graded commutativity, `exteriorPower.mul_comm_of_mem`, in the only shape the de Rham
computation needs: `Crystalline.dividedPowerDeRham_smul` produces its correction term as a
`Crystalline.leftWedge`, and the bigraded Leibniz rule
`Crystalline.dividedPowerDeRham_wedgeMul` consumes it as an `exteriorPower.wedgeMul`. -/
theorem leftWedge_wedgeMul {Omega : Type*} [AddCommGroup Omega] [Module B Omega] (i j : ℕ)
    (x : Omega) (omega : ⋀[B]^i Omega) (eta : ⋀[B]^j Omega) :
    leftWedge (i + j) x (exteriorPower.wedgeMul i j omega eta) =
      (-1 : B) ^ i • exteriorPower.degCongr (Nat.add_succ i j)
        (exteriorPower.wedgeMul i (j + 1) omega (leftWedge j x eta)) := by
  refine Subtype.ext ?_
  rw [leftWedge_coe, exteriorPower.wedgeMul_apply_coe, exteriorPower.coe_neg_one_pow_smul,
    exteriorPower.coe_degCongr, exteriorPower.wedgeMul_apply_coe, leftWedge_coe, ← mul_assoc,
    ← mul_assoc, exteriorPower.mul_comm_of_mem (p := 1) (q := i)
      (exteriorPower.ι_mem_degreeOne x) omega.2, Nat.one_mul]
  simp only [mul_assoc]

/-- A wedge of the images `f (v k)` of a tuple `v` with a repeated entry vanishes. -/
private theorem ιMulti_comp_eq_zero_of_not_injective {R M ι : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (j : ℕ) (f : ι → M) (v : Fin j → ι) (hv : ¬ Function.Injective v) :
    exteriorPower.ιMulti R j (fun k ↦ f (v k)) = 0 :=
  AlternatingMap.map_eq_zero_of_not_injective _ _ fun h ↦ hv fun _ _ hab ↦ h (congrArg f hab)

end Generic

namespace DividedPowerPolynomial

/-! ### The coefficient inclusion and the variable differentials -/

section Relative

variable (A : Type uA) [CommRing A] (B : DividedPowerRing.{uB}) [Algebra A B] (W : Type uW)

/-- The forms of the divided power polynomial algebra `P = B⟨x_w : w ∈ W⟩`. -/
abbrev dividedPowerPolynomialForms (n : ℕ) : Type (max uB uW) :=
  dividedPowerDifferentialForms (A := A) (setIndexedDividedPowerPolynomialDividedPowers B W) n

/-- The coefficient inclusion `B → P`, as a morphism of `A`-algebras. -/
abbrev coefficientAlgHom : (B : Type uB) →ₐ[A] setIndexedDividedPowerPolynomialAlgebra B W :=
  IsScalarTower.toAlgHom A (B : Type uB) (setIndexedDividedPowerPolynomialAlgebra B W)

/-- The coefficient inclusion is a morphism of divided power rings, by [Stacks, Tag 07H6]. -/
theorem coefficientAlgHom_isDPMorphism :
    DividedPowers.IsDPMorphism B.dividedPowers
      (setIndexedDividedPowerPolynomialDividedPowers B W)
      (coefficientAlgHom A B W).toRingHom :=
  setIndexedDividedPowerPolynomialCoefficient_isDPMorphism B W

/-- **The comparison `ψ` of forms along the coefficient inclusion `B → P`**, as a `B`-linear
map `Ωⁱ_{B/A,δ} → Ωⁱ_{P/A,δ'}`.

`Crystalline.mapDifferentialFormsOfDPMorphism` is semilinear along `algebraMap B P`, which is
the same thing read through the `B`-module structure of the target; the crossing is paid here,
once, rather than in every proof that uses it. -/
def coefficientFormsMap (i : ℕ) :
    dividedPowerDifferentialForms (A := A) B.dividedPowers i →ₗ[(B : Type uB)]
      dividedPowerPolynomialForms A B W i where
  toFun := mapDifferentialFormsOfDPMorphism (A := A) (J := B.ideal) (delta := B.dividedPowers)
    (setIndexedDividedPowerPolynomialDividedPowers B W) (coefficientAlgHom A B W)
    (coefficientAlgHom_isDPMorphism A B W) i
  map_add' := map_add _
  map_smul' b omega := by
    refine Eq.trans (map_smulₛₗ (mapDifferentialFormsOfDPMorphism (A := A) (J := B.ideal)
      (delta := B.dividedPowers) (setIndexedDividedPowerPolynomialDividedPowers B W)
      (coefficientAlgHom A B W) (coefficientAlgHom_isDPMorphism A B W) i) b omega) ?_
    exact algebraMap_smul (setIndexedDividedPowerPolynomialAlgebra B W) b _

/-- The comparison of forms, unfolded to `Crystalline.mapDifferentialFormsOfDPMorphism`. -/
theorem coefficientFormsMap_apply (i : ℕ)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) :
    coefficientFormsMap A B W i omega =
      mapDifferentialFormsOfDPMorphism (A := A) (J := B.ideal) (delta := B.dividedPowers)
        (setIndexedDividedPowerPolynomialDividedPowers B W) (coefficientAlgHom A B W)
        (coefficientAlgHom_isDPMorphism A B W) i omega :=
  rfl

/-- **The comparison of forms is a map of de Rham complexes**: `ψ (d ω) = d (ψ ω)`. -/
theorem coefficientFormsMap_dividedPowerDeRham (i : ℕ)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) :
    coefficientFormsMap A B W (i + 1) (dividedPowerDeRham B.dividedPowers i omega) =
      dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) i
        (coefficientFormsMap A B W i omega) :=
  mapDifferentialFormsOfDPMorphism_deRham (A := A) (hJ := B.dividedPowers) _ _
    (coefficientAlgHom_isDPMorphism A B W) i omega

/-- The comparison of forms respects the bigraded wedge product. -/
theorem coefficientFormsMap_wedgeMul (i j : ℕ)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i)
    (eta : dividedPowerDifferentialForms (A := A) B.dividedPowers j) :
    coefficientFormsMap A B W (i + j) (exteriorPower.wedgeMul i j omega eta) =
      exteriorPower.wedgeMul i j (coefficientFormsMap A B W i omega)
        (coefficientFormsMap A B W j eta) :=
  mapDifferentialFormsOfDPMorphism_wedgeMul (A := A) (hJ := B.dividedPowers) _ _
    (coefficientAlgHom_isDPMorphism A B W) i j omega eta

/-- **The one-form `d x_w` of `P`.**  The variable `x_w` lies in the divided power ideal
`IP + P₊` of `P` whatever the ideal `I` of the base is, so this is defined for an arbitrary
divided power base. -/
def variableDifferential (w : W) :
    dividedPowerDifferentials (A := A) (setIndexedDividedPowerPolynomialDividedPowers B W) :=
  dividedPowerDifferential (A := A) (setIndexedDividedPowerPolynomialDividedPowers B W)
    (dividedPowerPolynomialVariable (B : Type uB) w)

/-- **The wedge `d x_{v 0} ∧ ⋯ ∧ d x_{v (j-1)}` of `j` variable differentials.** -/
def variableWedge (j : ℕ) (v : Fin j → W) : dividedPowerPolynomialForms A B W j :=
  exteriorPower.ιMulti (setIndexedDividedPowerPolynomialAlgebra B W) j fun k ↦
    variableDifferential A B W (v k)

/-- A wedge of variable differentials is closed. -/
theorem dividedPowerDeRham_variableWedge (j : ℕ) (v : Fin j → W) :
    dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) j
      (variableWedge A B W j v) = 0 :=
  dividedPowerDeRham_ιMulti_dividedPowerDifferential (A := A)
    (setIndexedDividedPowerPolynomialDividedPowers B W) j fun k ↦
      dividedPowerPolynomialVariable (B : Type uB) (v k)

/-- Wedging one more variable differential on the left of a wedge of variable differentials. -/
theorem leftWedge_variableWedge (j : ℕ) (w : W) (v : Fin j → W) :
    leftWedge j (variableDifferential A B W w) (variableWedge A B W j v) =
      variableWedge A B W (j + 1) (Fin.cons w v) := by
  refine Eq.trans (leftWedge_ιMulti j _ _) ?_
  refine (exteriorPower.ιMulti (setIndexedDividedPowerPolynomialAlgebra B W)
    (j + 1)).congr_arg (funext fun k ↦ ?_)
  induction k using Fin.cases with
  | zero => rfl
  | succ m => rfl

/-! ### The sector generator and the bigraded Leibniz computation -/

/-- **The sector generator** `x^{[L]} · ψ(ω) ∧ d x_{v 0} ∧ ⋯ ∧ d x_{v (j-1)}` of
`Ω^{i+j}_{P/A,δ'}`, for an exponent vector `L`, a form `ω` of degree `i` on the base and a
tuple `v` of `j` variables.

Its **total multi-index** is `L + 1_{\{v 0, …, v (j-1)\}}`, and the computation below says that
the divided power de Rham differential preserves it. -/
def sectorGenerator (L : W →₀ ℕ) (i : ℕ)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) (j : ℕ) (v : Fin j → W) :
    dividedPowerPolynomialForms A B W (i + j) :=
  dividedPowerPolynomialMonomial (B : Type uB) L •
    exteriorPower.wedgeMul i j (coefficientFormsMap A B W i omega) (variableWedge A B W j v)

set_option synthInstance.maxHeartbeats 100000 in
-- instance search for the module structures on tensor products and exterior powers over the
-- divided power polynomial algebra is slow
/-- **The de Rham differential of a coefficient form wedged with variable differentials.**
The correction term of the bigraded Leibniz rule drops out, because a wedge of variable
differentials is closed, and what is left is the differential of the coefficient. -/
theorem dividedPowerDeRham_wedgeMul_variableWedge (i : ℕ)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) (j : ℕ)
    (v : Fin j → W) :
    dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) (i + j)
        (exteriorPower.wedgeMul i j (coefficientFormsMap A B W i omega)
          (variableWedge A B W j v)) =
      exteriorPower.degCongr (Nat.succ_add i j)
        (exteriorPower.wedgeMul (i + 1) j
          (coefficientFormsMap A B W (i + 1) (dividedPowerDeRham B.dividedPowers i omega))
          (variableWedge A B W j v)) := by
  refine Eq.trans (dividedPowerDeRham_wedgeMul_degCongr
    (setIndexedDividedPowerPolynomialDividedPowers B W) i j _ _) ?_
  have hfirst : exteriorPower.degCongr (Nat.succ_add i j)
        (exteriorPower.wedgeMul (i + 1) j
          (dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) i
            (coefficientFormsMap A B W i omega)) (variableWedge A B W j v)) =
      exteriorPower.degCongr (Nat.succ_add i j)
        (exteriorPower.wedgeMul (i + 1) j
          (coefficientFormsMap A B W (i + 1) (dividedPowerDeRham B.dividedPowers i omega))
          (variableWedge A B W j v)) :=
    congrArg (fun z : dividedPowerPolynomialForms A B W (i + 1) ↦
        exteriorPower.degCongr (Nat.succ_add i j)
          (exteriorPower.wedgeMul (i + 1) j z (variableWedge A B W j v)))
      (coefficientFormsMap_dividedPowerDeRham A B W i omega).symm
  have hsecond : (-1 : setIndexedDividedPowerPolynomialAlgebra B W) ^ i •
        exteriorPower.degCongr (Nat.add_succ i j)
          (exteriorPower.wedgeMul i (j + 1) (coefficientFormsMap A B W i omega)
            (dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) j
              (variableWedge A B W j v))) = 0 := by
    refine Eq.trans (congrArg (fun z : dividedPowerPolynomialForms A B W (j + 1) ↦
        (-1 : setIndexedDividedPowerPolynomialAlgebra B W) ^ i •
          exteriorPower.degCongr (Nat.add_succ i j)
            (exteriorPower.wedgeMul i (j + 1) (coefficientFormsMap A B W i omega) z))
      (dividedPowerDeRham_variableWedge A B W j v)) ?_
    rw [LinearMap.map_zero, LinearEquiv.map_zero, smul_zero]
  exact Eq.trans (congrArg₂ (· + ·) hfirst hsecond) (add_zero _)

/-- **Wedging one variable differential onto a sector generator.**  Moving `d x_w` past the
coefficient form `ψ(ω)` of degree `i` costs the sign `(-1)^i` and produces the sector generator
of bidegree `(i, j + 1)` on the tuple `w, v`. -/
theorem leftWedge_variableDifferential_wedgeMul (i : ℕ)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) (j : ℕ)
    (v : Fin j → W) (w : W) :
    leftWedge (i + j) (variableDifferential A B W w)
        (exteriorPower.wedgeMul i j (coefficientFormsMap A B W i omega)
          (variableWedge A B W j v)) =
      (-1 : setIndexedDividedPowerPolynomialAlgebra B W) ^ i •
        exteriorPower.degCongr (Nat.add_succ i j)
          (exteriorPower.wedgeMul i (j + 1) (coefficientFormsMap A B W i omega)
            (variableWedge A B W (j + 1) (Fin.cons w v))) :=
  Eq.trans (leftWedge_wedgeMul i j _ _ _)
    (congrArg (fun z : dividedPowerPolynomialForms A B W (j + 1) ↦
        (-1 : setIndexedDividedPowerPolynomialAlgebra B W) ^ i •
          exteriorPower.degCongr (Nat.add_succ i j)
            (exteriorPower.wedgeMul i (j + 1) (coefficientFormsMap A B W i omega) z))
      (leftWedge_variableWedge A B W j w v))

/-- **The bigraded Leibniz computation.**  The divided power de Rham differential of a sector
generator is

`d (x^{[L]} · ψ(ω) ∧ dx_v)
    = x^{[L]} · ψ(dω) ∧ dx_v + (-1)^i ∑_{w ∈ supp L} x^{[L - e_w]} · ψ(ω) ∧ dx_w ∧ dx_v`,

both terms again sector generators with the same total multi-index.  The first lives in
bidegree `(i + 1, j)` and the second in bidegree `(i, j + 1)`, so this exhibits `d` as the
total differential of the bicomplex `Kos(supp K) ⊗_B Ω^*_{B/A,δ}`.

The three inputs are: the Leibniz rule `Crystalline.dividedPowerDeRham_smul` for the monomial
coefficient; the shift rule
`Crystalline.DividedPowerPolynomial.dividedPowerDifferential_monomial_shift`, which is what
turns `d (x^{[L]})` into a sum of sector generators of the next bidegree; and the bigraded
Leibniz rule `Crystalline.dividedPowerDeRham_wedgeMul_degCongr`, whose correction term vanishes
because a wedge of variable differentials is closed.  The sign `(-1)^i` is the cost of moving
`d x_w` past `ψ(ω)`. -/
theorem sectorGenerator_dividedPowerDeRham (L : W →₀ ℕ) (i : ℕ)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) (j : ℕ)
    (v : Fin j → W) :
    dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) (i + j)
        (sectorGenerator A B W L i omega j v) =
      exteriorPower.degCongr (Nat.succ_add i j)
          (sectorGenerator A B W L (i + 1)
            (dividedPowerDeRham B.dividedPowers i omega) j v) +
        (-1 : setIndexedDividedPowerPolynomialAlgebra B W) ^ i •
          ∑ w ∈ L.support, exteriorPower.degCongr (Nat.add_succ i j)
            (sectorGenerator A B W (L.erase w + Finsupp.single w (L w - 1)) i omega (j + 1)
              (Fin.cons w v)) := by
  classical
  refine Eq.trans (dividedPowerDeRham_smul
    (setIndexedDividedPowerPolynomialDividedPowers B W) (i + j)
    (dividedPowerPolynomialMonomial (B : Type uB) L) _) ?_
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Eq.trans (congrArg (fun z : dividedPowerPolynomialForms A B W (i + j + 1) ↦
        dividedPowerPolynomialMonomial (B : Type uB) L • z)
      (dividedPowerDeRham_wedgeMul_variableWedge A B W i omega j v)) ?_
    exact (map_smul (exteriorPower.degCongr (Nat.succ_add i j)) _ _).symm
  · refine Eq.trans (congrArg (fun y : dividedPowerDifferentials (A := A)
          (setIndexedDividedPowerPolynomialDividedPowers B W) ↦
        leftWedge (i + j) y (exteriorPower.wedgeMul i j (coefficientFormsMap A B W i omega)
          (variableWedge A B W j v)))
      (dividedPowerDifferential_monomial_shift A B W L)) ?_
    refine Eq.trans (DFunLike.congr_fun (map_sum (leftWedge (i + j)) _ L.support) _) ?_
    refine Eq.trans (LinearMap.sum_apply L.support _ _) ?_
    refine Eq.trans (Finset.sum_congr rfl fun w _ ↦ ?_) Finset.smul_sum.symm
    refine Eq.trans (congrArg (fun g : dividedPowerPolynomialForms A B W (i + j) →ₗ[
          setIndexedDividedPowerPolynomialAlgebra B W]
          dividedPowerPolynomialForms A B W (i + j + 1) ↦
        g (exteriorPower.wedgeMul i j (coefficientFormsMap A B W i omega)
          (variableWedge A B W j v)))
      (map_smul (leftWedge (i + j)) (dividedPowerPolynomialMonomial (B : Type uB)
        (L.erase w + Finsupp.single w (L w - 1))) (variableDifferential A B W w))) ?_
    refine Eq.trans (LinearMap.smul_apply _ _ _) ?_
    refine Eq.trans (congrArg (fun z : dividedPowerPolynomialForms A B W (i + j + 1) ↦
        dividedPowerPolynomialMonomial (B : Type uB)
          (L.erase w + Finsupp.single w (L w - 1)) • z)
      (leftWedge_variableDifferential_wedgeMul A B W i omega j v w)) ?_
    refine Eq.trans (smul_comm _ _ _) ?_
    exact congrArg
      (fun z : dividedPowerPolynomialForms A B W (i + j + 1) ↦
        (-1 : setIndexedDividedPowerPolynomialAlgebra B W) ^ i • z)
      (map_smul (exteriorPower.degCongr (Nat.add_succ i j)) _ _).symm

/-! ### The sector map -/

/-- The sector generator as a `B`-linear map in its coefficient form. -/
def sectorGeneratorMap (L : W →₀ ℕ) (i j : ℕ) (v : Fin j → W) :
    dividedPowerDifferentialForms (A := A) B.dividedPowers i →ₗ[(B : Type uB)]
      dividedPowerPolynomialForms A B W (i + j) :=
  ((LinearMap.lsmul (setIndexedDividedPowerPolynomialAlgebra B W)
          (dividedPowerPolynomialForms A B W (i + j))
          (dividedPowerPolynomialMonomial (B : Type uB) L)).restrictScalars
        (B : Type uB)).comp
    ((((exteriorPower.wedgeMul i j).flip (variableWedge A B W j v)).restrictScalars
        (B : Type uB)).comp (coefficientFormsMap A B W i))

/-- The linear map `sectorGeneratorMap` sends a form `ω` to the sector generator of `ω`. -/
@[simp] theorem sectorGeneratorMap_apply (L : W →₀ ℕ) (i j : ℕ) (v : Fin j → W)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) :
    sectorGeneratorMap A B W L i j v omega = sectorGenerator A B W L i omega j v :=
  rfl

end Relative

/-- The multi-index `1_s = ∑_{w ∈ s} e_w` of a finite set of variables. -/
def finsetMultiIndex {iota : Type*} (s : Finset iota) : iota →₀ ℕ :=
  ∑ w ∈ s, Finsupp.single w 1

/-- The multi-index `1_s` takes the value `1` on `s` and `0` off `s`. -/
theorem finsetMultiIndex_apply {iota : Type*} [DecidableEq iota] (s : Finset iota) (w : iota) :
    finsetMultiIndex s w = if w ∈ s then 1 else 0 := by
  simp [finsetMultiIndex, Finset.sum_apply, Finsupp.single_apply]

/-- `1_s ≤ K` if and only if `s` is contained in the support of `K`. -/
theorem finsetMultiIndex_le_iff {iota : Type*} (s : Finset iota) (K : iota →₀ ℕ) :
    finsetMultiIndex s ≤ K ↔ s ⊆ K.support := by
  classical
  constructor
  · intro h w hw
    have hww := h w
    rw [finsetMultiIndex_apply, ite_eq_left hw] at hww
    exact Finsupp.mem_support_iff.mpr (by omega)
  · intro h w
    rw [finsetMultiIndex_apply]
    split_ifs with hw
    · exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (h hw))
    · exact Nat.zero_le _

/-- If `s` is contained in the support of `K`, then `(K - 1_s) + 1_s = K`. -/
theorem finsetMultiIndex_sub_add {iota : Type*} (s : Finset iota) (K : iota →₀ ℕ)
    (h : s ⊆ K.support) : K - finsetMultiIndex s + finsetMultiIndex s = K :=
  tsub_add_cancel_of_le ((finsetMultiIndex_le_iff s K).mpr h)

/-- The set `s` is contained in the support of `K + 1_s`. -/
theorem subset_support_add_finsetMultiIndex {iota : Type*} (s : Finset iota)
    (K : iota →₀ ℕ) : s ⊆ (K + finsetMultiIndex s).support := by
  rw [← finsetMultiIndex_le_iff]
  exact le_add_self

/-- Lowering the exponent vector `K - 1_s` by one more at a variable `w ∉ s` is lowering `K`
by one at each variable of `insert w s`.  The left hand side is the spelling in which the
shift rule `Crystalline.DividedPowerPolynomial.dividedPowerDifferential_monomial_shift`
produces it. -/
theorem lower_multiIndex_insert {iota : Type*} [DecidableEq iota] (K : iota →₀ ℕ)
    (s : Finset iota) (w : iota) (hw : w ∉ s) :
    (K - finsetMultiIndex s).erase w +
        Finsupp.single w ((K - finsetMultiIndex s) w - 1) =
      K - finsetMultiIndex (insert w s) := by
  ext u
  by_cases huw : u = w
  · subst u
    simp [finsetMultiIndex_apply, Finsupp.erase_same, hw]
  · simp [Finsupp.erase_ne huw, Finsupp.single_eq_of_ne huw, finsetMultiIndex_apply, huw]

/-- The support of `K - 1_s` is contained in the support of `K`. -/
theorem support_sub_finsetMultiIndex_subset {iota : Type*} (K : iota →₀ ℕ) (s : Finset iota) :
    (K - finsetMultiIndex s).support ⊆ K.support := by
  intro u hu
  simp only [Finsupp.mem_support_iff, Finsupp.coe_tsub, Pi.sub_apply] at *
  omega

/-- A variable in the support of `K` but not in the support of `K - 1_s` lies in `s`. -/
theorem mem_finset_of_notMem_sub_support {iota : Type*} (K : iota →₀ ℕ) (s : Finset iota)
    (u : iota) (hu : u ∈ K.support) (hnu : u ∉ (K - finsetMultiIndex s).support) : u ∈ s := by
  classical
  simp only [Finsupp.mem_support_iff, Finsupp.coe_tsub, Pi.sub_apply, not_not,
    finsetMultiIndex_apply] at *
  split_ifs at hnu with hs
  · exact hs
  · omega

/-- The image of a tuple extended by one entry on the left. -/
theorem image_fin_cons {iota : Type*} [DecidableEq iota] {n : ℕ} (u : iota)
    (v : Fin n → iota) :
    Finset.univ.image (Fin.cons u v : Fin (n + 1) → iota) =
      insert u (Finset.univ.image v) := by
  ext a
  simp [Fin.exists_fin_succ, eq_comm]

section Sector

variable (A : Type uA) [CommRing A] (B : DividedPowerRing.{uB}) [Algebra A B] (W : Type uW)
  [LinearOrder W]

/-- **The `(i, j)`-piece of the `K`-sector**: `⋀ʲ_B (supp K →₀ B) ⊗_B Ωⁱ_{B/A,δ}`.

The Koszul factor is free over `B` on the `j`-element subsets of `supp K`, so this is a direct
sum of copies of `Ωⁱ_{B/A,δ}` — but it is written as a tensor product, because that is the
shape in which `exteriorPower.contraction` and `exteriorPower.wedgeLeft` act on it, through
`LinearMap.rTensor`. -/
abbrev sectorModule (K : W →₀ ℕ) (i j : ℕ) : Type (max uB uW) :=
  (⋀[(B : Type uB)]^j (K.support →₀ (B : Type uB))) ⊗[(B : Type uB)]
    dividedPowerDifferentialForms (A := A) B.dividedPowers i

/-- The basis of `⋀ʲ_B (supp K →₀ B)` indexed by the `j`-element subsets of `supp K`. -/
abbrev sectorExteriorBasis (K : W →₀ ℕ) (j : ℕ) :
    Module.Basis (Set.powersetCard (K.support : Type uW) j) (B : Type uB)
      (⋀[(B : Type uB)]^j (K.support →₀ (B : Type uB))) :=
  Module.Basis.exteriorPower j
    (Finsupp.basisSingleOne (R := (B : Type uB)) (ι := (K.support : Type uW)))

omit [LinearOrder W] in
/-- **Reordering the variables of a sector generator** changes it by the sign of the
permutation: the wedge of the variable differentials is alternating. -/
theorem sectorGenerator_comp_perm (L : W →₀ ℕ) (i : ℕ)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) (j : ℕ) (v : Fin j → W)
    (sigma : Equiv.Perm (Fin j)) :
    sectorGenerator A B W L i omega j (v ∘ sigma) =
      sigma.sign • sectorGenerator A B W L i omega j v := by
  have hperm : variableWedge A B W j (v ∘ sigma) =
      sigma.sign • variableWedge A B W j v :=
    (exteriorPower.ιMulti (setIndexedDividedPowerPolynomialAlgebra B W) j).map_perm
      (fun k ↦ variableDifferential A B W (v k)) sigma
  refine Eq.trans (congrArg (fun z : dividedPowerPolynomialForms A B W j ↦
      dividedPowerPolynomialMonomial (B : Type uB) L •
        exteriorPower.wedgeMul i j (coefficientFormsMap A B W i omega) z) hperm) ?_
  simp only [Units.smul_def, map_zsmul]
  exact smul_comm _ _ _

/-- **The value of the sector map on the wedge of the variables `v`**: the sector generator
whose exponent vector is `K` lowered by one at each variable occurring in `v`, so that the
total multi-index is `K`. -/
def sectorValue (K : W →₀ ℕ) (i j : ℕ) (v : Fin j → W) :
    dividedPowerDifferentialForms (A := A) B.dividedPowers i →ₗ[(B : Type uB)]
      dividedPowerPolynomialForms A B W (i + j) :=
  sectorGeneratorMap A B W (K - finsetMultiIndex (Finset.univ.image v)) i j v

/-- Reordering the tuple of variables changes the sector map's value by the sign of the
permutation: the exponent vector depends only on the set of variables. -/
theorem sectorValue_comp_perm (K : W →₀ ℕ) (i j : ℕ) (v : Fin j → W)
    (sigma : Equiv.Perm (Fin j)) :
    sectorValue A B W K i j (v ∘ sigma) = sigma.sign • sectorValue A B W K i j v := by
  classical
  have himage : Finset.univ.image (v ∘ sigma) = Finset.univ.image v := by
    ext w
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
    exact ⟨fun ⟨a, ha⟩ ↦ ⟨sigma a, ha⟩,
      fun ⟨a, ha⟩ ↦ ⟨sigma.symm a, by simpa only [sigma.apply_symm_apply] using ha⟩⟩
  refine LinearMap.ext fun omega ↦ ?_
  refine Eq.trans (congrArg (fun s : Finset W ↦
      sectorGenerator A B W (K - finsetMultiIndex s) i omega j (v ∘ sigma)) himage) ?_
  exact Eq.trans (sectorGenerator_comp_perm A B W _ i omega j v sigma)
    (LinearMap.smul_apply sigma.sign (sectorValue A B W K i j v) omega).symm

/-- **The sector map** `⋀ʲ_B (supp K →₀ B) ⊗_B Ωⁱ_{B/A,δ} → Ω^{i+j}_{P/A,δ'}`, carrying the
basis wedge of a `j`-element subset `I ⊆ supp K` tensored with `ω` to the sector generator
`x^{[K - 1_I]} · ψ(ω) ∧ dx_I`.

Every element in the image has total multi-index `K`, and the computation below shows that the
divided power de Rham differential preserves that, which is what makes this a map of
complexes. -/
def relativeSectorMap (K : W →₀ ℕ) (i j : ℕ) :
    sectorModule A B W K i j →ₗ[(B : Type uB)] dividedPowerPolynomialForms A B W (i + j) :=
  TensorProduct.lift ((sectorExteriorBasis B W K j).constr (B : Type uB) fun I ↦
    sectorValue A B W K i j (Subtype.val ∘ Set.powersetCard.ofFinEmbEquiv.symm I))

/-- **The sector map on an arbitrary wedge of standard generators.**  The tuple `v` need not be
increasing: this is where the sign rule of `sectorValue_comp_perm` is spent. -/
theorem relativeSectorMap_tmul_ιMulti (K : W →₀ ℕ) (i j : ℕ)
    (v : Fin j → (K.support : Type uW))
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) :
    relativeSectorMap A B W K i j
        (exteriorPower.ιMulti (B : Type uB) j
          (fun k ↦ Finsupp.single (v k) (1 : (B : Type uB))) ⊗ₜ[(B : Type uB)] omega) =
      sectorValue A B W K i j (Subtype.val ∘ v) omega := by
  classical
  refine Eq.trans (TensorProduct.lift.tmul _ _) ?_
  by_cases hv : Function.Injective v
  · have hfun : (fun k ↦ Finsupp.single (v k) (1 : (B : Type uB))) =
        ⇑(Finsupp.basisSingleOne (R := (B : Type uB)) (ι := (K.support : Type uW))) ∘ v := by
      funext k
      rw [Function.comp_apply, Finsupp.coe_basisSingleOne]
    refine Eq.trans (congrArg (fun u : Fin j → ((K.support : Type uW) →₀ (B : Type uB)) ↦
      (sectorExteriorBasis B W K j).constr (B : Type uB)
          (fun I ↦ sectorValue A B W K i j
            (Subtype.val ∘ Set.powersetCard.ofFinEmbEquiv.symm I))
          (exteriorPower.ιMulti (B : Type uB) j u) omega) hfun) ?_
    exact congrArg
      (fun g : dividedPowerDifferentialForms (A := A) B.dividedPowers i →ₗ[(B : Type uB)]
          dividedPowerPolynomialForms A B W (i + j) ↦ g omega)
      (Module.Basis.exteriorPower_constr_ιMulti
        (Finsupp.basisSingleOne (R := (B : Type uB)) (ι := (K.support : Type uW))) j
        (fun u : Fin j → (K.support : Type uW) ↦ sectorValue A B W K i j (Subtype.val ∘ u))
        (fun u sigma ↦ sectorValue_comp_perm A B W K i j (Subtype.val ∘ u) sigma) v hv)
  · have hzero : exteriorPower.ιMulti (B : Type uB) j
        (fun k ↦ Finsupp.single (v k) (1 : (B : Type uB))) = 0 :=
      ιMulti_comp_eq_zero_of_not_injective j (fun u ↦ Finsupp.single u (1 : (B : Type uB))) v hv
    have hwzero : variableWedge A B W j (Subtype.val ∘ v) = 0 :=
      ιMulti_comp_eq_zero_of_not_injective j
        (fun u : (K.support : Type uW) ↦ variableDifferential A B W u) v hv
    have hl : (sectorExteriorBasis B W K j).constr (B : Type uB)
          (fun I ↦ sectorValue A B W K i j (Subtype.val ∘ Set.powersetCard.ofFinEmbEquiv.symm I))
          (exteriorPower.ιMulti (B : Type uB) j
            fun k ↦ Finsupp.single (v k) (1 : (B : Type uB))) omega = 0 :=
      Eq.trans (congrArg (fun g : dividedPowerDifferentialForms (A := A) B.dividedPowers i →ₗ[
            (B : Type uB)] dividedPowerPolynomialForms A B W (i + j) ↦ g omega)
          (congrArg ((sectorExteriorBasis B W K j).constr (B : Type uB)
            fun I ↦ sectorValue A B W K i j
              (Subtype.val ∘ Set.powersetCard.ofFinEmbEquiv.symm I)) hzero))
        (by rw [map_zero, LinearMap.zero_apply])
    refine Eq.trans hl ?_
    refine Eq.symm (Eq.trans (sectorGeneratorMap_apply A B W
      (K - finsetMultiIndex (Finset.univ.image (Subtype.val ∘ v))) i j _ omega) ?_)
    refine Eq.trans (congrArg (fun z : dividedPowerPolynomialForms A B W j ↦
      dividedPowerPolynomialMonomial (B : Type uB)
          (K - finsetMultiIndex (Finset.univ.image (Subtype.val ∘ v))) •
        exteriorPower.wedgeMul i j (coefficientFormsMap A B W i omega) z) hwzero) ?_
    rw [map_zero, smul_zero]

/-! ### The de Rham differential on a sector -/

omit [LinearOrder W] in
/-- A sector generator on a tuple with a repeated variable vanishes. -/
theorem sectorGenerator_eq_zero_of_not_injective (L : W →₀ ℕ) (i : ℕ)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) (j : ℕ)
    (v : Fin j → W) (hv : ¬ Function.Injective v) :
    sectorGenerator A B W L i omega j v = 0 := by
  have hwzero : variableWedge A B W j v = 0 :=
    ιMulti_comp_eq_zero_of_not_injective j (variableDifferential A B W) v hv
  rw [sectorGenerator, hwzero, map_zero, smul_zero]

/-- A sector generator whose extra variable already occurs in the tuple vanishes. -/
theorem sectorGenerator_cons_eq_zero (L : W →₀ ℕ) (i : ℕ)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) (j : ℕ)
    (v : Fin j → W) (w : W) (hw : w ∈ Finset.univ.image v) :
    sectorGenerator A B W L i omega (j + 1) (Fin.cons w v) = 0 := by
  classical
  obtain ⟨m, -, hm⟩ := Finset.mem_image.mp hw
  refine sectorGenerator_eq_zero_of_not_injective A B W L i omega (j + 1) _ fun hinj ↦ ?_
  have h0 : (Fin.cons w v : Fin (j + 1) → W) 0 = (Fin.cons w v : Fin (j + 1) → W) m.succ := by
    rw [Fin.cons_zero, Fin.cons_succ, hm]
  exact (Fin.succ_ne_zero m) (hinj h0).symm

/-- **The Koszul vector of the `K`-sector**, `∑_{w ∈ supp K} e_w`.  Wedging by it is the Koszul
direction of the sector differential, and the functional dual to one of its entries contracts
it to `1`, which is what makes the Koszul complex of the sector contractible. -/
def sectorVector (K : W →₀ ℕ) : (K.support : Type uW) →₀ (B : Type uB) :=
  ∑ u : (K.support : Type uW), Finsupp.single u 1

omit [LinearOrder W] in
/-- Wedging the Koszul vector onto `e_v ⊗ ω` gives the sum over `u ∈ supp K` of the
generators `e_{u, v} ⊗ ω`. -/
private theorem rTensor_wedgeLeft_sectorVector_tmul_ιMulti (K : W →₀ ℕ) (i j : ℕ)
    (v : Fin j → (K.support : Type uW))
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) :
    LinearMap.rTensor (dividedPowerDifferentialForms (A := A) B.dividedPowers i)
        (exteriorPower.wedgeLeft (sectorVector B W K) j)
        (exteriorPower.ιMulti (B : Type uB) j
          (fun k ↦ Finsupp.single (v k) (1 : (B : Type uB))) ⊗ₜ[(B : Type uB)] omega) =
      ∑ u : (K.support : Type uW),
        exteriorPower.ιMulti (B : Type uB) (j + 1)
            (fun k ↦ Finsupp.single ((Fin.cons u v : Fin (j + 1) → (K.support : Type uW)) k)
              (1 : (B : Type uB))) ⊗ₜ[(B : Type uB)] omega := by
  classical
  have hfam : ∀ u : (K.support : Type uW),
      (Fin.cons (Finsupp.single u (1 : (B : Type uB)))
          (fun k ↦ Finsupp.single (v k) (1 : (B : Type uB))) :
            Fin (j + 1) → ((K.support : Type uW) →₀ (B : Type uB))) =
        fun k ↦ Finsupp.single ((Fin.cons u v : Fin (j + 1) → (K.support : Type uW)) k)
          (1 : (B : Type uB)) := by
    intro u
    funext k
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨m, rfl⟩
    · rw [Fin.cons_zero, Fin.cons_zero]
    · rw [Fin.cons_succ, Fin.cons_succ]
  refine Eq.trans (LinearMap.rTensor_tmul _ _ _ _) ?_
  refine Eq.trans (congrArg (fun y : ⋀[(B : Type uB)]^(j + 1)
      ((K.support : Type uW) →₀ (B : Type uB)) ↦ y ⊗ₜ[(B : Type uB)] omega)
    (Eq.trans (exteriorPower.wedgeLeft_sum_ιMulti (R := (B : Type uB)) j Finset.univ
        (fun u : (K.support : Type uW) ↦ Finsupp.single u (1 : (B : Type uB))) _)
      (Finset.sum_congr rfl fun u _ ↦ Eq.trans (exteriorPower.wedgeLeft_ιMulti _ j _)
        ((exteriorPower.ιMulti (B : Type uB) (j + 1)).congr_arg (hfam u))))) ?_
  exact TensorProduct.sum_tmul _ _ _

/-- The sector map's value on the tuple `u, v` is the sector generator on the variables
`insert u (image v)`. -/
private theorem sectorValue_cons (K : W →₀ ℕ) (i j : ℕ) (v : Fin j → (K.support : Type uW))
    (u : (K.support : Type uW))
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) :
    sectorValue A B W K i (j + 1) (Subtype.val ∘ Fin.cons u v) omega =
      sectorGenerator A B W
        (K - finsetMultiIndex (insert (u : W) (Finset.univ.image (Subtype.val ∘ v)))) i omega
        (j + 1) (Fin.cons (u : W) (Subtype.val ∘ v)) := by
  classical
  refine Eq.trans (congrArg (fun g : Fin (j + 1) → W ↦
    sectorGeneratorMap A B W (K - finsetMultiIndex (Finset.univ.image g)) i (j + 1) g omega)
    (Fin.comp_cons Subtype.val u v)) ?_
  exact congrArg (fun t : Finset W ↦
    sectorGenerator A B W (K - finsetMultiIndex t) i omega (j + 1)
      (Fin.cons (u : W) (Subtype.val ∘ v))) (image_fin_cons (u : W) (Subtype.val ∘ v))

set_option synthInstance.maxHeartbeats 100000 in
-- instance search for the module structures on tensor products and exterior powers over the
-- divided power polynomial algebra is slow
/-- **The de Rham differential on a sector generator of the `K`-sector**, in the form the
operator identity is proved from: on the wedge of the standard generators indexed by a tuple
`v` of variables in `supp K`, tensored with a coefficient form `ω`. -/
theorem relativeSectorMap_dividedPowerDeRham_tmul_ιMulti (K : W →₀ ℕ) (i j : ℕ)
    (v : Fin j → (K.support : Type uW))
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) :
    dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) (i + j)
        (relativeSectorMap A B W K i j
          (exteriorPower.ιMulti (B : Type uB) j
            (fun k ↦ Finsupp.single (v k) (1 : (B : Type uB))) ⊗ₜ[(B : Type uB)] omega)) =
      exteriorPower.degCongr (Nat.succ_add i j)
          (relativeSectorMap A B W K (i + 1) j
            (exteriorPower.ιMulti (B : Type uB) j
                (fun k ↦ Finsupp.single (v k) (1 : (B : Type uB))) ⊗ₜ[(B : Type uB)]
              dividedPowerDeRham B.dividedPowers i omega)) +
        (-1 : setIndexedDividedPowerPolynomialAlgebra B W) ^ i •
          exteriorPower.degCongr (Nat.add_succ i j)
            (relativeSectorMap A B W K i (j + 1)
              (LinearMap.rTensor (dividedPowerDifferentialForms (A := A) B.dividedPowers i)
                (exteriorPower.wedgeLeft (sectorVector B W K) j)
                (exteriorPower.ιMulti (B : Type uB) j
                  (fun k ↦ Finsupp.single (v k) (1 : (B : Type uB))) ⊗ₜ[(B : Type uB)]
                    omega))) := by
  classical
  -- The left hand side, by the bigraded Leibniz computation.
  refine Eq.trans (congrArg (dividedPowerDeRham
      (setIndexedDividedPowerPolynomialDividedPowers B W) (i + j))
    (relativeSectorMap_tmul_ιMulti A B W K i j v omega)) ?_
  refine Eq.trans (sectorGenerator_dividedPowerDeRham A B W
    (K - finsetMultiIndex (Finset.univ.image (Subtype.val ∘ v))) i omega j
    (Subtype.val ∘ v)) ?_
  refine congrArg₂ (· + ·) ?_ ?_
  · exact congrArg (exteriorPower.degCongr (Nat.succ_add i j))
      (relativeSectorMap_tmul_ιMulti A B W K (i + 1) j v
        (dividedPowerDeRham B.dividedPowers i omega)).symm
  -- The Koszul term: wedging by the sector vector, expanded over `supp K`.
  refine congrArg (fun z : dividedPowerPolynomialForms A B W (i + j + 1) ↦
    (-1 : setIndexedDividedPowerPolynomialAlgebra B W) ^ i • z) ?_
  refine Eq.trans ?_ (congrArg (fun z : sectorModule A B W K i (j + 1) ↦
    exteriorPower.degCongr (Nat.add_succ i j) (relativeSectorMap A B W K i (j + 1) z))
      (rTensor_wedgeLeft_sectorVector_tmul_ιMulti A B W K i j v omega)).symm
  -- Both sides are now sums over `supp K`.
  refine Eq.trans ?_ (congrArg (exteriorPower.degCongr (Nat.add_succ i j))
    (Eq.trans (map_sum (relativeSectorMap A B W K i (j + 1)) _ Finset.univ)
      (Finset.sum_congr rfl fun u _ ↦ relativeSectorMap_tmul_ιMulti A B W K i (j + 1)
        (Fin.cons u v) omega))).symm
  refine Eq.trans ?_ (map_sum (exteriorPower.degCongr (Nat.add_succ i j)) _ Finset.univ).symm
  refine Eq.trans ?_ (Finset.sum_congr rfl fun u _ ↦ congrArg
    (exteriorPower.degCongr (Nat.add_succ i j)) (sectorValue_cons A B W K i j v u omega)).symm
  refine Eq.trans ?_ (Finset.sum_coe_sort K.support (fun w : W ↦
    exteriorPower.degCongr (Nat.add_succ i j) (sectorGenerator A B W
      (K - finsetMultiIndex (insert w (Finset.univ.image (Subtype.val ∘ v)))) i omega (j + 1)
      (Fin.cons w (Subtype.val ∘ v))))).symm
  -- Extend the sum from `supp (K - 1_s)` to `supp K`, then match term by term.
  refine Eq.trans (Finset.sum_subset
    (support_sub_finsetMultiIndex_subset K (Finset.univ.image (Subtype.val ∘ v)))
    (fun w hw hnw ↦ ?_)) (Finset.sum_congr rfl fun w hw ↦ ?_)
  · refine Eq.trans (congrArg (exteriorPower.degCongr (Nat.add_succ i j))
      (sectorGenerator_cons_eq_zero A B W _ i omega j (Subtype.val ∘ v) w
        (mem_finset_of_notMem_sub_support K (Finset.univ.image (Subtype.val ∘ v)) w hw hnw))) ?_
    exact map_zero _
  · by_cases hws : w ∈ Finset.univ.image (Subtype.val ∘ v)
    · rw [sectorGenerator_cons_eq_zero A B W _ i omega j _ w hws,
        sectorGenerator_cons_eq_zero A B W _ i omega j _ w hws]
    · exact congrArg (fun M : W →₀ ℕ ↦ exteriorPower.degCongr (Nat.add_succ i j)
        (sectorGenerator A B W M i omega (j + 1) (Fin.cons w (Subtype.val ∘ v))))
        (lower_multiIndex_insert K (Finset.univ.image (Subtype.val ∘ v)) w hws)

/-! ### The horizontal differential and the operator identity -/

/-- The sector basis vector indexed by `I`, as the wedge of the standard generators of the
variables of `I` in increasing order. -/
theorem sectorExteriorBasis_apply (K : W →₀ ℕ) (j : ℕ)
    (I : Set.powersetCard (K.support : Type uW) j) :
    sectorExteriorBasis B W K j I =
      exteriorPower.ιMulti (B : Type uB) j (fun k ↦ Finsupp.single
        (Set.powersetCard.ofFinEmbEquiv.symm I k) (1 : (B : Type uB))) :=
  exteriorPower.basis_apply _ j _ I

/-- **The sector read as a family of coefficient forms** indexed by the `j`-element subsets of
`supp K`.  The Koszul factor is free on those subsets, so the tensor product is a direct sum of
copies of `Ωⁱ_{B/A,δ}`; this is the identification, and it is what makes the horizontal
differential of the sector — which is not a tensor product of maps, the de Rham differential
being only `A`-linear — well defined. -/
def sectorModuleEquiv (K : W →₀ ℕ) (i j : ℕ) :
    sectorModule A B W K i j ≃ₗ[(B : Type uB)]
      (Set.powersetCard (K.support : Type uW) j →₀
        dividedPowerDifferentialForms (A := A) B.dividedPowers i) :=
  (TensorProduct.congr (sectorExteriorBasis B W K j).repr
      (LinearEquiv.refl (B : Type uB)
        (dividedPowerDifferentialForms (A := A) B.dividedPowers i))).trans
    (TensorProduct.finsuppScalarLeft (B : Type uB)
      (dividedPowerDifferentialForms (A := A) B.dividedPowers i)
      (Set.powersetCard (K.support : Type uW) j))

/-- The equivalence `sectorModuleEquiv` sends `e_I ⊗ ω` to the finitely supported function
`Finsupp.single I ω`. -/
theorem sectorModuleEquiv_basis_tmul (K : W →₀ ℕ) (i j : ℕ)
    (I : Set.powersetCard (K.support : Type uW) j)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) :
    sectorModuleEquiv A B W K i j
        (sectorExteriorBasis B W K j I ⊗ₜ[(B : Type uB)] omega) =
      Finsupp.single I omega := by
  classical
  change TensorProduct.finsuppScalarLeft _ _ _
    (TensorProduct.congr (sectorExteriorBasis B W K j).repr (LinearEquiv.refl _ _)
      (sectorExteriorBasis B W K j I ⊗ₜ[(B : Type uB)] omega)) = _
  rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply,
    (sectorExteriorBasis B W K j).repr_self,
    TensorProduct.finsuppScalarLeft_apply_tmul,
    Finsupp.sum_single_index (by rw [zero_smul, Finsupp.single_zero]), one_smul]

/-- The inverse of `sectorModuleEquiv` sends `Finsupp.single I ω` to `e_I ⊗ ω`. -/
theorem sectorModuleEquiv_symm_single (K : W →₀ ℕ) (i j : ℕ)
    (I : Set.powersetCard (K.support : Type uW) j)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) :
    (sectorModuleEquiv A B W K i j).symm (Finsupp.single I omega) =
      sectorExteriorBasis B W K j I ⊗ₜ[(B : Type uB)] omega :=
  (LinearEquiv.symm_apply_eq _).mpr (sectorModuleEquiv_basis_tmul A B W K i j I omega).symm

/-- **The horizontal differential of the `K`-sector**, `1 ⊗ d_B`: the divided power de Rham
differential of the base applied in each coordinate of the free Koszul factor.

It is only `A`-linear, and it is not `LinearMap.lTensor` of anything: `d_B` is not `B`-linear,
so there is no map of `B`-modules to tensor with.  What makes it well defined is that the
Koszul factor is free with a canonical basis, and that is the content of
`Crystalline.DividedPowerPolynomial.sectorModuleEquiv`. -/
def relativeSectorCoefficientDifferential (K : W →₀ ℕ) (i j : ℕ) :
    sectorModule A B W K i j →ₗ[A] sectorModule A B W K (i + 1) j :=
  (((sectorModuleEquiv A B W K (i + 1) j).symm.toLinearMap).restrictScalars A).comp
    ((Finsupp.mapRange.linearMap
        (dividedPowerDeRhamLinearMap (A := A) B.dividedPowers i)).comp
      (((sectorModuleEquiv A B W K i j).toLinearMap).restrictScalars A))

/-- The horizontal differential `relativeSectorCoefficientDifferential` sends `e_I ⊗ ω` to
`e_I ⊗ d_B ω`. -/
theorem relativeSectorCoefficientDifferential_basis_tmul (K : W →₀ ℕ) (i j : ℕ)
    (I : Set.powersetCard (K.support : Type uW) j)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) :
    relativeSectorCoefficientDifferential A B W K i j
        (sectorExteriorBasis B W K j I ⊗ₜ[(B : Type uB)] omega) =
      sectorExteriorBasis B W K j I ⊗ₜ[(B : Type uB)]
        dividedPowerDeRham B.dividedPowers i omega := by
  change (sectorModuleEquiv A B W K (i + 1) j).symm
    (Finsupp.mapRange.linearMap (dividedPowerDeRhamLinearMap (A := A) B.dividedPowers i)
      (sectorModuleEquiv A B W K i j
        (sectorExteriorBasis B W K j I ⊗ₜ[(B : Type uB)] omega))) = _
  rw [sectorModuleEquiv_basis_tmul, Finsupp.mapRange.linearMap_apply,
    Finsupp.mapRange_single (hf := map_zero _), dividedPowerDeRhamLinearMap_apply,
    sectorModuleEquiv_symm_single]

private theorem relativeSectorMap_dividedPowerDeRham_of_symm_single (K : W →₀ ℕ) (i j : ℕ)
    (I : Set.powersetCard (K.support : Type uW) j)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i)
    (y : sectorModule A B W K i j)
    (hy : (sectorModuleEquiv A B W K i j).symm (Finsupp.single I omega) = y) :
    dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) (i + j)
        (relativeSectorMap A B W K i j y) =
      exteriorPower.degCongr (Nat.succ_add i j)
          (relativeSectorMap A B W K (i + 1) j
            (relativeSectorCoefficientDifferential A B W K i j y)) +
        (-1 : setIndexedDividedPowerPolynomialAlgebra B W) ^ i •
          exteriorPower.degCongr (Nat.add_succ i j)
            (relativeSectorMap A B W K i (j + 1)
              (LinearMap.rTensor (dividedPowerDifferentialForms (A := A) B.dividedPowers i)
                (exteriorPower.wedgeLeft (sectorVector B W K) j) y)) := by
  classical
  have hy2 : y = exteriorPower.ιMulti (B : Type uB) j
      (fun k ↦ Finsupp.single (Set.powersetCard.ofFinEmbEquiv.symm I k)
        (1 : (B : Type uB))) ⊗ₜ[(B : Type uB)] omega := by
    rw [← hy, sectorModuleEquiv_symm_single, sectorExteriorBasis_apply]
  subst hy2
  have hD : relativeSectorCoefficientDifferential A B W K i j
        (exteriorPower.ιMulti (B : Type uB) j
          (fun k ↦ Finsupp.single (Set.powersetCard.ofFinEmbEquiv.symm I k)
            (1 : (B : Type uB))) ⊗ₜ[(B : Type uB)] omega) =
      exteriorPower.ιMulti (B : Type uB) j
          (fun k ↦ Finsupp.single (Set.powersetCard.ofFinEmbEquiv.symm I k)
            (1 : (B : Type uB))) ⊗ₜ[(B : Type uB)]
        dividedPowerDeRham B.dividedPowers i omega :=
    Eq.subst (motive := fun X : ⋀[(B : Type uB)]^j (K.support →₀ (B : Type uB)) ↦
        relativeSectorCoefficientDifferential A B W K i j
            (X ⊗ₜ[(B : Type uB)] omega) =
          X ⊗ₜ[(B : Type uB)] dividedPowerDeRham B.dividedPowers i omega)
      (sectorExteriorBasis_apply B W K j I)
      (relativeSectorCoefficientDifferential_basis_tmul A B W K i j I omega)
  refine Eq.trans (relativeSectorMap_dividedPowerDeRham_tmul_ιMulti A B W K i j
    (Set.powersetCard.ofFinEmbEquiv.symm I) omega) ?_
  exact congrArg (fun z : sectorModule A B W K (i + 1) j ↦
      exteriorPower.degCongr (Nat.succ_add i j)
          (relativeSectorMap A B W K (i + 1) j z) +
        (-1 : setIndexedDividedPowerPolynomialAlgebra B W) ^ i •
          exteriorPower.degCongr (Nat.add_succ i j)
            (relativeSectorMap A B W K i (j + 1)
              (LinearMap.rTensor
                (dividedPowerDifferentialForms (A := A) B.dividedPowers i)
                (exteriorPower.wedgeLeft (sectorVector B W K) j)
                (exteriorPower.ιMulti (B : Type uB) j
                    (fun k ↦ Finsupp.single
                      (Set.powersetCard.ofFinEmbEquiv.symm I k) (1 : (B : Type uB)))
                  ⊗ₜ[(B : Type uB)] omega)))) hD.symm

set_option synthInstance.maxHeartbeats 100000 in
-- instance search for the module structures on tensor products and exterior powers over the
-- divided power polynomial algebra is slow
/-- **The de Rham differential on the `K`-sector.**  Through the sector map, the divided power
de Rham differential of `P` is the total differential of the bicomplex
`Kos(supp K) ⊗_B Ω^*_{B/A,δ}`: the horizontal differential `1 ⊗ d_B`, plus `(-1)^i` times the
Koszul differential, which is wedging the Koszul factor by `∑_{w ∈ supp K} e_w`.

For `I = ⊥` the coefficient factor collapses, the first term disappears and the sign is `+1`,
which recovers the statement of the absolute argument that `d` *is* exterior multiplication by
the Koszul vector on each sector. -/
theorem relativeSectorMap_dividedPowerDeRham (K : W →₀ ℕ) (i j : ℕ)
    (x : sectorModule A B W K i j) :
    dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) (i + j)
        (relativeSectorMap A B W K i j x) =
      exteriorPower.degCongr (Nat.succ_add i j)
          (relativeSectorMap A B W K (i + 1) j
            (relativeSectorCoefficientDifferential A B W K i j x)) +
        (-1 : setIndexedDividedPowerPolynomialAlgebra B W) ^ i •
          exteriorPower.degCongr (Nat.add_succ i j)
            (relativeSectorMap A B W K i (j + 1)
              (LinearMap.rTensor (dividedPowerDifferentialForms (A := A) B.dividedPowers i)
                (exteriorPower.wedgeLeft (sectorVector B W K) j) x)) := by
  classical
  obtain ⟨f, rfl⟩ := (sectorModuleEquiv A B W K i j).symm.surjective x
  induction f using Finsupp.induction_linear with
  | zero => simp only [LinearEquiv.map_zero, LinearMap.map_zero, dividedPowerDeRham_zero, smul_zero,
      add_zero]
  | add f g hf hg =>
    simp only [LinearEquiv.map_add, LinearMap.map_add, dividedPowerDeRham_add, smul_add]
    exact Eq.trans (congrArg₂ (· + ·) hf hg) (by abel)
  | single I omega =>
    exact relativeSectorMap_dividedPowerDeRham_of_symm_single A B W K i j I omega _ rfl

end Sector


end DividedPowerPolynomial

end Crystalline

end
