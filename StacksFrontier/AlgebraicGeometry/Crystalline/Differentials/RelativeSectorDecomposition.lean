module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.RelativeSectorMap
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.PolynomialFormsDecomposition

/-!
# The sector decomposition of the forms of a divided power polynomial algebra

Let `A` be a ring, let `(B, I, δ)` be a divided power ring which is an `A`-algebra, let `W`
index a family of divided power variables and let `P = B⟨x_w : w ∈ W⟩`.
`Crystalline.DividedPowerPolynomial.dividedPowerPolynomialFormsEquiv` splits

`Ωⁿ_{P/A,δ'} ≅ ⨁_{i + j = n} (Set.powersetCard W j →₀ ((W →₀ ℕ) →₀ Ωⁱ_{B/A,δ}))`,

`B`-linearly: a form is a family of coefficient forms indexed by an exponent vector `L` and a
`j`-element subset `J` of `W`.  This module identifies the summand indexed by `(i, j, L, J)`
with the **sector generator**

`x^{[L]} · ψ(ω) ∧ d x_{J}`

of `Crystalline.DividedPowerPolynomial.sectorGenerator`, whose total multi-index is
`K = L + 1_J`, and so exhibits the decomposition as the assembly of the sector maps.

## What plays the part of the absolute basis

In the absolute argument `Ωⁿ_{P/A,δ'}` is **free** over `A` on the pairs `(L, J)`, and both
the contracting homotopy and the proof that it contracts are `Module.Basis.constr` and
`Module.Basis.ext` on that basis.  For a nontrivial divided power ideal `I` there is no basis:
the coefficient factor `Ωⁱ_{B/A,δ}` is an arbitrary `B`-module.  What survives is the
`Finsupp` above, and `Finsupp.lsum` and `Finsupp.lhom_ext` play the two parts — a map out is
prescribed by its values on `Finsupp.single`, and two maps out agreeing there are equal.

No direct sum over the total multi-index `K` is needed, and none is built: as in the absolute
argument the sector of a generator is determined by the generator, `K` being `L + 1_J`.

## Main definitions

* `Crystalline.DividedPowerPolynomial.polynomialBidegreeFormsMonomialEquiv` — the bidegree
  `(i, j)` summand as the free module on the pairs `(J, L)` with coefficients in `Ωⁱ_{B/A,δ}`.
* `Crystalline.DividedPowerPolynomial.sectorLiftSubset` — a `j`-element subset of `W` inside
  `supp K`, read as a `j`-element subset of `supp K`.

## Main results

* `Crystalline.DividedPowerPolynomial.dividedPowerPolynomialFormsEquiv_sectorGenerator` —
  **the decomposition on a sector generator**: it lands in the single summand `(i, j)`, at the
  slot indexed by the exponent vector and the subset.
* `Crystalline.DividedPowerPolynomial.dividedPowerPolynomialFormsEquiv_symm_lof_single` — the
  same read backwards, which is the form the assembly consumes.
* `Crystalline.DividedPowerPolynomial.relativeSectorMap_sectorLiftSubset` — the sector map of
  `K = L + 1_J` carries the sector basis vector of `J` to that generator.

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

section Decomposition

variable (A : Type uA) [CommRing A] (B : DividedPowerRing.{uB}) [Algebra A B] (W : Type uW)

/-- **The comparison of forms on a wedge of coefficient differentials.**  `ψ` carries
`d b₁ ∧ ⋯ ∧ d bᵢ` to the wedge of the differentials of the images, which is the only value of
`ψ` the decomposition needs: such wedges span `Ωⁱ_{B/A,δ}` over `B`. -/
theorem coefficientFormsMap_ιMulti (i : ℕ) (b : Fin i → (B : Type uB)) :
    coefficientFormsMap A B W i
        (exteriorPower.ιMulti (B : Type uB) i fun k ↦
          dividedPowerDifferential (A := A) B.dividedPowers (b k)) =
      exteriorPower.ιMulti (setIndexedDividedPowerPolynomialAlgebra B W) i fun k ↦
        dividedPowerDifferential (A := A) (setIndexedDividedPowerPolynomialDividedPowers B W)
          (algebraMap (B : Type uB) (setIndexedDividedPowerPolynomialAlgebra B W) (b k)) :=
  mapDifferentialFormsOfDPMorphism_ιMulti_d (A := A) B.ideal B.dividedPowers
    (setIndexedDividedPowerPolynomialDividedPowers B W) (coefficientAlgHom A B W)
    (coefficientAlgHom_isDPMorphism A B W) i b

/-- The base change of a wedge of coefficient differentials, on a pure tensor with scalar `1`. -/
theorem polynomialCoefficientFormsBaseChangeEquiv_one_tmul_ιMulti (i : ℕ)
    (a : Fin i → dividedPowerDifferentials (A := A) B.dividedPowers) :
    polynomialCoefficientFormsBaseChangeEquiv A B W i
        ((1 : setIndexedDividedPowerPolynomialAlgebra B W) ⊗ₜ[(B : Type uB)]
          exteriorPower.ιMulti (B : Type uB) i a) =
      exteriorPower.ιMulti (setIndexedDividedPowerPolynomialAlgebra B W) i fun k ↦
        (1 : setIndexedDividedPowerPolynomialAlgebra B W) ⊗ₜ[(B : Type uB)] a k := by
  rw [polynomialCoefficientFormsBaseChangeEquiv,
    ExteriorAlgebra.exteriorPowerBaseChange_tmul_ιMulti, one_smul]

/-- **The decomposition on a coefficient form wedged with variable differentials.**

`Crystalline.DividedPowerPolynomial.dividedPowerPolynomialFormsEquiv_wedge` is this for a
coefficient form that is itself a wedge of differentials; those span `Ωⁱ_{B/A,δ}` over `B`, so
`B`-linearity of both sides extends it to an arbitrary coefficient form.  That extension is
the whole point: for a nontrivial divided power ideal `I` a general `ω` is **not** a wedge of
differentials, and the absolute argument, which only ever meets wedges, never needs this. -/
theorem dividedPowerPolynomialFormsEquiv_wedgeMul_coefficientFormsMap (i j : ℕ)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) (v : Fin j → W) :
    dividedPowerPolynomialFormsEquiv A B W (i + j)
        (exteriorPower.wedgeMul i j (coefficientFormsMap A B W i omega)
          (variableWedge A B W j v)) =
      DirectSum.lof (setIndexedDividedPowerPolynomialAlgebra B W)
          {ij : ℕ × ℕ // ij.1 + ij.2 = i + j}
          (fun ij ↦ polynomialBidegreeForms A B W ij.1.1 ij.1.2) ⟨(i, j), rfl⟩
        (polynomialCoefficientFormsBaseChangeEquiv A B W i
              ((1 : setIndexedDividedPowerPolynomialAlgebra B W) ⊗ₜ[(B : Type uB)] omega) ⊗ₜ[
            setIndexedDividedPowerPolynomialAlgebra B W]
          exteriorPower.ιMulti (setIndexedDividedPowerPolynomialAlgebra B W) j fun k ↦
            Finsupp.single (v k) (1 : setIndexedDividedPowerPolynomialAlgebra B W)) := by
  have hspan : Submodule.span (B : Type uB)
      (⇑(exteriorPower.ιMulti (B : Type uB) i) ''
        {a : Fin i → dividedPowerDifferentials (A := A) B.dividedPowers |
          Set.range a ⊆ Set.range (dividedPowerDifferential (A := A) B.dividedPowers)}) = ⊤ :=
    exteriorPower.ιMulti_span_of_span (B : Type uB) i _
      (dividedPowerDifferentials_span (A := A) B.dividedPowers)
  have h :
      ((dividedPowerPolynomialFormsEquiv A B W (i + j)).toLinearMap.restrictScalars
          (B : Type uB)) ∘ₗ
        (((exteriorPower.wedgeMul i j).flip (variableWedge A B W j v)).restrictScalars
          (B : Type uB)) ∘ₗ
        coefficientFormsMap A B W i =
      ((DirectSum.lof (setIndexedDividedPowerPolynomialAlgebra B W)
            {ij : ℕ × ℕ // ij.1 + ij.2 = i + j}
            (fun ij ↦ polynomialBidegreeForms A B W ij.1.1 ij.1.2)
            ⟨(i, j), rfl⟩).restrictScalars (B : Type uB)) ∘ₗ
        (((TensorProduct.mk (setIndexedDividedPowerPolynomialAlgebra B W)
              (polynomialCoefficientForms A B W i) (polynomialVariableForms B W j)).flip
            (exteriorPower.ιMulti (setIndexedDividedPowerPolynomialAlgebra B W) j fun k ↦
              Finsupp.single (v k)
                (1 : setIndexedDividedPowerPolynomialAlgebra B W))).restrictScalars
          (B : Type uB)) ∘ₗ
        ((polynomialCoefficientFormsBaseChangeEquiv A B W i).toLinearMap.restrictScalars
          (B : Type uB)) ∘ₗ
        TensorProduct.mk (B : Type uB) (setIndexedDividedPowerPolynomialAlgebra B W)
          (dividedPowerDifferentialForms (A := A) B.dividedPowers i) 1 := by
    refine LinearMap.ext_on hspan ?_
    rintro x ⟨a, ha, rfl⟩
    choose b hb using fun k ↦ ha (Set.mem_range_self k)
    have ha' : a = fun k ↦ dividedPowerDifferential (A := A) B.dividedPowers (b k) :=
      (funext hb).symm
    subst ha'
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
      LinearEquiv.coe_coe, LinearMap.flip_apply, TensorProduct.mk_apply]
    have hw : exteriorPower.wedgeMul i j
          (coefficientFormsMap A B W i (exteriorPower.ιMulti (B : Type uB) i fun k ↦
            dividedPowerDifferential (A := A) B.dividedPowers (b k)))
          (variableWedge A B W j v) =
        exteriorPower.ιMulti (setIndexedDividedPowerPolynomialAlgebra B W) (i + j)
          (Fin.append
            (fun k ↦ dividedPowerDifferential (A := A)
              (setIndexedDividedPowerPolynomialDividedPowers B W)
              (algebraMap (B : Type uB) (setIndexedDividedPowerPolynomialAlgebra B W) (b k)))
            fun k ↦ dividedPowerDifferential (A := A)
              (setIndexedDividedPowerPolynomialDividedPowers B W)
              (dividedPowerPolynomialVariable (B : Type uB) (v k))) :=
      Eq.trans
        (congrArg (fun z : dividedPowerPolynomialForms A B W i ↦
            exteriorPower.wedgeMul i j z (variableWedge A B W j v))
          (coefficientFormsMap_ιMulti A B W i b))
        (exteriorPower.wedgeMul_ιMulti i j
          (fun k ↦ dividedPowerDifferential (A := A)
            (setIndexedDividedPowerPolynomialDividedPowers B W)
            (algebraMap (B : Type uB) (setIndexedDividedPowerPolynomialAlgebra B W) (b k)))
          fun k ↦ dividedPowerDifferential (A := A)
            (setIndexedDividedPowerPolynomialDividedPowers B W)
            (dividedPowerPolynomialVariable (B : Type uB) (v k)))
    have hbc : polynomialCoefficientFormsBaseChangeEquiv A B W i
          ((1 : setIndexedDividedPowerPolynomialAlgebra B W) ⊗ₜ[(B : Type uB)]
            exteriorPower.ιMulti (B : Type uB) i fun k ↦
              dividedPowerDifferential (A := A) B.dividedPowers (b k)) =
        exteriorPower.ιMulti (setIndexedDividedPowerPolynomialAlgebra B W) i fun k ↦
          (1 : setIndexedDividedPowerPolynomialAlgebra B W) ⊗ₜ[(B : Type uB)]
            dividedPowerDifferential (A := A) B.dividedPowers (b k) :=
      polynomialCoefficientFormsBaseChangeEquiv_one_tmul_ιMulti A B W i
        (fun k ↦ dividedPowerDifferential (A := A) B.dividedPowers (b k))
    refine Eq.trans (congrArg (fun z : dividedPowerPolynomialForms A B W (i + j) ↦
      dividedPowerPolynomialFormsEquiv A B W (i + j) z) hw) ?_
    refine Eq.trans (dividedPowerPolynomialFormsEquiv_wedge A B W i j b v) ?_
    exact congrArg (fun z : polynomialCoefficientForms A B W i ↦
        DirectSum.lof (setIndexedDividedPowerPolynomialAlgebra B W)
          {ij : ℕ × ℕ // ij.1 + ij.2 = i + j}
          (fun ij ↦ polynomialBidegreeForms A B W ij.1.1 ij.1.2) ⟨(i, j), rfl⟩
          (z ⊗ₜ[setIndexedDividedPowerPolynomialAlgebra B W]
            exteriorPower.ιMulti (setIndexedDividedPowerPolynomialAlgebra B W) j fun k ↦
              Finsupp.single (v k) (1 : setIndexedDividedPowerPolynomialAlgebra B W)))
      hbc.symm
  simpa only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
    LinearEquiv.coe_coe, LinearMap.flip_apply, TensorProduct.mk_apply] using
    DFunLike.congr_fun h omega

/-- **The decomposition on a sector generator.**  The generator `x^{[L]} · ψ(ω) ∧ d x_v` lands
in the single bidegree-`(i, j)` summand, as the pure tensor whose coefficient factor is
`x^{[L]} ⊗ ω`.  The monomial coefficient is carried through by `P`-linearity. -/
theorem dividedPowerPolynomialFormsEquiv_sectorGenerator (L : W →₀ ℕ) (i j : ℕ)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) (v : Fin j → W) :
    dividedPowerPolynomialFormsEquiv A B W (i + j) (sectorGenerator A B W L i omega j v) =
      DirectSum.lof (setIndexedDividedPowerPolynomialAlgebra B W)
          {ij : ℕ × ℕ // ij.1 + ij.2 = i + j}
          (fun ij ↦ polynomialBidegreeForms A B W ij.1.1 ij.1.2) ⟨(i, j), rfl⟩
        (polynomialCoefficientFormsBaseChangeEquiv A B W i
              (dividedPowerPolynomialMonomial (B : Type uB) L ⊗ₜ[(B : Type uB)] omega) ⊗ₜ[
            setIndexedDividedPowerPolynomialAlgebra B W]
          exteriorPower.ιMulti (setIndexedDividedPowerPolynomialAlgebra B W) j fun k ↦
            Finsupp.single (v k) (1 : setIndexedDividedPowerPolynomialAlgebra B W)) := by
  have hmonomial : dividedPowerPolynomialMonomial (B : Type uB) L •
        ((1 : setIndexedDividedPowerPolynomialAlgebra B W) ⊗ₜ[(B : Type uB)] omega) =
      dividedPowerPolynomialMonomial (B : Type uB) L ⊗ₜ[(B : Type uB)] omega := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  refine Eq.trans (map_smul (dividedPowerPolynomialFormsEquiv A B W (i + j))
    (dividedPowerPolynomialMonomial (B : Type uB) L) _) ?_
  refine Eq.trans (congrArg (fun z ↦ dividedPowerPolynomialMonomial (B : Type uB) L • z)
    (dividedPowerPolynomialFormsEquiv_wedgeMul_coefficientFormsMap A B W i j omega v)) ?_
  refine Eq.trans (map_smul (DirectSum.lof (setIndexedDividedPowerPolynomialAlgebra B W)
    {ij : ℕ × ℕ // ij.1 + ij.2 = i + j}
    (fun ij ↦ polynomialBidegreeForms A B W ij.1.1 ij.1.2) ⟨(i, j), rfl⟩)
    (dividedPowerPolynomialMonomial (B : Type uB) L) _).symm ?_
  refine congrArg (DirectSum.lof (setIndexedDividedPowerPolynomialAlgebra B W)
    {ij : ℕ × ℕ // ij.1 + ij.2 = i + j}
    (fun ij ↦ polynomialBidegreeForms A B W ij.1.1 ij.1.2) ⟨(i, j), rfl⟩) ?_
  refine Eq.trans (TensorProduct.smul_tmul' _ _ _).symm ?_
  exact congrArg (fun z : polynomialCoefficientForms A B W i ↦
      z ⊗ₜ[setIndexedDividedPowerPolynomialAlgebra B W]
        exteriorPower.ιMulti (setIndexedDividedPowerPolynomialAlgebra B W) j fun k ↦
          Finsupp.single (v k) (1 : setIndexedDividedPowerPolynomialAlgebra B W))
    (Eq.trans (map_smul (polynomialCoefficientFormsBaseChangeEquiv A B W i) _ _).symm
      (congrArg (polynomialCoefficientFormsBaseChangeEquiv A B W i) hmonomial))

/-! ### The bidegree summand as a free module on exponent vectors and subsets -/

variable [LinearOrder W]

/-- **The bidegree-`(i, j)` summand as the free module on the pairs `(J, L)`.**  It is the
composite of the freeness of the variable factor on the `j`-element subsets of `W` and the
freeness of `P` over `B` on the divided power monomials; only `B`-linearity survives the
second, which is why this is not an isomorphism of `P`-modules. -/
def polynomialBidegreeFormsMonomialEquiv (i j : ℕ) :
    polynomialBidegreeForms A B W i j ≃ₗ[(B : Type uB)]
      (Set.powersetCard W j →₀
        ((W →₀ ℕ) →₀ dividedPowerDifferentialForms (A := A) B.dividedPowers i)) :=
  ((polynomialBidegreeFormsFreeEquiv A B W i j).restrictScalars (B : Type uB)).trans
    (Finsupp.mapRange.linearEquiv (polynomialCoefficientMonomialEquiv A B W i))

/-- The value of the inverse of the free decomposition on a single slot: the pure tensor whose
coefficient factor is the monomial `x^{[L]}` against `ω` and whose variable factor is the
basis wedge of the subset `J`. -/
theorem polynomialBidegreeFormsMonomialEquiv_symm_single (i j : ℕ)
    (J : Set.powersetCard W j) (L : W →₀ ℕ)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) :
    (polynomialBidegreeFormsMonomialEquiv A B W i j).symm
        (Finsupp.single J (Finsupp.single L omega)) =
      polynomialCoefficientFormsBaseChangeEquiv A B W i
          (dividedPowerPolynomialMonomial (B : Type uB) L ⊗ₜ[(B : Type uB)] omega) ⊗ₜ[
        setIndexedDividedPowerPolynomialAlgebra B W] polynomialVariableFormsBasis B W j J := by
  classical
  refine (LinearEquiv.symm_apply_eq _).mpr (Eq.symm ?_)
  have hfree : polynomialBidegreeFormsFreeEquiv A B W i j
        (polynomialCoefficientFormsBaseChangeEquiv A B W i
            (dividedPowerPolynomialMonomial (B : Type uB) L ⊗ₜ[(B : Type uB)] omega) ⊗ₜ[
          setIndexedDividedPowerPolynomialAlgebra B W]
          polynomialVariableFormsBasis B W j J) =
      Finsupp.single J (dividedPowerPolynomialMonomial (B : Type uB) L ⊗ₜ[(B : Type uB)]
        omega) :=
    Eq.trans (polynomialBidegreeFormsFreeEquiv_tmul_basis A B W i j _ J)
      (congrArg (Finsupp.single J)
        ((polynomialCoefficientFormsBaseChangeEquiv A B W i).symm_apply_apply _))
  change Finsupp.mapRange.linearEquiv (polynomialCoefficientMonomialEquiv A B W i)
      (polynomialBidegreeFormsFreeEquiv A B W i j
        (polynomialCoefficientFormsBaseChangeEquiv A B W i
            (dividedPowerPolynomialMonomial (B : Type uB) L ⊗ₜ[(B : Type uB)] omega) ⊗ₜ[
          setIndexedDividedPowerPolynomialAlgebra B W]
          polynomialVariableFormsBasis B W j J)) = _
  rw [hfree, Finsupp.mapRange.linearEquiv_apply, Finsupp.mapRange_single (hf := map_zero _),
    polynomialCoefficientMonomialEquiv_monomial_tmul]

/-- The variable factor's basis vector, written as the wedge of the standard generators indexed
by the increasing enumeration of the subset. -/
theorem polynomialVariableFormsBasis_eq_ιMulti (j : ℕ) (J : Set.powersetCard W j) :
    polynomialVariableFormsBasis B W j J =
      exteriorPower.ιMulti (setIndexedDividedPowerPolynomialAlgebra B W) j fun k ↦
        Finsupp.single (Set.powersetCard.ofFinEmbEquiv.symm J k)
          (1 : setIndexedDividedPowerPolynomialAlgebra B W) :=
  polynomialVariableFormsBasis_apply B W j J

/-- **The decomposition, read backwards, on a single slot**: the summand indexed by
`(i, j, J, L)` is the sector generator `x^{[L]} · ψ(ω) ∧ d x_J`, whose total multi-index is
`L + 1_J`.  This is the statement the assembly of the contracting homotopy consumes, and the
relative replacement for the absolute basis vector of `Ωⁿ_{P/A,δ'}`. -/
theorem dividedPowerPolynomialFormsEquiv_symm_lof_single (i j : ℕ) (L : W →₀ ℕ)
    (J : Set.powersetCard W j)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) :
    (dividedPowerPolynomialFormsEquiv A B W (i + j)).symm
        (DirectSum.lof (setIndexedDividedPowerPolynomialAlgebra B W)
          {ij : ℕ × ℕ // ij.1 + ij.2 = i + j}
          (fun ij ↦ polynomialBidegreeForms A B W ij.1.1 ij.1.2) ⟨(i, j), rfl⟩
          ((polynomialBidegreeFormsMonomialEquiv A B W i j).symm
            (Finsupp.single J (Finsupp.single L omega)))) =
      sectorGenerator A B W L i omega j fun k ↦ Set.powersetCard.ofFinEmbEquiv.symm J k := by
  refine (LinearEquiv.symm_apply_eq _).mpr (Eq.symm ?_)
  refine Eq.trans (dividedPowerPolynomialFormsEquiv_sectorGenerator A B W L i j omega
    (fun k ↦ Set.powersetCard.ofFinEmbEquiv.symm J k)) ?_
  refine congrArg (DirectSum.lof (setIndexedDividedPowerPolynomialAlgebra B W)
    {ij : ℕ × ℕ // ij.1 + ij.2 = i + j}
    (fun ij ↦ polynomialBidegreeForms A B W ij.1.1 ij.1.2) ⟨(i, j), rfl⟩) ?_
  refine Eq.trans ?_ (polynomialBidegreeFormsMonomialEquiv_symm_single A B W i j J L omega).symm
  exact congrArg (fun z : polynomialVariableForms B W j ↦
      polynomialCoefficientFormsBaseChangeEquiv A B W i
          (dividedPowerPolynomialMonomial (B : Type uB) L ⊗ₜ[(B : Type uB)] omega) ⊗ₜ[
        setIndexedDividedPowerPolynomialAlgebra B W] z)
    (polynomialVariableFormsBasis_eq_ιMulti B W j J).symm

/-! ### The sector of a generator -/

/-- **A `j`-element subset of `W` inside `supp K`, read as a `j`-element subset of `supp K`.**
This is the index of the sector basis vector a generator comes from. -/
def sectorLiftSubset (K : W →₀ ℕ) (j : ℕ) (J : Set.powersetCard W j)
    (hJ : J.val ⊆ K.support) : Set.powersetCard (K.support : Type uW) j :=
  ⟨J.val.subtype (· ∈ K.support), by
    change (J.val.subtype (· ∈ K.support)).card = j
    rw [Finset.card_subtype, Finset.filter_eq_self.mpr fun i hi ↦ hJ hi]
    exact J.property⟩

/-- Pushing the lifted subset back down to `W` recovers the subset. -/
theorem sectorLiftSubset_map (K : W →₀ ℕ) (j : ℕ) (J : Set.powersetCard W j)
    (hJ : J.val ⊆ K.support) :
    Set.powersetCard.map j (OrderEmbedding.subtype (· ∈ K.support)).toEmbedding
        (sectorLiftSubset W K j J hJ) = J :=
  Subtype.ext (Finset.subtype_map_of_mem fun _ hi ↦ hJ hi)

/-- **The increasing enumeration of the lifted subset is the increasing enumeration of the
subset.**  The inclusion `supp K ↪ W` is an order embedding, so it commutes with taking the
increasing enumeration. -/
theorem ofFinEmbEquiv_symm_sectorLiftSubset (K : W →₀ ℕ) (j : ℕ) (J : Set.powersetCard W j)
    (hJ : J.val ⊆ K.support) (k : Fin j) :
    ((Set.powersetCard.ofFinEmbEquiv.symm (sectorLiftSubset W K j J hJ) k :
        (K.support : Type uW)) : W) = Set.powersetCard.ofFinEmbEquiv.symm J k := by
  have h := Set.powersetCard.ofFinEmbEquiv_symm_map (sectorLiftSubset W K j J hJ)
    (OrderEmbedding.subtype (· ∈ K.support))
  rw [sectorLiftSubset_map] at h
  exact congrFun h k

/-- The image of the increasing enumeration of a subset is the subset. -/
theorem image_ofFinEmbEquiv_symm (j : ℕ) (J : Set.powersetCard W j) :
    Finset.univ.image (fun k ↦ Set.powersetCard.ofFinEmbEquiv.symm J k) = J.val := by
  classical
  ext a
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  exact Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem J a

/-- **The sector map of `K = L + 1_J` carries the sector basis vector of `J` to the generator
indexed by `(L, J)`.**  This is where the total multi-index of a generator is spent: the
exponent vector `K` lowered by one at each variable of `J` is `L` again. -/
theorem relativeSectorMap_sectorLiftSubset (L : W →₀ ℕ) (i j : ℕ)
    (J : Set.powersetCard W j)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) :
    relativeSectorMap A B W (L + finsetMultiIndex J.val) i j
        (sectorExteriorBasis B W (L + finsetMultiIndex J.val) j
            (sectorLiftSubset W (L + finsetMultiIndex J.val) j J
              (subset_support_add_finsetMultiIndex J.val L)) ⊗ₜ[(B : Type uB)] omega) =
      sectorGenerator A B W L i omega j fun k ↦ Set.powersetCard.ofFinEmbEquiv.symm J k := by
  classical
  have henum : (fun k ↦ (Set.powersetCard.ofFinEmbEquiv.symm
        (sectorLiftSubset W (L + finsetMultiIndex J.val) j J
          (subset_support_add_finsetMultiIndex J.val L)) k : W)) =
      fun k ↦ Set.powersetCard.ofFinEmbEquiv.symm J k :=
    funext fun k ↦ ofFinEmbEquiv_symm_sectorLiftSubset W _ j J _ k
  refine Eq.trans (congrArg (relativeSectorMap A B W (L + finsetMultiIndex J.val) i j)
    (congrArg (fun z ↦ z ⊗ₜ[(B : Type uB)] omega)
      (sectorExteriorBasis_apply B W (L + finsetMultiIndex J.val) j _))) ?_
  refine Eq.trans (relativeSectorMap_tmul_ιMulti A B W (L + finsetMultiIndex J.val) i j _
    omega) ?_
  refine Eq.trans (congrArg (fun g : Fin j → W ↦
    sectorGeneratorMap A B W (L + finsetMultiIndex J.val -
      finsetMultiIndex (Finset.univ.image g)) i j g omega) henum) ?_
  refine Eq.trans (congrArg (fun s : Finset W ↦
    sectorGenerator A B W (L + finsetMultiIndex J.val - finsetMultiIndex s) i omega j
      fun k ↦ Set.powersetCard.ofFinEmbEquiv.symm J k) (image_ofFinEmbEquiv_symm W j J)) ?_
  exact congrArg (fun M : W →₀ ℕ ↦ sectorGenerator A B W M i omega j
      fun k ↦ Set.powersetCard.ofFinEmbEquiv.symm J k)
    (add_tsub_cancel_right L (finsetMultiIndex J.val))

end Decomposition

end DividedPowerPolynomial

end Crystalline

end
