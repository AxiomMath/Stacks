module

public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerPoincare.SquareZeroDerivations
import all StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerPoincare.SquareZeroDerivations

/-!
# The divided power Poincaré lemma: bases of the divided power differential forms

The second part of `StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerPoincare`: the module
`Ω¹_{P/A,δ}` of the divided power polynomial algebra `P = A⟨x_w : w ∈ W⟩` is free over `P` on the
differentials `d x_w` (`Crystalline.dividedPowerDifferentialsCoordinateEquiv`,
`Crystalline.dividedPowerDifferentialsBasis`), the differentials of divided power monomials, the
resulting bases of `Ωⁿ_{P/A,δ}` over `P` and over `A`, and the de Rham differential of a basis
element.

## References

* [Stacks Project, Tag 07LC](https://stacks.math.columbia.edu/tag/07LC)
-/
@[expose] public section

universe u v w uA uW uM

namespace Crystalline

attribute [local implicit_reducible] RestrictScalars

open DividedPowers
open scoped TensorProduct

section OrdinaryExactness

open CategoryTheory
open scoped RightActions

variable (A : Type u) [CommRing A] (W : Type w)

attribute [local implicit_reducible] coefficientDividedPowerRing
  DividedPowers.setIndexedDividedPowerPolynomialDividedPowerRing
attribute [local instance low] setIndexedDividedPowerPolynomialCommRing
attribute [local instance low] coefficientDividedPowerRingAlgebra
attribute [local instance low] setIndexedDividedPowerPolynomialAlgebra'
attribute [local instance low] setIndexedDividedPowerPolynomialDividedPowerRingAlgebra
attribute [local instance low] indexedDividedPowerPolynomialFinsuppModule
attribute [local instance low] indexedDividedPowerPolynomialFinsuppModuleOp
attribute [local instance low] indexedDividedPowerPolynomialFinsuppCentral

/-- The `P`-module structure on `Ω¹_{P/A,δ}` for `P = A⟨x_w : w ∈ W⟩`, stated on the underlying
divided power algebra so that instance search finds it without unfolding the bundled ring. -/
private noncomputable instance dividedPowerDifferentialsPolynomialModule :
    Module (DividedPowerAlgebra (↑(coefficientDividedPowerRing A))
      (W →₀ ↑(coefficientDividedPowerRing A)))
      (dividedPowerDifferentials (A := A)
        (setIndexedDividedPowerPolynomialDividedPowerRing
          (coefficientDividedPowerRing A) W).dividedPowers) :=
  inferInstanceAs (Module ↑(setIndexedDividedPowerPolynomialDividedPowerRing
    (coefficientDividedPowerRing A) W) _)

/-- The same module structure, with the coefficient ring `coefficientDividedPowerRing A` unfolded
to `A`. -/
private noncomputable instance dividedPowerDifferentialsPolynomialModule' :
    Module (DividedPowerAlgebra A (W →₀ A))
      (dividedPowerDifferentials (A := A)
        (setIndexedDividedPowerPolynomialDividedPowerRing
          (coefficientDividedPowerRing A) W).dividedPowers) :=
  inferInstanceAs (Module ↑(setIndexedDividedPowerPolynomialDividedPowerRing
    (coefficientDividedPowerRing A) W) _)

private theorem dividedPowerDifferential_span
    {R : Type*} [CommRing R] {S : DividedPowerRing} [Algebra R S] :
    Submodule.span (↑S) (Set.range
      (dividedPowerDifferential (A := R) S.dividedPowers)) = ⊤ := by
  let rel := dividedPowerDifferentialRelations (A := R) S.dividedPowers
  change Submodule.span (↑S) (Set.range fun b : ↑S ↦
    rel.mkQ (KaehlerDifferential.D R (↑S) b)) = ⊤
  have h := congrArg (Submodule.map rel.mkQ)
    (KaehlerDifferential.span_range_derivation R (↑S))
  simpa only [LinearMap.map_span, ← Set.range_comp, Function.comp_def,
    Submodule.map_top, Submodule.range_mkQ] using h

private theorem dividedPowerDifferentialsLift
    {R : Type*} [CommRing R] {S : DividedPowerRing} [Algebra R S]
    {M : Type*} [AddCommGroup M] [Module (↑S) M]
    (D : Crystalline.DividedPowerDerivation R S (algebraMap R (↑S)) M) :
    ∃! lift : dividedPowerDifferentials (A := R) S.dividedPowers →ₗ[↑S] M,
      ∀ b : ↑S, lift (dividedPowerDifferential (A := R) S.dividedPowers b) = D b := by
  let rel := dividedPowerDifferentialRelations (A := R) S.dividedPowers
  let : Module R M := Module.compHom M (algebraMap R (↑S))
  let : IsScalarTower R (↑S) M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let dA : Derivation R (↑S) M :=
    { toFun := D
      map_add' := D.map_add
      map_smul' := by
        intro a b
        rw [Algebra.smul_def, D.leibniz, D.map_ringHom, smul_zero, add_zero]
        rfl
      map_one_eq_zero' := D.map_one_eq_zero
      leibniz' := D.leibniz }
  let f : Ω[(↑S)⁄R] →ₗ[↑S] M := dA.liftKaehlerDifferential
  have hrel : rel ≤ LinearMap.ker f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨x, n⟩, rfl⟩
    change f (dividedPowerDifferentialRelation (A := R) S.dividedPowers x n) = 0
    simp only [dividedPowerDifferentialRelation, map_sub, map_smul]
    change dA.liftKaehlerDifferential
        (KaehlerDifferential.D R (↑S) (S.dividedPowers.dpow (n + 1) x)) -
      S.dividedPowers.dpow n x • dA.liftKaehlerDifferential
        (KaehlerDifferential.D R (↑S) x) = 0
    rw [dA.liftKaehlerDifferential_comp_D, dA.liftKaehlerDifferential_comp_D]
    change D (S.dividedPowers.dpow (n + 1) x) -
      S.dividedPowers.dpow n x • D x = 0
    rw [D.map_dpow (n + 1) (by omega) x x.property]
    simp
  let lift : dividedPowerDifferentials (A := R) S.dividedPowers →ₗ[↑S] M :=
    rel.liftQ f hrel
  have hlift (b : ↑S) :
      lift (dividedPowerDifferential (A := R) S.dividedPowers b) = D b := by
    change (rel.liftQ f hrel) (rel.mkQ (KaehlerDifferential.D R (↑S) b)) = D b
    rw [← LinearMap.comp_apply, rel.liftQ_mkQ]
    exact dA.liftKaehlerDifferential_comp_D b
  refine ⟨lift, hlift, ?_⟩
  intro g hg
  apply LinearMap.ext_on dividedPowerDifferential_span
  rintro _ ⟨b, rfl⟩
  rw [hg b, hlift b]

private noncomputable def canonicalDividedPowerDerivation
    {R : Type*} [CommRing R] {S : DividedPowerRing} [Algebra R S] :
    Crystalline.DividedPowerDerivation R S (algebraMap R (↑S))
      (dividedPowerDifferentials (A := R) S.dividedPowers) := by
  let rel := dividedPowerDifferentialRelations (A := R) S.dividedPowers
  let dA : Derivation R (↑S) (dividedPowerDifferentials (A := R) S.dividedPowers) :=
    rel.mkQ.compDer (KaehlerDifferential.D R (↑S))
  let dZ : Derivation ℤ (↑S) (dividedPowerDifferentials (A := R) S.dividedPowers) :=
    { toFun := dA
      map_add' := dA.map_add
      map_smul' := map_zsmul dA
      map_one_eq_zero' := dA.map_one_eq_zero
      leibniz' := dA.leibniz }
  refine ⟨dZ, ?_, ?_⟩
  · intro a
    change dA (algebraMap R (↑S) a) = 0
    exact dA.map_algebraMap a
  · intro n hn x hx
    cases n with
    | zero => omega
    | succ n =>
      change rel.mkQ (KaehlerDifferential.D R (↑S)
          (S.dividedPowers.dpow (n + 1) x)) =
        S.dividedPowers.dpow n x •
          rel.mkQ (KaehlerDifferential.D R (↑S) x)
      exact dividedPowerDifferential_dpow (A := R) S.dividedPowers ⟨x, hx⟩ n

-- The coordinate equivalence is assembled from two mutually inverse lifts through universal
-- properties, and the resulting instance towers exceed the default budget.
private noncomputable def dividedPowerDifferentialsCoordinateEquivData
    (A : Type u) [CommRing A] (W : Type w) :
    { e : dividedPowerDifferentials (A := A)
      (setIndexedDividedPowerPolynomialDividedPowerRing
        (coefficientDividedPowerRing A) W).dividedPowers ≃ₗ[
      ↑(setIndexedDividedPowerPolynomialDividedPowerRing
        (coefficientDividedPowerRing A) W)]
        (W →₀ ↑(setIndexedDividedPowerPolynomialDividedPowerRing
          (coefficientDividedPowerRing A) W)) //
      ∀ i : W, e (dividedPowerDifferential (A := A)
        (setIndexedDividedPowerPolynomialDividedPowerRing
          (coefficientDividedPowerRing A) W).dividedPowers
        (dividedPowerPolynomialVariable (coefficientDividedPowerRing A) i)) =
          Finsupp.single i 1 } := by
  classical
  let R := coefficientDividedPowerRing A
  let P := DividedPowerAlgebra (↑R) (W →₀ ↑R)
  letI : CommRing P :=
    (DividedPowerAlgebra.ringCon (↑R) (W →₀ ↑R)).instCommRingQuotient
  let q : ↑R →+* P :=
    (RingCon.mkₐ (↑R) (DividedPowerAlgebra.ringCon (↑R) (W →₀ ↑R))).toRingHom.comp
      (MvPolynomial.C : ↑R →+* MvPolynomial (ℕ × (W →₀ ↑R)) ↑R)
  let c : A →+* ↑R := RingHom.id A
  let qStd : A →+* P := q.comp c
  letI : Algebra A (↑R) := c.toAlgebra
  let S := setIndexedDividedPowerPolynomialDividedPowerRing R W
  let J := S.ideal
  let hJ := S.dividedPowers
  let qS := algebraMap A (↑S)
  letI : Algebra A P := qS.toAlgebra
  letI : Algebra A (↑S) := qS.toAlgebra
  have hAlg : algebraMap A (↑S) = qS := by
    ext a
    rfl
  let M := W →₀ P
  letI : Module P M := indexedDividedPowerPolynomialFinsuppModule (A := A) W
  letI : Module Pᵐᵒᵖ M := indexedDividedPowerPolynomialFinsuppModuleOp (A := A) W
  letI : IsCentralScalar P M := indexedDividedPowerPolynomialFinsuppCentral (A := A) W
  letI : Module P (dividedPowerDifferentials (A := A) hJ) := inferInstance
  let unopRingHom : (↑S)ᵐᵒᵖ →+* ↑S :=
    { toFun := MulOpposite.unop
      map_one' := rfl
      map_mul' := fun x y ↦ (mul_comm x.unop y.unop).symm
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  letI : Module (↑S)ᵐᵒᵖ (dividedPowerDifferentials (A := A) hJ) :=
    Module.compHom _ unopRingHom
  letI : IsCentralScalar (↑S) (dividedPowerDifferentials (A := A) hJ) := ⟨by
    intro c m
    rfl⟩
  let data := polynomialVariableDerivationData (A := A) W
  let D : DividedPowerDerivation A S qS M := Classical.choose data
  have hD := Classical.choose_spec data
  have hDcoeff (a : A) :
      D (setIndexedDividedPowerPolynomialCoefficientDPMorphism
        (coefficientDividedPowerRing A) W a) = 0 := hD.1 a
  have hDvar (i : W) :
      D (dividedPowerPolynomialVariable (coefficientDividedPowerRing A) i) =
        Finsupp.single i 1 := hD.2 i
  let liftData := dividedPowerDifferentialsLift (R := A) (S := S) (M := M) D
  let f := Classical.choose liftData
  have hf (b : P) : f (dividedPowerDifferential (A := A) hJ b) = D b :=
    (Classical.choose_spec liftData).1 b
  let g : M →ₗ[↑S] dividedPowerDifferentials (A := A) hJ :=
    Finsupp.linearCombination (↑S) (fun i ↦
      dividedPowerDifferential (A := A) hJ
        (dividedPowerPolynomialVariable (coefficientDividedPowerRing A) i))
  have hmap (a : A) : setIndexedDividedPowerPolynomialCoefficientDPMorphism
      (coefficientDividedPowerRing A) W a = qS a := by
    change (q.comp (RingHom.id A)) a = qStd a
    rfl
  let E : DividedPowerDerivation A S qS
      (dividedPowerDifferentials (A := A) hJ) :=
    { toDerivation := g.compDer D.toDerivation
      map_ringHom' := by
        intro a
        change g (D (qS a)) = 0
        rw [← hmap, hDcoeff]
        simp
      map_dpow' := by
        intro n hn x hx
        change g (D (S.dividedPowers.dpow n x)) =
          S.dividedPowers.dpow (n - 1) x • g (D x)
        rw [D.map_dpow n hn x hx]
        simp only [map_smul] }
  let C : DividedPowerDerivation A S qS
      (dividedPowerDifferentials (A := A) hJ) :=
    { toDerivation := (canonicalDividedPowerDerivation (R := A) (S := S)).toDerivation
      map_ringHom' := by
        intro a
        rw [← hAlg]
        exact (canonicalDividedPowerDerivation (R := A) (S := S)).map_ringHom a
      map_dpow' := by
        intro n hn x hx
        exact (canonicalDividedPowerDerivation (R := A) (S := S)).map_dpow n hn x hx }
  have hE : E = C := by
    apply setIndexedDividedPowerDerivation_ext W qS E C
    · intro a
      calc
        E (setIndexedDividedPowerPolynomialCoefficientDPMorphism
            (coefficientDividedPowerRing A) W a) = 0 := by
          change g (D (setIndexedDividedPowerPolynomialCoefficientDPMorphism
            (coefficientDividedPowerRing A) W a)) = 0
          rw [hDcoeff]
          simp
        _ = C (setIndexedDividedPowerPolynomialCoefficientDPMorphism
            (coefficientDividedPowerRing A) W a) := by
          change 0 = (canonicalDividedPowerDerivation (R := A) (S := S))
            (setIndexedDividedPowerPolynomialCoefficientDPMorphism
              (coefficientDividedPowerRing A) W a)
          rw [hmap]
          exact ((canonicalDividedPowerDerivation (R := A) (S := S)).map_ringHom a).symm
    · intro i
      change g (D (dividedPowerPolynomialVariable
        (coefficientDividedPowerRing A) i)) =
        C (dividedPowerPolynomialVariable (coefficientDividedPowerRing A) i)
      rw [hDvar i]
      change (Finsupp.linearCombination (↑S) (fun j ↦
        dividedPowerDifferential (A := A) hJ
          (dividedPowerPolynomialVariable (coefficientDividedPowerRing A) j)))
          (Finsupp.single i 1) =
        (canonicalDividedPowerDerivation (R := A) (S := S))
          (dividedPowerPolynomialVariable (coefficientDividedPowerRing A) i)
      rw [Finsupp.linearCombination_single]
      simp [canonicalDividedPowerDerivation, dividedPowerDifferential]
  have hspan : Submodule.span (↑S)
      (Set.range (dividedPowerDifferential (A := A) hJ)) = ⊤ :=
    dividedPowerDifferential_span (R := A) (S := S)
  have hfg : f.comp g = LinearMap.id := by
    apply LinearMap.ext
    intro x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add, hx, hy]; simp
    | single i a =>
      change f ((Finsupp.linearCombination (↑S) (fun j ↦
        dividedPowerDifferential (A := A) hJ
          (dividedPowerPolynomialVariable (coefficientDividedPowerRing A) j)))
          (Finsupp.single i a)) = Finsupp.single i a
      rw [Finsupp.linearCombination_single, map_smul, hf, hDvar]
      exact Finsupp.smul_single_one i a
  have hgf : g.comp f = LinearMap.id := by
    apply LinearMap.ext_on hspan
    rintro _ ⟨b, rfl⟩
    calc
      g (f (dividedPowerDifferential (A := A) hJ b)) = g (D b) := by rw [hf]
      _ = E b := rfl
      _ = C b := by exact congrArg (fun d : DividedPowerDerivation A S qS
          (dividedPowerDifferentials (A := A) hJ) ↦ d b) hE
      _ = dividedPowerDifferential (A := A) hJ b := rfl
  refine ⟨LinearEquiv.ofLinearMap f g hfg hgf, ?_⟩
  intro i
  change f (dividedPowerDifferential (A := A) hJ
    (dividedPowerPolynomialVariable (coefficientDividedPowerRing A) i)) =
      Finsupp.single i 1
  rw [hf, hDvar]

/-- **The coordinate equivalence `Ω¹_{P/A,δ} ≅ (W →₀ P)`**, for `P = A⟨x_w : w ∈ W⟩` the divided
power polynomial algebra on an arbitrary family of variables: the module of divided power
differentials of `P` is free over `P` on the differentials `d x_w` of the variables.  No finiteness
assumption is made on `W`.

The equivalence carries `d x_w` to the `w`-th coordinate vector
(`Crystalline.dividedPowerDifferentialsCoordinateEquiv_apply_variable`), so the `w`-th coordinate
of a differential is its `d x_w`-component; `Crystalline.dividedPowerDifferentialsBasis` is the
same statement packaged as a `Module.Basis` indexed by `W`.

It is assembled from two mutually inverse maps.  Forwards: the universal property of
`Ω¹_{P/A,δ}` factors the divided power derivation `P → (W →₀ P)` with prescribed values
`x_w ↦ e_w`, which exists by the universal property of the divided power polynomial algebra
applied to the square-zero divided power extension `P ⊕ (W →₀ P)`.  Backwards:
`Finsupp.linearCombination` of the family `w ↦ d x_w`.  That the backwards map is a section is a
computation on coordinate vectors; that it is a retraction holds because the differentials span,
and the two composites are compared as divided power derivations out of `P`, which are determined
by their values on the coefficients and the variables.

This is the freeness of `Ω` that the contracting homotopy of the divided power Poincaré lemma is
built on.  It is also the only handle in the library on the `d x_w`-coordinates of a connection,
which is why it is public: see
`StacksFrontier/AlgebraicGeometry/Crystalline/FreeDifferentials07JH.lean`. -/
@[no_expose]
public noncomputable def dividedPowerDifferentialsCoordinateEquiv
    (A : Type u) [CommRing A] (W : Type w) :
    dividedPowerDifferentials (A := A)
      (setIndexedDividedPowerPolynomialDividedPowerRing
        (coefficientDividedPowerRing A) W).dividedPowers ≃ₗ[
      ↑(setIndexedDividedPowerPolynomialDividedPowerRing
        (coefficientDividedPowerRing A) W)]
        (W →₀ ↑(setIndexedDividedPowerPolynomialDividedPowerRing
          (coefficientDividedPowerRing A) W)) :=
  (dividedPowerDifferentialsCoordinateEquivData A W).1

/-- **The coordinate equivalence sends `d x_i` to the `i`-th coordinate vector.**  Together with
`Crystalline.dividedPowerDifferentialsCoordinateEquiv` this is the statement that `Ω¹_{P/A,δ}` is
free *on the differentials of the variables*, and not merely free. -/
public theorem dividedPowerDifferentialsCoordinateEquiv_apply_variable
    (A : Type u) [CommRing A] (W : Type w) (i : W) :
    dividedPowerDifferentialsCoordinateEquiv A W
      (dividedPowerDifferential (A := A)
        (setIndexedDividedPowerPolynomialDividedPowerRing
          (coefficientDividedPowerRing A) W).dividedPowers
        (dividedPowerPolynomialVariable (coefficientDividedPowerRing A) i)) =
      Finsupp.single i 1 :=
  (dividedPowerDifferentialsCoordinateEquivData A W).2 i

/-- **The basis of `Ω¹_{P/A,δ}` given by the differentials of the variables**, for
`P = A⟨x_w : w ∈ W⟩` the divided power polynomial algebra on an arbitrary family of variables.
This is `Crystalline.dividedPowerDifferentialsCoordinateEquiv` read as a `Module.Basis` indexed by
`W`; `Crystalline.dividedPowerDifferentialsBasis_apply` identifies its `i`-th vector with
`d x_i`. -/
@[no_expose]
public noncomputable def dividedPowerDifferentialsBasis (A : Type u) [CommRing A] (W : Type w) :
    Module.Basis W
      ↑(setIndexedDividedPowerPolynomialDividedPowerRing (coefficientDividedPowerRing A) W)
      (dividedPowerDifferentials (A := A)
        (setIndexedDividedPowerPolynomialDividedPowerRing
          (coefficientDividedPowerRing A) W).dividedPowers) :=
  .ofRepr (dividedPowerDifferentialsCoordinateEquiv A W)

/-- **The `i`-th basis vector of `Ω¹_{P/A,δ}` is `d x_i`.** -/
@[simp]
public theorem dividedPowerDifferentialsBasis_apply
    (A : Type u) [CommRing A] (W : Type w) (i : W) :
    dividedPowerDifferentialsBasis A W i =
      dividedPowerDifferential (A := A)
        (setIndexedDividedPowerPolynomialDividedPowerRing
          (coefficientDividedPowerRing A) W).dividedPowers
        (dividedPowerPolynomialVariable (coefficientDividedPowerRing A) i) :=
  (dividedPowerDifferentialsCoordinateEquiv A W).symm_apply_eq.mpr
    (dividedPowerDifferentialsCoordinateEquiv_apply_variable A W i).symm

private theorem dividedPowerPolynomialVariable_mem_ideal
    (A : Type u) [CommRing A] (W : Type w) (i : W) :
    dividedPowerPolynomialVariable (coefficientDividedPowerRing A) i ∈
      (setIndexedDividedPowerPolynomialDividedPowerRing
        (coefficientDividedPowerRing A) W).ideal := by
  apply Ideal.mem_sup_right
  apply RingHom.mem_ker.mpr
  simpa [dividedPowerPolynomialAugmentation, dividedPowerPolynomialVariable] using
    (dividedPowersBot ↑(coefficientDividedPowerRing A)).dpow_one (Ideal.zero_mem ⊥)

private theorem derivation_prod
    {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [DecidableEq ι]
    (D : Derivation ℤ R M) (s : Finset ι) (f : ι → R) :
    D (∏ i ∈ s, f i) =
      ∑ i ∈ s, (∏ j ∈ s.erase i, f j) • D (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, D.leibniz, ih, Finset.sum_insert ha]
    simp only [Finset.erase_insert ha]
    rw [Finset.smul_sum]
    conv_lhs => rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hia : i ≠ a := fun h => ha (h ▸ hi)
    rw [Finset.erase_insert_of_ne (Ne.symm hia), Finset.prod_insert]
    · rw [mul_smul]
    · simp [ha]

private theorem dividedPowerDerivation_variableMonomial
    (A : Type u) [CommRing A] (W : Type w)
    {M : Type*} [AddCommGroup M]
    [Module (↑(setIndexedDividedPowerPolynomialDividedPowerRing
      (coefficientDividedPowerRing A) W)) M]
    (D : DividedPowerDerivation A
      (setIndexedDividedPowerPolynomialDividedPowerRing
        (coefficientDividedPowerRing A) W)
      (algebraMap A (↑(setIndexedDividedPowerPolynomialDividedPowerRing
        (coefficientDividedPowerRing A) W))) M)
    (i : W) (n : ℕ) :
    let S := setIndexedDividedPowerPolynomialDividedPowerRing
      (coefficientDividedPowerRing A) W
    D (dividedPowerPolynomialVariableMonomial
      (coefficientDividedPowerRing A) i (n + 1)) =
    S.dividedPowers.dpow n (⟨dividedPowerPolynomialVariable
      (coefficientDividedPowerRing A) i,
      dividedPowerPolynomialVariable_mem_ideal A W i⟩ : S.ideal) •
      D (dividedPowerPolynomialVariable (coefficientDividedPowerRing A) i) := by
  intro S
  let x : S.ideal := ⟨dividedPowerPolynomialVariable
    (coefficientDividedPowerRing A) i,
    dividedPowerPolynomialVariable_mem_ideal A W i⟩
  rw [← setIndexedDividedPowerPolynomialDividedPowers_dpow_variable
    (coefficientDividedPowerRing A) i (n + 1)]
  convert D.map_dpow (n + 1) (Nat.succ_pos n) x x.property using 1 <;>
    simp [x, S, setIndexedDividedPowerPolynomialDividedPowerRing]

private theorem dividedPowerDerivation_monomial
    (A : Type u) [CommRing A] (W : Type w) [DecidableEq W]
    {M : Type*} [AddCommGroup M]
    [Module (↑(setIndexedDividedPowerPolynomialDividedPowerRing
      (coefficientDividedPowerRing A) W)) M]
    (D : DividedPowerDerivation A
      (setIndexedDividedPowerPolynomialDividedPowerRing
        (coefficientDividedPowerRing A) W)
      (algebraMap A (↑(setIndexedDividedPowerPolynomialDividedPowerRing
        (coefficientDividedPowerRing A) W))) M)
    (K : W →₀ ℕ) :
    let S := setIndexedDividedPowerPolynomialDividedPowerRing
      (coefficientDividedPowerRing A) W
    D (dividedPowerPolynomialMonomial (coefficientDividedPowerRing A) K) =
      ∑ i ∈ K.support,
        ((∏ j ∈ K.support.erase i,
          dividedPowerPolynomialVariableMonomial (coefficientDividedPowerRing A) j (K j)) :
            ↑S) •
          D (dividedPowerPolynomialVariableMonomial
            (coefficientDividedPowerRing A) i (K i)) := by
  intro S
  classical
  change (D.toDerivation)
    (∏ i ∈ K.support,
      dividedPowerPolynomialVariableMonomial (coefficientDividedPowerRing A) i (K i)) =
    ∑ i ∈ K.support,
      ((∏ j ∈ K.support.erase i,
        dividedPowerPolynomialVariableMonomial (coefficientDividedPowerRing A) j (K j)) : ↑S) •
        D.toDerivation (dividedPowerPolynomialVariableMonomial
          (coefficientDividedPowerRing A) i (K i))
  exact derivation_prod D.toDerivation K.support
    (fun i => dividedPowerPolynomialVariableMonomial (coefficientDividedPowerRing A) i (K i))

private theorem dividedPowerDifferential_monomial
    (A : Type u) [CommRing A] (W : Type w) [DecidableEq W] (K : W →₀ ℕ) :
    let S := setIndexedDividedPowerPolynomialDividedPowerRing
      (coefficientDividedPowerRing A) W
    dividedPowerDifferential (A := A) S.dividedPowers
      (dividedPowerPolynomialMonomial (coefficientDividedPowerRing A) K) =
      ∑ i ∈ K.support,
        ((∏ j ∈ K.support.erase i,
          dividedPowerPolynomialVariableMonomial (coefficientDividedPowerRing A) j (K j)) :
            ↑S) •
          dividedPowerDifferential (A := A) S.dividedPowers
            (dividedPowerPolynomialVariableMonomial
              (coefficientDividedPowerRing A) i (K i)) := by
  intro S
  let : Algebra A (↑S) := (indexedDividedPowerPolynomialCoefficientMap A W).toAlgebra
  change (canonicalDividedPowerDerivation (R := A) (S := S))
      (dividedPowerPolynomialMonomial (coefficientDividedPowerRing A) K) =
    ∑ i ∈ K.support,
      ((∏ j ∈ K.support.erase i,
        dividedPowerPolynomialVariableMonomial (coefficientDividedPowerRing A) j (K j)) :
          ↑S) •
        (canonicalDividedPowerDerivation (R := A) (S := S))
          (dividedPowerPolynomialVariableMonomial
            (coefficientDividedPowerRing A) i (K i))
  exact dividedPowerDerivation_monomial A W
    (canonicalDividedPowerDerivation (R := A) (S := S)) K

private theorem dividedPowerDifferential_variableMonomial
    (A : Type u) [CommRing A] (W : Type w) (i : W) (n : ℕ) :
    let S := setIndexedDividedPowerPolynomialDividedPowerRing
      (coefficientDividedPowerRing A) W
    let x : S.ideal := ⟨dividedPowerPolynomialVariable
      (coefficientDividedPowerRing A) i,
      dividedPowerPolynomialVariable_mem_ideal A W i⟩
    dividedPowerDifferential (A := A) S.dividedPowers
      (dividedPowerPolynomialVariableMonomial
        (coefficientDividedPowerRing A) i (n + 1)) =
      S.dividedPowers.dpow n x •
        dividedPowerDifferential (A := A) S.dividedPowers x := by
  intro S x
  rw [← setIndexedDividedPowerPolynomialDividedPowers_dpow_variable
    (coefficientDividedPowerRing A) i (n + 1)]
  convert dividedPowerDifferential_dpow (A := A) S.dividedPowers x n using 1
  simp [x, S, setIndexedDividedPowerPolynomialDividedPowerRing]

private theorem dividedPowerPolynomialMonomial_erase_add_single
    (A : Type u) [CommRing A] {W : Type w} (K : W →₀ ℕ) (i : W) (n : ℕ) :
    dividedPowerPolynomialMonomial A (K.erase i + Finsupp.single i n) =
      dividedPowerPolynomialMonomial A (K.erase i) *
        dividedPowerPolynomialVariableMonomial A i n := by
  classical
  have hd : Disjoint (K.erase i).support (Finsupp.single i n).support := by
    refine Finset.disjoint_left.mpr fun a ha hna => ?_
    rw [Finsupp.support_erase, Finset.mem_erase] at ha
    rw [Finsupp.mem_support_iff, Finsupp.single_apply_ne_zero] at hna
    exact ha.1 hna.1
  unfold dividedPowerPolynomialMonomial dividedPowerPolynomialVariableMonomial
  rw [Finsupp.prod_add_index_of_disjoint hd,
    Finsupp.prod_single_index (by simp [DividedPowerAlgebra.dp_zero])]

private theorem dividedPowerDifferential_monomial_shift
    (A : Type u) [CommRing A] (W : Type w) (K : W →₀ ℕ) :
    let S := setIndexedDividedPowerPolynomialDividedPowerRing
      (coefficientDividedPowerRing A) W
    dividedPowerDifferential (A := A) S.dividedPowers
      (dividedPowerPolynomialMonomial (coefficientDividedPowerRing A) K) =
      ∑ i ∈ K.support,
        (dividedPowerPolynomialMonomial (coefficientDividedPowerRing A)
          (K.erase i + Finsupp.single i (K i - 1)) : ↑S) •
          dividedPowerDifferential (A := A) S.dividedPowers
            (dividedPowerPolynomialVariable (coefficientDividedPowerRing A) i) := by
  intro S
  classical
  rw [dividedPowerDifferential_monomial]
  apply Finset.sum_congr rfl
  intro i hi
  have hKi : 0 < K i := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
  have heq : K i - 1 + 1 = K i := Nat.sub_add_cancel hKi
  conv_lhs => rhs; rw [← heq]
  rw [dividedPowerDifferential_variableMonomial A W i (K i - 1)]
  rw [smul_smul]
  have hdp : S.dividedPowers.dpow (K i - 1)
      (⟨dividedPowerPolynomialVariable (coefficientDividedPowerRing A) i,
        dividedPowerPolynomialVariable_mem_ideal A W i⟩ : S.ideal) =
      dividedPowerPolynomialVariableMonomial (coefficientDividedPowerRing A) i
        (K i - 1) := by
    simpa [S, setIndexedDividedPowerPolynomialDividedPowerRing] using
      setIndexedDividedPowerPolynomialDividedPowers_dpow_variable
        (coefficientDividedPowerRing A) i (K i - 1)
  rw [hdp]
  congr 1
  have hprod :
      (K.erase i).prod (fun j m => DividedPowerAlgebra.dp
        (↑(coefficientDividedPowerRing A)) m (Finsupp.single j 1)) =
      ∏ j ∈ K.support.erase i,
        dividedPowerPolynomialVariableMonomial (coefficientDividedPowerRing A) j (K j) := by
    rw [Finsupp.prod, Finsupp.support_erase]
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [dividedPowerPolynomialVariableMonomial, Finsupp.erase_ne hji]
  rw [← hprod]
  exact (dividedPowerPolynomialMonomial_erase_add_single
    (↑(coefficientDividedPowerRing A)) K i (K i - 1)).symm

private theorem dividedPowerDifferentialsCoordinateEquiv_apply_dpow_variable
    (A : Type u) [CommRing A] (W : Type w) (i : W) (n : ℕ) :
    let S := setIndexedDividedPowerPolynomialDividedPowerRing
      (coefficientDividedPowerRing A) W
    let x : S.ideal := ⟨dividedPowerPolynomialVariable
      (coefficientDividedPowerRing A) i,
      dividedPowerPolynomialVariable_mem_ideal A W i⟩
    dividedPowerDifferentialsCoordinateEquiv A W
      (dividedPowerDifferential (A := A) S.dividedPowers
        (S.dividedPowers.dpow (n + 1) x)) =
      Finsupp.single i (S.dividedPowers.dpow n x) := by
  intro S x
  rw [dividedPowerDifferential_dpow (A := A) S.dividedPowers x n,
    map_smul, dividedPowerDifferentialsCoordinateEquiv_apply_variable,
    Finsupp.smul_single_one]

-- The exterior power of the coordinate basis is transported across `RestrictScalars` synonyms.
private noncomputable def dividedPowerDifferentialFormsBasis
    (A : Type u) [CommRing A] (W : Type w) (n : ℕ) :
    Module.Basis (Set.powersetCard W n)
      (↑(setIndexedDividedPowerPolynomialDividedPowerRing
        (coefficientDividedPowerRing A) W))
      (dividedPowerDifferentialForms (A := A)
        (B := ↑(setIndexedDividedPowerPolynomialDividedPowerRing
          (coefficientDividedPowerRing A) W))
        (setIndexedDividedPowerPolynomialDividedPowerRing
          (coefficientDividedPowerRing A) W).dividedPowers n) := by
  classical
  let S := setIndexedDividedPowerPolynomialDividedPowerRing
    (coefficientDividedPowerRing A) W
  let P : Type (max u w) := ↑S
  let Ω := dividedPowerDifferentials (A := A) S.dividedPowers
  letI : LinearOrder W := linearOrderOfSTO WellOrderingRel
  let coord := dividedPowerDifferentialsCoordinateEquiv A W
  let e : Ω ≃ₗ[P] (W →₀ P) := coord
  let bFinsupp : Module.Basis W P (W →₀ P) :=
    Finsupp.basisSingleOne (R := P) (ι := W)
  let bΩ : Module.Basis W P Ω := bFinsupp.map e.symm
  exact bΩ.exteriorPower n

private theorem dividedPowerDifferentialFormsBasis_apply
    (A : Type u) [CommRing A] (W : Type w) (n : ℕ)
    (I : Set.powersetCard W n) :
    let S := setIndexedDividedPowerPolynomialDividedPowerRing
      (coefficientDividedPowerRing A) W
    letI : DecidableRel (WellOrderingRel (α := W)) := Classical.decRel _
    letI : LinearOrder W := linearOrderOfSTO (WellOrderingRel (α := W))
    dividedPowerDifferentialFormsBasis A W n I =
      exteriorPower.ιMulti_family (↑S) n
        (fun i : W => dividedPowerDifferential (A := A) S.dividedPowers
          (dividedPowerPolynomialVariable (coefficientDividedPowerRing A) i)) I := by
  intro S
  classical
  let : LinearOrder W := linearOrderOfSTO WellOrderingRel
  unfold dividedPowerDifferentialFormsBasis
  rw [exteriorPower.basis_apply]
  unfold exteriorPower.ιMulti_family
  congr 1
  funext j
  change (dividedPowerDifferentialsCoordinateEquiv A W).symm
    (Finsupp.single (Set.powersetCard.ofFinEmbEquiv.symm I j) 1) =
      dividedPowerDifferential (A := A) S.dividedPowers
        (dividedPowerPolynomialVariable (coefficientDividedPowerRing A)
          (Set.powersetCard.ofFinEmbEquiv.symm I j))
  rw [← dividedPowerDifferentialsCoordinateEquiv_apply_variable A W
    (Set.powersetCard.ofFinEmbEquiv.symm I j)]
  exact LinearEquiv.symm_apply_apply _ _

-- As above, with the extra tower turning the `P`-basis of forms into an `A`-basis.
private noncomputable def dividedPowerDifferentialFormsABasis
    (A : Type u) [CommRing A] (W : Type w) (n : ℕ) :
    Module.Basis ((W →₀ ℕ) × Set.powersetCard W n) A
      (dividedPowerDifferentialForms (A := A)
        (B := ↑(setIndexedDividedPowerPolynomialDividedPowerRing
          (coefficientDividedPowerRing A) W))
        (setIndexedDividedPowerPolynomialDividedPowerRing
          (coefficientDividedPowerRing A) W).dividedPowers n) := by
  classical
  let S := setIndexedDividedPowerPolynomialDividedPowerRing
    (coefficientDividedPowerRing A) W
  letI : Algebra A (↑S) := indexedDividedPowerPolynomialCoefficientMap A W |>.toAlgebra
  letI : Module A (dividedPowerDifferentialForms (A := A) S.dividedPowers n) :=
    Module.compHom _ (algebraMap A (↑S))
  letI : IsScalarTower A (↑S)
      (dividedPowerDifferentialForms (A := A) S.dividedPowers n) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  letI : IsScalarTower A (DividedPowerAlgebra A (W →₀ A))
      (dividedPowerDifferentialForms (A := A) S.dividedPowers n) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  exact (DividedPowers.dividedPowerPolynomialMonomialBasis A W).smulTower
    (dividedPowerDifferentialFormsBasis A W n)

private theorem dividedPowerDifferentialFormsABasis_apply
    (A : Type u) [CommRing A] (W : Type w) (n : ℕ)
    (K : W →₀ ℕ) (I : Set.powersetCard W n) :
    dividedPowerDifferentialFormsABasis A W n (K, I) =
    dividedPowerPolynomialMonomial A K •
        dividedPowerDifferentialFormsBasis A W n I := by
  classical
  let S := setIndexedDividedPowerPolynomialDividedPowerRing
    (coefficientDividedPowerRing A) W
  let : Algebra A (↑S) := indexedDividedPowerPolynomialCoefficientMap A W |>.toAlgebra
  let : Module A (dividedPowerDifferentialForms (A := A) S.dividedPowers n) :=
    Module.compHom _ (algebraMap A (↑S))
  let : IsScalarTower A (↑S)
      (dividedPowerDifferentialForms (A := A) S.dividedPowers n) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let : IsScalarTower A (DividedPowerAlgebra A (W →₀ A))
      (dividedPowerDifferentialForms (A := A) S.dividedPowers n) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  unfold dividedPowerDifferentialFormsABasis
  rw [Module.Basis.smulTower_apply, dividedPowerPolynomialMonomialBasis_apply]

private theorem dividedPowerDifferentialFormsABasis_apply_monomial
    (A : Type u) [CommRing A] (W : Type w) (n : ℕ)
    (K : W →₀ ℕ) (I : Set.powersetCard W n) :
    let S := setIndexedDividedPowerPolynomialDividedPowerRing
      (coefficientDividedPowerRing A) W
    letI : DecidableRel (WellOrderingRel (α := W)) := Classical.decRel _
    letI : LinearOrder W := linearOrderOfSTO (WellOrderingRel (α := W))
    dividedPowerDifferentialFormsABasis A W n (K, I) =
      dividedPowerPolynomialMonomial A K •
        exteriorPower.ιMulti_family (↑S) n
          (fun i : W => dividedPowerDifferential (A := A) S.dividedPowers
            (dividedPowerPolynomialVariable (coefficientDividedPowerRing A) i)) I := by
  intro S
  classical
  let : LinearOrder W := linearOrderOfSTO WellOrderingRel
  rw [dividedPowerDifferentialFormsABasis_apply,
    dividedPowerDifferentialFormsBasis_apply]

private theorem dividedPowerPolynomialMonomial_zero
    (A : Type u) [CommRing A] (W : Type w) :
    dividedPowerPolynomialMonomial A (0 : W →₀ ℕ) = 1 := by
  simp [dividedPowerPolynomialMonomial]

private theorem dividedPowerPolynomialMonomial_single
    (A : Type u) [CommRing A] {W : Type w} (i : W) (n : ℕ) :
    dividedPowerPolynomialMonomial A (Finsupp.single i n) =
      dividedPowerPolynomialVariableMonomial A i n := by
  unfold dividedPowerPolynomialMonomial dividedPowerPolynomialVariableMonomial
  rw [Finsupp.prod_single_index (by simp [DividedPowerAlgebra.dp_zero])]

open scoped ExteriorAlgebra
open Module

private noncomputable def exteriorWedgeLeft
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (e : M) (n : ℕ) : (⋀[R]^n M) →ₗ[R] (⋀[R]^(n + 1) M) :=
  ((LinearMap.mulLeft R (ExteriorAlgebra.ι R e)).comp (⋀[R]^n M).subtype).codRestrict
    (⋀[R]^(n + 1) M) (fun x => by
      change ExteriorAlgebra.ι R e * (x : ExteriorAlgebra R M) ∈ ⋀[R]^(n + 1) M
      have := ExteriorAlgebra.gradedAlgebra R M
      convert SetLike.mul_mem_graded (Koszul.ι_mem_one e) x.property using 1
      congr 1
      omega
)

private theorem exteriorWedgeLeft_contract
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (φ : Module.Dual R M) (e : M) (he : φ e = 1) (n : ℕ)
    (x : ⋀[R]^(n + 1) M) :
    Koszul.d φ (n + 1) (exteriorWedgeLeft e (n + 1) x) +
      exteriorWedgeLeft e n (Koszul.d φ n x) = x := by
  apply Subtype.ext
  change Koszul.contraction φ (ExteriorAlgebra.ι R e * (x : ExteriorAlgebra R M)) +
    ExteriorAlgebra.ι R e * Koszul.contraction φ (x : ExteriorAlgebra R M) = x
  simpa only [he, one_smul] using (koszul_scalar_eq_homotopy φ e x).symm

private noncomputable def finsetMultiIndex {I : Type*} (s : Finset I) : I →₀ ℕ :=
  ∑ i ∈ s, Finsupp.single i 1

private theorem finsetMultiIndex_apply {I : Type*} [DecidableEq I] (s : Finset I) (i : I) :
    finsetMultiIndex s i = if i ∈ s then 1 else 0 := by
  classical
  simp [finsetMultiIndex, Finset.sum_apply, Finsupp.single_apply]

private theorem finsetMultiIndex_le_iff {I : Type*} (s : Finset I) (K : I →₀ ℕ) :
    finsetMultiIndex s ≤ K ↔ s ⊆ K.support := by
  classical
  constructor
  · intro h i hi
    have := h i
    rw [finsetMultiIndex_apply, ite_eq_left hi] at this
    exact Finsupp.mem_support_iff.mpr (by omega)
  · intro h i
    rw [finsetMultiIndex_apply]
    split_ifs with hi
    · have := Finsupp.mem_support_iff.mp (h hi)
      omega
    · exact Nat.zero_le _

private theorem finsetMultiIndex_insert {I : Type*} [DecidableEq I]
    (s : Finset I) (i : I) (hi : i ∉ s) :
    finsetMultiIndex (insert i s) = Finsupp.single i 1 + finsetMultiIndex s := by
  simp [finsetMultiIndex, Finset.sum_insert hi]

private theorem finsetMultiIndex_sub_add {I : Type*} (s : Finset I) (K : I →₀ ℕ)
    (h : s ⊆ K.support) :
    K - finsetMultiIndex s + finsetMultiIndex s = K :=
  tsub_add_cancel_of_le ((finsetMultiIndex_le_iff s K).mpr h)

private theorem subset_support_add_finsetMultiIndex {I : Type*} (s : Finset I)
    (K : I →₀ ℕ) : s ⊆ (K + finsetMultiIndex s).support := by
  rw [← finsetMultiIndex_le_iff]
  exact le_add_self

private theorem dividedPowerDeRhamDifferential_monomial
    (n : ℕ) (K : W →₀ ℕ) (v : Fin n → W) :
    let S := setIndexedDividedPowerPolynomialDividedPowerRing
      (coefficientDividedPowerRing A) W
    let dx := fun i : W => dividedPowerDifferential (A := A) S.dividedPowers
      (dividedPowerPolynomialVariable (coefficientDividedPowerRing A) i)
    (dividedPowerDeRhamComplex (A := A) S.dividedPowers).differential n
      ((dividedPowerPolynomialMonomial A K : ↑S) • exteriorPower.ιMulti (↑S) n (dx ∘ v)) =
      ∑ i ∈ K.support,
        (dividedPowerPolynomialMonomial A (K.erase i + Finsupp.single i (K i - 1)) : ↑S) •
          exteriorPower.ιMulti (↑S) (n + 1) (Fin.cons (dx i) (dx ∘ v)) := by
  classical
  intro S dx
  have hg := (dividedPowerDeRhamComplex (A := A) S.dividedPowers).differential_generator n
    (Fin.cons (dividedPowerPolynomialMonomial A K)
      (fun j => dividedPowerPolynomialVariable (coefficientDividedPowerRing A) (v j)))
  simp only [Fin.cons_zero, Fin.cons_succ] at hg
  refine hg.trans ?_
  have hc : (fun j : Fin (n + 1) => dividedPowerDifferential (A := A) S.dividedPowers
      (Fin.cons (α := fun _ => ↑S) (dividedPowerPolynomialMonomial A K : ↑S)
        (fun j : Fin n =>
          (dividedPowerPolynomialVariable (coefficientDividedPowerRing A) (v j) : ↑S)) j)) =
      Fin.cons (dividedPowerDifferential (A := A) S.dividedPowers
        (dividedPowerPolynomialMonomial A K)) (dx ∘ v) := by
    ext j
    refine Fin.cases ?_ (fun j => ?_) j <;> rfl
  have hs : dividedPowerDifferential (A := A) S.dividedPowers
      (dividedPowerPolynomialMonomial A K) =
      ∑ i ∈ K.support,
        (dividedPowerPolynomialMonomial A (K.erase i + Finsupp.single i (K i - 1)) : ↑S) •
          dx i := dividedPowerDifferential_monomial_shift A W K
  rw [hc, hs]
  apply Subtype.ext
  simp only [exteriorPower.ιMulti_apply_coe, Submodule.coe_sum, Submodule.coe_smul_of_tower,
    ExteriorAlgebra.ιMulti_succ_apply, Fin.cons_zero, Matrix.vecTail, map_sum,
    map_smul, Finset.sum_mul, smul_mul_assoc]
  rfl

end OrdinaryExactness

end Crystalline

end
