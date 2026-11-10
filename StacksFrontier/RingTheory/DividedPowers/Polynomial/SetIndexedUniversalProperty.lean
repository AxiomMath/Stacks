module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.Polynomial.SetIndexed

/-!
# Universal property of a set-indexed divided power polynomial algebra

Let `(A, I, γ)` be a divided power ring, `W` an arbitrary type of variables and `(C, J, δ)` a
divided power ring. A divided power morphism out of `A⟨x_w : w ∈ W⟩`, for the divided power
structure `DividedPowers.setIndexedDividedPowerPolynomialDividedPowers`, is determined by its
restriction to the coefficients and by the images of the variables, and every choice of a divided
power morphism `A → C` together with a family of elements of `J` indexed by `W` arises in this
way from exactly one morphism.

## Main results

* `DividedPowers.existsUnique_dPMorphism_from_setIndexedDividedPowerPolynomial` — the universal
  property of `A⟨x_w : w ∈ W⟩` for an arbitrary type `W` of variables.

## Implementation notes

The extension is not assembled stage by stage. The underlying algebra map is produced in one
step, as the divided power algebra lift of the linear map `(W →₀ A) → C` determined by the chosen
family, and the work is to see that it is a divided power morphism. For that the distinguished
ideal is written as the span of the images of the divided power ideals of all the finite stages,
and the two conditions of `DividedPowers.IsDPMorphism.on_span` are checked on such an image by
comparing the lift with the morphism that the finite-variable universal property produces on that
stage; the two agree because they agree on the divided power monomial basis of the stage.

Uniqueness is likewise reduced to a stage: any two morphisms agreeing on coefficients and on
variables restrict, along a finite-stage inclusion, to two morphisms out of the stage agreeing on
its coefficients and variables, hence are equal there by the finite-variable uniqueness, and every
element of the set-indexed algebra lies in some stage.

## References

* [Stacks Project, Tag 07H6](https://stacks.math.columbia.edu/tag/07H6)
-/

@[expose] public section

noncomputable section

namespace DividedPowers

universe u v w

/-- An element of the set-indexed divided power polynomial algebra that comes from the divided
power ideal of some finite stage. -/
private def finiteStageIdealImage {A : DividedPowerRing.{u}} {W : Type w}
    (x : setIndexedDividedPowerPolynomialAlgebra A W) : Prop :=
  ∃ (E : Finset W) (y : DividedPowerAlgebra A (E →₀ A)),
    y ∈ dividedPowerPolynomialIdeal A.ideal E ∧ finiteStageInclusion A E y = x

/-- The distinguished ideal of the set-indexed algebra is spanned by the images of the
distinguished ideals of the finite stages. -/
private theorem finiteStageIdealImage_span (A : DividedPowerRing.{u}) (W : Type w) :
    Ideal.span {x : setIndexedDividedPowerPolynomialAlgebra A W | finiteStageIdealImage x} =
      dividedPowerPolynomialIdeal A.ideal W := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro x ⟨E, y, hy, rfl⟩
    exact (finiteStageInclusion_isDPMorphism A E).ideal_comp
      (Ideal.mem_map_of_mem _ hy)
  · rw [dividedPowerPolynomialIdeal]
    apply sup_le
    · rw [Ideal.map_le_iff_le_comap (f := algebraMap A
        (setIndexedDividedPowerPolynomialAlgebra A W))]
      intro a ha
      apply Ideal.subset_span
      refine ⟨∅, algebraMap A (DividedPowerAlgebra A ((∅ : Finset W) →₀ A)) a, ?_, ?_⟩
      · change _ ∈ Ideal.map (algebraMap A
          (DividedPowerAlgebra A ((∅ : Finset W) →₀ A))) A.ideal ⊔ _
        exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha)
      · simp [finiteStageInclusion]
    · intro x hx
      obtain ⟨E, y, rfl⟩ := exists_finiteStage_lift A W x
      have hcomp := congrArg (fun g : DividedPowerAlgebra A (E →₀ A) →ₐ[A] A => g y)
        (dividedPowerPolynomialAugmentation_comp_finiteStageInclusion A E)
      have hy : y ∈ RingHom.ker (dividedPowerPolynomialAugmentation A E).toRingHom := by
        apply RingHom.mem_ker.mpr
        have hzero : (dividedPowerPolynomialAugmentation A W)
            (finiteStageInclusion A E y) = 0 := RingHom.mem_ker.mp hx
        change (dividedPowerPolynomialAugmentation A W)
            (finiteStageInclusion A E y) =
          (dividedPowerPolynomialAugmentation A E) y at hcomp
        rw [hzero] at hcomp
        exact hcomp.symm
      apply Ideal.subset_span
      refine ⟨E, y, ?_, rfl⟩
      change y ∈ Ideal.map (algebraMap A (DividedPowerAlgebra A (E →₀ A)))
        A.ideal ⊔ RingHom.ker (dividedPowerPolynomialAugmentation A E).toRingHom
      exact Ideal.mem_sup_right hy

/-- The universal property of a divided power polynomial algebra on an arbitrary type
of variables: a coefficient morphism and arbitrary images in the target ideal admit
exactly one extension as a divided power morphism. -/
@[stacks 07H6 "set_indexed_universal_property"]
public theorem existsUnique_dPMorphism_from_setIndexedDividedPowerPolynomial
    (A : DividedPowerRing.{u}) (W : Type w) (C : DividedPowerRing.{v})
    (f : _root_.DividedPowers.DPMorphism A.dividedPowers C.dividedPowers)
    (k : W → C.ideal) :
    ∃! φ : _root_.DividedPowers.DPMorphism
      (setIndexedDividedPowerPolynomialDividedPowers A W) C.dividedPowers,
      (φ.comp (setIndexedDividedPowerPolynomialCoefficientDPMorphism A W) = f ∧
        ∀ i : W, φ (dividedPowerPolynomialVariable A i) = (k i : C)) := by
  classical
  let _ : Algebra A C := f.toRingHom.toAlgebra
  let g : (W →₀ A) →ₗ[A] C := Finsupp.linearCombination A fun i => (k i : C)
  have hg : ∀ x, g x ∈ C.ideal := by
    intro x
    change (Finsupp.linearCombination A fun i => (k i : C)) x ∈ C.ideal
    rw [Finsupp.linearCombination_apply]
    apply C.ideal.sum_mem
    intro i hi
    change algebraMap A C (x i) * (k i : C) ∈ C.ideal
    exact C.ideal.mul_mem_left _ (k i).property
  let gAlg : DividedPowerAlgebra A (W →₀ A) →ₐ[A] C :=
    DividedPowerAlgebra.lift C.dividedPowers g hg
  have hstage (E : Finset W) :
      ∃ ψ : _root_.DividedPowers.DPMorphism (dividedPowerPolynomialDividedPowers A E)
          C.dividedPowers, ∀ y, gAlg.toRingHom (finiteStageInclusion A E y) = ψ y := by
    obtain ⟨ψ, hψ, -⟩ :=
      existsUnique_dPMorphism_from_dividedPowerPolynomial A E C f (fun i => k i.1)
    let ψA : DividedPowerAlgebra A (E →₀ A) →ₐ[A] C :=
      { toRingHom := ψ.toRingHom
        commutes' := fun a ↦ congrArg (fun q : _root_.DividedPowers.DPMorphism A.dividedPowers
          C.dividedPowers => q.toRingHom a) hψ.1 }
    refine ⟨ψ, fun y => DFunLike.congr_fun (?_ : gAlg.comp (finiteStageInclusion A E) = ψA) y⟩
    apply AlgHom.toLinearMap_injective
    apply (dividedPowerPolynomialMonomialBasis A E).ext
    intro n
    simp only [dividedPowerPolynomialMonomialBasis_apply,
      AlgHom.toLinearMap_apply, AlgHom.comp_apply]
    change gAlg (finiteStageInclusion A E
        (dividedPowerPolynomialMonomial A n)) =
      ψA (dividedPowerPolynomialMonomial A n)
    simp only [dividedPowerPolynomialMonomial, Finsupp.prod, map_prod]
    apply Finset.prod_congr rfl
    intro i hi
    change gAlg (finiteStageInclusion A E
        (dividedPowerPolynomialVariableMonomial A i (n i))) =
      ψ (dividedPowerPolynomialVariableMonomial A i (n i))
    rw [finiteStageInclusion_dp]
    calc
      gAlg (dividedPowerPolynomialVariableMonomial A (i : W) (n i)) =
          C.dividedPowers.dpow (n i) (k i.1 : C) := by
            simp only [dividedPowerPolynomialVariableMonomial, gAlg,
              DividedPowerAlgebra.lift_apply_dp]
            change C.dividedPowers.dpow (n i)
              ((Finsupp.linearCombination A fun j => (k j : C))
                (Finsupp.single (i : W) 1)) = _
            rw [Finsupp.linearCombination_single]
            simp
      _ = ψ (dividedPowerPolynomialVariableMonomial A i (n i)) := by
            have hvarmem : dividedPowerPolynomialVariable A i ∈
                dividedPowerPolynomialIdeal A.ideal E :=
              variable_mem_polynomialIdeal (ι := (E : Type w)) A i
            rw [← hψ.2 i]
            have hdp := ψ.dpow_comp (n := n i)
              (dividedPowerPolynomialVariable A i) hvarmem
            change C.dividedPowers.dpow (n i)
                (ψ.toRingHom (dividedPowerPolynomialVariable A i)) =
              ψ.toRingHom (dividedPowerPolynomialVariableMonomial A i (n i))
            rw [hdp, dividedPowerPolynomialDividedPowers_dpow_variable]
  have hdp : _root_.DividedPowers.IsDPMorphism
      (setIndexedDividedPowerPolynomialDividedPowers A W) C.dividedPowers
      gAlg.toRingHom := by
    apply _root_.DividedPowers.IsDPMorphism.on_span
      (hS := (finiteStageIdealImage_span A W).symm)
    · rintro x ⟨E, y, hy, rfl⟩
      obtain ⟨ψ, hψ⟩ := hstage E
      exact (hψ y).symm ▸ ψ.ideal_comp (Ideal.mem_map_of_mem _ hy)
    · intro n x hx
      obtain ⟨E, y, hy, rfl⟩ := hx
      obtain ⟨ψ, hψ⟩ := hstage E
      have hincl' :
          (setIndexedDividedPowerPolynomialDividedPowers A W).dpow n
              (finiteStageInclusion A E y) =
            finiteStageInclusion A E ((dividedPowerPolynomialDividedPowers A E).dpow n y) := by
        simpa using (finiteStageInclusion_isDPMorphism A E).dpow_comp (n := n) y hy
      calc
        gAlg.toRingHom ((setIndexedDividedPowerPolynomialDividedPowers A W).dpow n
            (finiteStageInclusion A E y)) =
            gAlg.toRingHom (finiteStageInclusion A E
              ((dividedPowerPolynomialDividedPowers A E).dpow n y)) := by
                rw [hincl']
        _ = ψ ((dividedPowerPolynomialDividedPowers A E).dpow n y) := hψ _
        _ = C.dividedPowers.dpow n (ψ y) := (ψ.dpow_comp y hy).symm
        _ = C.dividedPowers.dpow n (gAlg.toRingHom (finiteStageInclusion A E y)) := by
              rw [hψ y]
  let φ := _root_.DividedPowers.DPMorphism.mk' hdp
  have hcoeff :
      φ.comp (setIndexedDividedPowerPolynomialCoefficientDPMorphism A W) = f := by
    ext a
    change gAlg (algebraMap A (setIndexedDividedPowerPolynomialAlgebra A W) a) = f a
    calc
      gAlg (algebraMap A (setIndexedDividedPowerPolynomialAlgebra A W) a) =
          algebraMap A C a := gAlg.commutes a
      _ = f a := rfl
  have hvar : ∀ i : W, φ (dividedPowerPolynomialVariable A i) = (k i : C) := by
    intro i
    change gAlg (DividedPowerAlgebra.dp A 1 (Finsupp.single i 1)) = (k i : C)
    rw [DividedPowerAlgebra.lift_apply_dp]
    change C.dividedPowers.dpow 1
      ((Finsupp.linearCombination A fun j => (k j : C)) (Finsupp.single i 1)) = _
    rw [Finsupp.linearCombination_single]
    simpa using C.dividedPowers.dpow_one (k i).property
  refine ⟨φ, ⟨hcoeff, hvar⟩, ?_⟩
  intro ψ hψ
  apply _root_.DividedPowers.DPMorphism.ext
  funext x
  obtain ⟨E, y, rfl⟩ := exists_finiteStage_lift A W x
  have hres : ∀ χ : _root_.DividedPowers.DPMorphism
      (setIndexedDividedPowerPolynomialDividedPowers A W) C.dividedPowers,
      χ.comp (setIndexedDividedPowerPolynomialCoefficientDPMorphism A W) = f →
      (∀ i : W, χ (dividedPowerPolynomialVariable A i) = (k i : C)) →
      (χ.comp (_root_.DividedPowers.DPMorphism.mk'
        (finiteStageInclusion_isDPMorphism A E))).comp
          (dividedPowerPolynomialCoefficientDPMorphism A E) = f ∧
        ∀ i : E,
          (χ.comp (_root_.DividedPowers.DPMorphism.mk'
            (finiteStageInclusion_isDPMorphism A E)))
              (dividedPowerPolynomialVariable A i) = (k i.1 : C) := by
    intro χ hχ1 hχ2
    constructor
    · ext a
      change χ (finiteStageInclusion A E
        (algebraMap A (DividedPowerAlgebra A (E →₀ A)) a)) = f a
      rw [(finiteStageInclusion A E).commutes]
      exact congrArg (fun q : _root_.DividedPowers.DPMorphism A.dividedPowers
        C.dividedPowers => q a) hχ1
    · intro i
      change χ (finiteStageInclusion A E (dividedPowerPolynomialVariable A i)) = (k i.1 : C)
      have hv : finiteStageInclusion A E (dividedPowerPolynomialVariable A i) =
          dividedPowerPolynomialVariable A i.1 := by
        simpa [dividedPowerPolynomialVariable, dividedPowerPolynomialVariableMonomial] using
          finiteStageInclusion_dp A E i 1
      rw [hv]
      exact hχ2 i.1
  have hU := existsUnique_dPMorphism_from_dividedPowerPolynomial A E C f (fun i => k i.1)
  have hlocal := ExistsUnique.unique hU (hres ψ hψ.1 hψ.2) (hres φ hcoeff hvar)
  have hval := congrArg (fun q : _root_.DividedPowers.DPMorphism
      (dividedPowerPolynomialDividedPowers A E) C.dividedPowers => q y) hlocal
  change (ψ.comp (_root_.DividedPowers.DPMorphism.mk'
      (finiteStageInclusion_isDPMorphism A E))).toRingHom y =
    (φ.comp (_root_.DividedPowers.DPMorphism.mk'
      (finiteStageInclusion_isDPMorphism A E))).toRingHom y at hval
  rw [_root_.DividedPowers.DPMorphism.comp_toRingHom,
    _root_.DividedPowers.DPMorphism.comp_toRingHom, RingHom.comp_apply,
    RingHom.comp_apply] at hval
  exact hval

end DividedPowers

end
