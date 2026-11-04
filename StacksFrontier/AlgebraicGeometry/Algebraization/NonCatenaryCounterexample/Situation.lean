module

public import StacksFrontier.AlgebraicGeometry.Algebraization.NonCatenaryCounterexample.PinchedRing
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalFormalLocusDimensionCriterion
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.ClopenCriterion

/-!
# Hypotheses and failure for the non-catenary counterexample to Stacks 0EJA

Two general facts, and their instances at the situation of the counterexample:

* in a Noetherian local ring, an element of the maximal ideal outside some prime generates an ideal
  of cohomological dimension exactly one;
* the `(2, 3)`-inequalities fail as soon as, at some point `y` of `U ∩ Y` with `δ^Y_Z(y) ≤ 2`,
  some prime `𝔭 ∉ V(I𝒪_{X,y}^∧)` with `V(𝔭) ∩ V(I𝒪_{X,y}^∧) = {𝔪_y^∧}` carries depth zero.

## Main results

* `Stacks.LocalCohomology.cohomologicalDimension_span_singleton_eq_one`
* `Stacks.Algebraization.not_satisfiesDepthInequalities_two_three`
* `Stacks.NonCatenaryExample.cohomologicalDimension_situation` — `cd(A'', (x₁)) = 1`.
-/

@[expose] public noncomputable section

open IsLocalRing

universe u

namespace Stacks.LocalCohomology

/-- In a Noetherian local ring, an element of the maximal ideal lying outside some prime generates
an ideal of cohomological dimension exactly one. -/
theorem cohomologicalDimension_span_singleton_eq_one (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] {f : A} (hf : f ∈ maximalIdeal A)
    (p : PrimeSpectrum A) (hp : f ∉ p.asIdeal) :
    cohomologicalDimension A (Ideal.span {f}) (Ideal.span {f}).fg_of_isNoetherianRing = 1 := by
  refine le_antisymm (cohomologicalDimension_span_singleton_le_one A f) ?_
  by_contra hlt
  have hle :
      cohomologicalDimension A (Ideal.span {f}) (Ideal.span {f}).fg_of_isNoetherianRing ≤ 0 := by
    omega
  have hclopen := (isClopen_zeroLocus_iff_cohomologicalDimension_le_zero A _ _).mp hle
  have hm : closedPoint A ∈ PrimeSpectrum.zeroLocus ((Ideal.span {f} : Ideal A) : Set A) := by
    rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.span_le,
      Set.singleton_subset_iff]
    exact hf
  have hpm : p ⤳ closedPoint A := IsLocalRing.specializes_closedPoint p
  have := hpm.mem_open hclopen.isOpen hm
  rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.span_le,
    Set.singleton_subset_iff] at this
  exact hp this

end Stacks.LocalCohomology

namespace Stacks.Algebraization

/-- **The `(2, 3)`-inequalities fail at a prime of depth zero over a point at distance at most
two.** If at some point `y` of `U ∩ Y` with `δ^Y_Z(y) ≤ 2` a prime `𝔭 ∉ V(I𝒪_{X,y}^∧)` of the
completed local ring with `V(𝔭) ∩ V(I𝒪_{X,y}^∧) = {𝔪_y^∧}` has `depth((ℱ_y^∧)_𝔭) = 0`, then
clause (2) of Stacks 0EJ3 with `a = 2` fails there. -/
theorem not_satisfiesDepthInequalities_two_three (S : AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) (y : S.U.toScheme) (z : S.Y)
    (hyz : S.U.ι.base y = S.Yι.base z) (hδ : S.distanceToZ z ≤ 2)
    (p : PrimeSpectrum (completedLocalRing (idealOnOpen S) y))
    (hp : ¬ completedLocalIdeal (idealOnOpen S) y ≤ p.asIdeal)
    (hfib : adicClosedFibreThrough (idealOnOpen S) y p =
      {completedMaximalIdeal (idealOnOpen S) y})
    (hdepth : completedStalkDepth (idealOnOpen S) F y p = 0) :
    ¬ SatisfiesDepthInequalities S F 2 3 := by
  intro h
  have h2 := (h y z hyz p hp).2 hfib
  have hle : depthAddDistance S F y z p ≤ ((2 : ℤ) : EInt) := by
    unfold depthAddDistance
    rw [hdepth]
    have h0 : enatToEInt 0 = ((0 : ℤ) : EInt) := rfl
    rw [h0]
    have hδ' : enatToEInt (S.distanceToZ z) ≤ enatToEInt 2 := enatToEInt_mono hδ
    have h2' : enatToEInt 2 = ((2 : ℤ) : EInt) := rfl
    rw [h2'] at hδ'
    calc ((0 : ℤ) : EInt) + enatToEInt (S.distanceToZ z)
        = enatToEInt (S.distanceToZ z) := zero_add _
      _ ≤ ((2 : ℤ) : EInt) := hδ'
  exact absurd h2 (not_lt.mpr hle)

end Stacks.Algebraization

namespace Stacks.NonCatenaryExample

variable (K : Type u) [Field K] (e : K ≃+* FractionRing (MvPolynomial (Fin 3) K))

/-- The variable `x₁` does not lie in `Q₀ = (x₄, x₅)`. -/
theorem X0_notMem_idealQ0 : (MvPolynomial.X 0 : R6 K) ∉ idealQ0 K := by
  rw [mem_idealQ0_iff]; simp [mapQ0]

/-- The ideal `𝔟 = (Q₀B ∩ WB) ∩ A` is contained in `Q₀B ∩ A`. -/
theorem idealB_le_primeA_Q0 : idealB K e ≤ primeA K e (idealQ0 K) :=
  Ideal.comap_mono inf_le_left

/-- The element `x₁ ∈ A` does not lie in `Q₀B ∩ A`. -/
theorem elemF_notMem_primeA_Q0 : elemF K e ∉ primeA K e (idealQ0 K) := fun h =>
  X0_notMem_idealQ0 K ((algebraMap_mem_ext_iff K (hQ0 K) _).mp h)

/-- `cd(A'', (x₁)) = 1`. -/
theorem cohomologicalDimension_situation :
    Stacks.LocalCohomology.cohomologicalDimension (situation K e).A (situation K e).I
      (IsNoetherian.noetherian (situation K e).I) = 1 := by
  have hprime : ((primeA K e (idealQ0 K)).map (Ideal.Quotient.mk (idealB K e))).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact idealB_le_primeA_Q0 K e)
  refine Stacks.LocalCohomology.cohomologicalDimension_span_singleton_eq_one (RingA2 K e)
    (idealI_le_maximalIdeal K e (Ideal.subset_span (Set.mem_singleton _))) ⟨_, hprime⟩ ?_
  intro hmem
  apply elemF_notMem_primeA_Q0 K e
  have := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hmem
  obtain ⟨a, ha, hfa⟩ := this
  have hd : a - elemF K e ∈ primeA K e (idealQ0 K) := idealB_le_primeA_Q0 K e
    (Ideal.Quotient.eq.mp hfa)
  simpa using (primeA K e (idealQ0 K)).sub_mem ha hd

end Stacks.NonCatenaryExample

end
