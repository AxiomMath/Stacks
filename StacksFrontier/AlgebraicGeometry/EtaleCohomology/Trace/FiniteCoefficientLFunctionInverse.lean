module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FiniteCoefficientLFunction

/-!
# Recognising the inverse of the L-function from finite products

The L-function `L(X, ℱ) = ∏_{x ∈ |X|} det(1 - π_x^* T ^ (deg x) |_{ℱ_x̄}) ⁻¹` of a sheaf with
finite projective stalks is inverted by a power series `c` as soon as, for every `N`, `c` agrees up
to `T ^ N` with the finite product `∏_{x ∈ t} det(1 - π_x^* T ^ (deg x) |_{ℱ_x̄})` over a finite
set `t` of closed points containing those of degree at most `N`. This is how the identity
`L(X, ℱ) = det(1 - π_X^* T | RΓ_c(X_k̄, ℱ)) ⁻¹` of [Stacks, Tag 03UZ] is reached from its
truncations.

## Main results

* `Stacks.EtaleCohomology.mul_lFunctionOfFiniteProjectiveStalks_eq_one`.
* `Stacks.EtaleCohomology.mul_constructibleFlatLFunction_eq_one`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Frobenius

universe u w r

namespace Stacks.EtaleCohomology

/-- Two products agree up to `T ^ N` when their factors do. -/
theorem coeff_mul_eq_coeff_mul_of_le {S : Type*} [CommRing S] {a a' b b' : PowerSeries S} {N : ℕ}
    (ha : ∀ j ≤ N, PowerSeries.coeff j a = PowerSeries.coeff j a')
    (hb : ∀ j ≤ N, PowerSeries.coeff j b = PowerSeries.coeff j b') :
    ∀ j ≤ N, PowerSeries.coeff j (a * b) = PowerSeries.coeff j (a' * b') := by
  intro j hj
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have := Finset.mem_antidiagonal.1 hx
  rw [ha x.1 (by omega), hb x.2 (by omega)]

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ]
  [HasColimitsOfSize.{u, u} (ModuleCat.{w} Λ)] [HasLimitsOfSize.{u, u} (ModuleCat.{w} Λ)]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ))
  {k : Type u} [Field k] [Finite k] (f : X.obj ⟶ Spec (.of k)) [LocallyOfFiniteType f]
  (hfin : ∀ s : GeometricPoint X.obj, Module.Finite Λ ((etaleModuleStalkFunctor B X Λ s).obj F))
  (hproj : ∀ s : GeometricPoint X.obj,
    Module.Projective Λ ((etaleModuleStalkFunctor B X Λ s).obj F))

/-- **A power series agreeing with the finite products of the local characteristic series up to
every degree inverts the L-function.** -/
theorem mul_lFunctionOfFiniteProjectiveStalks_eq_one [QuasiCompact f] (c : PowerSeries Λ)
    (hc : ∀ N : ℕ, ∃ t : Finset (closedPoints X.obj),
      (∀ x : closedPoints X.obj, residueDegree f x.1 ≤ N → x ∈ t) ∧
      ∀ j ≤ N, PowerSeries.coeff j c = PowerSeries.coeff j
        (∏ x ∈ t, finiteProjectiveLocalCharSeries B X Λ F f hfin hproj x)) :
    c * lFunctionOfFiniteProjectiveStalks B X Λ F f hfin hproj = 1 := by
  ext N
  obtain ⟨t, ht, hct⟩ := hc N
  have hL : ∀ j ≤ N, PowerSeries.coeff j (lFunctionOfFiniteProjectiveStalks B X Λ F f hfin hproj) =
      PowerSeries.coeff j (∏ x ∈ t, finiteProjectiveLocalFactor B X Λ F f hfin hproj x) :=
    fun j hj => EulerSystem.coeff_eulerProduct_eq _ fun x hx =>
      ht x (((EulerSystem.mem_support _).1 hx).trans hj)
  rw [coeff_mul_eq_coeff_mul_of_le hct hL N le_rfl, ← Finset.prod_mul_distrib,
    Finset.prod_congr rfl fun x _ => finiteProjectiveLocalCharSeries_mul_localFactor B X Λ F f
      hfin hproj x, Finset.prod_const_one]

variable [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} Λ)]

/-- **A power series agreeing with the finite products of the local characteristic series up to
every degree inverts the L-function of a constructible flat sheaf.** -/
theorem mul_constructibleFlatLFunction_eq_one [QuasiCompact f]
    (hF : IsConstructibleFlatModuleSheaf B X Λ F) (c : PowerSeries Λ)
    (hc : ∀ N : ℕ, ∃ t : Finset (closedPoints X.obj),
      (∀ x : closedPoints X.obj, residueDegree f x.1 ≤ N → x ∈ t) ∧
      ∀ j ≤ N, PowerSeries.coeff j c = PowerSeries.coeff j
        (∏ x ∈ t, finiteProjectiveLocalCharSeries B X Λ F f
          (finite_etaleModuleStalk_of_isConstructibleFlatModuleSheaf B X Λ F hF)
          (projective_etaleModuleStalk_of_isConstructibleFlatModuleSheaf B X Λ F hF) x)) :
    c * constructibleFlatLFunction B X Λ F f hF = 1 :=
  mul_lFunctionOfFiniteProjectiveStalks_eq_one B X Λ F f _ _ c hc

end Stacks.EtaleCohomology
