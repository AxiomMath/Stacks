module

public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.CharSeries
public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.Trace
public import StacksFrontier.CategoryTheory.Trace.Sorites.Multiplicativity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CharSeriesTrace
public import StacksFrontier.RingTheory.PowerSeries.LogDerivative
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.PerfectTower
import all StacksFrontier.Homology.DerivedCategory.InverseSystem.PerfectTower

/-!
# The logarithmic derivative of the characteristic series of a perfect complex

For an endomorphism `f` of a perfect complex `K` over a commutative ring `R`,

`T d/dT log det(1 - f T | K)⁻¹ = ∑_{m ≥ 1} Tr(f ^ m | K) T ^ m`

as an identity of power series over `R`, valid over any commutative ring. It is proved for an
endomorphism of a finite projective module, for an endomorphism of a bounded complex of finite
projective modules, and for an endomorphism of a perfect object of the derived category.

## Main results

* `ProjectiveDeterminant.coeff_logDerivative_charSeries`: the coefficient of `T ^ m` of the
  logarithmic derivative of `det(1 - φ T)` is `-Tr(φ ^ m)`.
* `CategoryTheory.FilteredDerived.coeff_logDerivative_inv_alternatingCharSeries`: for an
  endomorphism `g` of a bounded complex `P` of finite projective modules, the coefficient of
  `T ^ m` of the logarithmic derivative of `det(1 - g T | P)⁻¹` is `Tr(g ^ m | P)`.
* `CategoryTheory.FilteredDerived.coeff_logDerivative_inv_perfectDerivedCharSeries`: the same for
  an endomorphism `f` of a perfect object `K` of the derived category, with `Tr(f ^ m | K)`.
-/

@[expose] public noncomputable section

open CategoryTheory PowerSeries

universe u v

/-! ### Finite projective modules -/

namespace ProjectiveDeterminant

variable {Λ : Type u} [CommRing Λ] {M : Type v} [AddCommGroup M] [Module Λ M]
  [Module.Finite Λ M] [Module.Projective Λ M]

/-- The trace of an endomorphism of a finite free module `Fin n → Λ`, read in `Λ`, is the trace of
its matrix. -/
theorem eval_freeModuleTrace {n : ℕ} (g : Module.End Λ (Fin n → Λ)) :
    Stacks.Trace.commutativeAdditiveCommutatorQuotientEval Λ
        (FilteredDerived.freeModuleTrace Λ (Fin n) g) =
      (LinearMap.toMatrix (Pi.basisFun Λ (Fin n)) (Pi.basisFun Λ (Fin n)) g).trace := by
  change (∑ i, g (FilteredDerived.standardBasisVector Λ (Fin n) i) i) = _
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, Pi.basisFun_apply,
    Pi.basisFun_repr]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : FilteredDerived.standardBasisVector Λ (Fin n) j = Pi.single j 1 := by
    funext x
    simp [FilteredDerived.standardBasisVector, Pi.single_apply]
  rw [hj]

/-- **The logarithmic derivative of `det(1 - φ T)`.** For an endomorphism `φ` of a finite
projective module and `m ≥ 1`, the coefficient of `T ^ m` of `T d/dT log det(1 - φ T)` is
`-Tr(φ ^ m)`. -/
theorem coeff_logDerivative_charSeries (φ : M →ₗ[Λ] M) {m : ℕ} (hm : m ≠ 0) :
    coeff m (logDerivative (charSeries φ 1)) =
      -Stacks.Trace.commutativeAdditiveCommutatorQuotientEval Λ
        (Stacks.Trace.projectiveModuleTrace Λ M (φ ^ m)) := by
  classical
  let h := Module.Finite.exists_comp_eq_id_of_projective Λ M
  let n := h.choose
  let p : (Fin n → Λ) →ₗ[Λ] M := h.choose_spec.choose
  let i : M →ₗ[Λ] (Fin n → Λ) := h.choose_spec.choose_spec.choose
  have hpi : p.comp i = LinearMap.id := h.choose_spec.choose_spec.choose_spec.2.2
  have htr : Stacks.Trace.projectiveModuleTrace Λ M (φ ^ m) =
      FilteredDerived.freeModuleTrace Λ (Fin n) (i.comp ((φ ^ m).comp p)) := rfl
  have hpow : ∀ k : ℕ, (i.comp (φ.comp p)) ^ (k + 1) = i.comp ((φ ^ (k + 1)).comp p) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, Module.End.mul_eq_comp]
      apply LinearMap.ext
      intro x
      have hx : p (i (φ (p x))) = φ (p x) := LinearMap.congr_fun hpi (φ (p x))
      simp only [LinearMap.comp_apply]
      rw [hx, pow_succ φ (k + 1), Module.End.mul_apply]
  let A := LinearMap.toMatrix (Pi.basisFun Λ (Fin n)) (Pi.basisFun Λ (Fin n)) (i.comp (φ.comp p))
  have hchar : charSeries φ 1 = Stacks.EtaleCohomology.localCharSeries A 1 := by
    rw [charSeries_retract i p hpi φ 1, charSeries_eq_det_matrix (Pi.basisFun Λ (Fin n))]
    rfl
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  rw [hchar, Stacks.EtaleCohomology.logDerivative_localCharSeries A one_ne_zero, map_neg,
    Nat.cast_one, one_mul, Stacks.EtaleCohomology.coeff_traceSeries, if_pos ⟨one_dvd _, hm⟩,
    Nat.div_one, htr, eval_freeModuleTrace, ← hpow k, ← LinearMap.toMatrix_pow]

end ProjectiveDeterminant

/-! ### Units of the power series ring -/

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- The inverse of a unit with constant coefficient `1` has constant coefficient `1`. -/
theorem constantCoeff_units_inv {u : (R⟦X⟧)ˣ} (hu : constantCoeff (u : R⟦X⟧) = 1) :
    constantCoeff ((u⁻¹ : (R⟦X⟧)ˣ) : R⟦X⟧) = 1 := by
  simpa only [map_mul, hu, one_mul, map_one] using congrArg constantCoeff (Units.mul_inv u)

/-- The logarithmic derivative of the inverse of a unit with constant coefficient `1`. -/
theorem logDerivative_units_inv {u : (R⟦X⟧)ˣ} (hu : constantCoeff (u : R⟦X⟧) = 1) :
    logDerivative ((u⁻¹ : (R⟦X⟧)ˣ) : R⟦X⟧) = -logDerivative (u : R⟦X⟧) := by
  have h := logDerivative_mul hu (constantCoeff_units_inv hu)
  rw [Units.mul_inv, logDerivative_one] at h
  linear_combination -h

end PowerSeries

/-! ### Bounded complexes of finite projective modules -/

namespace CategoryTheory.FilteredDerived

variable (R : Type u) [CommRing R]

/-- The degree `i` component of a power of an endomorphism of a complex is the power of the
degree `i` component. -/
theorem endPow_f_hom {P : CochainComplex (ModuleCat.{v} R) ℤ} (g : P ⟶ P) (m : ℕ) (i : ℤ) :
    ((End.asHom (End.of g ^ m)).f i).hom = (g.f i).hom ^ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change ((g ≫ End.asHom (End.of g ^ m)).f i).hom = _
    rw [HomologicalComplex.comp_f, ModuleCat.hom_comp, ih, pow_succ]
    rfl

/-- The degree `i` characteristic unit of a complex has constant coefficient `1`. -/
private theorem constantCoeff_charUnitAt {P : CochainComplex (ModuleCat.{v} R) ℤ}
    (hP : finiteProjectiveComplex R P) (g : P ⟶ P) (i : ℤ) :
    constantCoeff ((charUnitAt R P hP i (g.f i) : (R⟦X⟧)ˣ) : R⟦X⟧) = 1 := by
  let : Module.Projective R (P.X i) := (hP.2 i).1
  let : Module.Finite R (P.X i) := (hP.2 i).2
  rw [coe_charUnitAt]
  exact ProjectiveDeterminant.constantCoeff_charSeries _ one_ne_zero

/-- `det(1 - g T | P)` has constant coefficient `1`. -/
theorem constantCoeff_alternatingCharSeries (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (hP : finiteProjectiveComplex R P) (g : P ⟶ P) :
    constantCoeff ((alternatingCharSeries R P hP g : (R⟦X⟧)ˣ) : R⟦X⟧) = 1 := by
  classical
  let φ : (R⟦X⟧)ˣ →* Rˣ := Units.map (constantCoeff : R⟦X⟧ →+* R).toMonoidHom
  let U : ℤ → (R⟦X⟧)ˣ := fun i =>
    if Even i then charUnitAt R P hP i (g.f i) else (charUnitAt R P hP i (g.f i))⁻¹
  have hU : ∀ i, φ (U i) = 1 := by
    intro i
    have h1 : φ (charUnitAt R P hP i (g.f i)) = 1 :=
      Units.ext (constantCoeff_charUnitAt R hP g i)
    by_cases he : Even i
    · simp only [U, he, ite_true, h1]
    · simp only [U, he, ite_false, map_inv, h1, inv_one]
  have h : φ (alternatingCharSeries R P hP g) = 1 := by
    change φ (∏ᶠ i : ℤ, U i) = 1
    have hfin : (Function.mulSupport U).Finite := by
      refine (finite_nonzero_degrees R P hP).subset fun i hi hz => hi ?_
      have h1 := charUnitAt_eq_one_of_isZero R P hP i (g.f i) hz
      simp only [U, h1, inv_one, ite_self]
    rw [MonoidHom.map_finprod φ hfin]
    exact finprod_eq_one_of_forall_eq_one hU
  exact congrArg Units.val h

/-- **The logarithmic derivative of `det(1 - g T | P)⁻¹`.** For an endomorphism `g` of a bounded
complex of finite projective modules and `m ≥ 1`, the coefficient of `T ^ m` of
`T d/dT log det(1 - g T | P)⁻¹` is `Tr(g ^ m | P) = ∑ᵢ (-1)ⁱ Tr(gᵢ ^ m | Pⁱ)`. -/
theorem coeff_logDerivative_inv_alternatingCharSeries (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (hP : finiteProjectiveComplex R P) (g : P ⟶ P) {m : ℕ} (hm : m ≠ 0) :
    coeff m (logDerivative (((alternatingCharSeries R P hP g)⁻¹ : (R⟦X⟧)ˣ) : R⟦X⟧)) =
      Stacks.Trace.commutativeAdditiveCommutatorQuotientEval R
        (alternatingTrace R P hP (End.asHom (End.of g ^ m))) := by
  classical
  let S := (finite_nonzero_degrees R P hP).toFinset
  let U : ℤ → (R⟦X⟧)ˣ := fun i =>
    if Even i then charUnitAt R P hP i (g.f i) else (charUnitAt R P hP i (g.f i))⁻¹
  have hcu := constantCoeff_charUnitAt R hP g
  have hU1 : ∀ i ∉ S, U i = 1 := by
    intro i hi
    have hz : Limits.IsZero (P.X i) := by
      by_contra h
      exact hi ((finite_nonzero_degrees R P hP).mem_toFinset.2 h)
    have h1 := charUnitAt_eq_one_of_isZero R P hP i (g.f i) hz
    simp only [U, h1, inv_one, ite_self]
  have hprod : alternatingCharSeries R P hP g = ∏ i ∈ S, U i :=
    finprod_eq_prod_of_mulSupport_subset U (Function.mulSupport_subset_iff'.2 hU1)
  have hV : ∀ i, constantCoeff (((U i)⁻¹ : (R⟦X⟧)ˣ) : R⟦X⟧) = 1 := by
    intro i
    by_cases he : Even i
    · simp only [U, he, ite_true]
      exact PowerSeries.constantCoeff_units_inv (hcu i)
    · simp only [U, he, ite_false, inv_inv]
      exact hcu i
  rw [hprod, ← Finset.prod_inv_distrib, Units.coe_prod,
    PowerSeries.logDerivative_finsetProd _ _ fun i _ => hV i, map_sum]
  let t : ℤ → R := fun i =>
    let : Module.Projective R (P.X i) := (hP.2 i).1
    let : Module.Finite R (P.X i) := (hP.2 i).2
    Stacks.Trace.commutativeAdditiveCommutatorQuotientEval R
      (Stacks.Trace.projectiveModuleTrace R (P.X i) ((g.f i).hom ^ m))
  have hrhs : Stacks.Trace.commutativeAdditiveCommutatorQuotientEval R
      (alternatingTrace R P hP (End.asHom (End.of g ^ m))) =
      ∑ i ∈ S, (if Even i then t i else -t i) := by
    have hsupp : (Function.support fun i : ℤ =>
        let : Module.Projective R (P.X i) := (hP.2 i).1
        let : Module.Finite R (P.X i) := (hP.2 i).2
        let t' := Stacks.Trace.projectiveModuleTrace R (P.X i)
          ((End.asHom (End.of g ^ m)).f i).hom
        if Even i then t' else -t') ⊆ S := by
      intro i hi
      by_contra h
      apply hi
      have hz : Limits.IsZero (P.X i) := by
        by_contra h'
        exact h ((finite_nonzero_degrees R P hP).mem_toFinset.2 h')
      let : Module.Projective R (P.X i) := (hP.2 i).1
      let : Module.Finite R (P.X i) := (hP.2 i).2
      let : Subsingleton (P.X i) := ModuleCat.subsingleton_of_isZero hz
      simp only [projectiveModuleTrace_eq_zero_of_subsingleton, neg_zero, ite_self]
    rw [alternatingTrace, finsum_eq_sum_of_support_subset _ hsupp, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [t, endPow_f_hom]
    split_ifs <;> simp
  rw [hrhs]
  refine Finset.sum_congr rfl fun i _ => ?_
  let : Module.Projective R (P.X i) := (hP.2 i).1
  let : Module.Finite R (P.X i) := (hP.2 i).2
  by_cases he : Even i
  · simp only [U, he, ite_true]
    rw [PowerSeries.logDerivative_units_inv (hcu i), map_neg, coe_charUnitAt,
      ProjectiveDeterminant.coeff_logDerivative_charSeries _ hm, neg_neg]
  · simp only [U, he, ite_false, inv_inv]
    rw [coe_charUnitAt, ProjectiveDeterminant.coeff_logDerivative_charSeries _ hm]

/-! ### Perfect objects of the derived category -/

section Derived

attribute [local instance] HasDerivedCategory.standard

variable (S : Type) [CommRing S]

/-- **The logarithmic derivative of `det(1 - f T | K)⁻¹` for a perfect object `K`.** For an
endomorphism `f` of a perfect object of `D(S)` and `m ≥ 1`, the coefficient of `T ^ m` of
`T d/dT log det(1 - f T | K)⁻¹` is `Tr(f ^ m | K)`. -/
theorem coeff_logDerivative_inv_perfectDerivedCharSeries (K : DerivedCategory (ModuleCat.{v} S))
    (hK : StacksDraft.Perfect.IsPerfect K) (f : K ⟶ K) {m : ℕ} (hm : m ≠ 0) :
    coeff m (logDerivative (((perfectDerivedCharSeries S K hK f)⁻¹ : (S⟦X⟧)ˣ) : S⟦X⟧)) =
      Stacks.Trace.commutativeAdditiveCommutatorQuotientEval S
        (perfectDerivedTrace S ⟨K, hK⟩ (End.asHom (End.of f ^ m))) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := (isPerfect_iff S K).1 hK
  obtain ⟨g, hg⟩ := Stacks.InverseSystem.exists_cochainEndo P hP K e f
  have hgm : ∀ k : ℕ, DerivedCategory.Q.map (End.asHom (End.of g ^ k)) =
      e.hom ≫ End.asHom (End.of f ^ k) ≫ e.inv := by
    intro k
    induction k with
    | zero =>
      change DerivedCategory.Q.map (𝟙 P) = e.hom ≫ 𝟙 K ≫ e.inv
      simp
    | succ k ih =>
      change DerivedCategory.Q.map (g ≫ End.asHom (End.of g ^ k)) =
        e.hom ≫ (f ≫ End.asHom (End.of f ^ k)) ≫ e.inv
      rw [Functor.map_comp, hg, ih]
      simp
  rw [perfectDerivedCharSeries_eq_alternatingCharSeries S K hK f P hP e g hg,
    perfectDerivedTrace_eq_alternatingTrace S ⟨K, hK⟩ _ P hP e _ (hgm m)]
  exact coeff_logDerivative_inv_alternatingCharSeries S P hP g hm

/-- `det(1 - f T | K)` has constant coefficient `1` for an endomorphism of a perfect object. -/
theorem constantCoeff_perfectDerivedCharSeries (K : DerivedCategory (ModuleCat.{v} S))
    (hK : StacksDraft.Perfect.IsPerfect K) (f : K ⟶ K) :
    constantCoeff ((perfectDerivedCharSeries S K hK f : (S⟦X⟧)ˣ) : S⟦X⟧) = 1 := by
  obtain ⟨P, hP, ⟨e⟩⟩ := (isPerfect_iff S K).1 hK
  obtain ⟨g, hg⟩ := Stacks.InverseSystem.exists_cochainEndo P hP K e f
  rw [perfectDerivedCharSeries_eq_alternatingCharSeries S K hK f P hP e g hg]
  exact constantCoeff_alternatingCharSeries S P hP g

end Derived

end CategoryTheory.FilteredDerived

end
