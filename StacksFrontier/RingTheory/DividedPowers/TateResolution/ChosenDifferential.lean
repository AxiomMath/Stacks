module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.DifferentialLift
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.OddExtMap

/-!
# The differential prescribed on the variables, as a function of the presentation

`exists_differential_gradedDividedPowerPolynomial` produces *a* differential taking prescribed
values on the variables of a graded divided-power polynomial algebra. It is an existence
statement, and a degree-by-degree construction needs more than that: it has to compare the
differential of one stage with the differential of the next, and two existentially produced maps
cannot be compared. A linear map is not determined by its values on the coefficients and on the
variables, so there is nothing to compare them *by* either.

This file chooses the differential, so that it becomes a function of the presentation and of the
prescribed boundary, and proves that the choice commutes with a comparison map. The route is the
one the existence proof already takes. A degree-lowering map obeying the two Leibniz rules is the
same thing as a graded divided-power algebra map `x ↦ x + (D x) T` into the odd-variable
extension by one variable of degree one; that map — the *avatar* of the differential — is what
the universal property of the presentation produces, and because the universal property is a
`∃!` the avatar is a function. Two avatars into one odd-variable extension are then compared by
the uniqueness half of that same universal property, which is what makes the comparison a map of
complexes.

## Main definitions

* `DividedPowers.TateResolution.IndexedPresentation.oddAvatar` — the algebra map into the
  odd-variable extension whose second coefficient is the differential.
* `DividedPowers.TateResolution.IndexedPresentation.chosenDifferential` — the differential
  prescribed by a boundary, as a function of the presentation and the boundary.

## Main results

* `DividedPowers.TateResolution.IndexedPresentation.existsUnique_oddAvatar` — the universal
  property of the presentation, instantiated at an odd-variable extension.
* `DividedPowers.TateResolution.IndexedPresentation.oddAvatar_fst` — the avatar has the identity
  as its first coefficient.
* `DividedPowers.TateResolution.IndexedPresentation.chosenDifferential_coefficient`,
  `chosenDifferential_gen`, `chosenDifferential_grade_zero`, `chosenDifferential_mem_grade`,
  `chosenDifferential_leibniz` and `chosenDifferential_dpow` — the six properties of a
  differential, for the chosen one.
* `DividedPowers.TateResolution.IndexedPresentation.comparison_differential` — **the comparison
  map of two presentations is a map of complexes** for the prescribed differentials, as soon as
  the boundary prescribed on a variable in the image of the index map is the image of the
  boundary prescribed on the corresponding variable.
* `DividedPowers.TateResolution.IndexedPresentation.comparison_differential_eq_zero_iff` — the
  cycles of a presentation on a truncated family of variables are exactly the cycles of the
  presentation on the full family that lie in it.

## References

* [Stacks Project, Tag 09PM](https://stacks.math.columbia.edu/tag/09PM)
* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w

attribute [local implicit_reducible] TwistedModule

namespace IndexedPresentation

variable {R : Type u} {P : Type v} [CommRing R] [CommRing P] [Algebra R P]
  {idx idx' : ℕ → Type (max u v w)}

/-- **An algebra map of a presentation into an odd-variable extension**, prescribed by a
coefficient map, a value for each variable and a coefficient of the adjoined variable for each
variable. -/
public theorem existsUnique_oddAvatar (T : IndexedPresentation.{u, v, w} R P idx)
    {C : Type (max u v w)} [Ring C] [Algebra R C] (Cᵢ : ℕ → Submodule R C)
    [GradedAlgebra Cᵢ] [IsStrictlyGradedComm Cᵢ] (ε : DividedPowerStructure Cᵢ)
    (κ : P →ₐ[R] C) (hκ : ∀ p : P, κ p ∈ Cᵢ 0)
    (b : (Σ n : ℕ, idx n) → C) (hb : ∀ j, b j ∈ Cᵢ (j.1 + 1))
    (s : (Σ n : ℕ, idx n) → C) (hs : ∀ j, s j ∈ Cᵢ j.1) :
    ∃! g : T.A →ₐ[R] OddVariableExtension Cᵢ 1,
      (∀ p : P, g (T.coefficient p) = OddVariableExtension.inclusion Cᵢ 1 (κ p)) ∧
      (∀ j : Σ n : ℕ, idx n, g (T.gen j) =
        OddVariableExtension.inclusion Cᵢ 1 (b j) +
          OddVariableExtension.inclusion Cᵢ 1 (signRingEquiv Cᵢ 1 (s j)) *
            OddVariableExtension.generator Cᵢ 1) ∧
      (∀ (m : ℕ) (x : T.A), x ∈ T.grade m → g x ∈ OddVariableExtension.grade Cᵢ 1 m) ∧
      (∀ (n : ℕ) (x : T.A), x ∈ positiveEvenPart T.grade →
        (oddVariableDividedPowerStructure Cᵢ ε 1 Nat.one_pos odd_one).dpow n (g x) =
          g (T.gamma.dpow n x)) := by
  have hdeg : ∀ j : Σ n : ℕ, idx n,
      OddVariableExtension.inclusion Cᵢ 1 (b j) +
        OddVariableExtension.inclusion Cᵢ 1 (signRingEquiv Cᵢ 1 (s j)) *
          OddVariableExtension.generator Cᵢ 1 ∈
        OddVariableExtension.grade Cᵢ 1 (j.1 + 1) := by
    intro j
    rw [OddVariableExtension.mem_grade_coefficients_iff,
      coefficients_inclusion_add_mul_generator]
    refine ⟨hb j, ?_⟩
    rw [ite_eq_left (by omega : (1 : ℕ) ≤ j.1 + 1), Nat.add_sub_cancel,
      signRingEquiv_of_mem Cᵢ 1 j.1 (hs j)]
    exact (Cᵢ j.1).smul_mem _ (hs j)
  exact T.existsUnique_hom (OddVariableExtension.grade Cᵢ 1)
    (oddVariableDividedPowerStructure Cᵢ ε 1 Nat.one_pos odd_one)
    ((OddVariableExtension.inclusionAlgHom Cᵢ 1).comp κ)
    (fun j => OddVariableExtension.inclusion Cᵢ 1 (b j) +
      OddVariableExtension.inclusion Cᵢ 1 (signRingEquiv Cᵢ 1 (s j)) *
        OddVariableExtension.generator Cᵢ 1)
    (mem_grade_of_mem_degreeZeroGrade (OddVariableExtension.grade Cᵢ 1)
      ((OddVariableExtension.inclusionAlgHom Cᵢ 1).comp κ)
      (fun p => OddVariableExtension.inclusion_mem_grade Cᵢ 1 0 (hκ p)))
    (dpow_comp_of_degreeZero (OddVariableExtension.grade Cᵢ 1)
      (oddVariableDividedPowerStructure Cᵢ ε 1 Nat.one_pos odd_one)
      ((OddVariableExtension.inclusionAlgHom Cᵢ 1).comp κ))
    hdeg

/-- **The avatar of the differential prescribed by `t`**: the chosen algebra map of `T.A` into
its own odd-variable extension by a variable of degree one sending `x` to `x + (D x) T`. -/
public noncomputable def oddAvatar (T : IndexedPresentation.{u, v, w} R P idx)
    (t : (Σ n : ℕ, idx n) → T.A) (ht : ∀ j, t j ∈ T.grade j.1) :
    T.A →ₐ[R] OddVariableExtension T.grade 1 :=
  (T.existsUnique_oddAvatar T.grade T.gamma T.coefficient T.coefficient_mem_grade_zero
    T.gen T.gen_mem t ht).choose

variable (T : IndexedPresentation.{u, v, w} R P idx)
  (t : (Σ n : ℕ, idx n) → T.A) (ht : ∀ j, t j ∈ T.grade j.1)

/-- The characterising properties of the avatar, bundled. -/
private theorem oddAvatar_spec :
    (∀ p : P, T.oddAvatar t ht (T.coefficient p) =
      OddVariableExtension.inclusion T.grade 1 (T.coefficient p)) ∧
    (∀ j : Σ n : ℕ, idx n, T.oddAvatar t ht (T.gen j) =
      OddVariableExtension.inclusion T.grade 1 (T.gen j) +
        OddVariableExtension.inclusion T.grade 1 (signRingEquiv T.grade 1 (t j)) *
          OddVariableExtension.generator T.grade 1) ∧
    (∀ (m : ℕ) (x : T.A), x ∈ T.grade m →
      T.oddAvatar t ht x ∈ OddVariableExtension.grade T.grade 1 m) ∧
    (∀ (n : ℕ) (x : T.A), x ∈ positiveEvenPart T.grade →
      (oddVariableDividedPowerStructure T.grade T.gamma 1 Nat.one_pos odd_one).dpow n
        (T.oddAvatar t ht x) = T.oddAvatar t ht (T.gamma.dpow n x)) :=
  (T.existsUnique_oddAvatar T.grade T.gamma T.coefficient T.coefficient_mem_grade_zero
    T.gen T.gen_mem t ht).choose_spec.1

/-- The avatar sends each coefficient to its image in the odd-variable extension. -/
public theorem oddAvatar_coefficient (p : P) :
    T.oddAvatar t ht (T.coefficient p) =
      OddVariableExtension.inclusion T.grade 1 (T.coefficient p) :=
  (T.oddAvatar_spec t ht).1 p

/-- The avatar sends the variable `T.gen j` to `T.gen j + (t j) T`, up to the grading sign. -/
public theorem oddAvatar_gen (j : Σ n : ℕ, idx n) :
    T.oddAvatar t ht (T.gen j) =
      OddVariableExtension.inclusion T.grade 1 (T.gen j) +
        OddVariableExtension.inclusion T.grade 1 (signRingEquiv T.grade 1 (t j)) *
          OddVariableExtension.generator T.grade 1 :=
  (T.oddAvatar_spec t ht).2.1 j

/-- The avatar preserves the grading. -/
public theorem oddAvatar_mem_grade (m : ℕ) (x : T.A) (hx : x ∈ T.grade m) :
    T.oddAvatar t ht x ∈ OddVariableExtension.grade T.grade 1 m :=
  (T.oddAvatar_spec t ht).2.2.1 m x hx

/-- The avatar commutes with the divided powers on the positive even part. -/
public theorem oddAvatar_dpow (n : ℕ) (x : T.A) (hx : x ∈ positiveEvenPart T.grade) :
    (oddVariableDividedPowerStructure T.grade T.gamma 1 Nat.one_pos odd_one).dpow n
        (T.oddAvatar t ht x) = T.oddAvatar t ht (T.gamma.dpow n x) :=
  (T.oddAvatar_spec t ht).2.2.2 n x hx

/-- The avatar maps the positive even part into the positive even part. -/
public theorem oddAvatar_mem_positiveEvenPart {x : T.A} (hx : x ∈ positiveEvenPart T.grade) :
    T.oddAvatar t ht x ∈ positiveEvenPart (OddVariableExtension.grade T.grade 1) :=
  algHom_mem_positiveEvenPart T.grade (OddVariableExtension.grade T.grade 1)
    (T.oddAvatar t ht) (T.oddAvatar_mem_grade t ht) hx

/-- **The avatar has the identity as its first coefficient.** -/
public theorem oddAvatar_fst (x : T.A) :
    (OddVariableExtension.coefficients T.grade 1 (T.oddAvatar t ht x)).1 = x := by
  obtain ⟨gid, -, hu⟩ := T.existsUnique_hom T.grade T.gamma T.coefficient T.gen
    (mem_grade_of_mem_degreeZeroGrade T.grade T.coefficient T.coefficient_mem_grade_zero)
    (dpow_comp_of_degreeZero T.grade T.gamma T.coefficient) T.gen_mem
  have h1 : (oddExtFst T.grade).comp (T.oddAvatar t ht) = AlgHom.id R T.A := by
    refine (hu _ ?_).trans (hu _ ?_).symm
    · refine ⟨fun p => ?_, fun j => ?_, fun m a ha => ?_, fun n a ha => ?_⟩
      · show (OddVariableExtension.coefficients T.grade 1
            (T.oddAvatar t ht (T.coefficient p))).1 = T.coefficient p
        rw [T.oddAvatar_coefficient t ht p]
        rfl
      · show (OddVariableExtension.coefficients T.grade 1
            (T.oddAvatar t ht (T.gen j))).1 = T.gen j
        rw [T.oddAvatar_gen t ht j, coefficients_inclusion_add_mul_generator]
      · show (OddVariableExtension.coefficients T.grade 1
            (T.oddAvatar t ht a)).1 ∈ T.grade m
        exact ((OddVariableExtension.mem_grade_coefficients_iff T.grade 1 m _).mp
          (T.oddAvatar_mem_grade t ht m a ha)).1
      · show T.gamma.dpow n (OddVariableExtension.coefficients T.grade 1
            (T.oddAvatar t ht a)).1 =
          (OddVariableExtension.coefficients T.grade 1
            (T.oddAvatar t ht (T.gamma.dpow n a))).1
        rw [← T.oddAvatar_dpow t ht n a ha]
        exact (oddExtFst_dpow T.grade T.gamma n
          (T.oddAvatar_mem_positiveEvenPart t ht ha)).symm
    · exact ⟨fun _ => rfl, fun _ => rfl, fun _ _ ha => ha, fun _ _ _ => rfl⟩
  exact congrArg (fun k : T.A →ₐ[R] T.A => k x) h1

/-- **The differential of `T` prescribed by `t`**, as a function of `T` and `t`: the second
coefficient of the avatar, twisted by the grading sign. -/
public noncomputable def chosenDifferential : T.A →ₗ[R] T.A :=
  (signLinearMap T.grade 1).comp ((LinearMap.snd R T.A T.A).comp
    ((OddVariableExtension.coefficients T.grade 1).toLinearMap.comp
      (T.oddAvatar t ht).toLinearMap))

/-- The chosen differential is the sign-twisted second coefficient of the avatar. -/
public theorem chosenDifferential_apply (x : T.A) :
    T.chosenDifferential t ht x =
      signRingEquiv T.grade 1
        (OddVariableExtension.coefficients T.grade 1 (T.oddAvatar t ht x)).2 := rfl

/-- The chosen differential vanishes on the coefficients. -/
public theorem chosenDifferential_coefficient (p : P) :
    T.chosenDifferential t ht (T.coefficient p) = 0 := by
  rw [chosenDifferential_apply, T.oddAvatar_coefficient t ht p,
    OddVariableExtension.coefficients_inclusion]
  simp

/-- The chosen differential takes the prescribed value `t j` on the variable `T.gen j`. -/
public theorem chosenDifferential_gen (j : Σ n : ℕ, idx n) :
    T.chosenDifferential t ht (T.gen j) = t j := by
  rw [chosenDifferential_apply, T.oddAvatar_gen t ht j,
    coefficients_inclusion_add_mul_generator]
  exact signRingEquiv_signRingEquiv T.grade 1 (t j)

/-- The chosen differential vanishes in degree zero. -/
public theorem chosenDifferential_grade_zero (x : T.A) (hx : x ∈ T.grade 0) :
    T.chosenDifferential t ht x = 0 := by
  have hmem := ((OddVariableExtension.mem_grade_coefficients_iff T.grade 1 0
    (T.oddAvatar t ht x)).mp (T.oddAvatar_mem_grade t ht 0 x hx)).2
  rw [ite_eq_right (by omega : ¬ (1 : ℕ) ≤ 0), Submodule.mem_bot] at hmem
  rw [chosenDifferential_apply, hmem]
  simp

/-- The chosen differential lowers the degree by one. -/
public theorem chosenDifferential_mem_grade (n : ℕ) (x : T.A) (hx : x ∈ T.grade (n + 1)) :
    T.chosenDifferential t ht x ∈ T.grade n := by
  have hmem := ((OddVariableExtension.mem_grade_coefficients_iff T.grade 1 (n + 1)
    (T.oddAvatar t ht x)).mp (T.oddAvatar_mem_grade t ht (n + 1) x hx)).2
  rw [ite_eq_left (by omega : (1 : ℕ) ≤ n + 1), Nat.add_sub_cancel] at hmem
  rw [chosenDifferential_apply]
  exact signRingEquiv_mem_grade T.grade 1 hmem

/-- The chosen differential satisfies the graded Leibniz rule. -/
public theorem chosenDifferential_leibniz (i j : ℕ) (x y : T.A) (hx : x ∈ T.grade i)
    (_hy : y ∈ T.grade j) :
    T.chosenDifferential t ht (x * y) =
      T.chosenDifferential t ht x * y + (-1 : R) ^ i • (x * T.chosenDifferential t ht y) := by
  rw [chosenDifferential_apply, chosenDifferential_apply, chosenDifferential_apply, map_mul,
    OddVariableExtension.coefficients_mul, T.oddAvatar_fst t ht x, T.oddAvatar_fst t ht y,
    map_add, map_mul, map_mul, signRingEquiv_signRingEquiv,
    signRingEquiv_of_mem T.grade 1 i hx, one_mul, smul_mul_assoc, add_comm]

/-- The chosen differential satisfies `D(γₙ x) = D(x) γₙ₋₁(x)` on the positive even part. -/
public theorem chosenDifferential_dpow (n : ℕ) (x : T.A) (hn : n ≠ 0)
    (hx : x ∈ positiveEvenPart T.grade) :
    T.chosenDifferential t ht (T.gamma.dpow n x) =
      T.chosenDifferential t ht x * T.gamma.dpow (n - 1) x := by
  have hgx := T.oddAvatar_mem_positiveEvenPart t ht hx
  have heven : T.gamma.dpow (n - 1) x ∈ evenPart T.grade := by
    rcases Nat.eq_zero_or_pos (n - 1) with hz | hp
    · rw [hz, T.gamma.dpow_zero hx]
      exact Submodule.mem_iSup_of_mem 0 (by simpa using SetLike.one_mem_graded T.grade)
    · exact positiveEvenPart_le_evenPart T.grade (T.gamma.dpow_mem (by omega) hx)
  rw [chosenDifferential_apply, chosenDifferential_apply, ← T.oddAvatar_dpow t ht n x hx,
    coefficients_dpow T.grade T.gamma n hn hgx, T.oddAvatar_fst t ht x, map_mul,
    signRingEquiv_one_of_mem_evenPart T.grade heven, mul_comm_of_mem_evenPart T.grade heven]

/-- **A graded divided-power map of presentations carrying the prescribed boundaries to the
prescribed boundaries commutes with the prescribed differentials.** -/
public theorem chosenDifferential_comp (T : IndexedPresentation.{u, v, w} R P idx)
    (T' : IndexedPresentation.{u, v, w} R P idx') (e : ∀ n : ℕ, idx n → idx' n)
    (t : (Σ n : ℕ, idx n) → T.A) (ht : ∀ j, t j ∈ T.grade j.1)
    (t' : (Σ n : ℕ, idx' n) → T'.A) (ht' : ∀ j, t' j ∈ T'.grade j.1)
    (c : T.A →ₐ[R] T'.A)
    (hcgr : ∀ (m : ℕ) (y : T.A), y ∈ T.grade m → c y ∈ T'.grade m)
    (hcdp : ∀ (n : ℕ) (y : T.A), y ∈ positiveEvenPart T.grade →
      c (T.gamma.dpow n y) = T'.gamma.dpow n (c y))
    (hcco : ∀ p : P, c (T.coefficient p) = T'.coefficient p)
    (hcgen : ∀ j : Σ n : ℕ, idx n, c (T.gen j) = T'.gen ⟨j.1, e j.1 j.2⟩)
    (hcompat : ∀ j : Σ n : ℕ, idx n, t' ⟨j.1, e j.1 j.2⟩ = c (t j)) (x : T.A) :
    T'.chosenDifferential t' ht' (c x) = c (T.chosenDifferential t ht x) := by
  obtain ⟨g, -, hgu⟩ := T.existsUnique_oddAvatar T'.grade T'.gamma T'.coefficient
    T'.coefficient_mem_grade_zero (fun j => T'.gen ⟨j.1, e j.1 j.2⟩)
    (fun j => T'.gen_mem ⟨j.1, e j.1 j.2⟩) (fun j => c (t j))
    (fun j => hcgr j.1 (t j) (ht j))
  have key : (oddExtMap T.grade T'.grade 1 c hcgr).comp (T.oddAvatar t ht) =
      (T'.oddAvatar t' ht').comp c := by
    refine (hgu _ ?_).trans (hgu _ ?_).symm
    · refine ⟨fun p => ?_, fun j => ?_, fun m y hy => ?_, fun n y hy => ?_⟩
      · simp only [AlgHom.coe_comp, Function.comp_apply]
        rw [T.oddAvatar_coefficient t ht p, oddExtMap_inclusion, hcco p]
      · simp only [AlgHom.coe_comp, Function.comp_apply]
        rw [T.oddAvatar_gen t ht j, map_add, map_mul, oddExtMap_inclusion,
          oddExtMap_inclusion, oddExtMap_generator, hcgen j,
          algHom_signRingEquiv T.grade T'.grade c hcgr 1 (t j)]
      · exact oddExtMap_mem_grade T.grade T'.grade 1 c hcgr m _
          (T.oddAvatar_mem_grade t ht m y hy)
      · simp only [AlgHom.coe_comp, Function.comp_apply]
        rw [← T.oddAvatar_dpow t ht n y hy]
        exact (oddExtMap_dpow T.grade T'.grade T.gamma T'.gamma c hcgr hcdp n
          (T.oddAvatar_mem_positiveEvenPart t ht hy)).symm
    · refine ⟨fun p => ?_, fun j => ?_, fun m y hy => ?_, fun n y hy => ?_⟩
      · simp only [AlgHom.coe_comp, Function.comp_apply]
        rw [hcco p, T'.oddAvatar_coefficient t' ht' p]
      · simp only [AlgHom.coe_comp, Function.comp_apply]
        rw [hcgen j, T'.oddAvatar_gen t' ht' ⟨j.1, e j.1 j.2⟩, hcompat j]
      · exact T'.oddAvatar_mem_grade t' ht' m _ (hcgr m y hy)
      · simp only [AlgHom.coe_comp, Function.comp_apply]
        rw [T'.oddAvatar_dpow t' ht' n (c y)
          (T.mem_positiveEvenPart_of_mem T' c hcgr hy), hcdp n y hy]
  have hap := congrArg (fun k : T.A →ₐ[R] OddVariableExtension T'.grade 1 => k x) key
  have h2 : c (OddVariableExtension.coefficients T.grade 1 (T.oddAvatar t ht x)).2 =
      (OddVariableExtension.coefficients T'.grade 1 (T'.oddAvatar t' ht' (c x))).2 := by
    have h3 := congrArg (fun z => (OddVariableExtension.coefficients T'.grade 1 z).2) hap
    simpa only [AlgHom.coe_comp, Function.comp_apply,
      coefficients_oddExtMap T.grade T'.grade 1 c hcgr] using h3
  rw [chosenDifferential_apply, chosenDifferential_apply,
    algHom_signRingEquiv T.grade T'.grade c hcgr 1, h2]

/-- **The comparison map of two presentations commutes with their prescribed differentials.** -/
public theorem comparison_differential (T : IndexedPresentation.{u, v, w} R P idx)
    (T' : IndexedPresentation.{u, v, w} R P idx') (e : ∀ n : ℕ, idx n → idx' n)
    (t : (Σ n : ℕ, idx n) → T.A) (ht : ∀ j, t j ∈ T.grade j.1)
    (t' : (Σ n : ℕ, idx' n) → T'.A) (ht' : ∀ j, t' j ∈ T'.grade j.1)
    (hcompat : ∀ j : Σ n : ℕ, idx n, t' ⟨j.1, e j.1 j.2⟩ = T.comparison T' e (t j))
    (x : T.A) :
    T'.chosenDifferential t' ht' (T.comparison T' e x) =
      T.comparison T' e (T.chosenDifferential t ht x) :=
  T.chosenDifferential_comp T' e t ht t' ht' (T.comparison T' e)
    (T.comparison_mem_grade T' e)
    (fun n y hy => (T.comparison_dpow T' e n y hy).symm)
    (T.comparison_coefficient T' e) (T.comparison_gen T' e) hcompat x

/-- **An element of the source is a cycle exactly when its image is**, when the index map has a
degree-wise retraction. So the cycles of the algebra on a truncated family of variables are
exactly the cycles of the algebra on the full family that lie in it. -/
public theorem comparison_differential_eq_zero_iff (T : IndexedPresentation.{u, v, w} R P idx)
    (T' : IndexedPresentation.{u, v, w} R P idx') (e : ∀ n : ℕ, idx n → idx' n)
    (t : (Σ n : ℕ, idx n) → T.A) (ht : ∀ j, t j ∈ T.grade j.1)
    (t' : (Σ n : ℕ, idx' n) → T'.A) (ht' : ∀ j, t' j ∈ T'.grade j.1)
    (ρ : ∀ n : ℕ, idx' n → Option (idx n)) (hρ : ∀ (n : ℕ) (x : idx n), ρ n (e n x) = some x)
    (hcompat : ∀ j : Σ n : ℕ, idx n, t' ⟨j.1, e j.1 j.2⟩ = T.comparison T' e (t j))
    (x : T.A) :
    T'.chosenDifferential t' ht' (T.comparison T' e x) = 0 ↔
      T.chosenDifferential t ht x = 0 := by
  rw [T.comparison_differential T' e t ht t' ht' hcompat x]
  refine ⟨fun h => T.comparison_injective T' e ρ hρ ?_, fun h => by rw [h, map_zero]⟩
  rw [h, map_zero]

end IndexedPresentation

end DividedPowers.TateResolution

end
