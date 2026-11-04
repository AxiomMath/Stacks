module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.BaseRestriction
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.DegreeZeroGrading
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.DividedPowerTower
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Polynomial
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.VariableLift

/-! # The lift of a graded divided power polynomial algebra along a surjection of base rings

Let `q : R' → R` be a surjection of commutative rings and let `A` be a graded divided power
algebra over `R` presented as a divided power polynomial algebra over `R[xᵢ]`, with variables
`hpoly.indices n` in each degree `n + 1`. This file builds the algebra `B` lifting `A` along
`q`: the divided power polynomial algebra over `R'[xᵢ]` with the *same* set of variables in each
degree, together with the comparison map `π : B → A`.

`B` is the colimit of the `ω`-tower of
`StacksFrontier/RingTheory/DividedPowers/TateResolution/DividedPowerTower.lean` over the base
`R'[xᵢ]` graded in degree zero, and `π` is obtained from the tower's universal property by
sending `R'[xᵢ]` to `R[xᵢ]` through `q` and each variable to the corresponding variable of `A`.
This supplies the algebra, its grading, its divided powers, and the lift of the structure maps
in the square-zero lift of Tag 09PS.

## Main definitions

* `DividedPowers.TateResolution.liftIndex`, `DividedPowers.TateResolution.liftBase`,
  `DividedPowers.TateResolution.liftTowerStage` — the index sets, the degree-zero base
  `R'[xᵢ]`, and the stages of the tower over it.
* `DividedPowers.TateResolution.liftAlgebra` — the lifted algebra `B`, as a graded divided power
  algebra over `R'`.
* `DividedPowers.TateResolution.liftHom` — the comparison morphism `B → A`, and
  `DividedPowers.TateResolution.liftRingHom` the underlying ring homomorphism `π`.

## Main results

* `DividedPowers.TateResolution.liftHom_algebraMap` — `π` carries the structure map of `B` to
  that of `A` through `q`. This is `map_algebraMap` of
  `DividedPowers.TateResolution.IsSquareZeroLift`.
* `DividedPowers.TateResolution.liftHom_mem_grade` — `π` preserves homogeneous degrees, which is
  `map_mem_grade`.
* `DividedPowers.TateResolution.liftHom_dpow` — `π` is a morphism of divided powers, which is
  `map_dpow` of `DividedPowers.TateResolution.IsDividedPowerSquareZeroLift`.
* `DividedPowers.TateResolution.liftHom_surjective` — `π` is surjective, which is `surjective`.

## Implementation notes

The index sets and the base are `ULift`ed into the universe `max u v w z` in which the tower
lives: the tower's stages must all lie in one universe, and the universe of a stage produced by
`DividedPowers.TateResolution.exists_setVariableExtension_bundled` is the join of the base
ring's, the previous stage's, the index set's and the target's. Lifting the index sets rather
than the stages is what keeps that join constant, and it costs nothing — Tag 09PS asks only for
a *bijection* between the variables of `A` and those of `B`.

Surjectivity of `π` is proved by showing that its range is a subring of `A` containing every
generator of every finite variable stage of the presentation `hpoly`, and then invoking
`hpoly.finite_support`. The divided powers of a variable of *odd* degree need a separate
argument: such a variable is not in the positive even part unless it is zero, so its positive
divided powers vanish and lie in the range for that reason rather than by transport along `π`.

## References

* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
* [Stacks Project, Tag 09PS](https://stacks.math.columbia.edu/tag/09PS)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w z

attribute [local instance] GradedDPAlgebra.ring GradedDPAlgebra.algebra
  GradedDPAlgebra.graded GradedDPAlgebra.strict

attribute [local instance] gradedLimitGradedAlgebra gradedLimitStrictlyGradedComm

section Lift

variable {R' : Type u} {R : Type v} {A : Type w} {σ : Type z}
  [CommRing R'] [CommRing R] [Ring A] [Algebra R A]
  (q : R' →+* R) {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
  {γ : DividedPowerStructure 𝒜} {ι : MvPolynomial σ R →ₐ[R] A}
  (hpoly : GradedDividedPowerPolynomial 𝒜 γ ι)

/-- The degree-zero base of the tower: the polynomial ring `R'[xᵢ]` graded in degree zero,
placed in the universe in which the tower is built.

The last two type arguments are not used. They are there to fix that universe, which must
contain the universes of `R`, of `A` and of `σ` as well as that of `R'`: every stage of the
tower lies in one universe, and the universe of a stage is the join of the base ring's, the
previous stage's, the index set's and the target's. -/
public noncomputable abbrev liftBase (R' : Type u) (σ : Type z) (_R : Type v) (_A : Type w)
    [CommRing R'] : GradedDPAlgebra.{u, max u v w z} R' :=
  degreeZeroDPAlgebra R' (ULift.{max u v w z} (MvPolynomial σ R'))

/-- The polynomial ring `R'[xᵢ]` is the carrier of the base of the tower. -/
public noncomputable def liftBaseEquiv (R' : Type u) (σ : Type z) (R : Type v) (A : Type w)
    [CommRing R'] : (liftBase R' σ R A).carrier ≃ₐ[R'] MvPolynomial σ R' :=
  ULift.algEquiv

/-- The variables of the lifted algebra: those of `A`, moved into the universe in which the
tower lives. -/
public abbrev liftIndex (n : ℕ) : Type (max v w z) := ULift.{max v z} (hpoly.indices n)

/-- The `n`-th stage of the tower lifting `A`. -/
public noncomputable abbrev liftTowerStage (n : ℕ) : GradedDPAlgebra.{u, max u v w z} R' :=
  towerStage.{u, max v w z, w} (liftBase R' σ R A) (liftIndex hpoly) n

/-- The morphism from the `n`-th stage of the tower lifting `A` to the next. -/
public noncomputable abbrev liftTowerStep (n : ℕ) :
    GradedDPHom (liftTowerStage (R' := R') hpoly n) (liftTowerStage (R' := R') hpoly (n + 1)) :=
  towerStep.{u, max v w z, w} (liftBase R' σ R A) (liftIndex hpoly) n

/-- The variables of degree `n + 1` of the tower lifting `A`, as elements of its stage
`n + 1`. -/
public noncomputable abbrev liftTowerGenerator (n : ℕ) (j : liftIndex hpoly n) :
    (liftTowerStage (R' := R') hpoly (n + 1)).carrier :=
  towerGenerator.{u, max v w z, w} (liftBase R' σ R A) (liftIndex hpoly) n j

/-- The lifted algebra `B`: the divided power polynomial algebra over `R'[xᵢ]` with the same
variables in each degree as `A` has. -/
public noncomputable abbrev liftAlgebra : GradedDPAlgebra.{u, max u v w z} R' :=
  towerColimit.{u, max v w z, w} (liftBase R' σ R A) (liftIndex hpoly)

/-- The coefficient morphism of the lifted algebra: the inclusion of `R'[xᵢ]`. -/
public noncomputable abbrev liftCoefficientHom :
    GradedDPHom (liftBase R' σ R A) (liftAlgebra (R' := R') hpoly) :=
  towerCoefficient.{u, max v w z, w} (liftBase R' σ R A) (liftIndex hpoly)

/-- The variables of the lifted algebra. -/
public noncomputable abbrev liftVariable (n : ℕ) (j : hpoly.indices n) :
    (liftAlgebra (R' := R') hpoly).carrier :=
  towerVariable.{u, max v w z, w} (liftBase R' σ R A) (liftIndex hpoly) n (ULift.up j)

/-- Each variable of the lifted algebra is homogeneous of its prescribed degree. -/
public theorem liftVariable_mem (n : ℕ) (j : hpoly.indices n) :
    liftVariable (R' := R') hpoly n j ∈ (liftAlgebra (R' := R') hpoly).grade (n + 1) :=
  towerVariable_mem.{u, max v w z, w} (liftBase R' σ R A) (liftIndex hpoly) n
    (ULift.up.{max v z} j)

/-- Each step of the tower lifting `A` is a set-variable divided power extension in the sense of
`DividedPowers.TateResolution.IsSetVariableExtension`. This is the hypothesis under which a
graded derivation of a stage extends across the step. -/
public theorem liftTowerStage_isSetVariableExtension (n : ℕ) :
    IsSetVariableExtension (liftTowerStage (R' := R') hpoly n).grade
      (liftTowerStage (R' := R') hpoly n).gamma
      (liftTowerStage (R' := R') hpoly (n + 1)).grade
      (liftTowerStage (R' := R') hpoly (n + 1)).gamma
      (liftTowerStep (R' := R') hpoly n).hom (liftTowerGenerator (R' := R') hpoly n)
      (n + 1) n.succ_pos :=
  towerStage_isSetVariableExtension.{u, max v w z, w} (liftBase R' σ R A) (liftIndex hpoly) n

/-- The base morphism of the comparison: the polynomial ring `R'[xᵢ]` maps to `A` by reducing
coefficients along `q` and then applying the presentation of `A`. The grading and divided power
conditions are vacuous, the base having nothing in positive degree. -/
public noncomputable def liftBaseHom :
    GradedDPHom (liftBase R' σ R A) (restrictBaseDPAlgebra q 𝒜 γ) :=
  degreeZeroDPHom R' (ULift.{max u v w z} (MvPolynomial σ R'))
    (restrictBaseDPAlgebra q 𝒜 γ)
    { toRingHom := (ι : MvPolynomial σ R →+* A).comp
        ((MvPolynomial.map q).comp (liftBaseEquiv R' σ R A).toRingHom)
      commutes' := by
        intro r
        change ι (MvPolynomial.map q (liftBaseEquiv R' σ R A (algebraMap R' _ r))) =
          algebraMap R A (q r)
        rw [AlgEquiv.commutes, MvPolynomial.algebraMap_eq, MvPolynomial.map_C,
          ← MvPolynomial.algebraMap_eq, ι.commutes] }
    (fun p => hpoly.coefficient_mem (MvPolynomial.map q (liftBaseEquiv R' σ R A p)))

/-- The base morphism reduces the coefficients of a polynomial along `q` and applies `ι`. -/
@[simp]
public theorem liftBaseHom_apply (p : (liftBase R' σ R A).carrier) :
    (liftBaseHom q hpoly).hom p = ι (MvPolynomial.map q (liftBaseEquiv R' σ R A p)) := rfl

/-- The universal property pinning down the comparison morphism: the colimit of the tower maps
to `A` by the base morphism on `R'[xᵢ]` and by matching up the variables. -/
public theorem liftHom_spec :
    ∃! F : GradedDPHom (liftAlgebra (R' := R') hpoly) (restrictBaseDPAlgebra q 𝒜 γ),
      (∀ p : (liftBase R' σ R A).carrier,
          F.hom ((liftCoefficientHom (R' := R') hpoly).hom p) = (liftBaseHom q hpoly).hom p) ∧
        (∀ (n : ℕ) (j : liftIndex hpoly n),
          F.hom (towerVariable.{u, max v w z, w} (liftBase R' σ R A) (liftIndex hpoly) n j) =
            hpoly.generator ⟨n, j.down⟩) :=
  towerColimit_existsUnique_lift.{u, max v w z, w} (liftBase R' σ R A) (liftIndex hpoly)
    (restrictBaseDPAlgebra q 𝒜 γ) (liftBaseHom q hpoly)
    (fun n j => hpoly.generator ⟨n, j.down⟩)
    (fun n j => hpoly.generator_mem ⟨n, j.down⟩)

/-- The comparison morphism `B → A` of the lift: the morphism out of the colimit of the tower
determined by the base morphism and by sending each variable of `B` to the corresponding
variable of `A`. -/
public noncomputable def liftHom :
    GradedDPHom (liftAlgebra (R' := R') hpoly) (restrictBaseDPAlgebra q 𝒜 γ) :=
  (liftHom_spec q hpoly).choose

/-- The comparison morphism restricts to the base morphism on `R'[xᵢ]`. -/
public theorem liftHom_coefficient (p : (liftBase R' σ R A).carrier) :
    (liftHom q hpoly).hom ((liftCoefficientHom (R' := R') hpoly).hom p) =
      (liftBaseHom q hpoly).hom p :=
  (liftHom_spec q hpoly).choose_spec.1.1 p

/-- The comparison morphism sends each variable of `B` to the corresponding variable of `A`. -/
public theorem liftHom_variable (n : ℕ) (j : hpoly.indices n) :
    (liftHom q hpoly).hom (liftVariable (R' := R') hpoly n j) = hpoly.generator ⟨n, j⟩ :=
  (liftHom_spec q hpoly).choose_spec.1.2 n ⟨j⟩

/-- The comparison morphism, as a ring homomorphism. This is the `π` of Tag 09PS. -/
public noncomputable def liftRingHom : (liftAlgebra (R' := R') hpoly).carrier →+* A :=
  (liftHom q hpoly).hom.toRingHom

/-- The ring homomorphism `π` is the underlying map of the comparison morphism. -/
@[simp]
public theorem liftRingHom_apply (b : (liftAlgebra (R' := R') hpoly).carrier) :
    liftRingHom q hpoly b = (liftHom q hpoly).hom b := rfl

/-- The comparison morphism carries the structure map of `B` to that of `A` through `q`. This is
the clause `map_algebraMap` of `DividedPowers.TateResolution.IsSquareZeroLift`. -/
public theorem liftHom_algebraMap (r : R') :
    liftRingHom q hpoly (algebraMap R' (liftAlgebra (R' := R') hpoly).carrier r) =
      algebraMap R A (q r) :=
  (liftHom q hpoly).hom.commutes r

/-- The comparison morphism preserves homogeneous degrees. This is the clause `map_mem_grade` of
`DividedPowers.TateResolution.IsSquareZeroLift`. -/
public theorem liftHom_mem_grade (n : ℕ) (b : (liftAlgebra (R' := R') hpoly).carrier)
    (hb : b ∈ (liftAlgebra (R' := R') hpoly).grade n) : liftRingHom q hpoly b ∈ 𝒜 n :=
  (liftHom q hpoly).map_grade n b hb

/-- The comparison morphism, on a variable. -/
@[simp]
public theorem liftRingHom_variable (n : ℕ) (j : hpoly.indices n) :
    liftRingHom q hpoly (liftVariable (R' := R') hpoly n j) = hpoly.generator ⟨n, j⟩ :=
  liftHom_variable q hpoly n j

/-- The comparison morphism, on a coefficient. -/
public theorem liftRingHom_coefficient (p : MvPolynomial σ R') :
    liftRingHom q hpoly ((liftCoefficientHom (R' := R') hpoly).hom
        ((liftBaseEquiv R' σ R A).symm p)) = ι (MvPolynomial.map q p) := by
  rw [liftRingHom_apply, liftHom_coefficient, liftBaseHom_apply, AlgEquiv.apply_symm_apply]

/-- The comparison morphism is a morphism of divided powers. This is the clause `map_dpow` of
`DividedPowers.TateResolution.IsDividedPowerSquareZeroLift`. -/
public theorem liftHom_dpow (n : ℕ) (b : (liftAlgebra (R' := R') hpoly).carrier)
    (hb : b ∈ positiveEvenPart (liftAlgebra (R' := R') hpoly).grade) :
    γ.dpow n (liftRingHom q hpoly b) =
      liftRingHom q hpoly ((liftAlgebra (R' := R') hpoly).gamma.dpow n b) :=
  (liftHom q hpoly).map_dpow n b hb

/-- The comparison morphism is surjective. This is the clause `surjective` of
`DividedPowers.TateResolution.IsSquareZeroLift`.

Its range is a subring of `A` containing the image of every coefficient — because `q` is
surjective, so is the reduction of coefficients — and every variable, and it is closed under the
divided powers of a variable of positive even degree. A variable of odd degree is not in the
positive even part unless it is zero, so its positive divided powers vanish and lie in the range
for that reason instead. Those are exactly the generators of the finite variable stages of the
presentation of `A`, which cover `A`. -/
public theorem liftHom_surjective (hq : Function.Surjective q) :
    Function.Surjective (liftRingHom q hpoly) := by
  intro x
  rw [← RingHom.mem_range]
  obtain ⟨T, hT⟩ := hpoly.finite_support x
  refine (?_ : finiteVariableStage γ ι hpoly.generator T ≤ (liftRingHom q hpoly).range) hT
  refine Subring.closure_le.2 ?_
  rintro y (⟨p, rfl⟩ | ⟨⟨n, jn⟩, -, hy⟩)
  · obtain ⟨p', rfl⟩ := MvPolynomial.map_surjective q hq p
    exact RingHom.mem_range.2
      ⟨(liftCoefficientHom (R' := R') hpoly).hom ((liftBaseEquiv R' σ R A).symm p'),
        liftRingHom_coefficient q hpoly p'⟩
  · rcases hy with rfl | ⟨m, rfl⟩
    · exact RingHom.mem_range.2
        ⟨liftVariable (R' := R') hpoly n jn, liftRingHom_variable q hpoly n jn⟩
    · by_cases hpe : hpoly.generator ⟨n, jn⟩ ∈ positiveEvenPart 𝒜
      · rcases positiveEven_homogeneous_eq_zero_or_grade 𝒜
            (hpoly.generator_mem ⟨n, jn⟩) hpe with hz | ⟨e, he⟩
        · rcases m with _ | m
          · rw [hz, γ.dpow_zero (Submodule.zero_mem _)]
            exact one_mem _
          · rw [hz, γ.dpow_zero_eq_zero (Nat.succ_ne_zero m)]
            exact zero_mem _
        · have hvar : liftVariable (R' := R') hpoly n jn ∈
              positiveEvenPart (liftAlgebra (R' := R') hpoly).grade :=
            mem_positiveEvenPart_of_mem_grade _ (Nat.succ_pos e)
              (he ▸ liftVariable_mem (R' := R') hpoly n jn)
          refine RingHom.mem_range.2
            ⟨(liftAlgebra (R' := R') hpoly).gamma.dpow m (liftVariable (R' := R') hpoly n jn),
              ?_⟩
          rw [← liftHom_dpow q hpoly m _ hvar, liftRingHom_variable]
      · rw [γ.dpow_null hpe]
        exact zero_mem _

end Lift

end DividedPowers.TateResolution

end
