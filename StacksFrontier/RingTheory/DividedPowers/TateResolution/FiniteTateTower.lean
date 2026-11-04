module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.NoetherianCycles
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.StagePresentation
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.TateColimitDifferential

/-! # Tate's degreewise finite tower

`StacksFrontier/RingTheory/DividedPowers/TateResolution/TateTower.lean` builds Tate's dependent
`ω`-tower in the form the *existence* half of Tag 09PN needs: the variables adjoined in degree
`n + 1` are indexed by **all** the cycles of degree `n` of the stage `n`, so the differential of a
new variable is its own index and acyclicity costs no homology computation. The price is that the
index sets are as large as the stage, and the resulting resolution is not degreewise finite.

The *finiteness* half of Tag 09PN asks for a resolution with finitely many generators in each
degree, over a Noetherian ring and for an algebra of finite type. That is a different tower: at
each step one adjoins a **finite** family of variables killing a finite family of cycles that
generates all of them over the coefficient algebra. This file builds that tower.

The two inputs are already available. Each finite stage of a chain of set-variable extensions is a
graded divided power polynomial algebra over the base of the chain, by
`DividedPowers.TateResolution.chainStagePresentation`; and over a Noetherian coefficient algebra
the degree-`m` cycles of such an algebra with finitely many variables in each degree are spanned by
a finite family, by `DividedPowers.TateResolution.exists_finite_spanning_cycles`. What this file
adds is the recursion that interleaves them, and the acyclicity argument that replaces
`DividedPowers.TateResolution.exists_tateCycle_eq`: a cycle is no longer *prescribed*, it is a
combination of prescribed cycles with coefficients of degree zero, and such a combination is the
boundary of the corresponding combination of the killing variables.

The recursion is made total before anything is proved about it. The family adjoined above a stage
is `DividedPowers.TateResolution.chosenCycleFinset`, which is a spanning family when one exists and
the *empty* family otherwise. So the tower is a plain recursion on `ℕ` with no proof carried along,
and — this is the point of the empty fallback — its index sets are finite **unconditionally**. That
in turn makes the presentation of every stage have finitely many variables in each degree, hence
its cycles finitely generated over a Noetherian base, hence the fallback never taken. Carrying the
spanning property through the recursion instead would need the presentation of the stage inside the
invariant, and the presentation is only available once the whole chain is.

## Main definitions

* `DividedPowers.TateResolution.HasFiniteSpanningCycles` — a finite family of homogeneous cycles of
  a degree spanning all of them with coefficients of degree zero.
* `DividedPowers.TateResolution.chosenCycleFinset` — the family adjoined above a stage: a spanning
  one when one exists, and the empty family otherwise.
* `DividedPowers.TateResolution.finiteTateStage` — the `n`-th stage of the degreewise finite tower,
  with `DividedPowers.TateResolution.finiteTateAlgebra`,
  `DividedPowers.TateResolution.finiteTateDifferential`,
  `DividedPowers.TateResolution.finiteTateStep`,
  `DividedPowers.TateResolution.finiteTateIndex`,
  `DividedPowers.TateResolution.finiteTateCycle` and
  `DividedPowers.TateResolution.finiteTateGenerator` its components.
* `DividedPowers.TateResolution.finiteTateBase` — the base of the tower: a commutative algebra
  concentrated in degree zero with the zero differential and a prescribed *finite* family of
  degree-zero cycles.
* `DividedPowers.TateResolution.finiteTateColimit` — the colimit of the tower, with
  `DividedPowers.TateResolution.finiteTateColimitDifferential` its differential.

## Main results

* `DividedPowers.TateResolution.exists_boundary_of_gradeZero_combination` — a combination with
  coefficients of degree zero of cycles killed by variables is a boundary. This is the acyclicity
  clause that replaces "every cycle is prescribed".
* `DividedPowers.TateResolution.finite_finiteTateIndex` — the tower adjoins finitely many variables
  in each degree as soon as its base does.
* `DividedPowers.TateResolution.hasFiniteSpanningCycles_finiteTateStage` — over a Noetherian
  coefficient ring every degree of every stage has a finite spanning family of cycles, so the
  empty fallback of `chosenCycleFinset` is never taken.
* `DividedPowers.TateResolution.exists_finiteTateColimit_boundary_of_cycle` — the colimit is
  acyclic in positive degrees, and
  `DividedPowers.TateResolution.exists_finiteTateColimit_boundary_of_combination` — every
  combination with degree-zero coefficients of the cycles prescribed at a stage is a boundary,
  which in degree zero is exactness at the base.

## Implementation notes

Every stage lives in the single universe `max u v`, for the reason recorded in `TateTower.lean`:
the carrier of a stage is produced by the construction and the next stage is built out of it.

The coefficients of a combination are taken in degree zero of the stage itself rather than in the
coefficient algebra `P`. The two agree — nothing of degree zero is adjoined by any step — but the
degree-zero spelling needs no `Algebra P` instance on the stage, so the tower can be defined and
its acyclicity proved with no reference to `P` at all. `P` enters only in
`hasFiniteSpanningCycles_finiteTateStage`, where `Algebra P` is supplied by
`DividedPowers.TateResolution.coefficientAlgebra`.

## References

* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
* [Stacks Project, Tag 09PM](https://stacks.math.columbia.edu/tag/09PM)
* [Stacks Project, Tag 0F4I](https://stacks.math.columbia.edu/tag/0F4I)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w y

attribute [local instance] GradedDPAlgebra.ring GradedDPAlgebra.algebra
  GradedDPAlgebra.graded GradedDPAlgebra.strict

attribute [local instance] gradedLimitGradedAlgebra gradedLimitStrictlyGradedComm

attribute [local instance] TateDatum.dga TateDatum.compatible

section Boundary

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
  (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (d : A →ₗ[R] A)
  [IsDifferentialGradedAlgebra Aᵢ d]

/-- **The differential is linear over coefficients of degree zero.** The Leibniz rule applied to a
degree-zero factor has one term killed by the differential's vanishing in degree zero, and the sign
of the surviving term is `(-1) ^ 0`. -/
public theorem map_mul_of_mem_grade_zero {m : ℕ} {p x : A} (hp : p ∈ Aᵢ 0) (hx : x ∈ Aᵢ m) :
    d (p * x) = p * d x := by
  rw [IsDifferentialGradedAlgebra.leibniz (𝒜 := Aᵢ) (d := d) hp hx,
    IsDifferentialGradedAlgebra.d_grade_zero (𝒜 := Aᵢ) (d := d) hp]
  simp

/-- **A combination with coefficients of degree zero of cycles killed by variables is a
boundary.** If the variable `T j` of degree `n + 1` has `v j` for boundary, then the boundary of
the corresponding combination of the `T j` is the combination of the `v j`, by linearity of the
differential over degree-zero coefficients, and that combination is homogeneous of degree `n + 1`.

So a family of variables whose prescribed cycles *span* the cycles of a degree kills all of them.
This is what makes the degreewise finite tower acyclic; the existence half of Tag 09PN instead
prescribes every cycle individually, which is what costs it degreewise finiteness. -/
@[stacks 09PN "a spanning family kills every cycle of its degree, degree-zero coefficients"]
public theorem exists_boundary_of_gradeZero_combination {J : Type y} (v T : J → A) (n : ℕ)
    (hT : ∀ j : J, T j ∈ Aᵢ (n + 1)) (hdT : ∀ j : J, d (T j) = v j)
    (s : Finset J) (c : J → A) (hc : ∀ j : J, c j ∈ Aᵢ 0) :
    ∃ b : A, b ∈ Aᵢ (n + 1) ∧ d b = ∑ j ∈ s, c j * v j := by
  refine ⟨∑ j ∈ s, c j * T j, Submodule.sum_mem _ fun j _ => ?_, ?_⟩
  · simpa using SetLike.GradedMul.mul_mem (hc j) (hT j)
  · rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [map_mul_of_mem_grade_zero Aᵢ d (hc j) (hT j), hdT j]

end Boundary

section Choice

variable {R : Type u} [CommRing R]

/-- **A finite family of degree-`m` cycles spanning all of them with coefficients of degree
zero.** This is the condition under which the variables adjoined above a stage in degree `m + 1`
may be finite in number and still kill every cycle of degree `m`.

The coefficients are taken in degree zero of the datum itself rather than in a coefficient algebra
`P`: nothing of degree zero is adjoined by any step of the tower, so the two are the same
condition, and this spelling needs no `Algebra P` instance. -/
public def HasFiniteSpanningCycles (C : TateDatum.{u, v} R) (m : ℕ) : Prop :=
  ∃ s : Finset C.algebra.carrier,
    (∀ y ∈ s, y ∈ C.algebra.grade m ∧ C.differential y = 0) ∧
      ∀ x : C.algebra.carrier, x ∈ C.algebra.grade m → C.differential x = 0 →
        ∃ c : C.algebra.carrier → C.algebra.carrier,
          (∀ y : C.algebra.carrier, c y ∈ C.algebra.grade 0) ∧ ∑ y ∈ s, c y * y = x

open Classical in
/-- **The family of degree-`m` cycles that the degreewise finite tower kills above a datum**: a
finite spanning family when one exists, and the empty family otherwise.

The fallback is never taken — over a Noetherian coefficient ring a spanning family always exists,
by `DividedPowers.TateResolution.hasFiniteSpanningCycles_finiteTateStage` — but making the choice
total is what lets the tower be *defined* before anything is proved about it, and taking the
fallback to be empty rather than the set of all cycles is what makes the index sets of the tower
finite unconditionally. That finiteness is in turn the hypothesis under which the spanning family
is produced, so the two could not be established in the other order. -/
public noncomputable def chosenCycleFinset (C : TateDatum.{u, v} R) (m : ℕ) :
    Finset C.algebra.carrier :=
  if h : HasFiniteSpanningCycles C m then h.choose else ∅

/-- Every member of the chosen family is a cycle, homogeneous of its degree. -/
public theorem mem_chosenCycleFinset {C : TateDatum.{u, v} R} {m : ℕ} {y : C.algebra.carrier}
    (hy : y ∈ chosenCycleFinset C m) : y ∈ C.algebra.grade m ∧ C.differential y = 0 := by
  classical
  by_cases h : HasFiniteSpanningCycles C m
  · simp only [chosenCycleFinset, dite_eq_left h] at hy
    exact h.choose_spec.1 y hy
  · simp only [chosenCycleFinset, dite_eq_right h, Finset.notMem_empty] at hy

/-- **The chosen family spans the cycles of its degree** whenever a spanning family exists: every
degree-`m` cycle is a combination of its members with coefficients of degree zero. -/
public theorem exists_gradeZero_combination_of_chosenCycleFinset {C : TateDatum.{u, v} R}
    {m : ℕ} (h : HasFiniteSpanningCycles C m) {x : C.algebra.carrier}
    (hx : x ∈ C.algebra.grade m) (hdx : C.differential x = 0) :
    ∃ c : C.algebra.carrier → C.algebra.carrier,
      (∀ y : C.algebra.carrier, c y ∈ C.algebra.grade 0) ∧
        ∑ y ∈ chosenCycleFinset C m, c y * y = x := by
  classical
  simp only [chosenCycleFinset, dite_eq_left h]
  exact h.choose_spec.2 x hx hdx

end Choice

section Tower

variable {R : Type u} [CommRing R]

/-- **One step of the degreewise finite tower**: the stage above a given one, with the chosen
finite family of its degree-`n + 1` cycles prescribed as the family to be killed next.

The underlying datum is the same `DividedPowers.TateResolution.tateStepDatum` as for the tower of
the existence half, and definitionally so, which is what lets every statement about one step of
that tower be reused verbatim. Only the family prescribed for the *next* step differs. -/
public noncomputable def finiteTateNext {n : ℕ} (B : TateStageData.{u, v} R n) :
    TateStageData.{u, v} R (n + 1) where
  datum := tateStepDatum B
  kill := {y : (tateStepDatum B).algebra.carrier //
    y ∈ chosenCycleFinset (tateStepDatum B) (n + 1)}
  value := Subtype.val
  value_mem := fun j => (mem_chosenCycleFinset j.2).1
  value_cycle := fun j => (mem_chosenCycleFinset j.2).2

/-- **The family prescribed above any stage of the degreewise finite tower is finite.** This holds
with no hypothesis whatever, which is the point of the empty fallback in
`DividedPowers.TateResolution.chosenCycleFinset`: the finiteness of the index sets is what the
spanning family is later produced *from*. -/
public theorem finite_finiteTateNext_kill {n : ℕ} (B : TateStageData.{u, v} R n) :
    Finite (finiteTateNext B).kill :=
  inferInstanceAs (Finite {y : (tateStepDatum B).algebra.carrier //
    y ∈ chosenCycleFinset (tateStepDatum B) (n + 1)})

/-- **The `n`-th stage of the degreewise finite tower** over the base `A₀`: the base with, for each
`k < n`, a variable of degree `k + 1` adjoined for each member of the finite family chosen at the
stage `k`. -/
public noncomputable def finiteTateStage (A₀ : TateStageData.{u, v} R 0) :
    (n : ℕ) → TateStageData.{u, v} R n
  | 0 => A₀
  | n + 1 => finiteTateNext (finiteTateStage A₀ n)

variable (A₀ : TateStageData.{u, v} R 0)

/-- The stage zero of the tower is the prescribed base. -/
public theorem finiteTateStage_zero : finiteTateStage A₀ 0 = A₀ := rfl

/-- The stage `n + 1` of the tower is obtained from the stage `n` by killing its chosen family. -/
public theorem finiteTateStage_succ (n : ℕ) :
    finiteTateStage A₀ (n + 1) = finiteTateNext (finiteTateStage A₀ n) := rfl

/-- The `n`-th stage of the tower, as a graded divided power algebra. -/
public noncomputable abbrev finiteTateAlgebra (n : ℕ) : GradedDPAlgebra.{u, max u v} R :=
  (finiteTateStage A₀ n).datum.algebra

/-- The differential of the `n`-th stage of the tower. -/
public noncomputable abbrev finiteTateDifferential (n : ℕ) :
    (finiteTateAlgebra A₀ n).carrier →ₗ[R] (finiteTateAlgebra A₀ n).carrier :=
  (finiteTateStage A₀ n).datum.differential

/-- The index set of the variables of degree `n + 1` of the tower: the finite family chosen at the
stage `n`. -/
public abbrev finiteTateIndex (n : ℕ) : Type (max u v) := (finiteTateStage A₀ n).kill

/-- The degree-`n` cycle of the `n`-th stage that the variable indexed by `j` kills. -/
public noncomputable abbrev finiteTateCycle (n : ℕ) (j : finiteTateIndex A₀ n) :
    (finiteTateAlgebra A₀ n).carrier := (finiteTateStage A₀ n).value j

/-- The morphism from the `n`-th stage of the tower to the next. -/
public noncomputable def finiteTateStep (n : ℕ) :
    GradedDPHom (finiteTateAlgebra A₀ n) (finiteTateAlgebra A₀ (n + 1)) :=
  tateStepHom (finiteTateStage A₀ n)

/-- The variables of degree `n + 1` of the tower, as elements of its stage `n + 1`. -/
public noncomputable def finiteTateGenerator (n : ℕ) (j : finiteTateIndex A₀ n) :
    (finiteTateAlgebra A₀ (n + 1)).carrier :=
  tateStepGenerator (finiteTateStage A₀ n) j

/-- **The tower adjoins finitely many variables in each degree** as soon as its base does. -/
public theorem finite_finiteTateIndex (hA₀ : Finite A₀.kill) :
    ∀ n : ℕ, Finite (finiteTateIndex A₀ n)
  | 0 => hA₀
  | n + 1 => finite_finiteTateNext_kill (finiteTateStage A₀ n)

/-- Each step of the tower is a set-variable divided power extension of degree `n + 1`. -/
public theorem finiteTateStage_isSetVariableExtension (n : ℕ) :
    IsSetVariableExtension (finiteTateAlgebra A₀ n).grade (finiteTateAlgebra A₀ n).gamma
      (finiteTateAlgebra A₀ (n + 1)).grade (finiteTateAlgebra A₀ (n + 1)).gamma
      (finiteTateStep A₀ n).hom (finiteTateGenerator A₀ n) (n + 1) n.succ_pos :=
  tateStepHom_isSetVariableExtension (finiteTateStage A₀ n)

/-- Each step of the tower commutes with the differentials of its two stages. -/
public theorem finiteTateStep_differential (n : ℕ) (a : (finiteTateAlgebra A₀ n).carrier) :
    finiteTateDifferential A₀ (n + 1) ((finiteTateStep A₀ n).hom a) =
      (finiteTateStep A₀ n).hom (finiteTateDifferential A₀ n a) :=
  tateStepHom_differential (finiteTateStage A₀ n) a

/-- The differential of a variable of degree `n + 1` is the degree-`n` cycle it kills. -/
public theorem finiteTateGenerator_differential (n : ℕ) (j : finiteTateIndex A₀ n) :
    finiteTateDifferential A₀ (n + 1) (finiteTateGenerator A₀ n j) =
      (finiteTateStep A₀ n).hom (finiteTateCycle A₀ n j) :=
  tateStepGenerator_differential (finiteTateStage A₀ n) j

/-- Each cycle prescribed at the `n`-th stage is homogeneous of degree `n`. -/
public theorem finiteTateCycle_mem (n : ℕ) (j : finiteTateIndex A₀ n) :
    finiteTateCycle A₀ n j ∈ (finiteTateAlgebra A₀ n).grade n :=
  (finiteTateStage A₀ n).value_mem j

/-- Each cycle prescribed at the `n`-th stage is indeed a cycle. -/
public theorem finiteTateCycle_cycle (n : ℕ) (j : finiteTateIndex A₀ n) :
    finiteTateDifferential A₀ n (finiteTateCycle A₀ n j) = 0 :=
  (finiteTateStage A₀ n).value_cycle j

/-- Every stage of the tower is a differential graded algebra. -/
public theorem finiteTateDga (n : ℕ) :
    IsDifferentialGradedAlgebra (finiteTateAlgebra A₀ n).grade (finiteTateDifferential A₀ n) :=
  (finiteTateStage A₀ n).datum.dga

/-- The divided powers of every stage of the tower are compatible with its differential. -/
public theorem finiteTateCompatible (n : ℕ) :
    IsCompatibleWithDifferential (finiteTateAlgebra A₀ n).gamma (finiteTateDifferential A₀ n) :=
  (finiteTateStage A₀ n).datum.compatible

/-- Each step of the tower is injective: it is the coefficient morphism of a set-variable
extension. -/
public theorem finiteTateStep_injective (n : ℕ) :
    Function.Injective (finiteTateStep A₀ n).hom :=
  (finiteTateStage_isSetVariableExtension A₀ n).coefficient_injective

/-- Each variable of degree `n + 1` is homogeneous of degree `n + 1`. -/
public theorem finiteTateGenerator_mem (n : ℕ) (j : finiteTateIndex A₀ n) :
    finiteTateGenerator A₀ n j ∈ (finiteTateAlgebra A₀ (n + 1)).grade (n + 1) :=
  (finiteTateStage_isSetVariableExtension A₀ n).generator_mem j

end Tower

section Base

variable {R : Type u} [CommRing R] (P : Type (max u v)) [CommRing P] [Algebra R P]
  (s₀ : Finset P)

/-- **The base of the degreewise finite tower.** A commutative `R`-algebra `P` concentrated in
degree zero, carrying the zero differential, with a prescribed *finite* family `s₀` of degree-zero
cycles to be killed by the variables of degree one.

Where the existence half of Tag 09PN takes the whole of an ideal `I` as the family to be killed,
the finiteness half takes a finite generating family of `I`: every element of `I` is then a
combination of the family with coefficients in `P`, which lies in degree zero, so
`DividedPowers.TateResolution.exists_boundary_of_gradeZero_combination` still makes it a
boundary. -/
public noncomputable def finiteTateBase : TateStageData.{u, v} R 0 where
  datum := tateDatumOfZeroDifferential (degreeZeroDPAlgebra R P)
  kill := {p : P // p ∈ s₀}
  value := Subtype.val
  value_mem := fun _ => mem_degreeZeroGrade_zero R P _
  value_cycle := fun _ => rfl

/-- The base of the degreewise finite tower prescribes finitely many degree-one variables. -/
public theorem finite_finiteTateBase_kill :
    Finite (finiteTateBase.{u, v} (R := R) P s₀).kill :=
  inferInstanceAs (Finite {p : P // p ∈ s₀})

/-- The algebra of the base of the tower is `P` concentrated in degree zero. -/
public theorem finiteTateBase_algebra :
    finiteTateAlgebra (finiteTateBase.{u, v} (R := R) P s₀) 0 = degreeZeroDPAlgebra R P := rfl

/-- The differential of the base of the tower is zero. -/
public theorem finiteTateBase_differential :
    finiteTateDifferential (finiteTateBase.{u, v} (R := R) P s₀) 0 = 0 := rfl

/-- Every element of the base of the tower is homogeneous of degree zero. -/
public theorem finiteTateBase_mem_grade_zero
    (p : (finiteTateAlgebra (finiteTateBase.{u, v} (R := R) P s₀) 0).carrier) :
    p ∈ (finiteTateAlgebra (finiteTateBase.{u, v} (R := R) P s₀) 0).grade 0 :=
  mem_degreeZeroGrade_zero R P p

/-- **A morphism out of the base of the tower is no more than an algebra homomorphism landing in
degree zero.** This is the hypothesis `hbase` of
`DividedPowers.TateResolution.chainStagePresentation`, which the stepwise mapping property has to
be started off with. -/
public theorem finiteTateBase_exists_gradedDPHom (E : GradedDPAlgebra.{u, max u v} R)
    (f : (finiteTateAlgebra (finiteTateBase.{u, v} (R := R) P s₀) 0).carrier →ₐ[R] E.carrier)
    (hf : ∀ p : (finiteTateAlgebra (finiteTateBase.{u, v} (R := R) P s₀) 0).carrier,
      f p ∈ E.grade 0) :
    ∃ F : GradedDPHom (finiteTateAlgebra (finiteTateBase.{u, v} (R := R) P s₀) 0) E,
      ∀ p : (finiteTateAlgebra (finiteTateBase.{u, v} (R := R) P s₀) 0).carrier, F.hom p = f p :=
  ⟨degreeZeroDPHom R P E f hf, fun _ => rfl⟩

end Base

section Noetherian

variable {R : Type u} [CommRing R] (P : Type (max u v)) [CommRing P] [Algebra R P]
  (s₀ : Finset P)

/-- **Over a Noetherian coefficient ring every degree of every stage of the degreewise finite
tower has a finite spanning family of cycles**, so the empty fallback of
`DividedPowers.TateResolution.chosenCycleFinset` is never taken and the tower really does kill
every cycle.

This is where the two ingredients meet. The stage `N` is a graded divided power polynomial
algebra over `P` by `DividedPowers.TateResolution.chainStagePresentation`, with finitely many
variables in each degree because the index sets of the tower are finite unconditionally; so each of
its homogeneous pieces is a finitely generated `P`-module by
`DividedPowers.TateResolution.GradedDividedPowerPolynomial.fg_coefficientGrade`, and over the
Noetherian ring `P` the submodule of cycles is finitely generated too, which is
`DividedPowers.TateResolution.exists_finite_spanning_cycles`. Its coefficients lie in `P`, and the
coefficient morphism carries `P` into degree zero, which is the spelling
`DividedPowers.TateResolution.HasFiniteSpanningCycles` asks for. -/
@[stacks 09PN "finitely many variables suffice at each step over a Noetherian base"]
public theorem hasFiniteSpanningCycles_finiteTateStage [IsNoetherianRing P] (N m : ℕ) :
    HasFiniteSpanningCycles
      (finiteTateStage (finiteTateBase.{u, v} (R := R) P s₀) N).datum m := by
  classical
  let _ : CommRing
      (finiteTateAlgebra (finiteTateBase.{u, v} (R := R) P s₀) 0).carrier :=
    inferInstanceAs (CommRing P)
  have : IsNoetherianRing
      (finiteTateAlgebra (finiteTateBase.{u, v} (R := R) P s₀) 0).carrier :=
    inferInstanceAs (IsNoetherianRing P)
  have : ∀ i : ℕ, Finite (finiteTateIndex (finiteTateBase.{u, v} (R := R) P s₀) i) :=
    finite_finiteTateIndex (finiteTateBase.{u, v} (R := R) P s₀)
      (finite_finiteTateBase_kill P s₀)
  have : IsDifferentialGradedAlgebra
      (finiteTateAlgebra (finiteTateBase.{u, v} (R := R) P s₀) N).grade
      (finiteTateDifferential (finiteTateBase.{u, v} (R := R) P s₀) N) :=
    finiteTateDga (finiteTateBase.{u, v} (R := R) P s₀) N
  have h0 : ∀ p : (finiteTateAlgebra (finiteTateBase.{u, v} (R := R) P s₀) 0).carrier,
      chainStageCoefficient (finiteTateAlgebra (finiteTateBase.{u, v} (R := R) P s₀))
          (finiteTateStep (finiteTateBase.{u, v} (R := R) P s₀)) N p ∈
        (finiteTateAlgebra (finiteTateBase.{u, v} (R := R) P s₀) N).grade 0 := fun p =>
    (chainMap (finiteTateAlgebra (finiteTateBase.{u, v} (R := R) P s₀))
        (finiteTateStep (finiteTateBase.{u, v} (R := R) P s₀)) (Nat.zero_le N)).map_grade 0 p
      (finiteTateBase_mem_grade_zero P s₀ p)
  let _ : Algebra (finiteTateAlgebra (finiteTateBase.{u, v} (R := R) P s₀) 0).carrier
      (finiteTateAlgebra (finiteTateBase.{u, v} (R := R) P s₀) N).carrier :=
    coefficientAlgebra (finiteTateAlgebra (finiteTateBase.{u, v} (R := R) P s₀) N).grade
      (chainStageCoefficient (finiteTateAlgebra (finiteTateBase.{u, v} (R := R) P s₀))
        (finiteTateStep (finiteTateBase.{u, v} (R := R) P s₀)) N) h0
  let Q := chainStagePresentation
    (finiteTateAlgebra (finiteTateBase.{u, v} (R := R) P s₀))
    (finiteTateStep (finiteTateBase.{u, v} (R := R) P s₀))
    (finiteTateIndex (finiteTateBase.{u, v} (R := R) P s₀))
    (finiteTateGenerator (finiteTateBase.{u, v} (R := R) P s₀))
    (finiteTateStage_isSetVariableExtension (finiteTateBase.{u, v} (R := R) P s₀))
    (finiteTateBase_mem_grade_zero P s₀) (finiteTateBase_exists_gradedDPHom P s₀) N
  have : ∀ i : ℕ, Finite (Q.indices i) := fun i =>
    finite_chainStagePresentation_indices
      (finiteTateAlgebra (finiteTateBase.{u, v} (R := R) P s₀))
      (finiteTateStep (finiteTateBase.{u, v} (R := R) P s₀))
      (finiteTateIndex (finiteTateBase.{u, v} (R := R) P s₀))
      (finiteTateGenerator (finiteTateBase.{u, v} (R := R) P s₀))
      (finiteTateStage_isSetVariableExtension (finiteTateBase.{u, v} (R := R) P s₀))
      (finiteTateBase_mem_grade_zero P s₀) (finiteTateBase_exists_gradedDPHom P s₀) N i
  obtain ⟨s, hs, hspan⟩ := exists_finite_spanning_cycles
    (finiteTateAlgebra (finiteTateBase.{u, v} (R := R) P s₀) N).grade
    (finiteTateDifferential (finiteTateBase.{u, v} (R := R) P s₀) N) Q h0 (fun _ => rfl) m
  refine ⟨s, hs, fun x hx hdx => ?_⟩
  obtain ⟨c, hc⟩ := hspan x hx hdx
  refine ⟨fun y =>
    chainStageCoefficient (finiteTateAlgebra (finiteTateBase.{u, v} (R := R) P s₀))
      (finiteTateStep (finiteTateBase.{u, v} (R := R) P s₀)) N (c y),
    fun y => h0 (c y), ?_⟩
  rw [← hc]
  exact Finset.sum_congr rfl fun y _ => (Algebra.smul_def (c y) y).symm

end Noetherian

section Colimit

variable {R : Type u} [CommRing R] (A₀ : TateStageData.{u, v} R 0)

/-- **The colimit of the degreewise finite tower**: the graded divided power algebra obtained from
the base by adjoining, in every degree, a finite family of variables killing a spanning family of
the cycles of the degree below. -/
public noncomputable abbrev finiteTateColimit : GradedDPAlgebra.{u, max u v} R :=
  chainColimit (finiteTateAlgebra A₀) (finiteTateStep A₀)

/-- The morphism from the `n`-th stage of the tower into its colimit. -/
public noncomputable abbrev finiteTateInclusion (n : ℕ) :
    GradedDPHom (finiteTateAlgebra A₀ n) (finiteTateColimit A₀) :=
  chainColimitInclusion (finiteTateAlgebra A₀) (finiteTateStep A₀) n

/-- The coefficient morphism of the tower: the inclusion of its base into the colimit. -/
public noncomputable abbrev finiteTateCoefficient :
    GradedDPHom (finiteTateAlgebra A₀ 0) (finiteTateColimit A₀) :=
  finiteTateInclusion A₀ 0

/-- The variables of degree `n + 1` of the tower, as elements of its colimit. -/
public noncomputable def finiteTateVariable (n : ℕ) (j : finiteTateIndex A₀ n) :
    (finiteTateColimit A₀).carrier :=
  (finiteTateInclusion A₀ (n + 1)).hom (finiteTateGenerator A₀ n j)

/-- Each variable of the tower is homogeneous of its prescribed degree. -/
public theorem finiteTateVariable_mem (n : ℕ) (j : finiteTateIndex A₀ n) :
    finiteTateVariable A₀ n j ∈ (finiteTateColimit A₀).grade (n + 1) :=
  (finiteTateInclusion A₀ (n + 1)).map_grade (n + 1) _ (finiteTateGenerator_mem A₀ n j)

/-- Every structure morphism of the tower into its colimit is injective. -/
public theorem finiteTateInclusion_injective (n : ℕ) :
    Function.Injective (finiteTateInclusion A₀ n).hom :=
  chainColimitInclusion_injective (finiteTateAlgebra A₀) (finiteTateStep A₀)
    (finiteTateStep_injective A₀) n

/-- **The degree-`m` piece of the colimit is the image of the degree-`m` piece of the `m`-th
stage.** Every later step adjoins variables of degree greater than `m`. -/
public theorem exists_finiteTateInclusion_eq_of_mem_grade (m : ℕ)
    {x : (finiteTateColimit A₀).carrier} (hx : x ∈ (finiteTateColimit A₀).grade m) :
    ∃ y : (finiteTateAlgebra A₀ m).carrier, y ∈ (finiteTateAlgebra A₀ m).grade m ∧
      (finiteTateInclusion A₀ m).hom y = x :=
  exists_chainColimitInclusion_eq_of_mem_grade (finiteTateAlgebra A₀) (finiteTateStep A₀)
    (finiteTateGenerator A₀) (finiteTateStage_isSetVariableExtension A₀) m hx

/-- **The finite variable stages of the tower's variables cover its colimit.** -/
public theorem finiteTateColimit_finite_support (x : (finiteTateColimit A₀).carrier) :
    ∃ T : Finset (Σ n : ℕ, finiteTateIndex A₀ n),
      x ∈ finiteVariableStage (finiteTateColimit A₀).gamma (finiteTateCoefficient A₀).hom
        (fun j => finiteTateVariable A₀ j.1 j.2) T :=
  chainColimit_finite_support (finiteTateAlgebra A₀) (finiteTateStep A₀) (finiteTateIndex A₀)
    (finiteTateGenerator A₀) (fun n => n + 1) (fun n => n.succ_pos)
    (finiteTateStage_isSetVariableExtension A₀) (fun j => finiteTateVariable A₀ j.1 j.2)
    (fun n j => ⟨⟨n, j⟩, rfl⟩) x

/-- **The mapping property of the colimit of the tower, with the target universe free.** A morphism
out of the base together with a homogeneous value of degree `n + 1` for each variable of degree
`n + 1` extends to a morphism of graded divided power algebras out of the colimit, for a target in
*any* universe. -/
public theorem finiteTateColimit_exists_gradedDPHom (E : GradedDPAlgebra.{u, y} R)
    (g : GradedDPHom (finiteTateAlgebra A₀ 0) E)
    (t : (n : ℕ) → finiteTateIndex A₀ n → E.carrier)
    (ht : ∀ (n : ℕ) (j : finiteTateIndex A₀ n), t n j ∈ E.grade (n + 1)) :
    ∃ F : GradedDPHom (finiteTateColimit A₀) E,
      (∀ a : (finiteTateAlgebra A₀ 0).carrier,
          F.hom ((finiteTateCoefficient A₀).hom a) = g.hom a) ∧
        (∀ (n : ℕ) (j : finiteTateIndex A₀ n),
          F.hom (finiteTateVariable A₀ n j) = t n j) :=
  chainColimit_exists_gradedDPHom (finiteTateAlgebra A₀) (finiteTateStep A₀)
    (finiteTateIndex A₀) (finiteTateGenerator A₀) (fun n => n + 1) (fun n => n.succ_pos)
    (finiteTateStage_isSetVariableExtension A₀) E g t ht

/-- **The differential on the colimit of the degreewise finite tower exists.** The differentials of
the stages are compatible with the steps and the steps are injective, so
`DividedPowers.TateResolution.exists_chainColimitDifferential` applies. -/
public theorem exists_finiteTateColimitDifferential :
    ∃ D : (finiteTateColimit A₀).carrier →ₗ[R] (finiteTateColimit A₀).carrier,
      (∀ (n : ℕ) (x : (finiteTateAlgebra A₀ n).carrier),
          D ((finiteTateInclusion A₀ n).hom x) =
            (finiteTateInclusion A₀ n).hom (finiteTateDifferential A₀ n x)) ∧
        IsDifferentialGradedAlgebra (finiteTateColimit A₀).grade D ∧
          IsCompatibleWithDifferential (finiteTateColimit A₀).gamma D :=
  exists_chainColimitDifferential (finiteTateAlgebra A₀) (finiteTateStep A₀)
    (finiteTateDifferential A₀) (finiteTateDga A₀) (finiteTateCompatible A₀)
    (finiteTateStep_differential A₀) (finiteTateStep_injective A₀)

/-- **The differential on the colimit of the degreewise finite tower.** -/
public noncomputable def finiteTateColimitDifferential :
    (finiteTateColimit A₀).carrier →ₗ[R] (finiteTateColimit A₀).carrier :=
  (exists_finiteTateColimitDifferential A₀).choose

/-- The differential of the colimit restricts to the differential of each stage. -/
public theorem finiteTateColimitDifferential_inclusion (n : ℕ)
    (x : (finiteTateAlgebra A₀ n).carrier) :
    finiteTateColimitDifferential A₀ ((finiteTateInclusion A₀ n).hom x) =
      (finiteTateInclusion A₀ n).hom (finiteTateDifferential A₀ n x) :=
  (exists_finiteTateColimitDifferential A₀).choose_spec.1 n x

/-- The colimit of the tower, with this differential, is a differential graded algebra. -/
public theorem finiteTateColimitDga :
    IsDifferentialGradedAlgebra (finiteTateColimit A₀).grade
      (finiteTateColimitDifferential A₀) :=
  (exists_finiteTateColimitDifferential A₀).choose_spec.2.1

/-- The divided powers of the colimit are compatible with this differential. -/
public theorem finiteTateColimitCompatible :
    IsCompatibleWithDifferential (finiteTateColimit A₀).gamma
      (finiteTateColimitDifferential A₀) :=
  (exists_finiteTateColimitDifferential A₀).choose_spec.2.2

/-- **The differential of a variable of degree `n + 1` of the colimit is the degree-`n` cycle it
was adjoined to kill**, read in the colimit. -/
public theorem finiteTateColimitDifferential_variable (n : ℕ) (j : finiteTateIndex A₀ n) :
    finiteTateColimitDifferential A₀ (finiteTateVariable A₀ n j) =
      (finiteTateInclusion A₀ n).hom (finiteTateCycle A₀ n j) := by
  rw [finiteTateVariable,
    finiteTateColimitDifferential_inclusion A₀ (n + 1) (finiteTateGenerator A₀ n j),
    finiteTateGenerator_differential A₀ n j,
    chainColimitInclusion_step (finiteTateAlgebra A₀) (finiteTateStep A₀) n
      (finiteTateCycle A₀ n j)]

end Colimit

section Acyclicity

variable {R : Type u} [CommRing R] (A₀ : TateStageData.{u, v} R 0)
  (D : (finiteTateColimit A₀).carrier →ₗ[R] (finiteTateColimit A₀).carrier)
  (hD : ∀ (n : ℕ) (x : (finiteTateAlgebra A₀ n).carrier),
    D ((finiteTateInclusion A₀ n).hom x) =
      (finiteTateInclusion A₀ n).hom (finiteTateDifferential A₀ n x))

include hD in
/-- **Every combination with degree-zero coefficients of the cycles prescribed at a stage is a
boundary in the colimit.** The corresponding combination of the variables adjoined above that stage
is the boundary, by `DividedPowers.TateResolution.exists_boundary_of_gradeZero_combination`.

Taken at the base this is exactness in degree zero: the family prescribed there is a finite
generating family of the ideal to be killed, and an element of that ideal is a combination of the
family with coefficients in the base, which sits in degree zero. -/
public theorem exists_finiteTateColimit_boundary_of_combination (n : ℕ)
    (s : Finset (finiteTateIndex A₀ n))
    (c : finiteTateIndex A₀ n → (finiteTateAlgebra A₀ n).carrier)
    (hc : ∀ j : finiteTateIndex A₀ n, c j ∈ (finiteTateAlgebra A₀ n).grade 0) :
    ∃ b : (finiteTateColimit A₀).carrier, b ∈ (finiteTateColimit A₀).grade (n + 1) ∧
      D b = (finiteTateInclusion A₀ n).hom (∑ j ∈ s, c j * finiteTateCycle A₀ n j) := by
  have hdga : IsDifferentialGradedAlgebra (finiteTateAlgebra A₀ (n + 1)).grade
      (finiteTateDifferential A₀ (n + 1)) := finiteTateDga A₀ (n + 1)
  obtain ⟨b, hb, hdb⟩ := exists_boundary_of_gradeZero_combination
    (finiteTateAlgebra A₀ (n + 1)).grade (finiteTateDifferential A₀ (n + 1))
    (fun j => (finiteTateStep A₀ n).hom (finiteTateCycle A₀ n j))
    (finiteTateGenerator A₀ n) n (finiteTateGenerator_mem A₀ n)
    (finiteTateGenerator_differential A₀ n) s
    (fun j => (finiteTateStep A₀ n).hom (c j))
    (fun j => (finiteTateStep A₀ n).map_grade 0 _ (hc j))
  have hmul : ∑ j ∈ s, (finiteTateStep A₀ n).hom (c j) *
        (finiteTateStep A₀ n).hom (finiteTateCycle A₀ n j) =
      (finiteTateStep A₀ n).hom (∑ j ∈ s, c j * finiteTateCycle A₀ n j) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => (map_mul (finiteTateStep A₀ n).hom _ _).symm
  refine ⟨(finiteTateInclusion A₀ (n + 1)).hom b,
    (finiteTateInclusion A₀ (n + 1)).map_grade (n + 1) _ hb, ?_⟩
  rw [hD (n + 1) b, hdb, hmul,
    chainColimitInclusion_step (finiteTateAlgebra A₀) (finiteTateStep A₀) n _]

include hD in
/-- **The colimit of the degreewise finite tower is acyclic in positive degrees**, provided every
stage above the base really does have a finite spanning family of its cycles — which over a
Noetherian coefficient ring it does, by
`DividedPowers.TateResolution.hasFiniteSpanningCycles_finiteTateStage`.

The cycle is pulled back to the stage of its own degree, where it is still a cycle because the
structure morphism is injective; there it is a combination of the prescribed family with
coefficients of degree zero, and such a combination is a boundary. No homology is computed, but —
unlike the existence half of Tag 09PN — the cycle is not its own variable's boundary either: it is
a combination of the boundaries of finitely many variables. -/
public theorem exists_finiteTateColimit_boundary_of_cycle
    (hspan : ∀ n : ℕ, HasFiniteSpanningCycles (finiteTateStage A₀ (n + 1)).datum (n + 1))
    (n : ℕ) {a : (finiteTateColimit A₀).carrier}
    (ha : a ∈ (finiteTateColimit A₀).grade (n + 1)) (hda : D a = 0) :
    ∃ b : (finiteTateColimit A₀).carrier, b ∈ (finiteTateColimit A₀).grade (n + 2) ∧ D b = a := by
  obtain ⟨y, hy, hya⟩ := exists_finiteTateInclusion_eq_of_mem_grade A₀ (n + 1) ha
  have hdy : finiteTateDifferential A₀ (n + 1) y = 0 := by
    refine finiteTateInclusion_injective A₀ (n + 1) ?_
    rw [← hD (n + 1) y, hya, hda, map_zero]
  obtain ⟨c, hc, hcy⟩ := exists_gradeZero_combination_of_chosenCycleFinset (hspan n) hy hdy
  have hsum : ∑ j ∈ (chosenCycleFinset (finiteTateStage A₀ (n + 1)).datum (n + 1)).attach,
      c (finiteTateCycle A₀ (n + 1) j) * finiteTateCycle A₀ (n + 1) j = y :=
    (Finset.sum_attach _ fun z => c z * z).trans hcy
  obtain ⟨b, hb, hdb⟩ := exists_finiteTateColimit_boundary_of_combination A₀ D hD (n + 1)
    (chosenCycleFinset (finiteTateStage A₀ (n + 1)).datum (n + 1)).attach
    (fun j => c (finiteTateCycle A₀ (n + 1) j)) (fun j => hc _)
  exact ⟨b, hb, hdb.trans
    ((congrArg (finiteTateInclusion A₀ (n + 1)).hom hsum).trans hya)⟩

end Acyclicity

section ColimitAcyclicity

variable {R : Type u} [CommRing R] (A₀ : TateStageData.{u, v} R 0)

/-- **Every combination with degree-zero coefficients of the cycles prescribed at a stage is a
boundary**, for the differential of the colimit. -/
public theorem exists_finiteTateColimitDifferential_boundary_of_combination (n : ℕ)
    (s : Finset (finiteTateIndex A₀ n))
    (c : finiteTateIndex A₀ n → (finiteTateAlgebra A₀ n).carrier)
    (hc : ∀ j : finiteTateIndex A₀ n, c j ∈ (finiteTateAlgebra A₀ n).grade 0) :
    ∃ b : (finiteTateColimit A₀).carrier, b ∈ (finiteTateColimit A₀).grade (n + 1) ∧
      finiteTateColimitDifferential A₀ b =
        (finiteTateInclusion A₀ n).hom (∑ j ∈ s, c j * finiteTateCycle A₀ n j) :=
  exists_finiteTateColimit_boundary_of_combination A₀ (finiteTateColimitDifferential A₀)
    (finiteTateColimitDifferential_inclusion A₀) n s c hc

/-- **The colimit of the degreewise finite tower is acyclic in positive degrees**, for its own
differential. -/
public theorem exists_finiteTateColimitDifferential_boundary_of_cycle
    (hspan : ∀ n : ℕ, HasFiniteSpanningCycles (finiteTateStage A₀ (n + 1)).datum (n + 1))
    (n : ℕ) {a : (finiteTateColimit A₀).carrier}
    (ha : a ∈ (finiteTateColimit A₀).grade (n + 1))
    (hda : finiteTateColimitDifferential A₀ a = 0) :
    ∃ b : (finiteTateColimit A₀).carrier, b ∈ (finiteTateColimit A₀).grade (n + 2) ∧
      finiteTateColimitDifferential A₀ b = a :=
  exists_finiteTateColimit_boundary_of_cycle A₀ (finiteTateColimitDifferential A₀)
    (finiteTateColimitDifferential_inclusion A₀) hspan n ha hda

end ColimitAcyclicity

section BaseColimit

variable {R : Type u} [CommRing R] (P : Type (max u v)) [CommRing P] [Algebra R P]
  (s₀ : Finset P)

/-- **The degree-zero part of the colimit of the tower over a degree-zero base is the base.**
Nothing of degree zero is added by any step, and the base has nothing of positive degree. -/
public theorem mem_finiteTateColimit_grade_zero_iff
    (x : (finiteTateColimit (finiteTateBase.{u, v} (R := R) P s₀)).carrier) :
    x ∈ (finiteTateColimit (finiteTateBase.{u, v} (R := R) P s₀)).grade 0 ↔
      ∃ p : P, (finiteTateCoefficient (finiteTateBase.{u, v} (R := R) P s₀)).hom p = x := by
  refine ⟨fun hx => ?_, fun ⟨p, hp⟩ => ?_⟩
  · obtain ⟨z, -, hzx⟩ :=
      exists_finiteTateInclusion_eq_of_mem_grade (finiteTateBase.{u, v} (R := R) P s₀) 0 hx
    exact ⟨z, hzx⟩
  · exact hp ▸ (finiteTateCoefficient (finiteTateBase.{u, v} (R := R) P s₀)).map_grade 0 p
      (mem_degreeZeroGrade_zero R P p)

/-- **Every combination of the prescribed family of the base with coefficients in `P` is a boundary
in the colimit.** The base prescribes a finite family of degree-zero cycles, and a combination of
them with coefficients in `P` — which is exactly degree zero of the tower — is the boundary of the
corresponding combination of the variables of degree one.

With the family taken to be a finite generating family of an ideal `I`, this is exactness in degree
zero: every element of `I` becomes a boundary, not only the members of the family. -/
public theorem exists_finiteTateColimitDifferential_boundary_of_base (c : P → P) :
    ∃ b : (finiteTateColimit (finiteTateBase.{u, v} (R := R) P s₀)).carrier,
      b ∈ (finiteTateColimit (finiteTateBase.{u, v} (R := R) P s₀)).grade 1 ∧
        finiteTateColimitDifferential (finiteTateBase.{u, v} (R := R) P s₀) b =
          (finiteTateCoefficient (finiteTateBase.{u, v} (R := R) P s₀)).hom
            (∑ y ∈ s₀, c y * y) := by
  obtain ⟨b, hb, hdb⟩ := exists_finiteTateColimitDifferential_boundary_of_combination
    (finiteTateBase.{u, v} (R := R) P s₀) 0 s₀.attach (fun j => c j.1)
    (fun _ => mem_degreeZeroGrade_zero R P _)
  exact ⟨b, hb, hdb.trans (congrArg
    (finiteTateInclusion (finiteTateBase.{u, v} (R := R) P s₀) 0).hom
    (Finset.sum_attach _ fun z => c z * z))⟩

end BaseColimit

end DividedPowers.TateResolution

end
