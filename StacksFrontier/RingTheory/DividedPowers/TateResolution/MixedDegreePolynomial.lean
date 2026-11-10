module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.GradedPolynomialMap
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.SetVariableExtension.Construction

/-!
# Graded divided-power polynomial algebras with variables in every degree

Let `A` be a strictly graded-commutative nonnegatively graded algebra over a commutative ring
`R`, with divided powers `γ` on its positive even part, and let `ι : P → A` be a map of its
degree-zero coefficient algebra into it.  `A` is a *graded divided-power polynomial algebra*
over `P` when it is the directed union of the finite-variable stages of a family of homogeneous
variables, one family in each positive degree, each successor stage being the odd exterior or
even divided-power one-variable extension of its predecessor.

This file proves the mapping property of such an algebra: prescribing an algebra map on `P` and
a homogeneous value for each variable determines a unique map of graded algebras with divided
powers out of `A`.  Tag 0F4I gives the corresponding statement for a family of variables of one
fixed degree, for the algebra it constructs; what is proved here is the statement for variables
of all degrees at once, and for an *arbitrary* algebra satisfying the axioms rather than for a
particular construction.

## Main definitions

* `DividedPowers.TateResolution.component` — the homogeneous component of an element of a graded
  algebra, with its basic calculus.
* `DividedPowers.TateResolution.RestrictedStageGradedDividedPowerPolynomial` — the axioms
  above: homogeneous variables indexed by degree, an injective coefficient map into degree
  zero, covering by finite stages, and the identification of each successor stage with a
  one-variable extension whose `R`-algebra structure is restricted from the ambient algebra.

## Main results

* `DividedPowers.TateResolution.existsUnique_restrictedStageGradedDividedPowerPolynomial_map`
  — the mapping property.  The target may live in a universe independent of the source and its
  variables.
* `DividedPowers.TateResolution.mem_positiveEvenPart_of_map` — an injective grade-detecting
  additive map reflects membership in the positive even part.  This is what transports the
  divided-power condition across the successor identification, which only detects the grading
  degreewise.

## Implementation notes

The map is built one stage at a time and then glued.  For each finite set `S` of variables there
is a unique ring homomorphism out of the stage `S` taking the prescribed values, preserving
degrees, and carrying `γ` to the divided powers of the target wherever an element and its
divided power both lie in the stage (`IsStageLift`); uniqueness is proved first, from the fact
that the coefficients, the variables and their divided powers generate the stage, and existence
then follows by induction on `S`, the step being the universal property of the one-variable
extension transported along the successor identification.  Because each stage lift is unique,
the family is automatically compatible, so the glued map comes from
`finiteVariableStages_directedColimit` with no coherence argument.

The divided-power clause of `IsStageLift` is conditional — it relates `φ x` and `φ y` for
elements of the stage with `y = γₙ x` — rather than asserting that a stage is closed under
divided powers.  Closure holds, but the available proof of it
(`finiteVariableStage_dpow_mem`) assumes all variables have one and the same degree, which is
exactly the hypothesis dropped here.  The conditional form needs no closure: at the point of
use one passes to the union of two stages.

Each finite stage carries an `R`-algebra structure, and the successor axiom requires that its
structure map be the one restricted from `A`.  Without that requirement the structure map is
unconstrained — it may be twisted by any ring endomorphism of `R` without affecting any other
clause, since the ring structures involved do not refer to `R` — and no `R`-algebra map out of a
stage can then be produced.  `stageAlgebra` together with `coe_stageAlgebraMap` exhibits the
required structure, and the algebra structure produced by the construction of Tag 0F4I satisfies
the requirement, since its structure map factors through the coefficient algebra.

`RestrictedStageGradedDividedPowerPolynomial` is therefore *not* the same object as
`GradedDividedPowerPolynomial` of
`StacksFrontier.RingTheory.DividedPowers.TateResolution.GradedPolynomial`, which states the same
axioms without the clause on the stage structure maps and reaches the same mapping property by
running the induction on ring homomorphisms instead of on algebra maps.  The two differ exactly in
that clause: a `RestrictedStageGradedDividedPowerPolynomial` is in particular a
`GradedDividedPowerPolynomial`, so the mapping property proved here is the weaker of the two,
while the existence statement that produces this structure
(`exists_gradedDividedPowerPolynomial`) is the stronger of the two, and that is why the clause is
kept: Tag 0F4I's construction supplies it, and dropping it would weaken what is known about the
algebra it builds.

## References

* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
* [Stacks Project, Tag 0F4I](https://stacks.math.columbia.edu/tag/0F4I)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w z

section Components

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]

/-- The degree-`m` homogeneous component of an element of a graded algebra. -/
public noncomputable def component (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (m : ℕ)
    (x : A) : A :=
  (DirectSum.decompose 𝒜 x m : A)

/-- The degree-`m` component of `x` lies in `𝒜 m`. -/
public theorem component_mem (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (m : ℕ) (x : A) :
    component 𝒜 m x ∈ 𝒜 m :=
  (DirectSum.decompose 𝒜 x m).2

/-- Taking the degree-`m` component is additive. -/
public theorem component_add (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (m : ℕ) (x y : A) :
    component 𝒜 m (x + y) = component 𝒜 m x + component 𝒜 m y := by
  simp only [component, DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add]

/-- Every component of `0` is `0`. -/
public theorem component_zero (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (m : ℕ) :
    component 𝒜 m (0 : A) = 0 := by
  simp only [component, DirectSum.decompose_zero, DirectSum.zero_apply,
    ZeroMemClass.coe_zero]

/-- An element of `𝒜 m` is its own degree-`m` component. -/
public theorem component_of_mem_same (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] {m : ℕ}
    {x : A} (hx : x ∈ 𝒜 m) : component 𝒜 m x = x := by
  simp only [component, DirectSum.decompose_of_mem_same 𝒜 hx]

/-- An element of `𝒜 n` has vanishing degree-`m` component for `m ≠ n`. -/
public theorem component_of_mem_ne (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] {m n : ℕ}
    {x : A} (hx : x ∈ 𝒜 n) (hmn : m ≠ n) : component 𝒜 m x = 0 := by
  simp only [component, DirectSum.decompose_of_mem_ne 𝒜 hx (Ne.symm hmn)]

/-- Every element is the sum of its components over some finite set of degrees. -/
public theorem sum_component (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (x : A) :
    ∃ s : Finset ℕ, ∑ m ∈ s, component 𝒜 m x = x := by
  classical
  exact ⟨(DirectSum.decompose 𝒜 x).support, DirectSum.sum_support_decompose 𝒜 x⟩

/-- An element of the positive even part has vanishing components in every other degree. -/
public theorem component_eq_zero_of_mem_positiveEvenPart (𝒜 : ℕ → Submodule R A)
    [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜] {m : ℕ} (hm : ∀ k : ℕ, m ≠ 2 * (k + 1))
    {x : A} (hx : x ∈ positiveEvenPart 𝒜) : component 𝒜 m x = 0 := by
  refine Submodule.iSup_induction (p := fun k : ℕ => 𝒜 (2 * (k + 1)))
    (motive := fun y => component 𝒜 m y = 0) hx ?_ (component_zero 𝒜 m) ?_
  · intro k y hy
    exact component_of_mem_ne 𝒜 hy (hm k)
  · intro y y' hy hy'
    rw [component_add, hy, hy', add_zero]

/-- An element whose components all lie in positive even degrees, or vanish, lies in the
positive even part. -/
public theorem mem_positiveEvenPart_of_components (𝒜 : ℕ → Submodule R A)
    [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜] {x : A}
    (hx : ∀ m : ℕ, (∀ k : ℕ, m ≠ 2 * (k + 1)) → component 𝒜 m x = 0) :
    x ∈ positiveEvenPart 𝒜 := by
  obtain ⟨s, hs⟩ := sum_component 𝒜 x
  rw [← hs]
  refine Submodule.sum_mem _ fun m _ => ?_
  by_cases hm : ∀ k : ℕ, m ≠ 2 * (k + 1)
  · rw [hx m hm]; exact Submodule.zero_mem _
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, m = 2 * (k + 1) := by
      by_contra hc
      exact hm fun k hmk => hc ⟨k, hmk⟩
    exact Submodule.mem_iSup_of_mem k (hk ▸ component_mem 𝒜 m x)

end Components

section Reflection

variable {R : Type u} {A : Type v} {B : Type z}
variable [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]

/-- A grade-detecting additive map commutes with taking homogeneous components. -/
public theorem component_map (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (ℬ : ℕ → Submodule R B) [GradedAlgebra ℬ] (E : B →+ A)
    (hE : ∀ (m : ℕ) (x : B), x ∈ ℬ m → E x ∈ 𝒜 m) (m : ℕ) (x : B) :
    E (component ℬ m x) = component 𝒜 m (E x) := by
  induction x using DirectSum.Decomposition.inductionOn ℬ with
  | zero => simp only [component_zero, map_zero]
  | @homogeneous n y =>
      by_cases hmn : m = n
      · subst hmn
        rw [component_of_mem_same ℬ y.2, component_of_mem_same 𝒜 (hE m y y.2)]
      · rw [component_of_mem_ne ℬ y.2 hmn, map_zero,
          component_of_mem_ne 𝒜 (hE n y y.2) hmn]
  | add y y' hy hy' =>
      rw [component_add, map_add, map_add, component_add, hy, hy']

/-- An injective grade-detecting ring map reflects membership in the positive even part. -/
public theorem mem_positiveEvenPart_of_map (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜] (ℬ : ℕ → Submodule R B) [GradedAlgebra ℬ]
    [IsStrictlyGradedComm ℬ] (E : B →+ A) (hE : ∀ (m : ℕ) (x : B), x ∈ ℬ m → E x ∈ 𝒜 m)
    (hEinj : Function.Injective E) {x : B} (hx : E x ∈ positiveEvenPart 𝒜) :
    x ∈ positiveEvenPart ℬ := by
  refine mem_positiveEvenPart_of_components ℬ fun m hm => ?_
  refine hEinj ?_
  rw [component_map 𝒜 ℬ E hE m x, map_zero]
  exact component_eq_zero_of_mem_positiveEvenPart 𝒜 hm hx

end Reflection

/-! ### Finite-variable stages as subalgebras -/

section Stage

variable {R : Type u} {P : Type v} {A : Type w}
variable [CommRing R] [Ring P] [Algebra R P] [Ring A] [Algebra R A]
variable {Aᵢ : ℕ → Submodule R A} [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
variable (γ : DividedPowerStructure Aᵢ) (ι : P →ₐ[R] A)

/-- The coefficients lie in every finite-variable stage. -/
public theorem coefficient_mem_finiteVariableStage {J : Type*} (T : J → A) (S : Finset J)
    (p : P) : ι p ∈ finiteVariableStage γ ι T S :=
  Subring.subset_closure (Or.inl ⟨p, rfl⟩)

/-- A variable of the indexing set lies in the corresponding finite-variable stage. -/
public theorem generator_mem_finiteVariableStage {J : Type*} (T : J → A) {S : Finset J}
    {j : J} (hj : j ∈ S) : T j ∈ finiteVariableStage γ ι T S :=
  Subring.subset_closure (Or.inr ⟨j, hj, Or.inl rfl⟩)

/-- Every divided power of a variable lies in the corresponding finite-variable stage. -/
public theorem dpow_generator_mem_finiteVariableStage {J : Type*} (T : J → A) {S : Finset J}
    {j : J} (hj : j ∈ S) (n : ℕ) : γ.dpow n (T j) ∈ finiteVariableStage γ ι T S :=
  Subring.subset_closure (Or.inr ⟨j, hj, Or.inr ⟨n, rfl⟩⟩)

/-- The structure map `R → S` of a finite-variable stage `S`, followed by the inclusion
`S → A`, is the structure map `R → A`. -/
public theorem coe_stageAlgebraMap {J : Type*} (T : J → A) (S : Finset J) (r : R) :
    letI : Algebra R (finiteVariableStage γ ι T S) := stageAlgebra γ ι T S
    ((algebraMap R (finiteVariableStage γ ι T S) r : finiteVariableStage γ ι T S) : A) =
      algebraMap R A r := rfl

end Stage

/-! ### Graded divided-power polynomial algebras -/

/-- A graded divided-power polynomial algebra over `P`, obtained as the directed union of
finite successive odd exterior and even divided-power variable extensions, with variables in
every positive degree.

Each finite-variable stage carries the `R`-algebra structure restricted from the ambient
algebra, `stageAlgebra`; the successor condition says that adjoining one further variable to
a stage produces precisely the odd or even divided-power one-variable extension of that
stage, with its grading and its divided powers.

This is the form of the axioms in which Tag 0F4I's construction delivers them, and it is
strictly stronger than `GradedDividedPowerPolynomial` of
`StacksFrontier.RingTheory.DividedPowers.TateResolution.GradedPolynomial`: the successor condition
here also records that each stage's structure map `R → S` is the restriction of `R → A`, which that
version leaves unconstrained. Everything else is the same, up to quantifying over a finite set
`U` characterized by `k ∈ U ↔ k = j ∨ k ∈ S` instead of over `insert j S`, which spares the
index type a `DecidableEq`. -/
public structure RestrictedStageGradedDividedPowerPolynomial
    {R : Type u} {P : Type v} {A : Type w}
    [CommRing R] [Ring P] [Algebra R P] [Ring A] [Algebra R A]
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ]
    [IsStrictlyGradedComm Aᵢ] (γ : DividedPowerStructure Aᵢ)
    (ι : P →ₐ[R] A) where
  /-- Indices of the new variables in degree `n + 1`. -/
  indices : ℕ → Type w
  /-- The homogeneous new variables, indexed together with their degrees. -/
  generator : (Σ n : ℕ, indices n) → A
  generator_mem : ∀ j, generator j ∈ Aᵢ (j.1 + 1)
  coefficient_mem : ∀ p : P, ι p ∈ Aᵢ 0
  coefficient_injective : Function.Injective ι
  /-- The finite variable stages cover the algebra. -/
  finite_support : ∀ x : A, ∃ S : Finset (Σ n : ℕ, indices n),
    x ∈ finiteVariableStage γ ι generator S
  /-- Adjoining one variable to a finite stage is precisely the relevant odd or even
  divided-power extension, not merely an abstract universal-property algebra. -/
  successor : ∀ (S U : Finset (Σ n : ℕ, indices n)) (j : Σ n : ℕ, indices n), j ∉ S →
      (∀ k : Σ n : ℕ, indices n, k ∈ U ↔ k = j ∨ k ∈ S) →
      ∃ aS : Algebra R (finiteVariableStage γ ι generator S),
      letI : Algebra R (finiteVariableStage γ ι generator S) := aS
      (∀ r : R,
        ((algebraMap R (finiteVariableStage γ ι generator S) r :
          finiteVariableStage γ ι generator S) : A) = algebraMap R A r) ∧
      ∃ (Sᵢ : ℕ → Submodule R (finiteVariableStage γ ι generator S))
        (gS : GradedAlgebra Sᵢ),
        letI : GradedAlgebra Sᵢ := gS
        ∃ cS : IsStrictlyGradedComm Sᵢ,
          letI : IsStrictlyGradedComm Sᵢ := cS
          ∃ δS : DividedPowerStructure Sᵢ,
            (∀ (n : ℕ) (b : finiteVariableStage γ ι generator S),
              b ∈ positiveEvenPart Sᵢ →
                (δS.dpow n b : A) = γ.dpow n (b : A)) ∧
            (∀ hodd : Odd (j.1 + 1),
              ∃ e : OddVariableExtension Sᵢ (j.1 + 1) ≃+*
                  finiteVariableStage γ ι generator U,
                (∀ b : finiteVariableStage γ ι generator S,
                  ((e (OddVariableExtension.inclusion Sᵢ (j.1 + 1) b) :
                    finiteVariableStage γ ι generator U) : A) = b) ∧
                ((e (OddVariableExtension.generator Sᵢ (j.1 + 1)) :
                  finiteVariableStage γ ι generator U) : A) = generator j ∧
                (∀ (m : ℕ) (x : OddVariableExtension Sᵢ (j.1 + 1)),
                  x ∈ OddVariableExtension.grade Sᵢ (j.1 + 1) m ↔ (e x : A) ∈ Aᵢ m) ∧
                (∀ (n : ℕ) (x : OddVariableExtension Sᵢ (j.1 + 1)),
                  x ∈ positiveEvenPart (OddVariableExtension.grade Sᵢ (j.1 + 1)) →
                  γ.dpow n (e x : A) =
                    (e ((oddVariableDividedPowerStructure Sᵢ δS (j.1 + 1)
                      (Nat.zero_lt_succ j.1) hodd).dpow n x) : A))) ∧
            (∀ heven : Even (j.1 + 1),
              letI : Fact (Even (j.1 + 1)) := ⟨heven⟩
              ∃ e : EvenVariableAlgebra (finiteVariableStage γ ι generator S) ≃+*
                  finiteVariableStage γ ι generator U,
                (∀ b : finiteVariableStage γ ι generator S,
                  ((e (EvenVariableAlgebra.coeffEmbedding b) :
                    finiteVariableStage γ ι generator U) : A) = b) ∧
                ((e (EvenVariableAlgebra.monomial 1 1) :
                  finiteVariableStage γ ι generator U) : A) = generator j ∧
                (∀ (m : ℕ) (x : EvenVariableAlgebra (finiteVariableStage γ ι generator S)),
                  x ∈ EvenVariableAlgebra.grade Sᵢ (j.1 + 1) m ↔ (e x : A) ∈ Aᵢ m) ∧
                (∀ (n : ℕ) (x : EvenVariableAlgebra (finiteVariableStage γ ι generator S)),
                  x ∈ positiveEvenPart (EvenVariableAlgebra.grade Sᵢ (j.1 + 1)) →
                  γ.dpow n (e x : A) =
                    (e ((evenVariableDividedPowerStructure (j.1 + 1)
                      (Nat.zero_lt_succ j.1) δS).dpow n x) : A)))

/-! ### The mapping property -/

section UniversalProperty

variable {R : Type u} {P : Type v} {A : Type w} {D : Type z}
variable [CommRing R] [Ring P] [Algebra R P] [Ring A] [Algebra R A] [Ring D] [Algebra R D]
variable {Aᵢ : ℕ → Submodule R A} [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
variable {γ : DividedPowerStructure Aᵢ} {ι : P →ₐ[R] A}
variable {Dᵢ : ℕ → Submodule R D} [GradedAlgebra Dᵢ] [IsStrictlyGradedComm Dᵢ]

/-- The characterizing properties of the restriction to the finite stage `S` of a lift of
the prescribed data: it takes the prescribed values on the coefficients and on the variables
indexed by `S`, it preserves degrees, and it carries the divided powers of the ambient algebra
to those of the target whenever both an element and its divided power lie in the stage. -/
private def IsStageLift (γ : DividedPowerStructure Aᵢ) (ι : P →ₐ[R] A)
    (δ : DividedPowerStructure Dᵢ) (f : P →ₐ[R] D)
    {J : Type w} (T : J → A) (t : J → D) (S : Finset J)
    (φ : finiteVariableStage γ ι T S →+* D) : Prop :=
  (∀ (p : P) (hp : ι p ∈ finiteVariableStage γ ι T S), φ ⟨ι p, hp⟩ = f p) ∧
  (∀ (j : J) (hj : T j ∈ finiteVariableStage γ ι T S), j ∈ S → φ ⟨T j, hj⟩ = t j) ∧
  (∀ (m : ℕ) (x : finiteVariableStage γ ι T S), (x : A) ∈ Aᵢ m → φ x ∈ Dᵢ m) ∧
  (∀ (n : ℕ) (x y : finiteVariableStage γ ι T S),
      (x : A) ∈ positiveEvenPart Aᵢ → (y : A) = γ.dpow n (x : A) → δ.dpow n (φ x) = φ y)

/-! The empty stage. -/

private theorem exists_coefficient_of_mem_stage_empty (γ : DividedPowerStructure Aᵢ)
    (ι : P →ₐ[R] A) {J : Type w} (T : J → A) {a : A}
    (ha : a ∈ finiteVariableStage γ ι T (∅ : Finset J)) : ∃ p : P, ι p = a := by
  rw [finiteVariableStage_empty Aᵢ γ ι T] at ha
  have hle : Subring.closure (Set.range (ι : P → A)) ≤ (ι : P →+* A).range :=
    Subring.closure_le.mpr fun y hy => by
      obtain ⟨p, hp⟩ := hy
      exact ⟨p, hp⟩
  exact hle ha

private theorem mem_grade_zero_of_mem_stage_empty (γ : DividedPowerStructure Aᵢ)
    (ι : P →ₐ[R] A) (hι : ∀ p : P, ι p ∈ Aᵢ 0) {J : Type w} (T : J → A) {a : A}
    (ha : a ∈ finiteVariableStage γ ι T (∅ : Finset J)) : a ∈ Aᵢ 0 := by
  obtain ⟨p, hp⟩ := exists_coefficient_of_mem_stage_empty γ ι T ha
  exact hp ▸ hι p

private noncomputable def stageEmptyFun (γ : DividedPowerStructure Aᵢ) (ι : P →ₐ[R] A)
    (f : P →ₐ[R] D) {J : Type w} (T : J → A)
    (x : finiteVariableStage γ ι T (∅ : Finset J)) : D :=
  f (exists_coefficient_of_mem_stage_empty γ ι T x.2).choose

private theorem stageEmptyFun_eq (γ : DividedPowerStructure Aᵢ) {ι : P →ₐ[R] A}
    (hinj : Function.Injective ι) (f : P →ₐ[R] D) {J : Type w} (T : J → A)
    (x : finiteVariableStage γ ι T (∅ : Finset J)) {p : P} (hp : ι p = (x : A)) :
    stageEmptyFun γ ι f T x = f p := by
  have hc := (exists_coefficient_of_mem_stage_empty γ ι T x.2).choose_spec
  exact congrArg f (hinj (hc.trans hp.symm))

/-- The lift over the empty stage: the stage is the image of the coefficient algebra, so the
prescribed map on coefficients determines it. -/
private noncomputable def stageEmptyLift (γ : DividedPowerStructure Aᵢ) {ι : P →ₐ[R] A}
    (hinj : Function.Injective ι) (f : P →ₐ[R] D) {J : Type w} (T : J → A) :
    finiteVariableStage γ ι T (∅ : Finset J) →+* D where
  toFun := stageEmptyFun γ ι f T
  map_one' := by
    rw [stageEmptyFun_eq γ hinj f T _ (p := 1) (by rw [map_one]; rfl), map_one]
  map_zero' := by
    rw [stageEmptyFun_eq γ hinj f T _ (p := 0) (by rw [map_zero]; rfl), map_zero]
  map_mul' := by
    intro x y
    obtain ⟨p, hp⟩ := exists_coefficient_of_mem_stage_empty γ ι T x.2
    obtain ⟨q, hq⟩ := exists_coefficient_of_mem_stage_empty γ ι T y.2
    rw [stageEmptyFun_eq γ hinj f T x hp, stageEmptyFun_eq γ hinj f T y hq,
      stageEmptyFun_eq γ hinj f T (x * y) (p := p * q)
        (by rw [map_mul, hp, hq]; rfl), map_mul]
  map_add' := by
    intro x y
    obtain ⟨p, hp⟩ := exists_coefficient_of_mem_stage_empty γ ι T x.2
    obtain ⟨q, hq⟩ := exists_coefficient_of_mem_stage_empty γ ι T y.2
    rw [stageEmptyFun_eq γ hinj f T x hp, stageEmptyFun_eq γ hinj f T y hq,
      stageEmptyFun_eq γ hinj f T (x + y) (p := p + q)
        (by rw [map_add, hp, hq]; rfl), map_add]

private theorem isStageLift_stageEmptyLift (γ : DividedPowerStructure Aᵢ) {ι : P →ₐ[R] A}
    (hinj : Function.Injective ι) (hι : ∀ p : P, ι p ∈ Aᵢ 0)
    (δ : DividedPowerStructure Dᵢ) (f : P →ₐ[R] D) (hf : ∀ p : P, f p ∈ Dᵢ 0)
    {J : Type w} (T : J → A) (t : J → D) :
    IsStageLift γ ι δ f T t (∅ : Finset J) (stageEmptyLift γ hinj f T) := by
  refine ⟨fun p hp => stageEmptyFun_eq γ hinj f T ⟨ι p, hp⟩ rfl, ?_, ?_, ?_⟩
  · exact fun j _ hjS => absurd hjS (Finset.notMem_empty j)
  · intro m x hx
    obtain ⟨p, hp⟩ := exists_coefficient_of_mem_stage_empty γ ι T x.2
    have hval : stageEmptyLift γ hinj f T x = f p := stageEmptyFun_eq γ hinj f T x hp
    rw [hval]
    by_cases hm : m = 0
    · subst hm; exact hf p
    · have hzero : ι p = 0 := by
        have c1 := component_of_mem_same Aᵢ (hι p)
        have c2 := component_of_mem_ne Aᵢ (hp ▸ hx : ι p ∈ Aᵢ m) (Ne.symm hm)
        rw [← c1, c2]
      have hp0 : p = 0 := hinj (by rw [hzero, map_zero])
      rw [hp0, map_zero]
      exact Submodule.zero_mem _
  · intro n x y hx hy
    have h0 : (x : A) ∈ Aᵢ 0 := mem_grade_zero_of_mem_stage_empty γ ι hι T x.2
    have hx0 : (x : A) = 0 := by
      rcases positiveEven_homogeneous_eq_zero_or_grade Aᵢ h0 hx with hz | ⟨k, hk⟩
      · exact hz
      · omega
    have hxz : x = 0 := Subtype.ext hx0
    rw [hxz, map_zero]
    by_cases hn : n = 0
    · subst hn
      have hy1 : y = (1 : finiteVariableStage γ ι T (∅ : Finset J)) :=
        Subtype.ext (by
          rw [hy, hx0, γ.dpow_zero (Submodule.zero_mem _), OneMemClass.coe_one])
      rw [hy1, map_one, δ.dpow_zero (Submodule.zero_mem _)]
    · have hy0 : y = (0 : finiteVariableStage γ ι T (∅ : Finset J)) :=
        Subtype.ext (by
          rw [hy, hx0, γ.dpow_zero_eq_zero hn, ZeroMemClass.coe_zero])
      rw [hy0, map_zero, δ.dpow_zero_eq_zero hn]

/-! The inductive step: one more variable. -/

/-- A lift of the prescribed data over a stage `S`, composed with the inverse of an equivalence
from an extension `X` of `S` onto the stage `U` obtained by adjoining the variable `j`, is a lift
over `U`, provided the extension map `g` is compatible with the lift, the grading and the
divided powers. -/
private theorem isStageLift_comp_symm (δ : DividedPowerStructure Dᵢ) (f : P →ₐ[R] D)
    {J : Type w} (T : J → A) (t : J → D) {S U : Finset J} {j : J}
    (hU : ∀ k, k ∈ U ↔ k = j ∨ k ∈ S) {φ : finiteVariableStage γ ι T S →+* D}
    (hφ : IsStageLift γ ι δ f T t S φ) {X : Type*} [Ring X] [Algebra R X]
    (ℬ : ℕ → Submodule R X) [GradedAlgebra ℬ] [IsStrictlyGradedComm ℬ]
    (dX : DividedPowerStructure ℬ) (e : X ≃+* finiteVariableStage γ ι T U)
    (c : finiteVariableStage γ ι T S → X) (x₀ : X) (g : X →+* D)
    (hce : ∀ b, (e (c b) : A) = b) (hge : (e x₀ : A) = T j)
    (hgr : ∀ (m : ℕ) (x : X), x ∈ ℬ m ↔ (e x : A) ∈ Aᵢ m)
    (hdp : ∀ (n : ℕ) (x : X), x ∈ positiveEvenPart ℬ →
      γ.dpow n (e x : A) = (e (dX.dpow n x) : A))
    (hgc : ∀ b, g (c b) = φ b) (hgx : g x₀ = t j)
    (hgg : ∀ (m : ℕ) (x : X), x ∈ ℬ m → g x ∈ Dᵢ m)
    (hgd : ∀ (n : ℕ) (x : X), x ∈ positiveEvenPart ℬ → δ.dpow n (g x) = g (dX.dpow n x)) :
    IsStageLift γ ι δ f T t U (g.comp (e.symm : _ ≃+* X).toRingHom) := by
  have hcomp : ∀ (b : finiteVariableStage γ ι T S) (hb : (b : A) ∈ finiteVariableStage γ ι T U),
      g (e.symm ⟨b, hb⟩) = φ b := fun b hb => by
    rw [e.symm_apply_eq.mpr (Subtype.ext (hce b)).symm, hgc]
  refine ⟨fun p hp => ?_, fun k hk hkU => ?_, fun m x hx => ?_, fun n x y hx hy => ?_⟩
  · exact (hcomp ⟨ι p, coefficient_mem_finiteVariableStage γ ι T S p⟩ hp).trans (hφ.1 p _)
  · rcases (hU k).mp hkU with rfl | hkS
    · change g (e.symm _) = _
      rw [e.symm_apply_eq.mpr (Subtype.ext hge.symm), hgx]
    · exact (hcomp ⟨T k, generator_mem_finiteVariableStage γ ι T hkS⟩ hk).trans
        (hφ.2.1 k _ hkS)
  · exact hgg m _ ((hgr m (e.symm x)).mpr (by rwa [e.apply_symm_apply]))
  · have hpx := mem_positiveEvenPart_symm_of_ringEquiv Aᵢ ℬ _ e hgr hx
    have hyeq : e.symm y = dX.dpow n (e.symm x) :=
      e.symm_apply_eq.mpr (Subtype.ext (by rw [hy, ← hdp n _ hpx, e.apply_symm_apply]))
    change δ.dpow n (g (e.symm x)) = g (e.symm y)
    rw [hyeq, hgd n _ hpx]

private theorem exists_isStageLift_insert
    (h : RestrictedStageGradedDividedPowerPolynomial Aᵢ γ ι)
    (δ : DividedPowerStructure Dᵢ) (f : P →ₐ[R] D)
    (t : (Σ n : ℕ, h.indices n) → D) (ht : ∀ j, t j ∈ Dᵢ (j.1 + 1))
    (S U : Finset (Σ n : ℕ, h.indices n)) (j : Σ n : ℕ, h.indices n)
    (hjS : j ∉ S) (hU : ∀ k, k ∈ U ↔ k = j ∨ k ∈ S)
    {φ : finiteVariableStage γ ι h.generator S →+* D}
    (hφ : IsStageLift γ ι δ f h.generator t S φ) :
    ∃ ψ : finiteVariableStage γ ι h.generator U →+* D,
      IsStageLift γ ι δ f h.generator t U ψ := by
  obtain ⟨aS, hmapS, Sᵢ, gS, cS, δS, hδ, hoddcase, hevencase⟩ := h.successor S U j hjS hU
  let _ : Algebra R (finiteVariableStage γ ι h.generator S) := aS
  let _ : GradedAlgebra Sᵢ := gS
  let _ : IsStrictlyGradedComm Sᵢ := cS
  have hd : 0 < j.1 + 1 := Nat.succ_pos _
  have hcoeffmem : ∀ p : P, ι p ∈ finiteVariableStage γ ι h.generator S :=
    coefficient_mem_finiteVariableStage γ ι h.generator S
  let incl : finiteVariableStage γ ι h.generator S →ₐ[R] A :=
    { toFun := fun x => (x : A)
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := hmapS }
  have hcomm : ∀ r : R,
      φ (algebraMap R (finiteVariableStage γ ι h.generator S) r) = algebraMap R D r := by
    intro r
    have hmk : (algebraMap R (finiteVariableStage γ ι h.generator S) r) =
        ⟨ι (algebraMap R P r), hcoeffmem _⟩ :=
      Subtype.ext ((hmapS r).trans (ι.commutes r).symm)
    rw [hmk, hφ.1, f.commutes]
  let φA : finiteVariableStage γ ι h.generator S →ₐ[R] D := { φ with commutes' := hcomm }
  have hφA : ∀ b, φA b = φ b := fun _ => rfl
  have hlift : (∀ (m : ℕ) (b : finiteVariableStage γ ι h.generator S),
        b ∈ Sᵢ m ↔ (b : A) ∈ Aᵢ m) →
      (∀ m b, b ∈ Sᵢ m → φA b ∈ Dᵢ m) ∧
      ∀ n b, b ∈ positiveEvenPart Sᵢ → δ.dpow n (φA b) = φA (δS.dpow n b) := fun ha =>
    ⟨fun m b hb => hφ.2.2.1 m b ((ha m b).mp hb), fun n b hb => by
      rw [hφA, hφA, hφ.2.2.2 n b (δS.dpow n b)
        (algHom_mem_positiveEvenPart Sᵢ Aᵢ incl (fun m x hx => (ha m x).mp hx) hb) (hδ n b hb)]⟩
  rcases Nat.even_or_odd (j.1 + 1) with heven | hodd
  · -- even variable
    let _ : Fact (Even (j.1 + 1)) := ⟨heven⟩
    obtain ⟨e, hce, hge, hgr, hdp⟩ := hevencase heven
    obtain ⟨hf₁, hf₂⟩ := hlift fun m b => by
      rw [← hce b, ← hgr m (EvenVariableAlgebra.coeffEmbedding b),
        EvenVariableAlgebra.coeffEmbedding_mem_grade_iff]
    obtain ⟨g, hg, -⟩ := existsUnique_evenVariable_dividedPower_lift Sᵢ δS Dᵢ δ φA hf₁ hf₂
      (j.1 + 1) hd (t j) (ht j)
    exact ⟨_, isStageLift_comp_symm δ f h.generator t hU hφ _
      (evenVariableDividedPowerStructure (j.1 + 1) hd δS) e EvenVariableAlgebra.coeffEmbedding
      (EvenVariableAlgebra.monomial 1 1) g.toRingHom hce hge hgr hdp hg.1 hg.2.1 hg.2.2.1
      hg.2.2.2⟩
  · -- odd variable
    obtain ⟨e, hce, hge, hgr, hdp⟩ := hoddcase hodd
    obtain ⟨hf₁, hf₂⟩ := hlift fun m b => by
      rw [← hce b, ← hgr m (OddVariableExtension.inclusion Sᵢ (j.1 + 1) b),
        OddVariableExtension.mem_grade_coefficients_iff,
        OddVariableExtension.coefficients_inclusion]
      simp
    obtain ⟨g, hg, -⟩ := existsUnique_oddVariable_dividedPower_lift Sᵢ δS Dᵢ δ φA hf₁ hf₂
      (j.1 + 1) hd hodd (t j) (ht j)
    exact ⟨_, isStageLift_comp_symm δ f h.generator t hU hφ _
      (oddVariableDividedPowerStructure Sᵢ δS (j.1 + 1) hd hodd) e
      (OddVariableExtension.inclusion Sᵢ (j.1 + 1))
      (OddVariableExtension.generator Sᵢ (j.1 + 1)) g.toRingHom hce hge hgr hdp hg.1 hg.2.1
      hg.2.2.1 hg.2.2.2⟩

/-- Two lifts over nested finite stages agree wherever their arguments agree in the ambient
algebra, since the coefficients, the variables of the smaller stage and their divided powers
generate that stage. -/
private theorem isStageLift_agree (γ : DividedPowerStructure Aᵢ) (ι : P →ₐ[R] A)
    (δ : DividedPowerStructure Dᵢ) (f : P →ₐ[R] D) {J : Type w} (T : J → A) (t : J → D)
    {S U : Finset J} (hSU : S ⊆ U)
    {φ : finiteVariableStage γ ι T S →+* D} {ψ : finiteVariableStage γ ι T U →+* D}
    (hφ : IsStageLift γ ι δ f T t S φ) (hψ : IsStageLift γ ι δ f T t U ψ)
    (x : finiteVariableStage γ ι T S) (y : finiteVariableStage γ ι T U)
    (hxy : (x : A) = (y : A)) : φ x = ψ y := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  obtain rfl : x = y := hxy
  refine finiteVariableStage_ringHom_eq_of_subset γ ι T hSU φ ψ
    (fun p => (hφ.1 p _).trans (hψ.1 p _).symm)
    (fun k hk => (hφ.2.1 k _ hk).trans (hψ.2.1 k _ (hSU hk)).symm) (fun k hk n => ?_) x hx hy
  by_cases hp : T k ∈ positiveEvenPart Aᵢ
  · have e₁ := hφ.2.2.2 n ⟨T k, generator_mem_finiteVariableStage γ ι T hk⟩
      ⟨γ.dpow n (T k), dpow_generator_mem_finiteVariableStage γ ι T hk n⟩ hp rfl
    have e₂ := hψ.2.2.2 n ⟨T k, generator_mem_finiteVariableStage γ ι T (hSU hk)⟩
      ⟨γ.dpow n (T k), dpow_generator_mem_finiteVariableStage γ ι T (hSU hk) n⟩ hp rfl
    rw [← e₁, ← e₂, hφ.2.1 k _ hk, hψ.2.1 k _ (hSU hk)]
  · have hzS : (⟨γ.dpow n (T k), dpow_generator_mem_finiteVariableStage γ ι T hk n⟩ :
        finiteVariableStage γ ι T S) = 0 := Subtype.ext (γ.dpow_null hp)
    have hzU : (⟨γ.dpow n (T k), dpow_generator_mem_finiteVariableStage γ ι T (hSU hk) n⟩ :
        finiteVariableStage γ ι T U) = 0 := Subtype.ext (γ.dpow_null hp)
    rw [hzS, hzU, map_zero, map_zero]

private theorem exists_isStageLift (h : RestrictedStageGradedDividedPowerPolynomial Aᵢ γ ι)
    (δ : DividedPowerStructure Dᵢ) (f : P →ₐ[R] D) (hf : ∀ p : P, f p ∈ Dᵢ 0)
    (t : (Σ n : ℕ, h.indices n) → D) (ht : ∀ j, t j ∈ Dᵢ (j.1 + 1))
    (S : Finset (Σ n : ℕ, h.indices n)) :
    ∃ φ : finiteVariableStage γ ι h.generator S →+* D,
      IsStageLift γ ι δ f h.generator t S φ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      exact ⟨stageEmptyLift γ h.coefficient_injective f h.generator,
        isStageLift_stageEmptyLift γ h.coefficient_injective h.coefficient_mem δ f hf
          h.generator t⟩
  | insert j S hjS hS =>
      obtain ⟨φ, hφ⟩ := hS
      exact exists_isStageLift_insert h δ f t ht S (insert j S) j hjS
        (fun k => Finset.mem_insert) hφ

/-- The mapping property of an iterated graded divided-power polynomial algebra: prescribing
the values on the coefficient algebra and on the variables, subject to the degree conditions,
determines a unique map of graded algebras with divided powers. The target may live in a
universe independent of the source and its variables.

The hypothesis is `RestrictedStageGradedDividedPowerPolynomial`, which also requires each
stage's `R`-algebra structure to be restricted from the ambient algebra.
`existsUnique_gradedDividedPowerPolynomial_map` of
`StacksFrontier.RingTheory.DividedPowers.TateResolution.GradedPolynomialMap` has the identical
conclusion under the hypothesis without that clause, so it is the stronger of the two; this one is
the form that `exists_gradedDividedPowerPolynomial` applies, since Tag 0F4I's construction
delivers the clause. -/
@[stacks 09PN "mapping property of a graded divided-power polynomial algebra"]
public theorem existsUnique_restrictedStageGradedDividedPowerPolynomial_map
    (γ : DividedPowerStructure Aᵢ) (ι : P →ₐ[R] A)
    (h : RestrictedStageGradedDividedPowerPolynomial Aᵢ γ ι)
    (δ : DividedPowerStructure Dᵢ) (f : P →ₐ[R] D) (hf : ∀ p : P, f p ∈ Dᵢ 0)
    (t : (Σ n : ℕ, h.indices n) → D) (ht : ∀ j, t j ∈ Dᵢ (j.1 + 1)) :
    ∃! g : A →ₐ[R] D,
      (∀ p : P, g (ι p) = f p) ∧
      (∀ j : Σ n : ℕ, h.indices n, g (h.generator j) = t j) ∧
      (∀ (n : ℕ) (a : A), a ∈ Aᵢ n → g a ∈ Dᵢ n) ∧
      (∀ (n : ℕ) (a : A), a ∈ positiveEvenPart Aᵢ →
        g (γ.dpow n a) = δ.dpow n (g a)) := by
  classical
  choose F hF using exists_isStageLift h δ f hf t ht
  have hcompat : ∀ (S U : Finset (Σ n : ℕ, h.indices n))
      (x : finiteVariableStage γ ι h.generator S)
      (y : finiteVariableStage γ ι h.generator U), (x : A) = (y : A) → F S x = F U y := by
    intro S U x y hxy
    have hxV : (x : A) ∈ finiteVariableStage γ ι h.generator (S ∪ U) :=
      finiteVariableStage_le_of_subset γ ι h.generator Finset.subset_union_left x.2
    have h1 := isStageLift_agree γ ι δ f h.generator t
      (Finset.subset_union_left (s₂ := U)) (hF S) (hF (S ∪ U)) x ⟨(x : A), hxV⟩ rfl
    have h2 := isStageLift_agree γ ι δ f h.generator t
      (Finset.subset_union_right (s₁ := S)) (hF U) (hF (S ∪ U)) y ⟨(x : A), hxV⟩ hxy.symm
    rw [h1, ← h2]
  obtain ⟨g₀, hg₀, hg₀u⟩ := finiteVariableStages_directedColimit Aᵢ γ ι h.generator
    h.finite_support F hcompat
  have hgcoeff : ∀ p : P, g₀ (ι p) = f p := by
    intro p
    have hmem : ι p ∈ finiteVariableStage γ ι h.generator (∅ : Finset (Σ n, h.indices n)) :=
      coefficient_mem_finiteVariableStage γ ι h.generator _ p
    rw [hg₀ ∅ ⟨ι p, hmem⟩]
    exact (hF ∅).1 p hmem
  have hcomm : ∀ r : R, g₀ (algebraMap R A r) = algebraMap R D r := fun r => by
    rw [← ι.commutes r, hgcoeff, f.commutes]
  let g : A →ₐ[R] D := { g₀ with commutes' := hcomm }
  have hgval : ∀ a : A, g a = g₀ a := fun _ => rfl
  have hgen : ∀ j : Σ n : ℕ, h.indices n, g (h.generator j) = t j := by
    intro j
    have hmem : h.generator j ∈ finiteVariableStage γ ι h.generator {j} :=
      generator_mem_finiteVariableStage γ ι h.generator (Finset.mem_singleton_self j)
    rw [hgval, hg₀ {j} ⟨h.generator j, hmem⟩]
    exact (hF {j}).2.1 j hmem (Finset.mem_singleton_self j)
  have hgrade : ∀ (n : ℕ) (a : A), a ∈ Aᵢ n → g a ∈ Dᵢ n := by
    intro n a ha
    obtain ⟨S, hS⟩ := h.finite_support a
    rw [hgval, hg₀ S ⟨a, hS⟩]
    exact (hF S).2.2.1 n ⟨a, hS⟩ ha
  have hgdpow : ∀ (n : ℕ) (a : A), a ∈ positiveEvenPart Aᵢ →
      g (γ.dpow n a) = δ.dpow n (g a) := by
    intro n a ha
    obtain ⟨S, hS⟩ := h.finite_support a
    obtain ⟨S', hS'⟩ := h.finite_support (γ.dpow n a)
    have haV : a ∈ finiteVariableStage γ ι h.generator (S ∪ S') :=
      finiteVariableStage_le_of_subset γ ι h.generator Finset.subset_union_left hS
    have hdV : γ.dpow n a ∈ finiteVariableStage γ ι h.generator (S ∪ S') :=
      finiteVariableStage_le_of_subset γ ι h.generator Finset.subset_union_right hS'
    rw [hgval, hgval, hg₀ (S ∪ S') ⟨a, haV⟩, hg₀ (S ∪ S') ⟨γ.dpow n a, hdV⟩]
    exact ((hF (S ∪ S')).2.2.2 n ⟨a, haV⟩ ⟨γ.dpow n a, hdV⟩ ha rfl).symm
  refine ⟨g, ⟨hgcoeff, hgen, hgrade, hgdpow⟩, ?_⟩
  intro g' hg'
  have hres : ∀ (S : Finset (Σ n : ℕ, h.indices n))
      (x : finiteVariableStage γ ι h.generator S),
      (g' : A →+* D) (x : A) = F S x := by
    intro S x
    have hstage : IsStageLift γ ι δ f h.generator t S
        ((g' : A →+* D).comp (finiteVariableStage γ ι h.generator S).subtype) := by
      refine ⟨fun p _ => hg'.1 p, fun j _ hjS => hg'.2.1 j, fun m y hy => hg'.2.2.1 m _ hy,
        fun n y z hy hz => ?_⟩
      simp only [RingHom.comp_apply, Subring.coe_subtype]
      rw [hz]
      exact (hg'.2.2.2 n (y : A) hy).symm
    exact isStageLift_agree γ ι δ f h.generator t Finset.Subset.rfl hstage (hF S) x x rfl
  exact AlgHom.toRingHom_injective (hg₀u (g' : A →+* D) hres)

end UniversalProperty

end DividedPowers.TateResolution

end

