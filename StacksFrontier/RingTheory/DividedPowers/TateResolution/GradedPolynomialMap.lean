module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.GradedPolynomial
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.EvenVariableLift

/-! # The mapping property of a graded divided power polynomial algebra

A graded divided power polynomial algebra over `P` is generated, as a ring, by the image of `P`
together with the adjoined variables and their divided powers, and it is free on that data: a map
into any graded divided power algebra may be prescribed by its restriction to `P` and the images
of the variables, and is determined by them. This is the mapping property used to compare two
such presentations, and hence to recognise one graded divided power polynomial algebra as a base
change of another.

## Main results

* `DividedPowers.TateResolution.existsUnique_gradedDividedPowerPolynomial_map` — the mapping
  property into a graded divided power algebra in an independent universe.
* `DividedPowers.TateResolution.existsUnique_algEquiv_gradedDividedPowerPolynomial` — two graded
  divided power polynomial algebras with degreewise identified index data are uniquely isomorphic
  over the coefficients and the variables, in both directions.
* `DividedPowers.TateResolution.finiteVariableStage_ringHom_eq_of_subset` and
  `DividedPowers.TateResolution.finiteVariableStage_ringHom_ext` — a ring homomorphism out of a
  finite variable stage is determined by the coefficients, the variables and their divided powers.
* `DividedPowers.TateResolution.mem_positiveEvenPart_symm_of_ringEquiv` — a degree-matching
  isomorphism onto a subring reflects the positive even part.

## Implementation notes

The map is built stage by stage over the finite subsets of the index type, using the one-variable
mapping properties of `VariableLift`, and then assembled by the directed colimit presentation
`finiteVariableStages_directedColimit`. Compatibility of the stagewise maps is not arranged by
construction but deduced: each stagewise map is *unique* subject to prescribing the coefficients,
the variables in that stage and their divided powers, so the restriction of a later stage's map
agrees with the earlier one.

Compatibility with divided powers is established once, for the assembled map, by the graph
argument `ringHom_dpow_of_finiteVariableStage`, rather than stage by stage. This is why the
stagewise invariant records only the *values* at the divided powers of the variables and not full
divided power compatibility, which the one-variable mapping properties do not supply.

## References

* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
-/

@[expose] public noncomputable section

namespace DividedPowers.TateResolution

universe u v w z

section Stage

variable {R : Type u} {P : Type v} {A : Type w} [CommRing R] [Ring P] [Algebra R P]
  [Ring A] [Algebra R A] {Aᵢ : ℕ → Submodule R A} [GradedAlgebra Aᵢ]
  [IsStrictlyGradedComm Aᵢ] {J : Type*}

/-- The image of the coefficient algebra lies in every finite variable stage. -/
public theorem mem_finiteVariableStage_coefficient (γ : DividedPowerStructure Aᵢ)
    (ι : P →ₐ[R] A) (T : J → A) (S : Finset J) (p : P) :
    ι p ∈ finiteVariableStage γ ι T S :=
  Subring.subset_closure (Or.inl ⟨p, rfl⟩)

/-- A variable of the stage lies in the stage. -/
public theorem mem_finiteVariableStage_generator (γ : DividedPowerStructure Aᵢ)
    (ι : P →ₐ[R] A) (T : J → A) {S : Finset J} {j : J} (hj : j ∈ S) :
    T j ∈ finiteVariableStage γ ι T S :=
  Subring.subset_closure (Or.inr ⟨j, hj, Or.inl rfl⟩)

/-- The divided powers of a variable of the stage lie in the stage. -/
public theorem mem_finiteVariableStage_dpow_generator (γ : DividedPowerStructure Aᵢ)
    (ι : P →ₐ[R] A) (T : J → A) {S : Finset J} {j : J} (hj : j ∈ S) (n : ℕ) :
    γ.dpow n (T j) ∈ finiteVariableStage γ ι T S :=
  Subring.subset_closure (Or.inr ⟨j, hj, Or.inr ⟨n, rfl⟩⟩)

/-- The finite variable stages increase with the finite subset indexing their variables. -/
public theorem finiteVariableStage_le_of_subset (γ : DividedPowerStructure Aᵢ)
    (ι : P →ₐ[R] A) (T : J → A) {S U : Finset J} (h : S ⊆ U) :
    finiteVariableStage γ ι T S ≤ finiteVariableStage γ ι T U := by
  refine Subring.closure_mono ?_
  rintro x (hx | ⟨j, hj, hx⟩)
  exacts [Or.inl hx, Or.inr ⟨j, h hj, hx⟩]

/-- The structure map of the ambient algebra lands in every finite variable stage: it factors
through the coefficient algebra. -/
public theorem algebraMap_mem_finiteVariableStage (γ : DividedPowerStructure Aᵢ)
    (ι : P →ₐ[R] A) (T : J → A) (S : Finset J) (r : R) :
    algebraMap R A r ∈ finiteVariableStage γ ι T S := by
  rw [← ι.commutes r]
  exact mem_finiteVariableStage_coefficient γ ι T S _

/-- **The `R`-algebra structure on a finite variable stage.** A stage is a `Subring`, so it
carries no `R`-algebra structure of its own; it contains the image of the structure map, which is
central in the ambient algebra, and that is exactly what is needed. -/
@[instance_reducible]
public def stageAlgebra (γ : DividedPowerStructure Aᵢ) (ι : P →ₐ[R] A) (T : J → A)
    (S : Finset J) : Algebra R (finiteVariableStage γ ι T S) :=
  RingHom.toAlgebra' ((algebraMap R A).codRestrict (finiteVariableStage γ ι T S)
      (algebraMap_mem_finiteVariableStage γ ι T S))
    fun r x => Subtype.ext (Algebra.commutes r (x : A))

/-- Two ring homomorphisms out of nested finite variable stages which agree on the coefficients,
on the variables of the smaller stage and on the divided powers of those variables agree wherever
both are defined. -/
public theorem finiteVariableStage_ringHom_eq_of_subset {D : Type z} [Ring D]
    (γ : DividedPowerStructure Aᵢ) (ι : P →ₐ[R] A) (T : J → A)
    {S U : Finset J} (hSU : S ⊆ U)
    (g₁ : finiteVariableStage γ ι T S →+* D) (g₂ : finiteVariableStage γ ι T U →+* D)
    (hcoeff : ∀ p : P,
      g₁ ⟨ι p, mem_finiteVariableStage_coefficient γ ι T S p⟩ =
        g₂ ⟨ι p, mem_finiteVariableStage_coefficient γ ι T U p⟩)
    (hgen : ∀ (j : J) (hj : j ∈ S),
      g₁ ⟨T j, mem_finiteVariableStage_generator γ ι T hj⟩ =
        g₂ ⟨T j, mem_finiteVariableStage_generator γ ι T (hSU hj)⟩)
    (hdpow : ∀ (j : J) (hj : j ∈ S) (n : ℕ),
      g₁ ⟨γ.dpow n (T j), mem_finiteVariableStage_dpow_generator γ ι T hj n⟩ =
        g₂ ⟨γ.dpow n (T j), mem_finiteVariableStage_dpow_generator γ ι T (hSU hj) n⟩)
    (x : A) (hx : x ∈ finiteVariableStage γ ι T S)
    (hx' : x ∈ finiteVariableStage γ ι T U) :
    g₁ ⟨x, hx⟩ = g₂ ⟨x, hx'⟩ := by
  have hle := finiteVariableStage_le_of_subset γ ι T hSU
  revert hx'
  induction hx using Subring.closure_induction with
  | mem z hz =>
      intro _
      rcases hz with ⟨p, rfl⟩ | ⟨j, hj, rfl | ⟨n, rfl⟩⟩
      · exact hcoeff p
      · exact hgen j hj
      · exact hdpow j hj n
  | zero => exact fun _ => (map_zero g₁).trans (map_zero g₂).symm
  | one => exact fun _ => (map_one g₁).trans (map_one g₂).symm
  | add a b ha hb iha ihb =>
      intro _
      exact show g₁ (⟨a, ha⟩ + ⟨b, hb⟩) = g₂ (⟨a, hle ha⟩ + ⟨b, hle hb⟩) by
        rw [map_add, map_add, iha (hle ha), ihb (hle hb)]
  | neg a ha iha =>
      intro _
      exact show g₁ (-⟨a, ha⟩) = g₂ (-⟨a, hle ha⟩) by
        rw [map_neg, map_neg, iha (hle ha)]
  | mul a b ha hb iha ihb =>
      intro _
      exact show g₁ (⟨a, ha⟩ * ⟨b, hb⟩) = g₂ (⟨a, hle ha⟩ * ⟨b, hle hb⟩) by
        rw [map_mul, map_mul, iha (hle ha), ihb (hle hb)]

/-- Two ring homomorphisms out of a finite variable stage which agree on the coefficients, on the
variables and on their divided powers are equal. -/
public theorem finiteVariableStage_ringHom_ext {D : Type z} [Ring D]
    (γ : DividedPowerStructure Aᵢ) (ι : P →ₐ[R] A) (T : J → A) (S : Finset J)
    (g₁ g₂ : finiteVariableStage γ ι T S →+* D)
    (hcoeff : ∀ p : P,
      g₁ ⟨ι p, mem_finiteVariableStage_coefficient γ ι T S p⟩ =
        g₂ ⟨ι p, mem_finiteVariableStage_coefficient γ ι T S p⟩)
    (hgen : ∀ (j : J) (hj : j ∈ S),
      g₁ ⟨T j, mem_finiteVariableStage_generator γ ι T hj⟩ =
        g₂ ⟨T j, mem_finiteVariableStage_generator γ ι T hj⟩)
    (hdpow : ∀ (j : J) (hj : j ∈ S) (n : ℕ),
      g₁ ⟨γ.dpow n (T j), mem_finiteVariableStage_dpow_generator γ ι T hj n⟩ =
        g₂ ⟨γ.dpow n (T j), mem_finiteVariableStage_dpow_generator γ ι T hj n⟩) :
    g₁ = g₂ := by
  ext x
  obtain ⟨x, hx⟩ := x
  exact finiteVariableStage_ringHom_eq_of_subset γ ι T (Finset.Subset.refl S) g₁ g₂
    hcoeff hgen hdpow x hx hx

omit [IsStrictlyGradedComm Aᵢ] in
/-- Two homogeneous elements of distinct degrees which are equal are zero. -/
public theorem eq_zero_of_mem_grade_of_mem_grade {i m : ℕ} {a : A} (him : i ≠ m)
    (hi : a ∈ Aᵢ i) (hm : a ∈ Aᵢ m) : a = 0 :=
  (DirectSum.decompose_of_mem_same Aᵢ hm).symm.trans (DirectSum.decompose_of_mem_ne Aᵢ hi him)

end Stage


section GradedComponent

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

/-- The `m`th homogeneous component of an element of a graded algebra. -/
public def gradedPart (x : A) (m : ℕ) : A := ((DirectSum.decompose 𝒜 x m : 𝒜 m) : A)

/-- A homogeneous component is homogeneous of its degree. -/
public theorem gradedPart_mem (x : A) (m : ℕ) : gradedPart 𝒜 x m ∈ 𝒜 m :=
  (DirectSum.decompose 𝒜 x m).property

/-- Every homogeneous component of zero is zero. -/
@[simp]
public theorem gradedPart_zero (m : ℕ) : gradedPart 𝒜 (0 : A) m = 0 := by
  simp [gradedPart]

/-- Taking a homogeneous component is additive. -/
public theorem gradedPart_add (x y : A) (m : ℕ) :
    gradedPart 𝒜 (x + y) m = gradedPart 𝒜 x m + gradedPart 𝒜 y m := by
  simp [gradedPart]

/-- A homogeneous element is its own component in its own degree. -/
public theorem gradedPart_of_mem_same {x : A} {m : ℕ} (hx : x ∈ 𝒜 m) :
    gradedPart 𝒜 x m = x := DirectSum.decompose_of_mem_same 𝒜 hx

/-- A homogeneous element has no component in any other degree. -/
public theorem gradedPart_of_mem_ne {x : A} {i m : ℕ} (hx : x ∈ 𝒜 i) (h : i ≠ m) :
    gradedPart 𝒜 x m = 0 := DirectSum.decompose_of_mem_ne 𝒜 hx h

/-- The homogeneous component of a finite sum is the sum of the homogeneous components. -/
public theorem gradedPart_sum {J : Type*} (s : Finset J) (a : J → A) (m : ℕ) :
    gradedPart 𝒜 (∑ i ∈ s, a i) m = ∑ i ∈ s, gradedPart 𝒜 (a i) m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, gradedPart_add, ih, Finset.sum_insert hi]

/-- The homogeneous components of a finite sum of homogeneous elements are its terms. -/
public theorem gradedPart_sum_homogeneous (s : Finset ℕ) (a : ℕ → A)
    (ha : ∀ i, a i ∈ 𝒜 i) (m : ℕ) (hm : m ∈ s) :
    gradedPart 𝒜 (∑ i ∈ s, a i) m = a m := by
  classical
  rw [gradedPart_sum,
    Finset.sum_eq_single_of_mem m hm fun i _ hne => gradedPart_of_mem_ne 𝒜 (ha i) hne]
  exact gradedPart_of_mem_same 𝒜 (ha m)

/-- The homogeneous components of an element of the positive even part vanish outside the
positive even degrees. -/
public theorem gradedPart_eq_zero_of_mem_positiveEvenPart {x : A}
    (hx : x ∈ positiveEvenPart 𝒜) {m : ℕ} (hm : ¬ ∃ k : ℕ, m = 2 * (k + 1)) :
    gradedPart 𝒜 x m = 0 := by
  induction hx using Submodule.iSup_induction' with
  | mem k y hy => exact gradedPart_of_mem_ne 𝒜 hy fun h => hm ⟨k, h.symm⟩
  | zero => simp
  | add y z _ _ ih ih' => rw [gradedPart_add, ih, ih', add_zero]

end GradedComponent

section Reflect

variable {R : Type u} {A : Type v} {E : Type w} [CommRing R] [Ring A] [Algebra R A]
  [Ring E] [Algebra R E] (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
  (ℰ : ℕ → Submodule R E) [GradedAlgebra ℰ]

/-- A ring isomorphism from a graded ring onto a subring of a graded algebra which matches
degrees reflects the positive even part: an element of the subring which is positive even in the
ambient algebra is positive even for the transported grading. -/
public theorem mem_positiveEvenPart_symm_of_ringEquiv (T : Subring A) (e : E ≃+* T)
    (hdeg : ∀ (m : ℕ) (y : E), y ∈ ℰ m ↔ ((e y : T) : A) ∈ 𝒜 m)
    {x : T} (hx : (x : A) ∈ positiveEvenPart 𝒜) :
    e.symm x ∈ positiveEvenPart ℰ := by
  classical
  set y := e.symm x
  have hey : e y = x := e.apply_symm_apply x
  have hpart : ∀ m' : ℕ, ((e (gradedPart ℰ y m') : T) : A) ∈ 𝒜 m' := fun m' =>
    (hdeg m' _).1 (gradedPart_mem ℰ y m')
  have hxsum : (x : A) = ∑ m' ∈ (DirectSum.decompose ℰ y).support,
      ((e (gradedPart ℰ y m') : T) : A) := by
    conv_lhs => rw [← hey, ← DirectSum.sum_support_decompose ℰ y]
    rw [map_sum]
    simp only [gradedPart]
    exact AddSubmonoidClass.coe_finsetSum _ _
  rw [← DirectSum.sum_support_decompose ℰ y]
  refine Submodule.sum_mem _ fun m hm => ?_
  by_cases hgood : ∃ k : ℕ, m = 2 * (k + 1)
  · obtain ⟨k, hk⟩ := hgood
    refine Submodule.mem_iSup_of_mem k ?_
    rw [← hk]
    exact gradedPart_mem ℰ y m
  · have hcomp : gradedPart 𝒜 (x : A) m = ((e (gradedPart ℰ y m) : T) : A) := by
      rw [hxsum]
      exact gradedPart_sum_homogeneous 𝒜 _
        (fun m' => ((e (gradedPart ℰ y m') : T) : A)) hpart m hm
    have h0 : ((e (gradedPart ℰ y m) : T) : A) = 0 := by
      rw [← hcomp]
      exact gradedPart_eq_zero_of_mem_positiveEvenPart 𝒜 hx hgood
    have hz : gradedPart ℰ y m = 0 := e.map_eq_zero_iff.mp (Subtype.ext h0)
    rw [show ((DirectSum.decompose ℰ y m : ℰ m) : E) = gradedPart ℰ y m from rfl, hz]
    exact Submodule.zero_mem _

end Reflect


section Lift

open EvenVariableAlgebra OddVariableExtension

variable {R : Type u} {P : Type v} {A : Type w} {D : Type z}
  [CommRing R] [Ring P] [Algebra R P] [Ring A] [Algebra R A] [Ring D] [Algebra R D]
  {Aᵢ : ℕ → Submodule R A} [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
  {γ : DividedPowerStructure Aᵢ} {ι : P →ₐ[R] A}
  (hpoly : GradedDividedPowerPolynomial Aᵢ γ ι)
  {Dᵢ : ℕ → Submodule R D} [GradedAlgebra Dᵢ] [IsStrictlyGradedComm Dᵢ]
  (δ : DividedPowerStructure Dᵢ) (f : P →ₐ[R] D)
  (t : (Σ n : ℕ, hpoly.indices n) → D)

/-- A ring homomorphism out of a finite variable stage realises the prescribed data: it restricts
to `f` on the coefficients, sends each variable of the stage to its prescribed image, sends the
divided powers of an even-degree variable to the divided powers of its image, preserves
homogeneous degrees, and is compatible with divided powers. -/
private def IsStageLift (S : Finset (Σ n : ℕ, hpoly.indices n))
    (g : finiteVariableStage γ ι hpoly.generator S →+* D) : Prop :=
  (∀ p : P, g ⟨ι p, mem_finiteVariableStage_coefficient γ ι hpoly.generator S p⟩ = f p) ∧
  (∀ (j : Σ n : ℕ, hpoly.indices n) (hj : j ∈ S),
    g ⟨hpoly.generator j, mem_finiteVariableStage_generator γ ι hpoly.generator hj⟩ = t j) ∧
  (∀ (j : Σ n : ℕ, hpoly.indices n) (hj : j ∈ S) (n : ℕ), Even (j.1 + 1) →
    g ⟨γ.dpow n (hpoly.generator j),
        mem_finiteVariableStage_dpow_generator γ ι hpoly.generator hj n⟩ = δ.dpow n (t j)) ∧
  (∀ (m : ℕ) (x : finiteVariableStage γ ι hpoly.generator S), (x : A) ∈ Aᵢ m → g x ∈ Dᵢ m) ∧
  (∀ (n : ℕ) (x : finiteVariableStage γ ι hpoly.generator S),
    (x : A) ∈ positiveEvenPart Aᵢ →
    ∀ hmem : γ.dpow n (x : A) ∈ finiteVariableStage γ ι hpoly.generator S,
      g ⟨γ.dpow n (x : A), hmem⟩ = δ.dpow n (g x))

/-- Every divided power of a variable of odd degree is zero or one, so its image under a ring
homomorphism needs no prescribing. -/
private theorem dpow_odd_generator_eq_zero_or_one (j : Σ n : ℕ, hpoly.indices n)
    (hodd : Odd (j.1 + 1)) (n : ℕ) :
    γ.dpow n (hpoly.generator j) = 0 ∨ γ.dpow n (hpoly.generator j) = 1 := by
  by_cases hmem : hpoly.generator j ∈ positiveEvenPart Aᵢ
  · rcases positiveEven_homogeneous_eq_zero_or_grade Aᵢ (hpoly.generator_mem j) hmem with
      hz | ⟨c, hc⟩
    · rw [hz]
      obtain rfl | hn := eq_or_ne n 0
      · exact Or.inr (γ.dpow_zero (Submodule.zero_mem _))
      · exact Or.inl (γ.dpow_zero_eq_zero hn)
    · exact absurd hc (by obtain ⟨q, hq⟩ := hodd; omega)
  · exact Or.inl (γ.dpow_null hmem)

/-- The divided powers of a variable have a forced image under any realisation. -/
private theorem isStageLift_dpow_generator_eq
    {S U : Finset (Σ n : ℕ, hpoly.indices n)} (hSU : S ⊆ U)
    {g₁ : finiteVariableStage γ ι hpoly.generator S →+* D}
    {g₂ : finiteVariableStage γ ι hpoly.generator U →+* D}
    (h₁ : IsStageLift hpoly δ f t S g₁) (h₂ : IsStageLift hpoly δ f t U g₂)
    (j : Σ n : ℕ, hpoly.indices n) (hj : j ∈ S) (n : ℕ) :
    g₁ ⟨γ.dpow n (hpoly.generator j),
        mem_finiteVariableStage_dpow_generator γ ι hpoly.generator hj n⟩ =
      g₂ ⟨γ.dpow n (hpoly.generator j),
        mem_finiteVariableStage_dpow_generator γ ι hpoly.generator (hSU hj) n⟩ := by
  by_cases heven : Even (j.1 + 1)
  · exact (h₁.2.2.1 j hj n heven).trans (h₂.2.2.1 j (hSU hj) n heven).symm
  · rcases dpow_odd_generator_eq_zero_or_one hpoly j (Nat.not_even_iff_odd.mp heven) n with
      hz | ho
    · rw [show (⟨γ.dpow n (hpoly.generator j),
          mem_finiteVariableStage_dpow_generator γ ι hpoly.generator hj n⟩ :
          finiteVariableStage γ ι hpoly.generator S) = 0 from Subtype.ext hz,
        show (⟨γ.dpow n (hpoly.generator j),
          mem_finiteVariableStage_dpow_generator γ ι hpoly.generator (hSU hj) n⟩ :
          finiteVariableStage γ ι hpoly.generator U) = 0 from Subtype.ext hz,
        map_zero, map_zero]
    · rw [show (⟨γ.dpow n (hpoly.generator j),
          mem_finiteVariableStage_dpow_generator γ ι hpoly.generator hj n⟩ :
          finiteVariableStage γ ι hpoly.generator S) = 1 from Subtype.ext ho,
        show (⟨γ.dpow n (hpoly.generator j),
          mem_finiteVariableStage_dpow_generator γ ι hpoly.generator (hSU hj) n⟩ :
          finiteVariableStage γ ι hpoly.generator U) = 1 from Subtype.ext ho,
        map_one, map_one]

/-- A realisation of the prescribed data on a finite variable stage is unique. -/
private theorem isStageLift_unique {S : Finset (Σ n : ℕ, hpoly.indices n)}
    {g₁ g₂ : finiteVariableStage γ ι hpoly.generator S →+* D}
    (h₁ : IsStageLift hpoly δ f t S g₁) (h₂ : IsStageLift hpoly δ f t S g₂) : g₁ = g₂ :=
  finiteVariableStage_ringHom_ext γ ι hpoly.generator S g₁ g₂
    (fun p => (h₁.1 p).trans (h₂.1 p).symm)
    (fun j hj => (h₁.2.1 j hj).trans (h₂.2.1 j hj).symm)
    (isStageLift_dpow_generator_eq hpoly δ f t (Finset.Subset.refl S) h₁ h₂)

/-- Realisations on nested stages agree wherever both are defined. -/
private theorem isStageLift_agree {S U : Finset (Σ n : ℕ, hpoly.indices n)} (hSU : S ⊆ U)
    {g₁ : finiteVariableStage γ ι hpoly.generator S →+* D}
    {g₂ : finiteVariableStage γ ι hpoly.generator U →+* D}
    (h₁ : IsStageLift hpoly δ f t S g₁) (h₂ : IsStageLift hpoly δ f t U g₂)
    (x : A) (hx : x ∈ finiteVariableStage γ ι hpoly.generator S)
    (hx' : x ∈ finiteVariableStage γ ι hpoly.generator U) :
    g₁ ⟨x, hx⟩ = g₂ ⟨x, hx'⟩ :=
  finiteVariableStage_ringHom_eq_of_subset γ ι hpoly.generator hSU g₁ g₂
    (fun p => (h₁.1 p).trans (h₂.1 p).symm)
    (fun j hj => (h₁.2.1 j hj).trans (h₂.2.1 j (hSU hj)).symm)
    (isStageLift_dpow_generator_eq hpoly δ f t hSU h₁ h₂) x hx hx'


/-- A realisation of the prescribed data exists on every finite variable stage. The empty stage is
the image of the coefficient algebra; each successor stage is the relevant one-variable extension,
and the map is extended across it by the one-variable mapping property. -/
private theorem exists_isStageLift (hf : ∀ p : P, f p ∈ Dᵢ 0)
    (ht : ∀ j : Σ n : ℕ, hpoly.indices n, t j ∈ Dᵢ (j.1 + 1))
    (S : Finset (Σ n : ℕ, hpoly.indices n)) :
    ∃ g, IsStageLift hpoly δ f t S g := by
  let instDec : DecidableEq (Σ n : ℕ, hpoly.indices n) := Classical.decEq _
  refine Finset.induction_on S ?_ ?_
  · have hsurj : ∀ x : A, x ∈ finiteVariableStage γ ι hpoly.generator (∅ : Finset _) →
        ∃ p : P, ι p = x := by
      intro x hx
      induction hx using Subring.closure_induction with
      | mem y hy =>
          rcases hy with ⟨p, rfl⟩ | ⟨c, hc, -⟩
          · exact ⟨p, rfl⟩
          · exact absurd hc (Finset.notMem_empty c)
      | zero => exact ⟨0, map_zero ι⟩
      | one => exact ⟨1, map_one ι⟩
      | add a b _ _ iha ihb =>
          obtain ⟨p, hp⟩ := iha
          obtain ⟨q, hq⟩ := ihb
          exact ⟨p + q, by rw [map_add, hp, hq]⟩
      | neg a _ iha =>
          obtain ⟨p, hp⟩ := iha
          exact ⟨-p, by rw [map_neg, hp]⟩
      | mul a b _ _ iha ihb =>
          obtain ⟨p, hp⟩ := iha
          obtain ⟨q, hq⟩ := ihb
          exact ⟨p * q, by rw [map_mul, hp, hq]⟩
    let coeffHom := ι.toRingHom.codRestrict (finiteVariableStage γ ι hpoly.generator ∅)
      (mem_finiteVariableStage_coefficient γ ι hpoly.generator ∅)
    have hbij : Function.Bijective coeffHom := by
      refine ⟨fun p q hpq => hpoly.coefficient_injective (congrArg Subtype.val hpq), ?_⟩
      intro x
      obtain ⟨p, hp⟩ := hsurj x.1 x.2
      exact ⟨p, Subtype.ext hp⟩
    let coeffEquiv := RingEquiv.ofBijective coeffHom hbij
    have hval : ∀ (p : P)
        (hx : ι p ∈ finiteVariableStage γ ι hpoly.generator (∅ : Finset _)),
        (f.toRingHom.comp coeffEquiv.symm.toRingHom) ⟨ι p, hx⟩ = f p := by
      intro p _
      exact congrArg f (coeffEquiv.symm_apply_apply p)
    have hgrade0 : ∀ (m : ℕ) (x : finiteVariableStage γ ι hpoly.generator (∅ : Finset _)),
        (x : A) ∈ Aᵢ m →
        (f.toRingHom.comp coeffEquiv.symm.toRingHom) x ∈ Dᵢ m := by
      intro m x hx
      obtain ⟨p, hp⟩ := hsurj x.1 x.2
      have hxp : x = coeffEquiv p := Subtype.ext hp.symm
      change f (coeffEquiv.symm x) ∈ Dᵢ m
      rw [hxp, coeffEquiv.symm_apply_apply]
      by_cases hm : m = 0
      · subst m
        exact hf p
      · have hz : ι p = 0 := eq_zero_of_mem_grade_of_mem_grade (Ne.symm hm)
          (hpoly.coefficient_mem p) (by rw [hp]; exact hx)
        have hp0 : p = 0 := hpoly.coefficient_injective (by rw [hz, map_zero])
        rw [hp0, map_zero]
        exact Submodule.zero_mem _
    refine ⟨f.toRingHom.comp coeffEquiv.symm.toRingHom, fun p => hval p _,
      fun c hc => absurd hc (Finset.notMem_empty c),
      fun c hc _ _ => absurd hc (Finset.notMem_empty c), hgrade0, ?_⟩
    intro n x hx hmem
    obtain ⟨p, hp⟩ := hsurj x.1 x.2
    have hz : (x : A) = 0 := by
      rcases positiveEven_homogeneous_eq_zero_or_grade Aᵢ
        (show (x : A) ∈ Aᵢ 0 by rw [← hp]; exact hpoly.coefficient_mem p) hx with hzero | ⟨c, hc⟩
      · exact hzero
      · omega
    have hgx : (f.toRingHom.comp coeffEquiv.symm.toRingHom) x = 0 := by
      rw [show x = 0 from Subtype.ext hz, map_zero]
    rw [hgx]
    by_cases hn : n = 0
    · subst n
      have h1 : γ.dpow 0 (x : A) = 1 := by
        rw [hz]; exact γ.dpow_zero (Submodule.zero_mem _)
      rw [show (⟨γ.dpow 0 (x : A), hmem⟩ :
          finiteVariableStage γ ι hpoly.generator (∅ : Finset _)) = 1 from Subtype.ext h1,
        map_one, δ.dpow_zero (Submodule.zero_mem _)]
    · have h1 : γ.dpow n (x : A) = 0 := by rw [hz]; exact γ.dpow_zero_eq_zero hn
      rw [show (⟨γ.dpow n (x : A), hmem⟩ :
          finiteVariableStage γ ι hpoly.generator (∅ : Finset _)) = 0 from Subtype.ext h1,
        map_zero, δ.dpow_zero_eq_zero hn]
  · intro j S₀ hjS₀ ih
    obtain ⟨g, hg⟩ := ih
    have hd : 0 < j.1 + 1 := Nat.zero_lt_succ j.1
    obtain ⟨aS, -, Sᵢ, gS, cS, δS, hδ, hoddbr, hevenbr⟩ := hpoly.successor S₀ j hjS₀
    let := aS
    let := gS
    let := cS
    have hlift : (∀ (m : ℕ) (b : finiteVariableStage γ ι hpoly.generator S₀),
        b ∈ Sᵢ m → (b : A) ∈ Aᵢ m) →
        (∀ (m : ℕ) (b : finiteVariableStage γ ι hpoly.generator S₀), b ∈ Sᵢ m → g b ∈ Dᵢ m) ∧
        ∀ (n : ℕ) (b : finiteVariableStage γ ι hpoly.generator S₀),
          b ∈ positiveEvenPart Sᵢ → δ.dpow n (g b) = g (δS.dpow n b) := by
      intro hSmem
      refine ⟨fun m b hb => hg.2.2.2.1 m b (hSmem m b hb), fun n b hb => ?_⟩
      have hposS : (b : A) ∈ positiveEvenPart Aᵢ := by
        induction hb using Submodule.iSup_induction' with
        | mem c b hbm => exact Submodule.mem_iSup_of_mem c (hSmem _ b hbm)
        | zero => simp
        | add b b' _ _ ih ih' => simpa using Submodule.add_mem _ ih ih'
      have hmem : γ.dpow n (b : A) ∈ finiteVariableStage γ ι hpoly.generator S₀ := by
        rw [← hδ n b hb]
        exact (δS.dpow n b).2
      rw [← hg.2.2.2.2 n b hposS hmem]
      exact congrArg g (Subtype.ext (hδ n b hb).symm)
    rcases Nat.even_or_odd (j.1 + 1) with heven | hodd
    · have instFact : Fact (Even (j.1 + 1)) := ⟨heven⟩
      obtain ⟨e, he1, he2, he3, he4⟩ := hevenbr heven
      obtain ⟨hgS, hdpowS⟩ := hlift fun m b hb => by
        rw [← he1 b]
        exact (he3 m _).1 ((EvenVariableAlgebra.coeffEmbedding_mem_grade_iff ..).2 hb)
      obtain ⟨c, hc⟩ : ∃ c, j.1 + 1 = 2 * c := by
        obtain ⟨c, hc⟩ := heven
        exact ⟨c, by omega⟩
      have htpos : t j ∈ positiveEvenPart Dᵢ := by
        refine Submodule.mem_iSup_of_mem (c - 1) ?_
        rw [show 2 * (c - 1 + 1) = j.1 + 1 by omega]
        exact ht j
      have hmon1 : EvenVariableAlgebra.monomial 1
          (1 : finiteVariableStage γ ι hpoly.generator S₀) ∈
          positiveEvenPart (EvenVariableAlgebra.grade Sᵢ (j.1 + 1)) := by
        refine Submodule.mem_iSup_of_mem (c - 1) ?_
        rw [show 2 * (c - 1 + 1) = 1 * (j.1 + 1) by omega]
        exact EvenVariableAlgebra.monomial_one_mem_grade Sᵢ (j.1 + 1) 1
      obtain ⟨k, hk, -⟩ := existsUnique_evenVariableAlgebra_ringHom Sᵢ Dᵢ δ g hgS
        (j.1 + 1) hd heven (t j) (ht j)
      have hkdpow := evenVariableAlgebra_ringHom_dpow Sᵢ δS Dᵢ δ g hdpowS
        (j.1 + 1) hd (t j) (ht j) k hk.1 hk.2.1 hk.2.2
      have hextg : ∀ (b : finiteVariableStage γ ι hpoly.generator S₀)
          (hb : (b : A) ∈ finiteVariableStage γ ι hpoly.generator (insert j S₀)),
          (k.comp e.symm.toRingHom) ⟨(b : A), hb⟩ = g b := by
        intro b hb
        have h1 : (⟨(b : A), hb⟩ :
            finiteVariableStage γ ι hpoly.generator (insert j S₀)) =
            e (EvenVariableAlgebra.coeffEmbedding b) := Subtype.ext (he1 b).symm
        change k (e.symm ⟨(b : A), hb⟩) = g b
        rw [h1, e.symm_apply_apply, hk.1]
      have hdpowgen : ∀ n : ℕ, γ.dpow n (hpoly.generator j) =
          ((e (EvenVariableAlgebra.monomial n
            (1 : finiteVariableStage γ ι hpoly.generator S₀)) :
            finiteVariableStage γ ι hpoly.generator (insert j S₀)) : A) := by
        intro n
        have h := he4 n (EvenVariableAlgebra.monomial 1 1) hmon1
        rw [he2] at h
        refine h.trans (congrArg
          (fun y => ((e y : finiteVariableStage γ ι hpoly.generator (insert j S₀)) : A)) ?_)
        exact evenVariableDividedPowerStructure_dpow_monomial_one Sᵢ δS (j.1 + 1) hd n
      refine ⟨k.comp e.symm.toRingHom, ?_, ?_, ?_, ?_, ?_⟩
      · intro p
        exact (hextg ⟨ι p, mem_finiteVariableStage_coefficient γ ι hpoly.generator S₀ p⟩
          (mem_finiteVariableStage_coefficient γ ι hpoly.generator (insert j S₀) p)).trans
          (hg.1 p)
      · intro j' hj'
        rcases Finset.mem_insert.mp hj' with rfl | hj'S
        · rw [show (⟨hpoly.generator j',
              mem_finiteVariableStage_generator γ ι hpoly.generator hj'⟩ :
              finiteVariableStage γ ι hpoly.generator (insert j' S₀)) =
              e (EvenVariableAlgebra.monomial 1 1) from Subtype.ext he2.symm]
          change k (e.symm (e (EvenVariableAlgebra.monomial 1 1))) = t j'
          rw [e.symm_apply_apply, hk.2.1 1, δ.dpow_one htpos]
        · exact (hextg ⟨hpoly.generator j',
            mem_finiteVariableStage_generator γ ι hpoly.generator hj'S⟩ _).trans
            (hg.2.1 j' hj'S)
      · intro j' hj' n heven'
        rcases Finset.mem_insert.mp hj' with rfl | hj'S
        · rw [show (⟨γ.dpow n (hpoly.generator j'),
              mem_finiteVariableStage_dpow_generator γ ι hpoly.generator hj' n⟩ :
              finiteVariableStage γ ι hpoly.generator (insert j' S₀)) =
              e (EvenVariableAlgebra.monomial n 1) from Subtype.ext (hdpowgen n)]
          change k (e.symm (e (EvenVariableAlgebra.monomial n 1))) = δ.dpow n (t j')
          rw [e.symm_apply_apply, hk.2.1 n]
        · exact (hextg ⟨γ.dpow n (hpoly.generator j'),
            mem_finiteVariableStage_dpow_generator γ ι hpoly.generator hj'S n⟩ _).trans
            (hg.2.2.1 j' hj'S n heven')
      · intro m x hx
        change k (e.symm x) ∈ Dᵢ m
        refine hk.2.2 m (e.symm x) ?_
        rw [he3 m (e.symm x), e.apply_symm_apply]
        exact hx
      · intro n x hx hmem
        have hy : e.symm x ∈ positiveEvenPart (EvenVariableAlgebra.grade Sᵢ (j.1 + 1)) :=
          mem_positiveEvenPart_symm_of_ringEquiv Aᵢ
            (EvenVariableAlgebra.grade Sᵢ (j.1 + 1)) _ e he3 hx
        have hform := he4 n (e.symm x) hy
        rw [e.apply_symm_apply] at hform
        rw [show (⟨γ.dpow n (x : A), hmem⟩ :
            finiteVariableStage γ ι hpoly.generator (insert j S₀)) =
            e ((evenVariableDividedPowerStructure (j.1 + 1) hd δS).dpow n (e.symm x))
            from Subtype.ext hform]
        change k (e.symm (e ((evenVariableDividedPowerStructure (j.1 + 1) hd δS).dpow n
          (e.symm x)))) = δ.dpow n (k (e.symm x))
        rw [e.symm_apply_apply]
        exact (hkdpow n (e.symm x) hy).symm
    · obtain ⟨e, he1, he2, he3, he4⟩ := hoddbr hodd
      obtain ⟨hgS, hdpowS⟩ := hlift fun m b hb => by
        rw [← he1 b]
        exact (he3 m _).1 (OddVariableExtension.inclusion_mem_grade Sᵢ (j.1 + 1) m hb)
      obtain ⟨k, hk, -⟩ := existsUnique_oddVariableExtension_ringHom Sᵢ Dᵢ g hgS
        (j.1 + 1) hodd (t j) (ht j)
      have hkdpow := oddVariableExtension_ringHom_dpow Sᵢ δS Dᵢ δ g hgS hdpowS
        (j.1 + 1) hd hodd (t j) (ht j) k hk.1 hk.2.1
      have hextg : ∀ (b : finiteVariableStage γ ι hpoly.generator S₀)
          (hb : (b : A) ∈ finiteVariableStage γ ι hpoly.generator (insert j S₀)),
          (k.comp e.symm.toRingHom) ⟨(b : A), hb⟩ = g b := by
        intro b hb
        have h1 : (⟨(b : A), hb⟩ :
            finiteVariableStage γ ι hpoly.generator (insert j S₀)) =
            e (OddVariableExtension.inclusion Sᵢ (j.1 + 1) b) := Subtype.ext (he1 b).symm
        change k (e.symm ⟨(b : A), hb⟩) = g b
        rw [h1, e.symm_apply_apply, hk.1]
      refine ⟨k.comp e.symm.toRingHom, ?_, ?_, ?_, ?_, ?_⟩
      · intro p
        exact (hextg ⟨ι p, mem_finiteVariableStage_coefficient γ ι hpoly.generator S₀ p⟩
          (mem_finiteVariableStage_coefficient γ ι hpoly.generator (insert j S₀) p)).trans
          (hg.1 p)
      · intro j' hj'
        rcases Finset.mem_insert.mp hj' with rfl | hj'S
        · rw [show (⟨hpoly.generator j',
              mem_finiteVariableStage_generator γ ι hpoly.generator hj'⟩ :
              finiteVariableStage γ ι hpoly.generator (insert j' S₀)) =
              e (OddVariableExtension.generator Sᵢ (j'.1 + 1)) from Subtype.ext he2.symm]
          change k (e.symm (e (OddVariableExtension.generator Sᵢ (j'.1 + 1)))) = t j'
          rw [e.symm_apply_apply, hk.2.1]
        · exact (hextg ⟨hpoly.generator j',
            mem_finiteVariableStage_generator γ ι hpoly.generator hj'S⟩ _).trans
            (hg.2.1 j' hj'S)
      · intro j' hj' n heven'
        rcases Finset.mem_insert.mp hj' with rfl | hj'S
        · exact absurd heven' (Nat.not_even_iff_odd.mpr hodd)
        · exact (hextg ⟨γ.dpow n (hpoly.generator j'),
            mem_finiteVariableStage_dpow_generator γ ι hpoly.generator hj'S n⟩ _).trans
            (hg.2.2.1 j' hj'S n heven')
      · intro m x hx
        change k (e.symm x) ∈ Dᵢ m
        refine hk.2.2 m (e.symm x) ?_
        rw [he3 m (e.symm x), e.apply_symm_apply]
        exact hx
      · intro n x hx hmem
        have hy : e.symm x ∈
            positiveEvenPart (OddVariableExtension.grade Sᵢ (j.1 + 1)) :=
          mem_positiveEvenPart_symm_of_ringEquiv Aᵢ
            (OddVariableExtension.grade Sᵢ (j.1 + 1)) _ e he3 hx
        have hform := he4 n (e.symm x) hy
        rw [e.apply_symm_apply] at hform
        rw [show (⟨γ.dpow n (x : A), hmem⟩ :
            finiteVariableStage γ ι hpoly.generator (insert j S₀)) =
            e ((oddVariableDividedPowerStructure Sᵢ δS (j.1 + 1) hd hodd).dpow n (e.symm x))
            from Subtype.ext hform]
        change k (e.symm (e ((oddVariableDividedPowerStructure Sᵢ δS (j.1 + 1) hd hodd).dpow n
          (e.symm x)))) = δ.dpow n (k (e.symm x))
        rw [e.symm_apply_apply]
        exact (hkdpow n (e.symm x) hy).symm

/-- The mapping property of an iterated graded divided-power polynomial algebra.
The target may live in a universe independent of the source and its variables. -/
@[stacks 09PN "mapping property"]
public theorem existsUnique_gradedDividedPowerPolynomial_map
    {R : Type u} {P : Type v} {A : Type w} {D : Type z}
    [CommRing R] [Ring P] [Algebra R P] [Ring A] [Algebra R A]
    [Ring D] [Algebra R D]
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ]
    [IsStrictlyGradedComm Aᵢ] (γ : DividedPowerStructure Aᵢ)
    (ι : P →ₐ[R] A) (h : GradedDividedPowerPolynomial Aᵢ γ ι)
    (Dᵢ : ℕ → Submodule R D) [GradedAlgebra Dᵢ]
    [IsStrictlyGradedComm Dᵢ] (δ : DividedPowerStructure Dᵢ)
    (f : P →ₐ[R] D) (hf : ∀ p : P, f p ∈ Dᵢ 0)
    (t : (Σ n : ℕ, h.indices n) → D)
    (ht : ∀ j, t j ∈ Dᵢ (j.1 + 1)) :
    ∃! g : A →ₐ[R] D,
      (∀ p : P, g (ι p) = f p) ∧
      (∀ j : Σ n : ℕ, h.indices n, g (h.generator j) = t j) ∧
      (∀ (n : ℕ) (a : A), a ∈ Aᵢ n → g a ∈ Dᵢ n) ∧
      (∀ (n : ℕ) (a : A), a ∈ positiveEvenPart Aᵢ →
        g (γ.dpow n a) = δ.dpow n (g a)) := by
  classical
  choose gS hgS using exists_isStageLift h δ f t hf ht
  have hcompat : ∀ (S U : Finset (Σ n : ℕ, h.indices n))
      (x : finiteVariableStage γ ι h.generator S)
      (y : finiteVariableStage γ ι h.generator U),
      (x : A) = (y : A) → gS S x = gS U y := by
    intro S U x y hxy
    have hxu : (x : A) ∈ finiteVariableStage γ ι h.generator (S ∪ U) :=
      finiteVariableStage_le_of_subset γ ι h.generator Finset.subset_union_left x.2
    have hyu : (y : A) ∈ finiteVariableStage γ ι h.generator (S ∪ U) :=
      finiteVariableStage_le_of_subset γ ι h.generator Finset.subset_union_right y.2
    rw [isStageLift_agree h δ f t Finset.subset_union_left (hgS S) (hgS (S ∪ U)) (x : A) x.2 hxu,
      isStageLift_agree h δ f t Finset.subset_union_right (hgS U) (hgS (S ∪ U)) (y : A) y.2 hyu]
    exact congrArg (gS (S ∪ U)) (Subtype.ext hxy)
  obtain ⟨G, hG, hGuniq⟩ := finiteVariableStages_directedColimit Aᵢ γ ι h.generator
    h.finite_support gS hcompat
  have hGcoeff : ∀ p : P, G (ι p) = f p := by
    intro p
    rw [hG ∅ ⟨ι p, mem_finiteVariableStage_coefficient γ ι h.generator ∅ p⟩]
    exact (hgS ∅).1 p
  have hGalg : ∀ r : R, G (algebraMap R A r) = algebraMap R D r := by
    intro r
    rw [← ι.commutes r, hGcoeff, f.commutes r]
  have hGgen : ∀ j : Σ n : ℕ, h.indices n, G (h.generator j) = t j := by
    intro j
    rw [hG {j} ⟨h.generator j, mem_finiteVariableStage_generator γ ι h.generator
      (Finset.mem_singleton_self j)⟩]
    exact (hgS {j}).2.1 j (Finset.mem_singleton_self j)
  have hGgrade : ∀ (n : ℕ) (a : A), a ∈ Aᵢ n → G a ∈ Dᵢ n := by
    intro n a ha
    obtain ⟨S, hS⟩ := h.finite_support a
    rw [hG S ⟨a, hS⟩]
    exact (hgS S).2.2.2.1 n ⟨a, hS⟩ ha
  have hGdpow : ∀ (n : ℕ) (a : A), a ∈ positiveEvenPart Aᵢ →
      G (γ.dpow n a) = δ.dpow n (G a) := by
    intro n a ha
    obtain ⟨S, hS⟩ := h.finite_support a
    obtain ⟨S', hS'⟩ := h.finite_support (γ.dpow n a)
    have haV : a ∈ finiteVariableStage γ ι h.generator (S ∪ S') :=
      finiteVariableStage_le_of_subset γ ι h.generator Finset.subset_union_left hS
    have hdV : γ.dpow n a ∈ finiteVariableStage γ ι h.generator (S ∪ S') :=
      finiteVariableStage_le_of_subset γ ι h.generator Finset.subset_union_right hS'
    rw [hG (S ∪ S') ⟨γ.dpow n a, hdV⟩, hG (S ∪ S') ⟨a, haV⟩]
    exact (hgS (S ∪ S')).2.2.2.2 n ⟨a, haV⟩ ha hdV
  refine ⟨{ G with commutes' := hGalg }, ⟨hGcoeff, hGgen, hGgrade, hGdpow⟩, ?_⟩
  intro g' hg'
  have hkey : ∀ (S : Finset (Σ n : ℕ, h.indices n))
      (x : finiteVariableStage γ ι h.generator S),
      g'.toRingHom (x : A) = gS S x := by
    intro S x
    have hstage : IsStageLift h δ f t S
        (g'.toRingHom.comp (finiteVariableStage γ ι h.generator S).subtype) := by
      refine ⟨fun p => hg'.1 p, fun j hj => hg'.2.1 j, fun j hj n heven => ?_,
        fun m y hy => hg'.2.2.1 m (y : A) hy, fun n y hy hmem => ?_⟩
      · obtain ⟨c, hc⟩ : ∃ c, j.1 + 1 = 2 * c := by
          obtain ⟨c, hc⟩ := heven
          exact ⟨c, by omega⟩
        have hgenpos : h.generator j ∈ positiveEvenPart Aᵢ := by
          refine mem_positiveEvenPart_of_mem_grade Aᵢ (d := c) (by omega) ?_
          rw [← hc]
          exact h.generator_mem j
        change g' (γ.dpow n (h.generator j)) = δ.dpow n (t j)
        rw [hg'.2.2.2 n (h.generator j) hgenpos, hg'.2.1 j]
      · change g' (γ.dpow n (y : A)) = δ.dpow n (g' (y : A))
        exact hg'.2.2.2 n (y : A) hy
    exact DFunLike.congr_fun (isStageLift_unique h δ f t hstage (hgS S)) x
  have heq : g'.toRingHom = G := hGuniq g'.toRingHom hkey
  exact AlgHom.ext fun a => DFunLike.congr_fun heq a


/-- A graded, divided power compatible algebra map out of a graded divided power polynomial
algebra and a graded, divided power compatible map back, which fix the coefficients and variables
on the round trip, compose to the identity. -/
private theorem comp_eq_id_of_gradedDividedPowerPolynomial
    {R : Type u} {P : Type v} {A : Type w} {A' : Type z}
    [CommRing R] [Ring P] [Algebra R P] [Ring A] [Algebra R A] [Ring A'] [Algebra R A']
    {Aᵢ : ℕ → Submodule R A} [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
    {γ : DividedPowerStructure Aᵢ} {ι : P →ₐ[R] A}
    (h : GradedDividedPowerPolynomial Aᵢ γ ι)
    {Aᵢ' : ℕ → Submodule R A'} [GradedAlgebra Aᵢ'] [IsStrictlyGradedComm Aᵢ']
    {γ' : DividedPowerStructure Aᵢ'} (g : A →ₐ[R] A') (g' : A' →ₐ[R] A)
    (hcoeff : ∀ p : P, g' (g (ι p)) = ι p) (hgen : ∀ j, g' (g (h.generator j)) = h.generator j)
    (hgrade : ∀ (n : ℕ) (a : A), a ∈ Aᵢ n → g a ∈ Aᵢ' n)
    (hgrade' : ∀ (n : ℕ) (a : A'), a ∈ Aᵢ' n → g' a ∈ Aᵢ n)
    (hdpow : ∀ (n : ℕ) (a : A), a ∈ positiveEvenPart Aᵢ → g (γ.dpow n a) = γ'.dpow n (g a))
    (hdpow' : ∀ (n : ℕ) (a : A'), a ∈ positiveEvenPart Aᵢ' →
      g' (γ'.dpow n a) = γ.dpow n (g' a)) :
    g'.comp g = AlgHom.id R A := by
  obtain ⟨w, -, huniq⟩ := existsUnique_gradedDividedPowerPolynomial_map Aᵢ γ ι h Aᵢ γ ι
    h.coefficient_mem h.generator h.generator_mem
  refine (huniq (g'.comp g) ⟨hcoeff, hgen, fun n a ha => hgrade' n _ (hgrade n a ha),
    fun n a ha => ?_⟩).trans
    (huniq (AlgHom.id R A) ⟨fun p => rfl, fun j => rfl, fun n a ha => ha,
      fun n a _ => rfl⟩).symm
  exact (congrArg g' (hdpow n a ha)).trans
    (hdpow' n _ (algHom_mem_positiveEvenPart Aᵢ Aᵢ' g hgrade ha))

/-- Two graded divided power polynomial algebras over the same coefficient algebra, whose index
data are identified degreewise, are uniquely isomorphic over the coefficients and the variables,
and the isomorphism preserves the grading and the divided powers in both directions. This is the
form in which one recognises a graded divided power polynomial algebra as a base change of
another. -/
@[stacks 09PN "uniqueness of the presentation"]
public theorem existsUnique_algEquiv_gradedDividedPowerPolynomial
    {R : Type u} {P : Type v} {A : Type w} {A' : Type z}
    [CommRing R] [Ring P] [Algebra R P] [Ring A] [Algebra R A] [Ring A'] [Algebra R A']
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
    (γ : DividedPowerStructure Aᵢ) (ι : P →ₐ[R] A)
    (h : GradedDividedPowerPolynomial Aᵢ γ ι)
    (Aᵢ' : ℕ → Submodule R A') [GradedAlgebra Aᵢ'] [IsStrictlyGradedComm Aᵢ']
    (γ' : DividedPowerStructure Aᵢ') (ι' : P →ₐ[R] A')
    (h' : GradedDividedPowerPolynomial Aᵢ' γ' ι')
    (σ : (Σ n : ℕ, h.indices n) ≃ (Σ n : ℕ, h'.indices n))
    (hσ : ∀ j, (σ j).1 = j.1) :
    ∃! e : A ≃ₐ[R] A',
      (∀ p : P, e (ι p) = ι' p) ∧
      (∀ j, e (h.generator j) = h'.generator (σ j)) ∧
      (∀ (n : ℕ) (a : A), a ∈ Aᵢ n → e a ∈ Aᵢ' n) ∧
      (∀ (n : ℕ) (a : A), a ∈ positiveEvenPart Aᵢ → e (γ.dpow n a) = γ'.dpow n (e a)) ∧
      (∀ (n : ℕ) (a : A'), a ∈ Aᵢ' n → e.symm a ∈ Aᵢ n) ∧
      (∀ (n : ℕ) (a : A'), a ∈ positiveEvenPart Aᵢ' →
        e.symm (γ'.dpow n a) = γ.dpow n (e.symm a)) := by
  classical
  have hσ' : ∀ j' : Σ n : ℕ, h'.indices n, (σ.symm j').1 = j'.1 := by
    intro j'
    have hh := hσ (σ.symm j')
    rw [σ.apply_symm_apply] at hh
    exact hh.symm
  obtain ⟨g, hg, hguniq⟩ := existsUnique_gradedDividedPowerPolynomial_map Aᵢ γ ι h Aᵢ' γ' ι'
    h'.coefficient_mem (fun j => h'.generator (σ j))
    (fun j => by rw [← hσ j]; exact h'.generator_mem (σ j))
  obtain ⟨g', hg', hg'uniq⟩ := existsUnique_gradedDividedPowerPolynomial_map Aᵢ' γ' ι' h' Aᵢ γ ι
    h.coefficient_mem (fun j' => h.generator (σ.symm j'))
    (fun j' => by rw [← hσ' j']; exact h.generator_mem (σ.symm j'))
  have hid := comp_eq_id_of_gradedDividedPowerPolynomial h g g' (fun p => by rw [hg.1, hg'.1])
    (fun j => by rw [hg.2.1, hg'.2.1, σ.symm_apply_apply]) hg.2.2.1 hg'.2.2.1 hg.2.2.2 hg'.2.2.2
  have hid' := comp_eq_id_of_gradedDividedPowerPolynomial h' g' g (fun p => by rw [hg'.1, hg.1])
    (fun j => by rw [hg'.2.1, hg.2.1, σ.apply_symm_apply]) hg'.2.2.1 hg.2.2.1 hg'.2.2.2 hg.2.2.2
  refine ⟨AlgEquiv.ofAlgHom g g' hid' hid, ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2,
    hg'.2.2.1, hg'.2.2.2⟩, ?_⟩
  intro e he
  have hcoe : e.toAlgHom = g := hguniq e.toAlgHom ⟨he.1, he.2.1, he.2.2.1, he.2.2.2.1⟩
  exact AlgEquiv.ext fun a => DFunLike.congr_fun hcoe a


end Lift

end DividedPowers.TateResolution

end
