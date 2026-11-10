module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.ChainPresentation

/-! # Each finite stage of a chain of set-variable extensions is a divided power polynomial algebra

`StacksFrontier/RingTheory/DividedPowers/TateResolution/ChainPresentation.lean` presents the
*colimit* of an `ω`-chain whose `n`-th step adjoins variables of degree `n + 1` as a graded
divided power polynomial algebra over the base of the chain. This file does the same for each
finite stage `B N`, whose variables are those of degrees `1, …, N`.

That is not a curiosity. The existence half of Tag 09PN only ever needs the colimit, because the
variables it adjoins in degree `n + 1` are indexed by **all** the cycles of degree `n` and
acyclicity is then free. The finiteness half has to choose a *finite generating family* of those
cycles instead, and to know that a finite family generates them it has to know that the degree-`n`
piece of the stage `n` is a finitely generated module over the base — which is read off the
monomial expansion of a presentation of that stage, by
`DividedPowers.TateResolution.GradedDividedPowerPolynomial.fg_coefficientGrade`. So the stage
presentation is the input to the choice made at each step of the finite tower, and it has to be
available stage by stage rather than only in the limit.

The two substantive fields are proved exactly as for the colimit, but with the induction bounded
by `N`. Covering by the finite variable stages is the subring trick of
`DividedPowers.TateResolution.setVariableExtension_map_mem_subring`, applied along the transition
morphisms into `B N` rather than along the structure morphisms into the colimit; freeness is the
stepwise mapping property of
`DividedPowers.TateResolution.IsSetVariableExtension.existsUnique_ringHom`, assembled up to `N`
and then read off at `N`, with the variables above degree `N` given the value zero since they do
not exist in `B N`.

## Main definitions

* `DividedPowers.TateResolution.chainStageIndices` — the variables of the chain present at the
  stage `N`: those of degree `i + 1` for `i < N`.
* `DividedPowers.TateResolution.chainStageGenerator` and
  `DividedPowers.TateResolution.chainStageCoefficient` — those variables and the base, as elements
  of and a morphism into the stage.
* `DividedPowers.TateResolution.chainStagePresentation` — the stage as a graded divided power
  polynomial algebra over the base of the chain.

## Main results

* `DividedPowers.TateResolution.chainStage_finite_support` — the finite variable stages cover
  `B N`.
* `DividedPowers.TateResolution.chainStage_hasVariableMappingProperty` — `B N` is free on the base
  and the variables of degrees `1, …, N`.
* `DividedPowers.TateResolution.finite_chainStagePresentation_indices` — the presentation of the
  stage has finitely many variables in each degree as soon as the chain does.

## Implementation notes

The base of the chain has to be concentrated in degree zero, and has to be free there: a
presentation takes its coefficient algebra to sit in degree zero, and the stepwise mapping
property has to be started off by a morphism out of `B 0` preserving degrees and divided powers,
which a morphism landing in degree zero does not automatically give. Both are recorded as
hypotheses — `hbase0` and `hbase` — rather than by fixing `B 0` to be
`DividedPowers.TateResolution.degreeZeroDPAlgebra`, which would pin the base's carrier. For
Tate's tower `DividedPowers.TateResolution.degreeZeroDPHom` supplies `hbase`.

The transition morphisms are indexed by proofs of `n ≤ N`, and the inductions below use the
inequality in the goal rather than a reconstructed one, so that `rw` sees the same proof term.
`Nat.le` is a `Prop`, so any two proofs are interchangeable for `exact`, but not for `rw`.

## References

* [Stacks Project, Tag 0F4I](https://stacks.math.columbia.edu/tag/0F4I)
* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v

section StageChain

attribute [local instance] GradedDPAlgebra.ring GradedDPAlgebra.algebra
  GradedDPAlgebra.graded GradedDPAlgebra.strict

variable {R : Type u} [CommRing R] (B : ℕ → GradedDPAlgebra.{u, v} R)
  (step : ∀ n : ℕ, GradedDPHom (B n) (B (n + 1))) (Jdx : ℕ → Type v)
  (gen : (n : ℕ) → Jdx n → (B (n + 1)).carrier)
  (hext : ∀ n : ℕ, IsSetVariableExtension (B n).grade (B n).gamma (B (n + 1)).grade
    (B (n + 1)).gamma (step n).hom (gen n) (n + 1) n.succ_pos)

/-- The transition morphism to the next stage is the step. -/
public theorem chainMap_hom_le_succ (n : ℕ) (x : (B n).carrier) :
    (chainMap B step (Nat.le_succ n)).hom x = (step n).hom x := by
  rw [chainMap_succ B step (Nat.le_refl n) (Nat.le_succ n)]
  change (step n).hom ((chainMap B step (Nat.le_refl n)).hom x) = (step n).hom x
  rw [chainMap_hom_self]

/-- **The variables of the chain present at the stage `N`**: those of degree `i + 1` for `i < N`.
The variables of higher degree are adjoined by later steps, so the index type is empty from `N`
on. -/
public abbrev chainStageIndices (N i : ℕ) : Type v := {_j : Jdx i // i < N}

/-- A variable of the stage `N`, as an element of that stage: the variable of the chain it names,
carried up along the transition morphisms. -/
public noncomputable def chainStageGenerator (N : ℕ) (j : Σ i : ℕ, chainStageIndices Jdx N i) :
    (B N).carrier :=
  (chainMap B step j.2.2).hom (gen j.1 j.2.1)

/-- The base of the chain, as a coefficient algebra of the stage `N`. -/
public noncomputable abbrev chainStageCoefficient (N : ℕ) :
    (B 0).carrier →ₐ[R] (B N).carrier :=
  (chainMap B step (Nat.zero_le N)).hom

include hext in
/-- Each variable of the stage is homogeneous of its prescribed degree: it is homogeneous in the
stage that adjoined it, and the transition morphisms preserve degrees. -/
public theorem chainStageGenerator_mem (N : ℕ) (j : Σ i : ℕ, chainStageIndices Jdx N i) :
    chainStageGenerator B step Jdx gen N j ∈ (B N).grade (j.1 + 1) :=
  (chainMap B step j.2.2).map_grade (j.1 + 1) _ ((hext j.1).generator_mem j.2.1)

include hext in
/-- **Every stage below `N` maps into the union of the finite variable stages of `B N`.** The base
lands there as a coefficient, and each successor stage is generated over its predecessor by the
variables that step adjoins together with their divided powers, all of which are variables of the
stage `N` since their degree is at most `N`. -/
public theorem chainStage_mem_variableStageUnion (N : ℕ) :
    ∀ (n : ℕ) (h : n ≤ N) (b : (B n).carrier),
      (chainMap B step h).hom b ∈
        variableStageUnion (B N).gamma (chainStageCoefficient B step N)
          (chainStageGenerator B step Jdx gen N) := by
  intro n
  induction n with
  | zero =>
      intro h b
      exact coefficient_mem_variableStageUnion (B N).gamma (chainStageCoefficient B step N)
        (chainStageGenerator B step Jdx gen N) b
  | succ n ih =>
      intro h b
      refine setVariableExtension_map_mem_subring (B (n + 1)).gamma (gen n) (hext n)
        (B N).grade (B N).gamma
        (variableStageUnion (B N).gamma (chainStageCoefficient B step N)
          (chainStageGenerator B step Jdx gen N)) (chainMap B step h).hom
        (chainMap B step h).map_dpow (fun a => ?_) (fun j => ?_) (fun j m => ?_) b
      · rw [← chainMap_hom_le_succ B step n a, chainMap_hom_trans]
        exact ih _ a
      · exact generator_mem_variableStageUnion (B N).gamma (chainStageCoefficient B step N)
          (chainStageGenerator B step Jdx gen N) ⟨n, ⟨j, h⟩⟩
      · exact dpow_generator_mem_variableStageUnion (B N).gamma (chainStageCoefficient B step N)
          (chainStageGenerator B step Jdx gen N) ⟨n, ⟨j, h⟩⟩ m

include hext in
/-- **The finite variable stages cover the stage `N`.** This is the `finite_support` field of a
presentation of `B N` over the base of the chain. -/
public theorem chainStage_finite_support (N : ℕ) (x : (B N).carrier) :
    ∃ S : Finset (Σ i : ℕ, chainStageIndices Jdx N i),
      x ∈ finiteVariableStage (B N).gamma (chainStageCoefficient B step N)
        (chainStageGenerator B step Jdx gen N) S := by
  have h := chainStage_mem_variableStageUnion B step Jdx gen hext N N (Nat.le_refl N) x
  rwa [chainMap_hom_self] at h

include hext in
/-- **The stage `N` is free on the base of the chain and the variables of degrees `1, …, N`.** A
morphism out of the base landing in degree zero, together with a homogeneous value of degree
`i + 1` for each variable of degree `i + 1` with `i < N`, extends to a divided power morphism out
of `B N`.

The extension is assembled one step at a time by
`DividedPowers.TateResolution.IsSetVariableExtension.existsUnique_ringHom`, giving a morphism out
of *every* stage of the chain; the variables of degree above `N`, which `B N` does not contain,
are sent to zero. Reading the assembled family off at `N` gives the statement. -/
public theorem chainStage_hasVariableMappingProperty
    (hbase : ∀ (E : GradedDPAlgebra.{u, v} R) (f : (B 0).carrier →ₐ[R] E.carrier),
      (∀ p : (B 0).carrier, f p ∈ E.grade 0) →
        ∃ F : GradedDPHom (B 0) E, ∀ p : (B 0).carrier, F.hom p = f p)
    (N : ℕ) :
    HasVariableMappingProperty (B N).gamma (chainStageCoefficient B step N)
      (chainStageGenerator B step Jdx gen N) := by
  classical
  intro E f hf t ht
  obtain ⟨F0, hF0⟩ := hbase E f hf
  -- The value prescribed for a variable of the chain: the given one when the variable is present
  -- in the stage `N`, and zero otherwise.
  have hchoose : ∀ k : ℕ, ∃ tk : Jdx k → E.carrier,
      (∀ j : Jdx k, tk j ∈ E.grade (k + 1)) ∧
        ∀ (j : Jdx k) (h : k < N), tk j = t ⟨k, ⟨j, h⟩⟩ := by
    intro k
    by_cases h : k < N
    · exact ⟨fun j => t ⟨k, ⟨j, h⟩⟩, fun j => ht ⟨k, ⟨j, h⟩⟩, fun _ _ => rfl⟩
    · exact ⟨fun _ => 0, fun _ => Submodule.zero_mem _, fun _ h' => absurd h' h⟩
  choose tv htv htv_eq using hchoose
  have hone : ∀ (k : ℕ) (Gk : GradedDPHom (B k) E),
      ∃ Gk1 : GradedDPHom (B (k + 1)) E,
        (∀ x : (B k).carrier, Gk1.hom ((step k).hom x) = Gk.hom x) ∧
        (∀ j : Jdx k, Gk1.hom (gen k j) = tv k j) := by
    intro k Gk
    obtain ⟨g1, hg1, -⟩ := (hext k).existsUnique_ringHom E.grade E.gamma Gk.hom.toRingHom
      (tv k) Gk.map_grade Gk.map_dpow (htv k)
    have hcomm : ∀ r : R, g1 (algebraMap R (B (k + 1)).carrier r) =
        algebraMap R E.carrier r := by
      intro r
      rw [← (step k).hom.commutes r, hg1.1]
      exact Gk.hom.commutes r
    exact ⟨⟨{ toRingHom := g1, commutes' := hcomm }, hg1.2.2.1, hg1.2.2.2⟩, hg1.1, hg1.2.1⟩
  choose stepHom hstepRestrict hstepGen using hone
  let G : (n : ℕ) → GradedDPHom (B n) E := fun n => Nat.rec F0 (fun k Gk => stepHom k Gk) n
  have hGstep : ∀ (k : ℕ) (x : (B k).carrier),
      (G (k + 1)).hom ((step k).hom x) = (G k).hom x := fun k => hstepRestrict k (G k)
  have hGgen : ∀ (k : ℕ) (j : Jdx k), (G (k + 1)).hom (gen k j) = tv k j :=
    fun k => hstepGen k (G k)
  have key : ∀ (m n : ℕ) (h : n ≤ m) (b : (B n).carrier),
      (G m).hom ((chainMap B step h).hom b) = (G n).hom b := by
    intro m
    induction m with
    | zero =>
        intro n h b
        obtain rfl := Nat.le_zero.1 h
        rw [chainMap_hom_self]
    | succ m ih =>
        intro n h b
        rcases Nat.lt_or_ge n (m + 1) with hlt | hge
        · have h' : n ≤ m := Nat.le_of_lt_succ hlt
          rw [← chainMap_hom_trans B step h' (Nat.le_succ m), chainMap_hom_le_succ, hGstep m,
            ih n h' b]
        · obtain rfl : n = m + 1 := Nat.le_antisymm h hge
          rw [chainMap_hom_self]
  refine ⟨(G N).hom.toRingHom, fun p => ?_, fun j => ?_, (G N).map_grade, (G N).map_dpow⟩
  · exact (key N 0 (Nat.zero_le N) p).trans (hF0 p)
  · obtain ⟨i, jj, hi⟩ := j
    exact (key N (i + 1) hi (gen i jj)).trans ((hGgen i jj).trans (htv_eq i jj hi))

include hext in
/-- **The stage `N` of a chain of set-variable divided power extensions is a graded divided power
polynomial algebra over the base of the chain**, on the variables of degrees `1, …, N`.

This is `DividedPowers.TateResolution.gradedDividedPowerPolynomialOfMappingProperty` fed the two
statements above. Its use is finiteness: the degree-`m` piece of the stage is spanned over the
base by the divided power monomials of degree `m` in those variables, of which there are finitely
many when the chain adjoins finitely many variables at each step. -/
@[stacks 09PN "each finite stage is a graded divided power polynomial algebra"]
public noncomputable def chainStagePresentation
    (hbase0 : ∀ p : (B 0).carrier, p ∈ (B 0).grade 0)
    (hbase : ∀ (E : GradedDPAlgebra.{u, v} R) (f : (B 0).carrier →ₐ[R] E.carrier),
      (∀ p : (B 0).carrier, f p ∈ E.grade 0) →
        ∃ F : GradedDPHom (B 0) E, ∀ p : (B 0).carrier, F.hom p = f p)
    (N : ℕ) :
    GradedDividedPowerPolynomial (B N).grade (B N).gamma (chainStageCoefficient B step N) :=
  letI : IsHomogeneousVariableFamily (B N).grade (chainStageCoefficient B step N)
      (chainStageGenerator B step Jdx gen N) :=
    { coefficient_mem := fun p =>
        (chainMap B step (Nat.zero_le N)).map_grade 0 p (hbase0 p)
      variable_homogeneous := fun j => ⟨j.1 + 1, chainStageGenerator_mem B step Jdx gen hext N j⟩ }
  gradedDividedPowerPolynomialOfMappingProperty (B N).gamma (chainStageCoefficient B step N)
    (chainStageGenerator B step Jdx gen N) (chainStageGenerator_mem B step Jdx gen hext N)
    (chainMap_injective B step (fun n => (hext n).coefficient_injective) (Nat.zero_le N))
    (chainStage_finite_support B step Jdx gen hext N)
    (chainStage_hasVariableMappingProperty B step Jdx gen hext hbase N)

/-- The variables of the presentation of the stage `N` are its variables of degrees `1, …, N`. -/
public theorem chainStagePresentation_indices
    (hbase0 : ∀ p : (B 0).carrier, p ∈ (B 0).grade 0)
    (hbase : ∀ (E : GradedDPAlgebra.{u, v} R) (f : (B 0).carrier →ₐ[R] E.carrier),
      (∀ p : (B 0).carrier, f p ∈ E.grade 0) →
        ∃ F : GradedDPHom (B 0) E, ∀ p : (B 0).carrier, F.hom p = f p)
    (N : ℕ) :
    (chainStagePresentation B step Jdx gen hext hbase0 hbase N).indices =
      chainStageIndices Jdx N := rfl

/-- **The presentation of a stage has finitely many variables in each degree** as soon as the
chain adjoins finitely many at each step. This is the hypothesis under which
`DividedPowers.TateResolution.GradedDividedPowerPolynomial.fg_coefficientGrade` makes the
homogeneous pieces of the stage finitely generated over the base, and so the hypothesis that
makes the cycles of a degree finitely generated over a Noetherian base. -/
public theorem finite_chainStagePresentation_indices [∀ i : ℕ, Finite (Jdx i)]
    (hbase0 : ∀ p : (B 0).carrier, p ∈ (B 0).grade 0)
    (hbase : ∀ (E : GradedDPAlgebra.{u, v} R) (f : (B 0).carrier →ₐ[R] E.carrier),
      (∀ p : (B 0).carrier, f p ∈ E.grade 0) →
        ∃ F : GradedDPHom (B 0) E, ∀ p : (B 0).carrier, F.hom p = f p)
    (N i : ℕ) :
    Finite ((chainStagePresentation B step Jdx gen hext hbase0 hbase N).indices i) :=
  inferInstanceAs (Finite (chainStageIndices Jdx N i))

end StageChain

end DividedPowers.TateResolution

end
