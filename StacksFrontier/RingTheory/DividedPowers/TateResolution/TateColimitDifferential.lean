module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.TateTower

/-! # The differential on the colimit of Tate's tower

`StacksFrontier/RingTheory/DividedPowers/TateResolution/TateTower.lean` builds Tate's dependent
`ω`-tower: a stage `A(n)` for each `n`, each carrying a differential, each step adjoining the
variables of degree `n + 1` that kill the prescribed cycles of degree `n`. The colimit `A` of the
tower is a graded divided power algebra, but the stagewise differentials have to be assembled into
one operator on it before it is a differential graded algebra at all.

This file performs that assembly. The operator is built as an *additive* map by
`DividedPowers.TateResolution.chainColimit_existsUnique_addHom` — a differential is not a ring
homomorphism, so the colimit's universal property for morphisms cannot be used — and upgraded to a
linear map by `DividedPowers.TateResolution.gradedDerivationToLinearMap`, which needs no linearity
hypothesis because a graded derivation kills degree zero, where the structure map lands.

Every axiom of the assembled operator is then proved by reduction to a stage, and no axiom needs
anything about the tower beyond what a chain of injective steps gives. So the construction is
carried out for an arbitrary chain of graded divided power algebras with compatible differentials
and injective steps, and instantiated at the tower afterwards: the degree-zero clause, the
degree-lowering clause and square-zeroness reduce by
`DividedPowers.TateResolution.chainColimit_exists_stage` and
`DividedPowers.TateResolution.chainColimit_mem_grade_iff`, the Leibniz rule by moving two
homogeneous elements to a common stage, and the divided power rule by
`DividedPowers.TateResolution.mem_positiveEvenPart_of_map_mem_positiveEvenPart`, which reflects the
positive even part along a structure morphism because that morphism is injective.

With the operator in hand the acyclicity statements of `TateTower.lean`, which are stated for an
arbitrary operator restricting to the differential of each stage, apply to it directly: the
colimit of Tate's tower is acyclic in positive degrees and kills the base's prescribed ideal in
degree zero.

## Main definitions

* `DividedPowers.TateResolution.tateColimitDifferential` — the differential on the colimit of
  Tate's tower.

## Main results

* `DividedPowers.TateResolution.exists_chainColimitDifferential` — the differentials of a chain of
  graded divided power algebras with injective steps assemble into a differential on the colimit,
  compatible with its divided powers.
* `DividedPowers.TateResolution.chainColimit_exists_stage_pair_mem_grade` — two homogeneous
  elements of the colimit of a chain come from homogeneous elements of a common stage, which is
  what the Leibniz rule is proved at.
* `DividedPowers.TateResolution.tateColimitDifferential_inclusion` — the differential of the
  colimit restricts to the differential of each stage of Tate's tower. This is the hypothesis the
  acyclicity statements of `TateTower.lean` take.
* `DividedPowers.TateResolution.tateColimitDga` and
  `DividedPowers.TateResolution.tateColimitCompatible` — the colimit of Tate's tower, with this
  differential, is a differential graded algebra whose divided powers are compatible with the
  differential.
* `DividedPowers.TateResolution.tateColimitDifferential_variable` — the differential of a variable
  of degree `n + 1` of the colimit is the degree-`n` cycle it was adjoined to kill.
* `DividedPowers.TateResolution.exists_tateColimitDifferential_boundary_of_cycle` and
  `DividedPowers.TateResolution.exists_tateColimitDifferential_boundary_of_base` — acyclicity in
  positive degrees and exactness at the base, for this differential.

## Implementation notes

No stage-level universal property is used, and none is available: the construction of one step
quantifies the universe of its targets inside its own existential. The additive colimit property
of `ChainColimit.lean` is universe-free in its target, which is why the operator can be assembled
at all. The *multiplicative* mapping property of the colimit is
`DividedPowers.TateResolution.tateColimit_exists_gradedDPHom`.

The square-zero clause is the one axiom that needs no grading: `D (D x) = 0` follows from
`x` coming from some stage and the differential of that stage being square-zero, with no
decomposition into homogeneous pieces.

## References

* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
* [Stacks Project, Tag 09PK](https://stacks.math.columbia.edu/tag/09PK)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v

attribute [local instance] GradedDPAlgebra.ring GradedDPAlgebra.algebra
  GradedDPAlgebra.graded GradedDPAlgebra.strict

attribute [local instance] gradedLimitGradedAlgebra gradedLimitStrictlyGradedComm

section Chain

variable {R : Type u} [CommRing R] (B : ℕ → GradedDPAlgebra.{u, v} R)
  (step : ∀ n : ℕ, GradedDPHom (B n) (B (n + 1)))

/-- Two homogeneous elements of the colimit of a chain come from homogeneous elements of a common
stage, of the same two degrees: each comes from some stage, and the transition morphisms up to the
larger of the two indices preserve homogeneous degrees.

This is what the Leibniz rule for the assembled differential is proved at: the rule relates three
values of the operator, so all three arguments have to be read off one stage. -/
public theorem chainColimit_exists_stage_pair_mem_grade (i k : ℕ)
    {x y : (chainColimit B step).carrier}
    (hx : x ∈ (chainColimit B step).grade i) (hy : y ∈ (chainColimit B step).grade k) :
    ∃ (N : ℕ) (u v : (B N).carrier), u ∈ (B N).grade i ∧ v ∈ (B N).grade k ∧
      (chainColimitInclusion B step N).hom u = x ∧
        (chainColimitInclusion B step N).hom v = y := by
  obtain ⟨n₁, u, hu, hux⟩ := (chainColimit_mem_grade_iff B step i x).1 hx
  obtain ⟨n₂, v, hv, hvy⟩ := (chainColimit_mem_grade_iff B step k y).1 hy
  refine ⟨max n₁ n₂, (chainMap B step (le_max_left n₁ n₂)).hom u,
    (chainMap B step (le_max_right n₁ n₂)).hom v,
    (chainMap B step (le_max_left n₁ n₂)).map_grade i u hu,
    (chainMap B step (le_max_right n₁ n₂)).map_grade k v hv, ?_, ?_⟩
  · exact (chainColimitInclusion_chainMap B step (le_max_left n₁ n₂) u).trans hux
  · exact (chainColimitInclusion_chainMap B step (le_max_right n₁ n₂) v).trans hvy

/-- **The differential on the colimit of a chain.** Given a differential on each stage of a chain
of graded divided power algebras, compatible with the divided powers of that stage and with the
steps, and given that each step is injective, the colimit carries a differential restricting to
each of them, making it a differential graded algebra and compatible with its divided powers.

The operator is assembled additively and upgraded to a linear map, and each of its axioms is
proved by reduction to a stage. Injectivity of the steps is needed only for the divided power
rule, to know that an element whose image is positive even is itself positive even. -/
public theorem exists_chainColimitDifferential
    (d : ∀ n : ℕ, (B n).carrier →ₗ[R] (B n).carrier)
    (hdga : ∀ n : ℕ, IsDifferentialGradedAlgebra (B n).grade (d n))
    (hcompat : ∀ n : ℕ, IsCompatibleWithDifferential (B n).gamma (d n))
    (hstep : ∀ (n : ℕ) (x : (B n).carrier),
      d (n + 1) ((step n).hom x) = (step n).hom (d n x))
    (hinj : ∀ n : ℕ, Function.Injective (step n).hom) :
    ∃ D : (chainColimit B step).carrier →ₗ[R] (chainColimit B step).carrier,
      (∀ (n : ℕ) (x : (B n).carrier),
          D ((chainColimitInclusion B step n).hom x) =
            (chainColimitInclusion B step n).hom (d n x)) ∧
        IsDifferentialGradedAlgebra (chainColimit B step).grade D ∧
          IsCompatibleWithDifferential (chainColimit B step).gamma D := by
  classical
  obtain ⟨G, hG, -⟩ := chainColimit_existsUnique_addHom B step
    (fun n => (chainColimitInclusion B step n).hom.toAddMonoidHom.comp (d n).toAddMonoidHom)
    (by
      intro n x
      change (chainColimitInclusion B step (n + 1)).hom (d (n + 1) ((step n).hom x)) =
        (chainColimitInclusion B step n).hom (d n x)
      rw [hstep n x]
      exact chainColimitInclusion_step B step n (d n x))
  have hGstage : ∀ (n : ℕ) (x : (B n).carrier),
      G ((chainColimitInclusion B step n).hom x) =
        (chainColimitInclusion B step n).hom (d n x) := fun n x => hG n x
  have hzero : ∀ x : (chainColimit B step).carrier,
      x ∈ (chainColimit B step).grade 0 → G x = 0 := by
    intro x hx
    obtain ⟨n, u, hu, rfl⟩ := (chainColimit_mem_grade_iff B step 0 x).1 hx
    rw [hGstage n u, (hdga n).d_grade_zero hu, map_zero]
  have hmem : ∀ (m : ℕ) (x : (chainColimit B step).carrier),
      x ∈ (chainColimit B step).grade (m + 1) → G x ∈ (chainColimit B step).grade m := by
    intro m x hx
    obtain ⟨n, u, hu, rfl⟩ := (chainColimit_mem_grade_iff B step (m + 1) x).1 hx
    rw [hGstage n u]
    exact (chainColimitInclusion B step n).map_grade m _
      ((hdga n).d_mem hu)
  have hleib : ∀ (i k : ℕ) (x y : (chainColimit B step).carrier),
      x ∈ (chainColimit B step).grade i → y ∈ (chainColimit B step).grade k →
        G (x * y) = G x * y + (-1 : R) ^ i • (x * G y) := by
    intro i k x y hx hy
    obtain ⟨N, u, v, hu, hv, rfl, rfl⟩ := chainColimit_exists_stage_pair_mem_grade B step i k hx hy
    rw [← map_mul (chainColimitInclusion B step N).hom u v, hGstage N (u * v), hGstage N u,
      hGstage N v, (hdga N).leibniz hu hv, map_add, map_mul, map_smul, map_mul]
  have hsq : ∀ x : (chainColimit B step).carrier, G (G x) = 0 := by
    intro x
    obtain ⟨n, u, rfl⟩ := chainColimit_exists_stage B step x
    rw [hGstage n u, hGstage n (d n u),
      (hdga n).d_sq_zero u, map_zero]
  refine ⟨gradedDerivationToLinearMap (chainColimit B step).grade G hzero hleib,
    fun n x => by rw [gradedDerivationToLinearMap_apply, hGstage n x], ?_, ?_⟩
  · exact
      { d_grade_zero := fun hx => by simpa only [gradedDerivationToLinearMap_apply] using hzero _ hx
        d_mem := fun hx => by simpa only [gradedDerivationToLinearMap_apply] using hmem _ _ hx
        d_sq_zero := fun x => by simpa only [gradedDerivationToLinearMap_apply] using hsq x
        leibniz := fun hx hy => by
          simpa only [gradedDerivationToLinearMap_apply] using hleib _ _ _ _ hx hy }
  · refine { d_dpow := ?_ }
    intro m b hm hb
    obtain ⟨n, u, rfl⟩ := chainColimit_exists_stage B step b
    have hu : u ∈ positiveEvenPart (B n).grade :=
      mem_positiveEvenPart_of_map_mem_positiveEvenPart (B n).grade (chainColimit B step).grade
        (chainColimitInclusion B step n).hom
        (fun l a ha => (chainColimitInclusion B step n).map_grade l a ha)
        (chainColimitInclusion_injective B step hinj n) hb
    rw [chainColimitInclusion_dpow B step n m u hu,
      chainColimitInclusion_dpow B step n (m - 1) u hu,
      gradedDerivationToLinearMap_apply, gradedDerivationToLinearMap_apply, hGstage n _,
      hGstage n u, (hcompat n).d_dpow hm hu, map_mul]

end Chain

section Tower

variable {R : Type u} [CommRing R] (A₀ : TateStageData.{u, v} R 0)

/-- **The differential on the colimit of Tate's tower exists.** The differentials of the stages
are compatible with the steps and the steps are injective, so
`DividedPowers.TateResolution.exists_chainColimitDifferential` applies. -/
public theorem exists_tateColimitDifferential :
    ∃ D : (tateColimit A₀).carrier →ₗ[R] (tateColimit A₀).carrier,
      (∀ (n : ℕ) (x : (tateAlgebra A₀ n).carrier),
          D ((tateInclusion A₀ n).hom x) =
            (tateInclusion A₀ n).hom (tateDifferential A₀ n x)) ∧
        IsDifferentialGradedAlgebra (tateColimit A₀).grade D ∧
          IsCompatibleWithDifferential (tateColimit A₀).gamma D :=
  exists_chainColimitDifferential (tateAlgebra A₀) (tateStep A₀) (tateDifferential A₀)
    (tateDga A₀) (tateCompatible A₀) (tateStep_differential A₀) (tateStep_injective A₀)

/-- **The differential on the colimit of Tate's tower.** It restricts to the differential of every
stage, makes the colimit a differential graded algebra, and is compatible with the colimit's
divided powers. -/
public noncomputable def tateColimitDifferential :
    (tateColimit A₀).carrier →ₗ[R] (tateColimit A₀).carrier :=
  (exists_tateColimitDifferential A₀).choose

/-- The differential of the colimit restricts to the differential of each stage of Tate's tower.
This is the hypothesis under which
`DividedPowers.TateResolution.exists_tateColimit_boundary_of_cycle` and
`DividedPowers.TateResolution.exists_tateColimit_boundary_of_base` are stated. -/
public theorem tateColimitDifferential_inclusion (n : ℕ) (x : (tateAlgebra A₀ n).carrier) :
    tateColimitDifferential A₀ ((tateInclusion A₀ n).hom x) =
      (tateInclusion A₀ n).hom (tateDifferential A₀ n x) :=
  (exists_tateColimitDifferential A₀).choose_spec.1 n x

/-- The colimit of Tate's tower, with this differential, is a differential graded algebra. -/
public theorem tateColimitDga :
    IsDifferentialGradedAlgebra (tateColimit A₀).grade (tateColimitDifferential A₀) :=
  (exists_tateColimitDifferential A₀).choose_spec.2.1

/-- The divided powers of the colimit of Tate's tower are compatible with this differential. -/
public theorem tateColimitCompatible :
    IsCompatibleWithDifferential (tateColimit A₀).gamma (tateColimitDifferential A₀) :=
  (exists_tateColimitDifferential A₀).choose_spec.2.2

/-- **The differential of a variable of degree `n + 1` of the colimit is the cycle of degree `n`
it was adjoined to kill**, read in the colimit. This is
`DividedPowers.TateResolution.tateGenerator_differential` transported along the structure
morphisms. -/
public theorem tateColimitDifferential_variable (n : ℕ) (j : tateIndex A₀ n) :
    tateColimitDifferential A₀ (tateVariable A₀ n j) =
      (tateInclusion A₀ n).hom (tateCycle A₀ n j) := by
  rw [tateVariable, tateColimitDifferential_inclusion A₀ (n + 1) (tateGenerator A₀ n j),
    tateGenerator_differential A₀ n j,
    chainColimitInclusion_step (tateAlgebra A₀) (tateStep A₀) n (tateCycle A₀ n j)]

/-- **The colimit of Tate's tower is acyclic in positive degrees.** A homogeneous cycle of degree
`n + 1` is the differential of a homogeneous element of degree `n + 2`. -/
public theorem exists_tateColimitDifferential_boundary_of_cycle (n : ℕ)
    {a : (tateColimit A₀).carrier} (ha : a ∈ (tateColimit A₀).grade (n + 1))
    (hda : tateColimitDifferential A₀ a = 0) :
    ∃ b : (tateColimit A₀).carrier, b ∈ (tateColimit A₀).grade (n + 2) ∧
      tateColimitDifferential A₀ b = a :=
  exists_tateColimit_boundary_of_cycle A₀ (tateColimitDifferential A₀)
    (tateColimitDifferential_inclusion A₀) n ha hda

/-- **Every cycle prescribed at the base of Tate's tower is a boundary in the colimit.** With the
base's family taken to be the kernel of a presentation, this is exactness in degree zero. -/
public theorem exists_tateColimitDifferential_boundary_of_base (j : tateIndex A₀ 0) :
    ∃ b : (tateColimit A₀).carrier, b ∈ (tateColimit A₀).grade 1 ∧
      tateColimitDifferential A₀ b = (tateCoefficient A₀).hom (tateCycle A₀ 0 j) :=
  exists_tateColimit_boundary_of_base A₀ (tateColimitDifferential A₀)
    (tateColimitDifferential_inclusion A₀) j

end Tower

end DividedPowers.TateResolution

end
