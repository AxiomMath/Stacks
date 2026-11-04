module

public import StacksFrontier.Algebra.DGA.SourceProjective
public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import StacksCore.Tactic.StacksAttribute

/-!
# An acyclic graded-free differential graded module that is not source-projective

Over a field `k`, the dual-number algebra `k[ε]/(ε²)` placed in degree zero is a differential
graded algebra with zero differential.  It carries a differential graded module with one free
rank-one component in every integer degree, whose differential is multiplication by `ε`.  That
module is acyclic, yet its identity is nonzero in the homotopy category, so it is not
source-projective: graded freeness does not imply source-projectivity.

## Main definitions

* `Stacks.DifferentialGradedModule.SourceProjective.dualNumberAlgebra`: the dual-number algebra as
  a differential graded algebra
  concentrated in degree zero.
* `Stacks.DifferentialGradedModule.SourceProjective.dualNumberModule`: its doubly infinite rank-one
  complex.
* `Stacks.DifferentialGradedModule.SourceProjective.gradedFreeEquiv`: the identification of the
  underlying graded module with a direct
  sum of shifted copies of the regular module.
* `Stacks.DifferentialGradedModule.SourceProjective.gradedPieceEquiv`: the identification of each
  graded component with the dual
  numbers.

## Main results

* `Stacks.DifferentialGradedModule.SourceProjective.dualNumberAlgebra_carrier`,
  `Stacks.DifferentialGradedModule.SourceProjective.dualNumberAlgebra_algebraMap`,
  `Stacks.DifferentialGradedModule.SourceProjective.dualNumberAlgebra_grading`,
  `Stacks.DifferentialGradedModule.SourceProjective.dualNumberAlgebra_differential`: the
  algebra is the dual numbers, with its regular scalars, concentrated in degree zero, and with
  zero differential.
* `Stacks.DifferentialGradedModule.SourceProjective.gradedFreeEquiv_mem_iff`,
  `Stacks.DifferentialGradedModule.SourceProjective.dualNumberModule_differential`: graded
  freeness of the module, and its differential in the chosen coordinates.
* `Stacks.DifferentialGradedModule.SourceProjective.dualNumberModule_acyclic`: the module is
  acyclic.
* `Stacks.DifferentialGradedModule.SourceProjective.dualNumberModule_homotopy_id_ne_zero`: its
  identity is nonzero in the homotopy
  category.
* `Stacks.DifferentialGradedModule.SourceProjective.dualNumberModule_not_sourceProjective`: it is
  not source-projective.

## Implementation notes

The grading of the algebra is `⊤` in degree zero and `⊥` elsewhere, and the module is the direct
sum over `ℤ` of copies of the regular module, graded by the summand index.  The differential
sends the `n`-th summand into the `(n+1)`-st by right multiplication by `ε`; it squares to zero
because `ε² = 0`, and it is right `A`-linear because the algebra is commutative in the relevant
sense — the right multiplication is by a central element of the opposite algebra.

Acyclicity is exactness in each degree, which in the chosen coordinates is the statement that
every dual number killed by `ε` is `ε` times another one — true because `ε · (a + bε) = aε`, so a
dual number killed by `ε` has zero first coordinate.

Nonvanishing of the identity in the homotopy category is the absence of a contracting homotopy:
a homotopy `h` from the identity to zero would give `1 = d(h(x₀)) + h(ε · x₁)` in the degree-zero
summand, and both terms on the right have zero first coordinate — the first because the
differential's image does, the second because `ε` does.

## References

* [Stacks Project, Tag 09R0](https://stacks.math.columbia.edu/tag/09R0)
-/

@[expose] public section

open CategoryTheory
open scoped DirectSum

universe u

namespace Stacks.DifferentialGradedModule.SourceProjective

variable (k : Type u) [Field k]

/-- The grading of the dual numbers that concentrates them in degree zero. -/
def dnAlgGrading (n : ℤ) : Submodule (DualNumber k) (DualNumber k) :=
  if n = 0 then ⊤ else ⊥

/-- The decomposition map witnessing that the dual numbers are concentrated in degree zero:
everything is sent to the degree-zero summand. -/
noncomputable def dnAlgDecompose :
    DualNumber k →ₗ[DualNumber k] ⨁ n : ℤ, ↥(dnAlgGrading k n) := by
  classical
  let f : DualNumber k →ₗ[DualNumber k] ↥(dnAlgGrading k 0) :=
    LinearMap.codRestrict _ (LinearMap.id) (by intro x; simp [dnAlgGrading])
  exact DirectSum.lof (DualNumber k) ℤ (fun n => ↥(dnAlgGrading k n)) 0 ∘ₗ f

/-- The degree-zero grading of the dual numbers is a direct-sum decomposition. -/
@[instance_reducible] noncomputable def dnAlgGradingDecomposition :
    DirectSum.Decomposition (dnAlgGrading k) := by
  classical
  refine DirectSum.Decomposition.ofLinearMap (dnAlgGrading k) (dnAlgDecompose k) ?_ ?_
  · apply LinearMap.ext
    intro x
    simp [dnAlgDecompose, DirectSum.coeLinearMap]
  · apply LinearMap.ext
    intro z
    induction z using DirectSum.induction_on with
    | zero => simp
    | of n x =>
      by_cases hn : n = 0
      · subst n
        simp only [dnAlgDecompose, LinearMap.comp_apply, DirectSum.coeLinearMap_of,
          DirectSum.lof_eq_of]
        apply congrArg (DirectSum.of (fun i => ↥(dnAlgGrading k i)) 0)
        apply Subtype.ext
        rfl
      · have hx : (x : DualNumber k) = 0 := by simpa [dnAlgGrading, hn] using x.property
        have hx0 : x = 0 := Subtype.ext hx
        subst hx0
        simp
    | add z₁ z₂ hz₁ hz₂ => rw [map_add, map_add, hz₁, hz₂]

/-- The unit of the dual numbers is homogeneous of degree zero. -/
theorem dnAlgGradedOne : SetLike.GradedOne (dnAlgGrading k) :=
  ⟨by simp [dnAlgGrading]⟩

/-- The degree-zero grading of the dual numbers is multiplicative. -/
theorem dnAlgGradedMul : SetLike.GradedMul (dnAlgGrading k) := by
  classical
  refine ⟨?_⟩
  intro i j x y hx hy
  by_cases hi : i = 0 <;> by_cases hj : j = 0
  · subst i; subst j; simp [dnAlgGrading]
  · have hy0 : y = 0 := by simpa [dnAlgGrading, hj] using hy
    simp [hy0, dnAlgGrading]
  · have hx0 : x = 0 := by simpa [dnAlgGrading, hi] using hx
    simp [hx0, dnAlgGrading]
  · have hx0 : x = 0 := by simpa [dnAlgGrading, hi] using hx
    simp [hx0, dnAlgGrading]

/-- **Stacks Project, Tag 09R0.** The dual-number algebra, as a differential graded algebra
concentrated in degree zero. -/
@[stacks 09R0 "dual_number_counterexample"]
noncomputable def dualNumberAlgebra :
    DifferentialGradedAlgebra.{u, u} (DualNumber k) := by
  classical
  letI : DirectSum.Decomposition (dnAlgGrading k) := dnAlgGradingDecomposition k
  letI : SetLike.GradedOne (dnAlgGrading k) := dnAlgGradedOne k
  letI : SetLike.GradedMul (dnAlgGrading k) := dnAlgGradedMul k
  letI : SetLike.GradedMonoid (dnAlgGrading k) :=
    { toGradedOne := dnAlgGradedOne k
      toGradedMul := dnAlgGradedMul k }
  letI : GradedRing (dnAlgGrading k) :=
    { toGradedMonoid := inferInstance
      toDecomposition := dnAlgGradingDecomposition k }
  exact
    { A := DualNumber k
      ring := inferInstance
      isAlg := inferInstance
      grading := dnAlgGrading k
      gradedAlg := inferInstance
      d := 0
      d_comp_d := by simp
      d_mem := by intro n a _; exact Submodule.zero_mem _
      leibniz := by intro n m a b _ _; simp }

/-- **Stacks Project, Tag 09R0.** The differential graded algebra has exactly the dual-number
ring as its underlying algebra. -/
@[stacks 09R0 "dual_number_counterexample"]
theorem dualNumberAlgebra_carrier : (dualNumberAlgebra k).A = DualNumber k := rfl

/-- **Stacks Project, Tag 09R0.** The scalar structure on the concentrated algebra is the
regular one. -/
@[stacks 09R0 "dual_number_counterexample"]
theorem dualNumberAlgebra_algebraMap (r : DualNumber k) :
    cast (dualNumberAlgebra_carrier k)
      (algebraMap (DualNumber k) (dualNumberAlgebra k).A r) = r := rfl

/-- **Stacks Project, Tag 09R0.** The differential graded algebra is concentrated in degree
zero. -/
@[stacks 09R0 "dual_number_counterexample"]
theorem dualNumberAlgebra_grading (n : ℤ) :
    (dualNumberAlgebra k).grading n = if n = 0 then ⊤ else ⊥ := rfl

/-- **Stacks Project, Tag 09R0.** The differential graded algebra has zero differential. -/
@[stacks 09R0 "dual_number_counterexample"]
theorem dualNumberAlgebra_differential : (dualNumberAlgebra k).d = 0 := rfl

/- `dualNumberAlgebra` is made `instance_reducible` for the rest of this file.  Its underlying
algebra `(dualNumberAlgebra k).A` *is* `DualNumber k`, but only after unfolding a semireducible
definition, so without this every goal about the module mixes the two spellings, is "not
type-correct under the `implicit` transparency level", and neither `rw`, `simp` nor instance
search can cross the gap — `Module (DualNumber k) (dualNumberAlgebra k).A` is unsynthesizable
even though it is the dual numbers' own module structure.  This is an attribute rather than a
`set_option`; `instance_reducible` rather than `implicit_reducible` because the instance search
above needs it at the `instances` level. -/
attribute [local instance_reducible] dualNumberAlgebra

/-- The dual-number generator `ε`, read in the underlying algebra of the differential graded
algebra. -/
noncomputable def dnEpsInA : (dualNumberAlgebra k).A := (DualNumber.eps : DualNumber k)

/-- The square of `ε` vanishes in the underlying algebra. -/
theorem dnEpsInA_mul_self : dnEpsInA k * dnEpsInA k = 0 :=
  DualNumber.eps_mul_eps

/-- The underlying module of the counterexample: one copy of the regular module in every
integer degree. -/
noncomputable abbrev dnModuleCarrier := ⨁ _ : ℤ, MulOpposite (dualNumberAlgebra k).A

/-- The grading of the counterexample: the `n`-th graded piece is the `n`-th summand. -/
noncomputable def dnModuleGrading (n : ℤ) :
    Submodule (DualNumber k) (dnModuleCarrier k) :=
  LinearMap.range (DirectSum.lof (DualNumber k) ℤ
    (fun _ : ℤ => MulOpposite (dualNumberAlgebra k).A) n)

/-- The inclusion of the `n`-th copy of the regular module into the `n`-th graded piece. -/
noncomputable def dnModuleGradeInclusion (n : ℤ) :
    MulOpposite (dualNumberAlgebra k).A →ₗ[DualNumber k] ↥(dnModuleGrading k n) :=
  LinearMap.codRestrict (dnModuleGrading k n)
    (DirectSum.lof (DualNumber k) ℤ
      (fun _ : ℤ => MulOpposite (dualNumberAlgebra k).A) n)
    (fun x => ⟨x, rfl⟩)

/-- The decomposition map of the counterexample's grading, summand by summand. -/
noncomputable def dnModuleDecompose :
    dnModuleCarrier k →ₗ[DualNumber k] ⨁ n : ℤ, ↥(dnModuleGrading k n) :=
  DirectSum.lmap (dnModuleGradeInclusion k)

/-- The summand grading of the counterexample is a direct-sum decomposition. -/
@[instance_reducible] noncomputable def dnModuleGradingDecomposition :
    DirectSum.Decomposition (dnModuleGrading k) := by
  classical
  refine DirectSum.Decomposition.ofLinearMap (dnModuleGrading k) (dnModuleDecompose k) ?_ ?_
  · apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, dnModuleDecompose, DirectSum.lmap_lof,
      DirectSum.coeLinearMap_lof, dnModuleGradeInclusion]
    rfl
  · apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro x
    rcases x.property with ⟨a, h⟩
    have hx : x = ⟨DirectSum.lof (DualNumber k) ℤ
        (fun _ : ℤ => MulOpposite (dualNumberAlgebra k).A) i a, ⟨a, rfl⟩⟩ :=
      Subtype.ext h.symm
    rw [hx]
    simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof, dnModuleDecompose,
      DirectSum.lmap_lof, dnModuleGradeInclusion]
    apply congrArg (fun z : ↥(dnModuleGrading k i) =>
      DirectSum.lof (DualNumber k) ℤ (fun j => ↥(dnModuleGrading k j)) i z)
    apply Subtype.ext
    rfl

/-- The differential of the counterexample as a map of right modules: right multiplication by
`ε`, moving the summand index up by one. -/
noncomputable def dnModuleDifferentialOpp :
    dnModuleCarrier k →ₗ[MulOpposite (dualNumberAlgebra k).A] dnModuleCarrier k := by
  classical
  exact DirectSum.toModule (MulOpposite (dualNumberAlgebra k).A) ℤ (dnModuleCarrier k) fun n =>
    (DirectSum.lof (MulOpposite (dualNumberAlgebra k).A) ℤ
        (fun _ : ℤ => MulOpposite (dualNumberAlgebra k).A) (n + 1)).comp
      (LinearMap.mulRight (MulOpposite (dualNumberAlgebra k).A)
        (MulOpposite.op (dnEpsInA k)))

/-- The differential of the counterexample, read `R`-linearly. -/
noncomputable def dnModuleDifferential :
    dnModuleCarrier k →ₗ[DualNumber k] dnModuleCarrier k :=
  (dnModuleDifferentialOpp k).restrictScalars (DualNumber k)

/-- The differential on a single summand is right multiplication by `ε` into the next one. -/
theorem dnModuleDifferentialOpp_lof (n : ℤ)
    (a : MulOpposite (dualNumberAlgebra k).A) :
    dnModuleDifferentialOpp k (DirectSum.lof (MulOpposite (dualNumberAlgebra k).A) ℤ
      (fun _ : ℤ => MulOpposite (dualNumberAlgebra k).A) n a) =
      DirectSum.lof (MulOpposite (dualNumberAlgebra k).A) ℤ
        (fun _ : ℤ => MulOpposite (dualNumberAlgebra k).A) (n + 1)
        (a * MulOpposite.op (dnEpsInA k)) := by
  simp [dnModuleDifferentialOpp, DirectSum.toModule_lof, LinearMap.comp_apply,
    LinearMap.mulRight_apply]

/-- **Stacks Project, Tag 09R0.** The doubly infinite complex of free rank-one dual-number
modules. -/
@[stacks 09R0 "dual_number_counterexample"]
noncomputable def dualNumberModule :
    DifferentialGradedModule.{u, u, u} (dualNumberAlgebra k) := by
  classical
  letI : DirectSum.Decomposition (dnModuleGrading k) := dnModuleGradingDecomposition k
  exact
    { M := dnModuleCarrier k
      addCommGroup := inferInstance
      module := inferInstance
      rmodule := (inferInstance : Module (MulOpposite (dualNumberAlgebra k).A)
        (dnModuleCarrier k))
      isScalarTower := by
        change IsScalarTower (DualNumber k) (MulOpposite (dualNumberAlgebra k).A)
          (dnModuleCarrier k)
        exact inferInstance
      grading := dnModuleGrading k
      decomposition := inferInstance
      smul_mem := by
        intro n m x a hx ha
        change x ∈ LinearMap.range _ at hx
        rcases hx with ⟨y, rfl⟩
        by_cases hm : m = 0
        · subst m
          refine ⟨(MulOpposite.op a) • y, ?_⟩
          have hs := (DirectSum.lof (MulOpposite (dualNumberAlgebra k).A) ℤ
            (fun _ : ℤ => MulOpposite (dualNumberAlgebra k).A) n).map_smul
              (MulOpposite.op a) y
          simpa only [DirectSum.lof_eq_of, add_zero] using hs
        · have ha0 : a = 0 := by
            rw [dualNumberAlgebra_grading] at ha
            simpa [hm] using ha
          subst ha0
          simp
      d := dnModuleDifferential k
      d_comp_d := by
        apply LinearMap.ext
        intro x
        induction x using DirectSum.induction_on with
        | zero => simp [dnModuleDifferential, dnModuleDifferentialOpp]
        | of n a =>
          rw [← DirectSum.lof_eq_of (R := MulOpposite (dualNumberAlgebra k).A)]
          simp only [dnModuleDifferential, LinearMap.restrictScalars_apply,
            LinearMap.comp_apply, dnModuleDifferentialOpp_lof]
          rw [mul_assoc, ← MulOpposite.op_mul, dnEpsInA_mul_self, MulOpposite.op_zero,
            mul_zero]
          simp
        | add x y hx hy => simp only [map_add, hx, hy]
      d_mem := by
        intro n x hx
        change x ∈ LinearMap.range _ at hx
        rcases hx with ⟨y, rfl⟩
        refine ⟨y * MulOpposite.op (dnEpsInA k), ?_⟩
        simpa only [DirectSum.lof_eq_of, dnModuleDifferential,
          LinearMap.restrictScalars_apply] using (dnModuleDifferentialOpp_lof k n y).symm
      leibniz := by
        intro n m x a _ _
        change dnModuleDifferentialOpp k (MulOpposite.op a • x) =
          MulOpposite.op a • dnModuleDifferentialOpp k x +
            (n.negOnePow : ℤ) • (MulOpposite.op (0 : (dualNumberAlgebra k).A) • x)
        simp only [MulOpposite.op_zero, zero_smul, smul_zero, add_zero]
        exact (dnModuleDifferentialOpp k).map_smul (MulOpposite.op a) x }

/- `dualNumberModule` is made `implicit_reducible` for the same reason: its underlying module
`(dualNumberModule k).M` *is* the direct sum, but only after unfolding a semireducible
definition, so a goal naming both spellings is not type-correct at `implicit` transparency and no
rewrite fires in it.  Again an attribute, not a `set_option`. -/
attribute [local implicit_reducible] dualNumberModule

/-- **Stacks Project, Tag 09R0.** An isomorphism from the graded module to a direct sum of
shifted copies of its regular module. -/
@[stacks 09R0 "dual_number_counterexample"]
noncomputable def gradedFreeEquiv :
    (dualNumberModule k).M ≃ₗ[MulOpposite (dualNumberAlgebra k).A]
      (⨁ _ : ℤ, MulOpposite (dualNumberAlgebra k).A) := by
  delta dualNumberModule
  exact LinearEquiv.refl (MulOpposite (dualNumberAlgebra k).A) (dnModuleCarrier k)

/-- **Stacks Project, Tag 09R0.** The direct-sum coordinates identify each homogeneous piece
with its corresponding shifted copy of the regular module. -/
@[stacks 09R0 "dual_number_counterexample"]
theorem gradedFreeEquiv_mem_iff (n : ℤ) (x : (dualNumberModule k).M) :
    x ∈ (dualNumberModule k).grading n ↔
      ∃ a : MulOpposite (dualNumberAlgebra k).A,
        gradedFreeEquiv k x =
          DirectSum.lof (MulOpposite (dualNumberAlgebra k).A) ℤ
            (fun _ => MulOpposite (dualNumberAlgebra k).A) n a := by
  show (x : dnModuleCarrier k) ∈ dnModuleGrading k n ↔ _
  show x ∈ LinearMap.range (DirectSum.lof (DualNumber k) ℤ
    (fun _ : ℤ => MulOpposite (dualNumberAlgebra k).A) n) ↔ _
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, ha.symm⟩

/-- **Stacks Project, Tag 09R0.** The chosen regular-module coordinates on a homogeneous
component. -/
@[stacks 09R0 "dual_number_counterexample"]
noncomputable def gradedPieceEquiv (n : ℤ) :
    ((dualNumberModule k).grading n) ≃ₗ[DualNumber k] DualNumber k := by
  classical
  let f : MulOpposite (dualNumberAlgebra k).A →ₗ[DualNumber k] dnModuleCarrier k :=
    DirectSum.lof (DualNumber k) ℤ
      (fun _ : ℤ => MulOpposite (dualNumberAlgebra k).A) n
  have hf : Function.Injective f := by
    intro a b hab
    have h := congrArg (DirectSum.component (DualNumber k) ℤ
      (fun _ : ℤ => MulOpposite (dualNumberAlgebra k).A) n) hab
    simpa [f] using h
  let e : MulOpposite (dualNumberAlgebra k).A ≃ₗ[DualNumber k]
      ↥(dnModuleGrading k n) := LinearEquiv.ofInjective f hf
  change ↥(dnModuleGrading k n) ≃ₗ[DualNumber k] DualNumber k
  exact e.symm.trans (MulOpposite.opLinearEquiv (DualNumber k)).symm

private theorem gradedPieceEquiv_lof (n : ℤ)
    (a : MulOpposite (dualNumberAlgebra k).A) :
    gradedPieceEquiv k n ⟨DirectSum.lof (DualNumber k) ℤ
      (fun _ : ℤ => MulOpposite (dualNumberAlgebra k).A) n a, ⟨a, rfl⟩⟩ =
      MulOpposite.unop a := by
  classical
  simp only [gradedPieceEquiv, id_eq, LinearEquiv.trans_apply,
    MulOpposite.coe_opLinearEquiv_symm, MulOpposite.unop_inj]
  exact (LinearEquiv.symm_apply_eq _).2 rfl

/-- **Stacks Project, Tag 09R0.** In the regular coordinates, the differential is multiplication
by `ε`. -/
@[stacks 09R0 "dual_number_counterexample"]
theorem dualNumberModule_differential (n : ℤ) (x : (dualNumberModule k).grading n) :
    gradedPieceEquiv k (n + 1) ((dualNumberModule k).gradedDifferential n x) =
      DualNumber.eps * gradedPieceEquiv k n x := by
  classical
  rcases x.property with ⟨a, ha⟩
  have hx : x = ⟨DirectSum.lof (DualNumber k) ℤ
      (fun _ : ℤ => MulOpposite (dualNumberAlgebra k).A) n a, ⟨a, rfl⟩⟩ :=
    Subtype.ext ha.symm
  subst hx
  have hdiff : (dualNumberModule k).gradedDifferential n
      ⟨DirectSum.lof (DualNumber k) ℤ
        (fun _ : ℤ => MulOpposite (dualNumberAlgebra k).A) n a, ⟨a, rfl⟩⟩ =
      ⟨DirectSum.lof (DualNumber k) ℤ
        (fun _ : ℤ => MulOpposite (dualNumberAlgebra k).A) (n + 1)
        (a * MulOpposite.op (dnEpsInA k)),
        ⟨a * MulOpposite.op (dnEpsInA k), rfl⟩⟩ :=
    Subtype.ext (dnModuleDifferentialOpp_lof k n a)
  rw [hdiff, gradedPieceEquiv_lof, gradedPieceEquiv_lof, MulOpposite.unop_mul,
    MulOpposite.unop_op]
  rfl

/-- A dual number killed by `ε` is `ε` times another one. -/
private theorem eps_preimage {S : Type*} [Semiring S] {x : DualNumber S}
    (hx : DualNumber.eps * x = 0) :
    ∃ y : DualNumber S, DualNumber.eps * y = x := by
  have hx₀ : x.fst = 0 := by simpa [DualNumber.snd_mul] using congrArg TrivSqZeroExt.snd hx
  refine ⟨TrivSqZeroExt.inl x.snd, ?_⟩
  ext <;> simp [hx₀]

private theorem gradedDifferential_exact (n : ℤ)
    (x : (dualNumberModule k).grading (n + 1))
    (hx : (dualNumberModule k).gradedDifferential (n + 1) x = 0) :
    ∃ y : (dualNumberModule k).grading n,
      (dualNumberModule k).gradedDifferential n y = x := by
  have hx' : DualNumber.eps * gradedPieceEquiv k (n + 1) x = 0 := by
    have h := congrArg (gradedPieceEquiv k (n + 1 + 1)) hx
    rw [dualNumberModule_differential] at h
    exact h.trans ((gradedPieceEquiv k (n + 1 + 1)).map_zero)
  obtain ⟨a, ha⟩ := eps_preimage hx'
  refine ⟨(gradedPieceEquiv k n).symm a, ?_⟩
  apply (gradedPieceEquiv k (n + 1)).injective
  simpa only [dualNumberModule_differential, LinearEquiv.apply_symm_apply] using ha

/-- **Stacks Project, Tag 09R0.** The doubly infinite complex is acyclic. -/
@[stacks 09R0 "dual_number_counterexample"]
theorem dualNumberModule_acyclic :
    DifferentialGradedModule.acyclic (dualNumberAlgebra k)
      ((DifferentialGradedModule.toHomotopyCategory (dualNumberAlgebra k)).obj
        (dualNumberModule k)) := by
  show (dualNumberModule k).toCochainComplex.Acyclic
  rw [HomologicalComplex.acyclic_iff]
  intro n
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, n = m + 1 := ⟨n - 1, by omega⟩
  rw [HomologicalComplex.exactAt_iff' _ m (m + 1) (m + 1 + 1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  show ∀ x : (dualNumberModule k).grading (m + 1),
    (dualNumberModule k).toCochainComplex.d (m + 1) (m + 1 + 1) x = 0 →
      ∃ y : (dualNumberModule k).grading m,
        (dualNumberModule k).toCochainComplex.d m (m + 1) y = x
  simp only [DifferentialGradedModule.toCochainComplex_d]
  exact gradedDifferential_exact k m

private theorem differential_component_fst (n : ℤ) (x : dnModuleCarrier k) :
    (MulOpposite.unop (DirectSum.component (MulOpposite (dualNumberAlgebra k).A) ℤ
      (fun _ : ℤ => MulOpposite (dualNumberAlgebra k).A) n
      (dnModuleDifferential k x))).fst = 0 := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i a =>
    rw [← DirectSum.lof_eq_of (R := MulOpposite (dualNumberAlgebra k).A)]
    simp only [dnModuleDifferential, LinearMap.restrictScalars_apply,
      dnModuleDifferentialOpp_lof]
    by_cases h : i + 1 = n
    · subst h
      simp only [DirectSum.component.lof_self, MulOpposite.unop_mul, MulOpposite.unop_op]
      show (DualNumber.eps * (MulOpposite.unop a : DualNumber k)).fst = 0
      simp
    · simp [DirectSum.component.of, h]
  | add x y hx hy =>
    simp only [map_add, MulOpposite.unop_add]
    show (_ + _ : DualNumber k).fst = 0
    rw [TrivSqZeroExt.fst_add, hx, hy, add_zero]

/-- The identity of the complex is not homotopic to zero: a contracting homotopy would make
`1 : k` vanish. -/
private theorem not_homotopic_id_zero :
    ¬ DifferentialGradedModule.Homotopic (𝟙 (dualNumberModule k)) 0 := by
  classical
  rintro ⟨h⟩
  let x (n : ℤ) : dnModuleCarrier k :=
    DirectSum.lof (MulOpposite (dualNumberAlgebra k).A) ℤ
      (fun _ : ℤ => MulOpposite (dualNumberAlgebra k).A) n 1
  let h' : dnModuleCarrier k →ₗ[MulOpposite (dualNumberAlgebra k).A]
      dnModuleCarrier k := h.toLinearMap
  have hd : dnModuleDifferential k (x 0) = MulOpposite.op (dnEpsInA k) • x 1 := by
    show dnModuleDifferentialOpp k (x 0) = _
    simp [x, dnModuleDifferentialOpp_lof, ← map_smul, smul_eq_mul]
  have hh := h.homotopy_eq (x 0)
  change x 0 - 0 = dnModuleDifferential k (h' (x 0)) +
    h' (dnModuleDifferential k (x 0)) at hh
  rw [sub_zero, hd, map_smul] at hh
  have hc := congrArg (fun y : dnModuleCarrier k =>
    (MulOpposite.unop (DirectSum.component (MulOpposite (dualNumberAlgebra k).A) ℤ
      (fun _ : ℤ => MulOpposite (dualNumberAlgebra k).A) 0 y)).fst) hh
  have hone : (1 : k) = 0 := by
    simp only [map_add, map_smul, smul_eq_mul, MulOpposite.unop_add,
      MulOpposite.unop_mul, MulOpposite.unop_op] at hc
    simp only [x, DirectSum.component.lof_self, MulOpposite.unop_one] at hc
    change (1 : k) = (_ + _ * (DualNumber.eps : DualNumber k)).fst at hc
    simpa only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_mul, DualNumber.fst_eps, mul_zero,
      differential_component_fst, add_zero] using hc
  exact one_ne_zero hone

/-- **Stacks Project, Tag 09R0.** The identity of the complex survives passage to the homotopy
category. -/
@[stacks 09R0 "dual_number_counterexample"]
theorem dualNumberModule_homotopy_id_ne_zero :
    (𝟙 ((DifferentialGradedModule.toHomotopyCategory (dualNumberAlgebra k)).obj
      (dualNumberModule k))) ≠ 0 := by
  intro h
  apply not_homotopic_id_zero k
  apply (CategoryTheory.Quotient.functor_map_eq_iff
    (DifferentialGradedModule.homotopyRel (dualNumberAlgebra k)) _ _).mp
  simpa using h

/-- **Stacks Project, Tag 09R0.** Graded freeness does not imply source-projectivity: the
acyclic graded-free module above is not source-projective. -/
@[stacks 09R0 "dual_number_counterexample"]
theorem dualNumberModule_not_sourceProjective :
    ¬ sourceProjective (dualNumberAlgebra k)
      ((DifferentialGradedModule.toHomotopyCategory (dualNumberAlgebra k)).obj
        (dualNumberModule k)) := by
  intro h
  have hz : ((DifferentialGradedModule.quasiIsomorphisms (dualNumberAlgebra k)).Q).kernel
      ((DifferentialGradedModule.toHomotopyCategory (dualNumberAlgebra k)).obj
        (dualNumberModule k)) := by
    rw [DifferentialGradedModule.localization_kernel_eq_acyclic]
    exact dualNumberModule_acyclic k
  exact dualNumberModule_homotopy_id_ne_zero k ((h (dualNumberModule k)).injective
    (hz.eq_of_src _ _))

end Stacks.DifferentialGradedModule.SourceProjective

end
