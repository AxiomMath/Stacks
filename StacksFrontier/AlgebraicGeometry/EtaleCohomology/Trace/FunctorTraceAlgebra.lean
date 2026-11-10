module

public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.FunctorTrace
public import StacksFrontier.LinearAlgebra.BlockTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoefficientLevelSheaf
public import StacksFrontier.CategoryTheory.Trace.Sorites.Multiplicativity

/-!
# Twisted traces along restriction of scalars to a subring

Let `S` be a commutative `R`-algebra, finite free as an `R`-module. Restriction of scalars along
`R → S` carries finite projective `S`-modules to finite projective `R`-modules, and for `c ∈ S`
the map `θ♮ : S^♮ → R^♮` induced by restriction of scalars twisted by multiplication by `c`
(`CategoryTheory.FilteredDerived.functorTraceMap`) is `t ↦ Tr_{S/R}(c t)`.

## Main results

* `Stacks.EtaleCohomology.preservesFiniteProjective_restrictScalars_algebraMap`
* `Stacks.EtaleCohomology.eval_functorTraceMap_restrictScalarsSMulNatTrans`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.FilteredDerived

universe u

namespace Stacks.EtaleCohomology

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]

/-- A module finite over a finite `R`-algebra is finite over `R`. -/
theorem finite_restrictScalars_algebraMap [Module.Finite R S] (P : Type*) [AddCommGroup P]
    [Module S P] [Module.Finite S P] :
    letI : Module R P := Module.compHom P (algebraMap R S)
    Module.Finite R P := by
  let : Module R P := Module.compHom P (algebraMap R S)
  have : IsScalarTower R S P := ⟨fun r s p => by
    change (r • s) • p = algebraMap R S r • (s • p)
    rw [Algebra.smul_def, mul_smul]⟩
  exact Module.Finite.trans S P

/-- A module projective over an `R`-algebra which is free over `R` is projective over `R`. -/
theorem projective_restrictScalars_algebraMap [Module.Free R S] (P : Type*) [AddCommGroup P]
    [Module S P] [Module.Projective S P] :
    letI : Module R P := Module.compHom P (algebraMap R S)
    Module.Projective R P := by
  let : Module R P := Module.compHom P (algebraMap R S)
  have : IsScalarTower R S P := ⟨fun r s p => by
    change (r • s) • p = algebraMap R S r • (s • p)
    rw [Algebra.smul_def, mul_smul]⟩
  rcases Module.projective_def.mp (show Module.Projective S P from inferInstance) with ⟨i, hi⟩
  let q : (P →₀ S) →ₗ[S] P := Finsupp.linearCombination S id
  exact Module.Projective.of_split (i.restrictScalars R) (q.restrictScalars R) (by
    ext x
    exact hi x)

/-- **Restriction of scalars along a finite free algebra preserves finite projective modules.** -/
theorem preservesFiniteProjective_restrictScalars_algebraMap [Module.Free R S] [Module.Finite R S] :
    PreservesFiniteProjective.{0, u + 1}
      (ModuleCat.restrictScalars.{u + 1} (algebraMap R S)) :=
  fun P _ _ =>
    ⟨finite_restrictScalars_algebraMap R S P, projective_restrictScalars_algebraMap R S P⟩

/-- Over a commutative ring every class in the additive commutator quotient is the class of its
evaluation. -/
theorem additiveCommutatorQuotientMk_eval (x : AdditiveCommutatorQuotient S) :
    additiveCommutatorQuotientMk S (Stacks.Trace.commutativeAdditiveCommutatorQuotientEval S x) =
      x := by
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
  rfl

/-- **The twisted trace along restriction of scalars to `R` is `t ↦ Tr_{S/R}(c t)`**, for `θ`
multiplication by `c`. -/
theorem eval_functorTraceMap_restrictScalarsSMulNatTrans [Module.Free R S] [Module.Finite R S]
    (c : S) (x : AdditiveCommutatorQuotient S) :
    Stacks.Trace.commutativeAdditiveCommutatorQuotientEval R
        (functorTraceMap (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))
          (restrictScalarsSMulNatTrans.{u} (algebraMap R S) c)
          (preservesFiniteProjective_restrictScalars_algebraMap.{u} R S) x) =
      Algebra.trace R S (c * Stacks.Trace.commutativeAdditiveCommutatorQuotientEval S x) := by
  rw [← additiveCommutatorQuotientMk_eval S x, functorTraceMap_mk]
  set t := Stacks.Trace.commutativeAdditiveCommutatorQuotientEval S x
  simp only [functorTraceRaw, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  unfold functorTrace
  let : Module R (ULift.{u + 1} S) := Module.compHom _ (algebraMap R S)
  let e : ((ModuleCat.restrictScalars.{u + 1} (algebraMap R S)).obj
      (regularModule.{0, u + 1} S)) ≃ₗ[R] S :=
    { toFun := fun y => (y : ULift.{u + 1} S).down
      invFun := fun s => (⟨s⟩ : ULift.{u + 1} S)
      map_add' := fun _ _ => rfl
      map_smul' := fun r y => by
        change algebraMap R S r * (y : ULift.{u + 1} S).down = r • (y : ULift.{u + 1} S).down
        rw [Algebra.smul_def]
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have : Module.Free R ((ModuleCat.restrictScalars.{u + 1} (algebraMap R S)).obj
      (regularModule.{0, u + 1} S)) := Module.Free.of_equiv e.symm
  have : Module.Finite R ((ModuleCat.restrictScalars.{u + 1} (algebraMap R S)).obj
      (regularModule.{0, u + 1} S)) := Module.Finite.equiv e.symm
  rw [Stacks.Trace.projectiveModuleTrace_eq_mk_trace]
  change LinearMap.trace R _ _ = _
  rw [← LinearMap.trace_conj' _ e, Algebra.trace_apply]
  congr 1
  refine LinearMap.ext fun s => ?_
  change c * s * t = c * t * s
  ring

end Stacks.EtaleCohomology

end
