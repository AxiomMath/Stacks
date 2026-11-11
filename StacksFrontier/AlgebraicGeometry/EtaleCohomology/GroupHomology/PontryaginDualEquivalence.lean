module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupHomology.CoinvariantsDuality
public import StacksFrontier.Topology.Algebra.PontryaginDual.Compact

/-!
# Trivial duality: compact and discrete `G`-modules are anti-equivalent

Let `G` be a topological group. The functors `M ↦ M^∧ = Hom_cont(M, S¹)` from compact
`G`-modules to discrete `G`-modules and back (`Stacks.GroupHomology.discreteDual`,
`Stacks.GroupHomology.compactDual`) are quasi-inverse: the evaluation maps `M → (M^∧)^∧` are
isomorphisms, by Pontryagin duality for compact and for discrete abelian groups. So the dual
exchanges the two categories, as in the paragraph "Trivial duality" of [Stacks, Tag 03VI].

## Main definitions

* `Stacks.GroupHomology.compactEvaluationIso`, `Stacks.GroupHomology.discreteEvaluationIso`: the
  evaluation maps into the double dual, as natural isomorphisms.
* `Stacks.GroupHomology.discreteDualEquivalence G`: the anti-equivalence
  `(CompactGModule G)ᵒᵖ ≌ ContinuousGModule G`, `M ↦ M^∧`.
* `Stacks.GroupHomology.compactDualEquivalence G`: the anti-equivalence
  `(ContinuousGModule G)ᵒᵖ ≌ CompactGModule G`, `M ↦ M^∧`.

## Main results

* `Stacks.GroupHomology.CompactGModule.isIso_of_bijective`: a morphism of compact `G`-modules
  which is bijective is an isomorphism.
* `Stacks.GroupHomology.compactEvaluationHom_bijective`,
  `Stacks.GroupHomology.discreteEvaluationHom_bijective`: the evaluation maps are bijective.

## References

* [Stacks Project, Tag 03VI](https://stacks.math.columbia.edu/tag/03VI)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Stacks.GroupCohomology

universe u v

namespace Stacks.GroupHomology

namespace CompactGModule

variable {G : Type u} [Group G] [TopologicalSpace G] {M N : CompactGModule.{u, v} G}

/-- The inverse of a bijective morphism of compact `G`-modules: the inverse map is continuous
because a continuous bijection from a compact space to a Hausdorff space is a homeomorphism, and
it is equivariant because its inverse is. -/
def invOfBijective (f : M ⟶ N) (hf : Function.Bijective f.hom) : N ⟶ M :=
  let e : M ≃+ N := AddEquiv.ofBijective f.hom.toAddMonoidHom hf
  ofHom
    { toAddMonoidHom := e.symm.toAddMonoidHom
      continuous_toFun :=
        (f.hom.continuous.homeoOfEquivCompactToT2 (f := e.toEquiv)).symm.continuous }
    fun g n ↦ e.injective (by
      change e (e.symm (g • n)) = e (g • e.symm n)
      rw [e.apply_symm_apply]
      change g • n = f.hom (g • e.symm n)
      rw [f.map_smul]
      exact congrArg (g • ·) (e.apply_symm_apply n).symm)

/-- **A bijective morphism of compact `G`-modules is an isomorphism.** -/
lemma isIso_of_bijective (f : M ⟶ N) (hf : Function.Bijective f.hom) : IsIso f :=
  ⟨⟨invOfBijective f hf,
    hom_ext (ContinuousAddMonoidHom.ext fun m ↦
      (AddEquiv.ofBijective f.hom.toAddMonoidHom hf).symm_apply_apply m),
    hom_ext (ContinuousAddMonoidHom.ext fun n ↦
      (AddEquiv.ofBijective f.hom.toAddMonoidHom hf).apply_symm_apply n)⟩⟩

end CompactGModule

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

open AddPontryaginDual

attribute [local instance] carrierAction carrierMulAction carrierTopology discreteTopology_carrier

section Compact

/-- **The evaluation map of a compact `G`-module into its double dual is bijective**: this is
Pontryagin duality for the compact Hausdorff abelian group `M`, the characters of its discrete
dual being automatically continuous. -/
theorem compactEvaluationHom_bijective (M : CompactGModule.{u, v} G) :
    Function.Bijective (compactEvaluationHom G M) := by
  have : T2Space (Multiplicative M) := inferInstanceAs (T2Space M)
  have hb := Stacks.Pontryagin.eval_bijective_of_compactSpace (Multiplicative M)
  refine ⟨fun a b h ↦ ?_, fun Φ ↦ ?_⟩
  · apply Multiplicative.ofAdd.injective
    refine hb.1 (PontryaginDual.ext fun χ ↦ ?_)
    have h' := congrArg (fun F ↦ (show AddPontryaginDual (discreteDualObj G M).obj.obj.V from F)
      (Additive.ofMul χ)) h
    exact h'
  · let Ψ : PontryaginDual (PontryaginDual (Multiplicative M)) :=
      ⟨(toContinuousMonoidHom
          (show AddPontryaginDual (discreteDualObj G M).obj.obj.V from Φ)).toMonoidHom,
        continuous_of_discreteTopology⟩
    obtain ⟨a, ha⟩ := hb.2 Ψ
    refine ⟨Multiplicative.toAdd a, AddPontryaginDual.ext fun χ ↦ ?_⟩
    exact DFunLike.congr_fun ha (Additive.toMul χ)

/-- The evaluation map of a compact `G`-module into its double dual is an isomorphism. -/
instance isIso_compactEvaluation_app (M : CompactGModule.{u, v} G) :
    IsIso ((compactEvaluation G).app M) :=
  CompactGModule.isIso_of_bijective _ (compactEvaluationHom_bijective G M)

instance isIso_compactEvaluation : IsIso (compactEvaluation.{u, v} G) :=
  NatIso.isIso_of_isIso_app _

/-- **Pontryagin duality for compact `G`-modules**: the evaluation map `M ≅ (M^∧)^∧`, as a
natural isomorphism. -/
def compactEvaluationIso :
    𝟭 (CompactGModule.{u, v} G) ≅ (discreteDual G).rightOp ⋙ compactDual G :=
  asIso (compactEvaluation G)

end Compact

section Discrete

/-- **The evaluation map of a discrete `G`-module into its double dual is bijective**: this is
Pontryagin duality for the discrete abelian group underlying `M`. -/
theorem discreteEvaluationHom_bijective (M : ContinuousGModule.{u, v} G) :
    Function.Bijective (discreteEvaluationHom G M) := by
  have hb := Stacks.Pontryagin.eval_bijective_of_discreteTopology (Multiplicative M.obj.obj.V)
  refine ⟨fun a b h ↦ ?_, fun Φ ↦ ?_⟩
  · apply Multiplicative.ofAdd.injective
    refine hb.1 (PontryaginDual.ext fun χ ↦ ?_)
    exact congrArg (fun F ↦ (show AddPontryaginDual (compactDualObj G M) from F)
      (Additive.ofMul χ)) h
  · obtain ⟨a, ha⟩ := hb.2 (toContinuousMonoidHom Φ)
    refine ⟨Multiplicative.toAdd a, AddPontryaginDual.ext fun χ ↦ ?_⟩
    exact DFunLike.congr_fun ha (Additive.toMul χ)

/-- The evaluation map of a discrete `G`-module into its double dual, as an isomorphism. -/
def discreteEvaluationAppIso (M : ContinuousGModule.{u, v} G) :
    M ≅ discreteDualObj G (compactDualObj G M) :=
  isoOfAddEquiv (AddEquiv.ofBijective _ (discreteEvaluationHom_bijective G M))
    (((gModuleHomEquiv G _ _) ((discreteEvaluation G).app M)).2)

/-- The isomorphism `discreteEvaluationAppIso` is the evaluation map. -/
lemma discreteEvaluationAppIso_hom (M : ContinuousGModule.{u, v} G) :
    (discreteEvaluationAppIso G M).hom = (discreteEvaluation G).app M := rfl

/-- The evaluation map of a discrete `G`-module into its double dual is an isomorphism. -/
instance isIso_discreteEvaluation_app (M : ContinuousGModule.{u, v} G) :
    IsIso ((discreteEvaluation G).app M) := by
  rw [← discreteEvaluationAppIso_hom]
  exact (discreteEvaluationAppIso G M).isIso_hom

end Discrete

instance isIso_discreteEvaluation : IsIso (discreteEvaluation.{u, v} G) :=
  NatIso.isIso_of_isIso_app _

/-- **Pontryagin duality for discrete `G`-modules**: the evaluation map `M ≅ (M^∧)^∧`, as a
natural isomorphism. -/
def discreteEvaluationIso :
    𝟭 (ContinuousGModule.{u, v} G) ≅ (compactDual G).rightOp ⋙ discreteDual G :=
  asIso (discreteEvaluation G)

/-- **Trivial duality.** The functor `M ↦ M^∧ = Hom_cont(M, S¹)` is an anti-equivalence from
compact `G`-modules to discrete `G`-modules, with quasi-inverse `M ↦ M^∧` from discrete
`G`-modules to compact `G`-modules. -/
@[stacks 03VI "M ↦ M^∧ = Hom_cont(M, S¹) exchanges compact G-modules and discrete G-modules \
(an anti-equivalence)"]
def discreteDualEquivalence : (CompactGModule.{u, v} G)ᵒᵖ ≌ ContinuousGModule.{u, v} G :=
  CategoryTheory.Equivalence.mk (discreteDual G) (compactDual G).rightOp
    (NatIso.op (compactEvaluationIso G)).symm (discreteEvaluationIso G).symm

/-- **Trivial duality, from discrete to compact.** The functor `M ↦ M^∧ = Hom(M, S¹)` is an
anti-equivalence from discrete `G`-modules to compact `G`-modules, with quasi-inverse `M ↦ M^∧`
from compact `G`-modules to discrete `G`-modules. -/
@[stacks 03VI "M ↦ M^∧ = Hom(M, S¹) exchanges discrete G-modules and compact G-modules \
(an anti-equivalence)"]
def compactDualEquivalence : (ContinuousGModule.{u, v} G)ᵒᵖ ≌ CompactGModule.{u, v} G :=
  CategoryTheory.Equivalence.mk (compactDual G) (discreteDual G).rightOp
    (NatIso.op (discreteEvaluationIso G)).symm (compactEvaluationIso G).symm

/-- The functor of `discreteDualEquivalence` is `discreteDual`. -/
@[simp] lemma discreteDualEquivalence_functor :
    (discreteDualEquivalence.{u, v} G).functor = discreteDual G := rfl

/-- The functor of `compactDualEquivalence` is `compactDual`. -/
@[simp] lemma compactDualEquivalence_functor :
    (compactDualEquivalence.{u, v} G).functor = compactDual G := rfl

end Stacks.GroupHomology
