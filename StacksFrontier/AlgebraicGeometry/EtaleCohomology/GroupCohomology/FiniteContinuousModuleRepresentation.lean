module

public import Mathlib.Algebra.Module.Shrink
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.DualTensor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.UnibranchContinuousModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.ContinuousModuleScalarAction

/-!
# A finite module with a continuous action, as a representation in a prescribed universe

An object of `Stacks.GroupCohomology.FiniteTypeContinuousModule R G` over a finite ring `R` is a
finite `R`-module with a continuous action of `G`, but its underlying module lives in the
universe the category was formed in. This file reads such an object as a `Representation` on a
module in *any* universe, with the continuity of the action expressed as the openness of the set
of group elements acting by a prescribed endomorphism, and with the two tied together by a
`Representation.Equiv`.

Three things are needed. The underlying module is finite, so it is small in every universe and
`Shrink` produces a model of it there, with its module structure transported by
`Shrink.linearEquiv`; the representation is transported along that linear equivalence by
`LinearEquiv.conjRingEquiv`, the induced isomorphism of endomorphism rings; and openness is
transported because that isomorphism is a bijection, so the two sets of group elements are
preimages of one another.

Openness itself is the finiteness of the module again: the action is locally constant in the
group variable, because the module is discrete and the action continuous
(`Stacks.ContinuousCohomology.isLocallyConstant_rep`), so for each element of the module the
group elements sending it to a prescribed value form an open set, and an endomorphism is pinned
down by finitely many such conditions. This is
`Stacks.ContinuousCohomology.isOpen_rep_eq` with the chosen generators replaced by all elements
of the module, which drops that lemma's projectivity hypothesis.

## Main results

* `Stacks.ContinuousCohomology.isOpen_rep_eq_of_finite`: the group elements acting by a
  prescribed endomorphism of a finite continuous module form an open set.
* `Stacks.GroupCohomology.exists_representation_isOpen_rep_eq`: **a finite `R`-module with a
  continuous `G`-action is a representation of `G` on a module in any prescribed universe**,
  with open endomorphism fibres, equivalent to the given one.

## References

* [Stacks Project, Tag 04JP](https://stacks.math.columbia.edu/tag/04JP)
* [Stacks Project, Tag 0DV5](https://stacks.math.columbia.edu/tag/0DV5)
-/

@[expose] public noncomputable section

open CategoryTheory

universe t r v w

namespace Stacks.ContinuousCohomology

attribute [local instance] Stacks.DiscreteModuleTopology.hasForget₂ModuleCatTopCat
  Stacks.DiscreteModuleTopology.actionDiscreteTopology

variable (R : Type r) [CommRing R] (G : Type v) [Group G] [TopologicalSpace G]

/-- **The group elements acting by a prescribed endomorphism of a finite continuous module form
an open set.** The action is locally constant in the group variable, so each element of the
module contributes an open condition, and there are finitely many of them. -/
theorem isOpen_rep_eq_of_finite (M : Stacks.Injectives.ContinuousModule.{r, v, w} R G)
    [Finite M.obj.obj.V] (φ : M.obj.obj.V →ₗ[R] M.obj.obj.V) :
    IsOpen {g : G | rep R G M g = φ} := by
  have h : {g : G | rep R G M g = φ} =
      ⋂ x : M.obj.obj.V, {g : G | rep R G M g x = φ x} := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact ⟨fun hg x ↦ by rw [hg], fun hg ↦ LinearMap.ext hg⟩
  rw [h]
  exact isOpen_iInter_of_finite fun x ↦ (isLocallyConstant_rep R G M x).isOpen_fiber _

end Stacks.ContinuousCohomology

namespace Stacks.GroupCohomology

attribute [local instance] Stacks.DiscreteModuleTopology.hasForget₂ModuleCatTopCat
  Stacks.DiscreteModuleTopology.actionDiscreteTopology

variable (R : Type r) [CommRing R] [Finite R] (G : Type v) [Group G] [TopologicalSpace G]

/-- **A finite `R`-module with a continuous `G`-action, read as a representation on a module in a
prescribed universe.** The module is finite, so it has a model in any universe; the
representation and the openness of its endomorphism fibres transport along the linear
equivalence with that model, and the `Representation.Equiv` records that nothing was lost. -/
theorem exists_representation_isOpen_rep_eq
    (M : FiniteTypeContinuousModule.{r, v, w} R G) :
    ∃ (V : Type t) (_ : AddCommGroup V) (_ : Module R V) (_ : Finite V)
      (ρ : Representation R G V),
      (∀ φ : V →ₗ[R] V, IsOpen {σ : G | ρ σ = φ}) ∧
        Nonempty (ρ.Equiv (Stacks.ContinuousCohomology.rep R G M.obj)) := by
  have hfin : Finite M.obj.obj.obj.V :=
    (moduleCat_isFG_iff_finite R M.obj.obj.obj.V).1 M.property
  have hsmall : Small.{t} M.obj.obj.obj.V := inferInstance
  set e : Shrink.{t} M.obj.obj.obj.V ≃ₗ[R] M.obj.obj.obj.V := Shrink.linearEquiv R M.obj.obj.obj.V
  refine ⟨Shrink.{t} M.obj.obj.obj.V, inferInstance, inferInstance,
    Finite.of_equiv _ (equivShrink M.obj.obj.obj.V),
    e.conjRingEquiv.symm.toMulEquiv.toMonoidHom.comp (Stacks.ContinuousCohomology.rep R G M.obj),
    fun φ ↦ ?_, ?_⟩
  · have hset : {σ : G | e.conjRingEquiv.symm.toMulEquiv.toMonoidHom.comp
          (Stacks.ContinuousCohomology.rep R G M.obj) σ = φ} =
        {σ : G | Stacks.ContinuousCohomology.rep R G M.obj σ = e.conjRingEquiv φ} := by
      ext σ
      exact e.conjRingEquiv.toEquiv.symm_apply_eq
    rw [hset]
    exact Stacks.ContinuousCohomology.isOpen_rep_eq_of_finite R G M.obj _
  · refine ⟨Representation.Equiv.mk e fun g ↦ ?_⟩
    ext z
    exact e.apply_symm_apply _

end Stacks.GroupCohomology

end
