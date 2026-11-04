module

public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.Topology.LocallyConstant.Basic
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.Basic
public import StacksFrontier.RingTheory.ContinuousDual.SmallModel
public import StacksFrontier.Algebra.Category.ModuleCat.DiscreteTopology

/-!
# The continuous module `Mᵛ ⊗ N` with the diagonal action

Let `G` be a topological group, `R` a commutative ring, and let `M` and `N` be continuous
discrete `R`-`G`-modules with `M` finite projective over `R`. The contragredient action of `G` on
`Mᵛ = Hom_R(M, R)`, given by `(g · λ)(m) = λ(g⁻¹ · m)`, together with the given action on `N`,
makes the tensor product `Mᵛ ⊗_R N` a `G`-module for the diagonal action; this is the module in
which the Ext groups out of `M` are computed by continuous group cohomology,
[Stacks, Tag 0DVE].

## Main definitions

* `Stacks.ContinuousCohomology.continuousDualTensor` — the continuous discrete `R`-`G`-module
  presenting `Mᵛ ⊗_R N`, together with the equivalence of representations identifying it with the
  diagonal action on `Mᵛ ⊗_R N`.
* `Stacks.ContinuousCohomology.dualTensorContinuousModule` — that continuous module.

## Main results

* `Stacks.ContinuousCohomology.exists_isOpen_dualTprod_eq` — local constancy of the diagonal
  action, which is the continuity statement.

## Implementation notes

`Mᵛ ⊗_R N` is *presented* by a module in the coefficient universe of `M` and `N`: a dual is a
module of maps into the base ring and so a priori lives one universe higher.
`Stacks.DualTensor.smallModel` supplies such a presentation by splitting a finite free
presentation of `M`, and the diagonal representation is transported to it.

The object is returned as a `Sigma` type pairing the continuous module with a
`Representation.Equiv` onto `Representation.tprod (Representation.dual ρ_M) ρ_N`, rather than as a
bare module: the presentation `Stacks.DualTensor.smallModel` depends on a choice of finite free
presentation of `M` and so is not canonical, and the equivalence is what pins down its meaning.

## References

* [Stacks Project, Tag 0DVE](https://stacks.math.columbia.edu/tag/0DVE)
* [Stacks Project, Tag 04JF](https://stacks.math.columbia.edu/tag/04JF)
-/


@[expose] public noncomputable section

open CategoryTheory TensorProduct

universe u v w

namespace Stacks.ContinuousCohomology

attribute [local instance] Stacks.DiscreteModuleTopology.hasForget₂ModuleCatTopCat
  Stacks.DiscreteModuleTopology.actionDiscreteTopology

variable (R : Type u) [CommRing R] (G : Type v) [Group G] [TopologicalSpace G]

/-- The representation of `G` on the underlying `R`-module of a continuous discrete
`R`-`G`-module. -/
abbrev rep (X : Stacks.Injectives.ContinuousModule.{u, v, w} R G) :
    Representation R G X.obj.obj.V :=
  ((Rep.ActionToRep R G).obj X.obj.obj).ρ

/-- The action of `G` on a continuous discrete `R`-`G`-module is locally constant in the group
variable. -/
lemma isLocallyConstant_rep (X : Stacks.Injectives.ContinuousModule.{u, v, w} R G)
    (x : X.obj.obj.V) : IsLocallyConstant (fun g : G => rep R G X g x) := by
  have hX : ContinuousSMul G
      ((forget₂ (Action (ModuleCat.{w} R) G) TopCat).obj X.obj.obj) := X.obj.property
  have hcont := (continuous_prod_of_discrete_right.mp hX.continuous_smul)
    (x : (forget₂ (Action (ModuleCat.{w} R) G) TopCat).obj X.obj.obj)
  intro s
  exact hcont.isOpen_preimage _ (isOpen_discrete _)

/-- The set of group elements acting on a finite projective `M` exactly as a given one does is
open. -/
lemma isOpen_rep_eq (M : Stacks.Injectives.ContinuousModule.{u, v, w} R G)
    [Module.Finite R M.obj.obj.V] [Module.Projective R M.obj.obj.V] (g₀ : G) :
    IsOpen {g : G | rep R G M g = rep R G M g₀} := by
  have h : {g : G | rep R G M g = rep R G M g₀} =
      ⋂ i : Fin (Stacks.DualTensor.rank R M.obj.obj.V),
        {g : G | rep R G M g (Stacks.DualTensor.gen R M.obj.obj.V i)
          = rep R G M g₀ (Stacks.DualTensor.gen R M.obj.obj.V i)} := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact ⟨fun hg i => by rw [hg], fun hg =>
      _root_.Stacks.DualTensor.linearMap_eq_of_forall_gen R M.obj.obj.V hg⟩
  rw [h]
  exact isOpen_iInter_of_finite fun i =>
    (isLocallyConstant_rep R G M _).isOpen_fiber _

/-- Group elements with the same action on `M` have the same action by inverses. -/
lemma rep_inv_eq_of_rep_eq (M : Stacks.Injectives.ContinuousModule.{u, v, w} R G) {g g₀ : G}
    (hg : rep R G M g = rep R G M g₀) : rep R G M g⁻¹ = rep R G M g₀⁻¹ := by
  have hgg : (g⁻¹ : G) = g₀⁻¹ * (g₀ * g⁻¹) := by group
  rw [hgg, map_mul, map_mul, ← hg, ← map_mul, mul_inv_cancel, map_one, mul_one]

/-- **Local constancy of the diagonal action on `Mᵛ ⊗_R N`.** Every `g₀ : G` has an open
neighbourhood on whose elements the diagonal action on a fixed `x` agrees with that of `g₀`. -/
lemma exists_isOpen_dualTprod_eq (M N : Stacks.Injectives.ContinuousModule.{u, v, w} R G)
    [Module.Finite R M.obj.obj.V] [Module.Projective R M.obj.obj.V]
    (x : Module.Dual R M.obj.obj.V ⊗[R] N.obj.obj.V) (g₀ : G) :
    ∃ U : Set G, IsOpen U ∧ g₀ ∈ U ∧ ∀ g ∈ U,
      ((rep R G M).dual.tprod (rep R G N)) g x
        = ((rep R G M).dual.tprod (rep R G N)) g₀ x := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨Set.univ, isOpen_univ, trivial, fun g _ => by simp⟩
  | tmul l y =>
    refine ⟨{g : G | rep R G M g = rep R G M g₀} ∩
      {g : G | rep R G N g y = rep R G N g₀ y},
      (isOpen_rep_eq R G M g₀).inter ((isLocallyConstant_rep R G N y).isOpen_fiber _),
      ⟨rfl, rfl⟩, fun g hg => ?_⟩
    have hM : rep R G M g⁻¹ = rep R G M g₀⁻¹ := rep_inv_eq_of_rep_eq R G M hg.1
    have hN : rep R G N g y = rep R G N g₀ y := hg.2
    simp only [Representation.tprod_apply, TensorProduct.map_tmul,
      Representation.dual_apply, Module.Dual.transpose_apply, hM, hN]
  | add x₁ x₂ h₁ h₂ =>
    obtain ⟨U₁, hU₁, hg₁, he₁⟩ := h₁
    obtain ⟨U₂, hU₂, hg₂, he₂⟩ := h₂
    exact ⟨U₁ ∩ U₂, hU₁.inter hU₂, ⟨hg₁, hg₂⟩, fun g hg => by
      rw [map_add, map_add, he₁ g hg.1, he₂ g hg.2]⟩

section Construction

variable (M N : Stacks.Injectives.ContinuousModule.{u, v, w} R G)
  [Module.Finite R M.obj.obj.V] [Module.Projective R M.obj.obj.V]

/-- The diagonal representation on `Mᵛ ⊗_R N`, transported along
`Stacks.DualTensor.smallModelEquiv` to the presentation of `Mᵛ ⊗_R N` in the coefficient
universe. -/
def dualTensorSmallRep :
    Representation R G
      (Stacks.DualTensor.smallModel R M.obj.obj.V N.obj.obj.V) :=
  ((Stacks.DualTensor.smallModelEquiv R M.obj.obj.V
      N.obj.obj.V).conjRingEquiv.toMulEquiv.toMonoidHom).comp
    ((rep R G M).dual.tprod (rep R G N))

/-- The transported representation acts on `z` by transporting `z` back to `Mᵛ ⊗_R N`, acting
diagonally there, and transporting the result forward. -/
lemma dualTensorSmallRep_apply (g : G)
    (z : Stacks.DualTensor.smallModel R M.obj.obj.V N.obj.obj.V) :
    dualTensorSmallRep R G M N g z =
      Stacks.DualTensor.smallModelEquiv R M.obj.obj.V N.obj.obj.V
        (((rep R G M).dual.tprod (rep R G N)) g
          ((Stacks.DualTensor.smallModelEquiv R M.obj.obj.V N.obj.obj.V).symm z)) := rfl

/-- The equivalence of representations identifying the transported representation with the
diagonal action on `Mᵛ ⊗_R N`. -/
def dualTensorSmallEquiv :
    (dualTensorSmallRep R G M N).Equiv ((rep R G M).dual.tprod (rep R G N)) :=
  Representation.Equiv.mk
    (Stacks.DualTensor.smallModelEquiv R M.obj.obj.V N.obj.obj.V).symm
    fun g => by
      ext z
      simp [dualTensorSmallRep]

/-- The `G`-action on the presentation of `Mᵛ ⊗_R N`, as an object of
`Action (ModuleCat R) G`. -/
def dualTensorAction : Action (ModuleCat.{w} R) G :=
  (Rep.RepToAction R G).obj (Rep.of (dualTensorSmallRep R G M N))

/-- The representation underlying `dualTensorAction` is `dualTensorSmallRep`. -/
lemma rep_dualTensorAction (g : G)
    (z : Stacks.DualTensor.smallModel R M.obj.obj.V N.obj.obj.V) :
    ((Rep.ActionToRep R G).obj (dualTensorAction R G M N)).ρ g z =
      dualTensorSmallRep R G M N g z := rfl

/-- Local constancy of the diagonal action, as an `IsLocallyConstant` statement. -/
lemma isLocallyConstant_dualTprod
    (x : Module.Dual R M.obj.obj.V ⊗[R] N.obj.obj.V) :
    IsLocallyConstant (fun g : G => ((rep R G M).dual.tprod (rep R G N)) g x) := by
  rw [IsLocallyConstant.iff_exists_open]
  exact fun g₀ => exists_isOpen_dualTprod_eq R G M N x g₀

/-- The transported diagonal action is locally constant in the group variable. -/
lemma isLocallyConstant_dualTensorSmallRep
    (z : Stacks.DualTensor.smallModel R M.obj.obj.V N.obj.obj.V) :
    IsLocallyConstant (fun g : G => dualTensorSmallRep R G M N g z) :=
  (isLocallyConstant_dualTprod R G M N
    ((Stacks.DualTensor.smallModelEquiv R M.obj.obj.V N.obj.obj.V).symm z)).comp
    (fun t => Stacks.DualTensor.smallModelEquiv R M.obj.obj.V N.obj.obj.V t)

/-- The diagonal action on the presentation of `Mᵛ ⊗_R N` is continuous for the discrete
topology. -/
lemma dualTensorAction_isContinuous :
    Action.IsContinuous (V := ModuleCat.{w} R) (dualTensorAction R G M N) := by
  rw [Action.isContinuous_def, continuous_prod_of_discrete_right]
  intro z
  apply IsLocallyConstant.continuous
  exact isLocallyConstant_dualTensorSmallRep R G M N z

/-- The continuous discrete `R`-`G`-module presenting `Mᵛ ⊗_R N` with the diagonal action,
together with the equivariant `R`-linear identification of its representation with
`Representation.tprod (Representation.dual ρ_M) ρ_N`. -/
def continuousDualTensor :
    Σ P : Stacks.Injectives.ContinuousModule.{u, v, w} R G,
      (((Rep.ActionToRep R G).obj P.obj.obj).ρ.Equiv
        (((Rep.ActionToRep R G).obj M.obj.obj).ρ.dual.tprod
          ((Rep.ActionToRep R G).obj N.obj.obj).ρ)) :=
  ⟨⟨⟨dualTensorAction R G M N, dualTensorAction_isContinuous R G M N⟩, ⟨rfl⟩⟩,
    dualTensorSmallEquiv R G M N⟩

/-- The continuous discrete `R`-`G`-module `Mᵛ ⊗_R N` with the diagonal action. -/
abbrev dualTensorContinuousModule : Stacks.Injectives.ContinuousModule.{u, v, w} R G :=
  (continuousDualTensor R G M N).1

end Construction

end Stacks.ContinuousCohomology
