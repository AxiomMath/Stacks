module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupHomology.DerivedCoinvariants

/-!
# The action of a group on the derived coinvariants of a normal subgroup

Let `Γ` be a topological group, `G` a normal subgroup and `V` a `Λ`-module with an action of `Γ`
commuting with `Λ`, on which some open normal subgroup of `G` acts trivially; for instance a finite
module with a continuous action of a compact group. Then `V` is a module over the completed group
algebra `Λ[[G]]`, and an element `γ ∈ Γ` acts on `V` semilinearly with respect to the automorphism
of `Λ[[G]]` induced by conjugation `x ↦ γ x γ⁻¹` of `G`. Hence `γ` induces an endomorphism of the
derived coinvariants `LH₀(G, V) = V ⊗^L_{Λ[[G]]} Λ`. This is the action of `Γ` (through `Γ/G`) on
`LH₀(G, V)` of [Stacks, Tag 03VI] and of the abstract trace formula of [Stacks, Section 03VO].

All names are in the namespace `Stacks.GroupHomology`.

## Main definitions

* `conjContinuousMulEquiv`: conjugation by `γ` on a normal subgroup, as an automorphism of
  topological groups.
* `completedGroupAlgebraModule`: the `Λ[[G]]`-module structure on `V`, and
  `toCompletedGroupAlgebraModuleCat` the resulting object of `ModuleCat Λ[[G]]`.
* `conjActionHom`: the action of `γ`, as a morphism `V ⟶ σ_γ^* V`.
* `derivedCoinvariantsAction`: the induced endomorphism of `LH₀(G, V)`.

## References

* [Stacks Project, Tag 03VI](https://stacks.math.columbia.edu/tag/03VI)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Stacks.GroupHomology

open CompletedGroupAlgebra MonoidAlgebra

attribute [local instance] HasDerivedCategory.standard

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (G : Subgroup Γ)
  [G.Normal]

/-- Conjugation `x ↦ γ x γ⁻¹` on a normal subgroup, as an automorphism of topological groups. -/
public def conjContinuousMulEquiv (γ : Γ) : G ≃ₜ* G where
  toMulEquiv := MulAut.conjNormal γ
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const

/-- Conjugation by `γ` sends `x` to `γ x γ⁻¹`. -/
@[simp]
public theorem conjContinuousMulEquiv_apply (γ : Γ) (x : G) :
    ((conjContinuousMulEquiv G γ x : G) : Γ) = γ * x * γ⁻¹ :=
  rfl

variable (Λ : Type u) [Ring Λ] (V : Type u) [AddCommGroup V] [Module Λ V] [DistribMulAction Γ V]
  [SMulCommClass Γ Λ V]

/-- An open normal subgroup of `G` acts trivially on `V`. -/
public abbrev IsSmoothFor : Prop := ∃ U : OpenNormalSubgroup G, ∀ g ∈ U, ∀ v : V, g • v = v

variable {G V}

/-- The `Λ[[G]]`-module structure on `V`. -/
@[instance_reducible]
public def completedGroupAlgebraModule (hV : IsSmoothFor G V) :
    Module (CompletedGroupAlgebra Λ G) V :=
  Module.compHom V (CompletedGroupAlgebra.toAddMonoidEnd (Λ := Λ) (G := G) V hV)

/-- `V` as an object of `ModuleCat Λ[[G]]`. -/
public def toCompletedGroupAlgebraModuleCat (hV : IsSmoothFor G V) :
    ModuleCat.{u} (CompletedGroupAlgebra Λ G) :=
  letI := completedGroupAlgebraModule Λ hV
  ModuleCat.of _ V

omit [IsTopologicalGroup Γ] [G.Normal] in
/-- `Λ[[G]]` acts on `V` through `CompletedGroupAlgebra.toAddMonoidEnd`. -/
public theorem completedGroupAlgebra_smul_def (hV : IsSmoothFor G V)
    (a : CompletedGroupAlgebra Λ G) (v : V) :
    (letI := completedGroupAlgebraModule Λ hV; a • v) =
      CompletedGroupAlgebra.toAddMonoidEnd (Λ := Λ) (G := G) V hV a v :=
  rfl

omit [IsTopologicalGroup Γ] [G.Normal] in
/-- The constants of `Λ[[G]]` act on `V` through the `Λ`-module structure. -/
public theorem const_smul_eq (hV : IsSmoothFor G V) (a : Λ) (v : V) :
    (letI := completedGroupAlgebraModule Λ hV; (const a : CompletedGroupAlgebra Λ G) • v) =
      a • v := by
  rw [completedGroupAlgebra_smul_def, toAddMonoidEnd_const]

omit [IsTopologicalGroup Γ] [G.Normal] in
/-- The group elements of `Λ[[G]]` act on `V` through the action of `G`. -/
public theorem of_smul_eq (hV : IsSmoothFor G V) (g : G) (v : V) :
    (letI := completedGroupAlgebraModule Λ hV; (of g : CompletedGroupAlgebra Λ G) • v) =
      (g : Γ) • v := by
  rw [completedGroupAlgebra_smul_def, toAddMonoidEnd_of]
  rfl

/-- The action of `γ ∈ Γ` on `V` is semilinear for the automorphism `σ_γ` of `Λ[[G]]` induced by
conjugation by `γ`. -/
public theorem smul_completedGroupAlgebra_smul (hV : IsSmoothFor G V) (γ : Γ)
    (a : CompletedGroupAlgebra Λ G) (v : V) :
    γ • (CompletedGroupAlgebra.toAddMonoidEnd (Λ := Λ) (G := G) V hV a v) =
      CompletedGroupAlgebra.toAddMonoidEnd (Λ := Λ) (G := G) V hV
        (mapRingEquiv (conjContinuousMulEquiv G γ) a) (γ • v) := by
  obtain ⟨U, hU⟩ := hV
  have hU' : ∀ g ∈ U, ∀ v : V, g • v = v := hU
  set c := conjContinuousMulEquiv G γ
  have hC : ∀ g ∈ comapSubgroup (c : G →* G) (continuous_coe_monoidHom c) U, ∀ v : V,
      g • v = v := by
    intro g hg v
    have h := hU' _ (map_mem_of_mem_comapSubgroup _ _ U g hg) (γ • v)
    change (γ * g * γ⁻¹) • γ • v = γ • v at h
    rw [mul_smul, mul_smul, inv_smul_smul] at h
    exact smul_left_cancel γ h
  rw [toAddMonoidEnd_eq V ⟨U, hU⟩ _ hC, toAddMonoidEnd_eq V ⟨U, hU⟩ U hU',
    CompletedGroupAlgebra.mapRingEquiv_apply,
    eval_map _ (continuous_coe_monoidHom c) (map_mem_of_mem_comapSubgroup _ _ U)]
  induction eval (comapSubgroup (c : G →* G) (continuous_coe_monoidHom c) U) a using
    MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    have hadd : ∀ (f g : AddMonoid.End V) (w : V), (f + g) w = f w + g w := fun _ _ _ => rfl
    simp only [map_add, hadd, smul_add, hx, hy]
  | single q b =>
    induction q using QuotientGroup.induction_on with
    | H g =>
      rw [quotientMapAlgebra_single, quotientAlgebraAction_single, quotientAlgebraAction_single,
        smul_comm γ b]
      congr 1
      show γ • (g : Γ) • v = (γ * g * γ⁻¹) • γ • v
      rw [mul_smul, mul_smul, inv_smul_smul]
  all_goals exact continuous_coe_monoidHom c

/-- The action of `γ ∈ Γ` on `V`, as a morphism `V ⟶ σ_γ^* V` of `Λ[[G]]`-modules, where `σ_γ` is
the automorphism of `Λ[[G]]` induced by conjugation by `γ`. -/
public def conjActionHom (hV : IsSmoothFor G V) (γ : Γ) :
    toCompletedGroupAlgebraModuleCat Λ hV ⟶
      (twistFunctor Λ (conjContinuousMulEquiv G γ)).obj (toCompletedGroupAlgebraModuleCat Λ hV) :=
  ModuleCat.ofHom (X := toCompletedGroupAlgebraModuleCat Λ hV)
    (Y := (twistFunctor Λ (conjContinuousMulEquiv G γ)).obj (toCompletedGroupAlgebraModuleCat Λ hV))
    { toFun := fun v => (γ • (show V from v) : V)
      map_add' := fun x y => smul_add γ (show V from x) y
      map_smul' := fun a v => smul_completedGroupAlgebra_smul Λ hV γ a v }

/-- The morphism `V ⟶ σ_γ^* V` is `v ↦ γ • v`. -/
public theorem conjActionHom_apply (hV : IsSmoothFor G V) (γ : Γ)
    (v : toCompletedGroupAlgebraModuleCat Λ hV) :
    (conjActionHom Λ hV γ).hom v = (γ • (show V from v) : V) :=
  rfl

/-- **The action of `γ ∈ Γ` on the derived coinvariants** `LH₀(G, V) = V ⊗^L_{Λ[[G]]} Λ`. -/
public def derivedCoinvariantsAction (hV : IsSmoothFor G V) (γ : Γ) :
    derivedCoinvariants (toCompletedGroupAlgebraModuleCat Λ hV) ⟶
      derivedCoinvariants (toCompletedGroupAlgebraModuleCat Λ hV) :=
  derivedCoinvariantsTwistedMap (conjActionHom Λ hV γ)

end Stacks.GroupHomology

end
