module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.ModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FiniteTypeContinuousModuleCoinvariants

/-!
# Descending a continuous module along a surjection of profinite groups

Let `π : G →* H` be a continuous surjective homomorphism from a compact topological group to a
Hausdorff one, and let `M` be a finite `Λ`-module with a continuous `G`-action on which the kernel
of `π` acts trivially. Then the action factors through `H`, continuously for the discrete topology
on `M`, and restricting the resulting `Λ`-`H`-module along `π` gives back `M`.

For a curve `U` over a finite field `k` this is how a module on which the geometric fundamental
group acts trivially is a module over `π₁(Spec k)`, and so (Tag 0DV5) a sheaf pulled back from
`Spec k`: the input to the computation of the Frobenius on the top cohomology of the lisse sheaf
of the coinvariants `F''` in the proof of [Stacks, Tag 03VK].

## Main definitions

* `Stacks.GroupCohomology.finiteTypeContinuousModuleDescent`: the descended module.
* `Stacks.GroupCohomology.finiteTypeContinuousModuleDescentResIso`: its restriction is `M`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v w

namespace Stacks.GroupCohomology

open scoped Stacks.DiscreteModuleTopology

variable (Λ : Type u) [Ring Λ] {G H : Type v} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [T2Space H] (π : G →ₜ* H) (hs : Function.Surjective π)
  (M : FiniteTypeContinuousModule.{u, v, w} Λ G) (hM : ∀ g, π g = 1 → M.obj.obj.obj.ρ g = 1)

include hM in
/-- Elements of `G` with the same image under `π` act in the same way on `M`. -/
theorem finiteTypeContinuousModuleRepresentation_eq_of_eq {a b : G} (h : π a = π b) :
    finiteTypeContinuousModuleRepresentation Λ G M a =
      finiteTypeContinuousModuleRepresentation Λ G M b := by
  have h1 : π (b⁻¹ * a) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  have h2 : finiteTypeContinuousModuleRepresentation Λ G M (b⁻¹ * a) = 1 := by
    show (M.obj.obj.obj.ρ _).asHom.hom = 1
    rw [hM _ h1]
    rfl
  rw [← mul_inv_cancel_left b a, map_mul, h2, mul_one]

/-- The representation of `H` through which the action of `G` on `M` factors. -/
def finiteTypeContinuousModuleDescentRepresentation : Representation Λ H M.obj.obj.obj.V where
  toFun h := finiteTypeContinuousModuleRepresentation Λ G M (Function.surjInv hs h)
  map_one' := by
    rw [finiteTypeContinuousModuleRepresentation_eq_of_eq Λ π M hM
      ((Function.surjInv_eq hs 1).trans (map_one π).symm), map_one]
  map_mul' a b := by
    rw [← map_mul]
    exact finiteTypeContinuousModuleRepresentation_eq_of_eq Λ π M hM (by
      rw [map_mul, Function.surjInv_eq hs, Function.surjInv_eq hs, Function.surjInv_eq hs])

/-- The descended representation of `H` at `π g` acts on `M` as `g` does. -/
theorem finiteTypeContinuousModuleDescentRepresentation_apply (g : G) (v : M.obj.obj.obj.V) :
    finiteTypeContinuousModuleDescentRepresentation Λ π hs M hM (π g) v =
      (M.obj.obj.obj.ρ g).asHom v :=
  congrArg (fun φ : Module.End Λ M.obj.obj.obj.V => φ v)
    (finiteTypeContinuousModuleRepresentation_eq_of_eq Λ π M hM (Function.surjInv_eq hs (π g)))

include hs hM in
/-- The action of `H` on `M` through `finiteTypeContinuousModuleDescentRepresentation` is
continuous. -/
theorem isContinuous_finiteTypeContinuousModuleDescentRepresentation :
    (actionOfRepresentation Λ H M.obj.obj.obj.V
      (finiteTypeContinuousModuleDescentRepresentation Λ π hs M hM)).IsContinuous :=
  (isContinuous_actionOfRepresentation_iff _).2 fun v => by
    have hq : Topology.IsQuotientMap π :=
      (π.continuous.isClosedMap).isQuotientMap π.continuous hs
    refine hq.isOpen_preimage.1 ?_
    have : π ⁻¹' {h : H | finiteTypeContinuousModuleDescentRepresentation Λ π hs M hM h v = v} =
        {g : G | (M.obj.obj.obj.ρ g).asHom v = v} := by
      ext g
      simp only [Set.mem_preimage, Set.mem_setOf_eq,
        finiteTypeContinuousModuleDescentRepresentation_apply]
    rw [this]
    exact isOpen_stabilizer Λ G M.obj v

/-- **The `Λ`-`H`-module through which `M` factors.** -/
def finiteTypeContinuousModuleDescent : FiniteTypeContinuousModule.{u, v, w} Λ H :=
  ⟨ofRepresentation (finiteTypeContinuousModuleDescentRepresentation Λ π hs M hM)
      (isContinuous_finiteTypeContinuousModuleDescentRepresentation Λ π hs M hM),
    M.property⟩

/-- **Restricting the descended module along `π` gives back `M`.** -/
def finiteTypeContinuousModuleDescentResIso :
    (finiteTypeContinuousModuleRes Λ (π : G →ₜ* H)).obj
        (finiteTypeContinuousModuleDescent Λ π hs M hM) ≅ M :=
  ObjectProperty.isoMk _ (ObjectProperty.isoMk _ (ObjectProperty.isoMk _
    (Action.mkIso (Iso.refl _) fun g => by
      ext v
      exact finiteTypeContinuousModuleDescentRepresentation_apply Λ π hs M hM g v)))

end Stacks.GroupCohomology

end
