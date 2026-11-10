module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SubmoduleKer
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Topology.Sets.Opens
public import StacksFrontier.AlgebraicGeometry.Modules.SubmoduleCompleteLattice

/-!
# Submodules of a module on a scheme are determined on a basis

A submodule of a sheaf of modules on a scheme has local membership, so it is determined by its
sections over the members of a basis of the topology. Consequently two submodules agreeing on a
basis are equal, and an epimorphism identifies the quotient by any submodule agreeing with its
kernel on a basis with its target.

## Main results

* `Stacks.LefschetzCone.submodule_le_of_isBasis`: comparison of submodules on a basis.
* `Stacks.LefschetzCone.submodule_eq_of_isBasis`: equality of submodules on a basis.
* `Stacks.LefschetzCone.cokernelIsoOfEqKer`: the cokernel of the inclusion of the kernel of an
  epimorphism is its target, compatibly with the projection.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.LefschetzCone

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

variable {X : Scheme.{u}} {M : X.Modules}

/-- **A submodule is contained in another as soon as it is on a basis.** If `P(B i) ≤ Q(B i)` for
every member `B i` of a basis of the topology of `X`, then `P ≤ Q`. -/
public theorem submodule_le_of_isBasis {ι : Type*} {B : ι → X.Opens}
    (hB : Opens.IsBasis (Set.range B)) {P Q : M.Submodule}
    (h : ∀ i, P.obj (op (B i)) ≤ Q.obj (op (B i))) : P ≤ Q := by
  change P.toSubmodule ≤ Q.toSubmodule
  rw [PresheafOfModules.Submodule.le_iff]
  intro U s hs
  apply Q.isSheaf
  rw [Opens.mem_grothendieckTopology]
  intro x hx
  obtain ⟨_, ⟨i, rfl⟩, hxi, hiU⟩ := (Opens.isBasis_iff_nbhd.mp hB) hx
  refine ⟨B i, homOfLE hiU, ?_, hxi⟩
  exact h i (P.map (homOfLE hiU).op hs)

/-- **Two submodules agreeing on a basis are equal.** -/
public theorem submodule_eq_of_isBasis {ι : Type*} {B : ι → X.Opens}
    (hB : Opens.IsBasis (Set.range B)) {P Q : M.Submodule}
    (h : ∀ i, P.obj (op (B i)) = Q.obj (op (B i))) : P = Q :=
  le_antisymm (submodule_le_of_isBasis hB fun i => (h i).le)
    (submodule_le_of_isBasis hB fun i => (h i).ge)

/-- **The quotient by the kernel of an epimorphism is its target.** If a submodule `K` of `G` is
the kernel of an epimorphism `p : G ⟶ Q`, then the cokernel of the inclusion of `K` is `Q`, the
cokernel projection becoming `p`. -/
public def cokernelIsoOfEqKer {G Q : X.Modules} (p : G ⟶ Q) [Epi p] (K : G.Submodule)
    (hK : K = SheafOfModules.Submodule.ker p) :
    cokernel K.ι ≅ Q := by
  subst hK
  haveI : Epi (C := SheafOfModules X.ringCatSheaf) p := ‹Epi p›
  have hc : IsColimit (CokernelCofork.ofπ p (SheafOfModules.Submodule.ker_ι_comp p)) :=
    Abelian.epiIsCokernelOfKernel _ (SheafOfModules.Submodule.isLimitKernelFork p)
  exact (colimit.isColimit _).coconePointUniqueUpToIso hc

/-- The cokernel projection of the inclusion of `K` followed by `cokernelIsoOfEqKer p K hK` is
`p`. -/
@[reassoc]
public theorem cokernelIsoOfEqKer_hom {G Q : X.Modules} (p : G ⟶ Q) [Epi p] (K : G.Submodule)
    (hK : K = SheafOfModules.Submodule.ker p) :
    cokernel.π K.ι ≫ (cokernelIsoOfEqKer p K hK).hom = p := by
  subst hK
  exact (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom _ WalkingParallelPair.one

end Stacks.LefschetzCone

end
