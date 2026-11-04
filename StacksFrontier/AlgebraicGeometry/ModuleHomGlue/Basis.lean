module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.MorphismGluing

/-!
# Gluing morphisms of sheaves of modules from a basis

Let `X` be a scheme and `M`, `N` sheaves of `𝒪_X`-modules. A family of `Γ(X, B i)`-linear maps
`Γ(M, B i) → Γ(N, B i)`, indexed by a family of opens `B` forming a basis of the topology and
compatible with restriction between members of the family, is the action on sections of exactly
one morphism `M ⟶ N`.

## Main results

* `Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_isBasis`: **morphisms of sheaves of
  modules glue from a basis.**
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ModuleHomGlue

variable {X : Scheme.{u}} {M N : X.Modules} {ι : Type u} {B : ι → X.Opens}

/-- **Two morphisms of sheaves of modules agreeing on the sections over a basis are equal.** -/
theorem hom_ext_of_isBasis (hB : Opens.IsBasis (Set.range B)) {φ ψ : M ⟶ N}
    (h : ∀ i (s : Γ(M, B i)), φ.app (B i) s = ψ.app (B i) s) : φ = ψ := by
  refine Scheme.Modules.hom_ext φ ψ fun U => ?_
  ext s
  refine Stacks.Coherent.modulesSections_eq_of_locally_eq N U _ _ fun x hx => ?_
  obtain ⟨_, ⟨i, rfl⟩, hxi, hiU⟩ := Opens.isBasis_iff_nbhd.mp hB hx
  refine ⟨B i, hiU, hxi, ?_⟩
  exact (PresheafOfModules.naturality_apply φ.val (homOfLE hiU).op s).symm.trans
    ((h i _).trans (PresheafOfModules.naturality_apply ψ.val (homOfLE hiU).op s))

variable (B) in
/-- **Morphisms of sheaves of modules glue from a basis.** A family of additive maps on the
sections over the members of a family of opens forming a basis, linear over the functions there and
compatible with restriction, is the action on sections of a morphism of sheaves of modules. -/
theorem exists_hom_of_isBasis (hB : Opens.IsBasis (Set.range B))
    (g : ∀ i, Γ(M, B i) →+ Γ(N, B i))
    (hres : ∀ i j (h : B j ≤ B i) (s : Γ(M, B i)),
      g j (M.presheaf.map (homOfLE h).op s) = N.presheaf.map (homOfLE h).op (g i s))
    (hsmul : ∀ i (r : Γ(X, B i)) (s : Γ(M, B i)), g i (r • s) = r • g i s) :
    ∃ φ : M ⟶ N, ∀ i (s : Γ(M, B i)), φ.app (B i) s = g i s := by
  let α : (inducedFunctor B).op ⋙ M.presheaf ⟶ (inducedFunctor B).op ⋙ N.presheaf :=
    { app := fun i => AddCommGrpCat.ofHom (g i.unop)
      naturality := fun {i j} f => by
        refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun s => ?_)
        exact hres i.unop j.unop (leOfHom f.unop.hom) s }
  let ψ := (TopCat.Sheaf.restrictHomEquivHom M.presheaf
    (⟨Scheme.Modules.presheaf N, N.isSheaf⟩ : TopCat.Sheaf _ _) hB) α
  have hψ : ∀ i (s : Γ(M, B i)), ψ.app (op (B i)) s = g i s := fun i s =>
    congrArg (fun k => k s) (congrArg AddCommGrpCat.Hom.hom (TopCat.Sheaf.extend_hom_app M.presheaf
      (⟨Scheme.Modules.presheaf N, N.isSheaf⟩ : TopCat.Sheaf _ _) hB α i))
  have hnat : ∀ {U V : X.Opens} (h : V ≤ U) (s : Γ(M, U)),
      ψ.app (op V) (M.presheaf.map (homOfLE h).op s) =
        N.presheaf.map (homOfLE h).op (ψ.app (op U) s) := fun h s =>
    congrArg (fun k => AddCommGrpCat.Hom.hom k s) (ψ.naturality (homOfLE h).op)
  refine ⟨⟨PresheafOfModules.homMk ψ fun U r s => ?_⟩, hψ⟩
  refine Stacks.Coherent.modulesSections_eq_of_locally_eq N U.unop _ _ fun x hx => ?_
  obtain ⟨_, ⟨i, rfl⟩, hxi, hiU⟩ := Opens.isBasis_iff_nbhd.mp hB hx
  refine ⟨B i, hiU, hxi, ?_⟩
  have e6 : ψ.app (op (B i)) (M.presheaf.map (homOfLE hiU).op (r • s)) =
      N.presheaf.map (homOfLE hiU).op (ψ.app U (r • s)) := hnat hiU (r • s)
  refine e6.symm.trans ?_
  refine (congrArg (ψ.app (op (B i)))
    (PresheafOfModules.map_smul M.val (homOfLE hiU).op r s)).trans ?_
  refine (hψ i _).trans ?_
  refine (hsmul i (X.ringCatSheaf.val.map (homOfLE hiU).op r)
    (M.presheaf.map (homOfLE hiU).op s)).trans ?_
  have e7 : g i (M.presheaf.map (homOfLE hiU).op s) =
      N.presheaf.map (homOfLE hiU).op (ψ.app U s) := (hψ i _).symm.trans (hnat hiU s)
  rw [e7]
  exact (PresheafOfModules.map_smul N.val (homOfLE hiU).op r (ψ.app U s)).symm

end Stacks.AlgebraicGeometry.ModuleHomGlue

end
