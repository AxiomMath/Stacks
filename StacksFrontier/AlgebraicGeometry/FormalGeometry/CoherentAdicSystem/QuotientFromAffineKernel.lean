module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicInverseSystem.Sections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.IdealPowerLocal
public import StacksFrontier.AlgebraicGeometry.Modules.SubmoduleKernel

/-!
# The quotient `M / I ^ n M` recognized from an affine-local kernel

Clause 3 of `Stacks.Coherent.IsCoherentAdicSystem` asks, for each `n`, for an isomorphism
`F_(n+1) / I ^ (n+1) F_(n+1) ≅ F_n` *through* the transition map of the system. This file reduces
that clause to a computation which can be carried out one affine open at a time: an epimorphism
`p : M ⟶ N` whose kernel on the sections over every affine open `U` is `I(U) ^ n · M(U)` is the
projection `M → M / I ^ n M`, up to the unique isomorphism intertwining it with the cokernel
projection. The reduction is also given in a version whose hypothesis ranges over a basis of
affine opens rather than over every affine open.

## Main results

* `Stacks.Algebraization.exists_cokernelIso_of_kernelSubmodule_eq` — an epimorphism presents its
  target as the quotient by its own sectionwise kernel.
* `Stacks.Algebraization.kernelSubmodule_eq_idealPowerMultiple` — a map whose kernel on affine
  sections is `I(U) ^ n · M(U)` has `I ^ n M` as its sectionwise kernel.
* `Stacks.Algebraization.kernelSubmodule_eq_idealPowerMultiple_of_basis` — the same, with the
  computation asked for only on a basis of affine opens.
* `Stacks.Algebraization.exists_idealPowerQuotientIso_of_affine_ker` — the resulting form of
  clause 3.
* `Stacks.Algebraization.isCoherentAdicSystem_of_affine_ker` — membership in `Coh(X, I)` for an
  inverse system whose transitions are epimorphisms with those kernels.
* `Stacks.Algebraization.isCoherentAdicSystem_of_basis_ker` — the same from a basis of affine
  opens.

## References

* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped AlgebraicGeometry

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

variable {X : Scheme.{u}}

open AlgebraicGeometry.SheafOfModules.Submodule in
/-- An epimorphism of sheaves of modules on a scheme presents its target as the quotient by its
own sectionwise kernel, compatibly with the quotient projection. -/
public theorem exists_cokernelIso_of_kernelSubmodule_eq {M N : X.Modules} (p : M ⟶ N) [Epi p]
    (K : M.Submodule) (hK : AlgebraicGeometry.RegularIdealSheaf.kernelSubmodule p = K) :
    ∃ e : cokernel K.ιModules ≅ N, cokernel.π K.ιModules ≫ e.hom = p := by
  subst hK
  have hzero : (AlgebraicGeometry.RegularIdealSheaf.kernelSubmodule p).ιModules ≫ p = 0 :=
    ιModules_kernelSubmodule_comp p
  have hkι : (kernelIso p).inv ≫
      (AlgebraicGeometry.RegularIdealSheaf.kernelSubmodule p).ιModules = kernel.ι p := by
    rw [← kernelIso_hom_comp_ι p, Iso.inv_hom_id_assoc]
  have hι : kernel.ι p ≫
      cokernel.π (AlgebraicGeometry.RegularIdealSheaf.kernelSubmodule p).ιModules = 0 := by
    rw [← hkι, Category.assoc, cokernel.condition, comp_zero]
  refine ⟨⟨cokernel.desc _ p hzero,
    Abelian.epiDesc p
      (cokernel.π (AlgebraicGeometry.RegularIdealSheaf.kernelSubmodule p).ιModules) hι, ?_, ?_⟩,
    cokernel.π_desc _ _ _⟩
  · refine (cancel_epi
      (cokernel.π (AlgebraicGeometry.RegularIdealSheaf.kernelSubmodule p).ιModules)).mp ?_
    rw [Category.comp_id, ← Category.assoc, cokernel.π_desc, Abelian.comp_epiDesc]
  · refine (cancel_epi p).mp ?_
    rw [Category.comp_id, ← Category.assoc, Abelian.comp_epiDesc, cokernel.π_desc]

/-- The sectionwise kernel of a map whose kernel on affine sections is `I(U) ^ n • M(U)` is the
subsheaf `I ^ n M`. -/
public theorem kernelSubmodule_eq_idealPowerMultiple (I : X.IdealSheafData) (n : ℕ)
    {M N : X.Modules} (p : M ⟶ N)
    (hker : ∀ U : X.affineOpens, LinearMap.ker (p.val.app (op U.1)).hom =
      I.ideal U ^ n • (⊤ : Submodule Γ(X, U) Γ(M, U))) :
    AlgebraicGeometry.RegularIdealSheaf.kernelSubmodule p = idealPowerMultiple I n M :=
  le_antisymm
    (submodule_le_of_affine _ _ fun U x hx =>
      (idealPowerMultiple_le_iff I n M (idealPowerMultiple I n M)).mp le_rfl U
        ((hker U).le (LinearMap.mem_ker.mpr
          ((AlgebraicGeometry.RegularIdealSheaf.mem_kernelSubmodule p (op U.1) x).mp hx))))
    ((idealPowerMultiple_le_iff I n M _).mpr fun U x hx =>
      (AlgebraicGeometry.RegularIdealSheaf.mem_kernelSubmodule p (op U.1) x).mpr
        (LinearMap.mem_ker.mp ((hker U).ge hx)))

/-- **The sectionwise kernel of a map whose kernel is known on a basis of affine opens.** Let `S`
be a family of affine opens which is a basis of the topology: every point of every open of `X` has
a member of `S` around it inside that open. A map `p` whose kernel on the sections over each
member of `S` is `I(V) ^ n • M(V)` has `I ^ n M` as its sectionwise kernel. -/
public theorem kernelSubmodule_eq_idealPowerMultiple_of_basis (I : X.IdealSheafData) (n : ℕ)
    {M N : X.Modules} (p : M ⟶ N) (S : Set X.affineOpens)
    (hS : ∀ (W : X.Opens) (x : X), x ∈ W → ∃ V ∈ S, x ∈ V.1 ∧ V.1 ≤ W)
    (hker : ∀ V ∈ S, LinearMap.ker (p.val.app (op V.1)).hom =
      I.ideal V ^ n • (⊤ : Submodule Γ(X, V) Γ(M, V))) :
    AlgebraicGeometry.RegularIdealSheaf.kernelSubmodule p = idealPowerMultiple I n M := by
  refine le_antisymm (SheafOfModules.Submodule.le_iff.mpr
      (PresheafOfModules.Submodule.le_iff.mpr fun W s hs => ?_))
    (SheafOfModules.Submodule.le_iff.mpr
      (PresheafOfModules.Submodule.le_iff.mpr fun W s hs => ?_))
  · refine (idealPowerMultiple I n M).isSheaf s ?_
    rw [Opens.mem_grothendieckTopology]
    intro x hx
    obtain ⟨V, hVS, hxV, hVW⟩ := hS W.unop x hx
    refine ⟨V.1, homOfLE hVW, ?_, hxV⟩
    exact (idealPowerMultiple_le_iff I n M (idealPowerMultiple I n M)).mp le_rfl V
      ((hker V hVS).le (LinearMap.mem_ker.mpr
        ((AlgebraicGeometry.RegularIdealSheaf.mem_kernelSubmodule p (op V.1) _).mp
          ((AlgebraicGeometry.RegularIdealSheaf.kernelSubmodule p).toSubmodule.map_mem
            (homOfLE hVW).op hs))))
  · refine (AlgebraicGeometry.RegularIdealSheaf.kernelSubmodule p).isSheaf s ?_
    rw [Opens.mem_grothendieckTopology]
    intro x hx
    obtain ⟨V₀, h₀, hxV₀, hspan⟩ :=
      (mem_idealPowerMultiple_iff I n M W.unop s).mp hs x hx
    obtain ⟨V, hVS, hxV, hVV₀⟩ := hS V₀.1 x hxV₀
    have hcomp : M.val.map (homOfLE (hVV₀.trans h₀)).op s =
        M.val.map (homOfLE hVV₀).op (M.val.map (homOfLE h₀).op s) :=
      M.val.map_comp_apply (homOfLE h₀).op (homOfLE hVV₀).op s
    refine ⟨V.1, homOfLE (hVV₀.trans h₀), ?_, hxV⟩
    exact (AlgebraicGeometry.RegularIdealSheaf.mem_kernelSubmodule p (op V.1) _).mpr
      (LinearMap.mem_ker.mp
        (Eq.mpr (congrArg (· ∈ LinearMap.ker (p.val.app (op V.1)).hom) hcomp)
          ((hker V hVS).ge (map_mem_idealPowerSmul I n M hVV₀ hspan))))

/-- **The quotient `M / I ^ n M`, recognized from affine-local data.** An epimorphism
`p : M ⟶ N` whose kernel on the sections over every affine open `U` is `I(U) ^ n • M(U)`
presents `N` as `M / I ^ n M`, compatibly with the quotient projection. -/
public theorem exists_idealPowerQuotientIso_of_affine_ker (I : X.IdealSheafData) (n : ℕ)
    {M N : X.Modules} (p : M ⟶ N) [Epi p]
    (hker : ∀ U : X.affineOpens, LinearMap.ker (p.val.app (op U.1)).hom =
      I.ideal U ^ n • (⊤ : Submodule Γ(X, U) Γ(M, U))) :
    ∃ e : idealPowerQuotient I n M ≅ N,
      cokernel.π (idealPowerMultiple I n M).ι ≫ e.hom = p :=
  exists_cokernelIso_of_kernelSubmodule_eq p _ (kernelSubmodule_eq_idealPowerMultiple I n p hker)

/-- **Membership in `Coh(X, I)` from affine-local data.** An inverse system of coherent modules
annihilated by the successive ideal powers, whose transitions are epimorphisms with the expected
kernel over every affine open, is a coherent adic system along `I`. -/
public theorem isCoherentAdicSystem_of_affine_ker (I : X.IdealSheafData) (F : ℕᵒᵖ ⥤ X.Modules)
    (hcoh : ∀ n : ℕ, SheafOfModules.IsCoherent.{u} (F.obj (op n)))
    (hann : ∀ n : ℕ, idealPowerMultiple I (n + 1) (F.obj (op n)) = ⊥)
    (hepi : ∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op))
    (hker : ∀ (n : ℕ) (U : X.affineOpens),
      LinearMap.ker ((F.map (homOfLE (Nat.le_succ n)).op).val.app (op U.1)).hom =
        I.ideal U ^ (n + 1) • (⊤ : Submodule Γ(X, U) Γ(F.obj (op (n + 1)), U))) :
    Stacks.Coherent.IsCoherentAdicSystem I F :=
  ⟨hcoh, hann, fun n =>
    have := hepi n
    exists_idealPowerQuotientIso_of_affine_ker I (n + 1) _ (hker n)⟩

/-- **Membership in `Coh(X, I)` from a basis of affine opens.** An inverse system of coherent
modules annihilated by the successive ideal powers, whose transitions are epimorphisms with the
expected kernel over every member of a basis `S` of affine opens, is a coherent adic system
along `I`. -/
public theorem isCoherentAdicSystem_of_basis_ker (I : X.IdealSheafData) (F : ℕᵒᵖ ⥤ X.Modules)
    (S : Set X.affineOpens)
    (hS : ∀ (W : X.Opens) (x : X), x ∈ W → ∃ V ∈ S, x ∈ V.1 ∧ V.1 ≤ W)
    (hcoh : ∀ n : ℕ, SheafOfModules.IsCoherent.{u} (F.obj (op n)))
    (hann : ∀ n : ℕ, idealPowerMultiple I (n + 1) (F.obj (op n)) = ⊥)
    (hepi : ∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op))
    (hker : ∀ n : ℕ, ∀ V ∈ S,
      LinearMap.ker ((F.map (homOfLE (Nat.le_succ n)).op).val.app (op V.1)).hom =
        I.ideal V ^ (n + 1) • (⊤ : Submodule Γ(X, V) Γ(F.obj (op (n + 1)), V))) :
    Stacks.Coherent.IsCoherentAdicSystem I F :=
  ⟨hcoh, hann, fun n =>
    have := hepi n
    exists_cokernelIso_of_kernelSubmodule_eq _ _
      (kernelSubmodule_eq_idealPowerMultiple_of_basis I (n + 1) _ S hS (hker n))⟩

end Stacks.Algebraization

end
