module

public import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.TorsionFree
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.AffineLocalCriterion

/-!
# Reflexivity of the kernel of a map onto a torsion-free module

Let `X` be an integral locally Noetherian scheme and let `0 → ℱ → ℱ' → ℱ''` be an exact
sequence of coherent `𝒪_X`-modules.  If `ℱ'` is reflexive and `ℱ''` is torsion free then `ℱ`
is reflexive.

## Main results

* `AlgebraicGeometry.isReflexive_of_exact_of_isReflexive_of_isTorsionFree`: if `ℱ'` is reflexive
  and `ℱ''` is torsion free in an exact sequence `0 → ℱ → ℱ' → ℱ''` of coherent modules, then
  `ℱ` is reflexive.

## References

* [Stacks Project, Tag 0EBG](https://stacks.math.columbia.edu/tag/0EBG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace AlgebraicGeometry

/-- Evaluating an exact sequence `0 → ℱ → ℱ' → ℱ''` of modules on a scheme at an open `U` gives
an exact sequence of modules of sections over `U`. -/
private theorem sections_exact {X : Scheme.{u}} {U : X.Opens} {F F' F'' : X.Modules}
    (f : F ⟶ F') (g : F' ⟶ F'') [Mono f] (hfg : f ≫ g = 0)
    (hexact : (ShortComplex.mk f g hfg).Exact) :
    Function.Exact (fun s : Γ(F, U) => (f.app U) s) (fun s : Γ(F', U) => (g.app U) s) := by
  let T := Scheme.Modules.toPresheaf X
  let E := (evaluation X.Opensᵒᵖ Ab.{u}).obj (Opposite.op U)
  have : E.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  have : PreservesFiniteLimits E := inferInstance
  have hfgE : E.map (T.map f) ≫ E.map (T.map g) = 0 := by
    rw [← E.map_comp, ← T.map_comp, hfg]
    simp
  exact (ShortComplex.ab_exact_iff_function_exact (.mk _ _ hfgE)).mp
    (ShortComplex.exact_of_f_is_kernel _
      (KernelFork.mapIsLimit _ (KernelFork.mapIsLimit _ hexact.fIsKernel T) E))

/-- In an exact sequence `0 → ℱ → ℱ' → ℱ''` of coherent modules on an integral locally
Noetherian scheme, if `ℱ'` is reflexive and `ℱ''` is torsion free then `ℱ` is reflexive. -/
@[stacks 0EBG]
theorem isReflexive_of_exact_of_isReflexive_of_isTorsionFree {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] {F F' F'' : X.Modules} [_root_.SheafOfModules.IsCoherent F]
    [_root_.SheafOfModules.IsCoherent F'] [_root_.SheafOfModules.IsCoherent F'']
    (f : F ⟶ F') (g : F' ⟶ F'') [Mono f] (hfg : f ≫ g = 0)
    (hexact : (ShortComplex.mk f g hfg).Exact) (hF' : IsReflexive F')
    (hF'' : (letI : F''.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent F'';
      IsTorsionFree F'')) :
    IsReflexive F := by
  have : F.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent F
  have : F'.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent F'
  have : F''.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent F''
  refine (isReflexive_iff_sections_isReflexive X F).2 fun U hU => ?_
  by_cases hne : Nonempty U
  · have : IsDomain Γ(X, U) := IsIntegral.component_integral U
    have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    have hfin : ∀ (G : X.Modules) [_root_.SheafOfModules.IsCoherent G] [G.IsQuasicoherent],
        Module.Finite Γ(X, U) Γ(G, U) := fun G _ _ =>
      have := _root_.IsCoherent.toIsFiniteType G
      Stacks.AlgebraicGeometry.CoherentFinite.finite_sections G hU
    have := hfin F
    have := hfin F'
    have := hfin F''
    let sections := Scheme.Modules.toPresheafOfModules X ⋙
      PresheafOfModules.evaluation X.ringCatSheaf.obj (Opposite.op U)
    let fU : Γ(F, U) →ₗ[Γ(X, U)] Γ(F', U) := (sections.map f).hom
    let gU : Γ(F', U) →ₗ[Γ(X, U)] Γ(F'', U) := (sections.map g).hom
    exact _root_.isReflexive_of_exact_of_isReflexive_of_isTorsionFree fU gU
      ((ModuleCat.mono_iff_injective _).mp inferInstance) (sections_exact f g hfg hexact)
      ((isReflexive_iff_sections_isReflexive X F').mp hF' U hU)
      ((isTorsionFree_iff_forall_isAffineOpen F'').mp hF'' U hU)
  · obtain rfl : U = ⊥ := le_antisymm (fun z hz => (hne ⟨z, hz⟩).elim) bot_le
    have : Subsingleton Γ(X, (⊥ : X.Opens)) := ⟨fun _ _ =>
      TopCat.Presheaf.IsSheaf.section_ext (U := Opposite.op (⊥ : X.Opens))
        X.ringCatSheaf.property fun z hz => (hne ⟨z, hz⟩).elim⟩
    have : Subsingleton Γ(F, (⊥ : X.Opens)) := ⟨fun _ _ =>
      TopCat.Presheaf.IsSheaf.section_ext (U := Opposite.op (⊥ : X.Opens)) F.isSheaf
        fun z hz => (hne ⟨z, hz⟩).elim⟩
    exact ⟨⟨fun a b _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩⟩

end AlgebraicGeometry

end
