module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeSheafSections

/-!
# Epimorphisms out of a free sheaf of modules from locally generating global sections

A finite family `s` of global sections of a sheaf of modules `M` which generates `M` locally
defines an epimorphism `free ι ⟶ M`, and over an object on which locally surjective morphisms
of abelian sheaves are surjective on sections, the values of the `s i` generate the module of
sections there.

## Main results

* `Stacks.SheafOfModules.isLocallySurjective_freeHomEquiv_symm` and
  `Stacks.SheafOfModules.epi_freeHomEquiv_symm`: a finite family of global sections generating a
  sheaf of modules locally defines an epimorphism out of the free sheaf.
* `Stacks.SheafOfModules.span_range_eval_eq_top`: over an object on which locally surjective
  morphisms of sheaves of abelian groups are surjective on sections, such a family generates the
  module of sections.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

universe t v u

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  [HasWeakSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}]

/-- **A finite family of global sections generating a sheaf of modules locally defines an
epimorphism out of the free sheaf of modules.** The morphism `free ι ⟶ M` attached to `s` is
locally surjective as soon as every section of `M` over any object is, on a covering sieve, a
linear combination of the restrictions of the `s i`. -/
theorem isLocallySurjective_freeHomEquiv_symm {M : SheafOfModules.{t} R} {ι : Type t} [Fintype ι]
    (s : ι → M.sections)
    (hs : ∀ (V : C) (m : M.val.obj (op V)), ∃ S ∈ J V, ∀ ⦃W : C⦄ (g : W ⟶ V), S g →
      M.val.restrictₛₗ g.op m ∈
        Submodule.span (R.obj.obj (op W)) (Set.range fun i => (s i).eval (op W))) :
    Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf R).map (M.freeHomEquiv.symm s)) := by
  classical
  refine ⟨fun {V} m => ?_⟩
  obtain ⟨S, hS, h⟩ := hs V m
  refine J.superset_covering (fun W g hg => ?_) hS
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp (h g hg)
  refine ⟨freeMk (S := R) (op W) a, ?_⟩
  refine (app_freeMk (M.freeHomEquiv.symm s) (op W) a).trans (Eq.trans ?_ ha)
  exact Finset.sum_congr rfl fun i _ => by rw [app_unitOne_ιFree_comp, Equiv.apply_symm_apply]

/-- The epimorphism form of `isLocallySurjective_freeHomEquiv_symm`. -/
theorem epi_freeHomEquiv_symm {M : SheafOfModules.{t} R} {ι : Type t} [Fintype ι]
    (s : ι → M.sections)
    (hs : ∀ (V : C) (m : M.val.obj (op V)), ∃ S ∈ J V, ∀ ⦃W : C⦄ (g : W ⟶ V), S g →
      M.val.restrictₛₗ g.op m ∈
        Submodule.span (R.obj.obj (op W)) (Set.range fun i => (s i).eval (op W))) :
    Epi (M.freeHomEquiv.symm s) :=
  EpiMono.epi_of_isLocallySurjective _ (isLocallySurjective_freeHomEquiv_symm s hs)

/-- **Generation by global sections over an object with exact sections.** Let `s` be a finite
family of global sections of a sheaf of modules `M` which generates `M` locally: every section
over any object is, on a covering sieve, a linear combination of the restrictions of the `s i`.
Over an object `U` on which every locally surjective morphism of sheaves of abelian groups is
surjective on sections, the values of the `s i` over `U` generate the module `M(U)`. -/
theorem span_range_eval_eq_top {M : SheafOfModules.{t} R} {ι : Type t} [Fintype ι]
    (s : ι → M.sections)
    (hs : ∀ (V : C) (m : M.val.obj (op V)), ∃ S ∈ J V, ∀ ⦃W : C⦄ (g : W ⟶ V), S g →
      M.val.restrictₛₗ g.op m ∈
        Submodule.span (R.obj.obj (op W)) (Set.range fun i => (s i).eval (op W)))
    (U : C) (hU : ∀ {F G : Sheaf J AddCommGrpCat.{t}} (φ : F ⟶ G), Sheaf.IsLocallySurjective φ →
      Function.Surjective (φ.hom.app (op U))) :
    Submodule.span (R.obj.obj (op U)) (Set.range fun i => (s i).eval (op U)) = ⊤ := by
  classical
  have hloc := isLocallySurjective_freeHomEquiv_symm s hs
  refine eq_top_iff.mpr fun m _ => ?_
  obtain ⟨e, he⟩ := hU _ hloc m
  obtain ⟨a, ha⟩ := exists_eq_sum_smul_freeHomEquiv (M.freeHomEquiv.symm s) (op U) e
  rw [← (show (M.freeHomEquiv.symm s).val.app (op U) e = m from he), ← ha]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨i, by rw [Equiv.apply_symm_apply]⟩)

end Stacks.SheafOfModules

end
