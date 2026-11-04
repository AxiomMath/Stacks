module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Spaces
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective

/-!
# Sections over an open with one point are exact

Let `R` be a sheaf of rings on a topological space and `W` an open with exactly one point. Taking
sections over `W` preserves epimorphisms of sheaves of `R`-modules: a covering sieve of `W` must
contain an open containing its point, which is `W` itself, so local surjectivity on `W` is
surjectivity.

## Main results

* `Stacks.SheafOfModules.preservesEpimorphisms_evaluation_of_subsingleton`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.SheafOfModules

/-- **Sections over an open with exactly one point preserve epimorphisms.** A covering sieve of
such an open `W` contains an open containing its point, which is `W` itself; so an epimorphism
of sheaves of modules, being locally surjective, is surjective on sections over `W`. -/
theorem preservesEpimorphisms_evaluation_of_subsingleton {T : TopCat.{u}}
    (R : Sheaf (Opens.grothendieckTopology T) RingCat.{u}) (W : Opens T) [Subsingleton W]
    [Nonempty W] : (SheafOfModules.evaluation.{u} R (op W)).PreservesEpimorphisms where
  preserves {M N} φ hφ := by
    rw [ModuleCat.epi_iff_surjective]
    intro t
    obtain ⟨x, hx⟩ := ‹Nonempty W›
    have hcov := Stacks.SheafOfModules.EpiMono.imageSieve_mem_of_epi φ t
    obtain ⟨U, i, ⟨s, hs⟩, hxU⟩ := hcov x hx
    have hUW : U = W := le_antisymm (leOfHom i) (by
      intro y hy
      have he : (⟨y, hy⟩ : W) = ⟨x, hx⟩ := Subsingleton.elim _ _
      have hxy : y = x := congrArg Subtype.val he
      exact hxy.symm ▸ hxU)
    subst U
    have hi : i = 𝟙 W := Subsingleton.elim _ _
    subst i
    rw [op_id] at hs
    refine ⟨s, ?_⟩
    rw [CategoryTheory.Functor.map_id] at hs
    exact hs.trans rfl

end Stacks.SheafOfModules
