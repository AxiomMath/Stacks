module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# Constant sheaves of projective modules over a weakly contractible final object

Let `(C, J)` be a site with a final object `T` such that every locally surjective morphism of
sheaves of sets is surjective on sections over `T` (that is, `T` is weakly contractible, Stacks
090L). Then sections over `T` preserve epimorphisms of sheaves of modules, and since the constant
sheaf functor is left adjoint to sections over `T`, it carries projective modules to projective
sheaves of modules. Sections over `T`, preserving finite limits as every evaluation does, are
then an exact functor.

## Main results

* `Stacks.ConstantSheaf.preservesEpimorphisms_sheafSections_of_surjective_app`: sections over `T`
  preserve epimorphisms of sheaves of modules.
* `Stacks.ModuleSheaf.preservesFiniteColimits_sheafSections_of_surjective_app`: sections over
  `T` are an exact functor on sheaves of modules.
* `Stacks.ConstantSheaf.projective_constantSheaf_of_surjective_app`: the constant sheaf on a
  projective module is projective.

## References

* [Stacks Project, Tag 090L](https://stacks.math.columbia.edu/tag/090L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' v u

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (R : Type w') [Ring R]
  [HasSheafify J (ModuleCat.{w} R)] [J.HasSheafCompose (forget (ModuleCat.{w} R))]
  [J.WEqualsLocallyBijective (ModuleCat.{w} R)]
  {T : C}

/-- **Sections over a weakly contractible object preserve epimorphisms of sheaves of modules.**
An epimorphism of sheaves of modules is locally surjective, hence so is the underlying morphism
of sheaves of sets, which is then surjective on sections over `T` by hypothesis. -/
theorem preservesEpimorphisms_sheafSections_of_surjective_app
    (hW : ∀ {F G : Sheaf J (Type w)} (φ : F ⟶ G), Sheaf.IsLocallySurjective φ →
      Function.Surjective (φ.hom.app (op T))) :
    ((sheafSections J (ModuleCat.{w} R)).obj (op T)).PreservesEpimorphisms := by
  refine ⟨fun {F G} φ hφ => ?_⟩
  have h₁ : Sheaf.IsLocallySurjective φ :=
    (Sheaf.isLocallySurjective_iff_epi' (ModuleCat.{w} R) φ).2 hφ
  have h₂ : Sheaf.IsLocallySurjective
      ((sheafCompose J (CategoryTheory.forget (ModuleCat.{w} R))).map φ) := by
    rw [← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff]
    exact (Presheaf.isLocallySurjective_iff_whisker_forget _ φ.hom).mp
      ((Sheaf.isLocallySurjective_sheafToPresheaf_map_iff φ).mpr h₁)
  exact (ModuleCat.epi_iff_surjective _).2 (hW _ h₂)

/-- **The constant sheaf on a projective module is projective** on a site whose final object `T`
is weakly contractible: the constant sheaf functor is left adjoint to sections over `T`, which
preserve epimorphisms
(`Stacks.ConstantSheaf.preservesEpimorphisms_sheafSections_of_surjective_app`). -/
theorem projective_constantSheaf_of_surjective_app (hT : IsTerminal T)
    (hW : ∀ {F G : Sheaf J (Type w)} (φ : F ⟶ G), Sheaf.IsLocallySurjective φ →
      Function.Surjective (φ.hom.app (op T)))
    (M : ModuleCat.{w} R) [Projective M] :
    Projective ((constantSheaf J (ModuleCat.{w} R)).obj M) :=
  have := preservesEpimorphisms_sheafSections_of_surjective_app J R hW
  (constantSheafAdj J (ModuleCat.{w} R) hT).map_projective M inferInstance

end Stacks.ConstantSheaf

namespace Stacks.ModuleSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- **Sections over a weakly contractible object are exact** on sheaves of modules: they preserve
finite limits, as every evaluation functor does, and they preserve epimorphisms
(`Stacks.ConstantSheaf.preservesEpimorphisms_sheafSections_of_surjective_app`), hence they
preserve homology and so finite colimits. -/
theorem preservesFiniteColimits_sheafSections_of_surjective_app {T : C}
    (hW : ∀ {F G : Sheaf J (Type w)} (φ : F ⟶ G), Sheaf.IsLocallySurjective φ →
      Function.Surjective (φ.hom.app (op T)))
    (R : Type w) [Ring R] [HasSheafify J (ModuleCat.{w} R)]
    [J.HasSheafCompose (forget (ModuleCat.{w} R))] [J.WEqualsLocallyBijective (ModuleCat.{w} R)] :
    PreservesFiniteColimits ((sheafSections J (ModuleCat.{w} R)).obj (op T)) := by
  let E := (sheafSections J (ModuleCat.{w} R)).obj (op T)
  have : PreservesFiniteLimits E := inferInstanceAs (PreservesFiniteLimits
    (sheafToPresheaf J (ModuleCat.{w} R) ⋙ (evaluation Cᵒᵖ (ModuleCat.{w} R)).obj (op T)))
  have : E.Additive := inferInstanceAs
    (sheafToPresheaf J (ModuleCat.{w} R) ⋙ (evaluation Cᵒᵖ (ModuleCat.{w} R)).obj (op T)).Additive
  have : E.PreservesEpimorphisms :=
    Stacks.ConstantSheaf.preservesEpimorphisms_sheafSections_of_surjective_app J R hW
  have : E.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels E
  exact Functor.preservesFiniteColimits_of_preservesHomology E

end Stacks.ModuleSheaf
