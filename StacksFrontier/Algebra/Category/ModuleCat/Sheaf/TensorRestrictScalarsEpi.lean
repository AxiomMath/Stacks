module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraEpiDegree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorRestrictScalarsLax

/-!
# The lax comparison of the tensor product with restriction of scalars is an epimorphism

Let `ρ : 𝒜 ⟶ ℬ` be a morphism of sheaves of commutative rings on a space and let `F`, `G` be
sheaves of `ℬ`-modules. The lax comparison

`(F|_𝒜) ⊗_𝒜 (G|_𝒜) ⟶ (F ⊗_ℬ G)|_𝒜`

of `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorRestrictScalarsLax` is **an
epimorphism**: a pure tensor is in its image by definition, pure tensors generate the sections of
the presheaf tensor product, and the sheafification unit is locally surjective, so the comparison
is locally surjective and therefore epi.

Nothing is lost in the other direction either: a morphism out of `F ⊗_ℬ G` and the `𝒜`-linear
morphism it induces have the same image. That consequence is
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorRestrictScalarsImage`.

The proof is assembled from local surjectivity in three steps, because restriction of scalars does
not change the underlying morphism of presheaves of abelian groups: the comparison on presheaves
is sectionwise surjective, the sheafification unit of the tensor product over `ℬ` is locally
surjective, and restriction of scalars preserves local surjectivity. Their composite is the
transpose `laxLeg` of the comparison, and a morphism which becomes locally surjective after
precomposition with a morphism of presheaves of modules is an epimorphism
(`Stacks.SheafOfModules.epi_of_isLocallySurjective_fac`).

## Main results

* `Stacks.SheafOfModules.TensorRestrictScalars.surjective_sectionMap`: the comparison on sections
  over an open set is surjective.
* `Stacks.SheafOfModules.TensorRestrictScalars.isLocallySurjective_presheafComparison` and
  `isLocallySurjective_laxLeg`: the presheaf comparison and the transpose of the sheaf comparison
  are locally surjective.
* `Stacks.SheafOfModules.TensorRestrictScalars.epi_laxComparison`: **the lax comparison is an
  epimorphism.**

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
-/

@[expose] public section

open CategoryTheory Opposite TensorProduct TopologicalSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace
open PresheafOfModules (ringedSpaceOfSheaf)

universe u

namespace Stacks.SheafOfModules.TensorRestrictScalars

variable {Y : TopCat.{u}} (A B : Sheaf (Opens.grothendieckTopology ↥Y) CommRingCat.{u})
  (ρ : A ⟶ B)

section Surjective

variable (M N : PresheafOfModules.{u} (O (ringedSpaceOfSheaf B)))

theorem surjective_sectionMap (U : (Opens ↥Y)ᵒᵖ) :
    Function.Surjective (sectionMap A B ρ M N U) := by
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul m n => exact ⟨m ⊗ₜ[A.obj.obj U] n, rfl⟩
  | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, (map_add _ a b).trans (congrArg₂ (· + ·) ha hb)⟩

theorem isLocallySurjective_presheafComparison :
    PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology ↥Y)
      (presheafComparison A B ρ M N) := by
  refine Presheaf.isLocallySurjective_of_surjective _ _ fun U t => ?_
  obtain ⟨s, hs⟩ := surjective_sectionMap A B ρ M N U t
  exact ⟨s, (presheafComparison_app_apply A B ρ M N U s).trans hs⟩

/-- Restriction of scalars does not change the underlying morphism of presheaves of abelian
groups, so it preserves local surjectivity. -/
theorem isLocallySurjective_restrictScalarsPresheaf_map {M N}
    (f : M ⟶ N)
    (hf : PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology ↥Y) f) :
    PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology ↥Y)
      ((restrictScalarsPresheaf A B ρ).map f) := hf

end Surjective

section Epi

variable (F G : SheafOfModules.{u} (structureSheafRing (ringedSpaceOfSheaf B)))

theorem isLocallySurjective_laxLeg :
    PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology ↥Y)
      (laxLeg A B ρ F G) := by
  have h1 := isLocallySurjective_presheafComparison A B ρ F.val G.val
  have h2 : PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology ↥Y)
      (sheafifyUnit (ringedSpaceOfSheaf B)
        (PresheafOfModules.tensorObj (O := (ringedSpaceOfSheaf B).presheaf) F.val G.val)) :=
    PresheafOfModules.isLocallySurjective_sheafificationAdjunction_unit_app
      (𝟙 (structureSheafRing (ringedSpaceOfSheaf B)).obj)
      (PresheafOfModules.tensorObj (O := (ringedSpaceOfSheaf B).presheaf) F.val G.val)
  exact Stacks.SheafOfModules.isLocallySurjective_comp h1
    (isLocallySurjective_restrictScalarsPresheaf_map A B ρ _ h2)

theorem sheafifyUnit_comp_laxComparison :
    sheafifyUnit (ringedSpaceOfSheaf A)
        (PresheafOfModules.tensorObj (O := (ringedSpaceOfSheaf A).presheaf)
          ((restrictScalarsSheaf A B ρ).obj F).val
          ((restrictScalarsSheaf A B ρ).obj G).val) ≫ (laxComparison A B ρ F G).val =
      laxLeg A B ρ F G :=
  homEquiv_laxComparison A B ρ F G

theorem epi_laxComparison : Epi (laxComparison A B ρ F G) :=
  Stacks.SheafOfModules.epi_of_isLocallySurjective_fac (laxComparison A B ρ F G)
    (sheafifyUnit_comp_laxComparison A B ρ F G) (isLocallySurjective_laxLeg A B ρ F G)

end Epi

end Stacks.SheafOfModules.TensorRestrictScalars

end
