module

public import Mathlib.Algebra.Category.Grp.Colimits
public import StacksFrontier.Homology.Injectives.Sheaf.AbelianSheavesOnSpace
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Module.CharacterModule
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Topology.Sheaves.Skyscraper
public import StacksFrontier.CategoryTheory.Preadditive.Injective.Adjunction
public import StacksFrontier.CategoryTheory.Preadditive.Injective.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.InjectiveSheavesRestrictOnto
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Injective abelian sheaves on a topological space

Let `X` be a topological space. The category of sheaves of abelian groups on `X` has enough
injectives; in fact it admits functorial injective embeddings in the sense of Stacks Tag 0139.
Moreover an injective abelian sheaf is flasque: its restriction maps are all surjective.

## Main results

* `Stacks.Cohomology.abelianSheaf_enoughInjectives`: the category
  `TopCat.Sheaf AddCommGrpCat X` has enough injectives.
* `Stacks.Cohomology.abelianSheaf_hasFunctorialInjectiveEmbeddings`: it has functorial
  injective embeddings.
* `Stacks.Cohomology.isFlasque_of_injective`: an injective abelian sheaf is flasque;
  `Stacks.Cohomology.exists_isFlasque_mono`: every abelian sheaf embeds into a flasque one.

## Implementation notes

Abelian sheaves on `X` are `TopCat.Sheaf AddCommGrpCat X`. In the enough-injectives statements
the coefficient universe contains the universe of the space, so that the stalk colimits and the
point-indexed products used in the Stacks proof stay inside this category.

## References

* [Stacks Project, Tag 01DG](https://stacks.math.columbia.edu/tag/01DG)
* [Stacks Project, Tag 0139](https://stacks.math.columbia.edu/tag/0139)
* [Stacks Project, Tag 01EA](https://stacks.math.columbia.edu/tag/01EA)
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped ZeroObject

universe u v

namespace Stacks.Cohomology

open Stacks.Cohomology.InjectiveRestriction.Abelian

/-! ### Enough injectives -/

/-- The category of abelian sheaves on a topological space has enough injectives. -/
@[stacks 01DG "enough injectives",
  sga "4 II 6.9" "site of opens of a space",
  sga "4 V 0.1.1" "sheaves on a space"]
instance abelianSheaf_enoughInjectives (X : TopCat.{u}) :
    EnoughInjectives (TopCat.Sheaf AddCommGrpCat.{max u v} X) :=
  Stacks.Injectives.abelianSheaf_enoughInjectives.{u, v} X

/-- Abelian sheaves on a topological space admit functorial injective embeddings. -/
@[stacks 01DG "functorial injective embeddings",
  sga "4 II 6.9" "site of opens of a space",
  sga "4 V 0.1.1" "sheaves on a space"]
theorem abelianSheaf_hasFunctorialInjectiveEmbeddings (X : TopCat.{u}) :
    HasFunctorialInjectiveEmbeddings (TopCat.Sheaf AddCommGrpCat.{max u v} X) :=
  Stacks.Injectives.abelianSheaf_hasFunctorialInjectiveEmbeddings.{u, v} X

section Flasque

variable {X : TopCat.{u}}

/-- An injective sheaf of abelian groups on a topological space is flasque, stated with
Mathlib's `TopCat.Presheaf.IsFlasque`. -/
instance isFlasque_of_injective (I : TopCat.Sheaf AddCommGrpCat.{v} X) [Injective I] :
    TopCat.Presheaf.IsFlasque I.presheaf where
  epi {V W} i := by
    have hle : W.unop ≤ V.unop := leOfHom i.unop
    have hi : i = (homOfLE hle).op := Subsingleton.elim _ _
    rw [hi]
    exact ConcreteCategory.epi_of_surjective _
      (Stacks.Cohomology.InjectiveRestriction.injective_abelian_restriction_surjective I hle)

/-- Every abelian sheaf on a topological space embeds into a flasque one. -/
theorem exists_isFlasque_mono (X : TopCat.{u}) (F : TopCat.Sheaf AddCommGrpCat.{max u v} X) :
    ∃ G : TopCat.Sheaf AddCommGrpCat.{max u v} X, TopCat.Presheaf.IsFlasque G.presheaf ∧
      ∃ f : F ⟶ G, Mono f :=
  ⟨Injective.under F, isFlasque_of_injective _, Injective.ι F, inferInstance⟩

end Flasque

end Stacks.Cohomology

end
