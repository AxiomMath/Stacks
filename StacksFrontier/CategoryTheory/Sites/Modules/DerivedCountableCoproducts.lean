module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Coproducts
public import StacksFrontier.CategoryTheory.Sites.Modules.GrothendieckAbelian
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Countable direct sums in the derived category of presheaves of modules

A Grothendieck abelian category has exact countable direct sums: coproducts of every size exist,
and exactness of a countable direct sum follows from AB5 after shrinking the index universe.
Consequently, for a presheaf of rings `O` on a category `C`, the localization
`Q : C(Mod(O)) ⥤ D(Mod(O))` preserves countable coproducts, so a countable direct sum in
`D(Mod(O))` is computed by the termwise direct sum of representing complexes.

## Main results

* `hasExactCountableDirectSums_of_isGrothendieckAbelian`: a Grothendieck abelian category has
  exact countable direct sums.
* `Stacks.SheafOfModules.presheafOfModules_hasExactCountableDirectSums`: presheaves of modules
  have exact countable direct sums, at independent site, ring and module universes.
* `Stacks.SheafOfModules.derivedCategoryQ_preservesCountableCoproducts`: `DerivedCategory.Q` on
  complexes of presheaves of modules preserves coproducts indexed by a countable type.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

/-- A Grothendieck abelian category has exact countable direct sums. -/
theorem hasExactCountableDirectSums_of_isGrothendieckAbelian (A : Type u) [Category.{v} A]
    [Abelian A] [IsGrothendieckAbelian.{w} A] :
    HasExactCountableDirectSums A := by
  let : HasCoproducts.{0} A := hasCoproducts_shrink
  let : AB4OfSize.{0} A := AB4OfSize_shrink A
  refine ⟨inferInstance, fun J hJ => ?_⟩
  let : Countable J := hJ
  let : HasExactColimitsOfShape (Discrete J) A := CountableAB4.ofShape J
  exact ⟨inferInstance, inferInstance⟩

namespace Stacks.SheafOfModules

universe r t

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ RingCat.{r})

/-- Presheaves of modules have exact countable direct sums, with the site, ring and module
universes independent. -/
@[sga "3 I 3.1.1" "partial"]
theorem presheafOfModules_hasExactCountableDirectSums :
    HasExactCountableDirectSums (PresheafOfModules.{max u v r t} O) :=
  let : IsGrothendieckAbelian.{max u v r t} (PresheafOfModules.{max u v r t} O) :=
    presheafModulesGrothendieck.{u, v, r, t} O
  hasExactCountableDirectSums_of_isGrothendieckAbelian _

/-- The localization `Q : C(Mod(O)) ⥤ D(Mod(O))` preserves countable coproducts. -/
theorem derivedCategoryQ_preservesCountableCoproducts
    [HasDerivedCategory.{max u v r t} (PresheafOfModules.{max u v r t} O)]
    (J : Type) [Countable J] :
    PreservesColimitsOfShape (Discrete J)
      (DerivedCategory.Q (C := PresheafOfModules.{max u v r t} O)) :=
  derivedCategory_Q_preservesCoproductsOfShape (PresheafOfModules.{max u v r t} O)
    (presheafOfModules_hasExactCountableDirectSums.{v, u, r, t} O) J

end Stacks.SheafOfModules

end
