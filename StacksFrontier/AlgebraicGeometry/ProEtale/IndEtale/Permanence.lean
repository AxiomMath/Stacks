module

public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import StacksFrontier.RingTheory.Etale.FilteredColimit.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Permanence properties of ind-étale algebras

The class of ind-étale algebras over a commutative ring is stable under base change, under
composition, under filtered colimits, and it cancels on the left: a morphism of ind-étale
`A`-algebras `B → C` exhibits `C` as ind-étale over `B`.

All four assertions are already available in the filtered-colimit library for ind-étale ring
maps, where ind-étaleness is expressed by `CategoryTheory.ObjectProperty.ind` applied to the
property of being étale.  This module records the Stacks tags they realize.

## Main results

* `CommAlgCat.ind_etale_of_isPushout`: ind-étaleness is preserved by base change.
* `CommAlgCat.ind_etale_comp`: ind-étale algebra maps are closed under composition.
* `CategoryTheory.ObjectProperty.ind_ind`: applying the ind-construction twice to a property
  of finitely presentable objects is the same as applying it once; specialized to étale
  algebras over a fixed ring this says that a filtered colimit of ind-étale algebras is
  ind-étale.
* `CommRingCat.ind_etale_of_comp` and `CommAlgCat.ind_etale_of_comp`: the bundled-ring and
  algebra-tower forms of left cancellation.
* `CommRingCat.ind_etale_comp`: the bundled-ring form of closure under composition.

## Implementation notes

For base change the base-changed algebra is an abstract pushout algebra rather than a chosen
tensor product, so the statement is independent of the model of the tensor product and
specializes to the canonical algebra structure on `B ⊗[A] A'`.  Compatible ring maps
`A → B → C` are expressed by algebra structures together with `IsScalarTower A B C`.  Left
cancellation and composition are recorded in both the bundled-ring and the algebra-tower form
because clients use both representations; the bundled-ring form of composition is obtained
from the algebra-tower form by endowing the two ring maps with the algebra structures they
define.

## References

* [Stacks Project, Tag 097J](https://stacks.math.columbia.edu/tag/097J)
* [Stacks Project, Tag 097K](https://stacks.math.columbia.edu/tag/097K)
* [Stacks Project, Tag 097L](https://stacks.math.columbia.edu/tag/097L)
* [Stacks Project, Tag 097M](https://stacks.math.columbia.edu/tag/097M)
-/

@[expose] public section

add_to_stacks 097J CommAlgCat.ind_etale_of_isPushout
add_to_stacks 097K CommAlgCat.ind_etale_comp
add_to_stacks 097L CategoryTheory.ObjectProperty.ind_ind
add_to_stacks 097M CommRingCat.ind_etale_of_comp
add_to_stacks 097M CommAlgCat.ind_etale_of_comp

open CategoryTheory

universe u

namespace CommRingCat

/-- The composition of two ind-étale ring maps is ind-étale, in the bundled-ring spelling of
ind-étaleness as `CategoryTheory.MorphismProperty.ind` of `CommRingCat.etale`.

This is `CommAlgCat.ind_etale_comp` read through the algebra structures that the two ring maps
define, the composite carrying the algebra structure of the composed ring map. -/
theorem ind_etale_comp {A B C : CommRingCat.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (hf : MorphismProperty.ind.{u} CommRingCat.etale.{u} f)
    (hg : MorphismProperty.ind.{u} CommRingCat.etale.{u} g) :
    MorphismProperty.ind.{u} CommRingCat.etale.{u} (f ≫ g) := by
  let _ : Algebra A B := f.hom.toAlgebra
  let _ : Algebra B C := g.hom.toAlgebra
  let _ : Algebra A C := (g.hom.comp f.hom).toAlgebra
  let _ : IsScalarTower A B C := .of_algebraMap_eq fun _ ↦ rfl
  exact CommAlgCat.ind_etale_iff_ind_algebraMap.mp
    (CommAlgCat.ind_etale_comp
      (CommAlgCat.ind_etale_iff_ind_algebraMap.mpr hf)
      (CommAlgCat.ind_etale_iff_ind_algebraMap.mpr hg))

end CommRingCat
