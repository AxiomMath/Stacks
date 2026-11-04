module

public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentExactSequence
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentSquare

/-!
# The relative map of a tower as the map of a square

Let `R ⟶ A ⟶ C` and `R ⟶ B ⟶ C` be two towers of sheaves of commutative rings on a topological
space with the same composite `R ⟶ C`, say `p ≫ q = bc ≫ s`.  Stacks 0E1Y attaches to the second
tower the relative map `NL_{C/R} ⟶ NL_{C/B}`, whose source is the naive cotangent complex built
from the structure morphism `bc ≫ s`; a consumer meeting the *first* tower has instead the
complex built from `p ≫ q`, and the two are identified by `eqToHom` along the compatibility
equation.

This file absorbs that `eqToHom`: the composite

`eqToHom ≫ (NL_{C/R} ⟶ NL_{C/B})`

is the canonical map of Stacks 08TK attached to the commutative square with horizontal morphisms
`p ≫ q` and `s` and vertical morphisms `bc` and `𝟙 C`, with no transport left to carry.  That is
the form in which the stalk of the map is computable: the stalk of the map of a square is the
functorial map of the induced morphism of canonical presentations of the stalks
(`Stacks.NaiveCotangentAffineStalkLegs.stalkLegLinear_spaceNaiveCotangentComplexMapOfSquare_negOne`
and its degree `0` companion), whereas nothing computes the stalk of an `eqToHom` composed with a
relative map.

## Main results

* `Stacks.SheafOfModules.eqToHom_comp_spaceRelativeNaiveCotangentComplexMap`: **the absorption.**
* `Stacks.SheafOfModules.comp_id_eq_of_tower`: the compatibility equation of the two towers read
  as the commutativity of that square.

## Implementation notes

The statement is proved by generalising the structure morphism `p ≫ q` of the first tower to a
variable morphism `m : R ⟶ C` together with an equation `m = bc ≫ s`.  `subst` then eliminates
`m`, which turns the `eqToHom` into an identity; stated directly for `p ≫ q` there is nothing to
substitute, since `p ≫ q` is not a variable.  After the substitution the two sides are the same
map by definition: `Stacks.SheafOfModules.relativeNaiveCotangentComplexMap` *is* the map of the
square with vertical morphisms the first structure morphism and `𝟙 C`.

## References

* [Stacks Project, Tag 0E1Y](https://stacks.math.columbia.edu/tag/0E1Y), the base-change and
  relative maps of naive cotangent complexes of a tower of sheaves of rings.
* [Stacks Project, Tag 08TK](https://stacks.math.columbia.edu/tag/08TK), the canonical map of
  naive cotangent complexes attached to a square of sheaves of rings on a space.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

noncomputable section

namespace Stacks.SheafOfModules

variable {T : TopCat.{u}}
  (R A B C : CategoryTheory.Sheaf (Opens.grothendieckTopology T) CommRingCat.{u})
  (p : R ⟶ A) (q : A ⟶ C) (bc : R ⟶ B) (s : B ⟶ C) (hbc : p ≫ q = bc ≫ s)

include hbc in
/-- The compatibility equation of two towers with the same composite, read as the commutativity
of the square with horizontal morphisms `p ≫ q` and `s` and vertical morphisms `bc` and
`𝟙 C`. -/
theorem comp_id_eq_of_tower : (p ≫ q) ≫ 𝟙 C = bc ≫ s := by
  rw [Category.comp_id]; exact hbc

include hbc in
/-- **The `eqToHom` along the compatibility equation of two towers is absorbed into the relative
map of Stacks 0E1Y.**  For `p ≫ q = bc ≫ s`, the identification of the naive cotangent complex
of `C` over `R` built from `p ≫ q` with the one built from `bc ≫ s`, followed by the relative
map `NL_{C/R} ⟶ NL_{C/B}` of the second tower, is the canonical map of Stacks 08TK attached to
the square with vertical morphisms `bc` and `𝟙 C`. -/
theorem eqToHom_comp_spaceRelativeNaiveCotangentComplexMap :
    eqToHom (congrArg (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) R C)
          hbc) ≫
        spaceRelativeNaiveCotangentComplexMap R B C bc s =
      spaceNaiveCotangentComplexMapOfSquare R B C C (p ≫ q) s bc (𝟙 C)
        (comp_id_eq_of_tower R A B C p q bc s hbc) := by
  have key : ∀ (m : R ⟶ C) (e : m = bc ≫ s) (h : m ≫ 𝟙 C = bc ≫ s),
      eqToHom (congrArg (naiveCotangentComplex.{u, u, u, u}
            (Opens.grothendieckTopology T) R C) e) ≫
          spaceRelativeNaiveCotangentComplexMap R B C bc s =
        spaceNaiveCotangentComplexMapOfSquare R B C C m s bc (𝟙 C) h := by
    intro m e h
    subst e
    exact (Category.id_comp _).trans rfl
  exact key (p ≫ q) hbc _

end Stacks.SheafOfModules

end

end
