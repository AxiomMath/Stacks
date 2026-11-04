module

public import
  StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.ExtendingFunctorsCategories.Extension
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.FunctorsModuleCategories.Additivity
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.FunctorsModuleCategories.RightExact
public import
  StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.FunctorsModuleCategories.FiniteSubdiagrams
public import StacksCore.Tactic.StacksAttribute

/-!
# Additivity, direct sums and right exactness of extensions from finite modules

The filtered-colimit-preserving extension of an additive functor on finite modules is additive
and commutes with arbitrary direct sums, and the extension of a right exact functor is right
exact. For a Noetherian source ring the finite modules are finitely presented, so the first two
assertions are the ones already proved for finitely presented modules; the third is proved here
for an extension of a functor between categories of finite modules.

## Main results

* `ModuleCat.FGFilteredColimitExtension.preservesFiniteColimits` is right exactness of the
  extension.

## Implementation notes

The result is stated for an arbitrary filtered-colimit extension together with its specified
comparison isomorphism, rather than only for the chosen construction. The Noetherian hypothesis
on the source ring supplies the extension in the first place; once an extension is given the
proof uses only its restriction to the finite modules and filtered colimits of finite
subdiagrams, all inside the given module universe.

## References

* [Stacks Project, Tag 0GP6](https://stacks.math.columbia.edu/tag/0GP6)
* [Stacks Project, Tag 0GP9](https://stacks.math.columbia.edu/tag/0GP9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace ModuleCat

add_to_stacks 0GP6 "part (1), additivity" ModuleCat.filteredColimitExtension_additive
add_to_stacks 0GP6 "part (1), arbitrary direct sums"
  ModuleCat.filteredColimitExtension_preservesCoproducts
add_to_stacks 0GP6 "part (2)" ModuleCat.filteredColimitExtension_preservesFiniteColimits

/-- **Stacks Project, Tag 0GP9.** A filtered-colimit extension of a right exact functor on
finite modules is right exact. The Noetherian hypothesis on `A` is what supplies the extension
in the first place; the proof below only uses the extension. -/
@[stacks 0GP9 "right_exactness"]
lemma FGFilteredColimitExtension.preservesFiniteColimits
    (A : Type u) [CommRing A] [IsNoetherianRing A] (B : Type w) [CommRing B]
    {F : FGModuleCat.{v} A ⥤ FGModuleCat.{v} B}
    (E : FGFilteredColimitExtension.{u, v, w} A B F)
    [PreservesFiniteColimits F] :
    PreservesFiniteColimits E.functor :=
  preservesFiniteColimits_of_finiteModuleRestriction A B F E.functor E.iso

end ModuleCat
