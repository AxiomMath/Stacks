module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.ExtendingFunctorsCategories.Extension
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.ExtendingFunctorsCategories.FiniteModuleRestriction
public import StacksCore.Tactic.StacksAttribute

/-!
# Direct sums and extensions from finite modules

An additive functor between categories of finite modules over a Noetherian source ring has a
filtered-colimit-preserving extension which commutes with arbitrary direct sums.

## Main results

* `ModuleCat.FGFilteredColimitExtension.preservesCoproducts`: the extension preserves direct sums
  indexed by any type in the module universe.

## Implementation notes

The result applies to an arbitrary extension equipped with its filtered-colimit preservation and
its specified identification on the finite modules. Preservation of colimits of discrete shape
includes the canonical comparison with the direct sum and its naturality. Only the source ring
has to be Noetherian — finite modules over it are then finitely presented — while the target
module category has arbitrary direct sums for every commutative ring.

## References

* [Stacks Project, Tag 0GP9](https://stacks.math.columbia.edu/tag/0GP9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace ModuleCat

/-- **Stacks Project, Tag 0GP9.** An additive functor on finite modules has a
direct-sum-preserving filtered-colimit extension to all modules. -/
@[stacks 0GP9 "direct_sums"]
lemma FGFilteredColimitExtension.preservesCoproducts
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (B : Type w) [CommRing B]
    {F : FGModuleCat.{v} A ⥤ FGModuleCat.{v} B}
    (E : FGFilteredColimitExtension.{u, v, w} A B F)
    [F.Additive] (J : Type v) :
    PreservesColimitsOfShape (Discrete J) E.functor := by
  let : (forget₂ (FGModuleCat.{v} B) (ModuleCat.{v} B)).Additive := ⟨by intros; rfl⟩
  let : (forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A) ⋙ E.functor).Additive :=
    Functor.additive_of_iso E.iso.symm
  exact preservesCoproducts_of_finiteModuleRestriction A E.functor J

end ModuleCat
