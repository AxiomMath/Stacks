module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery
import StacksCore.Tactic.StacksAttribute

/-!
# K-flat complexes of sheaves of modules

Let `(C, O)` be a ringed site, with `O` a sheaf of commutative rings, and write
`Mod(O) = SheafOfModules (ringSheaf O)`. A cochain complex `K^•` of `O`-modules is *K-flat*
when `Tot(F^• ⊗_O K^•)` is acyclic for every acyclic cochain complex `F^•` of `O`-modules.
This is Stacks 06Y9, stated there for a ringed space; a ringed site is a meaningful
generalisation of that.

The tensor product of sheaves of modules — the sheafification of the sectionwise tensor
product `U ↦ F(U) ⊗_{O(U)} G(U)` — and its total complex are
`Stacks.SheafOfModules.Tensor.sheafTensor` and `Stacks.SheafOfModules.Tensor.tensorComplex`,
and the predicate is stated in terms of them.

## Main definitions

* `Stacks.SheafOfModules.IsKFlat`: K-flatness of a cochain complex of sheaves of modules on a
  ringed site, for the canonical tensor product.

## Implementation notes

The predicate is an abbreviation, so a client may introduce an acyclic complex and apply the
resulting acyclicity assertion directly.

`CochainComplex.KFlatMonoidal.KFlat` is K-flatness in an arbitrary abelian monoidal category,
and `CochainComplex.DerivedTensor.IsKFlat` is K-flatness with respect to an *arbitrary* tensor
bifunctor on sheaves of modules. The definition here is the instance of the latter at the
canonical tensor product.

The typeclass arguments are those of `Stacks.SheafOfModules.Tensor.tensorComplex`: additivity of
the tensor bifunctor in each variable, and the countable direct sums needed to form the total
complexes.

## References

* [Stacks Project, Tag 06Y9](https://stacks.math.columbia.edu/tag/06Y9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{w})
  [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
  [HasBinaryBiproducts (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf R))]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w} R).Additive]
  [∀ X, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w} R).obj X).Additive]
  [∀ (K₁ K₂ : HomologicalComplex
      (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf R)) (ComplexShape.up ℤ)),
    K₁.HasMapBifunctorReg K₂ (Stacks.SheafOfModules.Tensor.sheafTensor R) (ComplexShape.up ℤ)]

/-- A cochain complex `K` of sheaves of `R`-modules is **K-flat** if `Tot(F ⊗_R K)` is acyclic
for every acyclic cochain complex `F`. -/
@[stacks 06Y9]
abbrev IsKFlat
    (K : CochainComplex (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ) : Prop :=
  ∀ F : CochainComplex (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ,
    F.Acyclic → (((Stacks.SheafOfModules.Tensor.tensorComplex R).obj F).obj K).Acyclic

end Stacks.SheafOfModules
