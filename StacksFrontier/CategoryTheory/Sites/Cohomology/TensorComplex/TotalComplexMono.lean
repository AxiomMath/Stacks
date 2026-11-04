module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedCategory
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.LocalPureTensorSections
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TotalComplexMono

/-!
# The total tensor complex preserves degreewise monomorphisms against flat terms

Let `(C, 𝒪)` be a ringed site, let `j : K ⟶ A` be a morphism of complexes of `𝒪`-modules which
is injective in every degree, and let `B` be a complex of `𝒪`-modules all of whose terms are
flat. Then `Tot(j ⊗_𝒪 B)` is injective in every degree.

This is the statement that lets a subcomplex `K^• ⊆ M^•` be recognised inside
`Tot(M^• ⊗ N^•)` through `Tot(K^• ⊗ N^•)`, which is what the source of [Stacks, Tag 0FPV] uses
when it says that *"`Tot(𝒦^• ⊗ 𝒩^•) ⊂ Tot(ℳ^• ⊗ 𝒩^•)` by flatness of the modules `𝒩^n`"*, and
hence that the coevaluation factors through the subcomplex.

Nothing below is a clause of a tag; these are steps of a proof, so no `@[stacks …]` attribute is
attached.

## Main results

The two statements themselves are
`Stacks.Cohomology.LeftDualPerfect.mono_whiskerRight_of_isFlat_general` and
`Stacks.Cohomology.LeftDualPerfect.mono_mapBifunctorMap_f_general` of
`StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TotalComplexMono`, stated there over an
arbitrary small site; they are not restated here, so that there is one copy and not two. This
file keeps the three instances on `Mod(𝒪)` that its consumers read:

* `Stacks.SheafOfModules.DerivedMonoidal.hasFiniteBiproducts_mod`,
  `Stacks.SheafOfModules.DerivedMonoidal.ab4Mod` and
  `Stacks.SheafOfModules.DerivedMonoidal.ab4Mod₀`.

## Implementation notes

Degree `n` of the total complex is the coproduct of the `K^p ⊗ B^q` with `p + q = n`
(`HomologicalComplex.isColimitCofanιMapBifunctor`), and a coproduct of monomorphisms is a
monomorphism because `Mod(𝒪)` satisfies AB4: it is a Grothendieck abelian category, so AB5
holds and `CategoryTheory.AB4.of_AB5` applies. The index type of the coproduct is
`{ij : ℤ × ℤ // ij.1 + ij.2 = n}`, which lives in `Type`, so AB4 is needed at size `0` and is
obtained from the ambient one by `CategoryTheory.AB4OfSize_shrink`.

The universes are those of `Stacks.SheafOfModules.DerivedMonoidal.Mod`: a small site
`C : Type u` with `SmallCategory.{u} C` and sections in `Type u`. That is forced by the ambient
spelling of the modules, not by the argument.

## References

* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
* [Stacks Project, Tag 0FPD](https://stacks.math.columbia.edu/tag/0FPD)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open Opposite

universe u

namespace Stacks.SheafOfModules.DerivedMonoidal

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The category `Mod(𝒪)` of sheaves of `𝒪`-modules has finite biproducts, being abelian. -/
instance hasFiniteBiproducts_mod : HasFiniteBiproducts (Mod R) := Abelian.hasFiniteBiproducts

/-- `Mod(𝒪)` satisfies AB4 at size `u`: coproducts of monomorphisms are monomorphisms, since
AB5 holds in `Mod(𝒪)`. -/
instance ab4Mod : AB4OfSize.{u} (Mod R) := AB4.of_AB5 (Mod R)

/-- `Mod(𝒪)` satisfies AB4 at size `0`, obtained from AB4 at size `u` by shrinking, so that it
applies to coproducts indexed by types in `Type`. -/
instance ab4Mod₀ : AB4OfSize.{0} (Mod R) := AB4OfSize_shrink.{0, u} (Mod R)

end Stacks.SheafOfModules.DerivedMonoidal

end
