module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Triangulated.Generators
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Perfect.GeomReducedFibre.ModelTransfer
public import StacksFrontier.AlgebraicGeometry.Perfect.RegularCoherentPerfect
public import StacksFrontier.AlgebraicGeometry.StrongGenerator.CoherentUniformGeneratorUnconditional
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.ProperVanishing
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.CategoryTheory.Triangulated.ExactFunctorBoundedOperations
public import StacksFrontier.CategoryTheory.Triangulated.Generators
public import StacksFrontier.Homology.DerivedCategory.LocallySmall
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Defs
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree

/-!
# A generator with uniform bounds for the coherent modules of a proper smooth scheme

Let `k` be a field and let `X` be a scheme proper and smooth over `k`. Then there are integers
`m, n ≥ 1` and a finite locally free `𝒪_X`-module `𝒢` such that *every* coherent
`𝒪_X`-module lies in `smd(add(𝒢[-m, m])^{⋆ n})`: one window `[-m, m]` of shifts of `𝒢` and one
number `n` of extensions, the same for every coherent sheaf. This is [Stacks, Tag 0FZ7], read
here in the locally small derived category `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`.

## The proof

The tag is proved at the *standard* derived-category model as
`AlgebraicGeometry.exists_uniform_generator_isCoherent`, in
`StacksFrontier/AlgebraicGeometry/StrongGenerator/CoherentUniformGeneratorUnconditional.lean`: the
diagonal presentation of [Stacks, Tag 0FZ5] and the Fourier–Mukai functors through which the
source's argument runs are stated at that model. The two models are equivalent, by
`AlgebraicGeometry.Scheme.Modules.derivedModelEquiv`, but they sit at different universes and the
equivalence is not the identity, so the statement has to be carried across rather than reread.
That transport is all this file does, in two steps:

* the equivalence is exact, so [Stacks, Tag 0FX5] — here `Stacks.TriangulatedGenerators.`
  `retractClosure_extensionProductIter_biSup_shift_inverseImage_of_le` — moves
  `smd(add(𝒢[-m, m])^{⋆ n})` across it with the window `[-m, m]` and the level `n` unchanged,
  since each of the four closure operations transfers along an exact functor;
* `StacksDraft.Perfect.GeomReducedFibre.modelEquivSingleIso` identifies the image under the
  equivalence of a module placed in cohomological degree zero with that module placed in degree
  zero in the other model, which turns the transported membership into the one asserted.

## Main results

* `AlgebraicGeometry.exists_uniform_generator_isCoherent_of_diagonalEnvelope`:
  **[Stacks, Tag 0FZ7]** at the locally small model.

## Implementation notes

`smd`, `add` and `⋆ n` are `CategoryTheory.ObjectProperty.retractClosure`,
`CategoryTheory.ObjectProperty.binaryProductsClosure` and
`CategoryTheory.ObjectProperty.extensionProductIter`, and `E[c, d]` is
`⨆ i ∈ Set.Icc c d, E.isoClosure.shift i`, as in
`StacksFrontier/CategoryTheory/Triangulated/Generators.lean`. Mathlib's indexing counts extensions
rather than factors, so `P.extensionProductIter n` is the source's `P^{⋆ (n + 1)}`; the `n` of
the conclusion is therefore at least the source's `n = 1` whenever `1 ≤ n`, as asserted.

`ObjectProperty.shift j` is the inverse image under `⟦j⟧`, so a member of
`E.isoClosure.shift j` is isomorphic to some `E⟦-j⟧`. With `E` the singleton of `𝒢` placed in
cohomological degree zero, `E.isoClosure.shift j` is therefore `𝒢` placed in cohomological
degree `j`, and `⨆ i ∈ Set.Icc a b, E.isoClosure.shift i` is `𝒢` in the degrees `a, …, b`.

The ambient category is `DerivedCategory X.Modules` at the locally small model
`CategoryTheory.HasDerivedCategory.{u}` of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`. The membership asserted is the same
read in `D_perf(𝒪_X)` or in `D(𝒪_X)`, since the former is a full triangulated subcategory of the
latter closed under direct summands, so none of the four closure operations leaves it; reading it
in `D(𝒪_X)` is what lets the conclusion speak of a coherent module directly.

The window arithmetic of [Stacks, Tag 0FX2] and [Stacks, Tag 0FX4] that the source's proof
consumes is `StacksFrontier/CategoryTheory/Triangulated/BoundedWindows.lean`.

## References

* [Stacks Project, Tag 0FZ7](https://stacks.math.columbia.edu/tag/0FZ7)
* [Stacks Project, Tag 0FZ5](https://stacks.math.columbia.edu/tag/0FZ5)
* [Stacks Project, Tag 0FX2](https://stacks.math.columbia.edu/tag/0FX2)
* [Stacks Project, Tag 0FX4](https://stacks.math.columbia.edu/tag/0FX4)
* [Stacks Project, Tag 0FX5](https://stacks.math.columbia.edu/tag/0FX5)
* [Stacks Project, Tag 0FX9](https://stacks.math.columbia.edu/tag/0FX9)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.ObjectProperty

universe u

namespace AlgebraicGeometry

open Stacks.Cohomology.PerfectComplexes Stacks.TriangulatedGenerators
open StacksDraft.Perfect.GeomReducedFibre

/-- **[Stacks, Tag 0FZ7].** Let `k` be a field and let `X` be a scheme proper and smooth over
`k`. Then there are `m, n ≥ 1` and a finite locally free `𝒪_X`-module `𝒢` such that every
coherent `𝒪_X`-module is a direct summand of an `n`-fold extension of finite direct sums of the
shifts of `𝒢` by the degrees in `[-m, m]`.

This is the tag read in the locally small derived category
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`. It comes from
`AlgebraicGeometry.exists_uniform_generator_isCoherent`, the same tag at the standard model, by
transport along the exact equivalence `AlgebraicGeometry.Scheme.Modules.derivedModelEquiv`:
[Stacks, Tag 0FX5] carries `smd(add(𝒢[-m, m])^{⋆ n})` across an exact functor with the window and
the level unchanged, and `StacksDraft.Perfect.GeomReducedFibre.modelEquivSingleIso` identifies the
two readings of a module placed in cohomological degree zero.

The name records the route by which the statement was first proved here, from the diagonal
presentation of [Stacks, Tag 0FZ5]. -/
@[stacks 0FZ7 "the source's statement, read at the locally small derived-category model \
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` and proved there by transporting \
`AlgebraicGeometry.exists_uniform_generator_isCoherent` — the same tag at the standard model, in \
StacksFrontier/AlgebraicGeometry/StrongGenerator/CoherentUniformGeneratorUnconditional.lean — along \
the exact equivalence `AlgebraicGeometry.Scheme.Modules.derivedModelEquiv`, with Stacks 0FX5 \
(`Stacks.TriangulatedGenerators.`\
`retractClosure_extensionProductIter_biSup_shift_inverseImage_of_le`) moving the four closure \
operations with the window and the level fixed and \
`StacksDraft.Perfect.GeomReducedFibre.modelEquivSingleIso` identifying the two readings of a \
module in cohomological degree zero. The name records the route by which the statement was first \
proved here"]
theorem exists_uniform_generator_isCoherent_of_diagonalEnvelope
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsProper f] [Smooth f] :
    ∃ (m n : ℕ) (𝒢 : X.Modules), 1 ≤ m ∧ 1 ≤ n ∧
      SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) 𝒢 ∧
      ∀ F : X.Modules, F.IsCoherent →
        ((⨆ i ∈ Set.Icc (-(m : ℤ)) (m : ℤ), (ObjectProperty.singleton
            ((DerivedCategory.singleFunctor X.Modules 0).obj 𝒢)).isoClosure.shift i
          ).binaryProductsClosure.extensionProductIter n).retractClosure
            ((DerivedCategory.singleFunctor X.Modules 0).obj F) := by
  obtain ⟨m, n, G, hm, hn, hG, h⟩ := exists_uniform_generator_isCoherent f
  refine ⟨m, n, G, hm, hn, hG, fun F hF => ?_⟩
  -- Carry the standard-model membership across the exact equivalence of the two models, keeping
  -- the window `[-m, m]` and the level `n`: [Stacks, Tag 0FX5].
  have key := retractClosure_extensionProductIter_biSup_shift_inverseImage_of_le
    (Scheme.Modules.derivedModelEquiv X).functor
    (Q := (ObjectProperty.singleton
      ((DerivedCategory.singleFunctor X.Modules 0).obj G)).isoClosure)
    (fun Z hZ => by
      obtain rfl := (ObjectProperty.singleton_iff _ _).1 hZ
      exact ⟨_, (ObjectProperty.singleton_iff _ _).2 rfl,
        ⟨modelEquivSingleIso (HasDerivedCategory.standard _) _ G⟩⟩)
    (-(m : ℤ)) (m : ℤ) n _ (h F hF)
  rw [ObjectProperty.isoClosure_eq_self] at key
  -- The image of `F` placed in degree zero is `F` placed in degree zero in the other model.
  exact ObjectProperty.prop_of_iso _
    (modelEquivSingleIso (HasDerivedCategory.standard _) _ F) key

end AlgebraicGeometry

end
