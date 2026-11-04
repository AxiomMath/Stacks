module

public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.DiagonalBoxGeneratorUnconditional
public import StacksFrontier.AlgebraicGeometry.StrongGenerator.CoherentUniformGeneratorFromDiagonal

/-!
# A generator with uniform bounds for the coherent modules of a proper smooth scheme

Let `k` be a field and let `X` be a scheme proper and smooth over `k`. There are integers
`m, n ≥ 1` and a finite locally free `𝒪_X`-module `𝒢` such that every coherent `𝒪_X`-module
lies in `smd(add(𝒢[-m, m])^{⋆ n})`, with notation as in Derived Categories, Section 13.35. This is
[Stacks, Tag 0FZ7], under exactly the source's hypotheses.

## The proof

`AlgebraicGeometry.exists_uniform_generator_isCoherent_of_exists_triangEnvelope_diagonal` runs
the source's proof from the diagonal presentation `𝒪_Δ ∈ ⟨ℰ ⊠ 𝒢⟩`, and that presentation is
[Stacks, Tag 0FZ5], proved as `AlgebraicGeometry.exists_finiteLocallyFree_triangEnvelope_diagonal`.
A scheme proper over `k` is quasi-compact and separated over `k`, which is what that statement
asks.

## Main results

* `AlgebraicGeometry.exists_uniform_generator_isCoherent`: **[Stacks, Tag 0FZ7]**.

## Implementation notes

The derived category is read at `CategoryTheory.HasDerivedCategory.standard`, the model the
Fourier–Mukai functors of `StacksFrontier/AlgebraicGeometry/DerivedVarieties/FourierMukai/` and the
diagonal presentation of [Stacks, Tag 0FZ5] are stated at. `smd`, `add` and `⋆ n` are
`CategoryTheory.ObjectProperty.retractClosure`,
`CategoryTheory.ObjectProperty.binaryProductsClosure` and
`CategoryTheory.ObjectProperty.extensionProductIter`; `E[c, d]` is
`⨆ i ∈ Set.Icc c d, E.isoClosure.shift i`. Mathlib counts extensions rather than factors, so
`P.extensionProductIter n` is the source's `P^{⋆ (n + 1)}`. These subcategories grow with `n`,
so "for some `n ≥ 1`" means the same thing in either indexing.

## References

* [Stacks Project, Tag 0FZ7](https://stacks.math.columbia.edu/tag/0FZ7)
* [Stacks Project, Tag 0FZ5](https://stacks.math.columbia.edu/tag/0FZ5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

/-- **[Stacks, Tag 0FZ7].** Let `k` be a field and let `X` be a scheme proper and smooth over
`k`. There are integers `m, n ≥ 1` and a finite locally free `𝒪_X`-module `𝒢` such that every
coherent `𝒪_X`-module, placed in degree zero, is a direct summand of an object obtained by `n`
extensions from finite direct sums of the shifts of `𝒢` by the degrees in `[-m, m]`; that is,
it lies in `smd(add(𝒢[-m, m])^{⋆ n})`. -/
@[stacks 0FZ7]
theorem exists_uniform_generator_isCoherent {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [Smooth f] :
    ∃ (m n : ℕ) (𝒢 : X.Modules), 1 ≤ m ∧ 1 ≤ n ∧
      SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) 𝒢 ∧
      ∀ F : X.Modules, F.IsCoherent →
        ((⨆ i ∈ Set.Icc (-(m : ℤ)) (m : ℤ), (ObjectProperty.singleton
            ((DerivedCategory.singleFunctor X.Modules 0).obj 𝒢)).isoClosure.shift i
          ).binaryProductsClosure.extensionProductIter n).retractClosure
            ((DerivedCategory.singleFunctor X.Modules 0).obj F) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  exact exists_uniform_generator_isCoherent_of_exists_triangEnvelope_diagonal f
    (exists_finiteLocallyFree_triangEnvelope_diagonal f)

end AlgebraicGeometry

end
