module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.KernelVariable
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.KernelVariableBox
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.CoherentTorSheaves
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.DiagonalBoxGeneratorUnconditional
public import StacksFrontier.AlgebraicGeometry.StrongGenerator.CoherentBoxWindow
public import StacksFrontier.AlgebraicGeometry.StrongGenerator.UniformWindowTransfer

/-!
# A generator with uniform bounds for the coherent modules of a proper smooth scheme

Let `k` be a field and let `X` be a scheme proper and smooth over `k`. Then there are integers
`m, n ≥ 1` and a finite locally free `𝒪_X`-module `𝒢` such that every coherent `𝒪_X`-module
lies in `smd(add(𝒢[-m, m])^{⋆ n})`, with notation as in Derived Categories, Section 13.35. This
is [Stacks, Tag 0FZ7]. This file runs the source's proof from the diagonal presentation of
[Stacks, Tag 0FZ5], which is the one input taken as a hypothesis, in exactly the form
`AlgebraicGeometry.exists_finiteLocallyFree_triangEnvelope_diagonal_of_homVanishing` concludes.
No `stacks` attribute is attached here: the tag is registered on
`AlgebraicGeometry.exists_uniform_generator_isCoherent` in
`StacksFrontier/AlgebraicGeometry/StrongGenerator/CoherentUniformGeneratorUnconditional.lean`, where
the diagonal presentation is supplied by the proved [Stacks, Tag 0FZ5].

## The proof

The source's proof, step by step:

* [Stacks, Tag 0FZ5], the hypothesis: finite locally free `ℰ`, `𝒢` with `𝒪_Δ ∈ ⟨ℰ ⊠ 𝒢⟩` in
  `D(𝒪_{X × X})`.
* For each coherent `ℱ`, the exact functor `Ψ_ℱ = R pr_{2,*}(L pr_1^* ℱ ⊗^𝐋 −)`
  (`AlgebraicGeometry.fourierMukaiKernelFunctor`), with `Ψ_ℱ(𝒪_Δ) ≅ ℱ` ([Stacks, Tag 0FYV],
  `AlgebraicGeometry.fourierMukaiKernelFunctorDiagonalIso`).
* The box computation `Ψ_ℱ(ℰ ⊠ 𝒢) = RΓ(X, ℰ ⊗^𝐋 ℱ) ⊗_k 𝒢`, which lies in
  `smd(add(𝒢[a, b]))` whenever `RΓ(X, ℰ ⊗^𝐋 ℱ)` has cohomology only in `[a, b]`
  ([Stacks, Tag 08EU] together with finite dimensionality of cohomology, [Stacks, Tag 08E2];
  `AlgebraicGeometry.fourierMukaiKernelFunctor_box_mem_window`).
* The range `[a, b] = [0, t]` with `t` depending on `X` alone
  (`AlgebraicGeometry.exists_isZero_homology_dpush_singleTensor_of_isFiniteLocallyFree`,
  [Stacks, Tag 08D5]); this replaces the source's `[0, dim X]`.
* The level and the window read off the single object `𝒪_Δ` and carried along every `Ψ_ℱ`
  unchanged (`Stacks.TriangulatedGenerators.`
  `exists_uniform_retractClosure_extensionProductIter_of_triangEnvelope`, [Stacks, Tag 0FX5],
  [Stacks, Tag 0FX9]).

## Main results

* `AlgebraicGeometry.exists_uniform_generator_isCoherent_of_exists_triangEnvelope_diagonal`:
  the conclusion of [Stacks, Tag 0FZ7] from the diagonal presentation, and
  `AlgebraicGeometry.exists_uniform_generator_isCoherent_of_homVanishing` the same with that
  presentation supplied by [Stacks, Tag 0FZ5] from the `Hom`-vanishing of [Stacks, Tag 0FZ3].

## Implementation notes

The derived categories are read at `CategoryTheory.HasDerivedCategory.standard`, the model the
Fourier–Mukai functors and [Stacks, Tag 0FZ5] are stated at. `smd`, `add` and `⋆ n` are
`CategoryTheory.ObjectProperty.retractClosure`,
`CategoryTheory.ObjectProperty.binaryProductsClosure` and
`CategoryTheory.ObjectProperty.extensionProductIter`. Mathlib counts extensions rather than
factors, so `P.extensionProductIter n` is the source's `P^{⋆ (n + 1)}`; since these subcategories
increase with `n`, the existential statement is the same in either indexing.

## References

* [Stacks Project, Tag 0FZ7](https://stacks.math.columbia.edu/tag/0FZ7)
* [Stacks Project, Tag 0FZ6](https://stacks.math.columbia.edu/tag/0FZ6)
* [Stacks Project, Tag 0FZ5](https://stacks.math.columbia.edu/tag/0FZ5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

/-- **The uniform generator for the coherent modules, from a diagonal presentation.** Let `k` be
a field and let `X` be a scheme proper and smooth over `k`. Suppose there are finite locally free
`𝒪_X`-modules `ℰ` and `𝒢` with `𝒪_Δ ∈ ⟨ℰ ⊠ 𝒢⟩` in `D(𝒪_{X × X})`. Then there are integers
`m, n ≥ 1` such that every coherent `𝒪_X`-module, placed in degree zero, lies in
`smd(add(𝒢[-m, m])^{⋆ n})`.

The hypothesis `hdiag` is exactly the conclusion of
`AlgebraicGeometry.exists_finiteLocallyFree_triangEnvelope_diagonal_of_homVanishing`; everything
else in the proof of the source is done here. For each coherent `ℱ` the exact functor
`Ψ_ℱ = R pr_{2,*}(L pr_1^* ℱ ⊗^𝐋 −)` sends `𝒪_Δ` to `ℱ`
(`AlgebraicGeometry.fourierMukaiKernelFunctorDiagonalIso`) and `ℰ ⊠ 𝒢` into `smd(add(𝒢[0, t]))`
(`AlgebraicGeometry.fourierMukaiKernelFunctor_box_mem_window`), the window `[0, t]` depending on
`X` alone (`AlgebraicGeometry.exists_isZero_homology_dpush_singleTensor_of_isFiniteLocallyFree`);
the uniform transfer `exists_uniform_retractClosure_extensionProductIter_of_triangEnvelope` in
`Stacks.TriangulatedGenerators` then gives one `m` and one `n` for all `ℱ`. -/
theorem exists_uniform_generator_isCoherent_of_exists_triangEnvelope_diagonal {k : Type u}
    [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [Smooth f]
    (hdiag : ∃ E G : X.Modules,
      SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) E ∧
      SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) G ∧
      (ObjectProperty.singleton ((DerivedCategory.singleFunctor (pullback f f).Modules 0).obj
          (externalTensorProduct f f E G))).triangEnvelope
        ((DerivedCategory.singleFunctor (pullback f f).Modules 0).obj
          ((Scheme.Modules.pushforward (pullback.diagonal f)).obj
            (SheafOfModules.unit X.ringCatSheaf)))) :
    ∃ (m n : ℕ) (𝒢 : X.Modules), 1 ≤ m ∧ 1 ≤ n ∧
      SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) 𝒢 ∧
      ∀ F : X.Modules, F.IsCoherent →
        ((⨆ i ∈ Set.Icc (-(m : ℤ)) (m : ℤ), (ObjectProperty.singleton
            ((DerivedCategory.singleFunctor X.Modules 0).obj 𝒢)).isoClosure.shift i
          ).binaryProductsClosure.extensionProductIter n).retractClosure
            ((DerivedCategory.singleFunctor X.Modules 0).obj F) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨E, G, hE, hG, hdiag⟩ := hdiag
  obtain ⟨t, ht⟩ := exists_isZero_homology_dpush_singleTensor_of_isFiniteLocallyFree f E hE
  obtain ⟨m, n, hm, hn, h⟩ :=
    open Stacks.TriangulatedGenerators in
    exists_uniform_retractClosure_extensionProductIter_of_triangEnvelope
      (ι := {F : X.Modules // F.IsCoherent}) (fun F => fourierMukaiKernelFunctor f f
        ((DerivedCategory.singleFunctor X.Modules 0).obj F.1))
      _ _ hdiag ((DerivedCategory.singleFunctor X.Modules 0).obj G) 0 t
      (fun F => (DerivedCategory.singleFunctor X.Modules 0).obj F.1)
      (fun F => ⟨fourierMukaiKernelFunctorDiagonalIso f _⟩)
      (fun F => fourierMukaiKernelFunctor_box_mem_window f E G hE hG _
        ⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩
        (TorFormula.isCoherent_homology_singleFunctor_obj X F.1 F.2) 0 t (by omega)
        (fun i hi => ht F.1
          (And.left (((Stacks.AlgebraicGeometry.CoherentTFAE.coherent_tfae X F.1).out 1 2).mp F.2))
          i hi))
  exact ⟨m, n, G, hm, hn, hG, fun F hF => h ⟨F, hF⟩⟩

/-- **The uniform generator for the coherent modules, from the `Hom`-vanishing across a
cohomology gap.** The same conclusion as
`exists_uniform_generator_isCoherent_of_exists_triangEnvelope_diagonal`, with the diagonal
presentation produced by
`AlgebraicGeometry.exists_finiteLocallyFree_triangEnvelope_diagonal_of_homVanishing`; a proper
`X` over `k` is quasi-compact and separated over `k`, which is what that statement asks. -/
theorem exists_uniform_generator_isCoherent_of_homVanishing
    (hvan : HomVanishingAcrossCohomologyGap.{u}) {k : Type u} [Field k] {X : Scheme.{u}}
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
    (exists_finiteLocallyFree_triangEnvelope_diagonal_of_homVanishing hvan f)

end AlgebraicGeometry

end
