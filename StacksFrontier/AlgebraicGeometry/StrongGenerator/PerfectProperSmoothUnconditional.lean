module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.KernelVariableBox
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.ZeroDimensionalTestModules
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.CanonicalFunctor
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.QuasiCompactBounded
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.DiagonalBoxGeneratorUnconditional
public import StacksFrontier.AlgebraicGeometry.StrongGenerator.PerfectProperSmooth
public import StacksFrontier.CategoryTheory.Triangulated.FullSubcategoryEnvelope

/-!
# A strong generator for the perfect derived category of a proper smooth scheme

Let `k` be a field and let `X` be a scheme proper and smooth over `k`. Then `D_perf(𝒪_X)` has a
strong generator. This is [Stacks, Tag 0FZ6].

## The proof

It is the source's. [Stacks, Tag 0FZ5] gives finite locally free `ℰ`, `𝒢` with
`𝒪_Δ ∈ ⟨ℰ ⊠ 𝒢⟩` in `D(𝒪_{X × X})`, hence `𝒪_Δ ∈ ⟨ℰ ⊠ 𝒢⟩ₙ` for one `n`
([Stacks, Tag 0ATG]). For a perfect `K` the functor
`Ψ_K = R pr_{2,*}(L pr_1^* K ⊗^𝐋 −)` (`AlgebraicGeometry.fourierMukaiKernelFunctor`) is exact, so
it carries `⟨ℰ ⊠ 𝒢⟩ₙ` into `⟨Ψ_K(ℰ ⊠ 𝒢)⟩ₙ` ([Stacks, Tag 0FX5],
`Stacks.TriangulatedGenerators.triangEnvelopeIter_inverseImage_of_le`). Two computations finish:

* `Ψ_K(𝒪_Δ) ≅ K`, Example [Stacks, Tag 0FYV]
  (`AlgebraicGeometry.fourierMukaiKernelFunctorDiagonalIso`);
* `Ψ_K(ℰ ⊠ 𝒢) = RΓ(X, ℰ ⊗^𝐋 K) ⊗_k 𝒢 ∈ ⟨𝒢⟩₀`, by [Stacks, Tag 08EU], [Stacks, Tag 08IB], and
  the finite dimensionality of the cohomology of `X`, which is where properness enters
  (`AlgebraicGeometry.fourierMukaiKernelFunctor_box_mem_triangEnvelopeIter_zero`).

So every perfect `K` lies in `⟨𝒢⟩ₙ` in `D(𝒪_X)`, with `n` independent of `K`, and since
`D_perf(𝒪_X)` is a triangulated subcategory the same membership holds inside it
(`CategoryTheory.ObjectProperty.isStrongTriangulatedGenerator_of_triangEnvelopeIter_map_ι`).

## Main results

* `AlgebraicGeometry.isStrongTriangulatedGenerator_perfectDerivedCategory_of_diagonal`: `𝒢`
  strongly generates `D_perf(𝒪_X)` as soon as `𝒪_Δ ∈ ⟨ℰ ⊠ 𝒢⟩` for finite locally free `ℰ`, `𝒢`,
  for `X` proper and flat over `k`.
* `AlgebraicGeometry.exists_isStrongTriangulatedGenerator_perfectDerivedCategory`:
  **[Stacks, Tag 0FZ6]**, with `ℰ`, `𝒢` supplied by [Stacks, Tag 0FZ5]
  (`AlgebraicGeometry.exists_finiteLocallyFree_triangEnvelope_diagonal`).

## Implementation notes

`D_perf(𝒪_X)` is `Stacks.Perfect.BoundedLocallyFreeComplexes.PerfectDerivedCategory X` of
[Stacks, Tag 0F8I], the full subcategory of perfect objects of `D(𝒪_X)` at
`CategoryTheory.HasDerivedCategory.standard`, which is triangulated by
`Stacks.Perfect.BoundedLocallyFreeComplexes.perfectDerivedProperty_isTriangulated`. The
Fourier-Mukai computations are at the same model.

## References

* [Stacks Project, Tag 0FZ6](https://stacks.math.columbia.edu/tag/0FZ6)
* [Stacks Project, Tag 0FZ5](https://stacks.math.columbia.edu/tag/0FZ5)
* [Stacks Project, Tag 0FYV](https://stacks.math.columbia.edu/tag/0FYV)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 0ATG](https://stacks.math.columbia.edu/tag/0ATG)
* [Stacks Project, Tag 0FX5](https://stacks.math.columbia.edu/tag/0FX5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open Stacks.Perfect.BoundedLocallyFreeComplexes

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

/-- **A strong generator of `D_perf(𝒪_X)` from the diagonal.** Let `k` be a field and let
`f : X ⟶ Spec k` be proper and flat. If `ℰ` and `𝒢` are finite locally free `𝒪_X`-modules with
`𝒪_Δ ∈ ⟨ℰ ⊠ 𝒢⟩` in `D(𝒪_{X × X})`, then `𝒢` is a strong generator of `D_perf(𝒪_X)`.

This is the proof of [Stacks, Tag 0FZ6] after its first sentence, which invokes
[Stacks, Tag 0FZ5]. -/
theorem isStrongTriangulatedGenerator_perfectDerivedCategory_of_diagonal {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [Flat f] (E G : X.Modules)
    (hE : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (hG : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) G)
    (hdiag : (ObjectProperty.singleton ((DerivedCategory.singleFunctor (pullback f f).Modules 0).obj
          (externalTensorProduct f f E G))).triangEnvelope
        ((DerivedCategory.singleFunctor (pullback f f).Modules 0).obj
          ((Scheme.Modules.pushforward (pullback.diagonal f)).obj
            (SheafOfModules.unit X.ringCatSheaf)))) :
    (ObjectProperty.singleton (⟨(DerivedCategory.singleFunctor X.Modules 0).obj G,
      isPerfect_single_of_isFiniteLocallyFree' G hG⟩ : PerfectDerivedCategory X)
      ).IsStrongTriangulatedGenerator := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  -- The level is read off the single object `𝒪_Δ`, once and for all.
  obtain ⟨n, hn⟩ := (ObjectProperty.prop_triangEnvelope_iff _ _).1 hdiag
  refine isStrongTriangulatedGenerator_of_triangEnvelopeIter_map_ι
    (fun K : DerivedCategory X.Modules =>
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K) _ n fun K => ?_
  have hle : ObjectProperty.singleton ((DerivedCategory.singleFunctor X.Modules 0).obj G) ≤
      (ObjectProperty.singleton (⟨(DerivedCategory.singleFunctor X.Modules 0).obj G,
        isPerfect_single_of_isFiniteLocallyFree' G hG⟩ : PerfectDerivedCategory X)).map
        (ObjectProperty.ι _) :=
    singleton_le_iff.2 (prop_map_obj _ _ ((ObjectProperty.singleton_iff _ _).2 rfl))
  -- `K` is bounded with coherent cohomology.
  obtain ⟨a, b, ha, hb⟩ := Stacks.AlgebraicGeometry.PerfectCohomology.exists_isGE_isLE_of_isPerfect
    X K.obj K.property
  have hKb : DerivedCategory.TStructure.t.bounded K.obj := ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  have hKcoh := isCoherent_homology_of_isPerfect'
    X K.obj K.property
  -- Push `𝒪_Δ ∈ ⟨ℰ ⊠ 𝒢⟩ₙ` forward along the exact functor `Ψ_K`.
  have hK := Stacks.TriangulatedGenerators.triangEnvelopeIter_inverseImage_of_le
    (fourierMukaiKernelFunctor f f K.obj)
    (P := ObjectProperty.singleton ((DerivedCategory.singleFunctor (pullback f f).Modules 0).obj
      (externalTensorProduct f f E G)))
    (Q := ObjectProperty.singleton ((DerivedCategory.singleFunctor X.Modules 0).obj G))
    (singleton_le_iff.2
      (fourierMukaiKernelFunctor_box_mem_triangEnvelopeIter_zero f E G hE hG K.obj hKb hKcoh))
    n _ hn
  exact monotone_triangEnvelopeIter hle n _
    (ObjectProperty.prop_of_iso _ (fourierMukaiKernelFunctorDiagonalIso f K.obj) hK)

/-- **[Stacks, Tag 0FZ6].** Let `k` be a field and let `X` be a scheme proper and smooth over
`k`. Then `D_perf(𝒪_X)` has a strong generator: there are an object `𝒢` and an integer `n` with
`⟨𝒢⟩ₙ = D_perf(𝒪_X)`.

The generator is the module `𝒢` of [Stacks, Tag 0FZ5] placed in degree zero, as in the source:
[Stacks, Tag 0FZ5] applies because a proper scheme over `k` is quasi-compact and separated, and
`isStrongTriangulatedGenerator_perfectDerivedCategory_of_diagonal` is the rest of the proof, a
smooth morphism being flat. -/
@[stacks 0FZ6]
theorem exists_isStrongTriangulatedGenerator_perfectDerivedCategory {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [Smooth f] :
    ∃ G : PerfectDerivedCategory X, (ObjectProperty.singleton G).IsStrongTriangulatedGenerator := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨E, G, hE, hG, hdiag⟩ :=
    exists_finiteLocallyFree_triangEnvelope_diagonal f
  exact ⟨_, isStrongTriangulatedGenerator_perfectDerivedCategory_of_diagonal f E G hE hG hdiag⟩

end AlgebraicGeometry

end
