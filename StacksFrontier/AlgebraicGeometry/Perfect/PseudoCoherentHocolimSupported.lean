module

public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentHocolim

/-!
# Pseudo-coherent objects with support as homotopy colimits of perfect objects

Let `X` be a quasi-compact and quasi-separated scheme and let `T ⊆ X` be a closed subset whose
complement is quasi-compact. [Stacks, Tag 0DJP] says that an object `K` of `D(𝒪_X)` supported
on `T` is pseudo-coherent if and only if `K = hocolim Kₙ` for a system of perfect objects `Kₙ`,
each supported on `T`, such that `τ_{≥ -n} Kₙ ⟶ τ_{≥ -n} K` is an isomorphism for every `n`.

## Main results

* `Stacks.PseudoCoherentHocolim.isPseudoCoherent_iff_exists_supported_perfect_hocolim`:
  **[Stacks, Tag 0DJP]**, at an arbitrary model of `D(𝒪_X)`.

## Implementation notes

The system `(Kₙ)` is a functor `F : ℕ ⥤ D(𝒪_X)`, and `K = hocolim Kₙ` is
`CategoryTheory.Pretriangulated.IsHomotopyColimitWith F K c` (Definition 090Z), which records the
coprojections `c n : Kₙ ⟶ K` of the defining triangle; the map `τ_{≥ -n} Kₙ ⟶ τ_{≥ -n} K` of the
source is the truncation of `c n`. The direct sum of the system, needed to write the triangle
down, is part of the data of the second condition.

Both implications are proved in `StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentHocolim`,
together with [Stacks, Tag 0DJN]: (2) ⟹ (1) holds on any ringed space, and (1) ⟹ (2) builds the
tower from approximations of the triples `(T, K, m)`, which is the only change to the proof of
0DJN that the source asks for.

As there, the model `[HasDerivedCategory.{w} X.Modules]` is passed explicitly, because instance
search does not identify `X.Modules` with its spellings `SheafOfModules X.ringCatSheaf` and
`OXMod X.toRingedSpace`.

## References

* [Stacks Project, Tag 0DJP](https://stacks.math.columbia.edu/tag/0DJP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry

universe w u

namespace Stacks.PseudoCoherentHocolim

/-- **[Stacks, Tag 0DJP].** Let `X` be a quasi-compact and quasi-separated scheme, let `T ⊆ X` be
a closed subset with `X \ T` quasi-compact and let `K ∈ D(𝒪_X)` be supported on `T`. Then `K` is
pseudo-coherent if and only if `K = hocolim Kₙ` for a system `F` of perfect objects `Kₙ`, each
supported on `T`, such that `τ_{≥ -n} Kₙ ⟶ τ_{≥ -n} K` is an isomorphism for every `n`; here
`c n : Kₙ ⟶ K` are the coprojections of the homotopy colimit. The derived category is an
arbitrary model of `D(𝒪_X)`. -/
@[stacks 0DJP]
theorem isPseudoCoherent_iff_exists_supported_perfect_hocolim (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] [h : HasDerivedCategory.{w} X.Modules]
    (T : Set X) (hT : IsClosed T) (hTc : IsCompact Tᶜ) (K : DerivedCategory X.Modules)
    (hK : @Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn _ X.ringCatSheaf h T K) :
    @RingedSpace.IsPseudoCoherent X.toRingedSpace h K ↔
      ∃ (F : ℕ ⥤ DerivedCategory X.Modules) (_ : HasCoproduct F.obj) (c : ∀ n, F.obj n ⟶ K),
        (∀ n, @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace h (F.obj n)) ∧
        (∀ n, @Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn _ X.ringCatSheaf h
          T (F.obj n)) ∧
        IsHomotopyColimitWith F K c ∧
        ∀ n : ℕ, IsIso ((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).map (c n)) := by
  refine ⟨exists_perfect_hocolim_of_isPseudoCoherent_of_supportedOn T hT hTc K hK, ?_⟩
  rintro ⟨F, hF, c, hP, -, hc, htr⟩
  exact @isPseudoCoherent_of_isHomotopyColimitWith_perfect X.toRingedSpace h K F hF c hP hc htr

end Stacks.PseudoCoherentHocolim

end
