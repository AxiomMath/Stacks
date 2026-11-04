module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.IntegralRefinement
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.EtaleDiagonalComplement

/-!
# Fibre degrees on the complement of the graph of a compactified étale covering

Let `p = j ≫ ν : U ⟶ X` be an étale covering factored through an open immersion `j : U ⟶ T` with
dense image and an integral morphism `ν : T ⟶ X`, and let `W` be the complement of the graph of
`j` inside `U ×_X T`. A bound for the fibre degrees of `W ⟶ T` which holds over the dense image
of `j` holds over all of `T`, since for a flat separated morphism of finite presentation with
universally bounded fibres the locus where the fibre degree is at most `n` is closed.

## Main results

* `Stacks.MoreMorphisms.boundsFiberDegrees_of_dense_of_forall_mem` — a bound on the fibre degrees
  of a flat separated morphism of finite presentation with universally bounded fibres which holds
  over a dense set of points of the base holds over every point.
* `Stacks.MoreMorphisms.hasUniversallyBoundedFibers_openImmersionGraphCompl_ι_snd` — the
  complement of the graph has universally bounded fibres over `T`, its source being affine.
* `Stacks.MoreMorphisms.boundsFiberDegrees_openImmersionGraphCompl_of_denseRange` — a bound for
  the fibre degrees of the complement of the graph over the image of `j` extends to one over `T`.

## References

* [Stacks Project, Tag 03JA](https://stacks.math.columbia.edu/tag/03JA)
* [Stacks Project, Tag 07RY](https://stacks.math.columbia.edu/tag/07RY)
* [Stacks Project, Tag 09Z0](https://stacks.math.columbia.edu/tag/09Z0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.MoreMorphisms

variable {U X : Scheme.{u}}

/-- **Fibre-degree bounds spread from a dense set of points of the base.** If the fibre of a flat
separated morphism of finite presentation with universally bounded fibres has degree at most `n`
over every point of a dense subset of the base, then `n` bounds the degrees of all of its
fibres. -/
public theorem boundsFiberDegrees_of_dense_of_forall_mem {W T : Scheme.{u}} (g : W ⟶ T)
    [Flat g] [LocallyOfFinitePresentation g] [IsSeparated g]
    (hb : HasUniversallyBoundedFibers g) (n : ℕ) {D : Set T} (hD : Dense D)
    (hon : ∀ t ∈ D, ∃ r : ℕ, r ≤ n ∧
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank (g.fiberToSpecResidueField t) r) :
    BoundsFiberDegrees g (n : ℤ) := by
  have hcl := (isClosed_fiber_rank_lt g hb (n + 1)).closure_subset_iff (s := D)
  rw [hD.closure_eq] at hcl
  intro t
  obtain ⟨r, hr, hrank⟩ := hcl.mpr (fun t ht => let ⟨r, hr, h⟩ := hon t ht; ⟨r, by omega, h⟩)
    (Set.mem_univ t)
  exact ⟨r, by omega, hrank⟩

/-- The complement of the graph of `j` has universally bounded fibres over `T`, for `U` affine. -/
public theorem hasUniversallyBoundedFibers_openImmersionGraphCompl_ι_snd {T : Scheme.{u}}
    (j : U ⟶ T) (ν : T ⟶ X) [IsOpenImmersion j] [IsAffine U] [IsIntegralHom ν]
    [Etale (j ≫ ν)] :
    HasUniversallyBoundedFibers
      ((openImmersionGraphCompl j ν).ι ≫ pullback.snd (j ≫ ν) ν) := by
  have : IsAffine (openImmersionGraphCompl j ν).toScheme :=
    isAffine_openImmersionGraphCompl j ν
  have : CompactSpace (openImmersionGraphCompl j ν).toScheme :=
    Scheme.compactSpace_of_isAffine _
  obtain ⟨n, hn⟩ := exists_nat_boundsFiberDegrees_of_etale_of_compactSpace
    ((openImmersionGraphCompl j ν).ι ≫ pullback.snd (j ≫ ν) ν)
  exact ⟨(n : ℤ), hn⟩

/-- **The fibre-degree bound on the complement of the graph extends from the image of `j`.** If
the image of `j` is dense in `T` and the fibres of the complement of the graph have degree at
most `n` over the points of that image, then `n` bounds the degrees of all of its fibres. -/
public theorem boundsFiberDegrees_openImmersionGraphCompl_of_denseRange {T : Scheme.{u}}
    (j : U ⟶ T) (ν : T ⟶ X) [IsOpenImmersion j] [IsAffine U] [IsIntegralHom ν]
    [Etale (j ≫ ν)] (n : ℕ) (hj : DenseRange j.base)
    (hon : ∀ t ∈ Set.range j.base, ∃ r : ℕ, r ≤ n ∧
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank
        (((openImmersionGraphCompl j ν).ι ≫
          pullback.snd (j ≫ ν) ν).fiberToSpecResidueField t) r) :
    BoundsFiberDegrees ((openImmersionGraphCompl j ν).ι ≫ pullback.snd (j ≫ ν) ν) (n : ℤ) := by
  have : IsAffine (openImmersionGraphCompl j ν).toScheme :=
    isAffine_openImmersionGraphCompl j ν
  have : Etale ((openImmersionGraphCompl j ν).ι ≫ pullback.snd (j ≫ ν) ν) := inferInstance
  exact boundsFiberDegrees_of_dense_of_forall_mem _
    (hasUniversallyBoundedFibers_openImmersionGraphCompl_ι_snd j ν) n hj hon

end Stacks.MoreMorphisms

end
