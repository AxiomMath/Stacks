module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import StacksCore.Tactic.StacksAttribute

/-!
# Standard pro-étale coverings of affine schemes

A standard pro-étale covering of an affine scheme `T` is a finite family of weakly étale
morphisms `f i : X i ⟶ T` from affine schemes whose images cover `T`.

## Main definitions

* `AlgebraicGeometry.Scheme.IsStandardProEtaleCovering`: the predicate that a family of
  morphisms is a standard pro-étale covering.

## Main results

* `AlgebraicGeometry.Scheme.IsStandardProEtaleCovering.ofArrows_mem_proetalePrecoverage`: a
  standard pro-étale covering is a covering family of the pro-étale precoverage.

## References

* [Stacks Project, Tag 098E](https://stacks.math.columbia.edu/tag/098E)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Scheme

/-- A family of morphisms `f i : X i ⟶ T` is a *standard pro-étale covering* of `T` if `T` is
affine, the family is finite, each `X i` is affine, each `f i` is weakly étale, and the images of
the `f i` cover `T`. -/
@[stacks 098E]
structure IsStandardProEtaleCovering {T : Scheme.{u}} {ι : Type v} {X : ι → Scheme.{u}}
    (f : ∀ i, X i ⟶ T) : Prop where
  isAffine_target : IsAffine T
  finite_index : Finite ι
  isAffine_source (i : ι) : IsAffine (X i)
  weaklyEtale (i : ι) : WeaklyEtale (f i)
  iUnion_range_eq_univ : ⋃ i, Set.range (f i) = Set.univ

/-- A standard pro-étale covering is a covering family of the pro-étale precoverage. -/
theorem IsStandardProEtaleCovering.ofArrows_mem_proetalePrecoverage {T : Scheme.{u}}
    {ι : Type v} {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ T} (hf : IsStandardProEtaleCovering f) :
    Presieve.ofArrows X f ∈ proetalePrecoverage T := by
  have := hf.isAffine_target
  let 𝒰 : T.Cover (precoverage @WeaklyEtale) := Cover.mkOfCovers ι X f
    (fun x => Set.mem_iUnion.mp (hf.iUnion_range_eq_univ ▸ Set.mem_univ x)) hf.weaklyEtale
  have : Finite 𝒰.I₀ := hf.finite_index
  have : JointlySurjective (precoverage @WeaklyEtale) := instJointlySurjectivePrecoverage
  have (i : 𝒰.I₀) : QuasiCompact (𝒰.f i) :=
    have := hf.isAffine_source i
    (inferInstance : QuasiCompact (f i))
  exact (Cover.ofQuasiCompactCover 𝒰 (qc := QuasiCompactCover.of_finite)).mem₀

end AlgebraicGeometry.Scheme
