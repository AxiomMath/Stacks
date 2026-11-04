module

public import StacksFrontier.AlgebraicGeometry.ProjectiveLine.ClosedPoints

/-!
# The complement of a closed point of the projective line

For a homogeneous irreducible form `f ∈ k[T₀, T₁]` the standard open `D₊(f)` of
`ℙ¹_k = Proj k[T₀, T₁]` is exactly the complement of the closed point `V₊(f)`. It is therefore an
open subscheme of `ℙ¹_k` with one point removed, and since `f` has positive degree it is affine —
it is the curve `X` of [Stacks, Tag 0CDP], whose Picard group that tag computes.

## Main definitions

* `Stacks.ProjectiveLine.complementIsoSpec`: the complement of `V₊(f)` is the spectrum of the
  degree-zero part of `k[T₀, T₁]` localized away from `f`.

## Main results

* `Stacks.ProjectiveLine.coe_basicOpen_eq_compl_singleton` and
  `Stacks.ProjectiveLine.compl_coe_basicOpen_eq_singleton`: **`D₊(f) = ℙ¹_k ∖ {V₊(f)}`**, in both
  directions.
* `Stacks.ProjectiveLine.range_ι_basicOpen`: the same identification read as the range of the
  open immersion of the open subscheme `D₊(f)`.
* `Stacks.ProjectiveLine.isAffineOpen_basicOpen`: the complement of `V₊(f)` is an affine open.
* `Stacks.ProjectiveLine.compl_coe_basicOpen_X_eq_singleton` and
  `Stacks.ProjectiveLine.compl_range_ι_basicOpen_X_eq_singleton`: the complement of a standard
  chart of `ℙ¹_k` is the single closed point `V₊(Tᵢ)`.

## References

* [Stacks Project, Tag 0CDP](https://stacks.math.columbia.edu/tag/0CDP)
-/

@[expose] public section

open AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.ProjectiveLine

universe u

variable {k : Type u} [Field k] {d : ℕ} {f : MvPolynomial (Fin 2) k}

/-- A homogeneous irreducible form is a member of the graded piece in its own degree. -/
theorem mem_grading (hf : f.IsHomogeneous d) : f ∈ grading k d :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).mpr hf

/-- **The standard open `D₊(f)` is the complement of the closed point `V₊(f)`.** -/
theorem coe_basicOpen_eq_compl_singleton (hf : f.IsHomogeneous d) (hirr : Irreducible f) :
    (Proj.basicOpen (grading k) f : Set (Proj (grading k))) =
      ({pointOfForm hf hirr} : Set (ProjectiveSpectrum (grading k)))ᶜ := by
  rw [← zeroLocus_singleton_eq hf hirr]
  refine Set.ext fun x => ?_
  exact (Proj.mem_basicOpen (grading k) f x).trans
    (ProjectiveSpectrum.mem_compl_zeroLocus_iff_notMem (grading k)).symm

/-- **The complement of the standard open `D₊(f)` is the single closed point `V₊(f)`.** -/
theorem compl_coe_basicOpen_eq_singleton (hf : f.IsHomogeneous d) (hirr : Irreducible f) :
    ((Proj.basicOpen (grading k) f : Set (Proj (grading k))))ᶜ =
      ({pointOfForm hf hirr} : Set (ProjectiveSpectrum (grading k))) := by
  refine Set.ext fun x => ?_
  refine ((not_congr (Proj.mem_basicOpen (grading k) f x)).trans not_not).trans ?_
  exact ⟨fun hx => eq_pointOfForm_of_mem hf hirr x hx, fun hx => hx ▸ mem_pointOfForm hf hirr⟩

/-- The open subscheme `D₊(f)` of `ℙ¹_k` has the complement of `V₊(f)` as its range: it *is*
`ℙ¹_k` with the closed point `V₊(f)` removed. -/
theorem range_ι_basicOpen (hf : f.IsHomogeneous d) (hirr : Irreducible f) :
    Set.range (Proj.basicOpen (grading k) f).ι.base =
      ({pointOfForm hf hirr} : Set (ProjectiveSpectrum (grading k)))ᶜ := by
  rw [Scheme.Opens.range_ι, coe_basicOpen_eq_compl_singleton hf hirr]

/-- The complement of `V₊(f)` is an affine open of `ℙ¹_k`, because `f` has positive degree. -/
theorem isAffineOpen_basicOpen (hf : f.IsHomogeneous d) (hirr : Irreducible f) :
    IsAffineOpen (Proj.basicOpen (grading k) f) :=
  Proj.isAffineOpen_basicOpen (grading k) f (mem_grading hf) (pos_of_irreducible hf hirr)

/-- The complement of `V₊(f)` is an affine scheme. -/
theorem isAffine_basicOpen (hf : f.IsHomogeneous d) (hirr : Irreducible f) :
    IsAffine (Proj.basicOpen (grading k) f).toScheme :=
  isAffineOpen_basicOpen hf hirr

/-- **The complement of `V₊(f)` in `ℙ¹_k`** as the spectrum of a ring: the degree-zero part of
`k[T₀, T₁]` localized away from `f`. -/
noncomputable def complementIsoSpec (hf : f.IsHomogeneous d) (hirr : Irreducible f) :
    (Proj.basicOpen (grading k) f).toScheme ≅
      Spec (CommRingCat.of (HomogeneousLocalization.Away (grading k) f)) :=
  Proj.basicOpenIsoSpec (grading k) f (mem_grading hf) (pos_of_irreducible hf hirr)

/-! ### The complement of a standard chart -/

/-- **The complement of the standard chart `D₊(Tᵢ)` of `ℙ¹_k` is the single closed point
`V₊(Tᵢ)`.** -/
theorem compl_coe_basicOpen_X_eq_singleton (k : Type u) [Field k] (i : Fin 2) :
    ((Proj.basicOpen (grading k) (MvPolynomial.X i) : Set (Proj (grading k))))ᶜ =
      ({pointOfCoord k i} : Set (ProjectiveSpectrum (grading k))) :=
  compl_coe_basicOpen_eq_singleton (MvPolynomial.isHomogeneous_X k i)
    MvPolynomial.X_prime.irreducible

/-- The complement of the standard chart `D₊(Tᵢ)` of `ℙ¹_k`, read as the complement of the range
of the open immersion of that chart. -/
theorem compl_range_ι_basicOpen_X_eq_singleton (k : Type u) [Field k] (i : Fin 2) :
    (Set.range (Proj.basicOpen (grading k) (MvPolynomial.X i)).ι.base)ᶜ =
      ({pointOfCoord k i} : Set (ProjectiveSpectrum (grading k))) := by
  rw [Scheme.Opens.range_ι]
  exact compl_coe_basicOpen_X_eq_singleton k i

end Stacks.ProjectiveLine

end
