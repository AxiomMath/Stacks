module

public import StacksFrontier.AlgebraicGeometry.NormAmple.Basic
public import StacksFrontier.AlgebraicGeometry.NormInvertible.Vanishing
public import StacksFrontier.AlgebraicGeometry.QuasiAffineNonvanishing.Basic

/-!
# Norms of quasi-affine schemes

Let `f : X ⟶ Y` be a finite morphism of schemes admitting a norm of degree `d ≥ 1` on functions
(`Stacks.Norm.MorphismNorm`). If `X` is quasi-affine, then so is `Y`.

## Main results

* `Stacks.Divisors.isQuasiAffine_of_morphismNorm`: If `f` is finite and admits a norm of positive
  degree and `X` is quasi-affine, then so is `Y`.
* `Stacks.Divisors.isQuasiAffine_of_isFiniteLocallyFreeOfRank`: If `f` is finite locally free of
  constant positive rank and `X` is quasi-affine, then so is `Y`.

## References

* [Stacks Project, Tag 0BD1](https://stacks.math.columbia.edu/tag/0BD1)
* [Stacks Project, Tag 0BD0](https://stacks.math.columbia.edu/tag/0BD0)
* [Stacks Project, Tag 0BD2](https://stacks.math.columbia.edu/tag/0BD2)
* [Stacks Project, Tag 0BD5](https://stacks.math.columbia.edu/tag/0BD5)
* [Stacks Project, Tag 0BCZ](https://stacks.math.columbia.edu/tag/0BCZ)
* [Stacks Project, Tag 0F20](https://stacks.math.columbia.edu/tag/0F20)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
* [Stacks Project, Tag 01QE](https://stacks.math.columbia.edu/tag/01QE)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.Divisors
open Stacks.Norm (MorphismNormMap MorphismNorm HasNormOfDegree IsDeterminantNorm)

variable {X Y : Scheme.{u}}

/-- Let `f : X ⟶ Y` be a finite morphism of schemes admitting a norm of degree `d ≥ 1`. If `X`
is quasi-affine, then so is `Y`. -/
@[stacks 0BD1]
public theorem isQuasiAffine_of_morphismNorm (f : X ⟶ Y) [IsFinite f] {d : ℕ} (hd : 1 ≤ d)
    (N : MorphismNorm f d) [X.IsQuasiAffine] : Y.IsQuasiAffine := by
  have hsurj : Function.Surjective f.base := surjective_of_morphismNorm f hd N
  have hcpt : CompactSpace Y := ⟨hsurj.range_eq ▸ isCompact_range f.continuous⟩
  refine Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen Y fun y => ?_
  obtain ⟨V, hVaff, hyV, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (X := Y) (x := y)
      (U := (⊤ : Y.Opens)) (Opens.mem_top y)
  have hEfin : (f.base ⁻¹' {y}).Finite := f.finite_preimage_singleton y
  have hEW : (f.base ⁻¹' {y}) ⊆ ((f ⁻¹ᵁ V : X.Opens) : Set X) := by
    rintro x (rfl : f.base x = y)
    exact hyV
  obtain ⟨g, hgE, hgW⟩ :=
    X.exists_basicOpen_subset_of_finite_of_isQuasiAffine hEfin (f ⁻¹ᵁ V) hEW
  set a : Γ(X, f ⁻¹ᵁ (⊤ : Y.Opens)) :=
    X.presheaf.map (homOfLE (le_top : f ⁻¹ᵁ (⊤ : Y.Opens) ≤ ⊤)).op g with ha
  have hba : X.basicOpen a = X.basicOpen g := by
    rw [ha, X.basicOpen_res g (homOfLE (le_top : f ⁻¹ᵁ (⊤ : Y.Opens) ≤ ⊤)).op]
    simp
  set t : Γ(Y, (⊤ : Y.Opens)) := N.app ⊤ a with ht
  have hkey : ∀ y' : Y, y' ∈ Y.basicOpen t ↔
      ∀ x : X, f.base x = y' → x ∈ X.basicOpen g := by
    intro y'
    rw [← Y.evaluation_ne_zero_iff_mem_basicOpen (U := ⊤) y' (Opens.mem_top y') t, ht,
      ne_eq, evaluation_norm_eq_zero_iff_exists_zero_in_fibre f N.toMorphismNormMap ⊤ a y'
        (Opens.mem_top y')]
    exact ⟨fun h x hx => Classical.byContradiction fun hcon =>
        h ⟨x, hx, (X.evaluation_eq_zero_iff_notMem_basicOpen x (by trivial) a).2 (hba ▸ hcon)⟩,
      fun h ⟨x, hx, hz⟩ =>
        (X.evaluation_eq_zero_iff_notMem_basicOpen x (by trivial) a).1 hz (hba ▸ h x hx)⟩
  have hle : Y.basicOpen t ≤ V := by
    intro y' hy'
    obtain ⟨x, rfl⟩ := hsurj y'
    exact hgW ((hkey _).1 hy' x rfl)
  refine ⟨t, ?_, (hkey y).2 fun x hx => hgE hx⟩
  have hres : Y.basicOpen (Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t) = Y.basicOpen t := by
    rw [Y.basicOpen_res t (homOfLE (le_top : V ≤ ⊤)).op]
    exact inf_eq_right.2 hle
  exact hres ▸ hVaff.basicOpen _

/- Tag 0BD5 case (1) asks only for `f` finite locally free, with surjectivity a separate
hypothesis; the statement below is that case for a morphism of constant positive rank, and
becomes case (1) in general only after `Y` is cut into the opens where the rank is constant. -/
/-- If `f : X ⟶ Y` is finite locally free of constant rank `d > 0` and `X` is quasi-affine, then
so is `Y`. -/
public theorem isQuasiAffine_of_isFiniteLocallyFreeOfRank (f : X ⟶ Y) (d : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d] (hd : 0 < d) [X.IsQuasiAffine] :
    Y.IsQuasiAffine :=
  have : IsFinite f :=
    ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation f).mp
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree f d)).1
  isQuasiAffine_of_morphismNorm f hd (finiteLocallyFreeNormOfRank f d hd).1

end Stacks.Divisors

end
