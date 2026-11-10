module

public import StacksFrontier.AlgebraicGeometry.AffineClosedUnion.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.SupportedDerivedPushforwardImage
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.NoDeformations.CaseIIDiagonalStalk
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.NoDeformations.CaseIOffSubscheme
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierStalk.Stalkwise
public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk
public import Mathlib.Topology.JacobsonSpace

/-!
# The subscheme of Stacks 0G0R cuts out the diagonal on the fibre

In the situation of [Stacks, Tag 0G0R] let `Z ⊆ X ×_S Y` be the scheme-theoretic support of
`H^0(K)` and let `i : Y_s ×_k Y_s ⟶ X ×_S Y` be the comparison morphism. This file proves that the
inverse image of the ideal sheaf of `Z` along `i` is the ideal sheaf of the diagonal — that is,
`Z ∩ (X ×_S Y)_s = Δ_{Y_s/k}(Y_s)` as closed subschemes of `Y_s ×_k Y_s`.

That is the conclusion the source reaches by gluing its local pieces `Z(z)`: `Z_s` is the
diagonal. Here it is checked stalk by stalk. On the diagonal the stalk is computed by Case II
(`AlgebraicGeometry.exists_ideal_derivedStalk_iso_single_diagonal`); off it, both ideals are the
unit ideal, which for `Z` is Case I.

Case I is available at *closed* points only — the skyscraper whose vanishing it uses is supported
on the closure of its point — and the comparison has to be made at every point. The passage is
the Jacobson property of `Y_s ×_k Y_s`, a scheme of finite type over a field: a nonempty locally
closed subset of a Jacobson space contains a closed point of the space, so a closed subset
containing no closed point off the diagonal is contained in the diagonal.

## Main results

* `AlgebraicGeometry.cohomologySupportedOn_derivedPullback_diagonal`: the cohomology of `L i^*K`
  is supported on the diagonal.
* `AlgebraicGeometry.notMem_support_cohomologySupportIdeal_of_notMem_range_diagonal`: a point of
  `Y_s ×_k Y_s` off the diagonal has image off `Z` — at every point, not only at closed ones.
* `AlgebraicGeometry.comap_cohomologySupportIdeal_eq_ker_diagonal`: **the identification of ideal
  sheaves.**

## Implementation notes

The support of an ideal sheaf is a `TopologicalSpace.Closeds`, so the set `i⁻¹(Z)` is closed and
its difference with the (closed) image of the diagonal is locally closed, which is what
`nonempty_inter_closedPoints` consumes.

Off the diagonal the stalk of the inverse-image ideal sheaf is the image of the unit ideal under
the stalk map, and `Ideal.map_top` makes that the unit ideal with no surjectivity needed; the
stalk of the ideal sheaf of the diagonal is the unit ideal because the support of the kernel of a
closed immersion is its range (`Stacks.AffineClosedUnion.support_ker_eq_range`).

## References

* [Stacks Project, Tag 0G0R](https://stacks.math.columbia.edu/tag/0G0R)
* [Stacks Project, Tag 0G03](https://stacks.math.columbia.edu/tag/0G03)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

variable {k : Type u} [Field k] {S Y : Scheme.{u}}
  (q : S ⟶ Spec (.of k)) (g : Y ⟶ S) (s : Spec (.of k) ⟶ S)
  [LocallyOfFiniteType q] [QuasiCompact q] [Smooth g] [IsProper g]

omit [LocallyOfFiniteType q] [QuasiCompact q] [Smooth g] in
/-- **The cohomology of `L i^*K` is supported on the diagonal.** This is the hypothesis of
[Stacks, Tag 0G0R] read through [Stacks, Tag 0CSJ]: the derived restriction is the diagonal
kernel, whose cohomology is supported on the image of the diagonal. -/
theorem cohomologySupportedOn_derivedPullback_diagonal (hs : s ≫ q = 𝟙 _)
    (K : DerivedCategory (Limits.pullback (constantFamilyπ q g s) g).Modules)
    (hdiag : Nonempty ((derivedPullback
        (fibreSquareToProductComparison q g s hs).toLRSHom.toShHom).obj K ≅
      diagonalKernel (fibreAtRationalPointπ g s))) :
    CohomologySupportedOn (fibreAtRationalPointSelfProduct g s).ringCatSheaf
      (Set.range (Limits.pullback.diagonal (fibreAtRationalPointπ g s)).base)
      ((derivedPullback (fibreSquareToProductComparison q g s hs).toLRSHom.toShHom).obj K) := by
  obtain ⟨e⟩ := hdiag
  exact Stacks.Cohomology.PushforwardRestriction.cohomologySupportedOn_of_iso _ _ e.symm
    (cohomologySupportedOn_diagonalKernel (fibreAtRationalPointπ g s))

/-- **Case I of [Stacks, Tag 0G0R] at every point off the diagonal.** A point of `Y_s ×_k Y_s`
that does not lie on the diagonal has image off the scheme-theoretic support of `H^0(K)`.

For a closed point this is `AlgebraicGeometry.notMem_support_cohomologySupportIdeal_caseI`; the
general case follows because the set of points off the diagonal whose image lies on the support is
locally closed, and `Y_s ×_k Y_s` is Jacobson, so a nonempty such set would contain a closed
point. -/
theorem notMem_support_cohomologySupportIdeal_of_notMem_range_diagonal (hs : s ≫ q = 𝟙 _)
    (K : DerivedCategory (Limits.pullback (constantFamilyπ q g s) g).Modules)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := (Limits.pullback (constantFamilyπ q g s) g).toRingedSpace) K)
    (hdiag : Nonempty ((derivedPullback
        (fibreSquareToProductComparison q g s hs).toLRSHom.toShHom).obj K ≅
      diagonalKernel (fibreAtRationalPointπ g s)))
    (w : fibreAtRationalPointSelfProduct g s)
    (hw : w ∉ Set.range (Limits.pullback.diagonal (fibreAtRationalPointπ g s)).base) :
    (fibreSquareToProductComparison q g s hs) w ∉ (cohomologySupportIdeal K hK).support := by
  have hci : IsClosedImmersion (fibreSquareToProductComparison q g s hs) :=
    isClosedImmersion_fibreSquareToProductComparison q g s hs
  have hNoeth : IsNoetherian (Limits.pullback (constantFamilyπ q g s) g) :=
    isNoetherian_fibreProduct q g s
  have hT := cohomologySupportedOn_derivedPullback_diagonal q g s hs K hdiag
  have hJ : JacobsonSpace ↥(fibreAtRationalPointSelfProduct g s) :=
    LocallyOfFiniteType.jacobsonSpace
      (Limits.pullback.snd (fibreAtRationalPointπ g s) (fibreAtRationalPointπ g s) ≫
        fibreAtRationalPointπ g s)
  intro hmem
  set V : Set ↥(fibreAtRationalPointSelfProduct g s) :=
    (fibreSquareToProductComparison q g s hs).base ⁻¹'
        ((cohomologySupportIdeal K hK).support : Set _) \
      Set.range (Limits.pullback.diagonal (fibreAtRationalPointπ g s)).base with hV
  have hCclosed : IsClosed ((fibreSquareToProductComparison q g s hs).base ⁻¹'
      ((cohomologySupportIdeal K hK).support : Set _)) :=
    (cohomologySupportIdeal K hK).support.isClosed'.preimage
      (fibreSquareToProductComparison q g s hs).continuous
  have hDclosed : IsClosed
      (Set.range (Limits.pullback.diagonal (fibreAtRationalPointπ g s)).base) :=
    (Limits.pullback.diagonal
      (fibreAtRationalPointπ g s)).isClosedEmbedding.isClosed_range
  have hlc : IsLocallyClosed V := by
    rw [hV, Set.sdiff_eq]
    exact hCclosed.isLocallyClosed.inter hDclosed.isOpen_compl.isLocallyClosed
  have hne : V.Nonempty := ⟨w, hmem, hw⟩
  obtain ⟨w', ⟨hw'C, hw'D⟩, hw'cp⟩ := nonempty_inter_closedPoints hne hlc
  exact notMem_support_cohomologySupportIdeal_caseI (fibreSquareToProductComparison q g s hs)
    w' (mem_closedPoints_iff.mp hw'cp) _ hw'D K hK hT hw'C

/-- **The subscheme of [Stacks, Tag 0G0R] cuts out the diagonal on the fibre.** The inverse image
along `i` of the ideal sheaf of the scheme-theoretic support of `H^0(K)` is the ideal sheaf of the
diagonal of `Y_s ⟶ Spec k`. -/
theorem comap_cohomologySupportIdeal_eq_ker_diagonal (hs : s ≫ q = 𝟙 _)
    (K : DerivedCategory (Limits.pullback (constantFamilyπ q g s) g).Modules)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := (Limits.pullback (constantFamilyπ q g s) g).toRingedSpace) K)
    (hdiag : Nonempty ((derivedPullback
        (fibreSquareToProductComparison q g s hs).toLRSHom.toShHom).obj K ≅
      diagonalKernel (fibreAtRationalPointπ g s))) :
    (cohomologySupportIdeal K hK).comap (fibreSquareToProductComparison q g s hs) =
      (Limits.pullback.diagonal (fibreAtRationalPointπ g s)).ker := by
  have hci : IsClosedImmersion (fibreSquareToProductComparison q g s hs) :=
    isClosedImmersion_fibreSquareToProductComparison q g s hs
  refine IdealSheafData.eq_of_stalk_eq _ _ fun w => ?_
  rw [IdealSheafData.stalk_comap]
  by_cases hw : w ∈ Set.range (Limits.pullback.diagonal (fibreAtRationalPointπ g s)).base
  · obtain ⟨y, rfl⟩ := hw
    obtain ⟨I, ⟨eI⟩, hImap, -⟩ :=
      exists_ideal_derivedStalk_iso_single_diagonal q g s hs K hK hdiag y
    rw [stalk_cohomologySupportIdeal_of_derivedStalk_iso_single K hK _ I eI, hImap,
      IdealSheafData.stalk_ker_of_isClosedImmersion
        (Limits.pullback.diagonal (fibreAtRationalPointπ g s)) y]
  · have h₁ : IdealSheafData.stalk (cohomologySupportIdeal K hK)
        (fibreSquareToProductComparison q g s hs w) = ⊤ :=
      (Stacks.Divisors.stalk_eq_top_iff_notMem_support _ _).mpr
        (notMem_support_cohomologySupportIdeal_of_notMem_range_diagonal q g s hs K hK hdiag w hw)
    have h₂ : IdealSheafData.stalk
        (Limits.pullback.diagonal (fibreAtRationalPointπ g s)).ker w = ⊤ := by
      refine (Stacks.Divisors.stalk_eq_top_iff_notMem_support _ _).mpr fun hmem => hw ?_
      rw [← Stacks.AffineClosedUnion.support_ker_eq_range
        (Limits.pullback.diagonal (fibreAtRationalPointπ g s))]
      exact hmem
    rw [h₁, h₂, Ideal.map_top]

end AlgebraicGeometry

end
