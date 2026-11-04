module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.NoDeformations.ComparisonFibreShrink
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.NoDeformations.DiagonalKernelStalk
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.NoDeformations.FibreSquareStalk
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.NoDeformations.SmoothDiagonalStalk
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.NoDeformations.StalkKoszulDescription

/-!
# Case II of Stacks 0G0R at a point of the diagonal

Let `k` be a field, `q : S ⟶ Spec k` of finite type, `s` a `k`-rational point of `S`, and
`g : Y ⟶ S` smooth and proper; write `X = Y_s ×_k S` for the constant family,
`p : X ×_S Y ⟶ S` for the projection and `i : Y_s ×_k Y_s ⟶ X ×_S Y` for the comparison morphism.
Let `K` be a perfect object of `D(𝒪_{X ×_S Y})` whose derived restriction along `i` is the
diagonal kernel of `Y_s ⟶ Spec k`.

This file runs Case II of [Stacks, Tag 0G0R] at a point `Δ(y)` of the diagonal: the local ring of
`X ×_S Y` at `i(Δ(y))` carries an ideal `I` with `K` locally `𝒪 ⧸ I` in degree zero, with `I`
restricting on the fibre to the ideal of the diagonal, and with the quotient flat over the local
ring of `S`.

## Main results

* `AlgebraicGeometry.exists_ideal_derivedStalk_iso_single_diagonal`: **the statement above.**

## Implementation notes

The four inputs are combined with no new mathematics:

* `AlgebraicGeometry.derivedPullbackStalkIso` computes the derived stalk at `Δ(y)` of `L i^*K` as
  derived extension of scalars of the derived stalk of `K` at `i(Δ(y))` along the stalk map of
  `i`;
* the hypothesis replaces `L i^*K` by the diagonal kernel, whose derived stalk at `Δ(y)` is
  computed by `AlgebraicGeometry.derivedStalkDiagonalKernelIsoSingle`;
* [Stacks, Tag 0FDP], in the form
  `AlgebraicGeometry.exists_isRegular_span_ker_stalkMap_diagonal_of_smooth`, presents the ideal
  of the diagonal in that local ring by a regular sequence;
* `AlgebraicGeometry.exists_ringEquiv_quotient_stalk_fibreSquare` identifies the local ring of
  `Y_s ×_k Y_s` with the closed fibre of the stalk map of `p`, compatibly with the stalk map of
  `i`, so that the stalk map of `i` *is* the closed-fibre quotient map read through that
  isomorphism — which is what lets
  `AlgebraicGeometry.exists_ideal_derivedStalk_iso_single_of_closedFibre_koszul` be applied.

The membership of the regular sequence in the image of the maximal ideal, which the deformation
situation requires, comes from `AlgebraicGeometry.mem_map_maximalIdeal_of_surjective`: the ideal
of the diagonal is contained in the maximal ideal, and the stalk map of a closed immersion is
surjective.

## References

* [Stacks Project, Tag 0G0R](https://stacks.math.columbia.edu/tag/0G0R)
* [Stacks Project, Tag 0G0N](https://stacks.math.columbia.edu/tag/0G0N)
* [Stacks Project, Tag 0FDP](https://stacks.math.columbia.edu/tag/0FDP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

variable {k : Type u} [Field k] {S Y : Scheme.{u}}
  (q : S ⟶ Spec (.of k)) (g : Y ⟶ S) (s : Spec (.of k) ⟶ S)
  [LocallyOfFiniteType q] [QuasiCompact q] [Smooth g] [IsProper g]

omit [QuasiCompact q] in
/-- **Case II of [Stacks, Tag 0G0R] at a point of the diagonal.** The derived stalk of `K` at
`i(Δ(y))` is a cyclic module `𝒪 ⧸ I` in degree zero; the ideal `I` maps onto the ideal of the
diagonal in the local ring of `Y_s ×_k Y_s` at `Δ(y)`; and the quotient is flat over the local
ring of `S`. -/
theorem exists_ideal_derivedStalk_iso_single_diagonal (hs : s ≫ q = 𝟙 _)
    (K : DerivedCategory (Limits.pullback (constantFamilyπ q g s) g).Modules)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := (Limits.pullback (constantFamilyπ q g s) g).toRingedSpace) K)
    (hdiag : Nonempty ((derivedPullback
        (fibreSquareToProductComparison q g s hs).toLRSHom.toShHom).obj K ≅
      diagonalKernel (fibreAtRationalPointπ g s)))
    (y : fibreAtRationalPoint g s) :
    ∃ I : Ideal ((Limits.pullback (constantFamilyπ q g s) g).presheaf.stalk
        (fibreSquareToProductComparison q g s hs
          ((Limits.pullback.diagonal (fibreAtRationalPointπ g s)) y))),
      Nonempty ((derivedStalkFunctor (fibreSquareToProductComparison q g s hs
            ((Limits.pullback.diagonal (fibreAtRationalPointπ g s)) y))).obj K ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u}
            ((Limits.pullback (constantFamilyπ q g s) g).presheaf.stalk
              (fibreSquareToProductComparison q g s hs
                ((Limits.pullback.diagonal (fibreAtRationalPointπ g s)) y)))) 0).obj
          (ModuleCat.of _ (_ ⧸ I))) ∧
      Ideal.map ((fibreSquareToProductComparison q g s hs).stalkMap
          ((Limits.pullback.diagonal (fibreAtRationalPointπ g s)) y)).hom I =
        RingHom.ker ((Limits.pullback.diagonal (fibreAtRationalPointπ g s)).stalkMap y).hom ∧
      RingHom.Flat ((Ideal.Quotient.mk I).comp
        ((constantFamilyProductToBase q g s).stalkMap
          (fibreSquareToProductComparison q g s hs
            ((Limits.pullback.diagonal (fibreAtRationalPointπ g s)) y))).hom) := by
  classical
  have hNS : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian q
  have hFN : IsLocallyNoetherian (fibreAtRationalPoint g s) :=
    LocallyOfFiniteType.isLocallyNoetherian (fibreAtRationalPointπ g s)
  have hflat : Flat (constantFamilyProductToBase q g s) := flat_constantFamilyProductToBase q g s
  have hci : IsClosedImmersion (fibreSquareToProductComparison q g s hs) :=
    isClosedImmersion_fibreSquareToProductComparison q g s hs
  -- the regular sequence cutting out the diagonal at `y`
  obtain ⟨r, fbar, hfbarreg, hfbarspan⟩ :=
    exists_isRegular_span_ker_stalkMap_diagonal_of_smooth (fibreAtRationalPointπ g s) y
  -- the closed-fibre identification at the point `Δ(y)`
  obtain ⟨E, hE⟩ := exists_ringEquiv_quotient_stalk_fibreSquare q g s hs
    ((Limits.pullback.diagonal (fibreAtRationalPointπ g s)) y)
  have hcomp : (E : _ →+* _).comp (Ideal.Quotient.mk
        (stalkMapFibreIdeal (constantFamilyProductToBase q g s)
          (fibreSquareToProductComparison q g s hs
            ((Limits.pullback.diagonal (fibreAtRationalPointπ g s)) y)))) =
      ((fibreSquareToProductComparison q g s hs).stalkMap
        ((Limits.pullback.diagonal (fibreAtRationalPointπ g s)) y)).hom :=
    RingHom.ext fun b => hE b
  -- the Koszul data on the closed fibre
  have hfib : Nonempty ((totalDerivedExtensionScalars.{u, u, u}
      ((E : _ →+* _).comp (Ideal.Quotient.mk
        (stalkMapFibreIdeal (constantFamilyProductToBase q g s)
          (fibreSquareToProductComparison q g s hs
            ((Limits.pullback.diagonal (fibreAtRationalPointπ g s)) y)))))).functor.obj
      ((derivedStalkFunctor (fibreSquareToProductComparison q g s hs
        ((Limits.pullback.diagonal (fibreAtRationalPointπ g s)) y))).obj K) ≅
    (DerivedCategory.singleFunctor (ModuleCat.{u}
        ((Limits.pullback (fibreAtRationalPointπ g s) (fibreAtRationalPointπ g s)).presheaf.stalk
          ((Limits.pullback.diagonal (fibreAtRationalPointπ g s)) y))) 0).obj
      (ModuleCat.of _ (_ ⧸ Ideal.span (Set.range fbar)))) := by
    obtain ⟨ediag⟩ := hdiag
    refine ⟨?_⟩
    refine eqToIso (congrArg (fun φ => (totalDerivedExtensionScalars.{u, u, u} φ).functor.obj
      ((derivedStalkFunctor (fibreSquareToProductComparison q g s hs
        ((Limits.pullback.diagonal (fibreAtRationalPointπ g s)) y))).obj K)) hcomp) ≪≫ ?_
    refine ((derivedPullbackStalkIso (fibreSquareToProductComparison q g s hs)
      ((Limits.pullback.diagonal (fibreAtRationalPointπ g s)) y)).app K).symm ≪≫ ?_
    refine (derivedStalkFunctor
      ((Limits.pullback.diagonal (fibreAtRationalPointπ g s)) y)).mapIso ediag ≪≫ ?_
    refine derivedStalkDiagonalKernelIsoSingle (fibreAtRationalPointπ g s) y ≪≫ ?_
    exact eqToIso (congrArg (fun J => (DerivedCategory.singleFunctor (ModuleCat.{u}
      ((Limits.pullback (fibreAtRationalPointπ g s) (fibreAtRationalPointπ g s)).presheaf.stalk
        ((Limits.pullback.diagonal (fibreAtRationalPointπ g s)) y))) 0).obj
      (ModuleCat.of _ (_ ⧸ J))) hfbarspan.symm)
  -- the regular sequence lies in the maximal ideal, hence in the image of the maximal ideal
  have hmem : ∀ j, fbar j ∈ Ideal.map ((E : _ →+* _).comp (Ideal.Quotient.mk
      (stalkMapFibreIdeal (constantFamilyProductToBase q g s)
        (fibreSquareToProductComparison q g s hs
          ((Limits.pullback.diagonal (fibreAtRationalPointπ g s)) y)))))
      (IsLocalRing.maximalIdeal ((Limits.pullback (constantFamilyπ q g s) g).presheaf.stalk
        (fibreSquareToProductComparison q g s hs
          ((Limits.pullback.diagonal (fibreAtRationalPointπ g s)) y)))) := by
    intro j
    rw [hcomp]
    refine mem_map_maximalIdeal_of_surjective _
      (SurjectiveOnStalks.stalkMap_surjective (fibreSquareToProductComparison q g s hs) _) _ ?_
    -- a member of the ideal of the diagonal is not a unit
    have hmemker : fbar j ∈
        RingHom.ker ((Limits.pullback.diagonal (fibreAtRationalPointπ g s)).stalkMap y).hom := by
      rw [← hfbarspan]
      exact Ideal.subset_span ⟨j, rfl⟩
    by_contra hnot
    have hu : IsUnit (fbar j) := by rwa [← IsLocalRing.notMem_maximalIdeal]
    have : (1 : (Limits.pullback (fibreAtRationalPointπ g s)
        (fibreAtRationalPointπ g s)).presheaf.stalk
          ((Limits.pullback.diagonal (fibreAtRationalPointπ g s)) y)) ∈
        RingHom.ker ((Limits.pullback.diagonal (fibreAtRationalPointπ g s)).stalkMap y).hom :=
      (RingHom.ker _).eq_top_iff_one.mp
        (Ideal.eq_top_of_isUnit_mem _ hmemker hu)
    rw [RingHom.mem_ker, map_one] at this
    exact one_ne_zero this
  obtain ⟨I, hIsingle, hImap, hIflat⟩ :=
    exists_ideal_derivedStalk_iso_single_of_closedFibre_koszul
      (constantFamilyProductToBase q g s) _ E fbar hfbarreg hmem K hK hfib
  refine ⟨I, hIsingle, ?_, hIflat⟩
  rw [← hcomp, hImap, hfbarspan]

end AlgebraicGeometry

end
