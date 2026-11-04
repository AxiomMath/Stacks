module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.BaseChangeRelative
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecializationRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.WeightingRestriction
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.WeightingDvrCriterion

/-!
# The weighting attached to a relative zero-cycle, reduced to the case of a discrete valuation ring

Let `f : X ⟶ S` be locally quasi-finite with `S` locally Noetherian and let `α` be a relative
`0`-cycle on `X/S`. Then `w_α` is a weighting of `f`.

The weighting condition is checked after base change to the spectrum of a discrete valuation ring
on a finite open piece: there the base change `α'` of `α` is again a relative `0`-cycle, its
restriction `γ` to the piece is again one, and `w_γ` is the restriction of `w_α` pulled back,
so the first clause of Stacks Tag 0H5P over a discrete valuation ring applies. The piece is finite
over the base, hence quasi-compact, which is what makes the discrete-valuation-ring case available
without assuming `X` quasi-compact.

## Main results

* `Stacks.Chow.isWeighting_relativeCycleWeight_of_dvr_case` — the statement just made, with the
  two inputs it needs from elsewhere in the chapter taken as hypotheses: the base-change
  compatibility of `w_·` and the weighting property of `w_γ` over a discrete valuation ring.

## Implementation notes

The hypotheses `hbc` and `hdvr` are the preliminary lemma of the source
(`w_{g^*α} = w_α ∘ g'`, untagged upstream) and the first clause of the lemma over a discrete
valuation ring. Both are discharged where this result is consumed; nothing in the finished
development is conditional.

## References

* [Stacks Project, Tag 0H5P](https://stacks.math.columbia.edu/tag/0H5P)
* [Stacks Project, Tag 0H51](https://stacks.math.columbia.edu/tag/0H51)
* [Stacks Project, Tag 0F3B](https://stacks.math.columbia.edu/tag/0F3B)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- **Stacks Project, Tag 0H5P**, clause (1), reduced to the case of a discrete valuation ring:
the function `w_α` attached to a relative `0`-cycle on a locally quasi-finite morphism over a
locally Noetherian base is a weighting. -/
theorem isWeighting_relativeCycleWeight_of_dvr_case {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] [IsLocallyNoetherian S]
    (α : FamilyOfCycles f 0) (hα : IsRelativeCycle f 0 α)
    (hbc : ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      (c : Spec (.of R) ⟶ S),
      relativeCycleWeight (pullback.snd f c) (baseChangeFamily f c 0 α) =
        relativeCycleWeight f α ∘ pullback.fst f c)
    (hdvr : ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      {W : Scheme.{u}} (p : W ⟶ Spec (.of R)) [LocallyOfFiniteType p] [LocallyQuasiFinite p]
      [QuasiCompact p] (γ : FamilyOfCycles p 0), IsRelativeCycle p 0 γ →
      IsWeighting p (relativeCycleWeight p γ)) :
    IsWeighting f (relativeCycleWeight f α) := by
  refine isWeighting_of_forall_isFinite_over_isDiscreteValuationRing f _ ?_
  intro R _ _ _ c W ι hι hfinite
  have := hι
  have := hfinite
  set f' := pullback.snd f c with hf'
  set α' := baseChangeFamily f c 0 α with hα'def
  have hα'rel : IsRelativeCycle f' 0 α' := isRelativeCycle_baseChangeFamily f c 0 hα
  -- the restriction of `α'` to the finite open piece
  set γ : FamilyOfCycles (ι ≫ f') 0 :=
    (fun s ↦ fiberCycleRestrict f' (ι ≫ f') ι rfl s 0 (α' s)) with hγdef
  have hγrel : IsRelativeCycle (ι ≫ f') 0 γ :=
    isRelativeCycle_fiberCycleRestrict f' (ι ≫ f') ι rfl 0 hα'rel
  have hwγ : IsWeighting (ι ≫ f') (relativeCycleWeight (ι ≫ f') γ) :=
    hdvr R (ι ≫ f') γ hγrel
  have hfun : relativeCycleWeight (ι ≫ f') γ =
      relativeCycleWeight f α ∘ pullback.fst f c ∘ ι := by
    funext x
    rw [hγdef, relativeCycleWeight_fiberCycleRestrict f' ι α' x, hα'def,
      congrFun (hbc R c) (ι x)]
    rfl
  rwa [hfun] at hwγ

end Stacks.Chow

end
