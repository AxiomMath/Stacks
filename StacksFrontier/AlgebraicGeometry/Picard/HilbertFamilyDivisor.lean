module

public import StacksFrontier.AlgebraicGeometry.Picard.DivisorsOnSmoothCurves
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorOfPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Hilbert functor of a smooth relative curve parametrizes divisors

Let `X ⟶ S` be smooth of relative dimension one and let `T` be a scheme over `S`. A degree-`d`
Hilbert family in `X` over `T` is a closed subscheme of `X ×_S T` that is finite locally free of
degree `d` over `T`. Section 0B9C of the Stacks Project says that the degree-`d` Hilbert functor
`Hilb^d_{X/S}` then parametrizes relative effective Cartier divisors: its value at `T` is the set
of relative effective Cartier divisors `D ⊂ X ×_S T` over `T` which are finite locally free of
degree `d` over `T`, compatibly with base change. This file proves that identification as a
natural isomorphism of functors on schemes over `S`.

The content is one inclusion: a degree-`d` Hilbert family is a relative effective Cartier divisor.
Relative dimension one is stable under base change, so `X ×_S T ⟶ T` is again smooth of relative
dimension one, and a closed subscheme of a smooth relative curve that is finite locally free over
the base is a relative effective Cartier divisor (Tag 0B9D, implication (1) implies (2)). The
other inclusion holds by definition, and both maps preserve the ideal sheaf, so naturality is
definitional.

## Main definitions

* `Stacks.Hilbert.RelativeEffectiveCartierDivisorOfRank` — a relative effective Cartier divisor
  in `X ×_S T` over `T`, finite locally free of degree `d` over `T`.
* `Stacks.Hilbert.relativeEffectiveCartierDivisorFunctorOfRank` — the functor of such divisors,
  acting by base change; base change preserves them by Tag 056Q.

## Main results

* `Stacks.Hilbert.HilbertFamily.isRelativeEffectiveCartierDivisor` — a degree-`d` Hilbert family
  on a smooth relative curve is a relative effective Cartier divisor.
* `Stacks.Hilbert.hilbertFunctorOfRankIsoRelativeEffectiveCartierDivisorFunctorOfRank` —
  **Section 0B9C**: on a smooth relative curve, `Hilb^d_{X/S}` is isomorphic to the functor of
  degree-`d` relative effective Cartier divisors.

## Implementation notes

*The degree is part of the divisor functor.* A relative effective Cartier divisor carries no
degree of its own, and without properness of `X ⟶ S` it need not even be finite over the base
(Tag 0B9D: (2) implies (1) needs `X ⟶ S` proper; that implication is
`AlgebraicGeometry.isFiniteLocallyFree_iff_isRelativeEffectiveCartierDivisor_of_isProper`). So
the functor `Hilb^d_{X/S}` is identified with the functor of relative effective Cartier divisors
that are finite locally free of degree `d` over the base, which is how the section and the lemmas
following it (0B9E, 0B9F) use it.

## References

* [Stacks Project, Tag 0B9C](https://stacks.math.columbia.edu/tag/0B9C)
* [Stacks Project, Tag 0B9D](https://stacks.math.columbia.edu/tag/0B9D)
* [Stacks Project, Tag 056Q](https://stacks.math.columbia.edu/tag/056Q)
* [Stacks Project, Tag 062T](https://stacks.math.columbia.edu/tag/062T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Hilbert

/-- **Stacks Project, Section 0B9C, forward inclusion.** On a scheme smooth of relative dimension
one over `S`, a degree-`d` Hilbert family in `X` over `T` is a relative effective Cartier divisor
on `X ×_S T` over `T`.

Smoothness of relative dimension one is stable under base change, so `X ×_S T ⟶ T` is again
smooth of relative dimension one; the family is finite locally free of degree `d` over `T`,
hence finite locally free, and a finite locally free closed subscheme of a smooth relative curve
is a relative effective Cartier divisor. -/
@[stacks 0B9C "the forward inclusion of the section's identification: a degree-`d` Hilbert \
family on a smooth relative curve is a relative effective Cartier divisor.  The identification \
itself, as a natural isomorphism of functors, is \
`Stacks.Hilbert.hilbertFunctorOfRankIsoRelativeEffectiveCartierDivisorFunctorOfRank`"]
theorem HilbertFamily.isRelativeEffectiveCartierDivisor {S : Scheme.{u}} {X T : Over S}
    [SmoothOfRelativeDimension 1 X.hom] {d : ℕ} (Z : HilbertFamily X T d) :
    Stacks.Divisors.IsRelativeEffectiveCartierDivisor
      ((Over.pullback T.hom).obj X).hom Z.ideal :=
  have : SmoothOfRelativeDimension 1 ((Over.pullback T.hom).obj X).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback X.hom T.hom) inferInstance
  have := Z.isFiniteLocallyFreeOfRank
  have := Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
    (Z.ideal.subschemeι ≫ ((Over.pullback T.hom).obj X).hom) d
  isRelativeEffectiveCartierDivisor_of_isFiniteLocallyFree _ _

/-! ### The functor of degree-`d` relative effective Cartier divisors -/

/-- A degree-`d` relative effective Cartier divisor in `X` over `T`: a closed subscheme of
`X ×_S T` which is a relative effective Cartier divisor on `X ×_S T` over `T` (Tag 062T) and
which is finite locally free of degree `d` over `T`.

This is the set of which Section 0B9C says that, on a smooth relative curve, it is the value of
the Hilbert functor at `T`; the identification is
`Stacks.Hilbert.hilbertFunctorOfRankIsoRelativeEffectiveCartierDivisorFunctorOfRank`. -/
@[sga "4 XVII 6.3.8" "Values of Divⁿ_{X/S}"]
structure RelativeEffectiveCartierDivisorOfRank {S : Scheme.{u}} (X T : Over S) (d : ℕ) where
  /-- The ideal sheaf on `X ×_S T` cutting out the divisor. -/
  ideal : ((Over.pullback T.hom).obj X).left.IdealSheafData
  /-- The closed subscheme cut out by `ideal` is a relative effective Cartier divisor over `T`. -/
  isRelativeEffectiveCartierDivisor :
    Stacks.Divisors.IsRelativeEffectiveCartierDivisor ((Over.pullback T.hom).obj X).hom ideal
  /-- The closed subscheme cut out by `ideal` is finite locally free of degree `d` over `T`. -/
  isFiniteLocallyFreeOfRank :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (ideal.subschemeι ≫ ((Over.pullback T.hom).obj X).hom) d

/-- A degree-`d` relative effective Cartier divisor is determined by its ideal sheaf. -/
@[ext]
theorem RelativeEffectiveCartierDivisorOfRank.ext {S : Scheme.{u}} {X T : Over S} {d : ℕ}
    {D E : RelativeEffectiveCartierDivisorOfRank X T d} (h : D.ideal = E.ideal) : D = E := by
  obtain ⟨I, hI, hI'⟩ := D
  obtain ⟨J, hJ, hJ'⟩ := E
  subst h
  rfl

/-- **Base change of a degree-`d` relative effective Cartier divisor.** For a morphism
`g : T' ⟶ T` over `S`, the inverse image in `X ×_S T'` of a degree-`d` relative effective
Cartier divisor in `X ×_S T` is again one: it is an effective Cartier divisor by Tag 056Q, and
flatness and finite local freeness of degree `d` over the base are stable under base change. -/
@[ega "IV 21.15.9" "(D), special case", sga "4 XVII 6.3.8" "partial"]
def RelativeEffectiveCartierDivisorOfRank.baseChange {S : Scheme.{u}} (X : Over S)
    {T' T : Over S} {d : ℕ} (g : T' ⟶ T) (D : RelativeEffectiveCartierDivisorOfRank X T d) :
    RelativeEffectiveCartierDivisorOfRank X T' d where
  ideal := D.ideal.comap (familyBaseChangeMap X g)
  isRelativeEffectiveCartierDivisor :=
    have := D.isRelativeEffectiveCartierDivisor.2
    ⟨isEffectiveCartierDivisor_comap_of_isPullback _ _
        (isPullback_familyBaseChangeMap X g).flip D.ideal D.isRelativeEffectiveCartierDivisor.1,
      Flat.isStableUnderBaseChange.of_isPullback
        (isPullback_familyBaseChangeMap_subschemeι X g D.ideal)
        D.isRelativeEffectiveCartierDivisor.2⟩
  isFiniteLocallyFreeOfRank :=
    have := D.isFiniteLocallyFreeOfRank
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback
      (isPullback_familyBaseChangeMap_subschemeι X g D.ideal)

/-- The ideal sheaf of a base-changed divisor is the pullback of the original one. -/
theorem RelativeEffectiveCartierDivisorOfRank.baseChange_ideal {S : Scheme.{u}} (X : Over S)
    {T' T : Over S} {d : ℕ} (g : T' ⟶ T) (D : RelativeEffectiveCartierDivisorOfRank X T d) :
    (RelativeEffectiveCartierDivisorOfRank.baseChange X g D).ideal =
      D.ideal.comap (familyBaseChangeMap X g) :=
  rfl

/-- The functor of degree-`d` relative effective Cartier divisors of `X` over `S`: it sends an
`S`-scheme `T` to the closed subschemes of `X ×_S T` which are relative effective Cartier
divisors over `T`, finite locally free of degree `d` over `T`, and a morphism to the base change
of divisors. -/
@[ega "IV 21.15.9" "special case", sga "4 XVII 6.3.8"]
def relativeEffectiveCartierDivisorFunctorOfRank {S : Scheme.{u}} (X : Over S) (d : ℕ) :
    (Over S)ᵒᵖ ⥤ Type u where
  obj T := RelativeEffectiveCartierDivisorOfRank X T.unop d
  map g := ↾fun D ↦ RelativeEffectiveCartierDivisorOfRank.baseChange X g.unop D
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro D
    refine RelativeEffectiveCartierDivisorOfRank.ext ?_
    exact (RelativeEffectiveCartierDivisorOfRank.baseChange_ideal X _ D).trans
      (by rw [unop_id, familyBaseChangeMap_id, Scheme.IdealSheafData.comap_id]; rfl)
  map_comp g h := by
    apply ConcreteCategory.hom_ext
    intro D
    refine RelativeEffectiveCartierDivisorOfRank.ext ?_
    exact (RelativeEffectiveCartierDivisorOfRank.baseChange_ideal X _ D).trans
      (by rw [unop_comp, familyBaseChangeMap_comp, Scheme.IdealSheafData.comap_comp]; rfl)

/-- **Stacks Project, Section 0B9C.** For `X ⟶ S` smooth of relative dimension one, the
degree-`d` Hilbert functor `Hilb^d_{X/S}` is the functor of degree-`d` relative effective Cartier
divisors: for every `S`-scheme `T`, the closed subschemes of `X ×_S T` finite locally free of
degree `d` over `T` are exactly the relative effective Cartier divisors on `X ×_S T` over `T`
which are finite locally free of degree `d` over `T`, compatibly with base change in `T`.

Both directions send an ideal sheaf to itself. A Hilbert family is a relative effective Cartier
divisor by `Stacks.Hilbert.HilbertFamily.isRelativeEffectiveCartierDivisor` (Tag 0B9D,
(1) implies (2), on `X ×_S T ⟶ T`), and a divisor of degree `d` is in particular a Hilbert
family. -/
@[stacks 0B9C "the section's assertion that `Hilb^d_{X/S}` parametrizes relative effective \
Cartier divisors, read as a natural isomorphism of functors on schemes over `S` between \
`Hilb^d_{X/S}` and the functor sending `T` to the relative effective Cartier divisors \
`D ⊂ X_T` over `T` which are finite locally free of degree `d` over `T`.  This is the form in which the rest of the section uses \
it: 0B9E, 0B9F and the addition morphism on `Hilb^d` treat points of `Hilb^d` as divisors"]
def hilbertFunctorOfRankIsoRelativeEffectiveCartierDivisorFunctorOfRank {S : Scheme.{u}}
    (X : Over S) [SmoothOfRelativeDimension 1 X.hom] (d : ℕ) :
    hilbertFunctorOfRank X d ≅ relativeEffectiveCartierDivisorFunctorOfRank X d :=
  NatIso.ofComponents
    (fun _T ↦ Equiv.toIso
      { toFun := fun Z ↦
          { ideal := Z.ideal
            isRelativeEffectiveCartierDivisor := Z.isRelativeEffectiveCartierDivisor
            isFiniteLocallyFreeOfRank := Z.isFiniteLocallyFreeOfRank }
        invFun := fun D ↦
          { ideal := D.ideal
            isFiniteLocallyFreeOfRank := D.isFiniteLocallyFreeOfRank }
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl })
    (fun _ ↦ rfl)

/-- The isomorphism of Section 0B9C does not change the ideal sheaf of a family. -/
@[simp]
theorem hilbertFunctorOfRankIsoRelativeEffectiveCartierDivisorFunctorOfRank_hom_ideal
    {S : Scheme.{u}} (X : Over S) [SmoothOfRelativeDimension 1 X.hom] (d : ℕ) (T : (Over S)ᵒᵖ)
    (Z : (hilbertFunctorOfRank X d).obj T) :
    ((hilbertFunctorOfRankIsoRelativeEffectiveCartierDivisorFunctorOfRank X d).hom.app T Z).ideal =
      Z.ideal :=
  rfl

/-- The inverse of the isomorphism of Section 0B9C does not change the ideal sheaf of a
divisor. -/
@[simp]
theorem hilbertFunctorOfRankIsoRelativeEffectiveCartierDivisorFunctorOfRank_inv_ideal
    {S : Scheme.{u}} (X : Over S) [SmoothOfRelativeDimension 1 X.hom] (d : ℕ) (T : (Over S)ᵒᵖ)
    (D : (relativeEffectiveCartierDivisorFunctorOfRank X d).obj T) :
    ((hilbertFunctorOfRankIsoRelativeEffectiveCartierDivisorFunctorOfRank X d).inv.app T D).ideal =
      D.ideal :=
  rfl

end Stacks.Hilbert

end
