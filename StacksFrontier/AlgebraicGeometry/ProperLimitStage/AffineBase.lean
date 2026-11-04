module

public import StacksFrontier.AlgebraicGeometry.Limits.AffineNoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.ProperLimitStage.NoetherianChow

/-!
# Descending properness to a stage of the Noetherian approximation of an affine base

`StacksFrontier/AlgebraicGeometry/ProperLimitStage/NoetherianChow.lean` proves [Stacks, Tag
081F] — properness over the limit of a cofiltered system descends to a finite stage — with
Chow's lemma discharged, at the price of asking the stage base to be Noetherian. Its own
implementation note observes that this price is not paid when the limit presentation is the one
[Stacks, Tag 0EX4] uses, namely an arbitrary ring written as the filtered colimit of its
subalgebras of finite type over the integers: there every *stage* is Noetherian and only the
*limit* is not.

This file supplies that presentation and composes the two. The result is Tag 081F specialised to
the Noetherian approximation of `Spec R` for an arbitrary commutative ring `R`, with the
Noetherianity of the stage base no longer a hypothesis on the system but a consequence of how the
system is built.

## Main results

* `AlgebraicGeometry.exists_isProper_baseChange_specAdjoinFinsetDiagram`: a morphism over a stage
  of the Noetherian approximation of `Spec R` which becomes proper over `Spec R` is already
  proper over some later stage.

## Implementation notes

No Stacks attribute is attached. Tag 081F is stated for an arbitrary cofiltered system with
affine transitions over a quasi-compact quasi-separated base, and discharges Chow's lemma in the
quasi-compact quasi-separated case, [Stacks, Tag 0202]; the statement below is at one particular
system and still inherits `IsSeparated f₀.left` from the Noetherian case of Chow's lemma,
[Stacks, Tag 0200]. Both deviations are the ones `NoetherianChow.lean` already records.

What this does *not* do is produce the morphism `f₀` over a stage. That is the content of
[Stacks, Tag 09ZR] — the cofiltered presentation of a proper morphism — which is absent from this
repository, and it remains the step that separates [Stacks, Tag 0EX4]'s clause on top-degree
finiteness from its limit-descent proof. The contribution here is that every *other* hypothesis
of 081F is discharged for the affine presentation: the system's filteredness and smallness, the
affineness of its transitions, and the compactness, quasi-separation and Noetherianity of its
stages all hold by construction.

## References

* [Stacks Project, Tag 081F](https://stacks.math.columbia.edu/tag/081F)
* [Stacks Project, Tag 09ZR](https://stacks.math.columbia.edu/tag/09ZR)
* [Stacks Project, Tag 0EX4](https://stacks.math.columbia.edu/tag/0EX4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R]

/-- **Properness descends to a later stage of the Noetherian approximation of `Spec R`.** Let `R`
be a commutative ring, let `i₀` be a finite subset of `R` and let `f₀ : X₀ ⟶ Y₀` be a morphism of
schemes over `Spec ℤ[i₀]` which is separated and locally of finite type, with `Y₀` Noetherian.
If `f₀` becomes proper after base change to `Spec R`, then it is proper after base change to
`Spec ℤ[i]` for some finite `i ⊇ i₀`.

This is `AlgebraicGeometry.exists_isProper_baseChange_of_isLimit_of_isNoetherian`, [Stacks, Tag
081F] over a Noetherian stage, applied to `AlgebraicGeometry.isLimit_specAdjoinFinsetCone`. Every
hypothesis that theorem places on the *system* is discharged by the construction of the system:
`(Finset R)ᵒᵖ` is cofiltered and essentially small, the transition morphisms are affine
(`AlgebraicGeometry.isAffineHom_specAdjoinFinsetDiagram_map`), and the stages are Noetherian
(`AlgebraicGeometry.isNoetherian_specAdjoinFinsetDiagram_obj`) hence quasi-compact and
quasi-separated. The hypotheses that remain are the ones on `f₀` itself. -/
theorem exists_isProper_baseChange_specAdjoinFinsetDiagram
    (i₀ : (Finset R)ᵒᵖ) (X₀ Y₀ : Over ((specAdjoinFinsetDiagram R).obj i₀)) (f₀ : X₀ ⟶ Y₀)
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFiniteType f₀.left] [IsSeparated f₀.left] [IsNoetherian Y₀.left]
    [IsProper ((Over.pullback ((specAdjoinFinsetCone R).π.app i₀)).map f₀).left] :
    ∃ (i : (Finset R)ᵒᵖ) (hi : i ⟶ i₀),
      IsProper ((Over.pullback ((specAdjoinFinsetDiagram R).map hi)).map f₀).left :=
  exists_isProper_baseChange_of_isLimit_of_isNoetherian (specAdjoinFinsetDiagram R)
    (specAdjoinFinsetCone R) (isLimit_specAdjoinFinsetCone R) i₀ X₀ Y₀ f₀

end AlgebraicGeometry

end
