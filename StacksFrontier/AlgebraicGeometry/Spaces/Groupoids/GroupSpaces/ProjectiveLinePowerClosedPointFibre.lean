module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.GeneralLinearTwoPowerContraction
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperOverFieldClosedPointFibre

/-!
# An infinite fibre over a closed point, at a finite power of the projective line

A morphism `g : (ℙ¹_k)^α ⟶ Z` to an algebraic space separated over `Spec k`, with `α` a finite
index type, whose fibres on points are not all finite has an infinite fibre over a *closed* point
of `|Z|`.

The power `(ℙ¹_k)^α` is reindexed by `Fin (Nat.card α)`
(`AlgebraicGeometry.Space.projectiveLinePowerReindexIso`), where it is represented by the object
`AlgebraicGeometry.Space.projectiveSpacePowerSiteObject` of the big fppf site, whose structure
morphism is the proper one of the `Nat.card α`-fold self-product of `ℙ¹_k` over `Spec k`.

## Main results

* `AlgebraicGeometry.Space.exists_isClosed_singleton_infinite_fibre_projectiveLinePower`: a
  morphism out of a finite power of the projective line whose fibres on points are not all finite
  has an infinite fibre over a closed point of the target.

## References

* [Stacks Project, Tag 07W4](https://stacks.math.columbia.edu/tag/07W4)
* [Stacks Project, Tag 0AEM](https://stacks.math.columbia.edu/tag/0AEM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (k : Type u) [Field k] (B : BigFppfSite.{u})
  (hk : B.Contains (Spec (CommRingCat.of k)))

/-- **A morphism out of a finite power of the projective line whose fibres on points are not
all finite has an infinite fibre over a closed point of the target.**  Let `α` be a finite
index type, let `Z` be an algebraic space over `Spec k` separated over `Spec k` by `z`, and let
`g : (ℙ¹_k)^α ⟶ Z` be such that not every fibre of `g` on points is finite. Then some closed
point of `|Z|` has an infinite fibre. -/
theorem exists_isClosed_singleton_infinite_fibre_projectiveLinePower
    (α : Type v) [Small.{u} α] [Finite α]
    {Z : (BigFppfOver B (Spec (CommRingCat.of k)) hk)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk Z)
    (z : Z ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hk))))
    (hsep : IsSeparated B (Spec (CommRingCat.of k)) hk z)
    (g : projectiveLinePower k B hk α ⟶ Z)
    (hnot : ¬ ∀ y : points B (Spec (CommRingCat.of k)) hk Z,
      {x : points B (Spec (CommRingCat.of k)) hk (projectiveLinePower k B hk α) |
        pointsMap B (Spec (CommRingCat.of k)) hk (projectiveLinePower k B hk α) g x =
          y}.Finite) :
    ∃ w : points B (Spec (CommRingCat.of k)) hk Z, IsClosed {w} ∧
      {x : points B (Spec (CommRingCat.of k)) hk (projectiveLinePower k B hk α) |
        pointsMap B (Spec (CommRingCat.of k)) hk (projectiveLinePower k B hk α) g x =
          w}.Infinite := by
  let e : projectiveLinePower k B hk α ≅
      yoneda.obj (projectiveSpacePowerSiteObject k B hk (Nat.card α)) :=
    projectiveLinePowerReindexIso k B hk (Finite.equivFin α) ≪≫
      (projectiveSpacePowerYonedaIso k B hk (Nat.card α)).symm
  exact exists_isClosed_singleton_infinite_fibre_of_not_forall_finite B k hk
    (projectiveSpacePowerSiteObject k B hk (Nat.card α))
    (isProper_projectiveSpacePowerOver k (Nat.card α))
    (isAlgebraicSpace_of_iso B (Spec (CommRingCat.of k)) hk e.symm
      (isAlgebraicSpace_yoneda B (Spec (CommRingCat.of k)) hk _))
    e hZ z hsep g hnot

end AlgebraicGeometry.Space

end
