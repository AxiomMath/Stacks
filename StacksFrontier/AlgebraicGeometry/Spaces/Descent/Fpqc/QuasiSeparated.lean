module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcCoveringBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae

/-!
# The two comparisons behind fpqc locality of the separation axioms

Quasi-separatedness of a morphism of algebraic spaces over a scheme `S` (Stacks 03HL, part (3))
is local on the base for the fpqc topology of Stacks 03YH, which is **Stacks 041N**. This file
holds the two comparison statements that proof and its siblings at the other separation axioms
run on: the fibre-product reconciliation in the category of algebraic spaces, and the
identification of the relative diagonal object of a base change as a base change of the relative
diagonal object.

Stacks 041N itself is `AlgebraicGeometry.Space.isQuasiSeparated_isLocalAtTarget_fpqc` in
`StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedFpqcLocalAtTarget`, which this file imports,
and the property it is stated at is `AlgebraicGeometry.Space.quasiSeparatedProperty` there.

## Main results

* `AlgebraicGeometry.AlgebraicSpaces.hom_pullback_snd_iff`: a property of morphisms of presheaves
  which respects isomorphisms holds of the second projection of a fibre product taken in the
  category of algebraic spaces exactly when it holds of the second projection of the fibre product
  of presheaves.
* `Stacks.SeparationLocal.isPullback_diagonalObjMap`: the relative diagonal object of a base
  change is a base change of the relative diagonal object, the comparison being
  `Stacks.SeparationLocal.diagonalObjMap`.

## Implementation notes

The two sides of Mathlib's `CategoryTheory.MorphismProperty.IsLocalAtTarget` speak of
`CategoryTheory.Limits.pullback.snd` in the category of algebraic spaces, whereas the diagonal
comparison and the covering families are stated for the presheaf fibre product of Stacks 02X2.
`AlgebraicGeometry.AlgebraicSpaces.hom_pullback_snd_iff` is that comparison, made once and used
by every consumer; it subsumes
`AlgebraicGeometry.Space.quasiCompactMorphismProperty_pullback_snd_iff`, which is the same
statement at quasi-compactness.

## References

* [Stacks Project, Tag 03HL](https://stacks.math.columbia.edu/tag/03HL)
* [Stacks Project, Tag 03KL](https://stacks.math.columbia.edu/tag/03KL)
* [Stacks Project, Tag 03MR](https://stacks.math.columbia.edu/tag/03MR)
* [Stacks Project, Tag 03YH](https://stacks.math.columbia.edu/tag/03YH)
* [Stacks Project, Tag 041L](https://stacks.math.columbia.edu/tag/041L)
* [Stacks Project, Tag 041N](https://stacks.math.columbia.edu/tag/041N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace Stacks.SeparationLocal

open AlgebraicGeometry

variable {C : Type*} [Category* C] [HasPullbacks C]

/-- The relative diagonal *object* of a base change is a base change of the relative diagonal
object: for `f : X ⟶ Y` and `g : Z ⟶ Y`, the square exhibiting
`(X ×_Y Z) ×_Z (X ×_Y Z)` as `Z ×_Y (X ×_Y X)`, the two projections being the first projection
followed by the structure morphism and the comparison morphism
`Stacks.SeparationLocal.diagonalObjMap`. -/
theorem isPullback_diagonalObjMap {X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ Y) :
    IsPullback
      (pullback.fst (pullback.snd f g) (pullback.snd f g) ≫ pullback.snd f g)
      (diagonalObjMap f g) g (pullback.fst f f ≫ f) := by
  have hcomm : (pullback.fst (pullback.snd f g) (pullback.snd f g) ≫ pullback.snd f g) ≫ g =
      diagonalObjMap f g ≫ pullback.fst f f ≫ f := by
    rw [← Category.assoc, diagonalObjMap_fst, Category.assoc, Category.assoc,
      pullback.condition (f := f) (g := g)]
  -- A map into `(X ×_Y Z) ×_Z (X ×_Y Z)` is determined by its two legs to `Z` and `X ×_Y X`.
  have huniq : ∀ {W : C}
      (m m' : W ⟶ pullback (pullback.snd f g) (pullback.snd f g)),
      m ≫ pullback.fst (pullback.snd f g) (pullback.snd f g) ≫ pullback.snd f g =
        m' ≫ pullback.fst (pullback.snd f g) (pullback.snd f g) ≫ pullback.snd f g →
      m ≫ diagonalObjMap f g = m' ≫ diagonalObjMap f g → m = m' := by
    intro W m m' hbase hprod
    have hprodfst := congrArg (fun z ↦ z ≫ pullback.fst f f) hprod
    have hprodsnd := congrArg (fun z ↦ z ≫ pullback.snd f f) hprod
    simp only [Category.assoc, diagonalObjMap_fst, diagonalObjMap_snd] at hprodfst hprodsnd
    ext <;> simp_all [← pullback.condition (f := pullback.snd f g) (g := pullback.snd f g)]
  let lft (s : PullbackCone g (pullback.fst f f ≫ f)) :
      s.pt ⟶ pullback (pullback.snd f g) (pullback.snd f g) :=
    pullback.lift
      (pullback.lift (s.snd ≫ pullback.fst f f) s.fst
        (by simpa only [Category.assoc] using s.condition.symm))
      (pullback.lift (s.snd ≫ pullback.snd f f) s.fst
        (by rw [Category.assoc, ← pullback.condition (f := f) (g := f)]
            exact s.condition.symm))
      (by rw [pullback.lift_snd, pullback.lift_snd])
  have hfac₁ (s : PullbackCone g (pullback.fst f f ≫ f)) :
      lft s ≫ pullback.fst (pullback.snd f g) (pullback.snd f g) ≫ pullback.snd f g = s.fst := by
    rw [← Category.assoc, pullback.lift_fst, pullback.lift_snd]
  have hfac₂ (s : PullbackCone g (pullback.fst f f ≫ f)) : lft s ≫ diagonalObjMap f g = s.snd := by
    refine pullback.hom_ext ?_ ?_ <;> simp only [Category.assoc, diagonalObjMap_fst,
      diagonalObjMap_snd, lft, pullback.lift_fst_assoc, pullback.lift_snd_assoc, pullback.lift_fst]
  exact ⟨⟨hcomm⟩, ⟨PullbackCone.IsLimit.mk hcomm lft hfac₁ hfac₂ fun s m hm₁ hm₂ ↦
    huniq m _ (hm₁.trans (hfac₁ s).symm) (hm₂.trans (hfac₂ s).symm)⟩⟩

end Stacks.SeparationLocal

namespace AlgebraicGeometry.AlgebraicSpaces

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A property of morphisms of presheaves on the big fppf site of `S` which respects isomorphisms
holds of the second projection of a fibre product formed in the category of algebraic spaces over
`S` exactly when it holds of the second projection of the fibre product of presheaves: the two
are pullbacks of the same cospan of presheaves, so they differ by an isomorphism. -/
theorem hom_pullback_snd_iff (Q : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    [Q.RespectsIso] {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Z) (g : Y ⟶ Z) :
    Q (pullback.snd f g).hom ↔ Q (pullback.snd f.hom g.hom) := by
  have sq := isPullback_hom B S hS (IsPullback.of_hasPullback f g)
  have he : (sq.isoIsPullback _ _ (IsPullback.of_hasPullback f.hom g.hom)).hom ≫
      pullback.snd f.hom g.hom = (pullback.snd f g).hom :=
    sq.isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback f.hom g.hom)
  rw [← he, Q.cancel_left_of_respectsIso]

end AlgebraicGeometry.AlgebraicSpaces

end
