module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneInstanceB

/-!
# The slot `hT` of the target square of clause (1) of Stacks 0D2Z

The target square of clause (1) of [Stacks, Tag 0D2Z] at a scheme point `w : W ⟶ U(ψ)`
(`AlgebraicGeometry.Space.comp_comp_eq_map_of_target_squares`) consumes the target
identification `…InvertibleTwistingRestriction.chartTargetIso` of the chart map and the `ψ` leg
`…InvertibleTwistingRestriction.clauseOnePsiLeg` as composites of their factors (its hypotheses
`hT` and `hb`).  Both are read off the defining equations, so that the factors are the
definitions' own (with the abstracted proofs of the stored bodies), never a re-elaboration of
the same text.

## Main results

* `…InvertibleTwistingRestriction.chartTargetIso_hom_eq`: `…chartTargetIso` as the composite of
  its three factors.

The slot `hb` (the `ψ` leg as the composite of its two factors) is
`…InvertibleTwistingRestriction.clauseOnePsiLeg_eq` in
`StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneTargetEquations`.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

universe v₁ u₁ u m

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective

namespace AlgebraicGeometry.Space

/-- The `.hom` of a composite of three isomorphisms is the composite of their `.hom`s: a
morphism equal to the first is equal to the second. -/
theorem hom_eq_comp_comp_of_eq_trans_hom {C : Type u₁} [Category.{v₁} C] {X Y Z V : C}
    {A : X ≅ Y} {B : Y ≅ Z} {D : Z ≅ V} {t : X ⟶ V} (h : t = (A ≪≫ B ≪≫ D).hom) :
    t = A.hom ≫ B.hom ≫ D.hom :=
  h

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

variable {s : RelativeProjSituation.{u, m}}
  {X : AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase} {f : X ⟶ s.shrink.space}
  {L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O)}
  [hL : Stacks.SheafOfModules.IsInvertible
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L]
  {ψ : SheafOfModules.GradedAlgebra.UnitalHom
    ((gradedPull (X := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X)
      (Y := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space)
      (smallEtaleRingedToposHom s.shrink.site s.shrink.base s.shrink.containsBase f)).obj
        s.shrink.algebra)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L)}
  {W : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase}
  (w : yoneda.obj W ⟶ (locusSpaceOfUnitalHom s f L ψ).obj) (d : ℤ)

/-- **The target identification of the chart map is the composite of its three factors**: the
inverse of `AlgebraicGeometry.Space.pointTargetIso`, the transport along
`pointHom_locusPoint`, and the inverse comparison of Stacks 03LU for `w` and `U(ψ) ⊆ X`, read off
the defining equation of `…InvertibleTwistingRestriction.chartTargetIso`: the hypothesis `hT` of
`AlgebraicGeometry.Space.comp_comp_eq_map_of_target_squares`. -/
theorem chartTargetIso_hom_eq :
    type_of% (hom_eq_comp_comp_of_eq_trans_hom
      (congrArg Iso.hom (chartTargetIso.eq_1 (s := s) (f := f) (L := L) (ψ := ψ) w d))) :=
  hom_eq_comp_comp_of_eq_trans_hom
    (congrArg Iso.hom (chartTargetIso.eq_1 (s := s) (f := f) (L := L) (ψ := ψ) w d))

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
