module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothLocalAtSource
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionSmoothBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
import all StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionSmoothBaseChange

/-!
# The reduction of the source of a smooth representable morphism: the refined forms

The base change of a reduction along a smooth morphism representable by algebraic spaces is a
reduction of the source, without assuming that the spaces involved are formal algebraic spaces.

## Main results

* `AlgebraicGeometry.FormalSpace.IsReduction.pullback_of_smooth`: if `Yred ⟶ Y` is a reduction
  and `f : X ⟶ Y` is smooth and representable by algebraic spaces, then the projection
  `X ×_Y Yred ⟶ X` is a reduction of `X`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Smoothness in a larger value universe -/

/-! ### Relative properties along the universe-lifted Yoneda embedding -/

/-! ### Stacks 0GB3 in a larger value universe -/

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Two reductions of one sheaf -/

/-! ### Stacks 0GB7 -/

/-- The base change of a reduction along a morphism which is representable by algebraic spaces
and smooth is a reduction of the source: if `iY : Yred ⟶ Y` is a reduction of `Y` and `P` with
projections `fst : P ⟶ X` and `snd : P ⟶ Yred` is a fibre product `X ×_Y Yred`, then `fst`
exhibits `P` as a reduction of `X`. This is
`AlgebraicGeometry.FormalSpace.isReduction_pullback_reduction_of_smooth` without the hypotheses
that `X` and `Y` be formal algebraic spaces. -/
theorem IsReduction.pullback_of_smooth {X Y Yred P : FppfSheaf B S hS}
    {f : X ⟶ Y} (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (hsmooth : Space.HasPropertyULift.{u + 1} B S hS
      (Space.smoothPropertyULift.{u + 1} B S hS) f.hom hf)
    {iY : Yred ⟶ Y} (hiY : IsReduction B S hS Y Yred iY)
    {fst : P ⟶ X} {snd : P ⟶ Yred} (sq : IsPullback fst snd f iY) :
    IsReduction B S hS X P fst := by
  have sqh : IsPullback fst.hom snd.hom f.hom iY.hom := isPullback_sheafHom B S hS sq
  have hPalg : Space.IsAlgebraicSpaceULift.{u + 1} B S hS P.obj :=
    Space.isAlgebraicSpaceULift_of_iso B S hS sqh.flip.isoPullback.symm
      (Space.isAlgebraicSpaceULift_pullback_of_isRepresentableULift B S hS f.hom iY.hom hf
        hiY.algebraic)
  have hthick : Space.IsRepresentableThickeningULift.{u + 1} B S hS fst.hom :=
    AlgebraicGeometry.Space.relative_of_isPullback B S hS sqh hiY.isRepresentableThickening
  have hsndProp := Space.hasPropertyULift_of_isPullback B S hS sqh hf hsmooth
  have hsndSmooth : Space.IsSmoothULift.{u + 1} B S hS snd.hom :=
    Space.holdsOnEveryEtaleChartULift_of_forall_pullback_fst B S hS
      (@AlgebraicGeometry.Smooth.{u} : MorphismProperty Scheme.{u})
      AlgebraicGeometry.Smooth.isEtaleLocalOnSourceAndTarget hPalg hiY.algebraic snd.hom
      (fun U ξ => hsndProp U ξ)
  refine { algebraic := hPalg
           reduced := Space.hasEtaleLocalPropertyULift_isReduced_of_isSmoothULift B S hS
             hPalg hiY.algebraic snd.hom hsndSmooth hiY.reduced
           representable := hthick.rep
           thickening := hthick.property
           universal := fun U hUalg hUred g => ?_ }
  obtain ⟨m, hm, hmuniq⟩ := hiY.universal U hUalg hUred (g ≫ f)
  refine ⟨sq.lift g m hm.symm, sq.lift_fst _ _ _, fun l hl => ?_⟩
  have hlsnd : l ≫ snd = m :=
    hmuniq _ (by beta_reduce at hl ⊢; rw [Category.assoc, ← sq.w, ← Category.assoc, hl])
  exact sq.hom_ext (by rw [hl, sq.lift_fst]) (by rw [hlsnd, sq.lift_snd])

end AlgebraicGeometry.FormalSpace

end
