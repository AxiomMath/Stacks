module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AlmostBlowUp.PrincipalCenterHDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.AlmostBlowUpSheafCriterion
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.AlmostBlowUpSquareGluing

/-!
# Restricting a cartesian square of the big h site along a morphism into its base

Let `e : E ⟶ Z`, `d : E ⟶ X'` and `z : Z ⟶ X`, `b : X' ⟶ X` form a commutative square of the big h
site, and let `h : W ⟶ X` be a morphism into its base. The fibre products `W ×_X E`, `W ×_X Z` and
`W ×_X X'` of the site form the restricted square

`W ×_X E ⟶ W ×_X Z`, `W ×_X E ⟶ W ×_X X'`, `W ×_X Z ⟶ W`, `W ×_X X' ⟶ W`,

and if the original square is cartesian, so is the restricted one. This is the step of Interlude B
in the proof of Stacks 0EVF showing that the exceptional corner of an almost blowup square stays
cartesian after base change.

## Main definitions

* `AlgebraicGeometry.BigHOver.restrictExcToMod`: the map `W ×_X E ⟶ W ×_X X'`.
* `AlgebraicGeometry.BigHOver.restrictExcToCen`: the map `W ×_X E ⟶ W ×_X Z`.

## Main results

* `AlgebraicGeometry.BigHOver.isPullback_restrictExc`: the restriction of a cartesian square is
  cartesian.

## Implementation notes

The fibre products are the chosen ones of the site, and the statement is proved in the site rather
than for the underlying schemes, which avoids transporting a cartesian square along three
comparison isomorphisms.

## References

* [Stacks Project, Tag 0EVF](https://stacks.math.columbia.edu/tag/0EVF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

namespace BigHOver

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (F : (BigHOver B S hS)ᵒᵖ ⥤ Type v)

/-- The restriction of a square of the site to a morphism into its base, as the fibre product of
the exceptional corner, mapping to the restricted modification. -/
public def restrictExcToMod {X X' E W : BigHOver B S hS} (b : X' ⟶ X) (d : E ⟶ X')
    (h : W ⟶ X) : pullback h (d ≫ b) ⟶ pullback h b :=
  pullback.lift (pullback.fst h (d ≫ b)) (pullback.snd h (d ≫ b) ≫ d)
    (by rw [Category.assoc]; exact pullback.condition)

/-- The restriction of a square of the site to a morphism into its base, as the fibre product of
the exceptional corner, mapping to the restricted centre. -/
public def restrictExcToCen {X X' Z E W : BigHOver B S hS} (b : X' ⟶ X) (z : Z ⟶ X) (d : E ⟶ X')
    (e : E ⟶ Z) (hw : e ≫ z = d ≫ b) (h : W ⟶ X) :
    pullback h (d ≫ b) ⟶ pullback h z :=
  pullback.lift (pullback.fst h (d ≫ b)) (pullback.snd h (d ≫ b) ≫ e)
    (by rw [Category.assoc, hw]; exact pullback.condition)

/-- **The restriction of a cartesian square along a morphism into its base is cartesian.** For a
cartesian square `e ≫ z = d ≫ b` and `h : W ⟶ X`, the square formed by
`AlgebraicGeometry.BigHOver.restrictExcToCen`, `AlgebraicGeometry.BigHOver.restrictExcToMod` and
the first projections of `W ×_X Z` and `W ×_X X'` is cartesian. -/
public theorem isPullback_restrictExc {X X' Z E W : BigHOver B S hS} {b : X' ⟶ X} {z : Z ⟶ X}
    {d : E ⟶ X'} {e : E ⟶ Z} (hw : e ≫ z = d ≫ b) (hsq : IsPullback e d z b) (h : W ⟶ X) :
    IsPullback (restrictExcToCen B S hS b z d e hw h) (restrictExcToMod B S hS b d h)
      (pullback.fst h z) (pullback.fst h b) := by
  have hdfst : restrictExcToMod B S hS b d h ≫ pullback.fst h b = pullback.fst h (d ≫ b) :=
    pullback.lift_fst _ _ _
  have hdsnd : restrictExcToMod B S hS b d h ≫ pullback.snd h b =
      pullback.snd h (d ≫ b) ≫ d := pullback.lift_snd _ _ _
  have hefst : restrictExcToCen B S hS b z d e hw h ≫ pullback.fst h z =
      pullback.fst h (d ≫ b) := pullback.lift_fst _ _ _
  have hesnd : restrictExcToCen B S hS b z d e hw h ≫ pullback.snd h z =
      pullback.snd h (d ≫ b) ≫ e := pullback.lift_snd _ _ _
  have hUd : IsPullback (pullback.snd h (d ≫ b)) (restrictExcToMod B S hS b d h) d
      (pullback.snd h b) := by
    refine IsPullback.of_bot ?_ hdsnd.symm (IsPullback.of_hasPullback h b).flip
    rw [hdfst]
    exact (IsPullback.of_hasPullback h (d ≫ b)).flip
  refine IsPullback.of_right (h₁₂ := pullback.snd h z) ?_ ?_
    (IsPullback.of_hasPullback h z).flip
  · rw [hesnd, pullback.condition (f := h) (g := b)]
    exact hUd.paste_horiz hsq
  · rw [hefst, hdfst]

end BigHOver

end AlgebraicGeometry

end
