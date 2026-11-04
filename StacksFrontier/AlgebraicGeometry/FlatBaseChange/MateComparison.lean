module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Reduction
public import StacksFrontier.AlgebraicGeometry.FlatBaseChange.Pushforward

/-!
# The two canonical degree-zero base-change comparisons agree

For a commuting square `g' ≫ f = f' ≫ g` of schemes the library carries two constructions of
the canonical comparison `g^* f_* F ⟶ f'_* (g')^* F`:

* `Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans`, the mate of the
  identification of the two composite direct images around the square under the two
  pullback-pushforward adjunctions, which is the one whose locality on the base and reduction to
  an affine base are proved in `AffineBaseChangeIso/`, and for which [Stacks, Tag 02KG] is
  proved; and
* `Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange`, the adjoint transpose of the
  same identification precomposed with a unit, which is the one
  `TopDegreeBaseChange/StructureSheafSurjectivityBaseChange.lean` builds
  `directImageStructureSheafBaseChangeMap` on.

They are the same morphism: a mate *is* the adjoint transpose, read componentwise. This file
records that, so that the invertibility criteria proved for either one are available for the
other. In particular [Stacks, Tag 02KG] becomes a criterion for `pushforwardBaseChange`, which
otherwise has only the flat-base-change criterion
`Stacks.AlgebraicGeometry.FlatBaseChange.isIso_pushforwardBaseChange_of_isAffine`.

## Main results

* `Stacks.AlgebraicGeometry.FlatBaseChange.baseChangeNatTrans_app_eq_pushforwardBaseChange`:
  the two comparisons agree.
* `Stacks.AlgebraicGeometry.FlatBaseChange.isIso_pushforwardBaseChange_of_isAffineHom`:
  [Stacks, Tag 02KG] for `pushforwardBaseChange` — the comparison of a cartesian square whose
  right-hand morphism is affine is invertible at every quasi-coherent module.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 02N7](https://stacks.math.columbia.edu/tag/02N7)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.AlgebraicGeometry.FlatBaseChange

noncomputable section

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- **The mate form and the adjoint-transpose form of the degree-zero base-change comparison
agree.** Both are the inverse image along `g` of the direct image of a unit, followed by the
inverse image of the identification of the two composite direct images around the square,
followed by a counit; the first reads that off `CategoryTheory.mateEquiv` and the second off
`CategoryTheory.Adjunction.homEquiv`. -/
theorem baseChangeNatTrans_app_eq_pushforwardBaseChange (w : g' ≫ f = f' ≫ g) (F : X.Modules) :
    (AffinePushforward.baseChangeNatTrans w).app F = pushforwardBaseChange w F := by
  rw [pushforwardBaseChange, Adjunction.homEquiv_counit, pushforwardBaseChangeUnit]
  simp only [AffinePushforward.baseChangeNatTrans, mateEquiv, Functor.map_comp, Category.assoc]
  rfl

/-- **[Stacks, Tag 02KG] for `pushforwardBaseChange`.** The degree-zero base-change comparison
of a cartesian square whose right-hand morphism is affine is invertible at every quasi-coherent
module. This is
`Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom` read
through `baseChangeNatTrans_app_eq_pushforwardBaseChange`. -/
theorem isIso_pushforwardBaseChange_of_isAffineHom (hw : IsPullback g' f' f g) [IsAffineHom f]
    (F : X.Modules) [F.IsQuasicoherent] :
    IsIso (pushforwardBaseChange hw.w F) := by
  rw [← baseChangeNatTrans_app_eq_pushforwardBaseChange]
  exact AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom hw F

end

end Stacks.AlgebraicGeometry.FlatBaseChange

end
