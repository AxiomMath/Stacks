module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChangeFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFirstOrderThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleFlatTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Order

/-!
# Supplement to `ConormalModuleFirstOrderThickening`

The results of this module extend those of
`StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFirstOrderThickening`.
They use imports, universe variables or `open` declarations that the base module does not
have, and are kept in a module of their own so that its header is unchanged.

## Main results

* `eq_preimageSubspace_of_isPullback_subspaceInclusion`
* `isIso_conormalMap_firstOrderThickening_of_isPullback_of_isFlat`
-/

@[expose] public section

open CategoryTheory
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X' Y' : AlgebraicSpaces B S hS} (g : X' ⟶ Y') (Y : ClosedSubspaces B S hS Y'.1)

/-! ### Condition (1) read at an arbitrary cartesian square -/

/-- **A cartesian square of closed subspaces presents the upper one as an inverse image.**  Let
`X ⊆ X'` and `Y ⊆ Y'` be closed subspaces, `g : X' ⟶ Y'` a morphism of algebraic spaces and
`f : X ⟶ Y`.  If the square formed by the two inclusions, `g` and `f` is a fibre product square,
then `X` is the inverse image `g⁻¹(Y)` of [Stacks Project, Tag 083Q],
`AlgebraicGeometry.Space.preimageSubspace`.

One inclusion needs only that the square commutes: the inclusion of `X` followed by `g` factors
through the inclusion of `Y`, so its range lies in `Y` and `X` lies in the inverse image.  The
other is the lift through the fibre product of the canonical square
`AlgebraicGeometry.Space.conormalEtaleRestrictionSquare`, which exhibits the inclusion of
`g⁻¹(Y)` as factoring through the inclusion of `X`. -/
theorem eq_preimageSubspace_of_isPullback_subspaceInclusion (X : ClosedSubspaces B S hS X'.1)
    (f : (⟨X.1.toFunctor, X.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS))
    (sq : IsPullback (subspaceInclusion B S hS X' X) f g
      (subspaceInclusion B S hS Y' Y)) :
    X = preimageSubspace B S hS g Y := by
  refine Subtype.ext (le_antisymm ?_ ?_)
  · have hw : X.1.ι ≫ g.hom = f.hom ≫ Y.1.ι := congrArg (fun m => m.hom) sq.w
    have h1 : Subfunctor.range (X.1.ι ≫ g.hom) ≤ Y.1 := by
      rw [hw]
      exact (Subfunctor.range_comp_le f.hom Y.1.ι).trans (Subfunctor.range_ι Y.1).le
    refine (Subfunctor.range_ι X.1).symm.trans_le
      ((Subfunctor.image_le_iff (Subfunctor.range X.1.ι) g.hom Y.1).1 ?_)
    rw [← Subfunctor.range_comp]
    exact h1
  · have hl := sq.lift_fst (subspaceInclusion B S hS X' (preimageSubspace B S hS g Y))
      (preimageProjection B S hS g Y) (conormalEtaleRestrictionSquare B S hS g Y)
    have hl' : (sq.lift (subspaceInclusion B S hS X' (preimageSubspace B S hS g Y))
        (preimageProjection B S hS g Y)
        (conormalEtaleRestrictionSquare B S hS g Y)).hom ≫ X.1.ι =
        (Y.1.preimage g.hom).ι := congrArg (fun m => m.hom) hl
    calc (preimageSubspace B S hS g Y).1
        = Subfunctor.range (Y.1.preimage g.hom).ι := (Subfunctor.range_ι _).symm
      _ = Subfunctor.range (_ ≫ X.1.ι) := congrArg Subfunctor.range hl'.symm
      _ ≤ Subfunctor.range X.1.ι := Subfunctor.range_comp_le _ _
      _ = X.1 := Subfunctor.range_ι X.1

/-- **(1) ⟹ (2) of [Stacks Project, Tag 06BH].**  Let `(f, f') : (X ⊆ X') → (Y ⊆ Y')` be a
morphism of first-order thickenings of algebraic spaces whose square of ambient spaces is
cartesian, `X = Y ×_{Y'} X'`.  If `f'` is flat then the canonical map of conormal modules
`f^*𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` of [Stacks Project, Tag 04CP] is an isomorphism.

This is the implication at the shape in which the source states it, and it is stated with the
source's own two notions.  The second clause of condition (1) is the hypothesis `sq`, that the
square is cartesian, rather than the structural restriction carried by
`AlgebraicGeometry.Space.isIso_conormalMap_firstOrderThickening_of_isFlat`, in which the upper
closed subspace *is* the inverse image `g⁻¹(Y)` and the vertical morphism *is* the projection;
by `AlgebraicGeometry.Space.eq_preimageSubspace_of_isPullback_subspaceInclusion` a cartesian
square is of that shape, the upper subspace being forced to be `g⁻¹(Y)` and then the vertical
morphism forced too, the inclusion of `Y` being a monomorphism.  Flatness is the chartwise
flatness of [Stacks Project, Tag 03ML] part (1), `AlgebraicGeometry.Space.IsFlat`, which is what
the source's `f'` satisfies; it is carried to flatness of the induced morphism of small étale
ringed topoi by [Stacks Project, Tag 073C],
`AlgebraicGeometry.Space.isFlat_iff_smallEtaleRingedToposHom_isFlat`.

The two first-order thickening hypotheses are the setting of the tag rather than inputs to the
proof; the implementation notes of this file record the point. -/
theorem isIso_conormalMap_firstOrderThickening_of_isPullback_of_isFlat
    (X : ClosedSubspaces B S hS X'.1)
    (f : (⟨X.1.toFunctor, X.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS))
    (_hY : IsFirstOrderThickening B S hS Y' Y.1)
    (_hX : IsFirstOrderThickening B S hS X' X.1)
    (sq : IsPullback (subspaceInclusion B S hS X' X) f g
      (subspaceInclusion B S hS Y' Y))
    (hg : IsFlat B S hS g.hom) :
    IsIso (conormalMap B S hS X Y g f sq.w) := by
  obtain rfl : X = preimageSubspace B S hS g Y :=
    eq_preimageSubspace_of_isPullback_subspaceInclusion B S hS g Y X f sq
  obtain rfl : f = preimageProjection B S hS g Y := by
    have : Mono (subspaceInclusion B S hS Y' Y) := by
      apply (ObjectProperty.ι
        (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F)).mono_of_mono_map
      show Mono Y.1.ι
      infer_instance
    exact (cancel_mono (subspaceInclusion B S hS Y' Y)).1
      (sq.w.symm.trans (conormalEtaleRestrictionSquare B S hS g Y))
  exact isIso_conormalMap_firstOrderThickening_of_isFlat B S hS g Y _hY _hX
    ((isFlat_iff_smallEtaleRingedToposHom_isFlat B S hS g).1 hg)

end AlgebraicGeometry.Space

end
