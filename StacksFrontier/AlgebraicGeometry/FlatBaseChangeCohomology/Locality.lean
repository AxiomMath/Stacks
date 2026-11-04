module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.Pasting

/-!
# The base-change morphism for direct images is an isomorphism locally on the base

Let
```
X' --g'--> X
|f'        |f
S' --g-->  S
```
be a commutative square of schemes and let `ℱ` be a sheaf of modules on `X`.  Shrinking the
base to an open `V` of `S'` turns the square into the rectangle
```
f' ⁻¹ᵁ V --ι ≫ g'--> X
|f' ∣_ V             |f
    V    --ι ≫ g-->  S
```
and this file proves that the base-change morphism `g^* f_* ℱ ⟶ f'_* (g')^* ℱ` of the original
square is an isomorphism as soon as the base-change morphisms of those rectangles are, for `V`
ranging over an open covering of `S'`.

This is the `i = 0` case, for sheaves of modules, of the reduction to affine `S` and `S'` in the
proof of [Stacks, Tag 02KH] and of the base-change assertion of [Stacks, Tag 02KG]. It does not
use flatness of `g`, quasi-compactness or quasi-separatedness of `f`, or quasi-coherence of `ℱ`.

## Main results

* `Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_pullback_map_baseChangeNatTrans`:
  if the rectangle's base-change morphism is invertible at `ℱ`, so is the inverse image along
  `V.ι` of the square's base-change morphism at `ℱ`.
* `Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_isOpenCover`:
  the square's base-change morphism is invertible at `ℱ` once the rectangles' base-change
  morphisms are, over an open covering of `S'`.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.FlatBaseChangeCohomology

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'} {g : S' ⟶ S} {g' : X' ⟶ X}

/-- The rectangle obtained from a commutative square by shrinking the base to an open `V` of
`S'`: its lower-left morphism is `f' ∣_ V` and its two horizontal morphisms are composites with
the inclusions of `V` and of its preimage. -/
theorem pasteBase_restrictSquare (w : g' ≫ f = f' ≫ g) (V : S'.Opens) :
    ((f' ⁻¹ᵁ V).ι ≫ g') ≫ f = (f' ∣_ V) ≫ (V.ι ≫ g) :=
  pasteBase w (AffineBaseChange.restrictSquare f' V)

/-- If the base-change morphism of the rectangle obtained by shrinking the base to `V` is
invertible at `ℱ`, then so is the inverse image along `V.ι` of the base-change morphism of the
original square. -/
theorem isIso_pullback_map_baseChangeNatTrans (w : g' ≫ f = f' ≫ g) (V : S'.Opens)
    (M : X.Modules)
    (hw : IsIso ((AffinePushforward.baseChangeNatTrans (pasteBase_restrictSquare w V)).app M)) :
    IsIso ((Scheme.Modules.pullback V.ι).map
      ((AffinePushforward.baseChangeNatTrans w).app M)) := by
  have key := congrArg (fun t => TwoSquare.natTrans t |>.app M)
    (baseChangeSquare_pasteBase w (AffineBaseChange.restrictSquare f' V))
  simp only [TwoSquare.whiskerRight_app, TwoSquare.whiskerLeft_app,
    natTrans_baseChangeSquare] at key
  rw [key] at hw
  rw [isIso_comp_left_iff, isIso_comp_right_iff] at hw
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _
    (AffineBaseChange.isIso_baseChangeNatTrans_restrictSquare f' V _) hw

/-- Let `V` be an open covering of `S'`. If, for every member of the covering, the base-change
morphism of the rectangle obtained by shrinking the base to that member is invertible at `ℱ`, then
the base-change morphism of the square itself is invertible at `ℱ`. -/
theorem isIso_baseChangeNatTrans_of_isOpenCover (w : g' ≫ f = f' ≫ g) (M : X.Modules)
    {I : Type*} (V : I → S'.Opens) (hV : IsOpenCover V)
    (hloc : ∀ i, IsIso ((AffinePushforward.baseChangeNatTrans
      (pasteBase_restrictSquare w (V i))).app M)) :
    IsIso ((AffinePushforward.baseChangeNatTrans w).app M) := by
  refine AffineBaseChange.isIso_of_isIso_restrict _ V hV fun i => ?_
  have := isIso_pullback_map_baseChangeNatTrans w (V i) M (hloc i)
  have : IsIso ((Scheme.Modules.restrictFunctor (V i).ι).map
      ((AffinePushforward.baseChangeNatTrans w).app M) ≫
      (Scheme.Modules.restrictFunctorIsoPullback (V i).ι).hom.app _) := by
    rw [(Scheme.Modules.restrictFunctorIsoPullback (V i).ι).hom.naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((Scheme.Modules.restrictFunctorIsoPullback (V i).ι).hom.app _)

end Stacks.AlgebraicGeometry.FlatBaseChangeCohomology

end
