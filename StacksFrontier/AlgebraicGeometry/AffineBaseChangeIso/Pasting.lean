module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkMateComp
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.BaseChange

/-!
# Pasting of base-change morphisms for direct images of sheaves of modules

Two commutative squares of schemes sharing an edge paste to a commutative square
```
X'' --h'--> X' --g'--> X
|f''        |f'        |f
S'' --h-->  S' --g-->  S
```
and this file proves that the canonical base-change morphism of the outer square is the
pasting of the base-change morphisms of the two inner ones.  This is the compatibility without
which `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_baseChangeNatTrans_restrictSquare`,
which covers only a square whose lower horizontal morphism is an open immersion, cannot be
combined with anything.

## Main results

* `Stacks.AlgebraicGeometry.AffineBaseChangeIso.baseChangeNatTrans_paste`: the base-change
  morphism of the pasted square is the vertical composite of the two base-change morphisms,
  whiskered with the two comparisons `Scheme.Modules.pullbackComp`.
* `Stacks.AlgebraicGeometry.AffineBaseChangeIso.baseChangeNatTrans_comp_square_app`: the same
  statement evaluated at a module, which is the form every consumer uses.
* `Stacks.AlgebraicGeometry.AffineBaseChangeIso.pushforwardSquareIso_paste`: the same for the
  identification of composite direct images that the base-change morphism is the mate of.

## Route

The base-change morphism is the mate of `pushforwardSquareIso` under the two
pullback--pushforward adjunctions, so the statement is Mathlib's
`CategoryTheory.mateEquiv_hcomp` -- mates turn horizontal composition of squares of right
adjoints into vertical composition of squares of left adjoints -- once the adjunction
`Scheme.Modules.pullbackPushforwardAdjunction (h' ≫ g')` has been traded for the composite
adjunction, whose left and right adjoints are `Scheme.Modules.pullback g' ⋙ pullback h'` and
`pushforward h' ⋙ pushforward g'`.  That trade is `mateEquiv_conjugateEquiv_vcomp` and
`conjugateEquiv_mateEquiv_vcomp`, which replace a whiskering of a square by a whiskering of
its mate with the conjugate transformation; the conjugate in question is computed by Mathlib's
`Scheme.Modules.conjugateEquiv_pullbackComp_inv` and, in the other direction, by
`Stacks.ModuleSkyscraper.conjugateEquiv_pullbackComp_hom` below.

`pushforwardSquareIso_paste` is proved on sections: every component of
`Scheme.Modules.pushforwardComp` is an identity and every component of
`Scheme.Modules.pushforwardCongr` is a restriction map of the module along an equality of
opens, so both sides are the same single restriction map -- the two restriction maps are equal
because the category of opens of a scheme is a preorder, where `Subsingleton.elim` applies.

## What is not done

**No assertion of [Stacks, Tag 02KG] is proved here, and no project tag attribute is
attached.**  This file is a compatibility of the base-change morphism and says nothing about
when that morphism is invertible.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CategoryTheory.TwoSquare
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.AffineBaseChangeIso

section Conjugate

variable {X Y Z : Scheme.{u}}

end Conjugate

section Paste

variable {X'' X' X S'' S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
  {h' : X'' ⟶ X'} {f'' : X'' ⟶ S''} {h : S'' ⟶ S'}

/-- The composite of two commutative squares is a commutative square. -/
lemma comp_square (w : g' ≫ f = f' ≫ g) (w' : h' ≫ f' = f'' ≫ h) :
    (h' ≫ g') ≫ f = f'' ≫ h ≫ g := by
  rw [Category.assoc, w, ← Category.assoc, w', Category.assoc]

/-- The identification of the two composite direct images around the pasted square is the
horizontal composite of the identifications for the two squares, whiskered with the
comparisons of composite direct images. -/
lemma pushforwardSquareIso_paste (w : g' ≫ f = f' ≫ g) (w' : h' ≫ f' = f'' ≫ h) :
    TwoSquare.mk _ _ _ _
        (AffinePushforward.pushforwardSquareIso (comp_square w w')).hom =
      ((TwoSquare.mk _ _ _ _ (AffinePushforward.pushforwardSquareIso w').hom ≫ₕ
        TwoSquare.mk _ _ _ _ (AffinePushforward.pushforwardSquareIso w).hom).whiskerBottom
          (Scheme.Modules.pushforwardComp h g).hom).whiskerTop
        (Scheme.Modules.pushforwardComp h' g').inv := by
  ext M U : 2
  simp only [Functor.comp_obj, Scheme.Modules.pushforward_obj_obj, Scheme.Hom.comp_base,
    Opens.map_comp_obj, AffinePushforward.pushforwardSquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforwardComp_hom_app_app, Scheme.Modules.pushforwardCongr_hom_app_app,
    Scheme.Modules.pushforwardComp_inv_app_app, Category.comp_id, Category.id_comp,
    whiskerTop_app, whiskerBottom_app, hComp_app, Category.assoc,
    Scheme.Modules.pushforward_map_app, Scheme.Modules.pushforward_obj_presheaf_map,
    ← Functor.map_comp, ← op_comp]
  exact congrArg M.presheaf.map (congrArg Quiver.Hom.op (Subsingleton.elim _ _))

/-- The base-change morphism is the mate of `pushforwardSquareIso`, read in the direction that
computes the mate of the base-change morphism. -/
lemma mateEquiv_baseChangeNatTrans (w : g' ≫ f = f' ≫ g) :
    mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction g')
        (Scheme.Modules.pullbackPushforwardAdjunction g)
        (TwoSquare.mk _ _ _ _ (AffinePushforward.baseChangeNatTrans w)) =
      TwoSquare.mk _ _ _ _ (AffinePushforward.pushforwardSquareIso w).hom := by
  rw [AffinePushforward.baseChangeNatTrans_eq]
  exact (mateEquiv _ _).apply_symm_apply _

/-- **Pasting of base-change morphisms.**  The canonical base-change morphism of the square
obtained by pasting two commutative squares is the vertical composite of their base-change
morphisms, whiskered with the two comparisons of composite inverse images. -/
theorem baseChangeNatTrans_paste (w : g' ≫ f = f' ≫ g) (w' : h' ≫ f' = f'' ≫ h) :
    TwoSquare.mk _ _ _ _ (AffinePushforward.baseChangeNatTrans (comp_square w w')) =
      ((TwoSquare.mk _ _ _ _ (AffinePushforward.baseChangeNatTrans w) ≫ᵥ
          TwoSquare.mk _ _ _ _ (AffinePushforward.baseChangeNatTrans w')).whiskerRight
            (Scheme.Modules.pullbackComp h g).inv).whiskerLeft
        (Scheme.Modules.pullbackComp h' g').hom := by
  apply (mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction (h' ≫ g'))
    (Scheme.Modules.pullbackPushforwardAdjunction (h ≫ g))).injective
  rw [conjugateEquiv_mateEquiv_vcomp
        (Scheme.Modules.pullbackPushforwardAdjunction (h' ≫ g'))
        ((Scheme.Modules.pullbackPushforwardAdjunction g').comp
          (Scheme.Modules.pullbackPushforwardAdjunction h'))
        (Scheme.Modules.pullbackPushforwardAdjunction (h ≫ g)),
      mateEquiv_conjugateEquiv_vcomp
        ((Scheme.Modules.pullbackPushforwardAdjunction g').comp
          (Scheme.Modules.pullbackPushforwardAdjunction h'))
        ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
          (Scheme.Modules.pullbackPushforwardAdjunction h))
        (Scheme.Modules.pullbackPushforwardAdjunction (h ≫ g)),
      mateEquiv_hcomp, mateEquiv_baseChangeNatTrans, mateEquiv_baseChangeNatTrans,
      mateEquiv_baseChangeNatTrans, Scheme.Modules.conjugateEquiv_pullbackComp_inv,
      Stacks.ModuleSkyscraper.conjugateEquiv_pullbackComp_hom]
  exact pushforwardSquareIso_paste w w'

/-- The four factors of the base-change morphism of a pasted square at a module: two
comparisons of composite inverse images, which are invertible, and the two base-change
morphisms of the squares being pasted. -/
lemma baseChangeNatTrans_comp_square_app (w : g' ≫ f = f' ≫ g) (w' : h' ≫ f' = f'' ≫ h)
    (M : X.Modules) :
    (AffinePushforward.baseChangeNatTrans (comp_square w w')).app M =
      (Scheme.Modules.pullbackComp h g).inv.app ((Scheme.Modules.pushforward f).obj M) ≫
        (Scheme.Modules.pullback h).map ((AffinePushforward.baseChangeNatTrans w).app M) ≫
        (AffinePushforward.baseChangeNatTrans w').app ((Scheme.Modules.pullback g').obj M) ≫
        (Scheme.Modules.pushforward f'').map
          ((Scheme.Modules.pullbackComp h' g').hom.app M) := by
  have h₀ := congr_app (baseChangeNatTrans_paste w w') M
  simpa [TwoSquare.vComp, TwoSquare.whiskerLeft, TwoSquare.whiskerRight] using h₀

end Paste

end Stacks.AlgebraicGeometry.AffineBaseChangeIso

end
