module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkMateComp
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.BaseChange

/-!
# Pasting two base-change squares along the base

Two commutative squares of schemes which share an edge
```
X'' --a'--> X' --b'--> X
|f''        |f'        |f
S'' --a-->  S'  --b--> S
```
paste to a single commutative square with top `a' ≫ b'` and bottom `a ≫ b`.  This file proves
that the base-change morphism of the pasted square is, up to the canonical comparisons of
`AlgebraicGeometry.Scheme.Modules.pullback` and
`AlgebraicGeometry.Scheme.Modules.pushforward` with composition, the composite of the
base-change morphisms of the two pieces.  Consequently the pasted base-change morphism is
invertible as soon as both pieces are, and conversely a piece is invertible once the pasted
morphism and the other piece are.

This is the formal engine of the locality step of the base-change assertion of Stacks Tag
02KG: pasting the given cartesian square with the restriction square of a morphism over an
open of its target is what lets one replace the square by a square of affine schemes.

## Main results

* `Stacks.AlgebraicGeometry.AffineBaseChangeLocality.pushforwardSquareIso_hom_vcomp`: the
  identification of the two composite direct images around the pasted square is the
  horizontal composite of the identifications of the two pieces.
* `Stacks.AlgebraicGeometry.AffineBaseChangeLocality.baseChangeNatTrans_vcomp` and
  `Stacks.AlgebraicGeometry.AffineBaseChangeLocality.baseChangeNatTrans_vcomp_app`: the
  base-change morphism of the pasted square, as a 2-cell and in components.
* `Stacks.AlgebraicGeometry.AffineBaseChangeLocality.isIso_baseChangeNatTrans_vcomp` and
  `Stacks.AlgebraicGeometry.AffineBaseChangeLocality.isIso_map_baseChangeNatTrans_of_vcomp`:
  the two resulting transfers of invertibility.
* `Stacks.AlgebraicGeometry.AffineBaseChangeLocality.isIso_baseChangeNatTrans_congr`:
  invertibility of a base-change morphism only depends on the two horizontal morphisms of the
  square, not on the chosen proof that the square commutes.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules.pushforwardComp` has identity components and
`AlgebraicGeometry.Scheme.Modules.pushforwardCongr` has the restriction maps of the presheaf
along an equality of opens as components, so `pushforwardSquareIso_hom_vcomp` holds for the
trivial reason that both sides are the restriction map of one and the same inclusion of
opens; the opens of a scheme form a partial order, so there is nothing to check beyond
composing the restriction maps.

`baseChangeNatTrans_vcomp` is then pure mate calculus.  The base-change morphism is the mate
of `pushforwardSquareIso` under the pullback--pushforward adjunctions, and Mathlib's
`CategoryTheory.mateEquiv_hcomp` computes the mate of a horizontal composite -- but with
respect to the *composite* adjunction `pullback b' ⋙ pullback a' ⊣ pushforward a' ⋙
pushforward b'` rather than the adjunction of the composed morphism.  The two are compared by
`CategoryTheory.conjugateEquiv_mateEquiv_vcomp` and
`CategoryTheory.mateEquiv_conjugateEquiv_vcomp`, whose correction terms are the conjugates of
`AlgebraicGeometry.Scheme.Modules.pullbackComp`; those conjugates are
`AlgebraicGeometry.Scheme.Modules.pushforwardComp` by
`AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackComp_inv` and by
`Stacks.ModuleSkyscraper.conjugateEquiv_pullbackComp_hom` below.

`isIso_baseChangeNatTrans_congr` is proved by substituting the two equalities of morphisms;
the two commutation proofs are then proofs of the same proposition, hence equal.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.TwoSquare CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.AffineBaseChangeLocality

open Scheme.Modules (pullbackPushforwardAdjunction pullbackComp pushforwardComp)

variable {X'' X' X S'' S' S : Scheme.{u}} {a' : X'' ⟶ X'} {b' : X' ⟶ X} {f'' : X'' ⟶ S''}
  {f' : X' ⟶ S'} {f : X ⟶ S} {a : S'' ⟶ S'} {b : S' ⟶ S}

/-- The identification of the two composite direct images around a pasted square is the
horizontal composite of the identifications of the two pieces, whiskered with the comparisons
of the direct image with composition. -/
theorem pushforwardSquareIso_hom_vcomp (wa : a' ≫ f' = f'' ≫ a) (wb : b' ≫ f = f' ≫ b)
    (wab : (a' ≫ b') ≫ f = f'' ≫ (a ≫ b)) :
    (AffinePushforward.pushforwardSquareIso wab).hom =
      (((AffinePushforward.pushforwardSquareIso wa).hom ≫ₕ
            (AffinePushforward.pushforwardSquareIso wb).hom).whiskerTop
          (pushforwardComp a' b').inv).whiskerBottom (pushforwardComp a b).hom := by
  ext M U : 3
  simp only [AffinePushforward.pushforwardSquareIso, TwoSquare.hComp, Functor.comp_obj,
    Scheme.Modules.pushforward_obj_obj, Scheme.Hom.comp_base, Opens.map_comp_obj,
    whiskerBottom_app, whiskerTop_app, Category.assoc, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforward_map_app, Scheme.Modules.pushforward_obj_presheaf_map,
    Scheme.Modules.pushforwardComp_inv_app_app,
    Scheme.Modules.pushforwardComp_hom_app_app, Scheme.Modules.pushforwardCongr_hom_app_app,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.id_comp, Category.comp_id]
  rw [← Functor.map_comp]
  congr 1

/-- The conjugate, with respect to the adjunction of a composition and the composite of the
two adjunctions, of the comparison of inverse images with composition is the comparison of
direct images with composition.  This is the companion of Mathlib's
`AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackComp_inv`, in the other direction. -/
theorem Stacks.ModuleSkyscraper.conjugateEquiv_pullbackComp_hom {Y Z T : Scheme.{u}} (p : Y ⟶ Z)
  (q : Z ⟶ T) :
    conjugateEquiv (pullbackPushforwardAdjunction (p ≫ q))
        ((pullbackPushforwardAdjunction q).comp (pullbackPushforwardAdjunction p))
        (pullbackComp p q).hom = (pushforwardComp p q).inv := by
  have h := conjugateEquiv_comm
    ((pullbackPushforwardAdjunction q).comp (pullbackPushforwardAdjunction p))
    (pullbackPushforwardAdjunction (p ≫ q)) (α := (pullbackComp p q).inv)
    (β := (pullbackComp p q).hom) (by simp)
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  exact (Iso.hom_comp_eq_id _).mp h

/-- The base-change morphism of a pasted square is the vertical composite of the base-change
morphisms of the two pieces, whiskered with the comparisons of the inverse image with
composition. -/
theorem baseChangeNatTrans_vcomp (wa : a' ≫ f' = f'' ≫ a) (wb : b' ≫ f = f' ≫ b)
    (wab : (a' ≫ b') ≫ f = f'' ≫ (a ≫ b)) :
    AffinePushforward.baseChangeNatTrans wab =
      ((TwoSquare.mk _ _ _ _ (AffinePushforward.baseChangeNatTrans wb) ≫ᵥ
          TwoSquare.mk _ _ _ _ (AffinePushforward.baseChangeNatTrans wa)).whiskerLeft
            (pullbackComp a' b').hom).whiskerRight (pullbackComp a b).inv := by
  have ha : (mateEquiv (pullbackPushforwardAdjunction a') (pullbackPushforwardAdjunction a))
      (TwoSquare.mk _ _ _ _ (AffinePushforward.baseChangeNatTrans wa)) =
      TwoSquare.mk _ _ _ _ (AffinePushforward.pushforwardSquareIso wa).hom :=
    (mateEquiv _ _).apply_symm_apply _
  have hb : (mateEquiv (pullbackPushforwardAdjunction b') (pullbackPushforwardAdjunction b))
      (TwoSquare.mk _ _ _ _ (AffinePushforward.baseChangeNatTrans wb)) =
      TwoSquare.mk _ _ _ _ (AffinePushforward.pushforwardSquareIso wb).hom :=
    (mateEquiv _ _).apply_symm_apply _
  have h1 : (mateEquiv (pullbackPushforwardAdjunction (a' ≫ b'))
        (pullbackPushforwardAdjunction (a ≫ b)))
      (((TwoSquare.mk _ _ _ _ (AffinePushforward.baseChangeNatTrans wb) ≫ᵥ
          TwoSquare.mk _ _ _ _ (AffinePushforward.baseChangeNatTrans wa)).whiskerLeft
            (pullbackComp a' b').hom).whiskerRight (pullbackComp a b).inv) =
      TwoSquare.mk _ _ _ _ (AffinePushforward.pushforwardSquareIso wab).hom := by
    rw [mateEquiv_conjugateEquiv_vcomp _
        ((pullbackPushforwardAdjunction b).comp (pullbackPushforwardAdjunction a)) _,
      conjugateEquiv_mateEquiv_vcomp _
        ((pullbackPushforwardAdjunction b').comp (pullbackPushforwardAdjunction a')) _,
      mateEquiv_hcomp, ha, hb, Scheme.Modules.conjugateEquiv_pullbackComp_inv,
      Stacks.ModuleSkyscraper.conjugateEquiv_pullbackComp_hom, pushforwardSquareIso_hom_vcomp wa
        wb wab]
  exact (AffinePushforward.baseChangeNatTrans_eq wab).trans
    ((Equiv.eq_symm_apply _).mpr h1).symm

/-- The four factors of the base-change morphism of a pasted square at a module: the two outer
ones are the comparisons of the inverse image with composition, the two inner ones are the
base-change morphisms of the two pieces. -/
theorem baseChangeNatTrans_vcomp_app (wa : a' ≫ f' = f'' ≫ a) (wb : b' ≫ f = f' ≫ b)
    (wab : (a' ≫ b') ≫ f = f'' ≫ (a ≫ b)) (M : X.Modules) :
    (AffinePushforward.baseChangeNatTrans wab).app M =
      (pullbackComp a b).inv.app ((Scheme.Modules.pushforward f).obj M) ≫
        (Scheme.Modules.pullback a).map ((AffinePushforward.baseChangeNatTrans wb).app M) ≫
        (AffinePushforward.baseChangeNatTrans wa).app ((Scheme.Modules.pullback b').obj M) ≫
        (Scheme.Modules.pushforward f'').map ((pullbackComp a' b').hom.app M) := by
  have h := NatTrans.congr_app (baseChangeNatTrans_vcomp wa wb wab) M
  simpa [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp] using h

/-- If the base-change morphism of the right-hand piece becomes invertible after applying the
inverse image along the bottom of the left-hand piece, and the base-change morphism of the
left-hand piece is invertible, then the base-change morphism of the pasted square is
invertible. -/
theorem isIso_baseChangeNatTrans_vcomp (wa : a' ≫ f' = f'' ≫ a) (wb : b' ≫ f = f' ≫ b)
    (wab : (a' ≫ b') ≫ f = f'' ≫ (a ≫ b)) (M : X.Modules)
    (hb : IsIso ((Scheme.Modules.pullback a).map ((AffinePushforward.baseChangeNatTrans wb).app M)))
    (ha : IsIso ((AffinePushforward.baseChangeNatTrans wa).app
      ((Scheme.Modules.pullback b').obj M))) :
    IsIso ((AffinePushforward.baseChangeNatTrans wab).app M) := by
  rw [baseChangeNatTrans_vcomp_app wa wb wab M]
  have := hb
  have := ha
  infer_instance

/-- Conversely, if the base-change morphisms of the pasted square and of the left-hand piece
are invertible, then the base-change morphism of the right-hand piece becomes invertible after
applying the inverse image along the bottom of the left-hand piece. -/
theorem isIso_map_baseChangeNatTrans_of_vcomp (wa : a' ≫ f' = f'' ≫ a) (wb : b' ≫ f = f' ≫ b)
    (wab : (a' ≫ b') ≫ f = f'' ≫ (a ≫ b)) (M : X.Modules)
    (ha : IsIso ((AffinePushforward.baseChangeNatTrans wa).app
      ((Scheme.Modules.pullback b').obj M)))
    (hab : IsIso ((AffinePushforward.baseChangeNatTrans wab).app M)) :
    IsIso ((Scheme.Modules.pullback a).map
      ((AffinePushforward.baseChangeNatTrans wb).app M)) := by
  rw [baseChangeNatTrans_vcomp_app wa wb wab M] at hab
  have := ha
  simpa using hab

/-- Invertibility of the base-change morphism of a commutative square depends only on the two
horizontal morphisms of the square: replacing them by equal morphisms, and the commutation
proof by any other one, preserves it. -/
theorem isIso_baseChangeNatTrans_congr {Y' Y T' T : Scheme.{u}} {p' : Y' ⟶ T'} {p : Y ⟶ T}
    {q₁' q₂' : Y' ⟶ Y} {q₁ q₂ : T' ⟶ T} (hq' : q₁' = q₂') (hq : q₁ = q₂)
    (w₁ : q₁' ≫ p = p' ≫ q₁) (w₂ : q₂' ≫ p = p' ≫ q₂) (M : Y.Modules)
    (h : IsIso ((AffinePushforward.baseChangeNatTrans w₁).app M)) :
    IsIso ((AffinePushforward.baseChangeNatTrans w₂).app M) := by
  subst hq'
  subst hq
  exact h

end Stacks.AlgebraicGeometry.AffineBaseChangeLocality

end
