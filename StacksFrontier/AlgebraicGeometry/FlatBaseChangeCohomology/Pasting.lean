module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkMateComp
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.BaseChange

/-!
# Pasting base-change squares along the base

For a commutative square of schemes
```
X' --g'--> X
|f'        |f
S' --g-->  S
```
the canonical base-change morphism `g^* f_* ⟶ f'_* (g')^*` of sheaves of modules is
`Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans`, the mate of the identification
of the two composite direct images around the square.  This file proves that these morphisms
*paste along the base*: given a second square stacked to the left,
```
X'' --h'--> X' --g'--> X
|f''        |f'        |f
S'' --h-->  S'  --g--> S
```
the base-change morphism of the outer rectangle is the vertical composite of the two
base-change morphisms, transported along the canonical identifications
`AlgebraicGeometry.Scheme.Modules.pullbackComp` of an inverse image along a composite with the
composite of the inverse images.

## Main definitions

* `baseChangeSquare`: the base-change morphism `baseChangeNatTrans` of a commutative square,
  as a `CategoryTheory.TwoSquare`.
* `pushforwardSquare`: the identification `pushforwardSquareIso` of the two composite direct
  images around a commutative square, as a `CategoryTheory.TwoSquare`.

## Main results

* `pasteBase`: the outer rectangle obtained by stacking two commutative squares along the base
  commutes.
* `mateEquiv_baseChangeSquare`: the base-change square is the mate of the direct-image square.
* `pushforwardSquare_pasteBase`: the direct-image square of the outer rectangle is the
  horizontal composite of the two direct-image squares, whiskered by `pushforwardComp`.
* `baseChangeSquare_pasteBase`: the base-change morphism of the outer rectangle is the vertical
  composite of the two base-change morphisms, whiskered by the two `pullbackComp`
  identifications.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 0F6X](https://stacks.math.columbia.edu/tag/0F6X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.FlatBaseChangeCohomology

/-! ### Base-change and direct-image squares -/

variable {X X' X'' S S' S'' : Scheme.{u}}
  {f : X ⟶ S} {f' : X' ⟶ S'} {f'' : X'' ⟶ S''}
  {g : S' ⟶ S} {g' : X' ⟶ X} {h : S'' ⟶ S'} {h' : X'' ⟶ X'}

/-- The base-change morphism `g^* f_* ⟶ f'_* (g')^*` of a commutative square, packaged as a
`CategoryTheory.TwoSquare`. -/
noncomputable def baseChangeSquare (w : g' ≫ f = f' ≫ g) :
    TwoSquare (Scheme.Modules.pushforward f) (Scheme.Modules.pullback g')
      (Scheme.Modules.pullback g) (Scheme.Modules.pushforward f') :=
  TwoSquare.mk _ _ _ _ (AffinePushforward.baseChangeNatTrans w)

/-- The natural transformation underlying `baseChangeSquare w` is the base-change morphism
`AffinePushforward.baseChangeNatTrans w`. -/
@[simp]
theorem natTrans_baseChangeSquare (w : g' ≫ f = f' ≫ g) :
    baseChangeSquare w = AffinePushforward.baseChangeNatTrans w :=
  rfl

/-- The identification `g'_* ∘ f_* ≅ f'_* ∘ g_*` of the two composite direct images around a
commutative square, packaged as a `CategoryTheory.TwoSquare`. -/
noncomputable def pushforwardSquare (w : g' ≫ f = f' ≫ g) :
    TwoSquare (Scheme.Modules.pushforward g') (Scheme.Modules.pushforward f')
      (Scheme.Modules.pushforward f) (Scheme.Modules.pushforward g) :=
  TwoSquare.mk _ _ _ _ (AffinePushforward.pushforwardSquareIso w).hom

/-- The base-change square is the mate of the direct-image square. -/
theorem mateEquiv_baseChangeSquare (w : g' ≫ f = f' ≫ g) :
    (mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction g')
      (Scheme.Modules.pullbackPushforwardAdjunction g)) (baseChangeSquare w) =
      pushforwardSquare w :=
  Equiv.apply_symm_apply _ _

/-- Stacking two commutative squares along the base: the outer rectangle commutes. -/
theorem pasteBase (w₁ : g' ≫ f = f' ≫ g) (w₂ : h' ≫ f' = f'' ≫ h) :
    (h' ≫ g') ≫ f = f'' ≫ (h ≫ g) := by
  rw [Category.assoc, w₁, ← Category.assoc, w₂, Category.assoc]

/-! ### The pasting law -/

/-- The pasting law for base-change squares, stated with the composite adjunctions: the mate of
the vertical composite of the two base-change squares is the horizontal composite of the two
direct-image squares. -/
theorem mateEquiv_vComp_baseChangeSquare (w₁ : g' ≫ f = f' ≫ g) (w₂ : h' ≫ f' = f'' ≫ h) :
    (mateEquiv
        ((Scheme.Modules.pullbackPushforwardAdjunction g').comp
          (Scheme.Modules.pullbackPushforwardAdjunction h'))
        ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
          (Scheme.Modules.pullbackPushforwardAdjunction h)))
      (TwoSquare.vComp (baseChangeSquare w₁) (baseChangeSquare w₂)) =
      TwoSquare.hComp (pushforwardSquare w₂) (pushforwardSquare w₁) := by
  rw [CategoryTheory.mateEquiv_hcomp, mateEquiv_baseChangeSquare, mateEquiv_baseChangeSquare]

/-- The direct-image square of the outer rectangle, in terms of the two direct-image squares. -/
theorem pushforwardSquare_pasteBase (w₁ : g' ≫ f = f' ≫ g) (w₂ : h' ≫ f' = f'' ≫ h) :
    pushforwardSquare (pasteBase w₁ w₂) =
      ((TwoSquare.hComp (pushforwardSquare w₂) (pushforwardSquare w₁)).whiskerTop
        (Scheme.Modules.pushforwardComp h' g').inv).whiskerBottom
          (Scheme.Modules.pushforwardComp h g).hom := by
  ext M U
  simp only [pushforwardSquare, AffinePushforward.pushforwardSquareIso, Functor.comp_obj,
    Scheme.Modules.pushforward_obj_obj, Scheme.Hom.comp_base, Opens.map_comp_obj, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforwardComp_hom_app_app, Scheme.Modules.pushforwardCongr_hom_app_app,
    Scheme.Modules.pushforwardComp_inv_app_app, Category.comp_id, Category.id_comp,
    TwoSquare.whiskerBottom_app, TwoSquare.whiskerTop_app, TwoSquare.hComp_app, Functor.map_comp,
    Category.assoc, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.pushforward_obj_presheaf_map, AddCommGrpCat.hom_comp]
  congr 1
  rw [← AddCommGrpCat.hom_comp, ← Functor.map_comp]
  exact congrArg (fun t => AddCommGrpCat.Hom.hom (M.presheaf.map t)) (Subsingleton.elim _ _)

/-- **The base-change morphisms paste along the base.**  For two commutative squares stacked
along the base, the base-change morphism of the outer rectangle is the vertical composite of
the two base-change morphisms, whiskered by the canonical identifications of an inverse image
along a composite with the composite of the inverse images. -/
theorem baseChangeSquare_pasteBase (w₁ : g' ≫ f = f' ≫ g) (w₂ : h' ≫ f' = f'' ≫ h) :
    baseChangeSquare (pasteBase w₁ w₂) =
      ((TwoSquare.vComp (baseChangeSquare w₁) (baseChangeSquare w₂)).whiskerLeft
        (Scheme.Modules.pullbackComp h' g').hom).whiskerRight
          (Scheme.Modules.pullbackComp h g).inv := by
  apply (mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction (h' ≫ g'))
    (Scheme.Modules.pullbackPushforwardAdjunction (h ≫ g))).injective
  rw [mateEquiv_baseChangeSquare,
    CategoryTheory.mateEquiv_conjugateEquiv_vcomp
      (Scheme.Modules.pullbackPushforwardAdjunction (h' ≫ g'))
      ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
        (Scheme.Modules.pullbackPushforwardAdjunction h))
      (Scheme.Modules.pullbackPushforwardAdjunction (h ≫ g)),
    Scheme.Modules.conjugateEquiv_pullbackComp_inv,
    CategoryTheory.conjugateEquiv_mateEquiv_vcomp
      (Scheme.Modules.pullbackPushforwardAdjunction (h' ≫ g'))
      ((Scheme.Modules.pullbackPushforwardAdjunction g').comp
        (Scheme.Modules.pullbackPushforwardAdjunction h'))
      ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
        (Scheme.Modules.pullbackPushforwardAdjunction h)),
    Stacks.ModuleSkyscraper.conjugateEquiv_pullbackComp_hom, mateEquiv_vComp_baseChangeSquare]
  exact pushforwardSquare_pasteBase w₁ w₂

end Stacks.AlgebraicGeometry.FlatBaseChangeCohomology

end
