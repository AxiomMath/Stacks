module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Sites.CoverLifting

/-!
# The underlying presheaf transformation of a mate of sheaf functors

For a functor between sites which is both continuous and cocontinuous, restriction of sheaves is
left adjoint to the direct image (`CategoryTheory.Functor.sheafAdjunctionCocontinuous`), and on
underlying presheaves that adjunction is the right Kan extension adjunction
(`CategoryTheory.Functor.sheafAdjunctionCocontinuous_homEquiv_apply_hom` and the unit and counit
forms of the same).  Consequently a mate taken for two such adjunctions has, as its underlying
transformation of presheaves, the mate taken for the two right Kan extension adjunctions.

This is the step that moves a Beck–Chevalley 2-cell between sheaves to one between presheaves,
where right Kan extensions are available and the base change of
`CategoryTheory.TwoSquare.ranBaseChange` lives.

## Main results

* `Stacks.CategoryTheory.mateEquiv_symm_sheafAdjunctionCocontinuous_app_hom`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.TwoSquare

universe u

namespace Stacks.CategoryTheory

variable {Cn Ct Cn' Ct' : Type u} [SmallCategory Cn] [SmallCategory Ct] [SmallCategory Cn']
  [SmallCategory Ct']
  {Jn : GrothendieckTopology Cn} {K : GrothendieckTopology Ct}
  {Jn' : GrothendieckTopology Cn'} {K' : GrothendieckTopology Ct'}
  (i : Cn ⥤ Ct) [i.IsContinuous Jn K] [i.IsCocontinuous Jn K]
  (i' : Cn' ⥤ Ct') [i'.IsContinuous Jn' K'] [i'.IsCocontinuous Jn' K']
  (v : Cn ⥤ Cn') [v.IsCocontinuous Jn Jn']
  (V : Ct ⥤ Ct') [V.IsCocontinuous K K']

/-- **The mate of sheaf functors, on underlying presheaves.**  Let `i` and `i'` be continuous and
cocontinuous and let `v` and `V` be cocontinuous, forming a square of sites.  A 2-cell `β` between
the two composites of direct images of sheaves and a 2-cell `βp` between the two composites of
right Kan extensions of presheaves which agree on the underlying presheaf of every sheaf have
mates that agree likewise. -/
theorem mateEquiv_symm_sheafAdjunctionCocontinuous_app_hom
    (β : TwoSquare (i.sheafPushforwardCocontinuous (Type u) Jn K)
      (v.sheafPushforwardCocontinuous (Type u) Jn Jn')
      (V.sheafPushforwardCocontinuous (Type u) K K')
      (i'.sheafPushforwardCocontinuous (Type u) Jn' K'))
    (βp : TwoSquare (i.op.ran (H := Type u)) v.op.ran V.op.ran i'.op.ran)
    (hβ : ∀ Z : Sheaf Jn (Type u), (β.app Z).hom = βp.app Z.obj)
    (Y : Sheaf K (Type u)) :
    (((mateEquiv (i.sheafAdjunctionCocontinuous (Type u) Jn K)
          (i'.sheafAdjunctionCocontinuous (Type u) Jn' K')).symm β).app Y).hom =
      ((mateEquiv (i.op.ranAdjunction (Type u))
        (i'.op.ranAdjunction (Type u))).symm βp).app Y.obj := by
  have hres : ∀ {X Z : Sheaf K' (Type u)} (f : X ⟶ Z),
      ((i'.sheafPushforwardContinuous (Type u) Jn' K').map f).hom =
        ((whiskeringLeft Cn'ᵒᵖ Ct'ᵒᵖ (Type u)).obj i'.op).map f.hom := fun _ => rfl
  have hran : ∀ {X Z : Sheaf K (Type u)} (f : X ⟶ Z),
      ((V.sheafPushforwardCocontinuous (Type u) K K').map f).hom = V.op.ran.map f.hom :=
    fun _ => rfl
  simp only [mateEquiv_symm_apply, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app, Functor.comp_obj,
    Functor.comp_map, CategoryTheory.Functor.map_id,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom,
    Category.id_comp,
    hres, hran,
    Functor.sheafAdjunctionCocontinuous_unit_app_hom,
    Functor.sheafAdjunctionCocontinuous_counit_app_hom, hβ]
  rfl

end Stacks.CategoryTheory

end
