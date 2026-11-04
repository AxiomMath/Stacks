module

public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.Pasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BasePasting

/-!
# Pasting base-change squares along the direct images

For two commutative squares of schemes stacked along the vertical direction,
```
U' --h--> U
|j'       |j
X' --g'-> X
|f'       |f
S' --g--> S
```
the base-change morphism `g^* (j ≫ f)_* ⟶ (j' ≫ f')_* h^*` of the outer rectangle is the
base-change morphism of the lower square at `j_* M`, followed by `f'_*` applied to the
base-change morphism of the upper square at `M`.

## Main results

* `Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.pushforwardSquare_vComp`: the
  identifications of composite direct images stack.
* `Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.baseChangeNatTrans_vertical_app`: the
  base-change morphisms stack.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.FlatBaseChangeCohomology

variable {U U' X X' S S' : Scheme.{u}} {j : U ⟶ X} {j' : U' ⟶ X'} {h : U' ⟶ U}
  {f : X ⟶ S} {f' : X' ⟶ S'} {g : S' ⟶ S} {g' : X' ⟶ X}

/-- Composing with the image of an identity on the left and with an identity on the right does
nothing. -/
theorem map_comp_comp_eq {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) {A : C} {B : D}
    (a : A ⟶ A) (ha : a = 𝟙 A) (x : F.obj A ⟶ B) (b : B ⟶ B) (hb : b = 𝟙 B) :
    (F.map a ≫ x) ≫ b = x := by
  subst ha hb
  simp

/-- The commutativity of the outer rectangle of two vertically stacked squares. -/
theorem vertical_comm (wj : h ≫ j = j' ≫ g') (wf : g' ≫ f = f' ≫ g) :
    h ≫ (j ≫ f) = (j' ≫ f') ≫ g := by
  rw [← Category.assoc, wj, Category.assoc, wf, Category.assoc]

/-- **The identifications of the composite direct images stack** along the vertical
direction. -/
theorem pushforwardSquare_vComp (wj : h ≫ j = j' ≫ g') (wf : g' ≫ f = f' ≫ g) :
    pushforwardSquare (vertical_comm wj wf) =
      ((TwoSquare.vComp (pushforwardSquare wj) (pushforwardSquare wf)).whiskerRight
          (Scheme.Modules.pushforwardComp j f).inv).whiskerLeft
            (Scheme.Modules.pushforwardComp j' f').hom := by
  ext M V
  simp only [pushforwardSquare, AffinePushforward.pushforwardSquareIso, Functor.comp_obj,
    Scheme.Modules.pushforward_obj_obj, Scheme.Hom.comp_base, TopologicalSpace.Opens.map_comp_obj,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforwardComp_hom_app_app, Scheme.Modules.pushforwardCongr_hom_app_app,
    Scheme.Modules.pushforwardComp_inv_app_app, Category.comp_id, Category.id_comp,
    TwoSquare.natTrans, TwoSquare.whiskerLeft_app, TwoSquare.whiskerRight_app, TwoSquare.vComp_app,
    Functor.map_comp, Category.assoc,
    Scheme.Modules.pushforward_map_app, Scheme.Modules.pushforward_obj_presheaf_map,
    AddCommGrpCat.hom_comp]
  congr 1
  rw [← AddCommGrpCat.hom_comp, ← Functor.map_comp]
  exact congrArg (fun t => AddCommGrpCat.Hom.hom (M.presheaf.map t)) (Subsingleton.elim _ _)

/-- **The base-change morphisms stack along the vertical direction.** The base-change morphism of
the outer rectangle is the horizontal composite, in the sense of `CategoryTheory.TwoSquare`, of
the two base-change morphisms. -/
theorem baseChangeSquare_vertical (wj : h ≫ j = j' ≫ g') (wf : g' ≫ f = f' ≫ g) :
    baseChangeSquare (vertical_comm wj wf) =
      ((TwoSquare.hComp (baseChangeSquare wj) (baseChangeSquare wf)).whiskerTop
          (Scheme.Modules.pushforwardComp j f).inv).whiskerBottom
            (Scheme.Modules.pushforwardComp j' f').hom := by
  apply (mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction h)
    (Scheme.Modules.pullbackPushforwardAdjunction g)).injective
  rw [Stacks.Cohomology.BaseChange.mateEquiv_whisker,
    CategoryTheory.mateEquiv_vcomp _ (Scheme.Modules.pullbackPushforwardAdjunction g'),
    mateEquiv_baseChangeSquare, mateEquiv_baseChangeSquare, mateEquiv_baseChangeSquare,
    pushforwardSquare_vComp]

/-- **The base-change morphisms stack along the vertical direction**, at a module: the
base-change morphism of the outer rectangle at `M` is the base-change morphism of the lower
square at `j_* M` followed by `f'_*` of the base-change morphism of the upper square at `M`. -/
theorem baseChangeNatTrans_vertical_app (wj : h ≫ j = j' ≫ g') (wf : g' ≫ f = f' ≫ g)
    (M : U.Modules) :
    (AffinePushforward.baseChangeNatTrans (vertical_comm wj wf)).app M =
      (AffinePushforward.baseChangeNatTrans wf).app ((Scheme.Modules.pushforward j).obj M) ≫
        (Scheme.Modules.pushforward f').map ((AffinePushforward.baseChangeNatTrans wj).app M) := by
  have hh := congrArg (fun w => w.natTrans.app M) (baseChangeSquare_vertical wj wf)
  simp only [natTrans_baseChangeSquare, TwoSquare.natTrans, TwoSquare.whiskerBottom_app,
    TwoSquare.whiskerTop_app] at hh
  have hR : (TwoSquare.hComp (AffinePushforward.baseChangeNatTrans wj)
      (AffinePushforward.baseChangeNatTrans wf)).app M =
      (AffinePushforward.baseChangeNatTrans wf).app ((Scheme.Modules.pushforward j).obj M) ≫
        (Scheme.Modules.pushforward f').map
          ((AffinePushforward.baseChangeNatTrans wj).app M) := by
    simp [TwoSquare.hComp]
  exact hh.trans ((map_comp_comp_eq _ _ rfl _ _ rfl).trans hR)

end Stacks.AlgebraicGeometry.FlatBaseChangeCohomology

end
