module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.OpenRestriction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The localization square of a pullback of modules is the mate of its pushforward square

Let `u : C ⥤ D` be a continuous functor of sites carrying a comparison `φ` of structure sheaves,
and let `X` be an object of `C`. Restriction to the slice at `X` and to the slice at `u X`
commute with the direct image on the nose: both
`SheafOfModules.overFunctor R' (u X) ⋙ SheafOfModules.pushforward (overComparison φ X)` and
`SheafOfModules.pushforward φ ⋙ SheafOfModules.overFunctor R X` are the direct image along
`Over.forget X ⋙ u`, which is `Over.post u ⋙ Over.forget (u X)`. The localization square for the
*pullback*, `SheafOfModules.overFunctorPullbackIso` of Stacks 03FH (2), is built from the
uniqueness of left adjoints rather than from that identification, so nothing in its construction
says that it is the comparison that identification induces.

This file says it: the image of `SheafOfModules.overFunctorPullbackIso` under the adjunction of
the localized pullback is the restriction to the slice of the unit of the unlocalized pullback.
Equivalently, the localization square is the **mate** of the identification of the two direct
images.

## Main results

* `SheafOfModules.overPushforwardOverAdj_unit_pushforward`: the unit of the adjunction between
  restriction to a slice and direct image along `Over.star` commutes with a direct image, through
  the comparison of the two routes round the square of sites. This is `prodComparison_snd` read
  on sections.
* `SheafOfModules.homEquiv_overFunctorPullbackIso_hom_app`: **the localization square of the
  pullback is the mate of the identification of the two direct images.**

## Implementation notes

The square is a composite of three isomorphisms produced by
`CategoryTheory.Adjunction.leftAdjointUniq`, and each of them is characterized by
`CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app`: the image of the comparison under
the first adjunction's `homEquiv` is the second adjunction's unit. The proof applies that three
times — once for each of the two instances of
`SheafOfModules.pullbackPushforwardOverIso` and once for
`SheafOfModules.pullbackSquareIso` — and reduces everything to
`overPushforwardOverAdj_unit_pushforward`.

Both sides of the conclusion are morphisms out of `(overFunctor R X).obj M`, and
`SheafOfModules.overFunctor R X` is itself a left adjoint, by
`SheafOfModules.overPushforwardOverAdj`; the comparison is therefore checked after applying that
adjunction's `homEquiv`, which is injective. That is what turns the unit of the composite
adjunction appearing in `pullbackSquareIso` into something comparable with the unit of
`overPushforwardOverAdj`.

## References

* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
* [Stacks Project, Tag 04J0](https://stacks.math.columbia.edu/tag/04J0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe v u u₁ u₂ v₁ v₂

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D} [F.IsContinuous J K]
  {R : Sheaf J RingCat.{u}} {R' : Sheaf K RingCat.{u}}
  (φ : R ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R') (X : C)
  [(Over.post (X := X) F).IsContinuous (J.over X) (K.over (F.obj X))]
  [HasBinaryProducts C] [HasBinaryProducts D]
  [(Over.star X ⋙ Over.post F).IsContinuous J (K.over (F.obj X))]
  [(F ⋙ Over.star (F.obj X)).IsContinuous J (K.over (F.obj X))]

omit [HasBinaryProducts C] [HasBinaryProducts D]
  [(Over.star X ⋙ Over.post F).IsContinuous J (K.over (F.obj X))]
  [(F ⋙ Over.star (F.obj X)).IsContinuous J (K.over (F.obj X))] in
/-- **Restriction to a slice commutes with a direct image on the nose.** Restricting to the slice
at `u X` and then pushing forward along the localized functor is pushing forward along `u` and
then restricting to the slice at `X`: both are the direct image along
`Over.forget X ⋙ u = Over.post u ⋙ Over.forget (u X)`. -/
@[sga "4 IV 11.2.3" "partial"]
public theorem overFunctor_comp_pushforward_overComparison :
    overFunctor.{v} R' (F.obj X) ⋙ pushforward.{v} (overComparison φ X) =
      pushforward.{v} φ ⋙ overFunctor.{v} R X := rfl

/-- **The unit of `SheafOfModules.overPushforwardOverAdj` commutes with a direct image.** The
unit at a direct image is the direct image of the unit, followed by the comparison of the two
routes round the square of sites. On sections over an object `V` all three maps are restriction
maps of the module, and the identity between them is `CategoryTheory.Limits.prodComparison_snd`:
the product comparison of `u` followed by the second projection is `u` of the second
projection. -/
public theorem overPushforwardOverAdj_unit_pushforward
    (e : Over.star X ⋙ Over.post F ≅ F ⋙ Over.star (F.obj X))
    (hleft : ∀ Y : C, (e.hom.app Y).left = prodComparison F X Y)
    (Z : SheafOfModules.{v} R') :
    (pushforward.{v} φ).map ((overPushforwardOverAdj.{v} (F.obj X)).unit.app Z) ≫
        (pushforwardComp.{v} φ (pushforwardOver (F.obj X)) ≪≫
          pushforwardCongr₂.{v} _ e
            (comparisonComp_overComparison φ X e hleft) ≪≫
          (pushforwardComp.{v} (pushforwardOver X) (overComparison φ X)).symm).hom.app
          ((overFunctor.{v} R' (F.obj X)).obj Z) =
      (overPushforwardOverAdj.{v} X).unit.app ((pushforward.{v} φ).obj Z) := by
  ext V z
  have hL : (((pushforward.{v} φ).map ((overPushforwardOverAdj.{v} (F.obj X)).unit.app Z) ≫
      (pushforwardComp.{v} φ (pushforwardOver (F.obj X)) ≪≫
        pushforwardCongr₂.{v} _ e
          (comparisonComp_overComparison φ X e hleft) ≪≫
        (pushforwardComp.{v} (pushforwardOver X) (overComparison φ X)).symm).hom.app
        ((overFunctor.{v} R' (F.obj X)).obj Z)).val.app V) z =
      Z.val.map ((e.hom.app V.unop).left).op
        (Z.val.map ((Over.forgetAdjStar (F.obj X)).counit.app (F.obj V.unop)).op z) := rfl
  have hR : (((overPushforwardOverAdj.{v} X).unit.app ((pushforward.{v} φ).obj Z)).val.app V) z =
      Z.val.map (F.map ((Over.forgetAdjStar X).counit.app V.unop)).op z := rfl
  have key : (e.hom.app V.unop).left ≫
      (Over.forgetAdjStar (F.obj X)).counit.app (F.obj V.unop) =
      F.map ((Over.forgetAdjStar X).counit.app V.unop) := by
    rw [Over.forgetAdjStar_counit_app, Over.forgetAdjStar_counit_app, hleft]
    exact prodComparison_snd F X V.unop
  rw [hL]
  refine Eq.trans ?_ hR.symm
  rw [← key]
  exact (Z.val.map_comp_apply _ _ z).symm

variable [(pushforward.{v} φ).IsRightAdjoint]
  [(pushforward.{v} (overComparison φ X)).IsRightAdjoint]

/-- **The localization square of the pullback is the mate of the identification of the two direct
images.** Under the adjunction of the localized pullback, the comparison
`SheafOfModules.overFunctorPullbackIso` of Stacks 03FH (2) corresponds to the restriction to the
slice at `X` of the unit of the unlocalized pullback. -/
public theorem homEquiv_overFunctorPullbackIso_hom_app
    (e : Over.star X ⋙ Over.post F ≅ F ⋙ Over.star (F.obj X))
    (hleft : ∀ Y : C, (e.hom.app Y).left = prodComparison F X Y)
    (M : SheafOfModules.{v} R) :
    (pullbackPushforwardAdjunction.{v} (overComparison φ X)).homEquiv _ _
        ((overFunctorPullbackIso.{v} φ X e hleft).hom.app M) =
      (overFunctor.{v} R X).map ((pullbackPushforwardAdjunction.{v} φ).unit.app M) := by
  have hdec : (overFunctorPullbackIso.{v} φ X e hleft).hom.app M =
      (pullback.{v} (overComparison φ X)).map
          ((pullbackPushforwardOverIso.{v} (R := R) X).inv.app M) ≫
        (pullbackSquareIso.{v} (pushforwardOver X) (overComparison φ X) φ
            (pushforwardOver (F.obj X)) e
            (comparisonComp_overComparison φ X e hleft)).hom.app M ≫
          (pullbackPushforwardOverIso.{v} (R := R') (F.obj X)).hom.app
            ((pullback.{v} φ).obj M) := rfl
  set α := pushforwardComp.{v} φ (pushforwardOver (F.obj X)) ≪≫
    pushforwardCongr₂.{v} _ e (comparisonComp_overComparison φ X e hleft) ≪≫
    (pushforwardComp.{v} (pushforwardOver X) (overComparison φ X)).symm
  set A := ((pullbackPushforwardAdjunction.{v} φ).comp
    (pullbackPushforwardAdjunction.{v} (pushforwardOver (F.obj X)))).ofNatIsoRight α
  set B := (pullbackPushforwardAdjunction.{v} (pushforwardOver X)).comp
    (pullbackPushforwardAdjunction.{v} (overComparison φ X))
  rw [hdec, Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  refine ((overPushforwardOverAdj.{v} X).homEquiv _ _).injective ?_
  refine Eq.trans
    (Adjunction.homEquiv_naturality_right (overPushforwardOverAdj.{v} X) _ _) ?_
  have h1 : ((overPushforwardOverAdj.{v} X).homEquiv _ _)
        ((pullbackPushforwardOverIso.{v} (R := R) X).inv.app M) =
      (pullbackPushforwardAdjunction.{v} (pushforwardOver X)).unit.app M :=
    Adjunction.homEquiv_leftAdjointUniq_hom_app (overPushforwardOverAdj.{v} X)
      (pullbackPushforwardAdjunction.{v} (pushforwardOver X)) M
  rw [h1]
  have hpsi : (pullbackSquareIso.{v} (pushforwardOver X) (overComparison φ X) φ
        (pushforwardOver (F.obj X)) e (comparisonComp_overComparison φ X e hleft)).hom.app M =
      (Adjunction.leftAdjointUniq B A).hom.app M := rfl
  have hkey : ((pullbackPushforwardAdjunction.{v} (pushforwardOver X)).homEquiv _ _)
        (((pullbackPushforwardAdjunction.{v} (overComparison φ X)).homEquiv _ _)
          ((Adjunction.leftAdjointUniq B A).hom.app M)) = A.unit.app M := by
    refine Eq.trans ?_ (Adjunction.homEquiv_leftAdjointUniq_hom_app B A M)
    rw [Adjunction.comp_homEquiv]
    rfl
  rw [hpsi, Functor.map_comp, ← Category.assoc, ← Adjunction.homEquiv_unit, hkey]
  have hunit2 : A.unit.app M =
      ((pullbackPushforwardAdjunction.{v} φ).unit.app M ≫
        (pushforward.{v} φ).map
          ((pullbackPushforwardAdjunction.{v} (pushforwardOver (F.obj X))).unit.app
            ((pullback.{v} φ).obj M))) ≫
        α.hom.app ((pullback.{v} (pushforwardOver (F.obj X))).obj ((pullback.{v} φ).obj M)) := by
    rw [← Adjunction.homEquiv_id, Adjunction.homEquiv_ofNatIsoRight_apply,
      Adjunction.homEquiv_id, Adjunction.comp_unit_app]
    rfl
  have hrhs : ((overPushforwardOverAdj.{v} X).homEquiv _ _)
        ((overFunctor.{v} R X).map ((pullbackPushforwardAdjunction.{v} φ).unit.app M)) =
      (pullbackPushforwardAdjunction.{v} φ).unit.app M ≫
        (overPushforwardOverAdj.{v} X).unit.app
          ((pushforward.{v} φ).obj ((pullback.{v} φ).obj M)) :=
    ((overPushforwardOverAdj.{v} X).unit.naturality
      ((pullbackPushforwardAdjunction.{v} φ).unit.app M)).symm
  rw [hunit2]
  refine Eq.trans ?_ hrhs.symm
  rw [Category.assoc, Category.assoc]
  refine congrArg (fun t => (pullbackPushforwardAdjunction.{v} φ).unit.app M ≫ t) ?_
  have h2 : ((pullbackPushforwardAdjunction.{v} (pushforwardOver (F.obj X))).homEquiv _ _)
        ((pullbackPushforwardOverIso.{v} (R := R') (F.obj X)).hom.app ((pullback.{v} φ).obj M)) =
      (overPushforwardOverAdj.{v} (F.obj X)).unit.app ((pullback.{v} φ).obj M) :=
    Adjunction.homEquiv_leftAdjointUniq_hom_app
      (pullbackPushforwardAdjunction.{v} (pushforwardOver (F.obj X)))
      (overPushforwardOverAdj.{v} (F.obj X)) ((pullback.{v} φ).obj M)
  rw [← Functor.comp_map,
    ← α.hom.naturality
      ((pullbackPushforwardOverIso.{v} (R := R') (F.obj X)).hom.app ((pullback.{v} φ).obj M)),
    ← Category.assoc, Functor.comp_map, ← Functor.map_comp,
    ← Adjunction.homEquiv_unit (pullbackPushforwardAdjunction.{v} (pushforwardOver (F.obj X))),
    h2]
  exact overPushforwardOverAdj_unit_pushforward φ X e hleft ((pullback.{v} φ).obj M)

end SheafOfModules

end

