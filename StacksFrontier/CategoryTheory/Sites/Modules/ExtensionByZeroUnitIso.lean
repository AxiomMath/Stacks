module

public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.ExtensionByZeroTensor
public import Mathlib.CategoryTheory.Adjunction.Triple
public import Mathlib.CategoryTheory.Limits.Lattice
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Restriction of extension by zero is the identity, over a subterminal object

Let `(C, O)` be a ringed site whose underlying category has binary products, and let `U` be an
object of `C`. Restriction of sheaves of modules to the slice site `C/U` has a left adjoint, the
extension by zero `j_!` of Stacks 03DI, and a right adjoint, the pushforward `j_*` along
`Over.star U`. When `U` is *subterminal* — when the unit `V ⟶ U × V` of
`Over.forget U ⊣ Over.star U` is an isomorphism for every `V ⟶ U`, as happens for every open
of a topological space — restricting `j_*` back is the identity, so the counit of `j^* ⊣ j_*`
is an isomorphism, and by the adjoint-triple argument so is the unit `G ⟶ j^* j_! G`.

## Main results

* `Stacks.SheafOfModules.ExtensionByZero.isIso_extensionByZeroAdjunction_unit`: the unit of
  `j_! ⊣ j^*` is an isomorphism when the unit of `Over.forget U ⊣ Over.star U` is.
* `Stacks.SheafOfModules.ExtensionByZero.isIso_forgetAdjStar_unit_opens`: that is the case for
  every open of a topological space.

## References

* [Stacks Project, Tag 03DI](https://stacks.math.columbia.edu/tag/03DI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

namespace Stacks.SheafOfModules.ExtensionByZero

universe u

attribute [local implicit_reducible] CategoryTheory.Functor.sheafPushforwardContinuous

/-- **Every open of a topological space is subterminal**: the unit `V ⟶ U × V` of
`Over.forget U ⊣ Over.star U` is an isomorphism over `U`, morphisms of opens being unique. -/
instance isIso_forgetAdjStar_unit_opens {T : Type u} [TopologicalSpace T] (U : Opens T) :
    IsIso (Over.forgetAdjStar U).unit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro W
  exact ⟨Over.homMk (prod.snd : U ⨯ W.left ⟶ W.left) (Subsingleton.elim _ _),
    Over.OverMorphism.ext (Subsingleton.elim _ _), Over.OverMorphism.ext (Subsingleton.elim _ _)⟩

section Generic

variable {C : Type u} [Category.{u} C] [HasBinaryProducts C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} (x : C)

/-- The endofunctor `Over.forget x ⋙ Over.star x` of the slice over `x` is continuous for the
induced topology `J.over x`. -/
instance isContinuous_forget_comp_star :
    (Over.forget x ⋙ Over.star x).IsContinuous (J.over x) (J.over x) :=
  Functor.isContinuous_comp _ _ _ J _

/-- When the unit of `Over.forget x ⊣ Over.star x` is an isomorphism, the composite of the
ring-sheaf morphism `_root_.SheafOfModules.pushforwardOver x`, pushed forward along
`Over.forget x`, with the morphism induced by that unit is the identity of `R.over x`. -/
lemma pushforwardOver_comp_eq [IsIso (Over.forgetAdjStar x).unit] :
    (𝟙 (R.over x) ≫ ((Over.forget x).sheafPushforwardContinuous RingCat.{u} (J.over x) J).map
        (_root_.SheafOfModules.pushforwardOver (R := R) x)) ≫
      (Functor.sheafPushforwardContinuousNatTrans (asIso (Over.forgetAdjStar x).unit).hom
        RingCat.{u} (J.over x) (J.over x)).app (R.over x) = 𝟙 _ := by
  ext1
  refine NatTrans.ext (funext fun y => ?_)
  have h : ((Over.forgetAdjStar x).unit.app y.unop).left ≫
      (prod.snd : x ⨯ y.unop.left ⟶ y.unop.left) = 𝟙 _ := by
    rw [Over.forgetAdjStar_unit_app_left]
    exact prod.lift_snd _ _
  exact (R.obj.map_comp _ _).symm.trans ((congrArg (fun f => R.obj.map f.op) h).trans
    (R.obj.map_id _))

/-- Over a subterminal `x`, pushing forward along `Over.star x` and restricting back to the
slice over `x` is the identity. -/
noncomputable def pushforwardOverRestrictIso [IsIso (Over.forgetAdjStar x).unit] :
    _root_.SheafOfModules.pushforward.{u} (_root_.SheafOfModules.pushforwardOver (R := R) x) ⋙
      _root_.SheafOfModules.pushforward.{u} (𝟙 (R.over x)) ≅ 𝟭 _ :=
  _root_.SheafOfModules.pushforwardComp (𝟙 (R.over x))
      (_root_.SheafOfModules.pushforwardOver (R := R) x) ≪≫
    _root_.SheafOfModules.pushforwardNatIso _ (asIso (Over.forgetAdjStar x).unit) ≪≫
    _root_.SheafOfModules.pushforwardCongr (pushforwardOver_comp_eq x) ≪≫
    _root_.SheafOfModules.pushforwardId _

end Generic

variable (X : RingedSite.{u, u, u}) (U : X.C) [HasBinaryProducts X.C]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Restriction to the slice site over `U` is left adjoint to the pushforward along
`Over.star U`, with the left adjoint written as `SheafOfModules.overFunctor`. -/
@[ega "IV 11.9.17" "more general", sga "4 IV 14.2" "j^* ⊣ j_*"]
noncomputable def restrictionPushforwardAdjunction :
    _root_.SheafOfModules.overFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) U ⊣
      _root_.SheafOfModules.pushforward.{u}
        (_root_.SheafOfModules.pushforwardOver
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U) :=
  _root_.SheafOfModules.overPushforwardOverAdj U

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Over a subterminal `U`, restricting the pushforward is the identity**: the counit of
`j^* ⊣ j_*` is an isomorphism. Its component at `M` is, over `V ⟶ U`, the restriction of `M`
along the unit `V ⟶ U × V`, which is an isomorphism. -/
theorem isIso_restrictionPushforwardAdjunction_counit [IsIso (Over.forgetAdjStar U).unit] :
    IsIso (restrictionPushforwardAdjunction X U).counit :=
  (restrictionPushforwardAdjunction X U).isIso_counit_of_iso
    (pushforwardOverRestrictIso (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U)

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **`j^* j_! = id` over a subterminal object.** The unit of the extension-by-zero adjunction
`j_! ⊣ j^*` of Stacks 03DI is an isomorphism as soon as the unit of
`Over.forget U ⊣ Over.star U` is: `j_!`, `j^*` and `j_*` form an adjoint triple, and the counit
of `j^* ⊣ j_*` is an isomorphism. -/
theorem isIso_extensionByZeroAdjunction_unit [IsIso (Over.forgetAdjStar U).unit] :
    IsIso (extensionByZeroAdjunction X U).unit := by
  have := isIso_restrictionPushforwardAdjunction_counit X U
  exact (Adjunction.Triple.isIso_unit_iff_isIso_counit
    ⟨extensionByZeroAdjunction X U, restrictionPushforwardAdjunction X U⟩).2 inferInstance

end Stacks.SheafOfModules.ExtensionByZero
