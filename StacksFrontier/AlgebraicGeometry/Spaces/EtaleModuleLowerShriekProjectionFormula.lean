module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorIsoSections
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackTensorSections
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackSheafHomMapEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSite
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackProjectionFormula
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EssentiallySmallInternalHomPushforward
public meta import StacksFrontier.Tactic.HEqCongr

/-!
# The projection formula for extension by zero along an étale morphism

For an étale morphism `a : X' ⟶ X` of algebraic spaces, the projection map
`AlgebraicGeometry.Space.etaleModuleLowerShriekProjectionMap` is built from the comparison of
Stacks 03EL for the morphism of small étale ringed topoi, transported to étale restriction
`a^*M = M|_{X'}` along Stacks 03LW. This file computes that transported comparison on local
sections: on a sheafified pure tensor `s ⊗ t` of sections over a chart `V` of `X'` its inverse is
the sheafified pure tensor `s ⊗ t` over the composite chart of `X`, so it introduces no twist.
Together with Stacks 04M0 on slices this makes the map of Stacks 08JF for `a^*` invertible, and
hence the projection map an isomorphism.

## Main results

* `DerivedPullbackOfToposHom.pullbackTensorIsoOfIso_inv_val_app_toSheafify_pushforward`, in
  the namespace `Stacks.Cohomology`: the generic statement, for a morphism of ringed topoi whose
  pullback is identified with a pushforward compatibly with the units of Tag 03CZ.
* `AlgebraicGeometry.Space.pullbackTensorIsoOfIso_inv_val_app_toSheafify_etale`: the case of an
  étale morphism of algebraic spaces.
* `AlgebraicGeometry.Space.etaleModulePullback_restrFun_hom_existsUnique`: morphisms of restricted
  modules over a slice of `X'` are morphisms over the slice of `X` at the composite chart
  (Stacks 04M0), the slice hypothesis of the Fausk–Hu–May argument for the projection map.
* `AlgebraicGeometry.Space.isIso_etaleModuleLowerShriekProjectionMap`: the projection map
  `a_!(A ⊗ a^*M) ⟶ a_!A ⊗ M` is an isomorphism.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 08JF](https://stacks.math.columbia.edu/tag/08JF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry MonoidalCategory
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.SheafOfModules
open Stacks.PresheafOfModules.InternalHom

/-- Equality of two terms that are heterogeneously equal to the two sides of an equality. -/
private theorem eq_of_heq_of_eq_of_heq {α β : Sort _} {x y : α} {a b : β} (h₁ : HEq x a)
    (h : a = b) (h₂ : HEq b y) : x = y :=
  eq_of_heq (h₁.trans ((heq_of_eq h).trans h₂))

namespace Stacks.Cohomology.DerivedPullbackOfToposHom

universe c u

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf

variable {X Y : RingedTopos.{u, c, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)]
  (f : AlgebraicGeometry.RingedToposHom X Y)

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
/-- **Stacks 03EL transported to a pushforward, on local sections.** If the pullback of `f` is
identified, through `toModulesHom_eq_toRingedToposModulesHom` and `e`, with the pushforward along
a continuous functor `F`, compatibly with an identification `ε : f⁻¹ ≅ F_*` on the units of
Tag 03CZ, then the inverse of the transported comparison sends the sheafified pure tensor `x ⊗ y`
over `U` to the sheafified pure tensor `x ⊗ y` over `F U`. -/
theorem pullbackTensorIsoOfIso_inv_val_app_toSheafify_pushforward
    (F : X.C ⥤ Y.C) [F.IsContinuous X.J Y.J]
    (ε : f.toRingedToposModulesHom.toToposHom.inverseImage ≅
      F.sheafPushforwardContinuous (Type u) X.J Y.J)
    (φ : (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
      (F.sheafPushforwardContinuous RingCat.{u} X.J Y.J).obj
        ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (e₁ : f.toModulesHom.pullbackModules ≅ f.toRingedToposModulesHom.pullbackModules)
    (he₁ : e₁ = eqToIso (congrArg (fun g : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y ↦
      g.pullbackModules)
        (AlgebraicGeometry.RingedToposHom.toModulesHom_eq_toRingedToposModulesHom f)))
    (e : f.toRingedToposModulesHom.pullbackModules ≅ _root_.SheafOfModules.pushforward.{u} φ)
    (he : ∀ (G : _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
      (U : X.Cᵒᵖ)
      (m : ((inverseImageModules f.toRingedToposModulesHom.toToposHom
        ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).obj G).val.obj U),
      (e.hom.app G).val.app U (((Stacks.SheafOfModules.RingedToposPullback.structureAdjunction
          f.toRingedToposModulesHom).unit.app
          ((inverseImageModules f.toRingedToposModulesHom.toToposHom
            ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).obj G)).val.app U m) =
        (ε.hom.app (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) G)).hom.app
          U m)
    (A M : _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) (U : X.Cᵒᵖ)
    (x : ((_root_.SheafOfModules.pushforward.{u} φ).obj A).val.obj U)
    (y : ((_root_.SheafOfModules.pushforward.{u} φ).obj M).val.obj U) :
    ((pullbackTensorIsoOfIso f (e₁ ≪≫ e)).inv.app
          (A, M)).val.app U
      ((TensorSheafification.toSheafify X.O.obj
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).property
          (((_root_.SheafOfModules.pushforward.{u} φ).obj A).val ⊗
            ((_root_.SheafOfModules.pushforward.{u} φ).obj M).val)).app U (x ⊗ₜ y)) =
      (TensorSheafification.toSheafify Y.O.obj
          ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
          (A.val ⊗ M.val)).app (F.op.obj U) (x ⊗ₜ y) :=
  open RingedToposPullback in
  tensorIsoOfNatIsoRight_trans_eqToIso_pullbackTensorIso_inv_val_app_toSheafify_pushforward
    (AlgebraicGeometry.RingedToposHom.toModulesHom_eq_toRingedToposModulesHom f) e₁ he₁ F ε φ e he
    (pullbackTensorIsoUncurried f) rfl A M U x y

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
/-- **Stacks 03EL transported to a pushforward, as the tensor hypothesis of the map of Stacks
08JF.** Under the hypotheses of `pullbackTensorIsoOfIso_inv_val_app_toSheafify_pushforward`, the
transported comparison satisfies `AlgebraicGeometry.RingedSite.PushforwardTensorCompat`. -/
theorem pushforwardTensorCompat_pullbackTensorIsoOfIso
    (F : X.C ⥤ Y.C) [F.IsContinuous X.J Y.J]
    (ε : f.toRingedToposModulesHom.toToposHom.inverseImage ≅
      F.sheafPushforwardContinuous (Type u) X.J Y.J)
    (φ : (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
      (F.sheafPushforwardContinuous RingCat.{u} X.J Y.J).obj
        ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (e₁ : f.toModulesHom.pullbackModules ≅ f.toRingedToposModulesHom.pullbackModules)
    (he₁ : e₁ = eqToIso (congrArg (fun g : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y ↦
      g.pullbackModules)
        (AlgebraicGeometry.RingedToposHom.toModulesHom_eq_toRingedToposModulesHom f)))
    (e : f.toRingedToposModulesHom.pullbackModules ≅ _root_.SheafOfModules.pushforward.{u} φ)
    (he : ∀ (G : _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
      (U : X.Cᵒᵖ)
      (m : ((inverseImageModules f.toRingedToposModulesHom.toToposHom
        ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).obj G).val.obj U),
      (e.hom.app G).val.app U (((Stacks.SheafOfModules.RingedToposPullback.structureAdjunction
          f.toRingedToposModulesHom).unit.app
          ((inverseImageModules f.toRingedToposModulesHom.toToposHom
            ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).obj G)).val.app U m) =
        (ε.hom.app (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) G)).hom.app
          U m) :
    AlgebraicGeometry.RingedSite.PushforwardTensorCompat (X := X.toRingedSite)
      (Y := Y.toRingedSite) (u := F) φ (pullbackTensorIsoOfIso f (e₁ ≪≫ e)) :=
  ⟨fun A M U s t ↦ by
    have key := pullbackTensorIsoOfIso_inv_val_app_toSheafify_pushforward f F ε φ e₁ he₁ e he
      A M (op U) s t
    exact eq_of_heq_of_eq_of_heq (by heq_congr) key (by heq_congr)⟩

end Stacks.Cohomology.DerivedPullbackOfToposHom

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X X' : AlgebraicSpaces B S hS}

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits
attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

/-- `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_unit_app` with the composite
read on sections. -/
private theorem modulePullbackIsoEtaleModulePullback_unit_app_val_app (a : X' ⟶ X)
    (ha : IsEtale B S hS a.hom)
    (G : Modules.{u, u} B S hS X.1 X.2) (U : (SmallEtale B S hS X'.1)ᵒᵖ)
    (m : ((inverseImageModules.{u, u, u, u + 1, u, u + 1}
      (smallEtaleRingedToposHom B S hS a).toToposHom
      (structureRingSheaf B S hS X)).obj G).val.obj U) :
    ((modulePullbackIsoEtaleModulePullback B S hS a ha).hom.app G).val.app U
        (((extendScalarsFSharpAdjunction B S hS a).unit.app
          ((inverseImageModules.{u, u, u, u + 1, u, u + 1}
            (smallEtaleRingedToposHom B S hS a).toToposHom
            (structureRingSheaf B S hS X)).obj G)).val.app U m) =
      ((etaleModuleInverseImageIsoRestrictionTransport B S hS a ha).hom.app G).val.app U m :=
  modulePullbackIsoEtaleModulePullback_unit_app B S hS a ha G U m

/-- **Stacks 03LW, canonicity, at the unit of Tag 03CZ of the morphism of ringed topoi**: the
comparison of the pullback of modules with étale restriction sends the unit of a section `m` of
the inverse image to the comparison of Stacks 03LQ applied to `m`. -/
theorem modulePullbackIsoEtaleModulePullback_hom_app_structureAdjunction_unit (a : X' ⟶ X)
    (ha : IsEtale B S hS a.hom)
    (G : SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O)))
    (U : (SmallEtale B S hS X'.1)ᵒᵖ)
    (m : ((inverseImageModules
      (smallEtaleRingedToposHom B S hS a).toRingedToposModulesHom.toToposHom
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O))).obj
        G).val.obj U) :
    ((modulePullbackIsoEtaleModulePullback B S hS a ha).hom.app G).val.app U
      (((Stacks.SheafOfModules.RingedToposPullback.structureAdjunction
          (smallEtaleRingedToposHom B S hS a).toRingedToposModulesHom).unit.app
          ((inverseImageModules
            (smallEtaleRingedToposHom B S hS a).toRingedToposModulesHom.toToposHom
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O))).obj
              G)).val.app U m) =
      ((smallToposMorphismTypeU_inverseImageIso B S hS a ha).hom.app
        (Sheaf.moduleSheaf.{u, u, u + 1}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O)) G)).hom.app
          U m :=
  modulePullbackIsoEtaleModulePullback_unit_app_val_app a ha G U m

/-- **The comparison of Stacks 03EL along an étale morphism, transported to étale restriction,
on local sections**: its inverse sends the sheafified pure tensor `s ⊗ t` of two sections of
`A|_{X'}` and `M|_{X'}` over a chart `V` of `X'` to the sheafified pure tensor `s ⊗ t` over the
composite chart of `X`. -/
theorem pullbackTensorIsoOfIso_inv_val_app_toSheafify_etale (a : X' ⟶ X) (ha : IsEtale B S hS a.hom)
    (A M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
    (V : (SmallEtale B S hS X'.1)ᵒᵖ)
    (s : ((etaleModulePullback B S hS a ha).obj A).val.obj V)
    (t : ((etaleModulePullback B S hS a ha).obj M).val.obj V) :
    ((Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackTensorIsoOfIso
        (smallEtaleRingedToposHom B S hS a)
        (pullbackModulesIsoModulePullback B S hS a ≪≫
          modulePullbackIsoEtaleModulePullback B S hS a ha)).inv.app (A, M)).val.app V
      ((Stacks.SheafOfModules.TensorSheafification.toSheafify
          (smallEtaleRingedTopos B S hS X').O.obj
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X').O)).property
          (((etaleModulePullback B S hS a ha).obj A).val ⊗
            ((etaleModulePullback B S hS a ha).obj M).val)).app V (s ⊗ₜ t)) =
    (Stacks.SheafOfModules.TensorSheafification.toSheafify
          (smallEtaleRingedTopos B S hS X).O.obj
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O)).property
          (A.val ⊗ M.val)).app
      ((smallEtalePostcomp B S hS a ha).op.obj V) (s ⊗ₜ t) := by
  have key :=
    open Stacks.Cohomology in
    DerivedPullbackOfToposHom.pullbackTensorIsoOfIso_inv_val_app_toSheafify_pushforward
    (smallEtaleRingedToposHom B S hS a)
    (smallEtalePostcomp B S hS a ha) (smallToposMorphismTypeU_inverseImageIso B S hS a ha) _
    _ (pullbackModulesIsoModulePullback_eq_eqToIso a)
    (modulePullbackIsoEtaleModulePullback B S hS a ha)
    (modulePullbackIsoEtaleModulePullback_hom_app_structureAdjunction_unit a ha) A M V s t
  exact eq_of_heq_of_eq_of_heq (by heq_congr) key (by heq_congr)

/-- **Stacks 04M0 on morphisms of restricted modules.** For an étale `a : X' ⟶ X` and a chart `U`
of `X'`, every morphism `(a^*M)|_U ⟶ (a^*K)|_U` of restricted modules is, section by section, a
unique morphism `M|_{aU} ⟶ K|_{aU}` over the slice at the composite chart. -/
theorem etaleModulePullback_restrFun_hom_existsUnique (a : X' ⟶ X) (ha : IsEtale B S hS a.hom)
    (U : (smallEtaleRingedSite B S hS X'.1 X'.2).C) (M K : Modules.{u, u} B S hS X.1 X.2)
    (ψ : (restrFun (smallEtaleRingedSite B S hS X'.1 X'.2).O.obj U).obj
        (RingedSite.valOf (smallEtaleRingedSite B S hS X'.1 X'.2)
          ((etaleModulePullback B S hS a ha).obj M)) ⟶
      (restrFun (smallEtaleRingedSite B S hS X'.1 X'.2).O.obj U).obj
        (RingedSite.valOf (smallEtaleRingedSite B S hS X'.1 X'.2)
          ((etaleModulePullback B S hS a ha).obj K))) :
    ∃! α : (restrFun (smallEtaleRingedSite B S hS X.1 X.2).O.obj
          ((ringedSitePostcomp B S hS a ha).obj U)).obj
          (RingedSite.valOf (smallEtaleRingedSite B S hS X.1 X.2) M) ⟶
        (restrFun (smallEtaleRingedSite B S hS X.1 X.2).O.obj
          ((ringedSitePostcomp B S hS a ha).obj U)).obj
          (RingedSite.valOf (smallEtaleRingedSite B S hS X.1 X.2) K),
      ∀ {T : (smallEtaleRingedSite B S hS X'.1 X'.2).C} (q : T ⟶ U)
        (y : (RingedSite.valOf (smallEtaleRingedSite B S hS X'.1 X'.2)
          ((etaleModulePullback B S hS a ha).obj M)).obj (op T)),
        AnyUniverse.sectionOfRestr (smallEtaleRingedSite B S hS X'.1 X'.2).O.obj
            (RingedSite.valOf (smallEtaleRingedSite B S hS X'.1 X'.2)
              ((etaleModulePullback B S hS a ha).obj K)) U q
            ((ψ.app (op (Over.mk q))).hom
              (AnyUniverse.restrSection (smallEtaleRingedSite B S hS X'.1 X'.2).O.obj
                (RingedSite.valOf (smallEtaleRingedSite B S hS X'.1 X'.2)
                  ((etaleModulePullback B S hS a ha).obj M))
                U q y)) =
          AnyUniverse.sectionOfRestr (smallEtaleRingedSite B S hS X.1 X.2).O.obj
            (RingedSite.valOf (smallEtaleRingedSite B S hS X.1 X.2) K)
            ((ringedSitePostcomp B S hS a ha).obj U) ((ringedSitePostcomp B S hS a ha).map q)
            ((α.app (op (Over.mk ((ringedSitePostcomp B S hS a ha).map q)))).hom
              (AnyUniverse.restrSection (smallEtaleRingedSite B S hS X.1 X.2).O.obj
                (RingedSite.valOf (smallEtaleRingedSite B S hS X.1 X.2) M)
                ((ringedSitePostcomp B S hS a ha).obj U) ((ringedSitePostcomp B S hS a ha).map q)
                y)) := by
  let E : Over U ≌ Over ((ringedSitePostcomp B S hS a ha).obj U) :=
    SmallEtale.postcompOverEquivalence B S hS a ha U
  have hc1 : E.functor.IsContinuous ((smallEtaleRingedSite B S hS X'.1 X'.2).J.over U)
      ((smallEtaleRingedSite B S hS X.1 X.2).J.over ((ringedSitePostcomp B S hS a ha).obj U)) :=
    SmallEtale.isContinuous_overPostcomp B S hS a ha U
  have hc2 : E.inverse.IsContinuous
      ((smallEtaleRingedSite B S hS X.1 X.2).J.over ((ringedSitePostcomp B S hS a ha).obj U))
      ((smallEtaleRingedSite B S hS X'.1 X'.2).J.over U) :=
    SmallEtale.isContinuous_postcompOverInverse B S hS a ha U
  let RY := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O)
  let RX := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
  let φ : RY.over U ⟶ (E.functor.sheafPushforwardContinuous RingCat.{u}
      ((smallEtaleRingedSite B S hS X'.1 X'.2).J.over U)
      ((smallEtaleRingedSite B S hS X.1 X.2).J.over ((ringedSitePostcomp B S hS a ha).obj U))).obj
      (RX.over ((ringedSitePostcomp B S hS a ha).obj U)) := 𝟙 _
  let ψ' : RX.over ((ringedSitePostcomp B S hS a ha).obj U) ⟶
      (E.inverse.sheafPushforwardContinuous RingCat.{u}
        ((smallEtaleRingedSite B S hS X.1 X.2).J.over ((ringedSitePostcomp B S hS a ha).obj U))
        ((smallEtaleRingedSite B S hS X'.1 X'.2).J.over U)).obj (RY.over U) := 𝟙 _
  have H₁ : Functor.whiskerRight (NatTrans.op E.counit)
      (RX.over ((ringedSitePostcomp B S hS a ha).obj U)).obj =
      ψ'.hom ≫ E.inverse.op.whiskerLeft φ.hom := by
    ext : 2
    exact rfl
  have H₂ : φ.hom ≫ E.functor.op.whiskerLeft ψ'.hom ≫
      Functor.whiskerRight (NatTrans.op E.unit) (RY.over U).obj = 𝟙 (RY.over U).obj := by
    ext : 2
    exact rfl
  let e₀ := SheafOfModules.pushforwardPushforwardEquivalence.{u} E φ ψ' H₁ H₂
  let hff := e₀.fullyFaithfulFunctor
  let ψs : e₀.functor.obj (M.over ((ringedSitePostcomp B S hS a ha).obj U)) ⟶
      e₀.functor.obj (K.over ((ringedSitePostcomp B S hS a ha).obj U)) := ⟨ψ⟩
  let β := hff.preimage ψs
  have hβ : e₀.functor.map β = ψs := hff.map_preimage ψs
  refine ⟨β.val, fun {T} q y ↦ ?_, fun α' hα' ↦ ?_⟩
  · exact (congrArg (fun f : e₀.functor.obj (M.over ((ringedSitePostcomp B S hS a ha).obj U)) ⟶
      e₀.functor.obj (K.over ((ringedSitePostcomp B S hS a ha).obj U)) ↦
        (f.val.app (op (Over.mk q))).hom y) hβ).symm
  · let β' : M.over ((ringedSitePostcomp B S hS a ha).obj U) ⟶
        K.over ((ringedSitePostcomp B S hS a ha).obj U) := ⟨α'⟩
    have h : e₀.functor.map β' = e₀.functor.map β := by
      rw [hβ]
      apply SheafOfModules.hom_ext
      apply _root_.PresheafOfModules.hom_ext
      intro W
      obtain ⟨W⟩ := W
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact (hα' W.hom x).symm
    exact congrArg SheafOfModules.Hom.val (hff.map_injective h)

/-- **The tensor hypothesis of the map of Stacks 08JF for étale restriction**: the comparison of
Stacks 03EL, transported to `a^*M = M|_{X'}` along Stacks 03LW, is the identity on sheafified
local pure tensors. -/
theorem pushforwardTensorCompat_etaleModulePullback (a : X' ⟶ X) (ha : IsEtale B S hS a.hom) :
    @RingedSite.PushforwardTensorCompat (smallEtaleRingedSite B S hS X'.1 X'.2)
      (smallEtaleRingedSite B S hS X.1 X.2) _ _ _ _ (smallEtalePostcomp B S hS a ha)
      (smallEtaleRingedSite_isContinuous_smallEtalePostcomp B S hS a ha)
      (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O)))
      (Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackTensorIsoOfIso
        (smallEtaleRingedToposHom B S hS a)
        (pullbackModulesIsoModulePullback B S hS a ≪≫
          modulePullbackIsoEtaleModulePullback B S hS a ha)) :=
  Stacks.Cohomology.DerivedPullbackOfToposHom.pushforwardTensorCompat_pullbackTensorIsoOfIso
    (smallEtaleRingedToposHom B S hS a)
    (smallEtalePostcomp B S hS a ha) (smallToposMorphismTypeU_inverseImageIso B S hS a ha) _
    _ (pullbackModulesIsoModulePullback_eq_eqToIso a)
    (modulePullbackIsoEtaleModulePullback B S hS a ha)
    (modulePullbackIsoEtaleModulePullback_hom_app_structureAdjunction_unit a ha)

/-- **The slice hypothesis of the map of Stacks 08JF for étale restriction** (Stacks 04M0):
morphisms of restricted modules over a slice of `X'` come from unique morphisms over the slice of
`X` at the composite chart. -/
theorem pushforwardSliceUnique_etaleModulePullback (a : X' ⟶ X) (ha : IsEtale B S hS a.hom) :
    @RingedSite.PushforwardSliceUnique (smallEtaleRingedSite B S hS X'.1 X'.2)
      (smallEtaleRingedSite B S hS X.1 X.2) (smallEtalePostcomp B S hS a ha)
      (smallEtaleRingedSite_isContinuous_smallEtalePostcomp B S hS a ha)
      (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O))) := by
  refine @RingedSite.PushforwardSliceUnique.mk _ _ _
    (smallEtaleRingedSite_isContinuous_smallEtalePostcomp B S hS a ha) _ (fun U M K ψ ↦ ?_)
  obtain ⟨α, hα, huniq⟩ := etaleModulePullback_restrFun_hom_existsUnique a ha U M K ψ
  exact ⟨α, fun q y ↦ eq_of_heq_of_eq_of_heq (by heq_congr) (hα q y) (by heq_congr),
    fun α' h' ↦ huniq α' fun q y ↦
      eq_of_heq_of_eq_of_heq (by heq_congr) (h' q y) (by heq_congr)⟩

/-- **The projection formula for extension by zero along an étale morphism.** For an étale
`a : X' ⟶ X` of algebraic spaces, the projection map `a_!(A ⊗ a^*M) ⟶ a_!A ⊗ M` is an
isomorphism: its transpose is the map `a^*H(M, K) ⟶ H(a^*M, a^*K)` of Stacks 08JF, which is
invertible on sections over every chart. -/
theorem isIso_etaleModuleLowerShriekProjectionMap (a : X' ⟶ X) (ha : IsEtale B S hS a.hom)
    (A : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X'))
    (M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :
    IsIso (etaleModuleLowerShriekProjectionMap a ha A M) := by
  have : EssentiallySmall.{u} (smallEtaleRingedSite B S hS X.1 X.2).C := by
    change EssentiallySmall.{u} (SmallEtale B S hS X.1)
    infer_instance
  have : EssentiallySmall.{u} (smallEtaleRingedSite B S hS X'.1 X'.2).C := by
    change EssentiallySmall.{u} (SmallEtale B S hS X'.1)
    infer_instance
  exact PullbackInternalHom.isIso_leftAdjointProjectionMap_of_isIso_pullbackHomMap
    (etaleModuleLowerShriekAdjunction B S hS a ha) _ _ _
    (RingedSite.internalHomSheafSmallBifunctor (smallEtaleRingedSite B S hS X.1 X.2))
    (RingedSite.internalHomSheafSmallBifunctor (smallEtaleRingedSite B S hS X'.1 X'.2))
    (fun P ↦ RingedSite.internalHomSheafSmallAdjunction _ P)
    (fun P ↦ RingedSite.internalHomSheafSmallAdjunction _ P) A M
    (@RingedSite.isIso_pullbackHomMap_internalHomSheafSmall (smallEtaleRingedSite B S hS X'.1 X'.2)
      (smallEtaleRingedSite B S hS X.1 X.2) _ _ _ _ _ _ (smallEtalePostcomp B S hS a ha)
      (smallEtaleRingedSite_isContinuous_smallEtalePostcomp B S hS a ha)
      (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O))) _
      (pushforwardTensorCompat_etaleModulePullback a ha)
      (pushforwardSliceUnique_etaleModulePullback a ha) M)

end AlgebraicGeometry.Space

end
