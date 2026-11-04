module

public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.FunctorsModuleCategories.RingActions

/-!
# Recognising a functor between module categories from its value on the regular module

A functor from `ModuleCat A` to `ModuleCat B` which preserves all colimits is determined, up to
isomorphism, by its value on the rank-one free module `A` together with the action of `A` on
that value by multiplication. This file collects the constructions that make that precise and
are used both for bimodules over `ℤ` and for algebras over a base ring.

## Main definitions

* `ModuleCat.scalarMul` and `ModuleCat.regularMul` are multiplication by a scalar on a module
  and on the rank-one free module.
* `ModuleCat.imageAction` is the induced action of `A` on the value of a right exact functor.
* `ModuleCat.isoOfRegularAction` builds an isomorphism of colimit-preserving functors out of an
  equivariant isomorphism of their values on the rank-one free module.

## Main results

* `ModuleCat.isoOfRegularAction_hom_app`: that isomorphism restricts to the given one.

## Implementation notes

Right modules over `A` are left modules over `Aᵐᵒᵖ`, so the classification of right exact
coproduct-preserving functors in `ModuleCat.functorToRingActions_isEquivalence` applies to
functors out of `ModuleCat A` only after replacing `A` by `(Aᵐᵒᵖ)ᵐᵒᵖ`. The
`doubleOpposite*` declarations carry out that replacement; `ModuleCat.isoOfRegularAction` is the
statement one actually wants, with `A` itself.

## References

* [Stacks Project, Tag 0GNS](https://stacks.math.columbia.edu/tag/0GNS)
* [Stacks Project, Tag 0GNV](https://stacks.math.columbia.edu/tag/0GNV)
-/

@[expose] public section

namespace ModuleCat

universe u

open CategoryTheory CategoryTheory.Limits

variable (A B : Type u) [CommRing A] [CommRing B]

/-- Left multiplication by a scalar on the rank-one free module. -/
public def regularMul (a : A) : ModuleCat.of A A ⟶ ModuleCat.of A A :=
  ModuleCat.ofHom (LinearMap.mulLeft A a)

/-- Multiplication by a scalar on a module, as an endomorphism in `ModuleCat A`. -/
public def scalarMul (M : ModuleCat.{u} A) (a : A) : M ⟶ M :=
  ModuleCat.ofHom (LinearMap.lsmul A M a)

/-- Multiplication by `1` is the identity. -/
public lemma scalarMul_one (M : ModuleCat.{u} A) : scalarMul A M 1 = 𝟙 M := by
  ext x
  simp [scalarMul]

/-- Multiplication by a product is the composite, in the opposite order. -/
public lemma scalarMul_mul (M : ModuleCat.{u} A) (a b : A) :
    scalarMul A M (a * b) = scalarMul A M b ≫ scalarMul A M a := by
  ext x
  simp only [ModuleCat.comp_apply, scalarMul]
  exact mul_smul a b x

/-- The action of `A` on the value of a right exact functor at an `A`-module, obtained by
applying the functor to multiplication by each scalar. -/
public noncomputable def imageAction
    (A B : Type u) [CommRing A] [CommRing B]
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B)
    [PreservesFiniteColimits F] (M : ModuleCat.{u} A) :
    A →+* Module.End B (F.obj M) := by
  letI : F.Additive :=
    rightExactFunctor_le_additiveFunctor (ModuleCat.{u} A) (ModuleCat.{u} B)
      F (show PreservesFiniteColimits F from inferInstance)
  refine {
    toFun := fun a => (F.map (scalarMul A M a)).hom
    map_one' := ?_
    map_mul' := ?_
    map_zero' := ?_
    map_add' := ?_ }
  · change (F.map (scalarMul A M 1)).hom = LinearMap.id
    rw [scalarMul_one, F.map_id]
    rfl
  · intro a b
    rw [scalarMul_mul, F.map_comp]
    rfl
  · have h : scalarMul A M (0 : A) = 0 := by
      ext x
      simp [scalarMul]
    rw [h, F.map_zero]
    rfl
  · intro a b
    have h : scalarMul A M (a + b) = scalarMul A M a + scalarMul A M b := by
      ext x
      simp [scalarMul]
    rw [h, F.map_add]
    rfl

/-- Multiplication by a scalar is natural in the module. -/
public lemma scalarMul_natural {M N : ModuleCat.{u} A} (f : M ⟶ N) (a : A) :
    scalarMul A M a ≫ f = f ≫ scalarMul A N a := by
  ext x
  exact map_smul f.hom a x

/-- On the rank-one free module, left multiplication is multiplication by a scalar. -/
public lemma regularMul_eq_scalarMul (a : A) :
    regularMul A a = scalarMul A (ModuleCat.of A A) a := by
  ext
  rfl

/-- Left `A`-modules are the same as left `(Aᵐᵒᵖ)ᵐᵒᵖ`-modules. -/
public noncomputable def doubleOppositeModuleEquivalence :
    ModuleCat.{u} (Aᵐᵒᵖ)ᵐᵒᵖ ≌ ModuleCat.{u} A :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv (RingEquiv.opOp A)

/-- The regular module of `Aᵐᵒᵖ`, transported to `ModuleCat A`, is the regular module of `A`. -/
public noncomputable def doubleOppositeRegularIso :
    (doubleOppositeModuleEquivalence A).functor.obj
        (ModuleCat.of (Aᵐᵒᵖ)ᵐᵒᵖ Aᵐᵒᵖ) ≅ ModuleCat.of A A :=
  LinearEquiv.toModuleIso {
    toFun := MulOpposite.unop
    invFun := MulOpposite.op
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- `doubleOppositeRegularIso` intertwines the two descriptions of multiplication by a scalar. -/
public lemma doubleOppositeRegularIso_natural (a : A) :
    (doubleOppositeModuleEquivalence A).functor.map
        (regularModuleLeftMul Aᵐᵒᵖ (MulOpposite.op a)) ≫
          (doubleOppositeRegularIso A).hom =
      (doubleOppositeRegularIso A).hom ≫ regularMul A a := by
  ext x
  exact mul_comm x.unop a

/-- A colimit-preserving functor out of `ModuleCat A`, regarded as a right exact
coproduct-preserving functor out of `ModuleCat (Aᵐᵒᵖ)ᵐᵒᵖ`. -/
public noncomputable def doubleOppositePrecomposeObject
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B) [PreservesColimits F] :
    RightExactCoproductPreservingFunctor Aᵐᵒᵖ (ModuleCat.{u} B) := by
  haveI : PreservesColimits (doubleOppositeModuleEquivalence A).functor := by infer_instance
  haveI : PreservesColimits ((doubleOppositeModuleEquivalence A).functor ⋙ F) := by
    infer_instance
  exact ⟨(doubleOppositeModuleEquivalence A).functor ⋙ F,
    ⟨inferInstance, fun _ => inferInstance⟩⟩

/-- An isomorphism of the values of two functors at the regular module which respects the action
of the ring is an isomorphism of the associated objects with a ring action. -/
public noncomputable def doubleOppositeActionIso
    (F G : ModuleCat.{u} A ⥤ ModuleCat.{u} B)
    [PreservesColimits F] [PreservesColimits G]
    (e : F.obj ((doubleOppositeModuleEquivalence A).functor.obj
        (ModuleCat.of (Aᵐᵒᵖ)ᵐᵒᵖ Aᵐᵒᵖ)) ≅
      G.obj ((doubleOppositeModuleEquivalence A).functor.obj
        (ModuleCat.of (Aᵐᵒᵖ)ᵐᵒᵖ Aᵐᵒᵖ)))
    (he : ∀ a : Aᵐᵒᵖ,
      F.map ((doubleOppositeModuleEquivalence A).functor.map
          (regularModuleLeftMul Aᵐᵒᵖ a)) ≫ e.hom =
        e.hom ≫ G.map ((doubleOppositeModuleEquivalence A).functor.map
          (regularModuleLeftMul Aᵐᵒᵖ a))) :
    (functorToRingActions Aᵐᵒᵖ (ModuleCat.{u} B)).obj
        (doubleOppositePrecomposeObject A B F) ≅
      (functorToRingActions Aᵐᵒᵖ (ModuleCat.{u} B)).obj
        (doubleOppositePrecomposeObject A B G) := by
  apply (CategoryTheory.additiveFunctor (SingleObj Aᵐᵒᵖ) (ModuleCat.{u} B)).isoMk
  refine NatIso.ofComponents (fun X => ?_) ?_
  · cases X
    exact e
  · intro X Y f
    cases X
    cases Y
    exact he f

/-- Two colimit-preserving functors out of `ModuleCat A` agreeing equivariantly on the regular
module of `(Aᵐᵒᵖ)ᵐᵒᵖ` are isomorphic. -/
public noncomputable def isoOfDoubleOppositeAction
    (F G : ModuleCat.{u} A ⥤ ModuleCat.{u} B)
    [PreservesColimits F] [PreservesColimits G]
    (e : F.obj ((doubleOppositeModuleEquivalence A).functor.obj
        (ModuleCat.of (Aᵐᵒᵖ)ᵐᵒᵖ Aᵐᵒᵖ)) ≅
      G.obj ((doubleOppositeModuleEquivalence A).functor.obj
        (ModuleCat.of (Aᵐᵒᵖ)ᵐᵒᵖ Aᵐᵒᵖ)))
    (he : ∀ a : Aᵐᵒᵖ,
      F.map ((doubleOppositeModuleEquivalence A).functor.map
          (regularModuleLeftMul Aᵐᵒᵖ a)) ≫ e.hom =
        e.hom ≫ G.map ((doubleOppositeModuleEquivalence A).functor.map
          (regularModuleLeftMul Aᵐᵒᵖ a))) : F ≅ G := by
  let H := functorToRingActions Aᵐᵒᵖ (ModuleCat.{u} B)
  haveI : H.IsEquivalence := functorToRingActions_isEquivalence Aᵐᵒᵖ _
  let e₁ := (H.asEquivalence.fullyFaithfulFunctor.isoEquiv).symm
    (doubleOppositeActionIso A B F G e he)
  let e₂ := (isRightExactAndPreservesCoproducts Aᵐᵒᵖ (ModuleCat.{u} B)).ι.mapIso e₁
  let W := (Functor.whiskeringLeft
    (ModuleCat.{u} (Aᵐᵒᵖ)ᵐᵒᵖ) (ModuleCat.{u} A) (ModuleCat.{u} B)).obj
      (doubleOppositeModuleEquivalence A).functor
  haveI : W.IsEquivalence := inferInstance
  exact (W.asEquivalence.fullyFaithfulFunctor.isoEquiv).symm e₂

/-- Two colimit-preserving functors out of `ModuleCat A` agreeing on the regular module,
compatibly with multiplication by scalars, are isomorphic. -/
public noncomputable def isoOfRegularAction
    (F G : ModuleCat.{u} A ⥤ ModuleCat.{u} B)
    [PreservesColimits F] [PreservesColimits G]
    (e : F.obj (ModuleCat.of A A) ≅ G.obj (ModuleCat.of A A))
    (he : ∀ a : A,
      F.map (regularMul A a) ≫ e.hom = e.hom ≫ G.map (regularMul A a)) : F ≅ G := by
  let r := doubleOppositeRegularIso A
  let e' := F.mapIso r ≪≫ e ≪≫ (G.mapIso r).symm
  apply isoOfDoubleOppositeAction A B F G e'
  intro a
  have hr := doubleOppositeRegularIso_natural A a.unop
  change (doubleOppositeModuleEquivalence A).functor.map
      (regularModuleLeftMul Aᵐᵒᵖ a) ≫ r.hom =
    r.hom ≫ regularMul A a.unop at hr
  have hF := congrArg F.map hr
  have hG := congrArg G.map hr
  dsimp [e']
  rw [← Category.assoc (F.map _) (F.map r.hom) (e.hom ≫ G.map r.inv)]
  rw [← F.map_comp, hr, F.map_comp]
  simp only [← Category.assoc]
  rw [Category.assoc (F.map r.hom) (F.map (regularMul A a.unop)) e.hom]
  rw [he a.unop]
  simp only [← Category.assoc]
  have hr' : regularMul A a.unop ≫ r.inv =
      r.inv ≫ (doubleOppositeModuleEquivalence A).functor.map
        (regularModuleLeftMul Aᵐᵒᵖ a) := by
    calc
      regularMul A a.unop ≫ r.inv =
          (r.inv ≫ r.hom) ≫ regularMul A a.unop ≫ r.inv := by simp
      _ = r.inv ≫ (r.hom ≫ regularMul A a.unop) ≫ r.inv := by simp [Category.assoc]
      _ = r.inv ≫ ((doubleOppositeModuleEquivalence A).functor.map
          (regularModuleLeftMul Aᵐᵒᵖ a) ≫ r.hom) ≫ r.inv := by rw [← hr]
      _ = r.inv ≫ (doubleOppositeModuleEquivalence A).functor.map
          (regularModuleLeftMul Aᵐᵒᵖ a) := by simp [Category.assoc]
  rw [Category.assoc (F.map r.hom ≫ e.hom) (G.map (regularMul A a.unop)) (G.map r.inv)]
  rw [← G.map_comp, hr', G.map_comp]
  simp only [Category.assoc]

/-- The isomorphism of `isoOfRegularAction` restricts on the regular module to the given one. -/
public lemma isoOfRegularAction_hom_app
    (F G : ModuleCat.{u} A ⥤ ModuleCat.{u} B)
    [PreservesColimits F] [PreservesColimits G]
    (e : F.obj (ModuleCat.of A A) ≅ G.obj (ModuleCat.of A A))
    (he : ∀ a : A,
      F.map (regularMul A a) ≫ e.hom = e.hom ≫ G.map (regularMul A a)) :
    (isoOfRegularAction A B F G e he).hom.app (ModuleCat.of A A) = e.hom := by
  let U := (doubleOppositeModuleEquivalence A).functor
  let Y := ModuleCat.of (Aᵐᵒᵖ)ᵐᵒᵖ Aᵐᵒᵖ
  let r := doubleOppositeRegularIso A
  let e' := F.mapIso r ≪≫ e ≪≫ (G.mapIso r).symm
  let H := functorToRingActions Aᵐᵒᵖ (ModuleCat.{u} B)
  have : H.IsEquivalence := functorToRingActions_isEquivalence Aᵐᵒᵖ _
  have hAction : ∀ a : Aᵐᵒᵖ,
      F.map ((doubleOppositeModuleEquivalence A).functor.map
        (regularModuleLeftMul Aᵐᵒᵖ a)) ≫ e'.hom =
        e'.hom ≫ G.map ((doubleOppositeModuleEquivalence A).functor.map
          (regularModuleLeftMul Aᵐᵒᵖ a)) := by
    intro a
    have hr := doubleOppositeRegularIso_natural A a.unop
    change (doubleOppositeModuleEquivalence A).functor.map
        (regularModuleLeftMul Aᵐᵒᵖ a) ≫ r.hom =
      r.hom ≫ regularMul A a.unop at hr
    have hr' : regularMul A a.unop ≫ r.inv =
        r.inv ≫ (doubleOppositeModuleEquivalence A).functor.map
          (regularModuleLeftMul Aᵐᵒᵖ a) := by
      calc
        regularMul A a.unop ≫ r.inv =
            (r.inv ≫ r.hom) ≫ regularMul A a.unop ≫ r.inv := by simp
        _ = r.inv ≫ (r.hom ≫ regularMul A a.unop) ≫ r.inv := by simp [Category.assoc]
        _ = r.inv ≫ ((doubleOppositeModuleEquivalence A).functor.map
            (regularModuleLeftMul Aᵐᵒᵖ a) ≫ r.hom) ≫ r.inv := by
          rw [← hr]
        _ = r.inv ≫ (doubleOppositeModuleEquivalence A).functor.map
            (regularModuleLeftMul Aᵐᵒᵖ a) := by simp [Category.assoc]
    dsimp [e']
    rw [← Category.assoc, ← F.map_comp, hr, F.map_comp]
    simp only [← Category.assoc]
    rw [Category.assoc (F.map r.hom) (F.map (regularMul A a.unop)) e.hom]
    rw [he a.unop]
    simp only [← Category.assoc]
    rw [Category.assoc (F.map r.hom ≫ e.hom) (G.map (regularMul A a.unop)) (G.map r.inv)]
    rw [← G.map_comp, hr', G.map_comp]
    simp only [Category.assoc]
  let hIso := doubleOppositeActionIso A B F G e' hAction
  let e₁ := (H.asEquivalence.fullyFaithfulFunctor.isoEquiv).symm hIso
  let e₂ := (isRightExactAndPreservesCoproducts Aᵐᵒᵖ
      (ModuleCat.{u} B)).ι.mapIso e₁
  let W := (Functor.whiskeringLeft
    (ModuleCat.{u} (Aᵐᵒᵖ)ᵐᵒᵖ) (ModuleCat.{u} A) (ModuleCat.{u} B)).obj U
  have : W.IsEquivalence := inferInstance
  let α := (W.asEquivalence.fullyFaithfulFunctor.isoEquiv).symm e₂
  have hH : H.mapIso e₁ = hIso :=
    (H.asEquivalence.fullyFaithfulFunctor.isoEquiv).apply_symm_apply hIso
  have hHapp := congrArg (fun z => z.hom.hom.app (SingleObj.star Aᵐᵒᵖ)) hH
  have hE₂ : e₂.hom.app Y = e₁.hom.hom.app Y := rfl
  have hHapp' : e₁.hom.hom.app Y = e'.hom := hHapp
  have hW : W.mapIso α = e₂ :=
    (W.asEquivalence.fullyFaithfulFunctor.isoEquiv).apply_symm_apply e₂
  have hWapp := congrArg (fun z => z.hom.app Y) hW
  have hAt₁ : α.hom.app (U.obj Y) = e₁.hom.hom.app Y := by
    rw [← hE₂]
    simpa [W] using hWapp
  have hreg : e'.hom ≫ G.map r.hom = F.map r.hom ≫ α.hom.app (ModuleCat.of A A) := by
    rw [← hAt₁.trans hHapp']
    exact (α.hom.naturality r.hom).symm
  have hreg' : F.map r.hom ≫ e.hom = F.map r.hom ≫ α.hom.app (ModuleCat.of A A) := by
    simpa [e', Category.assoc] using hreg
  show α.hom.app (ModuleCat.of A A) = e.hom
  exact ((cancel_epi (F.map r.hom)).mp hreg').symm

end ModuleCat
