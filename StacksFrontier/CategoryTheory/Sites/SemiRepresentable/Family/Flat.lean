module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposFlat
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.Family.Morphism
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced

/-!
# Flatness of a morphism between ringed semi-representable localizations

The morphism of ringed topoi induced by a morphism of semi-representable objects is flat: its
structure map in inverse-image form is an isomorphism, and a morphism of sheaves of commutative
rings that is an isomorphism is flat, because the rank-one module it makes of its target is the
rank-one module of its source and tensoring with that is the identity functor.

## Main results

* `AlgebraicGeometry.RingedSite.familyMorphism_isFlat`: the induced morphism of ringed topoi is
  flat.

## Implementation notes

`isFlatMap_of_isIso` is the general statement that an isomorphism of sheaves of commutative
rings is flat; it is proved here because it is what the flatness of this particular morphism
rests on, and nothing in the development states it.

The sheaf of rings underlying `O` is `Stacks.SheafOfModules.Tensor.ringSheaf O`, which is built
from the underlying presheaf and the sheaf condition rather than as an image of `sheafCompose`.
Two instances therefore have to be supplied by hand instead of by `infer_instance`: the
isomorphy of the induced morphism of sheaves of rings, whose head is `sheafCompose` and so does
not match at instance transparency, and the fact that `SheafOfModules.forget` reflects
isomorphisms, whose search does not terminate at that spelling of the sheaf of rings.

## References

* [Stacks Project, Tag 0D9U](https://stacks.math.columbia.edu/tag/0D9U)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
* [Stacks Project, Tag 04JB](https://stacks.math.columbia.edu/tag/04JB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.SheafOfModules (ringPresheaf)

namespace AlgebraicGeometry.SheafOfModules

universe v u w

/-- Restriction of scalars along the identity of a presheaf of rings is the identity
functor. -/
noncomputable def presheafRestrictScalarsIdIso
    {C : Type u} [Category.{v, u} C] (R : Cᵒᵖ ⥤ RingCat.{w}) :
    _root_.PresheafOfModules.restrictScalars (𝟙 R) ≅ 𝟭 (_root_.PresheafOfModules R) := by
  let appIso (M : _root_.PresheafOfModules R) :
      _root_.PresheafOfModules.restrictScalarsObj M (𝟙 R) ≅ M := by
    refine {
      hom := {
        app := fun V =>
          (ModuleCat.restrictScalarsId'App
            (RingCat.Hom.hom ((𝟙 R : R ⟶ R).app V)) rfl (M.obj V)).hom
        naturality := by
          intro V W a
          apply ModuleCat.hom_ext
          rfl }
      inv := {
        app := fun V =>
          (ModuleCat.restrictScalarsId'App
            (RingCat.Hom.hom ((𝟙 R : R ⟶ R).app V)) rfl (M.obj V)).inv
        naturality := by
          intro V W a
          apply ModuleCat.hom_ext
          rfl }
      hom_inv_id := by
        apply _root_.PresheafOfModules.hom_ext
        intro V
        ext x
        change (ModuleCat.restrictScalars
            (RingCat.Hom.hom ((𝟙 R : R ⟶ R).app V))).obj (M.obj V) at x
        rfl
      inv_hom_id := by
        apply _root_.PresheafOfModules.hom_ext
        intro V
        ext x
        rfl }
  refine NatIso.ofComponents appIso ?_
  intro M N a
  apply _root_.PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  rfl

/-- The restriction of scalars along `α` of the rank-one module of the target. -/
private noncomputable abbrev restrictUnit {C : Type u} [Category.{v, u} C]
    {J : GrothendieckTopology C} {R R' : Sheaf J RingCat.{w}} (α : R ⟶ R') :
    _root_.SheafOfModules R :=
  (_root_.SheafOfModules.restrictScalars α).obj (_root_.SheafOfModules.unit R')

/-- The morphism from the rank-one module to the restriction of scalars of the rank-one module of
the target, sending `1` to `1`. -/
private noncomputable def unitToRestrictUnit {C : Type u} [Category.{v, u} C]
    {J : GrothendieckTopology C} {R R' : Sheaf J RingCat.{w}} (α : R ⟶ R') :
    _root_.SheafOfModules.unit R ⟶ restrictUnit α :=
  (restrictUnit α).unitHomEquiv.symm
    (_root_.PresheafOfModules.sectionsMk (fun V => (1 : R'.obj.obj V))
      (fun _ _ a => (R'.obj.map a).hom.map_one))

/-- Over an isomorphism of sheaves of rings, the morphism from the rank-one module to the
restriction of scalars of the rank-one module sending `1` to `1` is an isomorphism. -/
private theorem isIso_unitToRestrictUnit_of_isIso {C : Type u} [Category.{v, u} C]
    {J : GrothendieckTopology C} {R R' : Sheaf J RingCat.{w}} (α : R ⟶ R') [IsIso α] :
    IsIso (unitToRestrictUnit α) := by
  let F := restrictUnit α
  let s : F.sections := _root_.PresheafOfModules.sectionsMk (fun V => (1 : R'.obj.obj V))
    (fun _ _ a => (R'.obj.map a).hom.map_one)
  let e := unitToRestrictUnit α
  have hpre : IsIso ((_root_.PresheafOfModules.toPresheaf R.obj).map
      ((_root_.SheafOfModules.forget R).map e)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro V
    have hcomp : ∀ r : R.obj.obj V,
        (e.val.app V) r = ((α.hom.app V) r : F.val.obj V) := by
      intro r
      let : Module (R.obj.obj V) (F.val.obj V) := (F.val.obj V).isModule
      have h1 : (e.val.app V) (1 : R.obj.obj V) = s.eval V :=
        (_root_.SheafOfModules.unitHomEquiv_apply_coe F e V).symm.trans
          (congrArg (fun t : F.sections => t.val V) (by simp [e, unitToRestrictUnit, s, F]))
      have hlin : (e.val.app V) r = r • s.eval V := by
        calc
          (e.val.app V) r = (e.val.app V) (r • (1 : R.obj.obj V)) := by simp
          _ = r • (e.val.app V) (1 : R.obj.obj V) :=
            (e.val.app V).hom.map_smul r (1 : R.obj.obj V)
          _ = r • s.eval V := by rw [h1]
      rw [hlin]
      dsimp [s, _root_.PresheafOfModules.sectionsMk, F,
        _root_.PresheafOfModules.restrictScalarsObj]
      change (α.hom.app V r) * 1 = (α.hom.app V r)
      simp
    have heq : (forget₂ RingCat AddCommGrpCat).map (α.hom.app V) =
        ((_root_.PresheafOfModules.toPresheaf R.obj).map
          ((_root_.SheafOfModules.forget R).map e)).app V := by
      ext r
      exact (hcomp r).symm
    rw [← heq]
    exact Functor.map_isIso (forget₂ RingCat AddCommGrpCat) (α.hom.app V)
  have : IsIso ((_root_.SheafOfModules.forget R).map e) :=
    isIso_of_reflects_iso ((_root_.SheafOfModules.forget R).map e)
      (_root_.PresheafOfModules.toPresheaf R.obj)
  have : (_root_.SheafOfModules.forget R).ReflectsIsomorphisms :=
    (_root_.SheafOfModules.fullyFaithfulForget R).reflectsIsomorphisms
  exact isIso_of_reflects_iso e (_root_.SheafOfModules.forget R)

/-- Sheafifying after an endofunctor of presheaves of modules that is isomorphic to restriction
of scalars along the identity is the identity functor of sheaves of modules. -/
private noncomputable def forgetCompSheafificationIso {C : Type u} [Category.{v, u} C]
    {J : GrothendieckTopology C} [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify J AddCommGrpCat.{w}] {R : Sheaf J RingCat.{w}}
    {T : _root_.PresheafOfModules.{w} R.obj ⥤ _root_.PresheafOfModules.{w} R.obj}
    (hT : T ≅ _root_.PresheafOfModules.restrictScalars (𝟙 R.obj)) :
    _root_.SheafOfModules.forget R ⋙ T ⋙ _root_.PresheafOfModules.sheafification (𝟙 R.obj) ≅
      𝟭 _ := by
  let S := _root_.PresheafOfModules.sheafification (𝟙 R.obj)
  let adj := _root_.PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  let η : ∀ M : _root_.SheafOfModules R,
      ((_root_.SheafOfModules.forget R ⋙ T ⋙ S).obj M) ≅ M := fun M =>
    (S.mapIso (hT.app ((_root_.SheafOfModules.forget R).obj M))).trans
      (asIso (adj.counit.app M))
  exact NatIso.ofComponents η (by
    intro M N a
    dsimp only [η]
    let b := (_root_.SheafOfModules.forget R).map a
    calc
      S.map (T.map b) ≫ S.map (hT.hom.app ((_root_.SheafOfModules.forget R).obj N)) ≫
          adj.counit.app N =
          S.map (T.map b ≫ hT.hom.app ((_root_.SheafOfModules.forget R).obj N)) ≫
            adj.counit.app N := by
              rw [← Category.assoc, ← S.map_comp]
      _ = S.map (hT.hom.app ((_root_.SheafOfModules.forget R).obj M) ≫
          (_root_.PresheafOfModules.restrictScalars (𝟙 R.obj)).map b) ≫
            adj.counit.app N := by rw [← hT.hom.naturality b]
      _ = S.map (hT.hom.app ((_root_.SheafOfModules.forget R).obj M)) ≫
          S.map ((_root_.PresheafOfModules.restrictScalars (𝟙 R.obj)).map b) ≫
            adj.counit.app N := by rw [S.map_comp, Category.assoc]
      _ = S.map (hT.hom.app ((_root_.SheafOfModules.forget R).obj M)) ≫
          (adj.counit.app M ≫ a) := by
            congr 1
            simpa [Functor.comp_map, b] using adj.counit.naturality a)

/-- **Stacks 03ER.** An isomorphism of sheaves of commutative rings is a flat morphism: the
rank-one module it makes of its target, restricted along itself, is the rank-one module of its
source, and tensoring with that is the identity functor. -/
theorem isFlatMap_of_isIso {C : Type u} [Category.{v, u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify J AddCommGrpCat.{w}]
    {O O' : Sheaf J CommRingCat.{w}} (g : O ⟶ O') [IsIso g] :
    IsFlatMap.{v, u, w} g := by
  let R := Stacks.SheafOfModules.Tensor.ringSheaf O
  let R' := Stacks.SheafOfModules.Tensor.ringSheaf O'
  let α : R ⟶ R' := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map g
  have : IsIso α :=
    Functor.map_isIso (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})) g
  let F := restrictUnit α
  let e := unitToRestrictUnit α
  have he : IsIso e := isIso_unitToRestrictUnit_of_isIso α
  change IsFlat (O := O) F
  unfold IsFlat
  let T : _root_.PresheafOfModules R.obj ⥤ _root_.PresheafOfModules R.obj :=
    PresheafOfModules.tensorRight (O := O.obj) F.val
  let S := _root_.PresheafOfModules.sheafification (𝟙 R.obj)
  change exactFunctor _ _ (_root_.SheafOfModules.forget R ⋙ T ⋙ S)
  let : MonoidalCategory (_root_.PresheafOfModules R.obj) := by
    change MonoidalCategory (_root_.PresheafOfModules (ringPresheaf O.obj))
    infer_instance
  have hT : T ≅ _root_.PresheafOfModules.restrictScalars (𝟙 R.obj) := by
    change MonoidalCategory.tensorRight F.val ≅
      _root_.PresheafOfModules.restrictScalars (𝟙 R.obj)
    let e' : _root_.PresheafOfModules.unit R.obj ≅ F.val :=
      (_root_.SheafOfModules.forget R).mapIso (asIso e)
    have hTF : MonoidalCategory.tensorRight F.val ≅
        MonoidalCategory.tensorRight (_root_.PresheafOfModules.unit R.obj) :=
      NatIso.ofComponents
        (fun M => (MonoidalCategory.tensorLeft M).mapIso e'.symm)
        (fun a => (MonoidalCategory.whisker_exchange a e'.inv).symm)
    have hU : MonoidalCategory.tensorRight
        (_root_.PresheafOfModules.unit R.obj) ≅ 𝟭 (_root_.PresheafOfModules R.obj) := by
      change MonoidalCategory.tensorUnitRight (_root_.PresheafOfModules R.obj) ≅ _
      exact MonoidalCategory.rightUnitorNatIso (_root_.PresheafOfModules R.obj)
    exact hTF.trans (hU.trans (presheafRestrictScalarsIdIso R.obj).symm)
  have hid : _root_.SheafOfModules.forget R ⋙ T ⋙ S ≅ 𝟭 _ := forgetCompSheafificationIso hT
  exact (exactFunctor_iff _).mpr ⟨preservesFiniteLimits_of_natIso hid.symm,
    preservesFiniteColimits_of_natIso hid.symm⟩

end AlgebraicGeometry.SheafOfModules

namespace AlgebraicGeometry.RingedSite

universe w v u r

open CategoryTheory.SemiRepresentable

attribute [local instance] componentwiseTopology_hasSheafCompose_forget₂

/-- **Stacks 0D9U.** The morphism of ringed topoi induced by a morphism of semi-representable
objects is flat. -/
@[stacks 0D9U "f_flat"]
theorem familyMorphism_isFlat (X : RingedSite.{u, v, max u v w r})
    {K L : FormalCoproduct.{w} X.C} (f : K ⟶ L) :
    Stacks.Sheaf.RingedToposFlat.RingedToposHom.IsFlat.{max u v w, max u v w,
        max u v w r, max u v w, max u v w, max u v w r}
      (familyMorphism.{w, v, u, r} X f).val := by
  have : IsIso (familyMorphism.{w, v, u, r} X f).val.fSharpInverseImage :=
    (familyMorphism.{w, v, u, r} X f).property.2.2
  have : HasSheafify (componentwiseTopology X.J K) AddCommGrpCat.{max u v w r} :=
    Stacks.Sheaf.RingedToposFlat.hasSheafify_addCommGrp.{max u v w, max u v w,
      max u v w r} _
  have : (componentwiseTopology X.J K).WEqualsLocallyBijective
      AddCommGrpCat.{max u v w r} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v w r,
      max u v w, max u v w} _
  unfold Stacks.Sheaf.RingedToposFlat.RingedToposHom.IsFlat
    Stacks.Sheaf.RingedToposFlat.IsFlatMap
  exact SheafOfModules.isFlatMap_of_isIso
    ((Stacks.Sheaf.RingedToposFlat.sheafULift.{max u v w, max u v w, max u v w r}
      (componentwiseTopology X.J K)).map
      (familyMorphism.{w, v, u, r} X f).val.fSharpInverseImage)

end AlgebraicGeometry.RingedSite

end
