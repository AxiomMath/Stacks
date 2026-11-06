module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothPresentationQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.CategoryTheory.FiberedCategory.RelocalizeElementsProjection
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRestrict
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverBase
public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.RepresentableBySpace.Basic
public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.SectionBasedFunctor

/-!
# Quasi-compact morphisms of algebraic stacks

A 1-morphism of algebraic stacks over `S` which is representable by algebraic spaces carries two
quasi-compactness conditions, and Tag 050T says they agree. One is the relative property of
Properties of Stacks, Section 04XB at `AlgebraicGeometry.Space.IsQuasiCompact`: every algebraic
space representing a base change of the 1-morphism along a scheme-valued point of its target is
quasi-compact over that point. The other is Tag 050U: every base change of the 1-morphism by a
quasi-compact algebraic stack is a quasi-compact algebraic stack.

## Main definitions

* `AlgebraicGeometry.Stack.IsQuasiCompactMorphism`: quasi-compactness of a 1-morphism of
  algebraic stacks.

## Main results

* `AlgebraicGeometry.Stack.isQuasiCompact_iff_baseChange_quasiCompact`: the two conditions
  agree.

## References

* [Stacks Project, Tag 050T](https://stacks.math.columbia.edu/tag/050T)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w v₁ u₁

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A 1-morphism of algebraic stacks over `S` is *quasi-compact* when every base change of it by
a quasi-compact algebraic stack is again a quasi-compact algebraic stack, the fibre product being
the canonical 2-fibre product of algebraic stacks and quasi-compactness being
`AlgebraicGeometry.Stack.IsQuasiCompactStack`. -/
@[stacks 050U]
abbrev IsQuasiCompactMorphism {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ (𝒵 : AlgebraicStacks.{u, w} B S hS) (g : 𝒵 ⟶ 𝒴),
    IsQuasiCompactStack.{u, w} B S hS 𝒵.val 𝒵.property →
      IsQuasiCompactStack.{u, w} B S hS
        (twoFibreProductAlgebraicStack B S hS g f).val
        (twoFibreProductAlgebraicStack B S hS g f).property

/-- The source of a quasi-compact morphism into a quasi-compact algebraic space is
quasi-compact. -/
private theorem isQuasiCompact_source_of_isQuasiCompact
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hG : IsAlgebraicSpace B S hS G)
    (hGqc : Space.IsQuasiCompactSpace B S hS G) (f : F ⟶ G)
    (hf : Space.IsQuasiCompact B S hS f) :
    Space.IsQuasiCompactSpace B S hS F :=
  Space.isQuasiCompactSpace_of_iso B S hS (asIso (pullback.snd (𝟙 G) f)) (hf G hG hGqc (𝟙 G))

/-- A functor over `Over U` composed with the iterated-slice identification lies over the
structure morphism of `U`. -/
private theorem iteratedSliceBackward_comp_eq {C : Type*} [Category C] {S : C} (U : Over S)
    {D : Type*} [Category D] (G : Over U ⥤ D) (p : D ⥤ Over S) (h : G ⋙ p = Over.forget U) :
    (Over.iteratedSliceBackward U ⋙ G) ⋙ p = Over.map U.hom :=
  (Functor.assoc _ _ _).trans
    ((congrArg (fun q => Over.iteratedSliceBackward U ⋙ q) h).trans
      (Over.iteratedSliceBackward_forget U))

/-- The 1-morphism from the 2-fibre product taken over a scheme-valued point of `𝒵` to the
2-fibre product taken over `𝒵`. Let `a` be a 1-morphism to `𝒵` from the stack of a scheme `U`
over `S`, and let `g : 𝒵 ⟶ 𝒴` and `f : 𝒳 ⟶ 𝒴`. Composing `a` with the iterated-slice
identification of the big fppf site of `U` with the slice of the site over `U` turns `a` into a
scheme-valued point of `𝒴`; the 2-fibre product of `f` with that point then maps to the 2-fibre
product of `g` and `f`, with first leg the first projection followed by `a`, second leg the
second projection, and comparison 2-cell the one the local 2-fibre product already carries. -/
private def localTwoFibreProductToGlobal
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)
    {𝒵 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (a : (schemeFibredCategory B S hS U).val ⥤ᵇ 𝒵.val.val)
    (g : 𝒵 ⟶ 𝒴) (f : 𝒳 ⟶ 𝒴) :
    let y := Over.iteratedSliceBackward U ⋙ a.toFunctor ⋙
      CatFiberedInGroupoids.homFunctor g.hom
    TwoFibreProductOver (Over.map U.hom) 𝒳.val.val.p 𝒴.val.val.p y
      (CatFiberedInGroupoids.homFunctor f.hom) ⥤
    TwoFibreProductOver 𝒵.val.val.p 𝒳.val.val.p 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor g.hom) (CatFiberedInGroupoids.homFunctor f.hom) := by
  dsimp
  let y := Over.iteratedSliceBackward U ⋙ a.toFunctor ⋙
    CatFiberedInGroupoids.homFunctor g.hom
  let P := TwoFibreProductOver (Over.map U.hom) 𝒳.val.val.p 𝒴.val.val.p y
    (CatFiberedInGroupoids.homFunctor f.hom)
  let H : P ⥤ 𝒵.val.val.obj :=
    TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p 𝒴.val.val.p y
      (CatFiberedInGroupoids.homFunctor f.hom) ⋙
      Over.iteratedSliceBackward U ⋙ a.toFunctor
  let K : P ⥤ 𝒳.val.val.obj :=
    TwoFibreProductOver.snd (Over.map U.hom) 𝒳.val.val.p 𝒴.val.val.p y
      (CatFiberedInGroupoids.homFunctor f.hom)
  have hHbase := iteratedSliceBackward_comp_eq U a.toFunctor 𝒵.val.val.p (a.w.trans rfl)
  have hH : H ⋙ 𝒵.val.val.p =
      TwoFibreProductOver.structureFunctor (Over.map U.hom) 𝒳.val.val.p 𝒴.val.val.p y
        (CatFiberedInGroupoids.homFunctor f.hom) := by
    dsimp [H]
    rw [Functor.assoc, hHbase]
    exact TwoFibreProductOver.fst_comp_eq (p𝒳 := Over.map U.hom)
      (p𝒴 := 𝒳.val.val.p) (p𝒮 := 𝒴.val.val.p) (F := y)
      (G := CatFiberedInGroupoids.homFunctor f.hom)
  have hK : K ⋙ 𝒳.val.val.p =
      TwoFibreProductOver.structureFunctor (Over.map U.hom) 𝒳.val.val.p 𝒴.val.val.p y
        (CatFiberedInGroupoids.homFunctor f.hom) :=
    TwoFibreProductOver.snd_comp_eq
  let t : H ⋙ CatFiberedInGroupoids.homFunctor g.hom ≅
      K ⋙ CatFiberedInGroupoids.homFunctor f.hom :=
    TwoFibreProductOver.psiIso (Over.map U.hom) 𝒳.val.val.p 𝒴.val.val.p y
      (CatFiberedInGroupoids.homFunctor f.hom)
  have ht : ∀ x, 𝒴.val.val.p.IsHomLift
      (𝟙 ((TwoFibreProductOver.structureFunctor (Over.map U.hom) 𝒳.val.val.p
        𝒴.val.val.p y (CatFiberedInGroupoids.homFunctor f.hom)).obj x))
      (t.hom.app x) := by
    intro x
    change 𝒴.val.val.p.IsHomLift (𝟙 x.base) x.iso.hom
    exact TwoFibreProductOver.psiIso_hom_vertical (p𝒳 := Over.map U.hom)
      (p𝒴 := 𝒳.val.val.p) (p𝒮 := 𝒴.val.val.p)
      (F := y) (G := CatFiberedInGroupoids.homFunctor f.hom) x
  exact TwoFibreProductOver.lift 𝒵.val.val.p 𝒳.val.val.p 𝒴.val.val.p
    (CatFiberedInGroupoids.homFunctor g.hom) (CatFiberedInGroupoids.homFunctor f.hom)
    (TwoFibreProductOver.structureFunctor (Over.map U.hom) 𝒳.val.val.p 𝒴.val.val.p y
      (CatFiberedInGroupoids.homFunctor f.hom)) H K hH hK t ht

/-- `AlgebraicGeometry.Stack.localTwoFibreProductToGlobal` is strictly over the site: its
composite with the structure functor of the target is the structure functor of the source. -/
private theorem localTwoFibreProductToGlobal_comp_projection
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)
    {𝒵 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (a : (schemeFibredCategory B S hS U).val ⥤ᵇ 𝒵.val.val)
    (g : 𝒵 ⟶ 𝒴) (f : 𝒳 ⟶ 𝒴) :
    localTwoFibreProductToGlobal B S hS U a g f ⋙
        (twoFibreProductAlgebraicStack B S hS g f).val.val.p =
      TwoFibreProductOver.structureFunctor (Over.map U.hom) 𝒳.val.val.p 𝒴.val.val.p
        (Over.iteratedSliceBackward U ⋙ a.toFunctor ⋙
          CatFiberedInGroupoids.homFunctor g.hom)
        (CatFiberedInGroupoids.homFunctor f.hom) :=
  rfl

/-- The 1-morphism to the 2-fibre product of `g` and `f` from an algebraic space representing a
fibre of `f` over a scheme-valued point of `𝒵`. Suppose the first projection of the 2-fibre
product of `f` with the point `a` of Stacks 04XB is equivalent, over the slice of the site at
`U`, to the category of elements of a presheaf `F` on that slice. The 1-morphism goes from the
category of elements of the lower-shriek extension of `F` along the structure morphism of `U`,
and is `CategoryTheory.PresheafOfCategories.elementsToRelocalize` followed by the inverse of the
representing equivalence and by `AlgebraicGeometry.Stack.localTwoFibreProductToGlobal`. -/
private noncomputable def representedFibreToGlobal
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)
    {𝒵 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (a : (schemeFibredCategory B S hS U).val ⥤ᵇ 𝒵.val.val)
    (g : 𝒵 ⟶ 𝒴) (f : 𝒳 ⟶ 𝒴)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p 𝒴.val.val.p
        (Over.iteratedSliceBackward U ⋙ a.toFunctor ⋙
          CatFiberedInGroupoids.homFunctor g.hom)
        (CatFiberedInGroupoids.homFunctor f.hom))
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    (fibredCategory B S hS
      ((OverShriek.relocalizePresheafFunctor U.hom).obj F)).val ⥤ᵇ
        (twoFibreProductAlgebraicStack B S hS g f).val.val := by
  let D := PresheafOfCategories.elementsToRelocalize U.hom F
  let L := localTwoFibreProductToGlobal B S hS U a g f
  refine ⟨D ⋙ e.inv.functor ⋙ L, ?_⟩
  have hL : L ⋙ (twoFibreProductAlgebraicStack B S hS g f).val.val.p =
      TwoFibreProductOver.structureFunctor (Over.map U.hom) 𝒳.val.val.p 𝒴.val.val.p
        (Over.iteratedSliceBackward U ⋙ a.toFunctor ⋙
          CatFiberedInGroupoids.homFunctor g.hom)
        (CatFiberedInGroupoids.homFunctor f.hom) :=
    localTwoFibreProductToGlobal_comp_projection B S hS U a g f
  change D ⋙ e.inv.functor ⋙ (L ⋙
    (twoFibreProductAlgebraicStack B S hS g f).val.val.p) = _
  rw [hL, ← TwoFibreProductOver.fst_comp_eq, ← Functor.assoc e.inv.functor, e.inv.w]
  exact PresheafOfCategories.elementsToRelocalize_comp_eq U.hom F

/-- An object `q` of the 2-fibre product of `a` with the first projection lifts to the 2-fibre
product taken over the scheme-valued point: there is an object `l` of the latter with the same
base and a morphism from its image under `AlgebraicGeometry.Stack.localTwoFibreProductToGlobal`
to the second component of `q`. -/
private theorem exists_localFibre_lift
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)
    {𝒵 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (a : (schemeFibredCategory B S hS U).val ⥤ᵇ 𝒵.val.val)
    (g : 𝒵 ⟶ 𝒴) (f : 𝒳 ⟶ 𝒴)
    (q : TwoFibreProductOver (Over.forget U)
      (TwoFibreProductOver.structureFunctor 𝒵.val.val.p 𝒳.val.val.p 𝒴.val.val.p
        g.hom.hom.toFunctor f.hom.hom.toFunctor) 𝒵.val.val.p a.toFunctor
      (TwoFibreProductOver.fst 𝒵.val.val.p 𝒳.val.val.p 𝒴.val.val.p
        g.hom.hom.toFunctor f.hom.hom.toFunctor)) :
    ∃ l : TwoFibreProductOver (Over.map U.hom) 𝒳.val.val.p 𝒴.val.val.p
        (Over.iteratedSliceBackward U ⋙ a.toFunctor ⋙ g.hom.hom.toFunctor)
        f.hom.hom.toFunctor,
      l.base = q.base ∧
        Nonempty ((localTwoFibreProductToGlobal B S hS U a g f).obj l ⟶ q.y) := by
  let eU := ((Over.iteratedSliceEquiv U).unitIso.app q.x).symm
  have hx : (Over.map U.hom).obj ((Over.iteratedSliceForward U).obj q.x) =
      q.base := by
    refine Eq.trans ?_ q.hx
    exact CostructuredArrow.obj_ext _ _ rfl (by
      show (𝟙 _) ≫ q.x.left.hom = q.x.hom.left ≫ U.hom
      exact (Category.id_comp _).trans q.x.hom.w.symm)
  have heU : (Over.forget U).IsHomLift (𝟙 q.base) eU.hom := by
    refine IsHomLift.of_fac' (Over.forget U) (𝟙 q.base) eU.hom hx q.hx ?_
    refine PresheafOfCategories.over_hom_eq_conj hx q.hx
      (congrArg Over.left hx) (congrArg Over.left q.hx) _ _ ?_
    show (𝟙 _) = eqToHom (congrArg Over.left hx) ≫ 𝟙 q.base.left ≫
      eqToHom (congrArg Over.left q.hx).symm
    simp only [Category.id_comp, eqToHom_trans]
    rfl
  have haU : 𝒵.val.val.p.IsHomLift (𝟙 q.base) (a.map eU.hom) := by
    let _ : (schemeFibredCategory B S hS U).val.p.IsHomLift
      (𝟙 q.base) eU.hom := heU
    exact a.preserves_isHomLift _ _
  let t : a.obj ((Over.iteratedSliceBackward U).obj
      ((Over.iteratedSliceForward U).obj q.x)) ≅ q.y.x :=
    a.toFunctor.mapIso eU ≪≫ q.iso
  have ht : 𝒵.val.val.p.IsHomLift (𝟙 q.base) t.hom := by
    let _ := haU
    let _ := q.vertical
    show 𝒵.val.val.p.IsHomLift (𝟙 q.base) (a.map eU.hom ≫ q.iso.hom)
    infer_instance
  have hg : 𝒴.val.val.p.IsHomLift (𝟙 q.base) (g.hom.hom.map t.hom) := by
    let _ := ht
    exact g.hom.hom.preserves_isHomLift _ _
  have hiy : 𝒴.val.val.p.IsHomLift (𝟙 q.base) q.y.iso.hom := by
    rw [← q.hy]
    exact q.y.vertical
  let l : TwoFibreProductOver (Over.map U.hom) 𝒳.val.val.p 𝒴.val.val.p
      (Over.iteratedSliceBackward U ⋙ a.toFunctor ⋙ g.hom.hom.toFunctor)
      f.hom.hom.toFunctor := {
    base := q.base
    x := (Over.iteratedSliceForward U).obj q.x
    y := q.y.y
    hx := hx
    hy := q.y.hy.trans q.hy
    iso := g.hom.hom.toFunctor.mapIso t ≪≫ q.y.iso
    vertical := by
      let _ := hg
      let _ := hiy
      show 𝒴.val.val.p.IsHomLift (𝟙 q.base)
        (g.hom.hom.map t.hom ≫ q.y.iso.hom)
      infer_instance }
  refine ⟨l, rfl, ⟨?_⟩⟩
  refine TwoFibreProductOver.Hom.mk' t.hom (𝟙 _) ?_ ?_
  · let _ := ht
    show eqToHom _ ≫ 𝒳.val.val.p.map (𝟙 _) ≫ eqToHom _ =
      eqToHom _ ≫ 𝒵.val.val.p.map t.hom ≫ eqToHom _
    rw [IsHomLift.fac' 𝒵.val.val.p (𝟙 q.base) t.hom, CategoryTheory.Functor.map_id]
    simp only [Category.id_comp, eqToHom_trans]
    exact (eqToHom_trans _ _).trans (eqToHom_trans _ _).symm
  · show g.hom.hom.map t.hom ≫ q.y.iso.hom =
      (g.hom.hom.map t.hom ≫ q.y.iso.hom) ≫ f.hom.hom.map (𝟙 q.y.y)
    simp

/-- If the presentation `a` is surjective then
`AlgebraicGeometry.Stack.representedFibreToGlobal` is surjective on points. -/
private theorem representedFibreToGlobal_surjective
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)
    {𝒵 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (a : @Quiver.Hom (AlgebraicStacks.{u, w} B S hS) inferInstance
      (⟨schemeFibredCategory B S hS U,
      (isDeligneMumfordStack_schemeFibredCategory.{u, w}
        B S hS U).1⟩ : AlgebraicStacks.{u, w} B S hS) 𝒵)
    (g : 𝒵 ⟶ 𝒴) (f : 𝒳 ⟶ 𝒴)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p 𝒴.val.val.p
        (Over.iteratedSliceBackward U ⋙ a.hom.hom.toFunctor ⋙
          CatFiberedInGroupoids.homFunctor g.hom)
        (CatFiberedInGroupoids.homFunctor f.hom))
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (ha : IsSurjective B S hS a) :
    Function.Surjective (pointsMap B S hS
      (fibredCategory B S hS
        ((OverShriek.relocalizePresheafFunctor U.hom).obj F)).val
      (fibredCategory B S hS
        ((OverShriek.relocalizePresheafFunctor U.hom).obj F)).property
      (twoFibreProductAlgebraicStack B S hS g f).val.property
      (representedFibreToGlobal B S hS U a.hom.hom g f F e)) := by
  classical
  let P := twoFibreProductAlgebraicStack B S hS g f
  let π := (twoFibreProductSquareAlgebraicStacks B S hS g f).fst
  let Q := twoFibreProductAlgebraicStack B S hS a π
  have hsurj := isSurjective_of_isTwoFibreProduct B S hS
    (twoFibreProductSquareAlgebraicStacks B S hS a π)
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS a π) ha
  let F' := (OverShriek.relocalizePresheafFunctor U.hom).obj F
  let A := fibredCategory B S hS F'
  let R := PresheafOfCategories.relocalizeToElements U.hom F
  let L := localTwoFibreProductToGlobal B S hS U a.hom.hom g f
  let H := representedFibreToGlobal B S hS U a.hom.hom g f F e
  intro z
  obtain ⟨q, hq⟩ := hsurj z
  obtain ⟨r, rfl⟩ := Quotient.exists_rep q
  rw [← hq]
  simp only [AlgebraicStacks.pointsMap]
  rw [pointsMap_class]
  obtain ⟨l, hl, ⟨j⟩⟩ := exists_localFibre_lift B S hS U a.hom.hom g f r.obj
  let v := R.obj (e.hom.functor.obj l)
  have hv : A.val.p.obj v = r.base := by
    calc
      _ = (Over.map U.hom).obj
          ((presheafOfCategories (F ⋙ typeToCat)).p.obj (e.hom.functor.obj l)) := rfl
      _ = (Over.map U.hom).obj l.x :=
        congrArg (Over.map U.hom).obj (congrArg (fun K => K.obj l) e.hom.w)
      _ = l.base := l.hx
      _ = r.base := hl.trans r.over
  let s : FieldValuedPoint B S hS A.val := {
    carrier := r.carrier
    field := r.field
    base := r.base
    isSpec := r.isSpec
    obj := v
    «over» := hv }
  refine ⟨pointClass B S hS A.val A.property s, ?_⟩
  rw [pointsMap_class]
  apply (class_eq_class_iff_hasCommonExtension
    B S hS P.val.val P.val.property _ _).2
  let image := fieldValuedPointMap B S hS A.val H s
  have j' : image.obj ⟶ r.obj.y := L.map (e.unitIso.inv.app l) ≫ j
  exact ⟨image, ⟨𝟙 image.obj⟩, ⟨j'⟩⟩

/-- A presheaf of sets does not move a section along an identity. -/
private theorem map_id_section {C : Type*} [Category C] (F : Cᵒᵖ ⥤ Type u) (T : C)
    (s : F.obj (Opposite.op T)) : F.map (𝟙 T).op s = s :=
  CategoryTheory.Functor.map_id_apply F (Opposite.op T) s

/-- The functor from the category of elements of a presheaf `F` to the category over `U` given by
a morphism `k : F ⟶ yoneda.obj U`: an object `(T, s)` is sent to the morphism `T ⟶ U` that the
section `s` names. -/
private def elementsToOver {C : Type*} [Category C]
    {F : Cᵒᵖ ⥤ Type u} {U : C} (k : F ⟶ yoneda.obj U) :
    (presheafOfCategories (F ⋙ typeToCat)).obj ⥤ Over U where
  obj x := Over.mk (k.app (Opposite.op x.base) x.fiber.as)
  map {x y} g := Over.homMk g.base (by
    have hg : x.fiber.as = F.map g.base.op y.fiber.as := Discrete.eq_of_hom g.fiber
    change g.base ≫ k.app _ y.fiber.as = k.app _ x.fiber.as
    rw [hg]
    exact (ConcreteCategory.congr_hom (k.naturality g.base.op) y.fiber.as).symm)
  map_id _ := by apply Over.OverMorphism.ext; rfl
  map_comp _ _ := by apply Over.OverMorphism.ext; rfl

/-- The sections named by a 1-morphism into a category of elements form a compatible family, in
the sense of `AlgebraicGeometry.Stack.sectionBasedFunctor`. -/
private theorem basedSection_naturality {C : Type*} [Category C]
    {A : BasedCategory C} {F : Cᵒᵖ ⥤ Type u}
    (a : A ⥤ᵇ presheafOfCategories (F ⋙ typeToCat))
    {x y : A.obj} (g : x ⟶ y) :
    elementSection F (a.obj x) (A.p.obj x) (a.w_obj x) =
      F.map (A.p.map g).op (elementSection F (a.obj y) (A.p.obj y) (a.w_obj y)) :=
  elementSection_naturality F (a.map g) _ _ _ (CategoryTheory.Functor.congr_hom a.w g)

/-- A fibre product of presheaves of sets is computed sectionwise: evaluation at an object of the
site preserves the pullback square. -/
private theorem pullback_sections_isPullback {C : Type u₁} [Category.{v₁} C]
    {F G H : Cᵒᵖ ⥤ Type u} (f : F ⟶ H) (g : G ⟶ H) (T : Cᵒᵖ) :
    IsPullback ((pullback.fst f g).app T) ((pullback.snd f g).app T)
      (f.app T) (g.app T) :=
  (IsPullback.of_hasPullback f g).map ((evaluation Cᵒᵖ (Type u)).obj T)

/-- A section of a fibre product of presheaves of sets with given compatible components. -/
private noncomputable def pullbackSection {C : Type u₁} [Category.{v₁} C]
    {F G H : Cᵒᵖ ⥤ Type u} (f : F ⟶ H) (g : G ⟶ H) (T : Cᵒᵖ)
    (x : F.obj T) (y : G.obj T) (h : f.app T x = g.app T y) :
    (pullback f g).obj T :=
  Classical.choose (Types.exists_of_isPullback (pullback_sections_isPullback f g T) x y h)

/-- The first component of `AlgebraicGeometry.Stack.pullbackSection` is the first of the two
given sections. -/
private theorem pullbackSection_fst {C : Type u₁} [Category.{v₁} C]
    {F G H : Cᵒᵖ ⥤ Type u} (f : F ⟶ H) (g : G ⟶ H) (T : Cᵒᵖ)
    (x : F.obj T) (y : G.obj T) (h : f.app T x = g.app T y) :
    (pullback.fst f g).app T (pullbackSection f g T x y h) = x :=
  (Classical.choose_spec (Types.exists_of_isPullback
    (pullback_sections_isPullback f g T) x y h)).1

/-- The second component of `AlgebraicGeometry.Stack.pullbackSection` is the second of the two
given sections. -/
private theorem pullbackSection_snd {C : Type u₁} [Category.{v₁} C]
    {F G H : Cᵒᵖ ⥤ Type u} (f : F ⟶ H) (g : G ⟶ H) (T : Cᵒᵖ)
    (x : F.obj T) (y : G.obj T) (h : f.app T x = g.app T y) :
    (pullback.snd f g).app T (pullbackSection f g T x y h) = y :=
  (Classical.choose_spec (Types.exists_of_isPullback
    (pullback_sections_isPullback f g T) x y h)).2

/-- The 1-morphism into the category of elements of a fibre product of presheaves given by two
1-morphisms into categories of elements which agree after the two legs of the cospan: its family
of sections is the sectionwise fibre product of the two families. -/
private noncomputable def pullbackSectionFunctor {C : Type u₁} [Category.{v₁} C]
    {A : BasedCategory C} {F G H : Cᵒᵖ ⥤ Type u} (f : F ⟶ H) (g : G ⟶ H)
    (a : A ⥤ᵇ presheafOfCategories (F ⋙ typeToCat))
    (b : A ⥤ᵇ presheafOfCategories (G ⋙ typeToCat))
    (h : ∀ x, f.app _ (elementSection F (a.obj x) (A.p.obj x) (a.w_obj x)) =
      g.app _ (elementSection G (b.obj x) (A.p.obj x) (b.w_obj x))) :
    A ⥤ᵇ presheafOfCategories (pullback f g ⋙ typeToCat) := by
  apply sectionBasedFunctor A (pullback f g)
    (fun x => pullbackSection f g _ _ _ (h x))
  intro x y j
  have key : ∀ {E : Cᵒᵖ ⥤ Type u} (π : pullback f g ⟶ E)
      (c : A ⥤ᵇ presheafOfCategories (E ⋙ typeToCat))
      (hπ : ∀ x, π.app _ (pullbackSection f g _ _ _ (h x)) =
        elementSection E (c.obj x) (A.p.obj x) (c.w_obj x)),
      π.app _ (pullbackSection f g _ _ _ (h x)) =
        π.app _ ((pullback f g).map (A.p.map j).op (pullbackSection f g _ _ _ (h y))) := by
    intro E π c hπ
    have hn := ConcreteCategory.congr_hom (π.naturality (A.p.map j).op)
      (pullbackSection f g _ _ _ (h y))
    change π.app _ ((pullback f g).map _ _) = E.map _ (π.app _ _) at hn
    rw [hn, hπ, hπ]
    exact basedSection_naturality c j
  apply Types.ext_of_isPullback (pullback_sections_isPullback f g _)
  · exact key (pullback.fst f g) a fun x => pullbackSection_fst f g _ _ _ _
  · exact key (pullback.snd f g) b fun x => pullbackSection_snd f g _ _ _ _

/-- The category of elements of a presheaf over a representable presheaf, read over the big site
of the representing object: `AlgebraicGeometry.Stack.elementsToOver` followed by the
iterated-slice identification of the slice of the site over `U` with the big site of `U`. -/
private def elementsToLocalSite
    {C : Type*} [Category C] {S : C} (U : Over S)
    {H : (Over S)ᵒᵖ ⥤ Type u} (k : H ⟶ yoneda.obj U) :
    (presheafOfCategories (H ⋙ typeToCat)).obj ⥤ Over U.left :=
  elementsToOver k ⋙ Over.iteratedSliceForward U

/-- `AlgebraicGeometry.Stack.elementsToLocalSite` is strictly over the site: relocalizing it
along the structure morphism of `U` gives the structure functor of the category of elements. -/
private theorem elementsToLocalSite_comp
    {C : Type*} [Category C] {S : C} (U : Over S)
    {H : (Over S)ᵒᵖ ⥤ Type u} (k : H ⟶ yoneda.obj U) :
    elementsToLocalSite U k ⋙ Over.map U.hom =
      (presheafOfCategories (H ⋙ typeToCat)).p := by
  have hobj : ∀ x, (elementsToLocalSite U k ⋙ Over.map U.hom).obj x =
      (presheafOfCategories (H ⋙ typeToCat)).p.obj x := fun x =>
    CostructuredArrow.obj_ext _ _ rfl (by
      show (𝟙 _) ≫ x.base.hom = (k.app _ x.fiber.as).left ≫ U.hom
      exact (Category.id_comp _).trans (k.app _ x.fiber.as).w.symm)
  refine CategoryTheory.Functor.ext hobj ?_
  intro x y g
  refine PresheafOfCategories.over_hom_eq_conj (hobj x) (hobj y) rfl rfl _ _ ?_
  show g.base.left = (𝟙 _) ≫ g.base.left ≫ (𝟙 _)
  simp

/-- The structural morphism of a lower-shriek extension reads off the base of a relocalized
element: pushing along `q` the section named by the relocalization of an object of the category
of elements of `F` gives the structure morphism of that object's base, read in the slice over
`U`. -/
private theorem relocalize_elementSection_eq
    {C : Type*} [Category C] {S : C} (U : Over S)
    (F : (Over U.left)ᵒᵖ ⥤ Type u)
    (q : (OverShriek.relocalizePresheafFunctor U.hom).obj F ⟶ yoneda.obj U)
    (hq : ∀ T s, q.app T s = Over.homMk s.1.1 s.2)
    (x : (presheafOfCategories (F ⋙ typeToCat)).obj)
    (V : Over U.left) (hx : x.base = V)
    (T : Over S) (hV : (Over.map U.hom).obj V = T) :
    q.app (Opposite.op T)
      (elementSection ((OverShriek.relocalizePresheafFunctor U.hom).obj F)
        ((PresheafOfCategories.relocalizeToElements U.hom F).obj x) T
        ((congrArg (Over.map U.hom).obj hx).trans hV)) =
      eqToHom hV.symm ≫ (Over.homMk V.hom rfl : (Over.map U.hom).obj V ⟶ U) := by
  subst V
  subst T
  show q.app _ (((OverShriek.relocalizePresheafFunctor U.hom).obj F).map
    (𝟙 _).op ((PresheafOfCategories.relocalizeToElements U.hom F).obj x).fiber.as) = _
  simp only [op_id]
  exact hq _ _

/-- The structure morphism of `AlgebraicGeometry.Stack.elementsToLocalSite` is the morphism to `U`
that the section names. -/
private theorem elementsToLocalSite_section
    {C : Type*} [Category C] {S : C} (U : Over S)
    {H : (Over S)ᵒᵖ ⥤ Type u} (k : H ⟶ yoneda.obj U)
    (x : (presheafOfCategories (H ⋙ typeToCat)).obj)
    (T : Over S) (hx : x.base = T) :
    eqToHom ((Functor.congr_obj (elementsToLocalSite_comp U k) x).trans hx).symm ≫
      (Over.homMk ((elementsToLocalSite U k).obj x).hom rfl :
        (Over.map U.hom).obj ((elementsToLocalSite U k).obj x) ⟶ U) =
    k.app (Opposite.op T) (elementSection H x T hx) := by
  subst T
  simp only [elementSection, eqToHom_refl, op_id, CategoryTheory.Functor.map_id_apply]
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Over.eqToHom_left]
  show (𝟙 _) ≫ (k.app _ x.fiber.as).left = (k.app _ x.fiber.as).left
  exact Category.id_comp _

/-- The functor from a 2-fibre product taken over a category over the big site of `U` to the one
taken over the slice of the site at `U`: the comparison functor `ψ` of the source turns the first
projection into a leg over the slice; the second leg is the second projection and the comparison
2-cell is the one the source already carries. -/
private def localFibreFunctor
    {C : Type*} [Category C] {S : C} (U : Over S)
    (A X Y : BasedCategory (Over S))
    (ψ : A.obj ⥤ Over U.left) (hψ : ψ ⋙ Over.map U.hom = A.p)
    (y : Over U.left ⥤ Y.obj) (f : X ⥤ᵇ Y) :
    TwoFibreProductOver A.p X.p Y.p (ψ ⋙ y) f.toFunctor ⥤
      TwoFibreProductOver (Over.map U.hom) X.p Y.p y f.toFunctor := by
  let π₁ := TwoFibreProductOver.fst A.p X.p Y.p (ψ ⋙ y) f.toFunctor
  let π₂ := TwoFibreProductOver.snd A.p X.p Y.p (ψ ⋙ y) f.toFunctor
  let p := TwoFibreProductOver.structureFunctor A.p X.p Y.p (ψ ⋙ y) f.toFunctor
  refine TwoFibreProductOver.lift (Over.map U.hom) X.p Y.p y f.toFunctor p
    (π₁ ⋙ ψ) π₂ ?_ TwoFibreProductOver.snd_comp_eq
    (TwoFibreProductOver.psiIso A.p X.p Y.p (ψ ⋙ y) f.toFunctor) ?_
  · rw [Functor.assoc, hψ]
    exact TwoFibreProductOver.fst_comp_eq
  · intro x
    exact x.vertical

/-- The 2-fibre product taken over a category over the big site of `U`, read in the category of
elements of the lower-shriek extension of a representing presheaf:
`AlgebraicGeometry.Stack.localFibreFunctor` followed by the representing equivalence and by
`CategoryTheory.PresheafOfCategories.relocalizeToElements`. -/
private def baseChangeToRepresentedSpace
    {C : Type*} [Category C] {S : C} (U : Over S)
    (A X Y : BasedCategory (Over S))
    (ψ : A.obj ⥤ Over U.left) (hψ : ψ ⋙ Over.map U.hom = A.p)
    (y : Over U.left ⥤ Y.obj) (f : X ⥤ᵇ Y)
    (F : (Over U.left)ᵒᵖ ⥤ Type u)
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) X.p Y.p y f.toFunctor)
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    BasedCategory.ofFunctor
      (TwoFibreProductOver.structureFunctor A.p X.p Y.p (ψ ⋙ y) f.toFunctor) ⥤ᵇ
        presheafOfCategories
          ((OverShriek.relocalizePresheafFunctor U.hom).obj F ⋙ typeToCat) := by
  let L := localFibreFunctor U A X Y ψ hψ y f
  refine ⟨L ⋙ e.hom.functor ⋙ PresheafOfCategories.relocalizeToElements U.hom F, ?_⟩
  change L ⋙ e.hom.functor ⋙
    ((presheafOfCategories (F ⋙ typeToCat)).p ⋙ Over.map U.hom) = _
  rw [← Functor.assoc e.hom.functor, e.hom.w]
  change (TwoFibreProductOver.fst A.p X.p Y.p (ψ ⋙ y) f.toFunctor) ⋙
    ψ ⋙ Over.map U.hom = _
  rw [hψ]
  exact TwoFibreProductOver.fst_comp_eq

/-- The section of `H` beneath an object of the 2-fibre product and the section of the
lower-shriek extension named by its representing object agree over the presheaf represented by
`U`. -/
private theorem representedPullback_sections_agree
    {C : Type*} [Category C] {S : C} (U : Over S)
    (X Y : BasedCategory (Over S)) (y : Over U.left ⥤ Y.obj) (f : X ⥤ᵇ Y)
    (F : (Over U.left)ᵒᵖ ⥤ Type u)
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) X.p Y.p y f.toFunctor)
      (presheafOfCategories (F ⋙ typeToCat)).p)
    {H : (Over S)ᵒᵖ ⥤ Type u} (k : H ⟶ yoneda.obj U)
    (q : (OverShriek.relocalizePresheafFunctor U.hom).obj F ⟶ yoneda.obj U)
    (hq : ∀ T s, q.app T s = Over.homMk s.1.1 s.2)
    (x : TwoFibreProductOver (presheafOfCategories (H ⋙ typeToCat)).p X.p Y.p
      (elementsToLocalSite U k ⋙ y) f.toFunctor) :
    k.app (Opposite.op x.base) (elementSection H x.x x.base x.hx) =
      q.app (Opposite.op x.base)
        (elementSection ((OverShriek.relocalizePresheafFunctor U.hom).obj F)
          ((baseChangeToRepresentedSpace U (presheafOfCategories (H ⋙ typeToCat)) X Y
              (elementsToLocalSite U k) (elementsToLocalSite_comp U k) y f F e).obj x)
          x.base
          ((baseChangeToRepresentedSpace U (presheafOfCategories (H ⋙ typeToCat)) X Y
              (elementsToLocalSite U k) (elementsToLocalSite_comp U k) y f F e).w_obj x)) := by
  symm
  have he : (e.hom.functor.obj
        ((localFibreFunctor U (presheafOfCategories (H ⋙ typeToCat)) X Y
          (elementsToLocalSite U k) (elementsToLocalSite_comp U k) y f).obj x)).base =
      (elementsToLocalSite U k).obj x.x :=
    Functor.congr_obj e.hom.w _
  calc
    _ = eqToHom ((Functor.congr_obj (elementsToLocalSite_comp U k) x.x).trans x.hx).symm ≫
        (Over.homMk ((elementsToLocalSite U k).obj x.x).hom rfl :
          (Over.map U.hom).obj ((elementsToLocalSite U k).obj x.x) ⟶ U) :=
      relocalize_elementSection_eq U F q hq
        (e.hom.functor.obj ((localFibreFunctor U (presheafOfCategories (H ⋙ typeToCat)) X Y
          (elementsToLocalSite U k) (elementsToLocalSite_comp U k) y f).obj x))
        ((elementsToLocalSite U k).obj x.x) he x.base
        ((Functor.congr_obj (elementsToLocalSite_comp U k) x.x).trans x.hx)
    _ = _ := elementsToLocalSite_section U k x.x x.base x.hx

/-- The 2-fibre product of `f` with a scheme-valued point of `𝒴`, taken over the category of
elements of `H`, read in the category of elements of the fibre product of presheaves
`H ×_{h_U} Λ F`: its two families of sections are the first projection into `H` and
`AlgebraicGeometry.Stack.baseChangeToRepresentedSpace`. -/
private noncomputable def representedPullbackFunctor
    {C : Type*} [Category C] {S : C} (U : Over S)
    (X Y : BasedCategory (Over S)) (y : Over U.left ⥤ Y.obj) (f : X ⥤ᵇ Y)
    (F : (Over U.left)ᵒᵖ ⥤ Type u)
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) X.p Y.p y f.toFunctor)
      (presheafOfCategories (F ⋙ typeToCat)).p)
    {H : (Over S)ᵒᵖ ⥤ Type u} (k : H ⟶ yoneda.obj U)
    (q : (OverShriek.relocalizePresheafFunctor U.hom).obj F ⟶ yoneda.obj U)
    (hq : ∀ T s, q.app T s = Over.homMk s.1.1 s.2) :
    BasedCategory.ofFunctor
      (TwoFibreProductOver.structureFunctor (presheafOfCategories (H ⋙ typeToCat)).p
        X.p Y.p (elementsToLocalSite U k ⋙ y) f.toFunctor) ⥤ᵇ
      presheafOfCategories (pullback k q ⋙ typeToCat) :=
  pullbackSectionFunctor k q
    ⟨TwoFibreProductOver.fst (presheafOfCategories (H ⋙ typeToCat)).p X.p Y.p
        (elementsToLocalSite U k ⋙ y) f.toFunctor, TwoFibreProductOver.fst_comp_eq⟩
    (baseChangeToRepresentedSpace U (presheafOfCategories (H ⋙ typeToCat)) X Y
      (elementsToLocalSite U k) (elementsToLocalSite_comp U k) y f F e)
    (representedPullback_sections_agree U X Y y f F e k q hq)

/-- A vertical morphism of a category of elements does not change the section. -/
private theorem elementSection_eq_of_isHomLift
    {C : Type*} [Category C] (F : Cᵒᵖ ⥤ Type u)
    {x z : (presheafOfCategories (F ⋙ typeToCat)).obj} (j : x ⟶ z)
    (T : C) (hx : x.base = T) (hz : z.base = T)
    [hj : (presheafOfCategories (F ⋙ typeToCat)).p.IsHomLift (𝟙 T) j] :
    elementSection F x T hx = elementSection F z T hz := by
  have h := elementSection_naturality F j hx hz (𝟙 T)
    (IsHomLift.fac' (presheafOfCategories (F ⋙ typeToCat)).p (𝟙 T) j)
  rwa [map_id_section] at h

/-- `AlgebraicGeometry.Stack.representedPullbackFunctor` names every section of the fibre product
of presheaves: every section over `T` is the section of the image of an object of the 2-fibre
product over `T`. -/
private theorem representedPullbackFunctor_lift
    {C : Type*} [Category C] {S : C} (U : Over S)
    (X Y : BasedCategory (Over S)) (y : Over U.left ⥤ Y.obj)
    (hy : y ⋙ Y.p = Over.map U.hom) (f : X ⥤ᵇ Y)
    (F : (Over U.left)ᵒᵖ ⥤ Type u)
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) X.p Y.p y f.toFunctor)
      (presheafOfCategories (F ⋙ typeToCat)).p)
    {H : (Over S)ᵒᵖ ⥤ Type u} (k : H ⟶ yoneda.obj U)
    (q : (OverShriek.relocalizePresheafFunctor U.hom).obj F ⟶ yoneda.obj U)
    (hq : ∀ T s, q.app T s = Over.homMk s.1.1 s.2)
    (T : Over S) (s : (pullback k q).obj (Opposite.op T)) :
    ∃ x : TwoFibreProductOver (presheafOfCategories (H ⋙ typeToCat)).p X.p Y.p
        (elementsToLocalSite U k ⋙ y) f.toFunctor,
      ∃ hx : x.base = T,
        elementSection (pullback k q)
          ((representedPullbackFunctor U X Y y f F e k q hq).obj x) T hx = s := by
  let F' := (OverShriek.relocalizePresheafFunctor U.hom).obj F
  let pF := (presheafOfCategories (F ⋙ typeToCat)).p
  let R := PresheafOfCategories.relocalizeToElements U.hom F
  let a := (pullback.fst k q).app (Opposite.op T) s
  let b := (pullback.snd k q).app (Opposite.op T) s
  have hab : k.app _ a = q.app _ b :=
    ConcreteCategory.congr_hom (NatTrans.congr_app (pullback.condition (f := k) (g := q)) _) s
  let v : (presheafOfCategories (F ⋙ typeToCat)).obj :=
    ⟨Over.mk b.1.1, Discrete.mk b.1.2⟩
  let l := e.inv.functor.obj v
  have hl : l.x = v.base := Functor.congr_obj e.inv.w v
  let z : (presheafOfCategories (H ⋙ typeToCat)).obj := ⟨T, Discrete.mk a⟩
  let ψ := elementsToLocalSite U k
  have hz : ψ.obj z = v.base := congrArg Over.mk (congrArg Over.Hom.left (hab.trans (hq _ b)))
  have hV : (Over.map U.hom).obj v.base = T :=
    CostructuredArrow.obj_ext _ _ rfl (by
      show (𝟙 _) ≫ T.hom = b.1.1 ≫ U.hom
      exact (Category.id_comp _).trans b.2.symm)
  have hlbase : l.base = T := l.hx.symm.trans ((congrArg (Over.map U.hom).obj hl).trans hV)
  let az : BasedCategory.ofFunctor (Over.map U.hom) ⥤ᵇ Y := ⟨y, hy⟩
  let jx : ψ.obj z ⟶ l.x := eqToHom (hz.trans hl.symm)
  have hjx : (Over.map U.hom).IsHomLift (𝟙 T) jx :=
    IsHomLift.eqToHom_codomain_lift_id _ (l.hx.trans hlbase)
  let _ : (BasedCategory.ofFunctor (Over.map U.hom)).p.IsHomLift (𝟙 T) jx := hjx
  have hiy : Y.p.IsHomLift (𝟙 T) (y.map jx) := az.preserves_isHomLift _ _
  have hil : Y.p.IsHomLift (𝟙 T) l.iso.hom := by rw [← hlbase]; exact l.vertical
  let x : TwoFibreProductOver (presheafOfCategories (H ⋙ typeToCat)).p X.p Y.p
      (ψ ⋙ y) f.toFunctor := {
    base := T
    x := z
    y := l.y
    hx := rfl
    hy := l.hy.trans hlbase
    iso := y.mapIso (eqToIso (hz.trans hl.symm)) ≪≫ l.iso
    vertical := by
      let _ := hiy
      let _ := hil
      show Y.p.IsHomLift (𝟙 T) (y.map jx ≫ l.iso.hom)
      infer_instance }
  let L := localFibreFunctor U (presheafOfCategories (H ⋙ typeToCat)) X Y ψ
    (elementsToLocalSite_comp U k) y f
  let j : L.obj x ⟶ l := TwoFibreProductOver.Hom.mk' jx (𝟙 _) (by
    show eqToHom _ ≫ X.p.map (𝟙 _) ≫ eqToHom _ =
      eqToHom _ ≫ (Over.map U.hom).map jx ≫ eqToHom _
    rw [IsHomLift.fac' (Over.map U.hom) (𝟙 T) jx, CategoryTheory.Functor.map_id]
    simp only [Category.id_comp, eqToHom_trans]
    exact (eqToHom_trans _ _).trans (eqToHom_trans _ _).symm) (by
    show y.map jx ≫ l.iso.hom = (y.map jx ≫ l.iso.hom) ≫ f.map (𝟙 l.y)
    simp)
  have hj : (TwoFibreProductOver.fst (Over.map U.hom) X.p Y.p y f.toFunctor).IsHomLift
      (𝟙 v.base) j := by
    refine IsHomLift.of_fac' _ _ j hz hl ?_
    show jx = eqToHom hz ≫ (𝟙 v.base) ≫ eqToHom hl.symm
    simp [jx]
  let eh : BasedCategory.ofFunctor
      (TwoFibreProductOver.fst (Over.map U.hom) X.p Y.p y f.toFunctor) ⥤ᵇ
      presheafOfCategories (F ⋙ typeToCat) := ⟨e.hom.functor, e.hom.w⟩
  let m : e.hom.functor.obj (L.obj x) ⟶ v := e.hom.functor.map j ≫ e.counitIso.hom.app v
  have hm : pF.IsHomLift (𝟙 v.base) m := by
    let _ : (BasedCategory.ofFunctor
      (TwoFibreProductOver.fst (Over.map U.hom) X.p Y.p y f.toFunctor)).p.IsHomLift
        (𝟙 v.base) j := hj
    have _ : pF.IsHomLift (𝟙 v.base) (e.hom.functor.map j) := eh.preserves_isHomLift _ _
    let _ : pF.IsHomLift (𝟙 v.base) (e.counitIso.hom.app v) :=
      e.isHomLift_counitIso_hom_app v
    show pF.IsHomLift (𝟙 v.base) (e.hom.functor.map j ≫ e.counitIso.hom.app v)
    infer_instance
  have hR : (R.obj v).base = T := hV
  have hE : (R.obj (e.hom.functor.obj (L.obj x))).base = T :=
    (baseChangeToRepresentedSpace U _ X Y ψ (elementsToLocalSite_comp U k) y f F e).w_obj x
  have hm' : (presheafOfCategories (F' ⋙ typeToCat)).p.IsHomLift (𝟙 T) (R.map m) := by
    refine IsHomLift.of_fac' _ _ _ hE hR ?_
    show (Over.map U.hom).map m.base = _
    let _ := hm
    rw [show m.base = _ from IsHomLift.fac' pF (𝟙 v.base) m]
    simp only [Category.id_comp, eqToHom_trans]
    exact Eq.trans (eqToHom_map (Over.map U.hom) _) (eqToHom_trans _ _).symm
  have hb : elementSection F' (R.obj (e.hom.functor.obj (L.obj x))) T hE = b := by
    let _ := hm'
    rw [elementSection_eq_of_isHomLift F' (R.map m) T hE hR]
    obtain ⟨⟨bmap, bval⟩, hbmap⟩ := b
    obtain ⟨W, φ, rfl⟩ := Over.mk_surjective T
    change W ⟶ U.left at bmap
    change bmap ≫ U.hom = φ at hbmap
    subst φ
    show F'.map (𝟙 _).op _ = _
    exact Eq.trans (map_id_section F' _ _) rfl
  refine ⟨x, rfl, ?_⟩
  show (pullback k q).map (𝟙 T).op _ = s
  refine Eq.trans (map_id_section (pullback k q) T _) ?_
  show ((representedPullbackFunctor U X Y y f F e k q hq).obj x).fiber.as = s
  apply Types.ext_of_isPullback (pullback_sections_isPullback k q _)
  · refine Eq.trans (pullbackSection_fst k q (Opposite.op T) _ _
      (representedPullback_sections_agree U X Y y f F e k q hq x)) ?_
    exact map_id_section H T a
  · refine Eq.trans (pullbackSection_snd k q (Opposite.op T) _ _
      (representedPullback_sections_agree U X Y y f F e k q hq x)) ?_
    exact hb

/-- An algebraic space whose category of elements is a quasi-compact algebraic stack is
quasi-compact. -/
private theorem isQuasiCompact_of_compact_fibredCategory
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F)
    (hc : IsQuasiCompactStack B S hS
      (fibredCategory B S hS F)
      (isDeligneMumfordStack_fibredCategory.{u, w} B S hS F hF).1) :
    Space.IsQuasiCompactSpace B S hS F := by
  let A : AlgebraicStacks.{u, w} B S hS :=
    ⟨fibredCategory B S hS F,
      (isDeligneMumfordStack_fibredCategory B S hS F hF).1⟩
  obtain ⟨G, hG, hGqc, a, ha, _⟩ :=
    (hasQuasiCompactSchemeSmoothPresentation_iff_hasQuasiCompactSpaceSmoothPresentation
      B S hS A).mp
      ((hasAffineSmoothPresentation_iff_hasQuasiCompactSchemeSmoothPresentation
        B S hS A).mp
        ((isQuasiCompactStack_iff_hasAffineSmoothPresentation B S hS A).mp hc))
  let b := presheafMapOfBasedFunctor a.hom.hom
  have hs : Function.Surjective (Space.pointsMap B S hS G b) := by
    intro x
    obtain ⟨y, hy⟩ := ha (spacePointMap B S hS F A.val
      (BasedFunctor.id (fibredCategory B S hS F).val) x)
    obtain ⟨z, hz⟩ := (spacePointMap_id_bijective B S hS G).2 y
    refine ⟨z, (spacePointMap_id_bijective B S hS F).1 ?_⟩
    change spacePointMap B S hS G
      (fibredCategory B S hS G)
      (BasedFunctor.id (fibredCategory B S hS G).val) z = y at hz
    rw [spacePointMap_presheafMapOfBasedFunctor, hz]
    exact hy
  let _ := Space.pointTopology B S hS G
  let _ := Space.pointTopology B S hS F
  have _ : CompactSpace (Space.points B S hS G) :=
    (Space.isQuasiCompactSpace_iff_compactSpace_points B S hS G hG).mp hGqc
  have hcont : Continuous (Space.pointsMap B S hS G b) :=
    (Space.pointTopologyFamily B S hS).continuous hG hF b
  exact (Space.isQuasiCompactSpace_iff_compactSpace_points B S hS F hF).mpr
    (Function.Surjective.compactSpace hcont hs)

/-- For a 1-morphism of algebraic stacks over `S` representable by algebraic
spaces, quasi-compactness in the sense of Properties of Stacks, Section 04XB — every algebraic
space representing a base change along a scheme-valued point of the target is quasi-compact over
its base — is equivalent to quasi-compactness in the sense of Stacks 050U: every base change by a
quasi-compact algebraic stack is a quasi-compact algebraic stack. -/
@[stacks 050T]
public theorem isQuasiCompact_iff_baseChange_quasiCompact
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) :
    IsQuasiCompact B S hS f.hom ↔ IsQuasiCompactMorphism.{u, w} B S hS f := by
  constructor
  · intro h 𝒵 g h𝒵qc
    obtain ⟨U, hUqc, a, haSurj, haSmooth⟩ :=
      (hasAffineSmoothPresentation_iff_hasQuasiCompactSchemeSmoothPresentation
        B S hS 𝒵).mp
        ((isQuasiCompactStack_iff_hasAffineSmoothPresentation
          B S hS 𝒵).mp h𝒵qc)
    let 𝒰 : AlgebraicStacks.{u, w} B S hS :=
      ⟨schemeFibredCategory B S hS U,
        (isDeligneMumfordStack_schemeFibredCategory.{u, w}
          B S hS U).1⟩
    let y := Over.iteratedSliceBackward U ⋙
      CatFiberedInGroupoids.homFunctor (a.hom ≫ g.hom)
    have hcomp :
        (a.hom ≫ g.hom).hom.toFunctor ⋙ 𝒴.val.val.p = 𝒰.val.val.p :=
      (a.hom ≫ g.hom).hom.w
    have hy : y ⋙ 𝒴.val.val.p = Over.map U.hom :=
      iteratedSliceBackward_comp_eq U _ _ hcomp
    obtain ⟨F, hF, hEquiv⟩ := hf U y hy
    have hFiberQC := h U y hy F hF hEquiv
    let Fy := (spacesOverSmallerBaseFunctor
      B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩
    let q := algebraicSpaceMap B S hS U Fy
    have hTargetQC : Space.IsQuasiCompactSpace B S hS
        (yoneda.obj (Over.mk U.hom)) :=
      Space.isQuasiCompact_yoneda_of_compact B S hS (Over.mk U.hom) (by simpa using hUqc)
    have hFiberSourceQC : Space.IsQuasiCompactSpace B S hS Fy.1.left :=
      isQuasiCompact_source_of_isQuasiCompact B S hS
        (isAlgebraicSpace_yoneda B S hS (Over.mk U.hom))
        hTargetQC q.hom hFiberQC
    obtain ⟨e⟩ := hEquiv
    let F' := (OverShriek.relocalizePresheafFunctor U.hom).obj F
    have hF' : IsAlgebraicSpace B S hS F' :=
      isAlgebraicSpace_viewOver B U.left.1 S U.left.2 hS U.hom F hF
    have hF'qc : Space.IsQuasiCompactSpace B S hS F' :=
      Space.isQuasiCompactSpace_of_iso B S hS
        ((spacesOverSmallerBaseFunctorForgetIso
          B U.left.1 S U.left.2 hS U.hom).app ⟨F, hF⟩) hFiberSourceQC
    let 𝒜 : AlgebraicStacks.{u, w} B S hS :=
      ⟨fibredCategory B S hS F',
        (isDeligneMumfordStack_fibredCategory.{u, w} B S hS F' hF').1⟩
    let k : 𝒜 ⟶ twoFibreProductAlgebraicStack B S hS g f :=
      Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
        (representedFibreToGlobal B S hS U a.hom.hom g f F e))
    exact isQuasiCompactStack_of_isSurjective B S hS k
      (isQuasiCompactStack_fibredCategory B S hS F' hF' hF'qc _)
      (representedFibreToGlobal_surjective B S hS U a g f F e haSurj)
  · intro h U y hy F hF he
    have : HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance
    obtain ⟨e⟩ := he
    let Fy := (spacesOverSmallerBaseFunctor
      B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩
    let F' := (OverShriek.relocalizePresheafFunctor U.hom).obj F
    let i : Fy.1.left ≅ F' :=
      (spacesOverSmallerBaseFunctorForgetIso
        B U.left.1 S U.left.2 hS U.hom).app ⟨F, hF⟩
    let q : F' ⟶ yoneda.obj U := i.inv ≫ Fy.1.hom
    have hq : ∀ T s, q.app T s = Over.homMk s.1.1 s.2 :=
      spacesOverSmallerBaseFunctor_hom_app_forgetIso_inv_app
        B U.left.1 S U.left.2 hS U.hom ⟨F, hF⟩
    have hF' : IsAlgebraicSpace B S hS F' :=
      isAlgebraicSpace_viewOver B U.left.1 S U.left.2 hS U.hom F hF
    have hqc : Space.IsQuasiCompact B S hS q := by
      intro H hH hHqc k
      have : HasPullback k q := HasLimitsOfShape.has_limit _
      let A : AlgebraicStacks.{u, w} B S hS :=
        ⟨fibredCategory B S hS H,
          (isDeligneMumfordStack_fibredCategory B S hS H hH).1⟩
      let ψ := elementsToLocalSite U k
      let a : A ⟶ 𝒴 := Bicategory.InducedBicategory.mkHom
        (Bicategory.InducedBicategory.mkHom (BasedFunctor.mk (ψ ⋙ y)
          ((Functor.assoc ψ y 𝒴.val.val.p).trans
            ((congrArg (fun K => ψ ⋙ K) hy).trans (elementsToLocalSite_comp U k)))))
      let P := twoFibreProductAlgebraicStack B S hS a f
      have hP : IsQuasiCompactStack B S hS P.val P.property :=
        h A a (isQuasiCompactStack_fibredCategory B S hS H hH hHqc _)
      have hG : IsAlgebraicSpace B S hS (pullback k q) :=
        isAlgebraicSpace_pullback B S hS k q hH hF'
          (isAlgebraicSpace_yoneda B S hS U)
      let G : AlgebraicStacks.{u, w} B S hS :=
        ⟨fibredCategory B S hS (pullback k q),
          (isDeligneMumfordStack_fibredCategory B S hS (pullback k q) hG).1⟩
      let t : P ⟶ G := Bicategory.InducedBicategory.mkHom
        (Bicategory.InducedBicategory.mkHom
          (representedPullbackFunctor U 𝒳.val.val 𝒴.val.val y f.hom.hom F e k q hq))
      have ht : IsSurjective B S hS t := by
        intro z
        obtain ⟨r, hr⟩ := (spacePointMap_id_bijective B S hS (pullback k q)).2 z
        obtain ⟨r, rfl⟩ := Quot.exists_rep r
        obtain ⟨x, hx, hs⟩ := representedPullbackFunctor_lift U 𝒳.val.val 𝒴.val.val
          y hy f.hom.hom F e k q hq r.siteObject r.value
        let p : FieldValuedPoint B S hS P.val.val := {
          carrier := r.carrier
          field := r.field
          base := r.siteObject
          isSpec := Iso.refl _
          obj := x
          «over» := hx }
        refine ⟨pointClass B S hS P.val.val P.val.property p, ?_⟩
        rw [← hr]
        simp only [AlgebraicStacks.pointsMap]
        rw [pointsMap_class, spacePointMap_class]
        apply (class_eq_class_iff_hasCommonExtension B S hS _ _ _ _).2
        let v := spaceFieldValuedPoint B S hS (pullback k q) r
        refine ⟨v, ⟨?_⟩, ⟨𝟙 v.obj⟩⟩
        exact ⟨eqToHom ((t.hom.hom.w_obj x).trans hx).symm,
          Discrete.eqToHom hs.symm⟩
      exact isQuasiCompact_of_compact_fibredCategory.{u, w} B S hS (pullback k q) hG
        (isQuasiCompactStack_of_isSurjective B S hS t hP ht)
    intro H hH hHqc k
    have : HasPullback k q := HasLimitsOfShape.has_limit _
    have : HasPullback k Fy.1.hom := HasLimitsOfShape.has_limit _
    have h₁ := IsPullback.of_hasPullback k q
    have h₂ := IsPullback.of_hasPullback k Fy.1.hom
    have hp : IsPullback (pullback.fst k q) (pullback.snd k q ≫ i.inv) k Fy.1.hom := by
      refine h₁.of_iso (Iso.refl _) (Iso.refl _) i.symm (Iso.refl _) ?_ ?_ ?_ ?_
      all_goals simp [q]
    exact Space.isQuasiCompactSpace_of_iso B S hS (hp.isoIsPullback _ _ h₂) (hqc H hH hHqc k)

end AlgebraicGeometry.Stack

end
