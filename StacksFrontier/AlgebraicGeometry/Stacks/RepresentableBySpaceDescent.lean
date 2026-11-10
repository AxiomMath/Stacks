module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RepresentableByAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableByAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase
public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.MorphismRepresentableBySpaces.Criterion
public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.RepresentableBySpace.Characterization
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChange
public import StacksFrontier.CategoryTheory.FiberedCategory.FiberedInSetoids
public import StacksFrontier.CategoryTheory.FiberedCategory.PairIsoClassPresheaf
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Defs

/-!
# Representability by an algebraic space descends along a representable 1-morphism (Stacks 0300)

Let `r : 𝒲 ⟶ 𝒵` be a 1-morphism of categories fibred in groupoids over the big fppf site of `S`
which is representable by algebraic spaces, and suppose `𝒵` is *represented* by an algebraic space
in the sense of Stacks 04SV. Then so is `𝒲`.

## Main results

* `AlgebraicGeometry.isRepresentableByAlgebraicSpace_of_representable`: if `r : 𝒲 ⟶ 𝒵` is
  representable by algebraic spaces and `𝒵` is represented by an algebraic space, then so is `𝒲`.

## References

* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 0302](https://stacks.math.columbia.edu/tag/0302)
* [Stacks Project, Tag 02ZX](https://stacks.math.columbia.edu/tag/02ZX)
* [Stacks Project, Tag 02ZY](https://stacks.math.columbia.edu/tag/02ZY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.Limits

namespace AlgebraicGeometry

universe u v w u₁ v₁ u₂ v₂ u₃ v₃

private noncomputable def pullbackObjEquiv {C : Type u} [Category.{v} C]
    {F G H : C ⥤ Type w} (f : F ⟶ H) (g : G ⟶ H) (T : C) :
    (pullback f g).obj T ≃ Types.PullbackObj (f.app T) (g.app T) :=
  ((PreservesPullback.iso ((evaluation C (Type w)).obj T) f g).trans
    (Types.pullbackIsoPullback (f.app T) (g.app T))).toEquiv
private lemma pullbackObjEquiv_fst {C : Type u} [Category.{v} C]
    {F G H : C ⥤ Type w} (f : F ⟶ H) (g : G ⟶ H) (T : C)
    (x : (pullback f g).obj T) :
    (pullbackObjEquiv f g T x).1.1 = (pullback.fst f g).app T x := by
  change ((Types.pullbackIsoPullback (f.app T) (g.app T)).hom
    ((PreservesPullback.iso ((evaluation C (Type w)).obj T) f g).hom x)).1.1 = _
  rw [Types.pullbackIsoPullback_hom_fst]
  exact congrArg (fun h => h x)
    (PreservesPullback.iso_hom_fst ((evaluation C (Type w)).obj T) f g)
private lemma pullbackObjEquiv_snd {C : Type u} [Category.{v} C]
    {F G H : C ⥤ Type w} (f : F ⟶ H) (g : G ⟶ H) (T : C)
    (x : (pullback f g).obj T) :
    (pullbackObjEquiv f g T x).1.2 = (pullback.snd f g).app T x := by
  change ((Types.pullbackIsoPullback (f.app T) (g.app T)).hom
    ((PreservesPullback.iso ((evaluation C (Type w)).obj T) f g).hom x)).1.2 = _
  rw [Types.pullbackIsoPullback_hom_snd]
  exact congrArg (fun h => h x)
    (PreservesPullback.iso_hom_snd ((evaluation C (Type w)).obj T) f g)


-- Needed for the instance syntheses of `IsStronglyCartesian` in `isoClassMapOfCompEq` and of
-- `IsHomLift` in `pairClassFiberEquiv_map`.
set_option backward.isDefEq.respectTransparency false
private noncomputable def isoClassMapOfCompEq
    {C : Type u₁} [Category.{v₁, u₁} C]
    {X Y : Type u₂} [Category.{v₂, u₂} X] [Category.{v₂, u₂} Y]
    (p : X ⥤ C) (q : Y ⥤ C)
    [p.IsFiberedInSetoids] [q.IsFiberedInSetoids]
    (G : X ⥤ Y) (hG : G ⋙ q = p) : p.isoClassPresheaf ⟶ q.isoClassPresheaf := by
  let hGF : Functor.IsFibredOneMorphism p q G := {
    comp_eq := hG
    map_isStronglyCartesian := by
      intro R T f a b φ hφ
      let : q.IsHomLift f (G.map φ) := Functor.isHomLift_map_of_comp_eq hG f φ
      let hq := (inferInstance : q.IsFiberedInSetoids)
      exact hq.isFiberedInGroupoids.isStronglyCartesian_homLift f (G.map φ)
  }
  let mapClass (U : C) : p.isoClassPresheaf.obj (Opposite.op U) →
      q.isoClassPresheaf.obj (Opposite.op U) := Quotient.lift
    (fun x => Functor.isoClassMk q
      ((Functor.Fiber.mapOfComp p q G hG U).obj x))
    (fun x y h => Quotient.sound ((Functor.isIsomorphicSetoid_r_iff _ _).2 ⟨
      (Functor.Fiber.mapOfComp p q G hG U).mapIso
        (Functor.isIsomorphicSetoid_r_iff _ _ |>.1 h).some⟩))
  refine {
    app U := ↾mapClass U.unop
    naturality := ?_ }
  intro U V f
  ext c
  induction c using Quotient.ind with
  | _ x =>
    let y := (Functor.Fiber.mapOfComp p q G hG U.unop).obj x
    let φ := Functor.IsPreFibered.pullbackMap y.2 f.unop
    let φ' := G.map (Functor.IsPreFibered.pullbackMap x.2 f.unop)
    let : q.IsStronglyCartesian f.unop φ' :=
      hGF.map_isStronglyCartesian f.unop
        (Functor.IsPreFibered.pullbackMap x.2 f.unop) inferInstance
    let α := Functor.fiberIsoOfCartesian (p := q)
      (z := Functor.pullbackFiber q y f.unop)
      (z' := (Functor.Fiber.mapOfComp p q G hG V.unop).obj
        (Functor.pullbackFiber p x f.unop))
      (a := G.obj x.1) f.unop φ φ'
      (Functor.IsPreFibered.pullbackMap.IsCartesian y.2 f.unop)
      (by
        have : p.IsHomLift f.unop
            (Functor.IsPreFibered.pullbackMap x.2 f.unop) := inferInstance
        have := hGF.map_isStronglyCartesian f.unop
          (Functor.IsPreFibered.pullbackMap x.2 f.unop)
        infer_instance)
    have hα := Functor.isoClassMk_eq_of_iso α
    change mapClass V.unop
        (p.isoClassPresheaf.map f.unop.op (Functor.isoClassMk p x)) =
      q.isoClassPresheaf.map f.unop.op (mapClass U.unop (Functor.isoClassMk p x))
    rw [Functor.isoClassPresheaf_map_isoClassMk]
    change Functor.isoClassMk q
        ((Functor.Fiber.mapOfComp p q G hG V.unop).obj
          (Functor.pullbackFiber p x f.unop)) =
      q.isoClassPresheaf.map f (Functor.isoClassMk q y)
    have hrest := Functor.isoClassPresheaf_map_isoClassMk f.unop y
    exact hα.symm.trans hrest.symm

private lemma isoClassMapOfCompEq_app_isoClassMk
    {C : Type u₁} [Category.{v₁, u₁} C]
    {X Y : Type u₂} [Category.{v₂, u₂} X] [Category.{v₂, u₂} Y]
    (p : X ⥤ C) (q : Y ⥤ C)
    [p.IsFiberedInSetoids] [q.IsFiberedInSetoids]
    (G : X ⥤ Y) (hG : G ⋙ q = p) (U : C) (x : p.Fiber U) :
    (isoClassMapOfCompEq p q G hG).app (Opposite.op U) (Functor.isoClassMk p x) =
      Functor.isoClassMk q ((Functor.Fiber.mapOfComp p q G hG U).obj x) := by
  rfl

/-- Two lifts of the identity of `V` agree after composing with the image of an isomorphism of
the fibre. -/
private lemma comp_map_fiberInclusion_eq
    {C : Type u₁} [Category.{v₁, u₁} C]
    {X Y : Type u₂} [Category.{v₂, u₂} X] [Category.{v₂, u₂} Y]
    (p : X ⥤ C) (q : Y ⥤ C) [hq : q.IsFiberedInSetoids]
    (G : X ⥤ Y) (hG : G ⋙ q = p) {V : C} {x x' : p.Fiber V} (j : x ≅ x') {Z : Y}
    (φ : Z ⟶ G.obj x.1) (φ' : Z ⟶ G.obj x'.1)
    (hφ : q.IsHomLift (𝟙 V) φ) (hφ' : q.IsHomLift (𝟙 V) φ') :
    φ ≫ G.map (Functor.Fiber.fiberInclusion.map j.hom) = φ' := by
  have : q.IsHomLift (𝟙 V) (G.map (Functor.Fiber.fiberInclusion.map j.hom)) :=
    Functor.isHomLift_map_of_comp_eq hG (𝟙 V) _
  exact Functor.hom_unique_of_fiber_isThin q (𝟙 V) (hq.fiber_isThin V) _ _
    (by simpa using IsHomLift.comp q (𝟙 V) (𝟙 V) φ _) hφ'

/-- Pulling back along `m : f' ⟶ f` preserves the condition defining `pairClassFiberEquiv`. -/
private lemma isoClassMapOfCompEq_app_map_left
    {C : Type u₁} [Category.{v₁, u₁} C]
    {X Y : Type u₂} [Category.{v₂, u₂} X] [Category.{v₂, u₂} Y]
    (p : X ⥤ C) (q : Y ⥤ C) [p.IsFiberedInSetoids] [q.IsFiberedInSetoids]
    (G : X ⥤ Y) (hG : G ⋙ q = p) (U : C) (y : q.Fiber U) {f f' : Over U} (m : f' ⟶ f)
    (t : {a : p.isoClassPresheaf.obj (Opposite.op f.left) //
      (isoClassMapOfCompEq p q G hG).app (Opposite.op f.left) a =
        q.isoClassPresheaf.map f.hom.op (Functor.isoClassMk q y)}) :
    (isoClassMapOfCompEq p q G hG).app (Opposite.op f'.left)
        (p.isoClassPresheaf.map m.left.op t.1) =
      q.isoClassPresheaf.map f'.hom.op (Functor.isoClassMk q y) := by
  have hm : f.hom.op ≫ m.left.op = f'.hom.op := Quiver.Hom.unop_inj (Over.w m)
  rw [NatTrans.naturality_apply (isoClassMapOfCompEq p q G hG) m.left.op t.1, t.2, ← hm]
  simp only [Functor.map_comp, ConcreteCategory.comp_apply]

private noncomputable def pairClassFiberToPairData
    {C : Type u₁} [Category.{v₁, u₁} C]
    {X Y : Type u₂} [Category.{v₂, u₂} X] [Category.{v₂, u₂} Y]
    (p : X ⥤ C) (q : Y ⥤ C) [hp : p.IsFiberedInSetoids]
    [hq : q.IsFiberedInSetoids] (G : X ⥤ Y) (hG : G ⋙ q = p)
    (U : C) (y : q.Fiber U) (f : Over U)
    (t : {a : p.isoClassPresheaf.obj (Opposite.op f.left) //
      (isoClassMapOfCompEq p q G hG).app (Opposite.op f.left) a =
        q.isoClassPresheaf.map f.hom.op (Functor.isoClassMk q y)}) :
    Σ x : p.Fiber f.left, Σ φ : (q.pullbackFiber y f.hom).1 ⟶ G.obj x.1,
      PLift (q.IsHomLift (𝟙 f.left) φ) := by
  classical
  let x : p.Fiber f.left := Quotient.out t.1
  have hx : Functor.isoClassMk p x = t.1 := Quotient.out_eq t.1
  have hclass : (isoClassMapOfCompEq p q G hG).app (Opposite.op f.left)
      (Functor.isoClassMk p x) =
      q.isoClassPresheaf.map f.hom.op (Functor.isoClassMk q y) := by
    rw [hx]
    exact t.2
  have hpull : Functor.isoClassMk q
      ((Functor.Fiber.mapOfComp p q G hG f.left).obj x) =
      Functor.isoClassMk q (q.pullbackFiber y f.hom) := by
    calc
      _ = (isoClassMapOfCompEq p q G hG).app (Opposite.op f.left)
          (Functor.isoClassMk p x) :=
            (isoClassMapOfCompEq_app_isoClassMk p q G hG f.left x).symm
      _ = q.isoClassPresheaf.map f.hom.op (Functor.isoClassMk q y) := hclass
      _ = _ := Functor.isoClassPresheaf_map_isoClassMk f.hom y
  let i := Classical.choice (Functor.exists_iso_of_isoClassMk_eq hpull)
  let φ := Functor.Fiber.fiberInclusion.map i.inv
  have hφ : q.IsHomLift (𝟙 f.left) φ := i.inv.2
  exact ⟨x, φ, PLift.up hφ⟩

private noncomputable def pairClassFiberToPair
    {C : Type u₁} [Category.{v₁, u₁} C]
    {X Y : Type u₂} [Category.{v₂, u₂} X] [Category.{v₂, u₂} Y]
    (p : X ⥤ C) (q : Y ⥤ C) [hp : p.IsFiberedInSetoids]
    [hq : q.IsFiberedInSetoids] (G : X ⥤ Y) (hG : G ⋙ q = p)
    (U : C) (y : q.Fiber U) (f : Over U)
    (t : {a : p.isoClassPresheaf.obj (Opposite.op f.left) //
      (isoClassMapOfCompEq p q G hG).app (Opposite.op f.left) a =
        q.isoClassPresheaf.map f.hom.op (Functor.isoClassMk q y)}) :
    (PairIsoClass.presheaf G (Functor.chosenPullbacks q) y
      hp.isFiberedInGroupoids hq.isFiberedInGroupoids hG).obj (Opposite.op f) := by
  let d := pairClassFiberToPairData p q G hG U y f t
  exact PairIsoClass.mk G (Functor.chosenPullbacks q) y
    hp.isFiberedInGroupoids hq.isFiberedInGroupoids hG d.1 d.2.1 d.2.2.down

private noncomputable def pairClassToPairFiberData
    {C : Type u₁} [Category.{v₁, u₁} C]
    {X Y : Type u₂} [Category.{v₂, u₂} X] [Category.{v₂, u₂} Y]
    (p : X ⥤ C) (q : Y ⥤ C) [hp : p.IsFiberedInSetoids]
    [hq : q.IsFiberedInSetoids] (G : X ⥤ Y) (hG : G ⋙ q = p)
    (U : C) (y : q.Fiber U) (f : Over U)
    (t : (PairIsoClass.presheaf G (Functor.chosenPullbacks q) y
      hp.isFiberedInGroupoids hq.isFiberedInGroupoids hG).obj (Opposite.op f)) :
    Σ x : p.Fiber f.left, Σ φ : (q.pullbackFiber y f.hom).1 ⟶ G.obj x.1,
      {hφ : PLift (q.IsHomLift (𝟙 f.left) φ) //
        ((isoClassMapOfCompEq p q G hG).app (Opposite.op f.left)
            (Functor.isoClassMk p x) =
          q.isoClassPresheaf.map f.hom.op (Functor.isoClassMk q y)) ∧
        PairIsoClass.mk G (Functor.chosenPullbacks q) y
          hp.isFiberedInGroupoids hq.isFiberedInGroupoids hG x φ hφ.down = t} := by
  classical
  letI : p.IsFibered := hp.isFiberedInGroupoids.isFibered
  letI : q.IsFibered := hq.isFiberedInGroupoids.isFibered
  have hsurj := PairIsoClass.mk_surjective G (Functor.chosenPullbacks q)
    y hp.isFiberedInGroupoids hq.isFiberedInGroupoids hG t
  let x := Classical.choose hsurj
  let φ := Classical.choose (Classical.choose_spec hsurj)
  let hφ := Classical.choose (Classical.choose_spec (Classical.choose_spec hsurj))
  have hmk := Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec hsurj))
  letI : q.IsHomLift (𝟙 f.left) φ := hφ
  let ψ : q.pullbackFiber y f.hom ⟶ (Functor.Fiber.mapOfComp p q G hG f.left).obj x :=
    Functor.Fiber.homMk q f.left φ
  letI : IsGroupoid (q.Fiber f.left) := hq.isFiberedInGroupoids.fiber_isGroupoid f.left
  have hψ : IsIso ψ := by infer_instance
  have hclass :
      (isoClassMapOfCompEq p q G hG).app (Opposite.op f.left)
          (Functor.isoClassMk p x) =
        q.isoClassPresheaf.map f.hom.op (Functor.isoClassMk q y) := by
    calc
      _ = Functor.isoClassMk q ((Functor.Fiber.mapOfComp p q G hG f.left).obj x) :=
      isoClassMapOfCompEq_app_isoClassMk p q G hG f.left x
      _ = Functor.isoClassMk q (q.pullbackFiber y f.hom) :=
      Functor.isoClassMk_eq_of_iso (asIso ψ).symm
      _ = q.isoClassPresheaf.map f.hom.op (Functor.isoClassMk q y) :=
      (Functor.isoClassPresheaf_map_isoClassMk f.hom y).symm
  exact ⟨x, φ, ⟨PLift.up hφ, hclass, hmk⟩⟩

private noncomputable def pairClassToPairFiber
    {C : Type u₁} [Category.{v₁, u₁} C]
    {X Y : Type u₂} [Category.{v₂, u₂} X] [Category.{v₂, u₂} Y]
    (p : X ⥤ C) (q : Y ⥤ C) [hp : p.IsFiberedInSetoids]
    [hq : q.IsFiberedInSetoids] (G : X ⥤ Y) (hG : G ⋙ q = p)
    (U : C) (y : q.Fiber U) (f : Over U)
    (t : (PairIsoClass.presheaf G (Functor.chosenPullbacks q) y
      hp.isFiberedInGroupoids hq.isFiberedInGroupoids hG).obj (Opposite.op f)) :
    {a : p.isoClassPresheaf.obj (Opposite.op f.left) //
      (isoClassMapOfCompEq p q G hG).app (Opposite.op f.left) a =
        q.isoClassPresheaf.map f.hom.op (Functor.isoClassMk q y)} := by
  let d := pairClassToPairFiberData p q G hG U y f t
  exact ⟨Functor.isoClassMk p d.1, d.2.2.2.1⟩

private noncomputable def pairClassFiberEquiv
    {C : Type u₁} [Category.{v₁, u₁} C]
    {X Y : Type u₂} [Category.{v₂, u₂} X] [Category.{v₂, u₂} Y]
    (p : X ⥤ C) (q : Y ⥤ C) [hp : p.IsFiberedInSetoids]
    [hq : q.IsFiberedInSetoids] (G : X ⥤ Y) (hG : G ⋙ q = p)
    (U : C) (y : q.Fiber U) (f : Over U) :
    {a : p.isoClassPresheaf.obj (Opposite.op f.left) //
      (isoClassMapOfCompEq p q G hG).app (Opposite.op f.left) a =
        q.isoClassPresheaf.map f.hom.op (Functor.isoClassMk q y)} ≃
      (PairIsoClass.presheaf G (Functor.chosenPullbacks q) y
        hp.isFiberedInGroupoids hq.isFiberedInGroupoids hG).obj (Opposite.op f) := by
  classical
  letI : p.IsFibered := hp.isFiberedInGroupoids.isFibered
  letI : q.IsFibered := hq.isFiberedInGroupoids.isFibered
  refine {
    toFun := pairClassFiberToPair p q G hG U y f
    invFun := pairClassToPairFiber p q G hG U y f
    left_inv := ?_
    right_inv := ?_ }
  · intro t
    apply Subtype.ext
    let d := pairClassFiberToPairData p q G hG U y f t
    let z := pairClassFiberToPair p q G hG U y f t
    let e := pairClassToPairFiberData p q G hG U y f z
    let eφ := e.2.1
    let ehφ : PLift (q.IsHomLift (𝟙 f.left) eφ) := e.2.2.1
    have hpair : PairIsoClass.mk G (Functor.chosenPullbacks q) y
        hp.isFiberedInGroupoids hq.isFiberedInGroupoids hG e.1 eφ ehφ.down =
        PairIsoClass.mk G (Functor.chosenPullbacks q) y
          hp.isFiberedInGroupoids hq.isFiberedInGroupoids hG d.1 d.2.1 d.2.2.down := by
      calc
        _ = z := e.2.2.2.2
        _ = _ := rfl
    obtain ⟨j, hj⟩ := (PairIsoClass.mk_eq_mk_iff G (Functor.chosenPullbacks q)
      y hp.isFiberedInGroupoids hq.isFiberedInGroupoids hG
      (f := f) e.1 d.1 eφ ehφ.down d.2.1 d.2.2.down).1 hpair
    change Functor.isoClassMk p e.1 = t.1
    calc
      _ = Functor.isoClassMk p d.1 := Functor.isoClassMk_eq_of_iso j
      _ = t.1 := by
        change Functor.isoClassMk p (Quotient.out t.1) = t.1
        exact Quotient.out_eq t.1
  · intro t
    let d := pairClassToPairFiberData p q G hG U y f t
    let dφ := d.2.1
    let dhφ : PLift (q.IsHomLift (𝟙 f.left) dφ) := d.2.2.1
    let dclassEq := d.2.2.2.1
    let dmk := d.2.2.2.2
    let s : {a : p.isoClassPresheaf.obj (Opposite.op f.left) //
        (isoClassMapOfCompEq p q G hG).app (Opposite.op f.left) a =
          q.isoClassPresheaf.map f.hom.op (Functor.isoClassMk q y)} :=
      ⟨Functor.isoClassMk p d.1, dclassEq⟩
    let e := pairClassFiberToPairData p q G hG U y f s
    have hclasses : Functor.isoClassMk p e.1 = Functor.isoClassMk p d.1 := by
      change Functor.isoClassMk p (Quotient.out (Functor.isoClassMk p d.1)) = _
      exact Quotient.out_eq (Functor.isoClassMk p d.1)
    let j := Classical.choice (Functor.exists_iso_of_isoClassMk_eq hclasses)
    have hcomm := comp_map_fiberInclusion_eq p q G hG j e.2.1 d.2.1 e.2.2.down dhφ.down
    have hpair : PairIsoClass.mk G (Functor.chosenPullbacks q) y
        hp.isFiberedInGroupoids hq.isFiberedInGroupoids hG e.1 e.2.1 e.2.2.down =
        PairIsoClass.mk G (Functor.chosenPullbacks q) y
          hp.isFiberedInGroupoids hq.isFiberedInGroupoids hG d.1 d.2.1 dhφ.down :=
      (PairIsoClass.mk_eq_mk_iff G (Functor.chosenPullbacks q)
        y hp.isFiberedInGroupoids hq.isFiberedInGroupoids hG
        (f := f) e.1 d.1 e.2.1 e.2.2.down dφ dhφ.down).2 ⟨j, hcomm⟩
    change pairClassFiberToPair p q G hG U y f s = t
    calc
      _ = PairIsoClass.mk G (Functor.chosenPullbacks q) y
          hp.isFiberedInGroupoids hq.isFiberedInGroupoids hG e.1 e.2.1 e.2.2.down := by
            rfl
      _ = PairIsoClass.mk G (Functor.chosenPullbacks q) y
          hp.isFiberedInGroupoids hq.isFiberedInGroupoids hG d.1 d.2.1 d.2.2.1.down := hpair
      _ = t := dmk

private lemma pairClassFiberEquiv_map
    {C : Type u₁} [Category.{v₁, u₁} C]
    {X Y : Type u₂} [Category.{v₂, u₂} X] [Category.{v₂, u₂} Y]
    (p : X ⥤ C) (q : Y ⥤ C) [hp : p.IsFiberedInSetoids]
    [hq : q.IsFiberedInSetoids] (G : X ⥤ Y) (hG : G ⋙ q = p)
    (U : C) (y : q.Fiber U) {f f' : Over U} (m : f' ⟶ f)
    (t : {a : p.isoClassPresheaf.obj (Opposite.op f.left) //
      (isoClassMapOfCompEq p q G hG).app (Opposite.op f.left) a =
        q.isoClassPresheaf.map f.hom.op (Functor.isoClassMk q y)}) :
    pairClassFiberEquiv p q G hG U y f'
        ⟨p.isoClassPresheaf.map m.left.op t.1,
          isoClassMapOfCompEq_app_map_left p q G hG U y m t⟩ =
      (PairIsoClass.presheaf G (Functor.chosenPullbacks q) y
        hp.isFiberedInGroupoids hq.isFiberedInGroupoids hG).map m.op
        (pairClassFiberEquiv p q G hG U y f t) := by
  classical
  let : p.IsFibered := hp.isFiberedInGroupoids.isFibered
  let : q.IsFibered := hq.isFiberedInGroupoids.isFibered
  let t' : {a : p.isoClassPresheaf.obj (Opposite.op f'.left) //
      (isoClassMapOfCompEq p q G hG).app (Opposite.op f'.left) a =
        q.isoClassPresheaf.map f'.hom.op (Functor.isoClassMk q y)} :=
    ⟨p.isoClassPresheaf.map m.left.op t.1,
      isoClassMapOfCompEq_app_map_left p q G hG U y m t⟩
  let d := pairClassFiberToPairData p q G hG U y f t
  let d' := pairClassFiberToPairData p q G hG U y f' t'
  have hdclass : Functor.isoClassMk p d.1 = t.1 := by
    change Functor.isoClassMk p (Quotient.out t.1) = t.1
    exact Quotient.out_eq t.1
  have hd'class : Functor.isoClassMk p d'.1 = t'.1 := by
    change Functor.isoClassMk p (Quotient.out t'.1) = t'.1
    exact Quotient.out_eq t'.1
  obtain ⟨x₁, φ₁, hφ₁, χ, hχ, hsq⟩ :=
    PairIsoClass.exists_pair_of_hom G (Functor.chosenPullbacks q) y
      hp.isFiberedInGroupoids hq.isFiberedInGroupoids hG m d.1 d.2.1 d.2.2.down
  have hmap := PairIsoClass.presheaf_map_mk G (Functor.chosenPullbacks q) y
    hp.isFiberedInGroupoids hq.isFiberedInGroupoids hG m d.1 d.2.1 d.2.2.down
    x₁ φ₁ hφ₁ χ hχ hsq
  have hχcart : p.IsCartesian m.left χ := by
    have hstrong : p.IsStronglyCartesian m.left χ :=
      hp.isFiberedInGroupoids.isStronglyCartesian_homLift m.left χ
    infer_instance
  have hclass₁ : Functor.isoClassMk p x₁ = t'.1 := by
    calc
      _ = p.isoClassPresheaf.map m.left.op (Functor.isoClassMk p d.1) := by
        rw [Functor.isoClassPresheaf_map_isoClassMk]
        exact Functor.isoClassMk_eq_pullbackFiber_of_isCartesian
          m.left d.1 x₁ χ hχ hχcart
      _ = p.isoClassPresheaf.map m.left.op t.1 :=
        congrArg (p.isoClassPresheaf.map m.left.op) hdclass
      _ = t'.1 := rfl
  have hclass₂ : Functor.isoClassMk p d'.1 = Functor.isoClassMk p x₁ :=
    hd'class.trans hclass₁.symm
  obtain ⟨j⟩ := Functor.exists_iso_of_isoClassMk_eq hclass₂
  have hcomm := comp_map_fiberInclusion_eq p q G hG j d'.2.1 φ₁ d'.2.2.down hφ₁
  have hmk : pairClassFiberEquiv p q G hG U y f' t' =
      (PairIsoClass.presheaf G (Functor.chosenPullbacks q) y
        hp.isFiberedInGroupoids hq.isFiberedInGroupoids hG).map m.op
        (pairClassFiberEquiv p q G hG U y f t) := by
    change PairIsoClass.mk G (Functor.chosenPullbacks q) y
        hp.isFiberedInGroupoids hq.isFiberedInGroupoids hG
        d'.1 d'.2.1 d'.2.2.down =
      (PairIsoClass.presheaf G (Functor.chosenPullbacks q) y
        hp.isFiberedInGroupoids hq.isFiberedInGroupoids hG).map m.op
        (PairIsoClass.mk G (Functor.chosenPullbacks q) y
          hp.isFiberedInGroupoids hq.isFiberedInGroupoids hG
          d.1 d.2.1 d.2.2.down)
    rw [hmap]
    exact (PairIsoClass.mk_eq_mk_iff G (Functor.chosenPullbacks q) y
      hp.isFiberedInGroupoids hq.isFiberedInGroupoids hG (f := f')
      d'.1 x₁ d'.2.1 d'.2.2.down φ₁ hφ₁).2 ⟨j, hcomm⟩
  simpa only [t'] using hmk


/-- If `r : 𝒲 ⟶ 𝒵` is representable by algebraic spaces and `𝒵` is represented by an algebraic
space, then so is `𝒲`. -/
theorem isRepresentableByAlgebraicSpace_of_representable
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒲 𝒵 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
    (r : 𝒲 ⟶ 𝒵)
    (hr : IsRepresentableByAlgebraicSpaces B S hS r.hom)
    (h𝒵 : IsRepresentableByAlgebraicSpace B S hS 𝒵) :
    IsRepresentableByAlgebraicSpace B S hS 𝒲 := by
  have hZsetoid : 𝒵.val.p.IsFiberedInSetoids :=
    (isRepresentableByAlgebraicSpace_iff B S hS 𝒵).mp h𝒵 |>.1
  have hZfib : 𝒵.val.p.IsFibered := hZsetoid.isFiberedInGroupoids.isFibered
  let : 𝒵.val.p.IsFibered := hZfib
  let cZ : 𝒵.val.p.ChoiceOfPullbacks := Functor.chosenPullbacks 𝒵.val.p
  have hrFaithful :=
    ((isRepresentableByAlgebraicSpaces_iff_associatedMap B S hS r
      cZ).mp hr).1
  have hPsetoid : 𝒲.val.p.IsFiberedInSetoids := by
    refine ⟨𝒲.2, fun U x y => ⟨fun a b => ?_⟩⟩
    exact (hrFaithful U).map_injective ((hZsetoid.fiber_isThin U _ _).allEq _ _)
  have hZclasses :=
    (isRepresentableByAlgebraicSpace_iff B S hS 𝒵).mp h𝒵 |>.2
  have hrCriterion :=
    (isRepresentableByAlgebraicSpaces_iff_associatedMap B S hS r cZ).mp hr
  dsimp [IsAlgebraicSpaceIsoClassPresheaf] at hZclasses
  rcases hZclasses with ⟨FZ, hFZ, eZ, hnatZ⟩
  let representative (U : BigFppfOver B S hS)
      (z : FZ.obj (Opposite.op U)) : 𝒵.val.p.Fiber U :=
    Quotient.out ((eZ (Opposite.op U)).symm z)
  let relativeModel (U : BigFppfOver B S hS)
      (z : FZ.obj (Opposite.op U)) :=
    Classical.choose (hrCriterion.2 U (representative U z))
  let classMap := isoClassMapOfCompEq 𝒲.val.p 𝒵.val.p
    (CatFiberedInGroupoids.homFunctor r)
    (CatFiberedInGroupoids.homFunctor_comp_p r)
  let localId (U : BigFppfOver B S hS) :
      BigFppfOver B U.left.1 U.left.2 :=
    Over.mk (𝟙 (B.obj U.left.2))
  let localIdOver (U : BigFppfOver B S hS) : Over U :=
    U.iteratedSliceBackward.obj (localId U)
  have localIdOver_left (U : BigFppfOver B S hS) :
      (localIdOver U).left = U := by
    cases U
    rfl
  have localIdOver_hom (U : BigFppfOver B S hS) :
      (localIdOver U).hom = 𝟙 U := by
    apply Over.OverMorphism.ext
    rfl
  let smallValue (U : BigFppfOver B S hS) : Type u :=
    Σ z : FZ.obj (Opposite.op U),
      (relativeModel U z).obj (Opposite.op (localId U))
  let relativeEquiv (U : BigFppfOver B S hS)
      (z : FZ.obj (Opposite.op U)) :=
    Classical.choose
      (Classical.choose_spec (hrCriterion.2 U (representative U z))).2
  let fiberModelEquiv (U : BigFppfOver B S hS)
      (z : FZ.obj (Opposite.op U)) :
      {a : 𝒲.val.p.isoClassPresheaf.obj
          (Opposite.op (localIdOver U).left) //
        classMap.app (Opposite.op (localIdOver U).left) a =
          𝒵.val.p.isoClassPresheaf.map (localIdOver U).hom.op
            (Functor.isoClassMk 𝒵.val.p (representative U z))} ≃
        (relativeModel U z).obj (Opposite.op (localId U)) :=
    (pairClassFiberEquiv 𝒲.val.p 𝒵.val.p
      (CatFiberedInGroupoids.homFunctor r)
      (CatFiberedInGroupoids.homFunctor_comp_p r)
      U (representative U z) (localIdOver U)).trans
      (relativeEquiv U z (Opposite.op (localId U)))
  let fiberEquiv (U : BigFppfOver B S hS)
      (z : FZ.obj (Opposite.op U)) (f : Over U) :
      {a : 𝒲.val.p.isoClassPresheaf.obj (Opposite.op f.left) //
        classMap.app (Opposite.op f.left) a =
          𝒵.val.p.isoClassPresheaf.map f.hom.op
            (Functor.isoClassMk 𝒵.val.p (representative U z))} ≃
        (relativeModel U z).obj
          (Opposite.op (U.iteratedSliceForward.obj f)) := by
    let Q := PairIsoClass.presheaf (CatFiberedInGroupoids.homFunctor r)
      cZ (representative U z)
      hPsetoid.isFiberedInGroupoids hZsetoid.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor_comp_p r)
    let bff := U.iteratedSliceBackward.obj (U.iteratedSliceForward.obj f)
    let u : f ≅ bff := (Over.iteratedSliceEquiv U).unitIso.app f
    have e : Q.obj (Opposite.op bff) ≃
        (relativeModel U z).obj
          (Opposite.op (U.iteratedSliceForward.obj f)) :=
      relativeEquiv U z (Opposite.op (U.iteratedSliceForward.obj f))
    exact (pairClassFiberEquiv 𝒲.val.p 𝒵.val.p
      (CatFiberedInGroupoids.homFunctor r)
      (CatFiberedInGroupoids.homFunctor_comp_p r)
      U (representative U z) f).trans
        ((Q.mapIso u.symm.op).toEquiv.trans e)
  have fiberEquiv_map (U : BigFppfOver B S hS)
      (z : FZ.obj (Opposite.op U)) {f f' : Over U} (m : f' ⟶ f)
      (t : {a : 𝒲.val.p.isoClassPresheaf.obj (Opposite.op f.left) //
        classMap.app (Opposite.op f.left) a =
          𝒵.val.p.isoClassPresheaf.map f.hom.op
            (Functor.isoClassMk 𝒵.val.p (representative U z))}) :
      fiberEquiv U z f'
        ⟨𝒲.val.p.isoClassPresheaf.map m.left.op t.1,
          isoClassMapOfCompEq_app_map_left _ _ _ _ U (representative U z) m t⟩ =
        (relativeModel U z).map (U.iteratedSliceForward.op.map m.op)
          (fiberEquiv U z f t) := by
    let hrel := Classical.choose_spec
      (Classical.choose_spec (hrCriterion.2 U (representative U z))).2
    let Q := PairIsoClass.presheaf (CatFiberedInGroupoids.homFunctor r)
      cZ (representative U z)
      hPsetoid.isFiberedInGroupoids hZsetoid.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor_comp_p r)
    let η := (Over.iteratedSliceEquiv U).unitIso
    change relativeEquiv U z _ (Q.map (η.inv.app f').op
        (pairClassFiberEquiv 𝒲.val.p 𝒵.val.p
          (CatFiberedInGroupoids.homFunctor r)
          (CatFiberedInGroupoids.homFunctor_comp_p r)
          U (representative U z) f' _)) =
      (relativeModel U z).map (U.iteratedSliceForward.op.map m.op)
        (relativeEquiv U z _ (Q.map (η.inv.app f).op
          (pairClassFiberEquiv 𝒲.val.p 𝒵.val.p
            (CatFiberedInGroupoids.homFunctor r)
            (CatFiberedInGroupoids.homFunctor_comp_p r)
            U (representative U z) f t)))
    rw [pairClassFiberEquiv_map]
    rw [← hrel]
    apply congrArg (relativeEquiv U z _)
    change Q.map (η.inv.app f').op (Q.map m.op _) =
      Q.map ((U.iteratedSliceForward ⋙ U.iteratedSliceBackward).map m).op
        (Q.map (η.inv.app f).op _)
    calc
      _ = Q.map (m.op ≫ (η.inv.app f').op) _ :=
        (Q.map_comp_apply _ _ _).symm
      _ = Q.map ((η.inv.app f).op ≫
          ((U.iteratedSliceForward ⋙ U.iteratedSliceBackward).map m).op) _ :=
        congrArg (fun k => Q.map k _)
          (congrArg Quiver.Hom.op (η.inv.naturality m).symm)
      _ = _ := Q.map_comp_apply _ _ _
  have representative_class (U : BigFppfOver B S hS)
      (z : FZ.obj (Opposite.op U)) :
      eZ (Opposite.op U) (Functor.isoClassMk 𝒵.val.p (representative U z)) = z := by
    calc
      _ = eZ (Opposite.op U) ((eZ (Opposite.op U)).symm z) := by
        congr 1
        exact Quotient.out_eq ((eZ (Opposite.op U)).symm z)
      _ = z := Equiv.apply_symm_apply _ _
  have representative_map (U : BigFppfOver B S hS) (z : FZ.obj (Opposite.op U))
      (T : BigFppfOver B S hS) (τ : T ⟶ U) :
      eZ (Opposite.op T) (𝒵.val.p.isoClassPresheaf.map τ.op
        (Functor.isoClassMk 𝒵.val.p (representative U z))) = FZ.map τ.op z := by
    rw [hnatZ τ.op, representative_class]
  have representative_class_at_localId (U : BigFppfOver B S hS)
      (z : FZ.obj (Opposite.op U)) :
      eZ (Opposite.op (localIdOver U).left)
      (𝒵.val.p.isoClassPresheaf.map (localIdOver U).hom.op
          (Functor.isoClassMk 𝒵.val.p (representative U z))) = z := by
    cases U with
    | mk V R f =>
      let U' : BigFppfOver B S hS := ⟨V, R, f⟩
      have h := representative_map U' z _ (localIdOver U').hom
      have hmap : FZ.map (𝟙 (Opposite.op U')) z = z :=
        Functor.map_id_apply FZ (Opposite.op U') z
      simpa [U', localIdOver_left, localIdOver_hom, op_id] using h.trans hmap
  let classEquiv (U : BigFppfOver B S hS) :
      𝒲.val.p.isoClassPresheaf.obj (Opposite.op U) ≃ smallValue U := by
    classical
    refine {
      toFun := fun a => ?_
      invFun := fun s => ?_
      left_inv := ?_
      right_inv := ?_ }
    · let z := eZ (Opposite.op U) (classMap.app (Opposite.op U) a)
      have hsame : classMap.app (Opposite.op U) a =
          Functor.isoClassMk 𝒵.val.p (representative U z) := by
        apply (eZ (Opposite.op U)).injective
        calc
          _ = z := rfl
          _ = eZ (Opposite.op U) (Functor.isoClassMk 𝒵.val.p (representative U z)) :=
            (representative_class U z).symm
      have hclass : classMap.app (Opposite.op (localIdOver U).left) a =
          𝒵.val.p.isoClassPresheaf.map (localIdOver U).hom.op
            (Functor.isoClassMk 𝒵.val.p (representative U z)) := by
        apply (eZ (Opposite.op (localIdOver U).left)).injective
        have hnatClass := classMap.naturality_apply (localIdOver U).hom.op a
        calc
          eZ (Opposite.op (localIdOver U).left)
              (classMap.app (Opposite.op (localIdOver U).left) a) =
              eZ (Opposite.op (localIdOver U).left)
                (𝒵.val.p.isoClassPresheaf.map (localIdOver U).hom.op
                  (classMap.app (Opposite.op U) a)) := by
            apply congrArg (eZ (Opposite.op (localIdOver U).left))
            have hid : 𝒲.val.p.isoClassPresheaf.map
                (localIdOver U).hom.op a = a := by
              change 𝒲.val.p.isoClassPresheaf.map
                (𝟙 (Opposite.op U)) a = a
              exact Functor.map_id_apply _ _ _
            nth_rewrite 1 [← hid]
            exact hnatClass
          _ = eZ (Opposite.op (localIdOver U).left)
              (𝒵.val.p.isoClassPresheaf.map (localIdOver U).hom.op
                (Functor.isoClassMk 𝒵.val.p (representative U z))) := by
                  apply congrArg (eZ (Opposite.op (localIdOver U).left))
                  rw [hsame]
      exact ⟨z, (fiberModelEquiv U z) ⟨a, hclass⟩⟩
    · exact (fiberModelEquiv U s.1).symm s.2 |>.1
    · intro a
      simp only [Equiv.symm_apply_apply]
    · intro s
      cases U with
      | mk V R f =>
        let U' : BigFppfOver B S hS := ⟨V, R, f⟩
        cases s with
        | mk z y =>
          dsimp
          generalize hx : ((fiberModelEquiv U' z).symm y).1 = x at *
          have hfirst :
              eZ (Opposite.op (localIdOver U').left)
                (classMap.app (Opposite.op (localIdOver U').left) x) = z := by
            have h := ((fiberModelEquiv U' z).symm y).2
            rw [hx] at h
            exact (congrArg (eZ (Opposite.op (localIdOver U').left)) h).trans
              (representative_class_at_localId U' z)
          have hfirst' : eZ (Opposite.op U') (classMap.app (Opposite.op U') x) = z := by
            convert hfirst using 1
            · exact congrArg (fun T => FZ.obj (Opposite.op T)) (localIdOver_left U')
            · cases localIdOver_left U'
              rfl
          apply Sigma.ext
          · simpa [U'] using hfirst'
          · cases hfirst'
            let e := fiberModelEquiv U'
              (eZ (Opposite.op U') (classMap.app (Opposite.op U') x))
            change e ⟨x, _⟩ ≍ y
            apply heq_of_eq
            calc
              _ = e (e.symm y) := by
                apply congrArg e
                apply Subtype.ext
                exact hx.symm
              _ = y := Equiv.apply_symm_apply e y
  let F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u := {
    obj U := smallValue U.unop
    map := fun {U V} f => ↾fun x =>
      classEquiv V.unop
        (𝒲.val.p.isoClassPresheaf.map f ((classEquiv U.unop).symm x))
    map_id := by
      intro U
      apply ConcreteCategory.hom_ext
      intro x
      simp
    map_comp := by
      intro U V W f g
      apply ConcreteCategory.hom_ext
      intro x
      simp [Functor.map_comp]
  }
  let a : F ⟶ FZ := {
    app U := ↾fun x => x.1
    naturality := by
      intro U V f
      ext x
      let b := (classEquiv U.unop).symm x
      have hb : (classEquiv U.unop b).1 = x.1 :=
        congrArg Sigma.fst ((classEquiv U.unop).apply_symm_apply x)
      calc
        _ = eZ V
            (𝒵.val.p.isoClassPresheaf.map f
              (classMap.app U b)) := by
              change eZ V
                (classMap.app V
                  (𝒲.val.p.isoClassPresheaf.map f b)) = _
              congr 1
              exact classMap.naturality_apply f b
        _ = FZ.map f (eZ U (classMap.app U b)) :=
          hnatZ f (classMap.app U b)
        _ = FZ.map f x.1 := by
          change FZ.map f ((classEquiv U.unop b).1) = _
          exact congrArg (FZ.map f) hb
  }
  have ha : Space.IsRepresentableByAlgebraicSpaces B S hS a := by
    intro U ξ
    let z := ξ.app (Opposite.op U) (𝟙 U)
    let H := relativeModel U z
    have hH : IsAlgebraicSpace B U.left.1 U.left.2 H := by
      dsimp [H, relativeModel]
      exact (Classical.choose_spec
        (hrCriterion.2 U (representative U z))).1
    let H' := (OverShriek.relocalizePresheafFunctor U.hom).obj H
    have hH' : IsAlgebraicSpace B S hS H' :=
      isAlgebraicSpace_viewOver B U.left.1 S U.left.2 hS U.hom H hH
    have hIso : pullback ξ a ≅ H' := by
      let relocalizedSectionEquiv (T : BigFppfOver B S hS) :
          H'.obj (Opposite.op T) ≃
            {p : Σ ψ : T.left ⟶ B.obj U.left.2,
              H.obj (Opposite.op (Over.mk ψ)) // p.1 ≫ U.hom = T.hom} := by
        dsimp [H', OverShriek.relocalizePresheafFunctor,
          OverShriek.presheafFunctorToOver, OverShriek.fiberFunctor,
          OverShriek.fiber, OverShriek.presheafFunctor,
          OverShriek.presheafToYoneda, Functor.toOver,
          Functor.toCostructuredArrow]
        exact {
          toFun := fun x => ⟨x.1, by simpa using x.2⟩
          invFun := fun x => ⟨x.1, by simpa using x.2⟩
          left_inv := by intro x; rfl
          right_inv := by intro x; rfl }
      let pullbackAtEquiv (T : BigFppfOver B S hS) :
          (pullback ξ a).obj (Opposite.op T) ≃
            Types.PullbackObj (ξ.app (Opposite.op T)) (a.app (Opposite.op T)) :=
        pullbackObjEquiv ξ a (Opposite.op T)
      have hξ (T : BigFppfOver B S hS) (τ : T ⟶ U) :
          ξ.app (Opposite.op T) τ = FZ.map τ.op z := by
        simpa [z] using NatTrans.naturality_apply ξ τ.op (𝟙 U)
      have classFiberCondition (T : BigFppfOver B S hS)
          (τ : T ⟶ U) (s : smallValue T)
          (hs : ξ.app (Opposite.op T) τ = s.1) :
          classMap.app (Opposite.op T) ((classEquiv T).symm s) =
            𝒵.val.p.isoClassPresheaf.map τ.op
              (Functor.isoClassMk 𝒵.val.p (representative U z)) := by
        apply (eZ (Opposite.op T)).injective
        calc
          _ = s.1 := congrArg Sigma.fst ((classEquiv T).apply_symm_apply s)
          _ = ξ.app (Opposite.op T) τ := hs.symm
          _ = FZ.map τ.op z := hξ T τ
          _ = (eZ (Opposite.op T))
              (𝒵.val.p.isoClassPresheaf.map τ.op
                (Functor.isoClassMk 𝒵.val.p (representative U z))) :=
            (representative_map U z T τ).symm
      let sectionType (T : BigFppfOver B S hS) :=
        {p : Σ ψ : T.left ⟶ B.obj U.left.2,
          H.obj (Opposite.op (Over.mk ψ)) // p.1 ≫ U.hom = T.hom}
      let toSection (T : BigFppfOver B S hS)
          (x : Types.PullbackObj (ξ.app (Opposite.op T)) (a.app (Opposite.op T))) :
          sectionType T := by
        let τ : T ⟶ U := x.1.1
        let s : smallValue T := x.1.2
        let α := (classEquiv T).symm s
        have hs : ξ.app (Opposite.op T) τ = s.1 := by
          simpa [a] using x.2
        refine ⟨⟨τ.left,
          (fiberEquiv U z (Over.mk τ)) ⟨α, classFiberCondition T τ s hs⟩⟩, ?_⟩
        exact τ.w
      let fromSection (T : BigFppfOver B S hS)
          (x : sectionType T) :
          Types.PullbackObj (ξ.app (Opposite.op T)) (a.app (Opposite.op T)) := by
        let τ : T ⟶ U := Over.homMk x.1.1 x.2
        let α := (fiberEquiv U z (Over.mk τ)).symm x.1.2
        let s : smallValue T := classEquiv T α.1
        have hs : s.1 = ξ.app (Opposite.op T) τ := by
          calc
            _ = (eZ (Opposite.op T))
                (classMap.app (Opposite.op T) α.1) := rfl
            _ = (eZ (Opposite.op T))
                (𝒵.val.p.isoClassPresheaf.map τ.op
                  (Functor.isoClassMk 𝒵.val.p (representative U z))) :=
                    congrArg (eZ (Opposite.op T)) α.2
            _ = FZ.map τ.op z := representative_map U z T τ
            _ = ξ.app (Opposite.op T) τ := (hξ T τ).symm
        refine ⟨⟨τ, s⟩, ?_⟩
        simpa [a] using hs.symm
      let comparisonEquiv (T : BigFppfOver B S hS) :
          Types.PullbackObj (ξ.app (Opposite.op T)) (a.app (Opposite.op T)) ≃
            sectionType T := {
        toFun := toSection T
        invFun := fromSection T
        left_inv := by
          intro x
          apply Subtype.ext
          apply Prod.ext
          · exact Over.OverMorphism.ext rfl
          · simp [toSection, fromSection, Equiv.apply_symm_apply]
        right_inv := by
          intro x
          apply Subtype.ext
          apply Sigma.ext
          · rfl
          · simp [toSection, fromSection, Equiv.apply_symm_apply]
      }
      let componentEquiv (T : BigFppfOver B S hS) :
          (pullback ξ a).obj (Opposite.op T) ≃ H'.obj (Opposite.op T) :=
        (pullbackAtEquiv T).trans
          ((comparisonEquiv T).trans (relocalizedSectionEquiv T).symm)
      refine NatIso.ofComponents (fun T => (componentEquiv T.unop).toIso) ?_
      intro T T' k
      ext x
      let t := pullbackAtEquiv T.unop x
      let t' : Types.PullbackObj (ξ.app T') (a.app T') :=
        ⟨⟨k.unop ≫ t.1.1, F.map k t.1.2⟩, by
          change ξ.app T' ((yoneda.obj U).map k t.1.1) =
            a.app T' (F.map k t.1.2)
          rw [ξ.naturality_apply, a.naturality_apply, t.2]⟩
      have ht : pullbackAtEquiv T'.unop ((pullback ξ a).map k x) = t' := by
        apply Subtype.ext
        apply Prod.ext
        · change (pullbackObjEquiv ξ a T' ((pullback ξ a).map k x)).1.1 =
            (yoneda.obj U).map k (pullbackObjEquiv ξ a T x).1.1
          rw [pullbackObjEquiv_fst, pullbackObjEquiv_fst]
          exact (pullback.fst ξ a).naturality_apply k x
        · change (pullbackObjEquiv ξ a T' ((pullback ξ a).map k x)).1.2 =
            F.map k (pullbackObjEquiv ξ a T x).1.2
          rw [pullbackObjEquiv_snd, pullbackObjEquiv_snd]
          exact (pullback.snd ξ a).naturality_apply k x
      change componentEquiv T'.unop ((pullback ξ a).map k x) =
        H'.map k (componentEquiv T.unop x)
      apply (relocalizedSectionEquiv T'.unop).injective
      apply Subtype.ext
      change (toSection T'.unop
          (pullbackAtEquiv T'.unop ((pullback ξ a).map k x))).1 =
        ⟨k.unop.left ≫ (toSection T.unop t).1.1,
          H.map (Over.homMk k.unop.left rfl :
            Over.mk (k.unop.left ≫ (toSection T.unop t).1.1) ⟶
              Over.mk (toSection T.unop t).1.1).op (toSection T.unop t).1.2⟩
      rw [ht]
      apply Sigma.ext
      · rfl
      apply heq_of_eq
      dsimp only [toSection, t']
      have hm := fiberEquiv_map U z
        (Over.homMk k.unop rfl : Over.mk (k.unop ≫ t.1.1) ⟶ Over.mk t.1.1)
        ⟨(classEquiv T.unop).symm t.1.2,
          classFiberCondition T.unop t.1.1 t.1.2 t.2⟩
      convert hm using 1
      · rfl
      · exact congrArg (fiberEquiv U z (Over.mk (k.unop ≫ t.1.1)))
          (Subtype.ext ((classEquiv T'.unop).symm_apply_apply _))
      · rfl
    exact isAlgebraicSpace_of_iso B S hS hIso hH'
  have hFAlg := isAlgebraicSpace_of_isRepresentableByAlgebraicSpaces
    B S hS a ha hFZ
  have hClasses : IsAlgebraicSpaceIsoClassPresheaf B S hS 𝒲 := by
    let : 𝒲.val.p.IsFibered := hPsetoid.isFiberedInGroupoids.isFibered
    refine ⟨F, hFAlg, ⟨fun U => classEquiv U.unop, ?_⟩⟩
    intro U V q α
    change classEquiv V.unop
      (𝒲.val.p.isoClassPresheaf.map q α) =
        F.map q (classEquiv U.unop α)
    simp [F]
  exact (isRepresentableByAlgebraicSpace_iff B S hS 𝒲).mpr
    ⟨hPsetoid, hClasses⟩

end AlgebraicGeometry

end
