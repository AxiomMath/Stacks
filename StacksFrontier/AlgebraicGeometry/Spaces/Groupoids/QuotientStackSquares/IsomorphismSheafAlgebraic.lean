module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSliceFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeStackSmall
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.IsomorphismSheaf
public import StacksFrontier.AlgebraicGeometry.Size.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringRestrictionCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.SmallSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.ArrowFiberAlgebraicity
public import StacksFrontier.CategoryTheory.Sites.Stack.TwoFibreProductMorPresheafMap

/-!
# The isomorphism sheaves of a quotient stack are algebraic spaces

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `B` over a
scheme `S` of a big fppf site, and let `x`, `y` be two objects of the quotient stack `[U/R]` over
a test object `T`. By Stacks 044V the sheaf `Isom(x, y)` is an algebraic space as soon as `x` and
`y` come from points of the object space; in general they only do so fppf-locally on `T`. Stacks
044W is the consequence: there is an fppf covering of `T` over each member of which the
restriction of `Isom(x, y)` is an algebraic space.

## Main results

* `AlgebraicGeometry.Stack.isomPresheaf_locallyAlgebraicSpace`: `Isom(x, y)` becomes an
  algebraic space after an fppf covering of the test object.
* `AlgebraicGeometry.Stack.isAlgebraicSpace_isomPresheaf`: `Isom(x, y)` is itself an algebraic
  space over the scheme the test object lies over.

## Implementation notes

Over a member `f : V ⟶ T` of the covering, `Isom(x, y)` is read as a sheaf on the big fppf site of
`V` rather than on the slice over `V`: the comparison functor is
`CategoryTheory.Over.iteratedSliceBackward`, and the restriction of a sheaf on the slice over `T`
along `f` is precomposition with `CategoryTheory.Over.map f`. The algebraic space produced is the
restriction, along the structure morphism of `V`, of the arrow-space fibre product
`AlgebraicGeometry.Stack.arrowFiber` of Stacks 044V.

The sheaf `Isom(x, y)` takes values one universe up, because the hom sets of a stackification are
not small, so algebraicity cannot be asserted of it on the nose. Its sections are small, and the
algebraic space is the pointwise `Shrink`; algebraicity is stated as a pointwise bijection with
it, natural in the test object.

## References

* [Stacks Project, Tag 02ZB](https://stacks.math.columbia.edu/tag/02ZB)
* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 044V](https://stacks.math.columbia.edu/tag/044V)
* [Stacks Project, Tag 044W](https://stacks.math.columbia.edu/tag/044W)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 04SK](https://stacks.math.columbia.edu/tag/04SK)
* [Stacks Project, Tag 04TB](https://stacks.math.columbia.edu/tag/04TB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

/- The fibre of a fibred category and its inclusion are not unfolded at `implicit` transparency,
so the composites below -- which mix arrows of a fibre with arrows of the ambient category -- are
not seen as associable there. Naming the two definitions lets the ordinary tactics see through
it. -/
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion

universe u u₁ u₂ v₁ v₂ v w z

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site exceeds the default limit
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_IsomorphismSheafAlgebraic
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S) :
    HasPullbacks ((BigFppfOver C S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_IsomorphismSheafAlgebraic
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    {X Y Z : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

private theorem isAlgebraicSpace_product
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    {F G : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace C S hS F)
    (hG : IsAlgebraicSpace C S hS G) :
    IsAlgebraicSpace C S hS (F ⨯ G) := by
  let D := BigFppfOver C S hS
  let T : D := Over.mk (𝟙 (C.obj hS))
  let hT : IsTerminal T := Over.mkIdTerminal
  let hYT := isAlgebraicSpace_yoneda C S hS T
  let hYTterm : IsTerminal (yoneda.obj T) := hT.isTerminalObj yoneda T
  let r : F ⟶ yoneda.obj T := hYTterm.from F
  let s : G ⟶ yoneda.obj T := hYTterm.from G
  have hp : IsAlgebraicSpace C S hS (pullback r s) :=
    isAlgebraicSpace_pullback C S hS r s hF hG hYT
  let e : F ⨯ G ≅ pullback r s := by
    let hP := isProductOfIsTerminalIsPullback r s (pullback.fst r s)
      (pullback.snd r s) hYTterm
      (pullbackIsPullback r s)
    exact (limit.isLimit (pair F G)).conePointUniqueUpToIso hP
  exact AlgebraicGeometry.Space.isAlgebraicSpace_of_iso C S hS e.symm hp

private theorem arrowFiber_isAlgebraicSpace
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    (x y : G.objects.obj.obj (Opposite.op T)) :
    IsAlgebraicSpace C S hS (arrowFiber G T x y) := by
  exact isAlgebraicSpace_pullback C S hS
    (prod.lift (yonedaEquiv.symm y) (yonedaEquiv.symm x))
    (prod.lift G.target.hom G.source.hom) (isAlgebraicSpace_yoneda C S hS T) G.arrows.property
    (isAlgebraicSpace_product C S hS G.objects.property G.objects.property)

/-- The chosen pullback of an isomorphism of a fibre is an isomorphism. -/
theorem isIso_pullbackFiberHom
    {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
    {p : 𝒳 ⥤ 𝒮} [p.IsPreFibered] {U : 𝒮} {x y : p.Fiber U}
    (e : x ≅ y) {V : 𝒮} (f : V ⟶ U) :
    IsIso (Functor.pullbackFiberHom e.hom f) := by
  refine ⟨Functor.pullbackFiberHom e.inv f, ?_, ?_⟩
  · rw [← Functor.pullbackFiberHom_comp, e.hom_inv_id, Functor.pullbackFiberHom_id]
  · rw [← Functor.pullbackFiberHom_comp, e.inv_hom_id, Functor.pullbackFiberHom_id]

/-- Isomorphisms `x ≅ x'` and `y ≅ y'` in the fibre of a fibred category over `U` induce an
isomorphism of isomorphism presheaves `Isom(x, y) ≅ Isom(x', y')`: a local isomorphism is
conjugated by the restrictions of the two given isomorphisms. -/
noncomputable def isomPresheafIsoOfIso
    {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
    (p : 𝒳 ⥤ 𝒮) [p.IsFibered] {U : 𝒮}
    {x x' y y' : p.Fiber U} (e : x ≅ x') (e' : y ≅ y') :
    p.isomPresheaf x y ≅ p.isomPresheaf x' y' := by
  let m := Functor.morPresheafFiberIso p e e'
  refine NatIso.ofComponents (fun W => Equiv.toIso {
    toFun := fun z => ⟨m.hom.app W z.1, ?_⟩
    invFun := fun z => ⟨m.inv.app W z.1, ?_⟩
    left_inv := ?_
    right_inv := ?_ }) ?_
  · change IsIso (m.hom.app W z.1)
    let : IsIso z.1 := by exact z.2
    let : IsIso (Functor.pullbackFiberHom e.inv W.unop.hom) :=
      isIso_pullbackFiberHom e.symm W.unop.hom
    let : IsIso (Functor.pullbackFiberHom e'.hom W.unop.hom) :=
      isIso_pullbackFiberHom e' W.unop.hom
    change IsIso (Functor.pullbackFiberHom e.inv W.unop.hom ≫ z.1 ≫
      Functor.pullbackFiberHom e'.hom W.unop.hom)
    infer_instance
  · change IsIso (m.inv.app W z.1)
    let : IsIso z.1 := by exact z.2
    let : IsIso (Functor.pullbackFiberHom e.hom W.unop.hom) :=
      isIso_pullbackFiberHom e W.unop.hom
    let : IsIso (Functor.pullbackFiberHom e'.inv W.unop.hom) :=
      isIso_pullbackFiberHom e'.symm W.unop.hom
    change IsIso (Functor.pullbackFiberHom e.hom W.unop.hom ≫ z.1 ≫
      Functor.pullbackFiberHom e'.inv W.unop.hom)
    infer_instance
  · intro z; apply Subtype.ext
    change m.inv.app W (m.hom.app W z.1) = z.1
    exact m.hom_inv_id_app_apply W z.1
  · intro z; apply Subtype.ext
    change m.hom.app W (m.inv.app W z.1) = z.1
    exact m.inv_hom_id_app_apply W z.1
  · intro W W' f
    ext z
    apply Subtype.ext
    exact m.hom.naturality_apply f z.1

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site exceeds the default limit
private theorem isAlgebraicSpace_iteratedSliceFiber
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (V : BigFppfOver C S hS)
    {P : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (q : P ⟶ yoneda.obj V) (hP : IsAlgebraicSpace C S hS P) :
    IsAlgebraicSpace C V.left.1 V.left.2
      ((Over.iteratedSliceBackward V).op ⋙ OverShriek.fiber (𝟙 _) q) := by
  let R := OverShriek.relocalizeRestrict V.hom
  let T : BigFppfOver C V.left.1 V.left.2 := Over.mk (𝟙 _)
  let F := (Over.iteratedSliceBackward V).op ⋙ OverShriek.fiber (𝟙 _) q
  let a : yoneda.obj T ⟶ R.obj (yoneda.obj V) := {
    app := fun W => ↾fun _ => Over.homMk W.unop.hom
    naturality := by
      intro W W' g
      ext z
      apply Over.OverMorphism.ext
      exact (Over.w g.unop).symm }
  let b : F ⟶ yoneda.obj T := {
    app := fun W => ↾fun _ => Over.homMk W.unop.hom
    naturality := by
      intro W W' g
      ext z
      apply Over.OverMorphism.ext
      exact (Over.w g.unop).symm }
  let i : F ⟶ R.obj P := {
    app := fun _ => ↾fun z => z.1
    naturality := by intros; rfl }
  have hi : b ≫ a = i ≫ R.map q := by
    ext W z
    exact z.2.symm
  have hp : IsPullback b i a (R.map q) := by
    apply IsPullback.of_isLimit (c := PullbackCone.mk b i hi)
    refine PullbackCone.IsLimit.mk hi (fun s => {
      app := fun W => ↾fun z => ⟨s.snd.app W z, ?_⟩
      naturality := ?_ }) ?_ ?_ ?_
    · exact (congrArg (fun k => k.app W z) s.condition).symm
    · intro W W' g
      ext z
      apply Subtype.ext
      exact s.snd.naturality_apply g z
    · intro s
      ext W z
      exact (Over.mkIdTerminal : IsTerminal T).hom_ext _ _
    · intro s
      rfl
    · intro s m hm₁ hm₂
      ext W z
      apply Subtype.ext
      exact congrArg (fun k => k.app W z) hm₂
  have hRP := isAlgebraicSpace_relocalizeRestrict C V.left.1 S V.left.2 hS
    V.hom P hP
  have hRV := isAlgebraicSpace_relocalizeRestrict C V.left.1 S V.left.2 hS
    V.hom (yoneda.obj V) (isAlgebraicSpace_yoneda C S hS V)
  have hT := isAlgebraicSpace_yoneda C V.left.1 V.left.2 T
  exact AlgebraicGeometry.Space.isAlgebraicSpace_of_iso C V.left.1 V.left.2
    (hp.isoPullback).symm
    (isAlgebraicSpace_pullback C V.left.1 V.left.2 a (R.map q) hT hRP hRV)

/-- The restriction along the iterated slice of the arrow fibre of two points of the object space
is an algebraic space. -/
private theorem isAlgebraicSpace_iteratedSlice_arrowFiberOver
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (V : BigFppfOver C S hS) (x y : G.objects.obj.obj (Opposite.op V)) :
    IsAlgebraicSpace C V.left.1 V.left.2
      ((Over.iteratedSliceBackward V).op ⋙ arrowFiberOver G V x y) :=
  isAlgebraicSpace_iteratedSliceFiber C S hS V _ (arrowFiber_isAlgebraicSpace C S hS G V x y)

/-- The comparison isomorphisms between iterated and composite chosen pullbacks are natural in
the slice. -/
theorem pullbackFiberCompIso_naturality
    {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
    {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {U V : 𝒮} (x : p.Fiber U) (f : V ⟶ U)
    {A A' : Over V} (g : A ⟶ A') :
    Functor.Fiber.fiberInclusion.map (Functor.pullbackFiberCompIso x f A.hom).hom ≫
        p.pullbackFiberMap x ((Over.map f).map g) =
      p.pullbackFiberMap (p.pullbackFiber x f) g ≫
        Functor.Fiber.fiberInclusion.map
          (Functor.pullbackFiberCompIso x f A'.hom).hom := by
  unfold Functor.Fiber at x
  have hleft : p.IsHomLift g.left
      (Functor.Fiber.fiberInclusion.map (Functor.pullbackFiberCompIso x f A.hom).hom ≫
        p.pullbackFiberMap x ((Over.map f).map g)) := by
    have hmap : p.IsHomLift g.left (p.pullbackFiberMap x ((Over.map f).map g)) := by
      rw [← Over.map_map_left (f := f) (g := g)]
      exact Functor.pullbackFiberMap_isHomLift p x ((Over.map f).map g)
    have hcomp : p.IsHomLift (𝟙 A.left)
        (Functor.Fiber.fiberInclusion.map (Functor.pullbackFiberCompIso x f A.hom).hom) :=
      (Functor.pullbackFiberCompIso x f A.hom).hom.2
    exact @IsHomLift.comp_lift_id_left' _ _ _ _ p _ _ _ A.left
      (Functor.Fiber.fiberInclusion.map (Functor.pullbackFiberCompIso x f A.hom).hom)
      hcomp _ _ g.left (p.pullbackFiberMap x ((Over.map f).map g)) hmap
  have hright : p.IsHomLift g.left
      (p.pullbackFiberMap (p.pullbackFiber x f) g ≫
        Functor.Fiber.fiberInclusion.map
          (Functor.pullbackFiberCompIso x f A'.hom).hom) := by
    have hcomp : p.IsHomLift (𝟙 A'.left)
        (Functor.Fiber.fiberInclusion.map (Functor.pullbackFiberCompIso x f A'.hom).hom) :=
      (Functor.pullbackFiberCompIso x f A'.hom).hom.2
    have hmap : p.IsHomLift g.left (p.pullbackFiberMap (p.pullbackFiber x f) g) :=
      Functor.pullbackFiberMap_isHomLift p (p.pullbackFiber x f) g
    exact @IsHomLift.comp_lift_id_right' _ _ _ _ p _ _ _ _ _ g.left
      (p.pullbackFiberMap (p.pullbackFiber x f) g) hmap A'.left
      (Functor.Fiber.fiberInclusion.map (Functor.pullbackFiberCompIso x f A'.hom).hom) hcomp
  refine @Functor.IsStronglyCartesian.ext _ _ _ _ p _ _ _ _ (A'.hom ≫ f)
    (Functor.IsPreFibered.pullbackMap x.property (A'.hom ≫ f))
    (by infer_instance) _ _ g.left _ _ hleft hright ?_
  rw [Category.assoc]
  change _ ≫ _ ≫ Functor.IsPreFibered.pullbackMap x.property
      (((Over.map f).obj A').hom) = _
  rw [Functor.pullbackFiberMap_fac]
  change Functor.Fiber.fiberInclusion.map (Functor.pullbackFiberCompIso x f A.hom).hom ≫
      Functor.IsPreFibered.pullbackMap x.property (A.hom ≫ f) = _
  rw [Functor.pullbackFiberCompIso_hom_fac, Category.assoc,
    Functor.pullbackFiberCompIso_hom_fac, ← Category.assoc,
    Functor.pullbackFiberMap_fac]

/-- The isomorphism presheaf of the chosen pullbacks of `x` and `y` along `f : V ⟶ U` is the
restriction along `f` of the isomorphism presheaf of `x` and `y`. -/
noncomputable def isomPresheafPullbackCompIso
    {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
    (p : 𝒳 ⥤ 𝒮) [p.IsFibered] {U V : 𝒮} (x y : p.Fiber U) (f : V ⟶ U) :
    p.isomPresheaf (p.pullbackFiber x f) (p.pullbackFiber y f) ≅
      (Over.map f).op ⋙ p.isomPresheaf x y := by
  classical
  let comparisonX (A : Over V) := Functor.pullbackFiberCompIso x f A.hom
  let comparisonY (A : Over V) := Functor.pullbackFiberCompIso y f A.hom
  refine NatIso.ofComponents (fun A => Equiv.toIso {
    toFun := fun z => ⟨(comparisonX A.unop).inv ≫ z.1 ≫ (comparisonY A.unop).hom, ?_⟩
    invFun := fun z => ⟨(comparisonX A.unop).hom ≫ z.1 ≫ (comparisonY A.unop).inv, ?_⟩
    left_inv := ?_
    right_inv := ?_ }) ?_
  · let : IsIso z.1 := z.2; change IsIso _; infer_instance
  · let : IsIso z.1 := z.2; change IsIso _; infer_instance
  · intro z; apply Subtype.ext; simp [Category.assoc]
  · intro z; apply Subtype.ext; simp [Category.assoc]
  · intro A A' g
    ext z
    apply Subtype.ext
    change (comparisonX A'.unop).inv ≫
        p.morRestrict (p.pullbackFiber x f) (p.pullbackFiber y f) g.unop z.1 ≫
        (comparisonY A'.unop).hom =
      p.morRestrict x y ((Over.map f).map g.unop)
        ((comparisonX A.unop).inv ≫ z.1 ≫ (comparisonY A.unop).hom)
    apply Functor.morRestrict_uniq p x y ((Over.map f).map g.unop)
    change Functor.Fiber.fiberInclusion.map
        ((comparisonX A'.unop).inv ≫
          p.morRestrict (p.pullbackFiber x f) (p.pullbackFiber y f) g.unop z.1 ≫
          (comparisonY A'.unop).hom) ≫
        Functor.IsPreFibered.pullbackMap y.property (A'.unop.hom ≫ f) =
      p.pullbackFiberMap x ((Over.map f).map g.unop) ≫
        Functor.Fiber.fiberInclusion.map
          ((comparisonX A.unop).inv ≫ z.1 ≫ (comparisonY A.unop).hom) ≫
        Functor.IsPreFibered.pullbackMap y.property (A.unop.hom ≫ f)
    dsimp only [comparisonX, comparisonY]
    simp only [Functor.map_comp]
    rw [Category.assoc, Category.assoc, Functor.pullbackFiberCompIso_hom_fac,
      Functor.morRestrict_fac_assoc]
    have hnX := pullbackFiberCompIso_naturality x f g.unop
    have hniX : Functor.Fiber.fiberInclusion.map
        (Functor.pullbackFiberCompIso x f A'.unop.hom).inv ≫
          p.pullbackFiberMap (p.pullbackFiber x f) g.unop =
      p.pullbackFiberMap x ((Over.map f).map g.unop) ≫
        Functor.Fiber.fiberInclusion.map
          (Functor.pullbackFiberCompIso x f A.unop.hom).inv := by
      apply (cancel_epi
        (Functor.Fiber.fiberInclusion.map
          (Functor.pullbackFiberCompIso x f A'.unop.hom).hom)).mp
      rw [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id]
      change (𝟙 _) ≫ p.pullbackFiberMap (p.pullbackFiber x f) g.unop = _
      rw [Category.id_comp, ← Category.assoc, hnX,
        Category.assoc, ← Functor.map_comp, Iso.hom_inv_id]
      change _ = p.pullbackFiberMap (p.pullbackFiber x f) g.unop ≫ 𝟙 _
      rw [Category.comp_id]
    rw [← Category.assoc, hniX, ← Functor.pullbackFiberCompIso_hom_fac]
    repeat' rw [Category.assoc]

private noncomputable def quotientPrestackFiberSection
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (V : BigFppfOver C S hS)
    (z : (quotientPrestack G).p.Fiber V) :
    G.objects.obj.obj (Opposite.op V) := by
  rcases z with ⟨z, hz⟩
  change z.base = V at hz
  subst V
  exact (quotientPrestackEquivalence G).inverse.obj z |>.fiber

private lemma quotientPrestackFiberSection_image
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (V : BigFppfOver C S hS)
    (z : (quotientPrestack G).p.Fiber V) :
    ((Functor.fiberFunctorOfCompEq
      (isFibredOneMorphism_toQuotientStack G).comp_eq V).obj z).1 =
      (pointwiseToQuotientStack G).obj
        ⟨V, quotientPrestackFiberSection G V z⟩ := by
  rcases z with ⟨z, hz⟩
  change z.base = V at hz
  subst V
  rfl

/-- After an fppf covering of the test object both quotient-stack objects come from points of the
object space, and the isomorphism sheaf becomes the slice arrow fibre of those two points. -/
private theorem exists_covering_arrowFiberOver_iso
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    (x y : (quotientStack G).p.Fiber T) :
    ∃ R ∈ BigFppfOver.topology C S hS T,
      ∀ ⦃V : BigFppfOver C S hS⦄ ⦃f : V ⟶ T⦄,
        R.arrows f →
          ∃ x' y' : G.objects.obj.obj (Opposite.op V), (x = y → x' = y') ∧
            Nonempty (((Over.iteratedSliceBackward V).op ⋙ arrowFiberOver G V x' y') ⋙
                uliftFunctor.{u + 1, u} ≅
              (Over.iteratedSliceBackward V).op ⋙ (Over.map f).op ⋙
                (quotientStack G).p.isomPresheaf x y) := by
  classical
  let J := BigFppfOver.topology C S hS
  obtain ⟨R₁, hR₁, h₁⟩ := essImage_toQuotientStack G T x
  obtain ⟨R₂, hR₂, h₂⟩ := essImage_toQuotientStack G T y
  refine ⟨R₁ ⊓ R₂, J.intersection_covering hR₁ hR₂, fun V f hf => ?_⟩
  let Φ := Functor.fiberFunctorOfCompEq
    (isFibredOneMorphism_toQuotientStack G).comp_eq V
  rcases h₁ hf.1 with ⟨z₁, ⟨e₁⟩⟩
  have h₂f : ∃ z₂, Nonempty (Φ.obj z₂ ≅ Functor.pullbackFiber (quotientStack G).p y f) ∧
      (x = y → z₂ = z₁) := by
    by_cases hxy : x = y
    · subst hxy
      exact ⟨z₁, ⟨e₁⟩, fun _ => rfl⟩
    · obtain ⟨z₂, he₂⟩ := h₂ hf.2
      exact ⟨z₂, he₂, fun h => absurd h hxy⟩
  rcases h₂f with ⟨z₂, ⟨e₂⟩, hz⟩
  let x' := quotientPrestackFiberSection G V z₁
  let y' := quotientPrestackFiberSection G V z₂
  let xV := Φ.obj z₁
  let yV := Φ.obj z₂
  have hxV := quotientPrestackFiberSection_image G V z₁
  have hyV := quotientPrestackFiberSection_image G V z₂
  obtain ⟨e₄₄, _⟩ := isomPresheaf_iso_pullback
    C S hS G V x' y' xV yV hxV hyV
  let eXY := isomPresheafIsoOfIso (quotientStack G).p e₁ e₂
  refine ⟨x', y', fun h => by
    change quotientPrestackFiberSection G V z₁ = quotientPrestackFiberSection G V z₂
    rw [hz h], ?_⟩
  let ecanon := Functor.isoWhiskerLeft (Over.iteratedSliceBackward V).op e₄₄
  let epullback := isomPresheafPullbackCompIso
    (quotientStack G).p x y f
  exact ⟨ecanon ≪≫
    Functor.isoWhiskerLeft (Over.iteratedSliceBackward V).op (eXY ≪≫ epullback)⟩

/-- The isomorphism sheaf of two quotient-stack objects is locally
representable by an algebraic space in the fppf topology. -/
@[stacks 044W]
theorem isomPresheaf_locallyAlgebraicSpace
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    (x y : (quotientStack G).p.Fiber T) :
    ∃ R ∈ BigFppfOver.topology C S hS T,
      ∀ ⦃V : BigFppfOver C S hS⦄ ⦃f : V ⟶ T⦄,
        R.arrows f →
          ∃ F : (BigFppfOver C V.left.1 V.left.2)ᵒᵖ ⥤ Type u,
            IsAlgebraicSpace C V.left.1 V.left.2 F ∧
              Nonempty (F ⋙ uliftFunctor.{u + 1, u} ≅
                (Over.iteratedSliceBackward V).op ⋙ (Over.map f).op ⋙
                  (quotientStack G).p.isomPresheaf x y) := by
  obtain ⟨R, hR, hlocal⟩ := exists_covering_arrowFiberOver_iso C S hS G T x y
  refine ⟨R, hR, fun V f hf => ?_⟩
  obtain ⟨x', y', -, e⟩ := hlocal hf
  exact ⟨(Over.iteratedSliceBackward V).op ⋙ arrowFiberOver G V x' y',
    isAlgebraicSpace_iteratedSlice_arrowFiberOver C S hS G V x' y', e⟩

/-- **The isomorphism sheaf of two objects of a quotient stack has, fppf-locally, every
étale-chart property its arrow fibres have.** Let `Q` be a property of morphisms of schemes such
that the presheaf of arrows from `x'` to `y'` has `Q` on every étale chart over `V` for all points
`x'`, `y'` of the object space over `V` which are equal whenever `x = y`. Then fppf-locally on the
test object, `Isom(x, y)` is an algebraic space whose structure morphism has `Q` on every étale
chart. -/
theorem isomPresheaf_locallyHoldsOnEveryEtaleChart
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B) (Q : MorphismProperty Scheme.{u})
    (T : BigFppfOver C S hS)
    (x y : (quotientStack G).p.Fiber T)
    (hQ : ∀ (V : BigFppfOver C S hS) (x' y' : G.objects.obj.obj (Opposite.op V)),
      (x = y → x' = y') →
        Space.HoldsOnEveryEtaleChart C S hS Q
          (pullback.fst (prod.lift (yonedaEquiv.symm y') (yonedaEquiv.symm x'))
            (prod.lift G.target.hom G.source.hom))) :
    ∃ R ∈ BigFppfOver.topology C S hS T,
      ∀ ⦃V : BigFppfOver C S hS⦄ ⦃f : V ⟶ T⦄,
        R.arrows f →
          ∃ F : (BigFppfOver C V.left.1 V.left.2)ᵒᵖ ⥤ Type u,
            IsAlgebraicSpace C V.left.1 V.left.2 F ∧
            Space.HoldsOnEveryEtaleChart C V.left.1 V.left.2 Q (terminal.from F) ∧
              Nonempty (F ⋙ uliftFunctor.{u + 1, u} ≅
                (Over.iteratedSliceBackward V).op ⋙ (Over.map f).op ⋙
                  (quotientStack G).p.isomPresheaf x y) := by
  obtain ⟨R, hR, hlocal⟩ := exists_covering_arrowFiberOver_iso C S hS G T x y
  refine ⟨R, hR, fun V f hf => ?_⟩
  obtain ⟨x', y', hxy, e⟩ := hlocal hf
  refine ⟨(Over.iteratedSliceBackward V).op ⋙ arrowFiberOver G V x' y',
    isAlgebraicSpace_iteratedSlice_arrowFiberOver C S hS G V x' y', ?_, e⟩
  have hfibre := Space.holdsOnEveryEtaleChart_toYonedaId_iteratedSliceFiber C S hS Q V _
    (hQ V x' y' hxy)
  exact Space.holdsOnEveryEtaleChart_of_isTerminal C V.left.1 V.left.2
    (Over.mkIdTerminal.isTerminalObj yoneda _) terminalIsTerminal _ _ hfibre

/-- The isomorphism sheaf of two objects of the quotient stack of a groupoid whose source map is
locally of finite type is, fppf-locally on the test object, an algebraic space which is locally of
finite type over that object. -/
theorem isomPresheaf_locallyIsLocallyOfFiniteType
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (hs : Space.IsLocallyOfFiniteType C S hS G.source.hom)
    (T : BigFppfOver C S hS)
    (x y : (quotientStack G).p.Fiber T) :
    ∃ R ∈ BigFppfOver.topology C S hS T,
      ∀ ⦃V : BigFppfOver C S hS⦄ ⦃f : V ⟶ T⦄,
        R.arrows f →
          ∃ F : (BigFppfOver C V.left.1 V.left.2)ᵒᵖ ⥤ Type u,
            IsAlgebraicSpace C V.left.1 V.left.2 F ∧
            Space.IsLocallyOfFiniteType C V.left.1 V.left.2 (terminal.from F) ∧
              Nonempty (F ⋙ uliftFunctor.{u + 1, u} ≅
                (Over.iteratedSliceBackward V).op ⋙ (Over.map f).op ⋙
                  (quotientStack G).p.isomPresheaf x y) :=
  isomPresheaf_locallyHoldsOnEveryEtaleChart C S hS G _ T x y
    (fun V x' y' _ => Space.isLocallyOfFiniteType_arrowFiber_fst C S hS G hs V x' y')

/-! ### Globalizing: the isomorphism sheaf itself is an algebraic space (Stacks 04TB) -/

section Global

open Opposite

/-- A family in the big fppf site over `S` whose coproduct of underlying schemes is again of the
site's size is realized by an object of the site, together with the comparison isomorphism. -/
lemma exists_coproduct_of_contains
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    {I : Type u} (U : I → BigFppfOver C S hS)
    (hU : C.Contains (∐ (fun i => (BigFppfOver.toScheme C S hS).obj (U i)))) :
    ∃ (V : BigFppfOver C S hS) (j : ∀ i, U i ⟶ V),
      Nonempty (IsColimit (Cofan.mk V j)) ∧
      ∃ e : (∐ (fun i => (BigFppfOver.toScheme C S hS).obj (U i))) ≅
          (BigFppfOver.toScheme C S hS).obj V,
        ∀ i, Sigma.ι _ i ≫ e.hom = (BigFppfOver.toScheme C S hS).map (j i) := by
  let X := fun i => (BigFppfOver.toScheme C S hS).obj (U i)
  let Vobj := C.obj hU
  let vmap : Vobj ⟶ C.obj hS := C.inclusion.preimage
    (show C.inclusion.obj Vobj ⟶ C.inclusion.obj (C.obj hS) from
      Sigma.desc (fun i => C.inclusion.map (U i).hom))
  let V : BigFppfOver C S hS := Over.mk vmap
  have hw (i : I) :
      C.inclusion.preimage (show C.inclusion.obj (U i).left ⟶
        C.inclusion.obj Vobj from Sigma.ι X i) ≫ vmap = (U i).hom := by
    apply C.inclusion.map_injective
    simp only [Functor.map_comp, vmap, Functor.map_preimage, Sigma.ι_comp_desc]
  let j : ∀ i, U i ⟶ V := fun i => Over.homMk
    (C.inclusion.preimage (show C.inclusion.obj (U i).left ⟶
      C.inclusion.obj Vobj from Sigma.ι X i)) (hw i)
  refine ⟨V, j, ⟨Cofan.IsColimit.mk _ (fun c => ?_) ?_ ?_⟩, Iso.refl _, ?_⟩
  · let m₀ : C.inclusion.obj Vobj ⟶ C.inclusion.obj c.pt.left :=
      Sigma.desc (fun i => C.inclusion.map (c.inj i).left)
    let m : Vobj ⟶ c.pt.left := C.inclusion.preimage m₀
    have hm : m ≫ c.pt.hom = vmap := by
      apply C.inclusion.map_injective
      simp only [Functor.map_comp, m, Functor.map_preimage, vmap]
      apply Sigma.hom_ext
      intro i
      simp only [m₀, Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
      rw [← Functor.map_comp, Over.w]
    exact Over.homMk m hm
  · intro c i
    apply Over.OverMorphism.ext
    apply C.inclusion.map_injective
    change C.inclusion.map (C.inclusion.preimage (X := (U i).left) (Y := Vobj) (Sigma.ι X i) ≫
      C.inclusion.preimage (X := Vobj) (Y := c.pt.left)
        (Sigma.desc (fun i => C.inclusion.map (c.inj i).left))) = _
    rw [Functor.map_comp, Functor.map_preimage, Functor.map_preimage, Sigma.ι_comp_desc]
  · intro c m hm
    apply Over.OverMorphism.ext
    apply C.inclusion.map_injective
    apply Sigma.hom_ext
    intro i
    have hi := congrArg (fun f : U i ⟶ c.pt => C.inclusion.map f.left) (hm i)
    change Sigma.ι X i ≫ C.inclusion.map m.left = Sigma.ι X i ≫
      C.inclusion.map (C.inclusion.preimage (X := Vobj) (Y := c.pt.left)
        (Sigma.desc (fun i => C.inclusion.map (c.inj i).left)))
    rw [Functor.map_preimage, Sigma.ι_comp_desc]
    change C.inclusion.map (C.inclusion.preimage (X := (U i).left) (Y := Vobj)
      (Sigma.ι X i) ≫ m.left) = _ at hi
    simpa only [Functor.map_comp, Functor.map_preimage] using hi
  · intro i
    change Sigma.ι X i ≫ 𝟙 _ = C.inclusion.map
      (C.inclusion.preimage (X := (U i).left) (Y := Vobj) (Sigma.ι X i))
    rw [Category.comp_id, Functor.map_preimage]

/-- A family of the big fppf site over `S` whose image in schemes is an fppf covering is an
fppf covering family of the underlying category. -/
private lemma isFppfCovering_of_presieve₀_mem
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    {V : BigFppfOver C S hS} (E : PreZeroHypercover.{u + 1} V)
    (hE : (E.map (BigFppfOver.toScheme C S hS)).presieve₀ ∈
      Scheme.fppfPrecoverage ((BigFppfOver.toScheme C S hS).obj V)) :
    IsFppfCovering (κ := C.cutoff) ⟨V.left, E.map (Over.forget (C.obj hS))⟩ := by
  change (E.map (Over.forget (C.obj hS))).presieve₀ ∈
    Scheme.fppfPrecoverage.comap C.inclusion V.left
  rw [Precoverage.mem_comap_iff, ← PreZeroHypercover.presieve₀_map]
  exact hE

/-- A family of the big fppf site over `S` whose image in schemes is an fppf covering generates a
covering sieve. -/
lemma sieve_mem_of_fppf
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    {V : BigFppfOver C S hS} (E : PreZeroHypercover.{u + 1} V)
    (hE : (E.map (BigFppfOver.toScheme C S hS)).presieve₀ ∈
      Scheme.fppfPrecoverage ((BigFppfOver.toScheme C S hS).obj V)) :
    E.sieve₀ ∈ BigFppfOver.topology C S hS V := by
  let D := E.map (Over.forget (C.obj hS))
  have hD : IsFppfCovering ⟨V.left, D⟩ := isFppfCovering_of_presieve₀_mem C S hS E hE
  obtain ⟨⟨T', D'⟩, hD', ht, heq⟩ := C.fppf_has_representative ⟨V.left, D⟩ hD
  cases ht
  obtain ⟨_, ⟨β, hX, hf⟩⟩ := heq
  have hle : D'.sieve₀ ≤ D.sieve₀ := by
    rw [Sieve.generate_le_iff]
    rintro Z f ⟨i⟩
    rw [hf i]
    exact D.sieve₀.downward_closed (D.sieve₀_f (β i)) (eqToHom (hX i))
  apply (C.topology.mem_over_iff E.sieve₀).mpr
  change Sieve.overEquiv V (Sieve.ofArrows E.X E.f) ∈ _
  rw [Sieve.overEquiv_ofArrows]
  exact C.topology.superset_covering hle
    (Precoverage.generate_mem_toGrothendieck ⟨D', rfl, hD'⟩)

/-- The summands of a coproduct inside the big fppf site over `S` form a covering by
monomorphisms with empty pairwise intersections. -/
lemma coproduct_cover
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    {I : Type u} (X : I → BigFppfOver C S hS)
    (V : BigFppfOver C S hS) (j : ∀ i, X i ⟶ V)
    (e : (∐ (fun i => (BigFppfOver.toScheme C S hS).obj (X i))) ≅
      (BigFppfOver.toScheme C S hS).obj V)
    (he : ∀ i, Sigma.ι _ i ≫ e.hom = (BigFppfOver.toScheme C S hS).map (j i)) :
    (∀ i, Mono (j i)) ∧
    Sieve.ofArrows X j ∈ BigFppfOver.topology C S hS V ∧
    (∀ {i k}, i ≠ k → ∀ {Y : BigFppfOver C S hS}
      (a : Y ⟶ X i) (b : Y ⟶ X k), a ≫ j i = b ≫ j k →
        ⊥ ∈ BigFppfOver.topology C S hS Y) := by
  let T := BigFppfOver.toScheme C S hS
  let A := fun i => T.obj (X i)
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have : Mono (T.map (j i)) := by rw [← he i]; infer_instance
    exact T.mono_of_mono_map inferInstance
  · let E : PreZeroHypercover.{u + 1} V :=
      { I₀ := ULift.{u + 1} I, X := fun i => X i.down, f := fun i => j i.down }
    have hE : (E.map T).presieve₀ ∈ Scheme.fppfPrecoverage (T.obj V) := by
      rw [PreZeroHypercover.presieve₀, Scheme.fppfPrecoverage,
        Scheme.ofArrows_mem_precoverage_iff]
      constructor
      · intro t
        obtain ⟨t, rfl⟩ := e.hom.homeomorph.surjective t
        obtain ⟨⟨i, x⟩, rfl⟩ := (sigmaMk A).surjective t
        refine ⟨ULift.up i, x, ?_⟩
        change T.map (j i) x = _
        rw [← he i, Scheme.Hom.comp_apply, sigmaMk_mk]
        rfl
      · intro i
        change Flat (T.map (j i.down)) ∧ LocallyOfFinitePresentation (T.map (j i.down))
        rw [← he i.down]
        constructor <;> infer_instance
    have hh := sieve_mem_of_fppf C S hS E hE
    have hEq : E.sieve₀ = Sieve.ofArrows X j := by
      apply le_antisymm <;> rw [Sieve.generate_le_iff]
      · rintro Z f ⟨i⟩
        exact Sieve.ofArrows_mk X j i.down
      · rintro Z f ⟨i⟩
        exact E.sieve₀_f (ULift.up i)
    rwa [hEq] at hh
  · intro i k hik Y a b hab
    have hh : T.map a ≫ Sigma.ι A i = T.map b ≫ Sigma.ι A k := by
      apply (cancel_mono e.hom).mp
      rw [Category.assoc, he i, Category.assoc, he k, ← T.map_comp, ← T.map_comp, hab]
    have : IsEmpty (T.obj Y) := isEmpty_of_commSq_sigmaι_of_ne ⟨hh⟩ hik
    exact BigFppfOver.bot_mem_topology Y this

/-- Smallness of the sections of a sheaf is local on a covering sieve, over a small site. -/
private theorem small_of_locally_small_on_sieve
    {D : Type v} [Category.{w} D] [LocallySmall.{u} D] [Small.{u} D]
    {J : GrothendieckTopology D}
    {P : Dᵒᵖ ⥤ Type z} (hP : Presheaf.IsSheaf J P)
    {X : D} (R : Sieve X) (hR : R ∈ J X)
    (hlocal : ∀ ⦃Y⦄ (f : Y ⟶ X), R f → Small.{u} (P.obj (op Y)))
    {Y : D} (g : Y ⟶ X) : Small.{u} (P.obj (op Y)) := by
  classical
  let Q := R.pullback g
  have hQ : Q ∈ J Y := J.pullback_stable g hR
  let : LocallySmall.{u} (Over Y) := inferInstance
  let : ∀ Z : D, Small.{u} (Z ⟶ Y) := fun Z => LocallySmall.hom_small Z Y
  let : Small.{u} (Σ Z : D, Z ⟶ Y) := inferInstance
  let : Small.{u} (Over Y) :=
    small_of_surjective
      (f := fun (f : Σ Z : D, Z ⟶ Y) => CostructuredArrow.mk f.2)
      (fun A => ⟨⟨A.left, A.hom⟩, by cases A; rfl⟩)
  let : Small.{u} Q.arrows.category := inferInstance
  have hsmall (i : Q.arrows.category) : Small.{u} (P.obj (op i.obj.left)) := by
    apply hlocal (i.obj.hom ≫ g)
    simpa [Q, Sieve.pullback_apply] using i.property
  let : ∀ i : Q.arrows.category, Small.{u} (P.obj (op i.obj.left)) := hsmall
  apply small_of_injective (f := fun s : P.obj (op Y) =>
    fun i : Q.arrows.category ↦ P.map i.obj.hom.op s)
  intro s t hst
  exact (hP.isSeparated Y Q hQ) s t (fun Z f hf =>
    congrFun hst (Q.arrows.categoryMk f hf))

/-- Every covering sieve of the big fppf site over `S` contains a size-bounded fppf covering
family of the underlying scheme. -/
theorem exists_small_fppf_refinement_in_sieve
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    {T : BigFppfOver C S hS} {R : Sieve T}
    (hR : R ∈ BigFppfOver.topology C S hS T) :
    ∃ W : FppfCovering.{u} (C.inclusion.obj T.left),
      Cardinal.mk W.ι ≤ (C.inclusion.obj T.left).size ∧
      (∀ j, Scheme.size (W.X j) ≤ (C.inclusion.obj T.left).size) ∧
      ∀ j (hWsite : C.Contains (W.X j)), (Sieve.overEquiv T R)
        (C.inclusion.preimage (X := C.obj hWsite) (W.f j)) := by
  let Rbase : Sieve T.left := Sieve.overEquiv T R
  have hRbase : Rbase ∈ C.topology T.left := by
    change R ∈ (C.topology.over (C.obj hS)) T at hR
    exact (C.topology.mem_over_iff R).mp hR
  obtain ⟨E₀, hE₀, hle⟩ := Space.exists_covering_refining_sieve C hRbase
  have hE₀_ambient : (E₀.map C.inclusion).presieve₀ ∈
      Scheme.fppfPrecoverage (C.inclusion.obj T.left) := by
    rw [PreZeroHypercover.presieve₀_map]
    exact (Precoverage.mem_comap_iff).mp (C.isFppfCovering_of_isCovering hE₀)
  have hE₀_fields := by
    simpa only [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff] using
      hE₀_ambient
  let 𝒞 : FppfCovering (C.inclusion.obj T.left) := {
    ι := (E₀.map C.inclusion).I₀
    X i := (E₀.map C.inclusion).X i
    f i := (E₀.map C.inclusion).f i
    flat i := (hE₀_fields.2 i).1
    lfp i := (hE₀_fields.2 i).2
    jointly_surjective := hE₀_fields.1 }
  obtain ⟨W, hWref, hWcard, hWsize⟩ := exists_small_refinement
    (C.inclusion.obj T.left) 𝒞
  refine ⟨W, hWcard, hWsize, ?_⟩
  intro j hWsite
  obtain ⟨i, g, hg⟩ := hWref j
  have hgi : g ≫ C.inclusion.map (E₀.f i) = W.f j := hg
  have hg' : (C.inclusion.preimage (X := C.obj hWsite) (Y := E₀.X i) g) ≫ E₀.f i =
      C.inclusion.preimage (X := C.obj hWsite) (W.f j) := by
    apply C.inclusion.map_injective
    change C.inclusion.map (C.inclusion.preimage (X := C.obj hWsite) (Y := E₀.X i) g) ≫
      C.inclusion.map (E₀.f i) = C.inclusion.map
        (C.inclusion.preimage (X := C.obj hWsite) (Y := T.left) (W.f j))
    rw [Functor.map_preimage,
      show C.inclusion.map (C.inclusion.preimage (X := C.obj hWsite) (Y := E₀.X i) g) = g from
        Functor.map_preimage _ _]
    exact hgi
  have hi : Rbase (E₀.f i) := hle _ _ (E₀.presieve₀_f i)
  rw [← hg']
  exact Rbase.downward_closed hi
    (C.inclusion.preimage (X := C.obj hWsite) (Y := E₀.X i) g)

/-- Smallness of the sections of a sheaf over the covered object is local on a covering sieve,
over an essentially small site. -/
private theorem small_of_locally_small_on_sieve_essentiallySmall_atTarget
    {D : Type v} [Category.{w} D] [LocallySmall.{u} D] [EssentiallySmall.{u} D]
    {J : GrothendieckTopology D}
    {P : Dᵒᵖ ⥤ Type z} (hP : Presheaf.IsSheaf J P)
    {X : D} (R : Sieve X) (hR : R ∈ J X)
    (hlocal : ∀ ⦃Y⦄ (f : Y ⟶ X), R f → Small.{u} (P.obj (op Y))) :
    Small.{u} (P.obj (op X)) := by
  classical
  let e := equivSmallModel.{u} D
  let K := e.inverse.inducedTopology J
  let X' := e.functor.obj X
  let R' := (R.pullback (e.unitIso.inv.app X)).functorPullback e.inverse
  let P' := e.inverse.op ⋙ P
  let : e.inverse.IsCoverDense J := by
    constructor
    intro Z
    apply J.superset_covering (fun Y f hf => ?_) (J.top_mem Z)
    exact ⟨⟨e.functor.obj Z, f ≫ e.unitIso.hom.app Z, e.unitIso.inv.app Z, by simp⟩⟩
  have hP' : Presheaf.IsSheaf K P' := by
    let : e.inverse.IsDenseSubsite K J := inferInstance
    exact ((e.sheafCongr J K (Type z)).functor.obj ⟨P, hP⟩).property
  have hR' : R' ∈ K X' := by
    have hDense : e.inverse.IsDenseSubsite K J := inferInstance
    apply hDense.functorPushforward_mem_iff.mp
    apply J.superset_covering ?_ (J.pullback_stable (e.unitIso.inv.app X) hR)
    intro Y f hf
    let a : Y ⟶ X := f ≫ e.unitIso.inv.app X
    let g : e.functor.obj Y ⟶ X' := e.functor.map a
    have hn' : a ≫ e.unitIso.hom.app X = e.unitIso.hom.app Y ≫ e.inverse.map g := by
      simp [g, a]
    have hg : R' g := by
      change R (e.inverse.map g ≫ e.unitIso.inv.app X)
      have hfactor : e.unitIso.hom.app Y ≫ e.inverse.map g ≫ e.unitIso.inv.app X = a := by
        calc
          e.unitIso.hom.app Y ≫ e.inverse.map g ≫ e.unitIso.inv.app X =
              (a ≫ e.unitIso.hom.app X) ≫ e.unitIso.inv.app X := by
                rw [← Category.assoc, ← hn']
          _ = a := by simp
      have hmem : R (e.unitIso.hom.app Y ≫ (e.inverse.map g ≫ e.unitIso.inv.app X)) := by
        rw [hfactor]
        exact hf
      simpa using R.downward_closed hmem (e.unitIso.inv.app Y)
    refine ⟨e.functor.obj Y, g, e.unitIso.hom.app Y, hg, ?_⟩
    calc
      f = a ≫ e.unitIso.hom.app X := by simp [a]
      _ = e.unitIso.hom.app Y ≫ e.inverse.map g := hn'
  have hlocal' : ∀ ⦃Y'⦄ (f : Y' ⟶ X'), R' f → Small.{u} (P'.obj (op Y')) :=
    fun _ f hf => hlocal (e.inverse.map f ≫ e.unitIso.inv.app X) hf
  let : Small.{u} (SmallModel D) := inferInstance
  let : LocallySmall.{u} (SmallModel D) := inferInstance
  have hsmall' := small_of_locally_small_on_sieve hP' R' hR' hlocal' (𝟙 X')
  let eP : P.obj (op ((e.functor ⋙ e.inverse).obj X)) ≃ P.obj (op X) :=
    (P.mapIso (e.unitIso.app X).op).toEquiv
  exact (small_congr.{u} eP).1 hsmall'

/-- Smallness of the sections of a sheaf is local on a covering sieve, over an essentially small
site. -/
private theorem small_of_locally_small_on_sieve_essentiallySmall
    {D : Type v} [Category.{w} D] [LocallySmall.{u} D] [EssentiallySmall.{u} D]
    {J : GrothendieckTopology D} {P : Dᵒᵖ ⥤ Type z}
    (hP : Presheaf.IsSheaf J P) {X : D} (R : Sieve X) (hR : R ∈ J X)
    (hlocal : ∀ ⦃Z⦄ (f : Z ⟶ X), R f → Small.{u} (P.obj (op Z)))
    {Y : D} (g : Y ⟶ X) : Small.{u} (P.obj (op Y)) :=
  small_of_locally_small_on_sieve_essentiallySmall_atTarget hP
    (R.pullback g) (J.pullback_stable g hR) fun _ f hf => hlocal (f ≫ g) hf

private theorem essentiallySmall_sliceOver {D : Type*} [Category.{u} D]
    [EssentiallySmall.{u} D] (X : D) : EssentiallySmall.{u} (Over X) :=
  essentiallySmall_of_fully_faithful (Over.post (equivSmallModel.{u} D).functor)

/-- Restricting the iterated slice along a morphism of the slice agrees with restricting along
its underlying morphism, naturally. -/
private def iteratedSliceBackwardMapNatIso
    {D : Type v} [Category.{w} D] {S : D} {V T : Over S} (f : V ⟶ T) :
    Over.iteratedSliceBackward V ⋙ Over.map f ≅
      Over.map f.left ⋙ Over.iteratedSliceBackward T :=
  NatIso.ofComponents (fun W =>
    Over.isoMk (Over.isoMk (Iso.refl W.left) (by
      change 𝟙 W.left ≫ ((W.hom ≫ f.left) ≫ T.hom) = W.hom ≫ V.hom
      simp)) (by
      apply Over.OverMorphism.ext
      change 𝟙 W.left ≫ (W.hom ≫ f.left) = W.hom ≫ f.left
      simp)) (by
      intro W W' g
      apply Over.OverMorphism.ext
      apply Over.OverMorphism.ext
      change g.left ≫ 𝟙 W'.left = 𝟙 W.left ≫ g.left
      simp)

/-- Sections of a sheaf over the members of a covering by monomorphisms with empty pairwise
intersections glue, with no compatibility condition. -/
theorem exists_section_of_disjoint_cover
    {D : Type v} [Category.{w} D] (J : GrothendieckTopology D)
    {K : Type*} (X : K → D) (V : D) (j : ∀ i, X i ⟶ V)
    (hm : ∀ i, Mono (j i)) (hj : Sieve.ofArrows X j ∈ J V)
    (hd : ∀ {i k}, i ≠ k → ∀ {Y : D} (a : Y ⟶ X i) (b : Y ⟶ X k),
      a ≫ j i = b ≫ j k → ⊥ ∈ J Y)
    (P : Dᵒᵖ ⥤ Type z) (hP : Presheaf.IsSheaf J P)
    (s : ∀ i, P.obj (op (X i))) :
    ∃ t : P.obj (op V), ∀ i, P.map (j i).op t = s i := by
  classical
  let x (i : K) : PUnit ⟶ P.obj (op (X i)) := ↾fun _ => s i
  have hx : ∀ ⦃Y : D⦄ ⦃i k : K⦄ (a : Y ⟶ X i) (b : Y ⟶ X k),
      a ≫ j i = b ≫ j k → x i ≫ P.map a.op = x k ≫ P.map b.op := by
    intro Y i k a b hab
    by_cases hik : i = k
    · subst k
      have : a = b := (cancel_mono (j i)).mp hab
      subst b
      rfl
    · apply hP.hom_ext_ofArrows (X := fun e : PEmpty.{1} => e.elim) (fun e => e.elim)
        (by simpa [Sieve.ofArrows, Presieve.ofArrows_of_isEmpty] using hd hik a b hab)
      intro e
      exact e.elim
  obtain ⟨g, hg, -⟩ := hP.existsUnique_amalgamation_ofArrows j hj x hx
  exact ⟨g PUnit.unit, fun i => ConcreteCategory.congr_hom (hg i) PUnit.unit⟩

/-- Two objects of a stack in groupoids which become isomorphic over every member of a covering
by monomorphisms with empty pairwise intersections are isomorphic. -/
theorem exists_iso_of_disjoint_cover
    {D : Type v} [Category.{w} D] {E : Type*} [Category E]
    (J : GrothendieckTopology D) (p : E ⥤ D) [p.IsFibered]
    (hp : ∀ U x y, p.IsMorSheaf J U x y) (hpg : p.IsFiberedInGroupoids)
    {K : Type*} (X : K → D) (V : D) (j : ∀ i, X i ⟶ V)
    (hm : ∀ i, Mono (j i)) (hj : Sieve.ofArrows X j ∈ J V)
    (hd : ∀ {i k}, i ≠ k → ∀ {Y : D} (a : Y ⟶ X i) (b : Y ⟶ X k),
      a ≫ j i = b ≫ j k → ⊥ ∈ J Y)
    (x y : p.Fiber V)
    (hxy : ∀ i, Nonempty (Functor.pullbackFiber p x (j i) ≅
      Functor.pullbackFiber p y (j i))) : Nonempty (x ≅ y) := by
  classical
  let Z : K → Over V := fun i => Over.mk (j i)
  let W : Over V := Over.mk (𝟙 V)
  let k (i : K) : Z i ⟶ W := Over.homMk (j i)
  have hm' (i : K) : Mono (k i) := by
    have : Mono (j i) := hm i
    exact (Over.forget V).mono_of_mono_map inferInstance
  have hj' : Sieve.ofArrows Z k ∈ (J.over V) W := by
    apply (J.mem_over_iff _).mpr
    rw [Sieve.overEquiv_ofArrows]
    change Sieve.ofArrows X j ∈ J V
    exact hj
  have hd' : ∀ {i l}, i ≠ l → ∀ {Y : Over V} (a : Y ⟶ Z i) (b : Y ⟶ Z l),
      a ≫ k i = b ≫ k l → ⊥ ∈ (J.over V) Y := by
    intro i l hil Y a b hab
    apply (J.mem_over_iff _).mpr
    simpa using hd hil a.left b.left (congrArg (fun q => q.left) hab)
  obtain ⟨m, -⟩ := exists_section_of_disjoint_cover (J.over V) Z W k hm' hj' hd'
    (p.morPresheaf x y) (hp V x y) (fun i => (hxy i).some.hom)
  have : IsGroupoid (p.Fiber V) := hpg.fiber_isGroupoid V
  exact ⟨(Functor.pullbackFiberIdIso x).symm ≪≫ asIso m ≪≫ Functor.pullbackFiberIdIso y⟩

/-- An object of a fibre of the quotient stack in the essential image of the stackification map
is presented by a point of the object space. -/
theorem presented_of_essImage_toQuotientStack
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {T V : BigFppfOver C S hS} {f : V ⟶ T} {x : (quotientStack G).p.Fiber T}
    (h : (Functor.fiberFunctorOfCompEq
      (isFibredOneMorphism_toQuotientStack G).comp_eq V).essImage
      (Functor.pullbackFiber (quotientStack G).p x f)) :
    ∃ a : G.objects.obj.obj (op V), Nonempty
      ((pointwiseToQuotientStackFiber G V).obj a ≅
        Functor.pullbackFiber (quotientStack G).p x f) := by
  obtain ⟨a, ⟨e⟩⟩ := h
  rcases a with ⟨⟨V', a⟩, ha⟩
  change V' = V at ha
  subst V'
  exact ⟨a, ⟨e⟩⟩

/-- An object of a quotient stack comes from a point of the object space over every member of
some covering of the test object. -/
theorem exists_presented_pullback
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    (x : (quotientStack G).p.Fiber T) :
    ∃ R ∈ BigFppfOver.topology C S hS T,
      ∀ ⦃V⦄ (f : V ⟶ T), R f →
        ∃ a : G.objects.obj.obj (op V), Nonempty
          ((pointwiseToQuotientStackFiber G V).obj a ≅
            Functor.pullbackFiber (quotientStack G).p x f) := by
  obtain ⟨R, hR, hl⟩ := essImage_toQuotientStack G T x
  exact ⟨R, hR, fun V f hf => presented_of_essImage_toQuotientStack C S hS G (hl hf)⟩

/-- Points of the object space presenting an object of a quotient stack over the members of a
covering by monomorphisms with empty pairwise intersections glue to one over the total object. -/
theorem presented_pullback_of_disjoint_cover
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {K : Type*} (X : K → BigFppfOver C S hS)
    (V T : BigFppfOver C S hS) (j : ∀ i, X i ⟶ V)
    (hm : ∀ i, Mono (j i))
    (hj : Sieve.ofArrows X j ∈ BigFppfOver.topology C S hS V)
    (hd : ∀ {i k}, i ≠ k → ∀ {Y : BigFppfOver C S hS}
      (a : Y ⟶ X i) (b : Y ⟶ X k), a ≫ j i = b ≫ j k →
        ⊥ ∈ BigFppfOver.topology C S hS Y)
    (f : V ⟶ T) (fi : ∀ i, X i ⟶ T) (hfi : ∀ i, j i ≫ f = fi i)
    (x : (quotientStack G).p.Fiber T)
    (hl : ∀ i, ∃ a : G.objects.obj.obj (op (X i)), Nonempty
      ((pointwiseToQuotientStackFiber G (X i)).obj a ≅
        Functor.pullbackFiber (quotientStack G).p x (fi i))) :
    ∃ a : G.objects.obj.obj (op V), Nonempty
      ((pointwiseToQuotientStackFiber G V).obj a ≅
        Functor.pullbackFiber (quotientStack G).p x f) := by
  classical
  choose ai ei using hl
  obtain ⟨a, ha⟩ := exists_section_of_disjoint_cover
    (BigFppfOver.topology C S hS) X V j hm hj hd G.objects.obj
    G.objects.property.isSheaf ai
  refine ⟨a, exists_iso_of_disjoint_cover _ _ (isStack_quotientStack G).isMorSheaf
    (isFiberedInGroupoids_quotientStack G) X V j hm hj hd _ _ ?_⟩
  intro i
  refine ⟨presentedPullbackIso G V a ((pointwiseToQuotientStackFiber G V).obj a) rfl
    (Over.mk (j i)) ≪≫
    eqToIso (congrArg (pointwiseToQuotientStackFiber G (X i)).obj (ha i)) ≪≫
    (ei i).some ≪≫ ?_⟩
  exact (Functor.pullbackFiberCompIso' x f (j i) (fi i) (hfi i)).symm

/-- Two objects of a quotient stack both come from points of the object space over a single
surjective, flat, locally finitely presented member of a covering of the test object. -/
theorem exists_single_cover_presented_pair
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    (x y : (quotientStack G).p.Fiber T) :
    ∃ (V : BigFppfOver C S hS) (f : V ⟶ T),
      Flat (C.inclusion.map f.left) ∧
      LocallyOfFinitePresentation (C.inclusion.map f.left) ∧
      Surjective (C.inclusion.map f.left) ∧
      ∃ a b : G.objects.obj.obj (op V),
        Nonempty ((pointwiseToQuotientStackFiber G V).obj a ≅
          Functor.pullbackFiber (quotientStack G).p x f) ∧
        Nonempty ((pointwiseToQuotientStackFiber G V).obj b ≅
          Functor.pullbackFiber (quotientStack G).p y f) := by
  classical
  obtain ⟨Rx, hRx, hx⟩ := exists_presented_pullback C S hS G T x
  obtain ⟨Ry, hRy, hy⟩ := exists_presented_pullback C S hS G T y
  obtain ⟨W, hcard, hsize, hmem⟩ := exists_small_fppf_refinement_in_sieve C S hS
    ((BigFppfOver.topology C S hS).intersection_covering hRx hRy)
  have hW i : C.Contains (W.X i) := (hsize i).trans_lt T.left.property
  let wi i : C.obj (hW i) ⟶ T.left := C.inclusion.preimage (W.f i)
  let Wi i : BigFppfOver C S hS := Over.mk (wi i ≫ T.hom)
  let fi i : Wi i ⟶ T := Over.homMk (wi i)
  have hfi i : (Rx ⊓ Ry) (fi i) := by
    have hi := hmem i (hW i)
    rwa [Sieve.overEquiv_iff] at hi
  have hsum : C.Contains (∐ (fun i => (BigFppfOver.toScheme C S hS).obj (Wi i))) :=
    (schemeSize_coproduct_le W.X T.left.obj.size T.left.obj.aleph0_le_size hcard
      hsize).trans_lt T.left.property
  obtain ⟨V, j, ⟨hV⟩, e, he⟩ := exists_coproduct_of_contains C S hS Wi hsum
  obtain ⟨hm, hj, hd⟩ := coproduct_cover C S hS Wi V j e he
  let f : V ⟶ T := Cofan.IsColimit.desc hV fi
  have hfac i : j i ≫ f = fi i := Cofan.IsColimit.fac hV fi i
  have hmap : e.hom ≫ C.inclusion.map f.left = Sigma.desc W.f := by
    apply Sigma.hom_ext
    intro i
    rw [← Category.assoc, he i]
    change C.inclusion.map (j i).left ≫ C.inclusion.map f.left = _
    rw [← C.inclusion.map_comp]
    change C.inclusion.map (j i ≫ f).left = _
    rw [hfac, Sigma.ι_comp_desc]
    exact C.inclusion.map_preimage (X := C.obj (hW i)) (Y := T.left) (W.f i)
  let : ∀ i, Flat (W.f i) := W.flat
  let : ∀ i, LocallyOfFinitePresentation (W.f i) := W.lfp
  have hfFlat : Flat (C.inclusion.map f.left) := by
    let : MorphismProperty.RespectsIso (@Flat.{u}) := Flat.isStableUnderBaseChange.respectsIso
    apply (MorphismProperty.cancel_left_of_respectsIso (@Flat.{u}) e.hom _).mp
    rw [hmap]
    infer_instance
  have hfLfp : LocallyOfFinitePresentation (C.inclusion.map f.left) := by
    let : IsZariskiLocalAtSource (@LocallyOfFinitePresentation.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FinitePresentation)
    let : MorphismProperty.RespectsIso (@LocallyOfFinitePresentation.{u}) :=
      locallyOfFinitePresentation_isStableUnderBaseChange.respectsIso
    apply (MorphismProperty.cancel_left_of_respectsIso
      (@LocallyOfFinitePresentation.{u}) e.hom _).mp
    rw [hmap]
    exact IsZariskiLocalAtSource.sigmaDesc
      (P := @LocallyOfFinitePresentation.{u}) (fun i => W.lfp i)
  have hfSurj : Surjective (C.inclusion.map f.left) := by
    constructor
    intro t
    obtain ⟨i, a, ha⟩ := W.jointly_surjective t
    refine ⟨e.hom ((Sigma.ι W.X i) a), ?_⟩
    have hh := congrArg (fun q : W.X i ⟶ T.left.obj => q a)
      (show Sigma.ι W.X i ≫ e.hom ≫ C.inclusion.map f.left = W.f i by
        rw [hmap, Sigma.ι_comp_desc])
    exact hh.trans ha
  obtain ⟨a, ha⟩ := presented_pullback_of_disjoint_cover C S hS G Wi V T j hm hj hd
    f fi hfac x (fun i => hx (fi i) (hfi i).1)
  obtain ⟨b, hb⟩ := presented_pullback_of_disjoint_cover C S hS G Wi V T j hm hj hd
    f fi hfac y (fun i => hy (fi i) (hfi i).2)
  exact ⟨V, f, hfFlat, hfLfp, hfSurj, a, b, ha, hb⟩

/-- **The `Type u` model of `Isom(x, y)`.** The sheaf `Isom(x, y)`, which takes values in
`Type (u + 1)`, is in bijection, naturally in the test object, with a sheaf `F` of `Type u`; and
for every `f : V ⟶ T` over which both `x` and `y` come from points of the object space, the
product of `F` with the presheaf represented by `f` is an algebraic space. -/
theorem exists_shrunk_isomPresheaf
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    (x y : (quotientStack G).p.Fiber T) :
    let I := (Over.iteratedSliceBackward T).op ⋙ (quotientStack G).p.isomPresheaf x y
    ∃ F : (BigFppfOver C T.left.1 T.left.2)ᵒᵖ ⥤ Type u,
      Presheaf.IsSheaf (BigFppfOver.topology C T.left.1 T.left.2) F ∧
      (∃ e : ∀ U, I.obj U ≃ F.obj U,
        ∀ ⦃U V⦄ (f : U ⟶ V) (z : I.obj U), e V (I.map f z) = F.map f (e U z)) ∧
      ∀ (V : BigFppfOver C S hS) (f : V ⟶ T) (a b : G.objects.obj.obj (op V)),
        ((pointwiseToQuotientStackFiber G V).obj a ≅
          Functor.pullbackFiber (quotientStack G).p x f) →
        ((pointwiseToQuotientStackFiber G V).obj b ≅
          Functor.pullbackFiber (quotientStack G).p y f) →
        IsAlgebraicSpace C T.left.1 T.left.2 (yoneda.obj (Over.mk f.left) ⨯ F) := by
  classical
  dsimp only
  let I := (Over.iteratedSliceBackward T).op ⋙ (quotientStack G).p.isomPresheaf x y
  obtain ⟨R, hR, hRlocal⟩ := isomPresheaf_locallyAlgebraicSpace C S hS G T x y
  let p := (quotientStack G).p
  let J := BigFppfOver.topology C S hS
  let P := p.isomPresheaf x y
  let : LocallySmall.{u} (BigFppfOver C S hS) := inferInstance
  have hpStack : p.IsStack J := isStack_quotientStack G
  have hpGroupoid : p.IsFiberedInGroupoids := isFiberedInGroupoids_quotientStack G
  let : p.IsFibered := hpGroupoid.isFibered
  have hP : Presheaf.IsSheaf (J.over T) P :=
    (Presheaf.isSheaf_of_iso_iff (isomPresheafIsoMorPresheaf p hpGroupoid x y)).2
      (hpStack.isMorSheaf T x y)
  have hlocalSmall : ∀ ⦃V⦄ (f : V ⟶ T), R f → Small.{u} (P.obj (op (Over.mk f))) := by
    intro V f hf
    obtain ⟨F, hF, he⟩ := hRlocal (V := V) (f := f) hf
    rcases he with ⟨e⟩
    let V₀ : BigFppfOver C V.left.obj V.left.property := Over.mk (𝟙 (C.obj V.left.property))
    have hobj : (Over.map f).obj ((Over.iteratedSliceBackward V).obj V₀) = Over.mk f := by
      cases V
      rfl
    have ee0 := (e.app (op V₀)).toEquiv
    change ULift.{u + 1} (F.obj (op V₀)) ≃
      P.obj (op ((Over.map f).obj ((Over.iteratedSliceBackward V).obj V₀))) at ee0
    have ee : ULift.{u + 1} (F.obj (op V₀)) ≃ P.obj (op (Over.mk f)) := by
      rw [hobj] at ee0
      exact ee0
    exact Small.mk' (ee.symm.trans Equiv.ulift)
  let R' := (Sieve.overEquiv (Over.mk (𝟙 T))).symm R
  let : EssentiallySmall.{u} (BigFppfOver C S hS) := essentiallySmall_bigFppfOver C S hS
  let : EssentiallySmall.{u} (Over T) := essentiallySmall_sliceOver T
  have hR' : R' ∈ (J.over T) (Over.mk (𝟙 T)) :=
    J.overEquiv_symm_mem_over (Over.mk (𝟙 T)) R hR
  have hlocalSmall' : ∀ ⦃A⦄ (f : A ⟶ Over.mk (𝟙 T)), R' f → Small.{u} (P.obj (op A)) := by
    intro A f hf
    have hf' : R f.left := by
      change (Sieve.overEquiv (Over.mk (𝟙 T))).symm R f at hf
      change R ((Over.forget T).map f) at hf
      simpa using hf
    have hA : Over.mk f.left = A := by
      refine CostructuredArrow.obj_ext _ _ rfl ?_
      simpa using (Over.w f).symm
    rw [← hA]
    exact hlocalSmall f.left hf'
  have hsmallP : ∀ ⦃A : Over T⦄ (g : A ⟶ Over.mk (𝟙 T)), Small.{u} (P.obj (op A)) :=
    fun _ g => small_of_locally_small_on_sieve_essentiallySmall hP R' hR' hlocalSmall' g
  have hsmallI : ∀ U : (BigFppfOver C T.left.1 T.left.2)ᵒᵖ, Small.{u} (I.obj U) :=
    fun U => hsmallP (Over.mkIdTerminal.from ((Over.iteratedSliceBackward T).obj U.unop))
  let F : (BigFppfOver C T.left.1 T.left.2)ᵒᵖ ⥤ Type u := {
    obj U := Shrink (I.obj U)
    map {U V} f := TypeCat.ofHom
      ((equivShrink (I.obj V)).toFun ∘ I.map f ∘ (equivShrink (I.obj U)).symm)
    map_id := by
      intro U
      ext z
      simp [Function.comp_def]
    map_comp := by
      intro U V W f g
      ext z
      simp [Function.comp_def] }
  let e : ∀ U, I.obj U ≃ F.obj U := fun U => equivShrink (I.obj U)
  let eF : F ⋙ uliftFunctor.{u + 1, u} ≅ I := NatIso.ofComponents
    (fun U => (Equiv.ulift.trans (equivShrink (I.obj U)).symm).toIso) (by
      intro U V f
      ext z
      change (equivShrink (I.obj V)).symm
        (equivShrink (I.obj V) (I.map f ((equivShrink (I.obj U)).symm z.down))) = _
      simp only [Equiv.symm_apply_apply]
      rfl)
  let J' := BigFppfOver.topology C T.left.obj T.left.property
  let : (Over.iteratedSliceBackward T).IsContinuous J' (J.over T) := by
    change T.iteratedSliceBackward.IsContinuous (C.topology.over T.left)
      ((C.topology.over (C.obj hS)).over T)
    infer_instance
  have hI : Presheaf.IsSheaf J' I :=
    ((Over.iteratedSliceBackward T).sheafPushforwardContinuous (Type (u + 1))
      J' (J.over T)).obj ⟨P, hP⟩ |>.property
  have hFsheaf : Presheaf.IsSheaf J' F := Presheaf.isSheaf_of_isSheaf_comp J' F
    uliftFunctor.{u + 1, u} ((Presheaf.isSheaf_of_iso_iff eF).mpr hI)
  refine ⟨F, hFsheaf, ⟨e, ?_⟩, ?_⟩
  · intro U V f z
    change equivShrink (I.obj V) (I.map f z) =
      equivShrink (I.obj V) (I.map f ((equivShrink (I.obj U)).symm (equivShrink (I.obj U) z)))
    simp
  · intro V f a b ex ey
    let A := (Over.iteratedSliceBackward V).op ⋙ arrowFiberOver G V a b
    have hA : IsAlgebraicSpace C V.left.obj V.left.property A :=
      isAlgebraicSpace_iteratedSlice_arrowFiberOver C S hS G V a b
    let eA : A ⋙ uliftFunctor.{u + 1, u} ≅
        ((Over.map f.left).op ⋙ F) ⋙ uliftFunctor.{u + 1, u} :=
      Functor.isoWhiskerLeft (Over.iteratedSliceBackward V).op
        (isomPresheafPullbackIso G V a b
          ((pointwiseToQuotientStackFiber G V).obj a)
          ((pointwiseToQuotientStackFiber G V).obj b) rfl rfl) ≪≫
      Functor.isoWhiskerLeft (Over.iteratedSliceBackward V).op
        (isomPresheafIsoOfIso p ex ey) ≪≫
      Functor.isoWhiskerLeft (Over.iteratedSliceBackward V).op
        (isomPresheafPullbackCompIso p x y f) ≪≫
      Functor.isoWhiskerRight (NatIso.op (iteratedSliceBackwardMapNatIso f).symm) P ≪≫
      (Functor.isoWhiskerLeft (Over.map f.left).op eF).symm
    let L := (Functor.whiskeringRight
      (BigFppfOver C V.left.obj V.left.property)ᵒᵖ (Type u) (Type (u + 1))).obj
      uliftFunctor.{u + 1, u}
    have hres : IsAlgebraicSpace C V.left.obj V.left.property
        ((Over.map f.left).op ⋙ F) :=
      AlgebraicGeometry.Space.isAlgebraicSpace_of_iso C V.left.obj V.left.property
        (L.preimageIso eA) hA
    exact (isAlgebraicSpace_restrict_iff_product C V.left.obj T.left.obj
      V.left.property T.left.property f.left F).mp hres

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site exceeds the default limit
/-- The sheaf `Isom(x, y)` of isomorphisms between two objects of the quotient stack of a groupoid
in algebraic spaces, read on the big fppf site of the scheme the test object lies over, is an
algebraic space over that scheme.

Algebraicity is expressed by a pointwise bijection, natural in the test object, with a presheaf
of `Type u` which is an algebraic space: the hom sets of the stackification are not small, so
`Isom(x, y)` itself takes values one universe up. -/
@[stacks 04TB]
theorem isAlgebraicSpace_isomPresheaf
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    (x y : (quotientStack G).p.Fiber T) :
    let I := (Over.iteratedSliceBackward T).op ⋙ (quotientStack G).p.isomPresheaf x y
    ∃ F : (BigFppfOver C T.left.1 T.left.2)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace C T.left.1 T.left.2 F ∧
        ∃ e : ∀ U, I.obj U ≃ F.obj U,
          ∀ ⦃U V⦄ (f : U ⟶ V) (z : I.obj U), e V (I.map f z) = F.map f (e U z) := by
  classical
  obtain ⟨F, hFsheaf, ⟨e, he⟩, hrestriction⟩ := exists_shrunk_isomPresheaf C S hS B G T x y
  refine ⟨F, ?_, e, he⟩
  obtain ⟨V, f, hfFlat, hfLfp, hfSurj, a, b, ⟨ex⟩, ⟨ey⟩⟩ :=
    exists_single_cover_presented_pair C S hS G T x y
  have hprod : IsAlgebraicSpace C T.left.obj T.left.property
      (yoneda.obj (Over.mk f.left) ⨯ F) := hrestriction V f a b ex ey
  let J' := BigFppfOver.topology C T.left.obj T.left.property
  let E : PreZeroHypercover.{u + 1} (Over.mk (𝟙 T.left)) :=
    PreZeroHypercover.singleton (Over.homMk f.left : Over.mk f.left ⟶ Over.mk (𝟙 T.left))
  have hEfppf : (E.map (BigFppfOver.toScheme C T.left.obj T.left.property)).presieve₀ ∈
      Scheme.fppfPrecoverage ((BigFppfOver.toScheme C T.left.obj T.left.property).obj
        (Over.mk (𝟙 T.left))) := by
    rw [PreZeroHypercover.presieve₀, Scheme.fppfPrecoverage,
      Scheme.ofArrows_mem_precoverage_iff]
    constructor
    · intro t
      obtain ⟨z, hz⟩ := hfSurj.surj t
      exact ⟨PUnit.unit, z, hz⟩
    · intro i
      exact ⟨hfFlat, hfLfp⟩
  have hE : BigFppfOver.IsCovering C T.left.obj T.left.property
      ⟨Over.mk (𝟙 (C.obj T.left.property)), E⟩ :=
    ⟨isFppfCovering_of_presieve₀_mem C T.left.obj T.left.property E hEfppf,
      (C.coverings_isSite.1 (𝟙 T.left)).2⟩
  let H : Sheaf J' (Type u) := ⟨yoneda.obj (Over.mk f.left) ⨯ F, hprod.isSheaf⟩
  have hc : IsColimit (Cofan.mk H (fun _ : E.I₀ => 𝟙 H)) :=
    Cofan.IsColimit.mk _ (fun c => c.inj PUnit.unit) (by rintro c ⟨⟩; simp)
      (by rintro c m hm; simpa using hm PUnit.unit)
  exact isAlgebraicSpace_of_isCovering hFsheaf E hE (fun _ => hprod) (fun _ => 𝟙 H) hc hprod

end Global

end AlgebraicGeometry.Stack

end
