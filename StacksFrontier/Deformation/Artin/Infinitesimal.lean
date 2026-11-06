module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic.LinearCombination
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.FiberedCategory.ChoiceOfPullbacks
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoCategory
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Basic
public import StacksFrontier.Deformation.Lift

/-!
# Infinitesimal deformations

An *infinitesimal deformation* of an object `x` of a category fibred in groupoids over a
base `U` is a lift of `x` along an arrow `U' ⟶ U` of the base. This file develops the
three basic structural facts about such lifts.

First, lifts are *functorial*: a morphism `F` of categories fibred in groupoids, together
with a morphism `φ` from an object `y` over `V` to the pullback of `F x`, induces a functor
from lifts of `x` along `U' ⟶ U` to lifts of `y` along `V' ⟶ V`, for any commutative square
`c ≫ a = d ≫ b` in the base. The functor comes equipped with natural cartesian comparison
arrows, and it is unique up to a unique isomorphism commuting with those arrows. Applied to
the square of affine schemes attached to a morphism of deformation situations, this is the
pullback of lifts; applied to a composite of morphisms of fibred groupoids it gives the
composition isomorphism.

Second, a *deformation situation* is a surjection of rings with square-zero kernel, and a
composable triple of deformation situations over a common quotient is *short exact* when its
kernels form a short exact sequence. In that case the composite of the two transition maps
factors through the common quotient.

Third, for two lifts of one object the relative infinitesimal automorphisms of either lift
act on the morphisms between them, by precomposition on the left and by postcomposition on
the right, and each action is simply transitive.

## Main definitions

* `Deformation.Artin.Lift` — lifts of `x` along `a : U' ⟶ U`, together with their specified
  identification with `x` after restriction along `a`.
* `Deformation.Artin.LiftFunctor` — a functor between categories of lifts, bundled with its
  natural cartesian comparison arrows.
* `Deformation.Artin.IsDeformationSituation` — a square-zero surjection of rings.
* `Deformation.Artin.IsShortExactSequence` — short exactness of a composable triple of
  deformation situations.
* `Deformation.Artin.compositionMap` — composition of a morphism of lifts with relative
  infinitesimal automorphisms at both of its endpoints.
* `Deformation.Artin.leftCompositionAction`, `Deformation.Artin.rightCompositionAction` — the
  two resulting actions on morphisms of lifts.

## Main results

* `Deformation.Artin.liftFunctorOfPullback` — the induced functor on lifts attached to a
  commutative square in the base and a morphism out of the chosen pullback.
* `Deformation.Artin.liftFunctor_unique` — uniqueness of that functor up to a unique
  isomorphism commuting with the comparison arrows.
* `Deformation.Artin.liftFunctor_comp` — the comparison of the functor attached to a
  composite with the composite of the two attached functors.
* `Deformation.Artin.exists_factorization_through_base` — the composite of the transition
  maps of a short exact sequence of deformation situations factors through the base.
* `Deformation.Artin.splitExtensionRingEquiv` — the canonical isomorphism identifying `A₁`
  with the trivial square-zero extension of `A` by the kernel of `q₁`.
* `Deformation.Artin.leftComposition_bijective`,
  `Deformation.Artin.rightComposition_bijective` — simple transitivity of the two actions.

## References

* [Stacks Project, Tag 07Y7](https://stacks.math.columbia.edu/tag/07Y7)
* [Stacks Project, Tag 07YA](https://stacks.math.columbia.edu/tag/07YA)
* [Stacks Project, Tag 07YB](https://stacks.math.columbia.edu/tag/07YB)
* [Stacks Project, Tag 07YE](https://stacks.math.columbia.edu/tag/07YE)
-/

@[expose] public section

namespace Deformation.Artin

/-! ### Functoriality of categories of lifts -/

section
open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]
variable {X : Type u₂} [Category.{v₂} X]
variable {Y : Type u₃} [Category.{v₃} Y]

/-- Lifts of `x` along `a : U' ⟶ U`, including their specified identification with `x`
after restriction. -/
public abbrev Lift (p : X ⥤ C) {U' U : C} (a : U' ⟶ U) (x : X)
    (hx : p.obj x = U) :=
  (Over.post p).Fiber (Over.mk (a ≫ eqToHom hx.symm))

/-- A functor on lifts induced by a morphism of fibred categories and a morphism over the
base-change arrow. The comparison maps give the canonical cartesian squares and are natural in
morphisms of lifts. -/
public structure LiftFunctor (p : X ⥤ C) (q : Y ⥤ C) (F : X ⥤ Y)
    {U' U V' V : C} (a : U' ⟶ U) (b : V ⟶ U) (c : V' ⟶ U') (d : V' ⟶ V)
    (x : X) (hx : p.obj x = U) (y : Y) (hy : q.obj y = V)
    (φ : y ⟶ F.obj x) where
  /-- The underlying functor on categories of lifts. -/
  toFunctor : Lift p a x hx ⥤ Lift q d y hy
  /-- The comparison arrow from the image of a lift to the image under `F` of that lift. -/
  comparison (t : Lift p a x hx) :
    (toFunctor.obj t).1.left ⟶ F.obj t.1.left
  /-- Each comparison arrow is strongly cartesian over `c`. -/
  isCartesian (t : Lift p a x hx) :
    q.IsStronglyCartesian c (comparison t)
  /-- The square formed by a lift, its image, the comparison arrow and `φ` commutes. -/
  comm (t : Lift p a x hx) :
    (toFunctor.obj t).1.hom ≫ φ = comparison t ≫ F.map t.1.hom
  /-- The comparison arrows are natural in morphisms of lifts. -/
  natural {s t : Lift p a x hx} (m : s ⟶ t) :
    (toFunctor.map m).1.1 ≫ comparison t =
      comparison s ≫ F.map m.1.1

/-- The image of an object of a fibre under a functor over the base. -/
public def imageFiber (p : X ⥤ C) (q : Y ⥤ C) (F : X ⥤ Y)
    (hF : F ⋙ q = p) {U : C} (x : X) (hx : p.obj x = U) : q.Fiber U :=
  ⟨F.obj x, (congrArg (fun H : X ⥤ C => H.obj x) hF).trans hx⟩

/-- The morphism `F(x)|_V ⟶ y` of the source gives the corresponding morphism
`y ⟶ F(x)` over `V ⟶ U` by inverting in the groupoid fibre. -/
public noncomputable def pullbackComparison (p : X ⥤ C) (q : Y ⥤ C)
    (hq : q.IsFiberedInGroupoids) (F : X ⥤ Y) (hF : F ⋙ q = p)
    {V U : C} (b : V ⟶ U) (x : X) (hx : p.obj x = U)
    (y : Y) (hy : q.obj y = V) (e : q.ChoiceOfPullbacks)
    (φ : (e.pullbackFunctor b).obj (imageFiber p q F hF x hx) ⟶ ⟨y, hy⟩) :
    y ⟶ F.obj x := by
  letI : IsGroupoid (q.Fiber V) := hq.fiber_isGroupoid V
  letI : IsIso φ := IsGroupoid.all_isIso φ
  exact Functor.Fiber.fiberInclusion.map (inv φ) ≫
    e.map b (imageFiber p q F hF x hx)

/-- The source of a lift of `x` along `a : U' ⟶ U` lies over `U'`. -/
public lemma lift_base_obj (p : X ⥤ C) {U' U : C} (a : U' ⟶ U)
    (x : X) (hx : p.obj x = U) (t : Lift p a x hx) :
    p.obj t.1.left = U' := by
  have ht := t.2
  change (Over.post p).obj t.1 = Over.mk (a ≫ eqToHom hx.symm) at ht
  exact congrArg (fun o : Over (p.obj x) => o.left) ht

/-- The structure arrow of a lift of `x` along `a` lies over `a`. -/
public lemma lift_isHomLift (p : X ⥤ C) {U' U : C} (a : U' ⟶ U)
    (x : X) (hx : p.obj x = U) (t : Lift p a x hx) :
    p.IsHomLift a t.1.hom := by
  apply IsHomLift.of_fac' p a t.1.hom (lift_base_obj p a x hx t) hx
  have h := Over.w (eqToHom t.2)
  have hl : (eqToHom t.2).left = eqToHom (lift_base_obj p a x hx t) := by
    rw [Over.eqToHom_left]
  rw [hl] at h
  simpa [Lift, Over.post] using h.symm

/-- A functor over the base carries an arrow lying over `a` to an arrow lying over `a`. -/
public lemma lift_map_isHomLift (p : X ⥤ C) (q : Y ⥤ C) (F : X ⥤ Y)
    (hF : F ⋙ q = p) {R S : C} (a : R ⟶ S) {u v : X}
    (hu : p.obj u = R) (hv : p.obj v = S) (f : u ⟶ v)
    (hf : p.IsHomLift a f) : q.IsHomLift a (F.map f) := by
  let hdom : q.obj (F.obj u) = R := (Functor.congr_obj hF u).trans hu
  let hcod : q.obj (F.obj v) = S := (Functor.congr_obj hF v).trans hv
  apply IsHomLift.of_fac' q a (F.map f) hdom hcod
  calc
    q.map (F.map f) =
        eqToHom (Functor.congr_obj hF u) ≫ p.map f ≫
          eqToHom (Functor.congr_obj hF v).symm := by
      simpa [Functor.comp_map] using Functor.congr_hom hF f
    _ = eqToHom hdom ≫ a ≫ eqToHom hcod.symm := by
      rw [IsHomLift.fac' p a f]
      simp [eqToHom_trans, Category.assoc]

/-- An arrow to `y` lying over `d` is a lift of `y` along `d`. -/
public noncomputable def liftMk (q : Y ⥤ C) {V' V : C} (d : V' ⟶ V)
    (y : Y) (hy : q.obj y = V) {z : Y} (hz : q.obj z = V') (g : z ⟶ y)
    (hg : q.IsHomLift d g) : Lift q d y hy := by
  refine ⟨Over.mk g, ?_⟩
  cases hz
  change Over.mk (q.map g) = Over.mk (d ≫ eqToHom hy.symm)
  congr 1
  have h := IsHomLift.fac' q d g
  simpa using h

/-- The arrow `y ⟶ F(x)` obtained from the chosen pullback lies over `b`. -/
public lemma pullbackComparison_isHomLift (p : X ⥤ C) (q : Y ⥤ C)
    (hq : q.IsFiberedInGroupoids) (F : X ⥤ Y) (hF : F ⋙ q = p)
    {V U : C} (b : V ⟶ U) (x : X) (hx : p.obj x = U)
    (y : Y) (hy : q.obj y = V) (e : q.ChoiceOfPullbacks)
    (φ : (e.pullbackFunctor b).obj (imageFiber p q F hF x hx) ⟶ ⟨y, hy⟩) :
    q.IsHomLift b (pullbackComparison p q hq F hF b x hx y hy e φ) := by
  let : IsGroupoid (q.Fiber V) := hq.fiber_isGroupoid V
  let : IsIso φ := IsGroupoid.all_isIso φ
  dsimp [pullbackComparison]
  have hInv : q.IsHomLift (𝟙 V) (Functor.Fiber.fiberInclusion.map (inv φ)) := (inv φ).2
  have hMap : q.IsHomLift b (e.map b (imageFiber p q F hF x hx)) :=
    (e.isStronglyCartesian b (imageFiber p q F hF x hx)).toIsHomLift
  have hcomp : q.IsHomLift (𝟙 V ≫ b)
      (Functor.Fiber.fiberInclusion.map (inv φ) ≫ e.map b (imageFiber p q F hF x hx)) :=
    @IsHomLift.comp C Y _ _ q V V U y
      (e.obj b (imageFiber p q F hF x hx)).1 (imageFiber p q F hF x hx).1
      (𝟙 V) b (Functor.Fiber.fiberInclusion.map (inv φ))
      (e.map b (imageFiber p q F hF x hx)) hInv hMap
  simpa [imageFiber, Functor.Fiber.fiberInclusion] using hcomp

/-- The arrow from the chosen pullback of `y` along `d` to the source of the image of a
lift `t`, obtained by factoring through the cartesian arrow `F(t)`. -/
public noncomputable def bridgeComparison (p : X ⥤ C) (q : Y ⥤ C)
    (hq : q.IsFiberedInGroupoids) (F : X ⥤ Y) (hF : F ⋙ q = p)
    {U' U V' V : C} (a : U' ⟶ U) (b : V ⟶ U) (c : V' ⟶ U') (d : V' ⟶ V)
    (hsq : c ≫ a = d ≫ b) (x : X) (hx : p.obj x = U)
    (y : Y) (hy : q.obj y = V) (e : q.ChoiceOfPullbacks)
    (φ : (e.pullbackFunctor b).obj (imageFiber p q F hF x hx) ⟶ ⟨y, hy⟩)
    (t : Lift p a x hx) : (e.obj d ⟨y, hy⟩).1 ⟶ F.obj t.1.left := by
  letI : q.IsHomLift a (F.map t.1.hom) :=
    lift_map_isHomLift p q F hF a (lift_base_obj p a x hx t) hx t.1.hom
      (lift_isHomLift p a x hx t)
  letI : q.IsStronglyCartesian a (F.map t.1.hom) :=
    hq.isStronglyCartesian_homLift a (F.map t.1.hom)
  let ρ := e.map d ⟨y, hy⟩
  let φ₀ := pullbackComparison p q hq F hF b x hx y hy e φ
  letI : q.IsHomLift d ρ := e.isStronglyCartesian d ⟨y, hy⟩ |>.toIsHomLift
  letI : q.IsHomLift b φ₀ :=
    pullbackComparison_isHomLift p q hq F hF b x hx y hy e φ
  exact Functor.IsStronglyCartesian.map q a (F.map t.1.hom) (g := c)
    (show d ≫ b = c ≫ a from hsq.symm) (ρ ≫ φ₀)

/-- The defining factorization of `bridgeComparison` through the cartesian arrow `F(t)`. -/
public lemma bridgeComparison_fac (p : X ⥤ C) (q : Y ⥤ C)
    (hq : q.IsFiberedInGroupoids) (F : X ⥤ Y) (hF : F ⋙ q = p)
    {U' U V' V : C} (a : U' ⟶ U) (b : V ⟶ U) (c : V' ⟶ U') (d : V' ⟶ V)
    (hsq : c ≫ a = d ≫ b) (x : X) (hx : p.obj x = U)
    (y : Y) (hy : q.obj y = V) (e : q.ChoiceOfPullbacks)
    (φ : (e.pullbackFunctor b).obj (imageFiber p q F hF x hx) ⟶ ⟨y, hy⟩)
    (t : Lift p a x hx) :
    bridgeComparison p q hq F hF a b c d hsq x hx y hy e φ t ≫ F.map t.1.hom =
      e.map d ⟨y, hy⟩ ≫ pullbackComparison p q hq F hF b x hx y hy e φ := by
  dsimp [bridgeComparison]
  let : q.IsHomLift a (F.map t.1.hom) :=
    lift_map_isHomLift p q F hF a (lift_base_obj p a x hx t) hx t.1.hom
      (lift_isHomLift p a x hx t)
  let : q.IsStronglyCartesian a (F.map t.1.hom) :=
    hq.isStronglyCartesian_homLift a (F.map t.1.hom)
  let ρ := e.map d ⟨y, hy⟩
  let φ₀ := pullbackComparison p q hq F hF b x hx y hy e φ
  let : q.IsHomLift d ρ := e.isStronglyCartesian d ⟨y, hy⟩ |>.toIsHomLift
  let : q.IsHomLift b φ₀ :=
    pullbackComparison_isHomLift p q hq F hF b x hx y hy e φ
  exact Functor.IsStronglyCartesian.fac q a (F.map t.1.hom)
    (show d ≫ b = c ≫ a from hsq.symm) (ρ ≫ φ₀)

/-- `bridgeComparison` lies over the arrow `c` of the commutative square. -/
public lemma bridgeComparison_isHomLift (p : X ⥤ C) (q : Y ⥤ C)
    (hq : q.IsFiberedInGroupoids) (F : X ⥤ Y) (hF : F ⋙ q = p)
    {U' U V' V : C} (a : U' ⟶ U) (b : V ⟶ U) (c : V' ⟶ U') (d : V' ⟶ V)
    (hsq : c ≫ a = d ≫ b) (x : X) (hx : p.obj x = U)
    (y : Y) (hy : q.obj y = V) (e : q.ChoiceOfPullbacks)
    (φ : (e.pullbackFunctor b).obj (imageFiber p q F hF x hx) ⟶ ⟨y, hy⟩)
    (t : Lift p a x hx) :
    q.IsHomLift c (bridgeComparison p q hq F hF a b c d hsq x hx y hy e φ t) := by
  dsimp [bridgeComparison]
  infer_instance

/-- A morphism of lifts along `a` lies over the identity of the source of `a`. -/
public lemma lift_morphism_isHomLift (p : X ⥤ C) {U' U : C} (a : U' ⟶ U)
    (x : X) (hx : p.obj x = U) {s t : Lift p a x hx} (m : s ⟶ t) :
    p.IsHomLift (𝟙 U') m.1.left := by
  let base : Over (p.obj x) := Over.mk (a ≫ eqToHom hx.symm)
  have hm : (Over.post p).IsHomLift (𝟙 base) m.1 := m.2
  have hfac := IsHomLift.fac' (Over.post p) (𝟙 base) m.1
  have hforget := congrArg ((Over.forget (p.obj x)).map) hfac
  have hdomEq : (Over.post p).obj s.1 = base := s.2
  have hcodEq : (Over.post p).obj t.1 = base := t.2
  have hmap {u v : Over (p.obj x)} (h : u = v) :
      (Over.forget (p.obj x)).map (eqToHom h) = eqToHom (congrArg Over.left h) := by
    rw [eqToHom_map]
  apply IsHomLift.of_fac' p (𝟙 U') m.1.left
    (lift_base_obj p a x hx s) (lift_base_obj p a x hx t)
  have hforget' : p.map m.1.left =
      (Over.forget (p.obj x)).map (eqToHom hdomEq) ≫ 𝟙 U' ≫
        (Over.forget (p.obj x)).map (eqToHom hcodEq.symm) := by
    simpa [← Over.post_forget_eq_forget_comp, Functor.comp_map, base, Lift, Over.post]
      using hforget
  rwa [hmap hdomEq, hmap hcodEq.symm] at hforget'

/-- A commuting triangle over the identity is a morphism of lifts. -/
public def liftHomMk (q : Y ⥤ C) {V' V : C} (d : V' ⟶ V)
    (y : Y) (hy : q.obj y = V) {s t : Lift q d y hy}
    (f : s.1.left ⟶ t.1.left) (hf : q.IsHomLift (𝟙 V') f)
    (h : f ≫ t.1.hom = s.1.hom) : s ⟶ t := by
  refine ⟨Over.homMk f h, ?_⟩
  apply IsHomLift.of_fac' (Over.post q) (𝟙 (Over.mk (d ≫ eqToHom hy.symm)))
    (Over.homMk f h) s.2 t.2
  apply Over.OverMorphism.ext
  change q.map f = _
  let : q.IsHomLift (𝟙 V') f := hf
  have hfac := IsHomLift.fac' q (𝟙 V') f
  rw [hfac]
  simp only [Over.eqToHom_left, Over.comp_left, Category.id_comp]

/-- Every morphism of lifts in a category fibred in groupoids is an isomorphism. -/
public lemma lift_morphism_isIso (q : Y ⥤ C) (hq : q.IsFiberedInGroupoids)
    {V' V : C} (d : V' ⟶ V) (y : Y) (hy : q.obj y = V)
    {s t : Lift q d y hy} (m : s ⟶ t) : IsIso m := by
  let : IsIso m.1.left := by
    let sF : q.Fiber V' := ⟨s.1.left, lift_base_obj q d y hy s⟩
    let tF : q.Fiber V' := ⟨t.1.left, lift_base_obj q d y hy t⟩
    let mF : sF ⟶ tF := ⟨m.1.left, lift_morphism_isHomLift q d y hy m⟩
    let : IsGroupoid (q.Fiber V') := hq.fiber_isGroupoid V'
    have : IsIso mF := inferInstance
    exact Functor.map_isIso (Functor.Fiber.fiberInclusion (p := q) (S := V')) mF
  let iOver := Over.isoMk (asIso m.1.left) (Over.w m.1)
  have hi : m.1 = iOver.hom := by
    apply Over.OverMorphism.ext
    rfl
  let : IsIso m.1 := by
    rw [hi]
    exact Iso.isIso_hom iOver
  let : (Over.post q).IsHomLift
      (𝟙 (Over.mk (d ≫ eqToHom hy.symm))) m.1 := m.2
  refine ⟨⟨inv m.1, ?_⟩, ?_, ?_⟩
  · exact IsHomLift.lift_id_inv_isIso (Over.post q)
      (Over.mk (d ≫ eqToHom hy.symm)) m.1
  · apply Subtype.ext
    apply Over.OverMorphism.ext
    show (m.1 ≫ inv m.1).left = Over.Hom.left (𝟙 s.1)
    exact congrArg Over.Hom.left (IsIso.hom_inv_id m.1)
  · apply Subtype.ext
    apply Over.OverMorphism.ext
    show (inv m.1 ≫ m.1).left = Over.Hom.left (𝟙 t.1)
    exact congrArg Over.Hom.left (IsIso.inv_hom_id m.1)

/-- The image under `F` of the structure arrow of a lift along `a` lies over `a`. -/
public lemma lift_map_hom_isHomLift (p : X ⥤ C) (q : Y ⥤ C) (F : X ⥤ Y)
    (hF : F ⋙ q = p) {U' U : C} (a : U' ⟶ U)
    (x : X) (hx : p.obj x = U) (t : Lift p a x hx) :
    q.IsHomLift a (F.map t.1.hom) :=
  lift_map_isHomLift p q F hF a (lift_base_obj p a x hx t) hx t.1.hom
    (lift_isHomLift p a x hx t)

/-- The canonical functor on lifts attached to a commutative square `c ≫ a = d ≫ b` in the base
and a morphism `F(x)|_V ⟶ y` out of the chosen pullback. -/
@[stacks 07Y7 "the functor"]
public noncomputable def liftFunctorOfPullback (p : X ⥤ C) (q : Y ⥤ C)
    (hq : q.IsFiberedInGroupoids) (F : X ⥤ Y) (hF : F ⋙ q = p)
    {U' U V' V : C} (a : U' ⟶ U) (b : V ⟶ U) (c : V' ⟶ U') (d : V' ⟶ V)
    (hsq : c ≫ a = d ≫ b) (x : X) (hx : p.obj x = U)
    (y : Y) (hy : q.obj y = V) (e : q.ChoiceOfPullbacks)
    (φ : (e.pullbackFunctor b).obj (imageFiber p q F hF x hx) ⟶ ⟨y, hy⟩) :
    LiftFunctor p q F a b c d x hx y hy
      (pullbackComparison p q hq F hF b x hx y hy e φ) := by
  let yF : q.Fiber V := ⟨y, hy⟩
  let zF := e.obj d yF
  let ρ := e.map d yF
  have hρ : q.IsHomLift d ρ := (e.isStronglyCartesian d yF).toIsHomLift
  let baseLift : Lift q d y hy := liftMk q d y hy zF.2 ρ hρ
  let φ₀ := pullbackComparison p q hq F hF b x hx y hy e φ
  have hφ₀ : q.IsHomLift b φ₀ :=
    pullbackComparison_isHomLift p q hq F hF b x hx y hy e φ
  let constLift : Lift p a x hx ⥤ Lift q d y hy := {
    obj := fun _ => baseLift
    map := fun _ => 𝟙 baseLift
    map_id := by intro t; simp
    map_comp := by intro s t u f g; simp
  }
  refine ⟨constLift, bridgeComparison p q hq F hF a b c d hsq x hx y hy e φ, ?_, ?_, ?_⟩
  · intro t
    let : q.IsHomLift c (bridgeComparison p q hq F hF a b c d hsq x hx y hy e φ t) :=
      bridgeComparison_isHomLift p q hq F hF a b c d hsq x hx y hy e φ t
    exact hq.isStronglyCartesian_homLift c
      (bridgeComparison p q hq F hF a b c d hsq x hx y hy e φ t)
  · intro t
    change ρ ≫ φ₀ = bridgeComparison p q hq F hF a b c d hsq x hx y hy e φ t ≫
      F.map t.1.hom
    exact (bridgeComparison_fac p q hq F hF a b c d hsq x hx y hy e φ t).symm
  · intro s t m
    change Over.Hom.left (𝟙 (baseLift.1)) ≫
      bridgeComparison p q hq F hF a b c d hsq x hx y hy e φ t =
      bridgeComparison p q hq F hF a b c d hsq x hx y hy e φ s ≫ F.map m.1.left
    simp only [Over.id_left]
    change (𝟙 zF.1) ≫
      bridgeComparison p q hq F hF a b c d hsq x hx y hy e φ t =
      bridgeComparison p q hq F hF a b c d hsq x hx y hy e φ s ≫ F.map m.1.left
    simp only [Category.id_comp]
    change bridgeComparison p q hq F hF a b c d hsq x hx y hy e φ t =
      bridgeComparison p q hq F hF a b c d hsq x hx y hy e φ s ≫ F.map m.1.left
    let : p.IsHomLift (𝟙 U') m.1.left := lift_morphism_isHomLift p a x hx m
    let : q.IsHomLift (𝟙 U') (F.map m.1.left) :=
      lift_map_isHomLift p q F hF (𝟙 U') (lift_base_obj p a x hx s)
        (lift_base_obj p a x hx t) m.1.left (lift_morphism_isHomLift p a x hx m)
    let : q.IsHomLift a (F.map t.1.hom) := lift_map_hom_isHomLift p q F hF a x hx t
    let : q.IsHomLift c (bridgeComparison p q hq F hF a b c d hsq x hx y hy e φ t) :=
      bridgeComparison_isHomLift p q hq F hF a b c d hsq x hx y hy e φ t
    let compS := bridgeComparison p q hq F hF a b c d hsq x hx y hy e φ s
    let : q.IsHomLift c compS :=
      bridgeComparison_isHomLift p q hq F hF a b c d hsq x hx y hy e φ s
    let : q.IsHomLift c (compS ≫ F.map m.1.left) :=
      IsHomLift.comp_lift_id_right' q c compS U' (F.map m.1.left)
    let : q.IsStronglyCartesian a (F.map t.1.hom) :=
      hq.isStronglyCartesian_homLift a (F.map t.1.hom)
    apply Functor.IsStronglyCartesian.ext q a (F.map t.1.hom) c
    calc
      _ = ρ ≫ φ₀ := bridgeComparison_fac p q hq F hF a b c d hsq x hx y hy e φ t
      _ = compS ≫ F.map s.1.hom :=
        (bridgeComparison_fac p q hq F hF a b c d hsq x hx y hy e φ s).symm
      _ = compS ≫ (F.map m.1.left ≫ F.map t.1.hom) := by
        rw [← Functor.map_comp, Over.w m.1]
      _ = (compS ≫ F.map m.1.left) ≫ F.map t.1.hom := by
        simp [Category.assoc]

/-- Two functors on lifts with cartesian comparison arrows over the same square are uniquely
isomorphic by an isomorphism commuting with their comparison arrows. -/
@[stacks 07Y7 "uniqueness"]
public theorem liftFunctor_unique (p : X ⥤ C) (q : Y ⥤ C)
    (hq : q.IsFiberedInGroupoids) (F : X ⥤ Y)
    {U' U V' V : C} (a : U' ⟶ U) (b : V ⟶ U) (c : V' ⟶ U') (d : V' ⟶ V)
    (x : X) (hx : p.obj x = U) (y : Y) (hy : q.obj y = V)
    (φ : y ⟶ F.obj x)
    (L M : LiftFunctor p q F a b c d x hx y hy φ) :
    ∃! η : L.toFunctor ≅ M.toFunctor,
      ∀ t : Lift p a x hx,
        (η.hom.app t).1.1 ≫ M.comparison t = L.comparison t := by
  cases hy
  let hy : q.obj y = q.obj y := rfl
  have hc : c = 𝟙 V' ≫ c := by simp
  have hv {s t : Lift q d y hy} (m : s ⟶ t) : q.IsHomLift (𝟙 V') m.1.left :=
    lift_morphism_isHomLift q d y hy m
  have hM (t : Lift p a x hx) : q.IsStronglyCartesian c (M.comparison t) := M.isCartesian t
  have hL (t : Lift p a x hx) : q.IsHomLift c (L.comparison t) := (L.isCartesian t).toIsHomLift
  let α (t : Lift p a x hx) :=
    Functor.IsStronglyCartesian.map q c (M.comparison t) hc (L.comparison t)
  have hαv (t : Lift p a x hx) : q.IsHomLift (𝟙 V') (α t) :=
    Functor.IsStronglyCartesian.map_isHomLift q c (M.comparison t) hc (L.comparison t)
  have hα (t : Lift p a x hx) : α t ≫ M.comparison t = L.comparison t :=
    Functor.IsStronglyCartesian.fac q c (M.comparison t) hc (L.comparison t)
  let ηapp (t : Lift p a x hx) : L.toFunctor.obj t ⟶ M.toFunctor.obj t := by
    have hφ : q.IsStronglyCartesian (q.map φ) φ :=
      hq.isStronglyCartesian_homLift (q.map φ) φ
    let : q.IsHomLift d ((M.toFunctor.obj t).1.hom) :=
      lift_isHomLift q d y hy (M.toFunctor.obj t)
    let : q.IsHomLift d ((L.toFunctor.obj t).1.hom) :=
      lift_isHomLift q d y hy (L.toFunctor.obj t)
    let : q.IsHomLift d (α t ≫ (M.toFunctor.obj t).1.hom) := inferInstance
    have htriangle : α t ≫ (M.toFunctor.obj t).1.hom = (L.toFunctor.obj t).1.hom := by
      apply Functor.IsStronglyCartesian.ext q (q.map φ) φ d
      calc
        (α t ≫ (M.toFunctor.obj t).1.hom) ≫ φ =
            α t ≫ M.comparison t ≫ F.map t.1.hom := by
              rw [Category.assoc, M.comm t]
        _ = L.comparison t ≫ F.map t.1.hom := by rw [← hα t, Category.assoc]
        _ = (L.toFunctor.obj t).1.hom ≫ φ := (L.comm t).symm
    exact liftHomMk q d y hy (α t) (hαv t) htriangle
  have ηapp_fac (t : Lift p a x hx) :
      (ηapp t).1.left ≫ M.comparison t = L.comparison t := hα t
  have ηapp_natural {s t : Lift p a x hx} (m : s ⟶ t) :
      ηapp s ≫ M.toFunctor.map m = L.toFunctor.map m ≫ ηapp t := by
    apply Subtype.ext
    apply Over.OverMorphism.ext
    show (ηapp s).1.left ≫ (M.toFunctor.map m).1.left =
      (L.toFunctor.map m).1.left ≫ (ηapp t).1.left
    apply Functor.IsStronglyCartesian.ext q c (M.comparison t) (𝟙 V')
    calc
      ((ηapp s).1.left ≫ (M.toFunctor.map m).1.left) ≫ M.comparison t =
          (ηapp s).1.left ≫ M.comparison s ≫ F.map m.1.left := by
            rw [Category.assoc, M.natural m]
      _ = L.comparison s ≫ F.map m.1.left := by
            rw [← Category.assoc, ηapp_fac]
      _ = (L.toFunctor.map m).1.left ≫ L.comparison t := (L.natural m).symm
      _ = ((L.toFunctor.map m).1.left ≫ (ηapp t).1.left) ≫ M.comparison t := by
            rw [Category.assoc, ηapp_fac]
  let ηcomponents (t : Lift p a x hx) : L.toFunctor.obj t ≅ M.toFunctor.obj t := by
      let : IsIso (ηapp t) := lift_morphism_isIso q hq d y hy (ηapp t)
      exact asIso (ηapp t)
  let η : L.toFunctor ≅ M.toFunctor := NatIso.ofComponents ηcomponents
    (fun {s t} m => (ηapp_natural m).symm)
  have hηapp (t : Lift p a x hx) : η.hom.app t = ηapp t := by
    show (η.app t).hom = (ηcomponents t).hom
    exact congrArg Iso.hom (NatIso.ofComponents.app ηcomponents
      (fun {s t} m => (ηapp_natural m).symm) t)
  refine ⟨η, ?_, ?_⟩
  · intro t
    rw [hηapp t]
    exact ηapp_fac t
  · intro η' hη'
    apply Iso.ext
    apply NatTrans.ext
    funext t
    apply Subtype.ext
    apply Over.OverMorphism.ext
    rw [hηapp t]
    apply Functor.IsStronglyCartesian.ext q c (M.comparison t) (𝟙 V')
    calc
      (η'.hom.app t).1.left ≫ M.comparison t = L.comparison t := hη' t
      _ = (ηapp t).1.left ≫ M.comparison t := (ηapp_fac t).symm

/-- The functor on lifts induced by a composite of morphisms of fibred groupoids is
canonically isomorphic to the composite of the two functors on lifts. The second
morphism acts over the identity square at the target of the first. At every lift,
the isomorphism is the unique vertical morphism commuting with the two cartesian
comparison arrows. -/
@[stacks 07Y7 "compatibility with composition"]
public noncomputable def liftFunctor_comp
    {Z : Type*} [Category Z]
    (p : X ⥤ C) (q : Y ⥤ C) (r : Z ⥤ C)
    (_hq : q.IsFiberedInGroupoids) (hr : r.IsFiberedInGroupoids)
    (F : X ⥤ Y) (G : Y ⥤ Z)
    (_hF : F ⋙ q = p) (hG : G ⋙ r = q)
    {U' U V' V : C} (a : U' ⟶ U) (b : V ⟶ U)
    (c : V' ⟶ U') (d : V' ⟶ V)
    (_hsq : c ≫ a = d ≫ b)
    (x : X) (hx : p.obj x = U)
    (y : Y) (hy : q.obj y = V)
    (z : Z) (hz : r.obj z = V)
    (φ : y ⟶ F.obj x) (ψ : z ⟶ G.obj y)
    (_hφ : q.IsHomLift b φ) (_hψ : r.IsHomLift (𝟙 V) ψ)
    (L : LiftFunctor p q F a b c d x hx y hy φ)
    (M : LiftFunctor q r G d (𝟙 V) (𝟙 V') d y hy z hz ψ)
    (N : LiftFunctor p r (F ⋙ G) a b c d x hx z hz (ψ ≫ G.map φ)) :
    {η : L.toFunctor ⋙ M.toFunctor ≅ N.toFunctor //
      ∀ t : Lift p a x hx,
        (η.hom.app t).1.1 ≫ N.comparison t =
          M.comparison (L.toFunctor.obj t) ≫ G.map (L.comparison t)} := by
  let γ (t : Lift p a x hx) :=
    M.comparison (L.toFunctor.obj t) ≫ G.map (L.comparison t)
  let K : LiftFunctor p r (F ⋙ G) a b c d x hx z hz (ψ ≫ G.map φ) := {
    toFunctor := L.toFunctor ⋙ M.toFunctor
    comparison := γ
    isCartesian := by
      intro t
      let : r.IsStronglyCartesian (𝟙 V')
          (M.comparison (L.toFunctor.obj t)) := M.isCartesian (L.toFunctor.obj t)
      let : q.IsHomLift c (L.comparison t) := (L.isCartesian t).toIsHomLift
      let hGmap : r.IsHomLift c (G.map (L.comparison t)) :=
        lift_map_isHomLift q r G hG c
          (IsHomLift.domain_eq q c (L.comparison t))
          (IsHomLift.codomain_eq q c (L.comparison t))
          (L.comparison t) (L.isCartesian t).toIsHomLift
      let : r.IsHomLift c (G.map (L.comparison t)) := hGmap
      let : r.IsStronglyCartesian c (G.map (L.comparison t)) :=
        hr.isStronglyCartesian_homLift c (G.map (L.comparison t))
      simpa [γ] using
        (inferInstance : r.IsStronglyCartesian
          (𝟙 V' ≫ c) (M.comparison (L.toFunctor.obj t) ≫ G.map (L.comparison t)))
    comm := by
      intro t
      let u := L.toFunctor.obj t
      change (M.toFunctor.obj u).1.hom ≫ (ψ ≫ G.map φ) =
        γ t ≫ (F ⋙ G).map t.1.hom
      calc
        (M.toFunctor.obj u).1.hom ≫ (ψ ≫ G.map φ) =
            ((M.toFunctor.obj u).1.hom ≫ ψ) ≫ G.map φ := by simp [Category.assoc]
        _ = (M.comparison u ≫ G.map u.1.hom) ≫ G.map φ := by rw [M.comm u]
        _ = M.comparison u ≫ G.map (u.1.hom ≫ φ) := by
          simp only [Category.assoc, ← G.map_comp]
        _ = M.comparison u ≫ G.map (L.comparison t ≫ F.map t.1.hom) := by
          rw [L.comm t]
        _ = (M.comparison u ≫ G.map (L.comparison t)) ≫
              G.map (F.map t.1.hom) := by
          exact (congrArg (fun f => M.comparison u ≫ f)
            (G.map_comp (L.comparison t) (F.map t.1.hom))).trans
              (Category.assoc _ _ _).symm
        _ = γ t ≫ (F ⋙ G).map t.1.hom := by
          change (M.comparison (L.toFunctor.obj t) ≫ G.map (L.comparison t)) ≫
            G.map (F.map t.1.hom) = _
          rfl
    natural := by
      intro s t m
      change (M.toFunctor.map (L.toFunctor.map m)).1.left ≫ γ t =
        γ s ≫ (F ⋙ G).map m.1.left
      calc
        (M.toFunctor.map (L.toFunctor.map m)).1.left ≫ γ t =
            ((M.toFunctor.map (L.toFunctor.map m)).1.left ≫
              M.comparison (L.toFunctor.obj t)) ≫ G.map (L.comparison t) := by
                dsimp [γ]
                exact (Category.assoc _ _ _).symm
        _ = (M.comparison (L.toFunctor.obj s) ≫
              G.map ((L.toFunctor.map m).1.left)) ≫ G.map (L.comparison t) := by
                exact congrArg (fun f => f ≫ G.map (L.comparison t))
                  (M.natural (L.toFunctor.map m))
        _ = M.comparison (L.toFunctor.obj s) ≫
              G.map ((L.toFunctor.map m).1.left ≫ L.comparison t) := by
                exact (Category.assoc _ _ _).trans
                  (congrArg (fun f => M.comparison (L.toFunctor.obj s) ≫ f)
                    (G.map_comp (L.toFunctor.map m).1.left (L.comparison t)).symm)
        _ = M.comparison (L.toFunctor.obj s) ≫
              G.map (L.comparison s ≫ F.map m.1.left) := by
                exact congrArg (fun f => M.comparison (L.toFunctor.obj s) ≫ G.map f)
                  (L.natural m)
        _ = (M.comparison (L.toFunctor.obj s) ≫ G.map (L.comparison s)) ≫
              G.map (F.map m.1.left) := by
                exact (congrArg (fun f => M.comparison (L.toFunctor.obj s) ≫ f)
                  (G.map_comp (L.comparison s) (F.map m.1.left))).trans
                    (Category.assoc _ _ _).symm
        _ = γ s ≫ (F ⋙ G).map m.1.left := rfl
  }
  exact ⟨_, (liftFunctor_unique p r hr (F ⋙ G) a b c d x hx z hz (ψ ≫ G.map φ) K
    N).exists.choose_spec⟩

end

/-! ### Pullback of lifts along a morphism of deformation situations -/

add_to_stacks 07YA "pullback_of_lifts" Deformation.Artin.liftFunctorOfPullback
add_to_stacks 07YA "pullback_of_lifts" Deformation.Artin.liftFunctor_unique

/-! ### Short exact sequences of deformation situations -/

section

universe u₁ u₂ u₃ u

/-- A square-zero surjection of commutative rings, the algebraic part of a deformation
situation. -/
public abbrev IsDeformationSituation {A' : Type u₁} {A : Type u} [CommRing A'] [CommRing A]
    (q : A' →+* A) : Prop :=
  Function.Surjective q ∧ (RingHom.ker q) ^ 2 = ⊥

/-- A composable triple of deformation situations is short exact if its kernel sequence
`0 → I₃ → I₂ → I₁ → 0` is exact. The maps of situations run in the opposite direction
to the ring homomorphisms `f₂₁ : A₂' → A₁'` and `f₃₂ : A₃' → A₂'`. -/
@[stacks 07YE "short_exact_sequence_of_deformation_situations"]
public abbrev IsShortExactSequence {A₁ : Type u₁} {A₂ : Type u₂} {A₃ : Type u₃} {A : Type u}
    [CommRing A₁] [CommRing A₂] [CommRing A₃] [CommRing A]
    (q₁ : A₁ →+* A) (q₂ : A₂ →+* A) (q₃ : A₃ →+* A)
    (f₂₁ : A₂ →+* A₁) (f₃₂ : A₃ →+* A₂) : Prop :=
  IsDeformationSituation q₁ ∧ IsDeformationSituation q₂ ∧ IsDeformationSituation q₃ ∧
    q₁.comp f₂₁ = q₂ ∧ q₂.comp f₃₂ = q₃ ∧
    Function.Injective (fun z : RingHom.ker q₃ => f₃₂ z.1) ∧
    (∀ y : RingHom.ker q₂, f₂₁ y.1 = 0 ↔ ∃ z : RingHom.ker q₃, f₃₂ z.1 = y.1) ∧
    (∀ x : RingHom.ker q₁, ∃ y : RingHom.ker q₂, f₂₁ y.1 = x.1)

/-- The composite `A₃' → A₂' → A₁'` in a short exact sequence of deformation
situations factors through their common quotient `A`. -/
@[stacks 07YE "factorization_through_a"]
public theorem exists_factorization_through_base
    {A₁ : Type u₁} {A₂ : Type u₂} {A₃ : Type u₃} {A : Type u}
    [CommRing A₁] [CommRing A₂] [CommRing A₃] [CommRing A]
    (q₁ : A₁ →+* A) (q₂ : A₂ →+* A) (q₃ : A₃ →+* A)
    (f₂₁ : A₂ →+* A₁) (f₃₂ : A₃ →+* A₂)
    (h : IsShortExactSequence q₁ q₂ q₃ f₂₁ f₃₂) :
    ∃ g : A →+* A₁, g.comp q₃ = f₂₁.comp f₃₂ := by
  rcases h with ⟨_, _, ⟨hsurj, _⟩, _, hcomm, _, hexact, _⟩
  refine ⟨q₃.liftOfSurjective hsurj ⟨f₂₁.comp f₃₂, ?_⟩, q₃.liftOfSurjective_comp ..⟩
  intro x hx
  exact (hexact ⟨f₃₂ x, by
    simpa only [RingHom.mem_ker, ← hcomm, RingHom.comp_apply] using hx⟩).2 ⟨⟨x, hx⟩, rfl⟩

/-- The square-zero kernel of a deformation situation `q : A' →+* A`, as a module over `A`
through the isomorphism `A' ⧸ RingHom.ker q ≃+* A`. -/
noncomputable def kerModule {A' : Type u₁} {A : Type u} [CommRing A'] [CommRing A]
    (q : A' →+* A) (hq : IsDeformationSituation q) : Module A (RingHom.ker q) :=
  letI : Module (A' ⧸ RingHom.ker q) (RingHom.ker q) :=
    Module.IsTorsionBySet.module (R := A') (M := RingHom.ker q) (I := RingHom.ker q)
      fun x a => by
        have hm : (a : A') * (x : A') ∈ RingHom.ker q ^ 2 := by
          rw [pow_two]; exact Ideal.mul_mem_mul a.2 x.2
        rw [hq.2] at hm
        ext
        simpa using hm
  Module.compHom _ (RingHom.quotientKerEquivOfSurjective hq.1).symm.toRingHom

/-- The action of `A` on the kernel of a deformation situation `q : A' →+* A` through
`kerModule` agrees with the action of any preimage of the scalar under `q`. -/
theorem kerModule_smul {A' : Type u₁} {A : Type u} [CommRing A'] [CommRing A]
    (q : A' →+* A) (hq : IsDeformationSituation q) (x : A') (y : RingHom.ker q) :
    letI := kerModule q hq
    q x • y = x • y := by
  let : Module (A' ⧸ RingHom.ker q) (RingHom.ker q) :=
    Module.IsTorsionBySet.module (R := A') (M := RingHom.ker q) (I := RingHom.ker q)
      fun x a => by
        have hm : (a : A') * (x : A') ∈ RingHom.ker q ^ 2 := by
          rw [pow_two]; exact Ideal.mul_mem_mul a.2 x.2
        rw [hq.2] at hm
        ext
        simpa using hm
  show ((RingHom.quotientKerEquivOfSurjective hq.1).symm (q x)) • y = x • y
  have hxy : (RingHom.quotientKerEquivOfSurjective hq.1).symm (q x) = Ideal.Quotient.mk _ x := by
    rw [RingEquiv.symm_apply_eq]; rfl
  rw [hxy]; rfl

/-- **The canonical isomorphism `A₁ = A[I₁]`.** In a short exact sequence of deformation
situations, the splitting of `q₁` produced by `exists_factorization_through_base` exhibits
`A₁` as the trivial square-zero extension of `A` by its kernel `I₁ = ker q₁`. -/
@[stacks 07YE "canonical_isomorphism"]
noncomputable def splitExtensionRingEquiv
    {A₁ : Type u₁} {A₂ : Type u₂} {A₃ : Type u₃} {A : Type u}
    [CommRing A₁] [CommRing A₂] [CommRing A₃] [CommRing A]
    {q₁ : A₁ →+* A} {q₂ : A₂ →+* A} {q₃ : A₃ →+* A}
    {f₂₁ : A₂ →+* A₁} {f₃₂ : A₃ →+* A₂}
    (h : IsShortExactSequence q₁ q₂ q₃ f₂₁ f₃₂) :
    letI := kerModule q₁ h.1
    letI : Module Aᵐᵒᵖ (RingHom.ker q₁) :=
      Module.compHom _ (RingHom.fromOpposite (RingHom.id A) fun _ _ => Commute.all _ _)
    letI : IsCentralScalar A (RingHom.ker q₁) := ⟨fun _ _ => rfl⟩
    A₁ ≃+* TrivSqZeroExt A (RingHom.ker q₁) := by
  letI := kerModule q₁ h.1
  letI : Module Aᵐᵒᵖ (RingHom.ker q₁) :=
    Module.compHom _ (RingHom.fromOpposite (RingHom.id A) fun _ _ => Commute.all _ _)
  letI : IsCentralScalar A (RingHom.ker q₁) := ⟨fun _ _ => rfl⟩
  let g := (exists_factorization_through_base q₁ q₂ q₃ f₂₁ f₃₂ h).choose
  have hg : g.comp q₃ = f₂₁.comp f₃₂ :=
    (exists_factorization_through_base q₁ q₂ q₃ f₂₁ f₃₂ h).choose_spec
  have hgq3 : q₁.comp (g.comp q₃) = q₃ := by
    rw [hg, ← RingHom.comp_assoc, h.2.2.2.1, h.2.2.2.2.1]
  have hgq1 : ∀ a : A, q₁ (g a) = a := by
    intro a
    obtain ⟨x, hx⟩ := h.2.2.1.1 a
    have hcg := congrArg (fun φ : A₃ →+* A => φ x) hgq3
    simpa [hx] using hcg
  have hmem : ∀ a' : A₁, a' - g (q₁ a') ∈ RingHom.ker q₁ := fun a' => by
    rw [RingHom.mem_ker, map_sub, hgq1]; exact sub_self _
  have hz : ∀ a' b' : A₁, (a' - g (q₁ a')) * (b' - g (q₁ b')) = 0 := fun a' b' => by
    have hmul : (a' - g (q₁ a')) * (b' - g (q₁ b')) ∈ RingHom.ker q₁ ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mem_mul (hmem a') (hmem b')
    rwa [h.1.2, Submodule.mem_bot] at hmul
  let ΦtoFun : A₁ → TrivSqZeroExt A (RingHom.ker q₁) :=
    fun a' => (q₁ a', ⟨a' - g (q₁ a'), hmem a'⟩)
  let Φ : A₁ →+* TrivSqZeroExt A (RingHom.ker q₁) :=
    { toFun := ΦtoFun
      map_one' := by
        refine TrivSqZeroExt.ext ?_ (Subtype.ext ?_)
        · change q₁ 1 = (1 : TrivSqZeroExt A (RingHom.ker q₁)).fst
          simp [map_one]
        · change (1 : A₁) - g (q₁ 1) = ((1 : TrivSqZeroExt A (RingHom.ker q₁)).snd : RingHom.ker q₁)
          simp [map_one]
      map_mul' := fun a' b' => by
        refine TrivSqZeroExt.ext ?_ (Subtype.ext ?_)
        · change q₁ (a' * b') = (ΦtoFun a' * ΦtoFun b').fst
          rw [TrivSqZeroExt.fst_mul]
          change q₁ (a' * b') = q₁ a' * q₁ b'
          rw [map_mul]
        · change a' * b' - g (q₁ (a' * b')) =
            ((ΦtoFun a' * ΦtoFun b').snd : RingHom.ker q₁)
          rw [TrivSqZeroExt.snd_mul]
          change a' * b' - g (q₁ (a' * b')) =
            (q₁ a' • (⟨b' - g (q₁ b'), hmem b'⟩ : RingHom.ker q₁) +
              q₁ b' • (⟨a' - g (q₁ a'), hmem a'⟩ : RingHom.ker q₁) : RingHom.ker q₁)
          rw [kerModule_smul q₁ h.1, kerModule_smul q₁ h.1]
          change a' * b' - g (q₁ (a' * b')) = a' * (b' - g (q₁ b')) + b' * (a' - g (q₁ a'))
          rw [map_mul, map_mul]
          linear_combination -hz a' b'
      map_zero' := by
        refine TrivSqZeroExt.ext ?_ (Subtype.ext ?_)
        · change q₁ 0 = (0 : TrivSqZeroExt A (RingHom.ker q₁)).fst
          simp [map_zero]
        · change (0 : A₁) - g (q₁ 0) = ((0 : TrivSqZeroExt A (RingHom.ker q₁)).snd : RingHom.ker q₁)
          simp [map_zero]
      map_add' := fun a' b' => by
        refine TrivSqZeroExt.ext ?_ (Subtype.ext ?_)
        · change q₁ (a' + b') = (ΦtoFun a' + ΦtoFun b').fst
          rw [TrivSqZeroExt.fst_add]
          change q₁ (a' + b') = q₁ a' + q₁ b'
          rw [map_add]
        · change a' + b' - g (q₁ (a' + b')) =
            ((ΦtoFun a' + ΦtoFun b').snd : RingHom.ker q₁)
          rw [TrivSqZeroExt.snd_add]
          change a' + b' - g (q₁ (a' + b')) = (a' - g (q₁ a')) + (b' - g (q₁ b'))
          rw [map_add, map_add]; ring }
  let Ψ : TrivSqZeroExt A (RingHom.ker q₁) → A₁ := fun p => g p.fst + p.snd.1
  refine RingEquiv.ofBijective Φ (Function.bijective_iff_has_inverse.mpr ⟨Ψ, ?_, ?_⟩)
  · intro a'
    change g (q₁ a') + (a' - g (q₁ a')) = a'
    ring
  · intro p
    have hfst : q₁ (g p.fst + p.snd.1) = p.fst := by
      rw [map_add, hgq1, RingHom.mem_ker.mp p.snd.2, add_zero]
    refine TrivSqZeroExt.ext hfst (Subtype.ext ?_)
    change g p.fst + p.snd.1 - g (q₁ (g p.fst + p.snd.1)) = p.snd.1
    rw [hfst]; ring

end

/-! ### Simply transitive actions on morphisms of lifts -/

section
open CategoryTheory

universe u v uF vF

variable {C : Type u} [Category.{v} C] {F : Type uF} [Category.{vF} F]
variable {p : F ⥤ C} {A' A : C} {g : A' ⟶ A} {x : p.Fiber A}

/-- The fibre object underlying a lift. -/
public abbrev liftFiber (t : Deformation.Lift p g x) : p.Fiber A' :=
  ⟨t.obj, IsHomLift.domain_eq p g t.hom⟩

/-- Relative infinitesimal automorphisms of a lift. -/
public noncomputable abbrev infinitesimalAutomorphisms
    (hp : Deformation.IsCofiberedInGroupoids p)
    (t : Deformation.Lift p g x) :
    Subgroup (Aut (liftFiber t)) :=
  Deformation.relativeInfinitesimalAutomorphisms hp g t.hom t.isHomLift

/-- Composition with relative infinitesimal automorphisms on both sides of a
morphism of lifts. -/
@[stacks 07YB "composition_map"]
public noncomputable def compositionMap
    (hp : Deformation.IsCofiberedInGroupoids p)
    (t₁ t₂ : Deformation.Lift p g x) :
    ((infinitesimalAutomorphisms hp t₁ × (t₁ ⟶ t₂)) ×
      infinitesimalAutomorphisms hp t₂) → (t₁ ⟶ t₂) :=
  fun ⟨⟨a, f⟩, b⟩ =>
    { hom := a.1.asIso.hom.val ≫ f.hom ≫ b.1.asIso.hom.val
      isHomLift := by
        let : p.IsHomLift (𝟙 A') a.1.asIso.hom.val := a.1.asIso.hom.2
        let : p.IsHomLift (𝟙 A') b.1.asIso.hom.val := b.1.asIso.hom.2
        infer_instance
      fac := by
        have ha := (Deformation.mem_relativeInfinitesimalAutomorphisms_iff
          hp g t₁.hom t₁.isHomLift a.1).mp a.2
        have hb := (Deformation.mem_relativeInfinitesimalAutomorphisms_iff
          hp g t₂.hom t₂.isHomLift b.1).mp b.2
        calc
          (a.1.asIso.hom.val ≫ f.hom ≫ b.1.asIso.hom.val) ≫ t₂.hom =
              (a.1.asIso.hom.val ≫ f.hom) ≫ (b.1.asIso.hom.val ≫ t₂.hom) := by
                simp only [Category.assoc]
          _ = (a.1.asIso.hom.val ≫ f.hom) ≫ t₂.hom := by rw [hb]
          _ = a.1.asIso.hom.val ≫ (f.hom ≫ t₂.hom) := by rw [Category.assoc]
          _ = a.1.asIso.hom.val ≫ t₁.hom := by rw [f.fac]
          _ = t₁.hom := ha }

private theorem liftHom_isIso
    (hp : Deformation.IsCofiberedInGroupoids p)
    (t₁ t₂ : Deformation.Lift p g x)
    (f : t₁ ⟶ t₂) : IsIso f.hom := by
  let _ := CategoryTheory.Functor.IsFiberedInGroupoids.fiber_isGroupoid
    hp (Opposite.op A')
  have ht₁ : p.obj t₁.obj = A' := IsHomLift.domain_eq p g t₁.hom
  have ht₂ : p.obj t₂.obj = A' := IsHomLift.domain_eq p g t₂.hom
  let : p.IsHomLift (𝟙 A') f.hom := f.isHomLift
  have hfop : (p.op).IsHomLift (𝟙 (Opposite.op A')) (f.hom).op := by
    apply IsHomLift.of_fac'
      (p := p.op) (𝟙 (Opposite.op A')) f.hom.op
      (congrArg Opposite.op ht₂) (congrArg Opposite.op ht₁)
    have h := IsHomLift.fac' p (𝟙 A') f.hom
    simpa using congrArg (fun q => q.op) h
  let _ := hfop
  let a : (p.op).Fiber (Opposite.op A') :=
    ⟨Opposite.op t₂.obj, congrArg Opposite.op ht₂⟩
  let b : (p.op).Fiber (Opposite.op A') :=
    ⟨Opposite.op t₁.obj, congrArg Opposite.op ht₁⟩
  let φ : a ⟶ b := CategoryTheory.Functor.Fiber.homMk p.op
    (Opposite.op A') (f.hom).op
  have hφ : IsIso φ := by infer_instance
  have hmap : IsIso (f.hom).op := by
    have h := Functor.map_isIso (CategoryTheory.Functor.Fiber.fiberInclusion (p := p.op)
      (S := Opposite.op A')) φ
    change IsIso f.hom.op at h
    exact h
  exact (isIso_op_iff f.hom).mp hmap

/-- The left action of relative infinitesimal automorphisms of the source lift
on morphisms of lifts, by inverse precomposition. -/
@[stacks 07YB "groupoid_actions"]
public noncomputable def leftCompositionAction
    (hp : Deformation.IsCofiberedInGroupoids p)
    (t₁ t₂ : Deformation.Lift p g x)
    (a : infinitesimalAutomorphisms hp t₁) (f : t₁ ⟶ t₂) : t₁ ⟶ t₂ :=
  compositionMap hp t₁ t₂ ((a⁻¹, f), 1)

/-- The right action of relative infinitesimal automorphisms of the target lift
on morphisms of lifts, by inverse postcomposition. -/
@[stacks 07YB "groupoid_actions"]
public noncomputable def rightCompositionAction
    (hp : Deformation.IsCofiberedInGroupoids p)
    (t₁ t₂ : Deformation.Lift p g x)
    (f : t₁ ⟶ t₂) (b : infinitesimalAutomorphisms hp t₂) : t₁ ⟶ t₂ :=
  compositionMap hp t₁ t₂ ((1, f), b⁻¹)

private theorem fiberAut_hom_one (z : p.Fiber A') :
    (1 : Aut z).asIso.hom = 𝟙 z := rfl

private theorem fiber_id_val (z : p.Fiber A') :
    (𝟙 z : z ⟶ z).val = 𝟙 z.1 := rfl

private theorem infinitesimalAut_inv_mul_hom
    (hp : Deformation.IsCofiberedInGroupoids p)
    (t : Deformation.Lift p g x)
    (a b : infinitesimalAutomorphisms hp t) :
    ((a * b)⁻¹).1.asIso.hom.val = (a⁻¹).1.asIso.hom.val ≫ (b⁻¹).1.asIso.hom.val := rfl

private noncomputable def leftOrbitInverse
    (hp : Deformation.IsCofiberedInGroupoids p)
    (t₁ t₂ : Deformation.Lift p g x)
    (f h : t₁ ⟶ t₂) : infinitesimalAutomorphisms hp t₁ := by
  letI := liftHom_isIso hp t₁ t₂ f
  letI := liftHom_isIso hp t₁ t₂ h
  letI : p.IsHomLift (𝟙 A') (inv h.hom) := inferInstance
  letI : p.IsHomLift (𝟙 A') (inv f.hom) := inferInstance
  let φ : liftFiber t₁ ⟶ liftFiber t₁ :=
    CategoryTheory.Functor.Fiber.homMk p A' (f.hom ≫ inv h.hom)
  let ψ : liftFiber t₁ ⟶ liftFiber t₁ :=
    CategoryTheory.Functor.Fiber.homMk p A' (h.hom ≫ inv f.hom)
  let c : Aut (liftFiber t₁) := .of {
    hom := φ
    inv := ψ
    hom_inv_id := by
      apply Subtype.ext
      change (f.hom ≫ inv h.hom) ≫ (h.hom ≫ inv f.hom) = 𝟙 t₁.obj
      simp [Category.assoc]
    inv_hom_id := by
      apply Subtype.ext
      change (h.hom ≫ inv f.hom) ≫ (f.hom ≫ inv h.hom) = 𝟙 t₁.obj
      simp [Category.assoc] }
  refine ⟨c, ?_⟩
  apply (Deformation.mem_relativeInfinitesimalAutomorphisms_iff
    hp g t₁.hom t₁.isHomLift c).2
  simp only [c]
  change (f.hom ≫ inv h.hom) ≫ t₁.hom = t₁.hom
  calc
    (f.hom ≫ inv h.hom) ≫ t₁.hom = f.hom ≫ t₂.hom := by
      rw [Category.assoc, ← h.fac]
      simp
    _ = t₁.hom := f.fac

private noncomputable def rightOrbitInverse
    (hp : Deformation.IsCofiberedInGroupoids p)
    (t₁ t₂ : Deformation.Lift p g x)
    (f h : t₁ ⟶ t₂) : infinitesimalAutomorphisms hp t₂ := by
  letI := liftHom_isIso hp t₁ t₂ f
  letI := liftHom_isIso hp t₁ t₂ h
  letI : p.IsHomLift (𝟙 A') (inv f.hom) := inferInstance
  letI : p.IsHomLift (𝟙 A') (inv h.hom) := inferInstance
  let φ : liftFiber t₂ ⟶ liftFiber t₂ :=
    CategoryTheory.Functor.Fiber.homMk p A' (inv h.hom ≫ f.hom)
  let ψ : liftFiber t₂ ⟶ liftFiber t₂ :=
    CategoryTheory.Functor.Fiber.homMk p A' (inv f.hom ≫ h.hom)
  let c : Aut (liftFiber t₂) := .of {
    hom := φ
    inv := ψ
    hom_inv_id := by
      apply Subtype.ext
      change (inv h.hom ≫ f.hom) ≫ (inv f.hom ≫ h.hom) = 𝟙 t₂.obj
      simp [Category.assoc]
    inv_hom_id := by
      apply Subtype.ext
      change (inv f.hom ≫ h.hom) ≫ (inv h.hom ≫ f.hom) = 𝟙 t₂.obj
      simp [Category.assoc] }
  refine ⟨c, ?_⟩
  apply (Deformation.mem_relativeInfinitesimalAutomorphisms_iff
    hp g t₂.hom t₂.isHomLift c).2
  simp only [c]
  change (inv h.hom ≫ f.hom) ≫ t₂.hom = t₂.hom
  calc
    (inv h.hom ≫ f.hom) ≫ t₂.hom = inv h.hom ≫ t₁.hom := by rw [Category.assoc, f.fac]
    _ = t₂.hom := by rw [← h.fac]; simp

private theorem leftCompositionAction_hom
    (hp : Deformation.IsCofiberedInGroupoids p)
    (t₁ t₂ : Deformation.Lift p g x)
    (a : infinitesimalAutomorphisms hp t₁) (f : t₁ ⟶ t₂) :
    (leftCompositionAction hp t₁ t₂ a f).hom = (a⁻¹).1.asIso.hom.val ≫ f.hom := by
  simp [leftCompositionAction, compositionMap, fiberAut_hom_one, fiber_id_val]

private theorem leftOrbitInverse_apply
    (hp : Deformation.IsCofiberedInGroupoids p)
    (t₁ t₂ : Deformation.Lift p g x)
    (f h : t₁ ⟶ t₂) :
    leftCompositionAction hp t₁ t₂ (leftOrbitInverse hp t₁ t₂ f h) f = h := by
  let _ := liftHom_isIso hp t₁ t₂ f
  apply Deformation.Lift.Hom.ext
  rw [leftCompositionAction_hom]
  dsimp [leftOrbitInverse]
  show (h.hom ≫ inv f.hom) ≫ f.hom = h.hom
  simp [Category.assoc]

private theorem rightCompositionAction_hom
    (hp : Deformation.IsCofiberedInGroupoids p)
    (t₁ t₂ : Deformation.Lift p g x)
    (f : t₁ ⟶ t₂) (b : infinitesimalAutomorphisms hp t₂) :
    (rightCompositionAction hp t₁ t₂ f b).hom = f.hom ≫ (b⁻¹).1.asIso.hom.val := by
  simp [rightCompositionAction, compositionMap, fiberAut_hom_one, fiber_id_val]

private theorem rightOrbitInverse_apply
    (hp : Deformation.IsCofiberedInGroupoids p)
    (t₁ t₂ : Deformation.Lift p g x)
    (f h : t₁ ⟶ t₂) :
    rightCompositionAction hp t₁ t₂ f (rightOrbitInverse hp t₁ t₂ f h) = h := by
  let _ := liftHom_isIso hp t₁ t₂ f
  apply Deformation.Lift.Hom.ext
  rw [rightCompositionAction_hom]
  dsimp [rightOrbitInverse]
  show f.hom ≫ (inv f.hom ≫ h.hom) = h.hom
  simp

/-- The identity automorphism acts trivially on the left. -/
@[stacks 07YB "groupoid_actions"]
public theorem leftComposition_one (hp : Deformation.IsCofiberedInGroupoids p)
    (t₁ t₂ : Deformation.Lift p g x) (f : t₁ ⟶ t₂) :
    leftCompositionAction hp t₁ t₂ 1 f = f := by
  apply Deformation.Lift.Hom.ext
  simp [leftCompositionAction_hom, fiberAut_hom_one, fiber_id_val]

/-- The left action is compatible with multiplication of automorphisms. -/
@[stacks 07YB "groupoid_actions"]
public theorem leftComposition_mul (hp : Deformation.IsCofiberedInGroupoids p)
    (t₁ t₂ : Deformation.Lift p g x)
    (a b : infinitesimalAutomorphisms hp t₁) (f : t₁ ⟶ t₂) :
    leftCompositionAction hp t₁ t₂ (a * b) f =
      leftCompositionAction hp t₁ t₂ a (leftCompositionAction hp t₁ t₂ b f) := by
  apply Deformation.Lift.Hom.ext
  simp only [leftCompositionAction_hom]
  rw [infinitesimalAut_inv_mul_hom]
  simp [Category.assoc]

/-- The identity automorphism acts trivially on the right. -/
@[stacks 07YB "groupoid_actions"]
public theorem rightComposition_one (hp : Deformation.IsCofiberedInGroupoids p)
    (t₁ t₂ : Deformation.Lift p g x) (f : t₁ ⟶ t₂) :
    rightCompositionAction hp t₁ t₂ f 1 = f := by
  apply Deformation.Lift.Hom.ext
  simp [rightCompositionAction_hom, fiberAut_hom_one, fiber_id_val]

/-- The right action is compatible with multiplication of automorphisms. -/
@[stacks 07YB "groupoid_actions"]
public theorem rightComposition_mul (hp : Deformation.IsCofiberedInGroupoids p)
    (t₁ t₂ : Deformation.Lift p g x)
    (a b : infinitesimalAutomorphisms hp t₂) (f : t₁ ⟶ t₂) :
    rightCompositionAction hp t₁ t₂ (rightCompositionAction hp t₁ t₂ f a) b =
      rightCompositionAction hp t₁ t₂ f (a * b) := by
  apply Deformation.Lift.Hom.ext
  simp only [rightCompositionAction_hom, Category.assoc]
  rw [infinitesimalAut_inv_mul_hom]

/-- Infinitesimal automorphisms of a lift are determined by their inverses' underlying
morphisms. -/
private theorem eq_of_inv_hom_eq
    (hp : Deformation.IsCofiberedInGroupoids p)
    (t : Deformation.Lift p g x)
    {a b : infinitesimalAutomorphisms hp t}
    (h : (a⁻¹).1.asIso.hom.val = (b⁻¹).1.asIso.hom.val) : a = b := by
  have : (a⁻¹).1 = (b⁻¹).1 :=
    CategoryTheory.Aut.ext (Iso.ext (CategoryTheory.Functor.Fiber.hom_ext h))
  exact inv_injective (Subtype.ext this)

/-- At each morphism of lifts, the orbit map for the left action is a bijection. -/
@[stacks 07YB "groupoid_actions"]
public theorem leftComposition_bijective
    (hp : Deformation.IsCofiberedInGroupoids p)
    (t₁ t₂ : Deformation.Lift p g x)
    (f : t₁ ⟶ t₂) :
    Function.Bijective (fun a : infinitesimalAutomorphisms hp t₁ =>
      leftCompositionAction hp t₁ t₂ a f) :=
  ⟨by
      intro a b hab
      let _ := liftHom_isIso hp t₁ t₂ f
      have hhom := congrArg (fun q : t₁ ⟶ t₂ => q.hom) hab
      rw [leftCompositionAction_hom, leftCompositionAction_hom] at hhom
      have hcancel := congrArg (fun q : t₁.obj ⟶ t₂.obj => q ≫ inv f.hom) hhom
      exact eq_of_inv_hom_eq hp t₁ (by simpa [Category.assoc] using hcancel)
    , by
      intro h
      exact ⟨leftOrbitInverse hp t₁ t₂ f h,
        leftOrbitInverse_apply hp t₁ t₂ f h⟩⟩

/-- At each morphism of lifts, the orbit map for the right action is a bijection. -/
@[stacks 07YB "groupoid_actions"]
public theorem rightComposition_bijective
    (hp : Deformation.IsCofiberedInGroupoids p)
    (t₁ t₂ : Deformation.Lift p g x)
    (f : t₁ ⟶ t₂) :
    Function.Bijective (fun b : infinitesimalAutomorphisms hp t₂ =>
      rightCompositionAction hp t₁ t₂ f b) :=
  ⟨by
      intro a b hab
      let _ := liftHom_isIso hp t₁ t₂ f
      have hhom := congrArg (fun q : t₁ ⟶ t₂ => q.hom) hab
      rw [rightCompositionAction_hom, rightCompositionAction_hom] at hhom
      have hcancel := congrArg (fun q : t₁.obj ⟶ t₂.obj => inv f.hom ≫ q) hhom
      exact eq_of_inv_hom_eq hp t₂ (by simpa [Category.assoc] using hcancel)
    , by
      intro h
      exact ⟨rightOrbitInverse hp t₁ t₂ f h,
        rightOrbitInverse_apply hp t₁ t₂ f h⟩⟩

end

end Deformation.Artin
