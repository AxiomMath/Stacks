module

public import StacksFrontier.CategoryTheory.FiberedCategory.PullbackPseudofunctor
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.FiberIso
public import StacksFrontier.CategoryTheory.Sites.Descent.StrongTransDescentData
public import StacksFrontier.CategoryTheory.Sites.Stack.DescentDataEquivalence
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge
public import Mathlib.CategoryTheory.FiberedCategory.Grothendieck

/-!
# The transition functors of a pseudofunctor are the pullback functors of its fibration

Let `F : LocallyDiscrete 𝒮ᵒᵖ ⥤ᵖ Cat` be a pseudofunctor and let `p = CoGrothendieck.forget F` be
the fibred category it presents, Stacks 003S. Mathlib identifies the fibre of `p` over `S` with
the category `F S` (`CategoryTheory.Pseudofunctor.CoGrothendieck.comp_const`), and
`StacksFrontier/CategoryTheory/FiberedCategory/PullbackPseudofunctor.lean` builds from `p` the
pullback pseudofunctor of Stacks 02XO, whose transition functor along `f` is the chosen cartesian
pullback `f*`. This file proves that the two agree: under that identification the transition
functor `F f` *is* `f*`.

This is the strong naturality constraint of the comparison between `F` and the pullback
pseudofunctor of `∫ᶜ F`, i.e. of the round trip through the Grothendieck construction. It is the
step the library did not have: `CategoryTheory.Functor.isStack_pullbackPseudofunctor_iff` relates
`CategoryTheory.Functor.IsStack` of a fibred category to `CategoryTheory.Pseudofunctor.IsStack` of
*its* pullback pseudofunctor, and
`CategoryTheory.Pseudofunctor.StrongTrans.isStackFor_iff_of_app_isEquivalence` transports being a
stack along a fibrewise equivalence of pseudofunctors, so a strong transformation
`F ⟶ pullbackPseudofunctor (∫ᶜ F)` is what is needed to read a descent statement about `F` as one
about `∫ᶜ F`. What such a transformation still needs beyond the comparison proved here are its
three coherence axioms — `naturality_naturality`, `naturality_id` and `naturality_comp` of
`CategoryTheory.Pseudofunctor.StrongTrans` — which are *not* proved here.
`naturality_naturality` is automatic over a locally discrete base and is discharged by
`CategoryTheory.Pseudofunctor.catStrongTransOfIsLocallyDiscrete`, `naturality_id` is
`CategoryTheory.Pseudofunctor.CoGrothendieck.pullbackCmp_comp_pbMapId`, and `naturality_comp` is
`CategoryTheory.Pseudofunctor.CoGrothendieck.pullbackCmp_comp_pbMapComp`; the transformation
itself is `CategoryTheory.Pseudofunctor.CoGrothendieck.pullbackCmpStrongTrans`.

The comparison is indexed by a one-morphism of `LocallyDiscrete 𝒮ᵒᵖ` rather than by a morphism of
`𝒮`, because that is the index the coherence axioms of a strong transformation use: at an identity
they mention `F.map (𝟙 a)`, which is not the same term as `F.map (𝟙 S).op.toLoc`, and the
difference is invisible to a rewrite only at a transparency this development does not use.

## Main definitions

* `CategoryTheory.Pseudofunctor.CoGrothendieck.vertHom`: the vertical morphism of `∫ᶜ F` attached
  to a morphism of a fibre of `F`, written between structure literals.
* `CategoryTheory.Pseudofunctor.CoGrothendieck.fiberFunctor`: the identification of `F S` with the
  fibre of `∫ᶜ F` over `S`.
* `CategoryTheory.Pseudofunctor.CoGrothendieck.pullbackCmp`: the comparison isomorphism at an
  object.

## Main results

* `CategoryTheory.Pseudofunctor.CoGrothendieck.vertHom_comp_cartesianLift`: the tautological
  cartesian lifts of `∫ᶜ F` are natural in the fibre object.
* `CategoryTheory.Pseudofunctor.CoGrothendieck.cartesianLift_of_comp`: the tautological cartesian
  lifts of `∫ᶜ F` compose, modulo the composition constraint of `F`.
* `CategoryTheory.Pseudofunctor.CoGrothendieck.pullbackCmp_hom_fac`: the comparison carries the
  tautological cartesian lift to the chosen one.
* `CategoryTheory.Pseudofunctor.CoGrothendieck.pullbackCmpIso`: **the transition functor of `F`
  along `f` is the chosen pullback functor along `f`.**

## Implementation notes

Two spellings of the underlying object of an element of `CategoryTheory.Functor.Fiber` occur in the
library, `Fiber.fiberInclusion.obj z` and `z.1`, and the second is a `Subtype.val` applied to a
`Fiber`, hence type-correct only after the semireducible definition of `Fiber` is unfolded. Rather
than lowering the transparency at which the elaborator checks its motives, the four definitions
whose unfolding is needed are declared reducible at implicit transparency for this file.

For the same reason `vertHom` writes the two objects of `∫ᶜ F` as structure literals instead of as
values of `CategoryTheory.Pseudofunctor.CoGrothendieck.ι`: the base of a literal is read off by
projection, so the naturality equation of the cartesian lifts stays type-correct, whereas through
`ι` it does not.

## References

* [Stacks Project, Tag 003S](https://stacks.math.columbia.edu/tag/003S)
* [Stacks Project, Tag 02XO](https://stacks.math.columbia.edu/tag/02XO)
-/

@[expose] public noncomputable section

namespace CategoryTheory.Pseudofunctor.CoGrothendieck

open CategoryTheory CategoryTheory.Functor CategoryTheory.Functor.IsFibered Opposite
open scoped CategoryTheory.Bicategory

universe v₁ u₁ v₂ u₂

-- Load-bearing. `CategoryTheory.Functor.Fiber` is a subtype, and the `Fiber` API spells the
-- underlying object of a fibre element both as `Fiber.fiberInclusion.obj z` and as `z.1`; the
-- second reading is a `Subtype.val` applied to a `Fiber`, which is only type-correct once `Fiber`
-- has been unfolded. Declaring the definition reducible at implicit transparency is what lets
-- `rw` and instance synthesis see through it, so that the comparisons below need no transparency
-- option.
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.mk CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.IsFibered.fiberPullback

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] (F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂})

/-- The fibre of the Grothendieck construction over `S`, identified with `F S`. -/
abbrev fiberFunctor (S : 𝒮) : F.obj ⟨op S⟩ ⥤ (CoGrothendieck.forget F).Fiber S :=
  Fiber.inducedFunctor (CoGrothendieck.comp_const F S)

/-- The vertical morphism of `∫ᶜ F` attached to a morphism of a fibre of `F`, spelled out as a
morphism of `∫ᶜ F` between structure literals rather than through
`CategoryTheory.Pseudofunctor.CoGrothendieck.ι`.

Writing the two objects as literals is what makes the equations below type-correct at reducible
transparency: the base of a literal is read off by projection, whereas the base of `ι F S` only
reduces once the semireducible definition of `ι` is unfolded. -/
abbrev vertHom (S : 𝒮) {X Y : F.obj ⟨op S⟩} (α : X ⟶ Y) : (⟨S, X⟩ : ∫ᶜ F) ⟶ ⟨S, Y⟩ :=
  ⟨𝟙 S, α ≫ (F.mapId ⟨op S⟩).inv.toNatTrans.app Y⟩

/-- `CategoryTheory.Pseudofunctor.CoGrothendieck.ι` is the inclusion of a fibre by
`CategoryTheory.Pseudofunctor.CoGrothendieck.vertHom`. -/
lemma ι_map_eq_vertHom (S : 𝒮) {X Y : F.obj ⟨op S⟩} (α : X ⟶ Y) :
    (CoGrothendieck.ι F S).map α = vertHom F S α := rfl

/-- **The cartesian lifts of the Grothendieck construction are natural in the fibre object**, in
the literal spelling of `CategoryTheory.Pseudofunctor.CoGrothendieck.vertHom`. -/
lemma vertHom_comp_cartesianLift {V W : 𝒮} (f : W ⟶ V) {X Y : F.obj ⟨op V⟩} (α : X ⟶ Y) :
    vertHom F W ((F.map f.op.toLoc).toFunctor.map α) ≫ CoGrothendieck.cartesianLift Y f =
      CoGrothendieck.cartesianLift X f ≫ vertHom F V α := by
  refine CoGrothendieck.Hom.ext _ _ ?_ ?_
  · show 𝟙 W ≫ f = f ≫ 𝟙 V
    exact (Category.id_comp f).trans (Category.comp_id f).symm
  · simp only [CoGrothendieck.categoryStruct_comp_fiber, vertHom, op_id, Quiver.Hom.id_toLoc,
      Cat.Hom.id_toFunctor, Category.assoc, map_comp]
    rw [F.whiskerRight_mapId_inv_app, F.whiskerLeft_mapId_inv_app]
    simp only [categoryStruct_comp_base, op_comp, op_id, Quiver.Hom.comp_toLoc, Quiver.Hom.id_toLoc,
      Bicategory.Strict.rightUnitor_eqToIso, eqToIso.inv, PrelaxFunctor.map₂_eqToHom,
      Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app, map_id, Category.id_comp, Category.assoc,
      Cat.Hom.hom_inv_id_toNatTrans_app, Category.comp_id, Bicategory.Strict.leftUnitor_eqToIso]
    exact congrArg _ (eqToHom_trans _ _).symm

/-- **The tautological cartesian lifts of the Grothendieck construction compose**: the lift of
`g ≫ f` is the lift of `g` followed by the lift of `f`, corrected by the vertical morphism that
the identity constraint `CategoryTheory.Pseudofunctor.mapComp` of `F` attaches to the fibre
object.

The correcting `2`-morphism is taken as an argument `θ` together with its defining equation,
rather than written into the statement: the type of
`(F.mapComp f.op.toLoc g.op.toLoc).hom.toNatTrans.app X` spells its codomain through the
composition of `Cat`, `(F.map f.op.toLoc ≫ F.map g.op.toLoc).obj X`, whereas the domain of the
cartesian lift of `g` spells the same object by iterated application. The two are definitionally
equal, but the difference sits inside an *object* of `∫ᶜ F`, so a rewrite whose motive mentions it
is rejected at the transparency the tactic framework checks motives at. Handing the morphism in as
a variable makes all three factors match syntactically, and the instantiation `θ := …`, `hθ := rfl`
is discharged by the elaborator at the point of use. -/
lemma cartesianLift_of_comp {U V W : 𝒮} (f : V ⟶ U) (g : W ⟶ V) (X : F.obj ⟨op U⟩)
    (θ : (F.map (g ≫ f).op.toLoc).toFunctor.obj X ⟶
      (F.map g.op.toLoc).toFunctor.obj ((F.map f.op.toLoc).toFunctor.obj X))
    (hθ : θ = (F.mapComp f.op.toLoc g.op.toLoc).hom.toNatTrans.app X) :
    CoGrothendieck.cartesianLift X (g ≫ f) =
      vertHom F W θ ≫ CoGrothendieck.cartesianLift
          ((F.map f.op.toLoc).toFunctor.obj X) g ≫
        CoGrothendieck.cartesianLift X f := by
  refine CoGrothendieck.Hom.ext _ _ ?_ ?_
  · simp
  · subst hθ
    simp only [op_comp, Quiver.Hom.comp_toLoc, Cat.Hom.comp_toFunctor,
      CoGrothendieck.categoryStruct_comp_base, op_id, Quiver.Hom.id_toLoc,
      CoGrothendieck.categoryStruct_comp_fiber, Cat.Hom.id_toFunctor,
      CategoryTheory.Functor.map_id, Category.id_comp, F.mapComp_id_right_inv_app,
      CategoryTheory.Functor.id_obj, Bicategory.Strict.rightUnitor_eqToIso, eqToIso.inv,
      PrelaxFunctor.map₂_eqToHom, Cat.Hom₂.eqToHom_toNatTrans, CategoryTheory.eqToHom_app,
      Category.comp_id, eqToHom_naturality, Category.assoc, ← NatTrans.naturality_assoc,
      CategoryTheory.Functor.id_map, eqToHom_naturality_assoc,
      Cat.Hom.inv_hom_id_toNatTrans_app, Cat.Hom.hom_inv_id_toNatTrans_app_assoc]
    exact ((eqToHom_trans _ _).trans (eqToHom_refl _ _)).symm

/-! ### The comparison with the pullback pseudofunctor -/

/-- The comparison isomorphism at an object: the transition functor of `F` along `f`, read in the
fibre of `∫ᶜ F`, is the chosen pullback along `f`. Both objects carry a strongly cartesian
projection over `f` to the same object of `∫ᶜ F` — the tautological lift of the Grothendieck
construction and the chosen cartesian lift — so they are canonically isomorphic. -/
abbrev pullbackCmp {a b : LocallyDiscrete 𝒮ᵒᵖ} (φ : a ⟶ b) (X : F.obj a) :
    (fiberFunctor F b.as.unop).obj ((F.map φ).toFunctor.obj X) ≅
      (fiberPullback φ.as.unop).obj ((fiberFunctor F a.as.unop).obj X) :=
  letI := CoGrothendieck.isStronglyCartesian_homCartesianLift X φ.as.unop
  Functor.fiberIsoOfCartesian φ.as.unop (CoGrothendieck.cartesianLift X φ.as.unop)
    (IsPreFibered.pullbackMap ((fiberFunctor F a.as.unop).obj X).2 φ.as.unop)
    (Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian
      (CoGrothendieck.forget F) φ.as.unop (CoGrothendieck.cartesianLift X φ.as.unop))
    (IsPreFibered.pullbackMap.IsCartesian ((fiberFunctor F a.as.unop).obj X).2 φ.as.unop)

/-- The defining triangle of `CategoryTheory.Pseudofunctor.CoGrothendieck.pullbackCmp`: it carries
the tautological cartesian lift to the chosen one. -/
@[reassoc]
lemma pullbackCmp_hom_fac {a b : LocallyDiscrete 𝒮ᵒᵖ} (φ : a ⟶ b) (X : F.obj a) :
    Fiber.fiberInclusion.map (pullbackCmp F φ X).hom ≫
        IsPreFibered.pullbackMap ((fiberFunctor F a.as.unop).obj X).2 φ.as.unop =
      CoGrothendieck.cartesianLift X φ.as.unop :=
  letI := CoGrothendieck.isStronglyCartesian_homCartesianLift X φ.as.unop
  Functor.fiberIsoOfCartesian_hom_fac (p := CoGrothendieck.forget F) φ.as.unop _ _ _ _

/-- **The transition functor of `F` along `f` is the chosen pullback functor along `f`**, under the
identification of the fibres of `∫ᶜ F` with the values of `F`. This is the strong naturality
constraint of the comparison of `F` with the pullback pseudofunctor of `∫ᶜ F`. -/
def pullbackCmpIso {a b : LocallyDiscrete 𝒮ᵒᵖ} (φ : a ⟶ b) :
    (F.map φ).toFunctor ⋙ fiberFunctor F b.as.unop ≅
      fiberFunctor F a.as.unop ⋙ fiberPullback φ.as.unop :=
  NatIso.ofComponents (pullbackCmp F φ) (by
    intro X Y α
    refine Functor.fiber_hom_ext_of_cartesian φ.as.unop
      (IsPreFibered.pullbackMap ((fiberFunctor F a.as.unop).obj Y).2 φ.as.unop)
      (IsPreFibered.pullbackMap.IsCartesian
        ((fiberFunctor F a.as.unop).obj Y).2 φ.as.unop) _ _ ?_
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
      pullbackCmp_hom_fac]
    change Fiber.fiberInclusion.map
          ((fiberFunctor F b.as.unop).map ((F.map φ).toFunctor.map α)) ≫
        CoGrothendieck.cartesianLift Y φ.as.unop =
      Fiber.fiberInclusion.map (pullbackCmp F φ X).hom ≫
        Fiber.fiberInclusion.map
          (fiberPullbackMap φ.as.unop ((fiberFunctor F a.as.unop).map α)) ≫
          IsPreFibered.pullbackMap ((fiberFunctor F a.as.unop).obj Y).2 φ.as.unop
    rw [fiberPullbackMap_comm, ← Category.assoc, pullbackCmp_hom_fac]
    exact vertHom_comp_cartesianLift F φ.as.unop α)

end CategoryTheory.Pseudofunctor.CoGrothendieck

end
