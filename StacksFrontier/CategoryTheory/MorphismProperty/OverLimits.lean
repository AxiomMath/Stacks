module

public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import StacksFrontier.CategoryTheory.Sites.Continuous.CoveringPullbacks
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite products and systems of objects in over-categories with a morphism property

A finite nonempty product in the over-category `Over V` is an iterated fibre product over `V`.
So if a property `P` of morphisms is stable under base change and composition and respects
isomorphisms, then the structure morphism to `V` of a finite nonempty product of objects of
`Over V` whose structure morphisms satisfy `P` again satisfies `P`.

## Main definitions

* `CategoryTheory.MorphismProperty.Over.systemOver`: a system of objects of `T` mapping to an
  object `U₀` of `P.Over ⊤ X` by morphisms with property `P`, as a system in `P.Over ⊤ X`; with
  its maps `CategoryTheory.MorphismProperty.Over.systemOverπ` to `U₀` and the cone
  `CategoryTheory.MorphismProperty.Over.systemOverCone` from an object over `U₀`.

## Main results

* `CategoryTheory.MorphismProperty.prop_hom_pt_of_isLimit_fan`: the structure morphism of the
  vertex of a limit fan over a finite nonempty family in `Over V` has every property of the
  structure morphisms of the family which is stable under base change and composition.

## Implementation notes

The proof is by induction on the length of the family: a limit fan over `Fin (n + 2)` is
compared, by uniqueness of limits, with the fan obtained from a product of the last `n + 1`
objects and a pullback, `CategoryTheory.Limits.extendFanIsLimit`.  The products used along the
way exist as soon as the ambient category has pullbacks, by
`Stacks.Sites.hasProduct_over_fin`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.MorphismProperty

section FiniteProducts

variable {C : Type u} [Category.{v} C] [HasPullbacks C] (P : MorphismProperty C)
  [P.IsStableUnderBaseChange] [P.IsStableUnderComposition] [P.RespectsIso]

omit [HasPullbacks C] [P.IsStableUnderBaseChange] [P.IsStableUnderComposition] in
/-- The structure morphism of an object of `Over V` isomorphic to one with property `P` has
property `P`. -/
lemma prop_hom_of_iso {V : C} {A A' : CategoryTheory.Over V} (e : A ≅ A') (h : P A'.hom) :
    P A.hom := by
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((CategoryTheory.Over.forget V).map e.hom))
  rwa [← CategoryTheory.Over.w e.hom, P.cancel_left_of_respectsIso]

/-- **Finite products in over-categories.** Let `P` be a property of morphisms which is stable
under base change and composition.  The structure morphism of the vertex of a limit fan over a
finite nonempty family in `Over V` whose structure morphisms all have `P` has `P`. -/
@[sga "3 IV 3.4.1" "partial"]
theorem prop_hom_pt_of_isLimit_fan {V : C} :
    ∀ {n : ℕ} {Y : Fin (n + 1) → CategoryTheory.Over V} {c : Fan Y}, IsLimit c →
      (∀ a, P (Y a).hom) →
      P c.pt.hom := by
  intro n
  induction n with
  | zero =>
    intro Y c hc hY
    have : Unique (Fin (0 + 1)) := inferInstanceAs (Unique (Fin 1))
    have : HasProduct Y := hasProduct_unique Y
    exact P.prop_hom_of_iso
      (hc.conePointUniqueUpToIso (limit.isLimit _) ≪≫ productUniqueIso Y) (hY _)
  | succ n ih =>
    intro Y c hc hY
    have : HasProduct (fun i : Fin (n + 1) ↦ Y i.succ) :=
      Stacks.Sites.hasProduct_over_fin n _ fun _ _ _ ↦ inferInstance
    let c₂ : BinaryFan (Y 0) (Fan.mk (∏ᶜ fun i : Fin (n + 1) ↦ Y i.succ)
        (Pi.π fun i : Fin (n + 1) ↦ Y i.succ)).pt :=
      pullbackConeEquivBinaryFan.functor.obj
        (pullback.cone (Y 0).hom (∏ᶜ fun i : Fin (n + 1) ↦ Y i.succ).hom)
    have hc₂ : IsLimit c₂ := (pullback.isLimit _ _).pullbackConeEquivBinaryFanFunctor
    have hpt : P c₂.pt.hom := by
      show P (pullback.fst (Y 0).hom (∏ᶜ fun i : Fin (n + 1) ↦ Y i.succ).hom ≫ (Y 0).hom)
      rw [pullback.condition]
      exact P.comp_mem _ _ (P.pullback_snd _ _ (hY 0))
        (ih (productIsProduct _) fun a ↦ hY a.succ)
    exact P.prop_hom_of_iso
      (hc.conePointUniqueUpToIso (extendFanIsLimit Y (productIsProduct _) hc₂)) hpt

end FiniteProducts

namespace Over

variable {T : Type u} [Category.{v} T] (P : MorphismProperty T) [P.IsStableUnderComposition]
  {X : T} (U₀ : MorphismProperty.Over P ⊤ X) {A : Type*} [Category A] (D : A ⥤ T)
  (d : D ⟶ (Functor.const A).obj U₀.left) (hd : ∀ a, P (d.app a))

/-- A system of objects of `T` over the underlying object of `U₀ : P.Over ⊤ X`, whose structure
morphisms to `U₀` have property `P`, as a system of objects of `P.Over ⊤ X`. -/
def systemOver : A ⥤ MorphismProperty.Over P ⊤ X where
  obj a := MorphismProperty.Over.mk ⊤ (d.app a ≫ U₀.hom) (P.comp_mem _ _ (hd a) U₀.prop)
  map {a b} g := MorphismProperty.Over.homMk (D.map g) (by
    change D.map g ≫ d.app b ≫ U₀.hom = d.app a ≫ U₀.hom
    have := d.naturality g
    dsimp at this
    rw [reassoc_of% this]) trivial
  map_id a := MorphismProperty.Over.Hom.ext (D.map_id a)
  map_comp f g := MorphismProperty.Over.Hom.ext (D.map_comp f g)

/-- The object of `T` underlying `(systemOver P U₀ D d hd).obj a` is `D.obj a`. -/
lemma systemOver_obj_left (a : A) : ((systemOver P U₀ D d hd).obj a).left = D.obj a := rfl

/-- The morphism of `T` underlying `(systemOver P U₀ D d hd).map g` is `D.map g`. -/
lemma systemOver_map_left {a b : A} (g : a ⟶ b) :
    ((systemOver P U₀ D d hd).map g).left = D.map g := rfl

/-- The maps from `CategoryTheory.MorphismProperty.Over.systemOver` to `U₀`. -/
def systemOverπ : systemOver P U₀ D d hd ⟶ (Functor.const A).obj U₀ where
  app a := MorphismProperty.Over.homMk (d.app a) rfl trivial
  naturality {a b} g := MorphismProperty.Over.Hom.ext (by
    change D.map g ≫ d.app b = d.app a ≫ 𝟙 _
    simp)

/-- The morphism of `T` underlying `(systemOverπ P U₀ D d hd).app a` is `d.app a`. -/
lemma systemOverπ_app_left (a : A) : ((systemOverπ P U₀ D d hd).app a).left = d.app a := rfl

/-- The cone over `CategoryTheory.MorphismProperty.Over.systemOver` with vertex an object `V` of
`P.Over ⊤ X` over `U₀`, given by maps `V ⟶ D a` compatible with the structure morphisms. -/
def systemOverCone (V : MorphismProperty.Over P ⊤ X) (g : V ⟶ U₀)
    (p : (Functor.const A).obj V.left ⟶ D) (hp : ∀ a, p.app a ≫ d.app a = g.left) :
    Cone (systemOver P U₀ D d hd) where
  pt := V
  π :=
    { app a := MorphismProperty.Over.homMk (p.app a) (by
        change p.app a ≫ d.app a ≫ U₀.hom = V.hom
        rw [reassoc_of% (hp a)]
        exact MorphismProperty.Over.w g) trivial
      naturality {a b} f := MorphismProperty.Over.Hom.ext (by
        change 𝟙 _ ≫ p.app b = p.app a ≫ D.map f
        simpa using p.naturality f) }

/-- The morphism of `T` underlying the leg at `a` of `systemOverCone P U₀ D d hd V g p hp` is
`p.app a`. -/
lemma systemOverCone_π_app_left (V : MorphismProperty.Over P ⊤ X) (g : V ⟶ U₀)
    (p : (Functor.const A).obj V.left ⟶ D) (hp : ∀ a, p.app a ≫ d.app a = g.left) (a : A) :
    ((systemOverCone P U₀ D d hd V g p hp).π.app a).left = p.app a := rfl

/-- The image of `CategoryTheory.MorphismProperty.Over.systemOverCone` in `T` is the given cone,
so it is a limit as soon as that cone is. -/
def isLimitMapConeSystemOverCone (V : MorphismProperty.Over P ⊤ X) (g : V ⟶ U₀)
    (p : (Functor.const A).obj V.left ⟶ D) (hp : ∀ a, p.app a ≫ d.app a = g.left)
    (hc : IsLimit (Cone.mk V.left p)) :
    IsLimit ((MorphismProperty.Over.forget P ⊤ X ⋙ CategoryTheory.Over.forget X).mapCone
      (systemOverCone P U₀ D d hd V g p hp)) :=
  hc

end Over

end CategoryTheory.MorphismProperty
