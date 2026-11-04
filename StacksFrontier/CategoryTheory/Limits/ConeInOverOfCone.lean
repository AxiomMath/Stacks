module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Over

/-!
# A limit cone in an over category from a limit cone in the ambient category

Let `D : I ⥤ C` be a diagram, let `f i : D.obj i ⟶ S` be a family of morphisms compatible with
the transition morphisms of `D`, and let `c` be a cone over `D` equipped with a morphism
`m : c.pt ⟶ S` whose composites with the projections are the `f i`. Then `c` becomes a cone over
the lifted diagram `D.toOver S f _ : I ⥤ Over S`, and it is a limit cone there as soon as it is
one in `C` — provided `I` is nonempty, which is what makes the structure morphism of the vertex
of a competing cone recoverable from one of its projections.

The nonemptiness hypothesis is genuine: for `I` empty the limit in `Over S` is the terminal
object `𝟙 S`, not the terminal object of `C`.

## Main definitions

* `CategoryTheory.Limits.Cone.inOver`: the cone over `D.toOver S f _` attached to a cone over `D`
  and a morphism from its vertex to `S`.
* `CategoryTheory.Limits.Cone.ofOver`: the cone over `D` underlying a cone over `D.toOver S f _`.

## Main results

* `CategoryTheory.Limits.IsLimit.inOver`: `Cone.inOver` is a limit cone when the original cone
  is.

## Implementation notes

The lifted diagram is Mathlib's `CategoryTheory.Functor.toOver`, and
`CategoryTheory.Functor.toOver_comp_forget` identifies its composite with `Over.forget S` with
`D` *on the nose*, so a cone over the lifted diagram pushes forward to a cone over `D` with no
transport.
-/

@[expose] public section

namespace CategoryTheory.Limits

open CategoryTheory

universe w v u

variable {I : Type w} [Category.{v} I] {C : Type u} [Category.{v} C] {S : C}

/-- The cone in `Over S` attached to a cone `c` over `D` together with a morphism `m : c.pt ⟶ S`
whose composites with the projections of `c` are the chosen morphisms `f i : D.obj i ⟶ S`. -/
def Cone.inOver {D : I ⥤ C} (f : (i : I) → D.obj i ⟶ S)
    (hf : ∀ {i j : I} (g : i ⟶ j), D.map g ≫ f j = f i) (c : Cone D) (m : c.pt ⟶ S)
    (hm : ∀ i, c.π.app i ≫ f i = m) : Cone (D.toOver S f hf) where
  pt := Over.mk m
  π :=
    { app i := Over.homMk (c.π.app i) (hm i)
      naturality := fun i j g => by
        refine Over.OverMorphism.ext ?_
        change 𝟙 c.pt ≫ c.π.app j = c.π.app i ≫ D.map g
        rw [Category.id_comp, c.w g] }

/-- The vertex of `Cone.inOver f hf c m hm` is `Over.mk m`. -/
@[simp]
lemma Cone.inOver_pt {D : I ⥤ C} (f : (i : I) → D.obj i ⟶ S)
    (hf : ∀ {i j : I} (g : i ⟶ j), D.map g ≫ f j = f i) (c : Cone D) (m : c.pt ⟶ S)
    (hm : ∀ i, c.π.app i ≫ f i = m) :
    (Cone.inOver f hf c m hm).pt = Over.mk m :=
  rfl

/-- The underlying morphism of the `i`-th projection of `Cone.inOver f hf c m hm` is the `i`-th
projection of `c`. -/
@[simp]
lemma Cone.inOver_π_app_left {D : I ⥤ C} (f : (i : I) → D.obj i ⟶ S)
    (hf : ∀ {i j : I} (g : i ⟶ j), D.map g ≫ f j = f i) (c : Cone D) (m : c.pt ⟶ S)
    (hm : ∀ i, c.π.app i ≫ f i = m) (i : I) :
    ((Cone.inOver f hf c m hm).π.app i).left = c.π.app i :=
  rfl

/-- The cone over `D` obtained by forgetting the structure morphisms from a cone over the
diagram `D` lifted to `Over S`. -/
def Cone.ofOver {D : I ⥤ C} (f : (i : I) → D.obj i ⟶ S)
    (hf : ∀ {i j : I} (g : i ⟶ j), D.map g ≫ f j = f i) (K : Cone (D.toOver S f hf)) :
    Cone D where
  pt := K.pt.left
  π :=
    { app i := (K.π.app i).left
      naturality := fun i j g => congrArg Over.Hom.left (K.π.naturality g) }

/-- The vertex of `Cone.ofOver f hf K` is the underlying object `K.pt.left` of the vertex of
`K`. -/
@[simp]
lemma Cone.ofOver_pt {D : I ⥤ C} (f : (i : I) → D.obj i ⟶ S)
    (hf : ∀ {i j : I} (g : i ⟶ j), D.map g ≫ f j = f i) (K : Cone (D.toOver S f hf)) :
    (Cone.ofOver f hf K).pt = K.pt.left :=
  rfl

/-- The `i`-th projection of `Cone.ofOver f hf K` is the underlying morphism of the `i`-th
projection of `K`. -/
@[simp]
lemma Cone.ofOver_π_app {D : I ⥤ C} (f : (i : I) → D.obj i ⟶ S)
    (hf : ∀ {i j : I} (g : i ⟶ j), D.map g ≫ f j = f i) (K : Cone (D.toOver S f hf)) (i : I) :
    (Cone.ofOver f hf K).π.app i = (K.π.app i).left :=
  rfl

/-- A cone in `Over S` built from a limit cone in `C` is a limit cone, provided the index
category is nonempty. -/
def IsLimit.inOver [Nonempty I] {D : I ⥤ C} (f : (i : I) → D.obj i ⟶ S)
    (hf : ∀ {i j : I} (g : i ⟶ j), D.map g ≫ f j = f i) {c : Cone D} (hc : IsLimit c)
    (m : c.pt ⟶ S) (hm : ∀ i, c.π.app i ≫ f i = m) :
    IsLimit (Cone.inOver f hf c m hm) where
  lift K :=
    Over.homMk (hc.lift (Cone.ofOver f hf K))
      (by
        obtain ⟨i₀⟩ := ‹Nonempty I›
        change hc.lift (Cone.ofOver f hf K) ≫ m = K.pt.hom
        rw [← hm i₀, ← Category.assoc, hc.fac (Cone.ofOver f hf K) i₀]
        exact Over.w (K.π.app i₀))
  fac K i := Over.OverMorphism.ext (hc.fac (Cone.ofOver f hf K) i)
  uniq K n hn :=
    Over.OverMorphism.ext
      (hc.uniq (Cone.ofOver f hf K) n.left fun i => congrArg Over.Hom.left (hn i))

end CategoryTheory.Limits

end
