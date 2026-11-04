module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi
import StacksCore.Tactic.EgaSgaAttribute

/-!
# 2-morphisms of topoi

A *2-morphism* from a morphism of topoi `f : Sh(C) ⟶ Sh(D)` to another `g : Sh(C) ⟶ Sh(D)` is a
transformation of functors `t : f_* ⟶ g_*`. Because `f⁻¹ ⊣ f_*` and `g⁻¹ ⊣ g_*`, such a `t` is
the same datum as a transformation `g⁻¹ ⟶ f⁻¹`, going the other way; the latter is the unique
transformation for which the square identifying `Mor(𝒢, f_*ℱ)` with `Mor(f⁻¹𝒢, ℱ)` and
`Mor(𝒢, g_*ℱ)` with `Mor(g⁻¹𝒢, ℱ)` commutes.

2-morphisms compose vertically, by composing transformations of functors, and horizontally:
the horizontal composition `s ⋆ t` of `t : f_* ⟶ g_*` and `s : f'_* ⟶ g'_*` admits the two
descriptions `f'_*f_*ℱ ⟶ f'_*g_*ℱ ⟶ g'_*g_*ℱ` and `f'_*f_*ℱ ⟶ g'_*f_*ℱ ⟶ g'_*g_*ℱ`, and these
agree. The strict 2-category identities hold for these operations; they are recorded here as
theorems about the operations rather than as a bicategory structure, since set-theoretic
constraints (Stacks 00XB) prevent the formation of a 2-category of all topoi.

## Main definitions

* `TwoMorphismOfTopoi`: a 2-morphism between two morphisms of topoi `f, g : E → F` is a
  transformation of functors `f_* ⟶ g_*`.
* `TwoMorphismOfTopoi.id`: the identity 2-morphism.
* `TwoMorphismOfTopoi.inverseImage`: the induced transformation `g⁻¹ ⟶ f⁻¹`.
* `TwoMorphismOfTopoi.vcomp`: vertical composition.
* `TwoMorphismOfTopoi.hcomp`: horizontal composition `s ⋆ t`.
* `TwoMorphismOfTopoi.hcompInner` and `TwoMorphismOfTopoi.hcompOuter`: the two descriptions of
  the horizontal composition.

## Main results

* `TwoMorphismOfTopoi.homEquiv_symm_comp`: the adjunction square characterising the induced
  transformation `g⁻¹ ⟶ f⁻¹`, and `TwoMorphismOfTopoi.eq_inverseImage`: it is the only
  transformation satisfying it.
* `TwoMorphismOfTopoi.hcompInner_eq_hcompOuter`: the two descriptions of the horizontal
  composition `s ⋆ t` agree.
* `TwoMorphismOfTopoi.vcomp_assoc`, `.id_vcomp`, `.vcomp_id` and
  `TwoMorphismOfTopoi.hcomp_vcomp`: associativity and unitality of vertical composition, and the
  interchange law relating the two compositions.
-/

@[expose] public section

open CategoryTheory

universe v u v' u' v'' u''

/-- A *2-morphism* from a morphism of topoi `f : E → F` to a morphism of topoi `g : E → F` is a
transformation of functors `t : f_* ⟶ g_*`. -/
@[stacks 04IA "a 2-morphism f ⇒ g of morphisms of topoi is a transformation f_* ⟶ g_*",
  sga "4 IV 3.2",
  sga "4 IV 3.3.2" "2-arrows"]
def TwoMorphismOfTopoi {E : Type u} [Category.{v} E] {F : Type u'} [Category.{v'} F]
    (f g : MorphismOfTopoi E F) : Type _ :=
  f.pushforward ⟶ g.pushforward

namespace TwoMorphismOfTopoi

attribute [local implicit_reducible] TwoMorphismOfTopoi MorphismOfTopoi.comp

variable {E : Type u} [Category.{v} E] {F : Type u'} [Category.{v'} F]
  {G : Type u''} [Category.{v''} G]

section Vertical

variable {f g h k : MorphismOfTopoi E F}

/-- Two 2-morphisms with the same components are equal. -/
@[ext]
theorem ext {t t' : TwoMorphismOfTopoi f g} (h : ∀ ℱ : E, t.app ℱ = t'.app ℱ) : t = t' :=
  NatTrans.ext (funext h)

/-- The identity 2-morphism of a morphism of topoi, the identity transformation of `f_*`. -/
def id (f : MorphismOfTopoi E F) : TwoMorphismOfTopoi f f :=
  𝟙 f.pushforward

/-- The component at `ℱ` of the identity 2-morphism of `f` is the identity of `f_*ℱ`. -/
@[simp]
theorem id_app (f : MorphismOfTopoi E F) (ℱ : E) : (id f).app ℱ = 𝟙 (f.pushforward.obj ℱ) :=
  rfl

/-- Vertical composition of 2-morphisms: the composition of the two transformations of direct
image functors. -/
def vcomp (t : TwoMorphismOfTopoi f g) (t' : TwoMorphismOfTopoi g h) : TwoMorphismOfTopoi f h :=
  t ≫ t'

/-- The component at `ℱ` of a vertical composition is the composite of the components. -/
@[simp]
theorem vcomp_app (t : TwoMorphismOfTopoi f g) (t' : TwoMorphismOfTopoi g h) (ℱ : E) :
    (t.vcomp t').app ℱ = t.app ℱ ≫ t'.app ℱ :=
  rfl

/-- Vertical composition is associative. -/
theorem vcomp_assoc (t : TwoMorphismOfTopoi f g) (t' : TwoMorphismOfTopoi g h)
    (t'' : TwoMorphismOfTopoi h k) : (t.vcomp t').vcomp t'' = t.vcomp (t'.vcomp t'') :=
  Category.assoc t t' t''

/-- The identity 2-morphism is a left unit for vertical composition. -/
theorem id_vcomp (t : TwoMorphismOfTopoi f g) : (id f).vcomp t = t :=
  Category.id_comp t

/-- The identity 2-morphism is a right unit for vertical composition. -/
theorem vcomp_id (t : TwoMorphismOfTopoi f g) : t.vcomp (id g) = t :=
  Category.comp_id t

end Vertical

section InverseImage

variable {f g h : MorphismOfTopoi E F}

/-- The transformation `g⁻¹ ⟶ f⁻¹` of inverse image functors induced by a 2-morphism
`t : f_* ⟶ g_*` through the adjunctions `f⁻¹ ⊣ f_*` and `g⁻¹ ⊣ g_*`. Note that it goes the other
way. -/
def inverseImage (t : TwoMorphismOfTopoi f g) : g.inverseImage ⟶ f.inverseImage :=
  (conjugateEquiv f.adj g.adj).symm t

/-- The adjunction square characterising the induced transformation `g⁻¹ ⟶ f⁻¹`: composing with
`t` on `Mor(𝒢, f_*ℱ) = Mor(f⁻¹𝒢, ℱ)` is composing with `t` on `Mor(g⁻¹𝒢, ℱ)`. -/
theorem homEquiv_symm_comp (t : TwoMorphismOfTopoi f g) (𝒢 : F) (ℱ : E)
    (α : 𝒢 ⟶ f.pushforward.obj ℱ) :
    (g.adj.homEquiv 𝒢 ℱ).symm (α ≫ t.app ℱ) =
      t.inverseImage.app 𝒢 ≫ (f.adj.homEquiv 𝒢 ℱ).symm α := by
  have key : g.inverseImage.map (t.app ℱ) ≫ g.adj.counit.app ℱ =
      t.inverseImage.app (f.pushforward.obj ℱ) ≫ f.adj.counit.app ℱ :=
    conjugateEquiv_counit_symm f.adj g.adj t ℱ
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    key, ← Category.assoc, t.inverseImage.naturality α, Category.assoc]

/-- The induced transformation `g⁻¹ ⟶ f⁻¹` is the unique one making the adjunction square of
`TwoMorphismOfTopoi.homEquiv_symm_comp` commute. -/
theorem eq_inverseImage (t : TwoMorphismOfTopoi f g) (s : g.inverseImage ⟶ f.inverseImage)
    (hs : ∀ (𝒢 : F) (ℱ : E) (α : 𝒢 ⟶ f.pushforward.obj ℱ),
      (g.adj.homEquiv 𝒢 ℱ).symm (α ≫ t.app ℱ) = s.app 𝒢 ≫ (f.adj.homEquiv 𝒢 ℱ).symm α) :
    s = t.inverseImage := by
  ext 𝒢
  have h1 := hs 𝒢 (f.inverseImage.obj 𝒢) (f.adj.unit.app 𝒢)
  rw [homEquiv_symm_comp t 𝒢 (f.inverseImage.obj 𝒢) (f.adj.unit.app 𝒢)] at h1
  simpa using h1.symm

/-- The identity 2-morphism induces the identity transformation of inverse image functors. -/
theorem inverseImage_id (f : MorphismOfTopoi E F) :
    (id f).inverseImage = 𝟙 f.inverseImage :=
  conjugateEquiv_symm_id f.adj

/-- A vertical composition induces the composition of the two induced transformations of inverse
image functors, in the reverse order. -/
theorem inverseImage_vcomp (t : TwoMorphismOfTopoi f g) (t' : TwoMorphismOfTopoi g h) :
    (t.vcomp t').inverseImage = t'.inverseImage ≫ t.inverseImage :=
  (conjugateEquiv_symm_comp f.adj g.adj h.adj t t').symm

end InverseImage

section Horizontal

variable {f g h : MorphismOfTopoi E F} {f' g' h' : MorphismOfTopoi F G}

/-- The first description of the horizontal composition of `t : f_* ⟶ g_*` and `s : f'_* ⟶ g'_*`:
the composite `f'_*f_*ℱ ⟶ f'_*g_*ℱ ⟶ g'_*g_*ℱ`, which applies `t` first. -/
def hcompInner (s : TwoMorphismOfTopoi f' g') (t : TwoMorphismOfTopoi f g) :
    TwoMorphismOfTopoi (f'.comp f) (g'.comp g) :=
  Functor.whiskerRight t f'.pushforward ≫ Functor.whiskerLeft g.pushforward s

/-- The second description of the horizontal composition of `t : f_* ⟶ g_*` and
`s : f'_* ⟶ g'_*`: the composite `f'_*f_*ℱ ⟶ g'_*f_*ℱ ⟶ g'_*g_*ℱ`, which applies `s` first. -/
def hcompOuter (s : TwoMorphismOfTopoi f' g') (t : TwoMorphismOfTopoi f g) :
    TwoMorphismOfTopoi (f'.comp f) (g'.comp g) :=
  Functor.whiskerLeft f.pushforward s ≫ Functor.whiskerRight t g'.pushforward

/-- **The two descriptions of the horizontal composition agree**: applying `t` before `s` and
applying `s` before `t` give the same transformation `f'_*f_* ⟶ g'_*g_*`. -/
theorem hcompInner_eq_hcompOuter (s : TwoMorphismOfTopoi f' g') (t : TwoMorphismOfTopoi f g) :
    hcompInner s t = hcompOuter s t :=
  (Functor.whiskerLeft_comp_whiskerRight t s).symm

/-- Horizontal composition `s ⋆ t` of 2-morphisms of topoi: a 2-morphism from `f' ∘ f` to
`g' ∘ g`, given on `ℱ` by either of the two composites `f'_*f_*ℱ ⟶ g'_*g_*ℱ`. -/
@[stacks 04I9 "horizontal composition s ⋆ t of 2-morphisms of topoi, and its two descriptions"]
def hcomp (s : TwoMorphismOfTopoi f' g') (t : TwoMorphismOfTopoi f g) :
    TwoMorphismOfTopoi (f'.comp f) (g'.comp g) :=
  t ◫ s

/-- The horizontal composition is the composite `f'_*f_*ℱ ⟶ g'_*f_*ℱ ⟶ g'_*g_*ℱ`. -/
theorem hcomp_eq_hcompOuter (s : TwoMorphismOfTopoi f' g') (t : TwoMorphismOfTopoi f g) :
    s.hcomp t = hcompOuter s t :=
  Functor.NatTrans.hcomp_eq_whiskerLeft_comp_whiskerRight t s

/-- The horizontal composition is also the composite `f'_*f_*ℱ ⟶ f'_*g_*ℱ ⟶ g'_*g_*ℱ`. -/
theorem hcomp_eq_hcompInner (s : TwoMorphismOfTopoi f' g') (t : TwoMorphismOfTopoi f g) :
    s.hcomp t = hcompInner s t :=
  (hcomp_eq_hcompOuter s t).trans (hcompInner_eq_hcompOuter s t).symm

/-- The value of the horizontal composition at `ℱ`. -/
@[simp]
theorem hcomp_app (s : TwoMorphismOfTopoi f' g') (t : TwoMorphismOfTopoi f g) (ℱ : E) :
    (s.hcomp t).app ℱ =
      s.app (f.pushforward.obj ℱ) ≫ g'.pushforward.map (t.app ℱ) :=
  NatTrans.hcomp_app t s ℱ

/-- Horizontally composing with an identity 2-morphism on the source side whiskers by `f_*`. -/
theorem hcomp_id (s : TwoMorphismOfTopoi f' g') (f : MorphismOfTopoi E F) :
    s.hcomp (id f) = Functor.whiskerLeft f.pushforward s :=
  Functor.id_hcomp f.pushforward s

/-- Horizontally composing with an identity 2-morphism on the target side whiskers by `f'_*`. -/
theorem id_hcomp (f' : MorphismOfTopoi F G) (t : TwoMorphismOfTopoi f g) :
    (id f').hcomp t = Functor.whiskerRight t f'.pushforward :=
  Functor.hcomp_id t f'.pushforward

/-- Horizontal composition of identity 2-morphisms is the identity 2-morphism of the composite
morphism of topoi. -/
theorem hcomp_id_id (f : MorphismOfTopoi E F) (f' : MorphismOfTopoi F G) :
    (id f').hcomp (id f) = id (f'.comp f) :=
  (id_hcomp f' (id f)).trans (Functor.whiskerRight_id' f'.pushforward)

/-- The interchange law: horizontal composition of vertical composites is the vertical composite
of the horizontal compositions. -/
theorem hcomp_vcomp (s : TwoMorphismOfTopoi f' g') (s' : TwoMorphismOfTopoi g' h')
    (t : TwoMorphismOfTopoi f g) (t' : TwoMorphismOfTopoi g h) :
    (s.vcomp s').hcomp (t.vcomp t') = (s.hcomp t).vcomp (s'.hcomp t') :=
  NatTrans.exchange t t' s s'

end Horizontal

end TwoMorphismOfTopoi
