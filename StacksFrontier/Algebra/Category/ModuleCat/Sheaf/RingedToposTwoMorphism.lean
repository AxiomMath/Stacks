module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules
public import StacksFrontier.CategoryTheory.Sites.Topos.TwoMorphismOfTopoi
public import StacksFrontier.Deformation.ToposThickening.Trivialization.RingedToposComp
import StacksCore.Tactic.StacksAttribute

/-!
# 2-morphisms of ringed topoi

A 2-morphism between two morphisms of ringed topoi `f, g : (Sh(C), O_C) ⟶ (Sh(D), O_D)` is a
2-morphism `t : f_* ⟶ g_*` of the underlying morphisms of topoi which is compatible with the two
structure maps, in the sense that composing the structure map of `f` with `t` evaluated at the
source structure sheaf gives the structure map of `g`.

## Main definitions

* `Stacks.Sheaves.RingedToposModules.TwoMorphismOfRingedTopoi`: a compatible 2-morphism between
  two morphisms of ringed topoi.
* `Stacks.Sheaves.RingedToposModules.TwoMorphismOfRingedTopoi.id`: the identity 2-morphism.
* `AlgebraicGeometry.RingedToposHom.TwoMorphism` and
  `AlgebraicGeometry.RingedToposHom.TwoIso`: the same notion, and its invertible case, for the
  canonical two-field morphism of ringed topoi of Stacks 01D3 part (2).

## Main results

* `Stacks.Sheaves.RingedToposModules.TwoMorphismOfRingedTopoi.ext`: two 2-morphisms are equal as
  soon as their underlying natural transformations agree.
* `AlgebraicGeometry.RingedToposHom.TwoIso.refl`, `.symm`, `.trans`, `.whiskerLeft`,
  `.whiskerRight` and `.associator`: the calculus of 2-isomorphisms of ringed topoi.

## Implementation notes

**Two morphisms of ringed topoi, so two notions of 2-morphism.** The structure in the
`Stacks.Sheaves.RingedToposModules` namespace is the one for the four-field
`Stacks.Sheaves.RingedToposModules.RingedToposHom`, whose structure map lives at the `RingCat`
level and which carries both forms of it. The canonical two-field
`AlgebraicGeometry.RingedToposHom` of Stacks 01D3 part (2) is a different structure — see the
implementation notes of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/RingedToposHom.lean` for
why both are needed — and it is the one that *composes*
(`AlgebraicGeometry.RingedToposHom.comp`). Since Stacks 04IC's 2-morphisms are used precisely to
say that a diagram of composites commutes, the second half of this file gives Stacks 04IC for
that structure, with the compatibility equation written against
`AlgebraicGeometry.RingedTopos.forgetRing`, which forgets from `CommRingCat`, the level at which
the canonical structure map lives.

A 2-morphism of topoi is a transformation of the direct-image functors, and those act on sheaves
of *sets*; so the compatibility equation is written after forgetting the ring operations of the
two structure sheaves, which is composition with `forget RingCat`. This is not a weakening: the
underlying sheaf of sets of the direct image of a sheaf of rings is, on the nose, the direct
image of its underlying sheaf of sets (`pushforwardRingSheafIso` is `Iso.refl`), so the equation
is literally the source's equation `t ∘ f♯ = g♯` read on sections.

The morphism of ringed topoi is the library's `RingedToposHom`, which carries the structure map in
both its direct-image and its inverse-image form; only the direct-image form `fSharp` enters
here, as in the source.

## References

* [Stacks Project, Definition 18.2.2 (Tag 04IC)](https://stacks.math.columbia.edu/tag/04IC)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe v u w v' u' w'

namespace Stacks.Sheaves.RingedToposModules

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]

/-- A 2-morphism of ringed topoi: a natural transformation `f_* ⟶ g_*` of the underlying
direct-image functors commuting with the two maps from the target structure sheaf. -/
@[stacks 04IC]
structure TwoMorphismOfRingedTopoi (f g : RingedToposHom X Y) where
  /-- The underlying 2-morphism of the morphisms of topoi. -/
  t : TwoMorphismOfTopoi f.toToposHom g.toToposHom
  /-- Compatibility with the two maps from the target structure sheaf. -/
  commutes : (sheafCompose Y.J (forget RingCat.{w'})).map f.fSharp ≫
      t.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) =
    (sheafCompose Y.J (forget RingCat.{w'})).map g.fSharp

namespace TwoMorphismOfRingedTopoi

variable {f g : RingedToposHom X Y}

/-- A 2-morphism of ringed topoi is determined by its underlying natural transformation. -/
@[ext]
theorem ext {s t : TwoMorphismOfRingedTopoi f g} (h : s.t = t.t) : s = t := by
  cases s
  cases t
  cases h
  rfl

/-- The identity 2-morphism of a morphism of ringed topoi. -/
def id (f : RingedToposHom X Y) : TwoMorphismOfRingedTopoi f f where
  t := 𝟙 _
  commutes := by
    change (sheafCompose Y.J (forget RingCat.{w'})).map f.fSharp ≫ 𝟙 _ =
      (sheafCompose Y.J (forget RingCat.{w'})).map f.fSharp
    exact Category.comp_id _

/-- The underlying 2-morphism of topoi of the identity 2-morphism of `f` is the identity. -/
@[simp]
theorem id_t (f : RingedToposHom X Y) : (id f).t = 𝟙 f.toToposHom.pushforward := rfl

end TwoMorphismOfRingedTopoi

end Stacks.Sheaves.RingedToposModules

/-! ## 2-morphisms of the canonical morphisms of ringed topoi

The same definition for `AlgebraicGeometry.RingedToposHom`, together with the calculus of
2-isomorphisms — identity, inverse, vertical composition, the two whiskerings and the
associator — that a commutative diagram of ringed topoi is pasted out of. -/

namespace AlgebraicGeometry.RingedToposHom

open Stacks.Sheaves.ToposPushforward

universe v₁ u₁ w₁ v₂ u₂ w₂ v₃ u₃ w₃ v₄ u₄ w₄

variable {A : RingedTopos.{v₁, u₁, w₁}} {B : RingedTopos.{v₂, u₂, w₂}}
  [A.J.HasSheafCompose (forget RingCat.{w₁})]
  [B.J.HasSheafCompose (forget RingCat.{w₂})]
  [A.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w₂} RingCat.{w₂})]

/-- The structure map of a morphism of ringed topoi on underlying sheaves of sets, as a map
`O_D ⟶ f_*O_C` of sheaves of sets.

This is `B.forgetRing.map f.fSharp`, but with its target spelled as a value of the direct image
functor rather than as the direct image of a sheaf of commutative rings with its ring operations
forgotten. The two are the same object; the first spelling is the one the components of a
transformation of direct image functors have. -/
noncomputable def forgetFSharp (f : RingedToposHom A B) :
    B.forgetRing.obj B.O ⟶ f.toToposHom.pushforward.obj (A.forgetRing.obj A.O) :=
  B.forgetRing.map f.fSharp

/-- **Stacks 04IC for the canonical morphism of ringed topoi.** A 2-morphism between two
morphisms of ringed topoi `f, g : (Sh(C), O_C) ⟶ (Sh(D), O_D)` in the sense of Stacks 01D3
part (2): a transformation `t : f_* ⟶ g_*` of the underlying direct image functors — which is
exactly a `TwoMorphismOfTopoi` of the underlying morphisms of topoi — whose value at the
structure sheaf of the source carries the structure map of `f` to the structure map of `g`. -/
@[stacks 04IC "2-morphisms of the canonical two-field morphisms of ringed topoi of 01D3 part (2),
  which are the ones that compose"]
structure TwoMorphism (f g : RingedToposHom A B) where
  /-- The underlying 2-morphism of the morphisms of topoi. -/
  t : f.toToposHom.pushforward ⟶ g.toToposHom.pushforward
  /-- Compatibility with the two maps from the structure sheaf of the target. -/
  commutes : forgetFSharp f ≫ t.app (A.forgetRing.obj A.O) = forgetFSharp g

namespace TwoMorphism

variable {f g h : RingedToposHom A B}

/-- A 2-morphism of ringed topoi is determined by its underlying natural transformation. -/
@[ext]
theorem ext {s s' : TwoMorphism f g} (h : s.t = s'.t) : s = s' := by
  cases s
  cases s'
  cases h
  rfl

/-- The identity 2-morphism of a morphism of ringed topoi. -/
def id (f : RingedToposHom A B) : TwoMorphism f f where
  t := 𝟙 f.toToposHom.pushforward
  commutes := Category.comp_id _

/-- The underlying transformation of the identity 2-morphism is the identity of `f_*`. -/
@[simp]
theorem id_t (f : RingedToposHom A B) : (id f).t = 𝟙 f.toToposHom.pushforward := rfl

/-- Vertical composition of 2-morphisms of ringed topoi. -/
def vcomp (s : TwoMorphism f g) (s' : TwoMorphism g h) : TwoMorphism f h where
  t := s.t ≫ s'.t
  commutes := by
    rw [NatTrans.comp_app, ← Category.assoc, s.commutes, s'.commutes]

/-- The underlying transformation of a vertical composite is the composite of the underlying
transformations. -/
@[simp]
theorem vcomp_t (s : TwoMorphism f g) (s' : TwoMorphism g h) :
    (s.vcomp s').t = s.t ≫ s'.t :=
  rfl

end TwoMorphism

/-- A 2-*isomorphism* of morphisms of ringed topoi: an isomorphism of the underlying direct
image functors which is compatible with the two structure maps. Stacks says that a diagram of
ringed topoi *commutes* when its two composites are 2-isomorphic in this sense. -/
structure TwoIso (f g : RingedToposHom A B) where
  /-- The underlying isomorphism of the direct-image functors. -/
  e : f.toToposHom.pushforward ≅ g.toToposHom.pushforward
  /-- Compatibility with the two maps from the structure sheaf of the target. -/
  commutes : forgetFSharp f ≫ e.hom.app (A.forgetRing.obj A.O) = forgetFSharp g

namespace TwoIso

variable {f g h : RingedToposHom A B}

/-- The 2-morphism underlying a 2-isomorphism of ringed topoi. -/
def toTwoMorphism (s : TwoIso f g) : TwoMorphism f g where
  t := s.e.hom
  commutes := s.commutes

/-- The underlying transformation of the 2-morphism of a 2-isomorphism `s` is `s.e.hom`. -/
@[simp]
theorem toTwoMorphism_t (s : TwoIso f g) : s.toTwoMorphism.t = s.e.hom := rfl

/-- The 2-morphism underlying a 2-isomorphism of ringed topoi is invertible. -/
instance isIso_toTwoMorphism_t (s : TwoIso f g) : IsIso s.toTwoMorphism.t :=
  inferInstanceAs (IsIso s.e.hom)

/-- The identity 2-isomorphism. -/
def refl (f : RingedToposHom A B) : TwoIso f f where
  e := Iso.refl f.toToposHom.pushforward
  commutes := Category.comp_id _

/-- The inverse of a 2-isomorphism of ringed topoi. -/
def symm (s : TwoIso f g) : TwoIso g f where
  e := s.e.symm
  commutes := by
    rw [← s.commutes, Category.assoc, Iso.symm_hom, s.e.hom_inv_id_app, Category.comp_id]

/-- Vertical composition of 2-isomorphisms of ringed topoi. -/
def trans (s : TwoIso f g) (s' : TwoIso g h) : TwoIso f h where
  e := s.e ≪≫ s'.e
  commutes := by
    rw [Iso.trans_hom, NatTrans.comp_app, ← Category.assoc, s.commutes, s'.commutes]

end TwoIso

namespace TwoMorphism

variable {f g : RingedToposHom A B}

/-- A 2-morphism of ringed topoi whose underlying transformation of direct images is invertible
is a 2-isomorphism: the compatibility with the structure maps is the same equation. -/
noncomputable def toTwoIso (s : TwoMorphism f g) (hs : IsIso s.t) : TwoIso f g where
  e := @asIso _ _ _ _ s.t hs
  commutes := s.commutes

/-- The forward map of the 2-isomorphism built from an invertible 2-morphism `s` is `s.t`. -/
@[simp]
theorem toTwoIso_e_hom (s : TwoMorphism f g) (hs : IsIso s.t) :
    (s.toTwoIso hs).e.hom = s.t :=
  rfl

end TwoMorphism

/-! ### Whiskering and reassociation

The direct image of a composite of morphisms of ringed topoi is the composite of the direct
images, and its structure map is the composite of the structure maps (`forgetFSharp_comp`). Both
facts hold by definition, but only at default transparency, so the two composition operations are
made reducible locally; that is what lets the goals below be stated with the composite spelled
either way. -/

section Whiskering

variable {C : RingedTopos.{v₃, u₃, w₃}} {D : RingedTopos.{v₄, u₄, w₄}}
  [C.J.HasSheafCompose (forget RingCat.{w₃})]
  [D.J.HasSheafCompose (forget RingCat.{w₄})]
  [C.J.HasSheafCompose (forget₂ CommRingCat.{w₃} RingCat.{w₃})]
  [D.J.HasSheafCompose (forget₂ CommRingCat.{w₄} RingCat.{w₄})]

attribute [local implicit_reducible] AlgebraicGeometry.RingedToposHom.comp MorphismOfTopoi.comp

/-- The structure map of a composite of morphisms of ringed topoi, on underlying sheaves of
sets, is the composite of the two structure maps. This is `comp_fSharp_forget` with both sides
read through `forgetFSharp`. -/
theorem forgetFSharp_comp (g : RingedToposHom B C) (f : RingedToposHom A B) :
    forgetFSharp (g.comp f) =
      forgetFSharp g ≫ g.toToposHom.pushforward.map (forgetFSharp f) :=
  comp_fSharp_forget g f

namespace TwoIso

/-- Whiskering a 2-isomorphism on the right by a morphism of ringed topoi out of its target:
from `g ∘ f₁` to `g ∘ f₂`. -/
def whiskerRight {f₁ f₂ : RingedToposHom A B} (s : TwoIso f₁ f₂) (g : RingedToposHom B C) :
    TwoIso (g.comp f₁) (g.comp f₂) where
  e := Functor.isoWhiskerRight s.e g.toToposHom.pushforward
  commutes := by
    rw [forgetFSharp_comp g f₁, forgetFSharp_comp g f₂, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Category.assoc, ← Functor.map_comp, s.commutes]

/-- Whiskering a 2-isomorphism on the left by a morphism of ringed topoi into its source:
from `g₁ ∘ f` to `g₂ ∘ f`. -/
def whiskerLeft (f : RingedToposHom A B) {g₁ g₂ : RingedToposHom B C} (s : TwoIso g₁ g₂) :
    TwoIso (g₁.comp f) (g₂.comp f) where
  e := Functor.isoWhiskerLeft f.toToposHom.pushforward s.e
  commutes := by
    rw [forgetFSharp_comp g₁ f, forgetFSharp_comp g₂ f, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Category.assoc, s.e.hom.naturality, ← Category.assoc,
      s.commutes]

/-- Reassociating a composite of three morphisms of ringed topoi is a 2-isomorphism: the two
composites have the same direct image, and the two structure maps agree. -/
def associator (f : RingedToposHom A B) (g : RingedToposHom B C) (h : RingedToposHom C D) :
    TwoIso (h.comp (g.comp f)) ((h.comp g).comp f) where
  e := Functor.associator f.toToposHom.pushforward g.toToposHom.pushforward
    h.toToposHom.pushforward
  commutes := by
    have key : forgetFSharp (h.comp (g.comp f)) = forgetFSharp ((h.comp g).comp f) := by
      rw [forgetFSharp_comp h (g.comp f), forgetFSharp_comp g f,
        forgetFSharp_comp (h.comp g) f, forgetFSharp_comp h g, Functor.map_comp]
      exact (Category.assoc _ _ _).symm
    exact (Category.comp_id _).trans key

end TwoIso

namespace TwoMorphism

/-- Whiskering a 2-morphism on the right by a morphism of ringed topoi out of its target:
from `g ∘ f₁` to `g ∘ f₂`. This is `AlgebraicGeometry.RingedToposHom.TwoIso.whiskerRight`
without the invertibility. -/
def whiskerRight {f₁ f₂ : RingedToposHom A B} (s : TwoMorphism f₁ f₂) (g : RingedToposHom B C) :
    TwoMorphism (g.comp f₁) (g.comp f₂) where
  t := Functor.whiskerRight s.t g.toToposHom.pushforward
  commutes := by
    rw [forgetFSharp_comp g f₁, forgetFSharp_comp g f₂, Functor.whiskerRight_app,
      Category.assoc, ← Functor.map_comp, s.commutes]

/-- The underlying transformation of the right whiskering of `s` by `g` is the whiskering of
`s.t` by `g_*`. -/
@[simp]
theorem whiskerRight_t {f₁ f₂ : RingedToposHom A B} (s : TwoMorphism f₁ f₂)
    (g : RingedToposHom B C) :
    (s.whiskerRight g).t = Functor.whiskerRight s.t g.toToposHom.pushforward :=
  rfl

end TwoMorphism

end Whiskering

end AlgebraicGeometry.RingedToposHom

end
