module

import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.NormNum.Parity
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.Data.NNRat.Floor
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
import Mathlib.CategoryTheory.Monoidal.Mon

public import StacksCore.CategoryTheory.FiberedInGroupoids
public import StacksFrontier.CategoryTheory.DottedArrows.Defs

/-!
# Splitting a category of dotted arrows along a composition

Let `B` be a `(2,1)`-category (`Bicategory.IsLocallyGroupoid`) and consider a `2`-commutative
diagram

```
S --x--> X --f--> Y --g--> Z
|                          |
j                          ‖
|                          |
v                          v
T ----------z-------------> Z
```

with witness `γ : j ≫ z ⟶ x ≫ f ≫ g`. It has two associated categories of dotted arrows
(`CategoryTheory.DottedArrow`): the one `𝒟` of the outer rectangle, whose right edge is
`f ≫ g`, and the one `𝒟'` of the lower square, whose right edge is `g` and whose witness is `γ`
rebracketed by the associator. They are compared through an intermediate category `𝒟''`
(`DottedArrow.WithFactorization`): an object of `𝒟''` is an object `(a, α, β)` of `𝒟` together
with a factorization datum, namely a `1`-morphism `b : T ⟶ Y` and a `2`-morphism
`η : b ⟶ a ≫ f`. Composition of `1`-morphisms is diagrammatic throughout.

## Main definitions

* `CategoryTheory.CategoryIso`: an isomorphism of categories, a pair of strictly mutually
  inverse functors.
* `DottedArrow.WithFactorization`: the category `𝒟''`.
* `DottedArrow.compose`: the functor `𝒟'' ⥤ 𝒟'`, which forgets `a` and remembers `b`.
* `DottedArrow.toWithFactorization`: the functor `𝒟 ⥤ 𝒟''`, which takes `b := a ≫ f` and
  `η := 𝟙`.
* `DottedArrow.ofLowerUpper`: the dotted arrow of the outer rectangle assembled from dotted
  arrows of the lower square and of the upper square over it.

## Main results

* `DottedArrow.compose_isFiberedInGroupoids`: `compose` is fibred in groupoids.
* `DottedArrow.toWithFactorization_isEquivalence`: `toWithFactorization` is an equivalence of
  categories.
* `DottedArrow.fiber_categoryIso`: each fibre of `compose` is isomorphic, as a category, to the
  category of dotted arrows of the upper solid square over the corresponding bottom arrow.
* `DottedArrow.nonempty_of_lower_upper`: the outer rectangle has a dotted arrow if the lower
  square has one and every upper square it leaves has one.
-/

@[expose] public section


open CategoryTheory
open CategoryTheory.Bicategory

namespace CategoryTheory

universe w v u v₁ v₂ u₁ u₂

variable {B : Type u} [Bicategory.{w, v} B] [Bicategory.IsLocallyGroupoid B]

/-- An **isomorphism of categories** `C ≅ D`: a pair of functors that are strictly mutually
inverse, `functor ⋙ inverse = 𝟭 C` and `inverse ⋙ functor = 𝟭 D`; that is, an isomorphism in
`CategoryTheory.Cat`. -/
structure CategoryIso (C : Type u₁) (D : Type u₂) [Category.{v₁} C] [Category.{v₂} D] where
  /-- The forward functor. -/
  functor : C ⥤ D
  /-- The inverse functor. -/
  inverse : D ⥤ C
  /-- `functor` followed by `inverse` is the identity, on the nose. -/
  functor_inverse : functor ⋙ inverse = 𝟭 C
  /-- `inverse` followed by `functor` is the identity, on the nose. -/
  inverse_functor : inverse ⋙ functor = 𝟭 D

namespace DottedArrow

/-! ## The category `𝒟''` -/

/-- An object of `𝒟''`: a tuple `(a, α, β, b, η)` where `(a, α, β)` is an object of `𝒟` (the
dotted-arrow category of the outer rectangle, right edge `f ≫ g`), `b : T ⟶ Y` is a
`1`-morphism, and `η : b ⟶ (a ≫ f)` is a `2`-isomorphism (informally `η : b → f ∘ a`). -/
structure WithFactorization {S T X Y Z : B} (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y) (g : Y ⟶ Z)
    (z : T ⟶ Z) (γ : (j ≫ z) ⟶ (x ≫ f ≫ g)) where
  /-- The dotted 1-morphism `a : T ⟶ X`. -/
  a : T ⟶ X
  /-- `α : (j ≫ a) ⟶ x`. -/
  α : (j ≫ a) ⟶ x
  /-- `β : z ⟶ (a ≫ f ≫ g)`. -/
  β : z ⟶ (a ≫ f ≫ g)
  /-- The compatibility triangle for the outer rectangle. -/
  compat : γ = (j ◁ β) ≫ (α_ j a (f ≫ g)).inv ≫ (α ▷ (f ≫ g))
  /-- The auxiliary 1-morphism `b : T ⟶ Y`. -/
  b : T ⟶ Y
  /-- The 2-isomorphism `η : b ⟶ (a ≫ f)` (informally `η : b → f ∘ a`). -/
  η : b ⟶ (a ≫ f)

/-- A **morphism** of `𝒟''` is a pair `(θ₁, θ₂)`: `θ₁ : a ⟶ a'` a morphism in `𝒟`
(compatible with `α`'s and `β`'s), and `θ₂ : b ⟶ b'` with
`η' ∘ θ₂ = (id_f ⋆ θ₁) ∘ η`. -/
structure WithFactorization.Hom {S T X Y Z : B} {x : S ⟶ X} {j : S ⟶ T} {f : X ⟶ Y} {g : Y ⟶ Z}
    {z : T ⟶ Z} {γ : (j ≫ z) ⟶ (x ≫ f ≫ g)} (d d' : WithFactorization x j f g z γ) where
  /-- The `𝒟`-component `θ₁ : a ⟶ a'`. -/
  θ₁ : d.a ⟶ d'.a
  /-- Compatibility with the `α`'s. -/
  cond_α : d.α = (j ◁ θ₁) ≫ d'.α
  /-- Compatibility with the `β`'s. -/
  cond_β : d'.β = d.β ≫ (θ₁ ▷ (f ≫ g))
  /-- The auxiliary component `θ₂ : b ⟶ b'`. -/
  θ₂ : d.b ⟶ d'.b
  /-- Compatibility `η' ∘ θ₂ = (id_f ⋆ θ₁) ∘ η`. -/
  cond_η : θ₂ ≫ d'.η = d.η ≫ (θ₁ ▷ f)

namespace WithFactorization.Hom

variable {S T X Y Z : B} {x : S ⟶ X} {j : S ⟶ T} {f : X ⟶ Y} {g : Y ⟶ Z}
    {z : T ⟶ Z} {γ : (j ≫ z) ⟶ (x ≫ f ≫ g)}

omit [Bicategory.IsLocallyGroupoid B] in
/-- Two morphisms of `𝒟''` are equal if their `θ₁` and `θ₂` components are equal. -/
@[ext] theorem ext {d d' : WithFactorization x j f g z γ}
    {p q : WithFactorization.Hom d d'} (h1 : p.θ₁ = q.θ₁) (h2 : p.θ₂ = q.θ₂) : p = q := by
  cases p; cases q; simp_all

/-- The identity morphism of `𝒟''`. -/
@[implicit_reducible]
def id (d : WithFactorization x j f g z γ) : WithFactorization.Hom d d where
  θ₁ := 𝟙 d.a
  cond_α := by simp
  cond_β := by simp
  θ₂ := 𝟙 d.b
  cond_η := by simp

/-- Composition of morphisms of `𝒟''`. -/
@[implicit_reducible]
def comp {d d' d'' : WithFactorization x j f g z γ}
    (p : WithFactorization.Hom d d') (q : WithFactorization.Hom d' d'') :
    WithFactorization.Hom d d'' where
  θ₁ := p.θ₁ ≫ q.θ₁
  cond_α := by rw [p.cond_α, q.cond_α]; simp
  cond_β := by rw [q.cond_β, p.cond_β]; simp
  θ₂ := p.θ₂ ≫ q.θ₂
  cond_η := by
    rw [Category.assoc, q.cond_η, ← Category.assoc, p.cond_η, Category.assoc]; simp

end WithFactorization.Hom

/-- The category `𝒟''`. -/
instance instCategoryWithFactorization {S T X Y Z : B} {x : S ⟶ X} {j : S ⟶ T} {f : X ⟶ Y}
    {g : Y ⟶ Z} {z : T ⟶ Z} {γ : (j ≫ z) ⟶ (x ≫ f ≫ g)} :
    Category (WithFactorization x j f g z γ) where
  Hom := WithFactorization.Hom
  id := WithFactorization.Hom.id
  comp := WithFactorization.Hom.comp
  id_comp _ := WithFactorization.Hom.ext
    (by simp [WithFactorization.Hom.id, WithFactorization.Hom.comp])
    (by simp [WithFactorization.Hom.id, WithFactorization.Hom.comp])
  comp_id _ := WithFactorization.Hom.ext
    (by simp [WithFactorization.Hom.id, WithFactorization.Hom.comp])
    (by simp [WithFactorization.Hom.id, WithFactorization.Hom.comp])
  assoc _ _ _ := WithFactorization.Hom.ext (by simp [WithFactorization.Hom.comp])
    (by simp [WithFactorization.Hom.comp])

omit [Bicategory.IsLocallyGroupoid B] in
/-- The `θ₁` component of a composite in `𝒟''` is the composite of the `θ₁` components. -/
@[simp] theorem WithFactorization.Hom.comp_θ₁ {S T X Y Z : B} {x : S ⟶ X} {j : S ⟶ T} {f : X ⟶ Y}
    {g : Y ⟶ Z} {z : T ⟶ Z} {γ : (j ≫ z) ⟶ (x ≫ f ≫ g)} {d d' d'' : WithFactorization x j f g z γ}
    (p : d ⟶ d') (q : d' ⟶ d'') : (p ≫ q).θ₁ = p.θ₁ ≫ q.θ₁ := rfl

omit [Bicategory.IsLocallyGroupoid B] in
/-- The `θ₂` component of a composite in `𝒟''` is the composite of the `θ₂` components. -/
@[simp] theorem WithFactorization.Hom.comp_θ₂ {S T X Y Z : B} {x : S ⟶ X} {j : S ⟶ T} {f : X ⟶ Y}
    {g : Y ⟶ Z} {z : T ⟶ Z} {γ : (j ≫ z) ⟶ (x ≫ f ≫ g)} {d d' d'' : WithFactorization x j f g z γ}
    (p : d ⟶ d') (q : d' ⟶ d'') : (p ≫ q).θ₂ = p.θ₂ ≫ q.θ₂ := rfl

omit [Bicategory.IsLocallyGroupoid B] in
/-- The `θ₁` component of the identity of `d` in `𝒟''` is the identity of `d.a`. -/
@[simp] theorem WithFactorization.Hom.id_θ₁ {S T X Y Z : B} {x : S ⟶ X} {j : S ⟶ T} {f : X ⟶ Y}
    {g : Y ⟶ Z} {z : T ⟶ Z} {γ : (j ≫ z) ⟶ (x ≫ f ≫ g)} (d : WithFactorization x j f g z γ) :
    WithFactorization.Hom.θ₁ (𝟙 d) = 𝟙 d.a := rfl

omit [Bicategory.IsLocallyGroupoid B] in
/-- The `θ₂` component of the identity of `d` in `𝒟''` is the identity of `d.b`. -/
@[simp] theorem WithFactorization.Hom.id_θ₂ {S T X Y Z : B} {x : S ⟶ X} {j : S ⟶ T} {f : X ⟶ Y}
    {g : Y ⟶ Z} {z : T ⟶ Z} {γ : (j ≫ z) ⟶ (x ≫ f ≫ g)} (d : WithFactorization x j f g z γ) :
    WithFactorization.Hom.θ₂ (𝟙 d) = 𝟙 d.b := rfl

/-! ## The functor `compose : 𝒟'' ⥤ 𝒟'`

On objects, `(a, α, β, b, η) ↦ (b, (id_f ⋆ α) ∘ (η ⋆ id_j), (id_g ⋆ η⁻¹) ∘ β)`, and
on morphisms `(θ₁, θ₂) ↦ θ₂`. The target is the dotted-arrow category of the lower
square (right edge `g`, bottom `z`, witness `γ` rebracketed via the associator). -/

/-- The compatibility triangle satisfied by the dotted-arrow data for the lower square
obtained from an object `d` of `𝒟''`, with `1`-morphism `d.b`. -/
theorem compose_obj_compat {S T X Y Z : B} (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y)
    (g : Y ⟶ Z)
    (z : T ⟶ Z) (γ : (j ≫ z) ⟶ (x ≫ f ≫ g)) (d : WithFactorization x j f g z γ) :
    γ ≫ (α_ x f g).inv =
      (j ◁ (d.β ≫ (α_ d.a f g).inv ≫ (inv d.η ▷ g))) ≫ (α_ j d.b g).inv ≫
        (((j ◁ d.η) ≫ (α_ j d.a f).inv ≫ (d.α ▷ f)) ▷ g) := by
  conv_lhs => rw [d.compat]
  simp only [whiskerLeft_comp, comp_whiskerRight, Category.assoc]
  congr 1
  rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc, ← whiskerLeft_comp,
    IsIso.inv_hom_id, whiskerLeft_id, id_whiskerRight, Category.id_comp]
  bicategory

/-- The functor `compose : 𝒟'' ⥤ 𝒟'`. -/
@[implicit_reducible]
noncomputable def compose {S T X Y Z : B} (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y) (g : Y ⟶ Z)
    (z : T ⟶ Z) (γ : (j ≫ z) ⟶ (x ≫ f ≫ g)) :
    WithFactorization x j f g z γ ⥤ DottedArrow (x ≫ f) j g z (γ ≫ (α_ x f g).inv) where
  obj d :=
    { a := d.b
      α := (j ◁ d.η) ≫ (α_ j d.a f).inv ≫ (d.α ▷ f)
      β := d.β ≫ (α_ d.a f g).inv ≫ (inv d.η ▷ g)
      compat := compose_obj_compat x j f g z γ d }
  map {d d'} p :=
    { θ := p.θ₂
      cond_α := by
        dsimp only
        rw [p.cond_α, ← whiskerLeft_comp_assoc, p.cond_η]
        simp [whiskerLeft_comp, comp_whiskerRight]
      cond_β := by
        dsimp only
        rw [p.cond_β]
        simp only [Category.assoc]
        rw [associator_inv_naturality_left_assoc]
        have key : (p.θ₁ ▷ f) ≫ inv d'.η = inv d.η ≫ p.θ₂ := by
          rw [IsIso.eq_inv_comp, ← Category.assoc, ← p.cond_η]; simp
        rw [← comp_whiskerRight, ← comp_whiskerRight, key, comp_whiskerRight] }
  map_id _ := DottedArrow.Hom.ext (by rfl)
  map_comp _ _ := DottedArrow.Hom.ext (by rfl)

/-- The `1`-morphism of `compose.obj d` is `d.b`. -/
@[simp] theorem compose_obj_a {S T X Y Z : B} (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y)
    (g : Y ⟶ Z)
    (z : T ⟶ Z) (γ : (j ≫ z) ⟶ (x ≫ f ≫ g)) (d : WithFactorization x j f g z γ) :
    ((compose x j f g z γ).obj d).a = d.b := rfl

/-- `DottedArrow.compose` acts on a morphism by keeping its `θ₂` component, the `2`-morphism
between the factorization data `b`, and discarding `θ₁`. -/
theorem compose_map_θ {S T X Y Z : B} (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y) (g : Y ⟶ Z)
    (z : T ⟶ Z) (γ : (j ≫ z) ⟶ (x ≫ f ≫ g)) {d d' : WithFactorization x j f g z γ}
    (p : d ⟶ d') : ((compose x j f g z γ).map p).θ = p.θ₂ := rfl

/-! ## The equivalence `𝒟 ≌ 𝒟''`

The functor `toWithFactorization` is fully faithful and essentially surjective, hence an
equivalence. -/

/-- The functor `𝒟 ⥤ 𝒟''` given by `(a, α, β) ↦ (a, α, β, a ≫ f, 𝟙 (a ≫ f))` on objects and
`θ ↦ (θ, θ ▷ f)` on morphisms. -/
@[implicit_reducible]
noncomputable def toWithFactorization {S T X Y Z : B} (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y)
    (g : Y ⟶ Z) (z : T ⟶ Z) (γ : (j ≫ z) ⟶ (x ≫ f ≫ g)) :
    DottedArrow x j (f ≫ g) z γ ⥤ WithFactorization x j f g z γ where
  obj d :=
    { a := d.a
      α := d.α
      β := d.β
      compat := d.compat
      b := d.a ≫ f
      η := 𝟙 (d.a ≫ f) }
  map {d d'} p :=
    { θ₁ := p.θ
      cond_α := p.cond_α
      cond_β := p.cond_β
      θ₂ := p.θ ▷ f
      cond_η := by simp }
  map_id _ := WithFactorization.Hom.ext (by rfl) (by simp)
  map_comp _ _ := WithFactorization.Hom.ext (by rfl) (by simp)

omit [Bicategory.IsLocallyGroupoid B] in
/-- The `1`-morphism `a` of `toWithFactorization.obj d` is `d.a`. -/
@[simp] theorem toWithFactorization_obj_a {S T X Y Z : B} (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y)
    (g : Y ⟶ Z) (z : T ⟶ Z) (γ : (j ≫ z) ⟶ (x ≫ f ≫ g))
    (d : DottedArrow x j (f ≫ g) z γ) :
    ((toWithFactorization x j f g z γ).obj d).a = d.a := rfl

omit [Bicategory.IsLocallyGroupoid B] in
/-- The `2`-morphism `α` of `toWithFactorization.obj d` is `d.α`. -/
@[simp] theorem toWithFactorization_obj_α {S T X Y Z : B} (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y)
    (g : Y ⟶ Z) (z : T ⟶ Z) (γ : (j ≫ z) ⟶ (x ≫ f ≫ g))
    (d : DottedArrow x j (f ≫ g) z γ) :
    ((toWithFactorization x j f g z γ).obj d).α = d.α := rfl

omit [Bicategory.IsLocallyGroupoid B] in
/-- The `2`-morphism `β` of `toWithFactorization.obj d` is `d.β`. -/
@[simp] theorem toWithFactorization_obj_β {S T X Y Z : B} (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y)
    (g : Y ⟶ Z) (z : T ⟶ Z) (γ : (j ≫ z) ⟶ (x ≫ f ≫ g))
    (d : DottedArrow x j (f ≫ g) z γ) :
    ((toWithFactorization x j f g z γ).obj d).β = d.β := rfl

omit [Bicategory.IsLocallyGroupoid B] in
/-- The factorization `1`-morphism `b` of `toWithFactorization.obj d` is `d.a ≫ f`. -/
@[simp] theorem toWithFactorization_obj_b {S T X Y Z : B} (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y)
    (g : Y ⟶ Z) (z : T ⟶ Z) (γ : (j ≫ z) ⟶ (x ≫ f ≫ g))
    (d : DottedArrow x j (f ≫ g) z γ) :
    ((toWithFactorization x j f g z γ).obj d).b = d.a ≫ f := rfl

omit [Bicategory.IsLocallyGroupoid B] in
/-- The factorization `2`-morphism `η` of `toWithFactorization.obj d` is `𝟙 (d.a ≫ f)`. -/
@[simp] theorem toWithFactorization_obj_η {S T X Y Z : B} (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y)
    (g : Y ⟶ Z) (z : T ⟶ Z) (γ : (j ≫ z) ⟶ (x ≫ f ≫ g))
    (d : DottedArrow x j (f ≫ g) z γ) :
    ((toWithFactorization x j f g z γ).obj d).η = 𝟙 (d.a ≫ f) := rfl

omit [Bicategory.IsLocallyGroupoid B] in
/-- The `θ₁` component of `toWithFactorization.map p` is `p.θ`. -/
@[simp] theorem toWithFactorization_map_θ₁ {S T X Y Z : B} (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y)
    (g : Y ⟶ Z) (z : T ⟶ Z) (γ : (j ≫ z) ⟶ (x ≫ f ≫ g))
    {d d' : DottedArrow x j (f ≫ g) z γ} (p : d ⟶ d') :
    ((toWithFactorization x j f g z γ).map p).θ₁ = p.θ := rfl

omit [Bicategory.IsLocallyGroupoid B] in
/-- The `θ₂` component of `toWithFactorization.map p` is `p.θ ▷ f`. -/
@[simp] theorem toWithFactorization_map_θ₂ {S T X Y Z : B} (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y)
    (g : Y ⟶ Z) (z : T ⟶ Z) (γ : (j ≫ z) ⟶ (x ≫ f ≫ g))
    {d d' : DottedArrow x j (f ≫ g) z γ} (p : d ⟶ d') :
    ((toWithFactorization x j f g z γ).map p).θ₂ = p.θ ▷ f := rfl

/-- `toWithFactorization` is faithful. -/
instance toWithFactorization_faithful {S T X Y Z : B} (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y)
    (g : Y ⟶ Z) (z : T ⟶ Z) (γ : (j ≫ z) ⟶ (x ≫ f ≫ g)) :
    (toWithFactorization x j f g z γ).Faithful where
  map_injective {d d'} p q h := by
    apply DottedArrow.Hom.ext
    simpa using congrArg WithFactorization.Hom.θ₁ h

/-- `toWithFactorization` is full. -/
instance toWithFactorization_full {S T X Y Z : B} (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y)
    (g : Y ⟶ Z) (z : T ⟶ Z) (γ : (j ≫ z) ⟶ (x ≫ f ≫ g)) :
    (toWithFactorization x j f g z γ).Full where
  map_surjective {d d'} q := by
    refine ⟨{ θ := q.θ₁, cond_α := q.cond_α, cond_β := q.cond_β }, ?_⟩
    apply WithFactorization.Hom.ext
    · rfl
    · simpa [toWithFactorization] using q.cond_η.symm

/-- `toWithFactorization` is essentially surjective: every object `d` of `𝒟''` is
isomorphic to the image of `(d.a, d.α, d.β)`. -/
instance toWithFactorization_essSurj {S T X Y Z : B} (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y)
    (g : Y ⟶ Z) (z : T ⟶ Z) (γ : (j ≫ z) ⟶ (x ≫ f ≫ g)) :
    (toWithFactorization x j f g z γ).EssSurj where
  mem_essImage d := by
    refine ⟨{ a := d.a, α := d.α, β := d.β, compat := d.compat }, ?_⟩
    refine ⟨{
      hom := { θ₁ := 𝟙 d.a, cond_α := by simp, cond_β := by simp,
               θ₂ := inv d.η, cond_η := by simp }
      inv := { θ₁ := 𝟙 d.a, cond_α := by simp, cond_β := by simp,
               θ₂ := d.η, cond_η := by simp }
      hom_inv_id := by
        apply WithFactorization.Hom.ext <;>
          simp [WithFactorization.Hom.comp_θ₁, WithFactorization.Hom.comp_θ₂,
            WithFactorization.Hom.id_θ₁, WithFactorization.Hom.id_θ₂]
      inv_hom_id := by
        apply WithFactorization.Hom.ext <;>
          simp [WithFactorization.Hom.comp_θ₁, WithFactorization.Hom.comp_θ₂,
            WithFactorization.Hom.id_θ₁, WithFactorization.Hom.id_θ₂]
    }⟩

/-- `toWithFactorization` is an equivalence of categories `𝒟 ≌ 𝒟''`. -/
@[stacks 0H1B, stacks 0CLF]
instance toWithFactorization_isEquivalence {S T X Y Z : B} (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y)
    (g : Y ⟶ Z) (z : T ⟶ Z) (γ : (j ≫ z) ⟶ (x ≫ f ≫ g)) :
    (toWithFactorization x j f g z γ).IsEquivalence :=
  { }

/-! ## The fibre isomorphism

For each object `d'` of `𝒟'`, we construct an explicit on-the-nose isomorphism of
categories between the fibre `compose.Fiber d'` and the dotted-arrow category
`DottedArrow x j f d'.a d'.α` of the upper solid square (bottom arrow `d'.a`,
witness `d'.α`).

The forward functor sends a dotted arrow `(a, α, η)` of the upper square to the
object `(a, α, β', d'.a, η)` of `𝒟''`, where `β'` is chosen so that `compose` sends it
back to `d'` strictly on the nose. -/

/-- The underlying object of `𝒟''` produced by the fibre functor on `e`. -/
@[implicit_reducible]
noncomputable def toFiberObj {S T X Y Z : B} (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y)
    (g : Y ⟶ Z) (z : T ⟶ Z) (γ : (j ≫ z) ⟶ (x ≫ f ≫ g))
    (d' : DottedArrow (x ≫ f) j g z (γ ≫ (α_ x f g).inv))
    (e : DottedArrow x j f d'.a d'.α) : WithFactorization x j f g z γ where
  a := e.a
  α := e.α
  β := d'.β ≫ (e.β ▷ g) ≫ (α_ e.a f g).hom
  compat := by
    conv_lhs => rw [show γ = (γ ≫ (α_ x f g).inv) ≫ (α_ x f g).hom by simp, d'.compat, e.compat]
    simp only [whiskerLeft_comp, comp_whiskerRight, Category.assoc]
    bicategory
  b := d'.a
  η := e.β

/-- `compose` sends `toFiberObj e` to `d'`, on the nose. -/
theorem toFiber_over {S T X Y Z : B} (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y)
    (g : Y ⟶ Z) (z : T ⟶ Z) (γ : (j ≫ z) ⟶ (x ≫ f ≫ g))
    (d' : DottedArrow (x ≫ f) j g z (γ ≫ (α_ x f g).inv))
    (e : DottedArrow x j f d'.a d'.α) :
    (compose x j f g z γ).obj (toFiberObj x j f g z γ d' e) = d' := by
  refine DottedArrow.ext' rfl ?_ ?_
  · rw [eqToHom_refl, Category.id_comp]
    exact e.compat.symm
  · dsimp only [compose, toFiberObj]
    rw [eqToHom_refl, Category.comp_id]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← comp_whiskerRight, IsIso.hom_inv_id, id_whiskerRight, Category.comp_id]

/-- The forward fibre functor on morphisms: a morphism `θ : e ⟶ e'` of dotted
arrows of the upper square gives a morphism `(θ.θ, 𝟙 d'.a)` of `𝒟''` lying over
`𝟙 d'`. -/
@[implicit_reducible]
noncomputable def toFiberMap {S T X Y Z : B} (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y)
    (g : Y ⟶ Z) (z : T ⟶ Z) (γ : (j ≫ z) ⟶ (x ≫ f ≫ g))
    (d' : DottedArrow (x ≫ f) j g z (γ ≫ (α_ x f g).inv))
    {e e' : DottedArrow x j f d'.a d'.α} (θ : e ⟶ e') :
    toFiberObj x j f g z γ d' e ⟶ toFiberObj x j f g z γ d' e' where
  θ₁ := θ.θ
  cond_α := θ.cond_α
  cond_β := by
    dsimp only [toFiberObj]
    rw [θ.cond_β]
    simp only [comp_whiskerRight, Category.assoc]
    rw [associator_naturality_left]
  θ₂ := 𝟙 d'.a
  cond_η := by
    dsimp only [toFiberObj]
    rw [Category.id_comp, θ.cond_β]

/-- The forward functor `DottedArrow x j f d'.a d'.α ⥤ compose.Fiber d'`. -/
@[implicit_reducible]
noncomputable def toFiber {S T X Y Z : B} (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y)
    (g : Y ⟶ Z) (z : T ⟶ Z) (γ : (j ≫ z) ⟶ (x ≫ f ≫ g))
    (d' : DottedArrow (x ≫ f) j g z (γ ≫ (α_ x f g).inv)) :
    DottedArrow x j f d'.a d'.α ⥤ (compose x j f g z γ).Fiber d' where
  obj e := ⟨toFiberObj x j f g z γ d' e, toFiber_over x j f g z γ d' e⟩
  map {e e'} θ :=
    ⟨toFiberMap x j f g z γ d' θ, by
      apply IsHomLift.of_fac (compose x j f g z γ) (𝟙 d')
        (toFiberMap x j f g z γ d' θ)
        (toFiber_over x j f g z γ d' e) (toFiber_over x j f g z γ d' e')
      apply DottedArrow.Hom.ext
      rw [DottedArrow.Hom.comp_θ, DottedArrow.Hom.comp_θ,
        compose_map_θ,
        DottedArrow.Hom.eqToHom_θ, DottedArrow.Hom.eqToHom_θ]
      simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
      rfl⟩
  map_id e := Subtype.ext (WithFactorization.Hom.ext rfl rfl)
  map_comp {e e' e''} θ θ' :=
    Subtype.ext (WithFactorization.Hom.ext rfl (Category.id_comp (𝟙 d'.a)).symm)

namespace WithFactorization

omit [Bicategory.IsLocallyGroupoid B] in
/-- Extensionality for `𝒟''`, up to transport along equalities of the underlying
1-morphisms `a` and `b`. The `compat` field is a proposition and is ignored. -/
theorem ext' {S T X Y Z : B} {x : S ⟶ X} {j : S ⟶ T} {f : X ⟶ Y} {g : Y ⟶ Z}
    {z : T ⟶ Z} {γ : (j ≫ z) ⟶ (x ≫ f ≫ g)} {d d' : WithFactorization x j f g z γ}
    (ha : d.a = d'.a) (hb : d.b = d'.b)
    (hα : d.α = eqToHom (by rw [ha]) ≫ d'.α)
    (hβ : d.β = d'.β ≫ eqToHom (by rw [ha]))
    (hη : d.η = eqToHom (by rw [hb]) ≫ d'.η ≫ eqToHom (by rw [ha])) : d = d' := by
  cases d; cases d'
  cases ha; cases hb
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hα hβ hη
  subst hα hβ hη; rfl

end WithFactorization

/-- The `b`-field equality extracted from `compose.obj d = d'`: `d.b = d'.a`. -/
theorem fromFiber_b_eq {S T X Y Z : B} (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y)
    (g : Y ⟶ Z) (z : T ⟶ Z) (γ : (j ≫ z) ⟶ (x ≫ f ≫ g))
    (d' : DottedArrow (x ≫ f) j g z (γ ≫ (α_ x f g).inv))
    {d : WithFactorization x j f g z γ} (hd : (compose x j f g z γ).obj d = d') :
    d.b = d'.a :=
      (compose_obj_a x j f g z γ d).symm.trans (congrArg DottedArrow.a hd)

/-- The underlying upper-square dotted arrow produced by the inverse fibre functor
on a fibre object `⟨d, hd⟩`. -/
@[implicit_reducible]
noncomputable def fromFiberObj {S T X Y Z : B} (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y)
    (g : Y ⟶ Z) (z : T ⟶ Z) (γ : (j ≫ z) ⟶ (x ≫ f ≫ g))
    (d' : DottedArrow (x ≫ f) j g z (γ ≫ (α_ x f g).inv))
    (e : (compose x j f g z γ).Fiber d') : DottedArrow x j f d'.a d'.α where
  a := e.1.a
  α := e.1.α
  β := eqToHom (fromFiber_b_eq x j f g z γ d' e.2).symm ≫ e.1.η
  compat := by
    obtain ⟨d, hd⟩ := e
    simp only at *
    subst hd
    rw [whiskerLeft_comp, Category.assoc, whiskerLeft_eqToHom]
    simp only [compose_obj_a, eqToHom_refl, Category.id_comp]
    rfl

/-- A fibre morphism over `𝟙 d'` has its `b`-component `θ₂` essentially an
`eqToHom`. -/
theorem fromFiber_θ₂_eq {S T X Y Z : B} (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y)
    (g : Y ⟶ Z) (z : T ⟶ Z) (γ : (j ≫ z) ⟶ (x ≫ f ≫ g))
    (d' : DottedArrow (x ≫ f) j g z (γ ≫ (α_ x f g).inv))
    {e e' : (compose x j f g z γ).Fiber d'} (m : e ⟶ e') :
    m.1.θ₂ = eqToHom (fromFiber_b_eq x j f g z γ d' e.2)
        ≫ eqToHom (fromFiber_b_eq x j f g z γ d' e'.2).symm := by
  have hlift := m.2
  have hfac := IsHomLift.fac' (compose x j f g z γ) (𝟙 d') m.1
  have h := congrArg DottedArrow.Hom.θ hfac
  rw [compose_map_θ] at h
  rw [h]
  simp [DottedArrow.Hom.eqToHom_θ]

/-- The inverse fibre functor on morphisms. -/
@[implicit_reducible]
noncomputable def fromFiberMap {S T X Y Z : B} (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y)
    (g : Y ⟶ Z) (z : T ⟶ Z) (γ : (j ≫ z) ⟶ (x ≫ f ≫ g))
    (d' : DottedArrow (x ≫ f) j g z (γ ≫ (α_ x f g).inv))
    {e e' : (compose x j f g z γ).Fiber d'} (m : e ⟶ e') :
    fromFiberObj x j f g z γ d' e ⟶ fromFiberObj x j f g z γ d' e' where
  θ := m.1.θ₁
  cond_α := m.1.cond_α
  cond_β := by
    dsimp only [fromFiberObj]
    rw [Category.assoc, ← m.1.cond_η, fromFiber_θ₂_eq x j f g z γ d' m]
    simp

/-- The inverse functor `compose.Fiber d' ⥤ DottedArrow x j f d'.a d'.α`. -/
@[implicit_reducible]
noncomputable def fromFiber {S T X Y Z : B} (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y)
    (g : Y ⟶ Z) (z : T ⟶ Z) (γ : (j ≫ z) ⟶ (x ≫ f ≫ g))
    (d' : DottedArrow (x ≫ f) j g z (γ ≫ (α_ x f g).inv)) :
    (compose x j f g z γ).Fiber d' ⥤ DottedArrow x j f d'.a d'.α where
  obj e := fromFiberObj x j f g z γ d' e
  map {e e'} m := fromFiberMap x j f g z γ d' m
  map_id e := DottedArrow.Hom.ext (by rfl)
  map_comp {e e' e''} m m' := DottedArrow.Hom.ext (by rfl)

/-- Object round-trip: `fromFiber (toFiber e) = e`. -/
theorem fromFiber_toFiber_obj {S T X Y Z : B} (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y)
    (g : Y ⟶ Z) (z : T ⟶ Z) (γ : (j ≫ z) ⟶ (x ≫ f ≫ g))
    (d' : DottedArrow (x ≫ f) j g z (γ ≫ (α_ x f g).inv))
    (e : DottedArrow x j f d'.a d'.α) :
    (fromFiber x j f g z γ d').obj ((toFiber x j f g z γ d').obj e) = e := by
  refine DottedArrow.ext' rfl ?_ ?_
  · dsimp only [toFiberObj, fromFiberObj, toFiber, fromFiber]; rw [eqToHom_refl, Category.id_comp]
  · dsimp only [fromFiber, toFiber, fromFiberObj, toFiberObj]
    simp

/-- Object round-trip: `toFiber (fromFiber ⟨d, hd⟩) = ⟨d, hd⟩`. -/
theorem toFiber_fromFiber_obj {S T X Y Z : B} (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y)
    (g : Y ⟶ Z) (z : T ⟶ Z) (γ : (j ≫ z) ⟶ (x ≫ f ≫ g))
    (d' : DottedArrow (x ≫ f) j g z (γ ≫ (α_ x f g).inv))
    (e : (compose x j f g z γ).Fiber d') :
    (toFiber x j f g z γ d').obj ((fromFiber x j f g z γ d').obj e) = e := by
  apply Subtype.ext
  obtain ⟨d, hd⟩ := e
  refine WithFactorization.ext' rfl (fromFiber_b_eq x j f g z γ d' hd).symm ?_ ?_ ?_
  · dsimp only [toFiberObj, fromFiberObj, toFiber, fromFiber]
    rw [eqToHom_refl, Category.id_comp]
  · subst hd
    dsimp only [compose, toFiberObj, fromFiberObj, toFiber, fromFiber]
    simp [← comp_whiskerRight_assoc]
  · dsimp only [toFiberObj, fromFiberObj, toFiber, fromFiber]
    rw [eqToHom_refl, Category.comp_id]

omit [Bicategory.IsLocallyGroupoid B] in
/-- The underlying 2-morphism `θ₁` of an `eqToHom` between objects of `𝒟''`. -/
theorem WithFactorization.Hom.eqToHom_θ₁ {S T X Y Z : B} {x : S ⟶ X} {j : S ⟶ T} {f : X ⟶ Y}
    {g : Y ⟶ Z} {z : T ⟶ Z} {γ : (j ≫ z) ⟶ (x ≫ f ≫ g)} {d d' : WithFactorization x j f g z γ}
    (h : d = d') : (eqToHom h).θ₁ = eqToHom (by rw [h]) := by subst h; rfl

omit [Bicategory.IsLocallyGroupoid B] in
/-- The underlying 2-morphism `θ₂` of an `eqToHom` between objects of `𝒟''`. -/
theorem WithFactorization.Hom.eqToHom_θ₂ {S T X Y Z : B} {x : S ⟶ X} {j : S ⟶ T} {f : X ⟶ Y}
    {g : Y ⟶ Z} {z : T ⟶ Z} {γ : (j ≫ z) ⟶ (x ≫ f ≫ g)} {d d' : WithFactorization x j f g z γ}
    (h : d = d') : (eqToHom h).θ₂ = eqToHom (by rw [h]) := by subst h; rfl

/-- The underlying `𝒟''`-morphism of an `eqToHom` between fibre objects of `compose`. -/
theorem fiber_eqToHom_val {S T X Y Z : B} (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y)
    (g : Y ⟶ Z) (z : T ⟶ Z) (γ : (j ≫ z) ⟶ (x ≫ f ≫ g))
    (d' : DottedArrow (x ≫ f) j g z (γ ≫ (α_ x f g).inv))
    {e e' : (compose x j f g z γ).Fiber d'} (h : e = e') :
    (eqToHom h).1 = eqToHom (by rw [h]) := by subst h; rfl

/-- The fibre of `compose` over an object `d'` of `𝒟'` is isomorphic, as a category (a
`CategoryIso`, not merely an equivalence), to the category of dotted arrows of the upper solid
square, whose bottom arrow is `d'.a` and whose witness is `d'.α`. -/
@[stacks 0H1B, stacks 0CLF]
theorem fiber_categoryIso {S T X Y Z : B}
    (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y) (g : Y ⟶ Z) (z : T ⟶ Z)
    (γ : (j ≫ z) ⟶ (x ≫ f ≫ g))
    (d' : DottedArrow (x ≫ f) j g z (γ ≫ (α_ x f g).inv)) :
    Nonempty (CategoryIso ((compose x j f g z γ).Fiber d')
      (DottedArrow x j f d'.a d'.α)) :=
  ⟨{ functor := fromFiber x j f g z γ d'
     inverse := toFiber x j f g z γ d'
     functor_inverse := by
       refine CategoryTheory.Functor.ext
         (fun e => toFiber_fromFiber_obj x j f g z γ d' e) ?_
       intro e e' m
       apply Subtype.ext
       have hcomp : ((eqToHom (toFiber_fromFiber_obj x j f g z γ d' e)
               ≫ (𝟭 ((compose x j f g z γ).Fiber d')).map m
               ≫ eqToHom (toFiber_fromFiber_obj x j f g z γ d' e').symm) : _ ⟶ _).1
             = eqToHom (by rw [toFiber_fromFiber_obj x j f g z γ d' e])
               ≫ m.1 ≫ eqToHom (by rw [toFiber_fromFiber_obj x j f g z γ d' e']) := by
         rw [← fiber_eqToHom_val x j f g z γ d' (toFiber_fromFiber_obj x j f g z γ d' e),
           ← fiber_eqToHom_val x j f g z γ d' (toFiber_fromFiber_obj x j f g z γ d' e').symm]
         rfl
       apply WithFactorization.Hom.ext
       · show m.1.θ₁ = _
         rw [hcomp, WithFactorization.Hom.comp_θ₁, WithFactorization.Hom.comp_θ₁,
           WithFactorization.Hom.eqToHom_θ₁, WithFactorization.Hom.eqToHom_θ₁]
         simp
       · rw [hcomp, WithFactorization.Hom.comp_θ₂, WithFactorization.Hom.comp_θ₂,
           WithFactorization.Hom.eqToHom_θ₂, WithFactorization.Hom.eqToHom_θ₂,
           fromFiber_θ₂_eq x j f g z γ d' m]
         simp only [eqToHom_trans, eqToHom_refl]
         exact (eqToHom_refl d'.a rfl).symm
     inverse_functor := by
       refine CategoryTheory.Functor.ext
         (fun e => fromFiber_toFiber_obj x j f g z γ d' e) ?_
       intro e e' θ
       apply DottedArrow.Hom.ext
       rw [DottedArrow.Hom.comp_θ, DottedArrow.Hom.comp_θ,
           DottedArrow.Hom.eqToHom_θ, DottedArrow.Hom.eqToHom_θ]
       dsimp only [toFiberMap, fromFiberMap, toFiber, fromFiber]
       simp }⟩

/-- The `2`-morphism `α` of `compose.obj d` is `(j ◁ d.η) ≫ (α_ j d.a f).inv ≫ (d.α ▷ f)`. -/
@[simp] theorem compose_obj_α' {S T X Y Z : B} (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y)
    (g : Y ⟶ Z)
    (z : T ⟶ Z) (γ : (j ≫ z) ⟶ (x ≫ f ≫ g)) (d : WithFactorization x j f g z γ) :
    ((compose x j f g z γ).obj d).α = (j ◁ d.η) ≫ (α_ j d.a f).inv ≫ (d.α ▷ f) := rfl

/-- The `2`-morphism `β` of `compose.obj d` is `d.β ≫ (α_ d.a f g).inv ≫ (inv d.η ▷ g)`. -/
@[simp] theorem compose_obj_β' {S T X Y Z : B} (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y)
    (g : Y ⟶ Z)
    (z : T ⟶ Z) (γ : (j ≫ z) ⟶ (x ≫ f ≫ g)) (d : WithFactorization x j f g z γ) :
    ((compose x j f g z γ).obj d).β = d.β ≫ (α_ d.a f g).inv ≫ (inv d.η ▷ g) := rfl

/-- Transporting the `β`-datum of `V` along the factorization datum `ψ.θ ≫ u.η` recovers
`u.β`. -/
theorem compose_lift_β {S T X Y Z : B} (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y) (g : Y ⟶ Z)
    (z : T ⟶ Z) (γ : (j ≫ z) ⟶ (x ≫ f ≫ g))
    {V : DottedArrow (x ≫ f) j g z (γ ≫ (α_ x f g).inv)}
    {u : WithFactorization x j f g z γ} (ψ : V ⟶ (compose x j f g z γ).obj u) :
    V.β ≫ ((ψ.θ ≫ u.η) ▷ g) ≫ (α_ u.a f g).hom = u.β := by
  have hψβ := ψ.cond_β
  simp only [compose_obj_β'] at hψβ
  rw [comp_whiskerRight,
    show V.β ≫ (ψ.θ ▷ g ≫ u.η ▷ g) ≫ (α_ u.a f g).hom
        = (V.β ≫ ψ.θ ▷ g) ≫ (u.η ▷ g) ≫ (α_ u.a f g).hom by simp,
    ← hψβ]
  simp only [Category.assoc]
  rw [← Bicategory.comp_whiskerRight_assoc, IsIso.inv_hom_id, id_whiskerRight,
    Category.id_comp, Iso.inv_hom_id, Category.comp_id]

/-- **Lifting of morphisms along `compose`.** Let `u` be an object of `𝒟''` with
`compose.obj u = U`, and let `ψ : V ⟶ U` in `𝒟'`, so `ψ.θ : V.a ⟶ u.b`. Then `ψ` lifts:
the lift object is `v` with `v.a := u.a`, `v.α := u.α`, `v.b := V.a`, `v.η := ψ.θ ≫ u.η` and
`v.β := V.β ≫ ((ψ.θ ≫ u.η) ▷ g) ≫ (α_ u.a f g).hom`, and the lift morphism `φ : v ⟶ u` has
`θ₁ := 𝟙 u.a`, `θ₂ := ψ.θ`. Both `compose.obj v = V` and `compose.map φ = ψ` hold on the nose,
the latter up to the `eqToHom` casts recorded in the statement. -/
theorem compose_lift {S T X Y Z : B} (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y)
    (g : Y ⟶ Z) (z : T ⟶ Z) (γ : (j ≫ z) ⟶ (x ≫ f ≫ g))
    {U V : DottedArrow (x ≫ f) j g z (γ ≫ (α_ x f g).inv)} (ψ : V ⟶ U)
    (u : WithFactorization x j f g z γ) (hu : (compose x j f g z γ).obj u = U) :
    ∃ (v : WithFactorization x j f g z γ) (φ : v ⟶ u)
      (hv : (compose x j f g z γ).obj v = V),
      (compose x j f g z γ).map φ = eqToHom hv ≫ ψ ≫ eqToHom hu.symm :=
  by
  subst hu
  refine
    ⟨{ a := u.a
       α := u.α
       b := V.a
       η := ψ.θ ≫ u.η
       β := V.β ≫ ((ψ.θ ≫ u.η) ▷ g) ≫ (α_ u.a f g).hom
       compat := ?_ },
     { θ₁ := 𝟙 u.a
       θ₂ := ψ.θ
       cond_α := by simp
       cond_β := ?_
       cond_η := by simp }, ?_, ?_⟩
  · rw [compose_lift_β x j f g z γ ψ]
    exact u.compat
  · simp only [id_whiskerRight, Category.comp_id]
    exact (compose_lift_β x j f g z γ ψ).symm
  · refine DottedArrow.ext' (compose_obj_a ..) ?_ ?_
    · simp only [compose_obj_α', compose_obj_a, eqToHom_refl,
        Category.id_comp]
      rw [ψ.cond_α]; simp [whiskerLeft_comp]
    · simp only [compose_obj_β', compose_obj_a, eqToHom_refl, Category.comp_id, Category.assoc,
        Iso.hom_inv_id_assoc]
      rw [← Bicategory.comp_whiskerRight, IsIso.hom_inv_id, id_whiskerRight, Category.comp_id]
  · apply DottedArrow.Hom.ext
    rw [compose_map_θ, DottedArrow.Hom.comp_θ, DottedArrow.Hom.comp_θ, DottedArrow.Hom.eqToHom_θ,
      DottedArrow.Hom.eqToHom_θ]
    simp

/-- **Uniqueness of lifts along `compose`.** Given `φ : v ⟶ u`, `φ' : v' ⟶ u` in `𝒟''` and
`ψ : compose.obj v' ⟶ compose.obj v` with `ψ ≫ compose.map φ = compose.map φ'`, there is a
unique `χ : v' ⟶ v` with `compose.map χ = ψ` and `χ ≫ φ = φ'`. -/
theorem compose_unique_lift {S T X Y Z : B} (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y)
    (g : Y ⟶ Z) (z : T ⟶ Z) (γ : (j ≫ z) ⟶ (x ≫ f ≫ g))
    {u v v' : WithFactorization x j f g z γ} (φ : v ⟶ u) (φ' : v' ⟶ u)
    (ψ : (compose x j f g z γ).obj v' ⟶ (compose x j f g z γ).obj v)
    (hψ : ψ ≫ (compose x j f g z γ).map φ = (compose x j f g z γ).map φ') :
    ∃! (χ : v' ⟶ v), (compose x j f g z γ).map χ = ψ ∧ χ ≫ φ = φ' := by
  have hψθ : ψ.θ ≫ φ.θ₂ = φ'.θ₂ := by
    simpa only [DottedArrow.Hom.comp_θ, compose_map_θ] using congrArg DottedArrow.Hom.θ hψ
  refine ⟨{ θ₁ := φ'.θ₁ ≫ inv φ.θ₁
            θ₂ := ψ.θ
            cond_α := ?_
            cond_β := ?_
            cond_η := ?_ }, ⟨?_, ?_⟩, ?_⟩
  · have hθ : (φ'.θ₁ ≫ inv φ.θ₁) ≫ φ.θ₁ = φ'.θ₁ := by
      rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [φ.cond_α, ← Category.assoc, ← whiskerLeft_comp, hθ, ← φ'.cond_α]
  · rw [comp_whiskerRight, ← Category.assoc, ← φ'.cond_β, φ.cond_β, Category.assoc,
      ← comp_whiskerRight, IsIso.hom_inv_id, id_whiskerRight, Category.comp_id]
  · have hv : v.η = φ.θ₂ ≫ u.η ≫ (inv φ.θ₁ ▷ f) := by
      rw [← Category.assoc, φ.cond_η, Category.assoc, ← comp_whiskerRight,
        IsIso.hom_inv_id, id_whiskerRight, Category.comp_id]
    rw [hv, ← Category.assoc, hψθ, ← Category.assoc, φ'.cond_η, Category.assoc,
      ← comp_whiskerRight]
  · exact DottedArrow.Hom.ext (compose_map_θ ..)
  · apply WithFactorization.Hom.ext
    · dsimp
      rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    · exact hψθ
  · rintro χ ⟨hχ1, hχ2⟩
    apply WithFactorization.Hom.ext
    · have := congrArg WithFactorization.Hom.θ₁ hχ2
      rw [WithFactorization.Hom.comp_θ₁] at this
      dsimp only
      rw [← this, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    · exact congrArg DottedArrow.Hom.θ hχ1

/-- `compose : 𝒟'' ⥤ 𝒟'` is fibred in groupoids. -/
@[stacks 0H1B, stacks 0CLF]
theorem compose_isFiberedInGroupoids {S T X Y Z : B} (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y)
    (g : Y ⟶ Z) (z : T ⟶ Z) (γ : (j ≫ z) ⟶ (x ≫ f ≫ g)) :
    (compose x j f g z γ).IsFiberedInGroupoids where
  exists_lift := by
    intro V U ψ u hu
    obtain ⟨v, φ, hv, eq⟩ := compose_lift x j f g z γ ψ u hu
    exact ⟨v, φ, IsHomLift.of_fac' _ ψ φ hv hu eq⟩
  unique_lift := by
    intro a b c φ ψ bf hcomm
    exact compose_unique_lift x j f g z γ φ ψ bf hcomm

/-! ## Filling the outer rectangle in two steps

A dotted arrow for the outer rectangle is assembled from a dotted arrow `d'` for the lower
square together with a dotted arrow for the upper square whose bottom edge is `d'.a` and whose
witness is `d'.α`. -/

/-- Assemble a dotted arrow for the outer rectangle from a dotted arrow `d'` for the lower
square and a dotted arrow `e` for the upper square over `d'`. The diagonal is `e.a`, the upper
triangle is `e.α`, and the lower triangle is `d'.β` followed by `e.β` whiskered with `g`. -/
@[implicit_reducible]
noncomputable def ofLowerUpper {S T X Y Z : B} (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y)
    (g : Y ⟶ Z) (z : T ⟶ Z) (γ : (j ≫ z) ⟶ (x ≫ f ≫ g))
    (d' : DottedArrow (x ≫ f) j g z (γ ≫ (α_ x f g).inv))
    (e : DottedArrow x j f d'.a d'.α) :
    DottedArrow x j (f ≫ g) z γ where
  a := (toFiberObj x j f g z γ d' e).a
  α := (toFiberObj x j f g z γ d' e).α
  β := (toFiberObj x j f g z γ d' e).β
  compat := (toFiberObj x j f g z γ d' e).compat

omit [Bicategory.IsLocallyGroupoid B] in
/-- The `1`-morphism of `ofLowerUpper d' e` is `e.a`. -/
@[simp] theorem ofLowerUpper_a {S T X Y Z : B} (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y)
    (g : Y ⟶ Z) (z : T ⟶ Z) (γ : (j ≫ z) ⟶ (x ≫ f ≫ g))
    (d' : DottedArrow (x ≫ f) j g z (γ ≫ (α_ x f g).inv))
    (e : DottedArrow x j f d'.a d'.α) :
    (ofLowerUpper x j f g z γ d' e).a = e.a := rfl

omit [Bicategory.IsLocallyGroupoid B] in
/-- The upper `2`-morphism of `ofLowerUpper d' e` is `e.α`. -/
@[simp] theorem ofLowerUpper_α {S T X Y Z : B} (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y)
    (g : Y ⟶ Z) (z : T ⟶ Z) (γ : (j ≫ z) ⟶ (x ≫ f ≫ g))
    (d' : DottedArrow (x ≫ f) j g z (γ ≫ (α_ x f g).inv))
    (e : DottedArrow x j f d'.a d'.α) :
    (ofLowerUpper x j f g z γ d' e).α = e.α := rfl

omit [Bicategory.IsLocallyGroupoid B] in
/-- The lower `2`-morphism of `ofLowerUpper d' e` is `d'.β ≫ (e.β ▷ g) ≫ (α_ e.a f g).hom`. -/
@[simp] theorem ofLowerUpper_β {S T X Y Z : B} (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y)
    (g : Y ⟶ Z) (z : T ⟶ Z) (γ : (j ≫ z) ⟶ (x ≫ f ≫ g))
    (d' : DottedArrow (x ≫ f) j g z (γ ≫ (α_ x f g).inv))
    (e : DottedArrow x j f d'.a d'.α) :
    (ofLowerUpper x j f g z γ d' e).β = d'.β ≫ (e.β ▷ g) ≫ (α_ e.a f g).hom := rfl

/-- `ofLowerUpper` lies over `d'`: the object of `𝒟''` it comes from is sent to `d'` by
`compose`, on the nose. -/
alias compose_toWithFactorization_ofLowerUpper := CategoryTheory.DottedArrow.toFiber_over

omit [Bicategory.IsLocallyGroupoid B] in
/-- **Nonemptiness of a rectangle of dotted arrows from its two halves.** If the lower square
can be filled, and every filling of the lower square leaves an upper square that can be
filled, then the outer rectangle can be filled. -/
theorem nonempty_of_lower_upper {S T X Y Z : B} (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y)
    (g : Y ⟶ Z) (z : T ⟶ Z) (γ : (j ≫ z) ⟶ (x ≫ f ≫ g))
    (hlower : Nonempty (DottedArrow (x ≫ f) j g z (γ ≫ (α_ x f g).inv)))
    (hupper : ∀ d' : DottedArrow (x ≫ f) j g z (γ ≫ (α_ x f g).inv),
      Nonempty (DottedArrow x j f d'.a d'.α)) :
    Nonempty (DottedArrow x j (f ≫ g) z γ) :=
  hlower.elim fun d' => (hupper d').elim fun e => ⟨ofLowerUpper x j f g z γ d' e⟩

end DottedArrow

end CategoryTheory
