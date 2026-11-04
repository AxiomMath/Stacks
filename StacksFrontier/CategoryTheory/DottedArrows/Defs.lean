module

public import Mathlib.CategoryTheory.Bicategory.LocallyGroupoid
public import StacksCore.Tactic.StacksAttribute

/-!
# Categories of dotted arrows

Fix a bicategory `B` and a square of `1`-morphisms

```
S --x--> X
|        |
j        f
|        |
v        v
T --y--> Y
```

which `2`-commutes via a chosen `2`-morphism `γ : j ≫ y ⟶ x ≫ f`. A *dotted arrow* filling
the square is a diagonal `1`-morphism `a : T ⟶ X` together with `2`-morphisms
`α : j ≫ a ⟶ x` and `β : y ⟶ a ≫ f` whose horizontal pasting recovers `γ`; the pasting is
written diagrammatically, with the associator inserted, as
`γ = (j ◁ β) ≫ (α_ j a f).inv ≫ (α ▷ f)`. A morphism of dotted arrows is a `2`-morphism
`θ : a ⟶ a'` compatible with the `α`s and the `β`s, and these assemble into the *category of
dotted arrows* `DottedArrow x j f y γ`.

Composition of `1`-morphisms and vertical composition of `2`-morphisms are written
diagrammatically: `j ≫ y` is `y ∘ j`. When `B` is a `(2,1)`-category
(`Bicategory.IsLocallyGroupoid B`), the category of dotted arrows is a groupoid.

A `2`-endomorphism `δ` of `y` transports dotted arrows for `γ` to dotted arrows for
`(j ◁ δ) ≫ γ` by replacing `β` with `δ ≫ β`; this is an equivalence when `δ` is invertible.
Consequently, if every `2`-endomorphism of `j ≫ y` is such a restriction `j ◁ δ`, the category
of dotted arrows of a `(2,1)`-category square is independent of `γ` up to a noncanonical
equivalence, and a dotted arrow exists precisely when the square admits a diagonal with both
triangles `2`-commutative.

## Main definitions

* `CategoryTheory.DottedArrow`: a dotted arrow filling a `2`-commutative square.
* `CategoryTheory.DottedArrow.Hom`: a morphism of dotted arrows.
* `CategoryTheory.instCategoryDottedArrow`: the category of dotted arrows.
* `CategoryTheory.instGroupoidDottedArrow`: in a `(2,1)`-category it is a groupoid.
* `CategoryTheory.DottedArrow.congrWitness`: the functor changing the witness `γ` along a
  `2`-endomorphism of `y`.
* `CategoryTheory.DottedArrow.congrWitnessEquivalence`: it is an equivalence when the
  `2`-endomorphism is invertible.

## Main results

* `CategoryTheory.DottedArrow.nonempty_equivalence_congrWitness`: the category of dotted arrows
  does not depend on the witness up to equivalence, when every `2`-endomorphism of `j ≫ y` is
  of the form `j ◁ δ`.
* `CategoryTheory.DottedArrow.nonempty_iff_exists_diagonal`: under the same hypothesis, a dotted
  arrow exists exactly when both triangles `2`-commute for some diagonal.
-/

@[expose] public section

namespace CategoryTheory

open CategoryTheory.Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B]

/-- A **dotted arrow** for the `2`-commutative square with `x : S ⟶ X`, `j : S ⟶ T`,
`f : X ⟶ Y`, `y : T ⟶ Y` and witnessing `2`-morphism `γ : j ≫ y ⟶ x ≫ f`: a diagonal
`1`-morphism `a : T ⟶ X` together with `2`-morphisms `α : j ≫ a ⟶ x` and `β : y ⟶ a ≫ f`
pasting to `γ`. -/
@[stacks_fixed 0H18]
structure DottedArrow {S T X Y : B} (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y) (y : T ⟶ Y)
    (γ : (j ≫ y) ⟶ (x ≫ f)) where
  /-- The dotted `1`-morphism `a : T ⟶ X`. -/
  a : T ⟶ X
  /-- The `2`-morphism `α : (j ≫ a) ⟶ x` (informally `a ∘ j → x`). -/
  α : (j ≫ a) ⟶ x
  /-- The `2`-morphism `β : y ⟶ (a ≫ f)` (informally `y → f ∘ a`). -/
  β : y ⟶ (a ≫ f)
  /-- The compatibility triangle `γ = (id_f ⋆ α) ∘ (β ⋆ id_j)`. -/
  compat : γ = (j ◁ β) ≫ (α_ j a f).inv ≫ (α ▷ f)

namespace DottedArrow

variable {S T X Y : B} {x : S ⟶ X} {j : S ⟶ T} {f : X ⟶ Y} {y : T ⟶ Y}
  {γ : (j ≫ y) ⟶ (x ≫ f)}

/-- Extensionality for dotted arrows, up to transport along an equality of the underlying
`1`-morphism `a`. The `compat` field is a proposition, so it is ignored. -/
theorem ext' {d d' : DottedArrow x j f y γ}
    (ha : d.a = d'.a) (hα : d.α = eqToHom (by rw [ha]) ≫ d'.α)
    (hβ : d.β = d'.β ≫ eqToHom (by rw [ha])) : d = d' := by
  cases d; cases d'; cases ha
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hα hβ
  subst hα hβ; rfl

/-- A **morphism of dotted arrows** `(a, α, β) ⟶ (a', α', β')` is a `2`-morphism
`θ : a ⟶ a'` such that `α = α' ∘ (θ ⋆ id_j)` and `β' = (id_f ⋆ θ) ∘ β`. -/
@[stacks_fixed 0H18]
structure Hom (d d' : DottedArrow x j f y γ) where
  /-- The underlying `2`-morphism `θ : a ⟶ a'`. -/
  θ : d.a ⟶ d'.a
  /-- Compatibility with the `α`s: `α = (θ ⋆ id_j) ∘ α'` in diagrammatic order. -/
  cond_α : d.α = (j ◁ θ) ≫ d'.α
  /-- Compatibility with the `β`s: `β' = (id_f ⋆ θ) ∘ β` in diagrammatic order. -/
  cond_β : d'.β = d.β ≫ (θ ▷ f)

namespace Hom

/-- Two morphisms of dotted arrows are equal when their underlying `2`-morphisms are. -/
@[ext] theorem ext {d d' : DottedArrow x j f y γ} {p q : Hom d d'} (h : p.θ = q.θ) : p = q := by
  cases p; cases q; simp_all

/-- The identity morphism of dotted arrows. -/
def id (d : DottedArrow x j f y γ) : Hom d d where
  θ := 𝟙 d.a
  cond_α := by simp
  cond_β := by simp

/-- Composition of morphisms of dotted arrows, inherited from vertical composition of
`2`-morphisms. -/
def comp {d d' d'' : DottedArrow x j f y γ} (p : Hom d d') (q : Hom d' d'') : Hom d d'' where
  θ := p.θ ≫ q.θ
  cond_α := by rw [p.cond_α, q.cond_α]; simp
  cond_β := by rw [q.cond_β, p.cond_β]; simp

end Hom

end DottedArrow

/-- The **category of dotted arrows** for the square and the witness `γ`: objects are dotted
arrows and morphisms are morphisms of dotted arrows. -/
@[stacks 0H18]
instance instCategoryDottedArrow {S T X Y : B} {x : S ⟶ X} {j : S ⟶ T} {f : X ⟶ Y} {y : T ⟶ Y}
    {γ : (j ≫ y) ⟶ (x ≫ f)} : Category (DottedArrow x j f y γ) where
  Hom := DottedArrow.Hom
  id := DottedArrow.Hom.id
  comp := DottedArrow.Hom.comp
  id_comp _ := DottedArrow.Hom.ext (by simp [DottedArrow.Hom.id, DottedArrow.Hom.comp])
  comp_id _ := DottedArrow.Hom.ext (by simp [DottedArrow.Hom.id, DottedArrow.Hom.comp])
  assoc _ _ _ := DottedArrow.Hom.ext (by simp [DottedArrow.Hom.comp])

namespace DottedArrow

variable {S T X Y : B} {x : S ⟶ X} {j : S ⟶ T} {f : X ⟶ Y} {y : T ⟶ Y}
  {γ : (j ≫ y) ⟶ (x ≫ f)}

/-- The underlying `2`-morphism of a composite of morphisms of dotted arrows is the vertical
composite of the underlying `2`-morphisms. -/
@[simp] theorem Hom.comp_θ {d d' d'' : DottedArrow x j f y γ} (p : d ⟶ d') (q : d' ⟶ d'') :
    (p ≫ q).θ = p.θ ≫ q.θ := rfl

/-- The underlying `2`-morphism of the identity of a dotted arrow `d` is the identity of `d.a`. -/
@[simp] theorem Hom.id_θ (d : DottedArrow x j f y γ) : Hom.θ (𝟙 d) = 𝟙 d.a := rfl

/-- The underlying `2`-morphism of an `eqToHom` between dotted arrows is the corresponding
`eqToHom` of the underlying `1`-morphisms. -/
theorem Hom.eqToHom_θ {d d' : DottedArrow x j f y γ} (h : d = d') :
    (eqToHom h).θ = eqToHom (by rw [h]) := by
  subst h; rfl

end DottedArrow

/-- In a `(2,1)`-category — a bicategory all of whose `2`-morphisms are invertible, i.e. one
satisfying `Bicategory.IsLocallyGroupoid` — the category of dotted arrows is a **groupoid**:
a morphism of dotted arrows is invertible as soon as its underlying `2`-morphism is. -/
noncomputable instance instGroupoidDottedArrow [Bicategory.IsLocallyGroupoid B]
    {S T X Y : B} {x : S ⟶ X} {j : S ⟶ T} {f : X ⟶ Y} {y : T ⟶ Y}
    {γ : (j ≫ y) ⟶ (x ≫ f)} : Groupoid (DottedArrow x j f y γ) where
  inv {d d'} p :=
    { θ := inv p.θ
      cond_α := by
        rw [p.cond_α, ← Category.assoc, ← whiskerLeft_comp, IsIso.inv_hom_id, whiskerLeft_id,
          Category.id_comp]
      cond_β := by
        rw [p.cond_β, Category.assoc, ← comp_whiskerRight, IsIso.hom_inv_id, id_whiskerRight,
          Category.comp_id] }
  inv_comp _ := DottedArrow.Hom.ext (by simp)
  comp_inv _ := DottedArrow.Hom.ext (by simp)

namespace DottedArrow

variable {S T X Y : B} {x : S ⟶ X} {j : S ⟶ T} {f : X ⟶ Y} {y : T ⟶ Y}

/-- Changing the witnessing `2`-morphism along a `2`-endomorphism `δ` of `y` with
`γ' = (j ◁ δ) ≫ γ`: the diagonal and `α` are unchanged and `β` is replaced by `δ ≫ β`. -/
def congrWitness {γ γ' : (j ≫ y) ⟶ (x ≫ f)} (δ : y ⟶ y) (hδ : γ' = (j ◁ δ) ≫ γ) :
    DottedArrow x j f y γ ⥤ DottedArrow x j f y γ' where
  obj d :=
    { a := d.a
      α := d.α
      β := δ ≫ d.β
      compat := by
        have h : (j ◁ δ) ≫ γ = (j ◁ δ) ≫ ((j ◁ d.β) ≫ (α_ j d.a f).inv ≫ (d.α ▷ f)) :=
          congrArg _ d.compat
        rw [hδ, h, whiskerLeft_comp]; bicategory }
  map m :=
    { θ := m.θ
      cond_α := m.cond_α
      cond_β := by simpa using congrArg (fun q => δ ≫ q) m.cond_β }
  map_id _ := Hom.ext (by simp)
  map_comp _ _ := Hom.ext (by simp)

/-- `congrWitness` leaves the diagonal `1`-morphism of a dotted arrow unchanged. -/
@[simp] theorem congrWitness_obj_a {γ γ' : (j ≫ y) ⟶ (x ≫ f)} (δ : y ⟶ y)
    (hδ : γ' = (j ◁ δ) ≫ γ) (d : DottedArrow x j f y γ) :
    ((congrWitness δ hδ).obj d).a = d.a := rfl

/-- `congrWitness` leaves the `2`-morphism `α` of a dotted arrow unchanged. -/
@[simp] theorem congrWitness_obj_α {γ γ' : (j ≫ y) ⟶ (x ≫ f)} (δ : y ⟶ y)
    (hδ : γ' = (j ◁ δ) ≫ γ) (d : DottedArrow x j f y γ) :
    ((congrWitness δ hδ).obj d).α = d.α := rfl

/-- `congrWitness δ` replaces the `2`-morphism `β` of a dotted arrow by `δ ≫ β`. -/
@[simp] theorem congrWitness_obj_β {γ γ' : (j ≫ y) ⟶ (x ≫ f)} (δ : y ⟶ y)
    (hδ : γ' = (j ◁ δ) ≫ γ) (d : DottedArrow x j f y γ) :
    ((congrWitness δ hδ).obj d).β = δ ≫ d.β := rfl

/-- `congrWitness` leaves the underlying `2`-morphism of a morphism of dotted arrows unchanged. -/
@[simp] theorem congrWitness_map_θ {γ γ' : (j ≫ y) ⟶ (x ≫ f)} (δ : y ⟶ y)
    (hδ : γ' = (j ◁ δ) ≫ γ) {d d' : DottedArrow x j f y γ} (m : d ⟶ d') :
    ((congrWitness δ hδ).map m).θ = m.θ := rfl

/-- An invertible `2`-endomorphism `δ` of `y` with `γ' = (j ◁ δ) ≫ γ` makes `congrWitness`
an equivalence between the two categories of dotted arrows, with inverse given by `inv δ`. -/
noncomputable def congrWitnessEquivalence {γ γ' : (j ≫ y) ⟶ (x ≫ f)} (δ : y ⟶ y) [IsIso δ]
    (hδ : γ' = (j ◁ δ) ≫ γ) :
    DottedArrow x j f y γ ≌ DottedArrow x j f y γ' := by
  have hδ' : γ = (j ◁ inv δ) ≫ γ' := by
    rw [hδ, ← Category.assoc, ← whiskerLeft_comp, IsIso.inv_hom_id, whiskerLeft_id,
      Category.id_comp]
  refine Equivalence.mk (congrWitness δ hδ) (congrWitness (inv δ) hδ') ?_ ?_
  · exact NatIso.ofComponents
      (fun d => { hom := { θ := 𝟙 d.a, cond_α := by simp, cond_β := by simp }
                  inv := { θ := 𝟙 d.a, cond_α := by simp, cond_β := by simp }
                  hom_inv_id := Hom.ext (by simp), inv_hom_id := Hom.ext (by simp) })
      (fun m => Hom.ext (by simp))
  · exact NatIso.ofComponents
      (fun d => { hom := { θ := 𝟙 d.a, cond_α := by simp, cond_β := by simp }
                  inv := { θ := 𝟙 d.a, cond_α := by simp, cond_β := by simp }
                  hom_inv_id := Hom.ext (by simp), inv_hom_id := Hom.ext (by simp) })
      (fun m => Hom.ext (by simp))

variable [Bicategory.IsLocallyGroupoid B]

/-- In a `(2,1)`-category, if every `2`-endomorphism of `j ≫ y` is the restriction `j ◁ δ` of a
`2`-endomorphism of `y`, then the category of dotted arrows does not depend, up to a
noncanonical equivalence, on the `2`-morphism witnessing the `2`-commutativity of the square. -/
theorem nonempty_equivalence_congrWitness
    (hlift : ∀ ε : (j ≫ y) ⟶ (j ≫ y), ∃ δ : y ⟶ y, j ◁ δ = ε)
    (γ γ' : (j ≫ y) ⟶ (x ≫ f)) :
    Nonempty (DottedArrow x j f y γ ≌ DottedArrow x j f y γ') := by
  obtain ⟨δ, hδ⟩ := hlift (γ' ≫ inv γ)
  exact ⟨congrWitnessEquivalence δ (by rw [hδ, Category.assoc, IsIso.inv_hom_id,
    Category.comp_id])⟩

/-- In a `(2,1)`-category, if every `2`-endomorphism of `j ≫ y` is the restriction `j ◁ δ` of a
`2`-endomorphism of `y`, then a dotted arrow exists exactly when there is a diagonal
`1`-morphism making both triangles `2`-commute, with no condition relating the two
`2`-morphisms to the witness of the square. -/
theorem nonempty_iff_exists_diagonal (γ : (j ≫ y) ⟶ (x ≫ f))
    (hlift : ∀ ε : (j ≫ y) ⟶ (j ≫ y), ∃ δ : y ⟶ y, j ◁ δ = ε) :
    Nonempty (DottedArrow x j f y γ) ↔
      ∃ a : T ⟶ X, Nonempty ((j ≫ a) ⟶ x) ∧ Nonempty (y ⟶ (a ≫ f)) := by
  refine ⟨fun ⟨d⟩ => ⟨d.a, ⟨d.α⟩, ⟨d.β⟩⟩, fun ⟨a, ⟨α⟩, ⟨β⟩⟩ => ?_⟩
  obtain ⟨e⟩ := nonempty_equivalence_congrWitness (x := x) (f := f)
    hlift ((j ◁ β) ≫ (α_ j a f).inv ≫ (α ▷ f)) γ
  exact ⟨e.functor.obj { a := a, α := α, β := β, compat := rfl }⟩

end DottedArrow

end CategoryTheory
