module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack

/-!
# The 2-category of algebraic spaces over an algebraic stack (Stacks 04ZQ)

Let `𝒴` be an algebraic stack over `S`. Stacks 04ZQ introduces the 2-category `Spaces/𝒴`:

* an object is a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks which is representable by
  algebraic spaces;
* a 1-morphism `(g, β) : (f₁ : 𝒳₁ ⟶ 𝒴) ⟶ (f₂ : 𝒳₂ ⟶ 𝒴)` is a 1-morphism `g : 𝒳₁ ⟶ 𝒳₂`
  together with a 2-morphism `β : f₁ ⟶ g ≫ f₂`;
* a 2-morphism `(g, β) ⟶ (g', β')` is a 2-morphism `α : g ⟶ g'` with `β ≫ (α ▷ f₂) = β'`.

## Main definitions

* `AlgebraicGeometry.Stack.SpacesOverStack`: the objects of `Spaces/𝒴`.
* `AlgebraicGeometry.Stack.SpacesOverStack.Hom`: the 1-morphisms of `Spaces/𝒴`.
* `AlgebraicGeometry.Stack.SpacesOverStack.Hom₂`: the 2-morphisms of `Spaces/𝒴`.
* `AlgebraicGeometry.Stack.SpacesOverStack.Hom₂.isoMk`: a 2-morphism of `Spaces/𝒴` whose
  underlying 2-morphism of algebraic stacks is invertible, together with its inverse; the
  compatibility condition for the inverse is automatic.
* `AlgebraicGeometry.Stack.SpacesOverStack.instBicategory`: the 2-category structure carried by
  those objects, 1-morphisms and 2-morphisms.

## Implementation notes

`CategoryTheory.Bicategory.Strict` is deliberately *not* claimed. It does hold — the 2-category
of algebraic stacks is strict, so composition of 1-morphisms of `Spaces/𝒴` is associative and
unital on the nose — but it is not part of Stacks 04ZQ, and asserting it forces every structural
isomorphism here to be an `eqToIso`, which turns the three coherence computations below into
transport along equalities of dependent pairs. With the structural isomorphisms taken to be
those of the ambient 2-category instead, each is a short computation with the associator and the
unitors, and every coherence law of the new 2-category reduces, by extensionality of `Hom₂` in
its `map` field, to the corresponding law of the ambient one.

Nothing in the 2-category structure uses representability: it is data on the objects, carried
along, and the source states the definition for representable 1-morphisms because that is the
case of interest.

## References

* [Stacks Project, Tag 04ZQ](https://stacks.math.columbia.edu/tag/04ZQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

namespace AlgebraicGeometry.Stack

universe u w

/-- An object of the 2-category `Spaces/𝒴`: an algebraic stack over `S` together with a
1-morphism to `𝒴` which is representable by algebraic spaces. -/
@[stacks 04ZQ "the objects"]
structure SpacesOverStack
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒴 : AlgebraicStacks.{u, w} B S hS) where
  /-- The algebraic stack lying over `𝒴`. -/
  source : AlgebraicStacks.{u, w} B S hS
  /-- Its structure 1-morphism to `𝒴`. -/
  map : source ⟶ 𝒴
  /-- The structure 1-morphism is representable by algebraic spaces. -/
  representable : IsRepresentableByAlgebraicSpaces B S hS map.hom.hom

namespace SpacesOverStack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- A 1-morphism of `Spaces/𝒴`: a 1-morphism of the source stacks together with a 2-morphism
from the structure morphism of the source to its composite with that of the target. -/
@[stacks 04ZQ "the 1-morphisms"]
structure Hom (F G : SpacesOverStack B S hS 𝒴) where
  /-- The 1-morphism of source stacks. -/
  map : F.source ⟶ G.source
  /-- The comparison 2-morphism. -/
  comm : F.map ⟶ map ≫ G.map

/-- A 2-morphism of `Spaces/𝒴`: a 2-morphism of the underlying 1-morphisms of source stacks,
compatible with the two comparison 2-morphisms. -/
@[ext, stacks 04ZQ "the 2-morphisms"]
structure Hom₂ {F G : SpacesOverStack B S hS 𝒴} (f g : Hom F G) where
  /-- The 2-morphism of the 1-morphisms of source stacks. -/
  map : f.map ⟶ g.map
  /-- Compatibility with the comparison 2-morphisms. -/
  compat : f.comm ≫ map ▷ G.map = g.comm

namespace Hom

/-- The identity 1-morphism of `Spaces/𝒴`. -/
def id (F : SpacesOverStack B S hS 𝒴) : Hom F F := ⟨𝟙 F.source, (λ_ F.map).inv⟩

/-- Composition of 1-morphisms of `Spaces/𝒴`. -/
def comp {F G H : SpacesOverStack B S hS 𝒴} (f : Hom F G) (g : Hom G H) : Hom F H :=
  ⟨f.map ≫ g.map, f.comm ≫ f.map ◁ g.comm ≫ (α_ f.map g.map H.map).inv⟩

/-- The underlying 1-morphism of the identity of `F` is the identity of `F.source`. -/
@[simp]
theorem id_map (F : SpacesOverStack B S hS 𝒴) : (Hom.id F).map = 𝟙 F.source := rfl

/-- The comparison 2-morphism of the identity of `F` is the inverse left unitor of `F.map`. -/
@[simp]
theorem id_comm (F : SpacesOverStack B S hS 𝒴) : (Hom.id F).comm = (λ_ F.map).inv := rfl

/-- The underlying 1-morphism of a composite is the composite of the underlying 1-morphisms. -/
@[simp]
theorem comp_map {F G H : SpacesOverStack B S hS 𝒴} (f : Hom F G) (g : Hom G H) :
    (f.comp g).map = f.map ≫ g.map := rfl

/-- The comparison 2-morphism of `f.comp g` is `f.comm`, followed by `g.comm` whiskered on the
left by `f.map`, followed by the inverse associator. -/
@[simp]
theorem comp_comm {F G H : SpacesOverStack B S hS 𝒴} (f : Hom F G) (g : Hom G H) :
    (f.comp g).comm = f.comm ≫ f.map ◁ g.comm ≫ (α_ f.map g.map H.map).inv := rfl

end Hom

namespace Hom₂

/-- The identity 2-morphism of `Spaces/𝒴`. -/
def id {F G : SpacesOverStack B S hS 𝒴} (f : Hom F G) : Hom₂ f f where
  map := 𝟙 f.map
  compat := by rw [id_whiskerRight, Category.comp_id]

/-- Vertical composition of 2-morphisms of `Spaces/𝒴`. -/
def comp {F G : SpacesOverStack B S hS 𝒴} {f g h : Hom F G}
    (α : Hom₂ f g) (β : Hom₂ g h) : Hom₂ f h where
  map := α.map ≫ β.map
  compat := by rw [comp_whiskerRight, ← Category.assoc, α.compat, β.compat]

/-- A 2-morphism of `Spaces/𝒴` built from an invertible 2-morphism of the underlying
1-morphisms of algebraic stacks, together with its inverse: the compatibility condition for the
inverse is automatic. -/
def isoMk {F G : SpacesOverStack B S hS 𝒴} {f g : Hom F G}
    (e : f.map ≅ g.map) (h : f.comm ≫ e.hom ▷ G.map = g.comm) : Hom₂ f g × Hom₂ g f :=
  ⟨⟨e.hom, h⟩, ⟨e.inv, by
    rw [← h, Category.assoc, ← comp_whiskerRight, e.hom_inv_id, id_whiskerRight,
      Category.comp_id]⟩⟩

end Hom₂

/-- The 1-morphisms of `Spaces/𝒴`, with their identities and composition. -/
@[instance_reducible, stacks 04ZQ "composition of 1-morphisms"]
instance instCategoryStruct : CategoryStruct.{u + 1} (SpacesOverStack B S hS 𝒴) where
  Hom F G := Hom F G
  id F := Hom.id F
  comp f g := Hom.comp f g

/-- The category of 1-morphisms and 2-morphisms of `Spaces/𝒴` between two fixed objects: the
hom-category of its 2-category structure. -/
@[instance_reducible, stacks 04ZQ "the hom-categories"]
instance instHomCategory (F G : SpacesOverStack B S hS 𝒴) : Category.{u + 1} (F ⟶ G) where
  Hom f g := Hom₂ f g
  id f := Hom₂.id f
  comp α β := Hom₂.comp α β
  id_comp _ := Hom₂.ext (Category.id_comp _)
  comp_id _ := Hom₂.ext (Category.comp_id _)
  assoc _ _ _ := Hom₂.ext (Category.assoc _ _ _)

/-- An isomorphism of 1-morphisms of `Spaces/𝒴` from an isomorphism of the underlying
1-morphisms of algebraic stacks compatible with the comparison 2-morphisms. -/
def Hom₂.iso {F G : SpacesOverStack B S hS 𝒴} {f g : F ⟶ G}
    (e : f.map ≅ g.map) (h : f.comm ≫ e.hom ▷ G.map = g.comm) : f ≅ g where
  hom := (Hom₂.isoMk e h).1
  inv := (Hom₂.isoMk e h).2
  hom_inv_id := Hom₂.ext e.hom_inv_id
  inv_hom_id := Hom₂.ext e.inv_hom_id

/-- Left whiskering in `Spaces/𝒴`. -/
def whiskerLeftHom₂ {F G H : SpacesOverStack B S hS 𝒴} (f : Hom F G) {g h : Hom G H}
    (α : Hom₂ g h) : Hom₂ (f.comp g) (f.comp h) where
  map := f.map ◁ α.map
  compat := by
    have key : f.map ◁ g.comm ≫ f.map ◁ (α.map ▷ H.map) = f.map ◁ h.comm := by
      rw [← whiskerLeft_comp, α.compat]
    dsimp only [Hom.comp_comm, Hom.comp_map]
    simp only [Category.assoc, whisker_assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc (f.map ◁ g.comm), key]

/-- Right whiskering in `Spaces/𝒴`. -/
def whiskerRightHom₂ {F G H : SpacesOverStack B S hS 𝒴} {f g : Hom F G}
    (α : Hom₂ f g) (h : Hom G H) : Hom₂ (f.comp h) (g.comp h) where
  map := α.map ▷ h.map
  compat := by
    dsimp only [Hom.comp_comm, Hom.comp_map]
    simp only [Category.assoc]
    rw [← associator_inv_naturality_left, whisker_exchange_assoc,
      ← Category.assoc f.comm, α.compat]

/-- The associator of the 2-category of algebraic stacks is compatible with the comparison
2-morphisms of `(f.comp g).comp h` and `f.comp (g.comp h)`. -/
theorem associator_compat {F G H I : SpacesOverStack B S hS 𝒴}
    (f : Hom F G) (g : Hom G H) (h : Hom H I) :
    ((f.comp g).comp h).comm ≫ (α_ f.map g.map h.map).hom ▷ I.map =
      (f.comp (g.comp h)).comm := by
  dsimp only [Hom.comp_comm, Hom.comp_map]
  simp only [Category.assoc, whiskerLeft_comp]
  rw [← associator_inv_naturality_right_assoc, ← pentagon_inv_assoc,
    ← comp_whiskerRight, Iso.inv_hom_id, id_whiskerRight, Category.comp_id]

/-- The left unitor of the 2-category of algebraic stacks is compatible with the comparison
2-morphisms of `(Hom.id F).comp f` and `f`. -/
theorem leftUnitor_compat {F G : SpacesOverStack B S hS 𝒴} (f : Hom F G) :
    ((Hom.id F).comp f).comm ≫ (λ_ f.map).hom ▷ G.map = f.comm :=
  have key : (𝟙 F.source ◁ f.comm ≫ (α_ (𝟙 F.source) f.map G.map).inv) ≫
      (λ_ f.map).hom ▷ G.map = (λ_ F.map).hom ≫ f.comm := by
    rw [Category.assoc, ← leftUnitor_comp, leftUnitor_naturality]
  (Category.assoc _ _ _).trans
    ((congrArg (fun k => (λ_ F.map).inv ≫ k) key).trans (Iso.inv_hom_id_assoc _ _))

/-- The right unitor of the 2-category of algebraic stacks is compatible with the comparison
2-morphisms of `f.comp (Hom.id G)` and `f`. -/
theorem rightUnitor_compat {F G : SpacesOverStack B S hS 𝒴} (f : Hom F G) :
    (f.comp (Hom.id G)).comm ≫ (ρ_ f.map).hom ▷ G.map = f.comm :=
  have key : (f.map ◁ (λ_ G.map).inv ≫ (α_ f.map (𝟙 G.source) G.map).inv) ≫
      (ρ_ f.map).hom ▷ G.map = 𝟙 (f.map ≫ G.map) := by
    rw [Category.assoc, triangle_assoc_comp_left_inv_assoc, ← comp_whiskerRight,
      Iso.inv_hom_id, id_whiskerRight]
  (Category.assoc _ _ _).trans
    ((congrArg (fun k => f.comm ≫ k) key).trans (Category.comp_id f.comm))

/-- The 2-category `Spaces/𝒴` of algebraic spaces over the algebraic stack `𝒴`, with the
objects `SpacesOverStack`, the 1-morphisms `Hom` and the 2-morphisms `Hom₂`. -/
@[stacks 04ZQ "the 2-category structure"]
instance instBicategory : Bicategory.{u + 1, u + 1} (SpacesOverStack B S hS 𝒴) where
  whiskerLeft := fun {_ _ _} f {_ _} α => whiskerLeftHom₂ f α
  whiskerRight := fun {_ _ _} {_ _} α h => whiskerRightHom₂ α h
  associator := fun {_ _ _ _} f g h =>
    Hom₂.iso (f := (f.comp g).comp h) (g := f.comp (g.comp h))
      (α_ f.map g.map h.map) (associator_compat f g h)
  leftUnitor := fun {F _} f =>
    Hom₂.iso (f := (Hom.id F).comp f) (g := f) (λ_ f.map) (leftUnitor_compat f)
  rightUnitor := fun {_ G} f =>
    Hom₂.iso (f := f.comp (Hom.id G)) (g := f) (ρ_ f.map) (rightUnitor_compat f)
  whiskerLeft_id := by intros; apply Hom₂.ext; exact whiskerLeft_id _ _
  whiskerLeft_comp := by intros; apply Hom₂.ext; exact whiskerLeft_comp _ _ _
  id_whiskerLeft := by intros; apply Hom₂.ext; exact id_whiskerLeft _
  comp_whiskerLeft := by intros; apply Hom₂.ext; exact comp_whiskerLeft _ _ _
  id_whiskerRight := by intros; apply Hom₂.ext; exact id_whiskerRight _ _
  comp_whiskerRight := by intros; apply Hom₂.ext; exact comp_whiskerRight _ _ _
  whiskerRight_id := by intros; apply Hom₂.ext; exact whiskerRight_id _
  whiskerRight_comp := by intros; apply Hom₂.ext; exact whiskerRight_comp _ _ _
  whisker_assoc := by intros; apply Hom₂.ext; exact whisker_assoc _ _ _
  whisker_exchange := by intros; apply Hom₂.ext; exact whisker_exchange _ _
  pentagon := by intros; apply Hom₂.ext; exact pentagon _ _ _ _
  triangle := by intros; apply Hom₂.ext; exact triangle _ _

end SpacesOverStack

end AlgebraicGeometry.Stack

end
