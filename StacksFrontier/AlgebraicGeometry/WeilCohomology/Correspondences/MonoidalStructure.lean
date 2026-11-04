module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The symmetric monoidal structure on correspondences

On the category of correspondences the tensor product of objects is the product of schemes,
`X ⊗ Y = X × Y`, and the tensor product of morphisms is the exterior product
`c ⊗ c' = pr₁₃^*c · pr₂₄^*c'`. The associativity and commutativity constraints are the graphs
of the usual associativity and factor-switch isomorphisms of products of schemes, and the unit
is `Spec(k)`. With these the category of correspondences is symmetric monoidal.

## Main definitions

* `Stacks.WeilCohomology.CorrespondenceStructure`: the data of a category of correspondences on
  the objects of a symmetric monoidal category `C`: a morphism family with identities and
  composition, the graph of a morphism of `C`, and the tensor product of correspondences.
* `Stacks.WeilCohomology.CorrespondenceStructure.Obj`: its objects, those of `C`.
* `Stacks.WeilCohomology.CorrespondenceStructure.graphIso`: the graph of an isomorphism of `C`,
  as an isomorphism of correspondences.

## Main results

* `Stacks.WeilCohomology.CorrespondenceStructure.monoidalCategory` and
  `Stacks.WeilCohomology.CorrespondenceStructure.symmetricCategory`: the category of
  correspondences is symmetric monoidal for the exterior product.
* `Stacks.WeilCohomology.CorrespondenceStructure.tensorUnit_as`: its unit is the unit of `C`,
  namely `Spec(k)`.

## Implementation notes

The source works with the smooth projective schemes over `k`, whose products and factor switch
make them symmetric monoidal with unit `Spec(k)`; `C` here is that category, and a
correspondence of `C` from `X` to `Y` is an element of `Corrʳ(X, Y)` for the relevant degree.
Only one degree is carried at a time, as the constraints and the unit all have degree `0` and
the tensor product adds degrees: a graded category over `ℚ` is a category for each degree
together with the additive structure, and the monoidal axioms are identities between composites
of fixed total degree. Accordingly `CorrespondenceStructure` records a plain morphism family,
and the ℚ-linear structure, which the monoidal axioms do not involve, is absent.

Objects are a one-field wrapper around the objects of `C` rather than `C` itself, so that
`X ⊗ Y` is the product of the underlying schemes *by definition* and the constraints are the
graphs of the scheme-level constraints with no transport along equalities of objects.

The source's proof of the lemma is omitted. What the construction below supplies is the half
that is formal: given that the exterior product is a bifunctor and that the constraints are
natural, every monoidal and symmetric axiom — the pentagon, the triangle, both hexagons and the
symmetry of the braiding — follows from the corresponding axiom in `C` by applying the graph
functor, because `[Γ_f] ⊗ [Γ_g] = [Γ_{f × g}]` and `f ↦ [Γ_f]` is functorial (Stacks 0FG3).
Bifunctoriality and the four naturality squares are fields of `CorrespondenceStructure`: they
are statements about the exterior product of *arbitrary* correspondences, which graphs do not
determine, and the source proves neither.

## References

* [Stacks Project, Tag 0FG7](https://stacks.math.columbia.edu/tag/0FG7)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v u w

namespace Stacks.WeilCohomology

/-- The data of a category of correspondences on the objects of a symmetric monoidal category
`C`: for each pair of objects a type of correspondences, with identities and an associative
composition, the graph `[Γ_f]` of a morphism of `C`, and the exterior tensor product of
correspondences, which is a bifunctor for which the constraints of `C` are natural. -/
structure CorrespondenceStructure (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [SymmetricCategory C] where
  /-- The correspondences from one object to another. -/
  Hom : C → C → Type w
  /-- The identity correspondence, the class of the diagonal. -/
  id (X : C) : Hom X X
  /-- Composition of correspondences. -/
  comp {X Y Z : C} : Hom X Y → Hom Y Z → Hom X Z
  /-- The diagonal is a left identity for composition. -/
  id_comp {X Y : C} (f : Hom X Y) : comp (id X) f = f
  /-- The diagonal is a right identity for composition. -/
  comp_id {X Y : C} (f : Hom X Y) : comp f (id Y) = f
  /-- Composition of correspondences is associative. -/
  assoc {W X Y Z : C} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z) :
    comp (comp f g) h = comp f (comp g h)
  /-- The correspondence `[Γ_f]` of a morphism `f` of `C`. -/
  graph {X Y : C} (f : X ⟶ Y) : Hom X Y
  /-- The graph of an identity is the diagonal. -/
  graph_id (X : C) : graph (𝟙 X) = id X
  /-- Graphs compose: `[Γ_{f ≫ g}] = [Γ_g] ∘ [Γ_f]`. -/
  graph_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : graph (f ≫ g) = comp (graph f) (graph g)
  /-- The exterior tensor product of two correspondences. -/
  tensor {X₁ Y₁ X₂ Y₂ : C} : Hom X₁ Y₁ → Hom X₂ Y₂ → Hom (X₁ ⊗ X₂) (Y₁ ⊗ Y₂)
  /-- The exterior product of two graphs is the graph of the tensor product. -/
  tensor_graph {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    tensor (graph f) (graph g) = graph (f ⊗ₘ g)
  /-- The exterior product is compatible with composition in both variables. -/
  tensor_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} (f₁ : Hom X₁ Y₁) (f₂ : Hom X₂ Y₂) (g₁ : Hom Y₁ Z₁)
      (g₂ : Hom Y₂ Z₂) :
    comp (tensor f₁ f₂) (tensor g₁ g₂) = tensor (comp f₁ g₁) (comp f₂ g₂)
  /-- The associativity constraint is natural in all three variables. -/
  associator_naturality {X₁ Y₁ X₂ Y₂ X₃ Y₃ : C} (f₁ : Hom X₁ Y₁) (f₂ : Hom X₂ Y₂)
      (f₃ : Hom X₃ Y₃) :
    comp (tensor (tensor f₁ f₂) f₃) (graph (α_ Y₁ Y₂ Y₃).hom) =
      comp (graph (α_ X₁ X₂ X₃).hom) (tensor f₁ (tensor f₂ f₃))
  /-- The left unit constraint is natural. -/
  leftUnitor_naturality {X Y : C} (f : Hom X Y) :
    comp (tensor (id (𝟙_ C)) f) (graph (λ_ Y).hom) = comp (graph (λ_ X).hom) f
  /-- The right unit constraint is natural. -/
  rightUnitor_naturality {X Y : C} (f : Hom X Y) :
    comp (tensor f (id (𝟙_ C))) (graph (ρ_ Y).hom) = comp (graph (ρ_ X).hom) f
  /-- The commutativity constraint is natural in both variables. -/
  braiding_naturality {X₁ Y₁ X₂ Y₂ : C} (f₁ : Hom X₁ Y₁) (f₂ : Hom X₂ Y₂) :
    comp (tensor f₁ f₂) (graph (β_ Y₁ Y₂).hom) = comp (graph (β_ X₁ X₂).hom) (tensor f₂ f₁)

namespace CorrespondenceStructure

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- An object of the category of correspondences: an object of `C`. -/
structure Obj (S : CorrespondenceStructure.{v, u, w} C) where
  /-- The underlying object of `C`. -/
  as : C

variable (S : CorrespondenceStructure.{v, u, w} C)

/-- The category of correspondences: the objects of `C`, with `S.Hom` as morphisms. -/
instance category : Category.{w} S.Obj where
  Hom X Y := S.Hom X.as Y.as
  id X := S.id X.as
  comp f g := S.comp f g
  id_comp _ := S.id_comp _
  comp_id _ := S.comp_id _
  assoc _ _ _ := S.assoc _ _ _

variable {S}

/-- Composition of correspondences is the composition of the category of correspondences. -/
theorem comp_eq {X Y Z : S.Obj} (f : X ⟶ Y) (g : Y ⟶ Z) : f ≫ g = S.comp f g := rfl

/-- The identity of the category of correspondences is the diagonal. -/
theorem id_eq (X : S.Obj) : 𝟙 X = S.id X.as := rfl

/-- The graph of an isomorphism of `C`, as an isomorphism of correspondences. -/
def graphIso {X Y : C} (e : X ≅ Y) : (Obj.mk X : S.Obj) ≅ Obj.mk Y where
  hom := S.graph e.hom
  inv := S.graph e.inv
  hom_inv_id := by
    change S.comp (S.graph e.hom) (S.graph e.inv) = S.id X
    rw [← S.graph_comp, e.hom_inv_id, S.graph_id]
  inv_hom_id := by
    change S.comp (S.graph e.inv) (S.graph e.hom) = S.id Y
    rw [← S.graph_comp, e.inv_hom_id, S.graph_id]

/-- The forward morphism of `graphIso e` is the graph of `e.hom`. -/
@[simp]
theorem graphIso_hom {X Y : C} (e : X ≅ Y) : (graphIso (S := S) e).hom = S.graph e.hom := rfl

/-- The inverse morphism of `graphIso e` is the graph of `e.inv`. -/
@[simp]
theorem graphIso_inv {X Y : C} (e : X ≅ Y) : (graphIso (S := S) e).inv = S.graph e.inv := rfl

variable (S)

/-- The monoidal data on the category of correspondences: the product of `C` on objects, the
exterior product on morphisms, the unit of `C` as unit, and the graphs of the constraints of `C`
as associativity and unit constraints. -/
instance monoidalCategoryStruct : MonoidalCategoryStruct S.Obj where
  tensorObj X Y := Obj.mk (X.as ⊗ Y.as)
  whiskerLeft X _ _ f := S.tensor (S.id X.as) f
  whiskerRight f Y := S.tensor f (S.id Y.as)
  tensorHom f g := S.tensor f g
  tensorUnit := Obj.mk (𝟙_ C)
  associator X Y Z := graphIso (α_ X.as Y.as Z.as)
  leftUnitor X := graphIso (λ_ X.as)
  rightUnitor X := graphIso (ρ_ X.as)

/-- The unit of the category of correspondences is the unit of `C`, namely `Spec(k)`. -/
theorem tensorUnit_as : (𝟙_ S.Obj).as = 𝟙_ C := rfl

variable {S}

/-- The tensor product of correspondences is the exterior product. -/
theorem tensorHom_eq {X₁ Y₁ X₂ Y₂ : S.Obj} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    f ⊗ₘ g = S.tensor f g :=
  rfl

/-- Left whiskering in the category of correspondences is the exterior product with a
diagonal. -/
@[simp]
theorem whiskerLeft_eq (X : S.Obj) {Y Z : S.Obj} (f : Y ⟶ Z) :
    X ◁ f = S.tensor (S.id X.as) f :=
  rfl

/-- Right whiskering in the category of correspondences is the exterior product with a
diagonal. -/
@[simp]
theorem whiskerRight_eq {X Y : S.Obj} (f : X ⟶ Y) (Z : S.Obj) :
    f ▷ Z = S.tensor f (S.id Z.as) :=
  rfl

/-- The tensor product of objects of the category of correspondences is the tensor product of
the underlying objects of `C`. -/
@[simp]
theorem tensorObj_as (X Y : S.Obj) : (X ⊗ Y).as = X.as ⊗ Y.as := rfl

/-- The associativity constraint of the category of correspondences is the graph of the
associativity constraint of `C`. -/
@[simp]
theorem associator_hom (X Y Z : S.Obj) :
    (α_ X Y Z).hom = S.graph (α_ X.as Y.as Z.as).hom :=
  rfl

/-- The inverse associativity constraint of the category of correspondences is the graph of the
inverse associativity constraint of `C`. -/
@[simp]
theorem associator_inv (X Y Z : S.Obj) :
    (α_ X Y Z).inv = S.graph (α_ X.as Y.as Z.as).inv :=
  rfl

/-- The left unit constraint of the category of correspondences is the graph of the left unit
constraint of `C`. -/
@[simp]
theorem leftUnitor_hom (X : S.Obj) : (λ_ X).hom = S.graph (λ_ X.as).hom := rfl

/-- The right unit constraint of the category of correspondences is the graph of the right unit
constraint of `C`. -/
@[simp]
theorem rightUnitor_hom (X : S.Obj) : (ρ_ X).hom = S.graph (ρ_ X.as).hom := rfl

/-- The exterior product of a pair of identity correspondences is an identity. -/
theorem tensor_id (X Y : C) : S.tensor (S.id X) (S.id Y) = S.id (X ⊗ Y) := by
  rw [← S.graph_id, ← S.graph_id, S.tensor_graph, MonoidalCategory.id_tensorHom_id, S.graph_id]

variable (S)

/-- **Stacks Project, Tag 0FG7.** The exterior product of correspondences makes the category of
correspondences monoidal. The pentagon and the triangle hold because every morphism they
involve is a graph, so both sides are the graph of the corresponding composite in `C`. -/
@[stacks 0FG7 "the category of correspondences is monoidal for the exterior product"]
instance monoidalCategory : MonoidalCategory S.Obj :=
  .ofTensorHom
    (id_tensorHom_id := fun X Y => tensor_id X.as Y.as)
    (tensorHom_comp_tensorHom := fun f₁ f₂ g₁ g₂ => S.tensor_comp f₁ f₂ g₁ g₂)
    (associator_naturality := fun f₁ f₂ f₃ => S.associator_naturality f₁ f₂ f₃)
    (leftUnitor_naturality := fun f => S.leftUnitor_naturality f)
    (rightUnitor_naturality := fun f => S.rightUnitor_naturality f)
    (pentagon := fun W X Y Z => by
      simp only [comp_eq, id_eq, tensorHom_eq, tensorObj_as, associator_hom, ← S.graph_id,
        S.tensor_graph, ← S.graph_comp]
      exact congrArg S.graph (by
        simpa only [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom] using
          MonoidalCategory.pentagon W.as X.as Y.as Z.as))
    (triangle := fun X Y => by
      simp only [comp_eq, id_eq, tensorHom_eq, tensorObj_as, tensorUnit_as, associator_hom,
        leftUnitor_hom, rightUnitor_hom, ← S.graph_id, S.tensor_graph, ← S.graph_comp]
      exact congrArg S.graph (by
        simpa only [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom] using
          MonoidalCategory.triangle X.as Y.as))

/-- The factor switch of `C`, as the commutativity constraint of the category of
correspondences. Both hexagon identities hold because every morphism they involve is a graph. -/
instance braidedCategory : BraidedCategory S.Obj where
  braiding X Y := graphIso (β_ X.as Y.as)
  braiding_naturality_right X _ _ f := S.braiding_naturality (S.id X.as) f
  braiding_naturality_left f Z := S.braiding_naturality f (S.id Z.as)
  hexagon_forward X Y Z := by
    simp only [comp_eq, tensorObj_as, whiskerLeft_eq, whiskerRight_eq, associator_hom,
      graphIso_hom, ← S.graph_id, S.tensor_graph, ← S.graph_comp]
    exact congrArg S.graph (by
      simpa only [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom] using
        BraidedCategory.hexagon_forward X.as Y.as Z.as)
  hexagon_reverse X Y Z := by
    simp only [comp_eq, tensorObj_as, whiskerLeft_eq, whiskerRight_eq, associator_inv,
      graphIso_hom, ← S.graph_id, S.tensor_graph, ← S.graph_comp]
    exact congrArg S.graph (by
      simpa only [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom] using
        BraidedCategory.hexagon_reverse X.as Y.as Z.as)

variable {S}

/-- The commutativity constraint of the category of correspondences is the graph of the factor
switch of `C`. -/
@[simp]
theorem braiding_hom (X Y : S.Obj) : (β_ X Y).hom = S.graph (β_ X.as Y.as).hom := rfl

variable (S)

/-- **Stacks Project, Tag 0FG7.** The exterior product of correspondences makes the category of
correspondences symmetric monoidal with unit `Spec(k)`: the commutativity constraint is the
graph of the factor switch, which is an involution. -/
@[stacks 0FG7 "the category of correspondences is symmetric monoidal with unit Spec(k)"]
instance symmetricCategory : SymmetricCategory S.Obj where
  symmetry X Y := by
    change S.comp (S.graph (β_ X.as Y.as).hom) (S.graph (β_ Y.as X.as).hom) = S.id (X.as ⊗ Y.as)
    rw [← S.graph_comp, SymmetricCategory.symmetry, S.graph_id]

end CorrespondenceStructure

end Stacks.WeilCohomology

end
