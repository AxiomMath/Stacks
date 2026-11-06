module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.InertiaAlgebraic
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeInertiaProjectionRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.SpacesOverAlgebraicStack
public import StacksFrontier.CategoryTheory.RelativeInertia
public import StacksFrontier.CategoryTheory.TwoFibreProductOver

/-!
# The group law on the relative inertia

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks. The relative inertia
`I_{𝒳/𝒴}` has as objects the pairs `(x, α)` with `x` an object of `𝒳` and `α` an automorphism of
`x` in the fibre category of `𝒳` that `x` lives in, subject to `f(α) = id`; its projection
`π : I_{𝒳/𝒴} ⟶ 𝒳` is representable by algebraic spaces, so `I_{𝒳/𝒴}` is an object of the
2-category `Spaces/𝒳` of Stacks 04ZQ. On it there is a *composition law*

`c : I_{𝒳/𝒴} ×_𝒳 I_{𝒳/𝒴} ⟶ I_{𝒳/𝒴}`,
`((x, α), (x', α'), β) ↦ (x, α ∘ β⁻¹ ∘ α' ∘ β)`,

which makes sense because `β : x ⟶ x'` is an isomorphism of the fibre category, together with a
*neutral element* `e : 𝒳 ⟶ I_{𝒳/𝒴}`, `x ↦ (x, id_x)`. Both are morphisms over `𝒳`: `c` composed
with `π` is the first projection composed with `π`, and `e` composed with `π` is the identity.
This is the data of **Stacks 050R**.

The source asserts that this data makes `I_{𝒳/𝒴}` a group object in `Spaces/𝒳`, and omits the
verification of the group-object axioms. The axioms are not proved here either: they are
equations between isomorphism classes of 1-morphisms of `Spaces/𝒳`, and that category — together
with its finite products, which are the 2-fibre products over `𝒳` — is not available.

## Main definitions

* `CategoryTheory.RelativeInertia.composition`: the composition law `c`.
* `AlgebraicGeometry.Stack.relativeInertiaOverStack`: the relative inertia of a 1-morphism of
  algebraic stacks, as an object of the 2-category of morphisms to `𝒳` representable by
  algebraic spaces.

The neutral element is `CategoryTheory.RelativeInertia.neutralSection`, which already exists.

## Main results

* `CategoryTheory.RelativeInertia.composition_obj_auto_hom` and
  `CategoryTheory.RelativeInertia.composition_map_hom`: the composition law is given on objects
  by `α ∘ β⁻¹ ∘ α' ∘ β` and on morphisms by the first projection.
* `CategoryTheory.RelativeInertia.composition_comp_π`: the composition law is a morphism over
  the source, namely over the first projection.
* `CategoryTheory.RelativeInertia.map_conjugateAuto_eq_id` and
  `CategoryTheory.RelativeInertia.conjugateAuto_comm`: the formula `α ∘ β⁻¹ ∘ α' ∘ β` defines an
  automorphism killed by `f`, and the first component of a morphism of the 2-fibre product
  intertwines two such automorphisms.

## Implementation notes

The composition law needs no fibredness hypothesis on the structure functor and no
algebraicity: the formula `α ∘ β⁻¹ ∘ α' ∘ β` is an automorphism of `x` killed by `f` for purely
formal reasons, and a morphism of the 2-fibre product acts on it by conjugating the two
comparison isomorphisms into each other. It is therefore stated for an arbitrary functor
`F : S ⥤ S'` and an arbitrary structure functor `p : S ⥤ C`.

The `obj`-indexed fields of an object of the 2-fibre product are spelled through the projection
`π`, so the two arithmetic lemmas below are stated for a bare isomorphism `x ≅ x'` of the
underlying objects and then applied to the comparison isomorphism.

## References

* [Stacks Project, Tag 04ZQ](https://stacks.math.columbia.edu/tag/04ZQ)
* [Stacks Project, Tag 050Q](https://stacks.math.columbia.edu/tag/050Q)
* [Stacks Project, Tag 050R](https://stacks.math.columbia.edu/tag/050R)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.RelativeInertia

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {S : Type u₂} [Category.{v₂} S]
  {S' : Type u₃} [Category.{v₃} S']

/-- The automorphism `α ∘ β⁻¹ ∘ α' ∘ β` of `x` is killed by `F`, because `α` and `α'` are and
the two copies of `β` cancel. -/
theorem map_conjugateAuto_eq_id (F : S ⥤ S') {X Y : RelativeInertia F} (i : X.obj ≅ Y.obj) :
    F.map (i.hom ≫ Y.auto.asIso.hom ≫ i.inv ≫ X.auto.asIso.hom) = 𝟙 (F.obj X.obj) := by
  rw [F.map_comp, F.map_comp, F.map_comp, Y.cond, X.cond, Category.comp_id,
    Category.id_comp, ← F.map_comp, i.hom_inv_id, F.map_id]

/-- A morphism of the 2-fibre product intertwines the two automorphisms `α ∘ β⁻¹ ∘ α' ∘ β`: its
first component commutes with them, because it commutes with `α` and with `α'` and carries the
one comparison isomorphism to the other. -/
theorem conjugateAuto_comm (F : S ⥤ S') {X₁ Y₁ X₂ Y₂ : RelativeInertia F}
    (i₁ : X₁.obj ≅ Y₁.obj) (i₂ : X₂.obj ≅ Y₂.obj) (a : X₁ ⟶ X₂) (b : Y₁ ⟶ Y₂)
    (hw : a.hom ≫ i₂.hom = i₁.hom ≫ b.hom) :
    a.hom ≫ i₂.hom ≫ Y₂.auto.asIso.hom ≫ i₂.inv ≫ X₂.auto.asIso.hom =
      (i₁.hom ≫ Y₁.auto.asIso.hom ≫ i₁.inv ≫ X₁.auto.asIso.hom) ≫ a.hom := by
  have hb : b.hom ≫ i₂.inv = i₁.inv ≫ a.hom := by
    rw [Iso.comp_inv_eq, Category.assoc, hw, Iso.inv_hom_id_assoc]
  simp only [Category.assoc]
  rw [reassoc_of% hw, reassoc_of% b.comm, reassoc_of% hb, a.comm]

/-- **Stacks 050R, the composition law of the relative inertia.** On the 2-fibre product
`I_{S/S'} ×_S I_{S/S'}`, whose objects are the triples `((x, α), (x', α'), β)` with
`β : x ≅ x'` a vertical isomorphism, it is the functor
`((x, α), (x', α'), β) ↦ (x, α ∘ β⁻¹ ∘ α' ∘ β)`, acting on morphisms by their first component. -/
@[stacks 050R "the composition law"]
def composition (F : S ⥤ S') (p : S ⥤ C) :
    TwoFibreProductOver (RelativeInertia.π F ⋙ p) (RelativeInertia.π F ⋙ p) p
        (RelativeInertia.π F) (RelativeInertia.π F) ⥤ RelativeInertia F where
  obj A :=
    { obj := A.x.obj
      auto := .of (A.iso ≪≫ A.y.auto.asIso ≪≫ A.iso.symm ≪≫ A.x.auto.asIso)
      cond := map_conjugateAuto_eq_id F A.iso }
  map {A D} φ :=
    { hom := φ.a.hom
      comm := conjugateAuto_comm F A.iso D.iso φ.a φ.b φ.w }
  map_id _ := RelativeInertiaHom.ext rfl
  map_comp _ _ := RelativeInertiaHom.ext rfl

/-- The composition law leaves the underlying object of the first factor unchanged. -/
@[simp]
theorem composition_obj_obj (F : S ⥤ S') (p : S ⥤ C)
    (A : TwoFibreProductOver (RelativeInertia.π F ⋙ p) (RelativeInertia.π F ⋙ p) p
      (RelativeInertia.π F) (RelativeInertia.π F)) :
    ((composition F p).obj A).obj = A.x.obj := rfl

/-- The automorphism attached by the composition law to `((x, α), (x', α'), β)` is
`α ∘ β⁻¹ ∘ α' ∘ β`. -/
@[simp]
theorem composition_obj_auto_hom (F : S ⥤ S') (p : S ⥤ C)
    (A : TwoFibreProductOver (RelativeInertia.π F ⋙ p) (RelativeInertia.π F ⋙ p) p
      (RelativeInertia.π F) (RelativeInertia.π F)) :
    ((composition F p).obj A).auto.asIso.hom =
      A.iso.hom ≫ A.y.auto.asIso.hom ≫ A.iso.inv ≫ A.x.auto.asIso.hom := rfl

/-- On morphisms the composition law is the first projection. -/
@[simp]
theorem composition_map_hom (F : S ⥤ S') (p : S ⥤ C)
    {A D : TwoFibreProductOver (RelativeInertia.π F ⋙ p) (RelativeInertia.π F ⋙ p) p
      (RelativeInertia.π F) (RelativeInertia.π F)} (φ : A ⟶ D) :
    ((composition F p).map φ).hom = φ.a.hom := rfl

/-- **The composition law is a morphism over the source**: followed by the projection to `S` it
is the first projection of the 2-fibre product followed by that projection. -/
@[stacks 050R "the composition law is a morphism over the source"]
theorem composition_comp_π (F : S ⥤ S') (p : S ⥤ C) :
    composition F p ⋙ RelativeInertia.π F =
      TwoFibreProductOver.fst (RelativeInertia.π F ⋙ p) (RelativeInertia.π F ⋙ p) p
        (RelativeInertia.π F) (RelativeInertia.π F) ⋙ RelativeInertia.π F := rfl

end CategoryTheory.RelativeInertia

add_to_stacks 050R "the neutral element" CategoryTheory.RelativeInertia.neutralSection

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The relative inertia as an object of `Spaces/𝒳`.** For a 1-morphism `f : 𝒳 ⟶ 𝒴` of
algebraic stacks, the relative inertia `I_{𝒳/𝒴}` is an algebraic stack and its projection to
`𝒳` is representable by algebraic spaces, so the pair is an object of the 2-category of
Stacks 04ZQ. This is the ambient object of which Stacks 050R asserts that it is a group
object. -/
@[stacks 050R "the relative inertia as an object of the 2-category of morphisms to the source
  representable by algebraic spaces"]
noncomputable def relativeInertiaOverStack
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : SpacesOverStack B S hS 𝒳 where
  source := ⟨relativeInertia B S hS f.hom,
    isAlgebraicStack_relativeInertia.{u, w} B S hS 𝒳.val 𝒴.val f.hom 𝒳.property 𝒴.property⟩
  map := Bicategory.InducedBicategory.mkHom
    (Bicategory.InducedBicategory.mkHom (RelativeInertia.basedProjection f.hom.hom))
  representable :=
    isRepresentableByAlgebraicSpaces_relativeInertiaProjection_of_isAlgebraicStack.{u, u, u, w}
      B S hS 𝒳.val 𝒴.val f.hom 𝒳.property 𝒴.property

end AlgebraicGeometry.Stack

end
