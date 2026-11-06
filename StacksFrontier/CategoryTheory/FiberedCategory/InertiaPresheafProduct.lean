module

public import StacksFrontier.CategoryTheory.FiberedCategory.DiscreteTwoFibreProduct
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.Criterion
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.FibrewiseEquivalence
public import StacksCore.CategoryTheory.Inertia

/-!
# The inertia of a category over a base whose vertical automorphisms are a presheaf

Let `p : D ⥤ C` be a category over a base `C` and let `P` be a presheaf of sets on `C`.  A
*coordinatisation of the vertical automorphisms of `p` by `P`* is a bijection, for every object
`x` of `D`, between the automorphisms of `x` lying over the identity of `p(x)` and the elements
of `P(p(x))`, under which the commutation of a morphism `f : x ⟶ y` of `D` with two such
automorphisms is the equation `P(p(f))(coordinate at y) = coordinate at x`.

Given such a coordinatisation, the inertia `I_D` of `p` (`CategoryTheory.RelativeInertia` of `p`
with itself, whose objects are the pairs `(x, α)`) is equivalent, *as a category over `C`*, to the
product

`El P ×_C D`

of the category of elements of `P` with `D`, taken over `C`: its objects are the triples of an
object of `El P` over `U`, an object of `D` over `U`, and a vertical isomorphism of their images in
`C`.  The equivalence is the identity on the `D`-factor: it sends `(x, α)` to the pair of `x` and
the coordinate of `α`.

## Main definitions

* `CategoryTheory.Functor.VerticalAut`: the automorphisms of an object lying over an identity.
* `CategoryTheory.Functor.VerticalAutCoordinates`: a coordinatisation of them by a presheaf.
* `CategoryTheory.inertiaPresheafProduct`: the product `El P ×_C D` of the category of elements
  of `P` with `D`, taken in the categories over `C`, with its structure functor
  `CategoryTheory.inertiaPresheafProductStruct` to `C` and its projection
  `CategoryTheory.inertiaPresheafProductSnd` to `D`.
* `CategoryTheory.inertiaToPresheafProduct`: the comparison functor from the inertia.

## Main results

* `CategoryTheory.inertiaToPresheafProduct_fullyFaithful` and
  `CategoryTheory.hasVerticalPreimages_inertiaToPresheafProduct`: the comparison functor is fully
  faithful, and every object of the product is vertically isomorphic to one in its image.
* `CategoryTheory.inertiaEquivalenceOverPresheafProduct`: **the inertia of `p` is equivalent over
  `C` to `El P ×_C D`.**

## References

* [Stacks Project, Tag 034I](https://stacks.math.columbia.edu/tag/034I)
* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 02XV](https://stacks.math.columbia.edu/tag/02XV)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite PresheafOfCategories

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- The *vertical automorphisms* of an object `x` of a category over `C`: the automorphisms of
`x` whose image in `C` is the identity.  Together with `x` these are the objects of the inertia
`CategoryTheory.RelativeInertia`. -/
abbrev Functor.VerticalAut (p : D ⥤ C) (x : D) := {α : Aut x // p.map α.asIso.hom = 𝟙 (p.obj x)}

/-- A *coordinatisation of the vertical automorphisms of `p : D ⥤ C` by a presheaf of sets `P`
on `C`*: a bijection of the vertical automorphisms of every object `x` with the elements of
`P(p(x))`, under which the commutation of a morphism of `D` with two vertical automorphisms is
the restriction of the coordinate of the one at the target along the image of that morphism. -/
structure Functor.VerticalAutCoordinates (p : D ⥤ C) (P : Cᵒᵖ ⥤ Type v₁) where
  /-- The coordinates of the vertical automorphisms of an object. -/
  equiv (x : D) : p.VerticalAut x ≃ P.obj (op (p.obj x))
  /-- A morphism of `D` commutes with two vertical automorphisms exactly when the coordinate of
  the one at its target restricts to the coordinate of the one at its source. -/
  comm {x y : D} (f : x ⟶ y) (a : p.VerticalAut x) (b : p.VerticalAut y) :
    f ≫ b.1.asIso.hom = a.1.asIso.hom ≫ f ↔ P.map (p.map f).op (equiv y b) = equiv x a

namespace PresheafOfCategories

variable {P : Cᵒᵖ ⥤ Type v₁}

/-- The morphism of the category of elements of `P` over `f : V ⟶ W` from an element of `P(V)`
to an element of `P(W)` whose restriction along `f` it is. -/
def elementsHomOfEq {V W : C} {a : P.obj (op V)} {b : P.obj (op W)} (f : V ⟶ W)
    (h : a = P.map f.op b) :
    (⟨V, Discrete.mk a⟩ : (presheafOfCategories (P ⋙ typeToCat)).obj) ⟶ ⟨W, Discrete.mk b⟩ :=
  ⟨f, Discrete.eqToHom h⟩

/-- The base of `CategoryTheory.PresheafOfCategories.elementsHomOfEq` is the given morphism. -/
@[simp] theorem elementsHomOfEq_base {V W : C} {a : P.obj (op V)} {b : P.obj (op W)} (f : V ⟶ W)
    (h : a = P.map f.op b) : (elementsHomOfEq f h).base = f := rfl

/-- `CategoryTheory.PresheafOfCategories.elementsHomOfEq f h` lies over `f`. -/
theorem isHomLift_elementsHomOfEq {V W : C} {a : P.obj (op V)} {b : P.obj (op W)} (f : V ⟶ W)
    (h : a = P.map f.op b) : (discreteProjection P).IsHomLift f (elementsHomOfEq f h) :=
  IsHomLift.map (discreteProjection P) (elementsHomOfEq f h)

/-- Restricting an element of `P` along an isomorphism of `C` and then along its inverse
returns the element. -/
theorem map_op_hom_map_op_inv {V W : C} (e : V ≅ W) (z : P.obj (op V)) :
    P.map e.hom.op (P.map e.inv.op z) = z := by
  rw [← Functor.map_comp_apply, ← op_comp, e.hom_inv_id, op_id, Functor.map_id_apply]

end PresheafOfCategories

/-- The product `El P ×_C D` of the category of elements of a presheaf of sets `P` on `C` with a
category `D` over `C`, taken in the categories over `C`: an object is an object of `El P` over
some `U`, an object of `D` over the same `U`, and a vertical isomorphism of their images. -/
abbrev inertiaPresheafProduct (p : D ⥤ C) (P : Cᵒᵖ ⥤ Type v₁) :=
  TwoFibreProductOver (discreteProjection P) p (𝟭 C) (discreteProjection P) p

/-- The structure functor of `El P ×_C D` to the base `C`. -/
abbrev inertiaPresheafProductStruct (p : D ⥤ C) (P : Cᵒᵖ ⥤ Type v₁) :
    inertiaPresheafProduct p P ⥤ C :=
  TwoFibreProductOver.structureFunctor (discreteProjection P) p (𝟭 C) (discreteProjection P) p

/-- The projection of `El P ×_C D` to `D`. -/
abbrev inertiaPresheafProductSnd (p : D ⥤ C) (P : Cᵒᵖ ⥤ Type v₁) :
    inertiaPresheafProduct p P ⥤ D :=
  TwoFibreProductOver.snd (discreteProjection P) p (𝟭 C) (discreteProjection P) p

variable {p : D ⥤ C} {P : Cᵒᵖ ⥤ Type v₁}

/-- The object of the product `El P ×_C D` attached to an object `(x, α)` of the inertia: the
pair of `x` and the coordinate of `α`. -/
def inertiaProductObj (c : p.VerticalAutCoordinates P) (X : RelativeInertia p) :
    inertiaPresheafProduct p P where
  base := p.obj X.obj
  x := ⟨p.obj X.obj, Discrete.mk (c.equiv X.obj ⟨X.auto, X.cond⟩)⟩
  y := X.obj
  hx := rfl
  hy := rfl
  iso := Iso.refl _
  vertical := IsHomLift.id rfl

/-- The morphism of the product `El P ×_C D` attached to a morphism of the inertia: the morphism
itself on the `D`-factor, and the equation of coordinates on the `El P`-factor. -/
def inertiaProductMap (c : p.VerticalAutCoordinates P) {X Y : RelativeInertia p} (u : X ⟶ Y) :
    inertiaProductObj c X ⟶ inertiaProductObj c Y where
  hbase := p.map u.hom
  a := elementsHomOfEq (p.map u.hom)
    ((c.comm u.hom ⟨X.auto, X.cond⟩ ⟨Y.auto, Y.cond⟩).mp u.comm).symm
  b := u.hom
  ha := isHomLift_elementsHomOfEq (p.map u.hom) _
  hb := IsHomLift.map p u.hom
  w := (Category.comp_id _).trans (Category.id_comp _).symm

/-- **The comparison functor from the inertia of `p` to the product `El P ×_C D`.**  It sends
`(x, α)` to the pair of `x` and the coordinate of `α`, and is the identity on the `D`-factor. -/
def inertiaToPresheafProduct (c : p.VerticalAutCoordinates P) :
    RelativeInertia p ⥤ inertiaPresheafProduct p P where
  obj X := inertiaProductObj c X
  map u := inertiaProductMap c u
  map_id X := by
    apply TwoFibreProductOver.Hom.ext'
    · exact elements_hom_ext _ _ (p.map_id X.obj)
    · exact rfl
  map_comp {X Y Z} u v := by
    apply TwoFibreProductOver.Hom.ext'
    · exact elements_hom_ext _ _ (p.map_comp u.hom v.hom)
    · exact rfl

/-- The comparison functor sends an object of the inertia to
`CategoryTheory.inertiaProductObj`. -/
@[simp] theorem inertiaToPresheafProduct_obj (c : p.VerticalAutCoordinates P)
    (X : RelativeInertia p) : (inertiaToPresheafProduct c).obj X = inertiaProductObj c X := rfl

/-- The comparison isomorphism of `CategoryTheory.inertiaProductObj` is the identity. -/
@[simp] theorem inertiaProductObj_iso (c : p.VerticalAutCoordinates P) (X : RelativeInertia p) :
    (inertiaProductObj c X).iso = Iso.refl _ := rfl

/-- The comparison functor is strictly over the base `C`. -/
theorem inertiaToPresheafProduct_comp_struct (c : p.VerticalAutCoordinates P) :
    inertiaToPresheafProduct c ⋙ inertiaPresheafProductStruct p P =
      relativeInertiaStruct p p := rfl

/-- The comparison functor is strictly over `D`: it leaves the `D`-component untouched. -/
theorem inertiaToPresheafProduct_comp_snd (c : p.VerticalAutCoordinates P) :
    inertiaToPresheafProduct c ⋙ inertiaPresheafProductSnd p P = RelativeInertia.π p := rfl

/-- **The comparison functor is fully faithful.** -/
def inertiaToPresheafProduct_fullyFaithful (c : p.VerticalAutCoordinates P) :
    (inertiaToPresheafProduct c).FullyFaithful where
  preimage {X Y} u :=
    { hom := u.b
      comm := by
        have h1 := u.ha
        have h2 := u.hb
        have hb : p.map u.b = u.a.base :=
          (IsHomLift.fac' p u.hbase u.b).trans
            (IsHomLift.fac' (discreteProjection P) u.hbase u.a).symm
        refine (c.comm u.b ⟨X.auto, X.cond⟩ ⟨Y.auto, Y.cond⟩).mpr ?_
        rw [hb]
        exact u.a.fiber.eq.symm }
  map_preimage {X Y} u := by
    have h1 := u.ha
    have h2 := u.hb
    apply TwoFibreProductOver.Hom.ext'
    · exact elements_hom_ext _ _ ((IsHomLift.fac' p u.hbase u.b).trans
        (IsHomLift.fac' (discreteProjection P) u.hbase u.a).symm)
    · exact rfl
  preimage_map u := RelativeInertiaHom.ext rfl

private theorem baseAuxHom {X Y Z : C} (h₁ : X = Z) (h₂ : Y = Z) (f : Y ⟶ Y) (hf : f = 𝟙 Y)
    (g : X ⟶ Y) (hg : g = eqToHom h₁ ≫ eqToHom h₂.symm) :
    eqToHom h₂.symm ≫ f ≫ 𝟙 Y = eqToHom h₁.symm ≫ g ≫ 𝟙 Y := by
  subst hg; subst hf; subst h₁; subst h₂; simp

private theorem baseAuxInv {X Y Z : C} (h₁ : X = Z) (h₂ : Y = Z) (f : Y ⟶ Y) (hf : f = 𝟙 Y)
    (g : Y ⟶ X) (hg : g = eqToHom h₂ ≫ eqToHom h₁.symm) :
    𝟙 Y ≫ f ≫ eqToHom h₂ = 𝟙 Y ≫ g ≫ eqToHom h₁ := by
  subst hg; subst hf; subst h₁; subst h₂; simp

private theorem squareAuxHom {X Y : C} (g q : X ⟶ Y) (hq : q = g) (f : Y ⟶ Y) (hf : f = 𝟙 Y) :
    g ≫ 𝟙 Y = q ≫ f := by
  subst hq; subst hf; simp

private theorem squareAuxInv {X Y : C} (i : X ≅ Y) (g : Y ⟶ X) (hg : g = i.inv) (f : Y ⟶ Y)
    (hf : f = 𝟙 Y) : g ≫ i.hom = 𝟙 Y ≫ f := by
  subst hg; subst hf; simp

private theorem liftAuxHom {X Y Z : C} (h₁ : X = Z) (h₂ : Y = Z) (g : X ⟶ Y)
    (hg : g = eqToHom h₁ ≫ eqToHom h₂.symm) :
    eqToHom h₁.symm ≫ g ≫ 𝟙 Y = 𝟙 Z ≫ 𝟙 Z ≫ eqToHom h₂.symm := by
  subst hg; subst h₁; subst h₂; simp

/-- **Every object of the product is vertically isomorphic to one in the image of the comparison
functor.** -/
theorem hasVerticalPreimages_inertiaToPresheafProduct (c : p.VerticalAutCoordinates P) :
    Functor.HasVerticalPreimages (relativeInertiaStruct p p) (inertiaPresheafProductStruct p P)
      (inertiaToPresheafProduct c) := by
  intro Q
  have hv := Q.vertical
  have hvert : Q.iso.hom = eqToHom Q.hx ≫ eqToHom Q.hy.symm := by
    simpa only [Functor.id_map, Category.id_comp] using IsHomLift.fac' (𝟭 C) (𝟙 Q.base) Q.iso.hom
  have hQiso : Q.iso = eqToIso (Q.hx.trans Q.hy.symm) :=
    Iso.ext (hvert.trans (eqToHom_trans _ _))
  have hvertinv : Q.iso.inv = eqToHom Q.hy ≫ eqToHom Q.hx.symm := by
    rw [hQiso, eqToIso.inv, eqToHom_trans]
  obtain ⟨⟨α, hα⟩, hcoord⟩ : ∃ v : p.VerticalAut Q.y,
      c.equiv Q.y v = P.map Q.iso.inv.op Q.x.fiber.as :=
    ⟨_, (c.equiv Q.y).apply_symm_apply _⟩
  have hfib : Q.x.fiber.as = P.map Q.iso.hom.op (c.equiv Q.y ⟨α, hα⟩) :=
    ((congrArg (fun t => P.map Q.iso.hom.op t) hcoord).trans
      (map_op_hom_map_op_inv Q.iso Q.x.fiber.as)).symm
  obtain ⟨hel, helh, heli⟩ : ∃ e : Q.x ≅ (⟨p.obj Q.y, Discrete.mk (c.equiv Q.y ⟨α, hα⟩)⟩ :
      (presheafOfCategories (P ⋙ typeToCat)).obj),
      e.hom.base = Q.iso.hom ∧ e.inv.base = Q.iso.inv :=
    ⟨elementsIsoOfBaseIso Q.iso hfib, rfl, rfl⟩
  have hmh : (discreteProjection P).map hel.hom = Q.iso.hom := helh
  have hmi : (discreteProjection P).map hel.inv = Q.iso.inv := heli
  have h1 := baseAuxHom Q.hx Q.hy (p.map (𝟙 Q.y)) (p.map_id Q.y)
    ((discreteProjection P).map hel.hom) (hmh.trans hvert)
  have h2 := squareAuxHom ((discreteProjection P).map hel.hom) Q.iso.hom hmh.symm
    (p.map (𝟙 Q.y)) (p.map_id Q.y)
  have h3 := baseAuxInv Q.hx Q.hy (p.map (𝟙 Q.y)) (p.map_id Q.y)
    ((discreteProjection P).map hel.inv) (hmi.trans hvertinv)
  have h4 := squareAuxInv Q.iso ((discreteProjection P).map hel.inv) hmi
    (p.map (𝟙 Q.y)) (p.map_id Q.y)
  have h5 := liftAuxHom Q.hx Q.hy ((discreteProjection P).map hel.hom) (hmh.trans hvert)
  have h6 : hel.hom ≫ hel.inv = 𝟙 Q.x := hel.hom_inv_id
  have h7 : 𝟙 Q.y ≫ 𝟙 Q.y = 𝟙 Q.y := Category.id_comp _
  have h8 : hel.inv ≫ hel.hom
      = 𝟙 (⟨p.obj Q.y, Discrete.mk (c.equiv Q.y ⟨α, hα⟩)⟩ :
        (presheafOfCategories (P ⋙ typeToCat)).obj) := hel.inv_hom_id
  exact ⟨⟨Q.y, α, hα⟩, Q.hy,
    ⟨TwoFibreProductOver.Hom.mk' hel.hom (𝟙 Q.y) h1 h2,
      TwoFibreProductOver.Hom.mk' hel.inv (𝟙 Q.y) h3 h4,
      TwoFibreProductOver.Hom.ext' h6 h7, TwoFibreProductOver.Hom.ext' h8 h7⟩,
    IsHomLift.of_fac' _ (𝟙 Q.base) _ rfl Q.hy h5⟩

/-- The equivalence over `C` given by a functor `F` strictly over `C` together with a
quasi-inverse whose unit and counit are vertical (`CategoryTheory.Functor.IsEquivalenceOver`). -/
def equivalenceOverOfIsEquivalenceOver {E : Type u₃} [Category.{v₃} E] {q : D ⥤ C} {r : E ⥤ C}
    {F : D ⥤ E} (hF : F ⋙ r = q) (e : Functor.IsEquivalenceOver q r F) :
    StacksRepresentableCFG.EquivalenceOver q r where
  hom := ⟨F, hF⟩
  inv := ⟨e.inv, e.inv_over⟩
  unitIso := e.unitIso.symm
  counitIso := e.counitIso
  unit_over := by
    ext X
    have hv := e.unit_vertical X
    have := IsHomLift.lift_id_inv_isIso q (q.obj ((F ⋙ e.inv).obj X)) (e.unitIso.hom.app X)
    simpa using IsHomLift.fac' q (𝟙 (q.obj ((F ⋙ e.inv).obj X)))
      (CategoryTheory.inv (e.unitIso.hom.app X))
  counit_over := by
    ext X
    have hv := e.counit_vertical X
    simpa using IsHomLift.fac' r (𝟙 (r.obj ((e.inv ⋙ F).obj X))) (e.counitIso.hom.app X)

/-- **The inertia of a category over `C` whose vertical automorphisms are coordinatised by a
presheaf of sets `P` is the product `El P ×_C D`**, as categories over `C`: the comparison functor
sending `(x, α)` to the pair of `x` and the coordinate of `α` is an equivalence over `C`. -/
def inertiaEquivalenceOverPresheafProduct (c : p.VerticalAutCoordinates P) :
    StacksRepresentableCFG.EquivalenceOver (relativeInertiaStruct p p)
      (inertiaPresheafProductStruct p P) :=
  letI hff := inertiaToPresheafProduct_fullyFaithful c
  letI := hff.full
  letI := hff.faithful
  equivalenceOverOfIsEquivalenceOver (inertiaToPresheafProduct_comp_struct c)
    (Functor.isEquivalenceOver_of_exists_vertical_iso
      (inertiaToPresheafProduct_comp_struct c)
      (hasVerticalPreimages_inertiaToPresheafProduct c))

end CategoryTheory

end
