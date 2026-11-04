module

public import Mathlib.CategoryTheory.Grothendieck
public import StacksFrontier.CategoryTheory.EqToHomAbsorption

/-!
# Fibre components of morphisms of a Grothendieck construction

A morphism of `CategoryTheory.Grothendieck F` for `F : C ⥤ Cat` has a base component and a
fibre component, the latter typed in terms of the base component. This file records the
elementary manipulations of fibre components that a functor between two Grothendieck
constructions lying over `C` calls for.

`CategoryTheory.Grothendieck.baseHom` retypes the fibre component of a morphism along a known
value of its base component, and `CategoryTheory.Grothendieck.fibreHom` specialises that to a
morphism whose base component is an identity, which is then a morphism of a single fibre.
`CategoryTheory.Grothendieck.ofFibreHom` is the inverse construction.

A functor `P : Grothendieck F ⥤ Grothendieck F'` commuting strictly with the two projections
to `C` preserves the base object only up to the equality
`CategoryTheory.Grothendieck.baseObj_eq`. Its value at an object is therefore not literally an
object of the fibre over that base object; `CategoryTheory.Grothendieck.fibreObj` transports it
there, and `CategoryTheory.Grothendieck.fibreObjIso` is the resulting canonical isomorphism,
which is what makes the transport usable.

## Main definitions

* `CategoryTheory.Grothendieck.baseHom`: the fibre component retyped along a known base
  component.
* `CategoryTheory.Grothendieck.ofFibreHom`, `CategoryTheory.Grothendieck.fibreHom`: morphisms
  of a single fibre and morphisms over an identity of the base, read as one another.
* `CategoryTheory.Grothendieck.ofFibreIso`: an isomorphism of a fibre, read as an isomorphism
  of the Grothendieck construction over an identity of the base.
* `CategoryTheory.Grothendieck.fibreObj`, `CategoryTheory.Grothendieck.fibreObjIso`: the value
  of a functor over `C` at an object, transported into the fibre over the base object.
* `CategoryTheory.Grothendieck.rectify`, `CategoryTheory.Grothendieck.rectifyIso`: a functor
  whose composite with the projection is merely isomorphic to the projection, corrected to one
  commuting with the projections on the nose, and the isomorphism with the given functor.

## Main results

* `CategoryTheory.Grothendieck.ofFibreHom_fibreHom`,
  `CategoryTheory.Grothendieck.fibreHom_ofFibreHom`: the two readings are mutually inverse.
* `CategoryTheory.Grothendieck.hom_ext_of_fiber_isIso`: a morphism whose fibre component is an
  isomorphism can be cancelled from the left among morphisms with a common base component.
* `CategoryTheory.Grothendieck.mk_eqToHom_comp_mk_eqToHom`,
  `CategoryTheory.Grothendieck.ofFibreHom_comp_mk`,
  `CategoryTheory.Grothendieck.mk_comp_ofFibreHom`: the composites that occur when a morphism
  is presented by a base component and a fibre component.
* `CategoryTheory.Grothendieck.baseObj_eq`, `CategoryTheory.Grothendieck.baseMap_eq`: what a
  functor commuting strictly with the projections to `C` does to base components.
* `CategoryTheory.Grothendieck.rectify_comp_forget`: the corrected functor commutes with the
  projections.

## Implementation notes

An object of a fibre of `F : C ⥤ Cat` is typed by a `Cat.str` instance attached to the base
object, and the base object of `(⟨c, x⟩ : Grothendieck F)` is `c` only after reducing a
projection applied to a constructor. The two spellings are definitionally equal but not
syntactically so, and the `CategoryStruct.comp` of a composite records whichever one its
elaboration produced. Consequently `CategoryTheory.eqToHom_trans_assoc` and
`CategoryTheory.eqToHom_refl` can fail to fire on a composite of transports in which both
spellings occur. The lemmas `CategoryTheory.Grothendieck.eqToHom₂_trans_comp` and
`CategoryTheory.Grothendieck.eqToHom₃_trans_comp` below, like
`CategoryTheory.eqToHom_comp_of_refl`, are stated with a single category instance, so that they
apply in term position where the elaborator compares the spellings by unfolding.
-/

@[expose] public section

namespace CategoryTheory

namespace Grothendieck

universe v u v₂ u₂

/-- Two transports whose composite is a reflexive equation are absorbed on the left of a
composite. -/
theorem eqToHom₂_trans_comp {D : Type*} [Category* D] {X X' Z : D} (h : X = X') (h' : X' = X)
    (g : X ⟶ Z) : eqToHom h ≫ eqToHom h' ≫ g = g := by simp

/-- Three transports whose composite is a reflexive equation are absorbed on the left of a
composite. -/
theorem eqToHom₃_trans_comp {D : Type*} [Category* D] {X X' X'' Z : D} (h : X = X')
    (h' : X' = X'') (h'' : X'' = X) (g : X ⟶ Z) :
    eqToHom h ≫ eqToHom h' ≫ eqToHom h'' ≫ g = g := by simp

/-- Two transports whose composite is reflexive, and a reflexive transport further along the
composite, are absorbed. -/
theorem eqToHom₂_comp_comp_eqToHom_comp {D : Type*} [Category* D] {X X' Y Z : D}
    (h : X = X') (h' : X' = X) (f : X ⟶ Y) (h'' : Y = Y) (g : Y ⟶ Z) :
    eqToHom h ≫ eqToHom h' ≫ f ≫ eqToHom h'' ≫ g = f ≫ g := by simp

/-- Two transports and an identity compose to a transport. -/
theorem eqToHom₂_comp_id_eq {E : Type*} [Category* E] {X Y Z : E} (p : X = Y) (q : Y = Z)
    (r : X = Z) : eqToHom p ≫ eqToHom q ≫ 𝟙 Z = eqToHom r := by simp

variable {C : Type u} [Category.{v} C] {F : C ⥤ Cat.{v₂, u₂}}

/-! ### Fibre components along a known base component -/

/-- The fibre component of a morphism of a Grothendieck construction, retyped along a known
value `b` of its base component. -/
def baseHom {X Y : Grothendieck F} (σ : X ⟶ Y) {b : X.base ⟶ Y.base} (hσ : σ.base = b) :
    (F.map b).toFunctor.obj X.fiber ⟶ Y.fiber :=
  eqToHom (by rw [hσ]) ≫ σ.fiber

/-- A morphism of a Grothendieck construction is recovered from a known value of its base
component together with the retyped fibre component. -/
theorem mk_baseHom {X Y : Grothendieck F} (σ : X ⟶ Y) {b : X.base ⟶ Y.base} (hσ : σ.base = b) :
    (⟨b, baseHom σ hσ⟩ : X ⟶ Y) = σ := by
  refine Grothendieck.ext _ _ hσ.symm ?_
  simp only [baseHom, eqToHom_trans_assoc]
  exact eqToHom_comp_of_refl _ σ.fiber

/-- Retyping a fibre component along the base component itself leaves it unchanged. -/
@[simp]
theorem baseHom_rfl {X Y : Grothendieck F} (σ : X ⟶ Y) : baseHom σ rfl = σ.fiber :=
  eqToHom_comp_of_refl _ _

/-- The morphism of a Grothendieck construction over the identity of `c` determined by a
morphism of the fibre `F.obj c`. -/
def ofFibreHom {c : C} {x y : F.obj c} (a : x ⟶ y) : (⟨c, x⟩ : Grothendieck F) ⟶ ⟨c, y⟩ :=
  ⟨𝟙 c, eqToHom (by simp) ≫ a⟩

/-- `CategoryTheory.Grothendieck.ofFibreHom` is the action on morphisms of the inclusion
`CategoryTheory.Grothendieck.ι F c` of the fibre over `c`. -/
theorem ofFibreHom_eq_ι_map {c : C} {x y : F.obj c} (a : x ⟶ y) :
    ofFibreHom a = (ι F c).map a := rfl

/-- The base component of `CategoryTheory.Grothendieck.ofFibreHom a` is the identity. -/
@[simp]
theorem ofFibreHom_base {c : C} {x y : F.obj c} (a : x ⟶ y) :
    (ofFibreHom a).base = 𝟙 c := rfl

/-- `CategoryTheory.Grothendieck.ofFibreHom` preserves composition. -/
theorem ofFibreHom_comp {c : C} {x y z : F.obj c} (a : x ⟶ y) (b : y ⟶ z) :
    ofFibreHom a ≫ ofFibreHom b = ofFibreHom (a ≫ b) := by
  rw [ofFibreHom_eq_ι_map, ofFibreHom_eq_ι_map, ofFibreHom_eq_ι_map]
  exact ((ι F c).map_comp a b).symm

/-- `CategoryTheory.Grothendieck.ofFibreHom` preserves identities. -/
theorem ofFibreHom_id {c : C} (x : F.obj c) :
    ofFibreHom (𝟙 x) = 𝟙 (⟨c, x⟩ : Grothendieck F) := by
  rw [ofFibreHom_eq_ι_map, Functor.map_id]
  rfl

/-- `CategoryTheory.Grothendieck.ofFibreHom` is injective. -/
private theorem ofFibreHom_injective {c : C} {x y : F.obj c} {a b : x ⟶ y}
    (h : ofFibreHom a = ofFibreHom b) : a = b :=
  (ι F c).map_injective h

/-- An isomorphism of a fibre of `F`, read as an isomorphism of `Grothendieck F` over the
identity of the base object. -/
def ofFibreIso {c : C} {x y : F.obj c} (e : x ≅ y) :
    (⟨c, x⟩ : Grothendieck F) ≅ ⟨c, y⟩ where
  hom := ofFibreHom e.hom
  inv := ofFibreHom e.inv
  hom_inv_id := by rw [ofFibreHom_comp, e.hom_inv_id, ofFibreHom_id]
  inv_hom_id := by rw [ofFibreHom_comp, e.inv_hom_id, ofFibreHom_id]

/-- The forward morphism of `CategoryTheory.Grothendieck.ofFibreIso e` is
`CategoryTheory.Grothendieck.ofFibreHom e.hom`. -/
@[simp]
theorem ofFibreIso_hom {c : C} {x y : F.obj c} (e : x ≅ y) :
    (ofFibreIso e).hom = ofFibreHom e.hom := rfl

/-- The inverse morphism of `CategoryTheory.Grothendieck.ofFibreIso e` is
`CategoryTheory.Grothendieck.ofFibreHom e.inv`. -/
@[simp]
theorem ofFibreIso_inv {c : C} {x y : F.obj c} (e : x ≅ y) :
    (ofFibreIso e).inv = ofFibreHom e.inv := rfl

/-- Composing a morphism over an identity of the base with a morphism given by a base
component and a fibre component adds the former to the fibre component. -/
theorem ofFibreHom_comp_mk {c c' : C} {x y : F.obj c} {z : F.obj c'} (a : x ⟶ y)
    (b : c ⟶ c') (u : (F.map b).toFunctor.obj y ⟶ z) :
    ofFibreHom a ≫ (⟨b, u⟩ : (⟨c, y⟩ : Grothendieck F) ⟶ ⟨c', z⟩) =
      (⟨b, (F.map b).toFunctor.map a ≫ u⟩ : (⟨c, x⟩ : Grothendieck F) ⟶ ⟨c', z⟩) := by
  refine Grothendieck.ext _ _ (Category.id_comp b) ?_
  simp only [Grothendieck.comp_fiber, ofFibreHom, Functor.map_comp, eqToHom_map,
    Category.assoc, eqToHom_trans_assoc]
  exact eqToHom₂_trans_comp _ _ ((F.map b).toFunctor.map a ≫ u)

/-- Composing a morphism given by a base component and a fibre component with a morphism over
an identity of the base adds the latter to the fibre component. -/
theorem mk_comp_ofFibreHom {c c' : C} {x : F.obj c} {y z : F.obj c'} (b : c ⟶ c')
    (u : (F.map b).toFunctor.obj x ⟶ y) (a : y ⟶ z) :
    (⟨b, u⟩ : (⟨c, x⟩ : Grothendieck F) ⟶ ⟨c', y⟩) ≫ ofFibreHom a =
      (⟨b, u ≫ a⟩ : (⟨c, x⟩ : Grothendieck F) ⟶ ⟨c', z⟩) := by
  refine Grothendieck.ext _ _ (Category.comp_id b) ?_
  dsimp only [Grothendieck.comp_fiber, ofFibreHom]
  simp only [Functor.congr_hom (congrArg Cat.Hom.toFunctor (F.map_id c')) u,
    Cat.Hom.id_toFunctor, Functor.id_map, Category.assoc, eqToHom_trans_assoc]
  exact eqToHom₂_comp_comp_eqToHom_comp _ _ u _ a

/-- The composite of two morphisms whose fibre components are transports is the morphism over
the composite base component whose fibre component is again a transport. -/
theorem mk_eqToHom_comp_mk_eqToHom {X Y Z : Grothendieck F} {b : X.base ⟶ Y.base}
    {b' : Y.base ⟶ Z.base} (p : (F.map b).toFunctor.obj X.fiber = Y.fiber)
    (q : (F.map b').toFunctor.obj Y.fiber = Z.fiber)
    (r : (F.map (b ≫ b')).toFunctor.obj X.fiber = Z.fiber) :
    (((⟨b, eqToHom p⟩ : X ⟶ Y) ≫ (⟨b', eqToHom q⟩ : Y ⟶ Z)) : X ⟶ Z) =
      ⟨b ≫ b', eqToHom r⟩ := by
  refine Grothendieck.ext _ _ rfl ?_
  simp only [Grothendieck.comp_fiber, eqToHom_map, eqToHom_trans]

/-- A morphism of a Grothendieck construction between two objects of the fibre over `c` whose
base component is the identity of `c`, read as a morphism of the fibre `F.obj c`. -/
def fibreHom {c : C} {x y : F.obj c} (φ : (⟨c, x⟩ : Grothendieck F) ⟶ ⟨c, y⟩)
    (hφ : φ.base = 𝟙 c) : x ⟶ y :=
  eqToHom (show x = (F.map (𝟙 c)).toFunctor.obj x by simp) ≫ baseHom φ hφ

/-- Reading `CategoryTheory.Grothendieck.ofFibreHom a` back in the fibre recovers `a`. -/
@[simp]
theorem fibreHom_ofFibreHom {c : C} {x y : F.obj c} (a : x ⟶ y)
    (hφ : (ofFibreHom a).base = 𝟙 c) : fibreHom (ofFibreHom a) hφ = a := by
  simp only [fibreHom, baseHom, ofFibreHom]
  simp

/-- A morphism over the identity of the base is `CategoryTheory.Grothendieck.ofFibreHom` of its
reading in the fibre. -/
@[simp]
theorem ofFibreHom_fibreHom {c : C} {x y : F.obj c}
    (φ : (⟨c, x⟩ : Grothendieck F) ⟶ ⟨c, y⟩) (hφ : φ.base = 𝟙 c) :
    ofFibreHom (fibreHom φ hφ) = φ := by
  obtain ⟨b, u⟩ := φ
  change b = 𝟙 c at hφ
  subst hφ
  refine Grothendieck.ext _ _ rfl ?_
  simp only [fibreHom, baseHom, ofFibreHom, eqToHom_trans_assoc]
  exact eqToHom₂_trans_comp _ _ u

/-- Equal morphisms over the identity of the base have equal readings in the fibre. -/
theorem fibreHom_congr {c : C} {x y : F.obj c} {φ ψ : (⟨c, x⟩ : Grothendieck F) ⟶ ⟨c, y⟩}
    (h : φ = ψ) (hφ : φ.base = 𝟙 c) (hψ : ψ.base = 𝟙 c) : fibreHom φ hφ = fibreHom ψ hψ := by
  subst h; rfl

/-- The reading in the fibre of a composite of morphisms over the identity of the base is the
composite of their readings. -/
theorem fibreHom_comp {c : C} {x y z : F.obj c} (φ : (⟨c, x⟩ : Grothendieck F) ⟶ ⟨c, y⟩)
    (ψ : (⟨c, y⟩ : Grothendieck F) ⟶ ⟨c, z⟩) (hφ : φ.base = 𝟙 c) (hψ : ψ.base = 𝟙 c)
    (hφψ : (φ ≫ ψ).base = 𝟙 c) :
    fibreHom (φ ≫ ψ) hφψ = fibreHom φ hφ ≫ fibreHom ψ hψ := by
  apply ofFibreHom_injective
  rw [← ofFibreHom_comp, ofFibreHom_fibreHom, ofFibreHom_fibreHom, ofFibreHom_fibreHom]

/-- The reading in the fibre of an identity morphism is the identity. -/
theorem fibreHom_id {c : C} {x : F.obj c}
    (hφ : Grothendieck.Hom.base (𝟙 (⟨c, x⟩ : Grothendieck F)) = 𝟙 c) :
    fibreHom (𝟙 (⟨c, x⟩ : Grothendieck F)) hφ = 𝟙 x := by
  apply ofFibreHom_injective
  rw [ofFibreHom_fibreHom, ofFibreHom_id]

/-- Transporting a fibre morphism along a morphism of the base commutes with the canonical
morphisms to the transports. This is the naturality of
`CategoryTheory.Grothendieck.ιNatTrans`. -/
theorem ofFibreHom_comp_toTransport {A B : C} (f : A ⟶ B) {x y : F.obj A} (c : x ⟶ y) :
    ofFibreHom c ≫ Grothendieck.toTransport (⟨A, y⟩ : Grothendieck F) f =
      Grothendieck.toTransport (⟨A, x⟩ : Grothendieck F) f ≫
        ofFibreHom ((F.map f).toFunctor.map c) :=
  (ιNatTrans (F := F) f).naturality c

/-- The fibre components of two morphisms with the same base component agree as soon as the
morphisms do. -/
theorem fiber_eq_of_mk_eq {X Y : Grothendieck F} {b : X.base ⟶ Y.base}
    {u u' : (F.map b).toFunctor.obj X.fiber ⟶ Y.fiber}
    (h : (⟨b, u⟩ : X ⟶ Y) = ⟨b, u'⟩) : u = u' :=
  (Grothendieck.congr h).trans (eqToHom_comp_of_refl _ _)

/-- A square relating a fibre morphism over `A` and a fibre morphism over `B`, read in the
Grothendieck construction, determines the second from the first. -/
theorem eq_of_transport_square {A B : C} (f : A ⟶ B) {x y : F.obj A} (c : x ⟶ y)
    {x' y' : F.obj B} (hx : (F.map f).toFunctor.obj x = x')
    (hy : (F.map f).toFunctor.obj y = y') (c' : x' ⟶ y')
    (h : (⟨f, eqToHom hx⟩ : (⟨A, x⟩ : Grothendieck F) ⟶ ⟨B, x'⟩) ≫ ofFibreHom c' =
      ofFibreHom c ≫ (⟨f, eqToHom hy⟩ : (⟨A, y⟩ : Grothendieck F) ⟶ ⟨B, y'⟩)) :
    c' = eqToHom hx.symm ≫ (F.map f).toFunctor.map c ≫ eqToHom hy := by
  rw [mk_comp_ofFibreHom, ofFibreHom_comp_mk] at h
  have h' := fiber_eq_of_mk_eq h
  rw [← h', ← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]

/-! ### Cancelling a morphism with invertible fibre component -/

/-- A morphism of a Grothendieck construction whose fibre component is an isomorphism can be
cancelled from the left, among morphisms that share a base component. -/
theorem hom_ext_of_fiber_isIso {X Y Z : Grothendieck F} (ϖ : X ⟶ Y) [IsIso ϖ.fiber]
    {g₁ g₂ : Y ⟶ Z} (hbase : g₁.base = g₂.base) (h : ϖ ≫ g₁ = ϖ ≫ g₂) : g₁ = g₂ := by
  obtain ⟨b₁, u₁⟩ := g₁
  obtain ⟨b₂, u₂⟩ := g₂
  change b₁ = b₂ at hbase
  subst hbase
  refine congrArg (fun t => (⟨b₁, t⟩ : Y ⟶ Z)) ?_
  exact (cancel_epi _).1 ((cancel_epi _).1 (fiber_eq_of_mk_eq h))

/-! ### A functor commuting strictly with the projections to the base -/

section

variable {F' : C ⥤ Cat.{v₂, u₂}} (P : Grothendieck F ⥤ Grothendieck F')

variable (hP : P ⋙ forget F' = forget F)

/-- A functor commuting strictly with the two projections to the base preserves base
components, up to the transports along `CategoryTheory.Grothendieck.baseObj_eq`. -/
theorem baseMap_eq {X Y : Grothendieck F} (φ : X ⟶ Y) :
    (P.map φ).base =
      eqToHom (Functor.congr_obj hP X) ≫ φ.base ≫ eqToHom (Functor.congr_obj hP Y).symm :=
  Functor.congr_hom hP φ

/-- The fibre component of the value of a functor over the base at an object, transported into
the fibre over the base object itself. -/
def fibreObj (X : Grothendieck F) : F'.obj X.base :=
  (F'.map (eqToHom (Functor.congr_obj hP X))).toFunctor.obj (P.obj X).fiber

/-- The value of a functor over the base at an object is isomorphic to its transported fibre
component, included in the fibre over the base object. -/
def fibreObjIso (X : Grothendieck F) :
    (⟨X.base, fibreObj P hP X⟩ : Grothendieck F') ≅ P.obj X :=
  Grothendieck.transportIso (P.obj X) (eqToIso (Functor.congr_obj hP X))

/-- The base component of the forward morphism of `CategoryTheory.Grothendieck.fibreObjIso P hP X`
is the transport along `CategoryTheory.Grothendieck.baseObj_eq`. -/
@[simp]
theorem fibreObjIso_hom_base (X : Grothendieck F) :
    (fibreObjIso P hP X).hom.base = eqToHom (Functor.congr_obj hP X).symm := rfl

/-- The base component of the inverse morphism of `CategoryTheory.Grothendieck.fibreObjIso P hP X`
is the transport along `CategoryTheory.Grothendieck.baseObj_eq`. -/
@[simp]
theorem fibreObjIso_inv_base (X : Grothendieck F) :
    (fibreObjIso P hP X).inv.base = eqToHom (Functor.congr_obj hP X) := rfl

end

/-! ### Rectifying a functor that lies over the base only up to isomorphism -/

section

variable {F' : C ⥤ Cat.{v₂, u₂}} (P : Grothendieck F ⥤ Grothendieck F')
  (θ : P ⋙ forget F' ≅ forget F)

/-- A functor between Grothendieck constructions whose composite with the projection is merely
isomorphic to the projection, corrected to one commuting with the projections on the nose: the
value at an object is transported along the isomorphism of base objects. -/
def rectify : Grothendieck F ⥤ Grothendieck F' where
  obj X := (P.obj X).transport (θ.hom.app X)
  map {X Y} φ := (transportIso (P.obj X) (θ.app X)).hom ≫ P.map φ ≫
    (transportIso (P.obj Y) (θ.app Y)).inv
  map_id X := by simp
  map_comp φ ψ := by simp

/-- The value of `CategoryTheory.Grothendieck.rectify P θ` at `X` is `P.obj X` transported along
the component of `θ` at `X`. -/
@[simp]
theorem rectify_obj (X : Grothendieck F) :
    (rectify P θ).obj X = (P.obj X).transport (θ.hom.app X) := rfl

/-- `CategoryTheory.Grothendieck.rectify P θ` commutes with the projections to the base. -/
theorem rectify_comp_forget : rectify P θ ⋙ forget F' = forget F := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) fun X Y φ => ?_
  have h1 : ((rectify P θ).map φ).base =
      θ.inv.app X ≫ (P ⋙ forget F').map φ ≫ θ.hom.app Y := rfl
  have h2 : θ.inv.app X ≫ (P ⋙ forget F').map φ ≫ θ.hom.app Y = (forget F).map φ := by
    rw [θ.hom.naturality φ]
    exact Iso.inv_hom_id_app_assoc θ X ((forget F).map φ)
  exact (h1.trans h2).trans
    ((eqToHom_comp_of_refl _ _).trans (comp_eqToHom_of_refl _ _)).symm

/-- The corrected functor is isomorphic to the given one. -/
def rectifyIso : rectify P θ ≅ P :=
  NatIso.ofComponents (fun X => transportIso (P.obj X) (θ.app X))
    fun φ => by simp [rectify]

end

end Grothendieck

end CategoryTheory
