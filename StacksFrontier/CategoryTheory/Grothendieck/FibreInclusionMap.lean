module

public import Mathlib.CategoryTheory.GuitartExact.KanExtension
public import Mathlib.CategoryTheory.Grothendieck
public import StacksFrontier.CategoryTheory.EqToHomAbsorption

/-!
# Fibre inclusions and the functoriality of the Grothendieck construction

A natural transformation `α : F ⟶ G` of functors into `Cat` induces a functor between the
Grothendieck constructions of `F` and of `G` which preserves the base object. It therefore
carries the fibre over an object `c` of the base into the fibre over `c`, where it acts by the
component `α.app c`. We show that the resulting square of functors commutes on the nose, and
that it is Guitart exact.

## Main results

* `CategoryTheory.Grothendieck.comp_ι_map`: composing a morphism into the fibre over `c` with the
  image of a morphism of that fibre adds the latter to the fibre component.
* `CategoryTheory.Grothendieck.ι_comp_map`: the square formed by the two fibre inclusions over
  `c`, the component of the transformation at `c`, and the induced functor on Grothendieck
  constructions commutes as an equality of functors.
* `CategoryTheory.Grothendieck.guitartExact_ιCompMap`: that square is Guitart exact.
-/

@[expose] public section

open CategoryTheory

universe u

namespace CategoryTheory

namespace Grothendieck

/-- Two successive transports on the left of a morphism amount to a single transport. -/
private theorem transport_trans_comp {C : Type*} [Category* C] {X X' X'' Y : C} (p : X = X')
    (q : X' = X'') (r : X = X'') (m : X'' ⟶ Y) :
    eqToHom p ≫ eqToHom q ≫ m = eqToHom r ≫ m := by
  rw [← Category.assoc, eqToHom_trans]

/-- A transport and its inverse surrounding a composite are absorbed. -/
private theorem transport_absorb_comp {C : Type*} [Category* C] {X X' Y Z : C} (p : X = X')
    (q : X' = X) (r : Y = Y) (a : X ⟶ Y) (b : Y ⟶ Z) :
    eqToHom p ≫ eqToHom q ≫ a ≫ eqToHom r ≫ b = a ≫ b := by
  cases p
  simp

/-- A transport and its inverse surrounding an identity are absorbed. -/
private theorem transport_absorb_id {C : Type*} [Category* C] {X X' Z : C} (p : X = X')
    (q : X' = X) (m : X ⟶ Z) : (eqToHom p ≫ 𝟙 X') ≫ eqToHom q ≫ m = m := by
  cases p
  simp

/-- A transport and its inverse surrounding the left factor of a composite are absorbed. -/
private theorem transport_absorb_assoc {C : Type*} [Category* C] {X X' Y Z : C} (p : X = X')
    (q : X' = X) (m : X ⟶ Y) (n : Y ⟶ Z) :
    eqToHom p ≫ (eqToHom q ≫ m) ≫ n = m ≫ n := by
  cases p
  simp

variable {I : Type*} [Category* I] {F G : I ⥤ Cat.{u, u}}

/-- Composing a morphism of a Grothendieck construction whose target lies in the fibre over `c`
with the image of a morphism of that fibre adds the latter to the fibre component. -/
theorem comp_ι_map {c : I} {X : Grothendieck F} {Y Z : F.obj c} (f : X.base ⟶ c)
    (a : (F.map f).toFunctor.obj X.fiber ⟶ Y) (b : Y ⟶ Z) :
    (⟨f, a⟩ : X ⟶ (Grothendieck.ι F c).obj Y) ≫ (Grothendieck.ι F c).map b =
      (⟨f, a ≫ b⟩ : X ⟶ (Grothendieck.ι F c).obj Z) := by
  refine Grothendieck.ext _ _ (Category.comp_id f) ?_
  dsimp only [Grothendieck.ι, Grothendieck.comp_fiber]
  simp only [Functor.congr_hom (congrArg Cat.Hom.toFunctor (F.map_id c)) a,
    Cat.Hom.id_toFunctor, Functor.id_map, Category.assoc, eqToHom_trans_assoc]
  exact transport_absorb_comp _ _ _ a b

/-- The inclusion of the fibre over `c`, followed by the functor induced on Grothendieck
constructions by a natural transformation, is the component of that transformation at `c`
followed by the inclusion of the fibre over `c`. -/
theorem ι_comp_map (α : F ⟶ G) (c : I) :
    Grothendieck.ι F c ⋙ Grothendieck.map α = (α.app c).toFunctor ⋙ Grothendieck.ι G c :=
  CategoryTheory.Functor.ext_of_iso (Grothendieck.ιCompMap α c) (fun _ => rfl) (fun _ => rfl)

/-- The square formed by the two fibre inclusions over `c` and the functor induced on
Grothendieck constructions by a natural transformation is Guitart exact. -/
theorem guitartExact_ιCompMap (α : F ⟶ G) (c : I) :
    TwoSquare.GuitartExact (T := Grothendieck.ι F c) (L := (α.app c).toFunctor)
      (R := Grothendieck.map α) (B := Grothendieck.ι G c) (Grothendieck.ιCompMap α c).hom := by
  let w : TwoSquare (Grothendieck.ι F c) (α.app c).toFunctor (Grothendieck.map α)
      (Grothendieck.ι G c) := (Grothendieck.ιCompMap α c).hom
  show w.GuitartExact
  constructor
  intro Y y g
  let f := g.base
  let Z : F.obj c := (F.map f).toFunctor.obj Y.fiber
  have hobj : (α.app c).toFunctor.obj Z =
      (G.map f).toFunctor.obj ((α.app Y.base).toFunctor.obj Y.fiber) :=
    Functor.congr_obj (congrArg Cat.Hom.toFunctor (α.naturality f)) Y.fiber
  let a : Y ⟶ (Grothendieck.ι F c).obj Z := ⟨f, 𝟙 _⟩
  let b : (α.app c).toFunctor.obj Z ⟶ y := eqToHom hobj ≫ g.fiber
  have hmap : ∀ {Z' : F.obj c} (u : Z ⟶ Z'),
      (Grothendieck.map α).map (⟨f, u⟩ : Y ⟶ (Grothendieck.ι F c).obj Z') =
        (⟨f, eqToHom hobj.symm ≫ (α.app c).toFunctor.map u⟩ :
          (Grothendieck.map α).obj Y ⟶
            (Grothendieck.ι G c).obj ((α.app c).toFunctor.obj Z')) := by
    intro Z' u
    refine Grothendieck.ext _ _ rfl ?_
    simp only [Grothendieck.map, Cat.eqToHom_app]
    exact transport_trans_comp _ _ _ ((α.app c).toFunctor.map u)
  have hcomp : ∀ {Z' : F.obj c} (u : Z ⟶ Z') (m : (α.app c).toFunctor.obj Z' ⟶ y),
      (Grothendieck.map α).map (⟨f, u⟩ : Y ⟶ (Grothendieck.ι F c).obj Z') ≫
          w.app Z' ≫ (Grothendieck.ι G c).map m =
        (⟨f, (eqToHom hobj.symm ≫ (α.app c).toFunctor.map u) ≫ m⟩ :
          (Grothendieck.map α).obj Y ⟶ (Grothendieck.ι G c).obj y) := by
    intro Z' u m
    refine Eq.trans ?_ (comp_ι_map (F := G) f
      (eqToHom hobj.symm ≫ (α.app c).toFunctor.map u) m)
    rw [hmap]
    exact congrArg _ (Category.id_comp _)
  have comm : (Grothendieck.map α).map a ≫ w.app Z ≫ (Grothendieck.ι G c).map b = g := by
    refine Eq.trans (hcomp (𝟙 Z) b) ?_
    refine Grothendieck.ext _ _ rfl ?_
    simp only [eqToHom_refl, Category.id_comp, b, Functor.map_id]
    exact transport_absorb_id _ _ g.fiber
  let P : w.StructuredArrowRightwards g :=
    TwoSquare.StructuredArrowRightwards.mk w g Z a b comm
  have : Nonempty (w.StructuredArrowRightwards g) := ⟨P⟩
  have hinitial : ∀ Q : w.StructuredArrowRightwards g, Nonempty (P ⟶ Q) := by
    intro Q
    obtain ⟨Z', a', b', hcomm, rfl⟩ := TwoSquare.StructuredArrowRightwards.mk_surjective Q
    have hbase : a'.base = f := by
      simpa [w, Grothendieck.ιCompMap, Grothendieck.ι, Grothendieck.map] using
        congrArg Grothendieck.Hom.base hcomm
    obtain ⟨f', u⟩ := a'
    dsimp at hbase
    subst hbase
    have hcomm' : (⟨f, (eqToHom hobj.symm ≫ (α.app c).toFunctor.map u) ≫ b'⟩ :
        (Grothendieck.map α).obj Y ⟶ (Grothendieck.ι G c).obj y) = g :=
      (hcomp u b').symm.trans hcomm
    have hfiber : (α.app c).toFunctor.map u ≫ b' = b :=
      (transport_absorb_assoc hobj hobj.symm ((α.app c).toFunctor.map u) b').symm.trans
        ((congrArg (eqToHom hobj ≫ ·) (Grothendieck.congr hcomm')).trans
          (transport_trans_comp hobj _ hobj g.fiber))
    exact ⟨StructuredArrow.homMk (CostructuredArrow.homMk u hfiber) <|
      CostructuredArrow.hom_ext _ _ <|
        (comp_ι_map (F := F) f (𝟙 Z) u).trans (congrArg _ (Category.id_comp u))⟩
  exact zigzag_isConnected fun Q₁ Q₂ =>
    (Zigzag.of_inv (hinitial Q₁).some).trans (Zigzag.of_hom (hinitial Q₂).some)

end Grothendieck

end CategoryTheory

end
