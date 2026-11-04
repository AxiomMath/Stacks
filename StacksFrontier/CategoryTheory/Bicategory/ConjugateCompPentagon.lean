module

public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Iso

/-!
# Transfer of the composition pentagon along a conjugation

Let `C` be a category and suppose given two systems of functors over it: categories `D X` and
functors `T f : D X ⥤ D Y`, and categories `E X` and functors `P f : E X ⥤ E Y`. Suppose the
two systems are compared by a family of functors `c X : D X ⥤ E X` together with natural
isomorphisms `γ f : c X ⋙ P f ≅ T f ⋙ c Y`, and that each system carries a composition
comparison, `rT f g : T (f ≫ g) ≅ T f ⋙ T g` and `rP f g : P (f ≫ g) ≅ P f ⋙ P g`, the two
being compatible with `γ`.

Then the associativity coherence — the pentagon — for `rT` gives the pentagon for `rP`, at
every object in the image of `c`. When each `c X` is an equivalence, restriction along it is
faithful and that is the pentagon for `rP` outright.

## Main results

* `CategoryTheory.conjugateComp_hom`: the all-`hom` form of the compatibility between `γ` and
  the two composition comparisons;
* `CategoryTheory.pentagon_of_conjugateComp`: the pentagon for `rP` at an object in the image
  of `c`, from the pentagon for `rT`;
* `CategoryTheory.conjugateComp_eqToHom`: `γ` carries the identification of the two sides of an
  equality of morphisms of `C` from one system to the other.
-/

@[expose] public section

namespace CategoryTheory

universe v v₁ v₂ u u₁ u₂

variable {C : Type u} [Category.{v} C]
  (D : C → Type u₁) [∀ X, Category.{v₁} (D X)]
  (E : C → Type u₂) [∀ X, Category.{v₂} (E X)]
  (T : ∀ {X Y : C}, (X ⟶ Y) → (D X ⥤ D Y))
  (P : ∀ {X Y : C}, (X ⟶ Y) → (E X ⥤ E Y))
  (c : ∀ X : C, D X ⥤ E X)
  (γ : ∀ {X Y : C} (f : X ⟶ Y), c X ⋙ P f ≅ T f ⋙ c Y)
  (rT : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), T (f ≫ g) ≅ T f ⋙ T g)
  (rP : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), P (f ≫ g) ≅ P f ⋙ P g)

/-- The comparison family `γ` carries the identification of the two sides of an equality of
morphisms of `C` from one system to the other. -/
lemma conjugateComp_eqToHom {X Y : C} {p q : X ⟶ Y} (e : p = q) (F : D X) :
    (eqToHom (congrArg (fun k : X ⟶ Y => P k) e)).app ((c X).obj F) ≫ (γ q).hom.app F =
      (γ p).hom.app F ≫
        (c Y).map ((eqToHom (congrArg (fun k : X ⟶ Y => T k) e)).app F) := by
  subst e
  simp

/-- The all-`hom` form of the compatibility of `γ` with the two composition comparisons. -/
lemma conjugateComp_hom
    (hcomp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (F : D X),
      (P g).map ((γ f).hom.app F) ≫ (γ g).hom.app ((T f).obj F) ≫
          (c Z).map ((rT f g).inv.app F) =
        (rP f g).inv.app ((c X).obj F) ≫ (γ (f ≫ g)).hom.app F)
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (F : D X) :
    (rP f g).hom.app ((c X).obj F) ≫ (P g).map ((γ f).hom.app F) ≫
        (γ g).hom.app ((T f).obj F) =
      (γ (f ≫ g)).hom.app F ≫ (c Z).map ((rT f g).hom.app F) := by
  rw [← cancel_mono ((c Z).map ((rT f g).inv.app F))]
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id, hcomp,
    Iso.hom_inv_id_app_assoc]
  exact (Category.comp_id _).symm

/-- The composition pentagon transfers along a conjugation: if a system `P` of functors on
the `E`-side is compared with a system `T` on the `D`-side by a family `γ` of natural
isomorphisms compatible with the two systems' composition comparisons, then the pentagon for
`T` gives the pentagon for `P` at every object in the image of the comparison functors `c`. -/
lemma pentagon_of_conjugateComp
    (hcomp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (F : D X),
      (P g).map ((γ f).hom.app F) ≫ (γ g).hom.app ((T f).obj F) ≫
          (c Z).map ((rT f g).inv.app F) =
        (rP f g).inv.app ((c X).obj F) ≫ (γ (f ≫ g)).hom.app F)
    (hassocT : ∀ {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W),
      (rT (f ≫ g) h).hom ≫ Functor.whiskerRight (rT f g).hom (T h) ≫
          (Functor.associator (T f) (T g) (T h)).hom ≫
            Functor.whiskerLeft (T f) (rT g h).inv ≫ (rT f (g ≫ h)).inv =
        eqToHom (congrArg (fun k : X ⟶ W => T k) (Category.assoc f g h)))
    {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (F : D X) :
    ((rP (f ≫ g) h).hom ≫ Functor.whiskerRight (rP f g).hom (P h) ≫
        (Functor.associator (P f) (P g) (P h)).hom ≫
          Functor.whiskerLeft (P f) (rP g h).inv ≫ (rP f (g ≫ h)).inv).app
      ((c X).obj F) =
      (eqToHom (congrArg (fun k : X ⟶ W => P k) (Category.assoc f g h))).app
        ((c X).obj F) := by
  have hT := NatTrans.congr_app (hassocT f g h) F
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] at hT ⊢
  have hnatP : (rP g h).inv.app ((P f).obj ((c X).obj F)) ≫
      (P (g ≫ h)).map ((γ f).hom.app F) =
      (P h).map ((P g).map ((γ f).hom.app F)) ≫
        (rP g h).inv.app ((c Y).obj ((T f).obj F)) :=
    ((rP g h).inv.naturality ((γ f).hom.app F)).symm
  have hnatG : (P h).map ((c Z).map ((rT f g).hom.app F)) ≫
      (γ h).hom.app ((T g).obj ((T f).obj F)) =
      (γ h).hom.app ((T (f ≫ g)).obj F) ≫
        (c W).map ((T h).map ((rT f g).hom.app F)) :=
    (γ h).hom.naturality ((rT f g).hom.app F)
  have haux : ((rP (f ≫ g) h).hom.app ((c X).obj F) ≫
        (P h).map ((rP f g).hom.app ((c X).obj F)) ≫
          (rP g h).inv.app ((P f).obj ((c X).obj F)) ≫
            (rP f (g ≫ h)).inv.app ((c X).obj F)) ≫
      (γ (f ≫ g ≫ h)).hom.app F =
      (γ ((f ≫ g) ≫ h)).hom.app F ≫
        (c W).map ((eqToHom (congrArg (fun k : X ⟶ W => T k)
          (Category.assoc f g h))).app F) := by
    calc _
        = (rP (f ≫ g) h).hom.app ((c X).obj F) ≫
            (P h).map ((rP f g).hom.app ((c X).obj F)) ≫
              (rP g h).inv.app ((P f).obj ((c X).obj F)) ≫
                ((P (g ≫ h)).map ((γ f).hom.app F) ≫
                  (γ (g ≫ h)).hom.app ((T f).obj F) ≫
                    (c W).map ((rT f (g ≫ h)).inv.app F)) := by
          rw [hcomp f (g ≫ h) F]; simp only [Category.assoc]
      _ = (rP (f ≫ g) h).hom.app ((c X).obj F) ≫
            (P h).map ((rP f g).hom.app ((c X).obj F)) ≫
              ((P h).map ((P g).map ((γ f).hom.app F)) ≫
                (rP g h).inv.app ((c Y).obj ((T f).obj F))) ≫
                  (γ (g ≫ h)).hom.app ((T f).obj F) ≫
                    (c W).map ((rT f (g ≫ h)).inv.app F) := by
          rw [reassoc_of% hnatP]
          simp only [Category.assoc]
      _ = (rP (f ≫ g) h).hom.app ((c X).obj F) ≫
            (P h).map ((rP f g).hom.app ((c X).obj F)) ≫
              (P h).map ((P g).map ((γ f).hom.app F)) ≫
                ((P h).map ((γ g).hom.app ((T f).obj F)) ≫
                  (γ h).hom.app ((T g).obj ((T f).obj F)) ≫
                    (c W).map ((rT g h).inv.app ((T f).obj F))) ≫
                  (c W).map ((rT f (g ≫ h)).inv.app F) := by
          rw [hcomp g h ((T f).obj F)]; simp only [Category.assoc]
      _ = (rP (f ≫ g) h).hom.app ((c X).obj F) ≫
            (P h).map ((γ (f ≫ g)).hom.app F ≫ (c Z).map ((rT f g).hom.app F)) ≫
              (γ h).hom.app ((T g).obj ((T f).obj F)) ≫
                (c W).map ((rT g h).inv.app ((T f).obj F)) ≫
                  (c W).map ((rT f (g ≫ h)).inv.app F) := by
          rw [← conjugateComp_hom D E T P c γ rT rP hcomp f g F]
          simp only [Functor.map_comp, Category.assoc]
      _ = (rP (f ≫ g) h).hom.app ((c X).obj F) ≫
            (P h).map ((γ (f ≫ g)).hom.app F) ≫
              ((γ h).hom.app ((T (f ≫ g)).obj F) ≫
                (c W).map ((T h).map ((rT f g).hom.app F))) ≫
                (c W).map ((rT g h).inv.app ((T f).obj F)) ≫
                  (c W).map ((rT f (g ≫ h)).inv.app F) := by
          simp only [Functor.map_comp, Category.assoc]
          rw [reassoc_of% hnatG]
      _ = ((γ ((f ≫ g) ≫ h)).hom.app F ≫ (c W).map ((rT (f ≫ g) h).hom.app F)) ≫
            (c W).map ((T h).map ((rT f g).hom.app F)) ≫
              (c W).map ((rT g h).inv.app ((T f).obj F)) ≫
                (c W).map ((rT f (g ≫ h)).inv.app F) := by
          rw [← conjugateComp_hom D E T P c γ rT rP hcomp (f ≫ g) h F]
          simp only [Category.assoc]
      _ = (γ ((f ≫ g) ≫ h)).hom.app F ≫
            (c W).map ((eqToHom (congrArg (fun k : X ⟶ W => T k)
              (Category.assoc f g h))).app F) := by
          simp only [Category.assoc, ← Functor.map_comp]
          rw [hT]
  have hcancel :=
    haux.trans (conjugateComp_eqToHom D E T P c γ (Category.assoc f g h) F).symm
  exact (cancel_mono ((γ (f ≫ g ≫ h)).hom.app F)).1 hcancel

end CategoryTheory

end
