module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleBaseChangeMate

/-!
# Scaffolding for the horizontal pasting law for sheaves of modules

The degree-zero horizontal pasting law of Stacks 0E47 for sheaves of modules on algebraic spaces
has as its geometric content `AlgebraicGeometry.Space.modulePullbackSquareComparison_horizontal`.
This file proves the five hypotheses that
`Stacks.Cohomology.DerivedBaseChangePasting.squareComparison_horizontal` asks for in that
setting, and applies it.

## Main definitions

* `AlgebraicGeometry.Space.modulePullbackEq`,
  `AlgebraicGeometry.Space.modulePullbackCompEqLeft` and
  `AlgebraicGeometry.Space.modulePullbackCompEqRight`: the three equalities of module inverse
  images induced by an equality of morphisms.
* `AlgebraicGeometry.Space.modulePullbackSplit`: the comparison of Stacks 03LU for inverse
  images, in the splitting direction.

## Main results

* `AlgebraicGeometry.Space.modulePullbackSquareComparison_eq_square`: the square comparison
  `AlgebraicGeometry.Space.modulePullbackSquareComparison` is
  `AlgebraicGeometry.Space.modulePullbackSquare` at the equalities `rfl` and `comm.symm`.
* `AlgebraicGeometry.Space.modulePullbackSquareComparison_hom_eq`: the square comparison
  written out as its three factors in the forward direction.
* `AlgebraicGeometry.Space.modulePullbackTriangle_hom_app_assoc`: the associativity pentagon of
  Stacks 03LU at a module in the splitting direction.
* `Stacks.CategoryTheory.congr_inv_app_of_whiskerLeft_eq` and
  `Stacks.CategoryTheory.map_congr_inv_app_of_whiskerRight_eq`: compatibility of a comparison
  with an equality of functors, with the hypothesis taken between natural transformations.
* `AlgebraicGeometry.Space.modulePullbackSplit_congr_left_natTrans` and
  `AlgebraicGeometry.Space.modulePullbackSplit_congr_right_natTrans`: their inputs here.
* `AlgebraicGeometry.Space.modulePasting_pentagon_bottom`,
  `AlgebraicGeometry.Space.modulePasting_pentagon_top`,
  `AlgebraicGeometry.Space.modulePasting_pentagon_middle`,
  `AlgebraicGeometry.Space.modulePasting_congr_rightSquare` and
  `AlgebraicGeometry.Space.modulePasting_congr_leftSquare`: the five hypotheses `h1`–`h5` of
  `Stacks.Cohomology.DerivedBaseChangePasting.squareComparison_horizontal`.
* `AlgebraicGeometry.Space.modulePasting_factors`: the application of
  `squareComparison_horizontal`, with every square comparison written out as its three factors.

## Implementation notes

The square comparisons of the rectangle

```
        g''        g'
  X'' ———→ X' ———→ X
   | f''     | f'    | f
   v         v       v
  Y'' ———→ Y' ———→ Y
         h         g
```

enter `squareComparison_horizontal` through their `.inv`, because
`AlgebraicGeometry.Space.modulePullbackCompIso` points from the composite of inverse images to
the inverse image along the composite.  The comparisons whose source is a threefold composite
are the named-composite `AlgebraicGeometry.Space.modulePullbackTriangle`.

A component of `transportNatTrans e` is `eqToHom (Functor.congr_obj e M)`, and matching two
spellings of one transport there makes the kernel whnf `(modulePullback B S hS k).obj M`, which
times out.  So the two compatibility hypotheses take their transports as arguments, and the
identity for the unprimed comparison is supplied between natural transformations; the passage to
components happens in `Stacks.CategoryTheory.congr_inv_app_of_whiskerLeft_eq` and
`Stacks.CategoryTheory.map_congr_inv_app_of_whiskerRight_eq`, where the functors are variables.
For the same reason `modulePullbackSquareComparison_hom_eq` is proved by rewriting rather than by
`rfl`.

## References

* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
* [Stacks Project, Tag 0736](https://stacks.math.columbia.edu/tag/0736)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor
open Stacks.Cohomology.DerivedBaseChangePasting (transportNatTrans transportNatTrans_app)

universe u

namespace Stacks.CategoryTheory

/-- Transporting a componentwise identity between inverse comparisons along `eqToIso`s. -/
private theorem eqToIso_trans_inv_app_comp {A B : Type*} [Category* A] [Category* B]
    {K₁ K₂ L₁ L₂ H₁ H₂ : A ⥤ B} (C₁ : K₁ ≅ H₁) (C₂ : K₂ ≅ H₂)
    (q : K₁ = K₂) (r₁ : L₁ = K₁) (r₂ : L₂ = K₂) (s : L₁ = L₂) (M : A)
    (x : H₁.obj M ⟶ H₂.obj M)
    (hM : x ≫ C₂.inv.app M = C₁.inv.app M ≫ (transportNatTrans q).app M) :
    x ≫ (eqToIso r₂ ≪≫ C₂).inv.app M =
      (eqToIso r₁ ≪≫ C₁).inv.app M ≫ (transportNatTrans s).app M := by
  simp only [Iso.trans_inv, eqToIso.inv, NatTrans.comp_app, eqToHom_app,
    transportNatTrans_app, Category.assoc] at hM ⊢
  rw [reassoc_of% hM]
  simp only [eqToHom_trans]

/-- The compatibility of a comparison with an equality of its outer functor: the variant of
`Stacks.CategoryTheory.congr_inv_app_of_eqToIso_trans` in which the identity for `C₁`, `C₂` is
an equation of natural transformations, the transport whiskered by `G`. -/
theorem congr_inv_app_of_whiskerLeft_eq {A B C : Type*}
    [Category* A] [Category* B] [Category* C]
    {G : C ⥤ A} {F₁ F₂ : A ⥤ B} {K₁ K₂ L₁ L₂ : C ⥤ B}
    (C₁ : K₁ ≅ G ⋙ F₁) (C₂ : K₂ ≅ G ⋙ F₂) (D₁ : L₁ ≅ G ⋙ F₁) (D₂ : L₂ ≅ G ⋙ F₂)
    (p : F₁ = F₂) (q : K₁ = K₂) (r₁ : L₁ = K₁) (r₂ : L₂ = K₂) (s : L₁ = L₂)
    (h₁ : D₁ = eqToIso r₁ ≪≫ C₁) (h₂ : D₂ = eqToIso r₂ ≪≫ C₂)
    (h : Functor.whiskerLeft G (transportNatTrans p) ≫ C₂.inv =
      C₁.inv ≫ transportNatTrans q)
    (M : C) :
    (transportNatTrans p).app (G.obj M) ≫ D₂.inv.app M =
      D₁.inv.app M ≫ (transportNatTrans s).app M := by
  subst h₁ h₂
  exact eqToIso_trans_inv_app_comp C₁ C₂ q r₁ r₂ s M _
    (by simpa only [NatTrans.comp_app, Functor.whiskerLeft_app] using NatTrans.congr_app h M)

/-- The compatibility of a comparison with an equality of its inner functor: the variant of
`Stacks.CategoryTheory.map_congr_inv_app_of_eqToIso_trans` in which the identity for `C₁`, `C₂`
is an equation of natural transformations, whiskered by `F` on the right. -/
theorem map_congr_inv_app_of_whiskerRight_eq {A B C : Type*}
    [Category* A] [Category* B] [Category* C]
    {G₁ G₂ : C ⥤ A} {F : A ⥤ B} {K₁ K₂ L₁ L₂ : C ⥤ B}
    (C₁ : K₁ ≅ G₁ ⋙ F) (C₂ : K₂ ≅ G₂ ⋙ F) (D₁ : L₁ ≅ G₁ ⋙ F) (D₂ : L₂ ≅ G₂ ⋙ F)
    (p : G₁ = G₂) (q : K₁ = K₂) (r₁ : L₁ = K₁) (r₂ : L₂ = K₂) (s : L₁ = L₂)
    (h₁ : D₁ = eqToIso r₁ ≪≫ C₁) (h₂ : D₂ = eqToIso r₂ ≪≫ C₂)
    (h : Functor.whiskerRight (transportNatTrans p) F ≫ C₂.inv =
      C₁.inv ≫ transportNatTrans q)
    (M : C) :
    F.map ((transportNatTrans p).app M) ≫ D₂.inv.app M =
      D₁.inv.app M ≫ (transportNatTrans s).app M := by
  subst h₁ h₂
  exact eqToIso_trans_inv_app_comp C₁ C₂ q r₁ r₂ s M _
    (by simpa only [NatTrans.comp_app, Functor.whiskerRight_app] using NatTrans.congr_app h M)

end Stacks.CategoryTheory

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The transports and the comparison, as named constants -/

section Named

variable {V W : AlgebraicSpaces B S hS}

/-- The equality of module inverse images induced by an equality of morphisms. -/
theorem modulePullbackEq {k₁ k₂ : V ⟶ W} (e : k₁ = k₂) :
    modulePullback B S hS k₁ = modulePullback B S hS k₂ :=
  congrArg (modulePullback B S hS) e

/-- The equality of inverse images along a composite induced by an equality of the inner
morphism, as a named constant. -/
theorem modulePullbackCompEqLeft {X Y Z : AlgebraicSpaces B S hS} {a₁ a₂ : X ⟶ Y} (e : a₁ = a₂)
    (b : Y ⟶ Z) :
    modulePullback B S hS (a₁ ≫ b) = modulePullback B S hS (a₂ ≫ b) :=
  congrArg (fun k : X ⟶ Y => modulePullback B S hS (k ≫ b)) e

/-- The equality of inverse images along a composite induced by an equality of the outer
morphism, as a named constant. -/
theorem modulePullbackCompEqRight {X Y Z : AlgebraicSpaces B S hS} (a : X ⟶ Y) {b₁ b₂ : Y ⟶ Z}
    (e : b₁ = b₂) :
    modulePullback B S hS (a ≫ b₁) = modulePullback B S hS (a ≫ b₂) :=
  congrArg (fun k : Y ⟶ Z => modulePullback B S hS (a ≫ k)) e

/-- The comparison of Stacks 03LU for inverse images, in the splitting direction. -/
def modulePullbackSplit {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePullback B S hS (f ≫ g) ≅
      modulePullback B S hS g ⋙ modulePullback B S hS f :=
  (modulePullbackCompIso B S hS f g).symm

/-- `AlgebraicGeometry.Space.modulePullbackSplit` read backwards is the comparison of
Stacks 03LU. -/
theorem modulePullbackSplit_inv {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (modulePullbackSplit f g).inv = (modulePullbackCompIso B S hS f g).hom := rfl

/-- The named-composite comparison `AlgebraicGeometry.Space.modulePullbackTriangle` is a
transport followed by `AlgebraicGeometry.Space.modulePullbackSplit`. -/
theorem modulePullbackTriangle_eq_split {X Y Z : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    {g : Y ⟶ Z} {k : X ⟶ Z} (hk : f ≫ g = k) :
    modulePullbackTriangle B S hS hk =
      eqToIso (modulePullbackEq hk.symm) ≪≫ modulePullbackSplit f g := rfl

/-! ### The two compatibilities between natural transformations

These are the inputs that `Stacks.CategoryTheory.congr_inv_app_of_whiskerLeft_eq` and
`Stacks.CategoryTheory.map_congr_inv_app_of_whiskerRight_eq` take.  Each carries its two
transports as arguments, equalities of inverse images implied by the equality of morphisms
`e`. -/

section Compat

variable {V W Z : AlgebraicSpaces B S hS}

/-- Compatibility of the splitting comparison with an equality of the inner morphism, between
natural transformations: `AlgebraicGeometry.Space.modulePullbackCompIso_congr_left` one level
up. -/
theorem modulePullbackSplit_congr_left_natTrans {k₁ k₂ : V ⟶ W} (e : k₁ = k₂) (a : W ⟶ Z)
    (p : modulePullback B S hS k₁ = modulePullback B S hS k₂)
    (q : modulePullback B S hS (k₁ ≫ a) = modulePullback B S hS (k₂ ≫ a)) :
    Functor.whiskerLeft (modulePullback B S hS a) (transportNatTrans p) ≫
        (modulePullbackSplit k₂ a).inv =
      (modulePullbackSplit k₁ a).inv ≫ transportNatTrans q := by
  subst e
  ext M
  simp

/-- Compatibility of the splitting comparison with an equality of the outer morphism, between
natural transformations. -/
theorem modulePullbackSplit_congr_right_natTrans (a : V ⟶ W) {k₁ k₂ : W ⟶ Z} (e : k₁ = k₂)
    (p : modulePullback B S hS k₁ = modulePullback B S hS k₂)
    (q : modulePullback B S hS (a ≫ k₁) = modulePullback B S hS (a ≫ k₂)) :
    Functor.whiskerRight (transportNatTrans p) (modulePullback B S hS a) ≫
        (modulePullbackSplit a k₂).inv =
      (modulePullbackSplit a k₁).inv ≫ transportNatTrans q := by
  subst e
  ext M
  simp

end Compat

end Named

/-! ### The square comparison -/

section Square

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X)

/-- `AlgebraicGeometry.Space.modulePullbackSquareComparison` of a commutative square is
`AlgebraicGeometry.Space.modulePullbackSquare` at the equalities `rfl` and `comm.symm`. -/
theorem modulePullbackSquareComparison_eq_square (comm : g' ≫ f = f' ≫ g) :
    modulePullbackSquareComparison f g f' g' comm =
      modulePullbackSquare B S hS (e := g') (l := f) (r := f') (q := g) rfl comm.symm := rfl

/-- The square comparison in the forward direction, written out as its three factors. -/
theorem modulePullbackSquareComparison_hom_eq (comm : g' ≫ f = f' ≫ g) :
    (modulePullbackSquareComparison f g f' g' comm).hom =
      (modulePullbackCompIso B S hS g' f).hom ≫
        transportNatTrans (modulePullbackEq comm) ≫
        (modulePullbackCompIso B S hS f' g).inv := by
  rw [modulePullbackSquareComparison, ← eqToHom_eq_transportNatTrans]
  simp

end Square

/-! ### The associativity pentagon in the splitting direction -/

section Pentagon

variable {W X Y Z : AlgebraicSpaces B S hS}

/-- The associativity pentagon of Stacks 03LU at a module, in the splitting direction: for
three composable morphisms of algebraic spaces, the two ways of splitting the inverse image
along the threefold composite into three steps agree. -/
theorem modulePullbackTriangle_hom_app_assoc
    {f : W ⟶ X} {g : X ⟶ Y} {p : Y ⟶ Z} {k : W ⟶ Y} {q : X ⟶ Z} {r : W ⟶ Z}
    (hk : f ≫ g = k) (hq : g ≫ p = q) (hr : f ≫ q = r) (hkr : k ≫ p = r)
    (M : Modules.{u, u} B S hS Z.1 Z.2) :
    (modulePullbackTriangle B S hS hkr).hom.app M ≫
        (modulePullbackTriangle B S hS hk).hom.app ((modulePullback B S hS p).obj M) =
      (modulePullbackTriangle B S hS hr).hom.app M ≫
        (modulePullback B S hS f).map ((modulePullbackTriangle B S hS hq).hom.app M) := by
  have key := NatTrans.congr_app
    (congrArg Iso.hom (modulePullbackTriangle_assoc B S hS hk hq hr hkr)) M
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.comp_id] at key
  exact key

end Pentagon

/-! ### The first of the pasting law's five hypotheses -/

section Hyp

variable {X X' X'' Y Y' Y'' : AlgebraicSpaces B S hS} (f'' : X'' ⟶ Y'') (g : Y' ⟶ Y)
    (h : Y'' ⟶ Y')
variable (f : X ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X) (g'' : X'' ⟶ X')

/-- The pentagon along the bottom of the rectangle: hypothesis `h1` of
`Stacks.Cohomology.DerivedBaseChangePasting.squareComparison_horizontal`. -/
theorem modulePasting_pentagon_bottom (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (modulePullbackCompIso B S hS f'' h).hom.app ((modulePullback B S hS g).obj M) ≫
        (modulePullbackTriangle B S hS
          (f := f'' ≫ h) (g := g) (Category.assoc f'' h g)).symm.hom.app M =
      (modulePullback B S hS f'').map
          ((modulePullbackCompIso B S hS h g).hom.app M) ≫
        (modulePullbackCompIso B S hS f'' (h ≫ g)).hom.app M := by
  simpa only [modulePullbackTriangle_rfl, Iso.symm_inv, Iso.symm_hom] using
    (modulePullbackTriangle_inv_app_assoc B S hS (f := f'') (g := h) (p := g)
    (k := f'' ≫ h) (q := h ≫ g) (r := f'' ≫ h ≫ g) rfl rfl rfl (Category.assoc f'' h g) M).symm

/-- The pentagon along the top of the rectangle: hypothesis `h2` of
`Stacks.Cohomology.DerivedBaseChangePasting.squareComparison_horizontal`. -/
theorem modulePasting_pentagon_top (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (modulePullbackCompIso B S hS g'' g').hom.app ((modulePullback B S hS f).obj M) ≫
        (modulePullbackCompIso B S hS (g'' ≫ g') f).hom.app M =
      (modulePullback B S hS g'').map ((modulePullbackCompIso B S hS g' f).hom.app M) ≫
        (modulePullbackTriangle B S hS (f := g'') (g := g' ≫ f)
          (Category.assoc g'' g' f).symm).symm.hom.app M := by
  simpa only [modulePullbackTriangle_rfl, Iso.symm_inv, Iso.symm_hom] using
    (modulePullbackTriangle_inv_app_assoc B S hS (f := g'') (g := g') (p := f)
    (k := g'' ≫ g') (q := g' ≫ f) (r := (g'' ≫ g') ≫ f) rfl rfl
    (Category.assoc g'' g' f).symm rfl M).symm

/-- The pentagon along the diagonal of the rectangle: hypothesis `h3` of
`squareComparison_horizontal`. -/
theorem modulePasting_pentagon_middle (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (modulePullbackCompIso B S hS g'' f').hom.app ((modulePullback B S hS g).obj M) ≫
        (modulePullbackTriangle B S hS (f := g'' ≫ f') (g := g)
          (Category.assoc g'' f' g)).symm.hom.app M =
      (modulePullback B S hS g'').map ((modulePullbackCompIso B S hS f' g).hom.app M) ≫
        (modulePullbackTriangle B S hS (f := g'') (g := f' ≫ g)
          (k := g'' ≫ f' ≫ g) rfl).symm.hom.app M := by
  simpa only [modulePullbackTriangle_rfl, Iso.symm_inv, Iso.symm_hom] using
    (modulePullbackTriangle_inv_app_assoc B S hS (f := g'') (g := f') (p := g)
    (k := g'' ≫ f') (q := f' ≫ g) (r := g'' ≫ f' ≫ g) rfl rfl rfl
    (Category.assoc g'' f' g) M).symm

/-! ### The two compatibility hypotheses

These are `h4` and `h5` of `squareComparison_horizontal`.  Each takes the two transports its
statement needs as arguments. -/

/-- The compatibility of the comparison with the commutativity of the right-hand square:
hypothesis `h4` of `squareComparison_horizontal`. -/
theorem modulePasting_congr_rightSquare (comm : g' ≫ f = f' ≫ g)
    (esq : modulePullback B S hS (f' ≫ g) = modulePullback B S hS (g' ≫ f))
    (eWR : modulePullback B S hS (g'' ≫ f' ≫ g) =
      modulePullback B S hS ((g'' ≫ g') ≫ f))
    (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (modulePullback B S hS g'').map ((transportNatTrans esq).app M) ≫
        (modulePullbackTriangle B S hS (f := g'') (g := g' ≫ f)
          (Category.assoc g'' g' f).symm).symm.hom.app M =
      (modulePullbackTriangle B S hS (f := g'') (g := f' ≫ g)
          (k := g'' ≫ f' ≫ g) rfl).symm.hom.app M ≫
        (transportNatTrans eWR).app M :=
  Stacks.CategoryTheory.map_congr_inv_app_of_whiskerRight_eq
    (modulePullbackSplit g'' (f' ≫ g)) (modulePullbackSplit g'' (g' ≫ f))
    (modulePullbackTriangle B S hS (f := g'') (g := f' ≫ g) (k := g'' ≫ f' ≫ g) rfl)
    (modulePullbackTriangle B S hS (f := g'') (g := g' ≫ f)
      (Category.assoc g'' g' f).symm)
    esq (modulePullbackCompEqRight g'' comm.symm) _ _ eWR
    (modulePullbackTriangle_eq_split rfl)
    (modulePullbackTriangle_eq_split (Category.assoc g'' g' f).symm)
    (modulePullbackSplit_congr_right_natTrans g'' comm.symm esq
      (modulePullbackCompEqRight g'' comm.symm))
    M

/-- The compatibility of the comparison with the commutativity of the left-hand square:
hypothesis `h5` of `squareComparison_horizontal`. -/
theorem modulePasting_congr_leftSquare (comm' : g'' ≫ f' = f'' ≫ h)
    (esq' : modulePullback B S hS (f'' ≫ h) = modulePullback B S hS (g'' ≫ f'))
    (eRW : modulePullback B S hS (f'' ≫ h ≫ g) =
      modulePullback B S hS (g'' ≫ f' ≫ g))
    (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (transportNatTrans esq').app ((modulePullback B S hS g).obj M) ≫
        (modulePullbackTriangle B S hS (f := g'' ≫ f') (g := g)
          (Category.assoc g'' f' g)).symm.hom.app M =
      (modulePullbackTriangle B S hS (f := f'' ≫ h) (g := g)
          (Category.assoc f'' h g)).symm.hom.app M ≫
        (transportNatTrans eRW).app M :=
  Stacks.CategoryTheory.congr_inv_app_of_whiskerLeft_eq
    (modulePullbackSplit (f'' ≫ h) g) (modulePullbackSplit (g'' ≫ f') g)
    (modulePullbackTriangle B S hS (f := f'' ≫ h) (g := g) (Category.assoc f'' h g))
    (modulePullbackTriangle B S hS (f := g'' ≫ f') (g := g) (Category.assoc g'' f' g))
    esq' (modulePullbackCompEqLeft comm'.symm g) _ _ eRW
    (modulePullbackTriangle_eq_split (Category.assoc f'' h g))
    (modulePullbackTriangle_eq_split (Category.assoc g'' f' g))
    (modulePullbackSplit_congr_left_natTrans comm'.symm g esq'
      (modulePullbackCompEqLeft comm'.symm g))
    M

end Hyp

/-! ### The pasting, with every comparison written out as its three factors -/

section Pasting

variable {X X' X'' Y Y' Y'' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (f'' : X'' ⟶ Y'') (g : Y' ⟶ Y) (g' : X' ⟶ X) (h : Y'' ⟶ Y') (g'' : X'' ⟶ X')

/-- The horizontal pasting of the three square comparisons of a rectangle, with every
comparison written out as its three factors. -/
theorem modulePasting_factors (comm : g' ≫ f = f' ≫ g) (comm' : g'' ≫ f' = f'' ≫ h)
    (hW : g'' ≫ f' ≫ g = (g'' ≫ g') ≫ f) (hR : f'' ≫ h ≫ g = g'' ≫ f' ≫ g)
    (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (modulePullback B S hS f'').map ((modulePullbackCompIso B S hS h g).inv.app M) ≫
        ((modulePullbackCompIso B S hS f'' h).hom.app ((modulePullback B S hS g).obj M) ≫
          (transportNatTrans
              (congrArg (fun k : X'' ⟶ Y' => modulePullback B S hS k) comm').symm).app
            ((modulePullback B S hS g).obj M) ≫
          (modulePullbackCompIso B S hS g'' f').inv.app
            ((modulePullback B S hS g).obj M)) ≫
        (modulePullback B S hS g'').map
          ((modulePullbackCompIso B S hS f' g).hom.app M ≫
            (transportNatTrans
              (congrArg (fun k : X' ⟶ Y => modulePullback B S hS k) comm).symm).app M ≫
            (modulePullbackCompIso B S hS g' f).inv.app M) ≫
        (modulePullbackCompIso B S hS g'' g').hom.app ((modulePullback B S hS f).obj M) =
      (modulePullbackCompIso B S hS f'' (h ≫ g)).hom.app M ≫
        (transportNatTrans (congrArg (fun k : X'' ⟶ Y => modulePullback B S hS k)
          (pasteBaseComm f g f' g' h f'' g'' comm comm')).symm).app M ≫
        (modulePullbackCompIso B S hS (g'' ≫ g') f).inv.app M :=
  Stacks.Cohomology.DerivedBaseChangePasting.squareComparison_horizontal
    (modulePullbackCompIso B S hS h g) (modulePullbackCompIso B S hS g'' g')
    (modulePullbackCompIso B S hS f' g) (modulePullbackCompIso B S hS g' f)
    (modulePullbackCompIso B S hS f'' h) (modulePullbackCompIso B S hS g'' f')
    (modulePullbackCompIso B S hS f'' (h ≫ g))
    (modulePullbackCompIso B S hS (g'' ≫ g') f)
    (modulePullbackTriangle B S hS (f := f'' ≫ h) (g := g) (Category.assoc f'' h g)).symm
    (modulePullbackTriangle B S hS (f := g'') (g := g' ≫ f)
      (Category.assoc g'' g' f).symm).symm
    (modulePullbackTriangle B S hS (f := g'') (g := f' ≫ g) (k := g'' ≫ f' ≫ g) rfl).symm
    (modulePullbackTriangle B S hS (f := g'' ≫ f') (g := g) (Category.assoc g'' f' g)).symm
    (congrArg (fun k : X' ⟶ Y => modulePullback B S hS k) comm).symm
    (congrArg (fun k : X'' ⟶ Y' => modulePullback B S hS k) comm').symm
    (congrArg (fun k : X'' ⟶ Y => modulePullback B S hS k)
      (pasteBaseComm f g f' g' h f'' g'' comm comm')).symm
    (modulePullbackEq hW) (modulePullbackEq hR)
    (modulePasting_pentagon_bottom f'' g h) (modulePasting_pentagon_top f g' g'')
    (modulePasting_pentagon_middle g f' g'')
    (modulePasting_congr_rightSquare g f f' g' g'' comm
      (congrArg (fun k : X' ⟶ Y => modulePullback B S hS k) comm).symm
      (modulePullbackEq hW))
    (modulePasting_congr_leftSquare f'' g h f' g'' comm'
      (congrArg (fun k : X'' ⟶ Y' => modulePullback B S hS k) comm').symm
      (modulePullbackEq hR))
    M

end Pasting

end AlgebraicGeometry.Space

end
