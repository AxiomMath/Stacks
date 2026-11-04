module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Fibres of a 2-fibre product over a base (Stacks 02XI)

For morphisms of categories over a fixed base category `C`, the fibre category of the 2-fibre
product taken over `C` at an object `U` is canonically isomorphic to the 2-fibre product, of plain
categories, of the fibre categories.

A *category over `C`* is a category `X` with a structure functor `pX : X ⥤ C`, and a *morphism of
categories over `C`* from `(X, pX)` to `(S, pS)` is a functor `F : X ⥤ S` with `F ⋙ pS = pX`. The
fibre category `X_U` of Definition 032B is Mathlib's `CategoryTheory.Functor.Fiber pX U`: its
objects are the `x : X` with `pX x = U`, and its morphisms are the `φ` in `X` with
`pX.IsHomLift (𝟙 U) φ`. A morphism of categories over `C` restricts to a functor
`X_U ⥤ S_U` on fibres, which is `Functor.fiberMap` below. The 2-fibre product of plain categories
is Mathlib's `CategoryTheory.Limits.CategoricalPullback`.

The 2-fibre product of categories *over `C`* is not in Mathlib, so it is defined here as
`CategoricalPullbackOver`: an object is a quadruple `(U, x, y, f)` with `U : C`, with `x : X` and
`y : Y` lying over `U`, and with `f : F x ≅ G y` an isomorphism *in the fibre category `S_U`* —
which is encoded as an isomorphism `f` in `S` together with `pS.IsHomLift (𝟙 U) f.hom`. A morphism
is a pair `(a, b)` inducing the *same* morphism of `C` (the field `base_eq`) and making the square
`G b ∘ f = f' ∘ F a` commute. Note that this relative construction is genuinely different from the
absolute `CategoricalPullback F G`, whose objects carry an arbitrary isomorphism of `S`.

The two canonical functors `toFiberPullback` and `ofFiberPullback` are mutually inverse, so the
comparison is an isomorphism of categories, not merely an equivalence.

## Main definitions

* `CategoryTheory.Functor.fiberMap`: the functor `X_U ⥤ S_U` induced on fibres by a morphism of
  categories over `C`.
* `CategoryTheory.Limits.CategoricalPullbackOver`: the 2-fibre product of categories over `C`,
  with its structure functor `CategoricalPullbackOver.structureFunctor` to `C`.
* `CategoryTheory.Limits.CategoricalPullbackOver.toFiberPullback` and
  `CategoryTheory.Limits.CategoricalPullbackOver.ofFiberPullback`: the comparison functors
  between the fibre `(X ×_S Y)_U` and the 2-fibre product `X_U ×_{S_U} Y_U` of the fibres.

## Main results

* `CategoryTheory.Limits.CategoricalPullbackOver.toFiberPullback_comp_ofFiberPullback` and
  `CategoryTheory.Limits.CategoricalPullbackOver.ofFiberPullback_comp_toFiberPullback`: the two
  comparison functors are mutually inverse.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} [Category.{v₁} C]
variable {X : Type u₂} [Category.{v₂} X]
variable {Y : Type u₃} [Category.{v₃} Y]
variable {S : Type u₄} [Category.{v₄} S]
variable (pX : X ⥤ C) (pY : Y ⥤ C) (pS : S ⥤ C)
variable (F : X ⥤ S) (G : Y ⥤ S)

namespace Functor

/-- For `F` a morphism of categories over `C` (`hf : F ⋙ pS = pX`), an object `x` of the fibre
`X_U` is sent to an object of `S_U`: indeed `pS (F x) = pX x = U`. -/
theorem fiberMap_obj_eq (hf : F ⋙ pS = pX) (U : C) (x : pX.Fiber U) :
    pS.obj (F.obj x.1) = U := by
  have : (F ⋙ pS).obj x.1 = pX.obj x.1 := by rw [hf]
  simpa using this.trans x.2

/-- `IsHomLift` is transported through a functor `F`: if `φ` is a `(F ⋙ pS)`-lift of `𝟙 U`, then
`F.map φ` is a `pS`-lift of `𝟙 U`. -/
theorem isHomLift_map_of_comp {a b : X} (φ : a ⟶ b) {U : C}
    (hφ : (F ⋙ pS).IsHomLift (𝟙 U) φ) : pS.IsHomLift (𝟙 U) (F.map φ) :=
  IsHomLift.of_fac' pS (𝟙 U) (F.map φ)
    (IsHomLift.domain_eq (F ⋙ pS) (𝟙 U) φ) (IsHomLift.codomain_eq (F ⋙ pS) (𝟙 U) φ)
    (IsHomLift.fac' (F ⋙ pS) (𝟙 U) φ)

/-- The functor `F_U : X_U ⥤ S_U` induced on fibre categories by a morphism
`F : (X, pX) → (S, pS)` of categories over `C`; it is `F` on objects and on morphisms. -/
def fiberMap (hf : F ⋙ pS = pX) (U : C) : pX.Fiber U ⥤ pS.Fiber U where
  obj x := ⟨F.obj x.1, fiberMap_obj_eq pX pS F hf U x⟩
  map {x y} φ := ⟨F.map φ.1, isHomLift_map_of_comp pS F φ.1 (by rw [hf]; exact φ.2)⟩
  map_id x := Subtype.ext (F.map_id _)
  map_comp {x y z} φ ψ := Subtype.ext (F.map_comp _ _)

/-- `fiberMap` acts on objects as `F` does: the underlying object of `F_U x` is `F x`. -/
@[simp]
theorem fiberMap_obj_coe (hf : F ⋙ pS = pX) (U : C) (x : pX.Fiber U) :
    ((fiberMap pX pS F hf U).obj x).1 = F.obj x.1 := rfl

/-- `fiberMap` acts on morphisms as `F` does: the underlying morphism of `F_U φ` is `F φ`. -/
@[simp]
theorem fiberMap_map_coe (hf : F ⋙ pS = pX) (U : C) {x y : pX.Fiber U} (φ : x ⟶ y) :
    ((fiberMap pX pS F hf U).map φ).1 = F.map φ.1 := rfl

/-- Build an isomorphism in the fibre category `S_U` from an isomorphism in `S` whose `hom` lifts
`𝟙 U`. -/
def fiberIsoOfLift {U : C} {x y : pS.Fiber U} (f : x.1 ≅ y.1)
    (hf : pS.IsHomLift (𝟙 U) f.hom) : x ≅ y where
  hom := ⟨f.hom, hf⟩
  inv := ⟨f.inv, IsHomLift.lift_id_inv pS U f⟩
  hom_inv_id := Subtype.ext f.hom_inv_id
  inv_hom_id := Subtype.ext f.inv_hom_id

/-- The underlying morphism of `fiberIsoOfLift`, in `S`, is the given isomorphism's `hom`. -/
@[simp] theorem fiberIsoOfLift_hom_coe {U : C} {x y : pS.Fiber U} (f : x.1 ≅ y.1)
    (hf : pS.IsHomLift (𝟙 U) f.hom) : (fiberIsoOfLift pS f hf).hom.1 = f.hom := rfl

/-- A morphism of the fibre category `X_U` has `pX`-image the canonical `eqToHom`. -/
theorem fiber_map_eq_eqToHom {U : C} {a a' : pX.Fiber U} (u : a ⟶ a') :
    pX.map u.1 = eqToHom a.2 ≫ eqToHom a'.2.symm := by
  have : pX.IsHomLift (𝟙 U) u.1 := u.2
  rw [IsHomLift.fac' pX (𝟙 U) u.1]; simp

end Functor

namespace Limits

open _root_.CategoryTheory.Functor

/-- An object of the 2-fibre product `X ×_S Y` of categories *over* `C`: a base object
`base : C`, objects `fst : X` and `snd : Y` lying over `base`, and an isomorphism
`F fst ≅ G snd` lying in the fibre category `S_base`, i.e. whose `hom` is a `pS`-lift of
`𝟙 base`. -/
structure CategoricalPullbackOver where
  /-- the common image `U` in `C`. -/
  base : C
  /-- the `X`-component `x`. -/
  fst : X
  /-- the `Y`-component `y`. -/
  snd : Y
  /-- `fst` lies over `base`. -/
  hfst : pX.obj fst = base
  /-- `snd` lies over `base`. -/
  hsnd : pY.obj snd = base
  /-- the isomorphism `F fst ≅ G snd` in `S`. -/
  iso : F.obj fst ≅ G.obj snd
  /-- the isomorphism lies in the fibre category `S_base`. -/
  iso_lift : pS.IsHomLift (𝟙 base) iso.hom

variable {pX pY pS F G}

namespace CategoricalPullbackOver

/-- A morphism of `CategoricalPullbackOver` from `(U, x, y, f)` to `(U', x', y', f')` is a pair
`(a, b)` of morphisms of `X` and `Y` inducing the same morphism of `C` and making the square
`G b ∘ f = f' ∘ F a` commute in `S`. -/
structure Hom (P Q : CategoricalPullbackOver pX pY pS F G) where
  /-- the `X`-component `a : x ⟶ x'`. -/
  fst : P.fst ⟶ Q.fst
  /-- the `Y`-component `b : y ⟶ y'`. -/
  snd : P.snd ⟶ Q.snd
  /-- `a` and `b` induce the same morphism `base ⟶ base'` of `C`. -/
  base_eq : eqToHom P.hfst.symm ≫ pX.map fst ≫ eqToHom Q.hfst =
            eqToHom P.hsnd.symm ≫ pY.map snd ≫ eqToHom Q.hsnd
  /-- the commuting square `G b ∘ f = f' ∘ F a` in `S`. -/
  w : F.map fst ≫ Q.iso.hom = P.iso.hom ≫ G.map snd

attribute [reassoc] Hom.w

namespace Hom

/-- A morphism is determined by its two components. -/
@[ext]
theorem ext {P Q : CategoricalPullbackOver pX pY pS F G} {f g : Hom P Q}
    (h₁ : f.fst = g.fst) (h₂ : f.snd = g.snd) : f = g := by
  cases f; cases g; congr

/-- The identity morphism. -/
def id (P : CategoricalPullbackOver pX pY pS F G) : Hom P P where
  fst := 𝟙 P.fst
  snd := 𝟙 P.snd
  base_eq := by simp
  w := by simp

/-- Composition of morphisms. -/
def comp {P Q R : CategoricalPullbackOver pX pY pS F G} (f : Hom P Q) (g : Hom Q R) :
    Hom P R where
  fst := f.fst ≫ g.fst
  snd := f.snd ≫ g.snd
  base_eq := by
    have hf' := f.base_eq
    have hg' := g.base_eq
    simp only [Functor.map_comp, Category.assoc]
    have key : eqToHom P.hfst.symm ≫ pX.map f.fst ≫ pX.map g.fst ≫ eqToHom R.hfst =
        (eqToHom P.hfst.symm ≫ pX.map f.fst ≫ eqToHom Q.hfst) ≫
          (eqToHom Q.hfst.symm ≫ pX.map g.fst ≫ eqToHom R.hfst) := by
      simp
    have keyY : eqToHom P.hsnd.symm ≫ pY.map f.snd ≫ pY.map g.snd ≫ eqToHom R.hsnd =
        (eqToHom P.hsnd.symm ≫ pY.map f.snd ≫ eqToHom Q.hsnd) ≫
          (eqToHom Q.hsnd.symm ≫ pY.map g.snd ≫ eqToHom R.hsnd) := by
      simp
    rw [key, keyY, hf', hg']
  w := by simp [g.w, f.w_assoc]

end Hom

/-- The category structure on the 2-fibre product over `C`, with `Hom.id` as identities and
`Hom.comp` as composition. -/
instance category : Category (CategoricalPullbackOver pX pY pS F G) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := by apply Hom.ext <;> simp [Hom.comp, Hom.id]
  comp_id f := by apply Hom.ext <;> simp [Hom.comp, Hom.id]
  assoc f g h := by apply Hom.ext <;> simp [Hom.comp]

/-- The `X`-component of an identity morphism is an identity. -/
@[simp] theorem id_fst (P : CategoricalPullbackOver pX pY pS F G) :
    (𝟙 P : Hom P P).fst = 𝟙 P.fst := rfl

/-- The `Y`-component of an identity morphism is an identity. -/
@[simp] theorem id_snd (P : CategoricalPullbackOver pX pY pS F G) :
    (𝟙 P : Hom P P).snd = 𝟙 P.snd := rfl

/-- Composition is computed on `X`-components by composing them. -/
@[simp] theorem comp_fst {P Q R : CategoricalPullbackOver pX pY pS F G} (f : P ⟶ Q) (g : Q ⟶ R) :
    (f ≫ g).fst = f.fst ≫ g.fst := rfl

/-- Composition is computed on `Y`-components by composing them. -/
@[simp] theorem comp_snd {P Q R : CategoricalPullbackOver pX pY pS F G} (f : P ⟶ Q) (g : Q ⟶ R) :
    (f ≫ g).snd = f.snd ≫ g.snd := rfl

/-- The structure functor of `X ×_S Y` over `C`, sending `(U, x, y, f)` to `U`. -/
@[implicit_reducible]
def structureFunctor : CategoricalPullbackOver pX pY pS F G ⥤ C where
  obj P := P.base
  map {P Q} f := eqToHom P.hfst.symm ≫ pX.map f.fst ≫ eqToHom Q.hfst
  map_id P := by simp
  map_comp {P Q R} f g := by simp

/-- The structure functor sends an object to its base object. -/
@[simp] theorem structureFunctor_obj (P : CategoricalPullbackOver pX pY pS F G) :
    structureFunctor.obj P = P.base := rfl

/-- The structure functor sends a morphism to the image of its `X`-component, conjugated by the
identifications `pX fst = base`. -/
@[simp] theorem structureFunctor_map {P Q : CategoricalPullbackOver pX pY pS F G} (f : P ⟶ Q) :
    structureFunctor.map f = eqToHom P.hfst.symm ≫ pX.map f.fst ≫ eqToHom Q.hfst := rfl

/-- The `fst` component of an `eqToHom` is an `eqToHom`. -/
@[simp] theorem eqToHom_fst {P Q : CategoricalPullbackOver pX pY pS F G} (h : P = Q) :
    (eqToHom h : P ⟶ Q).fst = eqToHom (by subst h; rfl) := by subst h; rfl

/-- The `snd` component of an `eqToHom` is an `eqToHom`. -/
@[simp] theorem eqToHom_snd {P Q : CategoricalPullbackOver pX pY pS F G} (h : P = Q) :
    (eqToHom h : P ⟶ Q).snd = eqToHom (by subst h; rfl) := by subst h; rfl

end CategoricalPullbackOver

variable (pX pY pS F G)

open CategoricalPullbackOver

namespace CategoricalPullbackOver

/-- From a `structureFunctor`-lift of `𝟙 U`, the `X`-component lifts `𝟙 U`. -/
theorem isHomLift_fst {P Q : CategoricalPullbackOver pX pY pS F G}
    (φ : P ⟶ Q) {U : C} (hφ : (CategoricalPullbackOver.structureFunctor (pX := pX) (pY := pY)
      (pS := pS) (F := F) (G := G)).IsHomLift (𝟙 U) φ) :
    pX.IsHomLift (𝟙 U) φ.fst := by
  have hP : P.base = U := by
    have := IsHomLift.domain_eq (structureFunctor (F := F) (G := G)) (𝟙 U) φ
    simpa [structureFunctor] using this
  have hQ : Q.base = U := by
    have := IsHomLift.codomain_eq (structureFunctor (F := F) (G := G)) (𝟙 U) φ
    simpa [structureFunctor] using this
  have hfac := IsHomLift.fac (structureFunctor (F := F) (G := G)) (𝟙 U) φ
  apply IsHomLift.of_fac' pX (𝟙 U) φ.fst (P.hfst.trans hP) (Q.hfst.trans hQ)
  rw [structureFunctor_map] at hfac
  rw [hfac]
  simp

/-- From a `structureFunctor`-lift of `𝟙 U`, the `Y`-component lifts `𝟙 U`. -/
theorem isHomLift_snd {P Q : CategoricalPullbackOver pX pY pS F G}
    (φ : P ⟶ Q) {U : C} (hφ : (CategoricalPullbackOver.structureFunctor (pX := pX) (pY := pY)
      (pS := pS) (F := F) (G := G)).IsHomLift (𝟙 U) φ) :
    pY.IsHomLift (𝟙 U) φ.snd := by
  have hfst : pX.IsHomLift (𝟙 U) φ.fst := isHomLift_fst pX pY pS F G φ hφ
  have hP : P.base = U := P.hfst.symm.trans (IsHomLift.domain_eq pX (𝟙 U) φ.fst)
  have hQ : Q.base = U := Q.hfst.symm.trans (IsHomLift.codomain_eq pX (𝟙 U) φ.fst)
  have hfacX := IsHomLift.fac pX (𝟙 U) φ.fst
  apply IsHomLift.of_fac' pY (𝟙 U) φ.snd (P.hsnd.trans hP) (Q.hsnd.trans hQ)
  have hbe := φ.base_eq
  have hsolveY : pY.map φ.snd = eqToHom P.hsnd ≫ (eqToHom P.hsnd.symm ≫ pY.map φ.snd ≫ eqToHom
      Q.hsnd) ≫ eqToHom Q.hsnd.symm := by simp
  rw [hsolveY, ← hbe, hfacX]
  simp [eqToHom_trans]

/-- **Stacks 02XI.** The canonical functor `(X ×_S Y)_U ⥤ X_U ×_{S_U} Y_U`, sending
`(U, x, y, f)` to `(x, y, f)` and `(a, b)` to `(a, b)`. -/
@[stacks 02XI, implicit_reducible]
def toFiberPullback (hf : F ⋙ pS = pX) (hg : G ⋙ pS = pY) (U : C) :
    (CategoricalPullbackOver.structureFunctor (pX := pX) (pY := pY) (pS := pS) (F := F)
      (G := G)).Fiber U ⥤
    CategoricalPullback (Functor.fiberMap pX pS F hf U) (Functor.fiberMap pY pS G hg U) where
  obj P :=
    { fst := ⟨P.1.fst, P.1.hfst.trans P.2⟩
      snd := ⟨P.1.snd, P.1.hsnd.trans P.2⟩
      iso := Functor.fiberIsoOfLift pS P.1.iso (by
        have hb : P.1.base = U := P.2
        have := P.1.iso_lift; rw [hb] at this; exact this) }
  map {P Q} φ :=
    { fst := ⟨φ.1.fst, isHomLift_fst pX pY pS F G φ.1 φ.2⟩
      snd := ⟨φ.1.snd, isHomLift_snd pX pY pS F G φ.1 φ.2⟩
      w := Subtype.ext φ.1.w }
  map_id P := by
    apply CategoricalPullback.Hom.ext <;> apply Subtype.ext <;> rfl
  map_comp {P Q R} φ ψ := by
    apply CategoricalPullback.Hom.ext <;> apply Subtype.ext <;> rfl

/-- **Stacks 02XI.** The canonical functor `X_U ×_{S_U} Y_U ⥤ (X ×_S Y)_U` inverse to
`toFiberPullback`, sending `(x, y, f)` to `(U, x, y, f)` and `(a, b)` to `(a, b)`. -/
@[stacks 02XI, implicit_reducible]
def ofFiberPullback (hf : F ⋙ pS = pX) (hg : G ⋙ pS = pY) (U : C) :
    CategoricalPullback (Functor.fiberMap pX pS F hf U) (Functor.fiberMap pY pS G hg U) ⥤
    (CategoricalPullbackOver.structureFunctor (pX := pX) (pY := pY) (pS := pS) (F := F)
      (G := G)).Fiber U where
  obj T :=
    ⟨{ base := U
       fst := T.fst.1
       snd := T.snd.1
       hfst := T.fst.2
       hsnd := T.snd.2
       iso := { hom := T.iso.hom.1, inv := T.iso.inv.1,
                hom_inv_id := congrArg Subtype.val T.iso.hom_inv_id
                inv_hom_id := congrArg Subtype.val T.iso.inv_hom_id }
       iso_lift := T.iso.hom.2 }, rfl⟩
  map {T T'} m :=
    ⟨{ fst := m.fst.1
       snd := m.snd.1
       base_eq := by
         rw [Functor.fiber_map_eq_eqToHom pX m.fst, Functor.fiber_map_eq_eqToHom pY m.snd]; simp
       w := congrArg Subtype.val m.w }, by
      apply IsHomLift.of_fac' _ (𝟙 U) _ rfl rfl
      rw [structureFunctor_map, Functor.fiber_map_eq_eqToHom pX m.fst]
      simp⟩
  map_id T := by apply Subtype.ext; apply CategoricalPullbackOver.Hom.ext <;> rfl
  map_comp {T T' T''} m m' := by
    apply Subtype.ext; apply CategoricalPullbackOver.Hom.ext <;> rfl

/-! ### The explicit formulas for the two comparison functors -/

/-- `toFiberPullback` keeps the `X`-component of an object unchanged. -/
@[simp] theorem toFiberPullback_obj_fst (hf : F ⋙ pS = pX) (hg : G ⋙ pS = pY) (U : C)
    (P : (CategoricalPullbackOver.structureFunctor (pX := pX) (pY := pY) (pS := pS)
      (F := F) (G := G)).Fiber U) :
    ((toFiberPullback pX pY pS F G hf hg U).obj P).fst.1 = P.1.fst := rfl

/-- `toFiberPullback` keeps the `Y`-component of an object unchanged. -/
@[simp] theorem toFiberPullback_obj_snd (hf : F ⋙ pS = pX) (hg : G ⋙ pS = pY) (U : C)
    (P : (CategoricalPullbackOver.structureFunctor (pX := pX) (pY := pY) (pS := pS)
      (F := F) (G := G)).Fiber U) :
    ((toFiberPullback pX pY pS F G hf hg U).obj P).snd.1 = P.1.snd := rfl

/-- `toFiberPullback` keeps the gluing isomorphism unchanged; only its ambient category
changes, from `S` to the fibre `S_U`. -/
@[simp] theorem toFiberPullback_obj_iso (hf : F ⋙ pS = pX) (hg : G ⋙ pS = pY) (U : C)
    (P : (CategoricalPullbackOver.structureFunctor (pX := pX) (pY := pY) (pS := pS)
      (F := F) (G := G)).Fiber U) :
    ((toFiberPullback pX pY pS F G hf hg U).obj P).iso.hom.1 = P.1.iso.hom := rfl

/-- `toFiberPullback` keeps the `X`-component of a morphism unchanged. -/
@[simp] theorem toFiberPullback_map_fst (hf : F ⋙ pS = pX) (hg : G ⋙ pS = pY) (U : C)
    {P Q : (CategoricalPullbackOver.structureFunctor (pX := pX) (pY := pY) (pS := pS)
      (F := F) (G := G)).Fiber U} (φ : P ⟶ Q) :
    ((toFiberPullback pX pY pS F G hf hg U).map φ).fst.1 = φ.1.fst := rfl

/-- `toFiberPullback` keeps the `Y`-component of a morphism unchanged. -/
@[simp] theorem toFiberPullback_map_snd (hf : F ⋙ pS = pX) (hg : G ⋙ pS = pY) (U : C)
    {P Q : (CategoricalPullbackOver.structureFunctor (pX := pX) (pY := pY) (pS := pS)
      (F := F) (G := G)).Fiber U} (φ : P ⟶ Q) :
    ((toFiberPullback pX pY pS F G hf hg U).map φ).snd.1 = φ.1.snd := rfl

/-- `ofFiberPullback` reinstates the base object as the literal `U`. -/
@[simp] theorem ofFiberPullback_obj_base (hf : F ⋙ pS = pX) (hg : G ⋙ pS = pY) (U : C)
    (T : CategoricalPullback (Functor.fiberMap pX pS F hf U) (Functor.fiberMap pY pS G hg U)) :
    ((ofFiberPullback pX pY pS F G hf hg U).obj T).1.base = U := rfl

/-- `ofFiberPullback` keeps the `X`-component of an object unchanged. -/
@[simp] theorem ofFiberPullback_obj_fst (hf : F ⋙ pS = pX) (hg : G ⋙ pS = pY) (U : C)
    (T : CategoricalPullback (Functor.fiberMap pX pS F hf U) (Functor.fiberMap pY pS G hg U)) :
    ((ofFiberPullback pX pY pS F G hf hg U).obj T).1.fst = T.fst.1 := rfl

/-- `ofFiberPullback` keeps the `Y`-component of an object unchanged. -/
@[simp] theorem ofFiberPullback_obj_snd (hf : F ⋙ pS = pX) (hg : G ⋙ pS = pY) (U : C)
    (T : CategoricalPullback (Functor.fiberMap pX pS F hf U) (Functor.fiberMap pY pS G hg U)) :
    ((ofFiberPullback pX pY pS F G hf hg U).obj T).1.snd = T.snd.1 := rfl

/-- `ofFiberPullback` keeps the gluing isomorphism unchanged, reading it in `S` rather than in
the fibre `S_U`. -/
@[simp] theorem ofFiberPullback_obj_iso (hf : F ⋙ pS = pX) (hg : G ⋙ pS = pY) (U : C)
    (T : CategoricalPullback (Functor.fiberMap pX pS F hf U) (Functor.fiberMap pY pS G hg U)) :
    ((ofFiberPullback pX pY pS F G hf hg U).obj T).1.iso.hom = T.iso.hom.1 := rfl

/-- `ofFiberPullback` keeps the `X`-component of a morphism unchanged. -/
@[simp] theorem ofFiberPullback_map_fst (hf : F ⋙ pS = pX) (hg : G ⋙ pS = pY) (U : C)
    {T T' : CategoricalPullback (Functor.fiberMap pX pS F hf U) (Functor.fiberMap pY pS G hg U)}
    (m : T ⟶ T') : ((ofFiberPullback pX pY pS F G hf hg U).map m).1.fst = m.fst.1 := rfl

/-- `ofFiberPullback` keeps the `Y`-component of a morphism unchanged. -/
@[simp] theorem ofFiberPullback_map_snd (hf : F ⋙ pS = pX) (hg : G ⋙ pS = pY) (U : C)
    {T T' : CategoricalPullback (Functor.fiberMap pX pS F hf U) (Functor.fiberMap pY pS G hg U)}
    (m : T ⟶ T') : ((ofFiberPullback pX pY pS F G hf hg U).map m).1.snd = m.snd.1 := rfl

/-- The underlying morphism of a composite in a `structureFunctor`-fibre is the composite of the
underlying morphisms. -/
theorem fiber_coe_comp {U : C}
    {A B D : (CategoricalPullbackOver.structureFunctor (pX := pX) (pY := pY)
      (pS := pS) (F := F) (G := G)).Fiber U} (g : A ⟶ B) (k : B ⟶ D) :
    ((g ≫ k).1 : A.1 ⟶ D.1) = g.1 ≫ k.1 := rfl

/-- The underlying morphism of an `eqToHom` in a `structureFunctor`-fibre is an `eqToHom`. -/
theorem fiber_coe_eqToHom {U : C}
    {A B : (CategoricalPullbackOver.structureFunctor (pX := pX) (pY := pY)
      (pS := pS) (F := F) (G := G)).Fiber U} (e : A = B) :
    ((eqToHom e : A ⟶ B).1 : A.1 ⟶ B.1) = eqToHom (congrArg Subtype.val e) := by
  cases e; rfl

/-- **Stacks 02XI.** Composing the comparison functor with its inverse gives the identity on the
fibre `(X ×_S Y)_U`. -/
@[stacks 02XI]
theorem toFiberPullback_comp_ofFiberPullback (hf : F ⋙ pS = pX) (hg : G ⋙ pS = pY) (U : C) :
    toFiberPullback pX pY pS F G hf hg U ⋙ ofFiberPullback pX pY pS F G hf hg U = 𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun P => ?_) (fun P Q φ => ?_)
  · obtain ⟨P, hP⟩ := P
    cases hP
    rfl
  · apply Subtype.ext
    apply CategoricalPullbackOver.Hom.ext <;> simp [fiber_coe_comp, fiber_coe_eqToHom]

/-- **Stacks 02XI.** Composing the inverse comparison functor with the comparison functor gives
the identity on `X_U ×_{S_U} Y_U`. Together with
`toFiberPullback_comp_ofFiberPullback` this says the fibre of the 2-fibre product over `C` at `U`
is *isomorphic*, not merely equivalent, to the 2-fibre product of the fibres. -/
@[stacks 02XI]
theorem ofFiberPullback_comp_toFiberPullback (hf : F ⋙ pS = pX) (hg : G ⋙ pS = pY) (U : C) :
    ofFiberPullback pX pY pS F G hf hg U ⋙ toFiberPullback pX pY pS F G hf hg U = 𝟭 _ :=
  Functor.hext (fun _ => rfl) fun _ _ _ => HEq.rfl

end CategoricalPullbackOver

end Limits

end CategoryTheory
