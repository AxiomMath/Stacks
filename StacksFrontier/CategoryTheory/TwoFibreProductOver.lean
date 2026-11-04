module

public import Mathlib.CategoryTheory.FiberedCategory.HomLift
public import StacksCore.Tactic.StacksAttribute

/-!
# The 2-fibre product of categories over a base

Fix a base category `𝒞`. Given categories `𝒳`, `𝒴`, `𝒮` over `𝒞` with structure functors
`p𝒳`, `p𝒴`, `p𝒮` and functors `F : 𝒳 ⥤ 𝒮`, `G : 𝒴 ⥤ 𝒮`, the *2-fibre product* `𝒳 ×_𝒮 𝒴` in the
(2,1)-category of categories over `𝒞` has as objects the quadruples `(U, x, y, φ)` with `U : 𝒞`,
`x` over `U`, `y` over `U`, and `φ : F x ≅ G y` an isomorphism **vertical** over `U`, i.e. lying
over `𝟙 U`. A morphism `(U, x, y, φ) ⟶ (U', x', y', φ')` is a pair `(a, b)` of morphisms of `𝒳`
and `𝒴` lying over one common morphism `U ⟶ U'` of `𝒞` and making the comparison square commute.

## Main definitions

* `CategoryTheory.TwoFibreProductOver`: the 2-fibre product `𝒳 ×_𝒮 𝒴` of categories over `𝒞`.
* `CategoryTheory.TwoFibreProductOver.structureFunctor`: its structure functor to `𝒞`.
* `CategoryTheory.TwoFibreProductOver.fst`, `CategoryTheory.TwoFibreProductOver.snd`: the
  projections to `𝒳` and `𝒴`.
* `CategoryTheory.TwoFibreProductOver.psiIso`: the 2-cell `π₁ ⋙ F ≅ π₂ ⋙ G` filling the square.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]
variable {𝒳 : Type u₂} [Category.{v₂} 𝒳]
variable {𝒴 : Type u₃} [Category.{v₃} 𝒴]
variable {𝒮 : Type u₄} [Category.{v₄} 𝒮]

/-- An object of the 2-fibre product `𝒳 ×_𝒮 𝒴` of categories over `𝒞`: a quadruple
`(U, x, y, φ)` with `U : 𝒞`, objects `x : 𝒳` and `y : 𝒴` lying over `U`, and an
isomorphism `φ : F x ≅ G y` of `𝒮` which is vertical over `U`. -/
structure TwoFibreProductOver (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒮 : 𝒮 ⥤ 𝒞)
    (F : 𝒳 ⥤ 𝒮) (G : 𝒴 ⥤ 𝒮) where
  /-- The base object `U : 𝒞`. -/
  base : 𝒞
  /-- The object `x : 𝒳` lying over `U`. -/
  x : 𝒳
  /-- The object `y : 𝒴` lying over `U`. -/
  y : 𝒴
  /-- `x` lies over `U`. -/
  hx : p𝒳.obj x = base
  /-- `y` lies over `U`. -/
  hy : p𝒴.obj y = base
  /-- The comparison isomorphism `φ : F x ≅ G y`. -/
  iso : F.obj x ≅ G.obj y
  /-- `φ` is vertical over `U`, i.e. it lies over `𝟙 U`. -/
  vertical : p𝒮.IsHomLift (𝟙 base) iso.hom

namespace TwoFibreProductOver

variable {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒮 : 𝒮 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒮} {G : 𝒴 ⥤ 𝒮}

/-- A morphism `(U, x, y, φ) ⟶ (U', x', y', φ')` of the 2-fibre product: a pair `(a, b)`
of morphisms `a : x ⟶ x'` of `𝒳` and `b : y ⟶ y'` of `𝒴` lying over one common morphism
`U ⟶ U'` of `𝒞`, making the comparison square commute. -/
@[ext]
structure Hom (P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G) where
  /-- The common base morphism `U ⟶ U'`. -/
  hbase : P.base ⟶ Q.base
  /-- The `𝒳`-component `a : x ⟶ x'`. -/
  a : P.x ⟶ Q.x
  /-- The `𝒴`-component `b : y ⟶ y'`. -/
  b : P.y ⟶ Q.y
  /-- `a` lies over the base morphism. -/
  ha : p𝒳.IsHomLift hbase a
  /-- `b` lies over the base morphism. -/
  hb : p𝒴.IsHomLift hbase b
  /-- The comparison square commutes: `φ' ∘ F a = G b ∘ φ`. -/
  w : F.map a ≫ Q.iso.hom = P.iso.hom ≫ G.map b

attribute [reassoc] Hom.w

/-- The base morphism of a morphism of the 2-fibre product is determined by its
`𝒳`-component. -/
lemma Hom.hbase_eq {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (f : Hom P Q) :
    f.hbase = eqToHom P.hx.symm ≫ p𝒳.map f.a ≫ eqToHom Q.hx := by
  have := f.ha
  rw [IsHomLift.fac' p𝒳 f.hbase f.a]
  simp

/-- Two morphisms of the 2-fibre product with the same components are equal. -/
lemma Hom.ext' {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} {f g : Hom P Q}
    (ha : f.a = g.a) (hb : f.b = g.b) : f = g :=
  Hom.ext (by rw [f.hbase_eq, g.hbase_eq, ha]) ha hb

/-- The morphism of the 2-fibre product with components `a` and `b`, over the base morphism
induced by `a`, where `base` says that `b` induces the same base morphism. -/
def Hom.mk' {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (a : P.x ⟶ Q.x) (b : P.y ⟶ Q.y)
    (base : eqToHom P.hy.symm ≫ p𝒴.map b ≫ eqToHom Q.hy
      = eqToHom P.hx.symm ≫ p𝒳.map a ≫ eqToHom Q.hx)
    (w : F.map a ≫ Q.iso.hom = P.iso.hom ≫ G.map b) : Hom P Q where
  hbase := eqToHom P.hx.symm ≫ p𝒳.map a ≫ eqToHom Q.hx
  a := a
  b := b
  ha := IsHomLift.of_fac' p𝒳 _ a P.hx Q.hx (by simp)
  hb := IsHomLift.of_fac' p𝒴 _ b P.hy Q.hy (by rw [← base]; simp)
  w := w

/-- The `𝒳`-component of `Hom.mk' a b base w` is `a`. -/
@[simp] lemma Hom.mk'_a {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (a : P.x ⟶ Q.x)
    (b : P.y ⟶ Q.y) (base) (w) : (Hom.mk' a b base w).a = a := rfl

/-- The `𝒴`-component of `Hom.mk' a b base w` is `b`. -/
@[simp] lemma Hom.mk'_b {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (a : P.x ⟶ Q.x)
    (b : P.y ⟶ Q.y) (base) (w) : (Hom.mk' a b base w).b = b := rfl

/-- The base morphism of `Hom.mk' a b base w` is the one induced by the `𝒳`-component `a`. -/
@[simp] lemma Hom.mk'_hbase {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (a : P.x ⟶ Q.x)
    (b : P.y ⟶ Q.y) (base) (w) :
    (Hom.mk' a b base w).hbase = eqToHom P.hx.symm ≫ p𝒳.map a ≫ eqToHom Q.hx := rfl

/-- The identity morphism of the 2-fibre product. -/
@[simps]
def Hom.id (P : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G) : Hom P P where
  hbase := 𝟙 P.base
  a := 𝟙 P.x
  b := 𝟙 P.y
  ha := by rw [← P.hx]; infer_instance
  hb := by rw [← P.hy]; infer_instance
  w := by simp

/-- Composition of morphisms of the 2-fibre product, componentwise. -/
@[simps]
def Hom.comp {P Q R : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (f : Hom P Q) (g : Hom Q R) :
    Hom P R where
  hbase := f.hbase ≫ g.hbase
  a := f.a ≫ g.a
  b := f.b ≫ g.b
  ha := by have := f.ha; have := g.ha; infer_instance
  hb := by have := f.hb; have := g.hb; infer_instance
  w := by simp [f.w_assoc, g.w]

/-- The 2-fibre product is a category, with componentwise identities and composition. -/
instance instCategory : Category (TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := by apply Hom.ext <;> simp
  comp_id f := by apply Hom.ext <;> simp
  assoc f g h := by apply Hom.ext <;> simp

/-- The base morphism of the identity of `P` is the identity of `P.base`. -/
@[simp] lemma id_hbase (P : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G) :
    Hom.hbase (𝟙 P) = 𝟙 P.base := rfl

/-- The `𝒳`-component of the identity of `P` is the identity of `P.x`. -/
@[simp] lemma id_a (P : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G) : Hom.a (𝟙 P) = 𝟙 P.x := rfl

/-- The `𝒴`-component of the identity of `P` is the identity of `P.y`. -/
@[simp] lemma id_b (P : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G) : Hom.b (𝟙 P) = 𝟙 P.y := rfl

/-- Composition is over the composite base morphism. -/
@[simp] lemma comp_hbase {P Q R : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (f : P ⟶ Q) (g : Q ⟶ R) :
    (f ≫ g).hbase = f.hbase ≫ g.hbase := rfl

/-- Composition is componentwise on the `𝒳`-components. -/
@[simp] lemma comp_a {P Q R : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (f : P ⟶ Q) (g : Q ⟶ R) :
    (f ≫ g).a = f.a ≫ g.a := rfl

/-- Composition is componentwise on the `𝒴`-components. -/
@[simp] lemma comp_b {P Q R : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (f : P ⟶ Q) (g : Q ⟶ R) :
    (f ≫ g).b = f.b ≫ g.b := rfl

/-- The `𝒳`-component of an `eqToHom` of the 2-fibre product is an `eqToHom`. -/
@[simp] lemma eqToHom_a {P P' : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (e : P = P') :
    (eqToHom e).a = eqToHom (congrArg TwoFibreProductOver.x e) := by subst e; rfl

/-- The `𝒴`-component of an `eqToHom` of the 2-fibre product is an `eqToHom`. -/
@[simp] lemma eqToHom_b {P P' : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (e : P = P') :
    (eqToHom e).b = eqToHom (congrArg TwoFibreProductOver.y e) := by subst e; rfl

/-- The structure functor `𝒳 ×_𝒮 𝒴 ⥤ 𝒞` of the 2-fibre product as a category over `𝒞`:
`(U, x, y, φ) ↦ U` and `(a, b) ↦` their common base morphism. -/
@[simps]
def structureFunctor (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒮 : 𝒮 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒮) (G : 𝒴 ⥤ 𝒮) :
    TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G ⥤ 𝒞 where
  obj P := P.base
  map f := f.hbase

/-- The first projection `π₁ : 𝒳 ×_𝒮 𝒴 ⥤ 𝒳`, `(U, x, y, φ) ↦ x`, `(a, b) ↦ a`. -/
@[simps]
def fst (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒮 : 𝒮 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒮) (G : 𝒴 ⥤ 𝒮) :
    TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G ⥤ 𝒳 where
  obj P := P.x
  map f := f.a

/-- The second projection `π₂ : 𝒳 ×_𝒮 𝒴 ⥤ 𝒴`, `(U, x, y, φ) ↦ y`, `(a, b) ↦ b`. -/
@[simps]
def snd (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒮 : 𝒮 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒮) (G : 𝒴 ⥤ 𝒮) :
    TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G ⥤ 𝒴 where
  obj P := P.y
  map f := f.b

/-- The first projection is strictly over `𝒞`. -/
@[stacks 0040]
lemma fst_comp_eq : fst p𝒳 p𝒴 p𝒮 F G ⋙ p𝒳 = structureFunctor p𝒳 p𝒴 p𝒮 F G :=
  CategoryTheory.Functor.ext (fun P => P.hx) fun _ _ f => by
    have := f.ha
    exact IsHomLift.fac' p𝒳 f.hbase f.a

/-- The second projection is strictly over `𝒞`. -/
@[stacks 0040]
lemma snd_comp_eq : snd p𝒳 p𝒴 p𝒮 F G ⋙ p𝒴 = structureFunctor p𝒳 p𝒴 p𝒮 F G :=
  CategoryTheory.Functor.ext (fun P => P.hy) fun _ _ f => by
    have := f.hb
    exact IsHomLift.fac' p𝒴 f.hbase f.b

/-- The 2-cell `ψ : π₁ ⋙ F ≅ π₂ ⋙ G` filling the square, with component at
`(U, x, y, φ)` the comparison isomorphism `φ` itself. -/
@[simps!, stacks 0040]
def psiIso (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒮 : 𝒮 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒮) (G : 𝒴 ⥤ 𝒮) :
    (fst p𝒳 p𝒴 p𝒮 F G ⋙ F) ≅ (snd p𝒳 p𝒴 p𝒮 F G ⋙ G) :=
  NatIso.ofComponents (fun P => P.iso) fun f => f.w

/-- The underlying 2-cell `ψ : π₁ ⋙ F ⟶ π₂ ⋙ G`. -/
def psi (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒮 : 𝒮 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒮) (G : 𝒴 ⥤ 𝒮) :
    (fst p𝒳 p𝒴 p𝒮 F G ⋙ F) ⟶ (snd p𝒳 p𝒴 p𝒮 F G ⋙ G) :=
  (psiIso p𝒳 p𝒴 p𝒮 F G).hom

/-- The component of `ψ` at `(U, x, y, φ)` is the comparison isomorphism `φ`. -/
@[simp] lemma psi_app (P : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G) :
    (psi p𝒳 p𝒴 p𝒮 F G).app P = P.iso.hom := rfl

/-- Every component of the 2-cell `ψ` is vertical over `𝒞`: it lies over an identity. -/
@[stacks 0040]
lemma psiIso_hom_vertical (P : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G) :
    p𝒮.IsHomLift (𝟙 P.base) ((psiIso p𝒳 p𝒴 p𝒮 F G).hom.app P) :=
  P.vertical

/-- Every component of the inverse 2-cell `ψ⁻¹` is vertical over `𝒞` as well. -/
lemma psiIso_inv_vertical (P : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G) :
    p𝒮.IsHomLift (𝟙 P.base) ((psiIso p𝒳 p𝒴 p𝒮 F G).inv.app P) := by
  have := P.vertical
  exact inferInstanceAs (p𝒮.IsHomLift (𝟙 P.base) P.iso.inv)

end TwoFibreProductOver

end CategoryTheory
