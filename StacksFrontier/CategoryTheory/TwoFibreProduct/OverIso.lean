module

public import StacksFrontier.CategoryTheory.FibredOneMorphism
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverBase

/-!
# Isomorphisms and verticality in the 2-fibre product over a base

Fix a base category `C` and a cospan `F : X ⥤ S`, `G : Y ⥤ S` of categories over `C`. The
2-fibre product over `C` of Stacks 0040 is `CategoryTheory.TwoFibreProductOver`; a morphism of
it is a pair of morphisms of the two factors lying over one common morphism of `C`. This file
records the two basic facts about that description which every comparison of 2-fibre products
over a base needs: how to build an isomorphism from isomorphisms of the components, and that a
morphism lies over a morphism of `C` exactly when its components do.

The base-compatibility condition of a morphism is an equation between composites of `eqToHom`s
and the images of the components; `CategoryTheory.TwoFibreProductOver.isoMkVertical` is the
form in which it is discharged in practice, from verticality of the two components, and
`CategoryTheory.TwoFibreProductOver.eqToHom_comp_eq` is the elementary fact about `eqToHom`
that makes the bookkeeping go through.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.isoMk`: an isomorphism of the 2-fibre product from
  isomorphisms of the two components and the base compatibility.
* `CategoryTheory.TwoFibreProductOver.isoMkVertical`: the same from two *vertical*
  isomorphisms, the base compatibility then being automatic.

## Main results

* `CategoryTheory.TwoFibreProductOver.eqToHom_comp_eq`: any two composites of `eqToHom`s
  between the same objects agree.
* `CategoryTheory.TwoFibreProductOver.structureFunctor_isHomLift`,
  `CategoryTheory.TwoFibreProductOver.isHomLift_a` and
  `CategoryTheory.TwoFibreProductOver.isHomLift_b`: a morphism of the 2-fibre product lies over
  a morphism of `C` if and only if its two components do.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.TwoFibreProductOver

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

attribute [local implicit_reducible] fst snd structureFunctor

/-- Any two composites of `eqToHom`s between the same objects agree. -/
theorem eqToHom_comp_eq {D : Type u₁} [Category.{v₁} D] {A M N B : D} (h₁ : A = M)
    (h₂ : M = B) (h₃ : A = N) (h₄ : N = B) :
    eqToHom h₁ ≫ eqToHom h₂ = eqToHom h₃ ≫ eqToHom h₄ := by
  cases h₁
  cases h₂
  cases h₃
  simp
section Iso

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴] {𝒮 : Type u₄} [Category.{v₄} 𝒮]
  {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒮 : 𝒮 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒮} {G : 𝒴 ⥤ 𝒮}

/-- An isomorphism of the 2-fibre product built from isomorphisms of the two components. -/
noncomputable def isoMk {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (i : P.x ≅ Q.x)
    (j : P.y ≅ Q.y)
    (hb : eqToHom P.hy.symm ≫ p𝒴.map j.hom ≫ eqToHom Q.hy =
      eqToHom P.hx.symm ≫ p𝒳.map i.hom ≫ eqToHom Q.hx)
    (hw : F.map i.hom ≫ Q.iso.hom = P.iso.hom ≫ G.map j.hom) : P ≅ Q := by
  have : IsIso (Hom.mk' i.hom j.hom hb hw) :=
    isIso_of_isIso_components p𝒳 p𝒴 p𝒮 F G _
      (by simp only [Hom.mk'_a]; infer_instance) (by simp only [Hom.mk'_b]; infer_instance)
  exact asIso (Hom.mk' i.hom j.hom hb hw)

/-- The `𝒳`-component of `isoMk i j hb hw` is `i`. -/
@[simp] theorem isoMk_hom_a {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (i : P.x ≅ Q.x)
    (j : P.y ≅ Q.y) (hb) (hw) : (isoMk i j hb hw).hom.a = i.hom := rfl

/-- The `𝒴`-component of `isoMk i j hb hw` is `j`. -/
@[simp] theorem isoMk_hom_b {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (i : P.x ≅ Q.x)
    (j : P.y ≅ Q.y) (hb) (hw) : (isoMk i j hb hw).hom.b = j.hom := rfl

/-- An isomorphism of the 2-fibre product built from two vertical isomorphisms of the
components. -/
noncomputable def isoMkVertical {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} {U : 𝒞}
    (i : P.x ≅ Q.x) (j : P.y ≅ Q.y) (hi : p𝒳.IsHomLift (𝟙 U) i.hom)
    (hj : p𝒴.IsHomLift (𝟙 U) j.hom)
    (hw : F.map i.hom ≫ Q.iso.hom = P.iso.hom ≫ G.map j.hom) : P ≅ Q :=
  isoMk i j (by
    have := hi
    have := hj
    rw [IsHomLift.fac' p𝒳 (𝟙 U) i.hom, IsHomLift.fac' p𝒴 (𝟙 U) j.hom]
    simp) hw

/-- The `𝒳`-component of `isoMkVertical i j hi hj hw` is `i`. -/
@[simp] theorem isoMkVertical_hom_a {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} {U : 𝒞}
    (i : P.x ≅ Q.x) (j : P.y ≅ Q.y) (hi : p𝒳.IsHomLift (𝟙 U) i.hom)
    (hj : p𝒴.IsHomLift (𝟙 U) j.hom) (hw) : (isoMkVertical i j hi hj hw).hom.a = i.hom := rfl

/-- The `𝒴`-component of `isoMkVertical i j hi hj hw` is `j`. -/
@[simp] theorem isoMkVertical_hom_b {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} {U : 𝒞}
    (i : P.x ≅ Q.x) (j : P.y ≅ Q.y) (hi : p𝒳.IsHomLift (𝟙 U) i.hom)
    (hj : p𝒴.IsHomLift (𝟙 U) j.hom) (hw) : (isoMkVertical i j hi hj hw).hom.b = j.hom := rfl

end Iso

section HomLift

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴] {𝒮 : Type u₄} [Category.{v₄} 𝒮]
  {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒮 : 𝒮 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒮} {G : 𝒴 ⥤ 𝒮}

/-- A morphism of the 2-fibre product lies over a morphism of the base as soon as its
`𝒳`-component does. -/
theorem structureFunctor_isHomLift {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (φ : P ⟶ Q)
    {R S : 𝒞} (k : R ⟶ S) (h : p𝒳.IsHomLift k φ.a) :
    (structureFunctor p𝒳 p𝒴 p𝒮 F G).IsHomLift k φ := by
  have hR : (structureFunctor p𝒳 p𝒴 p𝒮 F G).obj P = R :=
    P.hx.symm.trans (IsHomLift.domain_eq p𝒳 k φ.a)
  have hS : (structureFunctor p𝒳 p𝒴 p𝒮 F G).obj Q = S :=
    Q.hx.symm.trans (IsHomLift.codomain_eq p𝒳 k φ.a)
  refine IsHomLift.of_fac' _ k φ hR hS ?_
  have h1 : (structureFunctor p𝒳 p𝒴 p𝒮 F G).map φ = φ.hbase := rfl
  rw [h1, φ.hbase_eq, IsHomLift.fac' p𝒳 k φ.a]
  simp

/-- The `𝒳`-component of a morphism of the 2-fibre product lies over the same morphism of the
base as the morphism itself. -/
theorem isHomLift_a {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (φ : P ⟶ Q) {R S : 𝒞} (k : R ⟶ S)
    (h : (structureFunctor p𝒳 p𝒴 p𝒮 F G).IsHomLift k φ) : p𝒳.IsHomLift k φ.a :=
  Functor.isHomLift_map_of_comp_eq (fst_comp_eq (p𝒳 := p𝒳) (p𝒴 := p𝒴) (p𝒮 := p𝒮) (F := F)
    (G := G)) k φ

/-- The `𝒴`-component of a morphism of the 2-fibre product lies over the same morphism of the
base as the morphism itself. -/
theorem isHomLift_b {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (φ : P ⟶ Q) {R S : 𝒞} (k : R ⟶ S)
    (h : (structureFunctor p𝒳 p𝒴 p𝒮 F G).IsHomLift k φ) : p𝒴.IsHomLift k φ.b :=
  Functor.isHomLift_map_of_comp_eq (snd_comp_eq (p𝒳 := p𝒳) (p𝒴 := p𝒴) (p𝒮 := p𝒮) (F := F)
    (G := G)) k φ

end HomLift

section EssSurj

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴] {𝒮 : Type u₄} [Category.{v₄} 𝒮]
  (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒮 : 𝒮 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒮) (G : 𝒴 ⥤ 𝒮)
  {W : Type u₅} [Category.{v₅} W] (pW : W ⥤ 𝒞) (H : W ⥤ 𝒳) (K : W ⥤ 𝒴)
  (hH : H ⋙ p𝒳 = pW) (hK : K ⋙ p𝒴 = pW) (t : H ⋙ F ≅ K ⋙ G)
  (ht : ∀ w, p𝒮.IsHomLift (𝟙 (pW.obj w)) (t.hom.app w))

/-- **The mediating 1-morphism of Stacks 0040 is essentially surjective when every object of the
2-fibre product is, over its own base, the image of an object of the test category.** The
hypothesis is the object-lifting datum in its unpacked form: for an object `(U, x, y, φ)` of
`𝒳 ×_𝒮 𝒴` an object `w` of `W` together with *vertical* isomorphisms `H w ≅ x` and `K w ≅ y`
intertwining the test 2-cell at `w` with `φ`. That is exactly an isomorphism
`lift w ≅ (U, x, y, φ)` of the 2-fibre product over `𝒞`
(`CategoryTheory.TwoFibreProductOver.isoMkVertical`).

Together with `CategoryTheory.TwoFibreProductOver.full_lift` and `…faithful_lift` this is what
recognises a 2-commutative square as 2-cartesian through its strict comparison with the canonical
2-fibre product. -/
lemma essSurj_lift
    (hsurj : ∀ P : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G, ∃ (w : W) (ι : H.obj w ≅ P.x)
      (κ : K.obj w ≅ P.y), p𝒳.IsHomLift (𝟙 P.base) ι.hom ∧
        p𝒴.IsHomLift (𝟙 P.base) κ.hom ∧
        F.map ι.hom ≫ P.iso.hom = t.hom.app w ≫ G.map κ.hom) :
    (lift p𝒳 p𝒴 p𝒮 F G pW H K hH hK t ht).EssSurj where
  mem_essImage P :=
    Exists.elim (hsurj P) fun w hw =>
      Exists.elim hw fun ι hι =>
        Exists.elim hι fun κ hκ =>
          ⟨w, ⟨isoMkVertical (U := P.base) ι κ hκ.1 hκ.2.1 hκ.2.2⟩⟩

end EssSurj

end CategoryTheory.TwoFibreProductOver

end
