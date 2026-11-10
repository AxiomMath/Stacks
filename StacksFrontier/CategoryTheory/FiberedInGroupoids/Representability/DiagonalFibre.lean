module

public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksFrontier.CategoryTheory.FiberedCategory.PresheafElementsEquivalence
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Diagonal
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.Criterion
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverComp

/-!
# The fibre of the diagonal is the sheaf of vertical morphisms

Let `𝒞` be a category, let `p : 𝒳 ⥤ 𝒞` be fibred in groupoids and let `𝒳 ×_𝒞 𝒳` be the product
of `𝒳` with itself in the 2-category of categories over `𝒞`, with its diagonal
`Δ : 𝒳 ⟶ 𝒳 ×_𝒞 𝒳`. For a category `𝒯` over `𝒞` and a 1-morphism `Y : 𝒯 ⟶ 𝒳 ×_𝒞 𝒳` over `𝒞`,
this file identifies the first projection of the 2-fibre product

`𝒯 ×_{Y, 𝒳 ×_𝒞 𝒳, Δ} 𝒳 ⟶ 𝒯`

with the category of elements of the presheaf on `𝒯` whose sections over `a` are the *vertical*
morphisms `Y₁ a ⟶ Y₂ a` of `𝒳`, where `Y₁`, `Y₂` are the two components of `Y`.

This is the fibrewise content of the first equivalence of Stacks 045G: for `𝒯` the big fppf site
over a scheme `U` and `Y` the pair of objects `x`, `y` of the fibre of `𝒳` over `U`, the presheaf
of vertical morphisms is `Isom(x, y)`, so the 2-fibre product whose representability the
diagonal condition asserts is the category of elements of that isomorphism presheaf.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.DiagonalFibre.VertHom`: the type of vertical morphisms
  between the values at `a` of two functors over `𝒞`.
* `CategoryTheory.TwoFibreProductOver.DiagonalFibre.VertHom.restrict`: their restriction along a
  morphism of `𝒯`, the unique vertical fill-in against the cartesian morphism `Y₂ h`.
* `CategoryTheory.TwoFibreProductOver.DiagonalFibre.vertHomPresheaf`: the resulting presheaf.
* `CategoryTheory.TwoFibreProductOver.sectOf` and
  `CategoryTheory.TwoFibreProductOver.DiagonalFibre.objOf`: the two directions of the
  identification on objects — the vertical morphism `α ∘ β⁻¹` attached to an object
  `(a, z, α : Y₁ a ≅ z, β : Y₂ a ≅ z)` of the 2-fibre product, and the standard object
  `(a, Y₂ a, m, id)` attached to a vertical morphism `m`.

## Main results

* `CategoryTheory.TwoFibreProductOver.DiagonalFibre.equivalenceOver`: the first projection of
  `𝒯 ×_{Y, 𝒳 ×_𝒞 𝒳, Δ} 𝒳` is equivalent over `𝒯` to the category of elements of
  `vertHomPresheaf`.
-/

@[expose] public section

open CategoryTheory Opposite Pseudofunctor

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄ t

namespace CategoryTheory.TwoFibreProductOver

section DiagonalSection

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {X : Type u₃} [Category.{v₃} X]
  {𝒯 : Type u₂} [Category.{v₂} 𝒯] {𝒴 : Type u₄} [Category.{v₄} 𝒴]
variable {p : X ⥤ 𝒞} {p𝒯 : 𝒯 ⥤ 𝒞} {q : 𝒴 ⥤ 𝒞} {F : X ⥤ 𝒴} {hF : F ⋙ q = p}

attribute [local implicit_reducible] _root_.CategoryTheory.TwoFibreProductOver.fst
  _root_.CategoryTheory.TwoFibreProductOver.snd
  _root_.CategoryTheory.TwoFibreProductOver.diagonal

variable {Y : 𝒯 ⥤ TwoFibreProductOver p p q F F}

/-- The vertical morphism `Y₁ a ⟶ Y₂ a` attached to an object of the 2-fibre product
`𝒯 ×_{Y, X ×_{F, 𝒴, F} X, Δ_F} X`. -/
def sectOf (A : TwoFibreProductOver p𝒯 p (structureFunctor p p q F F) Y (diagonal hF)) :
    (Y ⋙ fst p p q F F).obj A.x ⟶ (Y ⋙ snd p p q F F).obj A.x :=
  A.iso.hom.a ≫ A.iso.inv.b

/-- `sectOf` unfolded. -/
lemma sectOf_def (A : TwoFibreProductOver p𝒯 p (structureFunctor p p q F F) Y (diagonal hF)) :
    sectOf A = A.iso.hom.a ≫ A.iso.inv.b := rfl

variable {A B : TwoFibreProductOver p𝒯 p (structureFunctor p p q F F) Y (diagonal hF)}

/-- The second components of the two directions of the comparison isomorphism of an object of
the 2-fibre product are mutually inverse, in one order. -/
lemma iso_hom_b_comp_inv_b
    (A : TwoFibreProductOver p𝒯 p (structureFunctor p p q F F) Y (diagonal hF)) :
    A.iso.hom.b ≫ A.iso.inv.b = 𝟙 ((Y ⋙ snd p p q F F).obj A.x) := by
  have h := congrArg Hom.b A.iso.hom_inv_id
  rwa [comp_b, id_b] at h

/-- The same in the other order. -/
lemma iso_inv_b_comp_hom_b
    (A : TwoFibreProductOver p𝒯 p (structureFunctor p p q F F) Y (diagonal hF)) :
    A.iso.inv.b ≫ A.iso.hom.b = 𝟙 A.y := by
  have h := congrArg Hom.b A.iso.inv_hom_id
  rwa [comp_b, id_b] at h

/-- Naturality of the first component of the comparison isomorphism. -/
lemma hom_a_naturality (u : A ⟶ B) :
    (Y ⋙ fst p p q F F).map u.a ≫ B.iso.hom.a = A.iso.hom.a ≫ u.b := by
  have h := congrArg Hom.a u.w
  rwa [comp_a, comp_a] at h

/-- Naturality of the second component of the comparison isomorphism. -/
lemma hom_b_naturality (u : A ⟶ B) :
    (Y ⋙ snd p p q F F).map u.a ≫ B.iso.hom.b = A.iso.hom.b ≫ u.b := by
  have h := congrArg Hom.b u.w
  rwa [comp_b, comp_b] at h

/-- Naturality of the second component of the inverse comparison isomorphism. -/
lemma inv_b_naturality (u : A ⟶ B) :
    A.iso.inv.b ≫ (Y ⋙ snd p p q F F).map u.a = u.b ≫ B.iso.inv.b := by
  rw [← Category.comp_id ((Y ⋙ snd p p q F F).map u.a), ← iso_hom_b_comp_inv_b B,
    ← Category.assoc ((Y ⋙ snd p p q F F).map u.a), hom_b_naturality u, Category.assoc,
    ← Category.assoc A.iso.inv.b, iso_inv_b_comp_hom_b A]
  exact Category.id_comp _

/-- The sections of two objects of the 2-fibre product are compatible with a morphism between
them: the square against `Y₁ u` and `Y₂ u` commutes. -/
lemma sectOf_naturality (u : A ⟶ B) :
    sectOf A ≫ (Y ⋙ snd p p q F F).map u.a = (Y ⋙ fst p p q F F).map u.a ≫ sectOf B := by
  rw [sectOf_def, sectOf_def, Category.assoc, inv_b_naturality, ← Category.assoc,
    ← hom_a_naturality, Category.assoc]

end DiagonalSection

end CategoryTheory.TwoFibreProductOver

namespace CategoryTheory.TwoFibreProductOver.DiagonalFibre



variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {X : Type u₃} [Category.{v₃} X]
  {𝒯 : Type u₂} [Category.{v₂} 𝒯]

/-- The type of vertical morphisms `Y₁ a ⟶ Y₂ a`. -/
def VertHom (p : X ⥤ 𝒞) (p𝒯 : 𝒯 ⥤ 𝒞) (Y₁ Y₂ : 𝒯 ⥤ X) (a : 𝒯) : Type v₃ :=
  {φ : Y₁.obj a ⟶ Y₂.obj a // p.IsHomLift (𝟙 (p𝒯.obj a)) φ}

namespace VertHom

variable {p : X ⥤ 𝒞} {p𝒯 : 𝒯 ⥤ 𝒞} {Y₁ Y₂ : 𝒯 ⥤ X}

/-- Two vertical morphisms are equal if their underlying morphisms are. -/
@[ext] lemma ext {a : 𝒯} {φ ψ : VertHom p p𝒯 Y₁ Y₂ a} (h : φ.1 = ψ.1) : φ = ψ :=
  Subtype.ext h

/-- If `Y₂ ⋙ p = p𝒯`, then `Y₂ h` lies over `p𝒯 h`. -/
lemma isHomLift_map (h₂ : Y₂ ⋙ p = p𝒯) {a' a : 𝒯} (h : a' ⟶ a) :
    p.IsHomLift (p𝒯.map h) (Y₂.map h) := by
  refine IsHomLift.of_fac' p _ _ (Functor.congr_obj h₂ a') (Functor.congr_obj h₂ a) ?_
  have := Functor.congr_hom h₂ h
  simp only [Functor.comp_map] at this
  rw [this]

/-- If `Y₁ ⋙ p = p𝒯`, then `Y₁ h ≫ φ` lies over `p𝒯 h` for every vertical morphism `φ`. -/
lemma isHomLift_comp (h₁ : Y₁ ⋙ p = p𝒯) {a' a : 𝒯} (h : a' ⟶ a) (φ : VertHom p p𝒯 Y₁ Y₂ a) :
    p.IsHomLift (p𝒯.map h) (Y₁.map h ≫ φ.1) := by
  have h1 : p.IsHomLift (p𝒯.map h) (Y₁.map h) := isHomLift_map h₁ h
  have h2 := φ.2
  have : p.IsHomLift (p𝒯.map h ≫ 𝟙 (p𝒯.obj a)) (Y₁.map h ≫ φ.1) := inferInstance
  rwa [Category.comp_id] at this

variable (hp : p.IsFiberedInGroupoids) (h₁ : Y₁ ⋙ p = p𝒯) (h₂ : Y₂ ⋙ p = p𝒯)

/-- If `p` is fibred in groupoids and `Y₂ ⋙ p = p𝒯`, then `Y₂ h` is strongly cartesian. -/
private lemma isStronglyCartesian_map (hp : p.IsFiberedInGroupoids) (h₂ : Y₂ ⋙ p = p𝒯)
    {a' a : 𝒯} (h : a' ⟶ a) :
    p.IsStronglyCartesian (p𝒯.map h) (Y₂.map h) :=
  have := isHomLift_map h₂ h
  hp.isStronglyCartesian_homLift _ _

/-- Restriction of a vertical morphism along `h : a' ⟶ a`: the unique vertical morphism
`Y₁ a' ⟶ Y₂ a'` whose composite with `Y₂ h` is `Y₁ h ≫ φ`. -/
noncomputable def restrict {a' a : 𝒯} (h : a' ⟶ a) (φ : VertHom p p𝒯 Y₁ Y₂ a) :
    VertHom p p𝒯 Y₁ Y₂ a' :=
  have := isHomLift_map h₂ (Y₂ := Y₂) h
  have := isHomLift_comp h₁ h φ
  have _hsc : p.IsStronglyCartesian (p𝒯.map h) (Y₂.map h) :=
    hp.isStronglyCartesian_homLift _ _
  ⟨Functor.IsStronglyCartesian.map p (p𝒯.map h) (Y₂.map h) (Category.id_comp _).symm
      (Y₁.map h ≫ φ.1),
    inferInstance⟩

/-- The restriction of `φ` along `h`, composed with `Y₂ h`, is `Y₁ h ≫ φ`. -/
lemma restrict_fac {a' a : 𝒯} (h : a' ⟶ a) (φ : VertHom p p𝒯 Y₁ Y₂ a) :
    (restrict hp h₁ h₂ h φ).1 ≫ Y₂.map h = Y₁.map h ≫ φ.1 := by
  have := isStronglyCartesian_map hp h₂ h
  have := isHomLift_comp h₁ h φ
  exact Functor.IsStronglyCartesian.fac p (p𝒯.map h) (Y₂.map h) (Category.id_comp _).symm
    (Y₁.map h ≫ φ.1)

/-- A vertical morphism whose composite with `Y₂ h` is `Y₁ h ≫ φ` is the restriction of `φ`
along `h`. -/
lemma restrict_uniq {a' a : 𝒯} (h : a' ⟶ a) (φ : VertHom p p𝒯 Y₁ Y₂ a)
    (ψ : VertHom p p𝒯 Y₁ Y₂ a') (hψ : ψ.1 ≫ Y₂.map h = Y₁.map h ≫ φ.1) :
    ψ = restrict hp h₁ h₂ h φ := by
  have := isStronglyCartesian_map hp h₂ h
  have := isHomLift_comp h₁ h φ
  have : p.IsHomLift (𝟙 (p𝒯.obj a')) ψ.1 := ψ.2
  ext
  exact Functor.IsStronglyCartesian.map_uniq p (p𝒯.map h) (Y₂.map h) (Category.id_comp _).symm
    (Y₁.map h ≫ φ.1) ψ.1 hψ

/-- Restriction along the identity is the identity. -/
lemma restrict_id {a : 𝒯} (φ : VertHom p p𝒯 Y₁ Y₂ a) :
    restrict hp h₁ h₂ (𝟙 a) φ = φ :=
  (restrict_uniq hp h₁ h₂ (𝟙 a) φ φ (by
    rw [Functor.map_id, Functor.map_id]
    exact (Category.comp_id _).trans (Category.id_comp _).symm)).symm

/-- Restriction along a composite is the composite of the restrictions. -/
lemma restrict_comp {a'' a' a : 𝒯} (g : a'' ⟶ a') (f : a' ⟶ a) (φ : VertHom p p𝒯 Y₁ Y₂ a) :
    restrict hp h₁ h₂ (g ≫ f) φ = restrict hp h₁ h₂ g (restrict hp h₁ h₂ f φ) :=
  (restrict_uniq hp h₁ h₂ (g ≫ f) φ _ (by
    rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, restrict_fac,
      Category.assoc, restrict_fac, Category.assoc])).symm

/-- The presheaf on `𝒯` whose sections over `a` are the vertical morphisms `Y₁ a ⟶ Y₂ a`, with
restriction `CategoryTheory.TwoFibreProductOver.DiagonalFibre.VertHom.restrict`. -/
noncomputable def presheaf : 𝒯ᵒᵖ ⥤ Type v₃ where
  obj a := VertHom p p𝒯 Y₁ Y₂ a.unop
  map h := ↾fun φ => restrict hp h₁ h₂ h.unop φ
  map_id _ := by
    ext φ
    exact congrArg Subtype.val (restrict_id hp h₁ h₂ φ)
  map_comp f g := by
    ext φ
    exact congrArg Subtype.val (restrict_comp hp h₁ h₂ g.unop f.unop φ)

/-- The restriction maps of `presheaf` are given by `restrict`. -/
@[simp] lemma presheaf_map {a' a : 𝒯} (h : a' ⟶ a) (φ : VertHom p p𝒯 Y₁ Y₂ a) :
    (presheaf hp h₁ h₂).map h.op φ = restrict hp h₁ h₂ h φ := rfl

end VertHom


open CategoryTheory.TwoFibreProductOver
variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {X : Type u₃} [Category.{v₃} X]
  {𝒯 : Type u₂} [Category.{v₂} 𝒯]
variable {p : X ⥤ 𝒞} {p𝒯 : 𝒯 ⥤ 𝒞}

attribute [local implicit_reducible] _root_.CategoryTheory.TwoFibreProductOver.fst
  _root_.CategoryTheory.TwoFibreProductOver.snd
  _root_.CategoryTheory.TwoFibreProductOver.diagonal

/-- The product `𝒳 ×_𝒞 𝒳` of `p` with itself over `𝒞`. -/
abbrev Prod' (p : X ⥤ 𝒞) := TwoFibreProductOver p p (𝟭 𝒞) p p
/-- The structure functor `𝒳 ×_𝒞 𝒳 ⥤ 𝒞`. -/
abbrev ProdP (p : X ⥤ 𝒞) : Prod' p ⥤ 𝒞 := structureFunctor p p (𝟭 𝒞) p p
/-- The diagonal `𝒳 ⥤ 𝒳 ×_𝒞 𝒳`. -/
abbrev Diag (p : X ⥤ 𝒞) : X ⥤ Prod' p := diagonal (Functor.comp_id p)
/-- The first component of a functor `𝒯 ⥤ 𝒳 ×_𝒞 𝒳`. -/
abbrev Y₁' (Y : 𝒯 ⥤ Prod' p) : 𝒯 ⥤ X := Y ⋙ fst p p (𝟭 𝒞) p p
/-- The second component of a functor `𝒯 ⥤ 𝒳 ×_𝒞 𝒳`. -/
abbrev Y₂' (Y : 𝒯 ⥤ Prod' p) : 𝒯 ⥤ X := Y ⋙ snd p p (𝟭 𝒞) p p

variable {Y : 𝒯 ⥤ Prod' p} (hY : Y ⋙ ProdP p = p𝒯)

/-- If `Y` is a functor over `𝒞`, so is its first component. -/
lemma h1' (hY : Y ⋙ ProdP p = p𝒯) : Y₁' Y ⋙ p = p𝒯 := by
  rw [Functor.assoc, fst_comp_eq]; exact hY
/-- If `Y` is a functor over `𝒞`, so is its second component. -/
lemma h2' (hY : Y ⋙ ProdP p = p𝒯) : Y₂' Y ⋙ p = p𝒯 := by
  rw [Functor.assoc, snd_comp_eq]; exact hY

/-- The section `sectOf A` of an object `A` of the 2-fibre product is vertical. -/
lemma isHomLift_sectOf (hY : Y ⋙ ProdP p = p𝒯)
    (A : TwoFibreProductOver p𝒯 p (ProdP p) Y (Diag p)) :
    p.IsHomLift (𝟙 (p𝒯.obj A.x)) (sectOf A) := by
  have hA := A.iso.hom.ha
  have hB := A.iso.inv.hb
  have hcomp : p.IsHomLift (A.iso.hom.hbase ≫ A.iso.inv.hbase)
      (A.iso.hom.a ≫ A.iso.inv.b) := inferInstance
  have hid : A.iso.hom.hbase ≫ A.iso.inv.hbase = 𝟙 (Y.obj A.x).base := by
    have h := congrArg Hom.hbase A.iso.hom_inv_id
    rw [comp_hbase, id_hbase] at h
    exact h
  rw [hid] at hcomp
  have hbase : (Y.obj A.x).base = p𝒯.obj A.x := Functor.congr_obj hY A.x
  rw [hbase] at hcomp
  exact hcomp


section Obj

/-- A morphism lifting an identity is sent by `q` to an `eqToHom`. -/
private lemma map_eq_eqToHom_of_isHomLift_id {D : Type u₂} [Category.{v₂} D] {E : Type u₁}
    [Category.{v₁} E] (q : D ⥤ E) {Z W : D} (φ : Z ⟶ W) {R : E}
    (hZ : q.obj Z = R) (hW : q.obj W = R) (h : q.IsHomLift (𝟙 R) φ) :
    q.map φ = eqToHom (hZ.trans hW.symm) := by
  rw [IsHomLift.fac' q (𝟙 R) φ]
  simp

variable (hY : Y ⋙ ProdP p = p𝒯) (a : 𝒯)
  (m : VertHom p p𝒯 (Y₁' Y) (Y₂' Y) a)

/-- The base of `Y a` is `p𝒯 a`. -/
lemma base_eq_of_obj (hY : Y ⋙ ProdP p = p𝒯) (a : 𝒯) :
    (Y.obj a).base = p𝒯.obj a := Functor.congr_obj hY a

/-- The comparison isomorphism of `Y a` in `𝒳 ×_𝒞 𝒳` is an `eqToHom`. -/
lemma iso_hom_eq :
    (Y.obj a).iso.hom = eqToHom ((Y.obj a).hx.trans (Y.obj a).hy.symm) := by
  exact map_eq_eqToHom_of_isHomLift_id (𝟭 𝒞) _ (Y.obj a).hx (Y.obj a).hy (Y.obj a).vertical

/-- The image under `p` of a vertical morphism `m : Y₁ a ⟶ Y₂ a` is a composite of `eqToHom`s. -/
lemma map_sect_eq :
    p.map m.1 = eqToHom (Functor.congr_obj (h1' hY) a) ≫
      eqToHom (Functor.congr_obj (h2' hY) a).symm := by
  rw [map_eq_eqToHom_of_isHomLift_id p m.1 (Functor.congr_obj (h1' hY) a)
    (Functor.congr_obj (h2' hY) a) m.2]
  simp


/-- A vertical morphism is an isomorphism when `p` is fibred in groupoids. -/
lemma isIso_vertHom (hp : p.IsFiberedInGroupoids) : IsIso m.1 := by
  have hm := m.2
  have := hp.isStronglyCartesian_homLift (𝟙 (p𝒯.obj a)) m.1
  exact Functor.IsStronglyCartesian.isIso_of_base_isIso p (𝟙 (p𝒯.obj a)) m.1

/-- The image under `p` of the inverse of a vertical morphism `m : Y₁ a ⟶ Y₂ a` is a composite of
`eqToHom`s. -/
lemma map_inv_sect_eq (hp : p.IsFiberedInGroupoids) :
    letI := isIso_vertHom a m hp
    p.map (CategoryTheory.inv m.1) = eqToHom (Functor.congr_obj (h2' hY) a) ≫
      eqToHom (Functor.congr_obj (h1' hY) a).symm := by
  have := isIso_vertHom a m hp
  simp only [p.map_inv, map_sect_eq hY a m]
  simp

/-- The object of the 2-fibre product attached to a vertical morphism `Y₁ a ⟶ Y₂ a`. -/
noncomputable def objOf (hp : p.IsFiberedInGroupoids) :
    TwoFibreProductOver p𝒯 p (ProdP p) Y (Diag p) where
  base := p𝒯.obj a
  x := a
  y := (Y₂' Y).obj a
  hx := rfl
  hy := Functor.congr_obj (h2' hY) a
  iso :=
    have := isIso_vertHom a m hp
    { hom :=
        { hbase := eqToHom ((base_eq_of_obj hY a).trans
            (Functor.congr_obj (h2' hY) a).symm)
          a := m.1
          b := 𝟙 _
          ha := by
            refine IsHomLift.of_fac' p _ _ (Y.obj a).hx rfl ?_
            rw [map_sect_eq hY a m]
            simp
          hb := by
            refine IsHomLift.of_fac' p _ _ (Y.obj a).hy rfl ?_
            simp
          w := by
            rw [map_sect_eq hY a m, iso_hom_eq a]
            simp }
      inv :=
        { hbase := eqToHom (((base_eq_of_obj hY a).trans
            (Functor.congr_obj (h2' hY) a).symm).symm)
          a := CategoryTheory.inv m.1
          b := 𝟙 _
          ha := by
            refine IsHomLift.of_fac' p _ _ rfl (Y.obj a).hx ?_
            rw [map_inv_sect_eq hY a m hp]
            simp
          hb := by
            refine IsHomLift.of_fac' p _ _ rfl (Y.obj a).hy ?_
            simp
          w := by
            rw [map_inv_sect_eq hY a m hp, iso_hom_eq a]
            simp }
      hom_inv_id := Hom.ext' (by simp) (by simp)
      inv_hom_id := Hom.ext' (by simp) (by simp) }
  vertical := by
    refine IsHomLift.of_fac' (ProdP p) _ _ (base_eq_of_obj hY a)
      (Functor.congr_obj (h2' hY) a) ?_
    simp only [Category.id_comp, structureFunctor_map]
    exact (eqToHom_trans _ _).symm

end Obj


section BaseLemmas

/-- A morphism lying over an `eqToHom` is vertical. -/
private lemma isHomLift_id_of_eq_eqToHom {D : Type u₂} [Category.{v₂} D] {E : Type u₁}
    [Category.{v₁} E] (q : D ⥤ E) {Z W : D} (φ : Z ⟶ W) {R T : E} (f : R ⟶ T) (e : R = T)
    (hf : f = eqToHom e) (h : q.IsHomLift f φ) : q.IsHomLift (𝟙 (q.obj Z)) φ := by
  subst hf
  refine IsHomLift.of_fac' q _ _ rfl (((IsHomLift.codomain_eq q (eqToHom e) φ).trans e.symm).trans
    (IsHomLift.domain_eq q (eqToHom e) φ).symm) ?_
  rw [IsHomLift.fac' q (eqToHom e) φ]
  simp

variable (hY : Y ⋙ ProdP p = p𝒯)
  (A : TwoFibreProductOver p𝒯 p (ProdP p) Y (Diag p))

/-- The base of `Y A.x` is the base of `A`. -/
lemma baseEq (hY : Y ⋙ ProdP p = p𝒯)
    (A : TwoFibreProductOver p𝒯 p (ProdP p) Y (Diag p)) :
    (Y.obj A.x).base = A.base := (base_eq_of_obj hY A.x).trans A.hx

/-- The inverse of the comparison isomorphism of `A` is vertical. -/
lemma vertical_inv : (ProdP p).IsHomLift (𝟙 A.base) A.iso.inv := by
  have hv := A.vertical
  have h := IsHomLift.lift_id_inv_isIso (ProdP p) A.base A.iso.hom
  rwa [show CategoryTheory.inv A.iso.hom = A.iso.inv from by simp] at h

/-- The base component of the comparison isomorphism of `A` is an `eqToHom`. -/
lemma hbase_hom_eq (hY : Y ⋙ ProdP p = p𝒯)
    (A : TwoFibreProductOver p𝒯 p (ProdP p) Y (Diag p)) :
    A.iso.hom.hbase = eqToHom (baseEq hY A) ≫ eqToHom A.hy.symm := by
  rw [eqToHom_trans]
  exact map_eq_eqToHom_of_isHomLift_id (ProdP p) A.iso.hom (baseEq hY A) A.hy A.vertical

/-- The base component of the inverse comparison isomorphism of `A` is an `eqToHom`. -/
lemma hbase_inv_eq (hY : Y ⋙ ProdP p = p𝒯)
    (A : TwoFibreProductOver p𝒯 p (ProdP p) Y (Diag p)) :
    A.iso.inv.hbase = eqToHom A.hy ≫ eqToHom (baseEq hY A).symm := by
  rw [eqToHom_trans]
  exact map_eq_eqToHom_of_isHomLift_id (ProdP p) A.iso.inv A.hy (baseEq hY A) (vertical_inv A)

/-- The second component of the inverse comparison isomorphism of `A` is vertical. -/
lemma isHomLift_b_inv (hY : Y ⋙ ProdP p = p𝒯)
    (A : TwoFibreProductOver p𝒯 p (ProdP p) Y (Diag p)) :
    p.IsHomLift (𝟙 (p.obj A.y)) A.iso.inv.b := by
  exact isHomLift_id_of_eq_eqToHom p _ _ _ ((hbase_inv_eq hY A).trans (eqToHom_trans _ _))
    A.iso.inv.hb

/-- The second component of the comparison isomorphism of `A` is vertical. -/
lemma isHomLift_b_hom (hY : Y ⋙ ProdP p = p𝒯)
    (A : TwoFibreProductOver p𝒯 p (ProdP p) Y (Diag p)) :
    p.IsHomLift (𝟙 (p.obj ((Y.obj A.x).y))) A.iso.hom.b := by
  exact isHomLift_id_of_eq_eqToHom p _ _ _ ((hbase_hom_eq hY A).trans (eqToHom_trans _ _))
    A.iso.hom.hb

end BaseLemmas

section HomLiftHelper

/-- A vertical morphism lies over every `eqToHom` between the images of its source and target. -/
lemma isHomLift_eqToHom_of_id {D : Type u₂} [Category.{v₂} D] {E : Type u₁}
    [Category.{v₁} E] (q : D ⥤ E) {Z W : D} (φ : Z ⟶ W) {R T : E}
    (hR : q.obj Z = R) (hT : q.obj W = T) (e : R = T)
    (h : q.IsHomLift (𝟙 (q.obj Z)) φ) : q.IsHomLift (eqToHom e) φ := by
  have := h
  refine IsHomLift.of_fac' q _ _ hR hT ?_
  rw [IsHomLift.fac' q (𝟙 (q.obj Z)) φ]
  simp only [Category.id_comp, eqToHom_trans]

end HomLiftHelper

section ObjOfSimp

variable (hY : Y ⋙ ProdP p = p𝒯) (a : 𝒯) (m : VertHom p p𝒯 (Y₁' Y) (Y₂' Y) a)
  (hp : p.IsFiberedInGroupoids)

/-- The base of `objOf`. -/
@[simp] lemma objOf_base : (objOf hY a m hp).base = p𝒯.obj a := rfl
/-- The object of `𝒯` underlying `objOf`. -/
@[simp] lemma objOf_x : (objOf hY a m hp).x = a := rfl
/-- The object of `𝒳` underlying `objOf`. -/
@[simp] lemma objOf_y : (objOf hY a m hp).y = (Y₂' Y).obj a := rfl
/-- The first component of the comparison isomorphism of `objOf`. -/
@[simp] lemma objOf_iso_hom_a : (objOf hY a m hp).iso.hom.a = m.1 := rfl
/-- The second component of the comparison isomorphism of `objOf`. -/
@[simp] lemma objOf_iso_hom_b : (objOf hY a m hp).iso.hom.b = 𝟙 ((Y₂' Y).obj a) := rfl
/-- The second component of the inverse comparison isomorphism of `objOf`. -/
@[simp] lemma objOf_iso_inv_b : (objOf hY a m hp).iso.inv.b = 𝟙 ((Y₂' Y).obj a) := rfl

/-- The section of the object attached to a vertical morphism `m` is `m`. -/
@[simp] lemma sectOf_objOf : sectOf (objOf hY a m hp) = m.1 := by
  rw [sectOf_def]
  exact Category.comp_id _

end ObjOfSimp



section Equivalence

variable (hp : p.IsFiberedInGroupoids) (hY : Y ⋙ ProdP p = p𝒯)

/-- The presheaf on `𝒯` of vertical morphisms from the first to the second component of `Y`. -/
noncomputable abbrev vertHomPresheaf (hp : p.IsFiberedInGroupoids)
    (hY : Y ⋙ ProdP p = p𝒯) : 𝒯ᵒᵖ ⥤ Type v₃ :=
  VertHom.presheaf hp (h1' hY) (h2' hY)

/-- The comparison functor from the 2-fibre product `𝒯 ×_{𝒳 × 𝒳} 𝒳` to the category of
elements of the presheaf of vertical morphisms. -/
noncomputable def toElements (hp : p.IsFiberedInGroupoids) (hY : Y ⋙ ProdP p = p𝒯) :
    TwoFibreProductOver p𝒯 p (ProdP p) Y (Diag p) ⥤
      (presheafOfCategories (vertHomPresheaf hp hY ⋙ typeToCat)).obj where
  obj A := ⟨A.x, Discrete.mk ⟨sectOf A, isHomLift_sectOf hY A⟩⟩
  map {A B} u := ⟨u.a, Discrete.eqToHom
    (VertHom.restrict_uniq hp (h1' hY) (h2' hY) u.a ⟨sectOf B, isHomLift_sectOf hY B⟩
      ⟨sectOf A, isHomLift_sectOf hY A⟩ (sectOf_naturality u))⟩
  map_id _ := PresheafOfCategories.elements_hom_ext _ _ rfl
  map_comp _ _ := PresheafOfCategories.elements_hom_ext _ _ rfl

/-- The comparison functor from the category of elements of the presheaf of vertical morphisms
back to the 2-fibre product. -/
noncomputable def ofElements (hp : p.IsFiberedInGroupoids) (hY : Y ⋙ ProdP p = p𝒯) :
    (presheafOfCategories (vertHomPresheaf hp hY ⋙ typeToCat)).obj ⥤
      TwoFibreProductOver p𝒯 p (ProdP p) Y (Diag p) where
  obj P := objOf hY P.base P.fiber.as hp
  map {P Q} u :=
    { hbase := p𝒯.map u.base
      a := u.base
      b := (Y₂' Y).map u.base
      ha := IsHomLift.map p𝒯 u.base
      hb := VertHom.isHomLift_map (h2' hY) u.base
      w := by
        refine Hom.ext' ?_ ?_
        · have hfib : P.fiber.as
              = VertHom.restrict hp (h1' hY) (h2' hY) u.base Q.fiber.as :=
            Discrete.eq_of_hom u.fiber
          have hfac := VertHom.restrict_fac hp (h1' hY) (h2' hY) u.base Q.fiber.as
          simp only [comp_a]
          rw [hfib]
          exact hfac.symm
        · simp only [comp_b]
          exact (Category.comp_id _).trans (Category.id_comp _).symm }
  map_id P := Hom.ext' rfl (by
    change (Y₂' Y).map (𝟙 P.base) = _
    exact Functor.map_id _ _)
  map_comp u v := Hom.ext' rfl (by
    change (Y₂' Y).map (u.base ≫ v.base) = _
    exact Functor.map_comp _ _ _)

/-- The unit of the equivalence: an object of the 2-fibre product is isomorphic, vertically,
to the standard object attached to its section. -/
noncomputable def unitIso (hp : p.IsFiberedInGroupoids) (hY : Y ⋙ ProdP p = p𝒯) :
    𝟭 (TwoFibreProductOver p𝒯 p (ProdP p) Y (Diag p)) ≅
      toElements hp hY ⋙ ofElements hp hY :=
  NatIso.ofComponents
    (fun A =>
      { hom :=
          { hbase := eqToHom A.hx.symm
            a := 𝟙 A.x
            b := A.iso.inv.b
            ha := isHomLift_eqToHom_of_id p𝒯 (𝟙 A.x) A.hx rfl A.hx.symm
              (IsHomLift.id rfl)
            hb := isHomLift_eqToHom_of_id p A.iso.inv.b A.hy
              (Functor.congr_obj (h2' hY) A.x) A.hx.symm (isHomLift_b_inv hY A)
            w := by
              refine Hom.ext' ?_ ?_
              · change (Y.map (𝟙 A.x)).a ≫ sectOf A = A.iso.hom.a ≫ A.iso.inv.b
                rw [Functor.map_id, id_a, Category.id_comp, sectOf_def]
              · change (Y.map (𝟙 A.x)).b ≫ 𝟙 ((Y₂' Y).obj A.x) = A.iso.hom.b ≫ A.iso.inv.b
                rw [Functor.map_id, id_b, Category.id_comp, iso_hom_b_comp_inv_b A] }
        inv :=
          { hbase := eqToHom A.hx
            a := 𝟙 A.x
            b := A.iso.hom.b
            ha := isHomLift_eqToHom_of_id p𝒯 (𝟙 A.x) rfl A.hx A.hx
              (IsHomLift.id rfl)
            hb := isHomLift_eqToHom_of_id p A.iso.hom.b
              (Functor.congr_obj (h2' hY) A.x) A.hy A.hx (isHomLift_b_hom hY A)
            w := by
              refine Hom.ext' ?_ ?_
              · change (Y.map (𝟙 A.x)).a ≫ A.iso.hom.a = sectOf A ≫ A.iso.hom.b
                rw [Functor.map_id, id_a, Category.id_comp, sectOf_def, Category.assoc,
                  iso_inv_b_comp_hom_b A]
                exact (Category.comp_id _).symm
              · change (Y.map (𝟙 A.x)).b ≫ A.iso.hom.b
                  = 𝟙 ((Y₂' Y).obj A.x) ≫ A.iso.hom.b
                rw [Functor.map_id, id_b]
                rfl }
        hom_inv_id := Hom.ext' (Category.id_comp _) (iso_inv_b_comp_hom_b A)
        inv_hom_id := Hom.ext' (Category.id_comp _) (iso_hom_b_comp_inv_b A) })
    (by
      intro A B u
      refine Hom.ext' ?_ ?_
      · change u.a ≫ 𝟙 B.x = 𝟙 A.x ≫ u.a
        rw [Category.comp_id, Category.id_comp]
      · change u.b ≫ B.iso.inv.b = A.iso.inv.b ≫ (Y₂' Y).map u.a
        exact (inv_b_naturality u).symm)

/-- The counit of the equivalence: the section of the standard object attached to a vertical
morphism is that morphism. -/
noncomputable def counitIso (hp : p.IsFiberedInGroupoids) (hY : Y ⋙ ProdP p = p𝒯) :
    ofElements hp hY ⋙ toElements hp hY ≅
      𝟭 (presheafOfCategories (vertHomPresheaf hp hY ⋙ typeToCat)).obj :=
  NatIso.ofComponents
    (fun P =>
      { hom := ⟨𝟙 P.base, Discrete.eqToHom
          ((VertHom.ext (sectOf_objOf hY P.base P.fiber.as hp)).trans
            (VertHom.restrict_id hp (h1' hY) (h2' hY) P.fiber.as).symm)⟩
        inv := ⟨𝟙 P.base, Discrete.eqToHom
          ((VertHom.ext (sectOf_objOf hY P.base P.fiber.as hp)).symm.trans
            (VertHom.restrict_id hp (h1' hY) (h2' hY)
              ⟨sectOf (objOf hY P.base P.fiber.as hp),
                isHomLift_sectOf hY (objOf hY P.base P.fiber.as hp)⟩).symm)⟩
        hom_inv_id := PresheafOfCategories.elements_hom_ext _ _ (by
          change 𝟙 P.base ≫ 𝟙 P.base = 𝟙 P.base
          exact Category.id_comp _)
        inv_hom_id := PresheafOfCategories.elements_hom_ext _ _ (by
          change 𝟙 P.base ≫ 𝟙 P.base = 𝟙 P.base
          exact Category.id_comp _) })
    (by
      intro P Q u
      refine PresheafOfCategories.elements_hom_ext _ _ ?_
      change u.base ≫ 𝟙 Q.base = 𝟙 P.base ≫ u.base
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The 2-fibre product of a
scheme-valued point `Y` of `𝒳 × 𝒳` with the diagonal of `𝒳` is equivalent, over the base, to
the category of elements of the presheaf of vertical morphisms from the first to the second
component of `Y`. -/
noncomputable def equivalenceOver (hp : p.IsFiberedInGroupoids) (hY : Y ⋙ ProdP p = p𝒯) :
    StacksRepresentableCFG.EquivalenceOver
      (fst p𝒯 p (ProdP p) Y (Diag p))
      (presheafOfCategories (vertHomPresheaf hp hY ⋙ typeToCat)).p where
  hom := ⟨toElements hp hY, rfl⟩
  inv := ⟨ofElements hp hY, rfl⟩
  unitIso := unitIso hp hY
  counitIso := counitIso hp hY
  unit_over := by
    refine StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ ?_
    intro A
    refine IsHomLift.of_fac' (fst p𝒯 p (ProdP p) Y (Diag p)) _ _ rfl rfl ?_
    change 𝟙 A.x = _
    simp only [Category.id_comp, eqToHom_trans]
    rfl
  counit_over := by
    refine StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ ?_
    intro P
    refine IsHomLift.of_fac'
      (presheafOfCategories (vertHomPresheaf hp hY ⋙ typeToCat)).p _ _ rfl rfl ?_
    change 𝟙 P.base = _
    simp only [Category.id_comp, eqToHom_trans]
    rfl

/-- The first projection of
`𝒯 ×_{Y, 𝒳 ×_𝒞 𝒳, Δ} 𝒳` is equivalent over `𝒯` to the category of elements of a presheaf of sets
`F` exactly when `F` and the presheaf of vertical morphisms between the two components of `Y`
become isomorphic after both are lifted to a common value universe. -/
theorem nonempty_equivalenceOver_fst_iff (hp : p.IsFiberedInGroupoids)
    (hY : Y ⋙ ProdP p = p𝒯) (F : 𝒯ᵒᵖ ⥤ Type t) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
        (fst p𝒯 p (ProdP p) Y (Diag p))
        (presheafOfCategories (F ⋙ typeToCat)).p) ↔
      Nonempty (vertHomPresheaf hp hY ⋙ uliftFunctor.{t, v₃} ≅
        F ⋙ uliftFunctor.{v₃, t}) := by
  rw [← PresheafOfCategories.nonempty_equivalenceOver_iff (vertHomPresheaf hp hY) F]
  exact ⟨fun ⟨E⟩ => ⟨(equivalenceOver hp hY).symm.trans E⟩,
    fun ⟨e⟩ => ⟨(equivalenceOver hp hY).trans e⟩⟩

end Equivalence


end CategoryTheory.TwoFibreProductOver.DiagonalFibre

end
