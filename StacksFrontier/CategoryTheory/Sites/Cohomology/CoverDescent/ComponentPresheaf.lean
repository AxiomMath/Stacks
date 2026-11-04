module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.ConnectedComponents
public import Mathlib.CategoryTheory.FiberedCategory.Cartesian
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksFrontier.CategoryTheory.FiberedCategory.PresheafElementsEquivalence
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CoverDescent.Sections

/-! # The presheaf of components of a functor into a category

For a functor `z : 𝒵 ⥤ 𝒳` this file introduces the presheaf of sets `Ψ(z)` on `𝒳` whose value
at `y` is the set of connected components of the category of arrows `y ⟶ z(ζ)`. It is the left
Kan extension along `z` of the final presheaf, written out: morphisms `Ψ(z) ⟶ F` are the
compatible families of sections of `F` over the image of `z`.

When `𝒵` and `𝒳` are categories fibred in groupoids over a common base and `z` is a morphism of
fibred categories, `Ψ(z)` is the presheaf on `𝒳` that `z` represents: every arrow `y ⟶ z(ζ)`
is connected to one which is an isomorphism lying over an identity, and two such are connected
exactly when they differ by an isomorphism of `𝒵` lying over an identity. Consequently `Ψ`
carries 2-fibre products of fibred categories to fibre products of presheaves.

## Main definitions

* `Stacks.Sites.CoverDescent.componentPresheaf`: the presheaf `Ψ(z)`.
* `Stacks.Sites.CoverDescent.componentPresheafMap`: the map `Ψ(e ⋙ z) ⟶ Ψ(z)`.

## Main results

* `Stacks.Sites.CoverDescent.componentPresheafIsoOfIsTerminal`: if `𝒵` has a terminal object
  `t`, then `Ψ(z)` is the representable presheaf of `z(t)`.
* `Stacks.Sites.CoverDescent.componentPresheaf_id_unique`: `Ψ(𝟭 𝒳)` is the final presheaf.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace Stacks.Sites.CoverDescent

variable {𝒳 : Type u₁} [Category.{v₁} 𝒳] {𝒵 : Type u₂} [Category.{v₂} 𝒵]

/-- **The presheaf of components of a functor.** Its value at `y` is the set of connected
components of the category `StructuredArrow y z` of arrows from `y` to the image of `z`, and its
restriction maps are precomposition. -/
@[simps obj]
def componentPresheaf (z : 𝒵 ⥤ 𝒳) : 𝒳ᵒᵖ ⥤ Type (max u₂ v₁) where
  obj y := Quotient (Zigzag.setoid (StructuredArrow y.unop z))
  map g := ↾Quotient.map (StructuredArrow.map g.unop).obj
    (fun _ _ => zigzag_obj_of_zigzag (StructuredArrow.map g.unop))
  map_id y := TypeCat.homEquiv.injective (funext fun c => by
    induction c using Quotient.inductionOn with
    | h a => exact congrArg (Quotient.mk _) (StructuredArrow.map_id (f := a)))
  map_comp f g := TypeCat.homEquiv.injective (funext fun c => by
    induction c using Quotient.inductionOn with
    | h a =>
      exact congrArg (Quotient.mk _)
        (StructuredArrow.map_comp (f := g.unop) (f' := f.unop) (h := a)))

variable (z : 𝒵 ⥤ 𝒳)

/-- The class of an arrow `y ⟶ z(ζ)` in the presheaf of components. -/
abbrev componentMk {y : 𝒳} {ζ : 𝒵} (φ : y ⟶ z.obj ζ) : (componentPresheaf z).obj (op y) :=
  Quotient.mk (Zigzag.setoid _) (StructuredArrow.mk φ)

/-- Restricting the class of `φ : y ⟶ z(ζ)` along `g : y' ⟶ y` gives the class of `g ≫ φ`. -/
@[simp]
lemma componentPresheaf_map_mk {y y' : 𝒳} (g : y' ⟶ y) {ζ : 𝒵} (φ : y ⟶ z.obj ζ) :
    (componentPresheaf z).map g.op (componentMk z φ) = componentMk z (g ≫ φ) := rfl

/-- Every section of the presheaf of components is the class of an arrow. -/
lemma componentMk_surjective {y : 𝒳} (c : (componentPresheaf z).obj (op y)) :
    ∃ (ζ : 𝒵) (φ : y ⟶ z.obj ζ), componentMk z φ = c := by
  induction c using Quotient.inductionOn with
  | h x => exact ⟨x.right, x.hom, congrArg (Quotient.mk _) (StructuredArrow.eq_mk x).symm⟩

/-- Two arrows related by a morphism of `𝒵` have the same class. -/
lemma componentMk_eq_of_comp {y : 𝒳} {ζ ζ' : 𝒵} (φ : y ⟶ z.obj ζ) (m : ζ ⟶ ζ') :
    componentMk z φ = componentMk z (φ ≫ z.map m) :=
  Quot.sound (Zigzag.of_hom (StructuredArrow.mkPostcomp φ m))

/-! ### Functoriality -/

/-- **The map `Ψ(e ⋙ z) ⟶ Ψ(z)` induced by a functor `e : 𝒜 ⥤ 𝒵`**: it sends the class of
`y ⟶ z(e(a))` to the class of the same arrow, read as an arrow to the image of `z`. -/
@[simps]
def componentPresheafMap {𝒜 : Type u₂} [Category.{v₃} 𝒜] (e : 𝒜 ⥤ 𝒵) :
    componentPresheaf (e ⋙ z) ⟶ componentPresheaf z where
  app y := ↾Quotient.map (StructuredArrow.pre y.unop e z).obj
    (fun _ _ => zigzag_obj_of_zigzag (StructuredArrow.pre y.unop e z))
  naturality y y' g := TypeCat.homEquiv.injective (funext fun c => by
    induction c using Quotient.inductionOn
    rfl)

/-- The map `Ψ(e ⋙ z) ⟶ Ψ(z)` sends the class of an arrow `y ⟶ z(e(a))` to the class of the same
arrow. -/
@[simp]
lemma componentPresheafMap_mk {𝒜 : Type u₂} [Category.{v₃} 𝒜] (e : 𝒜 ⥤ 𝒵) {y : 𝒳} {a : 𝒜}
    (φ : y ⟶ z.obj (e.obj a)) :
    (componentPresheafMap z e).app (op y) (componentMk (e ⋙ z) φ) = componentMk z φ := rfl

/-- The functor of arrows induced by a functor `e` and a natural transformation
`α : z' ⟶ e ⋙ z`: an arrow `y ⟶ z'(a)` goes to its composite with `α_a`. -/
@[simps]
def structuredArrowMapOfNatTrans {𝒜 : Type u₂} [Category.{v₃} 𝒜] {ℬ : Type u₂} [Category.{v₂} ℬ]
    {z' : 𝒜 ⥤ 𝒳} (e : 𝒜 ⥤ ℬ) (zB : ℬ ⥤ 𝒳) (α : z' ⟶ e ⋙ zB) (y : 𝒳) :
    StructuredArrow y z' ⥤ StructuredArrow y zB where
  obj x := StructuredArrow.mk (x.hom ≫ α.app x.right)
  map {x x'} m := StructuredArrow.homMk (e.map m.right) (by
    change (x.hom ≫ α.app x.right) ≫ zB.map (e.map m.right) = x'.hom ≫ α.app x'.right
    rw [← StructuredArrow.w m, Category.assoc, Category.assoc]
    exact congrArg (x.hom ≫ ·) (α.naturality m.right).symm)
  map_id x := by ext; simp
  map_comp f g := by ext; simp

/-- **The map `Ψ(z') ⟶ Ψ(z)` induced by a functor `e` and a natural transformation
`α : z' ⟶ e ⋙ z`**: the class of `φ : y ⟶ z'(a)` goes to the class of `φ ≫ α_a`. -/
@[simps]
def componentPresheafMapOfNatTrans {𝒜 : Type u₂} [Category.{v₃} 𝒜] {ℬ : Type u₂}
    [Category.{v₂} ℬ] {z' : 𝒜 ⥤ 𝒳} (e : 𝒜 ⥤ ℬ) (zB : ℬ ⥤ 𝒳) (α : z' ⟶ e ⋙ zB) :
    componentPresheaf z' ⟶ componentPresheaf zB where
  app y := ↾Quotient.map (structuredArrowMapOfNatTrans e zB α y.unop).obj
    (fun _ _ => zigzag_obj_of_zigzag (structuredArrowMapOfNatTrans e zB α y.unop))
  naturality y y' g := TypeCat.homEquiv.injective (funext fun c => by
    induction c using Quotient.inductionOn with
    | h x =>
      exact congrArg (Quotient.mk _)
        (by simp only [structuredArrowMapOfNatTrans_obj, StructuredArrow.map_obj_hom,
          StructuredArrow.map_mk, Category.assoc]; rfl))

/-- The map `Ψ(z') ⟶ Ψ(z)` induced by `α : z' ⟶ e ⋙ z` sends the class of `φ : y ⟶ z'(a)` to the
class of `φ ≫ α_a`. -/
@[simp]
lemma componentPresheafMapOfNatTrans_mk {𝒜 : Type u₂} [Category.{v₃} 𝒜] {ℬ : Type u₂}
    [Category.{v₂} ℬ] {z' : 𝒜 ⥤ 𝒳} (e : 𝒜 ⥤ ℬ) (zB : ℬ ⥤ 𝒳) (α : z' ⟶ e ⋙ zB) {y : 𝒳}
    {a : 𝒜} (φ : y ⟶ z'.obj a) :
    (componentPresheafMapOfNatTrans e zB α).app (op y) (componentMk z' φ) =
      componentMk zB (φ ≫ α.app a) := rfl

/-- The map of presheaves of components induced by a composite is the composite of the maps. -/
lemma componentPresheafMap_comp {𝒜 ℬ : Type u₂} [Category.{v₃} 𝒜] [Category.{v₃} ℬ]
    (e : 𝒜 ⥤ ℬ) (e' : ℬ ⥤ 𝒵) :
    componentPresheafMap z (e ⋙ e') = componentPresheafMap (e' ⋙ z) e ≫ componentPresheafMap z e' :=
  natTrans_ext fun y c => by
    induction c using Quotient.inductionOn
    rfl

/-! ### A terminal object -/

/-- **If `𝒵` has a terminal object `t`, the presheaf of components of `z` is the representable
presheaf of `z(t)`.** Every arrow `y ⟶ z(ζ)` is connected to its composite with
`z(ζ ⟶ t)`, and two arrows to `z(t)` in the same component agree, since the composite with the
morphism to `t` is invariant along morphisms of `𝒵`. -/
def componentPresheafIsoOfIsTerminal {t : 𝒵} (ht : Limits.IsTerminal t) :
    componentPresheaf z ≅ uliftYoneda.{u₂}.obj (z.obj t) :=
  NatIso.ofComponents (fun y => Equiv.toIso
    { toFun := fun c => (Quotient.lift (fun x : StructuredArrow y.unop z =>
          (ULift.up (x.hom ≫ z.map (ht.from x.right)) :
            (uliftYoneda.{u₂}.obj (z.obj t)).obj y))
        (fun x x' (h : Zigzag x x') => by
          induction h with
          | refl => rfl
          | tail _ hzag ih =>
            rw [ih]
            rcases hzag with ⟨⟨m⟩⟩ | ⟨⟨m⟩⟩
            · congr 1
              rw [← StructuredArrow.w m, Category.assoc, ← z.map_comp, ht.hom_ext
                (m.right ≫ ht.from _) (ht.from _)]
            · congr 1
              rw [← StructuredArrow.w m, Category.assoc, ← z.map_comp, ht.hom_ext
                (m.right ≫ ht.from _) (ht.from _)]) c)
      invFun := fun f => componentMk z f.down
      left_inv := fun c => by
        induction c using Quotient.inductionOn with
        | h x =>
          change componentMk z (x.hom ≫ z.map (ht.from x.right)) = _
          rw [← componentMk_eq_of_comp]
          exact congrArg (Quotient.mk _) (StructuredArrow.eq_mk x).symm
      right_inv := fun f => by
        change ULift.up (f.down ≫ z.map (ht.from t)) = f
        rw [ht.hom_ext (ht.from t) (𝟙 t), z.map_id, Category.comp_id] })
    (fun {y y'} g => TypeCat.homEquiv.injective (funext fun c => by
      induction c using Quotient.inductionOn with
      | h x =>
        change ULift.up ((g.unop ≫ x.hom) ≫ z.map (ht.from x.right)) =
          ULift.up (g.unop ≫ x.hom ≫ z.map (ht.from x.right))
        rw [Category.assoc]))

/-! ### The identity functor -/

/-- **The presheaf of components of the identity functor is the final presheaf**: each of its
values has exactly one element, the class of the identity arrow, to which every arrow
`y ⟶ y'` is connected by itself. -/
@[instance_reducible]
def componentPresheafIdUnique (y : 𝒳ᵒᵖ) : Unique ((componentPresheaf (𝟭 𝒳)).obj y) where
  default := componentMk (𝟭 𝒳) (𝟙 y.unop)
  uniq c := by
    induction c using Quotient.inductionOn with
    | h x =>
      refine Quot.sound (Zigzag.symm (Zigzag.of_hom ?_))
      exact StructuredArrow.homMk x.hom (by simp)

/-! ### Morphisms of categories fibred in groupoids -/

/-- A morphism over an identity has an `eqToHom` as its image. -/
private theorem map_eq_eqToHom_of_isHomLift_id_aux {𝒞 : Type*} [Category 𝒞] (p : 𝒳 ⥤ 𝒞)
    {y x : 𝒳} (φ : y ⟶ x) [p.IsHomLift (𝟙 (p.obj y)) φ] :
    ∃ h : p.obj y = p.obj x, p.map φ = eqToHom h := by
  refine ⟨(IsHomLift.codomain_eq p (𝟙 (p.obj y)) φ).symm, ?_⟩
  rw [IsHomLift.fac' p (𝟙 (p.obj y)) φ]
  simp

/-- A morphism of `𝒵` relating two arrows over identities lies over an identity. -/
private theorem isHomLift_id_of_comp_eq_aux {𝒞 : Type*} [Category 𝒞] (p : 𝒳 ⥤ 𝒞) {y : 𝒳}
    {ζ₁ ζ₂ : 𝒵} (φ₁ : y ⟶ z.obj ζ₁) (φ₂ : y ⟶ z.obj ζ₂)
    [p.IsHomLift (𝟙 (p.obj y)) φ₁] [p.IsHomLift (𝟙 (p.obj y)) φ₂]
    (ψ : ζ₁ ⟶ ζ₂) (hψ : φ₁ ≫ z.map ψ = φ₂) :
    (z ⋙ p).IsHomLift (𝟙 ((z ⋙ p).obj ζ₁)) ψ := by
  obtain ⟨k₁, hk₁⟩ := map_eq_eqToHom_of_isHomLift_id_aux p φ₁
  obtain ⟨k₂, hk₂⟩ := map_eq_eqToHom_of_isHomLift_id_aux p φ₂
  have h := congrArg p.map hψ
  rw [p.map_comp, hk₁, hk₂] at h
  refine IsHomLift.of_fac' (z ⋙ p) _ ψ rfl (k₂.symm.trans k₁) ?_
  simp only [Functor.comp_map, eqToHom_refl, Category.id_comp]
  rw [← cancel_epi (eqToHom k₁), h, eqToHom_trans]

/-- A morphism over an identity in a category fibred in groupoids is an isomorphism. -/
private theorem isIso_of_isHomLift_id_fibered {𝒟 : Type*} [Category 𝒟] {𝒞 : Type*} [Category 𝒞]
    (p : 𝒟 ⥤ 𝒞) (hp : p.IsFiberedInGroupoids) {x x' : 𝒟} (φ : x ⟶ x')
    [p.IsHomLift (𝟙 (p.obj x)) φ] : IsIso φ := by
  have : p.IsStronglyCartesian (𝟙 (p.obj x)) φ := hp.isStronglyCartesian_homLift _ _
  exact Functor.IsStronglyCartesian.isIso_of_base_isIso p (𝟙 (p.obj x)) φ

section Fibred

variable {𝒞 : Type u₃} [Category.{v₃} 𝒞] (p : 𝒳 ⥤ 𝒞) (hp : p.IsFiberedInGroupoids)
  (hz : (z ⋙ p).IsFiberedInGroupoids)

include hp hz

/-- **Every arrow to the image of a morphism of fibred categories factors through a vertical
one.** For `φ : y ⟶ z(ζ)` there are a lift `c : ζ' ⟶ ζ` of the base morphism of `φ` and a
morphism `φ' : y ⟶ z(ζ')` over an identity with `φ = φ' ≫ z(c)`: the lift exists because `𝒵` is
fibred, and `φ'` because `z(c)` is cartesian, `𝒳` being fibred in groupoids. -/
lemma exists_vertical_factor {y : 𝒳} {ζ : 𝒵} (φ : y ⟶ z.obj ζ) :
    ∃ (ζ' : 𝒵) (φ' : y ⟶ z.obj ζ') (c : ζ' ⟶ ζ),
      p.IsHomLift (𝟙 (p.obj y)) φ' ∧ φ' ≫ z.map c = φ := by
  obtain ⟨ζ', c, hc⟩ := hz.exists_lift (p.map φ) ζ rfl
  have h₁ : p.IsHomLift (p.map φ) (z.map c) :=
    PresheafOfCategories.isHomLift_map_of_comp rfl (p.map φ) c hc
  have : p.IsStronglyCartesian (p.map φ) (z.map c) := hp.isStronglyCartesian_homLift _ _
  exact ⟨ζ', Functor.IsStronglyCartesian.map p (p.map φ) (z.map c) (Category.id_comp _).symm φ,
    c, inferInstance, Functor.IsStronglyCartesian.fac p (p.map φ) (z.map c) _ φ⟩

omit hp hz in
/-- A morphism over an identity has an `eqToHom` as its image. -/
lemma map_eq_eqToHom_of_isHomLift_id {y x : 𝒳} (φ : y ⟶ x) [p.IsHomLift (𝟙 (p.obj y)) φ] :
    ∃ h : p.obj y = p.obj x, p.map φ = eqToHom h :=
  map_eq_eqToHom_of_isHomLift_id_aux p φ

/-- **The comparison of two vertical factorizations along a morphism of arrows.** If `φ₁` and
`φ₂` are arrows to the image of `z` related by a morphism `m` of `𝒵`, any vertical factorizations
`φᵢ = φᵢ' ≫ z(cᵢ)` are related by a morphism `ψ` with `φ₁' ≫ z(ψ) = φ₂'`: it is the lift of
`c₁ ≫ m` through the cartesian morphism `c₂`. -/
lemma exists_comp_eq_of_vertical_factors {y : 𝒳} {ζ₁ ζ₂ ζ₁' ζ₂' : 𝒵} (m : ζ₁ ⟶ ζ₂)
    (φ₁ : y ⟶ z.obj ζ₁) (φ₂ : y ⟶ z.obj ζ₂) (hm : φ₁ ≫ z.map m = φ₂)
    (φ₁' : y ⟶ z.obj ζ₁') (c₁ : ζ₁' ⟶ ζ₁) [p.IsHomLift (𝟙 (p.obj y)) φ₁']
    (e₁ : φ₁' ≫ z.map c₁ = φ₁)
    (φ₂' : y ⟶ z.obj ζ₂') (c₂ : ζ₂' ⟶ ζ₂) [p.IsHomLift (𝟙 (p.obj y)) φ₂']
    (e₂ : φ₂' ≫ z.map c₂ = φ₂) :
    ∃ ψ : ζ₁' ⟶ ζ₂', φ₁' ≫ z.map ψ = φ₂' := by
  obtain ⟨h₁, hφ₁⟩ := map_eq_eqToHom_of_isHomLift_id p φ₁'
  obtain ⟨h₂, hφ₂⟩ := map_eq_eqToHom_of_isHomLift_id p φ₂'
  have hbase : (z ⋙ p).map (c₁ ≫ m) = eqToHom (h₁.symm.trans h₂) ≫ (z ⋙ p).map c₂ := by
    have k : p.map φ₁' ≫ p.map (z.map (c₁ ≫ m)) = p.map φ₂' ≫ p.map (z.map c₂) := by
      rw [← p.map_comp, ← p.map_comp, z.map_comp, ← Category.assoc, e₁, hm, e₂]
    rw [hφ₁, hφ₂] at k
    simp only [Functor.comp_map]
    rw [← cancel_epi (eqToHom h₁), k, eqToHom_trans_assoc]
  have : (z ⋙ p).IsStronglyCartesian ((z ⋙ p).map c₂) c₂ := hz.isStronglyCartesian_homLift _ _
  let ψ := Functor.IsStronglyCartesian.map (z ⋙ p) ((z ⋙ p).map c₂) c₂ hbase (c₁ ≫ m)
  have hψ : ψ ≫ c₂ = c₁ ≫ m := Functor.IsStronglyCartesian.fac _ _ _ _ _
  refine ⟨ψ, ?_⟩
  have hzc : p.IsHomLift (p.map (z.map c₂)) (z.map c₂) := inferInstance
  have : p.IsStronglyCartesian (p.map (z.map c₂)) (z.map c₂) := hp.isStronglyCartesian_homLift _ _
  have hψbase : p.map (z.map ψ) = eqToHom (h₁.symm.trans h₂) := by
    have := Functor.IsStronglyCartesian.map_isHomLift (z ⋙ p) ((z ⋙ p).map c₂) c₂ hbase (c₁ ≫ m)
    have h := IsHomLift.fac' (z ⋙ p) (eqToHom (h₁.symm.trans h₂)) ψ
    simpa using h
  have hl₁ : p.IsHomLift (p.map φ₂') (φ₁' ≫ z.map ψ) := by
    have h : p.map (φ₁' ≫ z.map ψ) = p.map φ₂' := by
      rw [p.map_comp, hφ₁, hψbase, hφ₂, eqToHom_trans]
    rw [← h]
    infer_instance
  refine Functor.IsStronglyCartesian.ext p (p.map (z.map c₂)) (z.map c₂) (p.map φ₂') ?_
  rw [Category.assoc, ← z.map_comp, hψ, z.map_comp, ← Category.assoc, e₁, hm, e₂]

/-- **Two vertical arrows in the same component differ by a morphism of `𝒵`.** If `φ₁` and `φ₂`
are arrows to the image of `z` over identities with the same class in the presheaf of
components, then `φ₂ = φ₁ ≫ z(ψ)` for some `ψ : ζ₁ ⟶ ζ₂`.

The relation "any two vertical factorizations are related by a morphism of `𝒵`" holds between
the endpoints of every morphism of arrows, by
`Stacks.Sites.CoverDescent.exists_comp_eq_of_vertical_factors`, it is transitive because vertical
factorizations exist, and it is symmetric because a morphism of `𝒵` lying over an isomorphism is
an isomorphism; so it holds between any two arrows joined by a zigzag. -/
lemma exists_comp_eq_of_componentMk_eq {y : 𝒳} {ζ₁ ζ₂ : 𝒵} (φ₁ : y ⟶ z.obj ζ₁)
    (φ₂ : y ⟶ z.obj ζ₂) [p.IsHomLift (𝟙 (p.obj y)) φ₁] [p.IsHomLift (𝟙 (p.obj y)) φ₂]
    (h : componentMk z φ₁ = componentMk z φ₂) : ∃ ψ : ζ₁ ⟶ ζ₂, φ₁ ≫ z.map ψ = φ₂ := by
  let R : StructuredArrow y z → StructuredArrow y z → Prop := fun x x' =>
    ∀ (ζ ζ' : 𝒵) (φ : y ⟶ z.obj ζ) (c : ζ ⟶ x.right) (φ' : y ⟶ z.obj ζ')
      (c' : ζ' ⟶ x'.right), p.IsHomLift (𝟙 (p.obj y)) φ → p.IsHomLift (𝟙 (p.obj y)) φ' →
      φ ≫ z.map c = x.hom → φ' ≫ z.map c' = x'.hom → ∃ ψ : ζ ⟶ ζ', φ ≫ z.map ψ = φ'
  have hhom : ∀ {x x' : StructuredArrow y z} (f : x ⟶ x'), R x x' := by
    intro x x' f ζ ζ' φ c φ' c' hφ hφ' e e'
    exact exists_comp_eq_of_vertical_factors z p hp hz f.right x.hom x'.hom
      (StructuredArrow.w f) φ c e φ' c' e'
  have hsymm : ∀ {x x' : StructuredArrow y z}, R x x' → R x' x := by
    intro x x' hR ζ ζ' φ c φ' c' hφ hφ' e e'
    obtain ⟨ψ, hψ⟩ := hR ζ' ζ φ' c' φ c hφ' hφ e' e
    have := isHomLift_id_of_comp_eq_aux z p φ' φ ψ hψ
    have : IsIso ψ := isIso_of_isHomLift_id_fibered (z ⋙ p) hz ψ
    refine ⟨inv ψ, ?_⟩
    rw [← hψ, Category.assoc, ← z.map_comp, IsIso.hom_inv_id, z.map_id, Category.comp_id]
  have htrans : ∀ {x x' x'' : StructuredArrow y z}, R x x' → R x' x'' → R x x'' := by
    intro x x' x'' hR hR' ζ ζ'' φ c φ'' c'' hφ hφ'' e e''
    obtain ⟨ζ', φ', c', hφ', e'⟩ := exists_vertical_factor z p hp hz x'.hom
    obtain ⟨ψ, hψ⟩ := hR ζ ζ' φ c φ' c' hφ hφ' e e'
    obtain ⟨ψ', hψ'⟩ := hR' ζ' ζ'' φ' c' φ'' c'' hφ' hφ'' e' e''
    exact ⟨ψ ≫ ψ', by rw [z.map_comp, ← Category.assoc, hψ, hψ']⟩
  have hzig : ∀ {x x' : StructuredArrow y z}, Zigzag x x' → R x x' := by
    intro x x' hxx'
    induction hxx' with
    | refl => exact hhom (𝟙 _)
    | tail _ hzag ih =>
      rcases hzag with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
      · exact htrans ih (hhom f)
      · exact htrans ih (hsymm (hhom f))
  exact hzig (Quotient.exact h) ζ₁ ζ₂ φ₁ (𝟙 _) φ₂ (𝟙 _) inferInstance inferInstance
    (by simp) (by simp)

/-- Every class in the presheaf of components of a morphism of fibred categories is represented
by an arrow over an identity. -/
lemma exists_vertical_componentMk {y : 𝒳} (c : (componentPresheaf z).obj (op y)) :
    ∃ (ζ : 𝒵) (φ : y ⟶ z.obj ζ), p.IsHomLift (𝟙 (p.obj y)) φ ∧ componentMk z φ = c := by
  obtain ⟨ζ, φ, rfl⟩ := componentMk_surjective z c
  obtain ⟨ζ', φ', c', hφ', e⟩ := exists_vertical_factor z p hp hz φ
  exact ⟨ζ', φ', hφ', by rw [componentMk_eq_of_comp z φ' c', e]⟩

omit hp hz in
/-- A morphism of `𝒵` relating two arrows over identities lies over an identity. -/
lemma isHomLift_id_of_comp_eq {y : 𝒳} {ζ₁ ζ₂ : 𝒵} (φ₁ : y ⟶ z.obj ζ₁) (φ₂ : y ⟶ z.obj ζ₂)
    [p.IsHomLift (𝟙 (p.obj y)) φ₁] [p.IsHomLift (𝟙 (p.obj y)) φ₂] (ψ : ζ₁ ⟶ ζ₂)
    (hψ : φ₁ ≫ z.map ψ = φ₂) : (z ⋙ p).IsHomLift (𝟙 ((z ⋙ p).obj ζ₁)) ψ :=
  isHomLift_id_of_comp_eq_aux z p φ₁ φ₂ ψ hψ

end Fibred

/-! ### 2-fibre products -/

section TwoFibreProduct

variable {𝒞 : Type (v₂ + 1)} [Category.{v₂} 𝒞] {𝒜 ℬ 𝒮 : Type (v₂ + 1)} [Category.{v₂} 𝒜]
  [Category.{v₂} ℬ] [Category.{v₂} 𝒮] (p : 𝒳 ⥤ 𝒞) (zS : 𝒮 ⥤ 𝒳)
  (pA : 𝒜 ⥤ 𝒞) (pB : ℬ ⥤ 𝒞) (pS : 𝒮 ⥤ 𝒞) (eA : 𝒜 ⥤ 𝒮) (eB : ℬ ⥤ 𝒮)

/-- **The comparison of the presheaf of components of a 2-fibre product with the fibre product
of the presheaves of components.** The class of `φ : y ⟶ z(a)` for an object `(a, b, ι)` of
`𝒜 ×_𝒮 ℬ` goes to the pair of classes of `φ`, read as an arrow to the image of `a`, and of
`φ ≫ z(ι)`, read as an arrow to the image of `b`. -/
def componentPresheafTwoFibreProductHom :
    componentPresheaf (TwoFibreProductOver.fst pA pB pS eA eB ⋙ eA ⋙ zS) ⟶
      fibreProductPresheaf (componentPresheafMap zS eA) (componentPresheafMap zS eB) :=
  fibreProductLift _ _ (componentPresheafMap (eA ⋙ zS) (TwoFibreProductOver.fst pA pB pS eA eB))
    (componentPresheafMapOfNatTrans (TwoFibreProductOver.snd pA pB pS eA eB) (eB ⋙ zS)
      (Functor.whiskerRight (TwoFibreProductOver.psi pA pB pS eA eB) zS))
    (natTrans_ext fun y c => by
      obtain ⟨ξ, φ, rfl⟩ := componentMk_surjective _ c
      exact componentMk_eq_of_comp zS φ ξ.iso.hom)

/-- The comparison map sends the class of `φ : y ⟶ z(a)`, for an object `(a, b, ι)` of the
2-fibre product, to the pair of the class of `φ` and the class of `φ ≫ z(ι)`. -/
lemma componentPresheafTwoFibreProductHom_mk {y : 𝒳}
    (ξ : TwoFibreProductOver pA pB pS eA eB) (φ : y ⟶ zS.obj (eA.obj ξ.x)) :
    ((componentPresheafTwoFibreProductHom zS pA pB pS eA eB).app (op y)
      (componentMk (TwoFibreProductOver.fst pA pB pS eA eB ⋙ eA ⋙ zS) φ)).1 =
      (componentMk (eA ⋙ zS) φ, componentMk (eB ⋙ zS) (φ ≫ zS.map ξ.iso.hom)) := rfl

/-- **The presheaf of components of a 2-fibre product of categories fibred in groupoids is the
fibre product of the presheaves of components**, as soon as `z : 𝒮 ⥤ 𝒳` is faithful.

Surjectivity: represent the two classes by arrows over identities; their images in the
presheaf of components of `z` agree, so the two arrows differ by a morphism `ψ` of `𝒮`, which
lies over an identity and hence is an isomorphism, and the object `(a, b, ψ)` of the 2-fibre
product is a preimage. Injectivity: two vertical arrows to the image of the 2-fibre product with
the same images differ by morphisms `α` on the first and `β` on the second component; faithfulness
of `z` makes `(α, β)` a morphism of the 2-fibre product, which joins the two arrows. -/
lemma bijective_componentPresheafTwoFibreProductHom (hp : p.IsFiberedInGroupoids)
    (hS : (zS ⋙ p).IsFiberedInGroupoids) (hA : (eA ⋙ zS ⋙ p).IsFiberedInGroupoids)
    (hB : (eB ⋙ zS ⋙ p).IsFiberedInGroupoids) (hpA : eA ⋙ zS ⋙ p = pA)
    (hpB : eB ⋙ zS ⋙ p = pB) (hpS : zS ⋙ p = pS) [zS.Faithful] (y : 𝒳ᵒᵖ) :
    Function.Bijective ((componentPresheafTwoFibreProductHom zS pA pB pS eA eB).app y) := by
  subst hpA hpB hpS
  obtain ⟨y⟩ := y
  have hP : ((TwoFibreProductOver.fst (eA ⋙ zS ⋙ p) (eB ⋙ zS ⋙ p) (zS ⋙ p) eA eB ⋙ eA ⋙ zS) ⋙
      p).IsFiberedInGroupoids := by
    have := TwoFibreProductOver.isFiberedInGroupoids (eA ⋙ zS ⋙ p) (eB ⋙ zS ⋙ p) (zS ⋙ p) eA eB
      hA hB hS rfl rfl
    rwa [← TwoFibreProductOver.fst_comp_eq] at this
  refine ⟨fun c₁ c₂ h => ?_, fun x => ?_⟩
  · obtain ⟨ξ₁, φ₁, hφ₁, rfl⟩ : ∃ (ξ₁ : TwoFibreProductOver (eA ⋙ zS ⋙ p) (eB ⋙ zS ⋙ p)
        (zS ⋙ p) eA eB) (φ₁ : y ⟶ zS.obj (eA.obj ξ₁.x)), p.IsHomLift (𝟙 (p.obj y)) φ₁ ∧
        componentMk (TwoFibreProductOver.fst _ _ _ eA eB ⋙ eA ⋙ zS) φ₁ = c₁ :=
      exists_vertical_componentMk _ p hp hP c₁
    obtain ⟨ξ₂, φ₂, hφ₂, rfl⟩ : ∃ (ξ₂ : TwoFibreProductOver (eA ⋙ zS ⋙ p) (eB ⋙ zS ⋙ p)
        (zS ⋙ p) eA eB) (φ₂ : y ⟶ zS.obj (eA.obj ξ₂.x)), p.IsHomLift (𝟙 (p.obj y)) φ₂ ∧
        componentMk (TwoFibreProductOver.fst _ _ _ eA eB ⋙ eA ⋙ zS) φ₂ = c₂ :=
      exists_vertical_componentMk _ p hp hP c₂
    have h' : (componentMk (eA ⋙ zS) φ₁, componentMk (eB ⋙ zS) (φ₁ ≫ zS.map ξ₁.iso.hom)) =
        (componentMk (eA ⋙ zS) φ₂, componentMk (eB ⋙ zS) (φ₂ ≫ zS.map ξ₂.iso.hom)) :=
      congrArg Subtype.val h
    rw [Prod.mk.injEq] at h'
    obtain ⟨α, hα⟩ : ∃ α : ξ₁.x ⟶ ξ₂.x, φ₁ ≫ zS.map (eA.map α) = φ₂ :=
      exists_comp_eq_of_componentMk_eq (eA ⋙ zS) p hp hA φ₁ φ₂ h'.1
    have hι : ∀ ξ : TwoFibreProductOver (eA ⋙ zS ⋙ p) (eB ⋙ zS ⋙ p) (zS ⋙ p) eA eB,
        p.IsHomLift (𝟙 ξ.base) (zS.map ξ.iso.hom) := fun ξ =>
      PresheafOfCategories.isHomLift_map_of_comp rfl _ _ ξ.vertical
    have : p.IsHomLift (𝟙 (p.obj y)) (φ₁ ≫ zS.map ξ₁.iso.hom) := by
      have := hι ξ₁
      exact IsHomLift.comp_lift_id_right' p (𝟙 (p.obj y)) φ₁ ξ₁.base _
    have : p.IsHomLift (𝟙 (p.obj y)) (φ₂ ≫ zS.map ξ₂.iso.hom) := by
      have := hι ξ₂
      exact IsHomLift.comp_lift_id_right' p (𝟙 (p.obj y)) φ₂ ξ₂.base _
    obtain ⟨β, hβ⟩ : ∃ β : ξ₁.y ⟶ ξ₂.y, (φ₁ ≫ zS.map ξ₁.iso.hom) ≫ zS.map (eB.map β) =
        φ₂ ≫ zS.map ξ₂.iso.hom :=
      exists_comp_eq_of_componentMk_eq (eB ⋙ zS) p hp hB _ _ h'.2
    have : IsIso φ₁ := isIso_of_isHomLift_id_fibered p hp φ₁
    have hw : eA.map α ≫ ξ₂.iso.hom = ξ₁.iso.hom ≫ eB.map β := by
      apply zS.map_injective
      apply (cancel_epi φ₁).1
      exact ((congrArg (φ₁ ≫ ·) (zS.map_comp _ _)).trans (Category.assoc _ _ _).symm).trans
        ((congrArg (· ≫ zS.map ξ₂.iso.hom) hα).trans (hβ.symm.trans
          ((Category.assoc _ _ _).trans (congrArg (φ₁ ≫ ·) (zS.map_comp _ _).symm))))
    have hbase : eqToHom ξ₁.hy.symm ≫ (eB ⋙ zS ⋙ p).map β ≫ eqToHom ξ₂.hy =
        eqToHom ξ₁.hx.symm ≫ (eA ⋙ zS ⋙ p).map α ≫ eqToHom ξ₂.hx := by
      have hι' : ∀ ξ : TwoFibreProductOver (eA ⋙ zS ⋙ p) (eB ⋙ zS ⋙ p) (zS ⋙ p) eA eB,
          (zS ⋙ p).map ξ.iso.hom = eqToHom (ξ.hx.trans ξ.hy.symm) := by
        intro ξ
        have := ξ.vertical
        rw [IsHomLift.fac' (zS ⋙ p) (𝟙 ξ.base) ξ.iso.hom]
        simp
      have k : (zS ⋙ p).map (eA.map α) ≫ (zS ⋙ p).map ξ₂.iso.hom =
          (zS ⋙ p).map ξ₁.iso.hom ≫ (zS ⋙ p).map (eB.map β) := by
        rw [← Functor.map_comp, ← Functor.map_comp]
        exact congrArg (zS ⋙ p).map hw
      rw [hι', hι'] at k
      have key : (zS ⋙ p).map (eB.map β) =
          eqToHom (ξ₁.hx.trans ξ₁.hy.symm).symm ≫ (zS ⋙ p).map (eA.map α) ≫
            eqToHom (ξ₂.hx.trans ξ₂.hy.symm) := by
        rw [k]
        simp
      show eqToHom _ ≫ (zS ⋙ p).map (eB.map β) ≫ eqToHom _ =
        eqToHom _ ≫ (zS ⋙ p).map (eA.map α) ≫ eqToHom _
      rw [key]
      simp
    let m : ξ₁ ⟶ ξ₂ := TwoFibreProductOver.Hom.mk' α β hbase hw
    exact Quot.sound (Zigzag.of_hom (StructuredArrow.homMk m hα))
  · obtain ⟨⟨cA, cB⟩, hx⟩ := x
    obtain ⟨a, φa, hφa, rfl⟩ := exists_vertical_componentMk _ p hp hA cA
    obtain ⟨b, φb, hφb, rfl⟩ := exists_vertical_componentMk _ p hp hB cB
    obtain ⟨ψ, hψ⟩ := exists_comp_eq_of_componentMk_eq zS p hp hS φa φb hx
    have hψv := isHomLift_id_of_comp_eq zS p φa φb ψ hψ
    have : IsIso ψ := isIso_of_isHomLift_id_fibered (zS ⋙ p) hS ψ
    let ξ : TwoFibreProductOver (eA ⋙ zS ⋙ p) (eB ⋙ zS ⋙ p) (zS ⋙ p) eA eB :=
      { base := (eA ⋙ zS ⋙ p).obj a
        x := a
        y := b
        hx := rfl
        hy := (IsHomLift.codomain_eq (zS ⋙ p) (𝟙 ((zS ⋙ p).obj (eA.obj a))) ψ)
        iso := asIso ψ
        vertical := hψv }
    refine ⟨componentMk (TwoFibreProductOver.fst _ _ _ eA eB ⋙ eA ⋙ zS) (ζ := ξ) φa, ?_⟩
    refine Subtype.ext ?_
    rw [componentPresheafTwoFibreProductHom_mk]
    exact Prod.ext rfl (congrArg (componentMk (eB ⋙ zS)) hψ)

end TwoFibreProduct

/-! ### Local surjectivity -/

section LocallySurjective

variable {𝒞 : Type u₃} [Category.{v₃} 𝒞] (p : 𝒳 ⥤ 𝒞) (J : GrothendieckTopology 𝒳)

/-- **The map of presheaves of components induced by a covering functor is locally
surjective.** Suppose that every arrow `φ : y ⟶ z(ζ)` becomes, along the members `g` of a covering
sieve of `y`, a composite with the image of a morphism `α : e(a) ⟶ ζ` over the base morphism of
`g ≫ φ`. Then `Ψ(e ⋙ z) ⟶ Ψ(z)` is locally surjective: the restriction of the class of `φ` along
such a `g` is the class of the arrow `y' ⟶ z(e(a))` through which `g ≫ φ` factors, `z(α)` being
cartesian. -/
lemma isLocallySurjective_componentPresheafMap {𝒜 : Type u₂} [Category.{v₃} 𝒜] (e : 𝒜 ⥤ 𝒵)
    (hp : p.IsFiberedInGroupoids)
    (h : ∀ ⦃y : 𝒳⦄ ⦃ζ : 𝒵⦄ (φ : y ⟶ z.obj ζ), ∃ S ∈ J y, ∀ ⦃y' : 𝒳⦄ ⦃g : y' ⟶ y⦄,
      S.arrows g → ∃ (a : 𝒜) (α : e.obj a ⟶ ζ), p.IsHomLift (p.map (g ≫ φ)) (z.map α)) :
    Presheaf.IsLocallySurjective J (componentPresheafMap z e) where
  imageSieve_mem {y} c := by
    obtain ⟨ζ, φ, rfl⟩ := componentMk_surjective z c
    obtain ⟨S, hS, hSlift⟩ := h φ
    refine J.superset_covering (fun y' g hg => ?_) hS
    obtain ⟨a, α, hα⟩ := hSlift hg
    have : p.IsStronglyCartesian (p.map (g ≫ φ)) (z.map α) := hp.isStronglyCartesian_homLift _ _
    let ψ := Functor.IsStronglyCartesian.map p (p.map (g ≫ φ)) (z.map α)
      (Category.id_comp _).symm (g ≫ φ)
    refine ⟨componentMk (e ⋙ z) ψ, ?_⟩
    show componentMk z ψ = componentMk z (g ≫ φ)
    rw [componentMk_eq_of_comp z ψ α, Functor.IsStronglyCartesian.fac]

end LocallySurjective

end Stacks.Sites.CoverDescent

end
