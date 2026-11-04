module

public import Mathlib.CategoryTheory.Bicategory.Grothendieck
public import Mathlib.CategoryTheory.Comma.Basic
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.Strict.Pseudofunctor
public import Mathlib.CategoryTheory.Bicategory.Functor.Cat
public import Mathlib.CategoryTheory.FiberedCategory.Grothendieck

/-!
# Inverse images in the Grothendieck construction of a pseudofunctor

Let `F` be a pseudofunctor from `𝒮ᵒᵖ` to categories and `G : 𝒟 ⥤ 𝒮` a functor. An object of the
comma category `Comma G (forget F)` is a triple `(A, (X, L), q : G A ⟶ X)` of an object of `𝒟`,
an object of the Grothendieck construction `∫ᶜ F` and a morphism of `𝒮`; sending it to the pair
`(A, q^* L)` of the Grothendieck construction of `F ∘ G` is a functor, whose value on a
morphism `(h, (f, φ))` is `h` together with the composite
`q'^* L' ⟶ q'^* f^* L ≅ (f ∘ q')^* L = (q ∘ G h)^* L ≅ (G h)^* q^* L`.

This is how a family over `X` together with a module `L` on `X` gives, for every point of the
base, the inverse image of `L` on the base change of the family, compatibly with all morphisms:
the functor laws are the coherences of the pseudofunctor `F`, proved here once at an abstract
pseudofunctor.

## Main definitions

* `CategoryTheory.Pseudofunctor.CoGrothendieck.inverseImage`: the functor.
* `CategoryTheory.Pseudofunctor.CoGrothendieck.forgetComp`: `(A, M) ↦ (G A, M)`.

## Main results

* `CategoryTheory.Pseudofunctor.CoGrothendieck.isIso_fiber_of_isIso`: the fibre of an isomorphism
  of a Grothendieck construction is an isomorphism.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Pseudofunctor.CoGrothendieck

open Opposite Bicategory

universe v₁ u₁ v₂ u₂ v₃ u₃

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒟 : Type u₃} [Category.{v₃} 𝒟]
  (F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}) (G : 𝒟 ⥤ 𝒮)

section Generic

variable {B : Type*} [Bicategory B] [Strict B] (F : Pseudofunctor B Cat.{v₂, u₂})

/-- The comparison of inverse images along a commutative square `f ≫ q = k = q' ≫ g`, applied
after the inverse image along `q` of a morphism `φ : Y ⟶ f^* Y'`. -/
def squareFiber {x x' y y' : B} (q : x ⟶ y) (q' : x' ⟶ y') (f : x' ⟶ x) (g : y' ⟶ y)
    (k : x' ⟶ y) (h₁ : f ≫ q = k) (h₂ : q' ≫ g = k) {Y : F.obj x} {Y' : F.obj x'}
    (φ : Y ⟶ (F.map f).toFunctor.obj Y') :
    (F.map q).toFunctor.obj Y ⟶ (F.map g).toFunctor.obj ((F.map q').toFunctor.obj Y') :=
  (F.map q).toFunctor.map φ ≫ (F.mapComp' f q k h₁).inv.toNatTrans.app Y' ≫
    (F.mapComp' q' g k h₂).hom.toNatTrans.app Y'

/-- The two-cell identity behind `squareFiber_comp`. -/
theorem squareFiber_comp_two_cell {x x' x'' y y' y'' : B} (q : x ⟶ y) (q' : x' ⟶ y')
    (q'' : x'' ⟶ y'') (f : x' ⟶ x) (g : y' ⟶ y) (k : x' ⟶ y) (h₁ : f ≫ q = k)
    (h₂ : q' ≫ g = k) (f' : x'' ⟶ x') (g' : y'' ⟶ y') (k' : x'' ⟶ y') (h₁' : f' ≫ q' = k')
    (h₂' : q'' ≫ g' = k') (f'' : x'' ⟶ x) (hf : f' ≫ f = f'') (g'' : y'' ⟶ y)
    (hg : g' ≫ g = g'') (k'' : x'' ⟶ y) (h₁'' : f'' ≫ q = k'') (h₂'' : q'' ≫ g'' = k'') :
    (F.mapComp' f' f f'' hf).inv ▷ F.map q ≫ (F.mapComp' f'' q k'' h₁'').inv ≫
        (F.mapComp' q'' g'' k'' h₂'').hom =
      (α_ _ _ _).hom ≫ F.map f' ◁ ((F.mapComp' f q k h₁).inv ≫ (F.mapComp' q' g k h₂).hom) ≫
        (α_ _ _ _).inv ≫
        ((F.mapComp' f' q' k' h₁').inv ≫ (F.mapComp' q'' g' k' h₂').hom) ▷ F.map g ≫
        (α_ _ _ _).hom ≫ F.map q'' ◁ (F.mapComp' g' g g'' hg).inv := by
  have hk : f' ≫ k = k'' := by rw [← h₁'', ← hf, ← h₁, Category.assoc]
  have hk' : k' ≫ g = k'' := by rw [← hk, ← h₁', Category.assoc, h₂]
  have e1 : (F.mapComp' f' f f'' hf).inv ▷ F.map q ≫ (F.mapComp' f'' q k'' h₁'').inv =
      (α_ _ _ _).hom ≫ F.map f' ◁ (F.mapComp' f q k h₁).inv ≫
        (F.mapComp' f' k k'' hk).inv := by
    rw [F.mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv f' f q f'' k k'' hf h₁ h₁'']
  have e2 : (F.mapComp' f' k k'' hk).inv =
      F.map f' ◁ (F.mapComp' q' g k h₂).hom ≫ (α_ _ _ _).inv ≫
        (F.mapComp' f' q' k' h₁').inv ▷ F.map g ≫
        (F.mapComp' k' g k'' hk').inv :=
    F.mapComp'₀₁₃_inv f' q' g k' k k'' h₁' h₂ hk
  have e3 : (F.mapComp' k' g k'' hk').inv ≫
      (F.mapComp' q'' g'' k'' h₂'').hom =
      (F.mapComp' q'' g' k' h₂').hom ▷ F.map g ≫ (α_ _ _ _).hom ≫
        F.map q'' ◁ (F.mapComp' g' g g'' hg).inv :=
    F.mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom q'' g' g k' g'' k'' h₂' hg hk'
  rw [reassoc_of% e1, e2]
  simp only [Category.assoc, e3, Bicategory.whiskerLeft_comp, Bicategory.comp_whiskerRight]

/-- **The inverse images along two pasted squares compose.** -/
theorem squareFiber_comp {x x' x'' y y' y'' : B} (q : x ⟶ y) (q' : x' ⟶ y')
    (q'' : x'' ⟶ y'') (f : x' ⟶ x) (g : y' ⟶ y) (k : x' ⟶ y) (h₁ : f ≫ q = k)
    (h₂ : q' ≫ g = k) (f' : x'' ⟶ x') (g' : y'' ⟶ y') (k' : x'' ⟶ y') (h₁' : f' ≫ q' = k')
    (h₂' : q'' ≫ g' = k') (f'' : x'' ⟶ x) (hf : f' ≫ f = f'') (g'' : y'' ⟶ y)
    (hg : g' ≫ g = g'') (k'' : x'' ⟶ y) (h₁'' : f'' ≫ q = k'') (h₂'' : q'' ≫ g'' = k'')
    {Y : F.obj x} {Y' : F.obj x'} {Y'' : F.obj x''} (φ : Y ⟶ (F.map f).toFunctor.obj Y')
    (φ' : Y' ⟶ (F.map f').toFunctor.obj Y'') :
    squareFiber F q q'' f'' g'' k'' h₁'' h₂''
        (φ ≫ (F.map f).toFunctor.map φ' ≫ (F.mapComp' f' f f'' hf).inv.toNatTrans.app Y'') =
      squareFiber F q q' f g k h₁ h₂ φ ≫
        (F.map g).toFunctor.map (squareFiber F q' q'' f' g' k' h₁' h₂' φ') ≫
        (F.mapComp' g' g g'' hg).inv.toNatTrans.app ((F.map q'').toFunctor.obj Y'') := by
  have key := congrArg (fun t => t.toNatTrans.app Y'')
    (squareFiber_comp_two_cell F q q' q'' f g k h₁ h₂ f' g' k' h₁' h₂' f'' hf g'' hg k'' h₁'' h₂'')
  simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.whiskerLeft_app,
    Cat.associator_hom_app, Cat.associator_inv_app, eqToHom_refl, Category.id_comp,
    Functor.map_comp, Category.assoc] at key
  simp only [squareFiber, Functor.map_comp, Category.assoc]
  rw [key, F.mapComp'_inv_naturality_assoc, F.mapComp'_hom_naturality_assoc]

/-- `squareFiber_comp` with the composite of the left-hand sides taken on the nose, as in the
composition of the Grothendieck construction. -/
theorem squareFiber_comp_mapComp {x x' x'' y y' y'' : B} (q : x ⟶ y) (q' : x' ⟶ y')
    (q'' : x'' ⟶ y'') (f : x' ⟶ x) (g : y' ⟶ y) (k : x' ⟶ y) (h₁ : f ≫ q = k)
    (h₂ : q' ≫ g = k) (f' : x'' ⟶ x') (g' : y'' ⟶ y') (k' : x'' ⟶ y') (h₁' : f' ≫ q' = k')
    (h₂' : q'' ≫ g' = k') (g'' : y'' ⟶ y)
    (hg : g' ≫ g = g'') (k'' : x'' ⟶ y) (h₁'' : (f' ≫ f) ≫ q = k'') (h₂'' : q'' ≫ g'' = k'')
    {Y : F.obj x} {Y' : F.obj x'} {Y'' : F.obj x''} (φ : Y ⟶ (F.map f).toFunctor.obj Y')
    (φ' : Y' ⟶ (F.map f').toFunctor.obj Y'') :
    squareFiber F q q'' (f' ≫ f) g'' k'' h₁'' h₂''
        (φ ≫ (F.map f).toFunctor.map φ' ≫ (F.mapComp f' f).inv.toNatTrans.app Y'') =
      squareFiber F q q' f g k h₁ h₂ φ ≫
        (F.map g).toFunctor.map (squareFiber F q' q'' f' g' k' h₁' h₂' φ') ≫
        (F.mapComp' g' g g'' hg).inv.toNatTrans.app ((F.map q'').toFunctor.obj Y'') := by
  have h := squareFiber_comp F q q' q'' f g k h₁ h₂ f' g' k' h₁' h₂' (f' ≫ f) rfl g'' hg k''
    h₁'' h₂'' φ φ'
  rwa [F.mapComp'_eq_mapComp] at h

/-- **The inverse image along an identity square is the identity.** -/
theorem squareFiber_id {x y : B} (q : x ⟶ y) (g : y ⟶ y) (hg : g = 𝟙 y) (k : x ⟶ y)
    (h₁ : 𝟙 x ≫ q = k) (h₂ : q ≫ g = k) (Y : F.obj x) :
    squareFiber F q q (𝟙 x) g k h₁ h₂ ((F.mapId x).inv.toNatTrans.app Y) =
      (F.mapId' g hg).inv.toNatTrans.app ((F.map q).toFunctor.obj Y) := by
  obtain rfl : k = q := h₁.symm.trans (Category.id_comp q)
  subst hg
  simp only [squareFiber, F.mapComp'_id_comp_inv_app, F.mapComp'_comp_id_hom_app,
    F.mapId'_eq_mapId]
  rw [← Functor.map_comp_assoc, Cat.Hom.inv_hom_id_toNatTrans_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

end Generic

/-- The square of a morphism of the comma category, in `LocallyDiscrete 𝒮ᵒᵖ`. -/
theorem inverseImage_square {c c' : Comma G (forget F)} (m : c ⟶ c') :
    c'.hom.op.toLoc ≫ (G.map m.left).op.toLoc = (c.hom ≫ m.right.base).op.toLoc :=
  congrArg (fun k : G.obj c.left ⟶ c'.right.base => k.op.toLoc) m.w

/-- The fibre of the inverse image of a morphism of the comma category: the inverse image of the
fibre of the morphism of `∫ᶜ F`, followed by the comparisons of the inverse images along the two
factorizations of the square. -/
def inverseImageFiber {c c' : Comma G (forget F)} (m : c ⟶ c') :
    (F.map c.hom.op.toLoc).toFunctor.obj c.right.fiber ⟶
      (F.map (G.map m.left).op.toLoc).toFunctor.obj
        ((F.map c'.hom.op.toLoc).toFunctor.obj c'.right.fiber) :=
  squareFiber F c.hom.op.toLoc c'.hom.op.toLoc m.right.base.op.toLoc (G.map m.left).op.toLoc
    (c.hom ≫ m.right.base).op.toLoc rfl (inverseImage_square F G m) m.right.fiber

/-- The identity isomorphism of the composite `G.op.toPseudofunctor.comp F` at `a` is
`F.mapId'` along `(G.map (𝟙 a)).op.toLoc`. -/
theorem comp_mapId (a : 𝒟) :
    (G.op.toPseudofunctor.comp F).mapId ⟨op a⟩ =
      F.mapId' (G.map (𝟙 a)).op.toLoc (by simp) :=
  rfl

/-- The composition isomorphism of the composite `G.op.toPseudofunctor.comp F` at `u` and `v` is
`F.mapComp'` along `G.map v`, `G.map u` and `G.map (u ≫ v)`. -/
theorem comp_mapComp {a b c : 𝒟} (u : a ⟶ b) (v : b ⟶ c) :
    (G.op.toPseudofunctor.comp F).mapComp v.op.toLoc u.op.toLoc =
      F.mapComp' (G.map v).op.toLoc (G.map u).op.toLoc (G.map (u ≫ v)).op.toLoc (by simp) :=
  rfl

/-- **The inverse image functor** `Comma G (forget F) ⥤ ∫ᶜ (F ∘ G)`, sending `(A, (X, L), q)`
to `(A, q^* L)`. -/
def inverseImage : Comma G (forget F) ⥤ ∫ᶜ (G.op.toPseudofunctor.comp F) where
  obj c := ⟨c.left, (F.map c.hom.op.toLoc).toFunctor.obj c.right.fiber⟩
  map m := ⟨m.left, inverseImageFiber F G m⟩
  map_id c := by
    ext
    · rfl
    · exact (squareFiber_id F c.hom.op.toLoc (G.map (𝟙 c.left)).op.toLoc (by simp) _ _ _
        c.right.fiber).trans (Category.comp_id _).symm
  map_comp {c c' c''} m m' := by
    ext
    · rfl
    · exact (squareFiber_comp_mapComp F c.hom.op.toLoc c'.hom.op.toLoc c''.hom.op.toLoc
        m.right.base.op.toLoc (G.map m.left).op.toLoc _ rfl (inverseImage_square F G m)
        m'.right.base.op.toLoc (G.map m'.left).op.toLoc _ rfl (inverseImage_square F G m')
        (G.map (m.left ≫ m'.left)).op.toLoc (by simp) _ rfl (inverseImage_square F G (m ≫ m'))
        m.right.fiber m'.right.fiber).trans (Category.comp_id _).symm

/-- Reading an object of the Grothendieck construction of `F ∘ G` in that of `F`:
`(A, M) ↦ (G A, M)`. -/
def forgetComp : ∫ᶜ (G.op.toPseudofunctor.comp F) ⥤ ∫ᶜ F where
  obj a := ⟨G.obj a.base, a.fiber⟩
  map m := ⟨G.map m.base, m.fiber⟩
  map_id a := by
    ext
    · exact G.map_id a.base
    · change ((G.op.toPseudofunctor.comp F).mapId ⟨op a.base⟩).inv.toNatTrans.app a.fiber =
        (F.mapId ⟨op (G.obj a.base)⟩).inv.toNatTrans.app a.fiber ≫ eqToHom _
      rw [comp_mapId]
      simp only [Pseudofunctor.mapId', Iso.trans_inv, PrelaxFunctor.map₂Iso_inv, eqToIso.inv,
        PrelaxFunctor.map₂_eqToHom]
      exact (Cat.Hom₂.comp_app _ _ _).trans (congrArg _ (Cat.eqToHom_app _ _ _ _))
  map_comp {a b c} m m' := by
    ext
    · exact G.map_comp m.base m'.base
    · change m.fiber ≫ (F.map (G.map m.base).op.toLoc).toFunctor.map m'.fiber ≫
          ((G.op.toPseudofunctor.comp F).mapComp m'.base.op.toLoc
            m.base.op.toLoc).inv.toNatTrans.app c.fiber = _
      rw [comp_mapComp]
      simp only [Pseudofunctor.mapComp', Iso.trans_inv, PrelaxFunctor.map₂Iso_inv, eqToIso.inv,
        PrelaxFunctor.map₂_eqToHom]
      refine (congrArg (fun t => _ ≫ _ ≫ t)
        ((Cat.Hom₂.comp_app
          (F.mapComp (G.map m'.base).op.toLoc (G.map m.base).op.toLoc).inv _ c.fiber).trans
            (congrArg _ (Cat.eqToHom_app _ _ _ _)))).trans ?_
      exact ((Category.assoc _ _ _).trans (congrArg _ (Category.assoc _ _ _))).symm

section IsIso

variable {F}

/-- The inverse image along an invertible morphism of `𝒮` is an equivalence. -/
def mapEquivalenceOfIso {a b : 𝒮} (u : a ⟶ b) (v : b ⟶ a) (huv : u ≫ v = 𝟙 a)
    (hvu : v ≫ u = 𝟙 b) :
    (F.obj ⟨op b⟩) ≌ (F.obj ⟨op a⟩) :=
  Equivalence.mk (F.map u.op.toLoc).toFunctor (F.map v.op.toLoc).toFunctor
    (Cat.Hom.toNatIso ((F.mapId _).symm ≪≫ F.mapComp' u.op.toLoc v.op.toLoc (𝟙 _)
      (by rw [show u.op.toLoc ≫ v.op.toLoc = (v ≫ u).op.toLoc from rfl, hvu]; rfl)))
    (Cat.Hom.toNatIso ((F.mapComp' v.op.toLoc u.op.toLoc (𝟙 _)
      (by rw [show v.op.toLoc ≫ u.op.toLoc = (u ≫ v).op.toLoc from rfl, huv]; rfl)).symm ≪≫
        F.mapId _))

/-- **The fibre of an isomorphism of the Grothendieck construction is an isomorphism.** -/
theorem isIso_fiber_of_isIso {X Y : ∫ᶜ F} (f : X ⟶ Y) [IsIso f] : IsIso f.fiber := by
  have hb : f.base ≫ (inv f).base = 𝟙 _ := congrArg Hom.base (IsIso.hom_inv_id f)
  have hc : (inv f).base ≫ f.base = 𝟙 _ := congrArg Hom.base (IsIso.inv_hom_id f)
  have h₁ := Hom.congr (IsIso.hom_inv_id f)
  have h₂ := Hom.congr (IsIso.inv_hom_id f)
  simp only [categoryStruct_comp_fiber, categoryStruct_id_fiber] at h₁ h₂
  have h₁' : f.fiber ≫ ((F.map f.base.op.toLoc).toFunctor.map (inv f).fiber ≫
      ((Cat.Hom.toNatIso (F.mapComp (inv f).base.op.toLoc f.base.op.toLoc)).app X.fiber).inv) =
      ((Cat.Hom.toNatIso (F.mapId ⟨op X.base⟩)).symm.app X.fiber ≪≫ eqToIso (by
        rw [show (inv f).base.op.toLoc ≫ f.base.op.toLoc = (f.base ≫ (inv f).base).op.toLoc
          from rfl, hb]; rfl)).hom := h₁
  have hr := (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) h₁').trans (Iso.hom_inv_id _))
  have h₂' : (inv f).fiber ≫ (F.map (inv f).base.op.toLoc).toFunctor.map f.fiber ≫
      ((Cat.Hom.toNatIso (F.mapComp f.base.op.toLoc (inv f).base.op.toLoc)).app Y.fiber).inv =
      ((Cat.Hom.toNatIso (F.mapId ⟨op Y.base⟩)).symm.app Y.fiber ≪≫ eqToIso (by
        rw [show f.base.op.toLoc ≫ (inv f).base.op.toLoc = ((inv f).base ≫ f.base).op.toLoc
          from rfl, hc]; rfl)).hom := h₂
  let J := ((Cat.Hom.toNatIso (F.mapId ⟨op Y.base⟩)).symm.app Y.fiber ≪≫ eqToIso (by
        rw [show f.base.op.toLoc ≫ (inv f).base.op.toLoc = ((inv f).base ≫ f.base).op.toLoc
          from rfl, hc]; rfl)) ≪≫
    (Cat.Hom.toNatIso (F.mapComp f.base.op.toLoc (inv f).base.op.toLoc)).app Y.fiber
  have hJ : (inv f).fiber ≫ (F.map (inv f).base.op.toLoc).toFunctor.map f.fiber = J.hom := by
    rw [Iso.trans_hom, ← h₂', Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  let E := mapEquivalenceOfIso (F := F) (inv f).base f.base hc hb
  have ht : (E.fullyFaithfulFunctor.preimage (J.inv ≫ (inv f).fiber)) ≫ f.fiber = 𝟙 _ :=
    E.fullyFaithfulFunctor.map_injective (by
      rw [Functor.map_comp, Functor.FullyFaithful.map_preimage, CategoryTheory.Functor.map_id]
      exact (Category.assoc _ _ _).trans ((congrArg (J.inv ≫ ·) hJ).trans J.inv_hom_id))
  refine ⟨_, hr, ?_⟩
  have e : E.fullyFaithfulFunctor.preimage (J.inv ≫ (inv f).fiber) = _ :=
    (Category.comp_id _).symm.trans ((congrArg (_ ≫ ·) hr).symm.trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) ht).trans (Category.id_comp _))))
  rwa [← e]

/-- The inverse image along a square of an isomorphism is an isomorphism. -/
theorem isIso_squareFiber {B : Type*} [Bicategory B] [Strict B] (F : Pseudofunctor B Cat.{v₂, u₂})
    {x x' y y' : B} (q : x ⟶ y) (q' : x' ⟶ y') (f : x' ⟶ x) (g : y' ⟶ y)
    (k : x' ⟶ y) (h₁ : f ≫ q = k) (h₂ : q' ≫ g = k) {Y : F.obj x} {Y' : F.obj x'}
    (φ : Y ⟶ (F.map f).toFunctor.obj Y') (hφ : IsIso φ) :
    IsIso (squareFiber F q q' f g k h₁ h₂ φ) := by
  unfold squareFiber
  infer_instance

/-- The fibre of the inverse image of a morphism of triples whose morphism of `∫ᶜ F` is an
isomorphism is an isomorphism. -/
theorem isIso_inverseImage_map_fiber (G : 𝒟 ⥤ 𝒮) {c c' : Comma G (forget F)} (m : c ⟶ c')
    (hm : IsIso m.right) : IsIso ((inverseImage F G).map m).fiber :=
  isIso_squareFiber F _ _ _ _ _ _ _ _ (isIso_fiber_of_isIso m.right)

end IsIso

section Injective

variable {F}

/-- `forgetComp` is faithful when `G` is. -/
instance forgetComp_faithful [G.Faithful] : (forgetComp F G).Faithful where
  map_injective {a b} m₁ m₂ h := by
    obtain ⟨b₁, φ₁⟩ := m₁
    obtain ⟨b₂, φ₂⟩ := m₂
    obtain rfl : b₁ = b₂ := G.map_injective (congrArg Hom.base h)
    obtain rfl : φ₁ = φ₂ := eq_of_heq (congr_arg_heq (fun t => t.fiber) h)
    rfl

/-- **The inverse image functor reflects equality of morphisms with the same base**, as soon as
the inverse image along the structure morphism of the source is injective on morphisms. -/
theorem inverseImage_map_injective {c c' : Comma G (forget F)} (μ₁ μ₂ : c ⟶ c')
    (hl : μ₁.left = μ₂.left) (hb : μ₁.right.base = μ₂.right.base)
    (hinj : ∀ φ ψ : c.right.fiber ⟶ (F.map μ₁.right.base.op.toLoc).toFunctor.obj c'.right.fiber,
      (F.map c.hom.op.toLoc).toFunctor.map φ = (F.map c.hom.op.toLoc).toFunctor.map ψ → φ = ψ)
    (h : (inverseImage F G).map μ₁ = (inverseImage F G).map μ₂) : μ₁ = μ₂ := by
  obtain ⟨l₁, ⟨b₁, φ₁⟩, w₁⟩ := μ₁
  obtain ⟨l₂, ⟨b₂, φ₂⟩, w₂⟩ := μ₂
  dsimp only at hl hb hinj
  subst hl hb
  have hφ : squareFiber F _ _ _ _ _ _ _ φ₁ = squareFiber F _ _ _ _ _ _ _ φ₂ :=
    eq_of_heq (congr_arg_heq (fun t => t.fiber) h)
  simp only [squareFiber, cancel_mono] at hφ
  obtain rfl := hinj φ₁ φ₂ hφ
  rfl

end Injective

section Cancel

variable {F}

/-- **Right cancellation by a morphism with invertible fibre**, among morphisms with the
same base. -/
theorem hom_ext_of_comp_right {Y Y'' Y' : ∫ᶜ F} (χ χ' : Y ⟶ Y'') (m : Y'' ⟶ Y')
    (hb : χ.base = χ'.base) (hm : IsIso m.fiber) (h : χ ≫ m = χ' ≫ m) : χ = χ' := by
  obtain ⟨b, φ⟩ := χ
  obtain ⟨b', φ'⟩ := χ'
  dsimp only at hb
  subst hb
  have h' : φ ≫ (F.map b.op.toLoc).toFunctor.map m.fiber ≫
      (F.mapComp m.base.op.toLoc b.op.toLoc).inv.toNatTrans.app Y'.fiber =
      φ' ≫ (F.map b.op.toLoc).toFunctor.map m.fiber ≫
      (F.mapComp m.base.op.toLoc b.op.toLoc).inv.toNatTrans.app Y'.fiber :=
    eq_of_heq (congr_arg_heq (fun t => t.fiber) h)
  rw [cancel_mono] at h'
  subst h'
  rfl

/-- **Left cancellation by a morphism with invertible fibre** whose inverse image is injective on
morphisms, among morphisms with the same base. -/
theorem hom_ext_of_comp_left {Y₁ Y Y' : ∫ᶜ F} (k : Y₁ ⟶ Y) (α β : Y ⟶ Y')
    (hb : α.base = β.base) (hk : IsIso k.fiber)
    (hinj : ∀ φ ψ : Y.fiber ⟶ (F.map α.base.op.toLoc).toFunctor.obj Y'.fiber,
      (F.map k.base.op.toLoc).toFunctor.map φ = (F.map k.base.op.toLoc).toFunctor.map ψ → φ = ψ)
    (h : k ≫ α = k ≫ β) : α = β := by
  obtain ⟨b, φ⟩ := α
  obtain ⟨b', φ'⟩ := β
  dsimp only at hb hinj
  subst hb
  have h' : k.fiber ≫ (F.map k.base.op.toLoc).toFunctor.map φ ≫
      (F.mapComp b.op.toLoc k.base.op.toLoc).inv.toNatTrans.app Y'.fiber =
      k.fiber ≫ (F.map k.base.op.toLoc).toFunctor.map φ' ≫
      (F.mapComp b.op.toLoc k.base.op.toLoc).inv.toNatTrans.app Y'.fiber :=
    eq_of_heq (congr_arg_heq (fun t => t.fiber) h)
  rw [cancel_epi, cancel_mono] at h'
  obtain rfl := hinj φ φ' h'
  rfl

end Cancel

section IsIsoOfFiber

variable {F}

/-- A morphism of the Grothendieck construction is the vertical morphism given by its fibre
followed by the cartesian lift of its base. -/
theorem ι_map_fiber_comp_cartesianLift {Y Y' : ∫ᶜ F} (m : Y ⟶ Y') :
    (ι F Y.base).map m.fiber ≫ cartesianLift Y'.fiber m.base = m := by
  ext
  · exact Category.id_comp _
  · show (m.fiber ≫ (F.mapId (⟨op Y.base⟩ : LocallyDiscrete 𝒮ᵒᵖ)).inv.toNatTrans.app _) ≫
        (F.map (𝟙 (⟨op Y.base⟩ : LocallyDiscrete 𝒮ᵒᵖ))).toFunctor.map (𝟙 _) ≫
        (F.mapComp m.base.op.toLoc (𝟙 (⟨op Y.base⟩ : LocallyDiscrete 𝒮ᵒᵖ))).inv.toNatTrans.app
          Y'.fiber = _
    rw [F.mapComp_id_right_inv_app]
    simp [Strict.rightUnitor_eqToIso, PrelaxFunctor.map₂_eqToHom]
    rfl

/-- **A morphism of the Grothendieck construction with invertible base and fibre is an
isomorphism.** -/
theorem isIso_of_isIso_base_of_isIso_fiber {Y Y' : ∫ᶜ F} (m : Y ⟶ Y') (hb : IsIso m.base)
    (hf : IsIso m.fiber) : IsIso m := by
  have := hf
  have := hb
  have := isStronglyCartesian_homCartesianLift Y'.fiber m.base
  have h₂ : IsIso (cartesianLift Y'.fiber m.base) :=
    Functor.IsStronglyCartesian.isIso_of_base_isIso (forget F) (f := m.base)
      (cartesianLift Y'.fiber m.base)
  rw [← ι_map_fiber_comp_cartesianLift m]
  have h₁ : IsIso ((ι F Y.base).map m.fiber) := Functor.map_isIso _ _
  exact @IsIso.comp_isIso _ _ _ _ _ ((ι F Y.base).map m.fiber) (cartesianLift Y'.fiber m.base) h₁ h₂

end IsIsoOfFiber

section MapComp'

variable {B : Type*} [Bicategory B] (F : Pseudofunctor B Cat.{v₂, u₂})

/-- A component of `mapComp'` is a transport followed by the component of `mapComp`. -/
theorem mapComp'_hom_app_eq {x y z : B} (f : x ⟶ y) (g : y ⟶ z) (fg : x ⟶ z) (h : f ≫ g = fg)
    (M : F.obj x) :
    (F.mapComp' f g fg h).hom.toNatTrans.app M =
      eqToHom (by rw [← h]) ≫ (F.mapComp f g).hom.toNatTrans.app M := by
  subst h
  rw [F.mapComp'_eq_mapComp]
  simp

/-- A component of the inverse of `mapComp'` is the component of the inverse of `mapComp`
followed by a transport. -/
theorem mapComp'_inv_app_eq {x y z : B} (f : x ⟶ y) (g : y ⟶ z) (fg : x ⟶ z) (h : f ≫ g = fg)
    (M : F.obj x) :
    (F.mapComp' f g fg h).inv.toNatTrans.app M =
      (F.mapComp f g).inv.toNatTrans.app M ≫ eqToHom (by rw [← h]) := by
  subst h
  rw [F.mapComp'_eq_mapComp]
  simp

end MapComp'

end CategoryTheory.Pseudofunctor.CoGrothendieck

end
