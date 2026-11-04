module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import StacksCore.CategoryTheory.FiberedInGroupoids
public import StacksFrontier.CategoryTheory.TwoFibreProductOver
public import StacksFrontier.CategoryTheory.FiberedCategory.SliceAsElements
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceProduct

/-!
# Terminal arrows into a scheme-valued point of a category fibred in groupoids

Let `p𝒳 : 𝒳 ⥤ 𝒞/X` and `p𝒴 : 𝒴 ⥤ 𝒞/X` be categories over a slice, `p𝒴` fibred in groupoids, let
`F : 𝒳 ⥤ 𝒴` be a 1-morphism over `𝒞/X` and let `y : 𝒞/A ⥤ 𝒴` be a "point" of `𝒴` over
`g : A ⟶ X`, i.e. `y ⋙ p𝒴 = Over.map g`. This file compares the 2-fibre product
`(𝒞/A) ×_{y, 𝒴, F} 𝒳` with the comma category `CostructuredArrow F (y(A/A))` of arrows
`F x ⟶ y(A/A)`: a terminal object of the former gives a terminal object of the latter
(`isTerminalToCostructuredArrow`). When the 2-fibre product is represented by `W ∈ 𝒞/A`, the
object corresponding to `id_W` is terminal and lies over `W` (`isTerminalRepresentingObject`,
`p𝒳_obj_representingObject_y`), so that the arrow `F x₀ ⟶ y(A/A)` of that object is terminal
(`isTerminalRepresentingArrow`).

This is the step "`𝒳` is represented by `U`" of the computation of the direct image along a
1-morphism representable by schemes: the direct image at `y(A/A)` is the right Kan extension,
a limit over the opposite of this comma category, hence the value at the terminal arrow.

## Main results

* `CategoryTheory.TwoFibreProductOver.TerminalArrow.isTerminalToCostructuredArrow`.
* `CategoryTheory.TwoFibreProductOver.TerminalArrow.isTerminalRepresentingArrow`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.TwoFibreProductOver.TerminalArrow

universe v₀ u₀ v₁ u₁ v₂ u₂

variable {𝒞 : Type u₀} [Category.{v₀} 𝒞] {X A : 𝒞} (g : A ⟶ X)
  {𝒳 : Type u₁} [Category.{v₁} 𝒳] {𝒴 : Type u₂} [Category.{v₂} 𝒴]
  (p𝒳 : 𝒳 ⥤ Over X) (p𝒴 : 𝒴 ⥤ Over X) (F : 𝒳 ⥤ 𝒴) (y : Over A ⥤ 𝒴)

/-- The tautological arrow from an object of `𝒞/A` to the terminal object `A/A`. -/
abbrev toTop (a : Over A) : a ⟶ Over.mk (𝟙 A) := Over.homMk a.hom (Category.comp_id _)

/-- Every arrow to `A/A` is the tautological one. -/
lemma toTop_eq {a : Over A} (u : a ⟶ Over.mk (𝟙 A)) : u = toTop a :=
  Over.OverMorphism.ext ((Over.w u).symm.trans (Category.comp_id _)).symm

/-- Composing with the tautological arrow to `A/A` gives the tautological arrow. -/
lemma map_comp_toTop {D : Type*} [Category D] (y : Over A ⥤ D) {a b : Over A} (u : a ⟶ b) :
    y.map u ≫ y.map (toTop b) = y.map (toTop a) := by
  rw [← Functor.map_comp, toTop_eq (_ ≫ _)]

/-- An object of the 2-fibre product `(𝒞/A) ×_𝒴 𝒳` read as an arrow `F x ⟶ y(A/A)`: the inverse
of its comparison isomorphism followed by `y` of the tautological arrow to `A/A`. -/
def toCostructuredArrow (z : TwoFibreProductOver (Over.map g) p𝒳 p𝒴 y F) :
    CostructuredArrow F (y.obj (Over.mk (𝟙 A))) :=
  CostructuredArrow.mk (Y := z.y) (z.iso.inv ≫ y.map (toTop z.x))

/-- Cancelling `eqToHom`s around an equation of composites. -/
lemma eqToHom_conj_cancel {C : Type*} [Category C] {P Q Q' R R' S S₁ : C}
    (K : Q ⟶ R) (T : R' ⟶ S) (T' : Q' ⟶ S) (α : P = Q) (β : R = R') (γ : S = S₁)
    (α' : P = Q') (δ : Q' = Q) (ε : R = R')
    (h : eqToHom α ≫ K ≫ eqToHom β ≫ T ≫ eqToHom γ = eqToHom α' ≫ T' ≫ eqToHom γ) :
    eqToHom δ ≫ K ≫ eqToHom ε ≫ T = T' := by
  subst α' α β γ
  simpa using h

/-- An `eqToHom` from an object to itself may be dropped in front of a composite. -/
lemma eqToHom_self_comp {C : Type*} [Category C] {P Q : C} (h : P = P) (k : P ⟶ Q) :
    eqToHom h ≫ k = k := by
  simp

/-- A functor identity `F ⋙ G = H` gives `G.map (F.map u)` as `H.map u` conjugated by `eqToHom`s. -/
private lemma map_map_eq_eqToHom_comp {C D E : Type*} [Category C] [Category D] [Category E]
    {F₁ : C ⥤ D} {G₁ : D ⥤ E} {H₁ : C ⥤ E} (h : F₁ ⋙ G₁ = H₁) {a b : C} (u : a ⟶ b) :
    G₁.map (F₁.map u) =
      eqToHom (Functor.congr_obj h a) ≫ H₁.map u ≫ eqToHom (Functor.congr_obj h b).symm :=
  Functor.congr_hom h u

section Lift

variable {g p𝒳 p𝒴 F y} (hF : F ⋙ p𝒴 = p𝒳) (hy : y ⋙ p𝒴 = Over.map g)

/-- The base morphism of an arrow `F x ⟶ y(A/A)`, read as a morphism of `𝒞/X`. -/
def baseArrow (c : CostructuredArrow F (y.obj (Over.mk (𝟙 A)))) :
    p𝒳.obj c.left ⟶ (Over.map g).obj (Over.mk (𝟙 A)) :=
  eqToHom (Functor.congr_obj hF c.left).symm ≫ p𝒴.map c.hom ≫
    eqToHom (Functor.congr_obj hy _)

/-- The object of `𝒞/A` that an arrow `F x ⟶ y(A/A)` lies over. -/
abbrev objOver (c : CostructuredArrow F (y.obj (Over.mk (𝟙 A)))) : Over A :=
  Over.mk (baseArrow hF hy c).left

/-- The object of `𝒞/A` lies over the base of the arrow. -/
lemma map_objOver (c : CostructuredArrow F (y.obj (Over.mk (𝟙 A)))) :
    (Over.map g).obj (objOver hF hy c) = p𝒳.obj c.left :=
  PresheafOfCategories.over_mk_eq (p𝒳.obj c.left) (h := (baseArrow hF hy c).left ≫ g) (by
    simpa using Over.w (baseArrow hF hy c))

/-- The two objects of `𝒴` to be compared lie over one object of `𝒞/X`. -/
lemma p𝒴_obj_eq (c : CostructuredArrow F (y.obj (Over.mk (𝟙 A)))) :
    p𝒴.obj (F.obj c.left) = p𝒴.obj (y.obj (objOver hF hy c)) :=
  (Functor.congr_obj hF c.left).trans ((map_objOver hF hy c).symm.trans
    (Functor.congr_obj hy _).symm)

/-- The base condition for the vertical comparison. -/
lemma lift_cond (c : CostructuredArrow F (y.obj (Over.mk (𝟙 A)))) :
    eqToHom (p𝒴_obj_eq hF hy c) ≫ p𝒴.map (y.map (toTop (objOver hF hy c))) = p𝒴.map c.hom := by
  have h2 : p𝒴.map c.hom = eqToHom (Functor.congr_obj hF c.left) ≫ baseArrow hF hy c ≫
      eqToHom (Functor.congr_obj hy _).symm := by
    simp [baseArrow]
  rw [map_map_eq_eqToHom_comp hy, h2]
  ext
  simp [baseArrow]

variable (hp𝒴 : p𝒴.IsFiberedInGroupoids)
include hp𝒴

/-- Two morphisms over one base morphism with a common composite to a third object agree: every
morphism of a category fibred in groupoids is cartesian. -/
lemma eq_of_comp_eq {w z z' : 𝒴} (u v : w ⟶ z) (k : z ⟶ z') (hpv : p𝒴.map u = p𝒴.map v)
    (h : u ≫ k = v ≫ k) : u = v :=
  (hp𝒴.unique_lift k (u ≫ k) (p𝒴.map u) (by rw [Functor.map_comp])).unique ⟨rfl, rfl⟩
    ⟨hpv.symm, h.symm⟩

/-- The vertical comparison `y(x) ⟶ F(c)` of an arrow `c : F x ⟶ y(A/A)` with the tautological
arrow of the object of `𝒞/A` it lies over. -/
def liftHom (c : CostructuredArrow F (y.obj (Over.mk (𝟙 A)))) :
    y.obj (objOver hF hy c) ⟶ F.obj c.left :=
  (hp𝒴.unique_lift c.hom (y.map (toTop (objOver hF hy c))) (eqToHom (p𝒴_obj_eq hF hy c).symm)
    (by rw [← lift_cond hF hy c, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp])).exists.choose

/-- The defining property of `liftHom`. -/
lemma liftHom_spec (c : CostructuredArrow F (y.obj (Over.mk (𝟙 A)))) :
    p𝒴.map (liftHom hF hy hp𝒴 c) = eqToHom (p𝒴_obj_eq hF hy c).symm ∧
      liftHom hF hy hp𝒴 c ≫ c.hom = y.map (toTop (objOver hF hy c)) :=
  (hp𝒴.unique_lift c.hom (y.map (toTop (objOver hF hy c))) (eqToHom (p𝒴_obj_eq hF hy c).symm)
    (by rw [← lift_cond hF hy c, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp])).exists.choose_spec

/-- The inverse of `liftHom`. -/
def liftInv (c : CostructuredArrow F (y.obj (Over.mk (𝟙 A)))) :
    F.obj c.left ⟶ y.obj (objOver hF hy c) :=
  (hp𝒴.unique_lift (y.map (toTop (objOver hF hy c))) c.hom (eqToHom (p𝒴_obj_eq hF hy c))
    (lift_cond hF hy c)).exists.choose

/-- The defining property of `liftInv`. -/
lemma liftInv_spec (c : CostructuredArrow F (y.obj (Over.mk (𝟙 A)))) :
    p𝒴.map (liftInv hF hy hp𝒴 c) = eqToHom (p𝒴_obj_eq hF hy c) ∧
      liftInv hF hy hp𝒴 c ≫ y.map (toTop (objOver hF hy c)) = c.hom :=
  (hp𝒴.unique_lift (y.map (toTop (objOver hF hy c))) c.hom (eqToHom (p𝒴_obj_eq hF hy c))
    (lift_cond hF hy c)).exists.choose_spec

/-- The vertical comparison isomorphism `y(x) ≅ F(c)`. -/
def liftIso (c : CostructuredArrow F (y.obj (Over.mk (𝟙 A)))) :
    y.obj (objOver hF hy c) ≅ F.obj c.left where
  hom := liftHom hF hy hp𝒴 c
  inv := liftInv hF hy hp𝒴 c
  hom_inv_id := eq_of_comp_eq hp𝒴 _ _ (y.map (toTop (objOver hF hy c)))
    (by rw [Functor.map_comp, (liftHom_spec hF hy hp𝒴 c).1, (liftInv_spec hF hy hp𝒴 c).1,
      eqToHom_trans, eqToHom_refl, Functor.map_id])
    (by rw [Category.assoc, (liftInv_spec hF hy hp𝒴 c).2, (liftHom_spec hF hy hp𝒴 c).2,
      Category.id_comp])
  inv_hom_id := eq_of_comp_eq hp𝒴 _ _ c.hom
    (by rw [Functor.map_comp, (liftHom_spec hF hy hp𝒴 c).1, (liftInv_spec hF hy hp𝒴 c).1,
      eqToHom_trans, eqToHom_refl, Functor.map_id])
    (by rw [Category.assoc, (liftHom_spec hF hy hp𝒴 c).2, (liftInv_spec hF hy hp𝒴 c).2,
      Category.id_comp])

/-- The object of the 2-fibre product `(𝒞/A) ×_𝒴 𝒳` lying over an arrow `F x ⟶ y(A/A)`. -/
def ofCostructuredArrow (c : CostructuredArrow F (y.obj (Over.mk (𝟙 A)))) :
    TwoFibreProductOver (Over.map g) p𝒳 p𝒴 y F where
  base := p𝒳.obj c.left
  x := objOver hF hy c
  y := c.left
  hx := map_objOver hF hy c
  hy := rfl
  iso := liftIso hF hy hp𝒴 c
  vertical := IsHomLift.of_fac' p𝒴 _ _
    ((Functor.congr_obj hy _).trans (map_objOver hF hy c))
    (Functor.congr_obj hF c.left)
    (by
      change p𝒴.map (liftHom hF hy hp𝒴 c) = _
      rw [(liftHom_spec hF hy hp𝒴 c).1]
      simp)

/-- The arrow of the object attached to an arrow is that arrow. -/
lemma toCostructuredArrow_ofCostructuredArrow_hom
    (c : CostructuredArrow F (y.obj (Over.mk (𝟙 A)))) :
    (toCostructuredArrow g p𝒳 p𝒴 F y (ofCostructuredArrow hF hy hp𝒴 c)).hom = c.hom :=
  (liftInv_spec hF hy hp𝒴 c).2

omit hp𝒴 in
/-- The comparison isomorphism of an object of the 2-fibre product is vertical: its inverse maps
to an `eqToHom` of the base. -/
lemma map_iso_inv (z : TwoFibreProductOver (Over.map g) p𝒳 p𝒴 y F) :
    p𝒴.map z.iso.inv = eqToHom ((Functor.congr_obj hF z.y).trans (z.hy.trans
      (z.hx.symm.trans (Functor.congr_obj hy z.x).symm))) := by
  have := z.vertical
  have hv : p𝒴.IsHomLift (𝟙 z.base) z.iso.inv := IsHomLift.lift_id_inv p𝒴 z.base z.iso
  rw [IsHomLift.fac' p𝒴 (𝟙 z.base) z.iso.inv]
  simp

omit hp𝒴 in
/-- The comparison isomorphism of an object of the 2-fibre product is vertical. -/
lemma map_iso_hom (z : TwoFibreProductOver (Over.map g) p𝒳 p𝒴 y F) :
    p𝒴.map z.iso.hom = eqToHom ((Functor.congr_obj hy z.x).trans (z.hx.trans
      (z.hy.symm.trans (Functor.congr_obj hF z.y).symm))) := by
  have := z.vertical
  rw [IsHomLift.fac' p𝒴 (𝟙 z.base) z.iso.hom]
  simp

omit hp𝒴 in
/-- The base condition for lifting a morphism of arrows to the 2-fibre product. -/
lemma base_cond (c : CostructuredArrow F (y.obj (Over.mk (𝟙 A))))
    (z : TwoFibreProductOver (Over.map g) p𝒳 p𝒴 y F) (dl : c.left ⟶ z.y)
    (key : F.map dl ≫ z.iso.inv ≫ y.map (toTop z.x) = c.hom) :
    (eqToHom (map_objOver hF hy c) ≫ p𝒳.map dl ≫ eqToHom (z.hy.trans z.hx.symm)) ≫
        (Over.map g).map (toTop z.x) = (Over.map g).map (toTop (objOver hF hy c)) := by
  have hw : p𝒴.map (F.map dl) ≫ p𝒴.map z.iso.inv ≫ p𝒴.map (y.map (toTop z.x)) =
      p𝒴.map c.hom := by
    rw [← Functor.map_comp, ← Functor.map_comp, key]
  rw [map_map_eq_eqToHom_comp hF, map_iso_inv hF hy, map_map_eq_eqToHom_comp hy,
    ← lift_cond hF hy c, map_map_eq_eqToHom_comp hy] at hw
  simp only [Category.assoc, eqToHom_trans_assoc] at hw
  rw [Category.assoc, Category.assoc]
  exact eqToHom_conj_cancel _ _ _ _ _ _ _ _ _ hw

omit hp𝒴 in
/-- The base morphism of a morphism of arrows, as a morphism of `𝒞/X`. -/
abbrev baseOfLeft (c : CostructuredArrow F (y.obj (Over.mk (𝟙 A))))
    (z : TwoFibreProductOver (Over.map g) p𝒳 p𝒴 y F) (dl : c.left ⟶ z.y) :
    (Over.map g).obj (objOver hF hy c) ⟶ (Over.map g).obj z.x :=
  eqToHom (map_objOver hF hy c) ≫ p𝒳.map dl ≫ eqToHom (z.hy.trans z.hx.symm)

omit hp𝒴 in
/-- The morphism of `𝒞/A` underlying a morphism of arrows. -/
def overOfLeft (c : CostructuredArrow F (y.obj (Over.mk (𝟙 A))))
    (z : TwoFibreProductOver (Over.map g) p𝒳 p𝒴 y F) (dl : c.left ⟶ z.y)
    (key : F.map dl ≫ z.iso.inv ≫ y.map (toTop z.x) = c.hom) :
    objOver hF hy c ⟶ z.x :=
  Over.homMk (baseOfLeft hF hy c z dl).left (by
    simpa using congrArg CommaMorphism.left (base_cond hF hy c z dl key))

omit hp𝒴 in
/-- `overOfLeft` lies over the base morphism. -/
lemma map_overOfLeft (c : CostructuredArrow F (y.obj (Over.mk (𝟙 A))))
    (z : TwoFibreProductOver (Over.map g) p𝒳 p𝒴 y F) (dl : c.left ⟶ z.y)
    (key : F.map dl ≫ z.iso.inv ≫ y.map (toTop z.x) = c.hom) :
    (Over.map g).map (overOfLeft hF hy c z dl key) = baseOfLeft hF hy c z dl :=
  Over.OverMorphism.ext rfl

/-- The morphism of the 2-fibre product lying over a morphism of arrows. -/
def homOfLeft (c : CostructuredArrow F (y.obj (Over.mk (𝟙 A))))
    (z : TwoFibreProductOver (Over.map g) p𝒳 p𝒴 y F) (dl : c.left ⟶ z.y)
    (key : F.map dl ≫ z.iso.inv ≫ y.map (toTop z.x) = c.hom) :
    ofCostructuredArrow hF hy hp𝒴 c ⟶ z :=
  Hom.mk' (overOfLeft hF hy c z dl key) dl
    (by
      change _ ≫ p𝒳.map dl ≫ _ = eqToHom (map_objOver hF hy c).symm ≫
        (Over.map g).map (overOfLeft hF hy c z dl key) ≫ eqToHom z.hx
      rw [map_overOfLeft]
      refine (eqToHom_self_comp _ _).trans ?_
      simp)
    (by
      refine eq_of_comp_eq hp𝒴 _ _ (z.iso.inv ≫ y.map (toTop z.x)) ?_ ?_
      · have h1 : p𝒴.map (y.map (overOfLeft hF hy c z dl key)) = _ :=
          Functor.congr_hom hy (overOfLeft hF hy c z dl key)
        have h3 : p𝒴.map (F.map dl) = eqToHom (Functor.congr_obj hF c.left) ≫ p𝒳.map dl ≫
            eqToHom (Functor.congr_obj hF z.y).symm := Functor.congr_hom hF dl
        change p𝒴.map (y.map (overOfLeft hF hy c z dl key) ≫ z.iso.hom) =
          p𝒴.map (liftHom hF hy hp𝒴 c ≫ F.map dl)
        rw [Functor.map_comp, Functor.map_comp, h1, map_overOfLeft, map_iso_hom hF hy,
          (liftHom_spec hF hy hp𝒴 c).1, h3]
        simp
      · have e2 : liftHom hF hy hp𝒴 c ≫ F.map dl ≫ z.iso.inv ≫ y.map (toTop z.x) =
            y.map (toTop (objOver hF hy c)) := by
          rw [key, (liftHom_spec hF hy hp𝒴 c).2]
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
        exact (map_comp_toTop y _).trans e2.symm)

/-- **A terminal object of the 2-fibre product `(𝒞/A) ×_𝒴 𝒳` gives a terminal arrow into
`y(A/A)`.** If `t` is terminal in `(𝒞/A) ×_{y, 𝒴, F} 𝒳`, then its arrow
`F t ⟶ y(A/A)` is terminal in `CostructuredArrow F (y(A/A))`. -/
def isTerminalToCostructuredArrow {t : TwoFibreProductOver (Over.map g) p𝒳 p𝒴 y F}
    (ht : IsTerminal t) : IsTerminal (toCostructuredArrow g p𝒳 p𝒴 F y t) :=
  IsTerminal.ofUniqueHom
    (fun c => CostructuredArrow.homMk (ht.from (ofCostructuredArrow hF hy hp𝒴 c)).b (by
      let h := ht.from (ofCostructuredArrow hF hy hp𝒴 c)
      let ha : objOver hF hy c ⟶ t.x := h.a
      let hb : c.left ⟶ t.y := h.b
      have hw : y.map ha ≫ t.iso.hom = (liftIso hF hy hp𝒴 c).hom ≫ F.map hb := h.w
      have e : F.map hb ≫ t.iso.inv = (liftIso hF hy hp𝒴 c).inv ≫ y.map ha := by
        rw [← cancel_epi (liftIso hF hy hp𝒴 c).hom, ← reassoc_of% hw]
        simp
      change F.map hb ≫ t.iso.inv ≫ y.map (toTop t.x) = c.hom
      rw [reassoc_of% e, map_comp_toTop]
      exact (liftInv_spec hF hy hp𝒴 c).2))
    (fun c m => CostructuredArrow.hom_ext _ _ (congrArg Hom.b
      (ht.hom_ext (homOfLeft hF hy hp𝒴 c t m.left (CostructuredArrow.w m))
        (ht.from (ofCostructuredArrow hF hy hp𝒴 c)))))

end Lift

section Representable

variable {W : Over A}
  (e : StacksRepresentableCFG.EquivalenceOver (TwoFibreProductOver.fst (Over.map g) p𝒳 p𝒴 y F)
    (presheafOfCategories (yoneda.obj W ⋙ typeToCat)).p)

/-- The object of the 2-fibre product `(𝒞/A) ×_𝒴 𝒳` corresponding, under an identification with
the category represented by `W`, to the identity of `W`. -/
abbrev representingObject : TwoFibreProductOver (Over.map g) p𝒳 p𝒴 y F :=
  e.inv.functor.obj ((PresheafOfCategories.sliceToElements W).obj (Over.mk (𝟙 W)))

/-- **When `(𝒞/A) ×_𝒴 𝒳` is represented by `W`, the object corresponding to `id_W` is
terminal.** -/
def isTerminalRepresentingObject : IsTerminal (representingObject g p𝒳 p𝒴 F y e) :=
  let e₁ := (PresheafOfCategories.sliceElementsEquivalenceOver W).toEquivalence
  let e₂ := e.toEquivalence.symm
  (Over.mkIdTerminal (X := W)).isTerminalObj (e₁.functor ⋙ e₂.functor)

/-- The terminal object lies over `W`. -/
lemma representingObject_x : (representingObject g p𝒳 p𝒴 F y e).x = W :=
  Functor.congr_obj e.inv.w ((PresheafOfCategories.sliceToElements W).obj (Over.mk (𝟙 W)))

/-- The object of `𝒳` underlying the terminal object lies over `W`, read in `𝒞/X`. -/
lemma p𝒳_obj_representingObject_y :
    p𝒳.obj (representingObject g p𝒳 p𝒴 F y e).y = (Over.map g).obj W :=
  (representingObject g p𝒳 p𝒴 F y e).hy.trans ((representingObject g p𝒳 p𝒴 F y e).hx.symm.trans
    (congrArg (Over.map g).obj (representingObject_x g p𝒳 p𝒴 F y e)))

/-- **The terminal arrow into a scheme-valued point over which the base change is represented.**
For `y : 𝒞/A ⥤ 𝒴` over `𝒞/X` and `F : 𝒳 ⥤ 𝒴` such that `(𝒞/A) ×_{y, 𝒴, F} 𝒳` is
represented by `W ∈ 𝒞/A`, the arrow `F x₀ ⟶ y(A/A)` of the object `x₀` corresponding to `id_W`
is terminal in `CostructuredArrow F (y(A/A))`; `x₀` lies over `W`
(`p𝒳_obj_representingObject_y`). -/
def isTerminalRepresentingArrow (hF : F ⋙ p𝒴 = p𝒳) (hy : y ⋙ p𝒴 = Over.map g)
    (hp𝒴 : p𝒴.IsFiberedInGroupoids) :
    IsTerminal (toCostructuredArrow g p𝒳 p𝒴 F y (representingObject g p𝒳 p𝒴 F y e)) :=
  isTerminalToCostructuredArrow hF hy hp𝒴 (isTerminalRepresentingObject g p𝒳 p𝒴 F y e)

end Representable

end CategoryTheory.TwoFibreProductOver.TerminalArrow
