module

public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsTotalPresheaf

/-!
# Sections of the total presheaf over the identity of `Z`

Let `Z` be a presheaf of sets on a category `C` and `F` a presheaf of sets on the category of
elements `El Z` of `Z`. A section of the structure morphism `Σ_Z F ⟶ Z` of the total presheaf
(`CategoryTheory.PresheafOfCategories.elementsTotalPresheaf`) is the same thing as a global
section of `F`: a family `t P ∈ F(P)` indexed by the objects `P` of `El Z` with
`F(m)(t Q) = t P` for every morphism `m : P ⟶ Q` of `El Z`.

## Main definitions

* `CategoryTheory.PresheafOfCategories.ElementsGlobalSection`: the compatible families.
* `CategoryTheory.PresheafOfCategories.elementsTotalSection`: the section of `Σ_Z F ⟶ Z` of a
  compatible family.
* `CategoryTheory.PresheafOfCategories.elementsSectionValue`: the value of a section of
  `Σ_Z F ⟶ Z` at an element of `Z`.
* `CategoryTheory.PresheafOfCategories.elementsTotalSectionEquiv`: the bijection between the two.
-/

@[expose] public section

open CategoryTheory Opposite

namespace CategoryTheory.PresheafOfCategories

universe v u

variable {C : Type u} [Category.{v} C] (Z : Cᵒᵖ ⥤ Type v)
  (F : ((presheafOfCategories (Z ⋙ typeToCat)).obj)ᵒᵖ ⥤ Type v)

/-- **Global sections of a presheaf on `El Z`**: families `t P ∈ F(P)` with `F(m)(t Q) = t P` for
every morphism `m : P ⟶ Q` of the category of elements of `Z`. -/
def ElementsGlobalSection : Type _ :=
  {t : ∀ P : (presheafOfCategories (Z ⋙ typeToCat)).obj, F.obj (op P) //
    ∀ {P Q : (presheafOfCategories (Z ⋙ typeToCat)).obj} (m : P ⟶ Q), F.map m.op (t Q) = t P}

/-- **The section of `Σ_Z F ⟶ Z` of a global section of `F`**: it sends `z ∈ Z(V)` to the pair
`(z, t(V, z))`. -/
def elementsTotalSection (t : ElementsGlobalSection Z F) : Z ⟶ elementsTotalPresheaf Z F where
  app V := ↾fun z => ⟨z, t.1 (elementsPoint Z (V := V.unop) z)⟩
  naturality V W g := by
    ext z
    refine Sigma.ext rfl (heq_of_eq ?_)
    exact (t.2 (elementsRestrict Z g z)).symm

/-- The section of a global section `t` sends `z ∈ Z(V)` to `(z, t(V, z))`. -/
@[simp]
lemma elementsTotalSection_app (t : ElementsGlobalSection Z F) (V : Cᵒᵖ) (z : Z.obj V) :
    (elementsTotalSection Z F t).app V z = ⟨z, t.1 (elementsPoint Z (V := V.unop) z)⟩ :=
  rfl

/-- The morphism `elementsTotalSection Z F t` is a section of `Σ_Z F ⟶ Z`. -/
lemma elementsTotalSection_comp_elementsTotalProj (t : ElementsGlobalSection Z F) :
    elementsTotalSection Z F t ≫ elementsTotalProj Z F = 𝟙 Z :=
  rfl

variable {Z F}

/-- A section of `Σ_Z F ⟶ Z` sends `z` to a pair with first component `z`. -/
lemma elementsTotal_app_fst_of_comp_eq_id {s : Z ⟶ elementsTotalPresheaf Z F}
    (hs : s ≫ elementsTotalProj Z F = 𝟙 Z) {V : Cᵒᵖ} (z : Z.obj V) : (s.app V z).1 = z :=
  types_congr_hom (NatTrans.congr_app hs V) z

/-- **The value of a section of `Σ_Z F ⟶ Z` at `z ∈ Z(V)`**: the second component of the pair it
sends `z` to, an element of `F(V, z)`. -/
def elementsSectionValue {s : Z ⟶ elementsTotalPresheaf Z F}
    (hs : s ≫ elementsTotalProj Z F = 𝟙 Z) {V : C} (z : Z.obj (op V)) :
    F.obj (op (elementsPoint Z z)) :=
  cast (congrArg (fun t => F.obj (op (elementsPoint Z t)))
    (elementsTotal_app_fst_of_comp_eq_id hs z)) (s.app (op V) z).2

/-- A section of `Σ_Z F ⟶ Z` sends `z` to the pair `(z, elementsSectionValue hs z)`. -/
lemma elementsTotal_app_eq {s : Z ⟶ elementsTotalPresheaf Z F}
    (hs : s ≫ elementsTotalProj Z F = 𝟙 Z) {V : C} (z : Z.obj (op V)) :
    s.app (op V) z = ⟨z, elementsSectionValue hs z⟩ := by
  refine Sigma.ext (elementsTotal_app_fst_of_comp_eq_id hs z) ?_
  exact (cast_heq _ _).symm

/-- The values of a section of `Σ_Z F ⟶ Z` are compatible with every morphism of `El Z`. -/
lemma elementsSectionValue_map {s : Z ⟶ elementsTotalPresheaf Z F}
    (hs : s ≫ elementsTotalProj Z F = 𝟙 Z) {P Q : (presheafOfCategories (Z ⋙ typeToCat)).obj}
    (m : P ⟶ Q) :
    F.map m.op (elementsSectionValue hs Q.fiber.as) = elementsSectionValue hs P.fiber.as := by
  have hz : P.fiber.as = Z.map m.base.op Q.fiber.as := Discrete.eq_of_hom m.fiber
  have h1 : (⟨P.fiber.as, F.map m.op (elementsSectionValue hs Q.fiber.as)⟩ :
        Σ t : Z.obj (op P.base), F.obj (op (elementsPoint Z t))) =
      ⟨Z.map m.base.op Q.fiber.as, F.map (elementsRestrict Z m.base.op Q.fiber.as).op
        (elementsSectionValue hs Q.fiber.as)⟩ :=
    totalMk_eq Z F (elementsSectionValue hs Q.fiber.as) m
      (elementsRestrict Z m.base.op Q.fiber.as) rfl
  have h2 : s.app (op P.base) (Z.map m.base.op Q.fiber.as) =
      (elementsTotalPresheaf Z F).map m.base.op (s.app (op Q.base) Q.fiber.as) :=
    types_congr_hom (s.naturality m.base.op) Q.fiber.as
  rw [elementsTotal_app_eq hs, elementsTotal_app_eq hs] at h2
  have h3 : (⟨Z.map m.base.op Q.fiber.as, elementsSectionValue hs (Z.map m.base.op Q.fiber.as)⟩ :
        Σ t : Z.obj (op P.base), F.obj (op (elementsPoint Z t))) =
      ⟨P.fiber.as, elementsSectionValue hs P.fiber.as⟩ := by
    rw [← hz]
  exact eq_of_heq (Sigma.mk.inj_iff.1 (h1.trans (h2.symm.trans h3))).2

/-- The global section of `F` of a section of `Σ_Z F ⟶ Z`. -/
def elementsGlobalSectionOf {s : Z ⟶ elementsTotalPresheaf Z F}
    (hs : s ≫ elementsTotalProj Z F = 𝟙 Z) : ElementsGlobalSection Z F :=
  ⟨fun P => elementsSectionValue hs P.fiber.as, fun m => elementsSectionValue_map hs m⟩

variable (Z F)

/-- **Sections of `Σ_Z F ⟶ Z` are global sections of `F`.** -/
def elementsTotalSectionEquiv :
    {s : Z ⟶ elementsTotalPresheaf Z F // s ≫ elementsTotalProj Z F = 𝟙 Z} ≃
      ElementsGlobalSection Z F where
  toFun s := elementsGlobalSectionOf s.2
  invFun t := ⟨elementsTotalSection Z F t, elementsTotalSection_comp_elementsTotalProj Z F t⟩
  left_inv s := by
    refine Subtype.ext (NatTrans.ext (funext fun V => ?_))
    ext z
    exact (elementsTotal_app_eq s.2 (V := V.unop) z).symm
  right_inv t := by
    refine Subtype.ext (funext fun P => ?_)
    have h := elementsTotal_app_eq (elementsTotalSection_comp_elementsTotalProj Z F t)
      (V := P.base) P.fiber.as
    exact (eq_of_heq (Sigma.mk.inj_iff.1 h).2).symm

/-- The global section associated with a section `s` of `Σ_Z F ⟶ Z` takes the value
`elementsSectionValue s.2 z` at the element `(V, z)` of `El Z`. -/
@[simp]
lemma elementsTotalSectionEquiv_apply_coe
    (s : {s : Z ⟶ elementsTotalPresheaf Z F // s ≫ elementsTotalProj Z F = 𝟙 Z})
    (P : (presheafOfCategories (Z ⋙ typeToCat)).obj) :
    (elementsTotalSectionEquiv Z F s).1 P = elementsSectionValue s.2 P.fiber.as :=
  rfl

/-- The section of `Σ_Z F ⟶ Z` associated with a global section `t` is
`elementsTotalSection Z F t`. -/
@[simp]
lemma elementsTotalSectionEquiv_symm_apply_coe (t : ElementsGlobalSection Z F) :
    ((elementsTotalSectionEquiv Z F).symm t).1 = elementsTotalSection Z F t :=
  rfl

end CategoryTheory.PresheafOfCategories

end
