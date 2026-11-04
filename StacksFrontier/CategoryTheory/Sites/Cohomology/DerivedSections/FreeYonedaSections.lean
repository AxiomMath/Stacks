module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Degree-zero sheaf cohomology is the presheaf of sections

Mathlib defines the sheaf cohomology presheaf `CategoryTheory.Sheaf.cohomologyPresheaf F n` of an
abelian sheaf `F` on a site `(C, J)` as the `Ext`-group in degree `n` out of the free abelian
sheaf on the representable presheaf `yoneda.obj U`. This file identifies it in degree zero with
the presheaf of sections of `F`, which Mathlib leaves as a `TODO`.

The identification is the composite of three bijections: the sheafification adjunction, the
adjunction between the free abelian group functor and the forgetful functor whiskered into
presheaves, and the Yoneda lemma. It is natural in both the object and the sheaf.

## Main definitions

* `Stacks.Cohomology.FreeYoneda.freeYoneda` is the free abelian sheaf on a representable
  presheaf of sets, the object out of which `Sheaf.cohomologyPresheaf` takes `Ext`-groups.
* `Stacks.Cohomology.FreeYoneda.sectionsAddEquiv` identifies morphisms out of it with sections.
* `Stacks.Cohomology.FreeYoneda.gen` is the canonical section of `freeYoneda J U` over `U`,
  the image of the identity under that identification.
* `Stacks.Cohomology.FreeYoneda.extSectionsAddEquiv` is the degree-zero `Ext`-group version.

## Main results

* `Stacks.Cohomology.FreeYoneda.cohomologyPresheafIsoSections`: the degree-zero sheaf cohomology
  presheaf is the presheaf of sections.
* `Stacks.Cohomology.FreeYoneda.sectionsEquiv_eq_app_gen` evaluates the identification: a
  morphism out of the free abelian sheaf on `U` corresponds to the value of its component at `U`
  on the canonical section.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Abelian

namespace Stacks.Cohomology.FreeYoneda

universe v u

noncomputable section

variable {C : Type u} [Category.{v} C]

section

variable (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{v}]

/-- The free abelian sheaf on a representable presheaf of sets. -/
abbrev freeYoneda : C ⥤ Sheaf J AddCommGrpCat.{v} :=
  yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙ presheafToSheaf J _

end

variable {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{v}]

/-- Morphisms out of the free abelian sheaf on `U` are the sections over `U`. -/
def sectionsEquiv (U : C) (F : Sheaf J AddCommGrpCat.{v}) :
    ((freeYoneda J).obj U ⟶ F) ≃ ToType (F.obj.obj (op U)) :=
  ((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv _ _).trans
    (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _).trans yonedaEquiv)

/-- `sectionsEquiv` as an isomorphism of abelian groups. -/
def sectionsAddEquiv (U : C) (F : Sheaf J AddCommGrpCat.{v}) :
    ((freeYoneda J).obj U ⟶ F) ≃+ ToType (F.obj.obj (op U)) where
  toEquiv := sectionsEquiv U F
  map_add' f g := by
    let q : ((((Functor.whiskeringRight Cᵒᵖ (Type v) AddCommGrpCat.{v}).obj
          AddCommGrpCat.free).obj (yoneda.obj U)) ⟶
        (sheafToPresheaf J AddCommGrpCat.{v}).obj F) → ToType (F.obj.obj (op U)) := fun k ↦
      yonedaEquiv ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _ k)
    calc sectionsEquiv U F (f + g)
        = q ((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv _ _ (f + g)) := rfl
      _ = q (((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv _ _ f) +
          ((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv _ _ g)) :=
          congrArg q ((sheafificationAdjunction J AddCommGrpCat.{v}).homAddEquiv_add _ _ f g)
      _ = _ := rfl

/-- `sectionsAddEquiv` applies as `sectionsEquiv`. -/
theorem sectionsAddEquiv_apply (U : C) (F : Sheaf J AddCommGrpCat.{v})
    (α : (freeYoneda J).obj U ⟶ F) : sectionsAddEquiv U F α = sectionsEquiv U F α :=
  rfl

/-- The canonical section of the free abelian sheaf on `U` over `U` itself. -/
def gen (U : C) : ToType (((freeYoneda J).obj U).obj.obj (op U)) :=
  sectionsEquiv U ((freeYoneda J).obj U) (𝟙 _)

/-- `sectionsEquiv` is natural in the sheaf: postcomposing with `β : F ⟶ G` corresponds to
applying the component of `β` at `U`. -/
theorem sectionsEquiv_naturality (U : C) {F G : Sheaf J AddCommGrpCat.{v}}
    (α : (freeYoneda J).obj U ⟶ F) (β : F ⟶ G) :
    sectionsEquiv U G (α ≫ β) = β.hom.app (op U) (sectionsEquiv U F α) := by
  dsimp only [sectionsEquiv, Equiv.trans_apply]
  rw [(sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv_naturality_right]
  rfl

/-- The section corresponding to a morphism out of the free abelian sheaf on `U` is the value of
its component at `U` on the canonical section `gen U`. -/
theorem sectionsEquiv_eq_app_gen (U : C) (F : Sheaf J AddCommGrpCat.{v})
    (α : (freeYoneda J).obj U ⟶ F) :
    sectionsEquiv U F α = α.hom.app (op U) (gen U) :=
  (congrArg (sectionsEquiv U F) (Category.id_comp α).symm).trans
    (sectionsEquiv_naturality U (𝟙 _) α)

/-- `sectionsEquiv` is natural in the object: precomposing with the map of free abelian sheaves
induced by `h : V ⟶ U` corresponds to restricting the section along `h`. -/
theorem sectionsEquiv_naturality_left {U V : C} (h : V ⟶ U) (F : Sheaf J AddCommGrpCat.{v})
    (α : (freeYoneda J).obj U ⟶ F) :
    sectionsEquiv V F ((freeYoneda J).map h ≫ α) = F.obj.map h.op (sectionsEquiv U F α) := by
  dsimp only [sectionsEquiv, Equiv.trans_apply]
  rw [show (freeYoneda J).map h = (presheafToSheaf J AddCommGrpCat.{v}).map
      (((Functor.whiskeringRight Cᵒᵖ (Type v) AddCommGrpCat.{v}).obj
        AddCommGrpCat.free).map (yoneda.map h)) from rfl,
    (sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv_naturality_left,
    (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv_naturality_left]
  exact (yonedaEquiv_naturality _ h).symm

section Ext

variable [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]

/-- Under `Ext.addEquiv₀`, composing a degree-zero `Ext` class with `Ext.mk₀ β` is postcomposition
with `β`. -/
theorem addEquiv₀_comp_mk₀ {A : Sheaf J AddCommGrpCat.{v}} {F G : Sheaf J AddCommGrpCat.{v}}
    (x : Ext.{v} A F 0) (β : F ⟶ G) :
    Ext.addEquiv₀ (x.comp (Ext.mk₀ β) (add_zero 0)) = Ext.addEquiv₀ x ≫ β := by
  exact (Ext.mk₀_bijective A G).injective (by simp [← Ext.mk₀_comp_mk₀])

/-- Under `Ext.addEquiv₀`, composing `Ext.mk₀ α` with a degree-zero `Ext` class is precomposition
with `α`. -/
theorem addEquiv₀_mk₀_comp {A B : Sheaf J AddCommGrpCat.{v}} {F : Sheaf J AddCommGrpCat.{v}}
    (α : A ⟶ B) (x : Ext.{v} B F 0) :
    Ext.addEquiv₀ ((Ext.mk₀ α).comp x (zero_add 0)) = α ≫ Ext.addEquiv₀ x := by
  exact (Ext.mk₀_bijective A F).injective (by simp [← Ext.mk₀_comp_mk₀])

/-- Degree-zero `Ext` out of the free abelian sheaf on `U` is the group of sections over `U`. -/
def extSectionsAddEquiv (U : C) (F : Sheaf J AddCommGrpCat.{v}) :
    Ext.{v} ((freeYoneda J).obj U) F 0 ≃+ ToType (F.obj.obj (op U)) :=
  Ext.addEquiv₀.trans (sectionsAddEquiv U F)

/-- `extSectionsAddEquiv` is natural in the sheaf. -/
theorem extSectionsAddEquiv_naturality (U : C) {F G : Sheaf J AddCommGrpCat.{v}}
    (x : Ext.{v} ((freeYoneda J).obj U) F 0) (β : F ⟶ G) :
    extSectionsAddEquiv U G (x.comp (Ext.mk₀ β) (add_zero 0)) =
      β.hom.app (op U) (extSectionsAddEquiv U F x) :=
  (congrArg (sectionsEquiv U G) (addEquiv₀_comp_mk₀ x β)).trans (sectionsEquiv_naturality U _ β)

/-- `extSectionsAddEquiv` is natural in the object: composing with `Ext.mk₀` of the map of free
abelian sheaves induced by `h : V ⟶ U` corresponds to restricting the section along `h`. -/
theorem extSectionsAddEquiv_naturality_left {U V : C} (h : V ⟶ U)
    (F : Sheaf J AddCommGrpCat.{v}) (x : Ext.{v} ((freeYoneda J).obj U) F 0) :
    extSectionsAddEquiv V F ((Ext.mk₀ ((freeYoneda J).map h)).comp x (zero_add 0)) =
      F.obj.map h.op (extSectionsAddEquiv U F x) :=
  (congrArg (sectionsEquiv V F) (addEquiv₀_mk₀_comp _ x)).trans
    (sectionsEquiv_naturality_left h F _)

/-- **Degree-zero sheaf cohomology is the presheaf of sections.** -/
def cohomologyPresheafIsoSections (F : Sheaf J AddCommGrpCat.{v}) :
    F.cohomologyPresheaf 0 ≅ (sheafToPresheaf J AddCommGrpCat.{v}).obj F :=
  NatIso.ofComponents (fun U ↦ (extSectionsAddEquiv U.unop F).toAddCommGrpIso)
    (fun {_ _} h ↦ ConcreteCategory.hom_ext _ _ fun x ↦
      ((ConcreteCategory.comp_apply _ _ x).trans
        (extSectionsAddEquiv_naturality_left h.unop F x)).trans
        (ConcreteCategory.comp_apply _ _ x).symm)

/-- The restriction maps of `Sheaf.cohomologyPresheaf` are precomposition with the induced map of
free abelian sheaves. -/
theorem cohomologyPresheaf_map_apply (F : Sheaf J AddCommGrpCat.{v}) (p : ℕ) {U V : C}
    (h : V ⟶ U) (x : Ext.{v} ((freeYoneda J).obj U) F p) :
    (F.cohomologyPresheaf p).map h.op x =
      (Ext.mk₀ ((freeYoneda J).map h)).comp x (zero_add p) :=
  rfl

/-- The action of `Sheaf.cohomologyPresheafFunctor` on a morphism of sheaves is postcomposition. -/
theorem cohomologyPresheafFunctor_map_app_apply {F G : Sheaf J AddCommGrpCat.{v}} (β : F ⟶ G)
    (p : ℕ) (U : C) (x : Ext.{v} ((freeYoneda J).obj U) F p) :
    ((Sheaf.cohomologyPresheafFunctor J p).map β).app (op U) x =
      x.comp (Ext.mk₀ β) (add_zero p) :=
  rfl

/-- The component at `U` of `cohomologyPresheafIsoSections` is `extSectionsAddEquiv`. -/
theorem cohomologyPresheafIsoSections_hom_app_apply (F : Sheaf J AddCommGrpCat.{v}) (U : C)
    (x : Ext.{v} ((freeYoneda J).obj U) F 0) :
    ((cohomologyPresheafIsoSections F).app (op U)).hom x = extSectionsAddEquiv U F x :=
  rfl

end Ext

end

end Stacks.Cohomology.FreeYoneda

end
