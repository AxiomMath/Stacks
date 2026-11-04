module

public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Sheafification
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sheafified representables

The sheafified Yoneda embedding sends an object `U` of a site to the sheafification `h_U^#` of
the presheaf it represents. A morphism `h_X^# ⟶ F` into a sheaf is the same as a section of `F`
over `X`, and every sheaf `F` of sets is the colimit of the sheafified representables `h_U^#`
over the opposite of its category of elements.

## Main definitions

* `CategoryTheory.Sheaf.sheafifiedYoneda`: the functor `U ↦ h_U^#`.
* `CategoryTheory.Sheaf.sectionEquiv`: Yoneda's lemma for sheaves, `Mor(h_X^#, F) ≃ F(X)`.
* `CategoryTheory.Sheaf.tautologicalSection`: the section of `h_X^#` over `X` corresponding to the
  identity of `h_X^#`.
* `CategoryTheory.Sheaf.indexingDiagram` and `CategoryTheory.Sheaf.coconeOfRepresentable`: the
  diagram of sheafified representables over the category of elements of a sheaf `F`, and its
  cocone with point `F`.
* `CategoryTheory.Sheaf.colimitOfRepresentable`: that cocone is a colimit.

## Main results

* `CategoryTheory.Sheaf.sectionEquiv_sheafifiedYoneda_map`: the section of `h_X^#` over `Y`
  corresponding to `h_l^#` is the image of `l : Y ⟶ X` under the sheafification map
  `h_X ⟶ h_X^#`.
* `CategoryTheory.Sheaf.mono_sheafifiedYoneda_map`: the sheafified Yoneda embedding preserves
  monomorphisms.

## References

* [Stacks Project, Tag 0GLW](https://stacks.math.columbia.edu/tag/0GLW)
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J (Type max u v)]

/-- The sheafified Yoneda embedding `U ↦ h_U^#`. -/
noncomputable def sheafifiedYoneda : C ⥤ Sheaf J (Type max u v) :=
  uliftYoneda.{u} ⋙ presheafToSheaf J (Type max u v)

/-- The sheafified representable `h_X^#` is the sheafification of the presheaf represented by
`X`. -/
@[simp, sga "4 V 2.4.1"]
theorem sheafifiedYoneda_obj (X : C) :
    (sheafifiedYoneda J).obj X = (presheafToSheaf J (Type max u v)).obj (uliftYoneda.{u}.obj X) :=
  rfl

/-- The map `h_g^#` of sheafified representables induced by `g : X ⟶ Y` is the sheafification of
the map of representable presheaves induced by `g`. -/
@[simp]
theorem sheafifiedYoneda_map {X Y : C} (g : X ⟶ Y) :
    (sheafifiedYoneda J).map g = (presheafToSheaf J (Type max u v)).map (uliftYoneda.{u}.map g) :=
  rfl

/-! ### Yoneda's lemma for sheaves of sets -/

/-- **Yoneda's lemma for sheaves of sets**: a morphism `h_X^# ⟶ F` out of a sheafified
representable is the same thing as a section of `F` over `X`. It is the sheafification adjunction
followed by Yoneda's lemma for presheaves. -/
@[sga "4 IV 8.2" "partial", sga "4 VIII 7.9.1"]
noncomputable def sectionEquiv {X : C} {F : Sheaf J (Type max u v)} :
    ((sheafifiedYoneda J).obj X ⟶ F) ≃ F.obj.obj (op X) :=
  ((sheafificationAdjunction J (Type max u v)).homEquiv (uliftYoneda.{u}.obj X) F).trans
    uliftYonedaEquiv.{u}

/-- Composing `α : h_X^# ⟶ F` with `β : F ⟶ G` acts on the corresponding sections by `β`. -/
theorem sectionEquiv_comp {X : C} {F G : Sheaf J (Type max u v)}
    (α : (sheafifiedYoneda J).obj X ⟶ F) (β : F ⟶ G) :
    sectionEquiv J (α ≫ β) = β.hom.app (op X) (sectionEquiv J α) :=
  congrArg (fun γ => uliftYonedaEquiv.{u} γ)
    ((sheafificationAdjunction J (Type max u v)).homEquiv_naturality_right α β)

/-- Precomposing `α : h_X^# ⟶ F` with `h_i^#`, for `i : Y ⟶ X`, restricts the corresponding
section along `i`. -/
theorem sectionEquiv_map_comp {X Y : C} (i : Y ⟶ X) {F : Sheaf J (Type max u v)}
    (α : (sheafifiedYoneda J).obj X ⟶ F) :
    sectionEquiv J ((sheafifiedYoneda J).map i ≫ α) = F.obj.map i.op (sectionEquiv J α) :=
  (congrArg (fun β : uliftYoneda.{u}.obj Y ⟶ (sheafToPresheaf J (Type max u v)).obj F =>
      uliftYonedaEquiv.{u} β)
    ((sheafificationAdjunction J (Type max u v)).homEquiv_naturality_left (uliftYoneda.{u}.map i)
      (show (presheafToSheaf J (Type max u v)).obj (uliftYoneda.{u}.obj X) ⟶ F from α))).trans
    (uliftYonedaEquiv_naturality
      ((sheafificationAdjunction J (Type max u v)).homEquiv (uliftYoneda.{u}.obj X) F α) i.op).symm

/-- The identity of `h_X^#` corresponds to the image of `𝟙 X` under the sheafification map
`h_X ⟶ h_X^#`. -/
theorem sectionEquiv_id (X : C) :
    sectionEquiv J (𝟙 ((sheafifiedYoneda J).obj X)) =
      (toSheafify J (uliftYoneda.{u}.obj X)).app (op X) (ULift.up (𝟙 X)) :=
  congrArg (fun γ => uliftYonedaEquiv.{u} γ)
    ((sheafificationAdjunction J (Type max u v)).homEquiv_id (uliftYoneda.{u}.obj X))

/-- The morphism `h_l^#` of sheafified representables is the section of `h_X^#` over `Y` obtained
from `l : Y ⟶ X` by the sheafification map `h_X ⟶ h_X^#`. -/
theorem sectionEquiv_sheafifiedYoneda_map {X Y : C} (l : Y ⟶ X) :
    sectionEquiv J ((sheafifiedYoneda J).map l) =
      (toSheafify J (uliftYoneda.{u}.obj X)).app (op Y) (ULift.up l) := by
  have h : uliftYonedaEquiv.{u}.symm (sectionEquiv J (𝟙 ((sheafifiedYoneda J).obj X)))
      = toSheafify J (uliftYoneda.{u}.obj X) := (Equiv.symm_apply_eq _).2 (sectionEquiv_id J X)
  rw [← h, ← Category.comp_id ((sheafifiedYoneda J).map l), sectionEquiv_map_comp]
  rfl

/-- Under `Mor(h_X^#, -) ≃ (-)(X)`, the action of a morphism of sheaves on sections corresponds to
postcomposition. -/
theorem sectionEquiv_symm_comp {X : C} {F G : Sheaf J (Type max u v)} (β : F ⟶ G)
    (x : F.obj.obj (op X)) :
    (sectionEquiv J).symm (β.hom.app (op X) x) = (sectionEquiv J).symm x ≫ β := by
  rw [Equiv.symm_apply_eq, sectionEquiv_comp, Equiv.apply_symm_apply]

/-- Under `Mor(h_X^#, -) ≃ (-)(X)`, restricting a section along `i : Y ⟶ X` corresponds to
precomposition with `h_i^#`. -/
theorem sectionEquiv_symm_map {X Y : C} (i : Y ⟶ X) {F : Sheaf J (Type max u v)}
    (x : F.obj.obj (op X)) :
    (sectionEquiv J).symm (F.obj.map i.op x) =
      (sheafifiedYoneda J).map i ≫ (sectionEquiv J).symm x := by
  rw [Equiv.symm_apply_eq, sectionEquiv_map_comp, Equiv.apply_symm_apply]

/-- The tautological section of `h_X^#` over `X`, corresponding to the identity of `h_X^#`. -/
noncomputable abbrev tautologicalSection (X : C) :
    ((sheafifiedYoneda J).obj X).obj.obj (op X) :=
  sectionEquiv J (𝟙 ((sheafifiedYoneda J).obj X))

/-- The restriction of the tautological section of `h_X^#` along `g : Y ⟶ X` is the section
corresponding to `h_g^#`. -/
theorem map_op_tautologicalSection {X Y : C} (g : Y ⟶ X) :
    ((sheafifiedYoneda J).obj X).obj.map g.op (tautologicalSection J X) =
      sectionEquiv J ((sheafifiedYoneda J).map g) := by
  rw [← Category.comp_id ((sheafifiedYoneda J).map g), sectionEquiv_map_comp]

/-! ### Sheaves as colimits of sheafified representables -/

variable (F : Sheaf J (Type max u v))

/-- The diagram `I ⥤ C` for the sheaf `F`: the index category `I` is the opposite of the
category of elements of `F`, whose objects are the pairs `(U, s)` with `s ∈ F(U)` and whose
morphisms `(U, s) ⟶ (U', s')` are the maps `f : U ⟶ U'` with `f^* s' = s`, and the diagram
sends `(U, s)` to `U`. -/
def indexingDiagram : F.obj.Elementsᵒᵖ ⥤ C := (CategoryOfElements.π F.obj).leftOp

/-- The cocone on the sheafified representables `h_{U_i}^#` with point `F`: the sheafification
of the tautological cocone on the representables, with `F^#` identified with `F`. -/
noncomputable def coconeOfRepresentable :
    Cocone (indexingDiagram J F ⋙ sheafifiedYoneda J) :=
  ((presheafToSheaf J (Type max u v)).mapCocone
      (Presheaf.coconeOfRepresentable F.obj)).extend (sheafificationIso F).inv

/-- The point of the cocone on the sheafified representables is the sheaf `F` itself. -/
@[simp]
theorem coconeOfRepresentable_pt : (coconeOfRepresentable J F).pt = F := rfl

/-- A sheaf `F` of sets on a site `C` is the colimit of the sheafified representables
`h_{U_i}^#` along the diagram `indexingDiagram J F`. -/
@[stacks 0GLW "(main statement) Every sheaf of sets on a site is the colimit of the sheafified
  representables over its category of elements. The final clause, that the diagram may be
  taken to land in a given family of objects covering every object, is not covered.",
  sga "4 IV 6.3" "for each sheaf F"]
noncomputable def colimitOfRepresentable : IsColimit (coconeOfRepresentable J F) :=
  IsColimit.ofIsoColimit
    (isColimitOfPreserves (presheafToSheaf J (Type max u v))
      (Presheaf.colimitOfRepresentable.{u} F.obj))
    (Cocone.ext (sheafificationIso F).symm (fun _ => rfl))

end CategoryTheory.Sheaf

/-! ### Sheafified representables of a monomorphism -/

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type max u v)] [J.WEqualsLocallyBijective (Type max u v)]

/-- The sheafified Yoneda embedding takes a monomorphism to a monomorphism. -/
lemma mono_sheafifiedYoneda_map {U V : C} (f : U ⟶ V) [Mono f] :
    Mono ((Sheaf.sheafifiedYoneda J).map f) := by
  have hloc : Sheaf.IsLocallyInjective ((Sheaf.sheafifiedYoneda J).map f) := by
    show Sheaf.IsLocallyInjective
      ((presheafToSheaf J (Type max u v)).map (uliftYoneda.map f))
    rw [Presheaf.isLocallyInjective_presheafToSheaf_map_iff]
    apply Presheaf.isLocallyInjective_of_injective
    intro T x y h
    apply ULift.ext
    apply (cancel_mono f).1
    exact congrArg ULift.down h
  exact Sheaf.mono_of_isLocallyInjective _

end CategoryTheory.Sheaf
