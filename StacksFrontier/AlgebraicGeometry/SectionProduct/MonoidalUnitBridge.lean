module

public import StacksFrontier.AlgebraicGeometry.SectionProduct.BijStalk

/-!
# The two units of the modules on a scheme, compared

The sheaves of modules on a scheme carry two different objects that both deserve the name "unit",
and the gap between them is what blocks the last step of clause 2 of [Stacks, Tag 01CY]:

* `𝟙_ X.Modules`, the monoidal unit of `Stacks.SheafInternalHom.schemeMonoidalCategory`. That
  monoidal structure is obtained by localizing the sectionwise one on presheaves of modules, so
  its unit is the **sheafification of the presheaf unit**, and it is what
  `Stacks.TensorSectionNonvanishing.mulRight` takes a global section as a morphism out of.
* `SheafOfModules.unit X.ringCatSheaf`, Mathlib's free sheaf of modules of rank one, which is the
  **presheaf unit together with a proof that it is already a sheaf**. It is what
  `AlgebraicGeometry.SheafOfModules.unitHomEquiv` — hence
  `Stacks.SectionProduct.app_bijective_of_le_nonvanishingLocus` — produces a morphism out of.

These are not the same object and not definitionally equal: `monoidalUnit_eq_sheafify_unit` below
records that the first is the sheafification of the second, and sheafifying a sheaf returns an
isomorphic, not an equal, sheaf. An equality between the two is rejected with "`𝟙_ X.Modules` is
not definitionally equal to `SheafOfModules.unit X.ringCatSheaf`", and no transparency setting can
change that. What is needed is a genuine comparison isomorphism: the counit of the sheafification
adjunction, which is an isomorphism because sheaves of modules are a reflective subcategory of
presheaves of modules. That isomorphism already exists, as
`AlgebraicGeometry.SheafOfModules.unitIso`, and everything below is phrased with it.

## Main definitions

* `Stacks.SectionProduct.ofUnitHom` and `Stacks.SectionProduct.toUnitHom`: the two directions of
  the induced bijection on morphisms into a fixed `L`, packaged as
  `Stacks.SectionProduct.ofUnitHomEquiv`. `ofUnitHom` is the one a caller wants: it turns a term
  of type `SheafOfModules.unit X.ringCatSheaf ⟶ L` into one of type `𝟙_ X.Modules ⟶ L`.
* `Stacks.SectionProduct.monoidalUnitHomEquiv`: the global sections of `L` are the morphisms out
  of the monoidal unit, by composing `ofUnitHomEquiv` with Mathlib's
  `SheafOfModules.unitHomEquiv`.

## Main results

* `Stacks.SectionProduct.monoidalUnit_eq_sheafify_unit`: the monoidal unit **is** the
  sheafification of Mathlib's unit, by `rfl` at default transparency. This is what makes
  `AlgebraicGeometry.SheafOfModules.unitIso` usable with `𝟙_ X.Modules` as its source.
* `Stacks.SectionProduct.mulRight_ofUnitHom`: **the transport lemma.** Multiplication by a
  re-seated section is the right unitor followed by the comparison isomorphism whiskered by `F`,
  followed by the section whiskered by `F`.
* `Stacks.SectionProduct.mulRight_eq_mulRight_ofUnitHom`: multiplication by an arbitrary
  `f : 𝟙_ X.Modules ⟶ L` **is** multiplication by the re-seated morphism carrying the same global
  section, so nothing is lost by always working with the re-seated form.
* `Stacks.SectionProduct.app_bijective_ofUnitHom`: re-seating does not disturb bijectivity on
  sections over an open, the comparison isomorphism being an isomorphism.
* `Stacks.SectionProduct.bijective_mapFun_mulRight_unitHomEquiv_symm` and
  `Stacks.SectionProduct.bijective_mapFun_mulRight_of_le_nonvanishingLocus`: **the payoff.**
  Clause 2 of [Stacks, Tag 01CY] in whiskered form, with its hypothesis discharged from
  nonvanishing rather than assumed. The first is stated for a section re-seated out of
  `SheafOfModules.unitHomEquiv`; the second is stated for an arbitrary morphism out of the
  monoidal unit, with the nonvanishing hypothesis read off its global section through
  `monoidalUnitHomEquiv`.

## Implementation notes

**Which direction the comparison points, and why.** `AlgebraicGeometry.SheafOfModules.unitIso`
goes *from* the monoidal unit *to* Mathlib's unit. That is the direction in which it is built — it
is a component of the counit of sheafification, whose source is a sheafification — and it is also
the direction a caller needs: `ofUnitHom g` is `unitIso.hom ≫ g`, so a morphism out of Mathlib's
unit is pre-composed and nothing has to be inverted at the point of use.

**Why every proof here is a term and not a rewrite.** A goal that mentions both units at once is
not type-correct at the *reducible* transparency at which `rw`, `simp only` and `conv` check their
motives, even though it is perfectly type-correct at default transparency. For instance,
`rw [Iso.hom_inv_id_assoc]` against the goal
`unitIso.hom ≫ unitIso.inv ≫ f = f` reports "Did not find an occurrence of
the pattern" against a pattern that is plainly there, with the explanation "the argument
`X.ringCatSheaf` has type `TopCat.Sheaf RingCat ↑X.toPresheafedSpace` but is expected to have type
`Sheaf (Opens.grothendieckTopology ↥X) RingCat`"; the same happens to
`MonoidalCategory.whiskerLeft_comp` and to `Functor.map_comp`. So each such step is discharged by
`exact`, which works at default transparency, applied to a declaration whose own type fixes the
spelling.

`app_bijective_of_hom_inv` and `app_bijective_of_eq_comp` are stated for plain
`PresheafOfModules` variables for the same reason: inside them no second spelling occurs, so the
ordinary rewriting tactics work, and the mixed-spelling unification is paid once, at their call
site in `app_bijective_ofUnitHom`.

**The isomorphism is not evaluated on a section anywhere.** As in the sibling file, the route to
the payoff only ever uses that the comparison is an isomorphism; no formula for its value on a
section is needed, and none is proved. Identifying `Stacks.TensorSectionNonvanishing.mulSec` with
an elementary tensor remains open, exactly as recorded in
`StacksFrontier/AlgebraicGeometry/TensorSectionNonvanishing/Basic.lean`.

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public noncomputable section

open CategoryTheory Category AlgebraicGeometry Opposite MonoidalCategory
  Stacks.SheafOfModules.TensorSheafification
open TopologicalSpace

universe u

namespace Stacks.SectionProduct

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {X : Scheme.{u}}

/-! ### The comparison isomorphism -/

/-- **The monoidal unit is the sheafification of Mathlib's unit sheaf of modules.** The monoidal
structure on `X.Modules` is the localization of the sectionwise one on presheaves of modules, so
its unit is the sheafification of the presheaf unit, and the underlying presheaf of modules of
`SheafOfModules.unit X.ringCatSheaf` is that presheaf unit. An equality, not merely an
isomorphism, and it holds at default transparency, which is what lets
`AlgebraicGeometry.SheafOfModules.unitIso` be used with the monoidal unit as its source. -/
theorem monoidalUnit_eq_sheafify_unit (X : Scheme.{u}) :
    (𝟙_ X.Modules) = (sheafify X.presheaf (hStruct X)).obj
      ((forgetFun X).obj (_root_.SheafOfModules.unit X.ringCatSheaf)) :=
  rfl

/-- The forward direction of `AlgebraicGeometry.SheafOfModules.unitIso` is the counit of the
sheafification adjunction at Mathlib's unit. -/
theorem unitIso_hom (X : Scheme.{u}) :
    (_root_.AlgebraicGeometry.SheafOfModules.unitIso X.presheaf (hStruct X)).hom =
      (sheafifyAdjunction X.presheaf (hStruct X)).counit.app
        (_root_.SheafOfModules.unit X.ringCatSheaf) :=
  rfl

/-! ### Re-seating a morphism out of Mathlib's unit -/

/-- **A morphism out of Mathlib's unit, read as a morphism out of the monoidal unit.** This is the
declaration a caller holding `L.unitHomEquiv.symm s` reaches for: its result has the type
`Stacks.TensorSectionNonvanishing.mulRight` requires. -/
def ofUnitHom {L : X.Modules}
    (g : (_root_.SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ L) : 𝟙_ X.Modules ⟶ L :=
  (_root_.AlgebraicGeometry.SheafOfModules.unitIso X.presheaf (hStruct X)).hom ≫ g

/-- `ofUnitHom` is pre-composition with the comparison isomorphism. -/
theorem ofUnitHom_eq {L : X.Modules}
    (g : (_root_.SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ L) :
    ofUnitHom g =
      (_root_.AlgebraicGeometry.SheafOfModules.unitIso X.presheaf (hStruct X)).hom ≫ g :=
  rfl

/-- **A morphism out of the monoidal unit, read as a morphism out of Mathlib's unit**: the inverse
of `ofUnitHom`, and what feeds `AlgebraicGeometry.SheafOfModules.unitHomEquiv`. -/
def toUnitHom {L : X.Modules} (f : 𝟙_ X.Modules ⟶ L) :
    (_root_.SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ L :=
  (_root_.AlgebraicGeometry.SheafOfModules.unitIso X.presheaf (hStruct X)).inv ≫ f

/-- `toUnitHom` is pre-composition with the inverse of the comparison isomorphism. -/
theorem toUnitHom_eq {L : X.Modules} (f : 𝟙_ X.Modules ⟶ L) :
    toUnitHom f =
      (_root_.AlgebraicGeometry.SheafOfModules.unitIso X.presheaf (hStruct X)).inv ≫ f :=
  rfl

/-- Re-seating out of the monoidal unit and back is the identity. -/
theorem ofUnitHom_toUnitHom {L : X.Modules} (f : 𝟙_ X.Modules ⟶ L) :
    ofUnitHom (toUnitHom f) = f :=
  (_root_.AlgebraicGeometry.SheafOfModules.unitIso X.presheaf (hStruct X)).hom_inv_id_assoc f

/-- Re-seating out of Mathlib's unit and back is the identity. -/
theorem toUnitHom_ofUnitHom {L : X.Modules}
    (g : (_root_.SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ L) :
    toUnitHom (ofUnitHom g) = g :=
  (_root_.AlgebraicGeometry.SheafOfModules.unitIso X.presheaf (hStruct X)).inv_hom_id_assoc g

/-- **Re-seating is a bijection**: the morphisms out of Mathlib's unit into `L` are exactly the
morphisms out of the monoidal unit into `L`. -/
def ofUnitHomEquiv (L : X.Modules) :
    ((_root_.SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ L) ≃ (𝟙_ X.Modules ⟶ L) where
  toFun := ofUnitHom
  invFun := toUnitHom
  left_inv := toUnitHom_ofUnitHom
  right_inv := ofUnitHom_toUnitHom

/-- **The global sections of `L` are the morphisms out of the monoidal unit.** Mathlib's
`AlgebraicGeometry.SheafOfModules.unitHomEquiv` says this for its own unit; this transports it
across `ofUnitHomEquiv`. -/
def monoidalUnitHomEquiv (L : X.Modules) : (𝟙_ X.Modules ⟶ L) ≃ L.sections :=
  (ofUnitHomEquiv L).symm.trans L.unitHomEquiv

/-- The inverse of `monoidalUnitHomEquiv` is `ofUnitHom` applied to Mathlib's section-to-morphism
bijection. -/
theorem monoidalUnitHomEquiv_symm_apply (L : X.Modules) (s : L.sections) :
    (monoidalUnitHomEquiv L).symm s = ofUnitHom (L.unitHomEquiv.symm s) :=
  rfl

/-! ### Transport of `mulRight` -/

open Stacks.TensorSectionNonvanishing

/-- `Stacks.TensorSectionNonvanishing.mulRight` is the right unitor followed by the whiskered
section, unfolded here so that the transport lemma can be stated as an equality of composites. -/
theorem mulRight_eq (F : X.Modules) {G : X.Modules} (f : 𝟙_ X.Modules ⟶ G) :
    mulRight F f = (ρ_ F).inv ≫ F ◁ f :=
  rfl

/-- **The transport lemma.** Multiplication by a section re-seated out of Mathlib's unit is the
right unitor, then the comparison isomorphism whiskered by `F`, then the section whiskered by
`F`. So `mulRight` conjugated along `AlgebraicGeometry.SheafOfModules.unitIso` is multiplication
by the same section, and a term of type `SheafOfModules.unit X.ringCatSheaf ⟶ L` may be used
wherever `f : 𝟙_ X.Modules ⟶ L` is required. -/
theorem mulRight_ofUnitHom (F : X.Modules) {L : X.Modules}
    (g : (_root_.SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ L) :
    mulRight F (ofUnitHom g) = (ρ_ F).inv ≫
      F ◁ (_root_.AlgebraicGeometry.SheafOfModules.unitIso X.presheaf (hStruct X)).hom ≫ F ◁ g :=
  whisker_eq (ρ_ F).inv (MonoidalCategory.whiskerLeft_comp F
    (_root_.AlgebraicGeometry.SheafOfModules.unitIso X.presheaf (hStruct X)).hom g)

/-- **Nothing is lost by always re-seating.** Multiplication by an arbitrary morphism `f` out of
the monoidal unit is multiplication by the morphism out of Mathlib's unit carrying the same
global section, so a statement proved for re-seated sections is a statement about every `f`. -/
theorem mulRight_eq_mulRight_ofUnitHom (F : X.Modules) {L : X.Modules}
    (f : 𝟙_ X.Modules ⟶ L) :
    mulRight F f
      = mulRight F (ofUnitHom (L.unitHomEquiv.symm (monoidalUnitHomEquiv L f))) :=
  congrArg (fun y : 𝟙_ X.Modules ⟶ L => mulRight F y)
    ((monoidalUnitHomEquiv L).symm_apply_apply f).symm

/-- Re-seating a section of `L` and reading its global section again returns that section. -/
theorem monoidalUnitHomEquiv_ofUnitHom_unitHomEquiv_symm (L : X.Modules) (s : L.sections) :
    monoidalUnitHomEquiv L (ofUnitHom (L.unitHomEquiv.symm s)) = s :=
  (monoidalUnitHomEquiv L).apply_symm_apply s

/-! ### Bijectivity on sections survives the re-seating -/

/-- A morphism of presheaves of modules with a two-sided inverse is bijective on sections over
every open. Stated with the inverse as data, and for plain `PresheafOfModules` variables, so that
only one spelling of the category occurs inside the proof. -/
theorem app_bijective_of_hom_inv
    {P Q : PresheafOfModules.{u} (structureSheaf X.presheaf (hStruct X)).obj}
    {φ : P ⟶ Q} {φ' : Q ⟶ P} (h1 : φ ≫ φ' = 𝟙 P) (h2 : φ' ≫ φ = 𝟙 Q) (U : X.Opens) :
    Function.Bijective (φ.app (op U)) := by
  have : IsIso φ := ⟨φ', h1, h2⟩
  exact ConcreteCategory.bijective_of_isIso ((PresheafOfModules.evaluation _ (op U)).map φ)

/-- A morphism of presheaves of modules that factors as a composite of two maps bijective on
sections over `U` is bijective on sections over `U`. -/
theorem app_bijective_of_eq_comp
    {P Q R : PresheafOfModules.{u} (structureSheaf X.presheaf (hStruct X)).obj}
    {φ : P ⟶ R} {α : P ⟶ Q} {β : Q ⟶ R} (hφ : φ = α ≫ β) (U : X.Opens)
    (hα : Function.Bijective (α.app (op U))) (hβ : Function.Bijective (β.app (op U))) :
    Function.Bijective (φ.app (op U)) := by
  subst hφ
  rw [PresheafOfModules.comp_app]
  exact hβ.comp hα

/-- **Re-seating does not disturb bijectivity on sections.** `ofUnitHom g` is `g` pre-composed
with an isomorphism, and the underlying presheaf functor carries that isomorphism to one that is
bijective on sections over every open. This is the only thing the payoff needs from
`AlgebraicGeometry.SheafOfModules.unitIso` beyond its existence. -/
theorem app_bijective_ofUnitHom {L : X.Modules}
    (g : (_root_.SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ L) (U : X.Opens)
    (h : Function.Bijective (((forgetFun X).map g).app (op U))) :
    Function.Bijective (((forgetFun X).map (ofUnitHom g)).app (op U)) := by
  have hmap : (forgetFun X).map (ofUnitHom g) = (forgetFun X).map
        (_root_.AlgebraicGeometry.SheafOfModules.unitIso X.presheaf (hStruct X)).hom ≫
      (forgetFun X).map g :=
    (forgetFun X).map_comp
      (_root_.AlgebraicGeometry.SheafOfModules.unitIso X.presheaf (hStruct X)).hom g
  exact app_bijective_of_eq_comp hmap U
    (app_bijective_of_hom_inv ((forgetFun X).mapIso
        (_root_.AlgebraicGeometry.SheafOfModules.unitIso X.presheaf (hStruct X))).hom_inv_id
      ((forgetFun X).mapIso
        (_root_.AlgebraicGeometry.SheafOfModules.unitIso X.presheaf (hStruct X))).inv_hom_id U) h

/-! ### The payoff: clause 2 of Tag 01CY with its hypothesis discharged -/

section Nonvanishing

open Stacks.SheafOfModules
open Stacks.SheafOfModules.TensorStalkRingedSpace

/-- **Multiplication by a nonvanishing global section is bijective on the stalk at every nearby
point.** `Stacks.SectionProduct.bijective_mapFun_mulRight_of_app_bijective` takes its hypothesis
`hf` as given; here it is discharged by
`Stacks.SectionProduct.app_bijective_of_le_nonvanishingLocus`, whose conclusion is about a
morphism out of Mathlib's unit and is carried across the comparison isomorphism by
`app_bijective_ofUnitHom`. -/
theorem bijective_mapFun_mulRight_unitHomEquiv_symm (F : X.Modules) (L N : X.Modules)
    (ψ : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (L)).obj (N)) ≅
        _root_.SheafOfModules.unit _) (s : L.sections)
    {W : X.Opens} {x : X} (hx : x ∈ W)
    (hW : ∀ y ∈ W,
      y ∈ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) L s) :
    Function.Bijective (Stacks.ModuleStalk.mapFun
      (mulRight F (ofUnitHom (L.unitHomEquiv.symm s))) x) :=
  bijective_mapFun_mulRight_of_app_bijective F (ofUnitHom (L.unitHomEquiv.symm s)) hx
    fun U hU => app_bijective_ofUnitHom _ U
      (app_bijective_of_le_nonvanishingLocus L N ψ s hW U hU)

/-- **The same statement for an arbitrary morphism out of the monoidal unit.** The nonvanishing
hypothesis is read off the global section of `f` through `monoidalUnitHomEquiv`, and the
conclusion is about `mulRight F f` itself, so a caller never has to mention Mathlib's unit. This
is the form the rest of the development consumes. -/
theorem bijective_mapFun_mulRight_of_le_nonvanishingLocus (F : X.Modules) (L N : X.Modules)
    (ψ : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (L)).obj (N)) ≅
        _root_.SheafOfModules.unit _)
    (f : 𝟙_ X.Modules ⟶ L) {W : X.Opens} {x : X} (hx : x ∈ W)
    (hW : ∀ y ∈ W, y ∈ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) L
      (monoidalUnitHomEquiv L f)) :
    Function.Bijective (Stacks.ModuleStalk.mapFun (mulRight F f) x) :=
  bijStalk_congr (mulRight_eq_mulRight_ofUnitHom F f).symm
    (bijective_mapFun_mulRight_unitHomEquiv_symm F L N ψ (monoidalUnitHomEquiv L f) hx hW)

end Nonvanishing

end Stacks.SectionProduct

end
