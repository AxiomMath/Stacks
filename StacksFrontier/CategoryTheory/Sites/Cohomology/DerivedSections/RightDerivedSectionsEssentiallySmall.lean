module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.BigSiteObjectCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaRightDerivedUnivLE
public import StacksFrontier.Homology.DerivedIndexing.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Derived sections on an essentially small site

Let `C` be a site with `C : Type u` and `Category.{v} C`. Sheaf cohomology over an object of the
site is the right derived functor of sections over that object; the identification is
`Stacks.Cohomology.FreeYonedaUnivLE.cohomologyPresheafObjIsoRightDerivedSections`, which is
stated with coefficients `AddCommGrpCat.{max u v t}`. The `u` there is not decoration: the
comparison it is built from, `ModuleSheafCohomology.nonempty_extFunctorObj_iso_rightDerived`,
takes its corepresentation in the form of an isomorphism onto
`preadditiveCoyoneda.obj (op X)`, whose values lie in the universe of the *morphisms* of
`Sheaf J AddCommGrpCat.{z}`, namely `max u z`. Demanding that this agree with the coefficient
universe `z` forces `u ≤ z`: the coefficients must dominate the objects of the site.

That condition fails exactly where it matters most. The big `τ`-site of schemes over `S` has its
objects in `Type (u + 1)` and its morphisms in `Type u`, so its natural abelian coefficients are
`AddCommGrpCat.{u}` and the condition asks for `u + 1 ≤ u`. Such a site is `EssentiallySmall.{u}`
and is never `Small.{u}` nor a `SmallCategory`, so no hypothesis of smallness recovers it either.

This file removes the condition. The corepresentation is replaced by its degree-zero `Ext` form,
`Hom(L U, -) ≅ Ext⁰(L U, -)` being an isomorphism of groups across universes rather than an
isomorphism of functors inside one; `ModuleSheafCohomology.extDeltaFunctor` is already universe
general, so the Grothendieck universality argument of [Stacks, Tag 010U] goes through with the
`Ext` universe free of the objects of the site. The coefficient universe becomes `max v t` with
`t` free, and on a site whose objects and morphisms share a universe nothing changes.

On an essentially small site the hypotheses that remain — enough injectives in the category of
abelian sheaves, and `Ext`-groups in the morphism universe of the site — hold automatically,
because abelian sheaves there form a Grothendieck abelian category
(`Stacks.Cohomology.BiggerSite.isGrothendieckAbelian_sheaf`).

## Main definitions

All in the namespace `Stacks.Cohomology.FreeYonedaUnivLE`.

* `extZeroIsoSections`: degree-zero `Ext` out of the free abelian sheaf on `U` is the group of
  sections over `U`.
* `cohomologyPresheafObjIsoRightDerivedSectionsOfEnoughInjectives`: `H^p(U, F)` is the `p`-th
  right derived functor of sections over `U`, with the coefficient universe independent of the
  objects of the site.
* `sheafCohomologyIsoRightDerivedSections`,
  `rightDerivedSheafToPresheafEvaluationIsoSheafCohomology`: the same identification for
  Mathlib's `CategoryTheory.Sheaf.H'`, in the two spellings of sections over an object.
* `sheafCohomologyIsoRightDerivedSectionsOfEssentiallySmall`,
  `rightDerivedSheafToPresheafEvaluationIsoSheafCohomologyOfEssentiallySmall`: the same on an
  essentially small site, with no hypothesis beyond the site and its sheafification.

## Main results

* `ModuleSheafCohomology.nonempty_extFunctorObj_iso_rightDerived_of_extZeroIso`: a left exact
  additive functor to abelian groups whose values are the degree-zero `Ext`-groups out of an
  object `X` has the `Ext`-functors out of `X` as its right derived functors. This is
  `ModuleSheafCohomology.nonempty_extFunctorObj_iso_rightDerived` with the `Ext` universe no
  longer tied to the morphisms of the category.
* `nonempty_extFunctorObj_iso_rightDerived_sections_of_enoughInjectives`: the functor-level
  comparison on an arbitrary site, with coefficients `AddCommGrpCat.{max v t}`.
* `hasExt_essentiallySmallSite`, `enoughInjectives_essentiallySmallSite`: the two hypotheses on
  an essentially small site.

## Implementation notes

The degree-zero input is an isomorphism `extFunctorObj X 0 ≅ G` rather than an isomorphism onto
`preadditiveCoyoneda.obj (op X)`; the two are equivalent when the `Ext` universe is the morphism
universe (`ModuleSheafCohomology.extZeroIsoCoyoneda`) and only the first is statable otherwise.
Both sides of the comparison are universal `δ`-functors — `extDeltaFunctor (𝟭 A) X` and
`Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives G` — so
`CategoryTheory.DeltaFunctor.IsUniversal.isoOfIso` extends the degree-zero identification to all
degrees. `EnoughInjectives` rather than `HasInjectiveResolutions` is what the universality of the
two `δ`-functors needs, so the hypothesis is not the same as the one of
`ModuleSheafCohomology.nonempty_extFunctorObj_iso_rightDerived`, and neither statement follows
from the other.

`hasExt_essentiallySmallSite` and `enoughInjectives_essentiallySmallSite` are theorems, not
instances, following Mathlib's policy on `CategoryTheory.HasExt`: a category has in general
several reasonable `Ext` universes, and two instances would make the universe of `Ext` ambiguous.
A consumer that needs to write `CategoryTheory.Sheaf.H'` over an essentially small site declares
them `local instance`, as the final section of this file does.

Only existence is asserted by the `δ`-functor argument, so the definitions below are choices and
no compatibility in degree zero with the canonical map to the right derived functor is claimed.
For the degree-zero statement that is canonical, use
`Stacks.Cohomology.FreeYonedaUnivLE.cohomologyPresheafIsoSections`.

## References

* [Stacks Project, Tag 010U](https://stacks.math.columbia.edu/tag/010U)
* [Stacks Project, Tag 03AY](https://stacks.math.columbia.edu/tag/03AY)
* [Stacks Project, Tag 09V3](https://stacks.math.columbia.edu/tag/09V3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Abelian

namespace ModuleSheafCohomology

universe w v u

noncomputable section

/-- Postcomposing a degree-zero `Ext`-class with the class of a morphism is, under
`CategoryTheory.Abelian.Ext.addEquiv₀`, composition of morphisms. -/
theorem addEquiv₀_comp_mk₀ {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]
    {X Y Z : A} (e : Ext X Y 0) (f : Y ⟶ Z) :
    Ext.addEquiv₀ (e.comp (Ext.mk₀ f) (add_zero 0)) = Ext.addEquiv₀ e ≫ f := by
  apply Ext.addEquiv₀.symm.injective
  simp only [AddEquiv.symm_apply_apply, Ext.addEquiv₀_symm_apply, ← Ext.mk₀_comp_mk₀,
    Ext.mk₀_addEquiv₀_apply]

/-- **The right derived functors of a corepresented left exact functor are the `Ext`-functors
out of the corepresenting object**, with the `Ext` universe independent of the morphisms of the
category. For an additive, left exact `G : A ⥤ AddCommGrpCat.{w}` whose values are the
degree-zero `Ext`-groups out of `X : A`, the `p`-th right derived functor of `G` is
`Extᵖ(X, -)`.

This is `ModuleSheafCohomology.nonempty_extFunctorObj_iso_rightDerived` with the corepresentation
read in degree-zero `Ext` instead of in `preadditiveCoyoneda`; both `extDeltaFunctor (𝟭 A) X` and
the right derived `δ`-functor of `G` are universal, so [Stacks, Tag 010U] extends the degree-zero
identification to every degree. -/
@[sga "3 XXIV 1.13" "more general"]
theorem nonempty_extFunctorObj_iso_rightDerived_of_extZeroIso
    {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A] [EnoughInjectives A]
    (G : A ⥤ AddCommGrpCat.{w}) [G.Additive] [PreservesFiniteLimits G] (X : A)
    (α : extFunctorObj X 0 ≅ G) (n : ℕ) :
    Nonempty (extFunctorObj X n ≅ G.rightDerived n) := by
  let := HasDerivedCategory.standard A
  let := HasDerivedCategory.standard AddCommGrpCat.{w}
  let : (extDeltaFunctor (𝟭 A) X).IsUniversal :=
    extDeltaFunctor_isUniversal (𝟭 A) X (by
      intro I hI m a
      change Ext X I (m + 1) at a
      exact Ext.eq_zero_of_injective a)
  let : (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives G).IsUniversal :=
    DeltaFunctor.isUniversal_of_isZero_injective _ (by
      intro m I _
      exact Functor.isZero_rightDerived_obj_injective_succ G m I)
  let e₀ : (extDeltaFunctor (𝟭 A) X).functor 0 ≅
      (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives G).functor 0 :=
    Functor.leftUnitor _ ≪≫ α ≪≫ G.rightDerivedZeroIsoSelf.symm
  let β := DeltaFunctor.IsUniversal.isoOfIso e₀
  exact ⟨(Functor.leftUnitor _).symm ≪≫
    { hom := β.hom.app n
      inv := β.inv.app n
      hom_inv_id := congrArg (fun η ↦ η.app n) β.hom_inv_id
      inv_hom_id := congrArg (fun η ↦ η.app n) β.inv_hom_id }⟩

end

end ModuleSheafCohomology

namespace Stacks.Cohomology.FreeYonedaUnivLE

universe s t v u

noncomputable section

/-- Sections over an object of the site are additive, at any coefficient universe. -/
instance additive_sheafSections_obj {D : Type u} [Category.{v} D]
    (K : GrothendieckTopology D) (U : D) :
    ((sheafSections K AddCommGrpCat.{s}).obj (op U)).Additive where
  map_add := by intros; rfl

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v t}]
  [HasExt.{max v t} (Sheaf J AddCommGrpCat.{max v t})]

/-- **Degree-zero `Ext` out of the free abelian sheaf on `U` is the group of sections over
`U`**, naturally in the sheaf. This is the corepresentation
`Stacks.Cohomology.FreeYonedaUnivLE.evaluationRepresentation` read through
`CategoryTheory.Abelian.Ext.addEquiv₀`, which makes it an identification of functors valued in
the coefficients rather than in the morphisms of the sheaf category. -/
def extZeroIsoSections (U : C) :
    extFunctorObj.{max v t} ((freeYoneda.{t} J).obj U) 0 ≅
      (sheafSections J AddCommGrpCat.{max v t}).obj (op U) :=
  NatIso.ofComponents
    (fun F ↦ (Ext.addEquiv₀.trans (sectionsAddEquiv.{t} U F)).toAddCommGrpIso) (by
      intro F G f
      ext e
      exact (congrArg (sectionsEquiv.{t} U G)
          (ModuleSheafCohomology.addEquiv₀_comp_mk₀ e f)).trans
        (sectionsEquiv_naturality.{t} U _ f))

section EnoughInjectives

variable [EnoughInjectives (Sheaf J AddCommGrpCat.{max v t})]

/-- **The `Ext`-functors out of the free abelian sheaf on `U` are the right derived functors of
sections over `U`**, at any coefficient universe dominating the morphisms of the site. This is
`Stacks.Cohomology.FreeYonedaUnivLE.nonempty_extFunctorObj_iso_rightDerived_sections` without the
requirement that the coefficients also dominate the objects of the site. -/
@[sga "4 V 2.1.2" "Ext^q(A_X, special case"]
theorem nonempty_extFunctorObj_iso_rightDerived_sections_of_enoughInjectives (U : C) (p : ℕ) :
    Nonempty (extFunctorObj.{max v t} ((freeYoneda.{t} J).obj U) p ≅
      ((sheafSections J AddCommGrpCat.{max v t}).obj (op U)).rightDerived p) :=
  ModuleSheafCohomology.nonempty_extFunctorObj_iso_rightDerived_of_extZeroIso
    ((sheafSections J AddCommGrpCat.{max v t}).obj (op U)) _ (extZeroIsoSections.{t} J U) p

/-- **Sheaf cohomology over an object of the site is right-derived sections**, at any coefficient
universe dominating the morphisms of the site.

This is a choice: see `nonempty_extFunctorObj_iso_rightDerived_sections_of_enoughInjectives`. -/
@[sga "4 V 2.1.2" "Ext^q(A_X"]
def cohomologyPresheafObjIsoRightDerivedSectionsOfEnoughInjectives
    (F : Sheaf J AddCommGrpCat.{max v t}) (p : ℕ) (U : C) :
    (cohomologyPresheaf.{max v t, t} F p).obj (op U) ≅
      (((sheafSections J AddCommGrpCat.{max v t}).obj (op U)).rightDerived p).obj F :=
  (nonempty_extFunctorObj_iso_rightDerived_sections_of_enoughInjectives.{t} J U p).some.app F

end EnoughInjectives

section Pinned

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}] [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{v})]

/-- **Mathlib's sheaf cohomology over an object of the site is right-derived sections.** For an
abelian sheaf `F` with coefficients in the morphism universe of the site,
`CategoryTheory.Sheaf.H' F p T` is the `p`-th right derived functor of sections over `T`,
evaluated at `F`.

This is `Stacks.Cohomology.SiteSections.cohomologyIsoRightDerivedSections` with `[SmallCategory C]`
replaced by the two hypotheses that a site whose objects live above its morphisms can still
satisfy; `freeYonedaIso` identifies the free abelian sheaf built on `uliftYoneda` with the one
built on `yoneda`.

This is a choice: see `nonempty_extFunctorObj_iso_rightDerived_sections_of_enoughInjectives`. -/
@[sga "4 V 2.1.2" "H^q(X"]
def sheafCohomologyIsoRightDerivedSections (F : Sheaf J AddCommGrpCat.{v}) (p : ℕ) (T : C) :
    Sheaf.H' F p T ≅
      (((sheafSections J AddCommGrpCat.{v}).obj (op T)).rightDerived p).obj F :=
  (cohomologyPresheafObjIsoPinned.{v} J F p T).symm ≪≫
    cohomologyPresheafObjIsoRightDerivedSectionsOfEnoughInjectives.{v} J F p T

/-- **The right derived functors of sections, written as the inclusion of abelian sheaves into
abelian presheaves followed by evaluation, are sheaf cohomology.** This is
`sheafCohomologyIsoRightDerivedSections` in the spelling
`sheafToPresheaf J A ⋙ (evaluation Cᵒᵖ A).obj (op T)` of sections over `T`. -/
def rightDerivedSheafToPresheafEvaluationIsoSheafCohomology
    (F : Sheaf J AddCommGrpCat.{v}) (p : ℕ) (T : C) :
    (((sheafToPresheaf J AddCommGrpCat.{v} ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (op T)).rightDerived p).obj F) ≅
      Sheaf.H' F p T :=
  (sheafCohomologyIsoRightDerivedSections.{v} J F p T).symm

end Pinned

section EssentiallySmall

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]

/-- **Abelian sheaves on an essentially small site have enough injectives**, with coefficients in
the morphism universe of the site: they form a Grothendieck abelian category. -/
theorem enoughInjectives_essentiallySmallSite :
    EnoughInjectives (Sheaf J AddCommGrpCat.{v}) :=
  have := Stacks.Cohomology.BiggerSite.isGrothendieckAbelian_sheaf.{v} J
  inferInstance

/-- **`Ext`-groups of abelian sheaves on an essentially small site lie in the morphism universe
of the site**, which is one universe below the morphisms of the sheaf category when the objects
of the site do not. -/
theorem hasExt_essentiallySmallSite : HasExt.{v} (Sheaf J AddCommGrpCat.{v}) :=
  have := Stacks.Cohomology.BiggerSite.isGrothendieckAbelian_sheaf.{v} J
  inferInstance

section

attribute [local instance] enoughInjectives_essentiallySmallSite hasExt_essentiallySmallSite

/-- **Sheaf cohomology over an object of an essentially small site is right-derived sections.**
This is `sheafCohomologyIsoRightDerivedSections` with its two hypotheses discharged; it applies
in particular to the big `τ`-sites of schemes, whose objects live one universe above their
morphisms, and which are therefore `EssentiallySmall` and never `SmallCategory`. -/
def sheafCohomologyIsoRightDerivedSectionsOfEssentiallySmall
    (F : Sheaf J AddCommGrpCat.{v}) (p : ℕ) (T : C) :
    Sheaf.H' F p T ≅
      (((sheafSections J AddCommGrpCat.{v}).obj (op T)).rightDerived p).obj F :=
  sheafCohomologyIsoRightDerivedSections.{v} J F p T

/-- **The derived-sections identification on an essentially small site**, with sections written
as the inclusion of abelian sheaves into abelian presheaves followed by evaluation. -/
def rightDerivedSheafToPresheafEvaluationIsoSheafCohomologyOfEssentiallySmall
    (F : Sheaf J AddCommGrpCat.{v}) (p : ℕ) (T : C) :
    (((sheafToPresheaf J AddCommGrpCat.{v} ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (op T)).rightDerived p).obj F) ≅
      Sheaf.H' F p T :=
  rightDerivedSheafToPresheafEvaluationIsoSheafCohomology.{v} J F p T

end

end EssentiallySmall

end

end Stacks.Cohomology.FreeYonedaUnivLE

end
