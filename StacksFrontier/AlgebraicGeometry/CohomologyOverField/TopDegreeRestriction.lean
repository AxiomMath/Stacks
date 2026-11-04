module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.Cohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedFunctors.ForgetfulInclusionCohomologyPresheaf
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.CompatibilityWithRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.SpectralSpaces

/-!
# The top-degree restriction map in the `cohomologyOverField` spelling

[Stacks, Tag 0A3G] clause (2) says that on a spectral space `X` of Krull dimension `d` the
restriction `H^d(X, ℱ) → H^d(U, ℱ)` is surjective for every quasi-compact open `U`. It is proved
in `StacksFrontier/Topology/Sheaves/Cohomology/Vanishing/SpectralSpaces.lean` as
`Stacks.CohomologyVanishing.surjective_cohomologyPresheaf_map_top_of_topologicalKrullDim_le`,
stated for Mathlib's `CategoryTheory.Sheaf.cohomologyPresheaf` — the `Ext`-group out of the free
abelian sheaf on `yoneda.obj U`.

The cohomology that `StacksFrontier/AlgebraicGeometry/TopDegreeCoherentFiniteness/Basic.lean` and
the rest of the coherent-finiteness development speak about is a different object:
`AlgebraicGeometry.cohomologyOverField`, the right derived functor of module-valued sections over
`⊤` with the `k`-action obtained by restricting scalars along the structure morphism. This file
transports clause (2) from the first spelling to the second, compatibly with restriction to an
open and `k`-linearly.

## The route, and why each step is available

The transport is four naturality squares, each of which identifies a *named* comparison
isomorphism rather than a chosen one — that is the whole difficulty, since
`Stacks.Cohomology.SiteSections.cohomologyIsoRightDerivedSections` is `Nonempty.some` of an
existence statement and therefore satisfies no equation relating two different opens.

1. `cohomologyPresheafIsoRightDerivedSections`: Mathlib's `Sheaf.H'` over `U` is the `n`-th right
   derived functor of sections over `U`. Sections over `U` are corepresented by the
   sheafification of the free abelian presheaf on `yoneda.obj U`
   (`ModuleSheafCohomology.evaluationRepresentation`), and that sheafification is exactly the
   object Mathlib takes `Ext` out of; so this is
   `ModuleSheafCohomology.extFunctorObjIsoRightDerived`, which is constructed and not chosen.
   Its compatibility with restriction is
   `ModuleSheafCohomology.extFunctorObjIsoRightDerived_naturality`, whose hypothesis is
   `Stacks.Cohomology.ModuleComparison.evaluationRepresentation_naturality`. The restriction map
   on `Sheaf.cohomologyPresheaf` *is* precomposition with the induced map of corepresenting
   objects, which is `cohomologyPresheaf_map_eq_extPrecomp` and holds by definition.
2. `Hrestrict_comp_sectionsComparisonIso`: [Stacks, Tag 03FD] over an open, as the named
   comparison `ModuleSheafCohomology.sectionsComparisonIso`, commutes with restriction. This is
   `Stacks.Cohomology.ModuleComparison.sectionsComparisonIso_naturality`.
3. `rightDerivedForgetCohomologyIso_app_naturality_open`: [Stacks, Tag 01ER] identifies the
   derived presheaf of the forgetful inclusion `Mod(O_X) ⟶ PMod(O_X)` with `U ↦ H^n(U, -)`
   compatibly with restriction between opens. This is
   `Stacks.Cohomology.DerivedForget.rightDerivedForgetCohomologyIso_naturality_open`.
4. `Stacks.Cohomology.DerivedForget.rightDerivedForgetEvaluationIso` identifies the value of that
   derived presheaf on `U` with the right derived functor of module-valued sections over `U`,
   `O_X(U)`-linearly, which is the object `cohomologyOverField` restricts scalars on.

Step 3 is where the `k`-linearity comes from: the restriction map lives in the derived presheaf
of *modules*, so it is semilinear along `Γ(X, ⊤) ⟶ Γ(X, U)`, and the two structure maps
`k ⟶ Γ(X, ⊤)` and `k ⟶ Γ(X, U)` differ by exactly that restriction
(`structureRingHom_comp`). Restricting scalars therefore turns it into a `k`-linear map.

## Main definitions

* `AlgebraicGeometry.cohomologyOverFieldOnOpen`: `H^n(U, ℱ)` as a `k`-vector space, for `U` an
  open of a scheme over `k`. At `U = ⊤` it is `AlgebraicGeometry.cohomologyOverField` on the
  nose (`AlgebraicGeometry.cohomologyOverFieldOnOpen_top`).
* `AlgebraicGeometry.cohomologyOverFieldRestrict`: the `k`-linear restriction map
  `H^n(X, ℱ) ⟶ H^n(U, ℱ)`.

## Main results

* `cohomologyPresheaf_map_comp_cohomologyPresheafIsoRightDerivedSections`, in the namespace
  `Stacks.Cohomology.ExtSections`: the comparison of Mathlib's `Ext`-model with right derived
  sections is compatible with restriction along any morphism of the site. This is the reusable
  core of the file.
* `Stacks.Cohomology.ExtSections.surjective_rightDerived_sectionsRestriction`,
  `.surjective_Hrestrict`, `.surjective_derivedForgetPresheaf_map`: the same surjectivity carried
  successively to right derived sections of abelian sheaves, to the module-valued `Hrestrict` of
  [Stacks, Tag 01E2], and to the derived presheaf of [Stacks, Tag 01ER].
* `AlgebraicGeometry.surjective_cohomologyOverFieldRestrict`: the `k`-linear restriction is
  surjective whenever the restriction on Mathlib's cohomology presheaf is.
* `AlgebraicGeometry.surjective_cohomologyOverFieldRestrict_of_topologicalKrullDim_le` and
  `AlgebraicGeometry.surjective_cohomologyOverFieldRestrict_of_finiteType`: the two together are
  clause (2) of [Stacks, Tag 0A3G] in the `cohomologyOverField` spelling, for a spectral space
  and for a scheme of finite type over `k` respectively. No coherence or quasi-coherence of `ℱ`
  is needed: clause (2) is a statement about an arbitrary abelian sheaf.

## Implementation notes

**No tag attribute is attached anywhere in this file.** Clause (2) of [Stacks, Tag 0A3G] is
already tagged on
`Stacks.CohomologyVanishing.surjective_cohomologyPresheaf_map_top_of_topologicalKrullDim_le`;
what is proved here is the same mathematics read through a different model of cohomology, which
is infrastructure for the consumers of `cohomologyOverField` rather than a further clause of the
tag.

**The hypotheses are those of clause (2) as formalized.** `topologicalKrullDim X ≤ d` is the
dimension hypothesis of
`Stacks.CohomologyVanishing.surjective_cohomologyPresheaf_map_top_of_topologicalKrullDim_le`,
which is weaker than the source's equality, and the spectral-space hypothesis is the hypothesis of
the tag. The finite-type version derives spectrality: a scheme quasi-compact and locally of finite
type over a field is noetherian, hence quasi-separated, and every scheme is `T0`, sober and
prespectral.

## References

* [Stacks Project, Tag 01E2](https://stacks.math.columbia.edu/tag/01E2)
* [Stacks Project, Tag 01ER](https://stacks.math.columbia.edu/tag/01ER)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 0A3G](https://stacks.math.columbia.edu/tag/0A3G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Cohomology.ExtSections

open CategoryTheory.Abelian ModuleSheafCohomology Stacks.Cohomology.ModuleComparison

/-! ### Transfer of surjectivity across a commuting square of abelian groups -/

/-- If a square of abelian groups commutes and its two vertical maps are isomorphisms, then one
horizontal map is surjective if and only if the other is. -/
private theorem surjective_iff_of_square {A B A' B' : AddCommGrpCat.{u}}
    {a : A ⟶ B} {a' : A' ⟶ B'} {eA : A ≅ A'} {eB : B ≅ B'}
    (hsq : a ≫ eB.hom = eA.hom ≫ a') : Function.Surjective a ↔ Function.Surjective a' := by
  have h : (eB.hom ∘ a) = a' ∘ eA.hom := funext fun x => ConcreteCategory.congr_hom hsq x
  rw [← Function.Surjective.of_comp_iff' (ConcreteCategory.bijective_of_isIso eB.hom) a, h,
    Function.Surjective.of_comp_iff _ (ConcreteCategory.bijective_of_isIso eA.hom).2]

/-! ### The comparison on a general small site -/

section Site

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{u}] [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
  [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{u})]

/-- The functor of sections over `U` on sheaves of abelian groups is additive. -/
local instance sheafSectionsSite_additive' (U : C) :
    ((sheafSections J AddCommGrpCat.{u}).obj (op U)).Additive where
  map_add := by intros; rfl

/-- The functor of sections over `U` on sheaves of abelian groups preserves finite limits. -/
local instance sheafSectionsSite_preservesFiniteLimits' (U : C) :
    PreservesFiniteLimits ((sheafSections J AddCommGrpCat.{u}).obj (op U)) :=
  preservesFiniteLimits_of_natIso (sheafSectionsNatIsoEvaluation J AddCommGrpCat.{u}).symm

/-- **Mathlib's sheaf cohomology over an object of the site is right derived sections, with no
choice made.** Sections over `U` are corepresented by the sheafification of the free abelian
presheaf on `yoneda.obj U`, and that sheafification is the object out of which Mathlib's
`CategoryTheory.Sheaf.cohomologyPresheaf` takes `Ext`; so the comparison is an instance of
`ModuleSheafCohomology.extFunctorObjIsoRightDerived`, which is built from the corepresentation
rather than chosen from an existence statement. That is what makes
`cohomologyPresheaf_map_comp_cohomologyPresheafIsoRightDerivedSections` a provable statement. -/
def cohomologyPresheafIsoRightDerivedSections (U : C) (n : ℕ) :
    extFunctorObj ((presheafToSheaf J AddCommGrpCat.{u}).obj
        (yoneda.obj U ⋙ AddCommGrpCat.free)) n ≅
      ((sheafSections J AddCommGrpCat.{u}).obj (op U)).rightDerived n :=
  extFunctorObjIsoRightDerived ((sheafSections J AddCommGrpCat.{u}).obj (op U)) _
    (evaluationRepresentation J U) n

omit [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{u})] in
/-- The restriction map of `CategoryTheory.Sheaf.cohomologyPresheaf` along `g : U ⟶ V` is
precomposition, in the first `Ext` variable, with the induced map `freeYonedaSheafMap` of the
objects corepresenting sections. Both sides are `(extFunctor n).map` of the same morphism, so
this holds by definition. -/
lemma cohomologyPresheaf_map_eq_extPrecomp {U V : C} (g : U ⟶ V) (n : ℕ)
    (F : Sheaf J AddCommGrpCat.{u}) :
    (F.cohomologyPresheaf n).map g.op = (extPrecomp (freeYonedaSheafMap J g) n).app F := rfl

/-- **The comparison of Mathlib's `Ext`-model with right derived sections is compatible with
restriction.** For `g : U ⟶ V` the restriction map on `Sheaf.cohomologyPresheaf` and the map that
`NatTrans.rightDerived` induces from restriction of sections agree under
`cohomologyPresheafIsoRightDerivedSections`, in every degree.

The restriction map upstairs is precomposition with `freeYonedaSheafMap`
(`cohomologyPresheaf_map_eq_extPrecomp`), so this is
`ModuleSheafCohomology.extFunctorObjIsoRightDerived_naturality` — naturality of the comparison in
the corepresenting object — whose hypothesis that the corepresentations match restriction of
sections with that map is
`Stacks.Cohomology.ModuleComparison.evaluationRepresentation_naturality`. -/
theorem cohomologyPresheaf_map_comp_cohomologyPresheafIsoRightDerivedSections
    {U V : C} (g : U ⟶ V) (n : ℕ) (F : Sheaf J AddCommGrpCat.{u}) :
    (F.cohomologyPresheaf n).map g.op ≫
        ((cohomologyPresheafIsoRightDerivedSections J U n).app F).hom =
      ((cohomologyPresheafIsoRightDerivedSections J V n).app F).hom ≫
        (NatTrans.rightDerived (sectionsRestriction J g) n).app F := by
  rw [cohomologyPresheaf_map_eq_extPrecomp]
  exact NatTrans.congr_app
    (extFunctorObjIsoRightDerived_naturality (freeYonedaSheafMap J g)
      (evaluationRepresentation J U) (evaluationRepresentation J V)
      (sectionsRestriction J g) (evaluationRepresentation_naturality J g) n) F

/-- Surjectivity of restriction on Mathlib's cohomology presheaf gives surjectivity of the
restriction map on right derived sections. -/
theorem surjective_rightDerived_sectionsRestriction
    {U V : C} (g : U ⟶ V) (n : ℕ) (F : Sheaf J AddCommGrpCat.{u})
    (hsurj : Function.Surjective ((F.cohomologyPresheaf n).map g.op)) :
    Function.Surjective ((NatTrans.rightDerived (sectionsRestriction J g) n).app F) :=
  (surjective_iff_of_square
    (cohomologyPresheaf_map_comp_cohomologyPresheafIsoRightDerivedSections J g n F)).1 hsurj

end Site

/-! ### Descent to module-valued cohomology on a space -/

section Space

variable {X : Type u} [TopologicalSpace X]
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- The restriction map `Hrestrict` on module-valued cohomology over an open and the restriction
map on right derived sections of the underlying abelian sheaf agree under the comparison of
[Stacks, Tag 03FD]. This is
`Stacks.Cohomology.ModuleComparison.sectionsComparisonIso_naturality` read at a single sheaf of
modules. -/
theorem Hrestrict_comp_sectionsComparisonIso {U V : Opens X} (h : U ≤ V) (n : ℕ)
    (F : SheafOfModules.{u} R) :
    Hrestrict R h n F ≫
        ((sectionsComparisonIso (Opens.grothendieckTopology X) R U n).app F).hom =
      ((sectionsComparisonIso (Opens.grothendieckTopology X) R V n).app F).hom ≫
        (NatTrans.rightDerived
          (sectionsRestriction (Opens.grothendieckTopology X) (homOfLE h)) n).app
            ((SheafOfModules.toSheaf R).obj F) :=
  NatTrans.congr_app
    (sectionsComparisonIso_naturality (Opens.grothendieckTopology X) R (homOfLE h) n) F

/-- Surjectivity of restriction on Mathlib's cohomology presheaf of the underlying abelian sheaf
gives surjectivity of `Hrestrict`, the restriction map on the cohomology of a sheaf of modules
over an open. -/
theorem surjective_Hrestrict {U V : Opens X} (h : U ≤ V) (n : ℕ) (F : SheafOfModules.{u} R)
    (hsurj : Function.Surjective
      ((((SheafOfModules.toSheaf R).obj F).cohomologyPresheaf n).map (homOfLE h).op)) :
    Function.Surjective (Hrestrict R h n F) :=
  (surjective_iff_of_square (Hrestrict_comp_sectionsComparisonIso R h n F)).2
    (surjective_rightDerived_sectionsRestriction (Opens.grothendieckTopology X)
      (homOfLE h) n ((SheafOfModules.toSheaf R).obj F) hsurj)

/-- The restriction clause of [Stacks, Tag 01ER], with the comparison read as an isomorphism of
objects rather than of functors. -/
theorem rightDerivedForgetCohomologyIso_app_naturality_open {U V : Opens X} (h : U ≤ V) (n : ℕ)
    (F : SheafOfModules.{u} R) :
    ((PresheafOfModules.toPresheaf R.obj).obj
          (((SheafOfModules.forget R).rightDerived n).obj F)).map (homOfLE h).op ≫
        ((Stacks.Cohomology.DerivedForget.rightDerivedForgetCohomologyIso R U n).app F).hom =
      ((Stacks.Cohomology.DerivedForget.rightDerivedForgetCohomologyIso R V n).app F).hom ≫
        Hrestrict R h n F :=
  Stacks.Cohomology.DerivedForget.rightDerivedForgetCohomologyIso_naturality_open R h n F

/-- Surjectivity of restriction on Mathlib's cohomology presheaf gives surjectivity of the
restriction map of the presheaf `R^n ι(ℱ)`, the `n`-th right derived functor of the inclusion of
sheaves of modules into presheaves of modules. This is the form the `k`-linear statement
consumes: the restriction there is a map of modules over the two section rings. -/
theorem surjective_derivedForgetPresheaf_map {U V : Opens X} (h : U ≤ V) (n : ℕ)
    (F : SheafOfModules.{u} R)
    (hsurj : Function.Surjective
      ((((SheafOfModules.toSheaf R).obj F).cohomologyPresheaf n).map (homOfLE h).op)) :
    Function.Surjective
      (((PresheafOfModules.toPresheaf R.obj).obj
        (((SheafOfModules.forget R).rightDerived n).obj F)).map (homOfLE h).op) :=
  (surjective_iff_of_square
    (rightDerivedForgetCohomologyIso_app_naturality_open R h n F)).2
    (surjective_Hrestrict R h n F hsurj)

end Space

end Stacks.Cohomology.ExtSections

/-! ### The `k`-linear statement on a scheme over a field -/

namespace AlgebraicGeometry

open Stacks.Cohomology.ExtSections

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The cohomology `H^n(U, ℱ)` of a module on a scheme over `k`, as a `k`-vector space.** It is
the `n`-th right derived functor of sections over `U` in the category of `O_X`-modules, with the
`k`-action obtained by restricting scalars along the structure map `k ⟶ Γ(X, U)`. At `U = ⊤` this
is `AlgebraicGeometry.cohomologyOverField`. -/
def cohomologyOverFieldOnOpen (U : X.Opens) (F : X.Modules) (n : ℕ) : ModuleCat.{u} k :=
  (ModuleCat.restrictScalars
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U (by simp)).hom).obj
    (((SheafOfModules.evaluation X.ringCatSheaf (op U)).rightDerived n).obj F)

/-- Over the whole scheme, `cohomologyOverFieldOnOpen` is `cohomologyOverField`. -/
lemma cohomologyOverFieldOnOpen_top (F : X.Modules) (n : ℕ) :
    cohomologyOverFieldOnOpen k f ⊤ F n = cohomologyOverField k f F n := rfl

/-- The structure map `k ⟶ Γ(X, U)` is the structure map `k ⟶ Γ(X, ⊤)` followed by restriction
of sections. This is `AlgebraicGeometry.Scheme.Hom.appLE_map`, and it is what makes the
semilinear restriction map on the derived presheaf of modules `k`-linear. -/
lemma structureRingHom_comp (U : X.Opens) :
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U (by simp)).hom =
      RingHom.comp (X.ringCatSheaf.obj.map
          (homOfLE (show U ≤ (⊤ : X.Opens) from le_top)).op).hom
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom := by
  have hmor : (Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U (by simp) =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)) ≫
        X.presheaf.map (homOfLE (show U ≤ (⊤ : X.Opens) from le_top)).op := by
    rw [Category.assoc]
    congr 1
    exact (Scheme.Hom.appLE_map f _ _).symm
  rw [hmor]
  rfl

/-- **The `k`-linear restriction map `H^n(X, ℱ) ⟶ H^n(U, ℱ)`.** Underneath it is the restriction
map of the presheaf `R^n ι(ℱ)` of [Stacks, Tag 01ER]; the two outer isomorphisms are
`Stacks.Cohomology.DerivedForget.rightDerivedForgetEvaluationIso`, which identifies the value of
that presheaf on an open with the right derived functor of module-valued sections there, and the
middle one is `ModuleCat.restrictScalarsComp'` applied to `structureRingHom_comp`, which is where
`k`-linearity enters. -/
def cohomologyOverFieldRestrict (U : X.Opens) (F : X.Modules) (n : ℕ) :
    cohomologyOverField k f F n ⟶ cohomologyOverFieldOnOpen k f U F n :=
  ((ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom).mapIso
        ((Stacks.Cohomology.DerivedForget.rightDerivedForgetEvaluationIso
          X.ringCatSheaf ⊤ n).app F)).inv ≫
    (ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom).map
      ((((SheafOfModules.forget X.ringCatSheaf).rightDerived n).obj F).map
        (homOfLE (show U ≤ (⊤ : X.Opens) from le_top)).op) ≫
    ((ModuleCat.restrictScalarsComp'
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom
        (X.ringCatSheaf.obj.map
          (homOfLE (show U ≤ (⊤ : X.Opens) from le_top)).op).hom
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U (by simp)).hom
        (structureRingHom_comp k f U)).app
      ((((SheafOfModules.forget X.ringCatSheaf).rightDerived n).obj F).obj (op U))).inv ≫
    ((ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U (by simp)).hom).mapIso
        ((Stacks.Cohomology.DerivedForget.rightDerivedForgetEvaluationIso
          X.ringCatSheaf U n).app F)).hom

/-- A composite of surjective maps of `k`-modules is surjective. -/
private theorem surjective_comp_moduleCat {A B C : ModuleCat.{u} k} (a : A ⟶ B) (b : B ⟶ C)
    (ha : Function.Surjective a) (hb : Function.Surjective b) :
    Function.Surjective (a ≫ b) := hb.comp ha

/-- **The transport.** If restriction to `U` is surjective on Mathlib's degree-`n` cohomology
presheaf of the underlying abelian sheaf of `ℱ`, then the `k`-linear restriction map
`cohomologyOverFieldRestrict` is surjective. Three of its four factors are isomorphisms, and the
remaining one is the restriction map of the derived presheaf of [Stacks, Tag 01ER], handled by
`Stacks.Cohomology.ExtSections.surjective_derivedForgetPresheaf_map`. -/
theorem surjective_cohomologyOverFieldRestrict (U : X.Opens) (F : X.Modules) (n : ℕ)
    (hsurj : Function.Surjective
      ((((SheafOfModules.toSheaf X.ringCatSheaf).obj F).cohomologyPresheaf n).map
        (homOfLE (show U ≤ (⊤ : X.Opens) from le_top)).op)) :
    Function.Surjective (cohomologyOverFieldRestrict k f U F n) := by
  have hP : Function.Surjective
      ((ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom).map
        ((((SheafOfModules.forget X.ringCatSheaf).rightDerived n).obj F).map
          (homOfLE (show U ≤ (⊤ : X.Opens) from le_top)).op)) :=
    surjective_derivedForgetPresheaf_map X.ringCatSheaf
      (show U ≤ (⊤ : X.Opens) from le_top) n F hsurj
  have hi {A B : ModuleCat.{u} k} (e : A ≅ B) :
      Function.Surjective e.hom ∧ Function.Surjective e.inv :=
    ⟨(ConcreteCategory.bijective_of_isIso e.hom).2, (ConcreteCategory.bijective_of_isIso e.inv).2⟩
  exact surjective_comp_moduleCat k _ _ (hi _).2
    (surjective_comp_moduleCat k _ _ hP (surjective_comp_moduleCat k _ _ (hi _).2 (hi _).1))

/-- **Clause (2) of [Stacks, Tag 0A3G] in the `cohomologyOverField` spelling.** Let `X` be a
scheme over a field `k` whose underlying space is spectral of Krull dimension at most `d`, let
`ℱ` be any `O_X`-module and let `U ⊆ X` be a quasi-compact open. Then the `k`-linear restriction
map `H^d(X, ℱ) → H^d(U, ℱ)` is surjective.

The surjectivity input is
`Stacks.CohomologyVanishing.surjective_cohomologyPresheaf_map_top_of_topologicalKrullDim_le`,
read at the underlying abelian sheaf of `ℱ`; nothing is assumed beyond its hypotheses. -/
theorem surjective_cohomologyOverFieldRestrict_of_topologicalKrullDim_le
    [SpectralSpace (X : Type u)] (F : X.Modules) (d : ℕ)
    (hdim : topologicalKrullDim (X : Type u) ≤ (d : WithBot ℕ∞))
    (U : X.Opens) (hU : IsCompact (U : Set X)) :
    Function.Surjective (cohomologyOverFieldRestrict k f U F d) :=
  surjective_cohomologyOverFieldRestrict k f U F d
    (Stacks.CohomologyVanishing.surjective_cohomologyPresheaf_map_top_of_topologicalKrullDim_le
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) d hdim U hU)

/-- **Clause (2) of [Stacks, Tag 0A3G] for a scheme of finite type over a field.** The spectral
hypothesis of `surjective_cohomologyOverFieldRestrict_of_topologicalKrullDim_le` is discharged:
such an `X` is locally noetherian by `AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`,
hence quasi-separated, it is compact because `f` is quasi-compact, and every scheme is `T0`,
sober and prespectral. -/
theorem surjective_cohomologyOverFieldRestrict_of_finiteType
    [LocallyOfFiniteType f] [QuasiCompact f] (F : X.Modules) (d : ℕ)
    (hdim : topologicalKrullDim (X : Type u) ≤ (d : WithBot ℕ∞))
    (U : X.Opens) (hU : IsCompact (U : Set X)) :
    Function.Surjective (cohomologyOverFieldRestrict k f U F d) := by
  have : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : SpectralSpace (X : Type u) := by constructor
  exact surjective_cohomologyOverFieldRestrict_of_topologicalKrullDim_le k f F d hdim U hU

end AlgebraicGeometry

end
