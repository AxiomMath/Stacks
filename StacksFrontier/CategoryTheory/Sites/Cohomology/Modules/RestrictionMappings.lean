module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EvaluationConservative
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcomposeNaturality
import StacksCore.Tactic.StacksAttribute

/-!
# Restriction mappings on the cohomology of sheaves of modules on a ringed site

Let `(C, O)` be a ringed site, let `ℱ` be a sheaf of `O`-modules and let `f : U ⟶ V` be a
morphism of `C`. The cohomology `Hⁿ(U, ℱ)` is the `n`-th right derived functor of the sections
functor `Γ(U, -) : Mod(O) ⥤ Mod(O(U))`. There is a canonical restriction mapping

`Hⁿ(V, ℱ) ⟶ Hⁿ(U, ℱ), ξ ↦ ξ|_U`,

functorial in `ℱ`: choosing an injective resolution `ℱ ⟶ I^•`, the restriction maps of the
sheaves `I^p` form a morphism of complexes `Γ(V, I^•) ⟶ Γ(U, I^•)`, and the restriction mapping
is the map it induces on `Hⁿ`. It is `O(V)`-linear, `Hⁿ(U, ℱ)` being an `O(V)`-module through
`O(V) ⟶ O(U)`.

Thus `U ↦ Hⁿ(U, ℱ)` is a presheaf of `O`-modules, the presheaf `H̲ⁿ(ℱ)`. Here it is the `n`-th
right derived functor of the inclusion `Mod(O) ⥤ PMod(O)`, applied to `ℱ`; its value at `U` is
identified with `Hⁿ(U, ℱ)`, naturally in `ℱ`, and under this identification its restriction
maps are the restriction mappings above.

## Main definitions

* `Stacks.Cohomology.SiteModules.sectionsRestriction`: the restriction maps of sections
  `Γ(V, ℱ) ⟶ Γ(U, ℱ)`, natural in `ℱ`.
* `Stacks.Cohomology.SiteModules.cohomologyRestriction`: the restriction mapping
  `Hⁿ(V, ℱ) ⟶ Hⁿ(U, ℱ)`, natural in `ℱ`.
* `Stacks.Cohomology.SiteModules.cohomologyPresheafFunctor`: the functor `ℱ ↦ H̲ⁿ(ℱ)` from
  sheaves of `O`-modules to presheaves of `O`-modules.
* `Stacks.Cohomology.SiteModules.cohomologyPresheafEvaluationIso`: the identification of the
  value of `H̲ⁿ(ℱ)` at `U` with `Hⁿ(U, ℱ)`.

## Main results

* `Stacks.Cohomology.SiteModules.cohomologyRestriction_app_eq`: the restriction mapping is
  computed by the restriction maps of an arbitrary injective resolution.
* `Stacks.Cohomology.SiteModules.cohomologyPresheaf_map`: the restriction maps of `H̲ⁿ(ℱ)` are
  the restriction mappings.

## References

* [Stacks Project, Tag 01FV](https://stacks.math.columbia.edu/tag/01FV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₁ u₁ v u

namespace Stacks.Cohomology.SiteModules

/-- Restriction of scalars between categories of modules is exact. -/
local instance restrictScalars_preservesHomology {R S : Type u} [Ring R] [Ring S] (f : R →+* S) :
    (ModuleCat.restrictScalars.{v} f).PreservesHomology where
  preservesKernels _ := inferInstance
  preservesCokernels _ := inferInstance

/-- For exact functors `E` and `E'`, the isomorphism `Rⁿ(F ⋙ E ⋙ E') ≅ RⁿF ⋙ E ⋙ E'` is the
isomorphism `Rⁿ((F ⋙ E) ⋙ E') ≅ Rⁿ(F ⋙ E) ⋙ E'` followed by `E'` applied to `Rⁿ(F ⋙ E) ≅ RⁿF ⋙ E`.
-/
private theorem rightDerivedCompIso_hom_app_comp {A : Type*} [Category* A] [Abelian A]
    [HasInjectiveResolutions A] {B : Type*} [Category* B] [Abelian B] {B' : Type*}
    [Category* B'] [Abelian B'] {B'' : Type*} [Category* B''] [Abelian B'']
    (F : A ⥤ B) [F.Additive] (E : B ⥤ B') [E.Additive] [E.PreservesHomology]
    (E' : B' ⥤ B'') [E'.Additive] [E'.PreservesHomology] [(E ⋙ E').PreservesHomology]
    (n : ℕ) (X : A) :
    (F.rightDerivedCompIso (E ⋙ E') n).hom.app X =
      ((F ⋙ E).rightDerivedCompIso E' n).hom.app X ≫
        E'.map ((F.rightDerivedCompIso E n).hom.app X) := by
  have h := Functor.rightDerivedCompIsoOfPreservesLeftHomology_hom_app_comp (𝟭 A) F E E' n
    (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) X
  simp only [Functor.rightDerivedCompIsoOfPreservesLeftHomology_eq_rightDerivedCompIso,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.whiskerLeft_app, Functor.id_obj] at h
  rw [← cancel_epi ((F.rightDerivedCompIso (E ⋙ E') n).inv.app X)]
  conv_rhs => rw [← h]
  simp [← Functor.map_comp]

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} (O : Sheaf J RingCat.{u})

/-- The restriction maps `Γ(V, ℱ) ⟶ Γ(U, ℱ)` of sheaves of `O`-modules along a morphism
`f : U ⟶ V` of the site, as a natural transformation of functors to `O(V)`-modules, the
sections over `U` being an `O(V)`-module through `O(V) ⟶ O(U)`. -/
def sectionsRestriction {U V : C} (f : U ⟶ V) :
    SheafOfModules.evaluation.{v} O (op V) ⟶
      SheafOfModules.evaluation.{v} O (op U) ⋙ ModuleCat.restrictScalars (O.obj.map f.op).hom :=
  Functor.whiskerLeft (SheafOfModules.forget O) (PresheafOfModules.restriction O.obj f.op)

variable [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [HasInjectiveResolutions (SheafOfModules.{v} O)]

/-- The restriction mapping `Hⁿ(V, ℱ) ⟶ Hⁿ(U, ℱ)`, `ξ ↦ ξ|_U`, along a morphism `f : U ⟶ V` of the
site, natural in the sheaf of `O`-modules `ℱ`. It is the map induced on cohomology by the
restriction of sections, and it is `O(V)`-linear for the `O(V)`-module structure on `Hⁿ(U, ℱ)`
through `O(V) ⟶ O(U)`. -/
@[stacks 01FV "restriction mapping"]
def cohomologyRestriction (n : ℕ) {U V : C} (f : U ⟶ V) :
    (SheafOfModules.evaluation.{v} O (op V)).rightDerived n ⟶
      (SheafOfModules.evaluation.{v} O (op U)).rightDerived n ⋙
        ModuleCat.restrictScalars (O.obj.map f.op).hom :=
  NatTrans.rightDerived (sectionsRestriction O f) n ≫
    ((SheafOfModules.evaluation O (op U)).rightDerivedCompIso _ n).hom

/-- The restriction mapping is computed from any injective resolution `ℱ ⟶ I^•`: it is the map
induced on `Hⁿ` by the morphism of complexes `Γ(V, I^•) ⟶ Γ(U, I^•)` given by the restriction maps
of the sheaves `I^p`, followed by the identification of `Hⁿ` of the restriction of scalars of
`Γ(U, I^•)` with the restriction of scalars of `Hⁿ(U, ℱ)`. -/
@[stacks 01FV "computed by an injective resolution"]
theorem cohomologyRestriction_app_eq (n : ℕ) {U V : C} (f : U ⟶ V)
    {F : SheafOfModules.{v} O} (I : InjectiveResolution F) :
    (cohomologyRestriction O n f).app F =
      ((I.isoRightDerivedObj (SheafOfModules.evaluation O (op V)) n).hom ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex (sectionsRestriction O f) _).app I.cocomplex) n ≫
        (I.isoRightDerivedObj (SheafOfModules.evaluation O (op U) ⋙
          ModuleCat.restrictScalars (O.obj.map f.op).hom) n).inv) ≫
      ((SheafOfModules.evaluation O (op U)).rightDerivedCompIso _ n).hom.app F := by
  rw [cohomologyRestriction, NatTrans.comp_app, InjectiveResolution.rightDerived_app_eq _ I]
  rfl

/-- The functor sending a sheaf of `O`-modules `ℱ` to the presheaf of `O`-modules
`H̲ⁿ(ℱ) : U ↦ Hⁿ(U, ℱ)`, defined as the `n`-th right derived functor of the inclusion of sheaves of
`O`-modules into presheaves of `O`-modules. -/
@[stacks 01FV "presheaf of modules"]
def cohomologyPresheafFunctor (n : ℕ) : SheafOfModules.{v} O ⥤ PresheafOfModules.{v} O.obj :=
  (SheafOfModules.forget O).rightDerived n

/-- The presheaf of `O`-modules `H̲ⁿ(ℱ) : U ↦ Hⁿ(U, ℱ)` of a sheaf of `O`-modules `ℱ`. -/
abbrev cohomologyPresheaf (n : ℕ) (F : SheafOfModules.{v} O) : PresheafOfModules.{v} O.obj :=
  (cohomologyPresheafFunctor O n).obj F

/-- The value of the presheaf `H̲ⁿ(ℱ)` at an object `U` of the site is the cohomology `Hⁿ(U, ℱ)`,
as an `O(U)`-module and naturally in `ℱ`. -/
@[stacks 01FV "values of the presheaf"]
def cohomologyPresheafEvaluationIso (n : ℕ) (U : C) :
    (SheafOfModules.evaluation.{v} O (op U)).rightDerived n ≅
      cohomologyPresheafFunctor O n ⋙ PresheafOfModules.evaluation O.obj (op U) :=
  (SheafOfModules.forget O).rightDerivedCompIso (PresheafOfModules.evaluation O.obj (op U)) n

/-- Under the identification of its values with the cohomology modules, the restriction map of the
presheaf `H̲ⁿ(ℱ)` along `f : U ⟶ V` is the restriction mapping `Hⁿ(V, ℱ) ⟶ Hⁿ(U, ℱ)`. -/
@[stacks 01FV "restriction maps of the presheaf"]
theorem cohomologyPresheaf_map (n : ℕ) {U V : C} (f : U ⟶ V) (F : SheafOfModules.{v} O) :
    (cohomologyPresheafEvaluationIso O n V).hom.app F ≫ (cohomologyPresheaf O n F).map f.op =
      (cohomologyRestriction O n f).app F ≫
        (ModuleCat.restrictScalars (O.obj.map f.op).hom).map
          ((cohomologyPresheafEvaluationIso O n U).hom.app F) := by
  have : (PresheafOfModules.evaluation O.obj (op U) ⋙
      ModuleCat.restrictScalars (O.obj.map f.op).hom).PreservesHomology :=
    Functor.preservesHomology_of_map_exact _ fun _ hS ↦
      (hS.map (PresheafOfModules.evaluation O.obj (op U))).map
        (ModuleCat.restrictScalars (O.obj.map f.op).hom)
  have h := (SheafOfModules.forget O).rightDerivedCompIso_hom_naturality
    (PresheafOfModules.restriction O.obj f.op) n F
  rwa [rightDerivedCompIso_hom_app_comp] at h

end Stacks.Cohomology.SiteModules
