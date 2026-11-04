module

public import Mathlib.CategoryTheory.Monad.Limits
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.HullCoherentReflexive
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.KernelCokernel
public import StacksFrontier.AlgebraicGeometry.ReflexiveHullAdjunction.Basic

/-!
# The category of coherent reflexive modules

Let `X` be an integral locally Noetherian scheme. The reflexive hull `F^∨∨` of a coherent
`𝒪_X`-module is again coherent and reflexive, so the hull is a reflection of the coherent modules
onto the full subcategory `𝒞` of coherent reflexive modules: taking reflexive hulls is a left
adjoint of the inclusion `𝒞 ⟶ Coh(𝒪_X)`, with the canonical map `F ⟶ F^∨∨` as its unit.

The category `𝒞` has finite biproducts, so it is an additive category.

## Main definitions

* `hullReflection`: the reflexive hull, as a functor from coherent modules to coherent reflexive
  modules.
* `hullReflectionAdjunction`: the adjunction `hullReflection X ⊣ inclusion X`.

## Main results

* `coherentModules_abelian`: the coherent modules on a scheme form an abelian category.
* `hullReflectionAdjunction_unit_app_hom`: the unit of the adjunction is the canonical map to the
  double dual.
* `hullReflectionAdjunction_homEquiv_apply`: the hom bijection is precomposition with that
  canonical map.
* `coherentReflexiveModules_hasFiniteBiproducts`: the coherent reflexive modules form an additive
  category.

## References

* [Stacks Project, Tag 0EBH](https://stacks.math.columbia.edu/tag/0EBH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveEquivalence (isCoherent_doubleDual)
open Stacks.AlgebraicGeometry.ReflexiveModules (toDoubleDual reflexiveHull)
open Stacks.AlgebraicGeometry.ReflexiveHull (CoherentModules CoherentReflexiveModules
  reflexiveProperty inclusion hullFunctor hullUnit hullUnit_app_hom hullAdjunction)

universe u

namespace AlgebraicGeometry

/-- Coherence of sheaves of modules on a scheme is a weak Serre class. -/
instance isWeakSerreClass_isCoherent (X : Scheme.{u}) :
    ObjectProperty.IsWeakSerreClass
      (fun M : SheafOfModules.{u} (structureSheaf X.sheaf) => M.IsCoherent) :=
  SheafOfModules.coherentModules_isWeakSerreClass

/-- Coherence of objects of `X.Modules` is a weak Serre class. -/
instance isWeakSerreClass_isCoherent_modules (X : Scheme.{u}) :
    ObjectProperty.IsWeakSerreClass (fun M : X.Modules => M.IsCoherent) :=
  SheafOfModules.coherentModules_isWeakSerreClass

/-- The coherent modules on a scheme form an abelian category. -/
noncomputable instance coherentModules_abelian (X : Scheme.{u}) :
    Abelian (CoherentModules X) :=
  (ObjectProperty.abelian_of_isWeakSerreClass
    (fun M : SheafOfModules.{u} (structureSheaf X.sheaf) => M.IsCoherent)).some

variable (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]

/-- On an integral locally Noetherian scheme, the reflexive hull `F ↦ F^∨∨` as a functor from
coherent modules to coherent reflexive modules. -/
noncomputable abbrev hullReflection : CoherentModules X ⥤ CoherentReflexiveModules X :=
  (reflexiveProperty X).lift
    (hullFunctor X fun F hF => have := hF; isCoherent_doubleDual F)
    fun F => have := F.property; isReflexive_reflexiveHull X F.obj

/-- On an integral locally Noetherian scheme, taking reflexive hulls is a left adjoint of the
inclusion of the coherent reflexive modules into the coherent modules. -/
@[stacks 0EBH "adjunction"]
noncomputable def hullReflectionAdjunction : hullReflection X ⊣ inclusion X :=
  hullAdjunction X (fun F hF => have := hF; isCoherent_doubleDual F)
    fun F hF => have := hF; isReflexive_reflexiveHull X F

/-- The reflection sends a coherent module to its reflexive hull. -/
theorem hullReflection_obj_obj_obj (F : CoherentModules X) :
    ((hullReflection X).obj F).obj.obj = reflexiveHull F.obj :=
  rfl

/-- The unit of the reflection is the canonical map to the double dual. -/
theorem hullReflectionAdjunction_unit_app_hom (F : CoherentModules X) :
    ((hullReflectionAdjunction X).unit.app F).hom = toDoubleDual F.obj :=
  have h := Stacks.CategoryTheory.reflectionAdjunction_unit_app (reflexiveProperty X)
    (hullFunctor X fun F hF => have := hF; isCoherent_doubleDual F)
    (hullUnit X _) _ _ _ F
  (congrArg (fun k : F ⟶ _ => k.hom) h).trans (hullUnit_app_hom X _ F)

/-- The hom bijection of the reflection is precomposition with the canonical map to the double
dual. -/
theorem hullReflectionAdjunction_homEquiv_apply (F : CoherentModules X)
    (G : CoherentReflexiveModules X) (φ : (hullReflection X).obj F ⟶ G) :
    ((hullReflectionAdjunction X).homEquiv F G φ).hom = toDoubleDual F.obj ≫ φ.hom.hom := by
  rw [Adjunction.homEquiv_unit, ObjectProperty.FullSubcategory.comp_hom,
    hullReflectionAdjunction_unit_app_hom]
  rfl

/-- The reflection of a morphism of coherent modules is its double dual. -/
theorem hullReflection_map_hom_hom {S S' : CoherentModules X} (u : S ⟶ S') :
    ((hullReflection X).map u).hom.hom =
      (Stacks.AlgebraicGeometry.ReflexiveModules.reflexiveHullFunctor X).map u.hom :=
  rfl

/-- The inclusion of the coherent reflexive modules into the coherent modules is reflective. -/
noncomputable instance reflective_inclusion : Reflective (inclusion X) where
  L := hullReflection X
  adj := hullReflectionAdjunction X

/-- The coherent reflexive modules on an integral locally Noetherian scheme form an additive
category: they have finite direct sums. -/
@[stacks 0EBH "additive"]
noncomputable instance coherentReflexiveModules_hasFiniteBiproducts :
    HasFiniteBiproducts (CoherentReflexiveModules X) :=
  have : HasFiniteColimits (CoherentReflexiveModules X) :=
    ⟨fun J _ _ =>
      have := (inferInstance : HasFiniteColimits (CoherentModules X)).out J
      hasColimitsOfShape_of_reflective (inclusion X)⟩
  HasFiniteBiproducts.of_hasFiniteCoproducts

end AlgebraicGeometry

end
