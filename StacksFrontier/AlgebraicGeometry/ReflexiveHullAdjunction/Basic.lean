module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import StacksFrontier.AlgebraicGeometry.Reflexive.DualMap
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.Hull
public import StacksFrontier.AlgebraicGeometry.ReflexiveHullAdjunction.Reflection
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation

/-!
# The reflexive-hull adjunction

Taking double duals is a left adjoint to the inclusion of the coherent reflexive modules into
the coherent modules, with the canonical map to the double dual as its unit.

The two geometric inputs, that the double dual of a coherent module is coherent and that it is
reflexive, are taken as hypotheses. From them one obtains the double-dual functor on coherent
modules, the triangle identity, and the identity `(j_F)^{∨∨} = j_{F^{∨∨}}`, which together give
the adjunction.

## Main definitions

* `hullFunctor`: The double-dual functor on coherent modules.
* `hullUnit`: The canonical map to the double dual, as a natural transformation.
* `hullAdjunction`: The double-dual functor is left adjoint to the inclusion of coherent
  reflexive modules into coherent modules.

## Main results

* `isCoherent_and_isReflexive_reflexiveHull_of_adjunction`: Such an adjunction forces the
  reflexive hull of a coherent module to be coherent and reflexive.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveHull

/-- Every inhabitant of the subtype
defining the canonical map to the reflexive hull has the same underlying morphism. -/
theorem toReflexiveHull_eq (X : Scheme.{u}) (F : X.Modules)
    (j : { j : F ⟶ reflexiveHull F //
      ∀ (U : X.Opens) (f : Γ(F, U)) (lam : Γ(dualSheaf F, U)),
        (((j.val.app (op U)).hom f).app (op (Over.mk (𝟙 U)))).hom lam =
          (lam.app (op (Over.mk (𝟙 U)))).hom f }) :
    j.1 = (toReflexiveHull F).1 :=
  eq_toDoubleDual_of_val_app_apply F j.1 j.2

/-- The category of coherent modules on a scheme. -/
abbrev CoherentModules (X : Scheme.{u}) :=
  ObjectProperty.FullSubcategory
    (C := SheafOfModules.{u} (structureSheaf X.sheaf)) (fun M => M.IsCoherent)

/-- Reflexivity, as a property of objects of the category of coherent modules. -/
abbrev reflexiveProperty (X : Scheme.{u}) : ObjectProperty (CoherentModules X) :=
  fun F => IsReflexive F.obj

/-- The category of coherent reflexive modules on a scheme. -/
abbrev CoherentReflexiveModules (X : Scheme.{u}) := (reflexiveProperty X).FullSubcategory

/-- Inclusion of coherent reflexive modules into coherent modules. -/
noncomputable abbrev inclusion (X : Scheme.{u}) :
    CoherentReflexiveModules X ⥤ CoherentModules X :=
  ObjectProperty.ι _

variable (X : Scheme.{u})
  (hcoh : ∀ F : X.Modules, F.IsCoherent → (reflexiveHull F).IsCoherent)

/-- The double-dual functor on coherent modules. -/
noncomputable def hullFunctor : CoherentModules X ⥤ CoherentModules X :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ reflexiveHullFunctor X)
    (fun F => hcoh F.obj F.property)

/-- The canonical map to the double dual, as a natural transformation of coherent modules. -/
noncomputable def hullUnit : 𝟭 (CoherentModules X) ⟶ hullFunctor X hcoh where
  app F := ObjectProperty.homMk (toDoubleDual F.obj)
  naturality _ _ u := ObjectProperty.hom_ext _ (toDoubleDual_naturality u.hom)

/-- The underlying morphism of the component of `hullUnit` at `F` is the canonical map
`toDoubleDual F.obj` to the double dual. -/
theorem hullUnit_app_hom (F : CoherentModules X) :
    ((hullUnit X hcoh).app F).hom = toDoubleDual F.obj :=
  rfl

/-- The component of `hullUnit` at a coherent module whose underlying module is reflexive is an
isomorphism. -/
theorem isIso_hullUnit_app (F : CoherentModules X) (h : IsReflexive F.obj) :
    IsIso ((hullUnit X hcoh).app F) := by
  have hiso : IsIso (toDoubleDual F.obj) := h
  obtain ⟨g, hg₁, hg₂⟩ := hiso.out
  exact ⟨ObjectProperty.homMk g, ObjectProperty.hom_ext _ hg₁, ObjectProperty.hom_ext _ hg₂⟩

/-- If the double dual of every coherent module is reflexive, then applying `hullFunctor` to the
component of `hullUnit` at `F` gives the component of `hullUnit` at `hullFunctor X hcoh F`, that
is, `(j_F)^{∨∨} = j_{F^{∨∨}}`. -/
theorem hullFunctor_map_hullUnit_app
    (href : ∀ F : X.Modules, F.IsCoherent → IsReflexive (reflexiveHull F))
    (F : CoherentModules X) :
    (hullFunctor X hcoh).map ((hullUnit X hcoh).app F) =
      (hullUnit X hcoh).app ((hullFunctor X hcoh).obj F) := by
  apply ObjectProperty.hom_ext
  have : IsIso (toDoubleDual (dualSheaf (dualSheaf F.obj))) := href F.obj F.property
  exact doubleDualMap_toDoubleDual F.obj

/-- The reflexive hull is a left adjoint of the inclusion of coherent reflexive modules. -/
noncomputable def hullAdjunction
    (href : ∀ F : X.Modules, F.IsCoherent → IsReflexive (reflexiveHull F)) :
    (reflexiveProperty X).lift (hullFunctor X hcoh)
        (fun F => href F.obj F.property) ⊣ inclusion X :=
  Stacks.CategoryTheory.reflectionAdjunction (reflexiveProperty X) (hullFunctor X hcoh)
    (hullUnit X hcoh) (fun F => href F.obj F.property)
    (fun F h => isIso_hullUnit_app X hcoh F h)
    (fun F => hullFunctor_map_hullUnit_app X hcoh href F)

/-- If the double dual of every coherent module is coherent and reflexive, then the double-dual
functor is left adjoint to the inclusion of coherent reflexive modules into coherent modules,
with unit given by the canonical map `toReflexiveHull` to the double dual. -/
noncomputable def reflexiveHullAdjunction
    (href : ∀ F : X.Modules, F.IsCoherent → IsReflexive (reflexiveHull F)) :
    { p : (Σ L : CoherentModules X ⥤ CoherentReflexiveModules X, L ⊣ inclusion X) //
      ∀ F : CoherentModules X,
        ∃ h : (p.1.obj F).obj.obj = reflexiveHull F.obj,
          (p.2.unit.app F).hom ≫ eqToHom h = (toReflexiveHull F.obj).1 } := by
  refine ⟨⟨_, hullAdjunction X hcoh href⟩, fun F => ⟨rfl, ?_⟩⟩
  have hunit := Stacks.CategoryTheory.reflectionAdjunction_unit_app (reflexiveProperty X)
    (hullFunctor X hcoh) (hullUnit X hcoh) (fun F => href F.obj F.property)
    (fun F h => isIso_hullUnit_app X hcoh F h)
    (fun F => hullFunctor_map_hullUnit_app X hcoh href F) F
  have h4 : ((hullAdjunction X hcoh href).unit.app F).hom =
      ((hullUnit X hcoh).app F).hom :=
    congrArg (fun k => k.hom) hunit
  exact Eq.trans (Stacks.CategoryTheory.comp_eqToHom_self _ _) h4

/-- Conversely, a left adjoint to the inclusion of coherent reflexive modules into coherent
modules whose unit is the canonical map to the reflexive hull forces the reflexive hull of a
coherent module to be coherent and reflexive. -/
theorem isCoherent_and_isReflexive_reflexiveHull_of_adjunction
    (p : { p : (Σ L : CoherentModules X ⥤ CoherentReflexiveModules X, L ⊣ inclusion X) //
      ∀ F : CoherentModules X,
        ∃ h : (p.1.obj F).obj.obj = reflexiveHull F.obj,
          (p.2.unit.app F).hom ≫ eqToHom h = (toReflexiveHull F.obj).1 })
    (F : X.Modules) (hF : F.IsCoherent) :
    (reflexiveHull F).IsCoherent ∧ IsReflexive (reflexiveHull F) := by
  obtain ⟨h, -⟩ := p.2 ⟨F, hF⟩
  exact ⟨h ▸ (p.1.1.obj ⟨F, hF⟩).obj.property, h ▸ (p.1.1.obj ⟨F, hF⟩).property⟩

end Stacks.AlgebraicGeometry.ReflexiveHull
