module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalVanishingFromCechVanishing
public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.CategoryTheory.Sites.GlobalSections

/-!
# Sections of an injective sheaf of modules are injective

Let `X` be a scheme, `Λ` a ring and `I` an injective object of the category of sheaves of
`Λ`-modules on the small étale site of `X`. Then for every étale `X`-scheme `W` the module of
sections `I(W)` is an injective `Λ`-module.

For `W = X` this holds because global sections are right adjoint to the constant sheaf functor,
which preserves monomorphisms (the constant presheaf functor does, and so does sheafification).
For general `W`, the sections `I(W)` are the global sections of the restriction `I|_W`, and
restriction preserves injectives since its left adjoint, extension by zero, preserves
monomorphisms.

This is an input to Step 7 of the proof of [Stacks, Tag 03UG]: with coefficients in a
self-injective ring `R = A[G]`, the functor `Hom_R(N, -)` applied to an injective resolution
computes cohomology because the sections of injective sheaves are injective `R`-modules.

## Main results

* `Stacks.EtaleCohomology.injective_etaleModuleGlobalSections`
* `Stacks.EtaleCohomology.injective_etaleModuleRestriction`
* `Stacks.EtaleCohomology.injective_etaleModule_sections`
* `Stacks.EtaleCohomology.moduleInjective_etaleModule_sections`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ]

/-- The constant sheaf functor into sheaves of modules on the small étale site preserves
monomorphisms: the constant presheaf functor and sheafification both do. -/
instance constantSheaf_etaleModules_preservesMonomorphisms (X : Scheme.{u}) :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).PreservesMonomorphisms := by
  unfold constantSheaf
  infer_instance

/-- **Global sections of an injective sheaf of modules form an injective object.** Global sections
are right adjoint to the constant sheaf functor, which preserves monomorphisms. -/
theorem injective_etaleModuleGlobalSections {X : Scheme.{u}} (I : EtaleModules.{u, r} Λ X)
    [Injective I] : Injective ((etaleModuleGlobalSections.{u, r} Λ X).obj I) :=
  (constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).map_injective I
    inferInstance

/-- **Restriction along an étale morphism preserves injective sheaves of modules**, its left
adjoint, extension by zero, preserving monomorphisms. -/
theorem injective_etaleModuleRestriction {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
    (I : EtaleModules.{u, r} Λ X) [Injective I] :
    Injective ((etaleModuleRestriction.{u, r} Λ j).obj I) :=
  (etaleModuleExtensionByZeroAdj.{u, r} Λ j).map_injective I inferInstance

/-- An étale `X`-scheme `W` is the image of the terminal object of the small étale site of `W`
under composition with its structure morphism. -/
def smallEtaleComposeIdIso {X : Scheme.{u}} (W : X.Etale) :
    (Scheme.Etale.smallEtaleCompose W.hom).obj (Scheme.Etale.mk (𝟙 W.left)) ≅ W :=
  MorphismProperty.Over.isoMk (Iso.refl _) (by
    rw [Scheme.Etale.smallEtaleCompose_obj_hom]; rfl)

/-- **Sections of an injective sheaf of modules over an étale `X`-scheme form an injective
object.** They are the global sections of the restriction to `W`, which is injective. -/
theorem injective_etaleModule_sections {X : Scheme.{u}} (I : EtaleModules.{u, r} Λ X)
    [Injective I] (W : X.Etale) : Injective (I.obj.obj (op W)) := by
  have := injective_etaleModuleRestriction Λ W.hom I
  have h := (constantSheafAdj W.left.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)
    (etaleMkIdIsTerminal W.left)).map_injective _ this
  exact Injective.of_iso (I.obj.mapIso (smallEtaleComposeIdIso W).op) h

/-- **Sections of an injective sheaf of modules over an étale `X`-scheme are an injective
module.** -/
theorem moduleInjective_etaleModule_sections {X : Scheme.{u}} (I : EtaleModules.{u, r} Λ X)
    [Injective I] (W : X.Etale) : Module.Injective Λ (I.obj.obj (op W)) :=
  have := injective_etaleModule_sections Λ I W
  Module.injective_module_of_injective_object Λ _

end Stacks.EtaleCohomology

end
