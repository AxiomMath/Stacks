module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Restrict
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.LocalizationComparison

/-!
# Restriction of a pushforward of sheaves of modules to an open

Restricting a pushforward along `f` to an open `V` of the target is the pushforward along the
restricted morphism `f ∣_ V` of the restriction to `f ⁻¹ᵁ V`. This is the ringed-space comparison
isomorphism of [Stacks, Tag 01E5], read on schemes: the scheme-level restriction functor and the
ringed-space one agree, and so do the two restricted morphisms.

## Main definitions

* `Stacks.LocalCohomology.schemePushforwardRestrictIso`: the comparison isomorphism on schemes.

## Main results

* `Stacks.LocalCohomology.schemeRestrictFunctor_eq_moduleRestriction`: the two restriction
  functors agree.
* `Stacks.LocalCohomology.ringedRestrictEq`: the sheafed-space morphism underlying `f ∣_ V` is
  the ringed-space restricted morphism.

## Implementation notes

`ringedRestrictEq` is proved by cancelling the monomorphism `openSubspaceInclusion`, which the
forgetful functor to presheafed spaces reflects, and then appealing to
`Stacks.Cohomology.HigherDirectImage.restrictedMorphism_comp_openSubspaceInclusion`.

## References

* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 0BK3](https://stacks.math.columbia.edu/tag/0BK3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits

universe u

namespace Stacks.LocalCohomology

/-- The restriction functor on sheaves of modules over a scheme is the ringed-space restriction
functor of [Stacks, Tag 01E5]. -/
public theorem schemeRestrictFunctor_eq_moduleRestriction (X : Scheme.{u}) (V : X.Opens) :
    Scheme.Modules.restrictFunctor V.ι =
      Stacks.Cohomology.HigherDirectImage.moduleRestriction X.toRingedSpace V := by
  change Scheme.Modules.restrictFunctor V.ι =
    restMod (Stacks.Cohomology.HigherDirectImage.asRingSheafedSpace X.toRingedSpace) V
  unfold Scheme.Modules.restrictFunctor restMod
  congr 1
  ext U
  simp [phiSh, Scheme.Opens.ι_appIso]
  rfl

/-- The morphism of sheafed spaces underlying the restriction `f ∣_ V` of a morphism of schemes
is the ringed-space restricted morphism of [Stacks, Tag 01E5]. -/
public theorem ringedRestrictEq
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) :
    (f ∣_ V).toLRSHom.toShHom =
      Stacks.Cohomology.HigherDirectImage.restrictedMorphism f.toLRSHom.toShHom V := by
  have hmono : Mono (Stacks.Cohomology.HigherDirectImage.openSubspaceInclusion
      Y.toRingedSpace V) := by
    apply (SheafedSpace.forgetToPresheafedSpace (C := CommRingCat)).mono_of_mono_map
    change Mono ((Y.toRingedSpace.toPresheafedSpace).ofRestrict V.isOpenEmbedding)
    infer_instance
  apply (cancel_mono (Stacks.Cohomology.HigherDirectImage.openSubspaceInclusion
    Y.toRingedSpace V)).mp
  change ((f ∣_ V) ≫ V.ι).toLRSHom.toShHom =
    Stacks.Cohomology.HigherDirectImage.restrictedMorphism f.toLRSHom.toShHom V ≫
      Stacks.Cohomology.HigherDirectImage.openSubspaceInclusion Y.toRingedSpace V
  rw [morphismRestrict_ι]
  change Stacks.Cohomology.HigherDirectImage.openSubspaceInclusion X.toRingedSpace
      (Stacks.Cohomology.HigherDirectImage.preimageOpen f.toLRSHom.toShHom V) ≫
      f.toLRSHom.toShHom =
    Stacks.Cohomology.HigherDirectImage.restrictedMorphism f.toLRSHom.toShHom V ≫
      Stacks.Cohomology.HigherDirectImage.openSubspaceInclusion Y.toRingedSpace V
  exact Stacks.Cohomology.HigherDirectImage.restrictedMorphism_comp_openSubspaceInclusion
    f.toLRSHom.toShHom V

/-- Restricting a pushforward to an open of the target is the pushforward along the restricted
morphism of the restriction to the preimage. -/
public noncomputable def schemePushforwardRestrictIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) :
    Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι ⋙
        Scheme.Modules.pushforward (f ∣_ V) ≅
      Scheme.Modules.pushforward f ⋙ Scheme.Modules.restrictFunctor V.ι := by
  rw [schemeRestrictFunctor_eq_moduleRestriction X (f ⁻¹ᵁ V),
    schemeRestrictFunctor_eq_moduleRestriction Y V]
  change Stacks.Cohomology.HigherDirectImage.moduleRestriction X.toRingedSpace (f ⁻¹ᵁ V) ⋙
      RingedSpaceModuleAdjunction.modulePushforward (f ∣_ V).toLRSHom.toShHom ≅
    RingedSpaceModuleAdjunction.modulePushforward f.toLRSHom.toShHom ⋙
      Stacks.Cohomology.HigherDirectImage.moduleRestriction Y.toRingedSpace V
  rw [ringedRestrictEq f V]
  exact Stacks.Cohomology.HigherDirectImage.modulePushforwardRestrictIso
    f.toLRSHom.toShHom V

end Stacks.LocalCohomology
