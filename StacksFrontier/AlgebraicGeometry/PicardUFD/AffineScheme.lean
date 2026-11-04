module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Affine
public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.Sections
public import StacksFrontier.AlgebraicGeometry.PicardUFD.Affine
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackInvertible

/-!
# Invertible sheaves on an affine scheme, and invertible modules over its ring of functions

`Stacks.PicardUFD.isTrivial_of_isInvertible_spec` says that an invertible sheaf of modules on
`Spec R` is trivial when `Pic R` is trivial. This file carries that across the canonical
isomorphism `Z ≅ Spec Γ(Z, 𝒪_Z)` of an arbitrary affine scheme, and reads off the consequence
for global sections: the global sections of an invertible sheaf on such a `Z` are free of rank
one over `Γ(Z, 𝒪_Z)`.

That is the passage between an invertible *sheaf* on an affine scheme and an invertible
*module* over its ring of functions. The hypothesis `Subsingleton (CommRing.Pic Γ(Z, 𝒪_Z))`
holds for a local ring and, by `CommRing.Pic`'s instance for `Finite (MaximalSpectrum _)`, for
a semi-local one — in particular for the ring of functions of a finite discrete subscheme,
which is the case [Stacks, Tag 0AGT] closes with "an invertible module over a local ring is
trivial".

## Main results

* `Stacks.PicardUFD.isTrivial_of_isInvertible_of_isAffine` — an invertible sheaf of modules on
  an affine scheme with trivial Picard group of functions is trivial.
* `Stacks.PicardUFD.nonempty_linearEquiv_appTop_of_isInvertible_of_isAffine` — its global
  sections are then free of rank one.

## Implementation notes

The transport is along `AlgebraicGeometry.Scheme.Modules.restrictFunctor` of the two directions
of `AlgebraicGeometry.Scheme.isoSpec`, packaged as the equivalence
`Stacks.AlgebraicGeometry.CoherenceCriteria.restrictEquiv`, whose unit identifies `L` with the
restriction of its restriction. Invertibility crosses by
`RingedSpaceModuleAdjunction.modulePullback_isInvertible_scheme` through
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, and the structure sheaf crosses
by `AlgebraicGeometry.Scheme.Modules.restrictUnitIso`.

## References

* [Stacks Project, Tag 0BDA](https://stacks.math.columbia.edu/tag/0BDA)
* [Stacks Project, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.PicardUFD

/-- **An invertible sheaf of modules on an affine scheme whose ring of functions has trivial
Picard group is trivial.** This is
`Stacks.PicardUFD.isTrivial_of_isInvertible_spec` carried across `Z ≅ Spec Γ(Z, 𝒪_Z)`. -/
public theorem isTrivial_of_isInvertible_of_isAffine (Z : Scheme.{u}) [IsAffine Z]
    [Subsingleton (CommRing.Pic Γ(Z, ⊤))] (L : Z.Modules)
    [Stacks.SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 L] :
    AlgebraicGeometry.SheafOfModules.IsTrivial Z.presheaf Z.ringCatSheaf.property L := by
  have hoiH : IsOpenImmersion Z.isoSpec.hom := IsOpenImmersion.of_isIso Z.isoSpec.hom
  have hoiI : IsOpenImmersion Z.isoSpec.inv := IsOpenImmersion.of_isIso Z.isoSpec.inv
  set e : Z.Modules ≌ (Spec Γ(Z, ⊤)).Modules :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.restrictEquiv Z.isoSpec with he
  have hinv : Stacks.SheafOfModules.IsInvertible (Spec Γ(Z, ⊤)).presheaf
      (Spec Γ(Z, ⊤)).ringCatSheaf.2 (e.functor.obj L) := by
    -- the type ascription pins the spelling of the pullback functor: `Scheme.Modules.pullback`
    -- and `modulePullback` are equal by `rfl` but give `IsInvertible` two instance keys.
    have h1 : Stacks.SheafOfModules.IsInvertible (Spec Γ(Z, ⊤)).presheaf
        (Spec Γ(Z, ⊤)).ringCatSheaf.2 ((Scheme.Modules.pullback Z.isoSpec.inv).obj L) :=
      RingedSpaceModuleAdjunction.modulePullback_isInvertible_scheme Z.isoSpec.inv L
    exact Stacks.SheafOfModules.isInvertible_of_iso _ _
      ((Scheme.Modules.restrictFunctorIsoPullback Z.isoSpec.inv).app L).symm
  obtain ⟨φ⟩ := isTrivial_of_isInvertible_spec Γ(Z, ⊤) (e.functor.obj L)
  refine ⟨(e.unitIso.app L) ≪≫ e.inverse.mapIso φ ≪≫ ?_⟩
  exact Scheme.Modules.restrictUnitIso Z.isoSpec.hom

/-- **The global sections of an invertible sheaf of modules on an affine scheme whose ring of
functions has trivial Picard group are free of rank one.** -/
public theorem nonempty_linearEquiv_appTop_of_isInvertible_of_isAffine (Z : Scheme.{u})
    [IsAffine Z] [Subsingleton (CommRing.Pic Γ(Z, ⊤))] (L : Z.Modules)
    [Stacks.SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 L] :
    Nonempty (Γ(L, (⊤ : Z.Opens)) ≃ₗ[Γ(Z, ⊤)] Γ(Z, ⊤)) :=
  Stacks.AlgebraicGeometry.PicardBaseChange.nonempty_linearEquiv_appTop_of_isTrivial Z L
    (isTrivial_of_isInvertible_of_isAffine Z L)

end Stacks.PicardUFD

end
