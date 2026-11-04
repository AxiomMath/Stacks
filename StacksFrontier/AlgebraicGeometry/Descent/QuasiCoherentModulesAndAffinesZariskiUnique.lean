module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteModules
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiRealFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffines

/-!
# Quasi-coherent modules on the small affine Zariski site: uniqueness

Let `S` be a scheme. The functor `𝒢 ↦ 𝒢ᵃ|_{S_{affine, Zar}}`, sending a quasi-coherent
`𝒪_S`-module to the restriction of its associated module to the affine objects of the small
Zariski site, is fully faithful. This is the uniqueness of `𝒢` in condition (4) of
[Stacks, Tag 0GZX] at `τ = Zariski`. The functor is the composite of `𝒢 ↦ 𝒢ᵃ` on quasi-coherent
modules and of restriction of sheaves of modules to the dense subsite of affine objects, and both
are fully faithful.

## Main definitions

* `AlgebraicGeometry.smallAffineZariskiModuleRestriction`: restriction of sheaves of modules from
  the small Zariski site of `S` to its small affine Zariski site, over the restricted structure
  sheaf.
* `AlgebraicGeometry.smallAffineZariskiAssociatedModuleQcoh`: the functor
  `𝒢 ↦ 𝒢ᵃ|_{S_{affine, Zar}}` on quasi-coherent `𝒪_S`-modules.

## Main results

* `AlgebraicGeometry.fullyFaithfulSmallAffineZariskiModuleRestriction`: the restriction functor is
  fully faithful.
* `AlgebraicGeometry.fullyFaithfulSmallAffineZariskiAssociatedModuleQcoh`: the functor
  `𝒢 ↦ 𝒢ᵃ|_{S_{affine, Zar}}` is fully faithful.
* `AlgebraicGeometry.smallAffineZariski_iso_of_associatedModuleQcoh_restriction_iso`: two
  quasi-coherent `𝒪_S`-modules whose associated modules have isomorphic restrictions to the small
  affine Zariski site are isomorphic.

## References

* [Stacks Project, Tag 0GZX](https://stacks.math.columbia.edu/tag/0GZX)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
* [Stacks Project, Tag 0GZW](https://stacks.math.columbia.edu/tag/0GZW)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Restriction of sheaves of modules from the small Zariski site of `S` to its small affine
Zariski site, taken over the restricted structure sheaf. -/
public noncomputable abbrev smallAffineZariskiModuleRestriction :=
  Stacks.DenseSubsiteModules.moduleRestriction (SmallAffineZariski.topology B S hS)
    (SmallZariski.topology B S hS) (SmallAffineZariski.inclusion B S hS)
    (SmallZariski.structureSheaf B S hS)

/-- The structure sheaf over which `AlgebraicGeometry.smallAffineZariskiModuleRestriction` takes
its values is the structure sheaf of the small affine Zariski ringed site. -/
public theorem ringRestriction_smallZariski_structureSheaf :
    Stacks.DenseSubsiteModules.ringRestriction (SmallAffineZariski.topology B S hS)
        (SmallZariski.topology B S hS) (SmallAffineZariski.inclusion B S hS)
        (SmallZariski.structureSheaf B S hS) =
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallAffineZariskiRingedSite B S hS).O) :=
  rfl

/-- Restriction of sheaves of modules to the small affine Zariski site is fully faithful. -/
public noncomputable def fullyFaithfulSmallAffineZariskiModuleRestriction :
    (smallAffineZariskiModuleRestriction B S hS).FullyFaithful :=
  .ofFullyFaithful _

/-- The functor sending a quasi-coherent `𝒪_S`-module `𝒢` to the restriction to the affine objects
of its associated module `𝒢ᵃ` on the small Zariski site. -/
public noncomputable abbrev smallAffineZariskiAssociatedModuleQcoh :=
  SmallZariski.associatedModuleQcoh B S hS ⋙ smallAffineZariskiModuleRestriction B S hS

/-- The functor `𝒢 ↦ 𝒢ᵃ|_{S_{affine, Zar}}` from the quasi-coherent `𝒪_S`-modules to the
`𝒪_affine`-modules on `S_{affine, Zar}` is fully faithful. -/
@[stacks 0GZX "(4) at τ = Zariski, uniqueness of 𝒢"]
public noncomputable def fullyFaithfulSmallAffineZariskiAssociatedModuleQcoh :
    (smallAffineZariskiAssociatedModuleQcoh B S hS).FullyFaithful :=
  (SmallZariski.fullyFaithfulAssociatedModuleQcoh B S hS).comp
    (fullyFaithfulSmallAffineZariskiModuleRestriction B S hS)

/-- Two quasi-coherent `𝒪_S`-modules whose associated modules have isomorphic restrictions to the
small affine Zariski site of `S` are isomorphic. -/
@[stacks 0GZX "(4) at τ = Zariski, uniqueness of 𝒢"]
public theorem smallAffineZariski_iso_of_associatedModuleQcoh_restriction_iso
    (G₁ G₂ : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory)
    (e : (smallAffineZariskiAssociatedModuleQcoh B S hS).obj G₁ ≅
      (smallAffineZariskiAssociatedModuleQcoh B S hS).obj G₂) :
    Nonempty (G₁.obj ≅ G₂.obj) :=
  ⟨(SheafOfModules.isQuasicoherent S.ringCatSheaf).ι.mapIso
    ((fullyFaithfulSmallAffineZariskiAssociatedModuleQcoh B S hS).preimageIso e)⟩

end AlgebraicGeometry

end
