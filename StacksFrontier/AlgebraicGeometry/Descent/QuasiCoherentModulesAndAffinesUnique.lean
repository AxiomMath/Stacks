module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteModules
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffines

/-!
# The uniqueness of `𝒢` in condition (4) of Stacks 0GZX

Condition (4) of Stacks 0GZX says that a presheaf of `𝒪_affine`-modules on `S_{affine, τ}`
comes from a **unique** quasi-coherent `𝒪_S`-module `𝒢` by the procedure of Descent,
Section 35.8, that is, is the restriction to the affine objects of `𝒢ᵃ`.  This file proves the
uniqueness half of that condition at `τ = étale`: the composite

`QCoh(𝒪_S) ⥤ Mod(S_étale, 𝒪) ⥤ Mod(S_{affine, étale}, 𝒪_affine)`,  `𝒢 ↦ 𝒢ᵃ|_{S_{affine, ét}}`

is **fully faithful**, so two quasi-coherent `𝒪_S`-modules with isomorphic restricted associated
modules are isomorphic.

Both factors are fully faithful, and neither full faithfulness carries a hypothesis.  The first
is Stacks 0GN7 at `τ = étale`,
`AlgebraicGeometry.SmallEtale.fullyFaithfulAssociatedModuleQcoh'`.  The second is the Comparison
Lemma for sheaves of modules, `Stacks.DenseSubsiteModules.moduleRestriction`, whose fullness and
faithfulness need only that the inclusion of the affine objects is a dense subsite inclusion —
Stacks 04HR, available as
`AlgebraicGeometry.SmallAffineEtale.inclusion_isDenseSubsite`.  In particular *no* part of
Descent, Proposition 03DX is used here: the equivalence of `(3)` and `(4)` which the source
deduces from 03DX is needed only for the **existence** of `𝒢`, which is proved separately, in
`StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffinesExists`.

## Main definitions

* `AlgebraicGeometry.smallAffineEtaleModuleRestriction`: restriction of sheaves of modules from
  the small étale site of `S` to its small affine étale site, over the restricted structure
  sheaf.
* `AlgebraicGeometry.smallAffineEtaleAssociatedModuleQcoh`: the functor
  `𝒢 ↦ 𝒢ᵃ|_{S_{affine, étale}}` of condition (4) of Stacks 0GZX at `τ = étale`.

## Main results

* `AlgebraicGeometry.fullyFaithfulSmallAffineEtaleModuleRestriction`: the restriction functor is
  fully faithful, with no hypothesis.
* `AlgebraicGeometry.fullyFaithfulSmallAffineEtaleAssociatedModuleQcoh` and
  `AlgebraicGeometry.smallAffineEtale_iso_of_associatedModuleQcoh_restriction_iso`:
  **Stacks 0GZX, the uniqueness of `𝒢` in condition (4) at `τ = étale`.**

## Coverage limits

The **existence** of `𝒢` in condition (4), and condition (3) read from condition (2), are not
proved here; they are in
`StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffinesExists`, and the two halves
are read together there as one equivalence of categories,
`AlgebraicGeometry.smallAffineEtaleAssociatedModuleQcohEquivalence`.

The same two statements at `τ = Zariski` are in
`StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffinesZariskiUnique` and
`StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffinesZariskiExists`, so nothing
of Stacks 0GZX is left open at either topology.  See the coverage note of
`StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffines`.

## References

* [Stacks Project, Tag 0GZX](https://stacks.math.columbia.edu/tag/0GZX)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 04HR](https://stacks.math.columbia.edu/tag/04HR)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Restriction of sheaves of modules from the small étale site of `S` to its small affine
étale site, taken over the restricted structure sheaf.  This is the functor induced on modules
by the equivalence of ringed topoi of Stacks 0GZW. -/
public noncomputable abbrev smallAffineEtaleModuleRestriction :=
  Stacks.DenseSubsiteModules.moduleRestriction (SmallAffineEtale.topology B S hS)
    (SmallEtale.topology B S hS) (SmallAffineEtale.inclusion B S hS)
    (SmallEtale.structureSheaf B S hS)

/-- The structure sheaf over which `AlgebraicGeometry.smallAffineEtaleModuleRestriction` takes
its values is the one the small affine étale ringed site of Stacks 0GZX carries. -/
public theorem ringRestriction_smallEtale_structureSheaf :
    Stacks.DenseSubsiteModules.ringRestriction (SmallAffineEtale.topology B S hS)
        (SmallEtale.topology B S hS) (SmallAffineEtale.inclusion B S hS)
        (SmallEtale.structureSheaf B S hS) =
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallAffineEtaleRingedSite B S hS).O) :=
  rfl

/-- **Restriction of sheaves of modules to the small affine étale site is fully faithful**, with
no hypothesis: the inclusion of the affine objects is a dense subsite inclusion by Stacks 04HR,
and the Comparison Lemma for sheaves of modules needs nothing more for full faithfulness. -/
public noncomputable def fullyFaithfulSmallAffineEtaleModuleRestriction :
    (smallAffineEtaleModuleRestriction B S hS).FullyFaithful :=
  .ofFullyFaithful _

/-- **The functor of condition (4) of Stacks 0GZX at `τ = étale`**: a quasi-coherent
`𝒪_S`-module `𝒢` is sent to the restriction to the affine objects of the associated module
`𝒢ᵃ` of Descent, Definition 03DU (4). -/
public noncomputable abbrev smallAffineEtaleAssociatedModuleQcoh :=
  SmallEtale.associatedModuleQcoh B S hS ⋙ smallAffineEtaleModuleRestriction B S hS

/-- **Stacks 0GZX, the uniqueness of `𝒢` in condition (4) at `τ = étale`.**  The functor
`𝒢 ↦ 𝒢ᵃ|_{S_{affine, étale}}` from the quasi-coherent `𝒪_S`-modules to the `𝒪_affine`-modules on
`S_{affine, étale}` is fully faithful: it is Stacks 0GN7 at `τ = étale` followed by the
Comparison Lemma for sheaves of modules on the dense subsite of affine objects. -/
@[stacks 0GZX "(4) at τ = étale, uniqueness of 𝒢"]
public noncomputable def fullyFaithfulSmallAffineEtaleAssociatedModuleQcoh :
    (smallAffineEtaleAssociatedModuleQcoh B S hS).FullyFaithful :=
  (SmallEtale.fullyFaithfulAssociatedModuleQcoh' B S hS).comp
    (fullyFaithfulSmallAffineEtaleModuleRestriction B S hS)

/-- **Stacks 0GZX, the uniqueness of `𝒢` in condition (4) at `τ = étale`**, read as a
uniqueness statement: two quasi-coherent `𝒪_S`-modules whose associated modules have isomorphic
restrictions to the small affine étale site of `S` are isomorphic. -/
@[stacks 0GZX "(4) at τ = étale, uniqueness of 𝒢"]
public theorem smallAffineEtale_iso_of_associatedModuleQcoh_restriction_iso
    (G₁ G₂ : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory)
    (e : (smallAffineEtaleAssociatedModuleQcoh B S hS).obj G₁ ≅
      (smallAffineEtaleAssociatedModuleQcoh B S hS).obj G₂) :
    Nonempty (G₁.obj ≅ G₂.obj) :=
  ⟨(SheafOfModules.isQuasicoherent S.ringCatSheaf).ι.mapIso
    ((fullyFaithfulSmallAffineEtaleAssociatedModuleQcoh B S hS).preimageIso e)⟩

end AlgebraicGeometry

end
