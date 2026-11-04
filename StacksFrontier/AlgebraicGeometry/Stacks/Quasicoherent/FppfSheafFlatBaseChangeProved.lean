module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AssociatedModuleBaseChangeFinalSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LiftedFppfFamilyFromDescent

/-!
# Stacks 076T

`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/FppfSheafFromFlatBaseChange.lean` reduces the
fppf sheaf condition of **Stacks 076T** to the sheaf condition along the families of arrows of
`𝒳` which lie over an fppf covering of schemes, and names that sheaf condition
`AlgebraicGeometry.Stack.IsSheafForLiftedFppfFamily`.  This file proves it, and with it Stacks
076T.

## What goes into it

Four modules supply the chain, each of which had carried the next as a hypothesis:

* `AlgebraicGeometry.Stack.associatedModuleBaseChangeFinalSectionsCompat` -- the compatibility on
  sections over the final object of the small étale site between the base change of **Stacks
  03LC (1)** and the base change of the presheaf of **Stacks 03DS**;
* `AlgebraicGeometry.Stack.liftedSectionsFactorFourSquare_of_compat` -- that compatibility gives
  the square for factor 4 of `AlgebraicGeometry.Stack.liftedSectionsIso`;
* `AlgebraicGeometry.Stack.liftedSectionsCocycle_of_factorFourSquare` -- that square gives the
  cocycle condition `AlgebraicGeometry.Stack.LiftedSectionsCocycle`;
* `AlgebraicGeometry.Stack.isSheafForLiftedFppfFamily` -- the cocycle condition gives the sheaf
  condition along a family lying over an fppf covering, which is the step of the source's proof.

## Main results

* `AlgebraicGeometry.Stack.isSheafForLiftedFppfFamily_of_isFiberedInGroupoids`: **the step of the
  proof of Stacks 076T, with nothing carried.**
* `AlgebraicGeometry.Stack.isSheaf_fppf_of_isLocallyQuasicoherent_of_flatBaseChange`: **Stacks
  076T.**

## References

* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
* [Stacks Project, Tag 06TP](https://stacks.math.columbia.edu/tag/06TP)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

universe u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- **The step of the proof of Stacks 076T.**  For a presheaf of modules over the structure
sheaf of a category fibred in groupoids over the big fppf category of schemes over `S` which is
locally quasi-coherent (**Stacks 06WJ**) and whose comparison map `c_φ` of **Stacks 06WC** is an
isomorphism along every arrow lying over a morphism of schemes which is flat and locally of
finite presentation, the sheaf condition holds along every family of arrows of `𝒳` which
generates a covering sieve of the inherited fppf topology and lies over an fppf covering of
schemes.

This is `AlgebraicGeometry.Stack.isSheafForLiftedFppfFamily` with its cocycle hypothesis
discharged: the cocycle condition comes from the factor-4 square by
`AlgebraicGeometry.Stack.liftedSectionsCocycle_of_factorFourSquare`, that square from the
base-change compatibility on sections over the final object by
`AlgebraicGeometry.Stack.liftedSectionsFactorFourSquare_of_compat`, and that compatibility is
`AlgebraicGeometry.Stack.associatedModuleBaseChangeFinalSectionsCompat`. -/
theorem isSheafForLiftedFppfFamily_of_isFiberedInGroupoids :
    IsSheafForLiftedFppfFamily B E h S hS p hp :=
  isSheafForLiftedFppfFamily B E h S hS p hp
    (liftedSectionsCocycle_of_factorFourSquare B E h S hS p hp
      (liftedSectionsFactorFourSquare_of_compat B E h S hS p hp
        (associatedModuleBaseChangeFinalSectionsCompat B E h S hS p hp)))

/-- **Stacks 076T.** Let `F` be a presheaf of modules over the structure sheaf of a category
fibred in groupoids over the big fppf category of schemes over `S`. If `F` is locally
quasi-coherent (**Stacks 06WJ**) and the comparison map `c_φ` of **Stacks 06WC** is an
isomorphism for every arrow of `𝒳` lying over a morphism of schemes which is flat and locally of
finite presentation, then `F` is a sheaf for the fppf topology of **Stacks 06TP**.

The sheaf condition is tested, by
`AlgebraicGeometry.Stack.isSheaf_of_isSheafFor_flatLfp`, on the families of arrows lying over an
fppf covering of schemes; along such a family hypothesis (b) applies to every member, and the
sheaf condition for it is
`AlgebraicGeometry.Stack.isSheafForLiftedFppfFamily_of_isFiberedInGroupoids`. -/
@[stacks 076T]
theorem isSheaf_fppf_of_isLocallyQuasicoherent_of_flatBaseChange
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hlqc : IsLocallyQuasicoherent B E h S hS p hp F)
    (hbc : HasFlatLfpBaseChangeProperty B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) F) :
    Presheaf.IsSheaf (associatedTopology B S hS p B.topology) F.presheaf :=
  isSheaf_of_isSheafFor_flatLfp B S hS p hp F.presheaf
    fun {_} R hR hflat =>
      isSheafForLiftedFppfFamily_of_isFiberedInGroupoids B E h S hS p hp F hlqc hbc R hR hflat

end AlgebraicGeometry.Stack

end
