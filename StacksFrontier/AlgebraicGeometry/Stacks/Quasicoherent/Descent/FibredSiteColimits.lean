module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.FibredSiteLocalization
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentAssembly

/-!
# The colimit clause of Stacks 06WN over one input, the localization step discharged

`AlgebraicGeometry.FibredSite.ClosedUnderColimitsOfSizeOfBase` is the reduction step of
Stacks 06WN, stated as a hypothesis in
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentAssembly`: closure of
quasi-coherence under colimits on the associated fppf site of `𝒳`, granted that closure on the
big fppf site of every scheme of `B`.  It is discharged here, by the equivalence of ringed sites
`(𝒳/x, 𝒪_𝒳|) ≌ ((Sch/U)_fppf, 𝒪)` of
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.FibredSiteLocalization`.

So the clauses assembled in `QuasicoherentAssembly` over *two* inputs stand here over *one*,
essential surjectivity of `𝓕 ↦ 𝓕^a` at every scheme of `B`, which is the surjectivity half of
Stacks 03DX (1).

## Main results

* `AlgebraicGeometry.FibredSite.closedUnderColimitsOfSizeOfBase`: **the reduction step of
  Stacks 06WN**, discharged.
* `AlgebraicGeometry.FibredSite.colimits_quasicoherentModules_of_surjective`: **Stacks 06WN (1)
  for the ambient category `Mod(𝒪_𝒳)`**, over essential surjectivity alone.
* `AlgebraicGeometry.FibredSite.preservesFiniteColimits_quasicoherentInclusion_of_surjective`:
  **Stacks 06WV (3), right exactness of the inclusion**, over essential surjectivity alone.

## Implementation notes

Nothing here carries a `stacks` attribute: a hypothesis is part of a citation, and essential
surjectivity of `𝓕 ↦ 𝓕^a` is still a hypothesis.  Over and above that, Stacks 06WN (1) compares
the colimits with those computed in `Mod(𝒳_Zar, 𝒪_𝒳)`, `Mod(𝒳_étale, 𝒪_𝒳)` and
`LQCoh(𝒪_𝒳)` as well, and only `Mod(𝒪_𝒳)` is below.

## References

* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 06WV](https://stacks.math.columbia.edu/tag/06WV)
* [Stacks Project, Tag 06WI](https://stacks.math.columbia.edu/tag/06WI)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] [EssentiallySmall.{u} 𝒳]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- **The reduction step of Stacks 06WN, discharged.**  The hypothesis
`AlgebraicGeometry.FibredSite.ClosedUnderColimitsOfSizeOfBase` holds: it is the localization
argument of Stacks 06WI, and
`AlgebraicGeometry.FibredSite.closedUnderColimitsOfSize_ringStructureSheafCore_of_base` proves
it. -/
public theorem closedUnderColimitsOfSizeOfBase :
    ClosedUnderColimitsOfSizeOfBase B S hS p hp :=
  closedUnderColimitsOfSize_ringStructureSheafCore_of_base B S hS p hp

/-- Closure of quasi-coherence under colimits of every shape `K : Type u` on the associated
fppf site of an essentially small category fibred in groupoids, over essential surjectivity of
`𝓕 ↦ 𝓕^a` at every scheme of `B` alone. -/
public theorem closedUnderColimitsOfSize_quasicoherentModules_of_surjective
    (hsurj : ∀ (T : Scheme.{u}) (hT : B.Contains T),
      BigFppfOver.QuasicoherentIsEssImageAssociatedModule B T hT) :
    SheafOfModules.ClosedUnderColimitsOfSize.{u, u + 1, u, u, u}
      (ringStructureSheafCore B S hS p hp .fppf) :=
  closedUnderColimitsOfSize_quasicoherentModules_of_descent B S hS p hp
    (closedUnderColimitsOfSizeOfBase B S hS p hp) hsurj

/-- **Stacks 06WN (1) for the ambient category `Mod(𝒪_𝒳)`**, over essential surjectivity of
`𝓕 ↦ 𝓕^a` at every scheme of `B` alone: the category of quasi-coherent modules on the
associated fppf site of an essentially small category fibred in groupoids has all colimits
indexed at the size of the site, and they agree with the colimits of the same diagram taken in
all module sheaves on that site. -/
public theorem colimits_quasicoherentModules_of_surjective
    (hsurj : ∀ (T : Scheme.{u}) (hT : B.Contains T),
      BigFppfOver.QuasicoherentIsEssImageAssociatedModule B T hT) :
    HasColimitsOfSize.{u, u} (quasicoherentModules.{u, u + 1, u, u} B S hS p hp) ∧
      PreservesColimitsOfSize.{u, u}
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          (ringStructureSheafCore B S hS p hp .fppf)).ι :=
  colimits_quasicoherentModules_of_descent B S hS p hp
    (closedUnderColimitsOfSizeOfBase B S hS p hp) hsurj

/-- **Stacks 06WV (3), right exactness of the inclusion**, over essential surjectivity of
`𝓕 ↦ 𝓕^a` at every scheme of `B` alone: the inclusion `QCoh(𝒪_𝒳) ⟶ Mod(𝒪_𝒳)` preserves finite
colimits. -/
public theorem preservesFiniteColimits_quasicoherentInclusion_of_surjective
    (hsurj : ∀ (T : Scheme.{u}) (hT : B.Contains T),
      BigFppfOver.QuasicoherentIsEssImageAssociatedModule B T hT) :
    PreservesFiniteColimits
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (ringStructureSheafCore B S hS p hp .fppf)).ι :=
  preservesFiniteColimits_quasicoherentInclusion_of_descent B S hS p hp
    (closedUnderColimitsOfSizeOfBase B S hS p hp) hsurj

end AlgebraicGeometry.FibredSite

end
