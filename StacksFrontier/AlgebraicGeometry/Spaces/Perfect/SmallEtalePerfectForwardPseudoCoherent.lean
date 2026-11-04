module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtalePseudoCoherentDescent
public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.PerfectToPseudoCoherentGeneral
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtalePerfectForward

/-!
# The pseudo-coherence half of the converse of Stacks 08HG

`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/SmallEtalePerfectForward.lean` proves the direction
`E` perfect ⟹ `ε^*E` perfect of Stacks 08HG. This file proves the first input of the converse:
if `ε^*E` is perfect then `E` is `m`-pseudo-coherent for every `m`. The converse itself and the
equivalence are in `StacksFrontier/AlgebraicGeometry/Spaces/Perfect/SmallEtalePerfectConverse.lean`.

## Main results

* `AlgebraicGeometry.SmallEtale.isPseudoCoherentFromZariski_of_isPerfectSmallEtale`: if `ε^*E`
  is perfect then `E` is `m`-pseudo-coherent for every `m`.  This is not a clause of Stacks 08HG
  and carries no tag.

## References

* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
* [Stacks Project, Tag 08HG](https://stacks.math.columbia.edu/tag/08HG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u d d'

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  [HasDerivedCategory.{d}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))]
  [HasDerivedCategory.{d'} (SheafOfModules.{u} (structureSheaf B S hS))]

/-- **The pseudo-coherence half of the converse of Stacks 08HG.**  If `ε^*E` is a perfect object
of `D(𝒪_étale)` then `E` is `m`-pseudo-coherent on the small Zariski site of `S`, for every
integer `m`.

This is not a clause of Stacks 08HG and carries no tag: it is the first input of the converse,
`AlgebraicGeometry.SmallEtale.isPerfectZariski_of_isPerfectSmallEtale`.

Both steps are library results read at the universes of the two sites: a perfect object of `D(𝒪)`
is `m`-pseudo-coherent (`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_isPerfect_general`,
on the small étale ringed site, a `RingedSite.{u + 1, u, u}`), and `m`-pseudo-coherence descends
along `ε` (`AlgebraicGeometry.SmallEtale.associatedModuleToPseudoCoherent`, clause (2) ⇒ (1) of
Stacks 08HE).  The second is read at the same termwise `ε^*` as clause (2) of this tag, so no
comparison of two pullbacks intervenes. -/
public theorem isPseudoCoherentFromZariski_of_isPerfectSmallEtale
    (E : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O)))
    (hE : IsPerfectSmallEtale B S hS E) (m : ℤ) :
    IsPseudoCoherentFromZariski S E m :=
  let : HasDerivedCategory.{d} (SheafOfModules.{u} S.ringCatSheaf) :=
    ‹HasDerivedCategory.{d} (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))›
  associatedModuleToPseudoCoherent B S hS E m
    (AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_isPerfect_general
      (smallEtaleRingedSite B S hS) hE m)

end AlgebraicGeometry.SmallEtale

end
