module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseRingedSiteHomGeneral
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorQuasicoherentOnSite
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseOpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentInternalHom

/-!
# Closure properties of the quasi-coherent modules on a big site

Descent, Lemma 0GNC lists six closure properties of the category `QCoh((Sch/S)_τ, 𝒪)` of
quasi-coherent modules on one of the five big sites of a scheme `S`,
`τ ∈ {Zariski, étale, smooth, syntomic, fppf}`: closure under direct sums (1), under colimits
(2), under cokernels (3), under extensions (4), under tensor products (5), and quasi-coherence
of the internal hom out of a finite locally free module (6).

This file proves clauses (5) and (6) for all five topologies at once.  The five sites are the
localizations `AlgebraicGeometry.BigFppfOver.baseOverTopology` of the five topologies of a
chosen big fppf site at the object `S`, all on the single category
`AlgebraicGeometry.BigFppfOver`, with the structure sheaf
`AlgebraicGeometry.FibredSite.baseStructureSheaf`; that is the presentation of the five big
sites used throughout this directory.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.baseRingedSite`: the big `τ`-site of `S` with its sheaf of
  global functions, read as a ringed site.

## Main results

* `AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_tensorSheaf`: **clause (5)** — the
  tensor product of two quasi-coherent `𝒪`-modules on `(Sch/S)_τ` is quasi-coherent.
* `AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_internalHomSheaf`: **clause (6)** — for
  quasi-coherent `𝓕` and `𝓖` with `𝓕` finite locally free, `𝓗om_𝒪(𝓕, 𝓖)` is quasi-coherent on
  `(Sch/S)_τ`.

## Implementation notes

Both clauses are instantiations at the big `τ`-sites of statements already proved for an
arbitrary ringed site, and the point of the instantiation is that the side conditions those
statements carry are *discharged* here rather than assumed: the big category of schemes over
`S` is essentially small, so abelian presheaves on the site and on each of its slices have a
sheafification whose weak equivalences are the locally bijective maps
(`AlgebraicGeometry.BigFppfOver.hasSheafify_baseOverTopology`,
`AlgebraicGeometry.BigFppfOver.hasSheafify_baseOver`,
`AlgebraicGeometry.BigFppfOver.wEqualsLocallyBijective_baseOverTopology` and
`AlgebraicGeometry.BigFppfOver.wEqualsLocallyBijective_baseOver`), and the forgetful functor
from commutative rings to rings preserves limits, so sheaves compose with it
(`AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat`).  The general statements are
`Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isQuasicoherentOnSite` (Stacks 03L6,
quasi-coherent case) and `AlgebraicGeometry.RingedSite.internalHomSheaf_isQuasicoherent`.

The tensor product is the one of Stacks 0GMW, the uncurried
`Stacks.SheafOfModules.Tensor.sheafTensor`, the sheafification of the objectwise tensor product;
the internal hom is the one of Stacks 03EM, `AlgebraicGeometry.RingedSite.internalHomSheaf`.
Quasi-coherence is `SheafOfModules.IsQuasicoherentOnSite`, the predicate of Stacks 03DL(6).

The objects of the big category of schemes over `S` lie in `Type (u + 1)` while its morphisms
and its structure sheaf lie in `Type u`, so the universe arguments of the two general
statements are written out: `u + 1` for the objects, `u` for the morphisms and for the
coefficient rings.  The internal hom of modules with sections in `Type u` has its sections in
`Type (u + 1)`, that being the universe in which a morphism of modules on a slice lives.

## The other clauses, and where they are

Clauses (1), (2), (3) and (4) are not proved here.  All four are proved elsewhere in the
library, at every `τ` and with no hypothesis, so the six clauses of the lemma are complete
between this file and those two.

Clauses (1), (2) and (3) are
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentColimitsBigSites`:
`AlgebraicGeometry.BigFppfOver.isClosedUnderColimitsOfShape_baseIsQuasicoherentOnSite` and its
discrete and parallel-pair cases.  They are proved the way the source proves them, by the
transfer of Lemma 06VE rather than by any statement about the slice of a big site at an affine
object: the quasi-coherent modules of `(Sch/S)_τ` are the essential image of the
colimit-preserving fully faithful functor `𝓕 ↦ 𝓕^a`, so they are closed under the colimits that
functor preserves.  The identification of that essential image is the essential surjectivity
half of Stacks 03DX (1); at an arbitrary `τ` it is the theorem
`AlgebraicGeometry.BigFppfOver.baseQuasicoherentIsEssImageAssociatedModule`, and at
`τ = fppf` it is `AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule'`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/EffectiveGlueAgreementRestrFun.lean`
`:702`).  In particular the three clauses carry no such hypothesis at the four topologies
`τ ≠ fppf`.

Clause (4) is
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BaseRestrictionRightExactAll.lean`, on
`AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_shortExact_X₂_all` and the
`CategoryTheory.ObjectProperty.IsClosedUnderExtensions` instance beside it.  It does not follow
from the other three: closure under extensions is independent of closure under kernels and
cokernels, as recorded in
`StacksFrontier.AlgebraicGeometry.Spaces.QuasiCoherentExactSequences`.  The source obtains it from
part (10) of Stacks 06VE — given a short exact sequence `0 → 𝓕₁^a → ℰ → 𝓕₂^a → 0` of
`𝒪`-modules, `ℰ` is again an `𝓕^a` — and that is the route taken, through the essential-image
form `AlgebraicGeometry.BigFppfOver.essImage_X₂_of_shortExact_big`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BaseExtensionEssImage.lean`).

## References

* [Stacks Project, Tag 0GNC](https://stacks.math.columbia.edu/tag/0GNC)
* [Stacks Project, Tag 03L6](https://stacks.math.columbia.edu/tag/03L6)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

-- The big `τ`-site of `S` as a ringed site is `AlgebraicGeometry.BigFppfOver.baseRingedSite`,
-- imported from
-- `StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseRingedSiteHomGeneral`.

/-- **Stacks 0GNC, part (5).**  The tensor product of two quasi-coherent `𝒪`-modules on the big
`τ`-site of a scheme `S` is quasi-coherent, for each of the five topologies.

The tensor product is the one of Stacks 0GMW, the sheafification of the objectwise tensor
product of the underlying presheaves of modules.  The statement is the quasi-coherent clause of
Stacks 03L6 on a ringed site,
`Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isQuasicoherentOnSite`, read at this
site: the two factors are globally presented on the members of two covering families, the
objects admitting an arrow into a member of each again cover, and over such an object the
tensor product of two globally presented modules is globally presented. -/
@[stacks 0GNC "part (5)"]
theorem isQuasicoherentOnSite_tensorSheaf (τ : SiteKind)
    (F G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O))
    [SheafOfModules.IsQuasicoherentOnSite F] [SheafOfModules.IsQuasicoherentOnSite G] :
    SheafOfModules.IsQuasicoherentOnSite
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (FibredSite.baseStructureSheaf B S hS τ))).obj (F, G)) := by
  have hF : SheafOfModules.IsQuasicoherentOnSite
    (R := Sheaf.toRingCat.{u, u + 1, u} (baseOverTopology B S hS τ)
      (FibredSite.baseStructureSheaf B S hS τ)) F := ‹_›
  have hG : SheafOfModules.IsQuasicoherentOnSite
    (R := Sheaf.toRingCat.{u, u + 1, u} (baseOverTopology B S hS τ)
      (FibredSite.baseStructureSheaf B S hS τ)) G := ‹_›
  exact Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isQuasicoherentOnSite _ _ F G

/-- **Stacks 0GNC, part (6).**  The internal hom `𝓗om_𝒪(𝓕, 𝓖)` of Stacks 03EM is quasi-coherent
on the big `τ`-site of a scheme `S`, for each of the five topologies, when `𝓕` and `𝓖` are
quasi-coherent and `𝓕` is finite locally free.

This is `AlgebraicGeometry.RingedSite.internalHomSheaf_isQuasicoherent`, the statement for an
arbitrary ringed site, with its two sheafification hypotheses on the slice sites discharged:
every slice of the big category of schemes over `S` is essentially small, so abelian presheaves
on it have a sheafification whose weak equivalences are the locally bijective maps. -/
@[stacks 0GNC "part (6)"]
theorem isQuasicoherentOnSite_internalHomSheaf (τ : SiteKind)
    (F G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O))
    [SheafOfModules.IsQuasicoherentOnSite F] [SheafOfModules.IsQuasicoherentOnSite G]
    [SheafOfModules.IsFiniteLocallyFree.{u, u, u + 1} F] :
    (RingedSite.internalHomSheaf (baseRingedSite B S hS τ) F G).IsQuasicoherentOnSite :=
  RingedSite.internalHomSheaf_isQuasicoherent (baseRingedSite B S hS τ) F G

end BigFppfOver

end AlgebraicGeometry

end
