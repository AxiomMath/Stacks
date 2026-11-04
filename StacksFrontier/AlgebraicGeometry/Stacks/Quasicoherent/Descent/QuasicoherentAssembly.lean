module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentColimitsUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentRightExact

/-!
# Colimits of quasi-coherent modules on fppf sites

The category of quasi-coherent modules on the big fppf site of a scheme, and on the associated
fppf site of an essentially small category fibred in groupoids, has colimits, and the inclusion
into all modules preserves them. At the big fppf site of `S` this holds over essential
surjectivity of `𝓕 ↦ 𝓕^a`; at the associated fppf site of `𝒳` it holds over essential
surjectivity at every scheme of `B` and the reduction step
`AlgebraicGeometry.FibredSite.ClosedUnderColimitsOfSizeOfBase`. Every "has colimits" is
`CategoryTheory.Limits.HasColimitsOfSize.{u, u}` and every "preserves colimits" is
`CategoryTheory.Limits.PreservesColimitsOfSize.{u, u}`, the index universe being the universe of
the site.

## Main definitions

* `AlgebraicGeometry.FibredSite.ClosedUnderColimitsOfSizeOfBase`: the reduction step of
  Stacks 06WN — if quasi-coherence is closed under colimits on the big fppf site of every scheme
  of `B`, then it is closed under colimits on the associated fppf site of `𝒳`.

## Main results

* `AlgebraicGeometry.BigFppfOver.colimits_quasicoherentOnSite'`: over essential surjectivity of
  `𝓕 ↦ 𝓕^a`, `QCoh((Sch/S)_fppf, 𝒪)` has colimits and the inclusion into all modules on
  `(Sch/S)_fppf` preserves them; this is Stacks 0GNE (1) for the ambient category
  `Mod((Sch/S)_fppf, 𝒪)`.
* `AlgebraicGeometry.FibredSite.closedUnderColimitsOfSize_quasicoherentModules_of_descent`:
  closure of quasi-coherence under colimits on the associated fppf site of `𝒳`, over the
  reduction step and essential surjectivity at every scheme of `B`.
* `AlgebraicGeometry.FibredSite.colimits_quasicoherentModules_of_descent`: over those two inputs,
  `QCoh(𝒪_𝒳)` has colimits and the inclusion into `Mod(𝒪_𝒳)` preserves them; this is
  Stacks 06WN (1) for the ambient category `Mod(𝒪_𝒳)`.
* `AlgebraicGeometry.FibredSite.hasFiniteColimits_quasicoherentModules_of_descent` and
  `AlgebraicGeometry.FibredSite.preservesFiniteColimits_quasicoherentInclusion_of_descent`: over
  those two inputs, `QCoh(𝒪_𝒳)` has finite colimits and the inclusion into `Mod(𝒪_𝒳)` preserves
  them, the right exactness of Stacks 06WV (3).

## References

* [Stacks Project, Tag 0GNE](https://stacks.math.columbia.edu/tag/0GNE)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 06WV](https://stacks.math.columbia.edu/tag/06WV)
* [Stacks Project, Tag 06WI](https://stacks.math.columbia.edu/tag/06WI)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0CN0](https://stacks.math.columbia.edu/tag/0CN0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Over essential surjectivity of `𝓕 ↦ 𝓕^a`, the category of quasi-coherent modules on the big
fppf site of `S` has all colimits indexed at the size of the site, and the inclusion into all
modules on `(Sch/S)_fppf` preserves them. -/
public theorem colimits_quasicoherentOnSite'
    (hsurj : QuasicoherentIsEssImageAssociatedModule B S hS) :
    HasColimitsOfSize.{u, u}
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          (structureSheaf B S hS)).FullSubcategory ∧
      PreservesColimitsOfSize.{u, u}
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          (structureSheaf B S hS)).ι :=
  ⟨hasColimitsOfSize_quasicoherentOnSite' B S hS hsurj,
    preservesColimitsOfSize_quasicoherentOnSite_ι' B S hS hsurj⟩

end BigFppfOver

namespace FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] [EssentiallySmall.{u} 𝒳]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- The reduction step of Stacks 06WN: if quasi-coherence of modules is closed under colimits on
the big fppf site of every scheme of `B`, then it is closed under colimits on the associated fppf
site of `𝒳`. -/
public abbrev ClosedUnderColimitsOfSizeOfBase : Prop :=
  (∀ (T : Scheme.{u}) (hT : B.Contains T),
      SheafOfModules.ClosedUnderColimitsOfSize.{u, u + 1, u, u, u}
        (BigFppfOver.structureSheaf B T hT)) →
    SheafOfModules.ClosedUnderColimitsOfSize.{u, u + 1, u, u, u}
      (ringStructureSheafCore B S hS p hp .fppf)

omit [EssentiallySmall.{u} 𝒳] in
/-- Closure of quasi-coherence under colimits of every shape `K : Type u` on the associated
fppf site of an essentially small category fibred in groupoids, over the reduction step of
Stacks 06WN and essential surjectivity of `𝓕 ↦ 𝓕^a` at every scheme of `B`. -/
public theorem closedUnderColimitsOfSize_quasicoherentModules_of_descent
    (hred : ClosedUnderColimitsOfSizeOfBase B S hS p hp)
    (hsurj : ∀ (T : Scheme.{u}) (hT : B.Contains T),
      BigFppfOver.QuasicoherentIsEssImageAssociatedModule B T hT) :
    SheafOfModules.ClosedUnderColimitsOfSize.{u, u + 1, u, u, u}
      (ringStructureSheafCore B S hS p hp .fppf) :=
  hred fun T hT ↦
    BigFppfOver.closedUnderColimitsOfSize_isQuasicoherentOnSite' B T hT (hsurj T hT)

/-- Over the reduction step of Stacks 06WN and essential surjectivity of `𝓕 ↦ 𝓕^a` at every
scheme of `B`, the category of quasi-coherent modules on the associated fppf site of an
essentially small category fibred in groupoids has all colimits indexed at the size of the site,
and the inclusion into all module sheaves on that site preserves them. -/
public theorem colimits_quasicoherentModules_of_descent
    (hred : ClosedUnderColimitsOfSizeOfBase B S hS p hp)
    (hsurj : ∀ (T : Scheme.{u}) (hT : B.Contains T),
      BigFppfOver.QuasicoherentIsEssImageAssociatedModule B T hT) :
    HasColimitsOfSize.{u, u} (quasicoherentModules.{u, u + 1, u, u} B S hS p hp) ∧
      PreservesColimitsOfSize.{u, u}
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          (ringStructureSheafCore B S hS p hp .fppf)).ι :=
  have hclosed := closedUnderColimitsOfSize_quasicoherentModules_of_descent B S hS p hp hred hsurj
  ⟨hasColimitsOfSize_quasicoherentModules B S hS p hp hclosed,
    preservesColimitsOfSize_quasicoherentInclusion B S hS p hp hclosed⟩

/-- Over the reduction step of Stacks 06WN and essential surjectivity of `𝓕 ↦ 𝓕^a` at every
scheme of `B`, the quasi-coherent modules on the associated fppf site of an essentially small
category fibred in groupoids have finite colimits. -/
public theorem hasFiniteColimits_quasicoherentModules_of_descent
    (hred : ClosedUnderColimitsOfSizeOfBase B S hS p hp)
    (hsurj : ∀ (T : Scheme.{u}) (hT : B.Contains T),
      BigFppfOver.QuasicoherentIsEssImageAssociatedModule B T hT) :
    HasFiniteColimits (quasicoherentModules.{u, u + 1, u, u} B S hS p hp) :=
  hasFiniteColimits_quasicoherentModules B S hS p hp
    (closedUnderColimitsOfSize_quasicoherentModules_of_descent B S hS p hp hred hsurj)

/-- Over the reduction step of Stacks 06WN and essential surjectivity of `𝓕 ↦ 𝓕^a` at every
scheme of `B`, the inclusion `QCoh(𝒪_𝒳) ⥤ Mod(𝒪_𝒳)` preserves finite colimits. -/
public theorem preservesFiniteColimits_quasicoherentInclusion_of_descent
    (hred : ClosedUnderColimitsOfSizeOfBase B S hS p hp)
    (hsurj : ∀ (T : Scheme.{u}) (hT : B.Contains T),
      BigFppfOver.QuasicoherentIsEssImageAssociatedModule B T hT) :
    PreservesFiniteColimits
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (ringStructureSheafCore B S hS p hp .fppf)).ι :=
  preservesFiniteColimits_quasicoherentInclusion B S hS p hp
    (closedUnderColimitsOfSize_quasicoherentModules_of_descent B S hS p hp hred hsurj)

end FibredSite

end AlgebraicGeometry

end
