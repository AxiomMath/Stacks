module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.QcohGlueAssembly
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.QcohGlueEffectivity
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.FpqcEffectiveUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.FibredSiteColimits

/-!
# The quasi-coherent colimit cluster over the gluing datum alone

The colimit results of Stacks 06WV, 06WN and 0GNE on the associated fppf site of a category
fibred in groupoids were carried over three separate inputs: essential surjectivity of
`𝓕 ↦ 𝓕^a` at every base, full faithfulness of that functor, and quasi-coherence of its values.
The last two are now theorems, and the first reduces — by
`AlgebraicGeometry.BigFppfOver.forall_quasicoherentIsEssImageAssociatedModule_of_isEffective` —
to the effectivity half of Stacks 023T together with the gluing datum of Stacks 03DX (1).
Effectivity is now also a theorem, for an arbitrary fpqc covering family and at an arbitrary
index universe
(`AlgebraicGeometry.QuasicoherentDescentData.isEffective_fpqcPrecoverage`,
`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherent/FpqcEffectiveUnconditional.lean:63`).

The two steps of that reduction — effectivity at index universe `u + 1` and essential
surjectivity of `𝓕 ↦ 𝓕^a` at every base over the gluing datum — are
`AlgebraicGeometry.BigFppfOver.isEffective_fpqcPrecoverage_siteIndex` and
`AlgebraicGeometry.BigFppfOver.forall_quasicoherentIsEssImageAssociatedModule_of_descentDatum`
of `StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/QcohGlueEffectivity.lean`, which this
file imports.

So this file restates the cluster over
`AlgebraicGeometry.BigFppfOver.AssociatedModuleGlueDescentDatum` and nothing else.  That Prop is
the one remaining residue of the whole group, and the reduction is what makes it so: before it,
the residue was a set of four conditions of which three were already discharged somewhere else
in the tree, which is not a thing a reader can check.

## Main results

* `AlgebraicGeometry.FibredSite.preservesFiniteColimits_quasicoherentInclusion_of_glueDatum`:
  **Stacks 06WV (3)** over the gluing datum alone.
* `AlgebraicGeometry.FibredSite.colimits_quasicoherentModules_of_glueDatum`:
  **Stacks 06WN (1)** over the gluing datum alone.
* `AlgebraicGeometry.FibredSite.closedUnderColimitsOfSize_quasicoherentModules_of_glueDatum`:
  the closure hypothesis `SheafOfModules.ClosedUnderColimitsOfSize` of the fibred site, over the
  gluing datum alone.  Nothing in either tree proved that hypothesis before; every consumer
  carried it.

## Implementation notes

**Nothing here is tagged, and that is forced.** Every statement below carries the gluing datum as
a hypothesis, and a hypothesis is part of a citation: a tag on any of them would claim the source
result while assuming an unproved input.  The tags belong on the hypothesis-free forms, which is
why these are stated so that discharging the single remaining Prop places them with no change to
any proof here.

The universe instantiation is the only thing to watch.
`AlgebraicGeometry.BigFppfOver.AssociatedModuleGlueDescentDatum` quantifies over covering
families of the big fppf site of `S`, whose index type lives in `Type (u + 1)`, and so the
effectivity input is needed at `PreZeroHypercover.{u + 1}`.  Chain A supplies it there because
`…isEffective_fpqcPrecoverage` is polymorphic in the index universe; an earlier effectivity
statement of this library was fixed at `Type u` and would not have fitted, which is the reason
that generalization was worth making.

## References

* [Stacks Project, Tag 06WV](https://stacks.math.columbia.edu/tag/06WV)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 0GNE](https://stacks.math.columbia.edu/tag/0GNE)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] [EssentiallySmall.{u} 𝒳]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- **The closure hypothesis of the fibred site, over the gluing datum alone.**  Closure of
quasi-coherence under colimits of every shape `K : Type u` on the associated fppf site of an
essentially small category fibred in groupoids.

Every consumer in this cluster carried this as a hypothesis and nothing in either tree concluded
it; this is the first statement of it over an input that is not itself a colimit-closure
assumption. -/
public theorem closedUnderColimitsOfSize_quasicoherentModules_of_glueDatum
    (hD : ∀ (T : Scheme.{u}) (hT : B.Contains T),
      BigFppfOver.AssociatedModuleGlueDescentDatum B T hT) :
    SheafOfModules.ClosedUnderColimitsOfSize.{u, u + 1, u, u, u}
      (ringStructureSheafCore B S hS p hp .fppf) :=
  closedUnderColimitsOfSize_quasicoherentModules_of_surjective B S hS p hp
    (BigFppfOver.forall_quasicoherentIsEssImageAssociatedModule_of_descentDatum B hD)

/-- **Stacks 06WN (1) for the ambient category `Mod(𝒪_𝒳)`, over the gluing datum alone**: the
quasi-coherent modules on the associated fppf site of an essentially small category fibred in
groupoids have all colimits indexed at the size of the site, and the inclusion into all module
sheaves preserves them. -/
public theorem colimits_quasicoherentModules_of_glueDatum
    (hD : ∀ (T : Scheme.{u}) (hT : B.Contains T),
      BigFppfOver.AssociatedModuleGlueDescentDatum B T hT) :
    HasColimitsOfSize.{u, u} (quasicoherentModules.{u, u + 1, u, u} B S hS p hp) ∧
      PreservesColimitsOfSize.{u, u}
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          (ringStructureSheafCore B S hS p hp .fppf)).ι :=
  colimits_quasicoherentModules_of_surjective B S hS p hp
    (BigFppfOver.forall_quasicoherentIsEssImageAssociatedModule_of_descentDatum B hD)

/-- **Stacks 06WV (3), right exactness of the inclusion, over the gluing datum alone**: the
inclusion `QCoh(𝒪_𝒳) ⟶ Mod(𝒪_𝒳)` of the quasi-coherent modules on the associated fppf site of an
essentially small category fibred in groupoids into all module sheaves preserves finite
colimits.

This is the site Stacks 06WV (3) is stated for, and the statement is the whole of that clause
over the one remaining Prop of the cluster. -/
public theorem preservesFiniteColimits_quasicoherentInclusion_of_glueDatum
    (hD : ∀ (T : Scheme.{u}) (hT : B.Contains T),
      BigFppfOver.AssociatedModuleGlueDescentDatum B T hT) :
    PreservesFiniteColimits
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (ringStructureSheafCore B S hS p hp .fppf)).ι :=
  preservesFiniteColimits_quasicoherentInclusion_of_surjective B S hS p hp
    (BigFppfOver.forall_quasicoherentIsEssImageAssociatedModule_of_descentDatum B hD)

/-- **Stacks 0GNE (1), the existence half, over the gluing datum alone**: the quasi-coherent
modules on the associated fppf site have finite colimits.  This is the finite-shape case of
`AlgebraicGeometry.FibredSite.colimits_quasicoherentModules_of_glueDatum`. -/
public theorem hasFiniteColimits_quasicoherentModules_of_glueDatum
    (hD : ∀ (T : Scheme.{u}) (hT : B.Contains T),
      BigFppfOver.AssociatedModuleGlueDescentDatum B T hT) :
    HasFiniteColimits (quasicoherentModules.{u, u + 1, u, u} B S hS p hp) :=
  hasFiniteColimits_quasicoherentModules B S hS p hp
    (closedUnderColimitsOfSize_quasicoherentModules_of_glueDatum B S hS p hp hD)

end FibredSite

end AlgebraicGeometry

end
