module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAffineQuasicoherentVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleSheafHomUnit
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.RestrictionUnivLE

/-!
# The first cohomology of the internal hom out of the structure sheaf vanishes

Let `T` be an affine scheme and `𝓖` a quasi-coherent `𝒪`-module on the small étale site of `T`
of Stacks 021B.  The first cohomology of `𝓗om_𝒪(𝒪, 𝓖)` vanishes.

This is the hypothesis that
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/InternalHomAffineVanishing.lean` carried under the
name `h03DW`, and it is the last input of Stacks 061J.  Two things discharge it.  The internal
hom out of the structure sheaf is the universe lift of `𝓖`
(`AlgebraicGeometry.SmallEtale.toSheafSheafHomUnitIso`), and a quasi-coherent `𝒪`-module on the
small étale site is the associated module of a quasi-coherent module on `T`
(Stacks 03DX (2), `AlgebraicGeometry.SmallEtale.quasicoherentIsEssImageAssociatedModule`), whose
lifted associated sheaf has vanishing first cohomology on an affine
(`AlgebraicGeometry.SmallEtale.subsingleton_sheafH_one_uliftFunctor_associatedAbelianSheaf`,
Stacks 03DW clause (2) with Stacks 01XB).

## Main results

* `AlgebraicGeometry.SmallEtale.subsingleton_sheafH_one_toSheafSheafHomUnit`: the vanishing,
  with no hypothesis beyond affineness of `T` and quasi-coherence of `𝓖`.  It is what
  `AlgebraicGeometry.SmallEtale.subsingleton_sheafH_one_sheafHom_unit` of
  `StacksFrontier/AlgebraicGeometry/EtaleCohomology/InternalHomAffineVanishing.lean` is proved
  from.

## Implementation notes

No `@[stacks 03DW]` attribute is carried here, and none should be: Stacks 03DW is a comparison
of cohomology in every degree and for five topologies, and it is already registered — on
`AlgebraicGeometry.smallEtaleQuasiCoherentGlobalCohomologyIso` for clause (2) at `τ = étale`, on
`AlgebraicGeometry.bigOverQuasiCoherentGlobalCohomologyIso` for clause (1), and on
`AlgebraicGeometry.BigFppfOver.hZeroBaseAssociatedModuleAddEquiv` for `q = 0`.  What is proved
here is one specialisation of it, in one spelling, and the name `h03DW` recorded where the input
came from rather than what the statement is.

`Stacks.Topology.hasExt_sheafOpens` is made a local instance: `CategoryTheory.HasExt` is an
`abbrev` for a universally quantified statement, so instance search unfolds it and never matches
a named lemma, and the Zariski-side `Ext` universe is carried as a hypothesis by
`AlgebraicGeometry.subsingleton_sheafH_smallEtaleAssociatedSheaf_of_isZero_hgroup` for that
reason.

## References

* [Stacks Project, Tag 061J](https://stacks.math.columbia.edu/tag/061J)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace AlgebraicGeometry.SmallEtale

attribute [local instance] Stacks.Topology.hasExt_sheafOpens

variable (B : BigEtaleSite.{u}) (T : Scheme.{u}) (hT : B.Contains T)
  [AlgebraicGeometry.IsAffine T]
  (G : SheafOfModules.{u} (structureSheaf B T hT)) [G.IsQuasicoherentOnSite]
  [HasSheafify (topology B T hT) AddCommGrpCat.{u + 1}]
  [HasExt.{w} (Sheaf (topology B T hT) AddCommGrpCat.{u + 1})]

/-- **The first cohomology of `𝓗om_𝒪(𝒪, 𝓖)` on the small étale site of an affine scheme
vanishes**, for a quasi-coherent `𝓖`.  This is the hypothesis `h03DW` of Stacks 061J, and it is
Stacks 03DW clause (2) together with Stacks 01XB in the only form that argument uses.

The internal hom out of the structure sheaf is the universe lift of `𝓖`; a quasi-coherent
`𝒪`-module on the site is an `Mᵃ` by Stacks 03DX (2); and the first cohomology of the lift of
`Mᵃ` vanishes on an affine. -/
theorem subsingleton_sheafH_one_toSheafSheafHomUnit :
    Subsingleton (Sheaf.H.{w}
      ((SheafOfModules.toSheaf (structureSheaf B T hT)).obj
        (sheafHom B T hT (SheafOfModules.unit (structureSheaf B T hT)) G)) 1) := by
  obtain ⟨M, ⟨e⟩⟩ := quasicoherentIsEssImageAssociatedModule B T hT G inferInstance
  have hM : M.obj.IsQuasicoherent := M.property
  have hvan := subsingleton_sheafH_one_uliftFunctor_associatedAbelianSheaf B T hT M.obj
  have hlift := (CategoryTheory.sheafCompose (topology B T hT)
      AddCommGrpCat.uliftFunctor.{u + 1, u}).mapIso
    ((SheafOfModules.toSheaf (structureSheaf B T hT)).mapIso e.symm)
  exact Stacks.CohomologyVanishing.subsingleton_ext_of_iso_target
    (toSheafSheafHomUnitIso B T hT G ≪≫ hlift).symm 1 hvan

end AlgebraicGeometry.SmallEtale

end
