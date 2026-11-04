module

public import Mathlib.CategoryTheory.Abelian.Subobject
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EssentiallySmallSiteSmallness
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.EffectiveGlueAgreementTransport
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.FibredSiteColimits
public import StacksFrontier.CategoryTheory.WellPowered.FullyFaithful

/-!
# The inputs of the special adjoint functor theorem for `QCoh(𝒪_𝒳)`

The coherator of **Stacks 0778** and of **Stacks 0781** part (2) is built in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/Coherator.lean` from the special adjoint
functor theorem, over hypotheses on `QCoh(𝒪_𝒳)`: that quasi-coherence is closed under colimits,
that `QCoh(𝒪_𝒳)` is locally small and well-copowered, and that it has a separator.  This file
proves the first three, at section universe `u`, for every essentially `u`-small category fibred
in groupoids over the big fppf site; that covers every algebraic stack, by
`AlgebraicGeometry.Stack.essentiallySmall_obj_algebraicStack`.

## Main results

* `AlgebraicGeometry.FibredSite.closedUnderColimitsOfSize_quasicoherentModules`: quasi-coherence
  on the associated fppf site is closed under colimits indexed at the universe of the site.  This
  is the hypothesis `hclosed` of the coherator, and the mathematical half of **Stacks 06WN**
  part (1).
* `AlgebraicGeometry.FibredSite.locallySmall_quasicoherentModules`: `QCoh(𝒪_𝒳)` is locally
  `u`-small (`hls`).
* `AlgebraicGeometry.FibredSite.wellPowered_op_quasicoherentModules`: `QCoh(𝒪_𝒳)` is
  well-copowered at `u` (`hwp`).

## Implementation notes

*Closure under colimits* is
`AlgebraicGeometry.FibredSite.closedUnderColimitsOfSize_quasicoherentModules_of_surjective` with
its one hypothesis, the essential surjectivity half of **Stacks 03DX** (1) at every scheme of the
site, discharged by `AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule'`.

*Local smallness.*  A morphism of quasi-coherent modules is a morphism of module sheaves on a site
whose objects lie in `Type (u + 1)`; it is determined by its components at a small set of
representatives, by `PresheafOfModules.locallySmall_of_essentiallySmall`, and the forgetful
functor to presheaves of modules is faithful.

*Well-copoweredness.*  The category of all module sheaves on the site is abelian and well-powered
at `u` (`SheafOfModules.wellPowered_of_essentiallySmall`), so it is well-copowered at `u` by
`CategoryTheory.Abelian.wellPowered_opposite`.  The inclusion of `QCoh(𝒪_𝒳)` is fully faithful
and preserves colimits, hence epimorphisms, so a quotient of a quasi-coherent module in
`QCoh(𝒪_𝒳)` is determined by the quotient of all module sheaves it gives, by
`Stacks.WellPoweredTransfer.wellPowered_of_fullyFaithful` applied to the opposite functor.

## References

* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 0781](https://stacks.math.columbia.edu/tag/0781)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] [EssentiallySmall.{u} 𝒳]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- **Quasi-coherence on the associated fppf site of `𝒳` is closed under colimits** indexed at
the universe of the site, for an essentially small category fibred in groupoids `𝒳`.  This is
the hypothesis `hclosed` of the coherators of **Stacks 0778** and **Stacks 0781** part (2), and
the mathematical half of **Stacks 06WN** part (1). -/
theorem closedUnderColimitsOfSize_quasicoherentModules :
    SheafOfModules.ClosedUnderColimitsOfSize.{u, u + 1, u, u, u}
      (ringStructureSheafCore B S hS p hp .fppf) :=
  closedUnderColimitsOfSize_quasicoherentModules_of_surjective B S hS p hp
    fun T hT => BigFppfOver.quasicoherentIsEssImageAssociatedModule' B T hT

/-- The category of module sheaves on the associated fppf site of `𝒳` is locally `u`-small. -/
private theorem locallySmall_sheafOfModules :
    LocallySmall.{u} (SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf)) :=
  have := PresheafOfModules.locallySmall_of_essentiallySmall.{u}
    (ringStructureSheafCore B S hS p hp .fppf).obj
  locallySmall_of_faithful
    (SheafOfModules.forget (ringStructureSheafCore B S hS p hp .fppf))

/-- **`QCoh(𝒪_𝒳)` is locally `u`-small**, for an essentially small category fibred in groupoids
`𝒳`: a morphism of module sheaves is determined by its components at a small set of
representatives of the objects of the site. -/
theorem locallySmall_quasicoherentModules :
    LocallySmall.{u} (quasicoherentModules.{u, u + 1, u, u} B S hS p hp) :=
  have := locallySmall_sheafOfModules B S hS p hp
  inferInstance

/-- **`QCoh(𝒪_𝒳)` is well-copowered at `u`**, for an essentially small category fibred in
groupoids `𝒳`.  All module sheaves on the associated fppf site form an abelian category which is
well-powered at `u`, hence well-copowered; the inclusion of `QCoh(𝒪_𝒳)` is fully faithful and
preserves epimorphisms, because it preserves colimits, so it reflects the order on quotients. -/
theorem wellPowered_op_quasicoherentModules :
    letI := locallySmall_quasicoherentModules B S hS p hp
    WellPowered.{u} (quasicoherentModules.{u, u + 1, u, u} B S hS p hp)ᵒᵖ := by
  let := locallySmall_quasicoherentModules B S hS p hp
  let := locallySmall_sheafOfModules B S hS p hp
  let : HasSheafify (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite _ _
  let : (BigFppfOver.associatedTopology B S hS p .fppf).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  let := SheafOfModules.wellPowered_of_essentiallySmall.{u}
    (ringStructureSheafCore B S hS p hp .fppf)
  let ι := (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    (ringStructureSheafCore B S hS p hp .fppf)).ι
  have : PreservesColimitsOfSize.{u, u} ι :=
    preservesColimitsOfSize_quasicoherentInclusion B S hS p hp
      (closedUnderColimitsOfSize_quasicoherentModules B S hS p hp)
  have : PreservesColimitsOfSize.{0, 0} ι := preservesColimitsOfSize_shrink ι
  have : ι.op.PreservesMonomorphisms :=
    ⟨fun f _ => (op_mono_iff (ι.map f.unop)).2 (ι.map_epi f.unop)⟩
  exact Stacks.WellPoweredTransfer.wellPowered_of_fullyFaithful ι.op

end AlgebraicGeometry.FibredSite

end
