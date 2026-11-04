module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentSiteAgreement

/-!
# Colimits of quasi-coherent modules on an algebraic stack

Let `𝒳` be an algebraic stack over `S`.  The category `QCoh(𝒪_𝒳)` of quasi-coherent modules on
the fppf site of `𝒳` has all (small) colimits, and they agree with the colimits computed in
`Mod(𝒪_𝒳)`.  In particular the inclusion `QCoh(𝒪_𝒳) → Mod(𝒪_𝒳)` is right exact.

The source proves this for any category fibred in groupoids over `(Sch/S)_fppf` (Stacks 06WN
(1)): quasi-coherence on `𝒳` is tested on the localizations `𝒳_fppf/x ≅ (Sch/U)_fppf`
(Stacks 06WI), restriction to a localization commutes with colimits, and on the big fppf site of
a scheme quasi-coherent modules are closed under colimits (Stacks 0GNC).  That general statement
is `AlgebraicGeometry.FibredSite.quasicoherentModules_colimits_siteAgreement`; this file reads
it on an algebraic stack and records the instances a consumer of `QCoh(𝒪_𝒳)` uses.

## Main results

* `AlgebraicGeometry.Stack.hasColimitsOfSize_quasicoherentModules` and
  `AlgebraicGeometry.Stack.preservesColimitsOfSize_quasicoherentInclusion`: the instances that
  `QCoh(𝒪_𝒳)` has colimits and that the inclusion preserves them.
* `AlgebraicGeometry.Stack.colimits_quasicoherentModules`: **Stacks 06WV (4)**.
* `AlgebraicGeometry.Stack.preservesFiniteColimits_quasicoherentInclusion`: the right
  exactness half of **Stacks 06WV (3)**.

## Implementation notes

"Colimits" are the colimits indexed by categories in the universe `u` of the schemes of the
site, which is the universe of the sets of sections of the modules involved; these are the small
colimits of the source.

## References

* [Stacks Project, Tag 06WV](https://stacks.math.columbia.edu/tag/06WV)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **`QCoh(𝒪_𝒳)` has all colimits**, for an algebraic stack `𝒳`. -/
instance hasColimitsOfSize_quasicoherentModules (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    HasColimitsOfSize.{u, u}
      (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids) :=
  FibredSite.hasColimitsOfSize_quasicoherentModules_of_isFiberedInGroupoids B S hS _ _

/-- **Colimits in `QCoh(𝒪_𝒳)` are colimits in `Mod(𝒪_𝒳)`**, for an algebraic stack `𝒳`: the
inclusion preserves all colimits. -/
instance preservesColimitsOfSize_quasicoherentInclusion (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    PreservesColimitsOfSize.{u, u}
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
          .fppf)).ι :=
  FibredSite.preservesColimitsOfSize_quasicoherentInclusion_of_isFiberedInGroupoids B S hS _ _

/-- For an algebraic stack `𝒳`, the category `QCoh(𝒪_𝒳)` has colimits, and they agree with
colimits in `Mod(𝒪_𝒳)`: the inclusion `QCoh(𝒪_𝒳) → Mod(𝒪_𝒳)` preserves them. -/
@[stacks 06WV "part (4): QCoh(𝒪_𝒳) has colimits and they agree with colimits in Mod(𝒪_𝒳)"]
theorem colimits_quasicoherentModules (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    HasColimitsOfSize.{u, u}
        (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
          𝒳.val.isFiberedInGroupoids) ∧
      PreservesColimitsOfSize.{u, u}
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
            .fppf)).ι :=
  ⟨inferInstance, inferInstance⟩

/-- **The inclusion `QCoh(𝒪_𝒳) → Mod(𝒪_𝒳)` is right exact**, for an algebraic stack `𝒳`: it
preserves finite colimits, because it preserves all colimits. -/
instance preservesFiniteColimits_quasicoherentInclusion (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    PreservesFiniteColimits
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
          .fppf)).ι :=
  PreservesColimitsOfSize.preservesFiniteColimits _

end AlgebraicGeometry.Stack

end
