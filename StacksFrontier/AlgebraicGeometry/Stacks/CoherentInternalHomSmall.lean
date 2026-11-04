module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherenceNotionComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentInternalHom
public import StacksFrontier.AlgebraicGeometry.Topologies.CoherentInternalHomSmallOnSite

/-!
# Coherence of the small internal Hom on an algebraic stack

Let `𝒳` be an algebraic stack, `ℱ` an `𝒪_𝒳`-module and `𝒢` an `𝒪_𝒳`-module coherent in the
sectionwise sense of Stacks 03DL(8).  This file proves that the internal Hom `𝓗om_{𝒪_𝒳}(ℱ, 𝒢)`
of Stacks 03EM, read at module universe `u` through
`AlgebraicGeometry.RingedSite.internalHomSheafSmall`, is coherent, under the source's own
hypothesis on `ℱ`.

## Main results

* `AlgebraicGeometry.Stack.isCoherentOnSite_internalHomSheafSmall`: the internal Hom out of an
  `O_X`-module of finite presentation into a Stacks 03DL(8)-coherent one is Stacks
  03DL(8)-coherent, with no hypothesis on the stack beyond being an algebraic stack.
* `AlgebraicGeometry.Stack.isCoherent_internalHomSheafSmall`: **Stacks 0GRD with the source's own
  hypothesis on the first argument**, that it be coherent in the sense of Stacks 0GR6, and the
  hypothesis on the second argument strengthened to Stacks 03DL(8) coherence.

## Implementation notes

`AlgebraicGeometry.Stack.isCoherent_internalHomSheaf` of
`StacksFrontier.AlgebraicGeometry.Stacks.CoherentInternalHom` asks the first argument to be finite
locally free, because over an object on which it is free the internal Hom is a finite product of
copies of the second argument.  For a first argument that is merely of finite presentation the
same argument gives that the internal Hom is locally a *kernel* of a map between finite products
of copies of the second argument,
`AlgebraicGeometry.RingedSite.exists_internalHomSheaf_iso_kernel`, and Stacks 03DL(8) coherence
of the second argument, taken as a hypothesis, is closed under those finite products and that
kernel, by `Stacks.SheafOfModules.isCoherentOnSite_piFin` and
`Stacks.SheafOfModules.isCoherentOnSite_kernel`.  The general-site statement is
`AlgebraicGeometry.RingedSite.isCoherentOnSite_internalHomSheafSmall` of
`StacksFrontier.AlgebraicGeometry.Topologies.CoherentInternalHomSmallOnSite`, which needs the fppf
site to be essentially small.  What separates this from Stacks 0GRD is the hypothesis on the
second argument, Stacks 03DL(8) coherence rather than Stacks 0GR6 coherence and strictly stronger
by `StacksFrontier.AlgebraicGeometry.Stacks.CoherenceNotionComparison`, together with the source's
object, the quasi-coherator's value on the internal Hom.

## References

* [Stacks Project, Tag 0GRD](https://stacks.math.columbia.edu/tag/0GRD)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 0GR6](https://stacks.math.columbia.edu/tag/0GR6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u t

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0GRD for the internal Hom of Stacks 03EM, with the source's own hypothesis on `ℱ`
and a strengthened one on `𝒢`.**  Let `𝒳` be an algebraic stack, let `ℱ` be an `𝒪_𝒳`-module of
finite presentation — which on a locally Noetherian `𝒳` is exactly coherence in the sense of
Stacks 0GR6, by `AlgebraicGeometry.Stack.isCoherent_iff_isCoherentModule` — and let `𝒢` be
coherent in the sectionwise sense of Stacks 03DL(8).  Then the internal Hom
`𝓗om_{𝒪_𝒳}(ℱ, 𝒢)`, read at module universe `u` through
`AlgebraicGeometry.RingedSite.internalHomSheafSmall`, is coherent in the sense of
Stacks 03DL(8).

This is `AlgebraicGeometry.RingedSite.isCoherentOnSite_internalHomSheafSmall` on the fppf
associated ringed site of `𝒳`, whose hypotheses on the slices of the topology are
`AlgebraicGeometry.FibredSite.hasWeakSheafify_over` and
`AlgebraicGeometry.FibredSite.wEqualsLocallyBijective_over` and whose essential smallness is
`AlgebraicGeometry.Stack.essentiallySmall_obj_algebraicStack`.  No hypothesis on `𝒳` beyond
being an algebraic stack is used. -/
theorem isCoherentOnSite_internalHomSheafSmall (𝒳 : AlgebraicStacks.{u, t} B S hS)
    [hsm : EssentiallySmall.{u} 𝒳.val.val.obj]
    (ℱ 𝒢 : SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl))
    (hℱ : ℱ.IsFinitePresentationOnSite)
    (h𝒢 : SheafOfModules.IsCoherentOnSite 𝒢) :
    SheafOfModules.IsCoherentOnSite
      (@RingedSite.internalHomSheafSmall.{u, u, u + 1, u}
        (FibredSite.ringedSite B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
          SiteKind.fppf) hsm ℱ 𝒢) := by
  have h1 (x : 𝒳.val.val.obj) := FibredSite.hasWeakSheafify_over B S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids SiteKind.fppf x
  have h2 (x : 𝒳.val.val.obj) :=
    FibredSite.wEqualsLocallyBijective_over B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids SiteKind.fppf x
  exact @RingedSite.isCoherentOnSite_internalHomSheafSmall.{u + 1, u, u}
    (FibredSite.ringedSite B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids SiteKind.fppf)
    hsm h1 h2 ℱ 𝒢 hℱ h𝒢

/-- **Stacks 0GRD for the internal Hom of Stacks 03EM, with the tag's own hypothesis on `ℱ`.**
Let `𝒳` be a locally Noetherian algebraic stack, let `ℱ` be a coherent `𝒪_𝒳`-module in the sense
of Stacks 0GR6 and let `𝒢` be coherent in the sectionwise sense of Stacks 03DL(8).  Then the
internal Hom `𝓗om_{𝒪_𝒳}(ℱ, 𝒢)` is a coherent `𝒪_𝒳`-module in the sense of Stacks 0GR6.

Two things still separate this from Stacks 0GRD, and the attribute names both; but the
hypothesis on the *first* argument is now the source's own, where
`AlgebraicGeometry.Stack.isCoherent_internalHomSheaf` asks it to be finite locally free.  What
remains is the hypothesis on the second argument, strengthened from Stacks 0GR6-coherence to the
sectionwise coherence of Stacks 03DL(8) — it is the coherence that
`Stacks.SheafOfModules.isCoherentOnSite_piFin` and
`Stacks.SheafOfModules.isCoherentOnSite_kernel` are closed under, and it implies but is not
implied by Stacks 0GR6-coherence, see
`StacksFrontier.AlgebraicGeometry.Stacks.CoherenceNotionComparison` — and the source's object,
which is not this internal Hom but its image under the quasi-coherator; see the module
documentation. -/
@[stacks 0GRD "the coherence of the internal Hom of Stacks 03EM itself, for a first argument \
satisfying the source's own condition of coherence in the sense of Stacks 0GR6; the condition \
on the second argument is strengthened to the sectionwise coherence of Stacks 03DL(8), which \
implies Stacks 0GR6-coherence and is not implied by it; and the source's object is the image \
hom(F, G) of this one under the quasi-coherator of Stacks 0GQN, which is not this statement's \
object"]
theorem isCoherent_internalHomSheafSmall (𝒳 : AlgebraicStacks.{u, t} B S hS)
    [hsm : EssentiallySmall.{u} 𝒳.val.val.obj]
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    (ℱ 𝒢 : SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl))
    (hℱ : IsCoherent B S hS 𝒳 ℱ)
    (h𝒢 : SheafOfModules.IsCoherentOnSite 𝒢) :
    IsCoherent B S hS 𝒳
      (@RingedSite.internalHomSheafSmall.{u, u, u + 1, u}
        (FibredSite.ringedSite B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
          SiteKind.fppf) hsm ℱ 𝒢) :=
  isCoherent_of_isCoherentOnSite B S hS 𝒳 h𝒳 _
    (isCoherentOnSite_internalHomSheafSmall B S hS 𝒳 ℱ 𝒢 hℱ.isFinitePresentationOnSite h𝒢)

end AlgebraicGeometry.Stack

end
