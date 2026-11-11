module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentTopologiesTwo.InternalHom
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentModules
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.InternalHom
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite

/-!
# Coherence of an internal Hom on a locally Noetherian algebraic stack

Let `𝒳` be a locally Noetherian algebraic stack.  Stacks 0GRD asserts that the quasi-coherent
internal hom `hom(ℱ, 𝒢)` of Stacks 0GQN is a coherent `𝒪_𝒳`-module as soon as `ℱ` and `𝒢` are
coherent.  What is proved here is the finite locally free case of that statement for the
internal Hom `𝓗om_{𝒪_𝒳}(ℱ, 𝒢)` of Stacks 03EM itself: on the big fppf site of `𝒳`, the internal
Hom from a finite locally free module into a coherent module is coherent.

See the implementation notes for what separates this from Stacks 0GRD.  Stacks 0GRD itself, about
the object `hom(ℱ, 𝒢)` the source's statement names and for coherent `ℱ` and `𝒢`, is
`AlgebraicGeometry.Stack.FlatFppf.isCoherent_coheratorInternalHom` of
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/CoheratorInternalHomCoherent.lean`.

## Main results

* `AlgebraicGeometry.Stack.isCoherent_internalHomSheaf`: on a locally Noetherian algebraic
  stack the internal Hom of Stacks 03EM from a finite locally free `𝒪_𝒳`-module into a coherent
  `𝒪_𝒳`-module is coherent in the sense of Stacks 0GR6.
* `AlgebraicGeometry.Stack.isCoherentModule_internalHomSheaf`: the same conclusion read as
  Stacks 0GR5(2), finite presentation on the big fppf site, which is what the proof produces.

## Implementation notes

**Which internal Hom.**  The source's `hom(ℱ, 𝒢)` is *not* the internal Hom of Stacks 03EM but
its image `Q(𝓗om_{𝒪_𝒳}(ℱ, 𝒢))` under the quasi-coherator of Stacks 0778, which is formed, as in
Stacks 0GQN, by `AlgebraicGeometry.Stack.FlatFppf.coheratorInternalHom` of
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/CoheratorInternalHom.lean`, and whose
coherence is `AlgebraicGeometry.Stack.FlatFppf.isCoherent_coheratorInternalHom`.  The statements
below are about `AlgebraicGeometry.RingedSite.internalHomSheaf` on the fppf associated ringed site
of `𝒳`, the module `𝓗om_{𝒪_𝒳}(ℱ, 𝒢)` that `Q` is applied to, whose sections lie one universe
above those of `ℱ` and `𝒢`.

**Why the first argument is finite locally free and not merely coherent.**  The source's proof
restricts along a smooth surjection `U → 𝒳` from a scheme, where `hom(ℱ, 𝒢)` becomes the Hom
sheaf of the restrictions by Stacks 0GQT, and appeals to the case of algebraic spaces,
Stacks 07UE.  The route taken here is instead the direct one on the site, which is how the
quasi-coherence of the same object is proved in
`AlgebraicGeometry.RingedSite.internalHomSheaf_isQuasicoherent`: over an object on which `ℱ` is
free on a finite basis, evaluation at the basis identifies `𝓗om(ℱ, 𝒢)` with a finite coproduct
of copies of `𝒢`, which inherits a finite global presentation from `𝒢`.  For a first argument
that is merely coherent the same argument gives only that `𝓗om(ℱ, 𝒢)` is locally a *kernel* of
a map between finite coproducts of copies of `𝒢`, and concluding from that needs coherence of
`𝒢` in the sense of Stacks 03DL(8) on the fppf site of `𝒳`, which is how
`AlgebraicGeometry.Stack.isCoherent_internalHomSheafSmall` proceeds.  A finite locally free module
on a locally Noetherian algebraic stack *is* coherent, by
`AlgebraicGeometry.Stack.isCoherent_of_isFiniteLocallyFreeOnSite`, so the hypothesis below is a
strengthening of the source's hypothesis on `ℱ`.

**Local Noetherianity.**  It is an explicit hypothesis, as in the source, and is used only
through `AlgebraicGeometry.Stack.isCoherent_iff_isCoherentModule` to pass from finite
presentation on the site to the conjunction defining
`AlgebraicGeometry.Stack.IsCoherent`; the finite-presentation statement
`AlgebraicGeometry.Stack.isCoherentModule_internalHomSheaf` does not need it, for the reason
recorded in `StacksFrontier/AlgebraicGeometry/Stacks/CoherentLocallyNoetherian.lean`.

**Universes.**  The two arguments have their sections in the universe `u` of the coefficient
rings, which is where the internal Hom of the fppf associated ringed site of `𝒳` is available:
the internal Hom of two `SheafOfModules.{m}` on a `RingedSite.{u', v', w'}` has its sections in
`max u' v' m`, and `AlgebraicGeometry.RingedSite.internalHomSheaf_isQuasicoherent` and its
finite refinement ask the arguments to be at the ring universe.  The conclusion is therefore
about a module whose sections lie one universe up; both
`AlgebraicGeometry.Stack.IsCoherent` and `AlgebraicGeometry.Stack.IsCoherentModule` leave that
universe free, so no lift is needed.

## References

* [Stacks Project, Tag 0GRD](https://stacks.math.columbia.edu/tag/0GRD)
* [Stacks Project, Tag 0GQN](https://stacks.math.columbia.edu/tag/0GQN)
* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 0GR5](https://stacks.math.columbia.edu/tag/0GR5)
* [Stacks Project, Tag 0GR6](https://stacks.math.columbia.edu/tag/0GR6)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 0GNC](https://stacks.math.columbia.edu/tag/0GNC)
* [Stacks Project, Tag 07UE](https://stacks.math.columbia.edu/tag/07UE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u t

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0GR5(2) for an internal Hom.**  On an algebraic stack the internal Hom of
Stacks 03EM from a finite locally free `𝒪_𝒳`-module into an `𝒪_𝒳`-module of finite presentation
is of finite presentation on the big fppf site.

This is `AlgebraicGeometry.RingedSite.internalHomSheaf_isFinitePresentationOnSite` on the fppf
associated ringed site of `𝒳`, whose hypotheses on the slices of the topology are
`AlgebraicGeometry.FibredSite.hasWeakSheafify_over` and
`AlgebraicGeometry.FibredSite.wEqualsLocallyBijective_over`, and whose
local-generators form of finite local freeness is
`AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_of_isFiniteLocallyFreeOnSite`. -/
theorem isCoherentModule_internalHomSheaf (𝒳 : AlgebraicStacks.{u, t} B S hS)
    (ℱ 𝒢 : SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl))
    (hℱ : ℱ.IsFiniteLocallyFreeOnSite) (h𝒢 : 𝒢.IsFinitePresentationOnSite) :
    IsCoherentModule B S hS 𝒳
      ((FibredSite.ringedSite B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        SiteKind.fppf).internalHomSheaf ℱ 𝒢) := by
  have h1 (x : 𝒳.val.val.obj) := FibredSite.hasWeakSheafify_over B S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids SiteKind.fppf x
  have h2 (x : 𝒳.val.val.obj) :=
    FibredSite.wEqualsLocallyBijective_over B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids SiteKind.fppf x
  exact @RingedSite.internalHomSheaf_isFinitePresentationOnSite
    (FibredSite.ringedSite B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids SiteKind.fppf)
    ℱ 𝒢 h1 h2 h𝒢
    (@AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_of_isFiniteLocallyFreeOnSite
      𝒳.val.val.obj _ _ _ h1 h2 ℱ hℱ)

/-- **A variant of Stacks 0GRD for the internal Hom of Stacks 03EM, with a finite locally free
first argument.**  Let `𝒳` be a locally Noetherian algebraic stack, let `ℱ` be a finite locally free
`𝒪_𝒳`-module and let `𝒢` be a coherent `𝒪_𝒳`-module.  Then the internal Hom
`𝓗om_{𝒪_𝒳}(ℱ, 𝒢)` on the big fppf site of `𝒳` is a coherent `𝒪_𝒳`-module.

Two things separate this from Stacks 0GRD.  The source's object is not this internal Hom but its
image `hom(ℱ, 𝒢) = Q(𝓗om_{𝒪_𝒳}(ℱ, 𝒢))` under the quasi-coherator, for which Stacks 0GRD is
`AlgebraicGeometry.Stack.FlatFppf.isCoherent_coheratorInternalHom`; and the source asks only
that `ℱ` be coherent, where this asks that it be finite locally free — a strengthening, since a
finite locally free module on a locally Noetherian algebraic stack is coherent by
`AlgebraicGeometry.Stack.isCoherent_of_isFiniteLocallyFreeOnSite`.  See the module
documentation. -/
theorem isCoherent_internalHomSheaf (𝒳 : AlgebraicStacks.{u, t} B S hS)
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    (ℱ 𝒢 : SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl))
    (hℱ : ℱ.IsFiniteLocallyFreeOnSite) (h𝒢 : IsCoherent B S hS 𝒳 𝒢) :
    IsCoherent B S hS 𝒳
      ((FibredSite.ringedSite B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        SiteKind.fppf).internalHomSheaf ℱ 𝒢) :=
  (isCoherent_iff_isCoherentModule B S hS 𝒳 h𝒳 _).mpr
    (isCoherentModule_internalHomSheaf B S hS 𝒳 ℱ 𝒢 hℱ h𝒢.isFinitePresentationOnSite)

end AlgebraicGeometry.Stack

end
