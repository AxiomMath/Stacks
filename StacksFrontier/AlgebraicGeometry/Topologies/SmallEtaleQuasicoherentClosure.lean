module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentFiniteProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentGrothendieck
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelian
public import StacksFrontier.CategoryTheory.ObjectProperty.ColimitsFromCoproducts
public import StacksFrontier.CategoryTheory.ObjectProperty.ShortExact
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Closure properties of quasi-coherent modules on a site, and on the small étale site

Stacks 0GNB asserts six closure properties of the quasi-coherent modules on the small étale site
of a scheme: arbitrary direct sums, arbitrary colimits, kernels and cokernels, two-out-of-three
in a short exact sequence, tensor products, and internal Hom out of a finitely presented module.
Its proof transfers all six from the corresponding properties of quasi-coherent modules on the
scheme itself along the equivalence of Stacks 03DX.

This file collects what the six reduce to, and proves outright the part of that reduction which
is formal.  Quasi-coherence is `SheafOfModules.IsQuasicoherentOnSite`, Stacks 03DL(6), so the
statements are made over an arbitrary sheaf of rings on an arbitrary site and then instantiated
on the small étale site of a scheme.

## Main results

* `SheafOfModules.isQuasicoherentOnSite_isClosedUnderFiniteCoproducts` and
  `SheafOfModules.isQuasicoherentOnSite_coproduct`: a **finite** direct sum of quasi-coherent
  modules is quasi-coherent.  This is unconditional.
* `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_coproduct`: the same on the small étale
  site of a scheme, where the ambient category is abelian, so again unconditional.
* `SheafOfModules.isQuasicoherentOnSite_isClosedUnderColimitsOfShape` and
  `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_isClosedUnderColimitsOfShape`: closure
  under colimits of a given small shape, from closure under cokernels together with the two
  direct sums the shape needs.
* `SheafOfModules.IsQuasicoherentOnSite.of_shortExact_X₁`,
  `SheafOfModules.IsQuasicoherentOnSite.of_shortExact_X₃` and their small étale instances: the
  outer two cases of two-out-of-three, from closure under kernels and under cokernels.

## Implementation notes

**No `@[stacks 0GNB]` attribute is carried, and no clause of Stacks 0GNB is claimed here**:
every statement below is a *reduction*, carrying as a hypothesis the closure property it reduces
to, and a hypothesis is part of a citation.  The clauses they reduce are:

* `isQuasicoherentOnSite_coproduct` is the finite case of the direct-sum clause, 0GNB(1), and the
  clause is about an *arbitrary* direct sum: two quasi-coherent modules are presented on two
  possibly different coverings of an object, and a Grothendieck topology is closed under finite
  intersections of covering sieves but not under infinite ones.
* `isQuasicoherentOnSite_isClosedUnderColimitsOfShape` reduces the colimit clause, 0GNB(2), to the
  cokernel half of 0GNB(3) and to 0GNB(1) — a colimit is a coequalizer of two maps between two
  direct sums of the objects of the diagram.
* `of_shortExact_X₁` and `of_shortExact_X₃` reduce two of the three cases of the short exact
  sequence clause, 0GNB(4), to 0GNB(3); the third case, an extension of quasi-coherent modules, is
  not a consequence of 0GNB(3) and is Stacks 06VE(10).  On the small étale site of a scheme it is
  *exactly* 06VE(10) and nothing more:
  `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_shortExact_X₂_of_essImageExtension`
  derives it from that clause, and
  `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_iff_essImage_associatedModuleQcoh` shows
  the two statements are the same one.

**The clauses themselves are theorems, proved elsewhere and not by these reductions.**
Stacks 03DX (2) at `τ = étale` is proved, unconditionally, as
`AlgebraicGeometry.SmallEtale.quasicoherentIsEssImageAssociatedModule` and
`AlgebraicGeometry.SmallEtale.isEquivalence_associatedModuleQcohOnSite'` in
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit`, so the source's own
proof — transport along that equivalence — is available, and it is run in
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleQuasicoherentTransfer`:
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_of_isColimit_cofan` is 0GNB(1),
`…_of_isColimit` is 0GNB(2),
`…_of_isColimit_cokernelCofork` and `…_of_isLimit_kernelFork` are 0GNB(3), and
`…_shortExact_X₁`, `…_shortExact_X₃` are two of the three cases of 0GNB(4).  That route needs
neither Stacks 03DW nor the lift hypothesis of
`SheafOfModules.HasGlobalPresentation.of_isColimit_cokernelCofork_of_lift` in
`StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels`, which is what an earlier
version of these notes recorded as the single missing input; the statements below are kept
because they are site-independent and are the form in which an *arbitrary* ringed site, where no
such equivalence is available, can consume the closure properties.

The remaining two clauses of Stacks 0GNB are elsewhere and are not restated here, and both are
theorems.  The tensor product clause, 0GNB(5), is
`AlgebraicGeometry.SmallEtale.tensorSheaf_isQuasicoherentOnSite` in
`StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleQuasicoherentTensor`.  The internal Hom
clause, 0GNB(6), is about a source of *finite presentation* in the sense of 03DL(7), and it is
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_internalHomSheaf` in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleInternalHomFinitePresentation`.

Its route is the one these notes used to record as blocked, and both of its steps are carried
out.  Over an object on which the source is a cokernel of a map of finite free modules the
internal Hom into `G` is a kernel of a map between two finite products of `G`, and
`SheafOfModules.isQuasicoherentOnSite_isClosedUnderFiniteProducts` and the kernel half of
0GNB(3) are both unconditional on the small étale site of a scheme.

* *Exhibiting the internal Hom as that kernel is Stacks 03EN*, left exactness of the internal
  Hom in its first variable.  It is
  `AlgebraicGeometry.SmallEtale.isLimit_kernelFork_internalHomSheafPre` in
  `StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleInternalHomPresentation`, obtained
  from `AlgebraicGeometry.RingedSite.isLimit_kernelFork_internalHomPre`, whose universes are
  free, read down the universe lift of the module sections.  That is why
  `Stacks.SheafOfModules.InternalHom.ihomCokernelIsoKernel` in
  `StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SheafInternalHomFirstVariable` is not the
  route: it is stated over a ring sheaf `Sheaf J CommRingCat.{max u v}` on a site `C : Type u`
  with `Category.{v} C`, while the small étale ringed site of a scheme is
  `RingedSite.{u + 1, u, u}` with a `CommRingCat.{u}`-valued structure sheaf, so `max u v` is
  `u + 1` and that form cannot be instantiated here.
* *The presentation of 03DL(7) is only local*, so the kernel lives on a slice of the site, while
  the kernel clause of 0GNB(3) is a statement about the site itself.  The descent is
  `AlgebraicGeometry.SmallEtale.objRestrictInternalHomSheafIso` — the comparison of the internal
  Hom with its restriction to a slice,
  `Stacks.SheafOfModules.InternalHom.internalHomOverIso` (Stacks 0E8H, whose universes are
  unconstrained), followed by the transport along the localization equivalence identifying the
  slice at an object with the small étale site of the scheme of that object — together with
  `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_objRestrict_iff`.

For comparison, the algebraic-space analogue of the same clause, Stacks 03M1(6), is formalized only
for a *global* finite presentation and only over a hypothesis — see
`AlgebraicGeometry.Space.isQuasicoherentOnSite_smallEtaleInternalHom_of_presentation`, whose
`h03DX` is the Descent criterion at the relevant module universe.  On the small étale site of a
*scheme* that hypothesis is proved unconditionally
(`AlgebraicGeometry.SmallEtale.quasicoherentIsEssImageAssociatedModule`), which is what makes
both the global-presentation case and the local case — the clause itself — unconditional here.

The general statements take the existence of the relevant colimits in the ambient category of all
sheaves of modules as hypotheses, since `SheafOfModules.IsQuasicoherentOnSite` is deliberately
phrased without any sheafification instance.  On the small étale site of a scheme at module
universe `u` those hypotheses are discharged by
`StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelian`, so the small étale corollaries
carry only the closure properties that are genuinely missing.

## References

* [Stacks Project, Tag 0GNB](https://stacks.math.columbia.edu/tag/0GNB)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u v r m

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r})

/-- Quasi-coherence of sheaves of modules on a site is closed under finite direct sums. -/
@[ega "0 5.1.3" "special case", ega "I 4.1.1" "Direct sums: finite case"]
instance isQuasicoherentOnSite_isClosedUnderFiniteCoproducts
    [HasZeroObject (SheafOfModules.{m} R)] [HasFiniteCoproducts (SheafOfModules.{m} R)] :
    (isQuasicoherentOnSite.{u, v, r, m} R).IsClosedUnderFiniteCoproducts :=
  ObjectProperty.IsClosedUnderFiniteCoproducts.mk'

/-- A finite direct sum of quasi-coherent sheaves of modules on a site is quasi-coherent. -/
@[ega "0 5.1.3" "special case", ega "I 4.1.1" "Direct sums: finite case"]
theorem isQuasicoherentOnSite_coproduct [HasZeroObject (SheafOfModules.{m} R)]
    [HasFiniteCoproducts (SheafOfModules.{m} R)] {ι : Type*} [Finite ι]
    (F : ι → SheafOfModules.{m} R) [HasCoproduct F]
    (h : ∀ i, (F i).IsQuasicoherentOnSite) : (∐ F).IsQuasicoherentOnSite :=
  ObjectProperty.prop_coproduct (isQuasicoherentOnSite.{u, v, r, m} R) h

/-- Quasi-coherence of sheaves of modules on a site is closed under colimits of a small shape `K`
as soon as it is closed under cokernels and under the two direct sums indexed by the objects and
by the arrows of `K`. -/
theorem isQuasicoherentOnSite_isClosedUnderColimitsOfShape
    [HasCokernels (SheafOfModules.{m} R)] (K : Type w) [SmallCategory K]
    [HasColimitsOfShape (Discrete.{w} K) (SheafOfModules.{m} R)]
    [HasColimitsOfShape (Discrete.{w} (Σ p : K × K, p.1 ⟶ p.2)) (SheafOfModules.{m} R)]
    [(isQuasicoherentOnSite.{u, v, r, m} R).IsClosedUnderCokernels]
    [(isQuasicoherentOnSite.{u, v, r, m} R).IsClosedUnderColimitsOfShape (Discrete.{w} K)]
    [(isQuasicoherentOnSite.{u, v, r, m} R).IsClosedUnderColimitsOfShape
      (Discrete.{w} (Σ p : K × K, p.1 ⟶ p.2))] :
    (isQuasicoherentOnSite.{u, v, r, m} R).IsClosedUnderColimitsOfShape K :=
  ObjectProperty.IsClosedUnderColimitsOfShape.of_coproducts_and_cokernels _ K

variable {R}

/-- The kernel term of a short exact sequence of sheaves of modules on a site is quasi-coherent
when the other two terms are, provided quasi-coherence is closed under kernels. -/
theorem IsQuasicoherentOnSite.of_shortExact_X₁ [Balanced (SheafOfModules.{m} R)]
    [(isQuasicoherentOnSite.{u, v, r, m} R).IsClosedUnderKernels]
    {T : ShortComplex (SheafOfModules.{m} R)} (hT : T.ShortExact)
    (h₂ : T.X₂.IsQuasicoherentOnSite) (h₃ : T.X₃.IsQuasicoherentOnSite) :
    T.X₁.IsQuasicoherentOnSite :=
  ObjectProperty.prop_X₁_of_shortExact_of_isClosedUnderKernels _ hT h₂ h₃

/-- The quotient term of a short exact sequence of sheaves of modules on a site is quasi-coherent
when the other two terms are, provided quasi-coherence is closed under cokernels. -/
theorem IsQuasicoherentOnSite.of_shortExact_X₃ [Balanced (SheafOfModules.{m} R)]
    [(isQuasicoherentOnSite.{u, v, r, m} R).IsClosedUnderCokernels]
    {T : ShortComplex (SheafOfModules.{m} R)} (hT : T.ShortExact)
    (h₁ : T.X₁.IsQuasicoherentOnSite) (h₂ : T.X₂.IsQuasicoherentOnSite) :
    T.X₃.IsQuasicoherentOnSite :=
  ObjectProperty.prop_X₃_of_shortExact_of_isClosedUnderCokernels _ hT h₁ h₂

end SheafOfModules

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A finite direct sum of quasi-coherent sheaves of modules on the small étale site of a scheme
is quasi-coherent.  This is the finite case of the direct-sum clause of Stacks 0GNB. -/
theorem isQuasicoherentOnSite_coproduct {ι : Type*} [Finite ι]
    (F : ι → SheafOfModules.{u} (structureSheaf B S hS)) [HasCoproduct F]
    (h : ∀ i, (F i).IsQuasicoherentOnSite) : (∐ F).IsQuasicoherentOnSite :=
  SheafOfModules.isQuasicoherentOnSite_coproduct _ F h

/-- On the small étale site of a scheme, quasi-coherence is closed under colimits of a small
shape `K` as soon as it is closed under cokernels and under the two direct sums indexed by the
objects and by the arrows of `K`.  This is the reduction of the colimit clause of Stacks 0GNB to
its cokernel and direct-sum clauses. -/
theorem isQuasicoherentOnSite_isClosedUnderColimitsOfShape (K : Type u) [SmallCategory K]
    (hcok : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureSheaf B S hS)).IsClosedUnderCokernels)
    (hobj : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureSheaf B S hS)).IsClosedUnderColimitsOfShape (Discrete.{u} K))
    (harr : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureSheaf B S hS)).IsClosedUnderColimitsOfShape
        (Discrete.{u} (Σ p : K × K, p.1 ⟶ p.2))) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureSheaf B S hS)).IsClosedUnderColimitsOfShape K :=
  have := hcok
  have := hobj
  have := harr
  SheafOfModules.isQuasicoherentOnSite_isClosedUnderColimitsOfShape _ K

/-- The kernel term of a short exact sequence of modules on the small étale site of a scheme is
quasi-coherent when the other two terms are, provided quasi-coherence is closed under kernels.
This is the reduction of one case of the short exact sequence clause of Stacks 0GNB to its kernel
clause. -/
theorem isQuasicoherentOnSite_of_shortExact_X₁
    (hker : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureSheaf B S hS)).IsClosedUnderKernels)
    {T : ShortComplex (SheafOfModules.{u} (structureSheaf B S hS))} (hT : T.ShortExact)
    (h₂ : T.X₂.IsQuasicoherentOnSite) (h₃ : T.X₃.IsQuasicoherentOnSite) :
    T.X₁.IsQuasicoherentOnSite :=
  have := hker
  SheafOfModules.IsQuasicoherentOnSite.of_shortExact_X₁ hT h₂ h₃

/-- The quotient term of a short exact sequence of modules on the small étale site of a scheme is
quasi-coherent when the other two terms are, provided quasi-coherence is closed under cokernels.
This is the reduction of one case of the short exact sequence clause of Stacks 0GNB to its
cokernel clause. -/
theorem isQuasicoherentOnSite_of_shortExact_X₃
    (hcok : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureSheaf B S hS)).IsClosedUnderCokernels)
    {T : ShortComplex (SheafOfModules.{u} (structureSheaf B S hS))} (hT : T.ShortExact)
    (h₁ : T.X₁.IsQuasicoherentOnSite) (h₂ : T.X₂.IsQuasicoherentOnSite) :
    T.X₃.IsQuasicoherentOnSite :=
  have := hcok
  SheafOfModules.IsQuasicoherentOnSite.of_shortExact_X₃ hT h₁ h₂

end AlgebraicGeometry.SmallEtale

end
