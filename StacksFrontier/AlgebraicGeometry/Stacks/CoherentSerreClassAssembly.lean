module

public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceClosure
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentKernelCokernelLocallyNoetherian

/-!
# The Serre-class assembly for coherent modules on a locally Noetherian algebraic stack

Let `𝒳` be a locally Noetherian algebraic stack.  Stacks 0GRB asserts among other things that
`Coh(𝒪_𝒳)` is a Serre subcategory of `QCoh(𝒪_𝒳)`.  Mathlib packages a Serre subcategory as
`CategoryTheory.ObjectProperty.IsSerreClass`, which is four mixins: `ContainsZero`,
`IsClosedUnderSubobjects`, `IsClosedUnderQuotients` and `IsClosedUnderExtensions`.

This file assembles those mixins for `AlgebraicGeometry.Stack.coherentOnSiteModules`, coherence
read as the sectionwise condition of Stacks 03DL(8), and shows that **the whole Serre-class
assertion reduces to the subobject mixin alone**: closure under quotients is a consequence of
closure under subobjects together with the cokernel clause of Stacks 0GR9, because in an abelian
category an epimorphism is the cokernel of its kernel.  Closure under subobjects in turn reduces,
by Stacks 01BY (1), to the single assertion that a submodule of a coherent module is of finite
type, which is where local Noetherianity has to enter and which this library does not have for a
stack.

## Main results

* `AlgebraicGeometry.Stack.coherentOnSiteModules_isClosedUnderSubobjects_of_isFiniteType`:
  closure under subobjects, over the assertion that a submodule of a coherent module is of finite
  type.  This is Stacks 01BY (1) and needs no Noetherianity of its own.
* `AlgebraicGeometry.Stack.coherentOnSiteModules_isClosedUnderQuotients`: closure under
  quotients, over closure under subobjects.
* `AlgebraicGeometry.Stack.coherentOnSiteModules_isSerreClass`: **the Serre-class assertion of
  Stacks 0GRB, over closure under subobjects.**
* `AlgebraicGeometry.Stack.coherentOnSiteModules_isSerreClass_of_isFiniteType`: the same, over
  the finite-type assertion, which is the one mathematical input missing.

## Implementation notes

**Nothing here is tagged, and the two reasons are different.**  Every statement below carries a
hypothesis that this library does not discharge, so none of them proves the clause of Stacks 0GRB
outright.  Independently of that, the ambient abelian category here is `Mod(𝒪_𝒳)` and not
`QCoh(𝒪_𝒳)`: the source's Serre subcategory sits inside the quasi-coherent modules, and
`QCoh(𝒪_𝒳)` is not available as an abelian category in this library, quasi-coherence of a
subobject of a quasi-coherent module being Stacks 06WV (3), (7) and absent — the same gap
recorded in `StacksFrontier.AlgebraicGeometry.Stacks.CoherentSerreSubcategoryLocallyNoetherian` for
part (2).  Taken in `Mod(𝒪_𝒳)` the subobject mixin quantifies over monomorphisms whose source
need not be quasi-coherent, so it is *stronger* than the source's subobject clause; that is
harmless for the statements below, which assume it rather than prove it, but it is why a tag
could not be carried here even if the finite-type input were available.

**Which mixins were already present, and which are new.**  Two of the four are already proved in
`StacksFrontier.AlgebraicGeometry.Stacks.CoherentKernelCokernelLocallyNoetherian` and are reused
verbatim, not restated: `AlgebraicGeometry.Stack.coherentOnSiteModules_containsZero` for
`ContainsZero`, and `AlgebraicGeometry.Stack.coherentOnSiteModules_isClosedUnderExtensions`,
which is Stacks 0GRA, for `IsClosedUnderExtensions`.  Neither of the remaining two is available
there.  What that file proves for kernels and cokernels is
`ObjectProperty.IsClosedUnderKernels` and `ObjectProperty.IsClosedUnderCokernels`, both of which
assume *both* modules coherent; `IsClosedUnderSubobjects` and `IsClosedUnderQuotients` assume
coherence of one module only and are strictly stronger.  Neither holds for Stacks 03DL(8)
coherence over an arbitrary ringed site, and the same counterexample refutes both: over the
spectrum of a valuation ring of rank one which is not discrete the structure sheaf is coherent,
its maximal ideal is a submodule which is not of finite type, and the residue field is a quotient
which is not coherent, recorded in
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentSubquotientNoetherian`.  So the quotient mixin is
*not* a repackaging of the cokernel clause of Stacks 0GR9, and cannot be, every clause of that
tag being proved over an arbitrary ringed site with local Noetherianity bound to an unused
binder.

**Why the quotient mixin is nevertheless free.**  Given closure under subobjects, the kernel of
an epimorphism `p : ℱ ⟶ 𝒢` out of a coherent module is coherent, and `𝒢` is a cokernel of its
inclusion by `CategoryTheory.Abelian.epiIsCokernelOfKernel`; the cokernel clause of Stacks 0GR9
then applies with both of its modules coherent.  This is the same factorization that
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentSubquotient` performs for algebraic spaces, where
the two assertions of Stacks 07UD are likewise reduced to the finite-type assertion alone.

**Where the remaining input would come from.**  On an algebraic space the finite-type assertion is
proved: it is `AlgebraicGeometry.Space.isFiniteType_of_mono_of_isQuasicoherentOnSite` in
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentSubquotientNoetherian`, and local Noetherianity of
a chart of a locally Noetherian stack is
`AlgebraicGeometry.Stack.hasEtaleLocalProperty_isLocallyNoetherian_of_chart`.  What is missing is
the transport along a smooth surjective chart, which the source performs by quoting Stacks 07UD:
that needs Stacks 0GQC, the restriction of a quasi-coherent module along a 1-morphism being
quasi-coherent, which appears in this library only as the undischarged
`AlgebraicGeometry.Space.RestrictionPreservesQuasicoherent`, and it needs exactness properties of
that restriction which are not proved either.  The obstruction is recorded at length in
`StacksFrontier.AlgebraicGeometry.Stacks.CoherentSerreSubcategoryLocallyNoetherian`.

**The module universe is the universe `u` of the schemes, and `𝒳` is assumed essentially small
there**, as in `StacksFrontier.AlgebraicGeometry.Stacks.CoherentKernelCokernelLocallyNoetherian`:
`ObjectProperty.IsSerreClass` is defined only over an abelian category, and `Mod(𝒪_𝒳)` is abelian
exactly when sheafification of presheaves of abelian groups with sections in `u` exists on the
fppf site of `𝒳`, which `AlgebraicGeometry.Stack.hasSheafifyAddCommGrpCat_associatedTopology`
supplies from essential smallness.

## References

* [Stacks Project, Tag 0GRB](https://stacks.math.columbia.edu/tag/0GRB)
* [Stacks Project, Tag 0GRA](https://stacks.math.columbia.edu/tag/0GRA)
* [Stacks Project, Tag 0GR9](https://stacks.math.columbia.edu/tag/0GR9)
* [Stacks Project, Tag 0GR5](https://stacks.math.columbia.edu/tag/0GR5)
* [Stacks Project, Tag 0GR6](https://stacks.math.columbia.edu/tag/0GR6)
* [Stacks Project, Tag 0GQC](https://stacks.math.columbia.edu/tag/0GQC)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 02MO](https://stacks.math.columbia.edu/tag/02MO)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 06WV](https://stacks.math.columbia.edu/tag/06WV)
* [Stacks Project, Tag 07UD](https://stacks.math.columbia.edu/tag/07UD)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u t

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : AlgebraicStacks.{u, t} B S hS) [EssentiallySmall.{u} 𝒳.val.val.obj]

omit [EssentiallySmall.{u} 𝒳.val.val.obj] in
/-- **The subobject mixin, over the finite-type assertion.**  If every submodule of a coherent
`𝒪_𝒳`-module is of finite type, then the coherent `𝒪_𝒳`-modules are closed under subobjects.

Coherence is the sectionwise condition of Stacks 03DL(8) on the big fppf ringed site of `𝒳`, and
the content is Stacks 01BY (1) there, at
`Stacks.SheafOfModules.isCoherentOnSite_of_mono`: a monomorphism of sheaves of modules is
injective on sections, so the relations among a finite family of sections of the submodule are
the relations among their images, and the relations clause of coherence is inherited verbatim
from the ambient module.  Nothing beyond the finite-type hypothesis is needed, and in particular
no Noetherianity: the hypothesis is where local Noetherianity of `𝒳` would be used, and it is
false without it. -/
theorem coherentOnSiteModules_isClosedUnderSubobjects_of_isFiniteType
    (hft : ∀ {M N : SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids B.topology le_rfl)} (ι : M ⟶ N) [Mono ι],
      SheafOfModules.IsCoherentOnSite N →
        PresheafOfModules.IsFiniteType
          (associatedTopology B S hS 𝒳.val.val.p B.topology) M.val) :
    (coherentOnSiteModules.{u, t} B S hS 𝒳).IsClosedUnderSubobjects where
  prop_of_mono ι _ hN :=
    _root_.Stacks.SheafOfModules.isCoherentOnSite_of_mono ι hN (hft ι hN)

/-- **The quotient mixin, over the subobject mixin.**  If the coherent `𝒪_𝒳`-modules are closed
under subobjects then they are closed under quotients.

In an abelian category an epimorphism `p : ℱ ⟶ 𝒢` is a cokernel of the inclusion of its kernel,
by `CategoryTheory.Abelian.epiIsCokernelOfKernel`.  That kernel is coherent because it is a
subobject of the coherent `ℱ`, so the cokernel clause of Stacks 0GR9 applies with both of its
modules coherent and gives coherence of `𝒢`.  Local Noetherianity is the hypothesis of the source
and is passed only to that clause, which does not use it. -/
theorem coherentOnSiteModules_isClosedUnderQuotients
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    [(coherentOnSiteModules.{u, t} B S hS 𝒳).IsClosedUnderSubobjects] :
    (coherentOnSiteModules.{u, t} B S hS 𝒳).IsClosedUnderQuotients where
  prop_of_epi p _ hF :=
    have := coherentOnSiteModules_isClosedUnderCokernels.{u, t} B S hS 𝒳 h𝒳
    (coherentOnSiteModules.{u, t} B S hS 𝒳).prop_of_isColimit_cokernelCofork
      (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel p))
      ((coherentOnSiteModules.{u, t} B S hS 𝒳).prop_of_mono (kernel.ι p) hF) hF

/-- **The Serre-subcategory clause of Stacks 0GRB, over the subobject mixin.**  On a locally
Noetherian algebraic stack `𝒳`, the coherent `𝒪_𝒳`-modules are a Serre class in `Mod(𝒪_𝒳)` as
soon as they are closed under subobjects.

The other three mixins of `CategoryTheory.ObjectProperty.IsSerreClass` are available
unconditionally: `AlgebraicGeometry.Stack.coherentOnSiteModules_containsZero` for the zero
object, `AlgebraicGeometry.Stack.coherentOnSiteModules_isClosedUnderExtensions`, which is
Stacks 0GRA, for extensions, and
`AlgebraicGeometry.Stack.coherentOnSiteModules_isClosedUnderQuotients` for quotients, that last
one being a consequence of the subobject hypothesis.  So the subobject mixin is the whole of what
is missing.

The statement carries no tag: it assumes its hardest clause, and the ambient abelian category is
`Mod(𝒪_𝒳)` rather than the `QCoh(𝒪_𝒳)` of the source; see the module documentation. -/
theorem coherentOnSiteModules_isSerreClass
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    [(coherentOnSiteModules.{u, t} B S hS 𝒳).IsClosedUnderSubobjects] :
    (coherentOnSiteModules.{u, t} B S hS 𝒳).IsSerreClass :=
  have := coherentOnSiteModules_containsZero.{u, t} B S hS 𝒳
  have := coherentOnSiteModules_isClosedUnderExtensions.{u, t} B S hS 𝒳 h𝒳
  have := coherentOnSiteModules_isClosedUnderQuotients.{u, t} B S hS 𝒳 h𝒳
  { }

/-- **The Serre-subcategory clause of Stacks 0GRB, over the finite-type assertion.**  On a
locally Noetherian algebraic stack `𝒳`, the coherent `𝒪_𝒳`-modules are a Serre class in
`Mod(𝒪_𝒳)` as soon as every submodule of a coherent `𝒪_𝒳`-module is of finite type.

This is the previous statement composed with
`AlgebraicGeometry.Stack.coherentOnSiteModules_isClosedUnderSubobjects_of_isFiniteType`, and it
isolates the single mathematical input the clause is missing.  That input is the one place where
local Noetherianity of `𝒳` carries weight, it is false without it, and its analogue for algebraic
spaces is proved: `AlgebraicGeometry.Space.isFiniteType_of_mono_of_isQuasicoherentOnSite`.  The
statement carries no tag; see the module documentation. -/
theorem coherentOnSiteModules_isSerreClass_of_isFiniteType
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    (hft : ∀ {M N : SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids B.topology le_rfl)} (ι : M ⟶ N) [Mono ι],
      SheafOfModules.IsCoherentOnSite N →
        PresheafOfModules.IsFiniteType
          (associatedTopology B S hS 𝒳.val.val.p B.topology) M.val) :
    (coherentOnSiteModules.{u, t} B S hS 𝒳).IsSerreClass :=
  have := coherentOnSiteModules_isClosedUnderSubobjects_of_isFiniteType.{u, t} B S hS 𝒳 hft
  coherentOnSiteModules_isSerreClass.{u, t} B S hS 𝒳 h𝒳

end AlgebraicGeometry.Stack

end
