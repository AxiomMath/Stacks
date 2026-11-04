module

public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.ReflexiveStalkCriterion.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Coherence of a dual module from a local kernel presentation, and Tag 0EBH

`StacksFrontier/AlgebraicGeometry/ReflexiveStalkCriterion/Basic.lean` states the adjunction of
[Stacks, Tag 0EBH](https://stacks.math.columbia.edu/tag/0EBH) under exactly one hypothesis: that
the dual of a coherent module on an integral locally Noetherian scheme is coherent.  That
hypothesis is [Stacks, Tag 01Y2](https://stacks.math.columbia.edu/tag/01Y2) at target the
structure sheaf, which the source reduces to
[Stacks, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ): the internal Hom out of a module
of finite presentation is, locally, the kernel of a map between two finite direct sums of copies
of the target.

This file performs the second half of that reduction, which is the half that is available.
`Stacks.SheafOfModules.isCoherent_of_locallyKernelFiniteCoproduct`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/CoherenceClosure.lean`) already derives coherence
of a sheaf of modules from a local kernel presentation over a coherent sheaf, and the structure
sheaf of a locally Noetherian scheme is coherent
(`Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent`).  Composing the two
turns Tag 0EBH's remaining hypothesis into a *purely local, structure-sheaf-only* statement:
that around every point the dual is the kernel of a morphism `𝒪|_U^{⊕m} ⟶ 𝒪|_U^{⊕n}`.

## Main definitions

* `IsLocallyStructureKernel M`: around every point, `M` is isomorphic to the kernel of a
  morphism between two finite direct sums of copies of the structure sheaf, restricted to a
  neighbourhood.  This is the conclusion of Tag 01CQ's first assertion, specialised to target
  the structure sheaf and spelled over the repository's own names.

## Main results

* `isCoherent_of_isLocallyStructureKernel`: on a locally Noetherian scheme such a module is
  coherent.
* `isCoherent_dualSheaf_of_isLocallyStructureKernel`: the consumer form, for a dual module --
  this is Tag 0EBH's missing hypothesis, at Tag 0EBH's own hypotheses.
* `reflexiveHullAdjunction_of_isLocallyStructureKernel`: Tag 0EBH's adjunction, from the local
  kernel presentation of duals alone.

## Implementation notes

Two distinct `IsCoherent` classes are in play and they are unbridged by instance search:
`SheafOfModules.IsCoherent` (Stacks Tag 01BW), which is what dot notation
`M.IsCoherent` resolves to for `M : X.Modules`, and
`Stacks.SheafOfModules.IsCoherent` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/Coherent.lean`, which is what the locality theory
of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/CoherenceClosure.lean` concludes.  The two have the
same fields and `Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isCoherent'` /
`isCoherent'_of_isCoherent` cross between them; both crossings are needed here, one for the
hypothesis on the structure sheaf and one for the conclusion.

The tag for Tag 01CQ is **withheld**: the local kernel presentation itself -- 01CQ's first
assertion -- is not proved here, and a declaration carrying it as a hypothesis is not a covering
set.  The tag for Tag 0EBH is withheld for the same reason.

## References

* [Stacks Project, Tag 0EBH](https://stacks.math.columbia.edu/tag/0EBH)
* [Stacks Project, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ)
* [Stacks Project, Tag 01Y2](https://stacks.math.columbia.edu/tag/01Y2)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.AlgebraicGeometry.InternalHomCoherent

variable {X : Scheme.{u}}

/-- A module on a scheme is **locally a kernel of a map between finite sums of the structure
sheaf** when around every point it is isomorphic to the kernel of a morphism
`𝒪|_U^{⊕m} ⟶ 𝒪|_U^{⊕n}`.

This is the conclusion of the first assertion of [Stacks, Tag 01CQ], specialised to target the
structure sheaf: for `F` of finite presentation, `SheafHom(F, 𝒪_X)` has this property. -/
def IsLocallyStructureKernel (M : X.Modules) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ m n : ℕ,
    ∃ f : (∐ fun _ : Fin m => (SheafOfModules.unit X.ringCatSheaf).over U) ⟶
          (∐ fun _ : Fin n => (SheafOfModules.unit X.ringCatSheaf).over U),
      Nonempty (M.over U ≅ kernel f)

/-- **On a locally Noetherian scheme a module that is locally the kernel of a map between finite
sums of copies of the structure sheaf is coherent.**

This is [Stacks, Tag 01BY] (1) and (2) in the local form supplied by
`Stacks.SheafOfModules.isCoherent_of_locallyKernelFiniteCoproduct`, fed with coherence of the
structure sheaf ([Stacks, Tag 01XZ]).  Local Noetherianity enters only through that one
input. -/
@[sga "6 I 3.6" "special case"]
theorem isCoherent_of_isLocallyStructureKernel [IsLocallyNoetherian X] (M : X.Modules)
    (h : IsLocallyStructureKernel M) : M.IsCoherent := by
  have hunit : Stacks.SheafOfModules.IsCoherent (SheafOfModules.unit X.ringCatSheaf) :=
    CoherenceCriteria.isCoherent'_of_isCoherent (CoherenceCriteria.structureSheaf_isCoherent X)
  exact CoherenceCriteria.isCoherent_of_isCoherent'
    (Stacks.SheafOfModules.isCoherent_of_locallyKernelFiniteCoproduct h)

/-- **Tag 0EBH's missing hypothesis, at Tag 0EBH's own hypotheses.**  On a locally Noetherian
scheme, if the dual of `F` is locally the kernel of a map between finite sums of copies of the
structure sheaf, then the dual of `F` is coherent.

Integrality of `X` is not used, so this discharges the hypothesis `hcd` of
`Stacks.AlgebraicGeometry.ReflexiveStalkCriterion.isCoherent_and_isReflexive_dualSheaf` for any
`F` whose dual admits such a presentation. -/
theorem isCoherent_dualSheaf_of_isLocallyStructureKernel [IsLocallyNoetherian X] (F : X.Modules)
    (h : IsLocallyStructureKernel (dualSheaf F)) : (dualSheaf F).IsCoherent :=
  isCoherent_of_isLocallyStructureKernel _ h

/-- **Stacks Tag 0EBH, the adjunction, from the local kernel presentation of duals alone.**

On an integral locally Noetherian scheme, if the dual of every coherent module is locally the
kernel of a map between finite sums of copies of the structure sheaf, then the double-dual
functor is left adjoint to the inclusion of coherent reflexive modules into coherent modules,
with the canonical bidual map as its unit.

This is `ReflexiveStalkCriterion.reflexiveHullAdjunction_of_isCoherent_dualSheaf` with its
coherence-of-duals hypothesis replaced by the local statement it reduces to.  The tag is
withheld: the local presentation is Tag 01CQ's first assertion and is not proved here. -/
noncomputable def reflexiveHullAdjunction_of_isLocallyStructureKernel (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X]
    (h : ∀ G : X.Modules, G.IsCoherent → IsLocallyStructureKernel (dualSheaf G)) :
    { p : (Σ L : ReflexiveHull.CoherentModules X ⥤ ReflexiveHull.CoherentReflexiveModules X,
        L ⊣ ReflexiveHull.inclusion X) //
      ∀ F : ReflexiveHull.CoherentModules X,
        ∃ e : (p.1.obj F).obj.obj = ReflexiveModules.reflexiveHull F.obj,
          (p.2.unit.app F).hom ≫ eqToHom e =
            (ReflexiveModules.toReflexiveHull F.obj).1 } :=
  ReflexiveStalkCriterion.reflexiveHullAdjunction_of_isCoherent_dualSheaf X
    (fun G hG => isCoherent_dualSheaf_of_isLocallyStructureKernel G (h G hG))

end Stacks.AlgebraicGeometry.InternalHomCoherent

end
