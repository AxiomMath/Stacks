module

public import StacksFrontier.AlgebraicGeometry.Ample.Defs
public import StacksFrontier.AlgebraicGeometry.CommonDegreeTwist.AffineSectionBasis
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic

/-!
# The two ampleness predicates of Stacks Tag 01PS agree

This repository carries **two** predicates for ampleness of an invertible `𝒪_X`-module, both
attributed to Stacks Tag 01PS:

* `Stacks.Ample.IsAmple`, which the `Stacks.Ample` cluster is written over. It is
  `Stacks.Ample.IsAmpleForPowers` at `Stacks.Ample.tensorPowModule`, so its nonvanishing loci are
  `Stacks.Ample.nonvanishingLocus`, produced existentially as an affine open of the scheme.
* `AlgebraicGeometry.Scheme.Modules.IsAmple`, which the `AmpleAndExtension` cluster is written
  over. Its tensor powers are `Stacks.SheafOfModules.Invertible.tensorPower` and its nonvanishing
  loci are `Stacks.SheafOfModules.nonvanishingOpen`, bundled by the openness theorem of Tag 01CY
  on the underlying ringed space.

Both are faithful readings of Tag 01PS, and they are the same condition:
`Stacks.AmpleBridge.isAmple_iff_isAmple`. A statement proved over either predicate may be used
against the other with no restatement.

## Main results

* `Stacks.AmplePredicateBridge.coe_nonvanishingOpen_sectionsOfTop` and
  `coe_nonvanishingOpen_eval`: the underlying set of the bundled nonvanishing open of Tag 01CY is
  the scheme-level nonvanishing locus, for a global section read either way round.

## Implementation notes

**No `@[stacks 01PS]` attribute is attached here.** The label is already on both predicates,
each of which states Tag 01PS in full; an equivalence between two statements of one tag is not a
third statement of it.

**The two tensor-power families are the same term.**
`Stacks.SheafOfModules.Invertible.tensorPower` and
`Stacks.SheafOfModules.TensorPower.tensorPower` are built from `tensorRightFunctor`s with
identical definitions, and differ only in how the equivalence hypothesis is presented — as
`AlgebraicGeometry.SheafOfModules.IsInvertible` for the former and as
`Functor.IsEquivalence` of the right-tensor functor for the latter. Both are `Prop`-valued, so
the two powers are definitionally equal, and `Stacks.AmpleProjectiveImmersion.tensorPowerModule`
is the second of them on a scheme. That is why the only comparison this file has to spend is
`Stacks.PowerFamilyBridge.isAmpleForPowers_tensorPowerModule_iff`, which relates
`Stacks.AmpleProjectiveImmersion.tensorPowerModule` to `Stacks.Ample.tensorPowModule`; the step
across to `Stacks.SheafOfModules.Invertible.tensorPower` costs nothing.

**The invertibility instance has to be transported by hand.**
`Stacks.PowerFamilyBridge.instIsInvertible` converts
`AlgebraicGeometry.SheafOfModules.IsInvertible` to `Stacks.SheafOfModules.IsInvertible` on an
arbitrary site, but it does not fire on the site of opens of a scheme, whose sheafification
instances are supplied locally where they are needed. `stacksIsInvertible` below is that
conversion at the scheme spelling, declared as an instance so that
`Stacks.SheafOfModules.nonvanishingOpen` can be named under the ampleness theory's hypothesis
alone.

**The section types differ and the translation is lossless in both directions.**
`Stacks.Ample.IsAmpleForPowers` quantifies over `Γ(M, ⊤)` and
`AlgebraicGeometry.Scheme.Modules.IsAmple` over `M.sections`;
`Stacks.SheafOfModules.sectionsOfTop` and evaluation at `⊤` move between them, and
`Stacks.SheafOfModules.nonvanishingLocus_sectionsOfTop_eval` says the nonvanishing locus only
sees the value over `⊤`, so neither direction loses a witness.

## References

* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace Stacks.AmplePredicateBridge

universe u

/-- **The two classes realising Stacks Tag 01CS agree on a scheme.** An `𝒪_X`-module invertible
in the sense the ampleness theory uses is invertible in the sense
`Stacks.SheafOfModules.nonvanishingOpen` asks for. This is
`Stacks.PowerFamilyBridge.instIsInvertible` at the scheme spelling, where it has to be given by
hand: the general instance carries sheafification hypotheses for the ambient site that are
supplied locally on the site of opens of a scheme, so instance search does not cross the gap on
its own. -/
instance stacksIsInvertible (X : Scheme.{u}) (M : X.Modules)
    [Stacks.Ample.IsInvertibleModule X M] :
    Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M :=
  (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
    X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) M).mpr inferInstance

/-- **The bundled nonvanishing open of Tag 01CY is the ample theory's nonvanishing locus.** The
left-hand side is the open subset the statement of `AlgebraicGeometry.Scheme.Modules.IsAmple`
applies `IsAffineOpen` to, for the global section `m` read as a restriction-compatible family;
the right-hand side is the set `Stacks.Ample.IsAmpleForPowers` produces existentially. -/
theorem coe_nonvanishingOpen_sectionsOfTop (X : Scheme.{u}) (M : X.Modules)
    [Stacks.Ample.IsInvertibleModule X M] (m : Γ(M, ⊤)) :
    (Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace) M
        (Stacks.SheafOfModules.sectionsOfTop M m) : Set X)
      = Stacks.Ample.nonvanishingLocus M m := by
  ext y
  exact (Stacks.AlgebraicGeometry.CommonDegreeTwist.mem_nonvanishingLocus_sectionsOfTop_iff'
    M m y).symm

/-- `Stacks.AmplePredicateBridge.coe_nonvanishingOpen_sectionsOfTop` read starting from a
restriction-compatible family rather than from a global element: the nonvanishing locus depends
on the family only through its value over `⊤`. -/
theorem coe_nonvanishingOpen_eval (X : Scheme.{u}) (M : X.Modules)
    [Stacks.Ample.IsInvertibleModule X M] (s : M.sections) :
    (Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace) M s : Set X)
      = Stacks.Ample.nonvanishingLocus M (s.eval (op ⊤)) := by
  rw [← coe_nonvanishingOpen_sectionsOfTop X M (s.eval (op ⊤))]
  change Stacks.SheafOfModules.nonvanishingLocus M s
      = Stacks.SheafOfModules.nonvanishingLocus M
          (Stacks.SheafOfModules.sectionsOfTop M (s.eval (op ⊤)))
  exact (Stacks.SheafOfModules.nonvanishingLocus_sectionsOfTop_eval M s).symm

end Stacks.AmplePredicateBridge

end
