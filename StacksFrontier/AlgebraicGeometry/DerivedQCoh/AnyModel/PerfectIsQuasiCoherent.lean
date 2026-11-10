module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.Basic
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
public import
  StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PseudoCoherentAndFiniteTorDimension

/-!
# A perfect object of `D(𝒪_X)` lies in `D_QCoh(𝒪_X)`, at any model

Let `X` be a scheme. A perfect object of the derived category of `𝒪_X`-modules has quasi-coherent
cohomology sheaves in every degree, that is, it belongs to `D_QCoh(𝒪_X)`. This is the composite of
[Stacks, Tag 08CM] — a perfect object is pseudo-coherent — with [Stacks, Tag 08E5] — a
pseudo-coherent object of the derived category of a scheme has quasi-coherent cohomology.

## Main results

* `Stacks.DerivedQCoh.AnyModel.isDQCoh_of_isPerfect` — a perfect object of `D(𝒪_X)` lies in
  `D_QCoh(𝒪_X)`.

## Implementation notes

**The chosen derived category is an explicit argument.** `CategoryTheory.HasDerivedCategory.{w} C`
carries the localization as data, so a statement proved at one choice says nothing about another;
and a statement cannot be written with that choice as an *instance* binder here, because the three
predicates involved are stated at three spellings of the same category of `𝒪_X`-modules —
`AlgebraicGeometry.Scheme.Modules X` for the object,
`Stacks.StrictlyPerfect.OXMod X.toRingedSpace` for perfectness, and
`SheafOfModules X.ringCatSheaf` for quasi-coherence — which are definitionally but not reducibly
equal, so instance search does not cross between them and a binder covering one spelling leaves
the other two to be resolved independently. Passing the model explicitly and seating it in the
remaining two spellings with `letI`, which is a type ascription and so a defeq check at default
transparency, resolves all three to the one model. This is the device of
`Stacks.DerivedQCoh.AnyModel.isPerfect_modelEquiv_iff` and
`Stacks.DerivedQCoh.AnyModel.isDQCoh_modelEquiv_iff`.

No derived category of an open subspace of `X` occurs: Tag 08CM,
`Stacks.Cohomology.TorAmplitude.isPseudoCoherent_of_isPerfect`, involves only the model of
`D(𝒪_X)`, the pseudo-coherence of an object being a condition on complexes representing its
restrictions and not on those restrictions as derived objects.

`Stacks.DerivedQCoh.OpenLift.isDQCoh_of_isPerfect` is this statement for `X = Spec A` at
`CategoryTheory.HasDerivedCategory.standard`. It is not restated as a corollary of this one:
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/OpenLift/ShiftedSummandLift.lean` seats that model as
a file-local instance at priority 10000, so a model argument there would be shadowed rather than
read, and its own docstring records that the conclusion is reached from `(Spec A).Modules` and not
from the `OXMod` spelling for budget reasons.

## References

* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
* [Stacks Project, Tag 08E5](https://stacks.math.columbia.edu/tag/08E5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open StrictlyPerfect

universe u w

namespace Stacks.DerivedQCoh.AnyModel

/-- **A perfect object of `D(𝒪_X)` lies in `D_QCoh(𝒪_X)`**, at any chosen derived category of
`𝒪_X`-modules. A perfect object is pseudo-coherent ([Stacks, Tag 08CM]), and the cohomology
sheaves of a pseudo-coherent object of the derived category of a scheme are quasi-coherent
([Stacks, Tag 08E5]). -/
theorem isDQCoh_of_isPerfect {X : AlgebraicGeometry.Scheme.{u}}
    (h : HasDerivedCategory.{w} X.Modules)
    (K : @DerivedCategory X.Modules _ _ h)
    (hK : @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace h K) :
    @Stacks.DerivedQCoh.IsDQCoh _ _ _ X.ringCatSheaf _ _ _ _ h K := by
  let : HasDerivedCategory.{w} (OXMod.{u, u, u} X.toRingedSpace) := h
  have hpc : AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent
      (X := X.toRingedSpace) K :=
    Stacks.Cohomology.TorAmplitude.isPseudoCoherent_of_isPerfect K hK
  exact fun n => AlgebraicGeometry.isQuasicoherentDerived_of_isPseudoCoherent X K hpc n

end Stacks.DerivedQCoh.AnyModel

end
