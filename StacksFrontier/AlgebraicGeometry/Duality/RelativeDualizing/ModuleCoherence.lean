module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.CoherentCohomology
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModule

/-!
# Coherence of the relative dualizing module

[Stacks, Tag 0AWI] asserts four things about the relative dualizing complex
`ω_X^• = f^! ω_S^•` of a proper morphism `f : X ⟶ Spec A` over a Noetherian local ring with a
normalized dualizing complex: that `ω_X^•` is a dualizing complex on `X`, that the relative
dualizing module `ω_X = H^{-dim X}(ω_X^•)` is coherent, and that `ω_X` is the first nonvanishing
cohomology sheaf. The second of those follows from the first with no further input about `f`:
coherence of the cohomology sheaves is a property of *any* dualizing complex on a locally
Noetherian scheme, which is
`Stacks.Duality.isCoherent_homology_of_isDualizingComplex`.

This file records that reduction at the relative dualizing module of
`StacksFrontier/AlgebraicGeometry/Duality/RelativeDualizingModule.lean`.

## Main results

* `Stacks.Duality.isCoherent_relativeDualizingModule` — the relative dualizing module is
  coherent as soon as the relative dualizing complex is a dualizing complex.

## Implementation notes

Neither properness of `f`, nor the normalization of the base complex, nor local Noetherianity of
the base appears: the reduction holds for any base. Under the hypotheses of the example the
dualizing property is proved, and with it coherence, in
`Stacks.Duality.isDualizingModuleOf_relativeDualizingModule` of
`StacksFrontier/AlgebraicGeometry/Duality/RelativeDualizing/DualizingModuleProperCharts.lean`.
The quasi-coherence-preservation datum `hpush` and the adjointness of the restricted derived
pushforward are explicit arguments, as everywhere in this directory, since
[Stacks, Tag 0A9E] is not available unconditionally. For a proper `f` over a Noetherian ring,
`IsLocallyNoetherian X` comes from `AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian f`.

The local instance is installed **with an explicit priority**, and that is load-bearing rather
than decorative. `Stacks.Duality.relativeDualizingModule` is generic in the morphism universe of
the derived categories, while `Dualizing.IsDualizingComplex` — hence everything in this
directory — exists only at `HasDerivedCategory.standard`. A plain
`attribute [local instance] HasDerivedCategory.standard` does *not* suffice here: this file
imports `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, a global `HasDerivedCategory.{u}`
instance, through `StacksFrontier/AlgebraicGeometry/Duality/RelativeDualizingModule.lean`, and an
imported global instance takes precedence over an unprioritised file-level local one. Without the
priority,
`relativeDualizingModule` is instantiated at the locally small model while the hypothesis `h`
speaks about the standard one, so that the two sides of a `rfl` differ in exactly one universe.
Raising the priority instantiates everything at the standard model and the statement closes by
definitional unfolding.

The tag attribute for [Stacks, Tag 0AWI] is on
`Stacks.Duality.isDualizingModuleOf_relativeDualizingModule`, which proves the whole example; the
reduction here carries none.

## References

* [Stacks Project, Tag 0AWI](https://stacks.math.columbia.edu/tag/0AWI)
* [Stacks Project, Tag 0AU3](https://stacks.math.columbia.edu/tag/0AU3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] HasDerivedCategory.standard

universe u

namespace Stacks.Duality

/-- **Coherence of the relative dualizing module from the dualizing property.**
The relative dualizing module `ω_X = H^{-dim X}(f^! ω_Y)` is coherent as soon as the relative
dualizing complex `f^! ω_Y` is a dualizing complex on `X`. -/
theorem isCoherent_relativeDualizingModule {X Y : Scheme.{u}} [IsLocallyNoetherian X] (f : X ⟶ Y)
    (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
    [(quasiCoherentDerivedPushforward f hpush).IsLeftAdjoint]
    (ωY : quasiCoherentDerivedCategory Y)
    (h : IsDualizingComplex (relativeDualizingComplex f hpush ωY).obj) :
    _root_.SheafOfModules.IsCoherent (relativeDualizingModule f hpush ωY) :=
  isCoherent_homology_of_isDualizingComplex h _

end Stacks.Duality

end
