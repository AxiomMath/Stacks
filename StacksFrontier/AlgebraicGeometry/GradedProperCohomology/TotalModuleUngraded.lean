module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealizationCoproductSectionsInt
public import StacksFrontier.AlgebraicGeometry.Constructions.GradedAlgebraToAlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.CohomologyGradedReesBaseChange
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.CohomologyDirectSum
public import StacksFrontier.AlgebraicGeometry.QcohLimits.RestrictScalars
public import StacksCore.Tactic.StacksAttribute

/-!
# The ungraded realization of a graded module, and its `𝒪_X`-module

`Stacks.AlgebraicGeometry.GradedProperCohomology.totalModule F` is the coproduct `∐ₙ ℱₙ` of the
homogeneous pieces of a graded `𝓑`-module, taken over **all** of `ℤ` and read as a single
`𝒪_X`-module. It is the sheaf [Stacks, Tag 0897] denotes by the same letter `ℱ` as the graded
module, and the sheaf whose direct image from the relative spectrum `X' = Spec_X(𝓑)` the proof
of that tag produces an `ℱ'` for.

To feed it to [Stacks, Tag 01SB] — `Stacks.AffineAlgebraEquivalence.relativeSpecQcohEquivalence`
— it must be a quasi-coherent module over the **ungraded realization** `𝓑.ungradedSheaf`, not
merely over `𝒪_X`: an `𝒪_X`-module carries no information about `π`. That module over
`𝓑.ungradedSheaf` is `SheafOfModules.GradedModule.ungradedSheaf F`, the sheafification of the
presheaf total module; this file identifies the `𝒪_X`-module underlying it with `totalModule F`
and concludes that it is quasi-coherent as soon as the homogeneous pieces are.

This is the module-side counterpart of `Stacks.RelativeSpec.gradedAlgebraSheaf` and
`Stacks.RelativeSpec.isQuasicoherent_gradedAlgebraSheaf`, which do the same for the algebra.

## Main definitions

* `Stacks.AlgebraicGeometry.GradedProperCohomology.ungradedTotalModule`: **the total module
  `⨁ₙ ℱₙ` of a graded `𝓑`-module as a sheaf of modules over the ungraded realization
  `𝓑.ungradedSheaf`.** This is `SheafOfModules.GradedModule.ungradedSheaf`, named at the
  scheme-level spelling used by [Stacks, Tag 0897].
* `Stacks.AlgebraicGeometry.GradedProperCohomology.totalModuleIsoUngradedTotalModule`: **its
  restriction of scalars to `𝒪_X` is `totalModule F`**, the coproduct of the homogeneous pieces
  over `ℤ`.

## Main results

* `Stacks.AlgebraicGeometry.GradedProperCohomology.isQuasicoherent_totalModule`: the coproduct
  `∐ₙ ℱₙ` is quasi-coherent as soon as every piece is.
* `Stacks.AlgebraicGeometry.GradedProperCohomology.isQuasicoherent_ungradedTotalModule`: **the
  total module is quasi-coherent over `𝓑.ungradedSheaf` as soon as every homogeneous piece is
  quasi-coherent over `𝒪_X`**, for a `𝓑` whose own ungraded realization is quasi-coherent.

## Implementation notes

**No vanishing hypothesis.** `SheafOfModules.GradedModule.coprodIsoUngradedSheaf` identifies the
underlying `𝒪_X`-module with the coproduct over the **nonnegative** degrees, and for that it
must assume that the negative pieces are zero, because the reindexing `ℕ → ℤ` is locally
bijective only then. Over `ℤ` no reindexing occurs — the direct sum over `ℤ` is already the
sections of the presheaf total module — so
`SheafOfModules.GradedModule.coprodIntIsoUngradedSheaf` is unconditional, and so is everything
here. `totalModule` is indexed by `ℤ`, which is why that is the form needed.

**Quasi-coherence of `𝓑` is a hypothesis on the algebra, not on the module.** [Stacks, Tag 0H88]
(`Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_of_isQuasicoherent_restrictScalars`) reads
quasi-coherence over `𝒪_X` as quasi-coherence over a sheaf of rings `𝒜` only for a `𝒜` that is
itself quasi-coherent as an `𝒪_X`-module. That is a property of `𝓑` alone, and for the Rees
algebra of an ideal sheaf it is
`Stacks.Cohomology.FormalFunctions.isQuasicoherent_reesAlgebraSheaf`.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 0H88](https://stacks.math.columbia.edu/tag/0H88)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.GradedProperCohomology

variable {X : Scheme.{u}}
  {𝓑 : _root_.SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf} [𝓑.IsCommutative]

/-! ### The total module over the ungraded realization -/

/-- **The total module `⨁ₙ ℱₙ` of a graded `𝓑`-module, as a sheaf of modules over the ungraded
realization `𝓑.ungradedSheaf`.** This is the object [Stacks, Tag 01SB] turns into the module
`ℱ'` on the relative spectrum `X' = Spec_X(𝓑)` with `π_* ℱ' ≅ ⨁ₙ ℱₙ`, which is what the proof
of [Stacks, Tag 0897] needs and what an `𝒪_X`-module cannot supply. -/
abbrev ungradedTotalModule (F : _root_.SheafOfModules.GradedModule 𝓑) :
    _root_.SheafOfModules.{u} 𝓑.ungradedSheaf :=
  _root_.SheafOfModules.GradedModule.ungradedSheaf F

/-- **The `𝒪_X`-module underlying the total module is `totalModule F = ∐ₙ ℱₙ`**, the coproduct
of the homogeneous pieces over all of `ℤ`.

There is no hypothesis: the direct sum over `ℤ` of the homogeneous sections is exactly the
presheaf total module whose sheafification `ungradedTotalModule` is, so the identification is
`Stacks.sheafifyDirectSumIso` followed by
`SheafOfModules.GradedModule.directSumIsoUngradedSheaf`. -/
def totalModuleIsoUngradedTotalModule (F : _root_.SheafOfModules.GradedModule 𝓑) :
    totalModule F ≅
      (_root_.SheafOfModules.restrictScalars.{u} 𝓑.ungradedStructureMap).obj
        (ungradedTotalModule F) :=
  _root_.SheafOfModules.GradedModule.coprodIntIsoUngradedSheaf F

/-! ### Quasi-coherence -/

omit [𝓑.IsCommutative] in
/-- **The coproduct `∐ₙ ℱₙ` of the homogeneous pieces is quasi-coherent as soon as every piece
is.** The grading is by `ℤ`, which lies in the universe of the scheme only when that universe is
`0`, so the index type is shrunk by
`Stacks.Cohomology.FormalFunctions.isQuasicoherent_coprod_of_small`. -/
theorem isQuasicoherent_totalModule (F : _root_.SheafOfModules.GradedModule 𝓑)
    (hqc : ∀ n : ℤ, (pieceModule F n).IsQuasicoherent) :
    (totalModule F).IsQuasicoherent :=
  Stacks.Cohomology.FormalFunctions.isQuasicoherent_coprod_of_small
    (fun n : ℤ => pieceModule F n) hqc

/-- **The total module of a graded `𝓑`-module is quasi-coherent over the ungraded realization
`𝓑.ungradedSheaf` as soon as every homogeneous piece is quasi-coherent over `𝒪_X`.**

The `𝒪_X`-module underlying it is the coproduct of the pieces
(`totalModuleIsoUngradedTotalModule`), which is quasi-coherent
(`isQuasicoherent_totalModule`); [Stacks, Tag 0H88] then reads that as quasi-coherence over
`𝓑.ungradedSheaf`, its hypothesis being that `𝓑.ungradedSheaf` is itself quasi-coherent as an
`𝒪_X`-module. -/
theorem isQuasicoherent_ungradedTotalModule (F : _root_.SheafOfModules.GradedModule 𝓑)
    (h𝓑 : ((_root_.SheafOfModules.restrictScalars.{u} 𝓑.ungradedStructureMap).obj
      (_root_.SheafOfModules.unit 𝓑.ungradedSheaf)).IsQuasicoherent)
    (hqc : ∀ n : ℤ, (pieceModule F n).IsQuasicoherent) :
    (ungradedTotalModule F).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_of_isQuasicoherent_restrictScalars
    𝓑.ungradedStructureMap h𝓑 (ungradedTotalModule F)
    ((_root_.SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (totalModuleIsoUngradedTotalModule F) (isQuasicoherent_totalModule F hqc))

/-- **The total module is quasi-coherent over `𝓑.ungradedSheaf` whenever `𝓑` is a quasi-coherent
sheaf of algebras and the homogeneous pieces are quasi-coherent.**

This is `isQuasicoherent_ungradedTotalModule` with its hypothesis on `𝓑` in the form the
relative spectrum uses it: `Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent` of
`Stacks.RelativeSpec.gradedAlgebraSheaf X 𝓑 hc`, whose underlying module is the restriction of
scalars of `𝓑.ungradedSheaf` along `𝓑.ungradedStructureMap` — the sheaf of rings being
`𝓑.ungradedSheaf` on the nose by `Stacks.RelativeSpec.ringSheaf_gradedAlgebraSheaf`, and the
structure morphism being `𝓑.ungradedStructureMap` on the nose because
`Stacks.CommRingSheaf.homMk` does not change the underlying morphism of sheaves of rings.

For the Rees algebra `⨁ₙ ℐⁿ` of an ideal sheaf the hypothesis is
`Stacks.Cohomology.FormalFunctions.isQuasicoherent_reesAlgebraSheaf`, so this applies to the
situation of [Stacks, Tag 0897] with nothing left to supply but quasi-coherence of the
homogeneous pieces, which is that tag's own hypothesis on the graded module. -/
theorem isQuasicoherent_ungradedTotalModule_of_algebraSheaf
    (hc : ∀ (i j : ℤ) (W : (TopologicalSpace.Opens ↥X)ᵒᵖ) (a : (𝓑.piece i).val.obj W)
      (b : (𝓑.piece j).val.obj W), HEq ((𝓑.mul i j).app W a b) ((𝓑.mul j i).app W b a))
    (h𝓑 : Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent
      (Stacks.RelativeSpec.gradedAlgebraSheaf X 𝓑 hc))
    (F : _root_.SheafOfModules.GradedModule 𝓑)
    (hqc : ∀ n : ℤ, (pieceModule F n).IsQuasicoherent) :
    (ungradedTotalModule F).IsQuasicoherent :=
  isQuasicoherent_ungradedTotalModule F h𝓑 hqc

end Stacks.AlgebraicGeometry.GradedProperCohomology

end
