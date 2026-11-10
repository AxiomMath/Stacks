module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineOpensChaoticQuasicoherentEquality
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModule
import StacksCore.Tactic.StacksAttribute

/-!
# The relative dualizing complex of a morphism over a quasi-compact base

Let `f : X ⟶ Y` be a quasi-compact quasi-separated morphism of schemes with `Y` quasi-compact,
and let `a = f^×` be the right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` of
[Stacks, Tag 0A9E]. This file names the object

`ω_{X/Y}^• = a(𝒪_Y)`

that [Stacks, Tag 0B6S] calls the *relative dualizing complex*, together with the trace map
`Tr_{f, 𝒪_Y} : Rf_* ω_{X/Y}^• ⟶ 𝒪_Y` of [Stacks, Tag 0AWG] that the Remark displays, which is
the counit of `Rf_* ⊣ f^×` at `𝒪_Y`.

Over `Y = Spec k` for a field `k` this is the dualizing complex
`Stacks.Duality.dualizingComplexOverField` of [Stacks, Tag 0BS2], which is built by the same two
steps in `StacksFrontier/AlgebraicGeometry/Duality/ProperOverFieldDuality.lean`; the content here is
that neither step needs the base to be the spectrum of a field.

## Main definitions

* `Stacks.Duality.relativeDualizingComplexStructureSheaf` — `ω_{X/Y}^• = a(𝒪_Y)`, the relative
  dualizing complex of [Stacks, Tag 0B6S].
* `Stacks.Duality.relativeDualizingTraceStructureSheaf` — the trace
  `Tr_{f, 𝒪_Y} : Rf_* ω_{X/Y}^• ⟶ 𝒪_Y`.

## What of [Stacks, Tag 0B6S] is covered here, and where the rest is

The Remark's setting is a proper flat morphism of finite presentation over a quasi-compact
quasi-separated `Y`. Each of those conditions implies one of the three conditions used below —
properness gives quasi-compactness and, through separatedness, quasi-separatedness of `f`, and
`Y` quasi-compact is `CompactSpace Y` — so the two objects below are defined in greater
generality than the Remark asks for.

Covered here: the two objects the Remark introduces, `ω_{X/Y}^• = a(𝒪_Y)` and `Tr_{f, 𝒪_Y}`.

Covered in
`StacksFrontier/AlgebraicGeometry/Duality/RelativeDualizingComplexTensorDescription.lean`,
at exactly the Remark's hypotheses:

* the functorial identification `a(K) = Lf^* K ⊗^{\mathbf L}_{𝒪_X} ω_{X/Y}^•` for
  `K ∈ D_QCoh(𝒪_Y)`, from [Stacks, Tag 0E4K]
  (`Stacks.Duality.relativeDualizingTensorIso`);
* the commuting square expressing `Tr_{f, K}` through `Tr_{f, 𝒪_Y}`, whose lower left equality
  is [Stacks, Tag 08EU] (`Stacks.Duality.map_relativeDualizingTensorIso_hom_app_comp_trace`).

Not covered: the two base-change statements of the Remark's last sentence,
`ω_{X'/Y'}^• = L(g')^* ω_{X/Y}^•` of [Stacks, Tag 0AAB] and the base change of the trace of
[Stacks, Tag 0B6J].

## Implementation notes

The derived-category model is left to instance search, which picks the locally small
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`. That is forced rather than chosen: the
right adjoint of [Stacks, Tag 0A9E] comes from Brown representability, whose `HasCoproducts`
condition fails at `CategoryTheory.HasDerivedCategory.standard`. See the implementation notes of
`StacksFrontier/AlgebraicGeometry/Duality/RelativeDualizingModule.lean`.

`Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs` is part (1) of
[Stacks, Tag 08D5], which is what lets `Rf_*` be restricted to the complexes with quasi-coherent
cohomology at all; it is applied directly rather than abbreviated, so that the two definitions
below read against the same term as every other consumer of
`Stacks.Duality.quasiCoherentDerivedPushforward`.

## References

* [Stacks Project, Tag 0B6S](https://stacks.math.columbia.edu/tag/0B6S)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0AWG](https://stacks.math.columbia.edu/tag/0AWG)
* [Stacks Project, Tag 0E4K](https://stacks.math.columbia.edu/tag/0E4K)
* [Stacks Project, Tag 0AAB](https://stacks.math.columbia.edu/tag/0AAB)
* [Stacks Project, Tag 0B6J](https://stacks.math.columbia.edu/tag/0B6J)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Duality

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] [CompactSpace Y]

/-- **The relative dualizing complex `ω_{X/Y}^• = a(𝒪_Y)`** of [Stacks, Tag 0B6S], for `a = f^×`
the right adjoint of [Stacks, Tag 0A9E]: the twisted inverse image of the structure sheaf of the
base, placed in degree zero.

Over `Y = Spec k` for a field `k` this is `Stacks.Duality.dualizingComplexOverField`, the
dualizing complex of [Stacks, Tag 0BS2]. -/
@[stacks 0B6S "the relative dualizing complex omega^bullet_{X/Y} = a(O_Y) that the Remark names, \
the right adjoint of Tag 0A9E applied to the structure sheaf; defined for every quasi-compact \
quasi-separated morphism to a quasi-compact scheme, so in particular under the Remark's hypotheses"]
def relativeDualizingComplexStructureSheaf : quasiCoherentDerivedCategory X :=
  letI := AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward f
  relativeDualizingComplex f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
    (Stacks.Duality.DerivedPushforward.derivedStructureSheaf Y)

/-- **The trace map `Tr_{f, 𝒪_Y} : Rf_* ω_{X/Y}^• ⟶ 𝒪_Y`** of [Stacks, Tag 0AWG], displayed in
[Stacks, Tag 0B6S]: the counit of `Rf_* ⊣ f^×` at the structure sheaf of the base.

That it induces the trace map `Tr_{f, K}` for every `K` in `D_QCoh(𝒪_Y)` — the commuting square
of the Remark — is `Stacks.Duality.map_relativeDualizingTensorIso_hom_app_comp_trace`. -/
@[stacks 0B6S "the trace map Tr_{f,O_Y} : Rf_* omega^bullet_{X/Y} to O_Y that the Remark \
displays, the counit of the adjunction of Tag 0A9E at the structure sheaf of the base"]
def relativeDualizingTraceStructureSheaf :
    (quasiCoherentDerivedPushforward f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
      (relativeDualizingComplexStructureSheaf f) ⟶
    Stacks.Duality.DerivedPushforward.derivedStructureSheaf Y :=
  letI := AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward f
  relativeDualizingComplexTrace f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
    (Stacks.Duality.DerivedPushforward.derivedStructureSheaf Y)

end Stacks.Duality

end
