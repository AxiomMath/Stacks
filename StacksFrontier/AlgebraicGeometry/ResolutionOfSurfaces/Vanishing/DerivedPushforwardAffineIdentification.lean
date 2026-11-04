module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.DerivedStructureSheaf
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.DualizingDivisor.DualityHomEquiv
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.DerivedPushforwardStructureSheaf

/-!
# `Hom_{D(A)}(κ[-1], Rf_*𝒪_X) = 0` at the derived direct image itself

In the vanishing situation of [Stacks, Tag 0AX8] the base is affine, `S = Spec(A)`. Derived
sheafification is therefore an equivalence `D(A) ≌ D_QCoh(𝒪_S)` ([Stacks, Tag 06Z0]), and its
inverse reads the derived direct image `Rf_*𝒪_X` — an object of `D_QCoh(𝒪_S)`, got by applying
the restricted unbounded derived direct image to the structure sheaf of `X` placed in
cohomological degree zero — as an object of `D(A)`. This file names that object and proves
[Stacks, Tag 0AXC] at it: for `X` normal, every morphism `κ[-1] ⟶ Rf_*𝒪_X` in `D(A)` is zero.

Leray over the base ring ([Stacks, Tag 0D5W]) identifies the object with the `A`-linear derived
global sections `RΓ(X, 𝒪_X)`, so the vanishing is
`AlgebraicGeometry.VanishingSituation.hom_residueFieldShift_derivedGlobalSections_eq_zero`
transported along an isomorphism.

## Main definitions

* `AlgebraicGeometry.VanishingSituation.derivedPushforwardStructureSheaf`: `Rf_*𝒪_X` as an
  object of `D(A)`, through the equivalence of [Stacks, Tag 06Z0].

## Main results

* `AlgebraicGeometry.VanishingSituation.derivedGlobalSectionsStructureSheafIsoPushforward`:
  that object is `RΓ(X, 𝒪_X)`.
* `AlgebraicGeometry.VanishingSituation`
  `.hom_residueFieldShift_derivedPushforwardStructureSheaf_eq_zero`: [Stacks, Tag 0AXC].

## Implementation notes

The source states Tag 0AXC with `A` Nagata as well as `X` normal. That hypothesis is not taken
here, so the statement below is stronger than the source's: Nagata enters the source's proof
only through [Stacks, Tag 0AXB], and the route of
`Vanishing/DerivedPushforwardStructureSheaf.lean`, which this file transports, avoids that tag.

`Rf_*` is read on `D_QCoh`, as the source does. The restriction needs the derived direct image
to preserve quasi-coherence of the cohomology sheaves, part (1) of [Stacks, Tag 08D5]; over a
quasi-compact quasi-separated morphism with quasi-compact affine target that is
`Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs`, which
`AlgebraicGeometry.DualizingDivisor.lerayIso` already supplies. The space-level hypotheses hold
because `f` is proper and `S` is affine, which is what `compactSpace_source` and
`quasiSeparatedSpace_source` record.

The equivalence and Leray are taken at the model of `D(A)` and `D(𝒪_X)` in force by default,
`ModuleCat.hasDerivedCategory` and `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, which
is the model the base carrier is stated at; the standard-model counterparts
`Stacks.Duality.standardTildeEquivalence` and `Stacks.Duality.standardLerayIso` live in a
different category and do not compose with it.

## References

* [Stacks Project, Tag 0AXC](https://stacks.math.columbia.edu/tag/0AXC)
* [Stacks Project, Tag 0AX8](https://stacks.math.columbia.edu/tag/0AX8)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory Stacks.Duality

universe u

namespace AlgebraicGeometry

namespace VanishingSituation

variable (V : VanishingSituation.{u})

/-- The source of a modification of the spectrum of a ring is a quasi-compact space. -/
instance compactSpace_source : CompactSpace V.X :=
  QuasiCompact.compactSpace_of_compactSpace V.f

/-- The source of a modification of the spectrum of a ring is a quasi-separated space. -/
instance quasiSeparatedSpace_source : QuasiSeparatedSpace V.X :=
  quasiSeparatedSpace_of_quasiSeparated V.f

/-- **`Rf_*𝒪_X` as an object of `D(A)`.** The restricted unbounded derived direct image of the
structure sheaf of `X`, placed in cohomological degree zero, carried from `D_QCoh(𝒪_S)` to `D(A)`
by the inverse of the derived sheafification equivalence of [Stacks, Tag 06Z0]. -/
def derivedPushforwardStructureSheaf : DerivedCategory (ModuleCat.{u} V.A) :=
  (DualizingDivisor.tildeEquivalence (A := V.A)).inverse.obj
    ((quasiCoherentDerivedPushforward V.f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs V.f)).obj
        (DerivedPushforward.derivedStructureSheaf V.X))

/-- **`Rf_*𝒪_X` read in `D(A)` is `RΓ(X, 𝒪_X)`.** Leray over the base ring ([Stacks, Tag 0D5W])
rewrites the `A`-linear derived global sections of `𝒪_X` as the derived global sections of
`Rf_*𝒪_X` on `S`, and the latter functor is the inverse of the equivalence of
[Stacks, Tag 06Z0]. -/
def derivedGlobalSectionsStructureSheafIsoPushforward :
    derivedGlobalSectionsStructureSheaf V.f ≅ V.derivedPushforwardStructureSheaf :=
  DualizingDivisor.lerayIso V.f (DerivedPushforward.derivedStructureSheaf V.X) ≪≫
    (DualizingDivisor.tildeEquivalenceInverseIso.app _).symm

/-- In Situation [Stacks, Tag 0AX8] with `X` normal, the group
`Hom_{D(A)}(κ[-1], Rf_*𝒪_X)` is zero: every morphism from `κ[-1]` to the derived direct image of
the structure sheaf, read in `D(A)` through the affine identification `D(A) = D_QCoh(𝒪_S)` of
[Stacks, Tag 06Z0], vanishes.

Leray over the base ring identifies that object with `RΓ(X, 𝒪_X)`, so this is
`hom_residueFieldShift_derivedGlobalSections_eq_zero` transported along
`derivedGlobalSectionsStructureSheafIsoPushforward`. The source also assumes `A` Nagata; that
hypothesis is not needed, since it enters the source's proof only through
[Stacks, Tag 0AXB]. -/
@[stacks 0AXC "the vanishing of Hom_{D(A)}(kappa[-1], Rf_*O_X) with Rf_*O_X the ACTUAL derived \
direct image: the restricted unbounded derived direct image quasiCoherentDerivedPushforward \
applied to the structure sheaf of X in degree zero, an object of D_QCoh(O_S), carried into D(A) \
by the inverse of the derived sheafification equivalence of Tag 06Z0 \
(DualizingDivisor.tildeEquivalence, the affine identification D(A) = D_QCoh(O_S) that the tag \
invokes). The vanishing is the base carrier \
hom_residueFieldShift_derivedGlobalSections_eq_zero transported along Leray over the base ring \
(Tag 0D5W, DualizingDivisor.lerayIso), which identifies that object with the A-linear derived \
global sections RGamma(X, O_X). Stated for X normal without the Nagata hypothesis on A, which \
enters the source's proof only through Tag 0AXB and is not needed on the route taken here"]
theorem hom_residueFieldShift_derivedPushforwardStructureSheaf_eq_zero [IsNormal V.X]
    (α : V.residueFieldShift ⟶ V.derivedPushforwardStructureSheaf) : α = 0 :=
  (cancel_mono V.derivedGlobalSectionsStructureSheafIsoPushforward.inv).1 <| by
    rw [Limits.zero_comp]
    exact V.hom_residueFieldShift_derivedGlobalSections_eq_zero _

end VanishingSituation

end AlgebraicGeometry

end
