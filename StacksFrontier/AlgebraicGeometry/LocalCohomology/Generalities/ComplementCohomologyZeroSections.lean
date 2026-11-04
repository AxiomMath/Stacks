module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.Generalities.ZeroLocusComplBridge
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.LocalCohomologyFiniteness
public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.Sections

/-!
# Degree-zero cohomology on the complement of a zero locus is sections there

Let `A` be a ring, let `I ⊆ A` be an ideal, let `X = Spec A`, `Z = V(I)` and `U = X ∖ Z`. The
derived functors of sections over `U` give the `A`-modules
`Stacks.LocalCohomologySequence.complementCohomologyBase I M p = H^p(U, M̃)`, and in degree zero
that functor is sections over `U` itself, because sections over an open are left exact.

This file records that identification and transports it to two other spellings of the same
`A`-module: `Stacks.LocalCohomology.sectionsOnAffineComplement`, sections of a sheaf on `Spec A`
over the open `U`, and `Stacks.LocalCohomology.complementGlobalSections`, global sections of a
sheaf on the open subscheme `U`.

## Main results

* `Stacks.LocalCohomologySequence.complementCohomologyZeroIso` — `H⁰(U, -)` is sections over `U`.
* `Stacks.LocalCohomologySequence.complementCohomologyBaseZeroIso` — `H⁰(U, M̃)`, read as an
  `A`-module, is `Stacks.LocalCohomology.sectionsOnAffineComplement`.
* `Stacks.LocalCohomologySequence.complementCohomologyBaseZeroIsoGlobalSections` — the same
  `A`-module is the global sections of the restriction of `M̃` to the open subscheme `U`.

## Implementation notes

The three spellings differ only in how the `A`-module structure is written down, and the first
two agree on the nose: `Stacks.LocalCohomologySequence.sectionsOnComplement_zeroLocus_eq` is a
`rfl` identifying the composite of sections over `U` with the scalar restriction of
`Stacks.LocalCohomologyTilde.globalToBase` with
`Stacks.LocalCohomology.sectionsOnAffineComplement`. The passage to the open subscheme is
`Stacks.LocalCohomology.sectionsOnAffineComplementIso`.

## References

* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Cohomology.SectionsWithSupport
open Stacks.LocalCohomologyTilde
open RingedSpaceModuleAdjunction

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.LocalCohomologySequence

/-- **Degree-zero cohomology on the complement is sections on the complement.** Sections over an
open of a ringed space are left exact, so the zeroth right derived functor of sections over
`U = Spec A ∖ V(I)` is that functor itself. This is the analogue for `U` of
`Stacks.LocalCohomologySequence.ambientCohomologyZeroIso`. -/
public def complementCohomologyZeroIso {A : CommRingCat.{u}} (I : Ideal A) :
    complementCohomology I 0 ≅
      sectionsOnComplement (Spec A).toRingedSpace (zeroLocusSubset I)
        (isClosed_zeroLocusSubset I) :=
  Functor.rightDerivedZeroIsoSelf _

/-- Sections over `U = Spec A ∖ V(I)` read as `A`-modules through
`Stacks.LocalCohomologyTilde.globalToBase` are
`Stacks.LocalCohomology.sectionsOnAffineComplement`: both restrict the scalars of the sections
over `U` along `A ≅ Γ(Spec A, 𝒪) ⟶ Γ(U, 𝒪)`. -/
public theorem sectionsOnComplement_zeroLocus_eq (R : Type u) [CommRing R] (I : Ideal R) :
    sectionsOnComplement (Spec (CommRingCat.of R)).toRingedSpace
          (zeroLocusSubset (A := CommRingCat.of R) I)
          (isClosed_zeroLocusSubset (A := CommRingCat.of R) I) ⋙
        globalToBase (CommRingCat.of R) =
      Stacks.LocalCohomology.sectionsOnAffineComplement R I :=
  rfl

/-- **Degree-zero cohomology of `M̃` on the complement of `V(I)` is the module of sections there.**
The `A`-module `H⁰(U, M̃)` of `Stacks.LocalCohomologySequence.complementCohomologyBase` is the
module of sections of `M̃` over the open `U = Spec A ∖ V(I)`. -/
public def complementCohomologyBaseZeroIso (R : Type u) [CommRing R] (I : Ideal R)
    (M : ModuleCat.{u} (CommRingCat.of R)) :
    complementCohomologyBase (A := CommRingCat.of R) I M 0 ≅
      (Stacks.LocalCohomology.sectionsOnAffineComplement R I).obj (tildeSheaf M) :=
  (globalToBase (CommRingCat.of R)).mapIso
    ((complementCohomologyZeroIso (A := CommRingCat.of R) I).app (tildeSheaf M))

/-- **Degree-zero cohomology of `M̃` on the complement of `V(I)` is the global sections of its
restriction to the open subscheme `U`**, that is, `Stacks.LocalCohomology.complementGlobalSections`
of `Stacks.LocalCohomology.complementTilde`. -/
public def complementCohomologyBaseZeroIsoGlobalSections (R : Type u) [CommRing R] (I : Ideal R)
    (M : ModuleCat.{u} (CommRingCat.of R)) :
    complementCohomologyBase (A := CommRingCat.of R) I M 0 ≅
      Stacks.LocalCohomology.complementGlobalSections R I
        (Stacks.LocalCohomology.complementTilde R I M) :=
  complementCohomologyBaseZeroIso R I M ≪≫
    ((Stacks.LocalCohomology.sectionsOnAffineComplementIso (A := R) I).app (tildeSheaf M)).symm

end Stacks.LocalCohomologySequence

end
