module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafDuality
public import StacksFrontier.AlgebraicGeometry.DerivedTilde.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalDualizingComplexNormalized
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedDualizingExistence
public import StacksFrontier.RingTheory.Dualizing.CohenMacaulayRings
import all StacksFrontier.RingTheory.Dualizing.CohenMacaulayRings
import StacksCore.Tactic.StacksAttribute

/-!
# `H¹(i^!(f^!ω_A)) ≅ ω_E`, the dualizing sheaf of the exceptional curve over `κ`

In Situation [Stacks, Tag 0B4W] let `X` be the blowup of `Spec(A)` in the maximal ideal,
`i : E ⟶ X` its exceptional divisor and `g : E ⟶ Spec(κ)` the structure morphism of `E` over the
centre, and let `ω_A` be a dualizing module for `A`. This file reads
`…/RationalSingularities/ExceptionalDualizingComplexNormalized.lean` on cohomology:

`H¹(i^!(f^!ω_A)) ≅ Stacks.Duality.dualizingSheafOverField g`,

the right-hand side being `ω_E = H^{-1}(g^!𝒪_{Spec κ})`, the dualizing sheaf of `E` as a proper
curve over `κ`.

Here `f^!ω_A` is `AlgebraicGeometry.RationalSingularitySituation.relativeDualizingComplex` with
`ω_A` in degree **zero**, which is the shape
`AlgebraicGeometry.RationalSingularitySituation.DualizingNormalization` of
`…/RationalSingularities/NormalizedDualizingExistence.lean` normalizes against. So for `ω_X`
normalized in the sense of [Stacks, Remark 0B4R] the left-hand side is `H¹(i^!(ω_X))`, which is
`ω_E` as clause (1) of [Stacks, Tag 0B64] names it — and the statement is `ecan` with `i^!` read
as the [Stacks, Tag 0A9E] right adjoint.

## Main results

* `AlgebraicGeometry.RationalSingularitySituation.localRingDimension_eq_two` — `dim(A) = 2` in the
  `Dualizing.localRingDimension` spelling the normalizing shift uses.
* `AlgebraicGeometry.RationalSingularitySituation`
  `.nonempty_homologyOne_twistedInverseImage_relativeDualizingComplex_iso_dualizingSheaf` — the
  isomorphism above, with nothing assumed beyond a dualizing module for `A`.
* `AlgebraicGeometry.RationalSingularitySituation`
  `.nonempty_homologyOne_twistedInverseImage_iso_dualizingSheaf_of_dualizingNormalization` — the
  same read at `ω_X`, for `ω_X` normalized in the sense of [Stacks, Remark 0B4R].

## Why the degree is one

The normalized dualizing complex of `A` is `ω_A[-dim A] = ω_A[-2]`, and
`…nonempty_twistedInverseImage_exceptional_iso_dualizingComplexOverField` identifies
`i^!(f^!(ω_A[-2]))` with `g^!(𝒪_{Spec κ})`. Moving the shift across — `i^!` and `f^!` are right
adjoints of shift-compatible functors, so they commute with the shift — gives
`(i^!(f^!(ω_A[0])))⟦2⟧ ≅ g^!(𝒪_{Spec κ})`, and `H^{-1}` of a complex shifted by `2` is `H^1` of
the complex. That `-1` is the degree `Stacks.Duality.dualizingSheafOverField` is taken in, and the
resulting `1` is the degree `AlgebraicGeometry.BlowUpDualizing.exceptionalDualizingModule` is taken
in; the match is the content of [Stacks, Remark 0B4R]'s `ω_X^• = ω_X[2]`, `ω_E^• = ω_E[1]`.

## How `ecan` is reached from here

`ecan` asks for `AlgebraicGeometry.BlowUpDualizing.exceptionalDualizingModule A ω_X`, which is
`H¹` of **derived sheaf Hom with exact support** at `CategoryTheory.HasDerivedCategory.standard`,
where the statements below are `H¹` of the [Stacks, Tag 0A9E] right adjoint at the locally small
model of [Stacks, Tag 079Q]. Identifying those two functors is [Stacks, Tag 0A9X], and that tag
is formalized twice. `Stacks.Duality.isDerivedSheafHomRightAdjoint_of_pseudoCoherent` takes the
right adjoint as a *parameter*, which is of no use at the standard model, where the
`HasCoproducts` of Brown representability fails and no parameter could be produced;
`Stacks.Duality.isDerivedSheafHomRightAdjoint_twistedInverseImage` of
`…/Duality/ClosedImmersionRightAdjointLocallySmall.lean` instead *produces* it, as the
[Stacks, Tag 0A9E] twisted inverse image, at the locally small model where Brown representability
does apply. That is the restatement the statements below were waiting for, and with it `ecan` is
`AlgebraicGeometry.BlowUpDualizing`
`.nonempty_exceptionalDualizingModule_iso_dualizingSheafOverField` of
`…/Duality/ExceptionalDualizingSheafIdentification.lean`; the crossing between the two models is
`closedImmersionDerivedSheafHomModelIso` with `modelHomologyFunctorIso` and
`modelSingleFunctorIso`.

No `@[stacks]` attribute is attached here: what this file assembles is the propagation of the
normalization, one link of that chain. Clause (2) of [Stacks, Tag 0B64] is registered on
`…isZero_firstCohomology_dualizingTwist_of_isDualizingRingModule` of that same `Duality/` file,
and clause (3) on `AlgebraicGeometry.BlowUpDualizing.epi_dualizingPullbackMap_of_normalized` of
`…/RationalSingularities/BlowUpDualizingGeneration.lean`, which still takes the global generation
of [Stacks, Tag 0B5H].

## Implementation notes

*Where `homologyShiftNatIso` belongs.* `AlgebraicGeometry.derivedCategoryHomologyShiftNatIso` is
generic and belongs in `…/Algebra/Homology/DerivedCategory/`; it is stated here because that part
of the tree is being extended elsewhere. It is the general form of
`Stacks.Duality.homologyShiftNatIso` of `…/Duality/ProperOverFieldDuality.lean`, which is the
case `a = 0` over a field.

## References

* [Stacks Project, Tag 0B4W](https://stacks.math.columbia.edu/tag/0B4W)
* [Stacks Project, Tag 0B4R](https://stacks.math.columbia.edu/tag/0B4R)
* [Stacks Project, Tag 0B64](https://stacks.math.columbia.edu/tag/0B64)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0A9X](https://stacks.math.columbia.edu/tag/0A9X)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Duality (singleQuasiCoherent)

universe u

namespace AlgebraicGeometry

/-- **`Hᵃ(K⟦n⟧) ≅ H^{n+a}(K)`** on the derived category of an abelian category, as a natural
isomorphism of functors. The homology functors form a shift sequence
(`CategoryTheory.Functor.ShiftSequence`) and `DerivedCategory.shift_homologyFunctor` identifies the
members of that sequence with the homology functors. -/
def derivedCategoryHomologyShiftNatIso (C : Type*) [Category C] [Abelian C]
    [HasDerivedCategory C] (n a a' : ℤ) (h : n + a = a') :
    shiftFunctor (DerivedCategory C) n ⋙ DerivedCategory.homologyFunctor C a ≅
      DerivedCategory.homologyFunctor C a' :=
  Functor.isoWhiskerLeft _ (eqToIso (DerivedCategory.shift_homologyFunctor C a)).symm ≪≫
    (DerivedCategory.homologyFunctor C 0).shiftIso n a a' h ≪≫
    eqToIso (DerivedCategory.shift_homologyFunctor C a')

/-- **Derived sheafification of a module placed in a single degree.** `M-tilde` of `M[m]` is
`(M-tilde)[m]`, read through the inclusion of `D_QCoh(𝒪_{Spec R})`.

This is `CategoryTheory.Functor.mapDerivedCategorySingleFunctor` for the exact functor `~`,
composed with `AlgebraicGeometry.derivedTildeCompι`. It is stated for a *variable* `R`, which is
forced: every typeclass about `AlgebraicGeometry.tilde.functor` is stated for a variable
`R : CommRingCat`, so instance synthesis finds nothing at `CommRingCat.of A` — see the
implementation notes of `…/Homology/PseudoCoherentRelative/TildeOpenImmersion.lean`. -/
def derivedTildeSingleIso (R : CommRingCat.{u}) (M : ModuleCat.{u} R) (m : ℤ) :
    ((derivedTilde R).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) m).obj M)).obj ≅
      (DerivedCategory.singleFunctor (Spec R).Modules m).obj ((tilde.functor R).obj M) :=
  (derivedTildeCompι R).app _ ≪≫ ((tilde.functor R).mapDerivedCategorySingleFunctor m).app M

namespace RationalSingularitySituation

variable (S : RationalSingularitySituation.{u})

/-- **`dim(A) = 2` in Situation [Stacks, Tag 0B4W]**, read as the natural number
`Dualizing.localRingDimension` rather than the `WithBot ℕ∞`-valued `ringKrullDim`. This is the
spelling in which the normalizing shift of a dualizing module is pinned, by
`Dualizing.isNormalizedDualizingComplex_single_neg_localRingDimension`. -/
theorem localRingDimension_eq_two : Dualizing.localRingDimension S.A = 2 := by
  have h := Dualizing.localRingDimension_cast_eq (A := S.A)
  rw [S.dimension_two] at h
  rw [show ((2 : WithBot ℕ∞)) = (((2 : ℕ) : ℕ∞) : WithBot ℕ∞) by norm_num] at h
  exact Nat.cast_inj.mp (WithBot.coe_inj.mp h)

/-- **`ω_A` in degree zero, shifted by `dim(A)`, is `ω_A` in degree `-dim(A)` after
sheafification.** The left-hand side is the object [Stacks, Remark 0B4R] normalizes `ω_X` against,
`AlgebraicGeometry.RationalSingularitySituation.baseDualizingComplex`; the right-hand side is the
normalized dualizing complex of `A` sheafified, which
`…nonempty_twistedInverseImage_residuePoint_iso_single` evaluates `j^!` at.

Derived sheafification carries a module in a single degree to its sheafification in that degree
(`CategoryTheory.Functor.mapDerivedCategorySingleFunctor`), and a module in degree zero shifted by
`d` is that module in degree `-d` (`DerivedCategory.singleFunctors`). -/
def baseDualizingComplexShiftIso (ωA : ModuleCat.{u} S.A) :
    (S.baseDualizingComplex ωA)⟦(Dualizing.localRingDimension S.A : ℤ)⟧ ≅
      (derivedTilde (CommRingCat.of S.A)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} S.A)
          (-(Dualizing.localRingDimension S.A : ℤ))).obj ωA) :=
  (ObjectProperty.fullyFaithfulι _).preimageIso
    (((ObjectProperty.ι _).commShiftIso
        (Dualizing.localRingDimension S.A : ℤ)).app (S.baseDualizingComplex ωA) ≪≫
      ((DerivedCategory.singleFunctors (Spec (CommRingCat.of S.A)).Modules).shiftIso
          (Dualizing.localRingDimension S.A : ℤ)
          (-(Dualizing.localRingDimension S.A : ℤ)) 0 (by omega)).app
        ((tilde.functor (CommRingCat.of S.A)).obj ωA) ≪≫
      (derivedTildeSingleIso (CommRingCat.of S.A) ωA
        (-(Dualizing.localRingDimension S.A : ℤ))).symm)

/-- **`H^{dim A - 1}(i^!(f^!ω_A)) ≅ ω_E`.** In Situation [Stacks, Tag 0B4W], for `ω_A` a dualizing
module for `A`, the cohomology of the exceptional inverse image along `i : E ⟶ X` of the relative
dualizing complex `f^!(ω_A)` — `ω_A` in degree zero, the shape [Stacks, Remark 0B4R] normalizes
`ω_X` against — in degree `dim(A) - 1` is the dualizing sheaf of `E` as a proper curve over the
residue field.

This is `…nonempty_twistedInverseImage_exceptional_iso_dualizingComplexOverField`, which reads the
same statement at `ω_A` in degree `-dim(A)`, with the shift `⟦dim A⟧` moved across `f^!` and `i^!`
— both commute with the shift, being right adjoints of shift-compatible functors — and then read
on cohomology: `H^{-1}` of a complex shifted by `dim(A)` is `H^{dim A - 1}` of the complex, and
`-1` is the degree `Stacks.Duality.dualizingSheafOverField` is taken in.

The degree is given as a parameter `m` with `dim(A) = m + 1` so that the dimension does not have
to be rewritten inside a type; `…nonempty_homologyOne_twistedInverseImage_iso_dualizingSheaf` is
the case `m = 1`. -/
theorem nonempty_homology_twistedInverseImage_relativeDualizingComplex_iso_dualizingSheaf
    (ωA : ModuleCat.{u} S.A) (n : ℤ)
    (hn : @Dualizing.IsDualizingComplex S.A _ _ (HasDerivedCategory.standard (ModuleCat.{u} S.A))
      ((@DerivedCategory.singleFunctor (ModuleCat.{u} S.A) _ _
        (HasDerivedCategory.standard (ModuleCat.{u} S.A)) n).obj ωA))
    (m : ℤ) (hm : (Dualizing.localRingDimension S.A : ℤ) = m + 1) :
    letI : IsProper (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A)) :=
      (cohenMacaulayCurveSituationExceptionalDivisor S).proper
    letI := BlowUpDualizing.compactSpace_blowUpScheme S
    letI := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward
      (BlowUpDualizing.exceptionalImmersion S.A)
    Nonempty ((DerivedCategory.homologyFunctor
          (BlowUpDualizing.exceptionalCurve S.A).Modules m).obj
        ((Stacks.Duality.twistedInverseImage (BlowUpDualizing.exceptionalImmersion S.A)
            (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
          ((rationalSingularitySituationBlowUp S).relativeDualizingComplex ωA)).obj ≅
      Stacks.Duality.dualizingSheafOverField
        (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))) := by
  let : IsProper (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A)) :=
    (cohenMacaulayCurveSituationExceptionalDivisor S).proper
  let := BlowUpDualizing.compactSpace_blowUpScheme S
  let := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward
    (blowUpToBase (BlowUpDualizing.centre S.A))
  let := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward
    (BlowUpDualizing.exceptionalImmersion S.A)
  let := (Stacks.Duality.twistedInverseImageAdjunction
    (blowUpToBase (BlowUpDualizing.centre S.A))
    (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs _)).rightAdjointCommShift ℤ
  let := (Stacks.Duality.twistedInverseImageAdjunction
    (BlowUpDualizing.exceptionalImmersion S.A)
    (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs _)).rightAdjointCommShift ℤ
  obtain ⟨L⟩ :=
    S.nonempty_twistedInverseImage_exceptional_iso_dualizingComplexOverField ωA n hn
  refine ⟨?_⟩
  -- `H^m(A) ≅ H^{-1}(A⟦dim A⟧)`, for `A` the underlying complex of `i^!(f^!ω_A)`.
  refine ((derivedCategoryHomologyShiftNatIso (BlowUpDualizing.exceptionalCurve S.A).Modules
    (Dualizing.localRingDimension S.A : ℤ) (-1) m (by omega)).app _).symm ≪≫ ?_
  refine (DerivedCategory.homologyFunctor
    (BlowUpDualizing.exceptionalCurve S.A).Modules (-1)).mapIso ?_
  -- The shift of the underlying complex is the underlying complex of the shift.
  refine (((ObjectProperty.ι _).commShiftIso
    (Dualizing.localRingDimension S.A : ℤ)).app _).symm ≪≫ ?_
  refine (ObjectProperty.ι _).mapIso ?_
  refine ?_ ≪≫ L
  -- `(i^!(f^!ω_A))⟦dim A⟧ ≅ i^!(f^!(ω_A[-dim A]))`: move the shift across `i^!`, then across
  -- `f^!`, then recognise `ω_A[0]⟦dim A⟧` as `ω_A[-dim A]` after sheafification.
  refine (((Stacks.Duality.twistedInverseImage (BlowUpDualizing.exceptionalImmersion S.A)
    (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs _)).commShiftIso
      (Dualizing.localRingDimension S.A : ℤ)).app _).symm ≪≫ ?_
  refine (Stacks.Duality.twistedInverseImage (BlowUpDualizing.exceptionalImmersion S.A)
    (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs _)).mapIso ?_
  refine (((Stacks.Duality.twistedInverseImage (blowUpToBase (BlowUpDualizing.centre S.A))
    (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs _)).commShiftIso
      (Dualizing.localRingDimension S.A : ℤ)).app _).symm ≪≫ ?_
  exact (Stacks.Duality.twistedInverseImage (blowUpToBase (BlowUpDualizing.centre S.A))
    (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs _)).mapIso
    ((rationalSingularitySituationBlowUp S).baseDualizingComplexShiftIso ωA)

/-- **`H¹(i^!(f^!ω_A)) ≅ ω_E`** in Situation [Stacks, Tag 0B4W], the case `dim(A) = 2` of
`…nonempty_homology_twistedInverseImage_relativeDualizingComplex_iso_dualizingSheaf`.

Degree one is the degree `AlgebraicGeometry.BlowUpDualizing.exceptionalDualizingModule` is taken
in, which is the degree [Stacks, Remark 0B4R] selects; so for `ω_X` normalized in the sense of
that remark this is `ecan` with `i^!` read as the [Stacks, Tag 0A9E] right adjoint rather than as
derived sheaf Hom with exact support. See the module documentation for the one identification that
separates the two. -/
theorem nonempty_homologyOne_twistedInverseImage_relativeDualizingComplex_iso_dualizingSheaf
    (ωA : ModuleCat.{u} S.A) (n : ℤ)
    (hn : @Dualizing.IsDualizingComplex S.A _ _ (HasDerivedCategory.standard (ModuleCat.{u} S.A))
      ((@DerivedCategory.singleFunctor (ModuleCat.{u} S.A) _ _
        (HasDerivedCategory.standard (ModuleCat.{u} S.A)) n).obj ωA)) :
    letI : IsProper (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A)) :=
      (cohenMacaulayCurveSituationExceptionalDivisor S).proper
    letI := BlowUpDualizing.compactSpace_blowUpScheme S
    letI := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward
      (BlowUpDualizing.exceptionalImmersion S.A)
    Nonempty ((DerivedCategory.homologyFunctor
          (BlowUpDualizing.exceptionalCurve S.A).Modules 1).obj
        ((Stacks.Duality.twistedInverseImage (BlowUpDualizing.exceptionalImmersion S.A)
            (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
          ((rationalSingularitySituationBlowUp S).relativeDualizingComplex ωA)).obj ≅
      Stacks.Duality.dualizingSheafOverField
        (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))) :=
  S.nonempty_homology_twistedInverseImage_relativeDualizingComplex_iso_dualizingSheaf ωA n hn 1
    (by rw [S.localRingDimension_eq_two]; norm_num)


/-- **`ecan` at the locally small model: `H¹(i^!(ω_X)) ≅ ω_E`** for `ω_X` normalized in the sense
of [Stacks, Remark 0B4R].

The normalization `N` identifies `f^!(ω_A)` with `ω_X` in degree zero, so this is
`…nonempty_homologyOne_twistedInverseImage_relativeDualizingComplex_iso_dualizingSheaf` read at
`ω_X`. The conclusion is `ecan` —
`AlgebraicGeometry.BlowUpDualizing.exceptionalDualizingModule A ω_X ≅`
`Stacks.Duality.dualizingSheafOverField g` — with one difference, and it is the only one left:
`exceptionalDualizingModule` takes the `H¹` of **derived sheaf Hom with exact support** at
`CategoryTheory.HasDerivedCategory.standard`, where this takes the `H¹` of the
[Stacks, Tag 0A9E] right adjoint `i^!` at the locally small model of [Stacks, Tag 079Q]. That
identification is [Stacks, Tag 0A9X] at the locally small model; see the module documentation
for it and for `ecan` itself. -/
theorem nonempty_homologyOne_twistedInverseImage_iso_dualizingSheaf_of_dualizingNormalization
    (ωA : ModuleCat.{u} S.A) (n : ℤ)
    (hn : @Dualizing.IsDualizingComplex S.A _ _ (HasDerivedCategory.standard (ModuleCat.{u} S.A))
      ((@DerivedCategory.singleFunctor (ModuleCat.{u} S.A) _ _
        (HasDerivedCategory.standard (ModuleCat.{u} S.A)) n).obj ωA))
    (ωX : (BlowUpDualizing.blowUpScheme S.A).Modules) (hq : ωX.IsQuasicoherent)
    (N : letI : IsLocallyNoetherian (rationalSingularitySituationBlowUp S).X :=
        BlowUpDualizing.isLocallyNoetherian_blowUpScheme S.A
      (rationalSingularitySituationBlowUp S).DualizingNormalization ωA ωX) :
    letI : IsProper (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A)) :=
      (cohenMacaulayCurveSituationExceptionalDivisor S).proper
    letI := BlowUpDualizing.compactSpace_blowUpScheme S
    letI := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward
      (BlowUpDualizing.exceptionalImmersion S.A)
    Nonempty ((DerivedCategory.homologyFunctor
          (BlowUpDualizing.exceptionalCurve S.A).Modules 1).obj
        ((Stacks.Duality.twistedInverseImage (BlowUpDualizing.exceptionalImmersion S.A)
            (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
          (singleQuasiCoherent ωX hq 0)).obj ≅
      Stacks.Duality.dualizingSheafOverField
        (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))) := by
  let : IsProper (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A)) :=
    (cohenMacaulayCurveSituationExceptionalDivisor S).proper
  let := BlowUpDualizing.compactSpace_blowUpScheme S
  let := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward
    (BlowUpDualizing.exceptionalImmersion S.A)
  let : IsLocallyNoetherian (rationalSingularitySituationBlowUp S).X :=
    BlowUpDualizing.isLocallyNoetherian_blowUpScheme S.A
  obtain ⟨e⟩ :=
    S.nonempty_homologyOne_twistedInverseImage_relativeDualizingComplex_iso_dualizingSheaf ωA n hn
  have hrel : (rationalSingularitySituationBlowUp S).relativeDualizingComplex ωA ≅
      singleQuasiCoherent ωX hq 0 :=
    (ObjectProperty.fullyFaithfulι _).preimageIso
      (X := (rationalSingularitySituationBlowUp S).relativeDualizingComplex ωA)
      (Y := singleQuasiCoherent ωX hq 0) N.normalizedIso
  refine ⟨(DerivedCategory.homologyFunctor
      (BlowUpDualizing.exceptionalCurve S.A).Modules 1).mapIso
    ((ObjectProperty.ι _).mapIso ((Stacks.Duality.twistedInverseImage
      (BlowUpDualizing.exceptionalImmersion S.A)
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs _)).mapIso
      hrel.symm)) ≪≫ e⟩
end RationalSingularitySituation

end AlgebraicGeometry

end
