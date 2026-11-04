module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategoryModel
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionRightAdjointSheafHomLocallySmall
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportQuasicoherentAnyModel
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpExceptionalDualizing
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalDualizingSheafNormalized
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonTransport
import StacksCore.Tactic.StacksAttribute

/-!
# `ω_E = H¹(a(ω_X))` is the dualizing sheaf of the exceptional curve over `κ`

In Situation [Stacks, Tag 0B4W] let `X` be the blowup of `Spec(A)` in the maximal ideal,
`i : E ⟶ X` its exceptional divisor and `g : E ⟶ Spec(κ)` the structure morphism of `E` over the
centre. Let `ω_A` be a dualizing module for `A` and let `ω_X` be a dualizing module on `X`
normalized in the sense of [Stacks, Remark 0B4R]. This file proves

`AlgebraicGeometry.BlowUpDualizing.exceptionalDualizingModule A ω_X ≅`
`Stacks.Duality.dualizingSheafOverField g`,

so that the module clause (1) of [Stacks, Tag 0B64]
(`AlgebraicGeometry.BlowUpDualizing.nonempty_exceptionalDualizingModule_iso_curveTwist`)
identifies with `ω_X|_E ⊗ 𝒪_E(-1)` is *the* dualizing sheaf of `E` as a proper curve over `κ`.
The corollary
`AlgebraicGeometry.BlowUpDualizing.nonempty_pullback_iso_dualizingSheafOverField_twist` is the
form the source uses in the proofs of clauses (2) and (3) of that tag: `ω_X|_E ≅ ω_E ⊗ 𝒪_E(1)`.

## Main results

* `AlgebraicGeometry.BlowUpDualizing`
  `.nonempty_exceptionalDualizingModule_iso_dualizingSheafOverField` — the identification.
* `AlgebraicGeometry.BlowUpDualizing.nonempty_dualizingSheafOverField_iso_curveTwist` —
  **clause (1) of [Stacks, Tag 0B64]**, `ω_E ≅ ω_X|_E ⊗ 𝒪_E(-1)` for the dualizing sheaf `ω_E` of
  `E` over `κ`, and the attribute site of that clause.
* `AlgebraicGeometry.BlowUpDualizing.nonempty_pullback_iso_dualizingSheafOverField_twist` —
  `ω_X|_E ≅ ω_E(1)` with `ω_E = Stacks.Duality.dualizingSheafOverField g`.

## The proof

`AlgebraicGeometry.RationalSingularitySituation`
`.nonempty_homologyOne_twistedInverseImage_iso_dualizingSheaf_of_dualizingNormalization`
propagates the normalization of [Stacks, Remark 0B4R] along the square `g ≫ j = i ≫ f` and reads
it on cohomology; its `i^!` is the right adjoint of [Stacks, Tag 0A9E] at the locally small
derived category of [Stacks, Tag 079Q]. `exceptionalDualizingModule` is instead `H¹` of derived
sheaf Hom with exact support at `CategoryTheory.HasDerivedCategory.standard`. The two are joined
by [Stacks, Tag 0A9X] at the locally small model,
`Stacks.Duality.LocallySmall.isDerivedSheafHomRightAdjoint_of_pseudoCoherent`, fed with the
adjunction of [Stacks, Tag 0A9E], and by a crossing of models for `R𝓗om(𝒪_E, -)`, for `H¹` and for
placement in degree zero (`Stacks.Duality.AnyModel.derivedSheafHomExactSupportModelIso`,
`StacksDraft.DerivedModel.modelHomologyFunctorIso`,
`StacksDraft.DerivedModel.modelSingleFunctorIso`).

## Provenance

The model comparisons `StacksDraft.DerivedModel.modelCompQhIso`,
`StacksDraft.DerivedModel.modelSingleFunctorIso` and the identification itself are used as they
stand; the comparison for `R𝓗om(𝒪_E, -)` is stated here for the arbitrary-model
functor `Stacks.Duality.AnyModel.derivedSheafHomExactSupport` of this tree.

## References

* [Stacks Project, Tag 0B64](https://stacks.math.columbia.edu/tag/0B64)
* [Stacks Project, Tag 0B4W](https://stacks.math.columbia.edu/tag/0B4W)
* [Stacks Project, Tag 0B4R](https://stacks.math.columbia.edu/tag/0B4R)
* [Stacks Project, Tag 0A9X](https://stacks.math.columbia.edu/tag/0A9X)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open Stacks.Duality (singleQuasiCoherent)
open StacksDraft.DerivedModel (modelEquiv modelHomologyFunctorIso rightDerivedModelIso)

universe w z u v

namespace StacksDraft.DerivedModel

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- **The comparison equivalence identifies the two localizations of the homotopy category.** It
is the comparison of the two localizations `Qh` themselves, so this is
`CategoryTheory.Localization.compUniqFunctor`. -/
def modelCompQhIso (h₁ : HasDerivedCategory.{w} A) (h₂ : HasDerivedCategory.{z} A) :
    @DerivedCategory.Qh A _ _ h₁ ⋙ (modelEquiv h₁ h₂).functor ≅
      @DerivedCategory.Qh A _ _ h₂ :=
  Localization.compUniqFunctor _ _ _

/-- **The comparison equivalence identifies the two single-object functors.** An object of `A`
placed in degree `n`, read in one model and carried over by the comparison, is the same object
placed in degree `n` in the other model. -/
def modelSingleFunctorIso (h₁ : HasDerivedCategory.{w} A) (h₂ : HasDerivedCategory.{z} A)
    (n : ℤ) :
    @DerivedCategory.singleFunctor A _ _ h₁ n ⋙ (modelEquiv h₁ h₂).functor ≅
      @DerivedCategory.singleFunctor A _ _ h₂ n :=
  Functor.associator (CochainComplex.singleFunctor A n) (@DerivedCategory.Q A _ _ h₁)
      (modelEquiv h₁ h₂).functor ≪≫
    Functor.isoWhiskerLeft (CochainComplex.singleFunctor A n) (modelCompQIso h₁ h₂)

end StacksDraft.DerivedModel

namespace Stacks.Duality.AnyModel

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})

/-- **`R ℰom(𝒪_Z, -)` read at two models of the derived category.** The right derived functor of
sheaf Hom with exact support along a closed quotient morphism of ringed spaces, taken at one
choice of derived categories and at another, agree up to the comparison equivalences on source
and target: both are total right derived functors of the same functor out of the homotopy
category, and a total right derived functor is unique up to a canonical isomorphism. -/
def derivedSheafHomExactSupportModelIso
    (hX₁ : HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing S.X)))
    (hZ₁ : HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing S.Z)))
    (hX₂ : HasDerivedCategory.{z} (SheafOfModules.{u} (structureSheafRing S.X)))
    (hZ₂ : HasDerivedCategory.{z} (SheafOfModules.{u} (structureSheafRing S.Z))) :
    @derivedSheafHomExactSupport S hX₁ hZ₁ ⋙ (modelEquiv hZ₁ hZ₂).functor ≅
      (modelEquiv hX₁ hX₂).functor ⋙ @derivedSheafHomExactSupport S hX₂ hZ₂ :=
  rightDerivedModelIso
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing S.X))
      (ComplexShape.up ℤ))
    (@derivedSheafHomExactSupportComparison S hX₁ hZ₁)
    (@derivedSheafHomExactSupportComparison S hX₂ hZ₂)
    (StacksDraft.DerivedModel.modelCompQhIso hX₁ hX₂)
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (StacksDraft.DerivedModel.modelCompQhIso hZ₁ hZ₂))

end Stacks.Duality.AnyModel

namespace AlgebraicGeometry.BlowUpDualizing

variable (S : RationalSingularitySituation.{u})

/-- **`ecan`: `ω_E = H¹(a(ω_X))` is the dualizing sheaf of `E` over `κ`.** In Situation
[Stacks, Tag 0B4W], for `ω_A` a dualizing module for `A` and `ω_X` a dualizing module on the
blowup normalized relative to `ω_A` in the sense of [Stacks, Remark 0B4R], the module
`AlgebraicGeometry.BlowUpDualizing.exceptionalDualizingModule A ω_X` is the dualizing sheaf
`Stacks.Duality.dualizingSheafOverField g` of the exceptional curve as a proper curve over the
residue field. See the module documentation for the proof. -/
theorem nonempty_exceptionalDualizingModule_iso_dualizingSheafOverField
    (ωA : ModuleCat.{u} S.A) (hωA : Stacks.Duality.IsDualizingRingModule S.A ωA)
    (ωX : (blowUpScheme S.A).Modules)
    (N : letI : IsLocallyNoetherian (rationalSingularitySituationBlowUp S).X :=
        isLocallyNoetherian_blowUpScheme S.A
      (rationalSingularitySituationBlowUp S).DualizingNormalization ωA ωX) :
    Nonempty (exceptionalDualizingModule S.A ωX ≅
      Stacks.Duality.dualizingSheafOverField
        (X := (cohenMacaulayCurveSituationExceptionalDivisor S).X)
        (cohenMacaulayCurveSituationExceptionalDivisor S).f) := by
  let : IsLocallyNoetherian (rationalSingularitySituationBlowUp S).X :=
    isLocallyNoetherian_blowUpScheme S.A
  let := BlowUpDualizing.compactSpace_blowUpScheme S
  let : IsLocallyNoetherian (blowUpScheme S.A) := isLocallyNoetherian_blowUpScheme S.A
  let := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward (exceptionalImmersion S.A)
  let : ωX.IsCoherent := N.isDualizing.1
  have hq : ωX.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent ωX
  obtain ⟨n, hn⟩ := hωA.2
  obtain ⟨espl⟩ :=
    S.nonempty_homologyOne_twistedInverseImage_iso_dualizingSheaf_of_dualizingNormalization
      ωA n hn ωX hq N
  have hpc : PseudoCoherent (exceptionalImmersion S.A) :=
    (pseudoCoherent_iff_locallyOfFiniteType _).2 inferInstance
  obtain ⟨e0A9X⟩ :=
    Stacks.Duality.LocallySmall.isDerivedSheafHomRightAdjoint_of_pseudoCoherent
      (exceptionalImmersion S.A) hpc
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs _) _
      (Stacks.Duality.twistedInverseImageAdjunction (exceptionalImmersion S.A)
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs _))
  let Q := Stacks.Duality.closedQuotient (exceptionalImmersion S.A)
  let hLSX : HasDerivedCategory.{u} (SheafOfModules.{u} (structureSheafRing Q.X)) :=
    inferInstance
  let hLSE : HasDerivedCategory.{u} (SheafOfModules.{u} (structureSheafRing Q.Z)) :=
    inferInstance
  let hstdX := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing Q.X))
  let hstdE := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing Q.Z))
  let M := (@DerivedCategory.singleFunctor _ _ _ hLSX 0).obj ωX
  let HstdE := @DerivedCategory.homologyFunctor _ _ _ hstdE 1
  let HlsE := @DerivedCategory.homologyFunctor _ _ _ hLSE 1
  let DstdE := @Stacks.Duality.AnyModel.derivedSheafHomExactSupport Q hstdX hstdE
  let DlsE := @Stacks.Duality.AnyModel.derivedSheafHomExactSupport Q hLSX hLSE
  let eSingle : (modelEquiv hLSX hstdX).functor.obj M ≅
      (@DerivedCategory.singleFunctor _ _ _ hstdX 0).obj ωX :=
    (StacksDraft.DerivedModel.modelSingleFunctorIso hLSX hstdX 0).app ωX
  let eModel : (modelEquiv hLSE hstdE).functor.obj (DlsE.obj M) ≅
      DstdE.obj ((modelEquiv hLSX hstdX).functor.obj M) :=
    (Stacks.Duality.AnyModel.derivedSheafHomExactSupportModelIso Q hLSX hLSE hstdX hstdE).app M
  let eHom : HstdE.obj ((modelEquiv hLSE hstdE).functor.obj (DlsE.obj M)) ≅ HlsE.obj (DlsE.obj M) :=
    (modelHomologyFunctorIso hLSE hstdE 1).app (DlsE.obj M)
  let eAdj := e0A9X.app
    ⟨singleQuasiCoherent ωX hq 0, ⟨0, fun m hm => by
      show IsZero ((DerivedCategory.homologyFunctor (blowUpScheme S.A).Modules m).obj
        ((DerivedCategory.singleFunctor (blowUpScheme S.A).Modules 0).obj ωX))
      exact DerivedCategory.isZero_of_isGE _ 0 m hm⟩⟩
  let e₁ : HstdE.obj (DstdE.obj ((@DerivedCategory.singleFunctor _ _ _ hstdX 0).obj ωX)) ≅
      HstdE.obj (DstdE.obj ((modelEquiv hLSX hstdX).functor.obj M)) :=
    HstdE.mapIso (DstdE.mapIso eSingle.symm)
  let e₂ : HstdE.obj (DstdE.obj ((modelEquiv hLSX hstdX).functor.obj M)) ≅
      HstdE.obj ((modelEquiv hLSE hstdE).functor.obj (DlsE.obj M)) :=
    HstdE.mapIso eModel.symm
  let e₃ : HlsE.obj (DlsE.obj M) ≅ _ := HlsE.mapIso eAdj.symm
  exact ⟨e₁ ≪≫ e₂ ≪≫ eHom ≪≫ e₃ ≪≫ espl⟩

/-- **[Stacks, Tag 0B64], clause (1).** In Situation [Stacks, Tag 0B4W] let `X` be the blowup of
`Spec(A)` in the maximal ideal with exceptional divisor `i : E ⟶ X`, let `ω_A` be a dualizing
module for `A` and let `ω_X` be the dualizing module of `X`, normalized relative to `ω_A` as in
[Stacks, Remark 0B4R]. Then `ω_E = ω_X|_E ⊗ 𝒪_E(-1)`, where `ω_E` is the dualizing sheaf
`Stacks.Duality.dualizingSheafOverField g` of `E` as a proper curve over the residue field `κ`.

This splices `AlgebraicGeometry.BlowUpDualizing.nonempty_exceptionalDualizingModule_iso_curveTwist`
(the adjunction formula, for the module `H¹(a(ω_X))`) with
`AlgebraicGeometry.BlowUpDualizing.nonempty_exceptionalDualizingModule_iso_dualizingSheafOverField`
(that module is the dualizing sheaf of `E` over `κ`). -/
@[stacks 0B64 "clause (1) in Situation 0B4W: for omega_A a dualizing module for A and omega_X the \
dualizing module of the blowup X of Spec(A) in the maximal ideal, normalized relative to omega_A \
as in Remark 0B4R (DualizingNormalization: omega_X dualizing with f^!(omega_A) = omega_X in degree \
zero), omega_E = omega_X|_E tensor O_E(-1), omega_E the dualizing sheaf dualizingSheafOverField g \
of the exceptional curve E as a proper curve over kappa. The source's route, Lemmas 0AA4 and \
0A9X, is followed: the adjunction formula and the normal sheaf O_E(-1) give \
H^1(a(omega_X)) = omega_X|_E tensor O_E(-1), and the propagation of the normalization along \
g ; j = i ; f identifies H^1(a(omega_X)) with dualizingSheafOverField g. The non-regularity of A \
is not used and not assumed (a generalization). Nothing is carried"]
theorem nonempty_dualizingSheafOverField_iso_curveTwist
    (ωA : ModuleCat.{u} S.A) (hωA : Stacks.Duality.IsDualizingRingModule S.A ωA)
    (ωX : (blowUpScheme S.A).Modules)
    (N : letI : IsLocallyNoetherian (rationalSingularitySituationBlowUp S).X :=
        isLocallyNoetherian_blowUpScheme S.A
      (rationalSingularitySituationBlowUp S).DualizingNormalization ωA ωX) :
    Nonempty (Stacks.Duality.dualizingSheafOverField
        (X := (cohenMacaulayCurveSituationExceptionalDivisor S).X)
        (cohenMacaulayCurveSituationExceptionalDivisor S).f ≅
      curveTwist S.A ((Scheme.Modules.pullback (exceptionalImmersion S.A)).obj ωX) (-1)) := by
  obtain ⟨e₁⟩ := nonempty_exceptionalDualizingModule_iso_curveTwist S.A ωX
  obtain ⟨e₂⟩ := nonempty_exceptionalDualizingModule_iso_dualizingSheafOverField S ωA hωA ωX N
  exact ⟨e₂.symm ≪≫ e₁⟩

/-- **`ω_X|_E ≅ ω_E ⊗ 𝒪_E(1)`**, with `ω_E` the dualizing sheaf of the exceptional curve over
`κ`: clause (1) of [Stacks, Tag 0B64] twisted once, read through
`nonempty_exceptionalDualizingModule_iso_dualizingSheafOverField`. This is the form in which the
source's proofs of clauses (2) and (3) of that tag use clause (1). -/
theorem nonempty_pullback_iso_dualizingSheafOverField_twist
    (ωA : ModuleCat.{u} S.A) (hωA : Stacks.Duality.IsDualizingRingModule S.A ωA)
    (ωX : (blowUpScheme S.A).Modules)
    (N : letI : IsLocallyNoetherian (rationalSingularitySituationBlowUp S).X :=
        isLocallyNoetherian_blowUpScheme S.A
      (rationalSingularitySituationBlowUp S).DualizingNormalization ωA ωX) :
    Nonempty ((Scheme.Modules.pullback (exceptionalImmersion S.A)).obj ωX ≅
      curveTwist S.A (Stacks.Duality.dualizingSheafOverField
        (X := (cohenMacaulayCurveSituationExceptionalDivisor S).X)
        (cohenMacaulayCurveSituationExceptionalDivisor S).f) 1) := by
  obtain ⟨e⟩ := nonempty_dualizingSheafOverField_iso_curveTwist S ωA hωA ωX N
  exact nonempty_pullback_dualizing_iso_curveTwist e

end AlgebraicGeometry.BlowUpDualizing

end
