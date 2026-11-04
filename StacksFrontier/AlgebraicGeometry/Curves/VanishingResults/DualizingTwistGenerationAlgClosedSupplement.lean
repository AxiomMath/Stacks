module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingTwistGenerationAlgClosed
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafCohenMacaulay
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingTwistGeneration
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingTwistSectionCount
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.SectionMultiplicationExtension
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.SituationVeryAmpleGeneration
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.TwistUntwistFiniteType
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.VeryAmpleVanishAtClosedPoint
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingTwistGenerationSupplement
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingTwistGenerationCoherent

/-!
# Further results on `DualizingTwistGenerationAlgClosed`

Results about the objects of
`StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingTwistGenerationAlgClosed` that
need imports beyond those of that module.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Ample (nonvanishingLocus)

universe u

namespace AlgebraicGeometry

namespace CohenMacaulayCurveSituation

variable (S : CohenMacaulayCurveSituation.{u})

/-- **What Section [Stacks, Tag 0B5B] attaches to the section of [Stacks, Tag 0B58] at a closed
point.** In Situation [Stacks, Tag 0B5D] over an algebraically closed field, for a very ample
invertible `ℒ` of degree at least two whose twist `ω_X ⊗ ℒ` is of finite type, every closed point
`x` carries the presentation
`AlgebraicGeometry.CohenMacaulayCurveSituation.VanishingSectionPresentation`: an exact sequence
`ω_X ⟶ ω_X ⊗ ℒ ⟶ 𝒬 ⟶ 0` whose quotient has zero-dimensional support and exactly `deg(ℒ)` global
sections, and whose first map lands in `𝔪_x (ω_X ⊗ ℒ)_x`.

The section itself is `exists_globalSection_vanishing_genericPoint`, which is [Stacks, Tag 0B58].
Multiplication by it, the zero-dimensionality of the support of its cokernel and the injectivity
of multiplication — which is where the Cohen--Macaulay assertion of clause (2) of
[Stacks, Tag 0BS2] enters, through
`noCoherentSubmoduleOfZeroDimensionalSupport_dualizingSheafOverField` — are
`exists_shortExact_sectionMul`. The count `dim_k H⁰(X, 𝒬) = deg(ℒ)` is
`finrank_cohomologyOverField_zero_eq_invertibleCurveDegree`, whose two inputs
`H⁰(X, ℒ^{⊗ -1}) = 0` and `H¹(X, ω_X ⊗ ℒ) = 0` are
`subsingleton_globalSections_tensorPowerModule_neg_one` and
`isZero_cohomologyOverField_one_dualizing_tensorSheaf`, the second of them [Stacks, Tag 0B62].
Coherence of `ω_X` and of `ω_X ⊗ ℒ` comes from `hFft` by
`isCoherent_dualizingSheafOverField_of_isFiniteType_tensorSheaf` and
`isCoherent_tensorSheaf_dualizingSheafOverField_of_isFiniteType`. -/
public def vanishingSectionData_dualizing_tensorSheaf [IsAlgClosed S.k] (L : S.X.Modules)
    [SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 L]
    (hL : Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple S.f L)
    (hFft : ((((Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨S.X.presheaf, CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp _ S.X.presheaf
                  (CategoryTheory.forget₂ CommRingCat RingCat)
                  S.X.ringCatSheaf.property⟩).obj
              (Stacks.Duality.dualizingSheafOverField S.f)).obj L)).IsFiniteType)
    (hd : 2 ≤ invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one) L)
    (x : S.X) (hx : IsClosed ({x} : Set S.X)) :
    S.VanishingSectionPresentation (Stacks.Duality.dualizingSheafOverField S.f)
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
                  ⟨S.X.presheaf, CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp _ S.X.presheaf
                    (CategoryTheory.forget₂ CommRingCat RingCat)
                    S.X.ringCatSheaf.property⟩).obj
                (Stacks.Duality.dualizingSheafOverField S.f)).obj L))
      (invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one) L) x :=
  have hωc : (Stacks.Duality.dualizingSheafOverField S.f).IsCoherent :=
    S.isCoherent_dualizingSheafOverField_of_isFiniteType_tensorSheaf L hFft
  have hFc : ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨S.X.presheaf, CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp _ S.X.presheaf
                (CategoryTheory.forget₂ CommRingCat RingCat)
                S.X.ringCatSheaf.property⟩).obj
            (Stacks.Duality.dualizingSheafOverField S.f)).obj L)).IsCoherent :=
    S.isCoherent_tensorSheaf_dualizingSheafOverField_of_isFiniteType L hFft
  have hs := S.exists_globalSection_vanishing_genericPoint L hL x hx
  have hdata := @CohenMacaulayCurveSituation.exists_shortExact_sectionMul S
    (Stacks.Duality.dualizingSheafOverField S.f) L _ hωc hFc
    S.noCoherentSubmoduleOfZeroDimensionalSupport_dualizingSheafOverField x hx hs.choose
    hs.choose_spec.1 hs.choose_spec.2
  { Q := hdata.choose
    α := hdata.choose_spec.choose
    β := hdata.choose_spec.choose_spec.choose
    comp_eq_zero := hdata.choose_spec.choose_spec.choose_spec.choose
    exact := hdata.choose_spec.choose_spec.choose_spec.choose_spec.1.exact
    epi := hdata.choose_spec.choose_spec.choose_spec.choose_spec.1.epi_g
    isQuasicoherent := hdata.choose_spec.choose_spec.choose_spec.choose_spec.2.2.1
    supp_dim_le := hdata.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.1
    finrank_cohomology_zero :=
      @CohenMacaulayCurveSituation.finrank_cohomologyOverField_zero_eq_invertibleCurveDegree
        S L _ (Stacks.Duality.dualizingSheafOverField S.f)
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
                    ⟨S.X.presheaf, CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp _ S.X.presheaf
                      (CategoryTheory.forget₂ CommRingCat RingCat)
                      S.X.ringCatSheaf.property⟩).obj
                  (Stacks.Duality.dualizingSheafOverField S.f)).obj L))
        hdata.choose hωc hFc hdata.choose_spec.choose_spec.choose_spec.choose_spec.2.1
        hdata.choose_spec.choose hdata.choose_spec.choose_spec.choose
        hdata.choose_spec.choose_spec.choose_spec.choose
        hdata.choose_spec.choose_spec.choose_spec.choose_spec.1
        hdata.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.1 rfl rfl
        (S.subsingleton_globalSections_tensorPowerModule_neg_one L hL hd)
        (S.isZero_cohomologyOverField_one_dualizing_tensorSheaf L hL hd)
    range_modulesStalk_le :=
      hdata.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.2 }

/-- **Stacks Project, Tag 0B5H over an algebraically closed field.** In Situation
[Stacks, Tag 0B5D] with `k` algebraically closed, let `ω_X = H^{-1}(f^×(𝒪_{Spec k}))` be the
dualizing sheaf of [Stacks, Tag 0BS2] and let `ℒ` be a very ample invertible `𝒪_X`-module with
`deg(ℒ) ≥ 2`. Then `ω_X ⊗ ℒ` is generated by its global sections.

The section of `ℒ` vanishing at a closed point which the source's proof chooses is
`exists_globalSection_vanishing_genericPoint`, proved here from [Stacks, Tag 0B58], and what
Section [Stacks, Tag 0B5B] does with such a section — the exact sequence
`ω_X ⟶ ω_X ⊗ ℒ ⟶ 𝒬 ⟶ 0` with `𝒬` of zero-dimensional support and `deg(ℒ)` global sections — is
`vanishingSectionData_dualizing_tensorSheaf`. See the module documentation for the one carried
input, `hFft`, the coherence assertion of clause (2) of [Stacks, Tag 0BS2], and for the base
change to `k̄` that the general case would need.

Cf. Stacks Tag 0B5H; not registered because it carries the hypothesis `hFft`, finite type of `ω_X ⊗
L` (the coherence assertion of clause (2) of Stacks Tag 0BS2), and is stated over an algebraically
closed field only. -/
public theorem nonempty_generatingSections_dualizing_tensorSheaf_of_isAlgClosed [IsAlgClosed S.k]
    (L : S.X.Modules) [SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 L]
    (hL : Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple S.f L)
    (hFft : ((((Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨S.X.presheaf, CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp _ S.X.presheaf
                  (CategoryTheory.forget₂ CommRingCat RingCat)
                  S.X.ringCatSheaf.property⟩).obj
              (Stacks.Duality.dualizingSheafOverField S.f)).obj L)).IsFiniteType)
    (hd : 2 ≤ invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one) L) :
    Nonempty ((((Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨S.X.presheaf, CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp _ S.X.presheaf
                  (CategoryTheory.forget₂ CommRingCat RingCat)
                  S.X.ringCatSheaf.property⟩).obj
              (Stacks.Duality.dualizingSheafOverField S.f)).obj L)).GeneratingSections :=
  S.nonempty_generatingSections_dualizing_tensorSheaf L hFft hd fun x hx =>
    S.vanishingSectionData_dualizing_tensorSheaf L hL hFft hd x hx

end CohenMacaulayCurveSituation

end AlgebraicGeometry

end
