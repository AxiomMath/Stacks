module

public import StacksFrontier.Algebra.Homology.DerivedCategory.TriangulatedFunctorShortExactHomology
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupFormsExceptionalComparison
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinMap
public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit

/-!
# Clause (3) of Stacks 0FUU as a vanishing statement

Fix a morphism `f : X ⟶ S` and a closed immersion `i : Z ⟶ X`; let `b : X' ⟶ X` be the blowing
up of `X` along `Z`, `j : E ⟶ X'` its exceptional divisor and `p : E ⟶ Z` the projection onto the
centre. The restriction of forms `ρ : Ω^a_{X'/S} ⟶ j_*Ω^a_{E/S}` is surjective, `j` being an
immersion; call its kernel `𝒦^a`, so that

`0 ⟶ 𝒦^a ⟶ Ω^a_{X'/S} ⟶ j_*Ω^a_{E/S} ⟶ 0`

is exact. The comparison `Rb_*Ω^a_{X'/S} ⟶ i_*Rp_*Ω^a_{E/S}` of clause (3) of
[Stacks, Tag 0FUU] is `Rb_*ρ` followed by isomorphisms, so by the long exact sequence of higher
direct images it is an isomorphism on cohomology in every degree `≥ 1` as soon as
`R^q b_*𝒦^a = 0` for every `q ≥ 1`. That vanishing is what the étale-local argument transports:
unlike the comparison map, a vanishing statement needs no compatibility of the base change
isomorphisms with anything.

## Main definitions

* `Stacks.DeRham.blowupFormsKernel`: the kernel `𝒦^a` of the restriction of forms.

## Main results

* `Stacks.DeRham.epi_blowupFormsRestriction`: the restriction of forms is surjective.
* `Stacks.DeRham.shortExact_blowupFormsKernel`: the short exact sequence above.
* `Stacks.DeRham.isIso_homology_blowupFormsRestrictionDerivedComparison_of_isZero`: **vanishing of
  `R^q b_*𝒦^a` for `q ≥ 1` gives clause (3)**, in an arbitrary model of each derived category.

## References

* [Stacks Project, Tag 0FUU](https://stacks.math.columbia.edu/tag/0FUU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DeRham.BlowupTriangle

universe u

attribute [-instance] CategoryTheory.catToReflQuiver

namespace Stacks.DeRham

variable {S X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i]

/-- **The restriction of forms to the exceptional divisor is surjective**: it is the unit of
`j^* ⊣ j_*`, surjective for the closed immersion `j`, followed by `j_*` of the surjection
`j^*Ω^a_{X'/S} ⟶ Ω^a_{E/S}`, and `j_*` is exact. -/
theorem epi_blowupFormsRestriction (a : ℕ) : Epi (blowupFormsRestriction f i (a : ℤ)) := by
  have h₁ := Stacks.ClosedImmersion.epi_unit_app (exceptionalInclusion i)
    (Scheme.Hom.relativeDifferentialForms (blowupMap i ≫ f) (a : ℤ))
  have : PreservesFiniteColimits (Scheme.Modules.pushforward (exceptionalInclusion i)) :=
    Stacks.ClosedImmersion.preservesFiniteColimits_modulePushforward
      (exceptionalInclusion i).toLRSHom.toShHom (exceptionalInclusion i).isClosedEmbedding
  have h₂ := Scheme.Hom.epi_relativeDifferentialFormsMap (exceptionalInclusion i)
    (blowupMap i ≫ f) (by simp) a
  rw [blowupFormsRestriction, Scheme.Hom.formsDirectImageComparison]
  infer_instance

/-- **The kernel `𝒦^a` of the restriction of forms** `Ω^a_{X'/S} ⟶ j_*Ω^a_{E/S}`: the sheaf of
`a`-forms on the blowup which vanish on the exceptional divisor. -/
abbrev blowupFormsKernel (a : ℤ) : (Stacks.Blowup.blowUp i.ker).Modules :=
  kernel (blowupFormsRestriction f i a)

/-- The short complex `𝒦^a ⟶ Ω^a_{X'/S} ⟶ j_*Ω^a_{E/S}`. -/
abbrev blowupFormsKernelSequence (a : ℤ) :
    ShortComplex (Stacks.Blowup.blowUp i.ker).Modules :=
  ShortComplex.mk (kernel.ι (blowupFormsRestriction f i a)) (blowupFormsRestriction f i a)
    (kernel.condition _)

/-- **The sequence `0 ⟶ 𝒦^a ⟶ Ω^a_{X'/S} ⟶ j_*Ω^a_{E/S} ⟶ 0` is exact.** -/
theorem shortExact_blowupFormsKernel (a : ℕ) :
    (blowupFormsKernelSequence f i (a : ℤ)).ShortExact :=
  ShortComplex.ShortExact.mk'
    (ShortComplex.kernelSequence_exact (blowupFormsRestriction f i (a : ℤ)))
    (inferInstanceAs (Mono (kernel.ι _))) (epi_blowupFormsRestriction f i a)

section Derived

variable [HasDerivedCategory (ModuleSheaves X.toRingedSpace)]
  [HasDerivedCategory (ModuleSheaves (Stacks.Blowup.blowUp i.ker).toRingedSpace)]
  [HasDerivedCategory (ModuleSheaves Z.toRingedSpace)]
  [HasDerivedCategory (ModuleSheaves (Stacks.Blowup.exceptionalDivisor i.ker).toRingedSpace)]

/-- In the comparison of clause (3), everything after `Rb_*ρ` is an isomorphism, so on
cohomology the comparison is invertible exactly when `Rb_*ρ` is. -/
theorem isIso_homology_blowupFormsRestrictionDerivedComparison_iff (a q : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor _ q).map
        (blowupFormsRestrictionDerivedComparison f i a)) ↔
      IsIso ((DerivedCategory.homologyFunctor _ q).map
        ((derivedPushforward (blowupMap i).toLRSHom.toShHom).map
          ((DerivedCategory.singleFunctor _ 0).map (blowupFormsRestriction f i a)))) := by
  let F := derivedPushforward (blowupMap i).toLRSHom.toShHom ⋙
    DerivedCategory.homologyFunctor (ModuleSheaves X.toRingedSpace) q
  have h₁ : IsIso (F.map
        ((DerivedCategory.singleFunctor _ 0).map (blowupFormsRestriction f i a))) ↔
      IsIso (F.map (DerivedCategory.Q.map ((HomologicalComplex.single (ModuleSheaves
        (Stacks.Blowup.blowUp i.ker).toRingedSpace) (ComplexShape.up ℤ) 0).map
          (blowupFormsRestriction f i a)))) :=
    Arrow.isIso_hom_iff_isIso_hom_of_isIso (F.mapArrow.mapIso (Arrow.isoOfNatIso
      (DerivedCategory.singleFunctorIsoCompQ
        (ModuleSheaves (Stacks.Blowup.blowUp i.ker).toRingedSpace) 0)
      (Arrow.mk (blowupFormsRestriction f i a)))).hom
  rw [blowupFormsRestrictionDerivedComparison, Functor.map_comp, isIso_comp_right_iff]
  exact h₁.symm

/-- **Clause (3) of [Stacks, Tag 0FUU] from the vanishing of the higher direct images of the
kernel.** If `R^q b_*𝒦^a = 0` for every `q ≥ 1`, then the comparison
`Rb_*Ω^a_{X'/S} ⟶ i_*Rp_*Ω^a_{E/S}` is an isomorphism on cohomology sheaves in every degree
`q ≥ 1`. -/
theorem isIso_homology_blowupFormsRestrictionDerivedComparison_of_isZero (a : ℕ)
    (h : ∀ q : ℤ, 1 ≤ q → IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((derivedPushforward (blowupMap i).toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor _ 0).obj (blowupFormsKernel f i (a : ℤ))))))
    (q : ℤ) (hq : 1 ≤ q) :
    IsIso ((DerivedCategory.homologyFunctor _ q).map
      (blowupFormsRestrictionDerivedComparison f i (a : ℤ))) := by
  let b := (blowupMap i).toLRSHom.toShHom
  have _ := SheafOfModules.isGrothendieckAbelianU.{u, u, u}
    (structureSheafRing (Stacks.Blowup.blowUp i.ker).toRingedSpace)
  let _ := Functor.IsRightDerivedFunctor.commShift (derivedPushforward b)
    (derivedPushforwardUnit b)
    (HomotopyCategory.quasiIso (ModuleSheaves (Stacks.Blowup.blowUp i.ker).toRingedSpace)
      (ComplexShape.up ℤ)) ℤ
  have _ : (derivedPushforward b).IsTriangulated :=
    Stacks.Injectives.rightDerivedFunctor_isTriangulated (modulePushforward b) _
      (derivedPushforwardUnit b)
  rw [isIso_homology_blowupFormsRestrictionDerivedComparison_iff]
  exact (shortExact_blowupFormsKernel f i a).isIso_homologyFunctor_map_g_of_isZero
    (derivedPushforward b) h q hq

end Derived

end Stacks.DeRham

end
