module

public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateConeFormsDirectImage
public import StacksFrontier.AlgebraicGeometry.DeRham.FormsDerivedComparisonHomology

/-!
# The comparison `Rb_*Ω^a_{L/S} ⟶ i_*Rp_*Ω^a_{P/S}` of clause (3) of Stacks 0FUR

In the standard situation of Section 50.16 of the source — `A = R[x₁, …, x_m, y₁, …, y_n]`
graded by `deg yⱼ = 1`, `X = Spec A`, the centre `i : Z = Spec(A₀) ⟶ X`, the projective bundle
`p : P = Proj(A) ⟶ Z`, and the blowup `b : L = Proj(⨁_d A_{≥ d}) ⟶ X` of `X` along `Z` with its
zero section `0 : P ⟶ L`, so that `b ∘ 0 = i ∘ p` — clause (3) of [Stacks, Tag 0FUR] is about
the canonical map

`Rb_*Ω^a_{L/S} ⟶ i_*Rp_*Ω^a_{P/S}`

in `D(𝒪_X)`. This file constructs it: `Rb_*` of the restriction of forms
`Ω^a_{L/S} ⟶ 0_*Ω^a_{P/S}`, followed by the comparison `0_* ⟶ R0_*` and by the comparisons
`Rb_*R0_* ≅ R(0 ≫ b)_* = R(p ≫ i)_* ≅ Ri_*Rp_*` of [Stacks, Tag 0D5T]. The recipe is the one of
`Stacks.DeRham.blowupFormsRestrictionDerivedComparison`, with the exceptional divisor replaced by
the projective bundle and its inclusion by the zero section, as in the source.

## Main definitions

* `Stacks.DeRham.CoordinateCone.coneFormsRestriction`: the restriction of forms
  `Ω^a_{L/S} ⟶ 0_*Ω^a_{P/S}` along the zero section.
* `Stacks.DeRham.CoordinateCone.coneFormsDerivedComparison`: **the map
  `Rb_*Ω^a_{L/S} ⟶ i_*Rp_*Ω^a_{P/S}` of clause (3)**, in an arbitrary model of each derived
  category.

## References

* [Stacks Project, Tag 0FUR](https://stacks.math.columbia.edu/tag/0FUR)
* [Stacks Project, Tag 0D5T](https://stacks.math.columbia.edu/tag/0D5T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DeRham.BlowupTriangle (unit compIso)

universe u

attribute [-instance] CategoryTheory.catToReflQuiver

namespace Stacks.DeRham.CoordinateCone

variable (R : Type u) [CommRing R] (m n : ℕ)

open Stacks.AlgebraicGeometry.ProjAndSpec
open Stacks.AlgebraicGeometry.ProjAndSpecTruncation (truncationConeData)

/-- The two factorisations `b ∘ 0 = i ∘ p` of `P ⟶ X`. -/
theorem zeroSection_comp_coneToAmbient :
    zeroSection (truncationConeData (yGrading R m n)) ≫ coneToAmbient R m n =
      coneBundleToCentre R m n ≫ coneCentreToAmbient R m n :=
  zeroSection_comp_toSpecA _

/-- **The restriction of forms to the zero section** `Ω^a_{L/S} ⟶ 0_*Ω^a_{P/S}`: the
comparison map on direct images of forms along `0 : P ⟶ L`. -/
def coneFormsRestriction (a : ℤ) :
    Scheme.Hom.relativeDifferentialForms (coneToBase R m n) a ⟶
      (Scheme.Modules.pushforward (zeroSection (truncationConeData (yGrading R m n)))).obj
        (Scheme.Hom.relativeDifferentialForms (coneBundleToBase R m n) a) :=
  Scheme.Hom.formsDirectImageComparison (zeroSection (truncationConeData (yGrading R m n)))
      (coneToBase R m n) a ≫
    (Scheme.Modules.pushforward (zeroSection (truncationConeData (yGrading R m n)))).map
      (eqToHom (congrArg (fun π => Scheme.Hom.relativeDifferentialForms π a)
        (by simp only [coneToBase, coneBundleToBase, coneCentreToBase, ← Category.assoc,
          zeroSection_comp_coneToAmbient])))

section Derived

variable
  [HasDerivedCategory (ModuleSheaves (Stacks.DeRham.coordinateAmbient R m n).toRingedSpace)]
  [HasDerivedCategory (ModuleSheaves (coneTotal R m n).toRingedSpace)]
  [HasDerivedCategory (ModuleSheaves (coneCentre R m n).toRingedSpace)]
  [HasDerivedCategory (ModuleSheaves (coneBundle R m n).toRingedSpace)]

/-- `Rb_*Ω^a_{L/S}`, in `D(𝒪_X)`. -/
abbrev coneFormsDerivedObj (a : ℤ) :
    DerivedCategory (ModuleSheaves (Stacks.DeRham.coordinateAmbient R m n).toRingedSpace) :=
  (derivedPushforward (coneToAmbient R m n).toLRSHom.toShHom).obj
    (DerivedCategory.Q.obj (Stacks.DeRham.singleComplex
      (Scheme.Hom.relativeDifferentialForms (coneToBase R m n) a)))

/-- `i_*Rp_*Ω^a_{P/S}`, in `D(𝒪_X)`. -/
abbrev coneBundleFormsDerivedObj (a : ℤ) :
    DerivedCategory (ModuleSheaves (Stacks.DeRham.coordinateAmbient R m n).toRingedSpace) :=
  (derivedPushforward (coneCentreToAmbient R m n).toLRSHom.toShHom).obj
    ((derivedPushforward (coneBundleToCentre R m n).toLRSHom.toShHom).obj
      (DerivedCategory.Q.obj (Stacks.DeRham.singleComplex
        (Scheme.Hom.relativeDifferentialForms (coneBundleToBase R m n) a))))

omit
  [HasDerivedCategory (ModuleSheaves (Stacks.DeRham.coordinateAmbient R m n).toRingedSpace)]
  [HasDerivedCategory (ModuleSheaves (coneTotal R m n).toRingedSpace)]
  [HasDerivedCategory (ModuleSheaves (coneCentre R m n).toRingedSpace)]
  [HasDerivedCategory (ModuleSheaves (coneBundle R m n).toRingedSpace)] in
/-- The two factorisations `b ∘ 0 = i ∘ p`, on the underlying morphisms of ringed spaces. -/
theorem zeroSection_toShHom_comp :
    (zeroSection (truncationConeData (yGrading R m n))).toLRSHom.toShHom ≫
        (coneToAmbient R m n).toLRSHom.toShHom =
      (coneBundleToCentre R m n).toLRSHom.toShHom ≫ (coneCentreToAmbient R m n).toLRSHom.toShHom :=
  congrArg (fun g => g.toLRSHom.toShHom) (zeroSection_comp_coneToAmbient R m n)

/-- **The canonical map `Rb_*Ω^a_{L/S} ⟶ i_*Rp_*Ω^a_{P/S}` of clause (3) of
[Stacks, Tag 0FUR]**, in `D(𝒪_X)`: `Rb_*` of the restriction of forms `Ω^a_{L/S} ⟶ 0_*Ω^a_{P/S}`
followed by the comparison `0_* ⟶ R0_*`, then the comparisons
`Rb_*R0_* ≅ R(0 ≫ b)_* = R(p ≫ i)_* ≅ Ri_*Rp_*` of [Stacks, Tag 0D5T]; this is the recipe
`Stacks.DeRham.formsDerivedComparisonOf` at the restriction of forms. -/
def coneFormsDerivedComparison (a : ℤ) :
    coneFormsDerivedObj R m n a ⟶ coneBundleFormsDerivedObj R m n a :=
  Stacks.DeRham.formsDerivedComparisonOf (coneToAmbient R m n)
    (zeroSection (truncationConeData (yGrading R m n))) (coneBundleToCentre R m n)
    (coneCentreToAmbient R m n) (zeroSection_toShHom_comp R m n)
    (Scheme.Hom.relativeDifferentialForms (coneBundleToBase R m n) a) (coneFormsRestriction R m n a)

end Derived

end Stacks.DeRham.CoordinateCone

end
