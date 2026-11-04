module

public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupDeRhamTriangleUnits
public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBlowupFormsDirectImage

/-!
# The comparison `Rb_*Ω^a_{X'/S} ⟶ i_*Rp_*Ω^a_{E/S}` of Stacks 0FUU, clause (3)

Fix a morphism `f : X ⟶ S` and a closed immersion `i : Z ⟶ X`. Write `b : X' ⟶ X` for the
blowing up of `X` along `Z`, `j : E ⟶ X'` for its exceptional divisor and `p : E ⟶ Z` for the
projection of the exceptional divisor onto the centre, so that `j ≫ b = p ≫ i`; the exceptional
divisor is read over `S` through the centre. Clause (3) of [Stacks, Tag 0FUU] is about the
canonical map

`Rb_*Ω^a_{X'/S} ⟶ i_*Rp_*Ω^a_{E/S}`

in the derived category `D(𝒪_X)`, of the forms of degree `a` placed in degree `0`. This file
constructs it. It is `Rb_*` of the restriction of forms `Ω^a_{X'/S} ⟶ j_*Ω^a_{E/S}`, followed by
the comparison `j_* ⟶ Rj_*` (invertible, `j` being a closed immersion) and by the comparisons
`Rb_*Rj_* ≅ R(j ≫ b)_* = R(p ≫ i)_* ≅ Ri_*Rp_*` of [Stacks, Tag 0D5T]; `Ri_*` is `i_*`, again
because `i` is a closed immersion.

## Main definitions

* `Stacks.DeRham.blowupFormsRestriction`: the restriction of forms `Ω^a_{X'/S} ⟶ j_*Ω^a_{E/S}`,
  the adjoint transpose of the canonical map `j^*Ω^a_{X'/S} ⟶ Ω^a_{E/S}` of Section 07HX.
* `Stacks.DeRham.blowupFormsRestrictionDerivedComparison`: **the map
  `Rb_*Ω^a_{X'/S} ⟶ i_*Rp_*Ω^a_{E/S}` of clause (3)**, in an arbitrary model of each derived
  category, as `Rb_*ρ` followed by `Stacks.DeRham.blowupFormsDerivedTail`, which is an
  isomorphism.

## Implementation notes

The derived direct images are those of the underlying morphisms of ringed spaces,
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward`, on the categories
`ModuleSheaves Y.toRingedSpace` of `𝒪_Y`-modules, which are `Y.Modules` by definition. The
units and the composition comparisons are those of
`StacksFrontier.AlgebraicGeometry.DeRham.BlowupDeRhamTriangle`, where the same four morphisms enter
the triangle of [Stacks, Tag 0FUV] at the level of de Rham complexes.

## References

* [Stacks Project, Tag 0FUU](https://stacks.math.columbia.edu/tag/0FUU)
* [Stacks Project, Tag 0D5T](https://stacks.math.columbia.edu/tag/0D5T)
* [Stacks Project, Section 07HX](https://stacks.math.columbia.edu/tag/07HX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DeRham.BlowupTriangle

universe u

attribute [-instance] CategoryTheory.catToReflQuiver

namespace Stacks.DeRham

variable {S X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i]

/-- **The restriction of forms to the exceptional divisor** `Ω^a_{X'/S} ⟶ j_*Ω^a_{E/S}`: the
comparison map on direct images of forms along `j : E ⟶ X'`, with `E` read over `S` through the
centre. On sections it restricts a local `a`-form on `X'` to `E`. -/
def blowupFormsRestriction (a : ℤ) :
    Scheme.Hom.relativeDifferentialForms (blowupMap i ≫ f) a ⟶
      (Scheme.Modules.pushforward (exceptionalInclusion i)).obj
        (Scheme.Hom.relativeDifferentialForms (exceptionalStructure f i) a) :=
  Scheme.Hom.formsDirectImageComparison (exceptionalInclusion i) (blowupMap i ≫ f) a ≫
    (Scheme.Modules.pushforward (exceptionalInclusion i)).map
      (eqToHom (congrArg (fun π => Scheme.Hom.relativeDifferentialForms π a)
        (exceptionalInclusion_comp f i)))

/-- The inclusion of the exceptional divisor is a closed immersion. -/
instance isClosedImmersion_exceptionalInclusion : IsClosedImmersion (exceptionalInclusion i) :=
  inferInstanceAs (IsClosedImmersion (Stacks.Blowup.exceptionalIdeal i.ker).subschemeι)

/-- A sheaf of modules on a scheme, as a complex concentrated in degree `0`. -/
abbrev singleComplex {Y : Scheme.{u}} (F : Y.Modules) :
    CochainComplex (ModuleSheaves Y.toRingedSpace) ℤ :=
  (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F

/-- The two factorisations `j ≫ b = p ≫ i` of `E ⟶ X`, on the underlying morphisms of ringed
spaces. -/
theorem exceptionalInclusion_toShHom_comp :
    (exceptionalInclusion i).toLRSHom.toShHom ≫ (blowupMap i).toLRSHom.toShHom =
      (exceptionalProjection i).toLRSHom.toShHom ≫ i.toLRSHom.toShHom :=
  congrArg (fun g => g.toLRSHom.toShHom) (exceptionalInclusion_comp_blowupMap i)

section Derived

variable [HasDerivedCategory (ModuleSheaves X.toRingedSpace)]
  [HasDerivedCategory (ModuleSheaves (Stacks.Blowup.blowUp i.ker).toRingedSpace)]
  [HasDerivedCategory (ModuleSheaves Z.toRingedSpace)]
  [HasDerivedCategory (ModuleSheaves (Stacks.Blowup.exceptionalDivisor i.ker).toRingedSpace)]

/-- `Rb_*Ω^a_{X'/S}`, in `D(𝒪_X)`. -/
abbrev blowupFormsDerivedObj (a : ℤ) :
    DerivedCategory (ModuleSheaves X.toRingedSpace) :=
  (derivedPushforward (blowupMap i).toLRSHom.toShHom).obj
    (DerivedCategory.Q.obj (singleComplex
      (Scheme.Hom.relativeDifferentialForms (blowupMap i ≫ f) a)))

/-- `i_*Rp_*Ω^a_{E/S}`, in `D(𝒪_X)`. -/
abbrev exceptionalFormsDerivedObj (a : ℤ) :
    DerivedCategory (ModuleSheaves X.toRingedSpace) :=
  (derivedPushforward i.toLRSHom.toShHom).obj
    ((derivedPushforward (exceptionalProjection i).toLRSHom.toShHom).obj
      (DerivedCategory.Q.obj (singleComplex
        (Scheme.Hom.relativeDifferentialForms (exceptionalStructure f i) a))))

/-- The part of the comparison of clause (3) after `Rb_*ρ`:
`Rb_*(j_*Ω^a_{E/S}) ⟶ Rb_*Rj_*Ω^a_{E/S} ≅ R(j ≫ b)_*Ω^a_{E/S}`
`= R(p ≫ i)_*Ω^a_{E/S} ≅ Ri_*Rp_*Ω^a_{E/S}`, the comparison `j_* ⟶ Rj_*` followed by the
comparisons of [Stacks, Tag 0D5T]. -/
def blowupFormsDerivedTail (a : ℤ) :
    (derivedPushforward (blowupMap i).toLRSHom.toShHom).obj
        (DerivedCategory.Q.obj (singleComplex
          ((Scheme.Modules.pushforward (exceptionalInclusion i)).obj
            (Scheme.Hom.relativeDifferentialForms (exceptionalStructure f i) a)))) ⟶
      exceptionalFormsDerivedObj f i a :=
  let j := (exceptionalInclusion i).toLRSHom.toShHom
  let G := Scheme.Hom.relativeDifferentialForms (exceptionalStructure f i) a
  (derivedPushforward (blowupMap i).toLRSHom.toShHom).map
      (DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex (modulePushforward j)
            (ComplexShape.up ℤ) 0).inv.app G) ≫
        unit j (singleComplex G)) ≫
    (compIso j (blowupMap i).toLRSHom.toShHom).inv.app _ ≫
    eqToHom (congrArg (fun g => (derivedPushforward g).obj
      (DerivedCategory.Q.obj (singleComplex G))) (exceptionalInclusion_toShHom_comp i)) ≫
    (compIso (exceptionalProjection i).toLRSHom.toShHom i.toLRSHom.toShHom).hom.app _

/-- The part of the comparison of clause (3) after `Rb_*ρ` is an isomorphism: `j` and `i` are
closed immersions, so `j_* ⟶ Rj_*` is invertible, and the other factors are isomorphisms. -/
instance isIso_blowupFormsDerivedTail (a : ℤ) : IsIso (blowupFormsDerivedTail f i a) := by
  let j := (exceptionalInclusion i).toLRSHom.toShHom
  let G := Scheme.Hom.relativeDifferentialForms (exceptionalStructure f i) a
  have h₁ : IsIso (unit j (singleComplex G)) :=
    isIso_unit_of_isClosedEmbedding _ (exceptionalInclusion i).isClosedEmbedding _
  have h₂ : IsIso (DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex
      (modulePushforward j) (ComplexShape.up ℤ) 0).inv.app G)) :=
    (DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
      (modulePushforward j) (ComplexShape.up ℤ) 0).app G).symm).isIso_hom
  have h₃ : IsIso ((derivedPushforward (blowupMap i).toLRSHom.toShHom).map
      (DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex
        (modulePushforward j) (ComplexShape.up ℤ) 0).inv.app G) ≫ unit j (singleComplex G))) :=
    @Functor.map_isIso _ _ _ _ _ _ _ _ (@IsIso.comp_isIso _ _ _ _ _ _ _ h₂ h₁)
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₃ inferInstance

/-- **The canonical map `Rb_*Ω^a_{X'/S} ⟶ i_*Rp_*Ω^a_{E/S}` of [Stacks, Tag 0FUU] clause (3)**,
in `D(𝒪_X)`: `Rb_*` of the restriction of forms `Ω^a_{X'/S} ⟶ j_*Ω^a_{E/S}`, followed by the
comparison `j_* ⟶ Rj_*` and the comparisons `Rb_*Rj_* ≅ R(j ≫ b)_* = R(p ≫ i)_* ≅ Ri_*Rp_*` of
[Stacks, Tag 0D5T]. -/
def blowupFormsRestrictionDerivedComparison (a : ℤ) :
    blowupFormsDerivedObj f i a ⟶ exceptionalFormsDerivedObj f i a :=
  (derivedPushforward (blowupMap i).toLRSHom.toShHom).map
      (DerivedCategory.Q.map
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map (blowupFormsRestriction f i a))) ≫
    blowupFormsDerivedTail f i a

end Derived

end Stacks.DeRham

end
