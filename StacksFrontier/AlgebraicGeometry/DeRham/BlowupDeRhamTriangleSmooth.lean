module

public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupDeRhamTriangleShortExact
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupSmoothCentreFormsKernelVanishing

/-!
# The blowup triangle of de Rham complexes

Fix a scheme `S`, a smooth morphism `f : X ⟶ S` and a closed immersion `i : Z ⟶ X` with `Z`
smooth over `S`. Write `b : X' ⟶ X` for the blowing up of `X` along `Z`, `j : E ⟶ X'` for its
exceptional divisor and `p : E ⟶ Z` for the projection onto the centre. This file proves
[Stacks, Tag 0FUV]: there is a distinguished triangle

`Ω^•_{X/S} ⟶ Rb_*Ω^•_{X'/S} ⊕ i_*Ω^•_{Z/S} ⟶ i_*Rp_*Ω^•_{E/S} ⟶ Ω^•_{X/S}[1]`

in `D(X, f^{-1}𝒪_S)` whose first two maps are built from the four canonical maps of
Section 07HX, the sign of `i_*Ω^•_{Z/S} ⟶ i_*Rp_*Ω^•_{E/S}` being reversed.

## Main results

* `Stacks.DeRham.BlowupTriangle.exists_distTriang`: [Stacks, Tag 0FUV].

## Implementation notes

The triangle comes from `exists_distTriang_of_shortExact`, whose two inputs are the short
exactness of the sequence of complexes
`0 ⟶ Ω^•_{X/S} ⟶ b_*Ω^•_{X'/S} ⊕ i_*Ω^•_{Z/S} ⟶ b_*j_*Ω^•_{E/S} ⟶ 0`
(`shortExact_blowupShortComplex`) and clause (3) of [Stacks, Tag 0FUU]
(`Stacks.DeRham.isIso_homology_blowupFormsRestrictionDerivedComparison_of_smooth`), which is
stated for `𝒪`-modules and read on `f^{-1}𝒪_S`-modules by
`isIso_homologyFunctor_map_inclusionChain_f`. Clauses (1) and (2) of [Stacks, Tag 0FUU] are not
used, so no hypothesis on the codimension of `Z` is needed. The derived categories of the
statement are arbitrary models; the derived categories of `𝒪`-modules, which appear only in the
proof, are given their standard models.

## References

* [Stacks Project, Tag 0FUV](https://stacks.math.columbia.edu/tag/0FUV)
* [Stacks Project, Tag 0FUU](https://stacks.math.columbia.edu/tag/0FUU)
* [Stacks Project, Section 07HX](https://stacks.math.columbia.edu/tag/07HX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open RingedSpaceModuleAdjunction Stacks.DeRhamDirectImage

universe u

attribute [-instance] CategoryTheory.catToReflQuiver

namespace Stacks.DeRham.BlowupTriangle

variable {S X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i] [Smooth f]
  [Smooth (i ≫ f)]
  [HasDerivedCategory (ModuleSheaves (inverseImageBase f))]
  [HasDerivedCategory (ModuleSheaves (inverseImageBase (blowupMap i ≫ f)))]
  [HasDerivedCategory (ModuleSheaves (inverseImageBase (i ≫ f)))]
  [HasDerivedCategory (ModuleSheaves (inverseImageBase (exceptionalStructure f i)))]

/-- **The blowup triangle of de Rham complexes.** Let `f : X ⟶ S` be smooth and let `i : Z ⟶ X`
be a closed immersion with `Z` smooth over `S`, of any codimension. Let `b : X' ⟶ X` be the
blowing up of `X` along `Z`, with exceptional divisor `j : E ⟶ X'` and projection `p : E ⟶ Z`.
Then there is a distinguished triangle

`Ω^•_{X/S} ⟶ Rb_*Ω^•_{X'/S} ⊕ i_*Ω^•_{Z/S} ⟶ i_*Rp_*Ω^•_{E/S} ⟶ Ω^•_{X/S}[1]`

in `D(X, f^{-1}𝒪_S)` whose first map has components the canonical maps
`Ω^•_{X/S} ⟶ Rb_*Ω^•_{X'/S}` and `Ω^•_{X/S} ⟶ i_*Ω^•_{Z/S}`, and whose second map has components
the canonical map `Rb_*Ω^•_{X'/S} ⟶ i_*Rp_*Ω^•_{E/S}` and the negative of the canonical map
`i_*Ω^•_{Z/S} ⟶ i_*Rp_*Ω^•_{E/S}`, for any models of the derived categories. -/
@[stacks 0FUV "the distinguished triangle Ω^•_{X/S} → Rb_*Ω^•_{X'/S} ⊕ i_*Ω^•_{Z/S} → \
i_*Rp_*Ω^•_{E/S} → Ω^•_{X/S}[1] in D(X, f^{-1}O_S) whose four maps are the canonical ones, the \
sign of i_*Ω^•_{Z/S} → i_*Rp_*Ω^•_{E/S} reversed; Z ⊂ X closed, X and Z smooth over S, any \
codimension"]
theorem exists_distTriang :
    ∃ δ : exceptionalDeRham f i ⟶ (deRham f)⟦(1 : ℤ)⟧,
      Triangle.mk (biprod.lift (toBlowUp f i) (toCentre f i))
        (biprod.desc (blowUpToExceptional f i) (-centreToExceptional f i)) δ ∈
          distTriang (DerivedCategory (ModuleSheaves (inverseImageBase f))) := by
  let : HasDerivedCategory (ModuleSheaves X.toRingedSpace) := HasDerivedCategory.standard _
  let : HasDerivedCategory (ModuleSheaves (Stacks.Blowup.blowUp i.ker).toRingedSpace) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory (ModuleSheaves Z.toRingedSpace) := HasDerivedCategory.standard _
  let : HasDerivedCategory
      (ModuleSheaves (Stacks.Blowup.exceptionalDivisor i.ker).toRingedSpace) :=
    HasDerivedCategory.standard _
  exact exists_distTriang_of_shortExact f i (shortExact_blowupShortComplex f i)
    (isIso_homologyFunctor_map_inclusionChain_f f i
      (isIso_homology_blowupFormsRestrictionDerivedComparison_of_smooth f i))

end Stacks.DeRham.BlowupTriangle

end
