module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.SheavesOfRings.RingedSpace
public import StacksFrontier.Cotangent.SheavesOfRings.RingedToposNaiveComparison

/-!
# The canonical map from the cotangent complex to the naive cotangent complex

Let `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` be a morphism of ringed spaces.  The cotangent complex `L_{X/S}`
is the cotangent complex of the morphism of sheaves of rings `f⁻¹𝒪_S ⟶ 𝒪_X` on the site of open
subsets of `X`, and the naive cotangent complex `NL_{X/S}` is the two-term complex

`I/I² ⟶ 𝒪_X ⊗_{P₀} Ω_{P₀/f⁻¹𝒪_S}`

of a polynomial presentation `P₀ ⟶ 𝒪_X`, with `I` the kernel of that presentation.  The
canonical chain map `L_{B/A} ⟶ NL(P₀ ⟶ B)` of Tag 08US, at the morphism of sheaves of rings
`f⁻¹𝒪_S ⟶ 𝒪_X`, is the canonical map `L_{X/S} ⟶ NL_{X/S}` of Tag 08UW.

## Main definitions

* `Stacks.Sheaves.RingedSpaceCotangent.naivePresentationComplex`: the naive cotangent complex
  `NL_{X/S}` of the presentation of `𝒪_X` by the degree-zero term of the standard resolution,
  as a cochain complex with `I/I²` in degree `-1` and `𝒪_X ⊗_{P₀} Ω_{P₀/f⁻¹𝒪_S}` in degree `0`.
* `Stacks.Sheaves.RingedSpaceCotangent.naiveComparison`: the canonical chain map
  `L_{X/S} ⟶ NL_{X/S}` of Tag 08UW.

## Main results

* `Stacks.Sheaves.RingedSpaceCotangent.naiveComparison_f_negOne` and
  `Stacks.Sheaves.RingedSpaceCotangent.naiveComparison_f_zero`: the two components of the
  chain map are the comparison arrows of Tag 08US.
* `Stacks.Sheaves.RingedSpaceCotangent.naiveComparison_f_negOne_apply`: on local sections the
  degree `-1` component sends the pure differential `d x` of a local section `x` of `P₁` to the
  class of `d₀ x - d₁ x` in `I/I²`.

## Implementation notes

The complex and the map are `CategoryTheory.Sheaf.naiveCotangentComplex` and
`CategoryTheory.Sheaf.naiveComparison` at the Grothendieck topology of the opens of `X` and at
the structure map `Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f`, which is
the morphism of sheaves of rings `f⁻¹𝒪_S ⟶ 𝒪_X`.

The naive cotangent complex is realized as the two-term complex of the conormal sequence of the
presentation `P₀ ⟶ 𝒪_X` by the degree-zero term of the standard resolution. That presentation
is a free `f⁻¹𝒪_S`-algebra sheaf on `𝒪_X`, spelled by `CategoryTheory.Sheaf.freeAlgebraSheaf`
(a coproduct with the sheafified pointwise free ring) rather than by
`Stacks.Sites.FreeAlgebra.freeAlgebraSheaf` (the sheafified pointwise polynomial ring), which is
the model used by `AlgebraicGeometry.RingedSpace.naiveCotangentComplex`.

## References

* [Stacks Project, Tag 08UW](https://stacks.math.columbia.edu/tag/08UW)
* [Stacks Project, Tag 08US](https://stacks.math.columbia.edu/tag/08US), the same comparison for
  a morphism of sheaves of rings on a site, of which Tag 08UW is a special case.
* [Stacks Project, Tag 08UU](https://stacks.math.columbia.edu/tag/08UU), the cotangent complex
  of a morphism of ringed spaces.
* [Stacks Project, Tag 08TN](https://stacks.math.columbia.edu/tag/08TN), the naive cotangent
  complex of a morphism of ringed spaces.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Category CategoryTheory.Limits Opposite Simplicial
open TopologicalSpace
open Stacks.Sheaves.RingedSpaceDifferentials (inverseImageStructureMap)

universe u

namespace Stacks.Sheaves.RingedSpaceCotangent

variable {X S : RingedSpace.{u, u}}

/-- The naive cotangent complex `NL_{X/S}` of a morphism of ringed spaces `f : X ⟶ S`, in the
presentation of `𝒪_X` over `f⁻¹𝒪_S` by the degree-zero term of the standard resolution: the
conormal sequence `I/I² ⟶ 𝒪_X ⊗_{P₀} Ω_{P₀/f⁻¹𝒪_S}` read as a cochain complex of sheaves of
`𝒪_X`-modules with `I/I²` in degree `-1`. -/
@[sga "6 0 4.4" "special case"]
noncomputable def naivePresentationComplex (f : X ⟶ S) :
    CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ :=
  CategoryTheory.Sheaf.naiveCotangentComplex (Opens.grothendieckTopology X.carrier)
    (inverseImageStructureMap f)

/-- The conormal sheaf `I/I²` is the degree `-1` term of `NL_{X/S}`. -/
noncomputable def naivePresentationComplexXNegOneIso (f : X ⟶ S) :
    (naivePresentationComplex f).X (-1) ≅
      (CategoryTheory.Sheaf.naiveSequence (Opens.grothendieckTopology X.carrier)
        (inverseImageStructureMap f)).X₁ :=
  CategoryTheory.Sheaf.naiveCotangentComplexXNegOneIso
    (Opens.grothendieckTopology X.carrier) (inverseImageStructureMap f)

/-- The sheaf `𝒪_X ⊗_{P₀} Ω_{P₀/f⁻¹𝒪_S}` is the degree `0` term of `NL_{X/S}`. -/
noncomputable def naivePresentationComplexXZeroIso (f : X ⟶ S) :
    (naivePresentationComplex f).X 0 ≅
      (CategoryTheory.Sheaf.naiveSequence (Opens.grothendieckTopology X.carrier)
        (inverseImageStructureMap f)).X₂ :=
  CategoryTheory.Sheaf.naiveCotangentComplexXZeroIso
    (Opens.grothendieckTopology X.carrier) (inverseImageStructureMap f)

/-- `NL_{X/S}` has no terms outside degrees `-1` and `0`. -/
theorem naivePresentationComplex_isZero_X (f : X ⟶ S) (i : ℤ) (hneg : i ≠ -1) (hzero : i ≠ 0) :
    IsZero ((naivePresentationComplex f).X i) :=
  CategoryTheory.Sheaf.naiveCotangentComplex_isZero_X
    (Opens.grothendieckTopology X.carrier) (inverseImageStructureMap f) i hneg hzero

/-- The canonical chain map `L_{X/S} ⟶ NL_{X/S}` of a morphism of ringed spaces:
`CategoryTheory.Sheaf.naiveComparison` at the morphism of sheaves of rings `f⁻¹𝒪_S ⟶ 𝒪_X`. -/
@[stacks 08UW "the canonical map `L_{X/Y} → NL_{X/Y}` as a morphism of cochain complexes of
sheaves of `O_X`-modules, with both of its components pinned by the lemmas below. Hypotheses
beyond the source: `NL_{X/Y}` is realized as the two-term complex of the conormal sequence of
the presentation `P₀ ⟶ O_X` by the degree-zero term of the standard resolution, whose free
algebra is spelled by `CategoryTheory.Sheaf.freeAlgebraSheaf`; the identification of that model
with the one of `AlgebraicGeometry.RingedSpace.naiveCotangentComplex` is not carried. The second
half of the tag, that this map identifies the naive cotangent complex with the truncation
`tau_{>=-1} L_{X/Y}`, is NOT proved and is nowhere assumed"]
noncomputable def naiveComparison (f : X ⟶ S) :
    cotangentComplex f ⟶ naivePresentationComplex f :=
  CategoryTheory.Sheaf.naiveComparison (Opens.grothendieckTopology X.carrier)
    (inverseImageStructureMap f)

/-- The degree `-1` component of the canonical map is the comparison arrow
`CategoryTheory.Sheaf.naiveComparisonNegOne` for the morphism of sheaves of rings
`f⁻¹𝒪_S ⟶ 𝒪_X`. -/
@[stacks 08UW "the degree `-1` component of the canonical map is the comparison arrow
`Omega_{P_1} ⊗ O_X → I/I²`, so the map is the canonical one. Same hypotheses as
`Stacks.Sheaves.RingedSpaceCotangent.naiveComparison`"]
theorem naiveComparison_f_negOne (f : X ⟶ S) :
    (naiveComparison f).f (-1) ≫ (naivePresentationComplexXNegOneIso f).hom =
      (CategoryTheory.Sheaf.cotangentComplex_degreeIso (Opens.grothendieckTopology X.carrier)
          (inverseImageStructureMap f) 1).hom ≫
        CategoryTheory.Sheaf.naiveComparisonNegOne (Opens.grothendieckTopology X.carrier)
          (inverseImageStructureMap f) :=
  (Iso.eq_comp_inv (naivePresentationComplexXNegOneIso f)).mp
    (CategoryTheory.Sheaf.naiveComparison_f_negOne (Opens.grothendieckTopology X.carrier)
      (inverseImageStructureMap f))

/-- The degree `0` component of the canonical map is the comparison arrow
`CategoryTheory.Sheaf.naiveComparisonZero` for the morphism of sheaves of rings `f⁻¹𝒪_S ⟶ 𝒪_X`. -/
@[stacks 08UW "the degree `0` component of the canonical map is the comparison arrow
`Omega_{P_0} ⊗ O_X → O_X ⊗ Omega_{P_0}`, so the map is the canonical one. Same hypotheses as
`Stacks.Sheaves.RingedSpaceCotangent.naiveComparison`"]
theorem naiveComparison_f_zero (f : X ⟶ S) :
    (naiveComparison f).f 0 ≫ (naivePresentationComplexXZeroIso f).hom =
      (CategoryTheory.Sheaf.cotangentComplex_degreeIso (Opens.grothendieckTopology X.carrier)
          (inverseImageStructureMap f) 0).hom ≫
        CategoryTheory.Sheaf.naiveComparisonZero (Opens.grothendieckTopology X.carrier)
          (inverseImageStructureMap f) :=
  (Iso.eq_comp_inv (naivePresentationComplexXZeroIso f)).mp
    (CategoryTheory.Sheaf.naiveComparison_f_zero (Opens.grothendieckTopology X.carrier)
      (inverseImageStructureMap f))

/-- The canonical map is zero outside degrees `-1` and `0`. -/
theorem naiveComparison_f_eq_zero (f : X ⟶ S) (i : ℤ) (hneg : i ≠ -1) (hzero : i ≠ 0) :
    (naiveComparison f).f i = 0 :=
  (naivePresentationComplex_isZero_X f i hneg hzero).eq_of_tgt _ _

/-- On local sections over an open `U` the degree `-1` component of the canonical map sends the
pure differential `d x` of a section `x` of `P₁` to the class of `d₀ x - d₁ x` in `I/I²`. -/
@[stacks 08UW "the value of the canonical map on local sections in degree `-1`: the pure
differential `d x` goes to the class of `d_0 x - d_1 x` in `I/I²`. Same hypotheses as
`Stacks.Sheaves.RingedSpaceCotangent.naiveComparison`"]
theorem naiveComparison_f_negOne_apply (f : X ⟶ S) (U : (Opens X.carrier)ᵒᵖ)
    (x : (CategoryTheory.Sheaf.resolutionTerm (Opens.grothendieckTopology X.carrier)
      (inverseImageStructureMap f) (op ⦋1⦌)).obj.obj U) :
    ((CategoryTheory.Sheaf.cotangentComplex_degreeIso (Opens.grothendieckTopology X.carrier)
          (inverseImageStructureMap f) 1).inv ≫ (naiveComparison f).f (-1) ≫
        (naivePresentationComplexXNegOneIso f).hom).val.app U
        (((CategoryTheory.Sheaf.cotangentSimplicialModule
          (Opens.grothendieckTopology X.carrier)
          (inverseImageStructureMap f)).universalDerivation (op ⦋1⦌)).d x) =
      CategoryTheory.Sheaf.conormalClassSection (Opens.grothendieckTopology X.carrier)
        (inverseImageStructureMap f) U
        (CategoryTheory.Sheaf.faceDifference (Opens.grothendieckTopology X.carrier)
          (inverseImageStructureMap f) U x) := by
  have h : (CategoryTheory.Sheaf.cotangentComplex_degreeIso
        (Opens.grothendieckTopology X.carrier) (inverseImageStructureMap f) 1).inv ≫
      (naiveComparison f).f (-1) ≫ (naivePresentationComplexXNegOneIso f).hom =
        CategoryTheory.Sheaf.naiveComparisonNegOne (Opens.grothendieckTopology X.carrier)
          (inverseImageStructureMap f) :=
    (Iso.inv_comp_eq _).mpr (naiveComparison_f_negOne f)
  rw [h]
  exact CategoryTheory.Sheaf.naiveComparisonNegOne_conormalClass
    (Opens.grothendieckTopology X.carrier) (inverseImageStructureMap f) U x

end Stacks.Sheaves.RingedSpaceCotangent

end
