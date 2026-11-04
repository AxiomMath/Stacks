module

public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle
public import StacksFrontier.AlgebraicGeometry.RingedSpace.NaiveCotangentComplex
public import StacksFrontier.Cotangent.SheavesOfRings.NaiveComparisonCanonical
public import StacksFrontier.Cotangent.SheavesOfRings.RingedSpaceCanonicalNaiveComparison
public import StacksFrontier.Cotangent.SheavesOfRings.RingedSpaceExtTruncation
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentDerivedExt
public import StacksFrontier.Homology.Injectives.FilteredComplex.HomComplex

/-!
# The naive cotangent complex of a morphism of ringed spaces is `τ_{≥ -1} L_{X/S}`

Let `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` be a morphism of ringed spaces.  This file identifies the naive
cotangent complex `NL_{X/S}` of Tag 08TN, `AlgebraicGeometry.RingedSpace.naiveCotangentComplex f`,
with the truncation `τ_{≥ -1} L_{X/S}` of the cotangent complex, as objects of `D(𝒪_X)`.  This is
the identification the proof of Tag 08UZ uses ("via the identification
`NL_{X/S} = τ_{≥ -1} L_{X/S}`").

## Main definitions

* `Stacks.Sheaves.RingedSpaceCotangent.canonicalNaiveComparison`: the canonical map
  `L_{X/S} ⟶ NL_{X/S}` into the naive cotangent complex of Tag 08TN, the case `f⁻¹𝒪_S ⟶ 𝒪_X` of
  `CategoryTheory.Sheaf.canonicalNaiveComparison`.
* `Stacks.Sheaves.RingedSpaceCotangent.naiveCotangentDerivedIsoTrunc`: **the isomorphism
  `NL_{X/S} ≅ τ_{≥ -1} L_{X/S}` in `D(𝒪_X)`**, with no hypothesis.
* `Stacks.Sheaves.RingedSpaceCotangent.naiveExtCotangentAddEquiv`: for `i ≤ 1`,
  `Ext^i_{𝒪_X}(NL_{X/S}, 𝒢) ≃+ Ext^i_{𝒪_X}(L_{X/S}, 𝒢)`, which is precomposition with the
  canonical map (`naiveExtCotangentAddEquiv_apply`).

## Main results

* `Stacks.Sheaves.RingedSpaceCotangent.canonicalNaiveComparison_isIso_homologyMap`: the
  canonical map is an isomorphism on `Hⁱ` for every `i ≥ -1`.
* `Stacks.Sheaves.RingedSpaceCotangent.isGE_relativeNaiveCotangentObj`: `NL_{X/S}` lies in degrees
  `≥ -1`.
* `Stacks.Sheaves.RingedSpaceCotangent.truncGEπ_comp_naiveCotangentDerivedIsoTrunc_inv`: the
  isomorphism composed with the truncation projection `L_{X/S} ⟶ τ_{≥ -1} L_{X/S}` is the image of
  the canonical map, so it is the canonical identification and not merely an abstract one.

## Implementation notes

The degree `-1` half of the identification, `H^{-1}(L_{X/S}) ≅ H^{-1}(NL_{X/S})`, is
`CategoryTheory.Sheaf.naiveComparison_isIso_homologyMap_negOne` of
`StacksFrontier.Cotangent.SheavesOfRings.NaiveComparisonCanonical`, proved on any site; the
passage from the presentation `P₀ ⟶ 𝒪_X` of the standard resolution to the polynomial
presentation of Tag 08TN is `CategoryTheory.Sheaf.naiveCotangentComplexIsoCanonical`.

`Stacks.Sheaves.RingedSpaceCotangent.canonicalNaiveComparison` and
`Stacks.Sheaves.RingedSpaceCotangent.canonicalNaiveComparison_isIso_homologyMap` are those of
`StacksFrontier.Cotangent.SheavesOfRings.RingedSpaceCanonicalNaiveComparison`.

The model of the derived category is `HasDerivedCategory.standard` as a local instance, as in
`StacksFrontier/Cotangent/SheavesOfRings/RingedSpaceExt.lean`.

## References

* [Stacks Project, Tag 08UW](https://stacks.math.columbia.edu/tag/08UW)
* [Stacks Project, Tag 08US](https://stacks.math.columbia.edu/tag/08US)
* [Stacks Project, Tag 08TN](https://stacks.math.columbia.edu/tag/08TN)
* [Stacks Project, Tag 08UZ](https://stacks.math.columbia.edu/tag/08UZ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Sheaves.RingedSpaceDifferentials (inverseImageStructureMap)
open AlgebraicGeometry.RingedSpaceThickening (relativeNaiveCotangentObj)

universe u

namespace Stacks.Sheaves.RingedSpaceCotangent

variable {X S : RingedSpace.{u, u}}

attribute [local instance] HasDerivedCategory.standard

/-- `NL_{X/S}` lies in cohomological degrees `≥ -1`: it has no terms below degree `-1`. -/
instance isGE_relativeNaiveCotangentObj (f : X ⟶ S) :
    DerivedCategory.TStructure.t.IsGE (relativeNaiveCotangentObj f) (-1) := by
  refine (DerivedCategory.isGE_Q_obj_iff _ _).2 ((CochainComplex.isGE_iff _ _).2 fun i hi => ?_)
  exact HomologicalComplex.ExactAt.of_isZero
    (RingedSpace.naiveCotangentComplex_isZero_X f i (by omega) (by omega))

/-- After the truncation `τ_{≥ -1}`, the canonical map `L_{X/S} ⟶ NL_{X/S}` becomes an
isomorphism in `D(𝒪_X)`. -/
instance isIso_truncGE_map_Q_canonicalNaiveComparison (f : X ⟶ S) :
    IsIso ((DerivedCategory.TStructure.t.truncGE (-1)).map
      (DerivedCategory.Q.map (canonicalNaiveComparison f))) := by
  rw [DerivedCategory.isIso_iff]
  intro i
  by_cases hi : -1 ≤ i
  · have h₁ := DerivedCategory.isIso_homologyMap_truncGEπ_app (-1) i hi
      (cotangentComplexDerived.{u, u + 1} f)
    have h₂ := DerivedCategory.isIso_homologyMap_truncGEπ_app (-1) i hi
      (relativeNaiveCotangentObj f)
    have h₃ : IsIso ((DerivedCategory.homologyFunctor _ i).map
        (DerivedCategory.Q.map (canonicalNaiveComparison f))) :=
      (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors
        (SheafOfModules.{u} (structureSheafRing X)) i) _).2
        (canonicalNaiveComparison_isIso_homologyMap f i hi)
    have hsq := congrArg (DerivedCategory.homologyFunctor _ i).map
      ((DerivedCategory.TStructure.t.truncGEπ (-1)).naturality
        (DerivedCategory.Q.map (canonicalNaiveComparison f)))
    simp only [Functor.id_map, Functor.map_comp] at hsq
    have hfac : (DerivedCategory.homologyFunctor _ i).map
        ((DerivedCategory.TStructure.t.truncGE (-1)).map
          (DerivedCategory.Q.map (canonicalNaiveComparison f))) =
        inv ((DerivedCategory.homologyFunctor _ i).map
            ((DerivedCategory.TStructure.t.truncGEπ (-1)).app
              (cotangentComplexDerived.{u, u + 1} f))) ≫
          (DerivedCategory.homologyFunctor _ i).map
            (DerivedCategory.Q.map (canonicalNaiveComparison f)) ≫
          (DerivedCategory.homologyFunctor _ i).map
            ((DerivedCategory.TStructure.t.truncGEπ (-1)).app (relativeNaiveCotangentObj f)) := by
      rw [IsIso.eq_inv_comp, hsq]
    rw [hfac]
    infer_instance
  · have hlt : i < -1 := by omega
    exact ⟨0, (DerivedCategory.isZero_of_isGE _ (-1) i hlt).eq_of_src _ _,
      (DerivedCategory.isZero_of_isGE _ (-1) i hlt).eq_of_src _ _⟩

/-- **The naive cotangent complex is the truncation `τ_{≥ -1} L_{X/S}`.**  In `D(𝒪_X)`,
`NL_{X/S} ≅ τ_{≥ -1} L_{X/S}`: `NL_{X/S}` lies in degrees `≥ -1`, so it is its own truncation,
and the truncation of the canonical map `L_{X/S} ⟶ NL_{X/S}` is an isomorphism because the
canonical map is an isomorphism on `Hⁱ` for every `i ≥ -1`. -/
noncomputable def naiveCotangentDerivedIsoTrunc (f : X ⟶ S) :
    relativeNaiveCotangentObj f ≅ truncCotangentComplexDerived f :=
  asIso ((DerivedCategory.TStructure.t.truncGEπ (-1)).app (relativeNaiveCotangentObj f)) ≪≫
    (asIso ((DerivedCategory.TStructure.t.truncGE (-1)).map
      (DerivedCategory.Q.map (canonicalNaiveComparison f)))).symm

/-- The identification is the canonical one: the truncation projection
`L_{X/S} ⟶ τ_{≥ -1} L_{X/S}` followed by the inverse of `naiveCotangentDerivedIsoTrunc` is the
image in `D(𝒪_X)` of the canonical map `L_{X/S} ⟶ NL_{X/S}`. -/
theorem truncGEπ_comp_naiveCotangentDerivedIsoTrunc_inv (f : X ⟶ S) :
    (DerivedCategory.TStructure.t.truncGEπ (-1)).app (cotangentComplexDerived.{u, u + 1} f) ≫
        (naiveCotangentDerivedIsoTrunc f).inv =
      DerivedCategory.Q.map (canonicalNaiveComparison f) := by
  rw [naiveCotangentDerivedIsoTrunc, Iso.trans_inv, Iso.symm_inv, asIso_hom, asIso_inv,
    ← Category.assoc, ← (DerivedCategory.TStructure.t.truncGEπ (-1)).naturality,
    Category.assoc, Functor.id_map, IsIso.hom_inv_id, Category.comp_id]

/-- **`Ext^i_{𝒪_X}(NL_{X/S}, 𝒢) = Ext^i_{𝒪_X}(L_{X/S}, 𝒢)` for `i ≤ 1`**, through
`NL_{X/S} ≅ τ_{≥ -1} L_{X/S}` and the bijectivity of restriction along the truncation projection
in those degrees. -/
noncomputable def naiveExtCotangentAddEquiv (f : X ⟶ S)
    (G : SheafOfModules.{u} (structureSheafRing X)) {i : ℤ} (hi : i ≤ 1) :
    DerivedCategory.Ext (relativeNaiveCotangentObj f)
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj G) i ≃+
      cotangentExt f G i :=
  (Stacks.Injectives.homCongrAddEquiv (naiveCotangentDerivedIsoTrunc f) (Iso.refl _)).trans
    (extTruncGECotangentAddEquiv f G hi)

/-- The identification `Ext^i(NL_{X/S}, 𝒢) ≃+ Ext^i(L_{X/S}, 𝒢)` is precomposition with the
canonical map `L_{X/S} ⟶ NL_{X/S}`. -/
theorem naiveExtCotangentAddEquiv_apply (f : X ⟶ S)
    (G : SheafOfModules.{u} (structureSheafRing X)) {i : ℤ} (hi : i ≤ 1)
    (ξ : DerivedCategory.Ext (relativeNaiveCotangentObj f)
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj G) i) :
    naiveExtCotangentAddEquiv f G hi ξ =
      DerivedCategory.Q.map (canonicalNaiveComparison f) ≫ ξ := by
  rw [naiveExtCotangentAddEquiv, AddEquiv.trans_apply, extTruncGECotangentAddEquiv_apply,
    Stacks.Injectives.homCongrAddEquiv_apply, Iso.refl_hom, Category.comp_id,
    ← Category.assoc, truncGEπ_comp_naiveCotangentDerivedIsoTrunc_inv]

end Stacks.Sheaves.RingedSpaceCotangent

end
