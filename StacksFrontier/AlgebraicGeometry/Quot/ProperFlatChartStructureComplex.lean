module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatChartPerfectComplexOfChart
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenInCoherentStack
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackSection
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissage
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissageFiltration
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SingleFunctorQcohDerived
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeCoefficients

/-!
# `𝒪_X[0]` satisfies the hypotheses of 08JR at a chart of `Spaces'_{fp, flat, proper}`

For `x` a flat, proper, finitely presented algebraic space `f : X → Spec A` over a Noetherian
ring `A`, the complex `𝒪_X[0]` is a bounded complex of coherent `𝒪_X`-modules, flat over `Spec A`,
with support proper over `Spec A`: the hypothesis on `𝒢^•` of [Stacks, Tag 08JR]
(`AlgebraicGeometry.Space.FlatProperSupportComplex`). Hence the perfect complex of Situation 07YX
at the chart exists as soon as `r : A` acts on `H^i(K ⊗ᴸ_A M)` through `H^i(K ⊗ᴸ_A (r • 𝟙_M))`.

## Main results

In the namespace `AlgebraicGeometry.Space.ProperFlatLift`:

* `flatProperSupportComplex_structureSingleComplex`: `𝒪_X[0]` is a bounded complex of coherent
  modules, flat over `Spec A`, with support proper over `Spec A`.
* `exists_isPerfect_derivedCohomology_iso_cotangentExt_of_isNoetherianRing`: a perfect complex
  `K` of `A`-modules with `H^i(K ⊗ᴸ_A −) ≅ Ext^i(L_{X/A}, 𝒪_X ⊗_A −)` for `i = 1, 2`.

## References

* [Stacks Project, Tag 08JR](https://stacks.math.columbia.edu/tag/08JR)
* [Stacks Project, Tag 07UB](https://stacks.math.columbia.edu/tag/07UB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t u

namespace AlgebraicGeometry.Space.ProperFlatLift

open Deformation.Artin

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
-- One standard-model line, scoped to this file: the base declarations
-- `Deformation.Artin.derivedCohomology` and `Deformation.Artin.boundaryMap` are stated in the
-- model `HasDerivedCategory.standard`.
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  (x : CartesianProperFlatSpaces B S hS)
  (hx : (cartesianProperFlatProjection B S hS).obj x = algebraOver A B S hS toS hA)

/-- Re-reading the base of a family along an equality of objects keeps it proper. -/
theorem isProper_commaHomAsSpaceMap_comp_eqToHom
    {G : Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    {V : BigFppfOver B S hS} (e : G.right = V) (h : IsProper B S hS G.hom) :
    IsProper B S hS
      (commaHomAsSpaceMap G ≫ (schemeSpaceFunctor B S hS).map (eqToHom e)).hom := by
  subst e
  rw [eqToHom_refl, CategoryTheory.Functor.map_id]
  exact h

/-- The structure morphism of `x` at a chart is proper. -/
theorem isProper_chartStructureMap : IsProper B S hS (chartStructureMap x hx).hom :=
  isProper_commaHomAsSpaceMap_comp_eqToHom hx x.obj.property.2.2

/-- **`𝒪_X[0]` satisfies the hypotheses of 08JR on `𝒢^•`**: it is bounded, `𝒪_X` is coherent
(`X` is locally Noetherian, being locally of finite type over `Spec A`, Stacks 07UB), flat over
`Spec A` (an invertible module along a flat morphism), and its support is contained in `|X|`,
which is proper over `Spec A`. -/
theorem flatProperSupportComplex_structureSingleComplex [IsNoetherianRing A] :
    FlatProperSupportComplex B S hS (chartStructureMap x hx)
      (isLocallyOfFiniteType_chartStructureMap x hx) (structureSingleComplex x.obj.obj.left) where
  bounded := ⟨0, 0, fun q hq =>
    HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)⟩
  isCoherent q := by
    by_cases h : q = 0
    · subst h
      have : Fact (HasEtaleLocalProperty B S hS x.obj.obj.left.1
          (fun V : Scheme.{u} => AlgebraicGeometry.IsLocallyNoetherian V)) :=
        ⟨isLocallyNoetherian_of_isLocallyOfFiniteType B S hS x.obj.obj.left.2
          (schemeSpace (algebraOver A B S hS toS hA)).2 (chartStructureMap x hx).hom
          (isLocallyOfFiniteType_chartStructureMap x hx) isNoetherian_schemeSpace_algebraOver.2.2⟩
      exact isCoherent_of_iso B S hS x.obj.obj.left.2
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).symm
        (isCoherent_structureSheaf B S hS x.obj.obj.left.1 x.obj.obj.left.2)
    · exact isCoherent_of_isZero B S hS x.obj.obj.left
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ h)
  isFlatOver q := by
    by_cases h : q = 0
    · subst h
      exact IsFlatOver.of_iso B S hS x.obj.obj.left.2
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).symm
        (isFlatOver_of_isInvertibleModule (chartStructureMap x hx) _
          (isFlat_chartStructureMap x hx) (isInvertibleModule_structureModule x.obj.obj.left))
    · exact isFlatOver_of_isZero B S hS (chartStructureMap x hx)
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ h)
  properSupport := ⟨Set.univ, isClosed_univ,
    isProper_comp B S hS
      (isAlgebraicSpace_reducedClosedSubspace B S hS x.obj.obj.left.1 x.obj.obj.left.2 Set.univ
        isClosed_univ) x.obj.obj.left.2 (schemeSpace (algebraOver A B S hS toS hA)).2 _ _
      (isProper_ι_reducedClosedSubspace B S hS x.obj.obj.left.1 x.obj.obj.left.2 Set.univ
        isClosed_univ) (isProper_chartStructureMap x hx),
    fun _ => Set.subset_univ _⟩

variable [HasDerivedCategory.{t} (modelModules x.obj.obj.left)]

/-- **The perfect complex of Situation 07YX at a chart, from 08JR.** For `x` a flat, proper,
finitely presented `f : X → Spec A` with `A` Noetherian, there are a perfect complex `K` of
`A`-modules and natural isomorphisms `e_i : H^i(K ⊗ᴸ_A −) ≅ T^i(−) = Ext^i(L_{X/A}, 𝒪_X ⊗_A −)`
for `i = 1, 2` carrying the boundary map of `K` to `chartExtConnecting x hx`, provided `r : A` acts
on `H^i(K ⊗ᴸ_A M)` through `H^i(K ⊗ᴸ_A (r • 𝟙_M))` (`hlin`). -/
theorem exists_isPerfect_derivedCohomology_iso_cotangentExt_of_isNoetherianRing
    [IsNoetherianRing A]
    (hlin : ∀ (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) (M : ModuleCat.{u} A) (r : A)
      (y : (derivedCohomology A K i).obj M), (derivedCohomology A K i).map (r • 𝟙 M) y = r • y) :
    ∃ (K : DerivedCategory (ModuleCat.{u} A))
      (e₁ : derivedCohomology A K 1 ≅
        cotangentExtOne (chartStructureMap x hx) (chartBaseRingHom x hx))
      (e₂ : derivedCohomology A K 2 ≅
        cotangentExtTwo (chartStructureMap x hx) (chartBaseRingHom x hx)),
      StacksDraft.Perfect.IsPerfect K ∧
        ∀ {Sq : ShortComplex (ModuleCat.{u} A)} (hSq : Sq.ShortExact),
          boundaryMap A K hSq ≫ e₂.hom.app Sq.X₁ = e₁.hom.app Sq.X₃ ≫ chartExtConnecting x hx hSq :=
  exists_isPerfect_derivedCohomology_iso_cotangentExt_of_flatProperSupport x hx
    (flatProperSupportComplex_structureSingleComplex x hx) hlin

end AlgebraicGeometry.Space.ProperFlatLift

end
