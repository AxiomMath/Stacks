module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatChartPerfectComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.IdentityMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty

/-!
# The chart hypotheses of the perfect complex of Situation 07YX

For `x` a flat, proper, finitely presented algebraic space `f : X → Spec A` over a Noetherian ring
`A`, this file proves the facts about the chart that
`AlgebraicGeometry.Space.ProperFlatLift.exists_isPerfect_derivedCohomology_iso_cotangentExt`
takes as arguments:

* `f` is locally of finite type and quasi-separated (it is of finite presentation);
* `Spec A`, as an algebraic space, is Noetherian;
* `M ↦ M~` (`AlgebraicGeometry.Space.affineBaseTilde`) has quasi-coherent values and is exact.

What remains is the 08JR hypothesis on `𝒢^• = 𝒪_X[0]` and the action of `A` on
`H^i(K ⊗ᴸ_A M)`.

## Main results

* `exists_isPerfect_derivedCohomology_iso_cotangentExt_of_flatProperSupport`: for `x` flat,
  proper and finitely presented over a Noetherian `A`, a perfect complex `K` of `A`-modules with
  `H^i(K ⊗ᴸ_A −) ≅ Ext^i(L_{X/A}, 𝒪_X ⊗_A −)` for `i = 1, 2`, given the 08JR hypothesis on
  `𝒪_X[0]` and the action of `A` on `H^i(K ⊗ᴸ_A M)`.

## References

* [Stacks Project, Tag 08JR](https://stacks.math.columbia.edu/tag/08JR)
* [Stacks Project, Remark 0D1P](https://stacks.math.columbia.edu/tag/0D1P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t u

namespace AlgebraicGeometry.Space.ProperFlatLift

open Deformation.Artin Stacks.Cohomology.SiteModules

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
-- One standard-model line, scoped to this file: the base declarations
-- `Deformation.Artin.derivedCohomology` and `Deformation.Artin.boundaryMap` are stated in the
-- model `HasDerivedCategory.standard`.
attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  (x : CartesianProperFlatSpaces B S hS)
  (hx : (cartesianProperFlatProjection B S hS).obj x = algebraOver A B S hS toS hA)

/-- Re-reading the base of a family along an equality of objects keeps it of finite
presentation. -/
theorem isFinitePresentation_commaHomAsSpaceMap_comp_eqToHom
    {G : Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    {V : BigFppfOver B S hS} (e : G.right = V) (h : IsFinitePresentation B S hS G.hom) :
    IsFinitePresentation B S hS
      (commaHomAsSpaceMap G ≫ (schemeSpaceFunctor B S hS).map (eqToHom e)).hom := by
  subst e
  rw [eqToHom_refl, CategoryTheory.Functor.map_id]
  exact h

/-- The structure morphism of `x` at a chart is of finite presentation. -/
theorem isFinitePresentation_chartStructureMap :
    IsFinitePresentation B S hS (chartStructureMap x hx).hom :=
  isFinitePresentation_commaHomAsSpaceMap_comp_eqToHom hx x.obj.property.1

/-- The structure morphism of `x` at a chart is locally of finite type. -/
theorem isLocallyOfFiniteType_chartStructureMap :
    IsLocallyOfFiniteType B S hS (chartStructureMap x hx).hom :=
  isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
    (isFinitePresentation_chartStructureMap x hx).1

/-- `Spec A`, for `A` Noetherian, is a Noetherian algebraic space. -/
theorem isNoetherian_schemeSpace_algebraOver [IsNoetherianRing A] :
    IsNoetherian B S hS B.contains_terminal (schemeSpace (algebraOver A B S hS toS hA)).1 :=
  ⟨isQuasiCompactSpace_yoneda_of_isAffine B S hS (algebraOver A B S hS toS hA)
      (inferInstanceAs (IsAffine (Spec (.of A)))),
    isAbsolutelyQuasiSeparated_yoneda_obj B S hS B.contains_terminal _
      (inferInstanceAs (QuasiSeparatedSpace (Spec (.of A)))),
    hasEtaleLocalProperty_of_representable B S hS _
      (fun T : Scheme.{u} => IsLocallyNoetherian T) (algebraOver A B S hS toS hA) (Iso.refl _)
      (inferInstanceAs (IsLocallyNoetherian (Spec (.of A))))⟩

variable [HasDerivedCategory.{t} (modelModules x.obj.obj.left)]

/-- **The perfect complex of Situation 07YX at a chart, from 08JR**, with the chart hypotheses
discharged. For `x` a flat, proper, finitely presented `f : X → Spec A` with `A` Noetherian, there
are a perfect complex `K` of `A`-modules and natural isomorphisms
`e_i : H^i(K ⊗ᴸ_A −) ≅ T^i(−) = Ext^i(L_{X/A}, 𝒪_X ⊗_A −)` for `i = 1, 2` carrying the boundary map
of `K` to `chartExtConnecting x hx`, provided `𝒪_X[0]` satisfies the hypotheses of 08JR on
`𝒢^•` (`hG`) and `r : A` acts on `H^i(K ⊗ᴸ_A M)` through `H^i(K ⊗ᴸ_A (r • 𝟙_M))` (`hlin`). -/
theorem exists_isPerfect_derivedCohomology_iso_cotangentExt_of_flatProperSupport
    [IsNoetherianRing A]
    (hG : FlatProperSupportComplex B S hS (chartStructureMap x hx)
      (isLocallyOfFiniteType_chartStructureMap x hx) (structureSingleComplex x.obj.obj.left))
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
  exists_isPerfect_derivedCohomology_iso_cotangentExt x hx B.contains_terminal
    (isLocallyOfFiniteType_chartStructureMap x hx)
    (isFinitePresentation_chartStructureMap x hx).2.2 isNoetherian_schemeSpace_algebraOver
    (fun M => isQuasicoherentOnSite_affineBaseTilde M)
    (fun hSq => shortExact_map_affineBaseTilde hSq)
    hG hlin

end AlgebraicGeometry.Space.ProperFlatLift

end
