module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatChartAffineTildeCohomology
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatChartCotangentCoherent
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatChartExtTransport
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatChartPerfectComparison

/-!
# The perfect complex of Situation 07YX at a chart of `Spaces'_{fp, flat, proper}`

Let `x` be a flat, proper, finitely presented algebraic space `f : X → Spec A` over a Noetherian
ring `A`, and `T^i(M) = Ext^i(L_{X/A}, 𝒪_X ⊗_A M)` (`i = 1, 2`) the deformation and obstruction
functors of [Stacks, Remark 0D1P] with their connecting map. As in the first proof of
[Stacks, Tag 08WA], [Stacks, Tag 08JR] gives a perfect complex `K` of `A`-modules with
`H^i(K ⊗ᴸ_A −) ≅ T^i` for `i = 1, 2`, natural and compatible with the boundary maps.

This file assembles that statement from
`exists_isPerfect_derivedCohomology_iso_cotangentExt_of_comparison` with the following inputs
(names not written in full are in the namespace `AlgebraicGeometry.Space.ProperFlatLift`):

* `L_{X/A} ∈ D^-_{Coh}` read on the small étale site
  (`exists_isCoherent_homology_isBoundedAbove_cotangentComplexDerived_chartStructureMap`),
* the comparison of `Ext` groups on the small étale site and on its model
  (`chartExtTransport`), and
* perfect complexes on `(Spec A)_étale` against perfect complexes of `A`-modules
  (`AlgebraicGeometry.Space.exists_isPerfect_smallEtaleTensorCohomology_affineBaseTilde_addEquiv`).

## The arguments taken, not proved here

* `hTop`, `hfqs`, `hY`, `hqc`, `hexact`: facts about the chart (quasi-separatedness of `f`,
  Noetherianity of `Spec A` in the site, quasi-coherence and exactness of `M ↦ M~`).
* `hf`, `hG`: `f` is locally of finite type, and `𝒪_X[0]` satisfies the hypotheses of 08JR on
  `𝒢^•` (bounded, coherent, flat over `Spec A`, proper support).
* `hlin`: `r : A` acts on `H^i(K ⊗ᴸ_A M)` through `H^i(K ⊗ᴸ_A (r • 𝟙_M))`.

## Main results

* `AlgebraicGeometry.Space.ProperFlatLift.exists_isPerfect_derivedCohomology_iso_cotangentExt`.

## References

* [Stacks Project, Tag 08JR](https://stacks.math.columbia.edu/tag/08JR)
* [Stacks Project, Remark 0D1P](https://stacks.math.columbia.edu/tag/0D1P)
* [Stacks Project, Tag 08WA](https://stacks.math.columbia.edu/tag/08WA)
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

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  (x : CartesianProperFlatSpaces B S hS)
  (hx : (cartesianProperFlatProjection B S hS).obj x = algebraOver A B S hS toS hA)
  [HasDerivedCategory.{t} (modelModules x.obj.obj.left)]

/-- **The perfect complex of Situation 07YX at a chart, from 08JR.** For `x` a flat, proper,
finitely presented `f : X → Spec A` with `A` Noetherian, there are a perfect complex `K` of
`A`-modules and natural isomorphisms `e_i : H^i(K ⊗ᴸ_A −) ≅ T^i(−) = Ext^i(L_{X/A}, 𝒪_X ⊗_A −)`
for `i = 1, 2`, carrying the boundary map of `K` to the connecting map `chartExtConnecting x hx`
of `T^•`. These are the data and condition (iv) asked of `theory` in
`Deformation.Artin.DualNotion.isOpenVersality_of_functorDeformationTheory`. -/
theorem exists_isPerfect_derivedCohomology_iso_cotangentExt [IsNoetherianRing A]
    (hTop : B.Contains (⊤_ Scheme.{u}))
    (hf : IsLocallyOfFiniteType B S hS (chartStructureMap x hx).hom)
    (hfqs : IsQuasiSeparated B S hS (chartStructureMap x hx).hom)
    (hY : IsNoetherian B S hS hTop (schemeSpace (algebraOver A B S hS toS hA)).1)
    (hqc : ∀ M : ModuleCat.{u} A,
      ((affineBaseTilde A B S hS toS hA).obj M).IsQuasicoherentOnSite)
    (hexact : ∀ {Sq : ShortComplex (ModuleCat.{u} A)}, Sq.ShortExact →
      (Sq.map (affineBaseTilde A B S hS toS hA)).ShortExact)
    (hG : FlatProperSupportComplex B S hS (chartStructureMap x hx) hf
      (structureSingleComplex x.obj.obj.left))
    (hlin : ∀ (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) (M : ModuleCat.{u} A) (r : A)
      (y : (derivedCohomology A K i).obj M), (derivedCohomology A K i).map (r • 𝟙 M) y = r • y) :
    ∃ (K : DerivedCategory (ModuleCat.{u} A))
      (e₁ : derivedCohomology A K 1 ≅
        cotangentExtOne (chartStructureMap x hx) (chartBaseRingHom x hx))
      (e₂ : derivedCohomology A K 2 ≅
        cotangentExtTwo (chartStructureMap x hx) (chartBaseRingHom x hx)),
      StacksDraft.Perfect.IsPerfect K ∧
        ∀ {Sq : ShortComplex (ModuleCat.{u} A)} (hSq : Sq.ShortExact),
          boundaryMap A K hSq ≫ e₂.hom.app Sq.X₁ =
            e₁.hom.app Sq.X₃ ≫ chartExtConnecting x hx hSq := by
  obtain ⟨E, ι, hEcoh, hEb⟩ :=
    exists_isCoherent_homology_isBoundedAbove_cotangentComplexDerived_chartStructureMap x hx hf
  exact exists_isPerfect_derivedCohomology_iso_cotangentExt_of_comparison x hx hTop hf hfqs hY hqc
    hexact E hEcoh hEb hG (chartExtTransport x hx E ι) (chartExtTransport_naturality x hx E ι)
    (fun hSq y => chartExtTransport_delta x hx E ι hf hG hSq (hexact hSq) y)
    (fun K hK => exists_isPerfect_smallEtaleTensorCohomology_affineBaseTilde_addEquiv A B S hS toS
      hA K hK) hlin

end AlgebraicGeometry.Space.ProperFlatLift

end
