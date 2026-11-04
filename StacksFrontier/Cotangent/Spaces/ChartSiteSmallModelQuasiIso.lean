module

public import StacksFrontier.Cotangent.Spaces.ChartSiteDifferentials
public import StacksFrontier.Cotangent.Spaces.ChartSiteSmallModelDerivedPullback
public import StacksFrontier.Cotangent.Spaces.ChartSiteSmallModelModules
public import StacksFrontier.Homology.HomotopyCategory.QuasiIsoAlongExactFunctor

/-!
# Quasi-isomorphisms on the small model of the chart site

Restriction of sheaves of modules from the site `C_{X/Λ}` of Tag 08VK to its small model is an
equivalence of abelian categories, hence exact, so the induced functor on homotopy categories of
complexes identifies the two classes of quasi-isomorphisms: the quasi-isomorphisms upstairs are
exactly the morphisms whose restriction to the small model is one.

## Main results

* `AlgebraicGeometry.Space.PolynomialChart.additive_smallChartModulesEquiv_functor`: restriction
  of sheaves of modules to the small model is additive. It is also exact, being an equivalence:
  instance search finds `PreservesFiniteLimits` and `PreservesFiniteColimits` for it through
  `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits` and
  `CategoryTheory.Limits.PreservesColimits.preservesFiniteColimits`.
* `AlgebraicGeometry.Space.PolynomialChart.quasiIso_smallChartModulesEquiv_iff` and
  `AlgebraicGeometry.Space.PolynomialChart.inverseImage_quasiIso_smallChartModulesEquiv`: the class
  `HomotopyCategory.quasiIso` of complexes of `R`-modules on the chart site is the inverse image
  of the class `HomotopyCategory.quasiIso` of complexes of modules over the restricted ring
  sheaf.
* `AlgebraicGeometry.Space.PolynomialChart.inverseImage_quasiIso_smallAffineModulesEquiv` and
  `AlgebraicGeometry.Space.PolynomialChart.inverseImage_quasiIso_smallChartStructureModulesEquiv`:
  the same statement at the two ring sheaves of the diagram of Tag 08VK, for the equivalences
  `AlgebraicGeometry.Space.PolynomialChart.smallAffineModulesEquiv` and
  `AlgebraicGeometry.Space.PolynomialChart.smallChartStructureModulesEquiv` onto the module
  categories of the small model on which the derived pullback `Li^*` of
  `AlgebraicGeometry.Space.PolynomialChart.derivedSmallHorizontalPullback` is formed.

## Implementation notes

The coefficient universe is `u + 1`, the universe of the objects of the chart site, in which the
ringed topoi of Tag 08VK are formed. Sheaves of modules on the chart site are abelian there
because abelian presheaves admit sheafification in that universe, which is
`AlgebraicGeometry.Space.PolynomialChart.hasSheafify_addCommGrpCat_topology`; on the small model
it is `AlgebraicGeometry.Space.PolynomialChart.hasSheafify_smallChartTopology`.

## References

* [Stacks Project, Tag 08VK](https://stacks.math.columbia.edu/tag/08VK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.PolynomialChart

variable (Λ : Type u) [CommRing Λ] (B : BigFppfSite.{u})
  (hS : B.Contains (Spec (CommRingCat.of Λ)))
  (X : (BigFppfOver B (Spec (CommRingCat.of Λ)) hS)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B (Spec (CommRingCat.of Λ)) hS X)

attribute [local instance] hasSheafify_addCommGrpCat_topology wEqualsLocallyBijective_topology

variable (R : Sheaf (topology Λ B hS X hX) RingCat.{u + 1})

/-- Restriction of sheaves of modules from the chart site to its small model is additive, being
an equivalence of additive categories. -/
theorem additive_smallChartModulesEquiv_functor :
    (smallChartModulesEquiv Λ B hS X hX R).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

attribute [local instance] additive_smallChartModulesEquiv_functor

variable {ι : Type*} (c : ComplexShape ι)

/-- **Restriction to the small model detects quasi-isomorphisms.** A morphism of the homotopy
category of complexes of `R`-modules on the chart site is a quasi-isomorphism if and only if its
restriction to the small model is one. -/
theorem quasiIso_smallChartModulesEquiv_iff
    {Y Z : HomotopyCategory (_root_.SheafOfModules.{u + 1} R) c} (f : Y ⟶ Z) :
    HomotopyCategory.quasiIso (_root_.SheafOfModules.{u + 1}
          ((restrictRingCatToSmallChart Λ B hS X hX).obj R)) c
        (((smallChartModulesEquiv Λ B hS X hX R).functor.mapHomotopyCategory
          c).map f) ↔
      HomotopyCategory.quasiIso (_root_.SheafOfModules.{u + 1} R) c f :=
  Functor.quasiIso_mapHomotopyCategory_map_iff c
    (smallChartModulesEquiv Λ B hS X hX R).functor f

/-- **The quasi-isomorphisms of the chart site are the inverse image of those of the small
model** along the equivalence of homotopy categories induced by restriction of sheaves of
modules. -/
theorem inverseImage_quasiIso_smallChartModulesEquiv :
    (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u + 1}
          ((restrictRingCatToSmallChart Λ B hS X hX).obj R)) c).inverseImage
        ((smallChartModulesEquiv Λ B hS X hX R).functor.mapHomotopyCategory c) =
      HomotopyCategory.quasiIso (_root_.SheafOfModules.{u + 1} R) c :=
  Functor.inverseImage_quasiIso_mapHomotopyCategory c
    (smallChartModulesEquiv Λ B hS X hX R).functor

/-! ### The two module categories of the diagram of Tag 08VK -/

/-- Restriction of sheaves of modules to the small model, read as an equivalence onto the
`𝒪`-modules of the small model of the ringed topos of Tag 08VK. -/
abbrev smallAffineModulesEquiv :
    _root_.SheafOfModules.{u + 1}
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1} (J := (topology Λ B hS X hX)))
          (liftedAffineSheaf Λ B hS X hX)) ≌
      _root_.SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallAffineRingedTopos Λ B hS X hX).O) :=
  smallChartModulesEquiv Λ B hS X hX
    ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1} (J := (topology Λ B hS X hX)))
      (liftedAffineSheaf Λ B hS X hX))

/-- Restriction of sheaves of modules to the small model, read as an equivalence onto the
`π⁻¹𝒪_X`-modules of the small model of the ringed topos of Tag 08VK. -/
abbrev smallChartStructureModulesEquiv :
    _root_.SheafOfModules.{u + 1}
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1} (J := (topology Λ B hS X hX)))
          (chartStructureSheaf Λ B hS X hX)) ≌
      _root_.SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (Stacks.Cohomology.ringedTopos (smallChartTopology Λ B hS X hX)
            (smallChartStructureSheaf Λ B hS X hX)).O) :=
  smallChartModulesEquiv Λ B hS X hX
    ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1} (J := (topology Λ B hS X hX)))
      (chartStructureSheaf Λ B hS X hX))

/-- Restriction of the `𝒪`-modules of the chart site to the small model is additive. -/
theorem additive_smallAffineModulesEquiv_functor :
    (smallAffineModulesEquiv Λ B hS X hX).functor.Additive :=
  additive_smallChartModulesEquiv_functor Λ B hS X hX _

/-- Restriction of the `π⁻¹𝒪_X`-modules of the chart site to the small model is additive. -/
theorem additive_smallChartStructureModulesEquiv_functor :
    (smallChartStructureModulesEquiv Λ B hS X hX).functor.Additive :=
  additive_smallChartModulesEquiv_functor Λ B hS X hX _

attribute [local instance] additive_smallAffineModulesEquiv_functor
  additive_smallChartStructureModulesEquiv_functor

/-- **The quasi-isomorphisms of complexes of `𝒪`-modules on the chart site are the inverse
image of those on the small model.** This is the class with respect to which
`AlgebraicGeometry.Space.PolynomialChart.hasLeftDerivedFunctor_smallEvaluation` derives the module
pullback along the horizontal arrow of the diagram of Tag 08VK. -/
theorem inverseImage_quasiIso_smallAffineModulesEquiv :
    (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallAffineRingedTopos Λ B hS X hX).O))
        (ComplexShape.up ℤ)).inverseImage
        ((smallAffineModulesEquiv Λ B hS X hX).functor.mapHomotopyCategory
          (ComplexShape.up ℤ)) =
      HomotopyCategory.quasiIso (_root_.SheafOfModules.{u + 1}
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1} (J := (topology Λ B hS X hX)))
          (liftedAffineSheaf Λ B hS X hX))) (ComplexShape.up ℤ) :=
  inverseImage_quasiIso_smallChartModulesEquiv Λ B hS X hX _ (ComplexShape.up ℤ)

/-- **The quasi-isomorphisms of complexes of `π⁻¹𝒪_X`-modules on the chart site are the inverse
image of those on the small model.** -/
theorem inverseImage_quasiIso_smallChartStructureModulesEquiv :
    (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (Stacks.Cohomology.ringedTopos (smallChartTopology Λ B hS X hX)
              (smallChartStructureSheaf Λ B hS X hX)).O))
        (ComplexShape.up ℤ)).inverseImage
        ((smallChartStructureModulesEquiv Λ B hS X hX).functor.mapHomotopyCategory
          (ComplexShape.up ℤ)) =
      HomotopyCategory.quasiIso (_root_.SheafOfModules.{u + 1}
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1} (J := (topology Λ B hS X hX)))
          (chartStructureSheaf Λ B hS X hX))) (ComplexShape.up ℤ) :=
  inverseImage_quasiIso_smallChartModulesEquiv Λ B hS X hX _ (ComplexShape.up ℤ)

end AlgebraicGeometry.Space.PolynomialChart

end
