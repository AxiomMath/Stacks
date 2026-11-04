module

public import StacksFrontier.Cotangent.ChartSiteDifferentials
public import StacksFrontier.Cotangent.ChartSiteSmallModelDerivedPullback
public import StacksFrontier.Cotangent.ChartSiteSmallModelModules
public import StacksFrontier.Homology.HomotopyCategory.QuasiIsoAlongExactFunctor

/-!
# Quasi-isomorphisms on the small model of the chart site

Restriction of sheaves of modules from the site `C_{X/Λ}` of Tag 08VA to its small model is an
equivalence of abelian categories, hence exact, so the induced functor on homotopy categories of
complexes identifies the two classes of quasi-isomorphisms: the quasi-isomorphisms upstairs are
exactly the morphisms whose restriction to the small model is one.

## Main results

* `AlgebraicGeometry.PolynomialChart.additive_smallChartModulesEquiv_functor`: restriction of
  sheaves of modules to the small model is additive. It is also exact, being an equivalence:
  instance search finds `PreservesFiniteLimits` and `PreservesFiniteColimits` for it through
  `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits` and
  `CategoryTheory.Limits.PreservesColimits.preservesFiniteColimits`.
* `AlgebraicGeometry.PolynomialChart.quasiIso_smallChartModulesEquiv_iff` and
  `AlgebraicGeometry.PolynomialChart.inverseImage_quasiIso_smallChartModulesEquiv`: the class
  `HomotopyCategory.quasiIso` of complexes of `R`-modules on the chart site is the inverse image
  of the class `HomotopyCategory.quasiIso` of complexes of modules over the restricted ring
  sheaf.
* `AlgebraicGeometry.PolynomialChart.inverseImage_quasiIso_smallAffineModulesEquiv` and
  `AlgebraicGeometry.PolynomialChart.inverseImage_quasiIso_smallChartStructureModulesEquiv`: the
  same statement at the two ring sheaves of the diagram of Tag 08VA, for the equivalences
  `AlgebraicGeometry.PolynomialChart.smallAffineModulesEquiv` and
  `AlgebraicGeometry.PolynomialChart.smallChartStructureModulesEquiv` onto the module categories
  of the small model on which the derived pullback `Li^*` of
  `AlgebraicGeometry.PolynomialChart.derivedSmallHorizontalPullback` is formed.

## Implementation notes

The coefficient universe is `u + 1`, the universe of the objects of the chart site, which is the
value of the free coefficient universe `max w (u + 1)` of Tag 08VA at which the diagram of ringed
topoi fits into a single universe. Sheaves of modules on the chart site are abelian there
because abelian presheaves admit sheafification in that universe, which is
`AlgebraicGeometry.PolynomialChart.hasSheafify_addCommGrpCat_topology`; on the small model this
is automatic, the site being small.

## References

* [Stacks Project, Tag 08VA](https://stacks.math.columbia.edu/tag/08VA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.PolynomialChart

variable (Λ : Type u) [CommRing Λ] (X : Scheme.{u})
    (structureMap : X ⟶ Spec (CommRingCat.of Λ))

/-- Abelian presheaves on the chart site admit sheafification in the universe `u + 1` of its
objects. -/
theorem hasSheafify_addCommGrpCat_topology_succ :
    HasSheafify (topology Λ X structureMap) AddCommGrpCat.{u + 1} :=
  hasSheafify_addCommGrpCat_topology.{u, u + 1} Λ X structureMap

/-- On the chart site the maps that sheafification of abelian presheaves inverts in the universe
`u + 1` of its objects are the locally bijective ones. -/
theorem wEqualsLocallyBijective_topology_succ :
    (topology Λ X structureMap).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  wEqualsLocallyBijective_topology.{u, u + 1} Λ X structureMap

attribute [local instance] hasSheafify_addCommGrpCat_topology_succ
  wEqualsLocallyBijective_topology_succ

variable (R : Sheaf (topology Λ X structureMap) RingCat.{u + 1})

/-- Restriction of sheaves of modules from the chart site to its small model is additive, being
an equivalence of additive categories. -/
theorem additive_smallChartModulesEquiv_functor :
    (smallChartModulesEquiv.{u + 1, u} Λ X structureMap R).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

attribute [local instance] additive_smallChartModulesEquiv_functor

variable {ι : Type*} (c : ComplexShape ι)

/-- **Restriction to the small model detects quasi-isomorphisms.** A morphism of the homotopy
category of complexes of `R`-modules on the chart site is a quasi-isomorphism if and only if its
restriction to the small model is one. -/
theorem quasiIso_smallChartModulesEquiv_iff
    {Y Z : HomotopyCategory (_root_.SheafOfModules.{u + 1} R) c} (f : Y ⟶ Z) :
    HomotopyCategory.quasiIso (_root_.SheafOfModules.{u + 1}
          ((restrictRingCatToSmallChart.{u + 1, u} Λ X structureMap).obj R)) c
        (((smallChartModulesEquiv.{u + 1, u} Λ X structureMap R).functor.mapHomotopyCategory
          c).map f) ↔
      HomotopyCategory.quasiIso (_root_.SheafOfModules.{u + 1} R) c f :=
  Functor.quasiIso_mapHomotopyCategory_map_iff c
    (smallChartModulesEquiv.{u + 1, u} Λ X structureMap R).functor f

/-- **The quasi-isomorphisms of the chart site are the inverse image of those of the small
model** along the equivalence of homotopy categories induced by restriction of sheaves of
modules. -/
theorem inverseImage_quasiIso_smallChartModulesEquiv :
    (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u + 1}
          ((restrictRingCatToSmallChart.{u + 1, u} Λ X structureMap).obj R)) c).inverseImage
        ((smallChartModulesEquiv.{u + 1, u} Λ X structureMap R).functor.mapHomotopyCategory c) =
      HomotopyCategory.quasiIso (_root_.SheafOfModules.{u + 1} R) c :=
  Functor.inverseImage_quasiIso_mapHomotopyCategory c
    (smallChartModulesEquiv.{u + 1, u} Λ X structureMap R).functor

/-! ### The two module categories of the diagram of Tag 08VA -/

/-- Restriction of sheaves of modules to the small model, read as an equivalence onto the
`𝒪`-modules of the small model of the ringed topos of Tag 08VA. -/
abbrev smallAffineModulesEquiv :
    _root_.SheafOfModules.{u + 1}
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1}
            (J := (topology Λ X structureMap)))
          (affineSheaf.{u, u + 1} Λ X structureMap)) ≌
      _root_.SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallAffineRingedTopos Λ X structureMap).O) :=
  smallChartModulesEquiv.{u + 1, u} Λ X structureMap
    ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1} (J := (topology Λ X structureMap)))
      (affineSheaf.{u, u + 1} Λ X structureMap))

/-- Restriction of sheaves of modules to the small model, read as an equivalence onto the
`π⁻¹𝒪_X`-modules of the small model of the ringed topos of Tag 08VA. -/
abbrev smallChartStructureModulesEquiv :
    _root_.SheafOfModules.{u + 1}
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1}
            (J := (topology Λ X structureMap)))
          (chartStructureSheaf.{u, u + 1} Λ X structureMap)) ≌
      _root_.SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (Stacks.Cohomology.ringedTopos (smallChartTopology Λ X structureMap)
            (smallChartStructureSheaf Λ X structureMap)).O) :=
  smallChartModulesEquiv.{u + 1, u} Λ X structureMap
    ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1} (J := (topology Λ X structureMap)))
      (chartStructureSheaf.{u, u + 1} Λ X structureMap))

/-- Restriction of the `𝒪`-modules of the chart site to the small model is additive. -/
theorem additive_smallAffineModulesEquiv_functor :
    (smallAffineModulesEquiv Λ X structureMap).functor.Additive :=
  additive_smallChartModulesEquiv_functor Λ X structureMap _

/-- Restriction of the `π⁻¹𝒪_X`-modules of the chart site to the small model is additive. -/
theorem additive_smallChartStructureModulesEquiv_functor :
    (smallChartStructureModulesEquiv Λ X structureMap).functor.Additive :=
  additive_smallChartModulesEquiv_functor Λ X structureMap _

attribute [local instance] additive_smallAffineModulesEquiv_functor
  additive_smallChartStructureModulesEquiv_functor

/-- **The quasi-isomorphisms of complexes of `𝒪`-modules on the chart site are the inverse
image of those on the small model.** This is the class with respect to which
`AlgebraicGeometry.PolynomialChart.hasLeftDerivedFunctor_smallEvaluation` derives the module
pullback along the horizontal arrow of the diagram of Tag 08VA. -/
theorem inverseImage_quasiIso_smallAffineModulesEquiv :
    (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallAffineRingedTopos Λ X structureMap).O))
        (ComplexShape.up ℤ)).inverseImage
        ((smallAffineModulesEquiv Λ X structureMap).functor.mapHomotopyCategory
          (ComplexShape.up ℤ)) =
      HomotopyCategory.quasiIso (_root_.SheafOfModules.{u + 1}
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1}
            (J := (topology Λ X structureMap)))
          (affineSheaf.{u, u + 1} Λ X structureMap))) (ComplexShape.up ℤ) :=
  inverseImage_quasiIso_smallChartModulesEquiv Λ X structureMap _ (ComplexShape.up ℤ)

/-- **The quasi-isomorphisms of complexes of `π⁻¹𝒪_X`-modules on the chart site are the inverse
image of those on the small model.** -/
theorem inverseImage_quasiIso_smallChartStructureModulesEquiv :
    (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (Stacks.Cohomology.ringedTopos (smallChartTopology Λ X structureMap)
              (smallChartStructureSheaf Λ X structureMap)).O))
        (ComplexShape.up ℤ)).inverseImage
        ((smallChartStructureModulesEquiv Λ X structureMap).functor.mapHomotopyCategory
          (ComplexShape.up ℤ)) =
      HomotopyCategory.quasiIso (_root_.SheafOfModules.{u + 1}
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1}
            (J := (topology Λ X structureMap)))
          (chartStructureSheaf.{u, u + 1} Λ X structureMap))) (ComplexShape.up ℤ) :=
  inverseImage_quasiIso_smallChartModulesEquiv Λ X structureMap _ (ComplexShape.up ℤ)

end AlgebraicGeometry.PolynomialChart

end
