module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.DerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsAlongIsomorphism
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology
public import StacksFrontier.CategoryTheory.Functor.Derived.EquivalenceConjugation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Modules.CoefficientChangePushforward
public import StacksFrontier.Cotangent.Spaces.ChartSiteSmallModelQuasiIso

/-!
# `Li^*` on the site of polynomial charts

The horizontal arrow `i : (Sh(C_{X/Λ}), π⁻¹𝒪_X) ⟶ (Sh(C_{X/Λ}), 𝒪)` of the diagram of
Tag 08VK is the identity on underlying topoi with structure map `i♯ : 𝒪 ⟶ π⁻¹𝒪_X`, and
`AlgebraicGeometry.Space.PolynomialChart.horizontalModuleInverseImage` is its module pullback `i^*`
on the chart site. This file produces the total left derived functor `Li^*` there.

The chart site has its objects in `Type (u + 1)` and its morphisms in `Type u`, so the K-flat
resolutions of Tag 06YS, which ask for one universe, are available only on its small model.
The passage from the small model is through the direct image: the two direct images of sheaves
of modules along `i` — the topos-level one and restriction of scalars along `i♯` — agree by
`AlgebraicGeometry.RingedToposHom.pushforwardModulesOfIdentityToposIso`, restriction of scalars
commutes with restriction to the small model, and `i^*` is a left adjoint of the result. The
derived functor is then transported along the two equivalences by
`CategoryTheory.Functor.hasLeftDerivedFunctor_conjugate_iff`.

## Main definitions

* `AlgebraicGeometry.Space.PolynomialChart.horizontalCoefficientMap`: `i♯ : 𝒪 ⟶ π⁻¹𝒪_X`, read as a
  map of the two structure sheaves of the diagram.
* `AlgebraicGeometry.Space.PolynomialChart.horizontalSiteHom` and `smallHorizontalSiteHom`: `i`
  presented as a change of coefficient rings, on the chart site and on its small model.
* `AlgebraicGeometry.Space.PolynomialChart.derivedHorizontalInverseImage`:
  `Li^* : D(𝒪) ⥤ D(π⁻¹𝒪_X)` on the chart site.

## Main results

* `AlgebraicGeometry.Space.PolynomialChart.horizontalPushforwardModulesIso`: the direct image
  `i_*` of sheaves of modules along `i` is restriction of scalars along `i♯`.
* `AlgebraicGeometry.Space.PolynomialChart.horizontalModuleInverseImageSmallModelIso`: `i^*` on the
  chart site is `i^*` on the small model, conjugated by the two restriction equivalences.
* `AlgebraicGeometry.Space.PolynomialChart.hasLeftDerivedFunctor_horizontalModuleInverseImage`:
  **`Li^*` exists on the chart site.**

## Implementation notes

The coefficient universe is `u + 1`, the universe of the objects of the chart site, in which the
ringed topoi of Tag 08VK are formed and at which the small model fits into a single universe.

`AlgebraicGeometry.RingedToposSiteHom.pullbackTopos`, the module pullback of a morphism of
ringed topoi presented by a functor of the underlying sites, is constructed only when the
sites are small in the universe of the sections of the structure sheaves, which the chart site
is at no universe. So `i^*` is the topos-level
`Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules`, which needs no such hypothesis,
and the
identification of the two direct images is what connects it to the small model, where the
site-level pullback does exist.

The square comparing restriction of scalars on the chart site with restriction of scalars on
the small model holds by `rfl`: both composites are Mathlib's `SheafOfModules.pushforward`
along the functor of the small model, taken at the same morphism of sheaves of rings.

## References

* [Stacks Project, Tag 08VM](https://stacks.math.columbia.edu/tag/08VM)
* [Stacks Project, Tag 08VK](https://stacks.math.columbia.edu/tag/08VK)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPullback
  Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space.PolynomialChart

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type u) [CommRing Λ] (B : BigFppfSite.{u})
  (hS : B.Contains (Spec (CommRingCat.of Λ)))
  (X : (BigFppfOver B (Spec (CommRingCat.of Λ)) hS)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B (Spec (CommRingCat.of Λ)) hS X)

attribute [-instance] CategoryTheory.Sheaf.hasSheafifyAddCommGrpCat
  CategoryTheory.Sheaf.wEqualsLocallyBijectiveAddCommGrpCat

attribute [local instance] hasSheafify_addCommGrpCat_topology wEqualsLocallyBijective_topology

/-! ### The horizontal arrow as a change of coefficient rings -/

/-- `i♯ : 𝒪 ⟶ π⁻¹𝒪_X`, the structure map of the horizontal arrow of the diagram of Tag 08VK,
read as a map of the two structure sheaves on the chart site. -/
def horizontalCoefficientMap :
    liftedAffineSheaf Λ B hS X hX ⟶ chartStructureSheaf Λ B hS X hX :=
  RingedToposHom.coefficientMapOfIdentityTopos (J := topology Λ B hS X hX)
    (O := liftedAffineSheaf Λ B hS X hX)
    (O' := chartStructureSheaf Λ B hS X hX)
    (liftedHorizontalHom Λ B hS X hX).fSharp

/-- The horizontal arrow `i` of the diagram of Tag 08VK, presented by the identity functor of
the chart site together with `i♯`. -/
abbrev horizontalSiteHom :
    RingedToposSiteHom
      ⟨PolynomialChart Λ B hS X hX, topology Λ B hS X hX,
        chartStructureSheaf Λ B hS X hX⟩
      ⟨PolynomialChart Λ B hS X hX, topology Λ B hS X hX,
        liftedAffineSheaf Λ B hS X hX⟩ :=
  RingedToposSiteHom.coefficientChange (topology Λ B hS X hX)
    (horizontalCoefficientMap Λ B hS X hX)

/-- The horizontal arrow `i` of the diagram of Tag 08VK, read on the small model of the chart
site: change of coefficient rings along the restriction of `i♯`. -/
abbrev smallHorizontalSiteHom :
    RingedToposSiteHom
      (Stacks.Cohomology.ringedTopos (smallChartTopology Λ B hS X hX)
        (smallChartStructureSheaf Λ B hS X hX))
      (smallAffineRingedTopos Λ B hS X hX) :=
  RingedToposSiteHom.coefficientChange (smallChartTopology Λ B hS X hX)
    ((restrictRingsToSmallChart Λ B hS X hX).map (horizontalCoefficientMap Λ B hS X hX))

/-! ### The direct image, and the comparison with the small model -/

/-- **`i_*` is restriction of scalars along `i♯`.** The direct image of sheaves of modules along
the horizontal arrow of the diagram of Tag 08VK, which transports the module structure along the
underlying geometric morphism, is restriction of scalars along `i♯`. -/
def horizontalPushforwardModulesIso :
    (liftedHorizontalHom Λ B hS X hX).pushforwardModules ≅
      (horizontalSiteHom Λ B hS X hX).pushforwardTopos :=
  RingedToposHom.pushforwardModulesOfIdentityToposIso
    (liftedHorizontalHom Λ B hS X hX).fSharp

/-- **`i_*` on the chart site is `i_*` on the small model.** Restriction of scalars along `i♯`
followed by restriction of modules to the small model is restriction of modules to the small
model followed by restriction of scalars along the restricted `i♯`: both are Mathlib's direct
image along the functor of the small model, at the same morphism of sheaves of rings. -/
theorem smallModel_pushforwardTopos_square :
    (smallChartStructureModulesEquiv Λ B hS X hX).functor ⋙
        (smallHorizontalSiteHom Λ B hS X hX).pushforwardTopos =
      (horizontalSiteHom Λ B hS X hX).pushforwardTopos ⋙
        (smallAffineModulesEquiv Λ B hS X hX).functor :=
  rfl

/-- `i_*` on the chart site, read as `i_*` on the small model conjugated by the two restriction
equivalences. -/
def horizontalPushforwardSmallModelIso :
    (liftedHorizontalHom Λ B hS X hX).pushforwardModules ≅
      ((smallChartStructureModulesEquiv Λ B hS X hX).functor ⋙
          (smallHorizontalSiteHom Λ B hS X hX).pushforwardTopos) ⋙
        (smallAffineModulesEquiv Λ B hS X hX).inverse :=
  horizontalPushforwardModulesIso Λ B hS X hX ≪≫ (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (smallAffineModulesEquiv Λ B hS X hX).unitIso

/-- **`i^*` on the chart site is `i^*` on the small model**, conjugated by the two restriction
equivalences. Both functors are left adjoints of the two direct images, which agree by
`horizontalPushforwardSmallModelIso`, so this is uniqueness of left adjoints. -/
def horizontalModuleInverseImageSmallModelIso :
    horizontalModuleInverseImage Λ B hS X hX ≅
      (smallAffineModulesEquiv Λ B hS X hX).functor ⋙
        (smallHorizontalSiteHom Λ B hS X hX).pullbackTopos ⋙
          (smallChartStructureModulesEquiv Λ B hS X hX).inverse :=
  Adjunction.leftAdjointUniq
    ((RingedToposHom.pullbackAdjPushforwardModules
      (liftedHorizontalHom Λ B hS X hX)).ofNatIsoRight
        (horizontalPushforwardSmallModelIso Λ B hS X hX))
    ((smallAffineModulesEquiv Λ B hS X hX).toAdjunction.comp
      ((smallHorizontalSiteHom Λ B hS X hX).pullbackPushforwardAdjunctionTopos.comp
        (smallChartStructureModulesEquiv Λ B hS X hX).symm.toAdjunction))

/-! ### The two equivalences, on homotopy and on derived categories -/

/-- Restriction of the `π⁻¹𝒪_X`-modules of the chart site to the small model is additive, being
an equivalence of additive categories. -/
theorem additive_smallChartStructureModulesEquiv_inverse :
    (smallChartStructureModulesEquiv Λ B hS X hX).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The same additivity, read at the functor of the inverse equivalence, which is the spelling
`Stacks.DerivedQCoh.Equivalence.mapDerivedCategory` asks for. -/
theorem additive_smallChartStructureModulesEquiv_symm_functor :
    (smallChartStructureModulesEquiv Λ B hS X hX).symm.functor.Additive :=
  additive_smallChartStructureModulesEquiv_inverse Λ B hS X hX

/-- `i^*` on the small model is additive, being a left adjoint. -/
theorem additive_pullbackTopos_smallHorizontalSiteHom :
    (smallHorizontalSiteHom Λ B hS X hX).pullbackTopos.Additive :=
  RingedToposSiteHom.pullbackTopos_additive (smallHorizontalSiteHom Λ B hS X hX)

attribute [local instance] additive_smallAffineModulesEquiv_functor
  additive_smallChartStructureModulesEquiv_functor
  additive_smallChartStructureModulesEquiv_inverse
  additive_smallChartStructureModulesEquiv_symm_functor
  horizontalModuleInverseImage_additive
  additive_pullbackTopos_smallHorizontalSiteHom

/-- Restriction of the `𝒪`-modules of the chart site to the small model is an equivalence on
homotopy categories of unbounded complexes. -/
theorem isEquivalence_mapHomotopyCategory_smallAffineModulesEquiv :
    ((smallAffineModulesEquiv Λ B hS X hX).functor.mapHomotopyCategory
      (ComplexShape.up ℤ)).IsEquivalence :=
  Stacks.DerivedFunctor.isEquivalence_mapHomotopyCategory _

attribute [local instance] isEquivalence_mapHomotopyCategory_smallAffineModulesEquiv

/-- Restriction of the `𝒪`-modules of the chart site to the small model, as an equivalence of
homotopy categories of unbounded complexes. -/
abbrev homotopyCategorySmallAffineEquiv :
    HomotopyCategory (_root_.SheafOfModules.{u + 1}
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1} (J := (topology Λ B hS X hX)))
          (liftedAffineSheaf Λ B hS X hX))) (ComplexShape.up ℤ) ≌
      HomotopyCategory (_root_.SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallAffineRingedTopos Λ B hS X hX).O))
        (ComplexShape.up ℤ) :=
  ((smallAffineModulesEquiv Λ B hS X hX).functor.mapHomotopyCategory
    (ComplexShape.up ℤ)).asEquivalence

/-- Extension of the `π⁻¹𝒪_X`-modules of the small model back to the chart site, as an
equivalence of derived categories: it is an exact equivalence of abelian categories. -/
abbrev derivedCategorySmallChartStructureEquiv :
    DerivedCategory (_root_.SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (Stacks.Cohomology.ringedTopos (smallChartTopology Λ B hS X hX)
            (smallChartStructureSheaf Λ B hS X hX)).O)) ≌
      DerivedCategory (_root_.SheafOfModules.{u + 1}
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1} (J := (topology Λ B hS X hX)))
          (chartStructureSheaf Λ B hS X hX))) :=
  Stacks.DerivedQCoh.Equivalence.mapDerivedCategory
    (smallChartStructureModulesEquiv Λ B hS X hX).symm

/-! ### The derived pullback -/

/-- Degreewise `i^*` on the chart site, followed by localization to the derived category, is its
counterpart on the small model conjugated by the two equivalences. This is
`horizontalModuleInverseImageSmallModelIso` applied degreewise and then read through the
factorization of the induced functor on derived categories. -/
def pullbackOnHomotopySmallModelIso :
    Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackOnHomotopy.{u, u + 1, u + 1,
        u, u + 1, u + 1} (liftedHorizontalHom Λ B hS X hX) ≅
      (homotopyCategorySmallAffineEquiv Λ B hS X hX).functor ⋙
        Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.pullbackOnHomotopy.{u + 1}
          (smallHorizontalSiteHom Λ B hS X hX) ⋙
          (derivedCategorySmallChartStructureEquiv Λ B hS X hX).functor :=
  Functor.isoWhiskerRight
      (Stacks.Homology.mapHomotopyCategoryIso
          (horizontalModuleInverseImageSmallModelIso Λ B hS X hX) (ComplexShape.up ℤ) ≪≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (ComplexShape.up ℤ)).symm ≪≫
        Functor.isoWhiskerLeft _
          (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (ComplexShape.up ℤ)).symm)
      DerivedCategory.Qh ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
      (smallChartStructureModulesEquiv Λ B hS X hX).inverse.mapDerivedCategoryFactorsh.symm)

/-- **`Li^*` exists on the site of polynomial charts.** Degreewise `i^*` followed by
localization to the derived category has a total left derived functor with respect to the
quasi-isomorphisms of complexes of `𝒪`-modules.

On the small model this is the derived pullback of Tag 06YY along a change of coefficient rings;
the quasi-isomorphisms of the chart site are the inverse image of those of the small model, and
total left derived functors are preserved by conjugation by equivalences. This is the existence
of the functor `Li^*` appearing in Tag 08VM. -/
theorem hasLeftDerivedFunctor_horizontalModuleInverseImage :
    ((horizontalModuleInverseImage Λ B hS X hX).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u + 1}
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1} (J := (topology Λ B hS X hX)))
          (liftedAffineSheaf Λ B hS X hX))) (ComplexShape.up ℤ)) := by
  have h := (Functor.hasLeftDerivedFunctor_conjugate_iff
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.pullbackOnHomotopy.{u + 1}
      (smallHorizontalSiteHom Λ B hS X hX))
    (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallAffineRingedTopos Λ B hS X hX).O))
      (ComplexShape.up ℤ))
    (homotopyCategorySmallAffineEquiv Λ B hS X hX)
    (derivedCategorySmallChartStructureEquiv Λ B hS X hX)).mp inferInstance
  rw [show (homotopyCategorySmallAffineEquiv Λ B hS X hX).functor =
    (smallAffineModulesEquiv Λ B hS X hX).functor.mapHomotopyCategory
      (ComplexShape.up ℤ) from rfl,
    inverseImage_quasiIso_smallAffineModulesEquiv] at h
  exact (Functor.hasLeftDerivedFunctor_iff_of_iso
    (pullbackOnHomotopySmallModelIso Λ B hS X hX) _).mpr h

attribute [local instance] hasLeftDerivedFunctor_horizontalModuleInverseImage

/-- `Li^* : D(𝒪) ⥤ D(π⁻¹𝒪_X)` on the site of polynomial charts, the total left derived functor
of the module pullback along the horizontal arrow of the diagram of Tag 08VK. -/
abbrev derivedHorizontalInverseImage :
    DerivedCategory (_root_.SheafOfModules.{u + 1}
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1} (J := (topology Λ B hS X hX)))
          (liftedAffineSheaf Λ B hS X hX))) ⥤
      DerivedCategory (_root_.SheafOfModules.{u + 1}
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1} (J := (topology Λ B hS X hX)))
          (chartStructureSheaf Λ B hS X hX))) :=
  ((horizontalModuleInverseImage Λ B hS X hX).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalLeftDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u + 1}
      ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1} (J := (topology Λ B hS X hX)))
        (liftedAffineSheaf Λ B hS X hX))) (ComplexShape.up ℤ))

end AlgebraicGeometry.Space.PolynomialChart

end
