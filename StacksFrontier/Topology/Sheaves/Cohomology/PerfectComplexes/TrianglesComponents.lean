module

public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles

/-!
# The components of the two comparisons of derived functors

`Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryIsoOfNatIso` and
`Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso` are the two isomorphisms
every chain of derived functors in the library is assembled from: the first says that isomorphic
exact functors induce isomorphic functors on derived categories, the second that the derived
functor of a composite is the composite of the derived functors.  Both are
`CategoryTheory.Localization.liftNatIso` of an isomorphism of functors on cochain complexes, so
both are determined by their components at the objects `DerivedCategory.Q.obj P`, and neither had
those components recorded.

That is the obstruction to unfolding any composite built from them — for instance
`AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing`, the derived stalk of a
pushforward along a closed immersion, which is six of them in a row and about which the library
proves nothing beyond its definition.  This file records the four components, so that such a
composite can be evaluated at `DerivedCategory.Q.obj P` and compared with the underived
isomorphism it descends from.

Everything here is stated over abstract abelian categories, where the two sides are composites of
free functors and every rewrite fires; the local-ring and `RingCat` spellings of a stalk, which
are definitionally but not reducibly equal, never appear.

## Main results

* `Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryIsoOfNatIso_hom_app` and
  `..._inv_app`: the components of the comparison induced by an isomorphism of exact functors —
  the two `Functor.mapDerivedCategoryFactors` with `DerivedCategory.Q` of the degreewise
  isomorphism between them.
* `Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso_hom_app` and
  `..._inv_app`: the components of the comparison of the derived functor of a composite with the
  composite of the derived functors.
* `Stacks.Cohomology.PerfectComplexTriangles.mapHomologicalComplexCompIso_refl_hom_app` and
  `..._inv_app`: the degreewise comparison at the identity of `F ⋙ G` is the identity, which is
  why the two statements above carry no third factor.

## Implementation notes

*Why the composite comparison's components carry no third factor.*  `mapDerivedCategoryCompIso`
is defined with `CategoryTheory.Functor.mapHomologicalComplexCompIso` of `Iso.refl (F ⋙ G)`
between its two `mapDerivedCategoryFactors`.  That isomorphism is the identity — it is the
identity in each degree, which is `mapHomologicalComplexCompIso_refl_inv_app` below — so it drops
out of the components and the two statements have two factors each rather than three.

## References

The derived-functor comparisons themselves are Mathlib's
`CategoryTheory.Functor.mapDerivedCategory` and `Functor.mapDerivedCategoryFactors`, lifted by
`CategoryTheory.Localization.liftNatIso`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace Stacks.Cohomology.PerfectComplexTriangles

universe u₁ u₂ u₃ v₁ v₂ v₃ w₁ w₂ w₃

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {E : Type u₃} [Category.{v₃} E] [Abelian E]

/-! ### The comparison induced by an isomorphism of exact functors -/

/-- **The component of `mapDerivedCategoryIsoOfNatIso` at `Q.obj P`.**  It is the universal
factorization of `F.mapDerivedCategory` through `DerivedCategory.Q`, then `Q` of the degreewise
isomorphism `e`, then the inverse factorization for `G`. -/
theorem mapDerivedCategoryIsoOfNatIso_hom_app
    [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
    (F G : C ⥤ D) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G)
    (P : CochainComplex C ℤ) :
    (mapDerivedCategoryIsoOfNatIso F G e).hom.app (DerivedCategory.Q.obj P) =
      F.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.app P) ≫
        G.mapDerivedCategoryFactors.inv.app P := by
  simp [mapDerivedCategoryIsoOfNatIso]

/-- `mapDerivedCategoryIsoOfNatIso_hom_app` for the inverse, which is the component for `e.symm`
read in the other order. -/
theorem mapDerivedCategoryIsoOfNatIso_inv_app
    [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
    (F G : C ⥤ D) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G)
    (P : CochainComplex C ℤ) :
    (mapDerivedCategoryIsoOfNatIso F G e).inv.app (DerivedCategory.Q.obj P) =
      G.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).inv.app P) ≫
        F.mapDerivedCategoryFactors.inv.app P := by
  simp [mapDerivedCategoryIsoOfNatIso]

/-! ### The comparison of the derived functor of a composite -/

/-- The degreewise comparison of `(F ⋙ G).mapHomologicalComplex` with the composite of the two
`mapHomologicalComplex`, taken at the identity of `F ⋙ G`, is the identity: it is the identity in
each degree. -/
theorem mapHomologicalComplexCompIso_refl_inv_app (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] (P : CochainComplex C ℤ) :
    (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).inv.app P =
      CategoryStruct.id _ := by
  ext n
  simp [Functor.mapHomologicalComplexCompIso]

/-- `mapHomologicalComplexCompIso_refl_inv_app` for the forward direction. -/
theorem mapHomologicalComplexCompIso_refl_hom_app (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] (P : CochainComplex C ℤ) :
    (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).hom.app P =
      CategoryStruct.id _ := by
  ext n
  simp [Functor.mapHomologicalComplexCompIso]

/-- **The component of `mapDerivedCategoryCompIso` at `Q.obj P`.**  It is the universal
factorization for `F ⋙ G`, then the inverse factorization for `G` at the degreewise image of `P`
under `F`, then `G.mapDerivedCategory` of the inverse factorization for `F`. -/
theorem mapDerivedCategoryCompIso_hom_app
    [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D] [HasDerivedCategory.{w₃} E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (P : CochainComplex C ℤ) :
    (mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Q.obj P) =
      (F ⋙ G).mapDerivedCategoryFactors.hom.app P ≫
        G.mapDerivedCategoryFactors.inv.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app P) := by
  simp [mapDerivedCategoryCompIso, mapHomologicalComplexCompIso_refl_inv_app]

/-- `mapDerivedCategoryCompIso_hom_app` for the inverse. -/
theorem mapDerivedCategoryCompIso_inv_app
    [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D] [HasDerivedCategory.{w₃} E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (P : CochainComplex C ℤ) :
    (mapDerivedCategoryCompIso F G).inv.app (DerivedCategory.Q.obj P) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        G.mapDerivedCategoryFactors.hom.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          (F ⋙ G).mapDerivedCategoryFactors.inv.app P := by
  simp [mapDerivedCategoryCompIso, mapHomologicalComplexCompIso_refl_hom_app]

end Stacks.Cohomology.PerfectComplexTriangles

end

end
