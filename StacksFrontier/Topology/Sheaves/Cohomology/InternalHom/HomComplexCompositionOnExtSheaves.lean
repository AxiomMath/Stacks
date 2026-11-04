module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexCompositionComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedSheafExt

/-!
# The composition product on Ext sheaves comes from the internal Hom complex

Let `X` be a topological space with a sheaf of rings `O_X` and let `K`, `L`, `M` be complexes of
`O_X`-modules. On a ringed space the composition morphism of derived internal Homs of Stacks
0A8V is the composition morphism of Stacks 0A98 for the site of opens of `X`, and the
composition of Ext sheaves is the map it induces on cohomology sheaves. This file transports the
compatibility of derived composition with the naive composition morphism of internal Hom
complexes — `AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_composition` — to both of
those.

The point of the transport is that the Ext sheaves of a Koszul-regular quotient are computed
through the internal Hom complex of the Koszul resolution, where the composition product is the
naive one of Stacks 0A91 and is therefore computable; the composition product the Ext sheaves
carry is the derived one. The two statements below are what identifies them.

## Main results

* `Stacks.SheafOfModules.strictlyPerfectHomComparison_derivedSheafHomComposition`: the
  composition square of a ringed space.
* `Stacks.SheafOfModules.strictlyPerfectHomComparison_derivedSheafExtComposition`: **the
  composition of Ext sheaves is the naive composition read through the comparison**, the image
  of the previous square under the `n`-th cohomology sheaf functor.

## Implementation notes

The first statement is the ringed-site statement instantiated at the site of opens of `X`, at
the canonical derived tensor product and the canonical derived internal Hom. It needs no proof
beyond that instantiation: `Stacks.SheafOfModules.derivedSheafHomComposition` is *defined* as
the ringed-site composition morphism for those two choices, so the two sides of the square are
the same morphisms, not merely isomorphic ones. It is recorded because every consumer on a
ringed space quantifies over `Stacks.SheafOfModules.derivedSheafHomComposition` and would
otherwise have to unfold the definition.

The second statement is the first one under a functor, and uses nothing about the cohomology
sheaf functor beyond its functoriality.

## References

* [Stacks Project, Tag 0A8V](https://stacks.math.columbia.edu/tag/0A8V)
* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
* [Stacks Project, Tag 0A98](https://stacks.math.columbia.edu/tag/0A98)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

/-- **The composition square of a ringed space.** The canonical comparison from the internal Hom
complex to the derived internal Hom carries the composition morphism of internal Hom complexes
of Stacks 0A91 to the composition morphism of derived internal Homs of Stacks 0A8V, with no
hypothesis on the three complexes. -/
theorem strictlyPerfectHomComparison_derivedSheafHomComposition
    (K L M : CochainComplex (StructureSheafModules Rc) ℤ) :
    RingedSite.derivedTensorMap (ringedSite Rc) (canonicalDerivedTensorProduct (ringedSite Rc))
          (RingedSite.strictlyPerfectHomComparison (ringedSite Rc) (derivedInternalHom Rc) L M)
          (RingedSite.strictlyPerfectHomComparison (ringedSite Rc)
            (derivedInternalHom Rc) K L) ≫
        derivedSheafHomComposition Rc (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
          (DerivedCategory.Q.obj M) =
      RingedSite.homComplexDerivedComposition (ringedSite Rc)
          (canonicalDerivedTensorProduct (ringedSite Rc)) K L M ≫
        RingedSite.strictlyPerfectHomComparison (ringedSite Rc) (derivedInternalHom Rc) K M :=
  RingedSite.strictlyPerfectHomComparison_composition (ringedSite Rc)
    (canonicalDerivedTensorProduct (ringedSite Rc)) (derivedInternalHom Rc) K L M

/-- **The composition of Ext sheaves is the naive composition read through the comparison.** The
map that the composition morphism of derived internal Homs induces on `n`-th cohomology sheaves
agrees, under the comparison from the internal Hom complex, with the map induced by the
composition morphism of internal Hom complexes of Stacks 0A91. -/
theorem strictlyPerfectHomComparison_derivedSheafExtComposition
    (K L M : CochainComplex (StructureSheafModules Rc) ℤ) (n : ℤ) :
    (DerivedCategory.homologyFunctor (StructureSheafModules Rc) n).map
          (RingedSite.derivedTensorMap (ringedSite Rc)
            (canonicalDerivedTensorProduct (ringedSite Rc))
            (RingedSite.strictlyPerfectHomComparison (ringedSite Rc)
              (derivedInternalHom Rc) L M)
            (RingedSite.strictlyPerfectHomComparison (ringedSite Rc)
              (derivedInternalHom Rc) K L)) ≫
        derivedSheafExtComposition Rc (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
          (DerivedCategory.Q.obj M) n =
      (DerivedCategory.homologyFunctor (StructureSheafModules Rc) n).map
          (RingedSite.homComplexDerivedComposition (ringedSite Rc)
            (canonicalDerivedTensorProduct (ringedSite Rc)) K L M) ≫
        (DerivedCategory.homologyFunctor (StructureSheafModules Rc) n).map
          (RingedSite.strictlyPerfectHomComparison (ringedSite Rc)
            (derivedInternalHom Rc) K M) := by
  have hmap := (DerivedCategory.homologyFunctor (StructureSheafModules Rc) n).map_comp
    (RingedSite.derivedTensorMap (ringedSite Rc) (canonicalDerivedTensorProduct (ringedSite Rc))
      (RingedSite.strictlyPerfectHomComparison (ringedSite Rc) (derivedInternalHom Rc) L M)
      (RingedSite.strictlyPerfectHomComparison (ringedSite Rc) (derivedInternalHom Rc) K L))
    (derivedSheafHomComposition Rc (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
      (DerivedCategory.Q.obj M))
  exact hmap.symm.trans ((congrArg
    (fun f => (DerivedCategory.homologyFunctor (StructureSheafModules Rc) n).map f)
    (strictlyPerfectHomComparison_derivedSheafHomComposition Rc K L M)).trans
    ((DerivedCategory.homologyFunctor (StructureSheafModules Rc) n).map_comp _ _))

end Stacks.SheafOfModules

end
