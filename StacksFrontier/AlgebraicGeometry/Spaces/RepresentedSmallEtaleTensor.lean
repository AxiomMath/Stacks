module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleRingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Topologies.SiteEquivalenceTensor

/-!
# The comparison of Stacks 04M0 is compatible with the tensor product

Let `U` be an object of the big fppf site over `S` and let `T` be the scheme underlying it.  The
small étale site of the algebraic space `yoneda.obj U` is equivalent to the small étale site of
`T`, and `AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence` is the induced
equivalence of the categories of sheaves of modules — a
`CategoryTheory.SheafOfModules.pushforward` along that comparison of sites with the *identity*
structure map, the two structure sheaves agreeing on the nose.  This file supplies its
compatibility with the tensor product sheaf of Stacks 01CA:

`(𝓕 ⊗_{𝒪_T} 𝓖)` read on `yoneda.obj U` is `𝓕 ⊗_{𝒪} 𝓖` read there,

with no hypothesis on `𝓕` or `𝓖`.  The two sheafifications are formed on different sites, so the
statement is not formal.

It is `Stacks.SheafOfModules.reindexTensorIso` — Stacks 03EL at the morphism of ringed sites
presented by the inverse of the comparison — instantiated at
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence`.  The one further input that
instantiation needs is the site condition for that inverse, and either direction of an
equivalence of sites is a morphism of sites: that is
`AlgebraicGeometry.Space.isMorphismOfSites_representedSmallEtaleEquivalence_inverse` below, from
`IsMorphismOfSites.ofIsDenseSubsite` and
`AlgebraicGeometry.Space.isDenseSubsite_representedSmallEtaleEquivalence_inverse`.

## Main results

* `AlgebraicGeometry.Space.isMorphismOfSites_representedSmallEtaleEquivalence_inverse`: the
  inverse of the comparison of Stacks 04M0 is a morphism of sites.
* `AlgebraicGeometry.Space.representedSmallEtaleModuleTensorIso`: **the comparison of
  Stacks 04M0 carries the tensor product sheaf to the tensor product sheaf.**
* `AlgebraicGeometry.Space.representedSchemeTensorBifunctor_obj` and
  `AlgebraicGeometry.Space.representedSpaceTensorBifunctor_obj`: the two `rfl` bridges from the
  bifunctor spelling Stacks 03EL is stated with to the tensor product sheaf of Tag 01CA that the
  consumers write.

## Implementation notes

The comparison is stated with `Stacks.SheafOfModules.Tensor.sheafTensor` taken at the named
sheaves of commutative rings `AlgebraicGeometry.Space.representedSchemeCommRingStructureSheaf`
and `AlgebraicGeometry.Space.structureSheaf`. The spelling the consumers write takes it instead at
the sheaf of commutative rings rebuilt from the sheaf condition of the underlying sheaf of rings;
the two `rfl` bridges to that spelling are separate lemmas. Writing the consumers' spelling into
the result type instead exhausts the heartbeat budget at `whnf`.

The topology of the small étale site of `yoneda.obj U` is named as
`AlgebraicGeometry.Space.SmallEtale.topology` rather than as the projection
`(AlgebraicGeometry.Space.smallEtaleRingedSite ‹_›).J`, to which it is definitionally equal:
`AlgebraicGeometry.Space.smallEtaleRingedSite` is not reducible, so with the projection spelling
instance search does not find the continuity of the comparison functor.

No `@[stacks]` attribute is claimed.  Stacks 03EL is registered on
`Stacks.SheafOfModules.pullbackTensorIso` and Stacks 04M0 is not asserted here; this is the
compatibility of one comparison with one construction.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- The comma categories indexing the right Kan extension along the inverse of the comparison of
Stacks 04M0 have limits of sets in the universe of the sections of the structure sheaves, being
essentially small in it.  This is what the left adjoint of the direct image is built from. -/
instance hasLimitsOfShape_structuredArrow_representedSmallEtaleEquivalence_inverse
    (W : (SmallEtale B S hS (yoneda.obj U))ᵒᵖ) :
    Limits.HasLimitsOfShape
      (StructuredArrow W (representedSmallEtaleEquivalence B S hS U).inverse.op) (Type u) :=
  have : EssentiallySmall.{u}
      (StructuredArrow W (representedSmallEtaleEquivalence B S hS U).inverse.op) :=
    inferInstance
  Limits.hasLimitsOfShape_of_essentiallySmall _ _

/-- **The inverse of the comparison of Stacks 04M0 is a morphism of sites.**  Either direction of
an equivalence of sites is one, by `IsMorphismOfSites.ofIsDenseSubsite`; the dense-subsite
property of this inverse is
`AlgebraicGeometry.Space.isDenseSubsite_representedSmallEtaleEquivalence_inverse`. -/
instance isMorphismOfSites_representedSmallEtaleEquivalence_inverse :
    _root_.IsMorphismOfSites.{u} (representedSmallEtaleEquivalence B S hS U).inverse
      (representedSchemeSmallEtaleTopology B S hS U)
      (SmallEtale.topology B S hS (yoneda.obj U)) :=
  IsMorphismOfSites.ofIsDenseSubsite _

/-- The structure sheaf of commutative rings of the small étale site of the scheme underlying
`U`. -/
noncomputable abbrev representedSchemeCommRingStructureSheaf :
    Sheaf (representedSchemeSmallEtaleTopology B S hS U) CommRingCat.{u} :=
  _root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj U) U.left.property

/-- On the small étale site of the scheme underlying `U` the bifunctor of Stacks 03EL is the
tensor product sheaf of Tag 01CA. -/
theorem representedSchemeTensorBifunctor_obj
    (M N : SheafOfModules.{u} (representedSchemeStructureSheaf B S hS U)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (representedSchemeCommRingStructureSheaf B S hS U)).obj M).obj N =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨(representedSchemeCommRingStructureSheaf B S hS U).obj,
          Presheaf.isSheaf_of_isSheaf_comp _
            (representedSchemeCommRingStructureSheaf B S hS U).obj
            (forget₂ CommRingCat RingCat)
            (_root_.AlgebraicGeometry.SmallEtale.structure_isSheaf (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj U) U.left.property)⟩).obj M).obj N := rfl

/-- On the small étale site of `yoneda.obj U` the bifunctor of Stacks 03EL is the tensor product
sheaf of Tag 01CA. -/
theorem representedSpaceTensorBifunctor_obj
    (M N : SheafOfModules.{u} (representedStructureRingSheaf B S hS U)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (structureSheaf B S hS (yoneda.obj U)
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))).obj M).obj N =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨(structureSheaf B S hS (yoneda.obj U)
            (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U)).obj,
          Presheaf.isSheaf_of_isSheaf_comp _ _ (forget₂ CommRingCat RingCat)
            (representedStructureRingSheaf B S hS U).property⟩).obj M).obj N := rfl

/-- **The comparison of Stacks 04M0 carries the tensor product sheaf to the tensor product
sheaf.**  For modules `𝓕` and `𝓖` on the small étale site of the scheme underlying `U`, the
`𝒪`-module on the small étale site of `yoneda.obj U` attached to `𝓕 ⊗ 𝓖` is the tensor product of
the ones attached to `𝓕` and to `𝓖`, with no hypothesis on `𝓕` or `𝓖`.

This is `Stacks.SheafOfModules.reindexTensorIso` — Stacks 03EL at the morphism of ringed sites
presented by the inverse of the comparison — at
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence`. -/
def representedSmallEtaleModuleTensorIso
    (M N : SheafOfModules.{u} (representedSchemeStructureSheaf B S hS U)) :
    (representedSmallEtaleModuleEquivalence B S hS U).functor.obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (representedSchemeCommRingStructureSheaf B S hS U)).obj M).obj N) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} (structureSheaf B S hS
        (yoneda.obj U) (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))).obj
        ((representedSmallEtaleModuleEquivalence B S hS U).functor.obj M)).obj
        ((representedSmallEtaleModuleEquivalence B S hS U).functor.obj N) :=
  Stacks.SheafOfModules.reindexTensorIso (SmallEtale.topology B S hS (yoneda.obj U))
    (representedSmallEtaleEquivalence B S hS U)
    (representedSchemeCommRingStructureSheaf B S hS U) M N

end AlgebraicGeometry.Space

end
