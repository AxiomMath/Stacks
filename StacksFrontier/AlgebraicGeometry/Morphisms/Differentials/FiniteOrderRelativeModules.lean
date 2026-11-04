module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.DeRhamOrderOne
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.FiniteOrderCategory
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.RelativeStructureSheafComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.DifferentialOperatorsLinear
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModuleFunctors

/-!
# Finite-order differential operators as morphisms of modules over the inverse image of `𝒪_S`

Let `a : X ⟶ S` be a morphism of schemes. A differential operator on `X/S` of finite order is
`a⁻¹𝒪_S`-linear on local sections, so the category of finite-order differential operators maps
to the category of modules over the structure sheaf of the inverse-image ringed space
`(X, a⁻¹𝒪_S)`, by the identity on underlying sheaves of abelian groups. The module structure is
restriction of scalars along the relative structure sheaf map, transported along the comparison
between the inverse image of `𝒪_S` formed in sheaves of rings and the one formed in sheaves of
commutative rings.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.relativeStructureSheafMapInverseImage` is the relative structure
  sheaf map read, through that comparison, as a morphism out of the structure sheaf of the
  inverse-image ringed space.
* `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.toInverseImageModules` is the
  resulting functor to `a⁻¹𝒪_S`-modules.

## Main results

* `AlgebraicGeometry.Scheme.Hom.relativeStructureSheafMapInverseImage_eq`: the transported map is
  the relative structure sheaf map formed in sheaves of commutative rings, so the module
  structure obtained by restriction of scalars along it is the structural one.
* `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.toInverseImageModules_map`: the
  functor acts on a morphism by the differential operator itself on local sections.

## References

* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
* [Stacks Project, Tag 0G44](https://stacks.math.columbia.edu/tag/0G44)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

namespace Scheme.Hom

/-- The structural morphism `a⁻¹𝒪_S ⟶ 𝒪_X` out of the structure sheaf of the inverse-image
ringed space `(X, a⁻¹𝒪_S)`, as a morphism of sheaves of rings. -/
noncomputable def relativeStructureSheafMapInverseImage (a : X ⟶ S) :
    (sheafCompose (Opens.grothendieckTopology (X.carrier : TopCat.{u}))
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
      ((TopCat.Sheaf.pullback CommRingCat.{u} a.base).obj S.sheaf) ⟶ X.ringCatSheaf :=
  (sheafCompose (Opens.grothendieckTopology (X.carrier : TopCat.{u}))
    (forget₂ CommRingCat.{u} RingCat.{u})).map a.relativeStructureSheafMapCommRingCat

/-- Read through the comparison of the two inverse images of `𝒪_S`, the structural morphism out
of the inverse-image ringed space is the relative structure sheaf map; so restriction of scalars
along it is restriction of scalars along the relative structure sheaf map. -/
theorem relativeStructureSheafMapInverseImage_eq (a : X ⟶ S) :
    relativeStructureSheafMapInverseImage a =
      (inverseImageRingSheafComparison a).inv ≫ a.relativeStructureSheafMap :=
  (Iso.eq_inv_comp _).2 (inverseImageRingSheafComparison_hom_comp a)

end Scheme.Hom

namespace FiniteOrderDifferentialOperatorCategory

variable {a : X ⟶ S}

/-- A differential operator on `X/S` of finite order has finite order relative to the structure
sheaf of the inverse-image ringed space `(X, a⁻¹𝒪_S)`. -/
lemma exists_isGlobalDiffOpOfOrder_inverseImage {F G : X.Modules} {D : DiffOp.GlobalOp F G}
    (hD : ∃ k, DiffOp.IsGlobalDiffOpOfOrder a.relativeStructureSheafMap k D) :
    ∃ k, DiffOp.IsGlobalDiffOpOfOrder
      (Scheme.Hom.relativeStructureSheafMapInverseImage a) k D :=
  hD.imp fun k hk => by
    rw [Scheme.Hom.relativeStructureSheafMapInverseImage_eq]
    exact DiffOp.isGlobalDiffOpOfOrder_comp_structureMap
      a.inverseImageRingSheafComparison.inv a.relativeStructureSheafMap k D hk

/-- The category of finite-order differential operators on `X/S` maps to the category of modules
over the inverse image `a⁻¹𝒪_S` of the structure sheaf of `S`: a finite-order differential
operator is `a⁻¹𝒪_S`-linear on local sections. -/
noncomputable def toInverseImageModules (a : X ⟶ S) :
    FiniteOrderDifferentialOperatorCategory a ⥤
      Modules (RingedSpace.inverseImage S.toRingedSpace a.base) where
  obj F :=
    (SheafOfModules.restrictScalars.{u} (Scheme.Hom.relativeStructureSheafMapInverseImage a)).obj
      F.module
  map f := DiffOp.GlobalOp.restrictScalarsHomOfFiniteOrder
    (Scheme.Hom.relativeStructureSheafMapInverseImage a) f.1
    (exists_isGlobalDiffOpOfOrder_inverseImage f.2)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The functor to `a⁻¹𝒪_S`-modules leaves a module unchanged, as a restriction of scalars. -/
lemma toInverseImageModules_obj (F : FiniteOrderDifferentialOperatorCategory a) :
    (toInverseImageModules a).obj F =
      (SheafOfModules.restrictScalars.{u}
        (Scheme.Hom.relativeStructureSheafMapInverseImage a)).obj F.module := rfl

/-- The functor to `a⁻¹𝒪_S`-modules sends a finite-order differential operator to itself, read as
an `a⁻¹𝒪_S`-linear map on local sections. -/
lemma toInverseImageModules_map {F G : FiniteOrderDifferentialOperatorCategory a} (f : F ⟶ G) :
    (toInverseImageModules a).map f =
      DiffOp.GlobalOp.restrictScalarsHomOfFiniteOrder
        (Scheme.Hom.relativeStructureSheafMapInverseImage a) f.1
        (exists_isGlobalDiffOpOfOrder_inverseImage f.2) := rfl

/-- The functor to `a⁻¹𝒪_S`-modules is additive. -/
instance : (toInverseImageModules a).Additive where
  map_add := rfl

end FiniteOrderDifferentialOperatorCategory

end AlgebraicGeometry
