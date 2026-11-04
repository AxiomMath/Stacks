module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.Multiplicative
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.BaseChange

/-!
# The multiplicative group algebraic space

Let `B` be an algebraic space over a scheme `S`.  The functor sending a scheme `T` over `B` to
the group `Γ(T, 𝒪_T^*)` of units in the global sections of its structure sheaf is represented by
the group algebraic space `Gₘ,B = B ×_S Gₘ,S`, the base change to `B` of the multiplicative
group scheme over `S`.

## Main definitions

* `AlgebraicGeometry.Space.multiplicativeGroupSiteObject` is the multiplicative group scheme
  over `S`, read as an object of the big fppf site over `S`.
* `AlgebraicGeometry.Space.multiplicativeGroupSpace`: **Stacks 043J**, the multiplicative group
  algebraic space over `B`.
* `AlgebraicGeometry.Space.multiplicativeGroupSpacePoints`: **Stacks 043J**, its group of points
  over a scheme over `B`, identified with the group of global units.

## Main results

* `AlgebraicGeometry.Space.multiplicativeGroupSpace_obj_X` identifies the underlying algebraic
  space with the fibre product of `B` and the functor of points of `Gₘ,S`.
* `AlgebraicGeometry.Space.multiplicativeGroupSpacePoints_apply` and
  `AlgebraicGeometry.Space.multiplicativeGroupSpacePoints_naturality` pin the identification on
  points down, naturally in the test scheme.

## Implementation notes

The base `B` is an arbitrary algebraic space over `S`; it is not assumed to be a scheme.  The
group law on points is the one prescribed by **Stacks 022U**, through the natural isomorphism
`AlgebraicGeometry.baseChangePointsIsoGlobalUnits`, whose components
`AlgebraicGeometry.baseChangePointsIsoGlobalUnits_hom_app` are pullback of the universal Laurent
coordinate; the comparison is therefore a `MulEquiv` for the multiplication of units, and cannot
be twisted by inversion.

The Laurent polynomial ring is of finite type over the integers, so the multiplicative group
scheme lies in every big fppf site, by **Stacks 000R**; so does its base change, being a fibre
product of two objects of the site.

## References

* [Stacks Project, Tag 043J](https://stacks.math.columbia.edu/tag/043J)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Space

variable (𝒞 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝒞.Contains S)

/-- The multiplicative group over the integers belongs to every big fppf site. -/
theorem contains_multiplicativeGroupULift :
    𝒞.Contains (multiplicativeGroupULift : Scheme.{u}) :=
  Scheme.size_Spec_lt_of_finiteType 𝒞.aleph0_lt_cutoff 𝒞.cutoff_isStrongPrelimit
    (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) (contains_specULiftZ 𝒞)

/-- The multiplicative group scheme over `S` belongs to the big fppf site of `S`. -/
theorem contains_multiplicativeGroupBaseChange (hS : 𝒞.Contains S) :
    𝒞.Contains (multiplicativeGroupBaseChange S) :=
  Scheme.size_pullback_lt _ _ (contains_multiplicativeGroupULift 𝒞) hS

/-- **Stacks Project, Tag 043J.** The multiplicative group scheme over `S`, read as an object of
the big fppf site over `S`. -/
@[stacks 043J "the multiplicative group scheme as an object of the site"]
noncomputable def multiplicativeGroupSiteObject : BigFppfOver 𝒞 S hS :=
  Over.mk (ObjectProperty.homMk (Scheme.asOver (multiplicativeGroupBaseChange S) S).hom
    (X := 𝒞.obj (contains_multiplicativeGroupBaseChange 𝒞 S hS)) (Y := 𝒞.obj hS))

/-- The group-scheme structure of `Gₘ,S` of **Stacks 022U**, read on the object of the site. -/
@[instance_reducible]
noncomputable def multiplicativeGroupSiteObjectGrpObj :
    GrpObj ((toSchemeOver 𝒞 S hS).obj (multiplicativeGroupSiteObject 𝒞 S hS)) :=
  multiplicativeGroupBaseChangeGrpObj S

/-- The restriction to the big fppf site over `S` of the functor of points of `Gₘ,S`. -/
noncomputable abbrev multiplicativeGroupPointsOnSite :
    (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ GrpCat.{u} :=
  pointsOnSite 𝒞 S hS (multiplicativeGroupSiteObject 𝒞 S hS)
    (multiplicativeGroupSiteObjectGrpObj 𝒞 S hS)

/-- **Stacks Project, Tag 043J.** The multiplicative group algebraic space
`Gₘ,B = B ×_S Gₘ,S` over an algebraic space `B` over `S`. -/
@[stacks 043J]
noncomputable def multiplicativeGroupSpace (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    (hB : IsAlgebraicSpace 𝒞 S hS B) : GroupAlgebraicSpace 𝒞 S hS B hB :=
  GroupAlgebraicSpace.ofGroupSchemeInSite 𝒞 S hS B hB (multiplicativeGroupSiteObject 𝒞 S hS)
    (multiplicativeGroupSiteObjectGrpObj 𝒞 S hS)

/-- **Stacks Project, Tag 043J.** The algebraic space underlying the multiplicative group
algebraic space is the fibre product `B ×_S Gₘ,S`. -/
@[stacks 043J "the underlying base change"]
theorem multiplicativeGroupSpace_obj_X (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    (hB : IsAlgebraicSpace 𝒞 S hS B) :
    (multiplicativeGroupSpace 𝒞 S hS B hB).obj.X =
      (Over.mk (prod.fst :
        B ⨯ (multiplicativeGroupPointsOnSite 𝒞 S hS ⋙ forget GrpCat) ⟶ B) : Over B) :=
  rfl

/-- **Stacks Project, Tag 043J.** The group of points of the multiplicative group algebraic
space over a scheme `T` over `B` is the group of units in the global sections of `T`. -/
@[stacks 043J "the functor of global units"]
noncomputable def multiplicativeGroupSpacePoints (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    (T : BigFppfOver 𝒞 S hS) (b : yoneda.obj T ⟶ B) :
    ((Over.mk b : Over B) ⟶
        Over.mk (prod.fst :
          B ⨯ (multiplicativeGroupPointsOnSite 𝒞 S hS ⋙ forget GrpCat) ⟶ B)) ≃*
      (globalUnits S).obj (Opposite.op ((toSchemeOver 𝒞 S hS).obj T)) :=
  GroupAlgebraicSpace.groupSchemePointsMulEquiv 𝒞 S hS B (multiplicativeGroupSiteObject 𝒞 S hS)
    (multiplicativeGroupSiteObjectGrpObj 𝒞 S hS) (globalUnits S)
    (baseChangePointsIsoGlobalUnits S) T b

/-- `AlgebraicGeometry.Space.multiplicativeGroupSpacePoints` reads a point through the second
projection of the fibre product and the canonical identification of **Stacks 022U**. -/
@[stacks 043J "the functor of global units"]
theorem multiplicativeGroupSpacePoints_apply (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    (T : BigFppfOver 𝒞 S hS) (b : yoneda.obj T ⟶ B)
    (x : (Over.mk b : Over B) ⟶
      Over.mk (prod.fst : B ⨯ (multiplicativeGroupPointsOnSite 𝒞 S hS ⋙ forget GrpCat) ⟶ B)) :
    multiplicativeGroupSpacePoints 𝒞 S hS B T b x =
      (baseChangePointsIsoGlobalUnits S).hom.app
        (Opposite.op ((toSchemeOver 𝒞 S hS).obj T))
        (yonedaEquiv (x.left ≫ (prod.snd :
          B ⨯ (multiplicativeGroupPointsOnSite 𝒞 S hS ⋙ forget GrpCat) ⟶ _))) :=
  GroupAlgebraicSpace.groupSchemePointsMulEquiv_apply 𝒞 S hS B _ _ _ _ T b x

/-- `AlgebraicGeometry.Space.multiplicativeGroupSpacePoints` is natural in the scheme over `B`,
so what is asserted is representability of the functor of global units and not a family of
unrelated group isomorphisms. -/
@[stacks 043J "the functor of global units"]
theorem multiplicativeGroupSpacePoints_naturality (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    (T U : BigFppfOver 𝒞 S hS) (f : T ⟶ U) (b : yoneda.obj U ⟶ B)
    (x : (Over.mk b : Over B) ⟶
      Over.mk (prod.fst : B ⨯ (multiplicativeGroupPointsOnSite 𝒞 S hS ⋙ forget GrpCat) ⟶ B)) :
    multiplicativeGroupSpacePoints 𝒞 S hS B T (yoneda.map f ≫ b)
        ((Over.homMk (yoneda.map f) :
          (Over.mk (yoneda.map f ≫ b) : Over B) ⟶ Over.mk b) ≫ x) =
      (globalUnits S ⋙ forget GrpCat).map ((toSchemeOver 𝒞 S hS).map f).op
        (multiplicativeGroupSpacePoints 𝒞 S hS B U b x) :=
  GroupAlgebraicSpace.groupSchemePointsMulEquiv_naturality 𝒞 S hS B _ _ _ _ T U f b x

end AlgebraicGeometry.Space

end
