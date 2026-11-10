module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.GeneralLinear
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.BaseChange

/-!
# The general linear group algebraic space

Let `B` be an algebraic space over a scheme `S` and let `n` be a natural number.  The functor
sending a scheme `T` over `B` to the group `GLₙ(Γ(T, 𝒪_T))` of invertible `n × n` matrices over
the global sections of its structure sheaf is represented by the group algebraic space
`GLₙ,B = B ×_S GLₙ,S`, the base change to `B` of the general linear group scheme over `S`.

## Main definitions

* `AlgebraicGeometry.Space.generalLinearSiteObject` is the general linear group scheme over `S`,
  read as an object of the big fppf site over `S`.
* `AlgebraicGeometry.Space.generalLinearSpace`: the general linear group algebraic space over
  `B`.
* `AlgebraicGeometry.Space.generalLinearSpacePoints`: its group of points over a scheme over `B`,
  identified with the group of invertible matrices over global sections.

## Main results

* `AlgebraicGeometry.Space.generalLinearSpace_obj_X` identifies the underlying algebraic space
  with the fibre product of `B` and the functor of points of `GLₙ,S`.
* `AlgebraicGeometry.Space.generalLinearSpacePoints_apply` and
  `AlgebraicGeometry.Space.generalLinearSpacePoints_naturality` pin the identification on points
  down, naturally in the test scheme.

## Implementation notes

The base `B` is an arbitrary algebraic space over `S`; it is not assumed to be a scheme.  The
group law on points is the one of **Stacks 022W**, through the natural isomorphism
`AlgebraicGeometry.baseChangeGroupPointsIso`, whose components are specified entrywise by
`AlgebraicGeometry.baseChangeGroupPointsIso_hom_app` as pullback of the generic matrix
coordinates.

The Stacks project states this example for `n ≥ 1`.  It is stated here for every natural number
`n`, since **Stacks 022W** constructs `GLₙ,S` for all `n`, the case `n = 0` giving the trivial
group scheme.

## References

* [Stacks Project, Tag 043M](https://stacks.math.columbia.edu/tag/043M)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Space

variable (𝒞 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝒞.Contains S) (n : ℕ)

/-- The general linear group scheme over the integers belongs to every big fppf site. -/
theorem contains_generalLinearScheme :
    𝒞.Contains (generalLinearScheme.{u} n) := by
  have hpoly :
      (Spec (.of (MvPolynomial (Fin n × Fin n) (ULift.{u} ℤ)))).size < 𝒞.cutoff :=
    Scheme.size_Spec_lt_of_finiteType 𝒞.aleph0_lt_cutoff 𝒞.cutoff_isStrongPrelimit
      (ULift.{u} ℤ) (MvPolynomial (Fin n × Fin n) (ULift.{u} ℤ)) (contains_specULiftZ 𝒞)
  change (Spec (.of (generalLinearCoordinateRing.{u} n))).size < 𝒞.cutoff
  exact Scheme.size_Spec_lt_of_isLocalization 𝒞.aleph0_lt_cutoff 𝒞.cutoff_isStrongPrelimit
    (Submonoid.powers (generalLinearDeterminant.{u} n))
    (generalLinearCoordinateRing.{u} n) hpoly

/-- The general linear group scheme over `S` belongs to the big fppf site of `S`. -/
theorem contains_generalLinearBaseChange (hS : 𝒞.Contains S) :
    𝒞.Contains (generalLinearBaseChange n S).left :=
  Scheme.size_pullback_lt _ _ (contains_generalLinearScheme 𝒞 n) hS

/-- The general linear group scheme over `S`, read as an object of the big fppf site over `S`. -/
@[stacks 043M "the general linear group scheme as an object of the site"]
noncomputable def generalLinearSiteObject : BigFppfOver 𝒞 S hS :=
  Over.mk (ObjectProperty.homMk (generalLinearBaseChange n S).hom
    (X := 𝒞.obj (contains_generalLinearBaseChange 𝒞 S n hS)) (Y := 𝒞.obj hS))

/-- The group-scheme structure of `GLₙ,S` of **Stacks 022W**, read on the object of the site. -/
@[instance_reducible]
noncomputable def generalLinearSiteObjectGrpObj :
    GrpObj ((toSchemeOver 𝒞 S hS).obj (generalLinearSiteObject 𝒞 S hS n)) :=
  generalLinearBaseChangeGrpObj n S

/-- The restriction to the big fppf site over `S` of the functor of points of `GLₙ,S`. -/
noncomputable abbrev generalLinearPointsOnSite :
    (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ GrpCat.{u} :=
  pointsOnSite 𝒞 S hS (generalLinearSiteObject 𝒞 S hS n)
    (generalLinearSiteObjectGrpObj 𝒞 S hS n)

/-- The general linear group algebraic space `GLₙ,B = B ×_S GLₙ,S` over an algebraic space `B`
over `S`. -/
@[stacks 043M]
noncomputable def generalLinearSpace (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    (hB : IsAlgebraicSpace 𝒞 S hS B) : GroupAlgebraicSpace 𝒞 S hS B hB :=
  GroupAlgebraicSpace.ofGroupSchemeInSite 𝒞 S hS B hB (generalLinearSiteObject 𝒞 S hS n)
    (generalLinearSiteObjectGrpObj 𝒞 S hS n)

/-- The algebraic space underlying the general linear group algebraic space is the fibre product
`B ×_S GLₙ,S`. -/
@[stacks 043M "the underlying base change"]
theorem generalLinearSpace_obj_X (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    (hB : IsAlgebraicSpace 𝒞 S hS B) :
    (generalLinearSpace 𝒞 S hS n B hB).obj.X =
      (Over.mk (prod.fst :
        B ⨯ (generalLinearPointsOnSite 𝒞 S hS n ⋙ forget GrpCat) ⟶ B) : Over B) :=
  rfl

/-- The group of points of the general linear group algebraic space over a scheme `T` over `B` is
the group of invertible `n × n` matrices over the global sections of `T`. -/
@[stacks 043M "the functor of invertible matrices"]
noncomputable def generalLinearSpacePoints (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    (T : BigFppfOver 𝒞 S hS) (b : yoneda.obj T ⟶ B) :
    ((Over.mk b : Over B) ⟶
        Over.mk (prod.fst :
          B ⨯ (generalLinearPointsOnSite 𝒞 S hS n ⋙ forget GrpCat) ⟶ B)) ≃*
      (generalLinearGroupOverFunctor n S).obj
        (Opposite.op ((toSchemeOver 𝒞 S hS).obj T)) :=
  GroupAlgebraicSpace.groupSchemePointsMulEquiv 𝒞 S hS B (generalLinearSiteObject 𝒞 S hS n)
    (generalLinearSiteObjectGrpObj 𝒞 S hS n) (generalLinearGroupOverFunctor n S)
    (baseChangeGroupPointsIso n S) T b

/-- `AlgebraicGeometry.Space.generalLinearSpacePoints` sends a point to the image of its second
projection to `GLₙ,S` under the canonical identification of **Stacks 022W**. -/
@[stacks 043M "the functor of invertible matrices"]
theorem generalLinearSpacePoints_apply (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    (T : BigFppfOver 𝒞 S hS) (b : yoneda.obj T ⟶ B)
    (x : (Over.mk b : Over B) ⟶
      Over.mk (prod.fst : B ⨯ (generalLinearPointsOnSite 𝒞 S hS n ⋙ forget GrpCat) ⟶ B)) :
    generalLinearSpacePoints 𝒞 S hS n B T b x =
      (baseChangeGroupPointsIso n S).hom.app
        (Opposite.op ((toSchemeOver 𝒞 S hS).obj T))
        (yonedaEquiv (x.left ≫ (prod.snd :
          B ⨯ (generalLinearPointsOnSite 𝒞 S hS n ⋙ forget GrpCat) ⟶ _))) :=
  GroupAlgebraicSpace.groupSchemePointsMulEquiv_apply 𝒞 S hS B _ _ _ _ T b x

/-- `AlgebraicGeometry.Space.generalLinearSpacePoints` is natural in the scheme over `B`. -/
@[stacks 043M "the functor of invertible matrices"]
theorem generalLinearSpacePoints_naturality (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    (T U : BigFppfOver 𝒞 S hS) (f : T ⟶ U) (b : yoneda.obj U ⟶ B)
    (x : (Over.mk b : Over B) ⟶
      Over.mk (prod.fst : B ⨯ (generalLinearPointsOnSite 𝒞 S hS n ⋙ forget GrpCat) ⟶ B)) :
    generalLinearSpacePoints 𝒞 S hS n B T (yoneda.map f ≫ b)
        ((Over.homMk (yoneda.map f) :
          (Over.mk (yoneda.map f ≫ b) : Over B) ⟶ Over.mk b) ≫ x) =
      (generalLinearGroupOverFunctor n S ⋙ forget GrpCat).map
        ((toSchemeOver 𝒞 S hS).map f).op
        (generalLinearSpacePoints 𝒞 S hS n B U b x) :=
  GroupAlgebraicSpace.groupSchemePointsMulEquiv_naturality 𝒞 S hS B _ _ _ _ T U f b x

end AlgebraicGeometry.Space

end
