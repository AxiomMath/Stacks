module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.Examples.GeneralLinear
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.UnitFixingGroupScheme

/-!
# The unit-fixing subgroup of `GL_d` as a group algebraic space over a general base

The group `G ⊆ GL_d` named in Stacks 05YQ is a group scheme over the integers
(`AlgebraicGeometry.FiniteFreeAlgebra.unitFixingGrpObj`). This file carries it to a general
base: its base change `G_S` is a group scheme over an arbitrary scheme `S`, it lies in the big
fppf site of `S`, and over an arbitrary algebraic space `B` over `S` it gives the group
algebraic space `G_B = B ×_S G_S` in the form `AlgebraicGeometry.Stack.quotientStackOfAction`
consumes, namely a group object of the slice of presheaves on the big fppf site over `B` whose
underlying presheaf is an algebraic space.

## Main definitions

* `AlgebraicGeometry.FiniteFreeAlgebra.unitFixingBaseChange`: the group scheme `G_S` over `S`,
  with `AlgebraicGeometry.FiniteFreeAlgebra.unitFixingBaseChangeGrpObj` its group structure.
* `AlgebraicGeometry.Space.unitFixingSiteObject`: `G_S` read as an object of the big fppf site
  over `S`, with `AlgebraicGeometry.Space.unitFixingSiteObjectGrpObj` its group structure.
* `AlgebraicGeometry.Space.unitFixingSpace`: the group algebraic space `G_B` over `B`.

## Main results

* `AlgebraicGeometry.FiniteFreeAlgebra.unitFixingBaseChangeGroupPointsIso`: the group-valued
  functor of points of `G_S` is the functor of unit-fixing invertible matrices over global
  sections, naturally in the `S`-scheme.
* `AlgebraicGeometry.Space.contains_unitFixingScheme` and
  `AlgebraicGeometry.Space.contains_unitFixingBaseChange`: `G` and `G_S` lie in the big fppf
  site.
* `AlgebraicGeometry.Space.unitFixingSpace_obj_X`,
  `AlgebraicGeometry.Space.unitFixingSpacePoints`,
  `AlgebraicGeometry.Space.unitFixingSpacePoints_apply` and
  `AlgebraicGeometry.Space.unitFixingSpacePoints_naturality` identify the underlying algebraic
  space and the group of points of `G_B`.

## Implementation notes

Nothing is rebuilt: the base change of the group structure is
`CategoryTheory.Over.grpObjMkPullbackSnd`, the comparison of points of a pullback group object
with points of the original is `CategoryTheory.Over.pullbackPointsMulEquiv`, and the passage to
a group algebraic space over `B` is
`AlgebraicGeometry.Space.GroupAlgebraicSpace.ofGroupSchemeInSite`, that is **Stacks 043I**. This
is the same chain as for `GL_n` in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/GroupSpaces/Examples/GeneralLinear.lean` and for
`μₙ` in `StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/GroupSpaces/Examples/RootsOfUnity.lean`.

The unit-fixing coordinate ring is a quotient of the coordinate ring of `GL_d`, hence of
cardinality at most that of the latter, so membership in the site follows from membership of
`GL_d` by **Stacks 000R (9)**.

## References

* [Stacks Project, Tag 043I](https://stacks.math.columbia.edu/tag/043I)
* [Stacks Project, Tag 05YP](https://stacks.math.columbia.edu/tag/05YP)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.FiniteFreeAlgebra

variable (d : ℕ) [NeZero d]

/-- The unit-fixing subgroup scheme `G_S` of `GL_{d,S}` over a scheme `S`, obtained by base
change from the integers. -/
noncomputable abbrev unitFixingBaseChange (S : Scheme.{u}) : Over S :=
  (Over.pullback (specULiftZIsTerminal.from S)).obj (unitFixingOver.{u} d)

/-- **Part of Stacks Project, Tag 05YQ.** The base change of the unit-fixing subgroup scheme
to a scheme `S` is a group scheme over `S`. -/
noncomputable instance unitFixingBaseChangeGrpObj (S : Scheme.{u}) :
    GrpObj (unitFixingBaseChange.{u} d S) :=
  Over.grpObjMkPullbackSnd
    (f := specULiftZIsTerminal.from (unitFixingScheme.{u} d))
    (g := specULiftZIsTerminal.from S)

/-- The group-valued functor of unit-fixing invertible matrices in global sections, on schemes
over `S`. -/
noncomputable abbrev unitFixingGroupOverSchemeFunctor (S : Scheme.{u}) :
    (Over S)ᵒᵖ ⥤ GrpCat.{u} :=
  (Over.forget S).op ⋙ unitFixingGroupFunctor.{u} d

/-- The group-valued points of `G_S` over a scheme over `S` are the points of `G` over that
scheme regarded over the integers. -/
noncomputable def unitFixingPullbackYonedaGrpIso (S : Scheme.{u}) :
    yonedaGrpObj (unitFixingBaseChange.{u} d S) ≅
      (Over.map (specULiftZIsTerminal.from S)).op ⋙ yonedaGrpObj (unitFixingOver.{u} d) := by
  refine NatIso.ofComponents (fun T =>
      (CategoryTheory.Over.pullbackPointsMulEquiv (T := T.unop)
        (b := specULiftZIsTerminal.from S)
        (h := specULiftZIsTerminal.from (unitFixingScheme.{u} d))).toGrpIso) ?_
  intro X Y f
  ext g
  exact Over.OverMorphism.ext rfl

/-- **Part of Stacks Project, Tag 05YQ.** For every scheme `S`, the group-valued functor of
points of `G_S` is naturally isomorphic to the group of unit-fixing invertible matrices in the
global sections of the varying `S`-scheme. -/
noncomputable def unitFixingBaseChangeGroupPointsIso (S : Scheme.{u}) :
    yonedaGrpObj (unitFixingBaseChange.{u} d S) ≅
      unitFixingGroupOverSchemeFunctor.{u} d S :=
  unitFixingPullbackYonedaGrpIso d S ≪≫ Functor.isoWhiskerLeft
    (Over.map (specULiftZIsTerminal.from S)).op
    (yonedaGrpObjIsoOfRepresentableBy (unitFixingOver.{u} d)
      (unitFixingGroupOverFunctor.{u} d) (unitFixingRepresentableBy d))

end AlgebraicGeometry.FiniteFreeAlgebra

namespace AlgebraicGeometry.Space

open AlgebraicGeometry.FiniteFreeAlgebra

variable (𝒞 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝒞.Contains S) (d : ℕ) [NeZero d]

/-- The unit-fixing subgroup scheme of `GL_d` over the integers belongs to every big fppf site:
its coordinate ring is a quotient of the coordinate ring of `GL_d`. -/
theorem contains_unitFixingScheme : 𝒞.Contains (unitFixingScheme.{u} d) := by
  change (Spec (CommRingCat.of (unitFixingCoordinateRing.{u} d))).size < 𝒞.cutoff
  refine Scheme.size_Spec_lt_of_mk_le_max 𝒞.aleph0_lt_cutoff 𝒞.cutoff_isStrongPrelimit
    (R := generalLinearCoordinateRing.{u} d) (contains_generalLinearScheme 𝒞 d) ?_
  exact (Cardinal.mk_le_of_surjective Ideal.Quotient.mk_surjective).trans (le_max_right _ _)

/-- The unit-fixing subgroup scheme `G_S` over `S` belongs to the big fppf site of `S`. -/
theorem contains_unitFixingBaseChange (hS : 𝒞.Contains S) :
    𝒞.Contains (unitFixingBaseChange.{u} d S).left :=
  Scheme.size_pullback_lt _ _ (contains_unitFixingScheme 𝒞 d) hS

/-- The unit-fixing subgroup scheme `G_S` over `S`, read as an object of the big fppf site over
`S`. -/
noncomputable def unitFixingSiteObject : BigFppfOver 𝒞 S hS :=
  Over.mk (ObjectProperty.homMk (unitFixingBaseChange.{u} d S).hom
    (X := 𝒞.obj (contains_unitFixingBaseChange 𝒞 S d hS)) (Y := 𝒞.obj hS))

/-- The group-scheme structure of `G_S` of **Stacks 05YN**, read on the object of the site. -/
@[instance_reducible]
noncomputable def unitFixingSiteObjectGrpObj :
    GrpObj ((toSchemeOver 𝒞 S hS).obj (unitFixingSiteObject 𝒞 S hS d)) :=
  unitFixingBaseChangeGrpObj d S

/-- The restriction to the big fppf site over `S` of the functor of points of `G_S`. -/
noncomputable abbrev unitFixingPointsOnSite :
    (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ GrpCat.{u} :=
  pointsOnSite 𝒞 S hS (unitFixingSiteObject 𝒞 S hS d)
    (unitFixingSiteObjectGrpObj 𝒞 S hS d)

/-- **Stacks Project, Tag 043I** for the unit-fixing subgroup of `GL_d`. The group algebraic
space `G_B = B ×_S G_S` over an algebraic space `B` over `S`. This is the group `G` of
**Stacks 05YN** in the form the quotient stack `[X/G]` of **Stacks 044Q** consumes. -/
noncomputable def unitFixingSpace (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    (hB : IsAlgebraicSpace 𝒞 S hS B) : GroupAlgebraicSpace 𝒞 S hS B hB :=
  GroupAlgebraicSpace.ofGroupSchemeInSite 𝒞 S hS B hB (unitFixingSiteObject 𝒞 S hS d)
    (unitFixingSiteObjectGrpObj 𝒞 S hS d)

/-- The algebraic space underlying the unit-fixing group algebraic space is the fibre product
`B ×_S G_S`. -/
theorem unitFixingSpace_obj_X (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    (hB : IsAlgebraicSpace 𝒞 S hS B) :
    (unitFixingSpace 𝒞 S hS d B hB).obj.X =
      (Over.mk (prod.fst :
        B ⨯ (unitFixingPointsOnSite 𝒞 S hS d ⋙ forget GrpCat) ⟶ B) : Over B) :=
  rfl

/-- The group of points of the unit-fixing group algebraic space over a scheme `T` over `B` is
the group of unit-fixing invertible matrices over the global sections of `T`. -/
noncomputable def unitFixingSpacePoints (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    (T : BigFppfOver 𝒞 S hS) (b : yoneda.obj T ⟶ B) :
    ((Over.mk b : Over B) ⟶
        Over.mk (prod.fst :
          B ⨯ (unitFixingPointsOnSite 𝒞 S hS d ⋙ forget GrpCat) ⟶ B)) ≃*
      (unitFixingGroupOverSchemeFunctor.{u} d S).obj
        (Opposite.op ((toSchemeOver 𝒞 S hS).obj T)) :=
  GroupAlgebraicSpace.groupSchemePointsMulEquiv 𝒞 S hS B (unitFixingSiteObject 𝒞 S hS d)
    (unitFixingSiteObjectGrpObj 𝒞 S hS d) (unitFixingGroupOverSchemeFunctor.{u} d S)
    (unitFixingBaseChangeGroupPointsIso d S) T b

/-- `AlgebraicGeometry.Space.unitFixingSpacePoints` reads a point through the second projection
of the fibre product and the canonical identification of **Stacks 05YN**. -/
theorem unitFixingSpacePoints_apply (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    (T : BigFppfOver 𝒞 S hS) (b : yoneda.obj T ⟶ B)
    (x : (Over.mk b : Over B) ⟶
      Over.mk (prod.fst : B ⨯ (unitFixingPointsOnSite 𝒞 S hS d ⋙ forget GrpCat) ⟶ B)) :
    unitFixingSpacePoints 𝒞 S hS d B T b x =
      (unitFixingBaseChangeGroupPointsIso d S).hom.app
        (Opposite.op ((toSchemeOver 𝒞 S hS).obj T))
        (yonedaEquiv (x.left ≫ (prod.snd :
          B ⨯ (unitFixingPointsOnSite 𝒞 S hS d ⋙ forget GrpCat) ⟶ _))) :=
  GroupAlgebraicSpace.groupSchemePointsMulEquiv_apply 𝒞 S hS B _ _ _ _ T b x

/-- `AlgebraicGeometry.Space.unitFixingSpacePoints` is natural in the scheme over `B`, so what
is asserted is representability of the functor of unit-fixing matrices and not a family of
unrelated group isomorphisms. -/
theorem unitFixingSpacePoints_naturality (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    (T U : BigFppfOver 𝒞 S hS) (f : T ⟶ U) (b : yoneda.obj U ⟶ B)
    (x : (Over.mk b : Over B) ⟶
      Over.mk (prod.fst : B ⨯ (unitFixingPointsOnSite 𝒞 S hS d ⋙ forget GrpCat) ⟶ B)) :
    unitFixingSpacePoints 𝒞 S hS d B T (yoneda.map f ≫ b)
        ((Over.homMk (yoneda.map f) :
          (Over.mk (yoneda.map f ≫ b) : Over B) ⟶ Over.mk b) ≫ x) =
      (unitFixingGroupOverSchemeFunctor.{u} d S ⋙ forget GrpCat).map
        ((toSchemeOver 𝒞 S hS).map f).op
        (unitFixingSpacePoints 𝒞 S hS d B U b x) :=
  GroupAlgebraicSpace.groupSchemePointsMulEquiv_naturality 𝒞 S hS B _ _ _ _ T U f b x

end AlgebraicGeometry.Space

end
