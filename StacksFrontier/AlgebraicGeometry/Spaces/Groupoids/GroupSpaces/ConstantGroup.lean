module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.Constant
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.BaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Constant group algebraic spaces

Let `B` be an algebraic space over a scheme `S` and let `G` be an abstract group.  The functor
sending a scheme `T` over `B` to the group of locally constant maps `T → G`, for the Zariski
topology on `T` and the discrete topology on `G`, is represented by the group algebraic space
`G_B = B ×_S G_S` over `B`, the base change to `B` of the constant group scheme over `S`.

## Main definitions

* `AlgebraicGeometry.Space.constantGroupSiteObject` is the constant group scheme `G_S`, read as
  an object of the big fppf site over `S`.
* `AlgebraicGeometry.Space.constantGroupSpace`: **Stacks 043O**, the constant group algebraic
  space `G_B = B ×_S G_S` over `B`.
* `AlgebraicGeometry.Space.constantGroupSpacePoints`: **Stacks 043O**, its group of points over
  a scheme over `B`, identified with the group of locally constant `G`-valued maps.

## Main results

* `AlgebraicGeometry.Space.constantGroupSpace_obj_X` identifies the underlying algebraic space
  with the fibre product of `B` and the functor of points of `G_S`.
* `AlgebraicGeometry.Space.constantGroupSpacePoints_apply` and
  `AlgebraicGeometry.Space.constantGroupSpacePoints_naturality` pin the identification on points
  down to the second projection of that fibre product followed by the canonical isomorphism of
  **Stacks 03YW**, naturally in the test scheme; so what is asserted is representability of the
  functor of locally constant maps, and the identification cannot be twisted by an automorphism
  of `G`.

## Implementation notes

The base `B` is an arbitrary algebraic space over `S`, as in **Stacks 043A**; it is not assumed
to be a scheme.  The group algebraic space is the base change of `G_S` along the structure
morphism of `B`, which is **Stacks 043I**,
`AlgebraicGeometry.Space.GroupAlgebraicSpace.ofGroupSchemeInSite`; the group law on its points
is therefore the one prescribed by **Stacks 03YW**, through
`AlgebraicGeometry.constantGroupSchemePointsIsoLocallyConstantMaps`, under which multiplication
is pointwise multiplication of functions.

The indexing group `G` lives in its own universe `v` and is only required to be small relative
to the universe of schemes, which is exactly what makes the coproduct of copies of `Spec ℤ`
indexed by `G` a scheme; the comparison on points is therefore stated after the universe-lifting
functor on groups, which is bookkeeping only, as the other side consists literally of locally
constant `G`-valued maps.

The hypothesis that the chosen big fppf site contains `G_S` is a genuine size condition rather
than an artefact: a single big site has a size cutoff, while `G` is an arbitrary abstract group,
so no site contains the constant group scheme of every group.

## References

* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 03YW](https://stacks.math.columbia.edu/tag/03YW)
* [Stacks Project, Tag 043H](https://stacks.math.columbia.edu/tag/043H)
* [Stacks Project, Tag 043I](https://stacks.math.columbia.edu/tag/043I)
* [Stacks Project, Tag 043O](https://stacks.math.columbia.edu/tag/043O)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

universe v u

namespace AlgebraicGeometry.Space

variable (𝒞 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝒞.Contains S)
  (G : Type v) [Small.{u} G] [Group G]

/-- **Stacks Project, Tag 043O.** The constant group scheme `G_S` of **Stacks 03YW**, read as an
object of the big fppf site over `S`.  That it belongs to the site is a size hypothesis on the
site: `G` is an arbitrary abstract group, so no single big site can contain `G_S` for all `G`. -/
@[stacks 043O "the constant group scheme as an object of the site"]
noncomputable def constantGroupSiteObject
    (hG : 𝒞.Contains (constantGroupScheme G S).X.left) : BigFppfOver 𝒞 S hS :=
  Over.mk (ObjectProperty.homMk (constantGroupScheme G S).X.hom
    (X := 𝒞.obj hG) (Y := 𝒞.obj hS))

/-- The group-scheme structure of `G_S` of **Stacks 03YW**, read on the object of the site. -/
@[instance_reducible]
noncomputable def constantGroupSiteObjectGrpObj
    (hG : 𝒞.Contains (constantGroupScheme G S).X.left) :
    GrpObj ((toSchemeOver 𝒞 S hS).obj (constantGroupSiteObject 𝒞 S hS G hG)) :=
  (constantGroupScheme G S).grp

/-- The restriction to the big fppf site over `S` of the functor of points of `G_S`. -/
noncomputable abbrev constantGroupPointsOnSite
    (hG : 𝒞.Contains (constantGroupScheme G S).X.left) :
    (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ GrpCat.{u} :=
  pointsOnSite 𝒞 S hS (constantGroupSiteObject 𝒞 S hS G hG)
    (constantGroupSiteObjectGrpObj 𝒞 S hS G hG)

/-- **Stacks Project, Tag 043O.** The constant group algebraic space `G_B = B ×_S G_S` over an
algebraic space `B` over `S`, for an abstract group `G`. -/
@[stacks 043O]
noncomputable def constantGroupSpace (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    (hB : IsAlgebraicSpace 𝒞 S hS B)
    (hG : 𝒞.Contains (constantGroupScheme G S).X.left) :
    GroupAlgebraicSpace 𝒞 S hS B hB :=
  GroupAlgebraicSpace.ofGroupSchemeInSite 𝒞 S hS B hB (constantGroupSiteObject 𝒞 S hS G hG)
    (constantGroupSiteObjectGrpObj 𝒞 S hS G hG)

/-- **Stacks Project, Tag 043O.** The algebraic space underlying the constant group algebraic
space is the fibre product `B ×_S G_S`. -/
@[stacks 043O "the underlying base change"]
theorem constantGroupSpace_obj_X (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    (hB : IsAlgebraicSpace 𝒞 S hS B)
    (hG : 𝒞.Contains (constantGroupScheme G S).X.left) :
    (constantGroupSpace 𝒞 S hS G B hB hG).obj.X =
      (Over.mk (prod.fst :
        B ⨯ (constantGroupPointsOnSite 𝒞 S hS G hG ⋙ forget GrpCat) ⟶ B) : Over B) :=
  rfl

/-- **Stacks Project, Tag 043O.** The group of points of the constant group algebraic space over
a scheme `T` over `B` is the group of locally constant `G`-valued maps on `T`. -/
@[stacks 043O "the functor of locally constant maps", sga "3 I 4.1" "Hom = loc const maps"]
noncomputable def constantGroupSpacePoints (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    (hG : 𝒞.Contains (constantGroupScheme G S).X.left) (T : BigFppfOver 𝒞 S hS)
    (b : yoneda.obj T ⟶ B) :
    ((Over.mk b : Over B) ⟶
        Over.mk (prod.fst :
          B ⨯ (constantGroupPointsOnSite 𝒞 S hS G hG ⋙ forget GrpCat) ⟶ B)) ≃*
      (locallyConstantMapsOver G S).obj (Opposite.op ((toSchemeOver 𝒞 S hS).obj T)) :=
  (GroupAlgebraicSpace.pointsMulEquiv 𝒞 S hS B
      (constantGroupPointsOnSite 𝒞 S hS G hG) T b).trans
    (MulEquiv.ulift.symm.trans
      ((constantGroupSchemePointsIsoLocallyConstantMaps G S).app
        (Opposite.op ((toSchemeOver 𝒞 S hS).obj T))).groupIsoToMulEquiv)

/-- `AlgebraicGeometry.Space.constantGroupSpacePoints` reads a point through the second
projection of the fibre product and the canonical identification of **Stacks 03YW**. -/
@[stacks 043O "the functor of locally constant maps"]
theorem constantGroupSpacePoints_apply (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    (hG : 𝒞.Contains (constantGroupScheme G S).X.left) (T : BigFppfOver 𝒞 S hS)
    (b : yoneda.obj T ⟶ B)
    (x : (Over.mk b : Over B) ⟶
      Over.mk (prod.fst :
        B ⨯ (constantGroupPointsOnSite 𝒞 S hS G hG ⋙ forget GrpCat) ⟶ B)) :
    constantGroupSpacePoints 𝒞 S hS G B hG T b x =
      (constantGroupSchemePointsIsoLocallyConstantMaps G S).hom.app
        (Opposite.op ((toSchemeOver 𝒞 S hS).obj T))
        (ULift.up (yonedaEquiv (x.left ≫ (prod.snd :
          B ⨯ (constantGroupPointsOnSite 𝒞 S hS G hG ⋙ forget GrpCat) ⟶ _)))) :=
  rfl

/-- `AlgebraicGeometry.Space.constantGroupSpacePoints` is natural in the scheme over `B`, so
what is asserted is representability of the functor of locally constant maps and not a family of
unrelated group isomorphisms. -/
@[stacks 043O "the functor of locally constant maps"]
theorem constantGroupSpacePoints_naturality (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    (hG : 𝒞.Contains (constantGroupScheme G S).X.left) (T U : BigFppfOver 𝒞 S hS) (f : T ⟶ U)
    (b : yoneda.obj U ⟶ B)
    (x : (Over.mk b : Over B) ⟶
      Over.mk (prod.fst :
        B ⨯ (constantGroupPointsOnSite 𝒞 S hS G hG ⋙ forget GrpCat) ⟶ B)) :
    constantGroupSpacePoints 𝒞 S hS G B hG T (yoneda.map f ≫ b)
        ((Over.homMk (yoneda.map f) :
          (Over.mk (yoneda.map f ≫ b) : Over B) ⟶ Over.mk b) ≫ x) =
      (locallyConstantMapsOver G S ⋙ forget GrpCat).map ((toSchemeOver 𝒞 S hS).map f).op
        (constantGroupSpacePoints 𝒞 S hS G B hG U b x) := by
  rw [constantGroupSpacePoints_apply, constantGroupSpacePoints_apply,
    ← GroupAlgebraicSpace.pointsMulEquiv_apply 𝒞 S hS B
      (constantGroupPointsOnSite 𝒞 S hS G hG),
    ← GroupAlgebraicSpace.pointsMulEquiv_apply 𝒞 S hS B
      (constantGroupPointsOnSite 𝒞 S hS G hG),
    GroupAlgebraicSpace.pointsMulEquiv_naturality]
  exact ConcreteCategory.congr_hom
    ((constantGroupSchemePointsIsoLocallyConstantMaps G S).hom.naturality
      ((toSchemeOver 𝒞 S hS).map f).op) _

end AlgebraicGeometry.Space

end
