module

public import Mathlib.Algebra.Polynomial.Cardinal
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.Additive
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.BaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The additive group algebraic space

Let `B` be an algebraic space over a scheme `S`. The functor sending a scheme `T` over `B` to
the additive group `Γ(T, 𝒪_T)` of global sections of its structure sheaf is represented by the
group algebraic space `Gₐ,B = B ×_S Gₐ,S`, the base change to `B` of the additive group scheme
over `S`.

## Main definitions

* `AlgebraicGeometry.Space.additiveGroupSiteObject` is the additive group scheme over `S`, read
  as an object of the big fppf site over `S`.
* `AlgebraicGeometry.Space.additiveGroupSpace`: **Stacks 043L**, the additive group algebraic
  space over `B`.
* `AlgebraicGeometry.Space.additiveGroupSpacePoints`: **Stacks 043L**, its group of points over
  a scheme over `B`, identified with the additive group of global sections.

## Main results

* `AlgebraicGeometry.Space.additiveGroupSpace_obj_X` identifies the underlying algebraic space
  with the fibre product of `B` and the functor of points of `Gₐ,S`.
* `AlgebraicGeometry.Space.additiveGroupSpacePoints_apply` and
  `AlgebraicGeometry.Space.additiveGroupSpacePoints_naturality` pin the identification on
  points down, naturally in the test scheme.

## References

* [Stacks Project, Tag 043L](https://stacks.math.columbia.edu/tag/043L)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Space

variable (𝒞 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝒞.Contains S)

/-- The affine line over the integers belongs to every big fppf site. -/
theorem contains_additiveGroup : 𝒞.Contains (additiveGroup : Scheme.{u}) := by
  change (Spec (.of (Polynomial (ULift.{u} ℤ)))).size < 𝒞.cutoff
  rw [Scheme.size_Spec]
  exact max_lt 𝒞.aleph0_lt_cutoff
    ((Polynomial.cardinalMk_le_max.trans
      (max_le Cardinal.mk_le_aleph0 le_rfl)).trans_lt 𝒞.aleph0_lt_cutoff)

/-- The additive group scheme over `S` belongs to the big fppf site of `S`. -/
theorem contains_additiveGroupBaseChange (hS : 𝒞.Contains S) :
    𝒞.Contains (additiveGroupBaseChange S) :=
  Scheme.size_pullback_lt _ _ (contains_additiveGroup 𝒞) hS

/-- The additive group scheme over `S`, read as an object of the big fppf site over `S`. -/
@[stacks 043L "the additive group scheme as an object of the site"]
noncomputable def additiveGroupSiteObject : BigFppfOver 𝒞 S hS :=
  Over.mk (ObjectProperty.homMk (Scheme.asOver (additiveGroupBaseChange S) S).hom
    (X := 𝒞.obj (contains_additiveGroupBaseChange 𝒞 S hS)) (Y := 𝒞.obj hS))

/-- The group-scheme structure of `Gₐ,S` of **Stacks 022V**, read on the object of the site. -/
@[instance_reducible, sga "3 I 4.3.1" "G_{a"]
noncomputable def additiveGroupSiteObjectGrpObj :
    GrpObj ((toSchemeOver 𝒞 S hS).obj (additiveGroupSiteObject 𝒞 S hS)) :=
  additiveGroupBaseChangeGrpObj S

/-- The restriction to the big fppf site over `S` of the functor of points of `Gₐ,S`. -/
noncomputable abbrev additiveGroupPointsOnSite :
    (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ GrpCat.{u} :=
  pointsOnSite 𝒞 S hS (additiveGroupSiteObject 𝒞 S hS) (additiveGroupSiteObjectGrpObj 𝒞 S hS)

/-- The additive group algebraic space `Gₐ,B = B ×_S Gₐ,S` over an algebraic space `B` over
`S`. -/
@[stacks 043L]
noncomputable def additiveGroupSpace (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    (hB : IsAlgebraicSpace 𝒞 S hS B) : GroupAlgebraicSpace 𝒞 S hS B hB :=
  GroupAlgebraicSpace.ofGroupSchemeInSite 𝒞 S hS B hB (additiveGroupSiteObject 𝒞 S hS)
    (additiveGroupSiteObjectGrpObj 𝒞 S hS)

/-- The algebraic space underlying the additive group algebraic space is the fibre product
`B ×_S Gₐ,S`. -/
@[stacks 043L "the underlying base change"]
theorem additiveGroupSpace_obj_X (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    (hB : IsAlgebraicSpace 𝒞 S hS B) :
    (additiveGroupSpace 𝒞 S hS B hB).obj.X =
      (Over.mk (prod.fst :
        B ⨯ (additiveGroupPointsOnSite 𝒞 S hS ⋙ forget GrpCat) ⟶ B) : Over B) :=
  rfl

/-- The group of points of the additive group algebraic space over a scheme `T` over `B` is the
additive group of global sections of `T`. -/
@[stacks 043L "the functor of global sections"]
noncomputable def additiveGroupSpacePoints (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    (T : BigFppfOver 𝒞 S hS) (b : yoneda.obj T ⟶ B) :
    ((Over.mk b : Over B) ⟶
        Over.mk (prod.fst :
          B ⨯ (additiveGroupPointsOnSite 𝒞 S hS ⋙ forget GrpCat) ⟶ B)) ≃*
      (globalSectionsAdditive S).obj (Opposite.op ((toSchemeOver 𝒞 S hS).obj T)) :=
  GroupAlgebraicSpace.groupSchemePointsMulEquiv 𝒞 S hS B (additiveGroupSiteObject 𝒞 S hS)
    (additiveGroupSiteObjectGrpObj 𝒞 S hS) (globalSectionsAdditive S)
    (additiveGroupBaseChangePointsIsoGlobalSections S) T b

/-- `AlgebraicGeometry.Space.additiveGroupSpacePoints` reads a point through the second
projection of the fibre product and the canonical identification of **Stacks 022V**. -/
@[stacks 043L "the functor of global sections"]
theorem additiveGroupSpacePoints_apply (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    (T : BigFppfOver 𝒞 S hS) (b : yoneda.obj T ⟶ B)
    (x : (Over.mk b : Over B) ⟶
      Over.mk (prod.fst : B ⨯ (additiveGroupPointsOnSite 𝒞 S hS ⋙ forget GrpCat) ⟶ B)) :
    additiveGroupSpacePoints 𝒞 S hS B T b x =
      (additiveGroupBaseChangePointsIsoGlobalSections S).hom.app
        (Opposite.op ((toSchemeOver 𝒞 S hS).obj T))
        (yonedaEquiv (x.left ≫ (prod.snd :
          B ⨯ (additiveGroupPointsOnSite 𝒞 S hS ⋙ forget GrpCat) ⟶ _))) :=
  GroupAlgebraicSpace.groupSchemePointsMulEquiv_apply 𝒞 S hS B _ _ _ _ T b x

/-- `AlgebraicGeometry.Space.additiveGroupSpacePoints` is natural in the scheme over `B`. -/
@[stacks 043L "the functor of global sections"]
theorem additiveGroupSpacePoints_naturality (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    (T U : BigFppfOver 𝒞 S hS) (f : T ⟶ U) (b : yoneda.obj U ⟶ B)
    (x : (Over.mk b : Over B) ⟶
      Over.mk (prod.fst : B ⨯ (additiveGroupPointsOnSite 𝒞 S hS ⋙ forget GrpCat) ⟶ B)) :
    additiveGroupSpacePoints 𝒞 S hS B T (yoneda.map f ≫ b)
        ((Over.homMk (yoneda.map f) :
          (Over.mk (yoneda.map f ≫ b) : Over B) ⟶ Over.mk b) ≫ x) =
      (globalSectionsAdditive S ⋙ forget GrpCat).map ((toSchemeOver 𝒞 S hS).map f).op
        (additiveGroupSpacePoints 𝒞 S hS B U b x) :=
  GroupAlgebraicSpace.groupSchemePointsMulEquiv_naturality 𝒞 S hS B _ _ _ _ T U f b x

end AlgebraicGeometry.Space

end
