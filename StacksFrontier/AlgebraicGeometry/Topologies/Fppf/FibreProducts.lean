module

public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksCore.Tactic.StacksAttribute

/-!
# Fibre products in big fppf sites

Schemes of size below a cardinal cutoff are closed under fibre products, so every category
of size-bounded schemes admits fibre products and its inclusion into schemes creates them.
Consequently, for a big fppf site `B` containing a scheme `S`, the underlying category of
`B`, the big fppf category over `S`, and its affine full subcategory all admit fibre
products, and their canonical functors to schemes preserve them.  The object `S / S` is
final in the slice.

## Main results

* `AlgebraicGeometry.schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan`: the size
  cutoff is closed under pullbacks.
* `AlgebraicGeometry.BigFppfSite.hasPullbacks_schemes`: the underlying category of a big fppf
  site admits fibre products.
* `CategoryTheory.Limits.createsLimitsOfShapeFullSubcategoryInclusion` (Mathlib, tagged here):
  its inclusion into schemes creates, hence preserves, fibre products.
* `AlgebraicGeometry.hasPullbacks_bigFppfOver`: the big fppf category over `S` admits fibre
  products.
* `AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme`: the canonical functor from the
  big fppf category over `S` to schemes preserves fibre products.
* `AlgebraicGeometry.isTerminal_mkId_bigFppfOver`: the big fppf category over `S` has a final
  object, namely `S / S`.
* `AlgebraicGeometry.hasPullbacks_bigAffineFppf`: the affine slice admits fibre products.
* `AlgebraicGeometry.preservesPullbacks_bigAffineFppfToScheme`: the canonical functor from
  the affine slice to schemes preserves fibre products.
* `AlgebraicGeometry.hasBinaryProducts_bigFppfOver`: the big fppf category over `S` has binary
  products.

## Implementation notes

Closure of the size cutoff under pullbacks is `AlgebraicGeometry.Scheme.size_pullback_lt`
transported along the isomorphism comparing an arbitrary cospan limit with a pullback; it
holds for every cardinal, with none of the extra conditions needed to build a big fppf
site.  Together with the full-subcategory limit instances it supplies fibre products in the
underlying big fppf category and their creation by the inclusion.  The big fppf category
over `S` is a slice, so the slice results supply its fibre products, their preservation by
the forgetful functor, and the final object `S / S`; preservation by the composite functor
to schemes follows from preservation by each factor.

## References

* [Stacks Project, Tag 021U](https://stacks.math.columbia.edu/tag/021U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Being of size below a cardinal cutoff is invariant under isomorphism of schemes. -/
public instance schemeSizeBelow_isClosedUnderIsomorphisms (κ : Cardinal.{u}) :
    (AlgebraicGeometry.schemeSizeBelow κ).IsClosedUnderIsomorphisms where
  of_iso e hX := by
    change _ < κ
    rwa [← Scheme.size_congr e]

/-- Schemes of size below a cardinal cutoff are closed under fibre products. -/
public instance schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan (κ : Cardinal.{u}) :
    (AlgebraicGeometry.schemeSizeBelow κ).IsClosedUnderLimitsOfShape WalkingCospan := by
  apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
  rintro X ⟨F, hF⟩
  let f := F.map WalkingCospan.Hom.inl
  let g := F.map WalkingCospan.Hom.inr
  let w' : (WidePullbackShape.wideCospan (F.obj none)
      (fun j => F.obj (some j)) (fun j => F.map (.term j))) ≅ cospan f g :=
    WidePullbackShape.functorExt (Iso.refl _)
      (fun j => eqToIso (by cases j <;> rfl)) (fun j => by cases j <;> simp [cospan, f, g])
  let w := (WidePullbackShape.diagramIsoWideCospan F).trans w'
  have hpull : (limit (cospan f g)).size < κ := by
    change (pullback f g).size < κ
    exact Scheme.size_pullback_lt f g (hF WalkingCospan.left)
      (hF WalkingCospan.right)
  change (limit F).size < κ
  exact (Scheme.size_congr (HasLimit.isoOfNatIso w)).trans_lt hpull

add_to_stacks 021U "closure of size-bounded schemes under fibre products"
  schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The underlying category of a big fppf site admits fibre products. -/
@[stacks 021U "fibre products in the big fppf site"]
public theorem BigFppfSite.hasPullbacks_schemes : HasPullbacks B.Schemes := inferInstance

add_to_stacks 021U "preservation by the big fppf site inclusion"
  CategoryTheory.Limits.createsLimitsOfShapeFullSubcategoryInclusion

/-- The big fppf category over `S` admits fibre products. -/
@[stacks 021U "fibre products in the big fppf slice"]
public theorem hasPullbacks_bigFppfOver :
    HasPullbacks (AlgebraicGeometry.BigFppfOver B S hS) := inferInstance

/-- The canonical functor from the big fppf category over `S` to the category of all schemes
preserves fibre products. -/
@[stacks 021U "preservation by the big fppf slice functor to schemes"]
public theorem preservesPullbacks_bigFppfOverToScheme :
    PreservesLimitsOfShape WalkingCospan
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS) := inferInstance

/-- The final object of the big fppf category over `S` is `S / S`, the identity of `S` viewed as
an object over `S`. -/
@[stacks 021U "the final object of the big fppf slice is S / S"]
public noncomputable def isTerminal_mkId_bigFppfOver :
    IsTerminal (C := AlgebraicGeometry.BigFppfOver B S hS) (Over.mk (𝟙 (B.obj hS))) :=
  Over.mkIdTerminal

/-- The inclusion of the affine slice into the big fppf category over `S` creates fibre
products, because a fibre product of affine schemes over an affine base is affine. -/
private noncomputable instance createsPullbacks_bigAffineFppfInclusion :
    CreatesLimitsOfShape WalkingCospan
      (AlgebraicGeometry.BigAffineFppf.inclusion B S hS) where
  CreatesLimit := fun {F} => by
    let G := AlgebraicGeometry.BigFppfOver.toScheme B S hS
    let D := F ⋙ AlgebraicGeometry.BigAffineFppf.inclusion B S hS
    letI (j : WalkingCospan) : IsAffine (G.obj (D.obj j)) := (F.obj j).property
    let t := pullback.cone (D.map WalkingCospan.Hom.inl) (D.map WalkingCospan.Hom.inr)
    exact createsLimitFullSubcategoryInclusion' F
      ((IsLimit.postcomposeInvEquiv (diagramIsoCospan D) t).symm (limit.isLimit _)) (by
      let e := PreservesPullback.iso G (D.map WalkingCospan.Hom.inl)
        (D.map WalkingCospan.Hom.inr)
      exact @IsAffine.of_isIso _ _ e.hom e.isIso_hom inferInstance)

/-- The category of affine objects in the big fppf category over `S` admits fibre products. -/
@[stacks 021U "fibre products in the big affine fppf site"]
public instance hasPullbacks_bigAffineFppf :
    HasPullbacks (AlgebraicGeometry.BigAffineFppf B S hS) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
    (AlgebraicGeometry.BigAffineFppf.inclusion B S hS)

/-- The canonical functor from affine objects over `S` to schemes preserves fibre products. -/
@[stacks 021U "preservation by the big affine fppf functor to schemes"]
public instance preservesPullbacks_bigAffineFppfToScheme :
    PreservesLimitsOfShape WalkingCospan
      (AlgebraicGeometry.BigAffineFppf.toScheme B S hS) :=
  comp_preservesLimitsOfShape _ _

/-- The big fppf category over `S` has binary products, being a slice with a final object and
fibre products. -/
public instance hasBinaryProducts_bigFppfOver :
    HasBinaryProducts (AlgebraicGeometry.BigFppfOver B S hS) :=
  hasBinaryProducts_of_hasTerminal_and_pullbacks _

end AlgebraicGeometry
