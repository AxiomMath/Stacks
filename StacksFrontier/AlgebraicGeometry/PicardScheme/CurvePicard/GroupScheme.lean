module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicardScheme
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.SliceFiniteProducts
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Picard scheme is a group scheme

When the Picard functor `Pic_{X/S}` of [Stacks, Tag 0B9L] is representable, its representing
object carries the group structure of the abelian-group-valued functor: by the Yoneda lemma a
representable presheaf of groups makes its representing object a group object
(`CategoryTheory.GrpObj.ofRepresentableBy`). The comparison functor from the big fppf site over
`S` to all schemes over `S` is fully faithful and preserves finite products, so it carries this
group object to a group scheme over `S`, the **Picard group scheme**
`Stacks.PicardFunctor.picardGrp`.

## Main definitions

* `Stacks.PicardFunctor.picardGrpFunctor`: the Picard functor as a presheaf of groups.
* `Stacks.PicardFunctor.picardGrpObj`: the group object structure on the representing object.
* `Stacks.PicardFunctor.picardGrp`: the Picard group scheme, an object of `Grp (Over S)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.PicardFunctor

variable (B : BigFppfSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (f : B.obj hX ⟶ B.obj hS)

/-- **The Picard functor as a presheaf of groups**: the abelian-group-valued Picard functor read
multiplicatively. -/
@[sga "7 IX 12.1"]
def picardGrpFunctor : (BigFppfOver B S hS)ᵒᵖ ⥤ GrpCat.{u + 1} :=
  picardAddFunctor B hX hS f ⋙ forget₂ AddCommGrpCat AddGrpCat ⋙ AddGrpCat.toGrp

/-- The underlying presheaf of sets of the Picard functor as a presheaf of groups is the Picard
functor. -/
def picardGrpFunctorForgetIso :
    picardGrpFunctor B hX hS f ⋙ forget GrpCat ≅ picardFunctor B hX hS f :=
  NatIso.ofComponents
    (fun T => ((picardFunctorIsoPicardAddFunctor B hX hS f).app T).symm)
    (fun {T T'} g => by
      ext x
      exact ConcreteCategory.congr_hom
        ((picardFunctorIsoPicardAddFunctor B hX hS f).inv.naturality g) x)

variable [(picardFunctor B hX hS f).IsRepresentable]

/-- The Picard functor as a presheaf of groups is represented by the Picard scheme. -/
def picardGrpRepresentableBy :
    (picardGrpFunctor B hX hS f ⋙ forget GrpCat).RepresentableBy
      (picardFunctor B hX hS f).reprX :=
  (picardFunctor B hX hS f).representableBy.ofIso (picardGrpFunctorForgetIso B hX hS f).symm

attribute [local instance] CartesianMonoidalCategory.ofHasFiniteProducts in
/-- **The group object structure of the representing object of the Picard functor**, in the big
fppf site over `S`. -/
@[instance_reducible]
def picardGrpObj : GrpObj (picardFunctor B hX hS f).reprX :=
  GrpObj.ofRepresentableBy _ (picardGrpFunctor B hX hS f) (picardGrpRepresentableBy B hX hS f)

attribute [local instance] CartesianMonoidalCategory.ofHasFiniteProducts
  Functor.Monoidal.ofChosenFiniteProducts in
/-- **The Picard group scheme** `Pic_{X/S}` as a group object in schemes over `S`: the image of
the group object `picardGrpObj` under the comparison functor from the big fppf site over `S` to
schemes over `S`, which preserves finite products. -/
def picardGrp : Grp (Over (B.inclusion.obj (B.obj hS))) :=
  haveI := preservesFiniteProducts_overPost_bigFppfInclusion B S hS
  letI := picardGrpObj B hX hS f
  (Over.post B.inclusion).mapGrp.obj (Grp.mk (picardFunctor B hX hS f).reprX)

/-- The underlying scheme over `S` of the Picard group scheme is the representing object of the
Picard functor. -/
theorem picardGrp_X : (picardGrp B hX hS f).X =
    (Over.post B.inclusion).obj (picardFunctor B hX hS f).reprX :=
  rfl

end Stacks.PicardFunctor
