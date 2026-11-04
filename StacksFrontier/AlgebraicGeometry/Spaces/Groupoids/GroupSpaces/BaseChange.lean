module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Internal.Types.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupActions
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation

/-!
# Base change of group algebraic spaces

A group algebraic space over an algebraic space `B` pulls back along any morphism `B' ⟶ B` of
algebraic spaces to a group algebraic space over `B'`.  Applied to the base `B` itself,
regarded as an algebraic space over the terminal presheaf, this produces the group algebraic
space `G_B = B ×_S G` attached to a group scheme `G` over `S`, which is the form in which all
the standard examples of group algebraic spaces arise.

## Main definitions

* `AlgebraicGeometry.Space.GroupAlgebraicSpace.baseChange`: **Stacks 043I**, the pullback of a
  group algebraic space along a morphism of algebraic spaces.
* `AlgebraicGeometry.Space.GroupAlgebraicSpace.ofPointsFunctor`: the group algebraic space over
  `B` whose functor of points on schemes over `B` is a prescribed presheaf of groups on the big
  fppf site over `S`, provided that presheaf is represented by an object of the site.
* `AlgebraicGeometry.Space.GroupAlgebraicSpace.pointsMulEquiv`: its group of points over a
  scheme over `B`.
* `AlgebraicGeometry.Space.GroupAlgebraicSpace.ofGroupSchemeInSite`: **Stacks 043I** for a group
  scheme `G` over `S` lying in the big fppf site, giving `G_B = B ×_S G`, with
  `AlgebraicGeometry.Space.pointsOnSite` the restriction to the site of its functor of points
  and `AlgebraicGeometry.Space.GroupAlgebraicSpace.groupSchemePointsMulEquiv` its group of
  points read through a prescribed description of that functor.
* `AlgebraicGeometry.Space.toSchemeOver` reads an object of the big fppf site over `S` as a
  scheme over `S`.
* `CategoryTheory.grpObjCompForget`: a presheaf of groups is a group object in presheaves of
  sets, and `CategoryTheory.overProdFstGrpObj` is the induced group object `B ⨯ P` over `B`.

## Main results

* `AlgebraicGeometry.Space.GroupAlgebraicSpace.baseChange_obj_X`,
  `AlgebraicGeometry.Space.GroupAlgebraicSpace.ofPointsFunctor_obj_X` and
  `AlgebraicGeometry.Space.GroupAlgebraicSpace.ofGroupSchemeInSite_obj_X` identify the
  underlying algebraic space over the new base with the fibre product.
* `AlgebraicGeometry.Space.GroupAlgebraicSpace.pointsMulEquiv_apply` and
  `AlgebraicGeometry.Space.GroupAlgebraicSpace.pointsMulEquiv_naturality` pin the group
  isomorphism on points down to the second projection, naturally in the test scheme, as do
  `AlgebraicGeometry.Space.GroupAlgebraicSpace.groupSchemePointsMulEquiv_apply` and
  `AlgebraicGeometry.Space.GroupAlgebraicSpace.groupSchemePointsMulEquiv_naturality`.

## Implementation notes

A group algebraic space over `B` is a group object of the slice of presheaves on the big fppf
site over `S` above `B`, whose underlying presheaf is an algebraic space, as set up in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/GroupActions.lean`.  Base change is therefore
the image of that group object under the finite-product-preserving pullback functor
`CategoryTheory.Over.pullback` between the two slices; the multiplication, identity and inverse
and all their coherences are carried by `CategoryTheory.Functor.mapGrp`, rather than chosen
again, and only algebraicity of the underlying presheaf has to be supplied.  That is
**Stacks 02X2**, `AlgebraicGeometry.isAlgebraicSpace_pullback`.

For the examples the base change is taken from the terminal algebraic space, where the fibre
product `B ×_S G` is the binary product `B ⨯ G` of presheaves.  Rather than transport a group
object along the comparison of the two, `ofPointsFunctor` builds the group object on `B ⨯ G`
directly out of its functor of points, which is `X ↦ Hom(X.left, G)` with its pointwise group
structure: this is what `CategoryTheory.GrpObj.ofRepresentableBy` is for, and it makes the
group law on points the prescribed one by construction, so no separate compatibility lemma is
needed.  Algebraicity of `B ⨯ G` is the restriction of `B` to the representing object of the
site, which is
`AlgebraicGeometry.Space.isAlgebraicSpace_prod_yoneda_obj`, a consequence of **Stacks 02WY**.

## References

* [Stacks Project, Tag 043I](https://stacks.math.columbia.edu/tag/043I)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

universe w v u

namespace CategoryTheory

/-! ### Group objects in a category of presheaves of sets -/

section PresheafOfGroups

variable {C : Type u} [Category.{v} C]

/-- Evaluation of the canonical map to a binary product of presheaves of sets. -/
lemma lift_app_apply {F G H : C ⥤ Type w} (f : F ⟶ G) (g : F ⟶ H) (X : C) (x : F.obj X) :
    (CartesianMonoidalCategory.lift f g).app X x = (f.app X x, g.app X x) :=
  Prod.ext congr($(CartesianMonoidalCategory.lift_fst f g).app X x)
    congr($(CartesianMonoidalCategory.lift_snd f g).app X x)

/-- The monoid-object structure on the presheaf of sets underlying a presheaf of groups. -/
noncomputable abbrev monObjCompForget (F : Cᵒᵖ ⥤ GrpCat.{w}) : MonObj (F ⋙ forget GrpCat) :=
  (Monoidal.MonFunctorCategoryEquivalence.inverseObj
    (F ⋙ forget₂ GrpCat MonCat ⋙ MonTypeEquivalenceMon.inverse)).mon

/-- A presheaf of groups is a group object in the category of presheaves of sets, with the
pointwise multiplication, identity and inverse. -/
@[instance_reducible, sga "3 I 2.1.1" "partial"]
noncomputable instance grpObjCompForget (F : Cᵒᵖ ⥤ GrpCat.{w}) :
    GrpObj (F ⋙ forget GrpCat) where
  __ := monObjCompForget F
  inv :=
    { app X := ↾fun x => x⁻¹
      naturality := by
        intros
        ext
        exact (map_inv _ _).symm }
  left_inv := by
    ext X x
    exact inv_mul_cancel x
  right_inv := by
    ext X x
    exact mul_inv_cancel x

/-- The sections of a presheaf of groups over an object, as a group, are the morphisms from the
presheaf represented by that object into the underlying presheaf of sets. -/
@[sga "3 I 1.6.1" "Hom(h_S, special case"]
noncomputable def yonedaHomMulEquiv (F : Cᵒᵖ ⥤ GrpCat.{v}) (X : C) :
    (yoneda.obj X ⟶ F ⋙ forget GrpCat) ≃* F.obj (Opposite.op X) where
  toEquiv := yonedaEquiv
  map_mul' := fun f g => by
    change (MonObj.mul (X := F ⋙ forget GrpCat)).app _
      ((CartesianMonoidalCategory.lift f g).app _ _) = _
    rw [lift_app_apply]
    rfl

/-- `CategoryTheory.yonedaHomMulEquiv` is evaluation at the identity. -/
lemma yonedaHomMulEquiv_apply (F : Cᵒᵖ ⥤ GrpCat.{v}) (X : C)
    (f : yoneda.obj X ⟶ F ⋙ forget GrpCat) :
    yonedaHomMulEquiv F X f = yonedaEquiv f :=
  rfl

end PresheafOfGroups

/-! ### The product with a group object, as a group object over the other factor -/

section OverProd

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasBinaryProducts C]

/-- The product `B ⨯ P`, viewed over `B` through its first projection, represents the functor
taking an object `X` over `B` to the morphisms from `X` to `P`. -/
noncomputable def overProdFstRepresentableBy (B P : C) [GrpObj P] :
    ((Over.forget B).op ⋙ yonedaGrpObj P ⋙ forget GrpCat).RepresentableBy
      (Over.mk (prod.fst : B ⨯ P ⟶ B)) where
  homEquiv :=
    { toFun := fun x => x.left ≫ prod.snd
      invFun := fun x => Over.homMk (prod.lift _ x)
      left_inv x := by
        apply Over.OverMorphism.ext
        apply prod.hom_ext
        · simpa using x.w.symm
        · simp
      right_inv x := prod.lift_snd _ _ }
  homEquiv_comp f g := Category.assoc _ _ _

/-- The group-object structure on `B ⨯ P` over `B` induced by a group object `P`: its points
over an object `X` over `B` are the morphisms `X.left ⟶ P`, with their pointwise group law. -/
@[instance_reducible]
noncomputable instance overProdFstGrpObj (B P : C) [GrpObj P]
    [CartesianMonoidalCategory (Over B)] : GrpObj (Over.mk (prod.fst : B ⨯ P ⟶ B)) :=
  GrpObj.ofRepresentableBy _ ((Over.forget B).op ⋙ yonedaGrpObj P)
    (overProdFstRepresentableBy B P)

/-- The points of `B ⨯ P` over an object `X` over `B` are the morphisms `X.left ⟶ P`, as
groups. -/
noncomputable def overProdFstHomMulEquiv (B P : C) [GrpObj P]
    [CartesianMonoidalCategory (Over B)] (X : Over B) :
    (X ⟶ Over.mk (prod.fst : B ⨯ P ⟶ B)) ≃* (X.left ⟶ P) :=
  ((yonedaGrpObjIsoOfRepresentableBy _ ((Over.forget B).op ⋙ yonedaGrpObj P)
    (overProdFstRepresentableBy B P)).app (Opposite.op X)).groupIsoToMulEquiv

/-- `CategoryTheory.overProdFstHomMulEquiv` is composition with the second projection. -/
lemma overProdFstHomMulEquiv_apply (B P : C) [GrpObj P]
    [CartesianMonoidalCategory (Over B)] (X : Over B)
    (x : X ⟶ Over.mk (prod.fst : B ⨯ P ⟶ B)) :
    overProdFstHomMulEquiv B P X x = x.left ≫ prod.snd :=
  rfl

end OverProd

/-- A two-sided inverse of an equivariance square. If `u ≫ m = a ≫ v`, and `a` and `m` have
left inverses `a'` and `m'`, then `v ≫ m' = a' ≫ u`. -/
theorem comp_eq_of_comp_eq {D : Type*} [Category D] {P P' X X' : D} {a : P ⟶ P'}
    {a' : P' ⟶ P} {u : P ⟶ X} {v : P' ⟶ X'} {m : X ⟶ X'} {m' : X' ⟶ X}
    (ha : a' ≫ a = 𝟙 P') (hm : m ≫ m' = 𝟙 X) (h : u ≫ m = a ≫ v) : v ≫ m' = a' ≫ u :=
  calc v ≫ m' = (a' ≫ a) ≫ v ≫ m' := by rw [ha, Category.id_comp]
    _ = a' ≫ (a ≫ v) ≫ m' := by simp only [Category.assoc]
    _ = a' ≫ (u ≫ m) ≫ m' := by rw [h]
    _ = a' ≫ u := by rw [Category.assoc, hm, Category.comp_id]

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (𝒞 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝒞.Contains S)

/-- The spectrum of the integers belongs to every big fppf site: its cardinality is countable
and the size cutoff of a big fppf site is uncountable. -/
theorem contains_specULiftZ : 𝒞.Contains (Spec (.of (ULift.{u} ℤ))) := by
  show (Spec (.of (ULift.{u} ℤ))).size < 𝒞.cutoff
  rw [Scheme.size_Spec]
  simpa using 𝒞.aleph0_lt_cutoff

/-- **Stacks Project, Tag 043I.** The pullback of a group algebraic space over `B` along a
morphism `B' ⟶ B` of algebraic spaces is a group algebraic space over `B'`. -/
@[stacks 043I]
noncomputable def GroupAlgebraicSpace.baseChange
    {B B' : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} {hB : IsAlgebraicSpace 𝒞 S hS B}
    (hB' : IsAlgebraicSpace 𝒞 S hS B') (f : B' ⟶ B)
    (G : GroupAlgebraicSpace 𝒞 S hS B hB) :
    GroupAlgebraicSpace 𝒞 S hS B' hB' :=
  ⟨(Over.pullback f).mapGrp.obj G.obj,
    isAlgebraicSpace_pullback 𝒞 S hS G.obj.X.hom f G.property hB' hB⟩

/-- **Stacks Project, Tag 043I.** The algebraic space underlying the pullback of a group
algebraic space is the fibre product of the original one with the new base. -/
@[stacks 043I "the underlying pullback"]
theorem GroupAlgebraicSpace.baseChange_obj_X
    {B B' : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} {hB : IsAlgebraicSpace 𝒞 S hS B}
    (hB' : IsAlgebraicSpace 𝒞 S hS B') (f : B' ⟶ B)
    (G : GroupAlgebraicSpace 𝒞 S hS B hB) :
    (GroupAlgebraicSpace.baseChange 𝒞 S hS hB' f G).obj.X =
      (Over.mk (pullback.snd G.obj.X.hom f) : Over B') :=
  rfl

section OfPointsFunctor

/-- The underlying presheaf of sets of a presheaf of groups on the big fppf site over `S` which
is represented by an object of the site is an algebraic space over `S`. -/
theorem isAlgebraicSpace_compForget_of_representableBy
    (F : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ GrpCat.{u}) {a : BigFppfOver 𝒞 S hS}
    (r : (F ⋙ forget GrpCat).RepresentableBy a) :
    IsAlgebraicSpace 𝒞 S hS (F ⋙ forget GrpCat) :=
  isAlgebraicSpace_of_iso 𝒞 S hS r.toIso.symm (isAlgebraicSpace_yoneda 𝒞 S hS a)

/-- The product of an algebraic space with the underlying presheaf of a presheaf of groups
represented by an object of the site is an algebraic space over `S`: it is the restriction of
the first factor to the representing object. -/
theorem isAlgebraicSpace_prod_compForget_of_representableBy
    (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) (hB : IsAlgebraicSpace 𝒞 S hS B)
    (F : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ GrpCat.{u}) {a : BigFppfOver 𝒞 S hS}
    (r : (F ⋙ forget GrpCat).RepresentableBy a) :
    IsAlgebraicSpace 𝒞 S hS (B ⨯ (F ⋙ forget GrpCat)) :=
  isAlgebraicSpace_of_iso 𝒞 S hS
    ((prod.mapIso (Iso.refl B) r.toIso.symm).trans (prod.braiding B (yoneda.obj a)))
    (isAlgebraicSpace_prod_yoneda_obj a hB)

/-- The group algebraic space over an algebraic space `B` whose points over a scheme `T` over
`B` are the sections over `T` of a prescribed presheaf of groups `F` on the big fppf site over
`S`, assuming `F` is represented by an object of that site.  Its underlying algebraic space is
the fibre product of `B` with that representing object. -/
noncomputable def GroupAlgebraicSpace.ofPointsFunctor
    (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) (hB : IsAlgebraicSpace 𝒞 S hS B)
    (F : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ GrpCat.{u}) {a : BigFppfOver 𝒞 S hS}
    (r : (F ⋙ forget GrpCat).RepresentableBy a) :
    GroupAlgebraicSpace 𝒞 S hS B hB :=
  ⟨Grp.mk (Over.mk (prod.fst : B ⨯ (F ⋙ forget GrpCat) ⟶ B)),
    isAlgebraicSpace_prod_compForget_of_representableBy 𝒞 S hS B hB F r⟩

/-- The algebraic space underlying
`AlgebraicGeometry.Space.GroupAlgebraicSpace.ofPointsFunctor` is, over `B`, the fibre product
of `B` with the representing object of the site. -/
theorem GroupAlgebraicSpace.ofPointsFunctor_obj_X
    (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) (hB : IsAlgebraicSpace 𝒞 S hS B)
    (F : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ GrpCat.{u}) {a : BigFppfOver 𝒞 S hS}
    (r : (F ⋙ forget GrpCat).RepresentableBy a) :
    (GroupAlgebraicSpace.ofPointsFunctor 𝒞 S hS B hB F r).obj.X =
      (Over.mk (prod.fst : B ⨯ (F ⋙ forget GrpCat) ⟶ B) : Over B) :=
  rfl

/-- The group of points of
`AlgebraicGeometry.Space.GroupAlgebraicSpace.ofPointsFunctor` over a scheme `T` over `B` is the
group of sections of `F` over `T`. -/
noncomputable def GroupAlgebraicSpace.pointsMulEquiv
    (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    (F : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ GrpCat.{u}) (T : BigFppfOver 𝒞 S hS)
    (b : yoneda.obj T ⟶ B) :
    ((Over.mk b : Over B) ⟶ Over.mk (prod.fst : B ⨯ (F ⋙ forget GrpCat) ⟶ B)) ≃*
      F.obj (Opposite.op T) :=
  (overProdFstHomMulEquiv B (F ⋙ forget GrpCat) (Over.mk b)).trans
    (yonedaHomMulEquiv F T)

/-- `AlgebraicGeometry.Space.GroupAlgebraicSpace.pointsMulEquiv` reads a point as the section
obtained from the second projection of the fibre product.  This pins the isomorphism down, so
the group law on the points is the group law of `F` and not a twist of it. -/
theorem GroupAlgebraicSpace.pointsMulEquiv_apply
    (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    (F : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ GrpCat.{u}) (T : BigFppfOver 𝒞 S hS)
    (b : yoneda.obj T ⟶ B)
    (x : (Over.mk b : Over B) ⟶ Over.mk (prod.fst : B ⨯ (F ⋙ forget GrpCat) ⟶ B)) :
    GroupAlgebraicSpace.pointsMulEquiv 𝒞 S hS B F T b x =
      yonedaEquiv (x.left ≫ (prod.snd : B ⨯ (F ⋙ forget GrpCat) ⟶ F ⋙ forget GrpCat)) :=
  rfl

/-- `AlgebraicGeometry.Space.GroupAlgebraicSpace.pointsMulEquiv` is natural in the scheme over
`B`: restricting a point along `f : T ⟶ U` restricts its section along `f`. -/
theorem GroupAlgebraicSpace.pointsMulEquiv_naturality
    (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    (F : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ GrpCat.{u}) (T U : BigFppfOver 𝒞 S hS) (f : T ⟶ U)
    (b : yoneda.obj U ⟶ B)
    (x : (Over.mk b : Over B) ⟶ Over.mk (prod.fst : B ⨯ (F ⋙ forget GrpCat) ⟶ B)) :
    GroupAlgebraicSpace.pointsMulEquiv 𝒞 S hS B F T (yoneda.map f ≫ b)
        ((Over.homMk (yoneda.map f) :
          (Over.mk (yoneda.map f ≫ b) : Over B) ⟶ Over.mk b) ≫ x) =
      (F ⋙ forget GrpCat).map f.op
        (GroupAlgebraicSpace.pointsMulEquiv 𝒞 S hS B F U b x) := by
  have h : ((Over.homMk (yoneda.map f) :
        (Over.mk (yoneda.map f ≫ b) : Over B) ⟶ Over.mk b) ≫ x).left ≫
        (prod.snd : B ⨯ (F ⋙ forget GrpCat) ⟶ F ⋙ forget GrpCat) =
      yoneda.map f ≫ (x.left ≫ prod.snd) := by
    simp
  rw [GroupAlgebraicSpace.pointsMulEquiv_apply, GroupAlgebraicSpace.pointsMulEquiv_apply, h,
    ← yonedaEquiv_naturality]

end OfPointsFunctor

section GroupSchemeInSite

/-- An object of the big fppf site over `S`, read as a scheme over `S`.  This is the functor
`AlgebraicGeometry.BigFppfOver.toScheme` with its target refined to the slice over `S`. -/
abbrev toSchemeOver : BigFppfOver 𝒞 S hS ⥤ Over S :=
  Over.post (X := 𝒞.obj hS) 𝒞.inclusion

/-- The restriction to the big fppf site over `S` of the group-valued functor of points of a
group scheme over `S` which belongs to that site. -/
noncomputable abbrev pointsOnSite (G : BigFppfOver 𝒞 S hS)
    (hG : GrpObj ((toSchemeOver 𝒞 S hS).obj G)) :
    (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ GrpCat.{u} :=
  letI := hG
  (toSchemeOver 𝒞 S hS).op ⋙ yonedaGrpObj ((toSchemeOver 𝒞 S hS).obj G)

/-- The functor of points on the site of an object of the site is represented by that object:
the slice over `S` of the site is a full subcategory of the slice over `S` of all schemes. -/
noncomputable def pointsOnSiteRepresentableBy (G : BigFppfOver 𝒞 S hS)
    (hG : GrpObj ((toSchemeOver 𝒞 S hS).obj G)) :
    (pointsOnSite 𝒞 S hS G hG ⋙ forget GrpCat).RepresentableBy G where
  homEquiv :=
    ((Functor.FullyFaithful.ofFullyFaithful 𝒞.inclusion).over (X := 𝒞.obj hS)).homEquiv
  homEquiv_comp f g := (toSchemeOver 𝒞 S hS).map_comp f g

/-- **Stacks Project, Tag 043I.** The group algebraic space `G_B = B ×_S G` over an algebraic
space `B` over `S` attached to a group scheme `G` over `S` belonging to the big fppf site: it is
the base change of `G`, regarded as a group algebraic space over the terminal algebraic space,
along the structure morphism of `B`.  Its points over a scheme `T` over `B` are the morphisms
`T ⟶ G` of schemes over `S`. -/
@[stacks 043I "the group algebraic space attached to a group scheme over the base"]
noncomputable def GroupAlgebraicSpace.ofGroupSchemeInSite
    (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) (hB : IsAlgebraicSpace 𝒞 S hS B)
    (G : BigFppfOver 𝒞 S hS) (hG : GrpObj ((toSchemeOver 𝒞 S hS).obj G)) :
    GroupAlgebraicSpace 𝒞 S hS B hB :=
  GroupAlgebraicSpace.ofPointsFunctor 𝒞 S hS B hB (pointsOnSite 𝒞 S hS G hG)
    (pointsOnSiteRepresentableBy 𝒞 S hS G hG)

/-- The algebraic space underlying
`AlgebraicGeometry.Space.GroupAlgebraicSpace.ofGroupSchemeInSite` is the fibre product of `B`
with the restriction to the site of the functor of points of `G`. -/
theorem GroupAlgebraicSpace.ofGroupSchemeInSite_obj_X
    (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) (hB : IsAlgebraicSpace 𝒞 S hS B)
    (G : BigFppfOver 𝒞 S hS) (hG : GrpObj ((toSchemeOver 𝒞 S hS).obj G)) :
    (GroupAlgebraicSpace.ofGroupSchemeInSite 𝒞 S hS B hB G hG).obj.X =
      (Over.mk (prod.fst : B ⨯ (pointsOnSite 𝒞 S hS G hG ⋙ forget GrpCat) ⟶ B) : Over B) :=
  rfl

/-- The group of points of `G_B = B ×_S G` over a scheme `T` over `B`, read through a
prescribed identification of the functor of points of the group scheme `G` with a group-valued
functor `K` on schemes over `S`.  For the standard examples `K` is the functor of units, of
global sections, of roots of unity or of invertible matrices. -/
noncomputable def GroupAlgebraicSpace.groupSchemePointsMulEquiv
    (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) (G : BigFppfOver 𝒞 S hS)
    (hG : GrpObj ((toSchemeOver 𝒞 S hS).obj G)) (K : (Over S)ᵒᵖ ⥤ GrpCat.{u})
    (e : letI := hG; yonedaGrpObj ((toSchemeOver 𝒞 S hS).obj G) ≅ K)
    (T : BigFppfOver 𝒞 S hS) (b : yoneda.obj T ⟶ B) :
    ((Over.mk b : Over B) ⟶
        Over.mk (prod.fst : B ⨯ (pointsOnSite 𝒞 S hS G hG ⋙ forget GrpCat) ⟶ B)) ≃*
      K.obj (Opposite.op ((toSchemeOver 𝒞 S hS).obj T)) :=
  (GroupAlgebraicSpace.pointsMulEquiv 𝒞 S hS B (pointsOnSite 𝒞 S hS G hG) T b).trans
    ((e.app (Opposite.op ((toSchemeOver 𝒞 S hS).obj T))).groupIsoToMulEquiv)

/-- `AlgebraicGeometry.Space.GroupAlgebraicSpace.groupSchemePointsMulEquiv` reads a point
through the second projection of the fibre product and the prescribed identification. -/
theorem GroupAlgebraicSpace.groupSchemePointsMulEquiv_apply
    (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) (G : BigFppfOver 𝒞 S hS)
    (hG : GrpObj ((toSchemeOver 𝒞 S hS).obj G)) (K : (Over S)ᵒᵖ ⥤ GrpCat.{u})
    (e : letI := hG; yonedaGrpObj ((toSchemeOver 𝒞 S hS).obj G) ≅ K)
    (T : BigFppfOver 𝒞 S hS) (b : yoneda.obj T ⟶ B)
    (x : (Over.mk b : Over B) ⟶
      Over.mk (prod.fst : B ⨯ (pointsOnSite 𝒞 S hS G hG ⋙ forget GrpCat) ⟶ B)) :
    GroupAlgebraicSpace.groupSchemePointsMulEquiv 𝒞 S hS B G hG K e T b x =
      e.hom.app (Opposite.op ((toSchemeOver 𝒞 S hS).obj T))
        (yonedaEquiv (x.left ≫
          (prod.snd : B ⨯ (pointsOnSite 𝒞 S hS G hG ⋙ forget GrpCat) ⟶ _))) :=
  rfl

/-- `AlgebraicGeometry.Space.GroupAlgebraicSpace.groupSchemePointsMulEquiv` is natural in the
scheme over `B`. -/
theorem GroupAlgebraicSpace.groupSchemePointsMulEquiv_naturality
    (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) (G : BigFppfOver 𝒞 S hS)
    (hG : GrpObj ((toSchemeOver 𝒞 S hS).obj G)) (K : (Over S)ᵒᵖ ⥤ GrpCat.{u})
    (e : letI := hG; yonedaGrpObj ((toSchemeOver 𝒞 S hS).obj G) ≅ K)
    (T U : BigFppfOver 𝒞 S hS) (f : T ⟶ U) (b : yoneda.obj U ⟶ B)
    (x : (Over.mk b : Over B) ⟶
      Over.mk (prod.fst : B ⨯ (pointsOnSite 𝒞 S hS G hG ⋙ forget GrpCat) ⟶ B)) :
    GroupAlgebraicSpace.groupSchemePointsMulEquiv 𝒞 S hS B G hG K e T (yoneda.map f ≫ b)
        ((Over.homMk (yoneda.map f) :
          (Over.mk (yoneda.map f ≫ b) : Over B) ⟶ Over.mk b) ≫ x) =
      (K ⋙ forget GrpCat).map ((toSchemeOver 𝒞 S hS).map f).op
        (GroupAlgebraicSpace.groupSchemePointsMulEquiv 𝒞 S hS B G hG K e U b x) := by
  let _inst := hG
  rw [GroupAlgebraicSpace.groupSchemePointsMulEquiv_apply,
    GroupAlgebraicSpace.groupSchemePointsMulEquiv_apply,
    ← GroupAlgebraicSpace.pointsMulEquiv_apply 𝒞 S hS B (pointsOnSite 𝒞 S hS G hG),
    ← GroupAlgebraicSpace.pointsMulEquiv_apply 𝒞 S hS B (pointsOnSite 𝒞 S hS G hG),
    GroupAlgebraicSpace.pointsMulEquiv_naturality]
  exact ConcreteCategory.congr_hom
    (e.hom.naturality ((toSchemeOver 𝒞 S hS).map f).op) _

end GroupSchemeInSite

end AlgebraicGeometry.Space

end
