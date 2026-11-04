module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.LciLocusBaseChange
public import StacksFrontier.CategoryTheory.Sites.Stack.SlicePointOfObject

/-!
# Every quintuple has data exhibiting its relative map

Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of stacks in groupoids over the big fppf site of a scheme `S`
which is representable by algebraic spaces, and let `Ξ = (U, Z, y, x, α)` be an object of the
relative finite Hilbert category `ℋ_d(𝒳/𝒴)`. The relative map `x_α : Z ⟶ X_y` of **Stacks 06CK**
is read off a `AlgebraicGeometry.Stack.FiniteHilbert.RelativeMapData` for `Ξ`, and the definition
of the local complete intersection locus quantifies over all of them. This file shows that there
is at least one.

Three ingredients enter. The scheme-valued point of `𝒴` over `U` extending the object `y` is the
essential surjectivity of the 2-Yoneda lemma, `CategoryTheory.Functor.exists_slicePoint`. The
algebraic space `X_y` representing the 2-fibre product of `F` with that point, and the
equivalence exhibiting it, are what representability by algebraic spaces (Stacks 02ZW) asserts.
The comparison isomorphism of the restriction of the point to `Z` with `F x` is produced by the
universal property of the identification `α` of the quintuple, which lies over the structure
morphism `q : Z ⟶ U` of the cover and is therefore strongly cartesian.

## Main definitions

* `AlgebraicGeometry.Stack.FiniteHilbert.RelativeMapData.ofPoint`: the data exhibiting the
  relative map, assembled from a scheme-valued point of `𝒴` over the base and an algebraic space
  representing the 2-fibre product of `F` with it. The point and the algebraic space are
  arguments, so a consumer which has a particular pair in hand — for instance the restriction of
  a point along a morphism of base objects together with the restriction of the algebraic space
  representing the unrestricted 2-fibre product — gets data whose point and whose space are the
  ones it chose.

## Main results

* `AlgebraicGeometry.Stack.FiniteHilbert.nonempty_relativeMapData`: **a quintuple of
  `ℋ_d(𝒳/𝒴)` has data exhibiting its relative map, as soon as `F` is representable by algebraic
  spaces.**

## Implementation notes

Nothing here inverts a morphism, in the same way that
`StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.LciLocusBaseChange` does not: the comparison
isomorphism at the cover is obtained as the unique vertical morphism factoring the restriction of
the point through `α`, by `CategoryTheory.Functor.IsStronglyCartesian.map`, and it is invertible
because it lies over an identity and `𝒴` is fibred in groupoids. The compatibility condition
`AlgebraicGeometry.Stack.FiniteHilbert.RelativeMapData.α_comp` is then the defining factorization
read with the inverse moved to the other side.

The verticality of the comparison isomorphism is produced over the cover `Z` read in the big fppf
site of `S` and transported to the cover read over the base through
`AlgebraicGeometry.Stack.FiniteHilbert.Object.overMap_coverOver`, which is the form the field of
`RelativeMapData` takes.

## References

* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 02ZW](https://stacks.math.columbia.edu/tag/02ZW)
* [Stacks Project, Tag 06CK](https://stacks.math.columbia.edu/tag/06CK)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒴 : StackInGroupoids.{w} (BigFppfOver B S hS) (BigFppfOver.topology B S hS)}
  {F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory} {d : ℕ}

namespace FiniteHilbert

variable (P : Object B S hS 𝒳 𝒴 F d)

section Point

/-- The restriction to the cover of a scheme-valued point of `𝒴` over the base, followed by the
identification of its value at the base with the object `y` of the quintuple, lies over the
structure morphism of the cover. -/
theorem isHomLift_map_coverToBase_comp
    (y : BigFppfOver B P.U.left.1 P.U.left.2 ⥤ 𝒴.toBasedCategory.obj)
    (hy : y ⋙ 𝒴.toBasedCategory.p = Over.map P.U.hom) (c : y.obj P.baseOver ⟶ P.y)
    (hc : 𝒴.toBasedCategory.p.IsHomLift (𝟙 P.U) c) :
    𝒴.toBasedCategory.p.IsHomLift P.q (y.map P.coverToBase ≫ c) :=
  have := PresheafOfCategories.isHomLift_map_of_comp hy P.q P.coverToBase
    (isHomLift_coverToBase P)
  have := hc
  IsHomLift.comp_lift_id_right' 𝒴.toBasedCategory.p P.q (y.map P.coverToBase) P.U c

/-- A morphism of `𝒴` lying over a morphism of the base is strongly cartesian, `𝒴` being fibred
in groupoids. -/
private theorem isStronglyCartesian_of_isHomLift {R T : BigFppfOver B S hS}
    {a b : 𝒴.toBasedCategory.obj} {f : R ⟶ T} {φ : a ⟶ b}
    (h : 𝒴.toBasedCategory.p.IsHomLift f φ) : 𝒴.toBasedCategory.p.IsStronglyCartesian f φ :=
  have := h
  𝒴.isStackInGroupoids.isFiberedInGroupoids.isStronglyCartesian_homLift f φ

/-- The identification `α` of a quintuple is strongly cartesian, `𝒴` being fibred in
groupoids. -/
theorem isStronglyCartesian_alpha :
    𝒴.toBasedCategory.p.IsStronglyCartesian P.q P.α :=
  isStronglyCartesian_of_isHomLift P.α_over

/-- The comparison morphism of the restriction of the point to the cover with `F x`, before it is
recognised as an isomorphism: the unique vertical morphism whose composite with the identification
`α` of the quintuple is the restriction of the point to the cover followed by the identification
at the base. -/
noncomputable def alphaHom
    (y : BigFppfOver B P.U.left.1 P.U.left.2 ⥤ 𝒴.toBasedCategory.obj)
    (hy : y ⋙ 𝒴.toBasedCategory.p = Over.map P.U.hom) (c : y.obj P.baseOver ⟶ P.y)
    (hc : 𝒴.toBasedCategory.p.IsHomLift (𝟙 P.U) c) :
    y.obj P.coverOver ⟶ F.toFunctor.obj P.x :=
  have := isStronglyCartesian_alpha P
  have := isHomLift_map_coverToBase_comp P y hy c hc
  Functor.IsStronglyCartesian.map 𝒴.toBasedCategory.p P.q P.α (Category.id_comp P.q).symm
    (y.map P.coverToBase ≫ c)

/-- The comparison morphism at the cover is vertical over the cover. -/
theorem isHomLift_alphaHom
    (y : BigFppfOver B P.U.left.1 P.U.left.2 ⥤ 𝒴.toBasedCategory.obj)
    (hy : y ⋙ 𝒴.toBasedCategory.p = Over.map P.U.hom) (c : y.obj P.baseOver ⟶ P.y)
    (hc : 𝒴.toBasedCategory.p.IsHomLift (𝟙 P.U) c) :
    𝒴.toBasedCategory.p.IsHomLift (𝟙 P.Z) (alphaHom P y hy c hc) :=
  have := isStronglyCartesian_alpha P
  have := isHomLift_map_coverToBase_comp P y hy c hc
  Functor.IsStronglyCartesian.map_isHomLift 𝒴.toBasedCategory.p P.q P.α
    (Category.id_comp P.q).symm (y.map P.coverToBase ≫ c)

/-- The defining factorization of the comparison morphism at the cover. -/
theorem alphaHom_comp
    (y : BigFppfOver B P.U.left.1 P.U.left.2 ⥤ 𝒴.toBasedCategory.obj)
    (hy : y ⋙ 𝒴.toBasedCategory.p = Over.map P.U.hom) (c : y.obj P.baseOver ⟶ P.y)
    (hc : 𝒴.toBasedCategory.p.IsHomLift (𝟙 P.U) c) :
    alphaHom P y hy c hc ≫ P.α = y.map P.coverToBase ≫ c :=
  have := isStronglyCartesian_alpha P
  have := isHomLift_map_coverToBase_comp P y hy c hc
  Functor.IsStronglyCartesian.fac 𝒴.toBasedCategory.p P.q P.α (Category.id_comp P.q).symm
    (y.map P.coverToBase ≫ c)

/-- The comparison morphism at the cover is invertible: it lies over an identity, and a morphism
of a category fibred in groupoids lying over an isomorphism is an isomorphism. -/
theorem isIso_alphaHom
    (y : BigFppfOver B P.U.left.1 P.U.left.2 ⥤ 𝒴.toBasedCategory.obj)
    (hy : y ⋙ 𝒴.toBasedCategory.p = Over.map P.U.hom) (c : y.obj P.baseOver ⟶ P.y)
    (hc : 𝒴.toBasedCategory.p.IsHomLift (𝟙 P.U) c) :
    IsIso (alphaHom P y hy c hc) :=
  have := isStronglyCartesian_of_isHomLift (isHomLift_alphaHom P y hy c hc)
  Functor.IsStronglyCartesian.isIso_of_base_isIso 𝒴.toBasedCategory.p (𝟙 P.Z)
    (alphaHom P y hy c hc)

/-- Data exhibiting the relative map of a quintuple, assembled from a scheme-valued point of `𝒴`
over the base extending the object `y` of the quintuple and an algebraic space representing the
2-fibre product of `F` with that point. -/
noncomputable def RelativeMapData.ofPoint
    (y : BigFppfOver B P.U.left.1 P.U.left.2 ⥤ 𝒴.toBasedCategory.obj)
    (hy : y ⋙ 𝒴.toBasedCategory.p = Over.map P.U.hom) (c : y.obj P.baseOver ⟶ P.y)
    (hc : 𝒴.toBasedCategory.p.IsHomLift (𝟙 P.U) c)
    (Xy : (BigFppfOver B P.U.left.1 P.U.left.2)ᵒᵖ ⥤ Type u)
    (hXy : IsAlgebraicSpace B P.U.left.1 P.U.left.2 Xy)
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map P.U.hom) 𝒳.toBasedCategory.p 𝒴.toBasedCategory.p y
        F.toFunctor)
      (presheafOfCategories (Xy ⋙ typeToCat)).p) : RelativeMapData P where
  y := y
  y_comp := hy
  yUnit := c
  yUnit_over := hc
  Xy := Xy
  isAlgebraicSpace := hXy
  e := e
  α := have := isIso_alphaHom P y hy c hc; asIso (alphaHom P y hy c hc)
  α_over := by
    have h := isHomLift_alphaHom P y hy c hc
    rwa [← Object.overMap_coverOver P] at h
  α_comp := by
    have hfac := alphaHom_comp P y hy c hc
    have := isIso_alphaHom P y hy c hc
    change (asIso (alphaHom P y hy c hc)).inv ≫ y.map P.coverToBase ≫ c = P.α
    rw [← hfac, asIso_inv, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

end Point

/-- **Every quintuple of `ℋ_d(𝒳/𝒴)` has data exhibiting its relative map**, as soon as the
1-morphism `F` is representable by algebraic spaces.

The scheme-valued point of `𝒴` over the base extending the object `y` of the quintuple is the
2-Yoneda lemma (`CategoryTheory.Functor.exists_slicePoint`), the algebraic space representing the
2-fibre product of `F` with it is what Stacks 02ZW supplies, and the comparison isomorphism of
the restriction of the point to the cover with `F x` is the unique vertical morphism factoring
that restriction through the identification `α` of the quintuple. -/
theorem nonempty_relativeMapData (hFrep : IsRepresentableByAlgebraicSpaces B S hS F) :
    Nonempty (RelativeMapData P) := by
  have _ := 𝒴.isStackInGroupoids.isFiberedInGroupoids.isFibered
  obtain ⟨y, hy, c, hc⟩ := Functor.exists_slicePoint 𝒴.toBasedCategory.p P.U P.y P.y_over
  obtain ⟨Xy, hXy, ⟨e⟩⟩ := hFrep P.U y hy
  exact ⟨RelativeMapData.ofPoint P y hy c hc Xy hXy e⟩

end FiniteHilbert

end AlgebraicGeometry.Stack

end
