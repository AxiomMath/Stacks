module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Reduction
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedPoints

/-!
# Completion of a formal algebraic space along a closed subset of its reduction

Let `S` be a scheme contained in a big fppf site `B`. A formal algebraic space `X` over `S` is
a sheaf of `Type (u + 1)` on the big fppf site of `S`, and it carries a reduction
`i : X_red ⟶ X`: a reduced algebraic space through which every morphism to `X` from a reduced
algebraic space factors uniquely. The inclusion of a reduction is bijective on points, so a
subset of `|X_red|` is the same thing as a subset of `|X|`.

For a closed subset `T ⊆ |X_red|` the *completion* `X_{/T}` of `X` along `T` is the subsheaf of
`X` whose sections over an object `U` of the site are the morphisms `U → X` with
`f(|U|) ⊆ T`, the point-set image being tested on the field-valued points of `U`.

Let `f : X' ⟶ X` be a morphism of formal algebraic spaces over `S`, let `f_red : X'_red ⟶ X_red`
be the induced morphism of reductions and let `T' = |f_red|⁻¹ T`. This file proves that

```
X'_{/T'} ──→ X'
   │          │ f
   ▼          ▼
X_{/T}  ──→ X
```

is a cartesian square.

## Main definitions

* `AlgebraicGeometry.Space.HasImageInULift` is the condition that a section of a presheaf of
  `Type (u + 1)` have point-set image inside a set of points.
* `AlgebraicGeometry.Space.isoSheafifySheaf` is the isomorphism of an fppf sheaf of
  `Type (u + 1)` with its own sheafification.
* `AlgebraicGeometry.Space.completionSubfunctorULift` is the subfunctor of sections with
  point-set image in a given set, `AlgebraicGeometry.Space.completionSheafULift` its fppf
  sheafification and `AlgebraicGeometry.Space.completionSheafULiftInclusion` the resulting
  morphism into the ambient sheaf.
* `AlgebraicGeometry.Space.completionMapULift` and
  `AlgebraicGeometry.Space.completionSheafMapULift` are the morphisms induced on completions
  by a morphism carrying one set of points into another.
* `AlgebraicGeometry.FormalSpace.reductionMap` is the morphism `f_red` of reductions induced
  by a morphism of formal algebraic spaces.
* `AlgebraicGeometry.FormalSpace.completionAlong` is the completion `X_{/T}` of a formal
  algebraic space along a subset `T` of its reduction,
  `AlgebraicGeometry.FormalSpace.completionAlongInclusion` its inclusion into `X` and
  `AlgebraicGeometry.FormalSpace.completionAlongMap` the morphism `X'_{/T'} ⟶ X_{/T}`.

## Main results

* `AlgebraicGeometry.Space.isPullback_completionSheafMapULift`: the completion square of a
  morphism of sheaves of `Type (u + 1)` is cartesian, for a set of points on the source which
  is exactly the inverse image of the one on the target.
* `AlgebraicGeometry.FormalSpace.isClosed_preimage_pointsMapULift`: **Stacks 0GVT**, the
  inverse image `T' = |f_red|⁻¹ T` of a closed subset of `|X_red|` is a closed subset of
  `|X'_red|`.
* `AlgebraicGeometry.FormalSpace.isPullback_completionAlongMap`: **Stacks 0GVT**, the square
  formed by `X'_{/T'} ⟶ X'` and `X_{/T} ⟶ X` over `f` is cartesian.

## Implementation notes

A formal algebraic space takes values in `Type (u + 1)`, the universe in which its point set
already lives, so the completion is a subfunctor of `X` itself and no universe lift intervenes;
this is the one difference from the completion of an algebraic space, where the subfunctor has
to be taken inside the universe lift of `X`.

The cartesian square is checked before sheafifying, where it is a sectionwise statement: a
section of `X'` over `U` is a section of the completion exactly when its image in `X` is a
section of the completion there, because the field-valued points of `X'` restricted from `U`
map to those of `X` and `T'` is the inverse image of `T`. Sheafification preserves fibre
products, and the two right-hand corners are already sheaves, so the square transports to the
fppf sheaves `X'` and `X`.

The morphism `f_red` is the one supplied by the universal property of the reduction of `X`,
and the subset `T ⊆ |X_red|` enters the completion through the bijection `|X_red| = |X|` given
by the inclusion of the reduction. Closedness of `T` is what makes `X_{/T}` a formal algebraic
space, which is a separate assertion, so the cartesian square is proved for an arbitrary
subset of `|X_red|` and closedness is carried only where the source carries it.

## References

* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
* [Stacks Project, Tag 0GVS](https://stacks.math.columbia.edu/tag/0GVS)
* [Stacks Project, Tag 0GVT](https://stacks.math.columbia.edu/tag/0GVT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ u₁ v₂ u₂ u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C) {A : Type u₂}
  [Category.{v₂} A]
  [∀ (P : Cᵒᵖ ⥤ A) (X : C) (R : J.Cover X), HasMultiequalizer (R.index P)]
  [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ A]

/-- Sheafifying a morphism into a sheaf and then undoing the sheafification isomorphism of the
target gives the morphism which the sheafification of the source lifts it to. -/
private theorem sheafifyMap_comp_isoSheafify_inv {P Q : Cᵒᵖ ⥤ A}
    (hQ : Presheaf.IsSheaf J Q) (η : P ⟶ Q) :
    J.sheafifyMap η ≫ (J.isoSheafify hQ).inv = J.sheafifyLift η hQ := by
  refine J.sheafifyLift_unique _ _ _ ?_
  rw [← Category.assoc, ← J.toSheafify_naturality, Category.assoc, ← J.isoSheafify_hom hQ,
    Iso.hom_inv_id, Category.comp_id]

/-- Undoing the sheafification isomorphism of a sheaf and then applying a morphism to another
sheaf gives the morphism which the sheafification of the source lifts it to. -/
private theorem isoSheafify_inv_comp {P Q : Cᵒᵖ ⥤ A} (hP : Presheaf.IsSheaf J P)
    (hQ : Presheaf.IsSheaf J Q) (f : P ⟶ Q) :
    (J.isoSheafify hP).inv ≫ f = J.sheafifyLift f hQ := by
  refine J.sheafifyLift_unique _ _ _ ?_
  rw [← Category.assoc, ← J.isoSheafify_hom hP, Iso.hom_inv_id, Category.id_comp]

end CategoryTheory.GrothendieckTopology

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The completion of a sheaf of large sets along a set of its points -/

/-- A section of a presheaf `X` of `Type (u + 1)` over an object `U` of the big fppf site of
`S` has point-set image in a set `T` of points of `X` when every field-valued point of `U`
restricts it to a field-valued point of `X` whose class belongs to `T`. -/
def HasImageInULift (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1))
    (T : Set (pointsULift.{u + 1} B S hS X)) (U : BigFppfOver B S hS)
    (x : X.obj (Opposite.op U)) : Prop :=
  ∀ p : FieldValuedPoint B S hS (yoneda.obj U),
    (⟨p.carrier, p.contained, p.toBase, X.map p.value.op x⟩ :
      FieldValuedPointULift.{u + 1} B S hS X).class B S hS X ∈ T

/-- Pushing the field-valued point cut out of a section `x` of `X'` by a field-valued point of
`U` along a morphism `f : X' ⟶ X` gives the field-valued point cut out of the image of `x` by
the same field-valued point of `U`. -/
private theorem fieldValuedPointULift_map_restrict
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (f : X' ⟶ X) (U : BigFppfOver B S hS)
    (p : FieldValuedPoint B S hS (yoneda.obj U)) (x : X'.obj (Opposite.op U)) :
    FieldValuedPointULift.map B S hS X' f
        ⟨p.carrier, p.contained, p.toBase, X'.map p.value.op x⟩ =
      (⟨p.carrier, p.contained, p.toBase, X.map p.value.op (f.app (Opposite.op U) x)⟩ :
        FieldValuedPointULift.{u + 1} B S hS X) := by
  show (⟨p.carrier, p.contained, p.toBase,
    f.app _ (X'.map p.value.op x)⟩ : FieldValuedPointULift.{u + 1} B S hS X) = _
  rw [NatTrans.naturality_apply f p.value.op x]

/-- Pushing the field-valued point cut out of a section `x` of `X'` by a field-valued point of
`U` along a morphism `f : X' ⟶ X` gives the field-valued point cut out of the image of `x` by
the same field-valued point of `U`. -/
alias fieldValuedPointULift_map_restrict' := fieldValuedPointULift_map_restrict

/-- The subfunctor of `X` whose sections are those with point-set image in `T`. Restriction
preserves the condition, since a field-valued point of the smaller object composes with the
restriction to a field-valued point of the larger one. -/
def completionSubfunctorULift (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1))
    (T : Set (pointsULift.{u + 1} B S hS X)) : Subfunctor X where
  obj U := {x | HasImageInULift B S hS X T U.unop x}
  map {U V} i x hx := by
    change HasImageInULift B S hS X T _ (X.map i x)
    intro p
    let q : FieldValuedPoint B S hS (yoneda.obj U.unop) :=
      { carrier := p.carrier
        field := p.field
        contained := p.contained
        toBase := p.toBase
        value := p.value ≫ i.unop }
    have hq := hx q
    dsimp [q] at hq
    simpa only [op_comp, Quiver.Hom.unop_op, Functor.map_comp,
      ConcreteCategory.comp_apply] using hq

/-- An fppf sheaf of `Type (u + 1)` is isomorphic to its own sheafification, the isomorphism
being the unit of the sheafification. -/
def isoSheafifySheaf (Z : FormalSpace.FppfSheaf B S hS) :
    Z ≅ (CategoryTheory.plusPlusSheaf (BigFppfOver.topology B S hS) (Type (u + 1))).obj Z.obj where
  hom := ObjectProperty.homMk ((BigFppfOver.topology B S hS).isoSheafify Z.property).hom
  inv := ObjectProperty.homMk ((BigFppfOver.topology B S hS).isoSheafify Z.property).inv
  hom_inv_id :=
    Sheaf.hom_ext ((BigFppfOver.topology B S hS).isoSheafify Z.property).hom_inv_id
  inv_hom_id :=
    Sheaf.hom_ext ((BigFppfOver.topology B S hS).isoSheafify Z.property).inv_hom_id

/-- The completion `X_{/T}` of a sheaf `X` of `Type (u + 1)` along a set `T` of its points:
the fppf sheafification of the subfunctor of sections with point-set image in `T`. -/
abbrev completionSheafULift (X : FormalSpace.FppfSheaf B S hS)
    (T : Set (pointsULift.{u + 1} B S hS X.obj)) : FormalSpace.FppfSheaf B S hS :=
  (CategoryTheory.plusPlusSheaf (BigFppfOver.topology B S hS) (Type (u + 1))).obj
    (completionSubfunctorULift B S hS X.obj T).toFunctor

/-- The morphism `X_{/T} ⟶ X` from a completion of `X` into `X` itself: the sheafification of
the inclusion of the completion subfunctor, read in `X` through the sheafification
isomorphism of `X`. -/
def completionSheafULiftInclusion (X : FormalSpace.FppfSheaf B S hS)
    (T : Set (pointsULift.{u + 1} B S hS X.obj)) :
    completionSheafULift B S hS X T ⟶ X :=
  (CategoryTheory.plusPlusSheaf (BigFppfOver.topology B S hS) (Type (u + 1))).map
      (completionSubfunctorULift B S hS X.obj T).ι ≫
    (isoSheafifySheaf B S hS X).inv

/-- On sections, the inclusion of a completion into the ambient sheaf is the morphism to which
the sheafification of the completion subfunctor lifts its inclusion. -/
theorem completionSheafULiftInclusion_hom (X : FormalSpace.FppfSheaf B S hS)
    (T : Set (pointsULift.{u + 1} B S hS X.obj)) :
    (completionSheafULiftInclusion B S hS X T).hom =
      (BigFppfOver.topology B S hS).sheafifyLift
        (completionSubfunctorULift B S hS X.obj T).ι X.property :=
  (BigFppfOver.topology B S hS).sheafifyMap_comp_isoSheafify_inv X.property _

/-- The morphism of completion subfunctors induced by a morphism `f : X' ⟶ X` of presheaves of
`Type (u + 1)` which carries the set `T'` of points of the source into the set `T` of points
of the target. -/
def completionMapULift {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (f : X' ⟶ X)
    (T' : Set (pointsULift.{u + 1} B S hS X')) (T : Set (pointsULift.{u + 1} B S hS X))
    (hsub : T' ⊆ pointsMapULift B S hS X' f ⁻¹' T) :
    (completionSubfunctorULift B S hS X' T').toFunctor ⟶
      (completionSubfunctorULift B S hS X T).toFunctor where
  app U := ↾fun x => ⟨f.app U x.1, by
    change HasImageInULift B S hS X T U.unop (f.app U x.1)
    intro p
    have hp := hsub (x.2 p)
    rwa [Set.mem_preimage, pointsMapULift_class,
      fieldValuedPointULift_map_restrict B S hS f U.unop p x.1] at hp⟩
  naturality := by
    intro U V i
    ext x
    apply Subtype.ext
    exact NatTrans.naturality_apply f i x.1

/-- The morphism of completions `X'_{/T'} ⟶ X_{/T}` induced by a morphism `f : X' ⟶ X` of fppf
sheaves of `Type (u + 1)` carrying `T'` into `T`. -/
def completionSheafMapULift {X' X : FormalSpace.FppfSheaf B S hS} (f : X' ⟶ X)
    (T' : Set (pointsULift.{u + 1} B S hS X'.obj))
    (T : Set (pointsULift.{u + 1} B S hS X.obj))
    (hsub : T' ⊆ pointsMapULift B S hS X'.obj f.hom ⁻¹' T) :
    completionSheafULift B S hS X' T' ⟶ completionSheafULift B S hS X T :=
  (CategoryTheory.plusPlusSheaf (BigFppfOver.topology B S hS) (Type (u + 1))).map
    (completionMapULift B S hS f.hom T' T hsub)

/-! ### The completion square -/

/-- The completion square of a morphism of presheaves of `Type (u + 1)` is cartesian already
before sheafifying: it is a cartesian square of presheaves, checked on sections over each
object of the site. -/
private theorem completionSubfunctorULift_square_isPullback
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (f : X' ⟶ X)
    (T' : Set (pointsULift.{u + 1} B S hS X')) (T : Set (pointsULift.{u + 1} B S hS X))
    (hsub : T' ⊆ pointsMapULift B S hS X' f ⁻¹' T)
    (hsup : pointsMapULift B S hS X' f ⁻¹' T ⊆ T') :
    IsPullback
      ((completionSubfunctorULift B S hS X' T').ι)
      (completionMapULift B S hS f T' T hsub)
      f
      ((completionSubfunctorULift B S hS X T).ι) := by
  apply IsPullback.of_forall_isPullback_app
  intro U
  apply (Types.isPullback_iff
    (t := (NatTrans.app ((completionSubfunctorULift B S hS X' T').ι) U))
    (r := (NatTrans.app f U))
    (l := (NatTrans.app (completionMapULift B S hS f T' T hsub) U))
    (b := (NatTrans.app ((completionSubfunctorULift B S hS X T).ι) U))).2
  refine ⟨by ext z; rfl, fun a b h => Subtype.ext h.left, ?_⟩
  intro x y h
  obtain ⟨y, hy⟩ := y
  obtain rfl : f.app U x = y := h
  refine ⟨⟨x, ?_⟩, rfl, rfl⟩
  show HasImageInULift B S hS X' T' U.unop x
  intro p
  apply hsup
  rw [Set.mem_preimage, pointsMapULift_class,
    fieldValuedPointULift_map_restrict B S hS f U.unop p x]
  exact hy p

/-- The completion square of a morphism `f : X' ⟶ X` of fppf sheaves of `Type (u + 1)` is
cartesian when the set of points on the source is the inverse image under `|f|` of the set of
points on the target. -/
theorem isPullback_completionSheafMapULift {X' X : FormalSpace.FppfSheaf B S hS} (f : X' ⟶ X)
    (T' : Set (pointsULift.{u + 1} B S hS X'.obj))
    (T : Set (pointsULift.{u + 1} B S hS X.obj))
    (hsub : T' ⊆ pointsMapULift B S hS X'.obj f.hom ⁻¹' T)
    (hsup : pointsMapULift B S hS X'.obj f.hom ⁻¹' T ⊆ T') :
    IsPullback
      (completionSheafULiftInclusion B S hS X' T')
      (completionSheafMapULift B S hS f T' T hsub)
      f
      (completionSheafULiftInclusion B S hS X T) := by
  refine ((completionSubfunctorULift_square_isPullback B S hS f.hom T' T hsub hsup).map
    (CategoryTheory.plusPlusSheaf (BigFppfOver.topology B S hS) (Type (u + 1)))).of_iso
    (Iso.refl _) (isoSheafifySheaf B S hS X').symm (Iso.refl _)
    (isoSheafifySheaf B S hS X).symm ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.id_comp]
    rfl
  · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl
  · exact Sheaf.hom_ext
      (((BigFppfOver.topology B S hS).sheafifyMap_comp_isoSheafify_inv
          X.property f.hom).trans
        ((BigFppfOver.topology B S hS).isoSheafify_inv_comp
          X'.property X.property f.hom).symm)
  · rw [Iso.refl_hom, Category.id_comp]
    rfl

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The reduction of a morphism -/

/-- The morphism `f_red : X'_red ⟶ X_red` of reductions induced by a morphism `f : X' ⟶ X` of
formal algebraic spaces over `S`: the factorisation of `X'_red ⟶ X' ⟶ X` supplied by the
universal property of the reduction of `X`. -/
def reductionMap {X' X Xred' Xred : FppfSheaf B S hS} {i' : Xred' ⟶ X'} {i : Xred ⟶ X}
    (hi' : IsReduction B S hS X' Xred' i') (hi : IsReduction B S hS X Xred i)
    (f : X' ⟶ X) : Xred' ⟶ Xred :=
  Classical.choose (hi.universal Xred' hi'.algebraic hi'.reduced (i' ≫ f))

/-- The morphism of reductions induced by `f : X' ⟶ X` is compatible with `f`. -/
theorem reductionMap_comp {X' X Xred' Xred : FppfSheaf B S hS} {i' : Xred' ⟶ X'}
    {i : Xred ⟶ X} (hi' : IsReduction B S hS X' Xred' i')
    (hi : IsReduction B S hS X Xred i) (f : X' ⟶ X) :
    reductionMap hi' hi f ≫ i = i' ≫ f :=
  (Classical.choose_spec (hi.universal Xred' hi'.algebraic hi'.reduced (i' ≫ f))).1

/-! ### The completion along a subset of the reduction -/

/-- The completion `X_{/T}` of a formal algebraic space `X` over `S` along a subset `T` of the
points of a reduction `i : X_red ⟶ X`: the completion of `X` along the image of `T` under the
bijection `|X_red| = |X|`. -/
def completionAlong {X Xred : FppfSheaf B S hS} (i : Xred ⟶ X)
    (T : Set (Space.pointsULift.{u + 1} B S hS Xred.obj)) : FppfSheaf B S hS :=
  Space.completionSheafULift B S hS X
    (Space.pointsMapULift.{u + 1} B S hS Xred.obj i.hom '' T)

/-- The inclusion `X_{/T} ⟶ X` of the completion of `X` along a subset of the points of a
reduction. -/
def completionAlongInclusion {X Xred : FppfSheaf B S hS} (i : Xred ⟶ X)
    (T : Set (Space.pointsULift.{u + 1} B S hS Xred.obj)) : completionAlong i T ⟶ X :=
  Space.completionSheafULiftInclusion B S hS X
    (Space.pointsMapULift.{u + 1} B S hS Xred.obj i.hom '' T)

/-- **Stacks 0GVT.** The inverse image `T' = |f_red|⁻¹ T` of a closed subset `T ⊆ |X_red|` is a
closed subset of `|X'_red|`, since the morphism of reductions is continuous on points. -/
@[stacks 0GVT "the closed subset `T'`"]
theorem isClosed_preimage_pointsMapULift {Xred' Xred : FppfSheaf B S hS}
    (fred : Xred' ⟶ Xred) (T : Set (Space.pointsULift.{u + 1} B S hS Xred.obj)) :
    letI := Space.pointTopologyULift.{u + 1} B S hS Xred.obj
    letI := Space.pointTopologyULift.{u + 1} B S hS Xred'.obj
    IsClosed T →
      IsClosed (Space.pointsMapULift.{u + 1} B S hS Xred'.obj fred.hom ⁻¹' T) := by
  let _instTarget := Space.pointTopologyULift.{u + 1} B S hS Xred.obj
  let _instSource := Space.pointTopologyULift.{u + 1} B S hS Xred'.obj
  exact fun hT ↦ hT.preimage (Space.continuous_pointsMapULift.{u + 1} B S hS fred.hom)

/-- Viewed inside `|X'|` through the bijection `|X'_red| = |X'|`, the inverse image
`|f_red|⁻¹ T` of a subset `T ⊆ |X_red|` is the inverse image under `|f|` of `T` viewed inside
`|X|`. -/
theorem image_preimage_pointsMapULift {X' X Xred' Xred : FppfSheaf B S hS}
    {i' : Xred' ⟶ X'} {i : Xred ⟶ X} (hi' : IsReduction B S hS X' Xred' i')
    (hi : IsReduction B S hS X Xred i) (f : X' ⟶ X)
    (T : Set (Space.pointsULift.{u + 1} B S hS Xred.obj)) :
    Space.pointsMapULift.{u + 1} B S hS Xred'.obj i'.hom ''
        (Space.pointsMapULift.{u + 1} B S hS Xred'.obj (reductionMap hi' hi f).hom ⁻¹' T) =
      Space.pointsMapULift.{u + 1} B S hS X'.obj f.hom ⁻¹'
        (Space.pointsMapULift.{u + 1} B S hS Xred.obj i.hom '' T) := by
  have hsq : ∀ p, Space.pointsMapULift.{u + 1} B S hS Xred.obj i.hom
        (Space.pointsMapULift.{u + 1} B S hS Xred'.obj (reductionMap hi' hi f).hom p) =
      Space.pointsMapULift.{u + 1} B S hS X'.obj f.hom
        (Space.pointsMapULift.{u + 1} B S hS Xred'.obj i'.hom p) := by
    intro p
    have h : (reductionMap hi' hi f).hom ≫ i.hom = i'.hom ≫ f.hom :=
      congrArg (·.hom) (reductionMap_comp hi' hi f)
    have h' := congrFun (congrArg (Space.pointsMapULift.{u + 1} B S hS Xred'.obj) h) p
    simpa only [Space.pointsMapULift_comp, Function.comp_apply] using h'
  apply Set.eq_of_subset_of_subset
  · rintro x ⟨p, hp, rfl⟩
    exact ⟨_, hp, hsq p⟩
  · intro x hx
    obtain ⟨t, ht, hteq⟩ := hx
    obtain ⟨p, hp⟩ := hi'.bijective_pointsMapULift.2 x
    refine ⟨p, ?_, hp⟩
    rw [Set.mem_preimage]
    have hinj := hi.bijective_pointsMapULift.1 (a₁ := Space.pointsMapULift.{u + 1} B S hS Xred'.obj
      (reductionMap hi' hi f).hom p) (a₂ := t) (by rw [hsq p, hp, hteq])
    rwa [hinj]

/-- The morphism `X'_{/T'} ⟶ X_{/T}` of completions induced by a morphism `f : X' ⟶ X` of
formal algebraic spaces over `S`, where `T' = |f_red|⁻¹ T`. -/
def completionAlongMap {X' X Xred' Xred : FppfSheaf B S hS} {i' : Xred' ⟶ X'}
    {i : Xred ⟶ X} (hi' : IsReduction B S hS X' Xred' i')
    (hi : IsReduction B S hS X Xred i) (f : X' ⟶ X)
    (T : Set (Space.pointsULift.{u + 1} B S hS Xred.obj)) :
    completionAlong i'
        (Space.pointsMapULift.{u + 1} B S hS Xred'.obj (reductionMap hi' hi f).hom ⁻¹' T) ⟶
      completionAlong i T :=
  Space.completionSheafMapULift B S hS f _ _
    (image_preimage_pointsMapULift hi' hi f T).subset

/-- **Stacks 0GVT.** Let `f : X' ⟶ X` be a morphism of formal algebraic spaces over `S`, let
`T ⊆ |X_red|` be a closed subset and let `T' = |f_red|⁻¹ T ⊆ |X'_red|`. Then the square formed
by `X'_{/T'} ⟶ X'`, `X_{/T} ⟶ X`, the morphism of completions and `f` is cartesian. -/
@[stacks 0GVT "the cartesian square", ega "I 10.9.9"]
theorem isPullback_completionAlongMap {X' X Xred' Xred : FppfSheaf B S hS}
    (_hX' : IsFormalAlgebraicSpace B S hS X') (_hX : IsFormalAlgebraicSpace B S hS X)
    {i' : Xred' ⟶ X'} {i : Xred ⟶ X} (hi' : IsReduction B S hS X' Xred' i')
    (hi : IsReduction B S hS X Xred i) (f : X' ⟶ X)
    (T : Set (Space.pointsULift.{u + 1} B S hS Xred.obj))
    (_hT : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS Xred.obj) T) :
    IsPullback
      (completionAlongInclusion i'
        (Space.pointsMapULift.{u + 1} B S hS Xred'.obj (reductionMap hi' hi f).hom ⁻¹' T))
      (completionAlongMap hi' hi f T)
      f
      (completionAlongInclusion i T) :=
  Space.isPullback_completionSheafMapULift B S hS f _ _
    (image_preimage_pointsMapULift hi' hi f T).subset
    (image_preimage_pointsMapULift hi' hi f T).symm.subset

end AlgebraicGeometry.FormalSpace

end
