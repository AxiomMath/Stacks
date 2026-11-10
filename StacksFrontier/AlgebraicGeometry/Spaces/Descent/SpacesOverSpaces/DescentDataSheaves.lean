module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.Effective

/-!
# Descent data in terms of sheaves

A sheaf `F` on the big fppf site equipped with a map to an algebraic space `T` whose fibre
products `X i ×_T F` with the members of a family `X i ⟶ T` are all algebraic spaces gives a
descent datum relative to that family: the components are the fibre products themselves and
the gluing isomorphisms are the two descriptions of `X i ×_T F ×_T X j`. This file constructs
that assignment and makes it a functor from the category of such sheaves to the category of
descent data.

## Main definitions

* `AlgebraicGeometry.Space.Descent.fibreComponent` is the fibre product `X i ×_T F`, viewed as
  a space over `X i`, and `AlgebraicGeometry.Space.Descent.fibreComponentMap` is its
  functoriality in `F`.
* `AlgebraicGeometry.Space.Descent.SheavesWithSpaceFibres` is the category of sheaves over `T`
  all of whose fibre products with the members of the family are algebraic spaces.
* `AlgebraicGeometry.Space.Descent.fibreMove` and
  `AlgebraicGeometry.Space.Descent.fibreTransport` are the move operation of those fibre
  products, which is the content of their gluing isomorphisms.
* `AlgebraicGeometry.Space.Descent.fibreDescentData` is the descent datum of such a sheaf,
  `AlgebraicGeometry.Space.Descent.fibreDescentMap` is its functoriality and
  `AlgebraicGeometry.Space.Descent.fibreDescentFunctor` is the resulting functor.
* `AlgebraicGeometry.Space.Descent.fppfFibreDescentFunctor` is that functor for an fppf
  covering of algebraic spaces, where the hypotheses on the family come from the covering.
* `AlgebraicGeometry.Space.Descent.algebraicSpacesOverToSheaves` views an algebraic space over
  `T` as such a sheaf.

## Main results

* `AlgebraicGeometry.Space.Descent.isPullback_fibreDescentData_obj`: the component of the
  descent datum at `i` is the fibre product of `F` with `X i`, which is the first of the two
  additional statements of the lemma.
* `AlgebraicGeometry.Space.Descent.fibreDescentData_obj` and
  `AlgebraicGeometry.Space.Descent.fibreDescentData_gluing` identify the components and the
  gluing isomorphisms of the descent datum, and
  `AlgebraicGeometry.Space.Descent.fibreMove_naturality` is the naturality that makes the
  assignment functorial.
* `AlgebraicGeometry.Space.Descent.isAlgebraicSpace_le_sheafWithSpaceFibres`: an algebraic
  space over `T` is a sheaf all of whose fibre products with the members of the family are
  algebraic spaces.

## Implementation notes

Only the functor from sheaves to descent data is constructed here. The functor in the other
direction, which is the coequalizer of the two maps from `∐ V i ×_T X j` to `∐ V i`, the
equivalence of categories it takes part in, and the statement that the sheaf is an algebraic
space exactly when the descent datum is effective are not in this file; they are
`AlgebraicGeometry.Space.Descent.descentQuotient` and
`AlgebraicGeometry.Space.Descent.fibreDescentFunctorEquivalence`, in
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/SpacesOverSpaces/DescentDataQuotient.lean`, and
`AlgebraicGeometry.Space.Descent.isAlgebraicSpace_iff_isEffective_fibreDescentData`, in
`DescentDataSheavesEquivalence.lean`, in the same directory.
The fppf covering hypothesis is what the equivalence needs, through full faithfulness; the
other direction turns out to need only that the target and the members of the family are
algebraic spaces, and the sheaf condition on `F` is used by neither.

The fibre product `X i ×_T F` is realized as `CategoryTheory.Limits.pullback F.hom (f i)`,
with its second projection as the structure map to `X i`, so the factors appear in the
opposite order to the source. This is the object underlying
`CategoryTheory.Over.pullback (f i)` applied to `F`, which is the convention of the pullback
of descent data in
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/SpacesOverSpaces/FamilyPullback.lean`, but that
functor is deliberately not used: its internal pullbacks are formed through the instance
`CategoryTheory.Limits.HasPullbacksAlong`, whose projections are not syntactically those of
`CategoryTheory.Limits.HasPullback`, so the simp set for pullbacks does not apply to them.
The maps `AlgebraicGeometry.Space.Descent.fibreComponentMap` are therefore constructed by
hand, and they agree with the maps of that functor.

The gluing isomorphisms are produced from a `CategoryTheory.FamilyTransport`, the move
operation of a family of gluing isomorphisms: for the fibre products it is given directly by
the universal property of the pullback, and `CategoryTheory.FamilyTransport.gluing_cocycle`
then supplies the cocycle condition. Morphisms of descent data are obtained the same way,
from `CategoryTheory.FamilyTransport.gluing_comm`.

Hypotheses carried explicitly rather than derived: the target `T` and the members `X i` are
algebraic spaces, as the category of descent data requires, and every fibre product
`X i ×_T F` is an algebraic space, which is part of the data of an object of
`AlgebraicGeometry.Space.Descent.SheavesWithSpaceFibres`. The fppf covering hypothesis of the
source is not needed for this direction and is therefore not assumed, except in
`AlgebraicGeometry.Space.Descent.fppfFibreDescentFunctor`, which specializes to it. The
sheaf condition on `F` is part of the objects of
`AlgebraicGeometry.Space.Descent.SheavesWithSpaceFibres` for faithfulness to the source, but
it is not used by any construction in this file.

## References

* [Stacks Project, Tag 0ADT](https://stacks.math.columbia.edu/tag/0ADT)
* [Stacks Project, Tag 0ADI](https://stacks.math.columbia.edu/tag/0ADI)
* [Stacks Project, Tag 03Y8](https://stacks.math.columbia.edu/tag/03Y8)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.Descent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable {ι : Type v} {X : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The fibre product `X i ×_T F` of a sheaf `F` over `T` with the `i`-th member of a family
of morphisms to `T`, as a space over `X i` through the second projection. -/
public abbrev fibreComponent (f : ∀ i, X i ⟶ T) (F : Over T) (i : ι) : Over (X i) :=
  Over.mk (pullback.snd F.hom (f i))

/-- Sheaves on the big fppf site endowed with a map to `T` whose fibre products with the
members of the family are all algebraic spaces. -/
public abbrev SheavesWithSpaceFibres (f : ∀ i, X i ⟶ T) :=
  ObjectProperty.FullSubcategory (fun F : Over T ↦
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) F.left ∧
      ∀ i, IsAlgebraicSpace B S hS (fibreComponent f F i).left)

/-- The map of fibre products `X i ×_T F ⟶ X i ×_T G` induced by a map of sheaves over `T`. -/
public def fibreComponentMap (f : ∀ i, X i ⟶ T) {F G : Over T} (ψ : F ⟶ G) (i : ι) :
    fibreComponent f F i ⟶ fibreComponent f G i :=
  Over.homMk (pullback.lift (pullback.fst F.hom (f i) ≫ ψ.left) (pullback.snd F.hom (f i)) (by
      rw [Category.assoc, Over.w ψ]
      exact pullback.condition))
    (pullback.lift_snd _ _ _)

/-- The induced map of fibre products preserves the projection to the sheaf. -/
@[reassoc (attr := simp)]
public lemma fibreComponentMap_left_fst (f : ∀ i, X i ⟶ T) {F G : Over T} (ψ : F ⟶ G) (i : ι) :
    (fibreComponentMap f ψ i).left ≫ pullback.fst G.hom (f i) =
      pullback.fst F.hom (f i) ≫ ψ.left :=
  pullback.lift_fst _ _ _

/-- The induced map of fibre products preserves the projection to the member of the family. -/
@[reassoc (attr := simp)]
public lemma fibreComponentMap_left_snd (f : ∀ i, X i ⟶ T) {F G : Over T} (ψ : F ⟶ G) (i : ι) :
    (fibreComponentMap f ψ i).left ≫ pullback.snd G.hom (f i) = pullback.snd F.hom (f i) :=
  pullback.lift_snd _ _ _

/-- The identity of a sheaf over `T` induces the identity of the fibre products. -/
@[simp]
public lemma fibreComponentMap_id (f : ∀ i, X i ⟶ T) (F : Over T) (i : ι) :
    fibreComponentMap f (𝟙 F) i = 𝟙 (fibreComponent f F i) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext <;> simp

/-- A composite of maps of sheaves over `T` induces the composite of the maps of fibre
products. -/
@[simp]
public lemma fibreComponentMap_comp (f : ∀ i, X i ⟶ T) {F G H : Over T} (ψ : F ⟶ G) (χ : G ⟶ H)
    (i : ι) :
    fibreComponentMap f (ψ ≫ χ) i = fibreComponentMap f ψ i ≫ fibreComponentMap f χ i := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext <;> simp

/-- A point of `X i ×_T F` and a point of `X j` over the same space over `T` have the same
image in `T`, so they are the two components of a point of `X j ×_T F`. -/
public lemma fibreMove_comm (f : ∀ i, X i ⟶ T) (F : Over T) {i j : ι} {Z : Over T}
    (v : Z ⟶ (Over.map (f i)).obj (fibreComponent f F i)) (y : Z ⟶ Over.mk (f j)) :
    (v.left ≫ pullback.fst F.hom (f i)) ≫ F.hom = y.left ≫ f j := by
  have hv := Over.w v
  have hy := Over.w y
  simp only [Over.map_obj_hom, Over.mk_hom] at hv hy
  rw [Category.assoc, pullback.condition, hv]
  exact hy.symm

/-- The move operation on the fibre products of a sheaf over `T` with the members of the
family: a point of `X i ×_T F` is carried to the point of `X j ×_T F` with the same image in
`F` and the prescribed image in `X j`. -/
public def fibreMove (f : ∀ i, X i ⟶ T) (F : Over T) {i j : ι} {Z : Over T}
    (v : Z ⟶ (Over.map (f i)).obj (fibreComponent f F i)) (y : Z ⟶ Over.mk (f j)) :
    Z ⟶ (Over.map (f j)).obj (fibreComponent f F j) :=
  Over.homMk (pullback.lift (v.left ≫ pullback.fst F.hom (f i)) y.left
      (fibreMove_comm f F v y)) (by
    have hy := Over.w y
    simp only [Over.map_obj_hom, Over.mk_hom] at hy ⊢
    rw [← Category.assoc, pullback.lift_snd]
    exact hy)

/-- The moved point has the same image in `F` as the original one. -/
@[reassoc (attr := simp)]
public lemma fibreMove_left_fst (f : ∀ i, X i ⟶ T) (F : Over T) {i j : ι} {Z : Over T}
    (v : Z ⟶ (Over.map (f i)).obj (fibreComponent f F i)) (y : Z ⟶ Over.mk (f j)) :
    (fibreMove f F v y).left ≫ pullback.fst F.hom (f j) =
      v.left ≫ pullback.fst F.hom (f i) :=
  pullback.lift_fst _ _ _

/-- The moved point has the prescribed image in `X j`. -/
@[reassoc (attr := simp)]
public lemma fibreMove_left_snd (f : ∀ i, X i ⟶ T) (F : Over T) {i j : ι} {Z : Over T}
    (v : Z ⟶ (Over.map (f i)).obj (fibreComponent f F i)) (y : Z ⟶ Over.mk (f j)) :
    (fibreMove f F v y).left ≫ pullback.snd F.hom (f j) = y.left :=
  pullback.lift_snd _ _ _

/-- The move operation of the fibre products of a sheaf over `T` with the members of the
family. Its gluing isomorphisms are the gluing isomorphisms of the descent datum. -/
public def fibreTransport (f : ∀ i, X i ⟶ T) (F : Over T) :
    FamilyTransport (fun i ↦ (Over.map (f i)).obj (fibreComponent f F i))
      (fun i ↦ Over.mk (f i)) (fun i ↦ structureMap (f i) (fibreComponent f F i)) where
  move v y := fibreMove f F v y
  comp_move k v y := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext <;> simp
  move_base v y := by
    apply Over.OverMorphism.ext
    simp [structureMap]
  move_self v := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext <;> simp [structureMap]
  move_comp v y z := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext <;> simp

/-- The move operation of a sheaf over `T` is given by `fibreMove`. -/
@[simp]
public lemma fibreTransport_move (f : ∀ i, X i ⟶ T) (F : Over T) {i j : ι} {Z : Over T}
    (v : Z ⟶ (Over.map (f i)).obj (fibreComponent f F i)) (y : Z ⟶ Over.mk (f j)) :
    (fibreTransport f F).move v y = fibreMove f F v y := rfl

/-- A map of sheaves over `T` commutes with the move operations on the fibre products. -/
public lemma fibreMove_naturality (f : ∀ i, X i ⟶ T) {F G : Over T} (ψ : F ⟶ G) {i j : ι}
    {Z : Over T} (v : Z ⟶ (Over.map (f i)).obj (fibreComponent f F i))
    (y : Z ⟶ Over.mk (f j)) :
    fibreMove f F v y ≫ (Over.map (f j)).map (fibreComponentMap f ψ j) =
      fibreMove f G (v ≫ (Over.map (f i)).map (fibreComponentMap f ψ i)) y := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext <;> simp

variable (f : ∀ i, X i ⟶ T) (hT : IsAlgebraicSpace B S hS T)
    (hX : ∀ i, IsAlgebraicSpace B S hS (X i))

/-- The descent datum of a sheaf over `T` whose fibre products with the members of the family
are algebraic spaces: the components are those fibre products and the gluing isomorphisms are
the two descriptions of `X i ×_T F ×_T X j`. -/
public def fibreDescentData (F : SheavesWithSpaceFibres f) : DescentData f hT hX where
  obj i := fibreComponent f F.obj i
  obj_isAlgebraicSpace i := F.property.2 i
  gluing i j := (fibreTransport f F.obj).gluing i j
  cocycle i j k := (fibreTransport f F.obj).gluing_cocycle i j k

/-- The component of the descent datum at `i` is the fibre product `X i ×_T F`. -/
@[simp]
public lemma fibreDescentData_obj (F : SheavesWithSpaceFibres f) (i : ι) :
    (fibreDescentData f hT hX F).obj i = fibreComponent f F.obj i := rfl

/-- The gluing isomorphisms of the descent datum come from the move operation on the fibre
products. -/
@[simp]
public lemma fibreDescentData_gluing (F : SheavesWithSpaceFibres f) (i j : ι) :
    (fibreDescentData f hT hX F).gluing i j = (fibreTransport f F.obj).gluing i j := rfl

/-- The component of the descent datum at `i` sits in the fibre product square for
`X i ×_T F`: its structure map to `X i` and its projection to `F` are a fibre product of
`f i` and the structure map of `F`. -/
@[stacks 0ADT "part (1) only: the component of the descent datum at i is the fibre product \
X i ×_T F. Not the equivalence of categories, and not part (2)"]
public lemma isPullback_fibreDescentData_obj (F : SheavesWithSpaceFibres f) (i : ι) :
    IsPullback ((fibreDescentData f hT hX F).obj i).hom (pullback.fst F.obj.hom (f i)) (f i)
      F.obj.hom :=
  (IsPullback.of_hasPullback F.obj.hom (f i)).flip

/-- The morphism of descent data induced by a map of sheaves over `T`: on the component at `i`
it is the induced map of fibre products with `X i`. -/
public def fibreDescentMap {F G : SheavesWithSpaceFibres f} (φ : F ⟶ G) :
    fibreDescentData f hT hX F ⟶ fibreDescentData f hT hX G where
  hom i := fibreComponentMap f φ.hom i
  comm i j :=
    (fibreTransport f F.obj).gluing_comm (fibreTransport f G.obj)
      (fun i ↦ (Over.map (f i)).map (fibreComponentMap f φ.hom i))
      (fun i ↦ structureMap_naturality (f i) (fibreComponentMap f φ.hom i))
      (fun v y ↦ fibreMove_naturality f φ.hom v y) i j

/-- The component of the morphism of descent data induced by a map of sheaves over `T`. -/
@[simp]
public lemma fibreDescentMap_hom {F G : SheavesWithSpaceFibres f} (φ : F ⟶ G) (i : ι) :
    (fibreDescentMap f hT hX φ).hom i = fibreComponentMap f φ.hom i := rfl

/-- The functor from sheaves over `T` whose fibre products with the members of the family are
algebraic spaces to descent data relative to the family. -/
@[stacks 0ADT "ONE FUNCTOR of the asserted equivalence, right to left: from sheaves over T \
whose fibre products with the family are algebraic spaces, to descent data. The cocycle \
condition is proved, not assumed. This declaration is that functor ALONE -- it asserts \
neither the equivalence nor part (2). Both are proved of this same functor elsewhere, in \
StacksFrontier/AlgebraicGeometry/Spaces/Descent/SpacesOverSpaces/\
DescentDataSheavesEquivalence.lean \
and DescentDataQuotient.lean: \
full faithfulness is fibreDescentFunctorFullyFaithful, essential surjectivity -- the \
left-to-right coequalizer direction, realized by the quotient sheaf descentQuotient -- is the \
instance essSurj_fibreDescentFunctor, the equivalence of categories itself is \
fibreDescentFunctorEquivalence, and part (2) is \
isAlgebraicSpace_iff_isEffective_fibreDescentData. The source's two natural isomorphisms are \
not built by hand: the equivalence is assembled from the two halves above"]
public def fibreDescentFunctor : SheavesWithSpaceFibres f ⥤ DescentData f hT hX where
  obj F := fibreDescentData f hT hX F
  map φ := fibreDescentMap f hT hX φ
  map_id F := DescentData.Hom.ext (funext (fibreComponentMap_id f F.obj))
  map_comp φ ψ := DescentData.Hom.ext (funext (fibreComponentMap_comp f φ.hom ψ.hom))

/-- The component of the descent datum of a sheaf over `T`, as produced by the functor, is the
fibre product `X i ×_T F`. -/
@[simp]
public lemma fibreDescentFunctor_obj_obj (F : SheavesWithSpaceFibres f) (i : ι) :
    ((fibreDescentFunctor f hT hX).obj F).obj i = fibreComponent f F.obj i := rfl

include hT hX in
/-- An algebraic space over `T` is a sheaf whose fibre products with the members of the family
are algebraic spaces. -/
public lemma isAlgebraicSpace_le_sheafWithSpaceFibres :
    (fun U : Over T ↦ IsAlgebraicSpace B S hS U.left) ≤
      (fun F : Over T ↦ Presheaf.IsSheaf (BigFppfOver.topology B S hS) F.left ∧
        ∀ i, IsAlgebraicSpace B S hS (fibreComponent f F i).left) := fun U hU ↦
  ⟨hU.isSheaf, fun i ↦ isAlgebraicSpace_pullback B S hS U.hom (f i) hU (hX i) hT⟩

/-- The algebraic spaces over `T` as sheaves over `T` whose fibre products with the members of
the family are algebraic spaces. Their descent data are the canonical ones, so they are the
objects whose descent datum is effective. -/
public def algebraicSpacesOverToSheaves :
    AlgebraicSpacesOver (B := B) (S := S) (hS := hS) T ⥤ SheavesWithSpaceFibres f :=
  ObjectProperty.ιOfLE (isAlgebraicSpace_le_sheafWithSpaceFibres f hT hX)

/-- For an fppf covering of algebraic spaces, the functor from sheaves over the target whose
fibre products with the members of the covering are algebraic spaces to descent data relative
to the covering. -/
public def fppfFibreDescentFunctor (hcov : Space.IsFppfCovering B S hS X f) :
    SheavesWithSpaceFibres f ⥤
      DescentData f hcov.target_isAlgebraicSpace hcov.source_isAlgebraicSpace :=
  fibreDescentFunctor f hcov.target_isAlgebraicSpace hcov.source_isAlgebraicSpace

end AlgebraicGeometry.Space.Descent

end
