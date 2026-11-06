module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenPointSetDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Coproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.EmptyOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteUnionRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.SeparatedClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence

/-!
# The operations on the finite part of a separated morphism

Let `f : X ⟶ Y` be a separated morphism of algebraic spaces over a scheme `S`. A section of the
finite part `(X/Y)_fin` over an algebraic space `T` is a pair `(a, Z)` consisting of a morphism
`a : T ⟶ Y` and an open subspace `Z` of `T ×_Y X` finite over `T`, and a section of
`(X/Y)_fin ×_Y (X/Y)_fin` over `T` is a pair of such pairs with the same first component. This
file records the sections over a fixed first component as
`AlgebraicGeometry.Space.FinitePartFibre` and constructs three of the four operations of
Stacks 04PI on them: the intersection `⋆₂`, and the two differences `⋆₃` and `⋆₄`. The fourth,
the union `⋆₁`, and the `F₂`-algebra structure whose addition it assembles are in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/FinitePart/Union.lean`.

The point of the remark is that these are defined at all. Each `Z` is a *closed* subspace of
`T ×_Y X` by Stacks 04PH, hence open and closed; so the intersection and the two differences
are again open and closed, and each of them is contained in one of `Z₁`, `Z₂`, therefore a
closed subspace of it, therefore finite over `T` because a closed immersion is finite.

## Main definitions

* `AlgebraicGeometry.Space.FinitePartFibre`: a section of `(X/Y)_fin` over `T` with prescribed
  image `a` in `Y`.
* `AlgebraicGeometry.Space.FinitePartFibre.star₂`,
  `AlgebraicGeometry.Space.FinitePartFibre.star₃` and
  `AlgebraicGeometry.Space.FinitePartFibre.star₄`: the operations `⋆₂`, `⋆₃` and `⋆₄` of
  Stacks 04PI.
* `AlgebraicGeometry.Space.FinitePartFibre.one`: for `f` finite, the section
  `1 = (a, T ×_Y X)`, the unit for the multiplication `⋆₂`.

## Main results

* `AlgebraicGeometry.Space.FinitePartFibre.equivFiniteOpenSubspace`: the sections with
  prescribed image in `Y` are the sections of `(X/Y)_fin` over `T` lying over `a`, so that a
  pair of them is a section of `(X/Y)_fin ×_Y (X/Y)_fin`.
* `AlgebraicGeometry.Space.FinitePartFibre.isClopen_pointSet`: the point set of a section is
  open and closed, which is Stacks 04PH read on points.
* `AlgebraicGeometry.Space.FinitePartFibre.pointSet_star₂`,
  `AlgebraicGeometry.Space.FinitePartFibre.pointSet_star₃` and
  `AlgebraicGeometry.Space.FinitePartFibre.pointSet_star₄`: the three operations are, on
  points, intersection and the two differences.
* `AlgebraicGeometry.Space.FinitePartFibre.isOpenImmersion_star₂_le_left`,
  `AlgebraicGeometry.Space.FinitePartFibre.isClosedImmersion_star₂_le_left` and their `right`
  counterparts: `Z₁ ∩ Z₂` is both open and closed inside `Z₁` and inside `Z₂`, which is the
  reason the remark gives for the operations to be defined.
* `AlgebraicGeometry.Space.FinitePartFibre.star₂_one` and
  `AlgebraicGeometry.Space.FinitePartFibre.star₂_one'`: for `f` finite, `1 s = s = s 1`.
* `AlgebraicGeometry.Space.FinitePartFibre.subspace_one` and
  `AlgebraicGeometry.Space.FinitePartFibre.subspace_zero`: the open subspace of the unit is the
  whole of `T ×_Y X` and that of the zero section is the empty one.

## Implementation notes

An open subspace is recorded as a `CategoryTheory.Subfunctor` of the ambient presheaf, and the
lattice of subfunctors is not the lattice of open subspaces: the pointwise difference of two
subfunctors is not a subfunctor, and the pointwise union of two open subspaces is not a sheaf.
The operations are therefore defined through the correspondence of Stacks 03BZ between open
subspaces of an algebraic space and open subsets of its space of points: each operation is
`AlgebraicGeometry.Space.openSubspaceOfPoints` applied to the corresponding operation on point
sets, which is legitimate because all the point sets involved are open and closed.

The union `⋆₁` is the one operation whose point set is contained in neither factor, so the
argument above does not give finiteness of its projection to `T`; it is therefore constructed
separately, and the laws proved here are the multiplicative ones together with those of the
zero section. The zero section takes a section as an argument, from which it inherits the
ambient space, rather than being produced from nothing.

For `f` finite the whole of `T ×_Y X` is finite over `T`, being a base change of `f`, so every
open and closed set of points cuts out a section of the finite part
(`AlgebraicGeometry.Space.FinitePartFibre.ofClopen`); the unit `1 = (a, T ×_Y X)` is the one
cut out by all of them.

## References

* [Stacks Project, Tag 04PI](https://stacks.math.columbia.edu/tag/04PI)
* [Stacks Project, Tag 04PH](https://stacks.math.columbia.edu/tag/04PH)
* [Stacks Project, Tag 04PC](https://stacks.math.columbia.edu/tag/04PC)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 081Y](https://stacks.math.columbia.edu/tag/081Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- **An open subspace of an algebraic space is an open subspace of any subfunctor containing
it.** The inclusion is a base change of the inclusion of the open subspace along the inclusion
of the larger subfunctor, the comparison triangle being Cartesian because the inclusion of a
subfunctor is a monomorphism.

This is the open-immersion counterpart of
`AlgebraicGeometry.Space.isClosedImmersion_homOfLe`. -/
theorem isOpenImmersion_homOfLe (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V W : Subfunctor A}
    (hV : IsOpenImmersion B S hS V.ι) (h : V ≤ W) :
    IsOpenImmersion B S hS (Subfunctor.homOfLe h) :=
  (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
    (IsPullback.of_horiz_isIso_mono (fst := 𝟙 V.toFunctor) (snd := Subfunctor.homOfLe h)
      (f := V.ι) (g := W.ι) ⟨by simp⟩) hV

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) {T : AlgebraicSpaces B S hS}

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance hasPullbacks_presheaf_finitePartOperations :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_finitePartOperations
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **Stacks 04PI.** A section of the finite part `(X/Y)_fin` over `T` whose image in `Y` is a
prescribed morphism `a : T ⟶ Y`: an open subspace of `T ×_Y X` whose projection to `T` is
finite.

A pair of these, for one and the same `a`, is exactly a section of
`(X/Y)_fin ×_Y (X/Y)_fin` over `T`; this is
`AlgebraicGeometry.Space.FinitePartFibre.equivFiniteOpenSubspace`. -/
structure FinitePartFibre (a : T ⟶ Y) where
  /-- The open subspace of the fibre product `T ×_Y X`. -/
  subspace : Subfunctor (pullback a.hom f.hom)
  /-- The subfunctor is an open subspace. -/
  isOpen : IsOpenSubspace B S hS subspace
  /-- The projection of the open subspace to `T` is finite. -/
  finite_projection : IsFinite B S hS (subspace.ι ≫ pullback.fst a.hom f.hom)

namespace FinitePartFibre

variable {B S hS f} {a : T ⟶ Y}

/-- The pair of Stacks 04PC determined by a section with prescribed image in `Y`. -/
def toPair (Z : FinitePartFibre B S hS f a) : FiniteOpenSubspace B S hS f T :=
  ⟨a, Z.subspace, Z.isOpen, Z.finite_projection⟩

/-- The morphism to `Y` of the pair determined by a section with prescribed image `a` is `a`. -/
@[simp]
theorem toPair_toBase (Z : FinitePartFibre B S hS f a) : Z.toPair.toBase = a := rfl

/-- The section with prescribed image in `Y` determined by a pair of Stacks 04PC whose
morphism to `Y` is that image. -/
def ofPair {p : FiniteOpenSubspace B S hS f T} (h : p.toBase = a) :
    FinitePartFibre B S hS f a := by
  obtain ⟨b, Z, hO, hF⟩ := p
  subst h
  exact ⟨Z, hO, hF⟩

/-- **Stacks 04PI.** The sections of `(X/Y)_fin` over `T` whose image in `Y` is `a` are the
open subspaces of `T ×_Y X` finite over `T`; so a pair of sections of `(X/Y)_fin` over `T`
with the same image in `Y` -- that is, a section of `(X/Y)_fin ×_Y (X/Y)_fin` over `T` -- is a
pair of elements of `FinitePartFibre`. -/
def equivFiniteOpenSubspace (a : T ⟶ Y) :
    FinitePartFibre B S hS f a ≃ {p : FiniteOpenSubspace B S hS f T // p.toBase = a} where
  toFun Z := ⟨Z.toPair, rfl⟩
  invFun p := ofPair p.2
  left_inv Z := rfl
  right_inv := by
    rintro ⟨⟨b, Z, hO, hF⟩, rfl⟩
    rfl

/-- The set of points of `T ×_Y X` lying in a section of the finite part. -/
def pointSet (Z : FinitePartFibre B S hS f a) :
    Set (points B S hS (pullback a.hom f.hom)) :=
  Set.range (pointsMap B S hS Z.subspace.toFunctor Z.subspace.ι)

variable (B S hS f)

/-- The fibre product `T ×_Y X` is an algebraic space over `S`. -/
theorem isAlgebraicSpace_ambient (a : T ⟶ Y) :
    IsAlgebraicSpace B S hS (pullback a.hom f.hom) :=
  isAlgebraicSpace_pullback B S hS a.hom f.hom T.property X.property Y.property

/-- If `f` is finite, then so is the projection `T ×_Y X ⟶ T`, being a base change of `f`. -/
theorem isFinite_pullback_fst_of_isFinite (hfin : IsFinite B S hS f.hom) (a : T ⟶ Y) :
    IsFinite B S hS (pullback.fst a.hom f.hom) :=
  isFinite_of_isPullback B S hS (IsPullback.of_hasPullback a.hom f.hom).flip hfin

variable {B S hS f}

/-- A section of the finite part is a closed subspace of `T ×_Y X`, by Stacks 04PH. -/
theorem isClosedSubspace (hf : IsSeparated B S hS f.hom) (Z : FinitePartFibre B S hS f a) :
    IsClosedSubspace B S hS Z.subspace :=
  FiniteOpenSubspace.isClosedSubspace B S hS f T Z.toPair hf

/-- **Stacks 04PH on points.** The point set of a section of the finite part is open and
closed: open because the section is an open subspace, closed because it is a closed subspace
by Stacks 04PH. -/
theorem isClopen_pointSet (hf : IsSeparated B S hS f.hom) (Z : FinitePartFibre B S hS f a) :
    IsClopen Z.pointSet :=
  ⟨isClosed_range_pointsMap_of_isClosedImmersion B S hS
      (isAlgebraicSpace_ambient B S hS f a) Z.subspace.ι (Z.isClosedSubspace hf).2,
    isOpen_range_pointsMap_of_isOpenImmersion B S hS Z.subspace.ι Z.isOpen.2⟩

/-- The open subspace of `T ×_Y X` cut out by an open and closed set of points which is
contained in the point set of a section of the finite part is again a section of the finite
part.

It is an open subspace because the set of points is open; its projection to `T` is finite
because it is a closed subspace of `T ×_Y X` contained in the given section, hence a closed
subspace of that section, hence finite over it by Stacks 081Y, and the given section is finite
over `T`. -/
def ofClopenSubset (Z : FinitePartFibre B S hS f a)
    (W : Set (points B S hS (pullback a.hom f.hom))) (hWo : IsOpen W) (hWc : IsClosed W)
    (hsub : W ⊆ Z.pointSet) : FinitePartFibre B S hS f a where
  subspace := openSubspaceOfPoints B S hS (pullback a.hom f.hom) W
  isOpen := isOpenSubspace_openSubspaceOfPoints B S hS
    (isAlgebraicSpace_ambient B S hS f a) W hWo
  finite_projection := by
    have hamb : IsAlgebraicSpace B S hS (pullback a.hom f.hom) :=
      isAlgebraicSpace_ambient B S hS f a
    have hRopen : IsOpenSubspace B S hS (openSubspaceOfPoints B S hS (pullback a.hom f.hom) W) :=
      isOpenSubspace_openSubspaceOfPoints B S hS hamb W hWo
    have hrange : Set.range (pointsMap B S hS
        (openSubspaceOfPoints B S hS (pullback a.hom f.hom) W).toFunctor
        (openSubspaceOfPoints B S hS (pullback a.hom f.hom) W).ι) = W :=
      range_pointsMap_ι_openSubspaceOfPoints B S hS W
    have hRclosed : IsClosedSubspace B S hS
        (openSubspaceOfPoints B S hS (pullback a.hom f.hom) W) :=
      ⟨hRopen.1, (isClosedImmersion_iff_isClosed_range_pointsMap B S hS hamb _
        (isImmersion_of_isOpenImmersion B S hS hRopen.2)).2 (by rw [hrange]; exact hWc)⟩
    have hle : openSubspaceOfPoints B S hS (pullback a.hom f.hom) W ≤ Z.subspace :=
      le_of_range_pointsMap_ι_subset B S hS Z.isOpen (by rw [hrange]; exact hsub)
    have hfin : IsFinite B S hS (Subfunctor.homOfLe hle) :=
      isFinite_of_isClosedImmersion B S hS _ (isClosedImmersion_homOfLe B S hS ⟨_, hRclosed⟩ hle)
    have heq : (openSubspaceOfPoints B S hS (pullback a.hom f.hom) W).ι ≫
        pullback.fst a.hom f.hom =
          Subfunctor.homOfLe hle ≫ Z.subspace.ι ≫ pullback.fst a.hom f.hom := by
      rw [← Category.assoc, Subfunctor.homOfLe_ι]
    rw [heq]
    exact isFinite_comp B S hS hfin Z.finite_projection

/-- The point set of the section cut out by an open and closed set of points `W` is `W`. -/
@[simp]
theorem pointSet_ofClopenSubset (Z : FinitePartFibre B S hS f a)
    (W : Set (points B S hS (pullback a.hom f.hom))) (hWo : IsOpen W) (hWc : IsClosed W)
    (hsub : W ⊆ Z.pointSet) :
    (Z.ofClopenSubset W hWo hWc hsub).pointSet = W :=
  range_pointsMap_ι_openSubspaceOfPoints B S hS W

/-- The open subspace of `T ×_Y X` cut out by an open and closed set of points is a section of
the finite part as soon as the whole of `T ×_Y X` is finite over `T`.

It is an open subspace because the set of points is open, and its projection to `T` is finite
because it is a closed subspace of `T ×_Y X`, hence finite over `T ×_Y X`, which is finite
over `T`. -/
def ofClopen (hamb : IsFinite B S hS (pullback.fst a.hom f.hom))
    (W : Set (points B S hS (pullback a.hom f.hom))) (hWo : IsOpen W) (hWc : IsClosed W) :
    FinitePartFibre B S hS f a where
  subspace := openSubspaceOfPoints B S hS (pullback a.hom f.hom) W
  isOpen := isOpenSubspace_openSubspaceOfPoints B S hS
    (isAlgebraicSpace_ambient B S hS f a) W hWo
  finite_projection :=
    isFinite_comp B S hS (isFinite_of_isClosedImmersion B S hS _
      (isClosedSubspace_openSubspaceOfPoints B S hS
        (isAlgebraicSpace_ambient B S hS f a) W hWo hWc).2) hamb

/-- The point set of the section cut out by an open and closed set of points `W` is `W`. -/
@[simp]
theorem pointSet_ofClopen (hamb : IsFinite B S hS (pullback.fst a.hom f.hom))
    (W : Set (points B S hS (pullback a.hom f.hom))) (hWo : IsOpen W) (hWc : IsClosed W) :
    (ofClopen hamb W hWo hWc).pointSet = W :=
  range_pointsMap_ι_openSubspaceOfPoints B S hS W

/-- A section whose point set is contained in that of another is a subfunctor of it. -/
private theorem subspace_le_of_pointSet_subset {Z₁ Z₂ : FinitePartFibre B S hS f a}
    (h : Z₁.pointSet ⊆ Z₂.pointSet) : Z₁.subspace ≤ Z₂.subspace :=
  le_of_range_pointsMap_ι_subset B S hS Z₂.isOpen h

/-- Two sections of the finite part over the same `a` with the same point set are equal. -/
theorem ext_pointSet {Z₁ Z₂ : FinitePartFibre B S hS f a} (h : Z₁.pointSet = Z₂.pointSet) :
    Z₁ = Z₂ := by
  have h₁ : Z₁.subspace = Z₂.subspace :=
    le_antisymm (subspace_le_of_pointSet_subset h.le) (subspace_le_of_pointSet_subset h.ge)
  cases Z₁; cases Z₂; subst h₁; rfl

section Operations

variable (hf : IsSeparated B S hS f.hom) (Z₁ Z₂ : FinitePartFibre B S hS f a)

/-- **Stacks 04PI, the operation `⋆₂`.** The intersection `(a, Z₁ ∩ Z₂)` of two sections of
the finite part lying over the same morphism to `Y`. -/
@[stacks 04PI "star_2_on_sections"]
def star₂ : FinitePartFibre B S hS f a :=
  Z₁.ofClopenSubset (Z₁.pointSet ∩ Z₂.pointSet)
    ((Z₁.isClopen_pointSet hf).2.inter (Z₂.isClopen_pointSet hf).2)
    ((Z₁.isClopen_pointSet hf).1.inter (Z₂.isClopen_pointSet hf).1)
    Set.inter_subset_left

/-- **Stacks 04PI, the operation `⋆₃`.** The difference `(a, Z₁ ∖ Z₂)` of two sections of the
finite part lying over the same morphism to `Y`. -/
@[stacks 04PI "star_3_on_sections"]
def star₃ : FinitePartFibre B S hS f a :=
  Z₁.ofClopenSubset (Z₁.pointSet \ Z₂.pointSet)
    ((Z₁.isClopen_pointSet hf).2.sdiff (Z₂.isClopen_pointSet hf).1)
    ((Z₁.isClopen_pointSet hf).1.sdiff (Z₂.isClopen_pointSet hf).2)
    Set.diff_subset

/-- **Stacks 04PI, the operation `⋆₄`.** The difference `(a, Z₂ ∖ Z₁)` of two sections of the
finite part lying over the same morphism to `Y`. -/
@[stacks 04PI "star_4_on_sections"]
def star₄ : FinitePartFibre B S hS f a :=
  Z₂.ofClopenSubset (Z₂.pointSet \ Z₁.pointSet)
    ((Z₂.isClopen_pointSet hf).2.sdiff (Z₁.isClopen_pointSet hf).1)
    ((Z₂.isClopen_pointSet hf).1.sdiff (Z₁.isClopen_pointSet hf).2)
    Set.diff_subset

/-- **Stacks 04PI, the operation `⋆₂`.** On points, `⋆₂(s, s')` is the intersection
`Z₁ ∩ Z₂`. -/
@[simp, stacks 04PI "star_2_on_points"]
theorem pointSet_star₂ : (star₂ hf Z₁ Z₂).pointSet = Z₁.pointSet ∩ Z₂.pointSet :=
  pointSet_ofClopenSubset _ _ _ _ _

/-- **Stacks 04PI, the operation `⋆₃`.** On points, `⋆₃(s, s')` is the difference
`Z₁ ∖ Z₂`. -/
@[simp, stacks 04PI "star_3_on_points"]
theorem pointSet_star₃ : (star₃ hf Z₁ Z₂).pointSet = Z₁.pointSet \ Z₂.pointSet :=
  pointSet_ofClopenSubset _ _ _ _ _

/-- **Stacks 04PI, the operation `⋆₄`.** On points, `⋆₄(s, s')` is the difference
`Z₂ ∖ Z₁`. -/
@[simp, stacks 04PI "star_4_on_points"]
theorem pointSet_star₄ : (star₄ hf Z₁ Z₂).pointSet = Z₂.pointSet \ Z₁.pointSet :=
  pointSet_ofClopenSubset _ _ _ _ _

/-- The intersection of two sections is contained in the first. -/
theorem star₂_le_left : (star₂ hf Z₁ Z₂).subspace ≤ Z₁.subspace :=
  subspace_le_of_pointSet_subset (by rw [pointSet_star₂]; exact Set.inter_subset_left)

/-- The intersection of two sections is contained in the second. -/
theorem star₂_le_right : (star₂ hf Z₁ Z₂).subspace ≤ Z₂.subspace :=
  subspace_le_of_pointSet_subset (by rw [pointSet_star₂]; exact Set.inter_subset_right)

/-- **Stacks 04PI.** `Z₁ ∩ Z₂` is open inside `Z₁`. -/
@[stacks 04PI "intersection_open_in_left"]
theorem isOpenImmersion_star₂_le_left :
    IsOpenImmersion B S hS (Subfunctor.homOfLe (star₂_le_left hf Z₁ Z₂)) :=
  isOpenImmersion_homOfLe B S hS (star₂ hf Z₁ Z₂).isOpen.2 _

/-- **Stacks 04PI.** `Z₁ ∩ Z₂` is closed inside `Z₁`. -/
@[stacks 04PI "intersection_closed_in_left"]
theorem isClosedImmersion_star₂_le_left :
    IsClosedImmersion B S hS (Subfunctor.homOfLe (star₂_le_left hf Z₁ Z₂)) :=
  isClosedImmersion_homOfLe B S hS ⟨_, (star₂ hf Z₁ Z₂).isClosedSubspace hf⟩ _

/-- **Stacks 04PI.** `Z₁ ∩ Z₂` is open inside `Z₂`. -/
@[stacks 04PI "intersection_open_in_right"]
theorem isOpenImmersion_star₂_le_right :
    IsOpenImmersion B S hS (Subfunctor.homOfLe (star₂_le_right hf Z₁ Z₂)) :=
  isOpenImmersion_homOfLe B S hS (star₂ hf Z₁ Z₂).isOpen.2 _

/-- **Stacks 04PI.** `Z₁ ∩ Z₂` is closed inside `Z₂`. -/
@[stacks 04PI "intersection_closed_in_right"]
theorem isClosedImmersion_star₂_le_right :
    IsClosedImmersion B S hS (Subfunctor.homOfLe (star₂_le_right hf Z₁ Z₂)) :=
  isClosedImmersion_homOfLe B S hS ⟨_, (star₂ hf Z₁ Z₂).isClosedSubspace hf⟩ _

/-- **Stacks 04PI.** The zero section `0 = (a, ∅)` of the `F₂`-algebra: the empty open
subspace, which is finite over `T`. -/
@[stacks 04PI "zero_of_the_f2_algebra"]
def zero : FinitePartFibre B S hS f a :=
  Z₁.ofClopenSubset ∅ isOpen_empty isClosed_empty (Set.empty_subset _)

/-- The point set of the zero section is empty. -/
@[simp]
theorem pointSet_zero : (zero Z₁).pointSet = (∅ : Set (points B S hS (pullback a.hom f.hom))) :=
  pointSet_ofClopenSubset _ _ _ _ _

/-- **Stacks 04PI.** The open subspace of the zero section is the empty one, so `0 = (a, ∅)`.

The empty open subspace of an algebraic space is the sheafification of the bottom subfunctor
and not the bottom subfunctor itself, whose sections over an object of the site with no points
are not those of a sheaf. -/
@[stacks 04PI "zero_is_the_empty_subspace"]
theorem subspace_zero : (zero Z₁).subspace =
    (⊥ : Subfunctor (pullback a.hom f.hom)).sheafify (BigFppfOver.topology B S hS) :=
  openSubspaceOfPoints_empty B S hS _

/-- The zero section does not depend on the section used to produce it. -/
theorem zero_eq_zero (Z₁ Z₂ : FinitePartFibre B S hS f a) : zero Z₁ = zero Z₂ :=
  ext_pointSet (by rw [pointSet_zero, pointSet_zero])

/-- **Stacks 04PI, the unit of the finite case.** When `f` is finite the section
`1 = (a, T ×_Y X)` cut out by all of the points of `T ×_Y X`, which is the restriction along
`a` of the pair `(1_Y, X)`. -/
@[stacks 04PI "unit_of_finite"]
def one (hfin : IsFinite B S hS f.hom) : FinitePartFibre B S hS f a :=
  ofClopen (isFinite_pullback_fst_of_isFinite B S hS f hfin a) Set.univ isOpen_univ
    isClosed_univ

/-- For `f` finite, the point set of the unit section is the set of all points of `T ×_Y X`. -/
@[simp]
theorem pointSet_one (hfin : IsFinite B S hS f.hom) :
    (one (a := a) hfin).pointSet = (Set.univ : Set (points B S hS (pullback a.hom f.hom))) :=
  pointSet_ofClopen _ _ _ _

/-- **Stacks 04PI, the unit of the finite case.** The open subspace of the unit is the whole
of `T ×_Y X`, so `1` is the restriction along `a` of the pair `(1_Y, X)`. -/
@[stacks 04PI "unit_is_the_whole_fibre_product"]
theorem subspace_one (hfin : IsFinite B S hS f.hom) :
    (one (a := a) hfin).subspace = ⊤ :=
  openSubspaceOfPoints_univ B S hS _

/-- **Stacks 04PI, the unit of the finite case.** `1 s = s`. -/
@[stacks 04PI "unit_of_finite_is_unit"]
theorem star₂_one (hfin : IsFinite B S hS f.hom) : star₂ hf (one hfin) Z₁ = Z₁ :=
  ext_pointSet (by rw [pointSet_star₂, pointSet_one, Set.univ_inter])

/-- **Stacks 04PI, the unit of the finite case.** `s 1 = s`. -/
theorem star₂_one' (hfin : IsFinite B S hS f.hom) : star₂ hf Z₁ (one hfin) = Z₁ :=
  ext_pointSet (by rw [pointSet_star₂, pointSet_one, Set.inter_univ])

/-- **Stacks 04PI.** The multiplication `s s' = ⋆₂(s, s')` is commutative. -/
@[stacks 04PI "multiplication_is_commutative"]
theorem star₂_comm : star₂ hf Z₁ Z₂ = star₂ hf Z₂ Z₁ :=
  ext_pointSet (by rw [pointSet_star₂, pointSet_star₂, Set.inter_comm])

/-- **Stacks 04PI.** The multiplication `s s' = ⋆₂(s, s')` is associative. -/
@[stacks 04PI "multiplication_is_associative"]
theorem star₂_assoc (Z₃ : FinitePartFibre B S hS f a) :
    star₂ hf (star₂ hf Z₁ Z₂) Z₃ = star₂ hf Z₁ (star₂ hf Z₂ Z₃) :=
  ext_pointSet (by simp only [pointSet_star₂, Set.inter_assoc])

/-- **Stacks 04PI.** The multiplication `s s' = ⋆₂(s, s')` is idempotent, as it must be in an
`F₂`-algebra of this kind. -/
theorem star₂_self : star₂ hf Z₁ Z₁ = Z₁ :=
  ext_pointSet (by rw [pointSet_star₂, Set.inter_self])

/-- **Stacks 04PI.** The zero section is absorbing for the multiplication. -/
theorem star₂_zero : star₂ hf Z₁ (zero Z₁) = zero Z₁ :=
  ext_pointSet (by rw [pointSet_star₂, pointSet_zero, Set.inter_empty])

/-- **Stacks 04PI.** `⋆₃(s, s) = 0`: a section differs from itself in nothing. -/
theorem star₃_self : star₃ hf Z₁ Z₁ = zero Z₁ :=
  ext_pointSet (by rw [pointSet_star₃, pointSet_zero, Set.diff_self])

/-- **Stacks 04PI.** `⋆₄(s, s) = 0`. -/
theorem star₄_self : star₄ hf Z₁ Z₁ = zero Z₁ :=
  ext_pointSet (by rw [pointSet_star₄, pointSet_zero, Set.diff_self])

/-- **Stacks 04PI.** `⋆₃(s, 0) = s`. -/
theorem star₃_zero : star₃ hf Z₁ (zero Z₁) = Z₁ :=
  ext_pointSet (by rw [pointSet_star₃, pointSet_zero, Set.diff_empty])

/-- **Stacks 04PI.** `⋆₄(0, s) = s`. -/
theorem star₄_zero : star₄ hf (zero Z₁) Z₁ = Z₁ :=
  ext_pointSet (by rw [pointSet_star₄, pointSet_zero, Set.diff_empty])

/-- **Stacks 04PI.** `⋆₂` distributes over `⋆₃`, which is the distributivity of the
multiplication over the difference. -/
theorem star₂_star₃ (Z₃ : FinitePartFibre B S hS f a) :
    star₂ hf (star₃ hf Z₁ Z₂) Z₃ = star₃ hf (star₂ hf Z₁ Z₃) (star₂ hf Z₂ Z₃) :=
  ext_pointSet (by
    simp only [pointSet_star₂, pointSet_star₃]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_diff]
    tauto)

/-- The three pieces `Z₁ ∖ Z₂`, `Z₁ ∩ Z₂` and `Z₂ ∖ Z₁` are pairwise disjoint on points. -/
theorem pointSet_star₃_disjoint_star₂ :
    Disjoint (star₃ hf Z₁ Z₂).pointSet (star₂ hf Z₁ Z₂).pointSet := by
  rw [pointSet_star₃, pointSet_star₂]
  exact Set.disjoint_left.2 fun _ hx hx' => hx.2 hx'.2

/-- The three pieces `Z₁ ∖ Z₂`, `Z₁ ∩ Z₂` and `Z₂ ∖ Z₁` are pairwise disjoint on points. -/
theorem pointSet_star₂_disjoint_star₄ :
    Disjoint (star₂ hf Z₁ Z₂).pointSet (star₄ hf Z₁ Z₂).pointSet := by
  rw [pointSet_star₄, pointSet_star₂]
  exact Set.disjoint_left.2 fun _ hx hx' => hx'.2 hx.1

/-- The three pieces `Z₁ ∖ Z₂`, `Z₁ ∩ Z₂` and `Z₂ ∖ Z₁` are pairwise disjoint on points. -/
theorem pointSet_star₃_disjoint_star₄ :
    Disjoint (star₃ hf Z₁ Z₂).pointSet (star₄ hf Z₁ Z₂).pointSet := by
  rw [pointSet_star₃, pointSet_star₄]
  exact Set.disjoint_left.2 fun _ hx hx' => hx.2 hx'.1

end Operations

end FinitePartFibre

end AlgebraicGeometry.Space

end
