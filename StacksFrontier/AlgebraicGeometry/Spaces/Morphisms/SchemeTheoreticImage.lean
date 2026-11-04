module

public import StacksFrontier.AlgebraicGeometry.Descent.ClosedImmersionEffectiveDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedFactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroScheme

/-!
# Scheme-theoretic images of morphisms of algebraic spaces (Stacks 082X)

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`. Stacks 082X asserts that there is a smallest closed subspace of `Y` through which
`f` factors. It is constructed here as the intersection, in the complete lattice of
subfunctors of `Y`, of all the closed subspaces of `Y` containing the image of `f`:

`Z = ⨅ {Z' closed subspace of Y ∣ range f ≤ Z'}`.

Factorization and minimality are then the two halves of the universal property of an
infimum, and the only substance is that `Z` is again a closed subspace, which is
`AlgebraicGeometry.Space.isClosedSubspace_sInf`. No quasi-coherent ideal sheaf is used, so
nothing here depends on the part of Stacks 03MB which produces a closed subspace from a
prescribed quasi-coherent ideal and which the library does not have; the construction is the
one `AlgebraicGeometry.Space.unionSubfunctor` of Stacks 0CYZ and
`AlgebraicGeometry.Space.zeroSchemeSubfunctor` of Stacks 0845 already use.

Factoring through a closed subspace is expressed by containment of the range subfunctor,
`CategoryTheory.Subfunctor.range f ≤ Z`, which for a subfunctor is equivalent to the existence
of a factorization through its inclusion; the factorization itself is
`CategoryTheory.Subfunctor.lift` and is named here
`AlgebraicGeometry.Space.toSchemeTheoreticImage`.

Stacks 0CP2, functoriality, follows: given a commutative square with vertical maps
`p : X₁ ⟶ X₂` and `q : Y₁ ⟶ Y₂`, the image of `f₁` lands in the inverse image of the image of
`f₂` along `q` — a closed subspace of `Y₁` by Stacks 083Q — so minimality of the image of `f₁`
provides the induced morphism, and both squares of Stacks 0CP2's diagram commute. The induced
morphism is unique because the inclusion of a subfunctor is a monomorphism.

For a morphism out of a *reduced* algebraic space the scheme-theoretic image is the reduced
closed subspace supported on the closure of the image of the point map, which is Stacks 0830,
part (1). The uniqueness half needs no descent and is
`AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_eq_of_isReduced_of_range_pointsMap_eq`:
*any* closed subspace of `Y` which is étale-locally reduced and whose point set is that closure
is the scheme-theoretic image. Both inequalities come from Stacks 03JJ, that a morphism out of
a reduced algebraic space factors through a closed subspace as soon as its point set does: one
direction factors the morphism through the given reduced closed subspace, so that minimality of
the scheme-theoretic image applies, the other factors the inclusion of the reduced closed
subspace through the scheme-theoretic image, whose point set is closed by Stacks 04CD.

The remaining ingredient is the *existence* of a reduced closed subspace on a closed set of
points, which is Stacks 03IQ:
`StacksFrontier/AlgebraicGeometry/Spaces/ReducedClosedSubspace.lean` proves
`AlgebraicGeometry.Space.reducedClosedSubspace` to be a closed subspace from effective descent
for closed immersions along the surjective étale morphisms of the site, and that descent holds
outright, by
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion`. So part (1)
of Stacks 0830 is unconditional and is
`AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_eq_reducedClosedSubspace`.

Part (2) of Stacks 0830, the compatibility with étale base change of the target, follows: the
inverse image along an étale morphism `g : V ⟶ Y` of the reduced closed subspace on a closed set
`T` is a closed subspace, étale-locally reduced, with point set the preimage of `T`, hence is the
reduced closed subspace there by the uniqueness half of Stacks 03IQ; and the preimage of the
closure of the image of `f` is the closure of the image of the base change of `f`, because the
point map of an étale morphism of algebraic spaces is open. The easy half for an arbitrary
commutative square rather than an étale base change is
`AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_le_preimage`.

## Main definitions

* `AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor`: the scheme-theoretic image of
  **Stacks 082X** as a subfunctor of the target, and
  `AlgebraicGeometry.Space.schemeTheoreticImage` the same bundled as an
  `AlgebraicGeometry.Space.ClosedSubspaces`.
* `AlgebraicGeometry.Space.toSchemeTheoreticImage`: the factorization of the morphism through
  its scheme-theoretic image.
* `AlgebraicGeometry.Space.schemeTheoreticImageMap`: the morphism of scheme-theoretic images
  induced by a commutative square, **Stacks 0CP2**.

## Main results

* `AlgebraicGeometry.Space.isClosedSubspace_schemeTheoreticImageSubfunctor`,
  `AlgebraicGeometry.Space.range_le_schemeTheoreticImageSubfunctor` and
  `AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_le` are the three assertions of
  **Stacks 082X**: the scheme-theoretic image is a closed subspace, the morphism factors
  through it, and it is contained in every closed subspace the morphism factors through.
* `AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_le_preimage`: in a commutative
  square, the scheme-theoretic image of the upper horizontal morphism is contained in the
  inverse image of the scheme-theoretic image of the lower one.
* `AlgebraicGeometry.Space.schemeTheoreticImageMap_ι` and
  `AlgebraicGeometry.Space.toSchemeTheoreticImage_comp_schemeTheoreticImageMap` are the right
  and left squares of **Stacks 0CP2**, and
  `AlgebraicGeometry.Space.eq_schemeTheoreticImageMap` the uniqueness of the induced
  morphism.
* `AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_eq_of_isReduced_of_range_pointsMap_eq`:
  a closed subspace which is étale-locally reduced and whose point set is the closure of the
  image of the point map of a morphism out of a reduced algebraic space is the scheme-theoretic
  image of that morphism. This is the uniqueness half of part (1) of Stacks 0830 and needs no
  descent.
* `AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_eq_reducedClosedSubspace` is **part
  (1) of Stacks 0830**: the scheme-theoretic image of a morphism out of a reduced algebraic
  space is the reduced closed subspace on the closure of the image of its point map.
* `AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_pullback_snd_of_isEtale` is **part (2)
  of Stacks 0830**: the scheme-theoretic image commutes with étale base change of the target.

## Implementation notes

`AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor` is defined for an arbitrary morphism
of presheaves on the big fppf category over `S`, as the predicates of
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms.lean` are; algebraicity of the target is
needed only for the closedness assertion and is a hypothesis of that theorem rather than of
the definition. Consequently minimality and the factorization hold with no algebraicity
hypothesis at all, and a consumer which already knows a closed subspace through which the
morphism factors needs none.

The induced morphism of Stacks 0CP2 is built from
`CategoryTheory.Subfunctor.fromPreimage`, the projection of an inverse image, rather than
from a chosen fibre product, matching
`StacksFrontier/AlgebraicGeometry/Spaces/SubspacePreimage.lean`.

## References

* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 03JJ](https://stacks.math.columbia.edu/tag/03JJ)
* [Stacks Project, Tag 04CD](https://stacks.math.columbia.edu/tag/04CD)
* [Stacks Project, Tag 082X](https://stacks.math.columbia.edu/tag/082X)
* [Stacks Project, Tag 0830](https://stacks.math.columbia.edu/tag/0830)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 0CP2](https://stacks.math.columbia.edu/tag/0CP2)
* [Stacks Project, Tag 0CYZ](https://stacks.math.columbia.edu/tag/0CYZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The scheme-theoretic image -/

section Image

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 082X.** The scheme-theoretic image of a morphism of algebraic spaces over `S`:
the intersection of all closed subspaces of the target containing the image of the
morphism. -/
@[stacks 082X "underlying subfunctor construction", stacks 082Y "the scheme-theoretic image"]
def schemeTheoreticImageSubfunctor (f : X ⟶ Y) : Subfunctor Y :=
  sInf {Z : Subfunctor Y | IsClosedSubspace B S hS Z ∧ Subfunctor.range f ≤ Z}

/-- **Stacks 082X.** A morphism of algebraic spaces over `S` factors through its
scheme-theoretic image. -/
@[stacks 082X "the morphism factors through the image"]
theorem range_le_schemeTheoreticImageSubfunctor (f : X ⟶ Y) :
    Subfunctor.range f ≤ schemeTheoreticImageSubfunctor B S hS f :=
  le_sInf fun _ hZ => hZ.2

/-- **Stacks 082X.** The scheme-theoretic image is contained in every closed subspace of the
target through which the morphism factors. -/
@[stacks 082X "minimality of the image"]
theorem schemeTheoreticImageSubfunctor_le (f : X ⟶ Y) {Z : Subfunctor Y}
    (hZ : IsClosedSubspace B S hS Z) (hfZ : Subfunctor.range f ≤ Z) :
    schemeTheoreticImageSubfunctor B S hS f ≤ Z :=
  sInf_le ⟨hZ, hfZ⟩

/-- **Stacks 082X.** The scheme-theoretic image is a closed subspace of the target. -/
@[stacks 082X "the image is a closed subspace"]
theorem isClosedSubspace_schemeTheoreticImageSubfunctor (f : X ⟶ Y)
    (hY : IsAlgebraicSpace B S hS Y) :
    IsClosedSubspace B S hS (schemeTheoreticImageSubfunctor B S hS f) :=
  isClosedSubspace_sInf B S hS hY _ fun _ hZ => hZ.1

/-- The scheme-theoretic image of Stacks 082X, bundled as a closed subspace of the target. -/
def schemeTheoreticImage (f : X ⟶ Y) (hY : IsAlgebraicSpace B S hS Y) :
    ClosedSubspaces B S hS Y :=
  ⟨schemeTheoreticImageSubfunctor B S hS f,
    isClosedSubspace_schemeTheoreticImageSubfunctor B S hS f hY⟩

/-- The factorization of a morphism through its scheme-theoretic image. -/
def toSchemeTheoreticImage (f : X ⟶ Y) :
    X ⟶ (schemeTheoreticImageSubfunctor B S hS f).toFunctor :=
  Subfunctor.lift f (range_le_schemeTheoreticImageSubfunctor B S hS f)

/-- The factorization of `f` through its scheme-theoretic image, followed by the inclusion of
the image into the target, is `f`. -/
@[simp]
theorem toSchemeTheoreticImage_ι (f : X ⟶ Y) :
    toSchemeTheoreticImage B S hS f ≫ (schemeTheoreticImageSubfunctor B S hS f).ι = f :=
  Subfunctor.lift_ι _ _

end Image

/-! ### Functoriality of the scheme-theoretic image -/

section Functoriality

variable {X₁ Y₁ X₂ Y₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂} {p : X₁ ⟶ X₂} {q : Y₁ ⟶ Y₂}

/-- In a commutative square, the image of the upper horizontal morphism lands in the inverse
image of the scheme-theoretic image of the lower one. -/
theorem range_le_preimage_schemeTheoreticImageSubfunctor (hsq : f₁ ≫ q = p ≫ f₂) :
    Subfunctor.range f₁ ≤ (schemeTheoreticImageSubfunctor B S hS f₂).preimage q := by
  rintro U x ⟨y, rfl⟩
  show q.app U (f₁.app U y) ∈ (schemeTheoreticImageSubfunctor B S hS f₂).obj U
  rw [show q.app U (f₁.app U y) = f₂.app U (p.app U y) by
    simpa using congrArg (fun k : X₁ ⟶ Y₂ => k.app U y) hsq]
  exact range_le_schemeTheoreticImageSubfunctor B S hS f₂ U ⟨_, rfl⟩

/-- In a commutative square, the scheme-theoretic image of the upper horizontal morphism is
contained in the inverse image of the scheme-theoretic image of the lower one: the latter is a
closed subspace by Stacks 083Q, and the upper horizontal morphism factors through it.

For an étale morphism `q` of algebraic spaces this is one half of part (2) of Stacks 0830; the
reverse inclusion is not proved. -/
theorem schemeTheoreticImageSubfunctor_le_preimage (hY₁ : IsAlgebraicSpace B S hS Y₁)
    (hY₂ : IsAlgebraicSpace B S hS Y₂) (hsq : f₁ ≫ q = p ≫ f₂) :
    schemeTheoreticImageSubfunctor B S hS f₁ ≤
      (schemeTheoreticImageSubfunctor B S hS f₂).preimage q :=
  schemeTheoreticImageSubfunctor_le B S hS f₁
    (isClosedSubspace_preimage B S hS q _ hY₂ hY₁
      (isClosedSubspace_schemeTheoreticImageSubfunctor B S hS f₂ hY₂))
    (range_le_preimage_schemeTheoreticImageSubfunctor B S hS hsq)

/-- **Stacks 0CP2.** The morphism of scheme-theoretic images induced by a commutative square
of algebraic spaces over `S`. -/
@[stacks 0CP2 "the induced morphism of scheme-theoretic images"]
def schemeTheoreticImageMap (hY₁ : IsAlgebraicSpace B S hS Y₁)
    (hY₂ : IsAlgebraicSpace B S hS Y₂) (hsq : f₁ ≫ q = p ≫ f₂) :
    (schemeTheoreticImageSubfunctor B S hS f₁).toFunctor ⟶
      (schemeTheoreticImageSubfunctor B S hS f₂).toFunctor :=
  Subfunctor.homOfLe (schemeTheoreticImageSubfunctor_le_preimage B S hS hY₁ hY₂ hsq) ≫
    (schemeTheoreticImageSubfunctor B S hS f₂).fromPreimage q

/-- **Stacks 0CP2**, the right square: the induced morphism of scheme-theoretic images is
compatible with their inclusions into the targets. -/
@[stacks 0CP2 "the right square"]
theorem schemeTheoreticImageMap_ι (hY₁ : IsAlgebraicSpace B S hS Y₁)
    (hY₂ : IsAlgebraicSpace B S hS Y₂) (hsq : f₁ ≫ q = p ≫ f₂) :
    schemeTheoreticImageMap B S hS hY₁ hY₂ hsq ≫
        (schemeTheoreticImageSubfunctor B S hS f₂).ι =
      (schemeTheoreticImageSubfunctor B S hS f₁).ι ≫ q := by
  rw [schemeTheoreticImageMap, Category.assoc, Subfunctor.fromPreimage_ι,
    ← Category.assoc, Subfunctor.homOfLe_ι]

/-- The morphism of scheme-theoretic images compatible with the inclusions into the targets is
unique, the inclusion of a subfunctor being a monomorphism. -/
theorem eq_schemeTheoreticImageMap (hY₁ : IsAlgebraicSpace B S hS Y₁)
    (hY₂ : IsAlgebraicSpace B S hS Y₂) (hsq : f₁ ≫ q = p ≫ f₂)
    (h : (schemeTheoreticImageSubfunctor B S hS f₁).toFunctor ⟶
      (schemeTheoreticImageSubfunctor B S hS f₂).toFunctor)
    (hh : h ≫ (schemeTheoreticImageSubfunctor B S hS f₂).ι =
      (schemeTheoreticImageSubfunctor B S hS f₁).ι ≫ q) :
    h = schemeTheoreticImageMap B S hS hY₁ hY₂ hsq :=
  (cancel_mono (schemeTheoreticImageSubfunctor B S hS f₂).ι).1
    (hh.trans (schemeTheoreticImageMap_ι B S hS hY₁ hY₂ hsq).symm)

/-- **Stacks 0CP2**, the left square: a morphism of scheme-theoretic images compatible with the
inclusions into the targets is also compatible with the factorizations of the horizontal
morphisms through their images. -/
@[stacks 0CP2 "the left square"]
theorem toSchemeTheoreticImage_comp_schemeTheoreticImageMap (hsq : f₁ ≫ q = p ≫ f₂)
    (h : (schemeTheoreticImageSubfunctor B S hS f₁).toFunctor ⟶
      (schemeTheoreticImageSubfunctor B S hS f₂).toFunctor)
    (hh : h ≫ (schemeTheoreticImageSubfunctor B S hS f₂).ι =
      (schemeTheoreticImageSubfunctor B S hS f₁).ι ≫ q) :
    toSchemeTheoreticImage B S hS f₁ ≫ h = p ≫ toSchemeTheoreticImage B S hS f₂ := by
  refine (cancel_mono (schemeTheoreticImageSubfunctor B S hS f₂).ι).1 ?_
  rw [Category.assoc, hh, ← Category.assoc, toSchemeTheoreticImage_ι, Category.assoc,
    toSchemeTheoreticImage_ι]
  exact hsq

end Functoriality

/-! ### The scheme-theoretic image of a reduced algebraic space -/

section Reduced

attribute [local instance] pointTopology

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A morphism that factors through the inclusion of a subfunctor has range inside it. -/
private theorem range_le_of_comp_ι_eq {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Z : Subfunctor G}
    {f : F ⟶ G} (g : F ⟶ Z.toFunctor) (hg : g ≫ Z.ι = f) : Subfunctor.range f ≤ Z := by
  simpa only [hg, Subfunctor.range_ι] using Subfunctor.range_comp_le g Z.ι

/-- In a pullback square the preimage of the range of the point map of `p` along `|h|` is the
range of the point map of `p'`. -/
private theorem preimage_range_pointsMap_of_isPullback {W W' Z Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {c : W' ⟶ W} {p' : W' ⟶ Z'} {p : W ⟶ Z} {h : Z' ⟶ Z} (sq : IsPullback c p' p h) :
    pointsMap B S hS Z' h ⁻¹' Set.range (pointsMap B S hS W p) =
      Set.range (pointsMap B S hS W' p') := by
  rw [← Set.image_univ (f := pointsMap B S hS W p),
    preimage_image_pointsMap_of_isPullback B S hS sq Set.univ, Set.preimage_univ, Set.image_univ]

/-- The point set of the scheme-theoretic image is closed and contains the image of the point
map of the morphism, hence contains its closure. -/
theorem closure_range_pointsMap_subset_range_pointsMap_schemeTheoreticImage (f : X ⟶ Y)
    (hY : IsAlgebraicSpace B S hS Y) :
    closure (Set.range (pointsMap B S hS X f)) ⊆
      Set.range (pointsMap B S hS (schemeTheoreticImageSubfunctor B S hS f).toFunctor
        (schemeTheoreticImageSubfunctor B S hS f).ι) := by
  refine closure_minimal ?_ (isClosed_range_pointsMap_of_isClosedImmersion B S hS hY _
    (isClosedSubspace_schemeTheoreticImageSubfunctor B S hS f hY).2)
  conv_lhs => rw [← toSchemeTheoreticImage_ι B S hS f,
    pointsMap_comp B S hS X (toSchemeTheoreticImage B S hS f)
      (schemeTheoreticImageSubfunctor B S hS f).ι]
  exact Set.range_comp_subset_range _ _

/-- **The uniqueness half of part (1) of Stacks 0830.** A closed subspace of `Y` which is
étale-locally reduced and whose set of points is the closure of the image of the point map of
`f` *is* the scheme-theoretic image of `f`, provided the source of `f` is a reduced algebraic
space. Since
the scheme-theoretic image is a closed subspace by Stacks 082X, this says that it is the
reduced induced structure on the closure of the image of `f`.

Both inequalities are Stacks 03JJ, that a morphism out of a reduced algebraic space factors
through a closed subspace as soon as its point map does. In one direction it factors `f`
through `Z`, so that minimality of the scheme-theoretic image applies; in the other it factors
the inclusion of `Z` through the scheme-theoretic image, whose set of points is closed by
Stacks 04CD and contains the image of the point map of `f`.

No descent hypothesis is needed, and none of the two reducedness hypotheses can be dropped:
without `hXred` the scheme-theoretic image can be a nonreduced subspace of the same support,
and `hZred` is what makes the inclusion of `Z` factor through it. The tag sits on
`AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_eq_reducedClosedSubspace` instead,
because part (1) asserts in addition that such a `Z` exists, which is Stacks 03IQ. -/
theorem schemeTheoreticImageSubfunctor_eq_of_isReduced_of_range_pointsMap_eq (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hXred : HasEtaleLocalProperty B S hS X (fun W : Scheme.{u} => IsReduced W))
    {Z : Subfunctor Y} (hZ : IsClosedSubspace B S hS Z)
    (hZred : HasEtaleLocalProperty B S hS Z.toFunctor (fun W : Scheme.{u} => IsReduced W))
    (hZT : Set.range (pointsMap B S hS Z.toFunctor Z.ι) =
      closure (Set.range (pointsMap B S hS X f))) :
    schemeTheoreticImageSubfunctor B S hS f = Z := by
  refine le_antisymm ?_ ?_
  · obtain ⟨g, hg⟩ := (exists_lift_closedSubspace_iff_pointsMap_range_subset B S hS hY hX
      Z hZ hXred f).2 (by rw [hZT]; exact subset_closure)
    exact schemeTheoreticImageSubfunctor_le B S hS f hZ (range_le_of_comp_ι_eq B S hS g hg)
  · obtain ⟨g, hg⟩ := (exists_lift_closedSubspace_iff_pointsMap_range_subset B S hS hY hZ.1
      (schemeTheoreticImageSubfunctor B S hS f)
      (isClosedSubspace_schemeTheoreticImageSubfunctor B S hS f hY) hZred Z.ι).2
      (by
        rw [hZT]
        exact closure_range_pointsMap_subset_range_pointsMap_schemeTheoreticImage B S hS f hY)
    simpa only [Subfunctor.range_ι] using range_le_of_comp_ι_eq B S hS g hg

/-- **Stacks 0830, part (1).** The scheme-theoretic image of a morphism out of a reduced
algebraic space is the reduced closed subspace supported on the closure of the image of its
point map.

The identification itself is
`AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_eq_of_isReduced_of_range_pointsMap_eq`,
which needs no descent; what it has to be fed is that
`AlgebraicGeometry.Space.reducedClosedSubspace` is a closed subspace, the existence half of
Stacks 03IQ. That comes from
`AlgebraicGeometry.Space.isClosedSubspace_reducedClosedSubspace`
together with
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion`, effective
descent for closed immersions along the surjective étale morphisms of the site. -/
@[stacks 0830 "part (1): the image is the reduced induced structure on the closure"]
theorem schemeTheoreticImageSubfunctor_eq_reducedClosedSubspace (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hXred : HasEtaleLocalProperty B S hS X (fun W : Scheme.{u} => IsReduced W)) :
    schemeTheoreticImageSubfunctor B S hS f =
      reducedClosedSubspace B S hS Y hY
        (closure (Set.range (pointsMap B S hS X f))) isClosed_closure :=
  schemeTheoreticImageSubfunctor_eq_of_isReduced_of_range_pointsMap_eq B S hS f hX hY hXred
    (isClosedSubspace_reducedClosedSubspace B S hS Y hY _ isClosed_closure)
    (hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS Y hY _ isClosed_closure)
    (range_pointsMap_ι_reducedClosedSubspace B S hS Y hY _ isClosed_closure)

/-- An étale-local property of schemes passes from an algebraic space to any algebraic space
étale over it: every étale chart of the source becomes, after composition with the étale
morphism, an étale chart of the target, and by Stacks 03E8 the property may be tested on all
étale charts. -/
theorem hasEtaleLocalProperty_of_isEtale {P : ObjectProperty Scheme.{u}}
    [P.IsLocal Scheme.etalePrecoverage] {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) {h : F ⟶ G}
    (hh : IsEtale B S hS h) (hP : HasEtaleLocalProperty B S hS G P) :
    HasEtaleLocalProperty B S hS F P :=
  (exists_atlas_iff_forall_etale B S hS F P hF).2 fun W φ hφ =>
    (exists_atlas_iff_forall_etale B S hS G P hG).1 hP W (φ ≫ h) (hh W φ hφ)

/-- **Stacks 0830, part (2).** The scheme-theoretic image of a morphism out of a reduced
algebraic space commutes with étale base change of the target: for an étale morphism
`g : V ⟶ Y`, the scheme-theoretic image of `X ×_Y V ⟶ V` is the inverse image along `g` of the
scheme-theoretic image of `f`.

By part (1) both sides are reduced closed subspaces, so it is enough to identify their point
sets and appeal to the uniqueness half of Stacks 03IQ,
`AlgebraicGeometry.Space.eq_reducedClosedSubspace`. The inverse image along `g` of the reduced
closed subspace on the closure of the image of `f` is a closed subspace by Stacks 083Q, is
étale-locally reduced because its projection to that subspace is a base change of `g`, hence
étale, and has point set the preimage along `|g|` of that closure. That preimage is the closure
of the image of `X ×_Y V ⟶ V`, because `|g|` is open by Stacks 03IR and the image of
`X ×_Y V ⟶ V` is the preimage along `|g|` of the image of `f` by Stacks 03H4. -/
@[stacks 0830 "part (2): compatibility with étale base change of the target"]
theorem schemeTheoreticImageSubfunctor_pullback_snd_of_isEtale
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (g : V ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hV : IsAlgebraicSpace B S hS V)
    (hXred : HasEtaleLocalProperty B S hS X (fun W : Scheme.{u} => IsReduced W))
    (hg : IsEtale B S hS g) :
    schemeTheoreticImageSubfunctor B S hS (pullback.snd f g) =
      (schemeTheoreticImageSubfunctor B S hS f).preimage g := by
  have hXV : IsAlgebraicSpace B S hS (pullback f g) :=
    isAlgebraicSpace_pullback B S hS f g hX hV hY
  have hsq : IsPullback (pullback.fst f g) (pullback.snd f g) f g := IsPullback.of_hasPullback f g
  -- `X ×_Y V` is étale over `X`, hence reduced.
  have hfst : IsEtale B S hS (pullback.fst f g) :=
    isEtale_of_isPullback B S hS _ _ _ _
      (AlgebraicSpaces.isPullback_fiberProduct B S hS
        (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
        (ObjectProperty.homMk g : (⟨V, hV⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)).flip hg
  have hXVred : HasEtaleLocalProperty B S hS (pullback f g)
      (fun W : Scheme.{u} => IsReduced W) :=
    hasEtaleLocalProperty_of_isEtale B S hS hXV hX hfst hXred
  -- The image of the base change is the preimage of the image, and `|g|` is open.
  have hrange : pointsMap B S hS V g ⁻¹' Set.range (pointsMap B S hS X f) =
      Set.range (pointsMap B S hS (pullback f g) (pullback.snd f g)) :=
    preimage_range_pointsMap_of_isPullback B S hS hsq
  have hclosure : closure (Set.range (pointsMap B S hS (pullback f g) (pullback.snd f g))) =
      pointsMap B S hS V g ⁻¹' closure (Set.range (pointsMap B S hS X f)) := by
    rw [← hrange]
    exact ((isOpenMap_pointsMap_of_isEtale B S hS g hV hY hg).preimage_closure_eq_closure_preimage
      (continuous_pointsMap B S hS g) _).symm
  -- The inverse image of the reduced closed subspace on the closure is a reduced closed
  -- subspace with that preimage as point set.
  set Z := reducedClosedSubspace B S hS Y hY (closure (Set.range (pointsMap B S hS X f)))
    isClosed_closure with hZdef
  have hZc : IsClosedSubspace B S hS Z :=
    isClosedSubspace_reducedClosedSubspace B S hS Y hY _ isClosed_closure
  have hZpre : IsClosedSubspace B S hS (Z.preimage g) :=
    isClosedSubspace_preimage B S hS g Z hY hV hZc
  have hpreSq : IsPullback (Z.fromPreimage g) (Z.preimage g).ι Z.ι g :=
    Subfunctor.isPullback_preimage g Z
  have hfromEtale : IsEtale B S hS (Z.fromPreimage g) :=
    isEtale_of_isPullback B S hS _ _ _ _
      (show IsPullback
          (ObjectProperty.homMk (Z.fromPreimage g) :
            (⟨(Z.preimage g).toFunctor, hZpre.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Z.toFunctor, hZc.1⟩)
          (ObjectProperty.homMk (Z.preimage g).ι : _ ⟶ ⟨V, hV⟩)
          (ObjectProperty.homMk Z.ι : _ ⟶ ⟨Y, hY⟩)
          (ObjectProperty.homMk g : (⟨V, hV⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩) from
        IsPullback.of_map_of_faithful
          (F := ObjectProperty.ι (fun T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
            IsAlgebraicSpace B S hS T)) hpreSq).flip hg
  have hZrange : Set.range (pointsMap B S hS Z.toFunctor Z.ι) =
      closure (Set.range (pointsMap B S hS X f)) :=
    range_pointsMap_ι_reducedClosedSubspace B S hS Y hY _ isClosed_closure
  have hpreRange : Set.range (pointsMap B S hS (Z.preimage g).toFunctor (Z.preimage g).ι) =
      pointsMap B S hS V g ⁻¹' Set.range (pointsMap B S hS Z.toFunctor Z.ι) :=
    (preimage_range_pointsMap_of_isPullback B S hS hpreSq).symm
  rw [schemeTheoreticImageSubfunctor_eq_reducedClosedSubspace B S hS (pullback.snd f g) hXV hV
      hXVred, schemeTheoreticImageSubfunctor_eq_reducedClosedSubspace B S hS f hX hY hXred,
    ← hZdef]
  exact (eq_reducedClosedSubspace B S hS V hV _ isClosed_closure (Z.preimage g) hZpre
    (by rw [hpreRange, hZrange, ← hclosure])
    (hasEtaleLocalProperty_of_isEtale B S hS hZpre.1 hZc.1 hfromEtale
      (hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS Y hY _
        isClosed_closure))).symm

end Reduced

end AlgebraicGeometry.Space

end
