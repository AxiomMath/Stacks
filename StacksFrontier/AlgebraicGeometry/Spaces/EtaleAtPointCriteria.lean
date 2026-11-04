module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.EtaleLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.UnramifiedLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.Germ.InducedProperty
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPointOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSquares
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.EtaleAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UnramifiedLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Unramified

/-!
# Étaleness and unramifiedness of a morphism of algebraic spaces at a point

Two pointwise criteria for morphisms of algebraic spaces over a scheme `S` are proved here.

The first is that étaleness at a point of the source is smoothness together with unramifiedness
at that point, which for morphisms of schemes is Stacks 02GK. The second transfers
unramifiedness at a point across a cartesian square: a point of the source of a base change
whose base change is unramified has unramified image, so a morphism locally of finite type is
unramified at every point in the image of the projection of an unramified base change.

## Main results

* `AlgebraicGeometry.Space.isEtaleAt_iff_isSmoothAt_and_isUnramifiedAt`: a morphism of algebraic
  spaces is étale at a point if and only if it is smooth and unramified there; its two
  implications are
  `AlgebraicGeometry.Space.isEtaleAt_of_isSmoothAt_of_isUnramifiedAt` and
  `AlgebraicGeometry.Space.isSmoothAt_and_isUnramifiedAt_of_isEtaleAt`.
* `AlgebraicGeometry.Space.isUnramifiedAt_of_isUnramified_baseChange` and its étale corollary
  `AlgebraicGeometry.Space.isUnramifiedAt_of_isEtale_baseChange` transfer unramifiedness at a
  point along a cartesian square.

## Implementation notes

The three conditions at a point — smooth, unramified, étale — each assert the corresponding
condition on *some* open subspace through the point, and the three open subspaces supplied by
the hypotheses need not agree. The passage to a common neighbourhood is made by the germ
formulation of Stacks 04RF,
`AlgebraicGeometry.Space.holdsOnEveryEtaleChartAtPoint_iff_exists_open`: the conditions become
conditions on the germ of the morphism of schemes read in a pointed étale chart, where the
intersection is taken by restricting two representatives to a common open neighbourhood
(`MorphismOfGerms.hasRepresentativeWithProperty_inf`), and the resulting germ condition for
étaleness is turned back into an open subspace by the same equivalence. On a representative the
remaining step is the scheme-level statement
`AlgebraicGeometry.etaleAt_iff_smoothAt_and_unramifiedAt` at each of its points.

The transfer of unramifiedness along a cartesian square is part (2) of Stacks 05W2,
`AlgebraicGeometry.Space.setOf_isUnramifiedAt_eq_preimage_of_isPullback`, which is stated for a
cartesian square in the category `AlgebraicGeometry.AlgebraicSpaces` of algebraic spaces. A
cartesian square of presheaves whose four vertices are algebraic spaces is one, because the
inclusion of that full subcategory is fully faithful and therefore reflects pullbacks. The
pointwise reading of unramifiedness of the base change is condition (2) of Stacks 03ZK,
`AlgebraicGeometry.Space.isUnramified_tfae`.

## References

* [Stacks Project, Tag 02GK](https://stacks.math.columbia.edu/tag/02GK)
* [Stacks Project, Tag 03ZK](https://stacks.math.columbia.edu/tag/03ZK)
* [Stacks Project, Tag 04RF](https://stacks.math.columbia.edu/tag/04RF)
* [Stacks Project, Tag 04RH](https://stacks.math.columbia.edu/tag/04RH)
* [Stacks Project, Tag 05W2](https://stacks.math.columbia.edu/tag/05W2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Two properties of morphisms of schemes which are étale local on the source and target hold
together on a representative of a morphism of germs as soon as each holds on one: restrict a
representative carrying the first to a common open neighbourhood on which it agrees with a
representative carrying the second. -/
private theorem MorphismOfGerms.hasRepresentativeWithProperty_inf
    (P Q : MorphismProperty Scheme.{u})
    (hP : _root_.AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget P)
    (hQ : _root_.AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget Q)
    {X Y : GermOfScheme.{u}} (f : MorphismOfGerms X Y)
    (hp : MorphismOfGerms.HasRepresentativeWithProperty P f)
    (hq : MorphismOfGerms.HasRepresentativeWithProperty Q f) :
    MorphismOfGerms.HasRepresentativeWithProperty (P ⊓ Q) f := by
  obtain ⟨p, hp, hpp⟩ := hp
  obtain ⟨q, hq, hqq⟩ := hq
  obtain ⟨W, hxW, hWp, hWq, heq⟩ := MorphismOfGerms.mk_eq_mk_iff.mp (hp.trans hq.symm)
  let r : MorphismOfGerms.Representative X Y :=
    { source := W
      mem_source := hxW
      hom := X.scheme.homOfLE hWp ≫ p.hom
      map_point := by
        change p.hom (X.scheme.homOfLE hWp ⟨X.point, hxW⟩) = Y.point
        rw [Scheme.homOfLE_apply']
        exact p.map_point }
  refine ⟨r, ?_, ?_, ?_⟩
  · exact (MorphismOfGerms.mk_eq_mk_iff.mpr ⟨W, hxW, le_rfl, hWp, by simp [r]⟩).trans hp
  · exact hP.precomp.precomp _ (by infer_instance) _ hpp
  · change Q (X.scheme.homOfLE hWp ≫ p.hom)
    rw [heq]
    exact hQ.precomp.precomp _ (by infer_instance) _ hqq

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section EtaleAtPoint

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A property of morphisms of schemes which is étale local on the source and target holds on
every étale chart at a point as soon as it holds on every étale chart of an open subspace through
the point. -/
private theorem holdsOnEveryEtaleChartAtPoint_of_exists_open
    (P : MorphismProperty Scheme.{u}) (hP : IsEtaleLocalOnSourceAndTarget P)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (x : points B S hS X)
    (h : ∃ U : Subfunctor X, IsOpenSubspace B S hS U ∧
      ∃ x' : points B S hS U.toFunctor, pointsMap B S hS U.toFunctor U.ι x' = x ∧
        HoldsOnEveryEtaleChart B S hS P (U.ι ≫ f)) :
    HoldsOnEveryEtaleChartAtPoint B S hS (MorphismOfGerms.HasRepresentativeWithProperty P) f x := by
  obtain ⟨U, hU, y, hy, h⟩ := h
  exact (holdsOnEveryEtaleChartAtPoint_iff_exists_open B S hS P hP hX hY f x).mpr
    ⟨U, hU, ⟨y, hy⟩, h⟩

/-- A morphism of algebraic spaces over `S` which is smooth and unramified at a point of its
source is étale there.

Smoothness and unramifiedness at the point are read as germ conditions in every pointed étale
chart, where they are carried by a single representative; étaleness of that representative is
the scheme-level Stacks 02GK at each of its points, and the resulting germ condition is an open
subspace through the point on which the morphism is étale. -/
theorem isEtaleAt_of_isSmoothAt_of_isUnramifiedAt
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (x : points B S hS X) (hsm : IsSmoothAt B S hS f x) (hur : IsUnramifiedAt B S hS f x) :
    IsEtaleAt B S hS f x := by
  have hsm' := holdsOnEveryEtaleChartAtPoint_of_exists_open B S hS (@Smooth.{u})
    Smooth.isEtaleLocalOnSourceAndTarget hX hY f x hsm
  have hur' := holdsOnEveryEtaleChartAtPoint_of_exists_open B S hS (@Unramified.{u})
    Unramified.isEtaleLocalOnSourceAndTarget hX hY f x hur
  have he : HoldsOnEveryEtaleChartAtPoint B S hS
      (MorphismOfGerms.HasRepresentativeWithProperty (@Etale.{u})) f x := by
    intro c
    obtain ⟨r, hr, hs, hu⟩ := MorphismOfGerms.hasRepresentativeWithProperty_inf
      (@Smooth.{u}) (@Unramified.{u}) Smooth.isEtaleLocalOnSourceAndTarget
      Unramified.isEtaleLocalOnSourceAndTarget _ (hsm' c) (hur' c)
    refine ⟨r, hr, (etale_iff_forall_etaleAt r.hom).mpr fun y => ?_⟩
    exact (etaleAt_iff_smoothAt_and_unramifiedAt r.hom y).mpr
      ⟨⟨⊤, trivial, @instSmoothResLE _ _ r.hom ⊤ ⊤ le_top hs⟩, hu.unramifiedAt y⟩
  obtain ⟨U, hU, ⟨y, hy⟩, heU⟩ :=
    (holdsOnEveryEtaleChartAtPoint_iff_exists_open B S hS (@Etale.{u})
      etale_isEtaleLocalOnSourceAndTarget hX hY f x).mp he
  exact ⟨U, hU, y, hy, (isEtale_iff_holdsOnEveryEtaleChart B S hS hU.1 hY _).mpr heU⟩

/-- A morphism of algebraic spaces over `S` which is étale at a point of its source is smooth
and unramified there: the open subspace witnessing étaleness witnesses both, by Stacks 04XX and
Stacks 06CR. -/
theorem isSmoothAt_and_isUnramifiedAt_of_isEtaleAt
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (x : points B S hS X)
    (he : IsEtaleAt B S hS f x) :
    IsSmoothAt B S hS f x ∧ IsUnramifiedAt B S hS f x := by
  obtain ⟨U, hU, x', hx', h⟩ := he
  exact ⟨⟨U, hU, x', hx', isSmooth_of_isEtale B S hS hY h⟩,
    ⟨U, hU, x', hx', isUnramified_of_isEtale B S hS h⟩⟩

/-- A morphism of algebraic spaces over `S` is étale at a point of its source if and only if it
is smooth and unramified at that point. -/
@[stacks 02GK "for algebraic spaces, at a point"]
theorem isEtaleAt_iff_isSmoothAt_and_isUnramifiedAt
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (x : points B S hS X) :
    IsEtaleAt B S hS f x ↔ IsSmoothAt B S hS f x ∧ IsUnramifiedAt B S hS f x :=
  ⟨isSmoothAt_and_isUnramifiedAt_of_isEtaleAt B S hS hY f x,
    fun h => isEtaleAt_of_isSmoothAt_of_isUnramifiedAt B S hS hX hY f x h.1 h.2⟩

end EtaleAtPoint

section BaseChange

variable {X X' Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Unramifiedness at a point transfers down a cartesian square of algebraic spaces over `S`
whose right-hand morphism is locally of finite type: if the base change `f'` is unramified then
`f` is unramified at the image of every point of the source of `f'`.

The square of presheaves is a cartesian square in the category of algebraic spaces, because the
inclusion of that full subcategory reflects pullbacks, so part (2) of Stacks 05W2 identifies the
unramified locus of `f'` with the inverse image of the unramified locus of `f`; the first is
everything, by condition (2) of Stacks 03ZK. -/
theorem isUnramifiedAt_of_isUnramified_baseChange
    (hX : IsAlgebraicSpace B S hS X) (hX' : IsAlgebraicSpace B S hS X')
    (hY : IsAlgebraicSpace B S hS Y) (hY' : IsAlgebraicSpace B S hS Y')
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g) (hf : IsLocallyOfFiniteType B S hS f)
    (hf' : IsUnramified B S hS f') (w : points B S hS X') :
    IsUnramifiedAt B S hS f (pointsMap B S hS X' g' w) := by
  have sqA : IsPullback
      (ObjectProperty.homMk g' : (⟨X', hX'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩)
      (ObjectProperty.homMk f' : (⟨X', hX'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y', hY'⟩)
      (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
      (ObjectProperty.homMk g : (⟨Y', hY'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩) :=
    IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ sq.w) sq
  have hlocus := setOf_isUnramifiedAt_eq_preimage_of_isPullback B S hS sqA hf
  have hpt : ∀ z : points B S hS X', IsUnramifiedAt B S hS f' z :=
    ((isUnramified_tfae B S hS hX' hY' f').out 1 2).mp hf'
  exact (Set.ext_iff.mp hlocus w).mp (hpt w)

/-- Unramifiedness at a point transfers down a cartesian square of algebraic spaces over `S`
whose right-hand morphism is locally of finite type and whose base change is étale: an étale
morphism of algebraic spaces is unramified, by Stacks 06CR. -/
theorem isUnramifiedAt_of_isEtale_baseChange
    (hX : IsAlgebraicSpace B S hS X) (hX' : IsAlgebraicSpace B S hS X')
    (hY : IsAlgebraicSpace B S hS Y) (hY' : IsAlgebraicSpace B S hS Y')
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g) (hf : IsLocallyOfFiniteType B S hS f)
    (hf' : IsEtale B S hS f') (w : points B S hS X') :
    IsUnramifiedAt B S hS f (pointsMap B S hS X' g' w) :=
  isUnramifiedAt_of_isUnramified_baseChange B S hS hX hX' hY hY' sq hf
    (isUnramified_of_isEtale B S hS hf') w

end BaseChange

end Space

end AlgebraicGeometry

end
