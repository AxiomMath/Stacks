module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.ReducedSmoothLocal
public import Mathlib.CategoryTheory.ObjectProperty.SiteLocal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.ClosedImmersionEffectiveDescent
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.Reduced
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres

/-!
# The reduced closed subspace of an algebraic space on a closed set of points

Let `X` be an algebraic space over a scheme `S` and let `T` be a closed subset of the set of
points of `X`. This file constructs the reduced closed subspace of `X` supported on `T` and
proves that it is the only one.

The construction is étale-local on a chart. Fix a surjective étale chart `φ : U ⟶ X` by an
object `U` of the big fppf site. The part of `U` lying over `T` is a closed subset of the
scheme `U`, and it carries the reduced induced closed subscheme structure of Stacks 01J3. That
subscheme is invariant under the relation `R = U ×_X U`, because the two legs of the relation
are étale and the vanishing ideal of a closed set pulls back, along an étale morphism, to the
vanishing ideal of the preimage of that set. Invariant subschemes of a chart cut out
subfunctors of `X`, by `AlgebraicGeometry.Space.invariantSubspace` of Stacks 07TW, and the
subfunctor so obtained is the reduced closed subspace.

Reducedness of a scheme is used here as an *étale-local property* in the sense of Stacks 03E6,
and that notion is only applicable to reducedness once reducedness is known to be local for
the étale precoverage. That instance is proved here, from two inputs in the library: a scheme smooth
— in particular étale — over a reduced scheme is reduced, which is Stacks 033B through
`AlgebraicGeometry.isReduced_of_smooth_of_isAffine`, and reducedness descends along a flat
surjection, which is Stacks 06QM through
`AlgebraicGeometry.isReduced_of_flat_of_surjective`.

## Main definitions

* `AlgebraicGeometry.Space.atlasPointSet`, `AlgebraicGeometry.Space.atlasVanishingIdeal` and
  `AlgebraicGeometry.Space.atlasReducedSubscheme`: the part of a chart lying over a set of
  points of `X`, the vanishing ideal of that part, and the reduced induced closed subscheme it
  cuts out.
* `AlgebraicGeometry.Space.reducedClosedSubspaceOfChart`: the subspace of `X` cut out by that
  subscheme.
* `AlgebraicGeometry.Space.reducedClosedSubspace`: the same at a chart taken from the atlas
  clause of the algebraic-space hypothesis. This is the reduced closed subspace as *data*: it
  is a `CategoryTheory.Subfunctor` of `X`, not a subtype bundling its specification, so a
  consumer may use it inside a type without projecting a proof component out of it.

## Main results

* `AlgebraicGeometry.isReduced_isLocal_etale` of
  `StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.ReducedSmoothLocal`, imported here:
  reducedness is a local property for
  the étale precoverage. This is the instance which
  `AlgebraicGeometry.Space.HasEtaleLocalProperty` — Stacks 03E6 — needs in order to be
  applied to reducedness at all.
* `AlgebraicGeometry.Scheme.IdealSheafData.comap_vanishingIdeal_of_etale`: the pullback of the
  vanishing ideal of a closed set along an étale morphism is the vanishing ideal of the
  preimage of that set.
* `AlgebraicGeometry.Space.isInvariantSubscheme_atlasReducedSubscheme`: the reduced induced
  closed subscheme of a chart is invariant under the relation of the chart. This is the step
  at which the subschemes constructed étale-locally glue.
* `AlgebraicGeometry.Space.range_pointsMap_ι_reducedClosedSubspace` and
  `AlgebraicGeometry.Space.hasEtaleLocalProperty_isReduced_reducedClosedSubspace`: the
  subspace has point set `T`, and it is reduced. Both are unconditional.
* `AlgebraicGeometry.Space.eq_reducedClosedSubspace`: **uniqueness**, unconditional. A closed
  subspace of `X` which is étale-locally reduced is determined by its set of points.
* `AlgebraicGeometry.Space.isClosedSubspace_reducedClosedSubspace` and
  `AlgebraicGeometry.Space.existsUnique_reducedClosedSubspace`: the subspace is a closed
  subspace, and **Stacks 03IQ in full** — both unconditional, see below.
  `AlgebraicGeometry.Space.isClosedSubspace_reducedClosedSubspace_of_closedImmersionDescent`
  is the closed-subspace clause with the descent of closed immersions taken as a hypothesis,
  for consumers which carry it, and the chart-level statements leading to it keep that
  hypothesis as an explicit argument.

## What is assumed

Nothing. That the constructed subspace is a *closed subspace* — that is, that its inclusion
into `X` is representable and a closed immersion after every representable base change — needs
`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale B S hS @IsClosedImmersion`,
which is Stacks 02W8 at the closed immersions in the form Stacks 03I2 consumes, and that is
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion` of
`StacksFrontier/AlgebraicGeometry/Descent/ClosedImmersionEffectiveDescent.lean`: a closed
immersion is affine, so the affine effective descent of Stacks 0245 — which
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isAffineHom` proves outright —
produces the descended morphism, and fppf descent of closed immersions, Stacks 02L6, says that
it is again a closed immersion. The quasi-affine case of Stacks 0247 is not needed.

The descent input is used for one thing only: the *representability* of the inclusion, through
`AlgebraicGeometry.Space.isAlgebraicSpace_and_presheaf_invariantSubspace`. Once the inclusion
is representable, that it is a closed immersion after every base change needs no descent of
objects, only the fpqc locality of closed immersions, and that is
`AlgebraicGeometry.Space.presheaf_invariantSubspace_of_isLocalAtTarget`.

It is needed at the closed immersions, not at the immersions: the subscheme of the chart which
is being descended is the reduced induced *closed* subscheme, so the property fed to
`AlgebraicGeometry.Space.isAlgebraicSpace_and_presheaf_invariantSubspace` may be
`AlgebraicGeometry.IsClosedImmersion`. That is what makes the hypothesis dischargeable here
and not in `AlgebraicGeometry.Space.invariantLocallyClosedSubschemeEquiv`, which asks for the
same statement at `AlgebraicGeometry.IsImmersion`: the closed-immersion form follows from the
immersion form by `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_le`, and
not conversely.

Stacks 03IQ is carried by the covering set `AlgebraicGeometry.Space.reducedClosedSubspace`,
`AlgebraicGeometry.Space.range_pointsMap_ι_reducedClosedSubspace`,
`AlgebraicGeometry.Space.hasEtaleLocalProperty_isReduced_reducedClosedSubspace`,
`AlgebraicGeometry.Space.isClosedSubspace_reducedClosedSubspace`,
`AlgebraicGeometry.Space.eq_reducedClosedSubspace` and
`AlgebraicGeometry.Space.existsUnique_reducedClosedSubspace`, each attribute carrying a
comment naming the part of the tag it states. All six are unconditional.

The closed-subspace clause really does need descent along the étale cover: it cannot be
obtained by exhibiting the base change of the subspace to an arbitrary object of the site
directly, because that base change is the scheme-theoretic preimage and is *not* the reduced
induced structure on the preimage of `T`. Taking `X = U = Spec k[t]`, `T = {0}` and the test
object `Spec k[x] ⟶ X`, `x ↦ x²`, the base change is cut out by `(x²)` while the reduced
induced structure on the preimage is cut out by `(x)`. So no canonical ideal on the test object
reproduces it, and the ideal genuinely has to be descended.

## Implementation notes

`AlgebraicGeometry.isReduced_of_forall_exists_flat` is the pointwise form of Stacks 06QM: a
scheme is reduced as soon as every one of its points is hit by a flat morphism from a reduced
scheme. Only this form is strong enough for the locality instance, whose covering families are
not single morphisms; the proof is the stalkwise argument of
`AlgebraicGeometry.isReduced_of_flat_of_surjective` with the global surjection replaced by a
preimage chosen at each point.

`AlgebraicGeometry.isReduced_of_smooth` is deduced from the affine-target statement by base
change along an affine open cover of the target, rather than by restricting the morphism: the
pullback cover of a cover of the target is already an open cover of the source, and smoothness
of the projection is stability under base change.

The point topology is `AlgebraicGeometry.Space.pointTopology`, installed as a local
instance in this file as in
`StacksFrontier/AlgebraicGeometry/Spaces/OpenSubspaceCorrespondence.lean`.
No `Classical.choose` of an existence statement about subspaces occurs; the only choice made is
of a chart, from the atlas clause of the algebraic-space hypothesis, and
`AlgebraicGeometry.Space.eq_reducedClosedSubspaceOfChart` shows the result does not depend on
it.

Uniqueness is proved by comparing the base changes of the two subspaces to one chart, where
both are reduced closed subschemes with the same support and are therefore equal — one
inequality being the factorisation of a map from a reduced scheme through a vanishing ideal,
Stacks 0356, and the other that a vanishing ideal is the largest quasi-coherent ideal with its
support, Stacks 01J3. It needs no descent because the base change of a closed subspace to the
chart is representable by hypothesis.

## References

* [Stacks Project, Tag 01J3](https://stacks.math.columbia.edu/tag/01J3)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 02L6](https://stacks.math.columbia.edu/tag/02L6)
* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 033B](https://stacks.math.columbia.edu/tag/033B)
* [Stacks Project, Tag 0356](https://stacks.math.columbia.edu/tag/0356)
* [Stacks Project, Tag 03E6](https://stacks.math.columbia.edu/tag/03E6)
* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 06QM](https://stacks.math.columbia.edu/tag/06QM)
* [Stacks Project, Tag 07TW](https://stacks.math.columbia.edu/tag/07TW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Reducedness is local for the étale precoverage -/

/-- The pointwise form of the descent of reducedness along a flat surjection: a scheme is
reduced as soon as every point of it is in the image of a flat morphism from a reduced scheme.

At a point, the chosen morphism induces a flat local homomorphism of local rings on stalks,
which is therefore faithfully flat, and reducedness descends along it. -/
@[ega "IV 11.3.13" "more general",
  ega "IV 2.1.13" "more general",
  ega "IV 4.4.1" "if X ⊗_k K is reduced"]
theorem isReduced_of_forall_exists_flat {X : Scheme.{u}}
    (H : ∀ x : X, ∃ (Y : Scheme.{u}) (f : Y ⟶ X), Flat f ∧ IsReduced Y ∧
      x ∈ Set.range f.base) :
    IsReduced X := by
  refine @isReduced_of_isReduced_stalk X fun x => ?_
  obtain ⟨Y, f, hflat, hred, y, rfl⟩ := H x
  have hff : (f.stalkMap y).hom.FaithfullyFlat := by
    let : Algebra (X.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) :=
      (f.stalkMap y).hom.toAlgebra
    have : Module.Flat (X.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) :=
      Flat.stalkMap f y
    have : IsLocalHom (algebraMap (X.presheaf.stalk (f.base y)) (Y.presheaf.stalk y)) :=
      inferInstanceAs (IsLocalHom (f.stalkMap y).hom)
    exact Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact hff.isReduced

/-- **Stacks 033B for schemes.** The source of a smooth morphism with reduced target is
reduced.

The affine-target case is `AlgebraicGeometry.isReduced_of_smooth_of_isAffine`; the general
case follows by base change along an affine open cover of the target, which is an open cover
of the source. -/
theorem isReduced_of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] [IsReduced Y] :
    IsReduced X := by
  let 𝒰 := Y.affineOpenCover.openCover
  have : ∀ i, IsReduced ((𝒰.pullback₁ f).X i) := by
    intro i
    have : IsOpenImmersion (𝒰.f i) := 𝒰.map_prop i
    exact @isReduced_of_smooth_of_isAffine _ _ (pullback.snd f (𝒰.f i))
      (MorphismProperty.of_isPullback (P := @Smooth) (IsPullback.of_hasPullback f (𝒰.f i))
        ‹Smooth f›)
      (inferInstanceAs (IsAffine (Spec _))) (isReduced_of_isOpenImmersion (𝒰.f i))
  exact IsReduced.of_openCover X (𝒰.pullback₁ f)

/-- The source of an étale morphism with reduced target is reduced, an étale morphism being
smooth. -/
theorem isReduced_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [IsReduced Y] :
    IsReduced X :=
  isReduced_of_smooth f

/-! ### Reduced closed subschemes pull back along étale morphisms -/

namespace Scheme.IdealSheafData

/-- The pullback of a reduced closed subscheme along an étale morphism is reduced: the
pullback subscheme is, up to isomorphism, a fibre product which is étale over the subscheme
one started with. -/
theorem isReduced_subscheme_comap {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y)
    [Etale f] (hI : IsReduced I.subscheme) :
    IsReduced (I.comap f).subscheme := by
  have : IsReduced I.subscheme := hI
  have : IsReduced (pullback f I.subschemeι) :=
    isReduced_of_etale (pullback.snd f I.subschemeι)
  exact ObjectProperty.prop_of_iso (P := fun Z : Scheme.{u} => IsReduced Z)
    (I.comapIso f).symm ‹_›

/-- Two quasi-coherent ideals with reduced closed subschemes and the same support are equal:
both are the vanishing ideal of that support. -/
theorem eq_of_isReduced_subscheme_of_support_eq {X : Scheme.{u}} (I J : X.IdealSheafData)
    (hI : IsReduced I.subscheme) (hJ : IsReduced J.subscheme) (h : I.support = J.support) :
    I = J := by
  have : IsReduced I.subscheme := hI
  have : IsReduced J.subscheme := hJ
  rw [eq_vanishingIdeal_of_isReduced_subscheme I I.support rfl,
    eq_vanishingIdeal_of_isReduced_subscheme J I.support h.symm]

/-- The pullback along an étale morphism of the vanishing ideal of a closed set is the
vanishing ideal of the preimage of that set. This is the sense in which the reduced induced
closed subscheme structure is étale-local.

The preimage is passed as a closed set `D` together with the equation describing it, so that
no continuity proof has to be named in the statement. -/
theorem comap_vanishingIdeal_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]
    (C : Closeds Y) (D : Closeds X) (hD : (D : Set X) = f.base ⁻¹' (C : Set Y)) :
    (vanishingIdeal C).comap f = vanishingIdeal D := by
  refine eq_of_isReduced_subscheme_of_support_eq _ _
    (isReduced_subscheme_comap _ f (isReduced_subscheme_vanishingIdeal C))
    (isReduced_subscheme_vanishingIdeal D) (Closeds.ext ?_)
  rw [support_comap]
  change f.base ⁻¹' ((vanishingIdeal C).support : Set Y) = _
  rw [coe_support_vanishingIdeal, coe_support_vanishingIdeal, hD]

/-- Two pullbacks of a reduced closed subscheme, viewed as subobjects of the two sources,
agree as soon as the two pullback ideals have the same support. Both legs are required to be
étale, which is what makes the pullback ideals reduced. -/
theorem pullback_subobject_eq_of_support_comap_eq {U R : Scheme.{u}} (I : U.IdealSheafData)
    (f g : R ⟶ U) [Etale f] [Etale g] (hI : IsReduced I.subscheme)
    (hfg : (I.comap f).support = (I.comap g).support) :
    (Subobject.pullback f).obj (Subobject.mk I.subschemeι) =
      (Subobject.pullback g).obj (Subobject.mk I.subschemeι) := by
  have hideal : I.comap f = I.comap g :=
    eq_of_isReduced_subscheme_of_support_eq _ _ (isReduced_subscheme_comap I f hI)
      (isReduced_subscheme_comap I g hI) hfg
  have key : ∀ (h : R ⟶ U), (Subobject.pullback h).obj (Subobject.mk I.subschemeι) =
      Subobject.mk (I.comap h).subschemeι := by
    intro h
    have hh : (I.comapIso h).hom ≫ (pullbackSymmetry h I.subschemeι).hom ≫
        pullback.snd I.subschemeι h = (I.comap h).subschemeι := by
      rw [pullbackSymmetry_hom_comp_snd]
      exact comapIso_hom_fst I h
    rw [Subobject.pullback_obj_mk (IsPullback.of_hasPullback I.subschemeι h)]
    refine Subobject.mk_eq_mk_of_comm _ _
      (I.comapIso h ≪≫ pullbackSymmetry h I.subschemeι).symm ?_
    rw [← hh]
    simp
  rw [key f, key g, hideal]

end Scheme.IdealSheafData

/-! ### The reduced induced closed subscheme of a chart -/

namespace Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : BigFppfOver B S hS}

/-- The comparison map to the scheme is the forward map of the comparison bijection. -/
theorem pointsToScheme_pointsEquivScheme_symm (V : BigFppfOver B S hS)
    (x : (BigFppfOver.toScheme B S hS).obj V) :
    pointsToScheme B S hS V ((pointsEquivScheme B S hS V).symm x) = x :=
  (pointsEquivScheme B S hS V).apply_symm_apply x

/-- The subset of a chart `U` of `X` lying over a set `T` of points of `X`: the preimage of
`T` under the map on points induced by the chart, transported to the scheme `U` along the
bijection `AlgebraicGeometry.Space.pointsEquivScheme`. -/
noncomputable def atlasPointSet (φ : yoneda.obj U ⟶ X) (T : Set (points B S hS X)) :
    Set ((BigFppfOver.toScheme B S hS).obj U) :=
  {x | pointsMap B S hS (yoneda.obj U) φ ((pointsEquivScheme B S hS U).symm x) ∈ T}

/-- A point `x` of the chart `U` lies over `T` if and only if the point of `X` it determines
through `φ` lies in `T`. -/
theorem mem_atlasPointSet_iff (φ : yoneda.obj U ⟶ X) (T : Set (points B S hS X))
    (x : (BigFppfOver.toScheme B S hS).obj U) :
    x ∈ atlasPointSet B S hS φ T ↔
      pointsMap B S hS (yoneda.obj U) φ ((pointsEquivScheme B S hS U).symm x) ∈ T :=
  Iff.rfl

/-- The set lying over `T` in a chart is the image of the preimage of `T` under the comparison
map to the scheme. -/
theorem atlasPointSet_eq_image (φ : yoneda.obj U ⟶ X) (T : Set (points B S hS X)) :
    atlasPointSet B S hS φ T =
      pointsToScheme B S hS U '' (pointsMap B S hS (yoneda.obj U) φ ⁻¹' T) :=
  (Equiv.image_eq_preimage_symm (pointsEquivScheme B S hS U)
    (pointsMap B S hS (yoneda.obj U) φ ⁻¹' T)).symm

/-- The set lying over a closed set of points in a chart is closed. -/
theorem isClosed_atlasPointSet (φ : yoneda.obj U ⟶ X) (T : Set (points B S hS X))
    (hT : IsClosed T) : IsClosed (atlasPointSet B S hS φ T) := by
  rw [atlasPointSet_eq_image, ← isClosed_pointTopology_yoneda_iff_isClosed_image]
  exact hT.preimage (continuous_pointsMap B S hS φ)

/-- The comparison bijections intertwine the map on points induced by a morphism of the site
with the underlying map of schemes. -/
theorem pointsEquivScheme_symm_map {V : BigFppfOver B S hS} (h : V ⟶ U)
    (x : (BigFppfOver.toScheme B S hS).obj V) :
    (pointsEquivScheme B S hS U).symm (((BigFppfOver.toScheme B S hS).map h).base x) =
      pointsMap B S hS (yoneda.obj V) (yoneda.map h)
        ((pointsEquivScheme B S hS V).symm x) :=
  (pointsEquivScheme B S hS U).symm_apply_eq.2 <| by
    change _ = pointsToScheme B S hS U (pointsMap B S hS (yoneda.obj V) (yoneda.map h)
      ((pointsEquivScheme B S hS V).symm x))
    rw [pointsToScheme_pointsMap_yoneda, pointsToScheme_pointsEquivScheme_symm]

/-- A point of an object `V` of the site over the chart lies over `T` exactly when the point
of `X` it determines lies in `T`. -/
theorem mem_atlasPointSet_map_iff {V : BigFppfOver B S hS} (h : V ⟶ U)
    (φ : yoneda.obj U ⟶ X) (T : Set (points B S hS X))
    (x : (BigFppfOver.toScheme B S hS).obj V) :
    ((BigFppfOver.toScheme B S hS).map h).base x ∈ atlasPointSet B S hS φ T ↔
      pointsMap B S hS (yoneda.obj V) (yoneda.map h ≫ φ)
        ((pointsEquivScheme B S hS V).symm x) ∈ T := by
  rw [mem_atlasPointSet_iff, pointsEquivScheme_symm_map, pointsMap_comp]
  exact Iff.rfl

variable {φ : yoneda.obj U ⟶ X}
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ)

include hs in
/-- The two legs of the relation of a chart form a pullback square over the chart. -/
theorem isPullback_yoneda_map_atlasRelation :
    IsPullback (yoneda.map (atlasRelationTarget B S hS hs))
      (yoneda.map (atlasRelationSource B S hS hs)) φ φ := by
  rw [show yoneda.map (atlasRelationTarget B S hS hs) = hs.rep.fst φ from
    yoneda.map_preimage _]
  exact hs.rep.isPullback φ

include hs he in
/-- The source leg of the relation of an étale chart is étale. -/
theorem etale_atlasRelationSource :
    _root_.AlgebraicGeometry.Etale
      ((BigFppfOver.toScheme B S hS).map (atlasRelationSource B S hS hs)) :=
  he.property φ _ _ (isPullback_yoneda_map_atlasRelation B S hS hs)

include hs he in
/-- The target leg of the relation of an étale chart is étale. -/
theorem etale_atlasRelationTarget :
    _root_.AlgebraicGeometry.Etale
      ((BigFppfOver.toScheme B S hS).map (atlasRelationTarget B S hS hs)) :=
  he.property φ _ _ (isPullback_yoneda_map_atlasRelation B S hS hs).flip

/-- The quasi-coherent ideal of the chart `U` cutting out the reduced induced closed subscheme
on the part of `U` lying over a closed set `T` of points of `X`. -/
noncomputable def atlasVanishingIdeal (φ : yoneda.obj U ⟶ X) (T : Set (points B S hS X))
    (hT : IsClosed T) : ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    ⟨atlasPointSet B S hS φ T, isClosed_atlasPointSet B S hS φ T hT⟩

/-- The support of `AlgebraicGeometry.Space.atlasVanishingIdeal` is the part of the chart
lying over `T`. -/
theorem coe_support_atlasVanishingIdeal (φ : yoneda.obj U ⟶ X) (T : Set (points B S hS X))
    (hT : IsClosed T) :
    ((atlasVanishingIdeal B S hS φ T hT).support :
      Set ((BigFppfOver.toScheme B S hS).obj U)) = atlasPointSet B S hS φ T :=
  Scheme.IdealSheafData.coe_support_vanishingIdeal _

/-- The reduced induced closed subscheme of the chart `U` on the part of `U` lying over a
closed set `T` of points of `X`, as a subobject of `U`. -/
noncomputable def atlasReducedSubscheme (φ : yoneda.obj U ⟶ X) (T : Set (points B S hS X))
    (hT : IsClosed T) : Subobject ((BigFppfOver.toScheme B S hS).obj U) :=
  Subobject.mk (atlasVanishingIdeal B S hS φ T hT).subschemeι

/-- The reduced induced closed subscheme of a chart is a closed subscheme. -/
theorem isClosedImmersion_arrow_atlasReducedSubscheme (φ : yoneda.obj U ⟶ X)
    (T : Set (points B S hS X)) (hT : IsClosed T) :
    _root_.AlgebraicGeometry.IsClosedImmersion
      (atlasReducedSubscheme B S hS φ T hT).arrow := by
  change _root_.AlgebraicGeometry.IsClosedImmersion
    (Subobject.mk (atlasVanishingIdeal B S hS φ T hT).subschemeι).arrow
  rw [← Subobject.underlyingIso_hom_comp_eq_mk
    (atlasVanishingIdeal B S hS φ T hT).subschemeι]
  infer_instance

/-- The reduced induced closed subscheme of a chart is an immersed subscheme. -/
theorem isImmersion_arrow_atlasReducedSubscheme (φ : yoneda.obj U ⟶ X)
    (T : Set (points B S hS X)) (hT : IsClosed T) :
    _root_.AlgebraicGeometry.IsImmersion (atlasReducedSubscheme B S hS φ T hT).arrow :=
  have := isClosedImmersion_arrow_atlasReducedSubscheme B S hS φ T hT
  inferInstance

/-- The reduced induced closed subscheme of a chart is reduced. -/
theorem isReduced_atlasReducedSubscheme (φ : yoneda.obj U ⟶ X)
    (T : Set (points B S hS X)) (hT : IsClosed T) :
    IsReduced (Subobject.underlying.obj (atlasReducedSubscheme B S hS φ T hT)) :=
  ObjectProperty.prop_of_iso (P := fun Z : Scheme.{u} => IsReduced Z)
    (Subobject.underlyingIso (atlasVanishingIdeal B S hS φ T hT).subschemeι).symm
    (Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _)

include hs he in
/-- **The reduced induced closed subscheme of a chart is invariant under the relation of the
chart.** This is the step at which the closed subschemes constructed étale-locally glue: the
two pullbacks of the ideal along the two legs of the relation are both reduced, because the
legs are étale, and they have the same support, because the two legs have the same composite
with the chart; and a reduced closed subscheme is determined by its support. -/
theorem isInvariantSubscheme_atlasReducedSubscheme (T : Set (points B S hS X))
    (hT : IsClosed T) :
    IsInvariantSubscheme B S hS hs (atlasReducedSubscheme B S hS φ T hT) := by
  have ht := etale_atlasRelationTarget B S hS hs he
  have hsrc := etale_atlasRelationSource B S hS hs he
  have hsupp : ((atlasVanishingIdeal B S hS φ T hT).comap
        ((BigFppfOver.toScheme B S hS).map (atlasRelationTarget B S hS hs))).support =
      ((atlasVanishingIdeal B S hS φ T hT).comap
        ((BigFppfOver.toScheme B S hS).map (atlasRelationSource B S hS hs))).support := by
    refine Closeds.ext ?_
    rw [Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_comap]
    change ((BigFppfOver.toScheme B S hS).map (atlasRelationTarget B S hS hs)).base ⁻¹'
        ((atlasVanishingIdeal B S hS φ T hT).support : Set _) =
      ((BigFppfOver.toScheme B S hS).map (atlasRelationSource B S hS hs)).base ⁻¹'
        ((atlasVanishingIdeal B S hS φ T hT).support : Set _)
    ext x
    rw [Set.mem_preimage, Set.mem_preimage, coe_support_atlasVanishingIdeal,
      mem_atlasPointSet_map_iff, mem_atlasPointSet_map_iff,
      yoneda_map_atlasRelationSource_comp B S hS hs]
  exact Scheme.IdealSheafData.pullback_subobject_eq_of_support_comap_eq
    (atlasVanishingIdeal B S hS φ T hT) _ _
    (Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _) hsupp

/-! ### The reduced closed subspace cut out by a closed set of points -/

/-- The map on points induced by a morphism of the site, read through the comparison
bijections, is the underlying map of schemes. -/
theorem pointsMap_yoneda_map_eq {V : BigFppfOver B S hS} (h : V ⟶ U) :
    pointsMap B S hS (yoneda.obj V) (yoneda.map h) =
      (pointsEquivScheme B S hS U).symm ∘ ((BigFppfOver.toScheme B S hS).map h).base ∘
        (pointsEquivScheme B S hS V) := by
  funext w
  refine (pointsEquivScheme B S hS U).injective ?_
  rw [Function.comp_apply, Function.comp_apply, Equiv.apply_symm_apply]
  exact pointsToScheme_pointsMap_yoneda B S hS h w

/-- The range of the map on points induced by a morphism of the site is the range of the
underlying map of schemes, read through the comparison bijection. -/
theorem range_pointsMap_yoneda_map {V : BigFppfOver B S hS} (h : V ⟶ U) :
    Set.range (pointsMap B S hS (yoneda.obj V) (yoneda.map h)) =
      (pointsEquivScheme B S hS U).symm ''
        Set.range ((BigFppfOver.toScheme B S hS).map h).base := by
  rw [pointsMap_yoneda_map_eq, Set.range_comp, Set.range_comp,
    (pointsEquivScheme B S hS V).surjective.range_eq, Set.image_univ]

/-- **The part of a chart lying over the point set of a subfunctor is the range of the base
change of that subfunctor to the chart.**

The inclusion from right to left is the only place where the surjectivity of the comparison
map from the points of a fibre product to the fibre product of the point sets is used. -/
theorem range_map_eq_atlasPointSet (W : Subfunctor X) {V : BigFppfOver B S hS}
    {i : V ⟶ U} {k : yoneda.obj V ⟶ W.toFunctor}
    (hk : IsPullback k (yoneda.map i) W.ι φ) :
    Set.range ((BigFppfOver.toScheme B S hS).map i).base =
      atlasPointSet B S hS φ (Set.range (pointsMap B S hS W.toFunctor W.ι)) := by
  ext x
  rw [mem_atlasPointSet_iff]
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨pointsMap B S hS (yoneda.obj V) k ((pointsEquivScheme B S hS V).symm v), ?_⟩
    rw [pointsEquivScheme_symm_map, ← Function.comp_apply
        (f := pointsMap B S hS (yoneda.obj U) φ), ← pointsMap_comp, ← hk.w, pointsMap_comp]
    rfl
  · rintro ⟨z, hz⟩
    obtain ⟨w, -, hw⟩ := exists_points_of_isPullback B S hS hk z
      ((pointsEquivScheme B S hS U).symm x) hz
    refine ⟨(pointsEquivScheme B S hS V) w, (pointsEquivScheme B S hS U).symm.injective ?_⟩
    rwa [pointsEquivScheme_symm_map, Equiv.symm_apply_apply]

/-- The reduced closed subspace of `X` cut out by a closed set `T` of points of `X`, computed
from a chart `φ`: it is the subspace cut out by the reduced induced closed subscheme of the
chart on the part of the chart lying over `T`.

This is explicit data, built from the chart: the only choice it involves is the chart itself. -/
noncomputable def reducedClosedSubspaceOfChart (φ : yoneda.obj U ⟶ X)
    (T : Set (points B S hS X)) (hT : IsClosed T) : Subfunctor X :=
  invariantSubspace B S hS φ (atlasReducedSubscheme B S hS φ T hT)

/-- A property of morphisms of schemes, stable under base change, defines a property of
morphisms of presheaves on the site which is again stable under base change. -/
private theorem presheaf_inverseImage_of_isPullback (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] {F₁ F₂ F₃ F₄ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : F₁ ⟶ F₃} {g : F₂ ⟶ F₃} {f' : F₄ ⟶ F₂} {g' : F₄ ⟶ F₁} (h : IsPullback f' g' g f)
    (hg : (MorphismProperty.presheaf (MorphismProperty.inverseImage P
      (BigFppfOver.toScheme B S hS))) g) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage P
      (BigFppfOver.toScheme B S hS))) g' :=
  have := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS))
  MorphismProperty.of_isPullback h hg

/-- The range of a morphism of schemes is unchanged by precomposition with an isomorphism. -/
private theorem range_iso_comp {A A' Y : Scheme.{u}} (ε : A ≅ A') (g : A' ⟶ Y) :
    Set.range (ε.hom ≫ g).base = Set.range g.base := by
  simp [Set.range_comp]

include hs he in
/-- The chart of `AlgebraicGeometry.Space.reducedClosedSubspaceOfChart` furnished by a
presentation of the reduced induced closed subscheme of the chart: a surjective étale chart
whose underlying scheme is reduced. This is the étale-local reducedness of the subspace, and
simultaneously the chart used to compute its point set. -/
theorem exists_reducedChart (T : Set (points B S hS X)) (hT : IsClosed T) :
    ∃ (V : BigFppfOver B S hS) (i : V ⟶ U)
      (k : yoneda.obj V ⟶ (reducedClosedSubspaceOfChart B S hS φ T hT).toFunctor),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) k ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) k ∧
        IsReduced ((BigFppfOver.toScheme B S hS).obj V) ∧
        Set.range ((BigFppfOver.toScheme B S hS).map i).base =
          atlasPointSet B S hS φ T ∧
        k ≫ (reducedClosedSubspaceOfChart B S hS φ T hT).ι = yoneda.map i ≫ φ := by
  obtain ⟨V, i, e, hei⟩ := exists_presentation B S hS _
    (isImmersion_arrow_atlasReducedSubscheme B S hS φ T hT)
  obtain ⟨k, hk⟩ := exists_isPullback_yoneda_presentation B S hS hs _
    (isInvariantSubscheme_atlasReducedSubscheme B S hS hs he T hT) i e hei
  refine ⟨V, i, k, presheaf_inverseImage_of_isPullback B S hS _ hk.flip hs,
    presheaf_inverseImage_of_isPullback B S hS _ hk.flip he,
    ObjectProperty.prop_of_iso (P := fun Z : Scheme.{u} => IsReduced Z) e.symm
      (isReduced_atlasReducedSubscheme B S hS φ T hT), ?_, hk.w⟩
  have h2 : Set.range ⇑(atlasVanishingIdeal B S hS φ T hT).subschemeι =
      Set.range ⇑(atlasReducedSubscheme B S hS φ T hT).arrow := by
    rw [show (atlasVanishingIdeal B S hS φ T hT).subschemeι =
        (Subobject.underlyingIso (atlasVanishingIdeal B S hS φ T hT).subschemeι).symm.hom ≫
          (atlasReducedSubscheme B S hS φ T hT).arrow from
      (Subobject.underlyingIso_arrow _).symm]
    exact range_iso_comp _ _
  rw [← hei, range_iso_comp e _, ← h2, Scheme.IdealSheafData.range_subschemeι]
  exact coe_support_atlasVanishingIdeal B S hS φ T hT

include hs he in
/-- **The subspace cut out by the reduced induced closed subscheme of a chart is
étale-locally reduced**, Stacks 03E6 at reducedness. The chart is a presentation of that
subscheme, which is reduced. -/
theorem hasEtaleLocalProperty_isReduced_reducedClosedSubspaceOfChart
    (T : Set (points B S hS X)) (hT : IsClosed T) :
    HasEtaleLocalProperty B S hS (reducedClosedSubspaceOfChart B S hS φ T hT).toFunctor
      (fun Y : Scheme.{u} => IsReduced Y) := by
  obtain ⟨V, i, k, hks, hke, hVred, -, -⟩ := exists_reducedChart B S hS hs he T hT
  exact ⟨V, k, hks, hke, hVred⟩

include hs he in
/-- **The point set of the subspace cut out by the reduced induced closed subscheme of a
chart is the closed set one started with.**

The point set of the subspace is computed on its chart, and there it is the image under the
chart of the part of `U` lying over `T`, which is the preimage of `T`; the chart of `X` being
surjective on points, the image of that preimage is `T` again. -/
theorem range_pointsMap_ι_reducedClosedSubspaceOfChart (T : Set (points B S hS X))
    (hT : IsClosed T) :
    Set.range (pointsMap B S hS (reducedClosedSubspaceOfChart B S hS φ T hT).toFunctor
      (reducedClosedSubspaceOfChart B S hS φ T hT).ι) = T := by
  obtain ⟨V, i, k, hks, -, -, hi, hw⟩ := exists_reducedChart B S hS hs he T hT
  have hcomp : Set.range (pointsMap B S hS
        (reducedClosedSubspaceOfChart B S hS φ T hT).toFunctor
        (reducedClosedSubspaceOfChart B S hS φ T hT).ι) =
      Set.range (pointsMap B S hS (yoneda.obj V) (k ≫
        (reducedClosedSubspaceOfChart B S hS φ T hT).ι)) := by
    rw [pointsMap_comp]
    exact ((isSurjective_of_presheafSurjective B S hS k hks).range_comp _).symm
  rw [hcomp, hw, pointsMap_comp, Set.range_comp, range_pointsMap_yoneda_map, hi]
  change pointsMap B S hS (yoneda.obj U) φ ''
    ((pointsEquivScheme B S hS U).symm '' atlasPointSet B S hS φ T) = T
  rw [show atlasPointSet B S hS φ T =
      (pointsEquivScheme B S hS U).symm ⁻¹' (pointsMap B S hS (yoneda.obj U) φ ⁻¹' T) from rfl,
    Set.image_preimage_eq _ (pointsEquivScheme B S hS U).symm.surjective,
    Set.image_preimage_eq _ (isSurjective_of_presheafSurjective B S hS φ hs)]

/-- Closed immersions are monomorphisms. `AlgebraicGeometry.Space.isImmersion_le_monomorphisms`
is the same statement for immersions. -/
private theorem isClosedImmersion_le_monomorphisms :
    (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) ≤ MorphismProperty.monomorphisms Scheme.{u} :=
  fun _ _ f hf => by
    have := hf
    exact (inferInstance : Mono f)

include hs he in
/-- **The subspace cut out by the reduced induced closed subscheme of a chart is a closed
subspace**, given effective descent for *closed* immersions along the surjective étale
morphisms of the site. That hypothesis is Stacks 02W8 at the closed immersions and is proved
outright by
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion`; it is taken
as an argument here, and discharged in
`AlgebraicGeometry.Space.isClosedSubspace_reducedClosedSubspace`.

The descent hypothesis supplies only the *representability* of the inclusion, through
`AlgebraicGeometry.Space.isAlgebraicSpace_and_presheaf_invariantSubspace`; once the inclusion
is representable, that it is a closed immersion after every base change is
`AlgebraicGeometry.Space.presheaf_invariantSubspace_of_isLocalAtTarget`, which needs no
descent of objects, only the fpqc locality of closed immersions.

The subscheme being descended here is a *closed* subscheme of the chart, so the property fed to
`AlgebraicGeometry.Space.isAlgebraicSpace_and_presheaf_invariantSubspace` is
`AlgebraicGeometry.IsClosedImmersion` rather than `AlgebraicGeometry.IsImmersion`. That makes
the hypothesis strictly weaker: effective descent at the immersions implies effective descent at
the closed immersions, by
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_le`, and not conversely. -/
theorem isClosedSubspace_reducedClosedSubspaceOfChart
    (hdesc : IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}))
    (hX : IsAlgebraicSpace B S hS X) (T : Set (points B S hS X)) (hT : IsClosed T) :
    IsClosedSubspace B S hS (reducedClosedSubspaceOfChart B S hS φ T hT) := by
  have him := isImmersion_arrow_atlasReducedSubscheme B S hS φ T hT
  have hci := isClosedImmersion_arrow_atlasReducedSubscheme B S hS φ T hT
  have hinv := isInvariantSubscheme_atlasReducedSubscheme B S hS hs he T hT
  have hA := isAlgebraicSpace_and_presheaf_invariantSubspace B S hS hs he hdesc
    hX _ him hci hinv
  have hloc := Stacks.Descent.isClosedImmersion_isLocalAtTarget_fpqc
  exact ⟨hA.1, presheaf_invariantSubspace_of_isLocalAtTarget B S hS hs he _ him hci hinv
    hA.2.rep⟩

include hs he in
/-- **Stacks 03IQ, existence**, at a chart supplied by the caller.

A closed subset of the points of an algebraic space carries a reduced closed subspace
structure with that point set. The witness is explicit data,
`AlgebraicGeometry.Space.reducedClosedSubspaceOfChart`, built from the chart; the
closed-subspace clause is the only one needing descent, and that descent is
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion`.

This declaration does **not** carry `@[stacks 03IQ]`: it is the statement at a chart supplied
by the caller, and the tag's covering set is the chart-free family ending in
`AlgebraicGeometry.Space.existsUnique_reducedClosedSubspace`, which takes its chart from the
atlas clause of the algebraic-space hypothesis. -/
theorem exists_isClosedSubspace_range_pointsMap_eq_and_hasEtaleLocalProperty_isReduced
    (hX : IsAlgebraicSpace B S hS X) (T : Set (points B S hS X)) (hT : IsClosed T) :
    ∃ Z : Subfunctor X,
      IsClosedSubspace B S hS Z ∧
        Set.range (pointsMap B S hS Z.toFunctor Z.ι) = T ∧
          HasEtaleLocalProperty B S hS Z.toFunctor (fun Y : Scheme.{u} => IsReduced Y) :=
  ⟨reducedClosedSubspaceOfChart B S hS φ T hT,
    isClosedSubspace_reducedClosedSubspaceOfChart B S hS hs he
      (isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion B S hS) hX T hT,
    range_pointsMap_ι_reducedClosedSubspaceOfChart B S hS hs he T hT,
    hasEtaleLocalProperty_isReduced_reducedClosedSubspaceOfChart B S hS hs he T hT⟩

/-! ### Uniqueness -/

/-- **An object of the site which is a surjective étale chart of an étale-locally reduced
presheaf has reduced underlying scheme.** The two charts are compared through their fibre
product over the presheaf, which is étale over each of them: so it is reduced, being étale
over a reduced scheme, and it is a flat surjection onto the chart in question. -/
theorem isReduced_of_hasEtaleLocalProperty_isReduced
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : HasEtaleLocalProperty B S hS F (fun Y : Scheme.{u} => IsReduced Y))
    {V : BigFppfOver B S hS} {ψ : yoneda.obj V ⟶ F}
    (hψe : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) ψ) :
    IsReduced ((BigFppfOver.toScheme B S hS).obj V) := by
  obtain ⟨V₀, χ, hχs, hχe, hV₀⟩ := hF
  have hc₁s : Surjective ((BigFppfOver.toScheme B S hS).map (hχs.rep.snd ψ)) :=
    hχs.property_snd ψ
  have hc₁e : _root_.AlgebraicGeometry.Etale
      ((BigFppfOver.toScheme B S hS).map (hχs.rep.snd ψ)) := hχe.property_snd ψ
  have hsq : IsPullback (yoneda.map (hχs.rep.snd ψ))
      (yoneda.map (yoneda.preimage (hχs.rep.fst ψ))) ψ χ := by
    rw [yoneda.map_preimage]
    exact (hχs.rep.isPullback ψ).flip
  have hc₀e : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map
      (yoneda.preimage (hχs.rep.fst ψ))) := hψe.property χ _ _ hsq
  have hV₀' : IsReduced ((BigFppfOver.toScheme B S hS).obj V₀) := hV₀
  have : IsReduced ((BigFppfOver.toScheme B S hS).obj (hχs.rep.pullback ψ)) :=
    isReduced_of_etale ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (hχs.rep.fst ψ)))
  exact isReduced_of_flat_of_surjective ((BigFppfOver.toScheme B S hS).map (hχs.rep.snd ψ))

include hs in
/-- **An invariant subscheme of the chart cutting out a closed subspace of `X` is a closed
subscheme of the chart.** This is the forward direction of
`AlgebraicGeometry.Space.closed_iff` with the descent hypothesis removed: that hypothesis is
used in the source only for the reverse direction.

The base change of the inclusion of the subspace along the chart is a closed immersion
because the inclusion is; and it presents the same subscheme of the chart, an immersed
subscheme being determined by its functor of points. -/
theorem isClosedImmersion_arrow_of_isClosedSubspace_invariantSubspace
    (Z : Subobject ((BigFppfOver.toScheme B S hS).obj U))
    (himZ : _root_.AlgebraicGeometry.IsImmersion Z.arrow)
    (hinvZ : IsInvariantSubscheme B S hS hs Z)
    (hc : IsClosedSubspace B S hS (invariantSubspace B S hS φ Z)) :
    _root_.AlgebraicGeometry.IsClosedImmersion Z.arrow := by
  have hRI : MorphismProperty.RespectsIso (@_root_.AlgebraicGeometry.IsImmersion.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hci : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hc.2.rep.snd φ)) := hc.2.property_snd φ
  have hmono : Mono ((BigFppfOver.toScheme B S hS).map (hc.2.rep.snd φ)) := inferInstance
  have hpres : (Subobject.underlyingIso
        ((BigFppfOver.toScheme B S hS).map (hc.2.rep.snd φ))).symm.hom ≫
      (Subobject.mk ((BigFppfOver.toScheme B S hS).map (hc.2.rep.snd φ))).arrow =
      (BigFppfOver.toScheme B S hS).map (hc.2.rep.snd φ) := Subobject.underlyingIso_arrow _
  have hsp : subschemePoints B S hS
      (Subobject.mk ((BigFppfOver.toScheme B S hS).map (hc.2.rep.snd φ))) =
      subschemePoints B S hS Z := by
    rw [subschemePoints_eq_range B S hS _ _ hpres,
      range_yoneda_snd_eq_preimage B S hS φ hc.2.rep,
      preimage_invariantSubspace B S hS hs Z hinvZ]
  have hZeq : Subobject.mk ((BigFppfOver.toScheme B S hS).map (hc.2.rep.snd φ)) = Z :=
    subschemePoints_injective B S hS
      ((property_toScheme_map_iff_of_presentation B S hS _ _ hpres
        (@_root_.AlgebraicGeometry.IsImmersion.{u})).1 inferInstance) himZ hsp
  rw [← hZeq]
  exact (property_toScheme_map_iff_of_presentation B S hS _ _ hpres
    (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})).1 hci

/-- **A reduced closed subscheme of the chart with the right support is the reduced induced
one.** One inequality is the factorisation of a map from a reduced scheme through the
vanishing ideal of a closed set containing its range, Stacks 0356; the other is that the
vanishing ideal is the largest quasi-coherent ideal with its support, Stacks 01J3. -/
theorem eq_atlasReducedSubscheme (Z : Subobject ((BigFppfOver.toScheme B S hS).obj U))
    (hciZ : _root_.AlgebraicGeometry.IsClosedImmersion Z.arrow)
    (hredZ : IsReduced (Subobject.underlying.obj Z))
    (T : Set (points B S hS X)) (hT : IsClosed T)
    (hrange : Set.range Z.arrow.base = atlasPointSet B S hS φ T) :
    Z = atlasReducedSubscheme B S hS φ T hT := by
  refine le_antisymm ?_ ?_
  · obtain ⟨g, hg⟩ := (Scheme.IdealSheafData.exists_lift_subschemeι_iff_range_subset_support
      (atlasVanishingIdeal B S hS φ T hT) Z.arrow).2
        (by rw [coe_support_atlasVanishingIdeal B S hS φ T hT, hrange])
    rw [← Subobject.mk_arrow Z]
    exact Subobject.mk_le_mk_of_comm g hg
  · have hker : Scheme.Hom.ker Z.arrow ≤ atlasVanishingIdeal B S hS φ T hT := by
      refine le_trans (Scheme.IdealSheafData.le_radical _) (le_of_eq ?_)
      rw [← Scheme.IdealSheafData.vanishingIdeal_support]
      refine congrArg Scheme.IdealSheafData.vanishingIdeal (Closeds.ext ?_)
      rw [Scheme.Hom.support_ker Z.arrow, hrange]
      exact (isClosed_atlasPointSet B S hS φ T hT).closure_eq
    rw [← Subobject.mk_arrow Z]
    exact Subobject.mk_le_mk_of_comm
      (IsClosedImmersion.lift Z.arrow _
        (by rwa [Scheme.IdealSheafData.ker_subschemeι]))
      (IsClosedImmersion.lift_fac _ _ _)

include hs he in
/-- **Stacks 03IQ, uniqueness, unconditionally.** A closed subspace of `X` which is
étale-locally reduced is determined by its set of points: it is the subspace cut out by the
reduced induced closed subscheme of any surjective étale chart on the part of the chart lying
over that set.

No descent hypothesis is needed. The base change of the subspace to the chart exists because
the inclusion of a closed subspace is representable by hypothesis, and the identification of
that base change with the reduced induced closed subscheme is then a statement about closed
subschemes of one scheme. -/
theorem eq_reducedClosedSubspaceOfChart (hX : IsAlgebraicSpace B S hS X)
    (T : Set (points B S hS X)) (hT : IsClosed T) (W : Subfunctor X)
    (hWc : IsClosedSubspace B S hS W)
    (hWT : Set.range (pointsMap B S hS W.toFunctor W.ι) = T)
    (hWr : HasEtaleLocalProperty B S hS W.toFunctor (fun Y : Scheme.{u} => IsReduced Y)) :
    W = reducedClosedSubspaceOfChart B S hS φ T hT := by
  have hWi : IsLocallyClosedSubspace B S hS W :=
    ⟨hWc.1, MorphismProperty.relative_monotone
      (MorphismProperty.monotone_inverseImage (BigFppfOver.toScheme B S hS)
        isClosedImmersion_le_isImmersion) _ hWc.2⟩
  obtain ⟨ZW, ⟨himW, hinvW⟩, hZW⟩ := exists_invariantSubspace_eq B S hS hs he hX W hWi
  subst hZW
  have hciW := isClosedImmersion_arrow_of_isClosedSubspace_invariantSubspace
    B S hS hs ZW himW hinvW hWc
  obtain ⟨V, i, e, hei⟩ := exists_presentation B S hS ZW himW
  obtain ⟨k, hk⟩ := exists_isPullback_yoneda_presentation B S hS hs ZW hinvW i e hei
  have hredV : IsReduced ((BigFppfOver.toScheme B S hS).obj V) :=
    isReduced_of_hasEtaleLocalProperty_isReduced B S hS hWr
      (presheaf_inverseImage_of_isPullback B S hS _ hk.flip he)
  have hredZW : IsReduced (Subobject.underlying.obj ZW) :=
    ObjectProperty.prop_of_iso (P := fun Z : Scheme.{u} => IsReduced Z) e hredV
  have hrange : Set.range ZW.arrow.base = atlasPointSet B S hS φ T := by
    have h1 := range_map_eq_atlasPointSet B S hS (invariantSubspace B S hS φ ZW) hk
    rwa [hWT, ← hei, range_iso_comp] at h1
  rw [reducedClosedSubspaceOfChart,
    ← eq_atlasReducedSubscheme B S hS ZW hciW hredZW T hT hrange]

/-! ### The reduced closed subspace of an algebraic space -/

/-- **The reduced closed subspace of an algebraic space supported on a closed set of
points**, as data rather than as a choice of a witness to an existence statement.

It is `AlgebraicGeometry.Space.reducedClosedSubspaceOfChart` at a chart chosen from the
atlas clause of the algebraic-space hypothesis. The choice is of a chart, which the
hypothesis provides; it is not a choice of the subspace, and by
`AlgebraicGeometry.Space.eq_reducedClosedSubspaceOfChart` the result does not depend on it. -/
@[stacks 03IQ "the subspace itself, on a closed set of points"]
noncomputable def reducedClosedSubspace (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X)
    (T : Set (points B S hS X)) (hT : IsClosed T) : Subfunctor X :=
  reducedClosedSubspaceOfChart B S hS
    (Classical.choose (Classical.choose_spec hX.exists_atlas)) T hT

/-- **The point set of the reduced closed subspace is the closed set one started with.** -/
@[stacks 03IQ "property (a): the point set of the subspace is the given closed set"]
theorem range_pointsMap_ι_reducedClosedSubspace (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X)
    (T : Set (points B S hS X)) (hT : IsClosed T) :
    Set.range (pointsMap B S hS (reducedClosedSubspace B S hS X hX T hT).toFunctor
      (reducedClosedSubspace B S hS X hX T hT).ι) = T :=
  range_pointsMap_ι_reducedClosedSubspaceOfChart B S hS
    (Classical.choose_spec (Classical.choose_spec hX.exists_atlas)).1
    (Classical.choose_spec (Classical.choose_spec hX.exists_atlas)).2 T hT

/-- **The reduced closed subspace is reduced**, in the étale-local sense of Stacks 03E6. -/
@[stacks 03IQ "property (b): the subspace is reduced"]
theorem hasEtaleLocalProperty_isReduced_reducedClosedSubspace
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) (T : Set (points B S hS X)) (hT : IsClosed T) :
    HasEtaleLocalProperty B S hS (reducedClosedSubspace B S hS X hX T hT).toFunctor
      (fun Y : Scheme.{u} => IsReduced Y) :=
  hasEtaleLocalProperty_isReduced_reducedClosedSubspaceOfChart B S hS
    (Classical.choose_spec (Classical.choose_spec hX.exists_atlas)).1
    (Classical.choose_spec (Classical.choose_spec hX.exists_atlas)).2 T hT

/-- Effective descent at the closed immersions follows from effective descent at the
immersions, a closed immersion being an immersion. This is the direction in which
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_le` transfers the
hypothesis; it is needed only to feed a consumer which carries the immersion form, since the
closed-immersion form is proved outright by
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion`. -/
private theorem isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion_of_isImmersion
    (hdesc : IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})) :
    IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) := by
  have _hd := Stacks.Descent.isClosedImmersion_descendsAlong_fppf.{u}
  have _hri : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact isEffectiveDescentAlongSurjectiveEtale_of_le hdesc isClosedImmersion_le_isImmersion

/-- **The reduced closed subspace is a closed subspace**, with effective descent for closed
immersions along the surjective étale morphisms of the site taken as an argument — Stacks 02W8
at the closed immersions. That hypothesis is proved outright by
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion`, so the
statement to prefer is `AlgebraicGeometry.Space.isClosedSubspace_reducedClosedSubspace`; this
form is retained for consumers which already carry the hypothesis. -/
theorem isClosedSubspace_reducedClosedSubspace_of_closedImmersionDescent
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) (T : Set (points B S hS X)) (hT : IsClosed T)
    (hdesc : IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})) :
    IsClosedSubspace B S hS (reducedClosedSubspace B S hS X hX T hT) :=
  isClosedSubspace_reducedClosedSubspaceOfChart B S hS
    (Classical.choose_spec (Classical.choose_spec hX.exists_atlas)).1
    (Classical.choose_spec (Classical.choose_spec hX.exists_atlas)).2
    hdesc hX T hT

/-- **The reduced closed subspace is a closed subspace**, unconditionally: the inclusion of
`AlgebraicGeometry.Space.reducedClosedSubspace` into `X` is representable and a closed immersion
after every representable base change.

This is
`AlgebraicGeometry.Space.isClosedSubspace_reducedClosedSubspace_of_closedImmersionDescent` with
its hypothesis discharged by
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion`. -/
@[stacks 03IQ "property (c): the subspace is a closed subspace"]
theorem isClosedSubspace_reducedClosedSubspace
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) (T : Set (points B S hS X)) (hT : IsClosed T) :
    IsClosedSubspace B S hS (reducedClosedSubspace B S hS X hX T hT) :=
  isClosedSubspace_reducedClosedSubspace_of_closedImmersionDescent B S hS X hX T hT
    (isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion B S hS)

/-- **Stacks 03IQ, uniqueness, unconditionally.** A closed subspace of an algebraic space
which is étale-locally reduced and has a given set of points is
`AlgebraicGeometry.Space.reducedClosedSubspace`. -/
@[stacks 03IQ "uniqueness, unconditionally"]
theorem eq_reducedClosedSubspace (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X)
    (T : Set (points B S hS X)) (hT : IsClosed T) (W : Subfunctor X)
    (hWc : IsClosedSubspace B S hS W)
    (hWT : Set.range (pointsMap B S hS W.toFunctor W.ι) = T)
    (hWr : HasEtaleLocalProperty B S hS W.toFunctor (fun Y : Scheme.{u} => IsReduced Y)) :
    W = reducedClosedSubspace B S hS X hX T hT :=
  eq_reducedClosedSubspaceOfChart B S hS
    (Classical.choose_spec (Classical.choose_spec hX.exists_atlas)).1
    (Classical.choose_spec (Classical.choose_spec hX.exists_atlas)).2
    hX T hT W hWc hWT hWr

/-- **Stacks 03IQ**: a closed subset of the points of an algebraic space carries a unique
reduced closed subspace structure, with no hypothesis.

Uniqueness is `AlgebraicGeometry.Space.eq_reducedClosedSubspace`, the witness is the
datum `AlgebraicGeometry.Space.reducedClosedSubspace`, and the closed-subspace clause of
existence is `AlgebraicGeometry.Space.isClosedSubspace_reducedClosedSubspace`, whose own
descent hypothesis is discharged by
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion`. -/
@[stacks 03IQ "existence and uniqueness"]
theorem existsUnique_reducedClosedSubspace
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) (T : Set (points B S hS X)) (hT : IsClosed T) :
    ∃! Z : Subfunctor X,
      IsClosedSubspace B S hS Z ∧
        Set.range (pointsMap B S hS Z.toFunctor Z.ι) = T ∧
          HasEtaleLocalProperty B S hS Z.toFunctor (fun Y : Scheme.{u} => IsReduced Y) :=
  ⟨reducedClosedSubspace B S hS X hX T hT,
    ⟨isClosedSubspace_reducedClosedSubspace B S hS X hX T hT,
      range_pointsMap_ι_reducedClosedSubspace B S hS X hX T hT,
      hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS X hX T hT⟩,
    fun W hW => eq_reducedClosedSubspace B S hS X hX T hT W hW.1 hW.2.1 hW.2.2⟩

/-- **Stacks 03IQ** at the hypothesis of effective descent for immersions. This is
`AlgebraicGeometry.Space.existsUnique_reducedClosedSubspace`, whose hypothesis-free form
supersedes it; it is retained for
`AlgebraicGeometry.Space.existsUnique_reducedInducedSubspace`, which still carries effective
descent for immersions for reasons of its own. New consumers should use the unconditional
statement.

This declaration does **not** carry `@[stacks 03IQ]`: the statement of that tag has no
descent hypothesis. -/
theorem existsUnique_reducedClosedSubspace_of_immersionDescent
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) (T : Set (points B S hS X)) (hT : IsClosed T)
    (hdesc : IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})) :
    ∃! Z : Subfunctor X,
      IsClosedSubspace B S hS Z ∧
        Set.range (pointsMap B S hS Z.toFunctor Z.ι) = T ∧
          HasEtaleLocalProperty B S hS Z.toFunctor (fun Y : Scheme.{u} => IsReduced Y) :=
  ⟨reducedClosedSubspace B S hS X hX T hT,
    ⟨isClosedSubspace_reducedClosedSubspace_of_closedImmersionDescent B S hS X hX T hT
        (isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion_of_isImmersion B S hS hdesc),
      range_pointsMap_ι_reducedClosedSubspace B S hS X hX T hT,
      hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS X hX T hT⟩,
    fun W hW => eq_reducedClosedSubspace B S hS X hX T hT W hW.1 hW.2.1 hW.2.2⟩

end Space

end AlgebraicGeometry

end
