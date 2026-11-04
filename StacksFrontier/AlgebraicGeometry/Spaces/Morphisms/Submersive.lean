module

public import Mathlib.Algebra.MvPolynomial.Cardinal
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.PointTopologyEtaleOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusRelative
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Submersive and universally submersive morphisms of algebraic spaces (Stacks 0412)

A morphism of algebraic spaces over a scheme `S` is *submersive* when the map it induces on
points is a quotient map — submersive in the sense of Stacks 0406, part (2) — and
*universally submersive* when its base change along every morphism from an algebraic space
over `S` is submersive.

Alongside the two definitions this file proves the three permanence properties of universal
submersiveness: a universally submersive morphism is submersive, and both submersiveness and
universal submersiveness are stable under composition and under base change. They are proved
in the shape the open analogue in
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/Open.lean` has them, and rest on the same one
fact about the point topology: a morphism which factors as an isomorphism followed by a
morphism with quotient map on points has quotient map on points itself. For submersiveness
the isomorphism is the inverse of the second projection of the base change along the identity,
for base change it is the pasting isomorphism `W ×_Z (Z ×_Y X) ≅ W ×_Y X`, and for composition
it is the other pasting isomorphism `W ×_Z X ≅ (W ×_Z Y) ×_Y X`.

It then proves that a flat, quasi-compact, surjective morphism is universally submersive, and
that for a *representable* morphism universal submersiveness coincides with universal
submersiveness in the sense of Stacks 03HA, that is, with every represented base change being
a universally submersive morphism of schemes.

## Main definitions

* `AlgebraicGeometry.Space.IsSubmersive`: **Stacks 0412**, part (1).
* `AlgebraicGeometry.Space.UniversallySubmersive`: **Stacks 0412**, part (2).

## Main results

* `AlgebraicGeometry.Space.isQuotientMap_pointsMap_of_comp_isIso`: a morphism which becomes one
  with quotient map on points after precomposition with an isomorphism has quotient map on
  points.
* `AlgebraicGeometry.Space.isQuotientMap_pointsMap_of_pullback_fst_id`: if the base change of
  `f` along the identity of its target has quotient map on points, so does `f`.
* `AlgebraicGeometry.Space.isQuotientMap_pointsMap_pullback_fst_pullback_fst`: if the base
  change of `f : X ⟶ Y` along a composite `w ≫ g` has quotient map on points, so does the base
  change along `w` of the base change along `g`.
* `AlgebraicGeometry.Space.isSubmersive_of_universallySubmersive`: a universally submersive
  morphism of algebraic spaces is submersive.
* `AlgebraicGeometry.Space.IsSubmersive.comp` and
  `AlgebraicGeometry.Space.universallySubmersive_comp` are the two assertions of
  **Stacks 0CFS**.
* `AlgebraicGeometry.Space.universallySubmersive_pullback` is **Stacks 0CFR**.
* `AlgebraicGeometry.Space.isOpen_iff_isOpen_preimage_pointsMap`,
  `AlgebraicGeometry.Space.isClosed_iff_isClosed_preimage_pointsMap`,
  `AlgebraicGeometry.Space.isSubmersive_of_isFlat_of_isQuasiCompact_of_isSurjective` and
  `AlgebraicGeometry.Space.universallySubmersive_of_isFlat_of_isQuasiCompact_of_isSurjective`
  are the four assertions of **Stacks 0413**.
* `AlgebraicGeometry.Space.presheaf_universallySubmersive_iff_universallySubmersive` is
  **Stacks 0CFQ**, the comparison of the two notions for a representable morphism.
* `AlgebraicGeometry.Space.isQuotientMap_pointsMap_yoneda_iff`: the map on points of a morphism
  of the site is a quotient map exactly when the underlying map of schemes is.

## Implementation notes

The point set is `AlgebraicGeometry.Space.points` of Stacks 03BU and the induced map is
`AlgebraicGeometry.Space.pointsMap`. The topology is
`AlgebraicGeometry.Space.pointTopology`, the topology detected by scheme-valued points, which
is the topology every family satisfying the three clauses of Stacks 03BX assigns to an
algebraic space by `AlgebraicGeometry.Space.PointTopologyFamily.topology_eq`; so the
predicates below are about the topology the source's definition of submersiveness is about,
and nothing here rests on a `Classical.choose`.

Submersiveness of a continuous map is `Topology.IsQuotientMap`, following the routing of
Stacks 0406, part (2), recorded in `StacksCore/Topology/Defs/Induced.lean`.

As in the open case the predicates are stated for arbitrary morphisms of presheaves on the big
fppf site of `S`, algebraicity of the source and target being imposed by clients, and they are
abbreviations, so that a client may use the `Topology.IsQuotientMap` API without a conversion
lemma. Algebraicity of the covering object `Z` *is* part of the universal condition and is
therefore a hypothesis of the quantifier, as in the source.

`AlgebraicGeometry.Space.pointTopology` is a `def`, not an instance. The definitions supply it
with `letI`; the results that follow install it as a local instance instead, so that
`Topology.IsQuotientMap` and `Continuous` elaborate without explicit topology arguments.

The reverse implication of Stacks 0CFQ has to produce
`CategoryTheory.MorphismProperty.universally`, whose quantifier runs over base changes by
*arbitrary* schemes, from a condition that only sees the schemes inside the size cutoff of the
site. The section on the affine-space test supplies that step: it is the quotient-map
counterpart of `AlgebraicGeometry.universallyClosed_of_bounded_closed_baseChanges`, and its
statements are about schemes alone. They are kept private here, next to their one consumer,
rather than stated as library results about affine space.

## References

* [Stacks Project, Tag 0412](https://stacks.math.columbia.edu/tag/0412)
* [Stacks Project, Tag 0413](https://stacks.math.columbia.edu/tag/0413)
* [Stacks Project, Tag 0CFQ](https://stacks.math.columbia.edu/tag/0CFQ)
* [Stacks Project, Tag 0CFR](https://stacks.math.columbia.edu/tag/0CFR)
* [Stacks Project, Tag 0CFS](https://stacks.math.columbia.edu/tag/0CFS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### Submersive and universally submersive morphisms -/

section Defs

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 0412, part (1).** A morphism of algebraic spaces over `S` is *submersive* when the
map it induces on points is a quotient map for the topology detected by scheme-valued points.

This is unrelated to the notion of a submersion of differential manifolds. -/
@[stacks 0412 "part (1): submersive", sga "1 IX 2.1" "submersive", ega "IV 15.7.8" "more general"]
abbrev IsSubmersive (f : F ⟶ G) : Prop :=
  letI := pointTopology B S hS F
  letI := pointTopology B S hS G
  Topology.IsQuotientMap (pointsMap B S hS F f)

/-- **Stacks 0412, part (2).** A morphism of algebraic spaces over `S` is *universally
submersive* when its base change along every morphism to its target from an algebraic space
over `S` is submersive. -/
@[stacks 0412 "part (2): universally submersive", sga "1 IX 2.1" "univ. submersive"]
abbrev UniversallySubmersive (f : F ⟶ G) : Prop :=
  ∀ (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS Z →
    ∀ g : Z ⟶ G, IsSubmersive B S hS (pullback.fst g f)

end Defs

/-! ### Submersiveness on points of a base change -/

section Comparisons

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- If a morphism of presheaves on the big fppf site of `S` becomes, after precomposition with
an isomorphism, a morphism whose map on points is a quotient map, then its own map on points is
a quotient map: the map on points of an isomorphism is a homeomorphism by
`AlgebraicGeometry.Space.pointsHomeomorphOfIso`. -/
theorem isQuotientMap_pointsMap_of_comp_isIso {F F' G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : F ⟶ F') [IsIso e] {g : F' ⟶ G} {f : F ⟶ G} (hfg : e ≫ g = f)
    (hg : Topology.IsQuotientMap (pointsMap B S hS F' g)) :
    Topology.IsQuotientMap (pointsMap B S hS F f) := by
  subst hfg
  rw [pointsMap_comp]
  exact hg.comp (pointsHomeomorphOfIso B S hS (asIso e)).isQuotientMap

/-- **Stacks 0412.** If the base change of `f : X ⟶ Y` along the identity of `Y` has quotient
map on points, then so does `f`: the second projection of that base change is an isomorphism
which identifies its first projection with `f`.

Applied to the instance at the identity of `Y` of the quantifier defining universal
submersiveness, this says that a universally submersive morphism of algebraic spaces is
submersive. -/
theorem isQuotientMap_pointsMap_of_pullback_fst_id {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y)
    (h : Topology.IsQuotientMap
      (pointsMap B S hS (pullback (𝟙 Y) f) (pullback.fst (𝟙 Y) f))) :
    Topology.IsQuotientMap (pointsMap B S hS X f) := by
  refine isQuotientMap_pointsMap_of_comp_isIso B S hS (inv (pullback.snd (𝟙 Y) f)) ?_ h
  have hc : pullback.fst (𝟙 Y) f = pullback.snd (𝟙 Y) f ≫ f := by
    simpa using pullback.condition (f := 𝟙 Y) (g := f)
  rw [hc, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

/-- **Stacks 0CFR.** If the base change of `f : X ⟶ Y` along a composite `w ≫ g` has quotient
map on points, then so does the base change along `w` of the base change along `g`: the pasting
isomorphism `W ×_Z (Z ×_Y X) ≅ W ×_Y X` identifies the two first projections to `W`. -/
theorem isQuotientMap_pointsMap_pullback_fst_pullback_fst
    {X Y Z W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (g : Z ⟶ Y) (w : W ⟶ Z)
    (h : Topology.IsQuotientMap
      (pointsMap B S hS (pullback (w ≫ g) f) (pullback.fst (w ≫ g) f))) :
    Topology.IsQuotientMap (pointsMap B S hS (pullback w (pullback.fst g f))
      (pullback.fst w (pullback.fst g f))) :=
  isQuotientMap_pointsMap_of_comp_isIso B S hS (pullbackRightPullbackFstIso g f w).hom
    (pullbackRightPullbackFstIso_hom_fst g f w) h

/-- For a morphism of the big fppf site of `S`, the induced map on points is a quotient map for
the point topology exactly when the underlying map of schemes is a quotient map: the two are
conjugate by the homeomorphisms of `AlgebraicGeometry.Space.schemePointsHomeomorph`. -/
theorem isQuotientMap_pointsMap_yoneda_iff {U V : BigFppfOver B S hS} (h : U ⟶ V) :
    Topology.IsQuotientMap (pointsMap B S hS (yoneda.obj U) (yoneda.map h)) ↔
      Topology.IsQuotientMap ⇑((BigFppfOver.toScheme B S hS).map h) := by
  rw [pointsMap_yoneda_eq_conj]
  refine ⟨fun hq => ?_, fun hq =>
    (schemePointsHomeomorph B S hS V).symm.isQuotientMap.comp
      (hq.comp (schemePointsHomeomorph B S hS U).isQuotientMap)⟩
  have heq : ⇑((BigFppfOver.toScheme B S hS).map h) =
      (schemePointsHomeomorph B S hS V) ∘
        ((schemePointsHomeomorph B S hS V).symm ∘
          ⇑((BigFppfOver.toScheme B S hS).map h) ∘
            (schemePointsHomeomorph B S hS U)) ∘
        (schemePointsHomeomorph B S hS U).symm := by
    funext x; simp
  rw [heq]
  exact (schemePointsHomeomorph B S hS V).isQuotientMap.comp
    (hq.comp (schemePointsHomeomorph B S hS U).symm.isQuotientMap)

end Comparisons

/-! ### Permanence properties of submersiveness and universal submersiveness -/

section Permanence

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A universally submersive morphism of algebraic spaces over `S` is submersive: it is the
instance of the defining quantifier at the identity of the target, whose base change has second
projection an isomorphism. -/
theorem isSubmersive_of_universallySubmersive (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G)
    (hf : UniversallySubmersive B S hS f) :
    IsSubmersive B S hS f :=
  isQuotientMap_pointsMap_of_pullback_fst_id B S hS f (hf G hG (𝟙 G))

/-- **Stacks 0CFS, submersive morphisms.** A composition of submersive morphisms of algebraic
spaces over `S` is submersive: the map on points of a composition is the composition of the
maps on points. -/
@[stacks 0CFS "submersive"]
theorem IsSubmersive.comp {f : F ⟶ G} {g : G ⟶ H} (hg : IsSubmersive B S hS g)
    (hf : IsSubmersive B S hS f) :
    IsSubmersive B S hS (f ≫ g) := by
  show Topology.IsQuotientMap (pointsMap B S hS F (f ≫ g))
  rw [pointsMap_comp]
  exact Topology.IsQuotientMap.comp hg hf

/-- **Stacks 0CFR.** A base change of a universally submersive morphism of algebraic spaces
over `S` is universally submersive.

Nothing is needed beyond unwinding the definition: a base change of `Z ×_Y X ⟶ Z` along
`k : W ⟶ Z` is a base change of `X ⟶ Y` along `k ≫ g`. -/
@[stacks 0CFR]
theorem universallySubmersive_pullback {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (_hX : IsAlgebraicSpace B S hS X) (_hY : IsAlgebraicSpace B S hS Y)
    (_hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Z ⟶ Y)
    (hf : UniversallySubmersive B S hS f) :
    UniversallySubmersive B S hS (pullback.fst g f) := fun W hW k ↦
  isQuotientMap_pointsMap_pullback_fst_pullback_fst B S hS f g k (hf W hW (k ≫ g))

/-- **Stacks 0CFS, universally submersive morphisms.** A composition of universally submersive
morphisms of algebraic spaces over `S` is universally submersive.

The base change `W ×_Z X ⟶ W` of the composite along `k : W ⟶ Z` is identified by the pasting
isomorphism `W ×_Z X ≅ (W ×_Z Y) ×_Y X` with the composition of a base change of `X ⟶ Y` and a
base change of `Y ⟶ Z`. -/
@[stacks 0CFS "universally submersive"]
theorem universallySubmersive_comp {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (_hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : UniversallySubmersive B S hS f) (hg : UniversallySubmersive B S hS g) :
    UniversallySubmersive B S hS (f ≫ g) := by
  intro W hW k
  have hP : IsAlgebraicSpace B S hS (pullback k g) :=
    isAlgebraicSpace_pullback B S hS k g hW hY hZ
  exact isQuotientMap_pointsMap_of_comp_isIso B S hS (pullbackLeftPullbackSndIso k g f).inv
    (pullbackLeftPullbackSndIso_inv_fst k g f)
    (IsSubmersive.comp B S hS (hg W hW k) (hf (pullback k g) hP (pullback.snd k g)))

end Permanence

/-! ### Flat quasi-compact surjective morphisms are universally submersive -/

section Fpqc

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A base change of a flat morphism of algebraic spaces over `S` is flat. -/
private theorem isFlat_pullback_fst {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Z ⟶ Y) (hflat : IsFlat B S hS f) :
    IsFlat B S hS (pullback.fst g f) :=
  (isFlat_isStableUnderBaseChange B S hS).of_isPullback
    (AlgebraicSpaces.isPullback_fiberProduct B S hS
      (ObjectProperty.homMk g : (⟨Z, hZ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
      (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)).flip hflat

/-- **Stacks 0413 on an affine chart.** If a subset `T` of the points of `Y` has open inverse
image under a flat, quasi-compact, surjective `f : X ⟶ Y`, then its inverse image under any
morphism to `Y` from a presheaf represented by an object of the site with affine underlying
scheme is open.

This is the heart of Stacks 0413. An affine object is quasi-compact, so quasi-compactness of
`f` makes the base change `A ×_Y X` quasi-compact and Stacks 03H6 provides an *affine* étale
surjective chart `W ⟶ A ×_Y X`; the composite `W ⟶ A` is then a flat surjective morphism of
affine schemes, hence quasi-compact, hence a quotient map of schemes by Stacks 02JY. Openness
is read back along it: the inverse image of `T` in `W` also computes through `X`, where it is
open by hypothesis. -/
private theorem isOpen_preimage_pointsMap_of_isAffine
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hflat : IsFlat B S hS f) (hqc : IsQuasiCompact B S hS f) (hsurj : IsSurjective B S hS f)
    {T : Set (points B S hS Y)} (hT : IsOpen (pointsMap B S hS X f ⁻¹' T))
    (A : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj A)]
    (g : yoneda.obj A ⟶ Y) :
    IsOpen (pointsMap B S hS (yoneda.obj A) g ⁻¹' T) := by
  have hA : IsAlgebraicSpace B S hS (yoneda.obj A) := isAlgebraicSpace_yoneda B S hS A
  have hP : IsAlgebraicSpace B S hS (pullback g f) :=
    isAlgebraicSpace_pullback B S hS g f hA hX hY
  obtain ⟨W, i, hWaff, hiSurj, hiEtale⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS _ hP).mp
      (hqc _ hA ((isQuasiCompactSpace_iff_compactSpace_points B S hS _ hA).mpr
        (compactSpace_points_yoneda B S hS A)) g)
  have hfstflat := isFlat_pullback_fst B S hS hX hY hA f g hflat
  obtain ⟨e, he⟩ : ∃ e : W ⟶ A, yoneda.map e = i ≫ pullback.fst g f :=
    ⟨yoneda.preimage _, yoneda.map_preimage _⟩
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj W) := hWaff
  have : Flat ((BigFppfOver.toScheme B S hS).map e) :=
    (holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      AlgebraicGeometry.Flat.isEtaleLocalOnSourceAndTarget e).mp
      (he ▸ isFlat_comp B S hS (isAlgebraicSpace_yoneda B S hS W) hP hA i (pullback.fst g f)
        (isFlat_of_isEtale B S hS hiEtale) hfstflat)
  have : Surjective ((BigFppfOver.toScheme B S hS).map e) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ e).mp
      ((surjective_yonedaMap_iff_surjective_pointsMap B S hS e).mpr
        (he ▸ isSurjective_comp B S hS (isSurjective_of_presheafSurjective B S hS i hiSurj)
          (surjective_pointsMap_of_isPullback B S hS (IsPullback.of_hasPullback g f).flip hsurj)))
  have hquot : Topology.IsQuotientMap (pointsMap B S hS (yoneda.obj W) (i ≫ pullback.fst g f)) :=
    he ▸ (isQuotientMap_pointsMap_yoneda_iff B S hS e).mpr
      (AlgebraicGeometry.Flat.isQuotientMap_of_surjective _)
  rw [← hquot.isOpen_preimage, ← Set.preimage_comp, ← pointsMap_comp,
    show (i ≫ pullback.fst g f) ≫ g = (i ≫ pullback.snd g f) ≫ f by
      simp only [Category.assoc, pullback.condition],
    pointsMap_comp, Set.preimage_comp]
  exact hT.preimage (continuous_pointsMap B S hS (i ≫ pullback.snd g f))

/-- **Stacks 0413, open subsets.** A subset of the points of the target of a flat,
quasi-compact, surjective morphism of algebraic spaces over `S` is open exactly when its
inverse image on points is open.

Openness in the point topology is tested on the presheaves represented by the objects of the
site, and openness there is openness in the representing scheme, hence local on its affine
opens; those affine opens are objects of the site with affine underlying scheme, so
`AlgebraicGeometry.Space.isOpen_preimage_pointsMap_of_isAffine` applies to each. -/
@[stacks 0413 "open subsets",
  ega "IV 2.3.12" "open case",
  sga "1 VIII 4.3" "open subsets",
  sga "1 IX 2.2" "flat qc case, open"]
theorem isOpen_iff_isOpen_preimage_pointsMap
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hflat : IsFlat B S hS f) (hqc : IsQuasiCompact B S hS f) (hsurj : IsSurjective B S hS f)
    (T : Set (points B S hS Y)) :
    IsOpen T ↔ IsOpen (pointsMap B S hS X f ⁻¹' T) := by
  refine ⟨fun hT ↦ hT.preimage (continuous_pointsMap B S hS f), fun hT ↦ ?_⟩
  rw [isOpen_pointTopology_iff]
  intro A a
  rw [← isOpen_yoneda_iff_isSchemeOpen,
    ← (schemePointsHomeomorph B S hS A).symm.isOpen_preimage, isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨-, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    ((BigFppfOver.toScheme B S hS).obj A).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ x) isOpen_univ
  obtain ⟨A', u, huimm, hurange, huaff⟩ :=
    BigFppfOver.exists_affineOpen_restrict B S hS A ⟨U, hU⟩
  have := huimm
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj A') := huaff
  have hpre : (BigFppfOver.toScheme B S hS).map u ⁻¹'
      ((schemePointsHomeomorph B S hS A).symm ⁻¹'
        (pointsMap B S hS (yoneda.obj A) a ⁻¹' T)) =
      (schemePointsHomeomorph B S hS A').symm ⁻¹'
        (pointsMap B S hS (yoneda.obj A') (yoneda.map u ≫ a) ⁻¹' T) := by
    ext y
    simp only [Set.mem_preimage, pointsMap_comp, Function.comp_apply, pointsMap_yoneda_eq_conj,
      Homeomorph.apply_symm_apply]
  have hopen := (isOpen_preimage_pointsMap_of_isAffine B S hS hX hY f hflat hqc hsurj hT A'
    (yoneda.map u ≫ a)).preimage (schemePointsHomeomorph B S hS A').symm.continuous
  rw [← hpre] at hopen
  refine ⟨(BigFppfOver.toScheme B S hS).map u '' _, Set.image_preimage_subset _ _,
    ((BigFppfOver.toScheme B S hS).map u).isOpenEmbedding.isOpenMap _ hopen, ?_⟩
  obtain ⟨y, hy⟩ : x ∈ Set.range ((BigFppfOver.toScheme B S hS).map u) := hurange ▸ hxU
  exact ⟨y, by rw [Set.mem_preimage, hy]; exact hx, hy⟩

/-- **Stacks 0413, closed subsets.** A subset of the points of the target of a flat,
quasi-compact, surjective morphism of algebraic spaces over `S` is closed exactly when its
inverse image on points is closed. This is
`AlgebraicGeometry.Space.isOpen_iff_isOpen_preimage_pointsMap` at the complement. -/
@[stacks 0413 "closed subsets",
  ega "IV 2.3.12" "closed case",
  sga "1 VIII 4.3" "closed subsets",
  sga "1 IX 2.2" "flat qc case, closed"]
theorem isClosed_iff_isClosed_preimage_pointsMap
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hflat : IsFlat B S hS f) (hqc : IsQuasiCompact B S hS f) (hsurj : IsSurjective B S hS f)
    (T : Set (points B S hS Y)) :
    IsClosed T ↔ IsClosed (pointsMap B S hS X f ⁻¹' T) := by
  simpa only [← isOpen_compl_iff, Set.preimage_compl] using
    isOpen_iff_isOpen_preimage_pointsMap B S hS hX hY f hflat hqc hsurj Tᶜ

/-- **Stacks 0413, submersiveness.** A flat, quasi-compact, surjective morphism of algebraic
spaces over `S` is submersive: it is surjective on points, and openness of a subset of the
points of its target is openness of the inverse image. -/
@[stacks 0413 "submersive",
  ega "IV 15.7.8" "fppf ⇒ submersive",
  ega "IV 2.3.12",
  sga "1 VIII 4.3",
  sga "1 IX 2.2" "flat qc submersive"]
theorem isSubmersive_of_isFlat_of_isQuasiCompact_of_isSurjective
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hflat : IsFlat B S hS f) (hqc : IsQuasiCompact B S hS f) (hsurj : IsSurjective B S hS f) :
    IsSubmersive B S hS f := by
  show Topology.IsQuotientMap (pointsMap B S hS X f)
  exact ⟨Topology.IsCoinducing.of_isOpen_preimage_iff_isOpen fun T ↦
    (isOpen_iff_isOpen_preimage_pointsMap B S hS hX hY f hflat hqc hsurj T).symm, hsurj⟩

/-- **Stacks 0413, universal submersiveness.** A flat, quasi-compact, surjective morphism of
algebraic spaces over `S` is universally submersive: each of the three hypotheses is stable
under base change, by Stacks 03MO, Stacks 03HF and Stacks 03MH. -/
@[stacks 0413 "universally submersive"]
theorem universallySubmersive_of_isFlat_of_isQuasiCompact_of_isSurjective
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hflat : IsFlat B S hS f) (hqc : IsQuasiCompact B S hS f) (hsurj : IsSurjective B S hS f) :
    UniversallySubmersive B S hS f := by
  intro Z hZ g
  exact isSubmersive_of_isFlat_of_isQuasiCompact_of_isSurjective B S hS
    (isAlgebraicSpace_pullback B S hS g f hZ hX hY) hZ (pullback.fst g f)
    (isFlat_pullback_fst B S hS hX hY hZ f g hflat)
    (isQuasiCompact_of_isPullback B S hS (IsPullback.of_hasPullback g f).flip hqc)
    (surjective_pointsMap_of_isPullback B S hS (IsPullback.of_hasPullback g f).flip hsurj)

end Fpqc

/-! ### Universal quotient maps of schemes are tested on affine spaces

The statements of this section are about schemes only, and are the input the size-cutoff step
of Stacks 0CFQ needs: a base change of a morphism of schemes along a morphism from an
*arbitrary* scheme is a quotient map as soon as the base changes along the projections of the
affine spaces over its target are, and those are controlled inside the size cutoff of the site
by a cofinality argument. They are the quotient-map counterpart of
`AlgebraicGeometry.universallyClosed_of_bounded_closed_baseChanges`.
-/

section AffineSpaceTests

open Opposite

/-- Reindexing affine space along a map of index types is an affine morphism. -/
private lemma isAffineHom_reindex {I J : Type u} (i : J → I) (X : Scheme.{u}) :
    AlgebraicGeometry.IsAffineHom (AffineSpace.reindex i X) := by
  have : AlgebraicGeometry.IsAffineHom (AffineSpace.reindex i X ≫ 𝔸(J; X) ↘ X) := by
    rw [AffineSpace.reindex_over]; infer_instance
  exact AlgebraicGeometry.IsAffineHom.of_comp _ (𝔸(J; X) ↘ X)

/-- Reindexing twice is reindexing along the composite. -/
private lemma reindex_comp_fun {I J K : Type u} (i : J → I) (j : K → J) (X : Scheme.{u}) :
    AffineSpace.reindex i X ≫ AffineSpace.reindex j X =
      AffineSpace.reindex (i ∘ j) X := by
  simpa only [types_comp, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk] using
    (AffineSpace.reindex_comp (TypeCat.ofHom j) (TypeCat.ofHom i) X).symm

/-- The diagram of the affine spaces over `X` indexed by the finite subsets of `I`, with the
reindexing morphisms between them. -/
private noncomputable abbrev affineSpaceFiniteDiagram (I : Type u) (X : Scheme.{u}) :
    (Finset I)ᵒᵖ ⥤ Scheme.{u} where
  obj J := 𝔸(J.unop; X)
  map {J K} h := AffineSpace.reindex (fun i : K.unop =>
    (⟨i.1, (leOfHom h.unop) i.2⟩ : J.unop)) X
  map_id J := by
    apply AffineSpace.hom_ext <;> simp
  map_comp h k := by
    rw [reindex_comp_fun]
    congr 1

/-- Affine space on `I` is a cone over `AlgebraicGeometry.Space.affineSpaceFiniteDiagram`. -/
private noncomputable abbrev affineSpaceFiniteCone (I : Type u) (X : Scheme.{u}) :
    Cone (affineSpaceFiniteDiagram I X) where
  pt := 𝔸(I; X)
  π := {
    app J := AffineSpace.reindex (Subtype.val : J.unop → I) X
    naturality {J K} h := by
      dsimp [affineSpaceFiniteDiagram]
      simp only [Category.id_comp]
      rw [reindex_comp_fun]; congr 1 }

/-- Affine space on `I` is the limit of the affine spaces on the finite subsets of `I`: a
morphism into it is the same thing as its value on the empty subset together with one
coordinate function for each element of `I`. -/
private noncomputable abbrev affineSpaceFiniteConeIsLimit (I : Type u) (X : Scheme.{u}) :
    IsLimit (affineSpaceFiniteCone I X) := by
  classical
  refine {
    lift := fun c => AffineSpace.homOfVector
      (c.π.app (op ∅) ≫ 𝔸((∅ : Finset I); X) ↘ X)
      (fun i => (c.π.app (op {i})).appTop (AffineSpace.coord X ⟨i, by simp⟩))
    fac := ?_
    uniq := ?_ }
  · intro c J
    apply AffineSpace.hom_ext
    · have h := c.w ((homOfLE (Finset.empty_subset J.unop)).op)
      have h' := congrArg (fun f => f ≫ 𝔸((∅ : Finset I); X) ↘ X) h
      simpa [affineSpaceFiniteCone, affineSpaceFiniteDiagram] using h'.symm
    · intro i
      have h := c.w ((homOfLE (Finset.singleton_subset_iff.mpr i.2)).op)
      have h' := congrArg (fun f => f.appTop (AffineSpace.coord X
        (⟨i.1, by simp⟩ : ({i.1} : Finset I)))) h
      change
        (AffineSpace.homOfVector
          (c.π.app (op ∅) ≫ 𝔸((∅ : Finset I); X) ↘ X)
          (fun i => (c.π.app (op {i})).appTop (AffineSpace.coord X ⟨i, by simp⟩)) ≫
          AffineSpace.reindex (Subtype.val : J.unop → I) X).appTop
          (AffineSpace.coord X i) =
        (c.π.app J).appTop (AffineSpace.coord X i)
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        AffineSpace.reindex_appTop_coord, AffineSpace.homOfVector_appTop_coord]
      change
        (c.π.app J ≫
            (affineSpaceFiniteDiagram I X).map
              ((homOfLE (Finset.singleton_subset_iff.mpr i.2)).op)).appTop
            (AffineSpace.coord X (⟨i.1, by simp⟩ : ({i.1} : Finset I))) =
          (c.π.app (op {i.1})).appTop
            (AffineSpace.coord X (⟨i.1, by simp⟩ : ({i.1} : Finset I))) at h'
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        AffineSpace.reindex_appTop_coord] at h'
      exact h'.symm
  · intro c m hm
    dsimp only [affineSpaceFiniteCone] at m hm ⊢
    apply AffineSpace.hom_ext
    · have h := congrArg (fun f => f ≫ 𝔸((∅ : Finset I); X) ↘ X) (hm (op ∅))
      rw [Category.assoc, AffineSpace.reindex_over] at h
      rw [AffineSpace.homOfVector_over]; exact h
    · intro i
      have h := hm (op {i})
      change m ≫ AffineSpace.reindex (Subtype.val : ({i} : Finset I) → I) X = _ at h
      have h' := congrArg (fun f => f.appTop (AffineSpace.coord X
        (⟨i, by simp⟩ : ({i} : Finset I)))) h
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        AffineSpace.reindex_appTop_coord] at h'
      rw [AffineSpace.homOfVector_appTop_coord]; exact h'

/-- A quasi-compact open of affine space on `I` comes from a finite subset of `I`. -/
private lemma exists_finite_preimage_open (I : Type u) (X : Scheme.{u})
    (U : (𝔸(I; X)).Opens) (hU : IsCompact (U : Set (𝔸(I; X)))) :
    ∃ (J : Finset I) (V : (𝔸(J; X)).Opens),
      (AffineSpace.reindex (Subtype.val : J → I) X) ⁻¹ᵁ V = U := by
  let D := affineSpaceFiniteDiagram I X
  let {i j : (Finset I)ᵒᵖ} (f : i ⟶ j) : AlgebraicGeometry.IsAffineHom (D.map f) :=
    isAffineHom_reindex _ X
  obtain ⟨J, V, _, h⟩ := exists_preimage_eq D (affineSpaceFiniteCone I X)
    (affineSpaceFiniteConeIsLimit I X) U hU
  exact ⟨J.unop, V, h⟩

/-- A union of fewer than `κ` finite subsets has cardinality less than `κ`, for `κ`
uncountable. -/
private lemma mk_iUnion_finset_lt {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 < κ) {A I : Type u}
    (hA : Cardinal.mk A < κ) (F : A → Finset I) :
    Cardinal.mk (⋃ a, (F a : Set I)) < κ := by
  refine (Cardinal.mk_iUnion_le _).trans_lt ?_
  exact Cardinal.mul_lt_of_lt hκ.le hA <|
    (ciSup_le' fun a => (Cardinal.lt_aleph0_of_finite (F a)).le).trans_lt hκ

/-- A supremum of opens of affine space on `I`, each coming from a subset `F a` of `I`, comes
from the union of these subsets. -/
private lemma exists_preimage_iSup_eq {A : Sort*} {I : Type u} (X : Scheme.{u})
    (U : A → (𝔸(I; X)).Opens) (F : A → Set I)
    (hU : ∀ a, ∃ V : (𝔸(F a; X)).Opens,
      AffineSpace.reindex (Subtype.val : F a → I) X ⁻¹ᵁ V = U a) :
    ∃ V : (𝔸(⋃ a, F a; X)).Opens,
      AffineSpace.reindex (Subtype.val : (⋃ a, F a : Set I) → I) X ⁻¹ᵁ V = ⨆ a, U a := by
  choose V hV using hU
  let inc (a : A) : F a → (⋃ a, F a : Set I) := fun x => ⟨x.1, Set.mem_iUnion.mpr ⟨a, x.2⟩⟩
  refine ⟨⨆ a, AffineSpace.reindex (inc a) X ⁻¹ᵁ V a, ?_⟩
  rw [Scheme.Hom.preimage_iSup]
  refine iSup_congr fun a => ?_
  rw [← Scheme.Hom.comp_preimage, reindex_comp_fun]
  exact hV a

/-- A supremum of fewer than `κ` quasi-compact opens of affine space on `I` comes from a subset
of `I` of cardinality less than `κ`. -/
private lemma exists_small_preimage_iSup {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 < κ)
    {A I : Type u} (hA : Cardinal.mk A < κ) (X : Scheme.{u}) (U : A → (𝔸(I; X)).Opens)
    (hU : ∀ a, IsCompact (U a : Set (𝔸(I; X)))) :
    ∃ (J : Set I), Cardinal.mk J < κ ∧ ∃ V : (𝔸(J; X)).Opens,
      AffineSpace.reindex (Subtype.val : J → I) X ⁻¹ᵁ V = ⨆ a, U a := by
  classical
  choose F V hV using fun a => exists_finite_preimage_open I X (U a) (hU a)
  exact ⟨_, mk_iUnion_finset_lt hκ hA F, exists_preimage_iSup_eq X U (fun a => (F a : Set I))
    fun a => ⟨V a, hV a⟩⟩

/-- An open of affine space on `I` containing the image of a scheme which is quasi-compact over
a scheme of size less than `κ` contains one coming from a subset of `I` of cardinality less
than `κ` which still contains that image. -/
private lemma exists_small_preimage_open_of_quasiCompact {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 < κ) (I : Type u) (X : Scheme.{u})
    {Z Z₀ : Scheme.{u}} (p : Z ⟶ Z₀) [QuasiCompact p]
    (hZ : Z₀.size < κ) (r : Z ⟶ 𝔸(I; X)) (W : (𝔸(I; X)).Opens)
    (hr : ∀ z, r z ∈ W) :
    ∃ (J : Set I), Cardinal.mk J < κ ∧ ∃ V : (𝔸(J; X)).Opens,
      (∀ z, r z ∈ AffineSpace.reindex (Subtype.val : J → I) X ⁻¹ᵁ V) ∧
      AffineSpace.reindex (Subtype.val : J → I) X ⁻¹ᵁ V ≤ W := by
  classical
  let A := { U : (𝔸(I; X)).affineOpens // U.1 ≤ W }
  have hcov : ∀ z : Z, ∃ U : A, r z ∈ U.1.1 := by
    intro z
    obtain ⟨_, ⟨U, hU, rfl⟩, hz, hUW⟩ := (𝔸(I; X)).isBasis_affineOpens.exists_subset_of_mem_open
      (hr z) W.isOpen
    exact ⟨⟨⟨U, hU⟩, hUW⟩, hz⟩
  have hf (U : Z₀.affineOpens) : ∃ F : Finset A,
      (p ⁻¹' (U.1 : Set Z₀)) ⊆ ⋃ a ∈ F, r ⁻¹' (a.1.1 : Set (𝔸(I; X))) :=
    (QuasiCompact.isCompact_preimage (f := p) _ U.1.2 U.2.isCompact).elim_finite_subcover
      _ (fun a => a.1.1.isOpen.preimage r.continuous) fun z _ => Set.mem_iUnion.mpr (hcov z)
  choose F hF using hf
  let A' : Set A := ⋃ U, (F U : Set A)
  have hA' : Cardinal.mk A' < κ :=
    mk_iUnion_finset_lt hκ ((Scheme.mk_affineOpens_le_size Z₀).trans_lt hZ) F
  obtain ⟨J, hJ, V, hV⟩ := exists_small_preimage_iSup hκ hA' X
    (fun a : A' => a.1.1.1) (fun a => a.1.1.2.isCompact)
  refine ⟨J, hJ, V, ?_, ?_⟩
  · intro z
    rw [hV]
    obtain ⟨_, ⟨U, hU, rfl⟩, hz, _⟩ := Z₀.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (p z)) isOpen_univ
    obtain ⟨a, haF, hza⟩ := Set.mem_iUnion₂.mp (hF ⟨U, hU⟩ hz)
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨⟨a, Set.mem_iUnion.mpr ⟨⟨U, hU⟩, haF⟩⟩, hza⟩
  · rw [hV]
    exact iSup_le fun a => a.1.2

/-- Affine space on an index type of cardinality less than `κ` over a scheme of size less than
`κ` has size less than `κ`. -/
private lemma size_affineSpace_lt {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 < κ) {I : Type u}
    (hI : Cardinal.mk I < κ) {X : Scheme.{u}} (hX : X.size < κ) : (𝔸(I; X)).size < κ := by
  apply Scheme.size_pullback_lt _ _ hX
  rw [Scheme.size_Spec]
  refine max_lt hκ (MvPolynomial.cardinalMk_le_max.trans_lt ?_)
  exact max_lt (max_lt (by simpa using hκ) hI) hκ

/-- Reindexing affine space along an injection is surjective: a vector indexed by the smaller
type extends by zero. -/
private lemma surjective_reindex {I J : Type u} (i : J → I) (hi : Function.Injective i)
    (X : Scheme.{u}) : Function.Surjective (AffineSpace.reindex i X) := by
  classical
  let s : 𝔸(J; X) ⟶ 𝔸(I; X) := AffineSpace.homOfVector (𝔸(J; X) ↘ X)
    (Function.extend i (AffineSpace.coord X) 0)
  have hs : s ≫ AffineSpace.reindex i X = 𝟙 _ := by
    apply AffineSpace.hom_ext
    · simp [s]
    · intro j
      show (s ≫ AffineSpace.reindex i X).appTop (AffineSpace.coord X j) =
        AffineSpace.coord X j
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        AffineSpace.reindex_appTop_coord]
      simpa [s] using congrFun (Function.extend_comp hi (AffineSpace.coord X) 0) j
  exact fun x => ⟨s x, by simpa using congrArg (fun t : 𝔸(J; X) ⟶ 𝔸(J; X) => t x) hs⟩

/-- A countable supremum of opens of affine space on `I`, each coming from a subset of `I` of
cardinality less than `κ`, comes from such a subset, provided the cofinality of `κ` is
uncountable. -/
private lemma exists_small_preimage_iSup_nat {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 < κ)
    (hcof : Cardinal.aleph0 < κ.ord.cof) {I : Type u} (X : Scheme.{u})
    (U : ℕ → (𝔸(I; X)).Opens)
    (hU : ∀ n, ∃ (J : Set I), Cardinal.mk J < κ ∧ ∃ V : (𝔸(J; X)).Opens,
      AffineSpace.reindex (Subtype.val : J → I) X ⁻¹ᵁ V = U n) :
    ∃ (J : Set I), Cardinal.mk J < κ ∧ ∃ V : (𝔸(J; X)).Opens,
      AffineSpace.reindex (Subtype.val : J → I) X ⁻¹ᵁ V = ⨆ n, U n := by
  classical
  choose F hF V hV using hU
  refine ⟨⋃ n : ULift.{u} ℕ, F n.down, ?_, ?_⟩
  · refine (Cardinal.mk_iUnion_le _).trans_lt ?_
    exact Cardinal.mul_lt_of_lt hκ.le (by simpa using hκ)
      (Cardinal.iSup_lt_of_lt_cof_ord (by simpa using hcof) fun n => hF n.down)
  · rw [← Equiv.ulift.iSup_comp (g := U)]
    exact exists_preimage_iSup_eq X (fun n : ULift.{u} ℕ => U n.down) (fun n => F n.down)
      fun n => ⟨V n.down, hV n.down⟩

/-- Taking affine space on `I` preserves cartesian squares. -/
private lemma isPullback_affineSpace_map (I : Type u) {W X Y Z : Scheme.{u}} {p : W ⟶ X}
    {q : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (sq : IsPullback p q f g) :
    IsPullback (AffineSpace.map I p) (AffineSpace.map I q)
      (AffineSpace.map I f) (AffineSpace.map I g) := by
  have hw : AffineSpace.map I p ≫ AffineSpace.map I f =
      AffineSpace.map I q ≫ AffineSpace.map I g := by
    rw [← AffineSpace.map_comp, ← AffineSpace.map_comp, sq.w]
  apply (IsPullback.paste_vert_iff (AffineSpace.isPullback_map g) hw).mp
  simpa only [AffineSpace.map_over] using
    (AffineSpace.isPullback_map p).paste_vert sq

/-- One step of the saturation construction: an open `U` of affine space on `I` coming from a
small subset of `I` and contained in `W` is enlarged, inside `W` and still coming from a small
subset, so as to contain the `q`-image of the `p`-preimage of `U`, where `p, q : R ⟶ X` is the
pair of projections of a fibre product of size less than `κ`. -/
private lemma exists_small_open_relation_step {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 < κ)
    (I : Type u) {R X : Scheme.{u}} (hR : R.size < κ) (p q : R ⟶ X)
    (W U : (𝔸(I; X)).Opens)
    (hW : AffineSpace.map I p ⁻¹ᵁ W ≤ AffineSpace.map I q ⁻¹ᵁ W)
    (hUW : U ≤ W)
    (hU : ∃ (J : Set I), Cardinal.mk J < κ ∧ ∃ V : (𝔸(J; X)).Opens,
      AffineSpace.reindex (Subtype.val : J → I) X ⁻¹ᵁ V = U) :
    ∃ (V : (𝔸(I; X)).Opens), V ≤ W ∧
      (AffineSpace.map I p ⁻¹ᵁ U ≤ AffineSpace.map I q ⁻¹ᵁ V) ∧
      ∃ (J : Set I), Cardinal.mk J < κ ∧ ∃ V₀ : (𝔸(J; X)).Opens,
        AffineSpace.reindex (Subtype.val : J → I) X ⁻¹ᵁ V₀ = V := by
  obtain ⟨J, hJ, V, rfl⟩ := hU
  let jR := AffineSpace.reindex (Subtype.val : J → I) R
  let T : (𝔸(J; R)).Opens := AffineSpace.map J p ⁻¹ᵁ V
  let Z : (𝔸(I; R)).Opens := jR ⁻¹ᵁ T
  have hZ : Z = AffineSpace.map I p ⁻¹ᵁ
      (AffineSpace.reindex (Subtype.val : J → I) X ⁻¹ᵁ V) := by
    dsimp [Z, T, jR]
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage,
      AffineSpace.map_reindex]
  let a := jR ∣_ T
  have : AlgebraicGeometry.IsAffineHom a :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @AlgebraicGeometry.IsAffineHom) (isPullback_morphismRestrict jR T).flip
      (isAffineHom_reindex _ R)
  have hT : T.toScheme.size < κ :=
    (Scheme.size_coe_opens_le _ T).trans_lt (size_affineSpace_lt hκ hJ hR)
  let r : Z.toScheme ⟶ 𝔸(I; X) := Z.ι ≫ AffineSpace.map I q
  have hr : ∀ z, r z ∈ W := by
    intro z
    apply hW
    apply (AffineSpace.map I p).preimage_mono hUW
    show z.1 ∈ AffineSpace.map I p ⁻¹ᵁ
      (AffineSpace.reindex (Subtype.val : J → I) X ⁻¹ᵁ V)
    rw [← hZ]
    exact z.2
  obtain ⟨K, hK, O, hO, hOW⟩ :=
    exists_small_preimage_open_of_quasiCompact hκ I X a hT r W hr
  refine ⟨AffineSpace.reindex (Subtype.val : K → I) X ⁻¹ᵁ O, hOW, ?_,
    K, hK, O, rfl⟩
  intro z hz
  have hz' : z ∈ Z := by simpa only [hZ] using hz
  exact hO ⟨z, hz'⟩

/-- Iterating `AlgebraicGeometry.Space.exists_small_open_relation_step` countably often
saturates `U` for the relation induced by `p, q : R ⟶ X`: the resulting open still comes from a
subset of `I` of cardinality less than `κ`, by the uncountable cofinality of `κ`. -/
private lemma exists_small_open_saturated {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 < κ)
    (hcof : Cardinal.aleph0 < κ.ord.cof) (I : Type u) {R X : Scheme.{u}} (hR : R.size < κ)
    (p q : R ⟶ X) (W U : (𝔸(I; X)).Opens)
    (hW : AffineSpace.map I p ⁻¹ᵁ W ≤ AffineSpace.map I q ⁻¹ᵁ W)
    (hUW : U ≤ W)
    (hU : ∃ (J : Set I), Cardinal.mk J < κ ∧ ∃ V : (𝔸(J; X)).Opens,
      AffineSpace.reindex (Subtype.val : J → I) X ⁻¹ᵁ V = U) :
    ∃ (V : (𝔸(I; X)).Opens), U ≤ V ∧ V ≤ W ∧
      (AffineSpace.map I p ⁻¹ᵁ V ≤ AffineSpace.map I q ⁻¹ᵁ V) ∧
      ∃ (J : Set I), Cardinal.mk J < κ ∧ ∃ V₀ : (𝔸(J; X)).Opens,
        AffineSpace.reindex (Subtype.val : J → I) X ⁻¹ᵁ V₀ = V := by
  classical
  let D := { V : (𝔸(I; X)).Opens // V ≤ W ∧
    ∃ (J : Set I), Cardinal.mk J < κ ∧ ∃ V₀ : (𝔸(J; X)).Opens,
      AffineSpace.reindex (Subtype.val : J → I) X ⁻¹ᵁ V₀ = V }
  have hstep (V : D) := exists_small_open_relation_step hκ I hR p q W V.1
    hW V.2.1 V.2.2
  choose next hnext using hstep
  let step : D → D := fun V => ⟨next V, (hnext V).1, (hnext V).2.2⟩
  let seq : ℕ → D := Nat.rec ⟨U, hUW, hU⟩ (fun _ V => step V)
  let V : (𝔸(I; X)).Opens := ⨆ n, (seq n).1
  refine ⟨V, le_iSup (fun n => (seq n).1) 0, iSup_le (fun n => (seq n).2.1), ?_, ?_⟩
  · dsimp [V]
    rw [Scheme.Hom.preimage_iSup, Scheme.Hom.preimage_iSup]
    exact iSup_le fun n => (hnext (seq n)).2.1.trans
      (le_iSup (fun m => AffineSpace.map I q ⁻¹ᵁ (seq m).1) (n + 1))
  · exact exists_small_preimage_iSup_nat hκ hcof X (fun n => (seq n).1)
      (fun n => (seq n).2.2)

/-- The square comparing affine space on `I` with affine space on `J` along a morphism of
schemes is cartesian. -/
private lemma isPullback_affineSpace_reindex {I J : Type u} (i : J → I) {X Y : Scheme.{u}}
    (f : X ⟶ Y) :
    IsPullback (AffineSpace.map I f) (AffineSpace.reindex i X)
      (AffineSpace.reindex i Y) (AffineSpace.map J f) := by
  apply (IsPullback.paste_vert_iff (AffineSpace.isPullback_map (n := J) f)
    (AffineSpace.map_reindex i f)).mp
  simpa using AffineSpace.isPullback_map (n := I) f

/-- The preimage under `AffineSpace.map I f` of a set is saturated for the relation
`X ×_Y X`. -/
private lemma map_fst_preimage_le_map_snd_preimage {I : Type u} {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A : Set (𝔸(I; Y))} (hA : IsOpen (AffineSpace.map I f ⁻¹' A)) :
    AffineSpace.map I (pullback.fst f f) ⁻¹ᵁ ⟨AffineSpace.map I f ⁻¹' A, hA⟩ ≤
      AffineSpace.map I (pullback.snd f f) ⁻¹ᵁ ⟨AffineSpace.map I f ⁻¹' A, hA⟩ := by
  intro z hz
  show AffineSpace.map I f (AffineSpace.map I (pullback.snd f f) z) ∈ A
  change AffineSpace.map I f (AffineSpace.map I (pullback.fst f f) z) ∈ A at hz
  have h := congrArg (fun t : 𝔸(I; pullback f f) ⟶ 𝔸(I; Y) => t z)
    (show AffineSpace.map I (pullback.fst f f) ≫ AffineSpace.map I f =
        AffineSpace.map I (pullback.snd f f) ≫ AffineSpace.map I f by
      rw [← AffineSpace.map_comp, ← AffineSpace.map_comp, pullback.condition])
  exact h ▸ hz

/-- An open of affine space on a subset `J ⊆ I` whose preimage in affine space on `I` is
saturated for the relation `X ×_Y X` is saturated for `AffineSpace.map J f`. -/
private lemma preimage_image_affineSpace_map_eq {I : Type u} {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : Set I) (V : (𝔸(I; X)).Opens) (VJ : (𝔸(J; X)).Opens)
    (hVJ : AffineSpace.reindex (Subtype.val : J → I) X ⁻¹ᵁ VJ = V)
    (hVsat : AffineSpace.map I (pullback.fst f f) ⁻¹ᵁ V ≤
      AffineSpace.map I (pullback.snd f f) ⁻¹ᵁ V) :
    AffineSpace.map J f ⁻¹' (AffineSpace.map J f '' (VJ : Set (𝔸(J; X)))) =
      (VJ : Set (𝔸(J; X))) := by
  let jX := AffineSpace.reindex (Subtype.val : J → I) X
  let jR := AffineSpace.reindex (Subtype.val : J → I) (pullback f f)
  refine subset_antisymm ?_ (Set.subset_preimage_image _ _)
  rintro a ⟨b, hb, hab⟩
  obtain ⟨z, hzp, hzq⟩ := Scheme.exists_preimage_of_isPullback
    (isPullback_affineSpace_map J (IsPullback.of_hasPullback f f)) b a hab
  obtain ⟨z', hz'⟩ :=
    surjective_reindex (Subtype.val : J → I) Subtype.val_injective (pullback f f) z
  have hc (t : pullback f f ⟶ X) : jX (AffineSpace.map I t z') = AffineSpace.map J t z := by
    have h := congrArg (fun k : 𝔸(I; pullback f f) ⟶ 𝔸(J; X) => k z')
      (AffineSpace.map_reindex (Subtype.val : J → I) t)
    change jX (AffineSpace.map I t z') = AffineSpace.map J t (jR z') at h
    rwa [hz'] at h
  have hp : AffineSpace.map I (pullback.fst f f) z' ∈ V := by
    rw [← hVJ]
    show jX (AffineSpace.map I (pullback.fst f f) z') ∈ VJ
    rwa [hc (pullback.fst f f), hzp]
  have hq := hVsat hp
  rw [← hVJ] at hq
  change jX (AffineSpace.map I (pullback.snd f f) z') ∈ VJ at hq
  rwa [hc (pullback.snd f f), hzq] at hq

/-- A base change of a surjective morphism of schemes is surjective. -/
private lemma surjective_of_isPullback {W X Y Z : Scheme.{u}} {p : W ⟶ X} {q : W ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (sq : IsPullback p q f g) [Surjective g] : Surjective p :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Surjective) sq.flip inferInstance

/-- The size-cutoff step. A surjective morphism of schemes `f : X ⟶ Y` with `X` of size less
than `κ` induces a quotient map on affine space over an arbitrary index type `I` as soon as it
does over every subset of `I` of cardinality less than `κ`.

An open of affine space on `I` saturated for the equivalence relation `X ×_Y X` is enlarged, by
`AlgebraicGeometry.Space.exists_small_open_saturated`, to a saturated open coming from a small
subset of `I`, where the hypothesis applies. -/
private lemma quotientMap_affineSpace_map_of_small {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 < κ) (hcof : Cardinal.aleph0 < κ.ord.cof)
    (I : Type u) {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f] (hX : X.size < κ)
    (hQ : ∀ J : Set I, Cardinal.mk J < κ →
      Topology.IsQuotientMap (AffineSpace.map J f)) :
    Topology.IsQuotientMap (AffineSpace.map I f) := by
  classical
  let F := AffineSpace.map I f
  have hsurj : Surjective F := surjective_of_isPullback (AffineSpace.isPullback_map (n := I) f)
  refine ⟨Topology.IsCoinducing.of_isOpen_preimage_iff_isOpen ?_, hsurj.surj⟩
  intro A
  refine ⟨fun hA => ?_, fun hA => hA.preimage F.continuous⟩
  rw [isOpen_iff_forall_mem_open]
  intro y hy
  obtain ⟨x, hxy⟩ := hsurj.surj y
  let W : (𝔸(I; X)).Opens := ⟨F ⁻¹' A, hA⟩
  have hx : x ∈ W := by
    show F x ∈ A
    rwa [hxy]
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
    (𝔸(I; X)).isBasis_affineOpens.exists_subset_of_mem_open hx W.isOpen
  obtain ⟨J₀, V₀, hV₀⟩ := exists_finite_preimage_open I X U hU.isCompact
  obtain ⟨V, hUV, hVW, hVsat, J, hJ, VJ, hVJ⟩ :=
    exists_small_open_saturated hκ hcof I (Scheme.size_pullback_lt f f hX hX)
      (pullback.fst f f) (pullback.snd f f) W U (map_fst_preimage_le_map_snd_preimage f hA) hUW
      ⟨J₀, (Cardinal.lt_aleph0_of_finite J₀).trans hκ, V₀, hV₀⟩
  let jX := AffineSpace.reindex (Subtype.val : J → I) X
  let jY := AffineSpace.reindex (Subtype.val : J → I) Y
  let FJ := AffineSpace.map J f
  have hsat : FJ ⁻¹' (FJ '' (VJ : Set (𝔸(J; X)))) = (VJ : Set (𝔸(J; X))) :=
    preimage_image_affineSpace_map_eq f J V VJ hVJ hVsat
  have hopen : IsOpen (FJ '' (VJ : Set (𝔸(J; X)))) :=
    (hQ J hJ).isCoinducing.isOpen_preimage.mp (by rw [hsat]; exact VJ.isOpen)
  refine ⟨jY ⁻¹' (FJ '' (VJ : Set (𝔸(J; X)))), ?_,
    hopen.preimage jY.continuous, ?_⟩
  · intro z hz
    obtain ⟨a, ha, haz⟩ := hz
    obtain ⟨b, hb₁, hb₂⟩ := Scheme.exists_preimage_of_isPullback
      (isPullback_affineSpace_reindex (Subtype.val : J → I) f) z a haz.symm
    have hb : b ∈ V := by
      rw [← hVJ]
      show jX b ∈ VJ
      rwa [hb₂]
    have h := hVW hb
    change F b ∈ A at h
    rwa [hb₁] at h
  · have hxV := hUV hxU
    rw [← hVJ] at hxV
    refine ⟨jX x, hxV, ?_⟩
    have h := congrArg (fun t : 𝔸(I; X) ⟶ 𝔸(J; Y) => t x)
      (AffineSpace.map_reindex (Subtype.val : J → I) f)
    change jY (F x) = FJ (jX x) at h
    rw [hxy] at h
    exact h.symm

/-- A base change of a quotient map of schemes along a closed immersion is a quotient map. -/
private lemma quotientMap_of_isPullback_closedImmersion {W X Y Z : Scheme.{u}} {p : W ⟶ X}
    {q : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (sq : IsPullback p q f g)
    [AlgebraicGeometry.IsClosedImmersion f] (hg : Topology.IsQuotientMap g) :
    Topology.IsQuotientMap p := by
  have : Surjective g := ⟨hg.surjective⟩
  have := surjective_of_isPullback sq
  have : AlgebraicGeometry.IsClosedImmersion q :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @AlgebraicGeometry.IsClosedImmersion) sq inferInstance
  rw [Topology.isQuotientMap_iff_isClosed]
  refine ⟨Surjective.surj (f := p), fun A => ⟨fun hA => hA.preimage p.continuous, ?_⟩⟩
  intro hA
  apply f.isClosedEmbedding.isClosed_iff_image_isClosed.mpr
  apply (Topology.isQuotientMap_iff_isClosed.mp hg).2 (f '' A) |>.mpr
  rw [← Scheme.image_preimage_eq_of_isPullback sq]
  exact q.isClosedEmbedding.isClosedMap _ hA

/-- A base change of a quotient map of schemes along an open immersion is a quotient map. -/
private lemma quotientMap_of_isPullback_openImmersion {W X Y Z : Scheme.{u}} {p : W ⟶ X}
    {q : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (sq : IsPullback p q f g)
    [AlgebraicGeometry.IsOpenImmersion f] (hg : Topology.IsQuotientMap g) :
    Topology.IsQuotientMap p := by
  have : Surjective g := ⟨hg.surjective⟩
  have := surjective_of_isPullback sq
  have : AlgebraicGeometry.IsOpenImmersion q :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @AlgebraicGeometry.IsOpenImmersion) sq inferInstance
  refine ⟨Topology.IsCoinducing.of_isOpen_preimage_iff_isOpen ?_, Surjective.surj (f := p)⟩
  intro A
  refine ⟨fun hA => ?_, fun hA => hA.preimage p.continuous⟩
  apply f.isOpenEmbedding.isOpen_iff_image_isOpen.mpr
  apply hg.isCoinducing.isOpen_preimage.mp
  rw [← Scheme.image_preimage_eq_of_isPullback sq]
  exact q.isOpenEmbedding.isOpenMap _ hA

/-- A base change of `g : Y ⟶ Z` along a morphism `f : X ⟶ Z` between affine schemes is a
quotient map as soon as every base change of `g` to an affine space over `Z` is: `f` factors as
a closed immersion into affine space on the global sections of `X` followed by the projection,
and `AlgebraicGeometry.Space.quotientMap_of_isPullback_closedImmersion` applies. -/
private lemma quotientMap_of_affineSpace_tests_of_isAffine {W X Y Z : Scheme.{u}} [IsAffine X]
    [IsAffine Z] {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (sq : IsPullback p q f g)
    (hg : ∀ I : Type u, Topology.IsQuotientMap (AffineSpace.map I g)) :
    Topology.IsQuotientMap p := by
  let I := Γ(X, ⊤)
  let c : X ⟶ 𝔸(I; Z) := AffineSpace.homOfVector f id
  have : AlgebraicGeometry.IsClosedImmersion c :=
    AlgebraicGeometry.IsClosedImmersion.of_surjective_of_isAffine c
    (fun x => ⟨AffineSpace.coord Z x, AffineSpace.homOfVector_appTop_coord f id x⟩)
  let r := pullback.fst c (AffineSpace.map I g)
  let t := pullback.snd c (AffineSpace.map I g) ≫ (𝔸(I; Y) ↘ Y)
  have hrt : r ≫ f = t ≫ g := by
    dsimp [r, t]
    rw [← AffineSpace.homOfVector_over f id, ← Category.assoc,
      pullback.condition, Category.assoc, AffineSpace.map_over, Category.assoc]
  let m := sq.lift r t hrt
  have hr : Topology.IsQuotientMap r :=
    quotientMap_of_isPullback_closedImmersion (IsPullback.of_hasPullback c _) (hg I)
  apply Topology.IsQuotientMap.of_comp m.continuous p.continuous
  convert hr using 1
  show (fun x => (m ≫ p) x) = _
  rw [sq.lift_fst]

/-- **The affine-space test.** A base change of a quotient map of schemes `g : Y ⟶ Z` along an
arbitrary morphism `f : X ⟶ Z` is a quotient map as soon as every base change of `g` to an
affine space over `Z` is one.

Quotient maps are Zariski local on the target and detected after restriction to an open of the
source, so the statement reduces to the case of an affine open of `X` mapping into an affine
open of `Z`, which is
`AlgebraicGeometry.Space.quotientMap_of_affineSpace_tests_of_isAffine`. -/
private lemma quotientMap_of_affineSpace_tests {W X Y Z : Scheme.{u}} {p : W ⟶ X} {q : W ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (sq : IsPullback p q f g) (hg : Topology.IsQuotientMap g)
    (hA : ∀ I : Type u, Topology.IsQuotientMap (AffineSpace.map I g)) :
    Topology.IsQuotientMap p := by
  have : Surjective g := ⟨hg.surjective⟩
  have := surjective_of_isPullback sq
  refine ⟨Topology.IsCoinducing.of_isOpen_preimage_iff_isOpen ?_, Surjective.surj (f := p)⟩
  intro A
  refine ⟨fun hpre => ?_, fun h => h.preimage p.continuous⟩
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  change Z.Opens at U
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ f ⁻¹' (U : Set Z) from hxU) (U.isOpen.preimage f.continuous)
  change X.Opens at V
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  let gU := pullback.fst U.ι g
  let fV := f.resLE U V hVU
  have hAU (I : Type u) : Topology.IsQuotientMap (AffineSpace.map I gU) := by
    have : AlgebraicGeometry.IsOpenImmersion (AffineSpace.map I U.ι) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @AlgebraicGeometry.IsOpenImmersion)
        (AffineSpace.isPullback_map U.ι).flip inferInstance
    exact quotientMap_of_isPullback_openImmersion
      (isPullback_affineSpace_map I (IsPullback.of_hasPullback U.ι g)) (hA I)
  let r := pullback.fst fV gU
  let t := pullback.snd fV gU ≫ pullback.snd U.ι g
  have hr : Topology.IsQuotientMap r :=
    quotientMap_of_affineSpace_tests_of_isAffine
      (IsPullback.of_hasPullback fV gU) hAU
  have hrt : (r ≫ V.ι) ≫ f = t ≫ g := by
    dsimp [r, t]
    rw [Category.assoc, ← f.resLE_comp_ι hVU, ← Category.assoc]
    show (pullback.fst fV gU ≫ fV) ≫ U.ι = _
    rw [pullback.condition, Category.assoc, Category.assoc, ← pullback.condition]
  let m := sq.lift (r ≫ V.ι) t hrt
  have hlocal : IsOpen (V.ι ⁻¹' A) := by
    apply hr.isCoinducing.isOpen_preimage.mp
    have heq : r ⁻¹' (V.ι ⁻¹' A) = m ⁻¹' (p ⁻¹' A) := by
      show (r ≫ V.ι) ⁻¹' A = (m ≫ p) ⁻¹' A
      rw [sq.lift_fst]
    rw [heq]
    exact hpre.preimage m.continuous
  exact ⟨V.ι '' (V.ι ⁻¹' A), Set.image_preimage_subset _ _,
    V.ι.isOpenEmbedding.isOpenMap _ hlocal, ⟨x, hxV⟩, hx, rfl⟩

end AffineSpaceTests

/-! ### Representable morphisms -/

section Representable

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of presheaves all of whose represented base changes satisfy `P` has, for each
represented base change, *all* of its own base changes inside the source category satisfying
`P` — which is to say it satisfies `P.universally` relatively. -/
private theorem relative_universally_of_relative {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) [Limits.PreservesLimitsOfShape Limits.WalkingCospan F] (P : MorphismProperty C)
    {X Y : D} {f : X ⟶ Y} (hf : P.relative F f) :
    P.universally.relative F f := by
  refine ⟨hf.1, ?_⟩
  intro U V g k s hpb U' V' i₁ i₂ s' hs'
  exact hf.2 (F.map i₂ ≫ g) (F.map i₁ ≫ k) s' ((hs'.flip.map F).paste_horiz hpb)

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A represented base change of a morphism all of whose base changes by algebraic spaces are
submersive is a quotient map of schemes: the comparison isomorphism identifies it with the base
change along the representable target, and
`AlgebraicGeometry.Space.isQuotientMap_pointsMap_yoneda_iff` descends the conclusion from
points to schemes. -/
private theorem isQuotientMap_of_isPullback_yoneda (f : X ⟶ Y)
    (hf : UniversallySubmersive B S hS f) {U V : BigFppfOver B S hS}
    (g : yoneda.obj U ⟶ Y) (k : yoneda.obj V ⟶ X) (s : V ⟶ U)
    (hpb : IsPullback k (yoneda.map s) f g) :
    Topology.IsQuotientMap ⇑((BigFppfOver.toScheme B S hS).map s) :=
  (isQuotientMap_pointsMap_yoneda_iff B S hS s).mp
    (isQuotientMap_pointsMap_of_comp_isIso B S hS hpb.flip.isoPullback.hom
      hpb.flip.isoPullback_hom_fst (hf (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) g))

/-- A base change inside the size cutoff of the site of a represented base change which is
universally a quotient map along morphisms of the site is a quotient map: a fibre product over
an object of the site with a base inside the cutoff is itself inside the cutoff, so the square
comes from a square of the site. -/
private theorem quotientMap_of_small_baseChange {U V : BigFppfOver B S hS} (s : V ⟶ U)
    (hs : (MorphismProperty.inverseImage
      (topologically @Topology.IsQuotientMap : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).universally s)
    {V' U' : Scheme.{u}}
    (i₁ : V' ⟶ (BigFppfOver.toScheme B S hS).obj V)
    (i₂ : U' ⟶ (BigFppfOver.toScheme B S hS).obj U) (s' : V' ⟶ U')
    (hs' : IsPullback s' i₁ i₂ ((BigFppfOver.toScheme B S hS).map s))
    (hU' : B.Contains U') : Topology.IsQuotientMap s' := by
  have hV' : B.Contains V' := by
    show V'.size < B.cutoff
    rw [Scheme.size_congr hs'.isoPullback]
    exact Scheme.size_pullback_lt _ _ hU' V.left.property
  let UB : B.Schemes := B.obj hU'
  let VB : B.Schemes := B.obj hV'
  let j₂ : UB ⟶ U.left := ObjectProperty.homMk i₂
  let j₁ : VB ⟶ V.left := ObjectProperty.homMk i₁
  let t : VB ⟶ UB := ObjectProperty.homMk s'
  have hw : t ≫ j₂ = j₁ ≫ s.left := by
    apply ObjectProperty.hom_ext
    exact hs'.w
  let UO : BigFppfOver B S hS := Over.mk (j₂ ≫ U.hom)
  let VO : BigFppfOver B S hS := Over.mk (j₁ ≫ V.hom)
  let k₁ : VO ⟶ V := Over.homMk j₁
  let k₂ : UO ⟶ U := Over.homMk j₂
  let tO : VO ⟶ UO := Over.homMk t (by
    dsimp [VO, UO]
    rw [← Category.assoc, hw, Category.assoc, s.w])
  exact hs k₁ k₂ tO (IsPullback.of_map_of_faithful (BigFppfOver.toScheme B S hS) hs')

/-- **Stacks 0CFQ.** A representable morphism `f : X ⟶ Y` of algebraic spaces over `S` is
universally submersive in the sense of Stacks 03HA — each of its represented base changes is a
universally submersive morphism of schemes — if and only if every base change of it by an
algebraic space over `S` is submersive on points, which is universal submersiveness in the
sense of Stacks 0412, part (2).

The implication from left to right chooses a scheme atlas `a : U ⟶ Z` of the base `Z`: the
chosen represented base change of `f` along `a ≫ g` is a quotient map of schemes, hence on
points, and it factors through the base change along `g` by a continuous map, so
`Topology.IsQuotientMap.of_comp` gives the conclusion.

The converse must upgrade quotient-map-ness of the base changes available inside the size
cutoff of the site to the unbounded `CategoryTheory.MorphismProperty.universally`. That is what
the affine-space test `AlgebraicGeometry.Space.quotientMap_of_affineSpace_tests` is for: the
base changes of a represented base change to the affine spaces over its target are inside the
cutoff once the index type is small, by
`AlgebraicGeometry.Space.quotientMap_of_small_baseChange`, and
`AlgebraicGeometry.Space.quotientMap_affineSpace_map_of_small` removes the smallness
restriction. No algebraicity hypothesis on `X` or `Y` is needed, only representability of
`f`. -/
@[stacks 0CFQ]
theorem presheaf_universallySubmersive_iff_universallySubmersive (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f) :
    (MorphismProperty.inverseImage
        ((topologically @Topology.IsQuotientMap : MorphismProperty Scheme.{u}).universally)
        (BigFppfOver.toScheme B S hS)).presheaf f ↔
      UniversallySubmersive B S hS f := by
  classical
  set T := BigFppfOver.toScheme B S hS
  set P : MorphismProperty Scheme.{u} := topologically @Topology.IsQuotientMap
  constructor
  · intro hleft Z hZ g
    obtain ⟨U, a, haSurj, haEtale⟩ := hZ.exists_atlas
    obtain ⟨V, s, t, sq⟩ := hleft.1 (a ≫ g)
    have hs : Topology.IsQuotientMap (pointsMap B S hS (yoneda.obj V) (yoneda.map s)) :=
      (isQuotientMap_pointsMap_yoneda_iff B S hS s).mpr
        (MorphismProperty.universally_le P _ (hleft.2 (a ≫ g) t s sq))
    have ha : Topology.IsQuotientMap (pointsMap B S hS (yoneda.obj U) a) :=
      isQuotientMap_pointsMap_of_presheafEtale B S hS a haEtale
        ((surjective_iff_surjective_pointsMap B S hS Z hZ U a).mp haSurj)
    let β : yoneda.obj V ⟶ pullback g f :=
      pullback.lift (yoneda.map s ≫ a) t (by rw [Category.assoc, sq.w])
    show Topology.IsQuotientMap (pointsMap B S hS (pullback g f) (pullback.fst g f))
    refine Topology.IsQuotientMap.of_comp (continuous_pointsMap B S hS β)
      (continuous_pointsMap B S hS (pullback.fst g f)) ?_
    rw [← pointsMap_comp, pullback.lift_fst, pointsMap_comp]
    exact ha.comp hs
  · intro hright
    refine ⟨hf, ?_⟩
    intro U V g k s hpb
    have hbounded : (P.inverseImage T).universally s :=
      (relative_universally_of_relative yoneda (P.inverseImage T)
        ⟨hf, by
          intro _ _ g' k' t ht
          exact isQuotientMap_of_isPullback_yoneda B S hS f hright g' k' t ht⟩).2 g k s hpb
    have hsQuot : Topology.IsQuotientMap ⇑(T.map s) :=
      isQuotientMap_of_isPullback_yoneda B S hS f hright g k s hpb
    have : Surjective (T.map s) := ⟨hsQuot.surjective⟩
    have hAffine (I : Type u) : Topology.IsQuotientMap (AffineSpace.map I (T.map s)) :=
      quotientMap_affineSpace_map_of_small B.aleph0_lt_cutoff B.aleph0_lt_cutoff_cof I
        (T.map s) V.left.property fun J hJ => quotientMap_of_small_baseChange B S hS s hbounded
        (AffineSpace.over J (T.obj V)).hom (AffineSpace.over J (T.obj U)).hom
        (AffineSpace.map J (T.map s)) (AffineSpace.isPullback_map (T.map s))
        (size_affineSpace_lt B.aleph0_lt_cutoff hJ U.left.property)
    intro U' V' i₁ i₂ s' hs'
    exact quotientMap_of_affineSpace_tests hs' hsQuot hAffine

end Representable

end AlgebraicGeometry.Space

end
