module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.LocalCompleteIntersectionEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection.KoszulLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection.KoszulLocusOnBase

/-!
# The local complete intersection locus on the base, with nothing assumed

Consider a commutative triangle of algebraic spaces over a scheme `S`: a morphism `f : X ⟶ Y`
together with morphisms `p : X ⟶ Z` and `q : Y ⟶ Z` such that `f ≫ q = p`. If `p` is flat,
locally of finite presentation and closed, and `q` is flat and locally of finite presentation,
then there is an open subspace `W` of `Z` through which a morphism `Z' ⟶ Z` factors exactly when
the base change `f_{Z'} : X_{Z'} ⟶ Y_{Z'}` is a local complete intersection morphism. This is
**Stacks 06CE**.

The criterion is available from two hypotheses: étale source locality of the Koszul property of
morphisms of schemes, and the base-change assertion of **Stacks 06CA**. Both are discharged here
— the first by `AlgebraicGeometry.isLocalCompleteIntersectionMorphism_isLocalAtSource_etale`, the
second by `AlgebraicGeometry.Space.setOf_koszulAt_pullbackMap`, which needs only the first — so
the statement of the tag carries no hypothesis beyond those of the source.

## Main results

* `AlgebraicGeometry.Space.koszulLocusStableUnderBaseChange`: the base-change assertion of
  Stacks 06CA holds.
* `AlgebraicGeometry.Space.factorsThrough_koszulLocusOnBase_iff`: a morphism `Z' ⟶ Z` factors
  through `AlgebraicGeometry.Space.koszulLocusOnBase` exactly when the base change of `f` along
  it is a local complete intersection morphism.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_factorsThrough_iff_isLocalCompleteIntersection`
  is **Stacks 06CE** in the existential form of the source.

## Implementation notes

The two spellings of the base change of `f` have to be matched: `Stacks 06CA` is stated for
`CategoryTheory.Limits.pullback.map` with identity maps on `Z'` and on `Z`, and
`AlgebraicGeometry.Space.KoszulLocusStableUnderBaseChange` for
`AlgebraicGeometry.Space.baseChangeOverBase`. The two agree, by the universal property of the
pullback, because composing with an identity changes nothing.

## References

* [Stacks Project, Tag 06CE](https://stacks.math.columbia.edu/tag/06CE)
* [Stacks Project, Tag 06CA](https://stacks.math.columbia.edu/tag/06CA)
* [Stacks Project, Tag 069P](https://stacks.math.columbia.edu/tag/069P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on the big fppf site over `S`, given directly: instance search for
them times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_koszulLocusOnBaseUnconditional :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_koszulLocusOnBaseUnconditional
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_koszulLocusOnBaseUnconditional B S hS).has_limit _

/-- The two spellings of the base change of `f : X ⟶ Y` along `g : Z' ⟶ Z` agree:
`AlgebraicGeometry.Space.baseChangeOverBase` is the map of pullbacks induced by `f` and the
identities of `Z'` and of `Z`. -/
theorem baseChangeOverBase_eq_pullbackMap {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (p : X ⟶ Z) (q : Y ⟶ Z) (hfq : f ≫ q = p) {Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g : Z' ⟶ Z) :
    baseChangeOverBase B S hS f p q hfq g =
      pullback.map p g q g f (𝟙 Z') (𝟙 Z)
        (by simpa only [Category.comp_id] using hfq.symm) (by simp) := by
  refine pullback.hom_ext ?_ ?_ <;>
    simp only [baseChangeOverBase, pullback.map, pullback.lift_fst, pullback.lift_snd,
      Category.comp_id]

/-- **The base-change assertion of Stacks 06CA holds.** For a commutative triangle of algebraic
spaces over `S` with `p` and `q` flat and locally of finite presentation, the base change of `f`
along any `Z' ⟶ Z` is Koszul at a point of `|X ×_Z Z'|` exactly when `f` is Koszul at its image
in `|X|`.

This is `AlgebraicGeometry.Space.setOf_koszulAt_pullbackMap` read at one point, its hypothesis of
étale source locality of the Koszul property of morphisms of schemes supplied by
`AlgebraicGeometry.isLocalCompleteIntersectionMorphism_isLocalAtSource_etale`. -/
@[stacks 06CA "part (2) in the pointwise form the hypothesis of Stacks 06CE asks for"]
theorem koszulLocusStableUnderBaseChange : KoszulLocusStableUnderBaseChange B S hS := by
  intro X Y Z hX hY hZ f p q hfq hpflat hplfp hqflat hqlfp Z' hZ' g x'
  have h := setOf_koszulAt_pullbackMap B S hS
    _root_.AlgebraicGeometry.isLocalCompleteIntersectionMorphism_isLocalAtSource_etale
    hX hY hZ hZ' f p q hfq hpflat hplfp hqflat hqlfp g
  rw [baseChangeOverBase_eq_pullbackMap B S hS f p q hfq g]
  exact Iff.of_eq
    (congrArg (fun t : Set (points B S hS (pullback p g)) => x' ∈ t) h)

variable {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 06CE, with the open subspace named.** Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S` whose source and target are given over a third algebraic space `Z` by morphisms
`p : X ⟶ Z` and `q : Y ⟶ Z` with `f ≫ q = p`. If `p` is flat, locally of finite presentation and
closed and `q` is flat and locally of finite presentation, then a morphism `Z' ⟶ Z` from an
algebraic space factors through `AlgebraicGeometry.Space.koszulLocusOnBase` exactly when the base
change of `f` along it is a local complete intersection morphism. -/
@[stacks 06CE "with the open subspace named rather than quantified over"]
theorem factorsThrough_koszulLocusOnBase_iff
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z) (hfq : f ≫ q = p)
    (hpflat : IsFlat B S hS p) (hplfp : IsLocallyOfFinitePresentation B S hS p)
    (hpc : IsClosedMorphism B S hS p) (hqflat : IsFlat B S hS q)
    (hqlfp : IsLocallyOfFinitePresentation B S hS q)
    (Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ' : IsAlgebraicSpace B S hS Z') (g : Z' ⟶ Z) :
    (∃ r : Z' ⟶ (koszulLocusOnBase B S hS f p).toFunctor,
        r ≫ (koszulLocusOnBase B S hS f p).ι = g) ↔
      IsLocalCompleteIntersection B S hS (baseChangeOverBase B S hS f p q hfq g) :=
  factorsThrough_koszulLocusOnBase_iff_isLocalCompleteIntersection B S hS
    _root_.AlgebraicGeometry.isLocalCompleteIntersectionMorphism_isLocalAtSource_etale
    (koszulLocusStableUnderBaseChange B S hS) hX hY hZ f p q hfq hpflat hplfp hpc hqflat hqlfp
    Z' hZ' g

/-- **Stacks 06CE.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` whose source and
target are given over a third algebraic space `Z` by morphisms `p : X ⟶ Z` and `q : Y ⟶ Z` with
`f ≫ q = p`. If `p` is flat, locally of finite presentation and closed and `q` is flat and
locally of finite presentation, then there is an open subspace `W` of `Z` through which a
morphism `Z' ⟶ Z` from an algebraic space factors exactly when the base change
`f_{Z'} : X_{Z'} ⟶ Y_{Z'}` of `f` along it is a local complete intersection morphism.

The open subspace is `AlgebraicGeometry.Space.koszulLocusOnBase`: the complement of the image
under `p` of the non-Koszul locus of `f`. -/
@[stacks 06CE]
theorem exists_isOpenSubspace_factorsThrough_iff_isLocalCompleteIntersection
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z) (hfq : f ≫ q = p)
    (hpflat : IsFlat B S hS p) (hplfp : IsLocallyOfFinitePresentation B S hS p)
    (hpc : IsClosedMorphism B S hS p) (hqflat : IsFlat B S hS q)
    (hqlfp : IsLocallyOfFinitePresentation B S hS q) :
    ∃ W : Subfunctor Z, IsOpenSubspace B S hS W ∧
      ∀ (Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS Z') (g : Z' ⟶ Z),
        (∃ r : Z' ⟶ W.toFunctor, r ≫ W.ι = g) ↔
          IsLocalCompleteIntersection B S hS (baseChangeOverBase B S hS f p q hfq g) :=
  exists_isOpenSubspace_iff_isLocalCompleteIntersection_baseChange B S hS
    _root_.AlgebraicGeometry.isLocalCompleteIntersectionMorphism_isLocalAtSource_etale
    (koszulLocusStableUnderBaseChange B S hS) hX hY hZ f p q hfq hpflat hplfp hpc hqflat hqlfp

end AlgebraicGeometry.Space

end
