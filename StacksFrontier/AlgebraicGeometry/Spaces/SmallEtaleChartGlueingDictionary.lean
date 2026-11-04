module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartCanonicalGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRestrictionComp

/-!
# The chart-to-slice dictionary and the composition isomorphisms

Stacks 03LS says that a sheaf on the small étale site of an algebraic space `X` is the same thing
as a family of sheaves on the small étale sites of the étale scheme charts of `X` together with
comparison isomorphisms satisfying the cocycle condition.  Stacks 0GWK says the same with the
*slices* `X_étale/U` in place of the charts' small étale sites, and
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalenceClosure` identifies the two
indexings object by object: `AlgebraicGeometry.Space.chartRestriction_overPullbackIso` and
`AlgebraicGeometry.Space.chartInverseImage_overMapPullbackIso`.

What is still missing for the equivalence is that the dictionary is *compatible with the
composition isomorphisms* on both sides, i.e. that it carries
`AlgebraicGeometry.Space.chartRestrictionComp` and
`AlgebraicGeometry.Space.chartInverseImageComp` to `CategoryTheory.Sheaf.pushforwardOverMapIso`
and `CategoryTheory.GrothendieckTopology.overMapPullbackComp`.  This file supplies the
mathematical content of the half of that compatibility which concerns a morphism of charts, and
isolates what is left of it, which is bookkeeping with
`CategoryTheory.Functor.sheafPushforwardContinuousComp'`.

## Main definitions

* `AlgebraicGeometry.Space.chartPostcompSheafIso`: the
  `CategoryTheory.Functor.sheafPushforwardContinuousComp'` half of
  `AlgebraicGeometry.Space.chartInverseImage_overMapPullbackIso`, i.e. the dictionary with the
  comparison of Stacks 03LQ factored out.

## Main results

* `AlgebraicGeometry.Space.chartInverseImageComp_eq`: the chartwise comparison
  `AlgebraicGeometry.Space.chartInverseImageComp` carries no transport at all — it *is* the
  inverse-image composition isomorphism of Stacks 03G2, part (3), for the represented morphisms
  of charts, because `AlgebraicGeometry.Space.chartMap_comp` holds by `rfl`.
* `AlgebraicGeometry.Space.chartInverseImage_overMapPullbackIso_eq`: the dictionary for a
  morphism of charts is the comparison of Stacks 03LQ followed by
  `AlgebraicGeometry.Space.chartPostcompSheafIso`.
* `AlgebraicGeometry.Space.chartInverseImageComp_inverseImageIso`: **the chart-level bridge** —
  the two comparisons of Stacks 03LQ for two composable morphisms of charts, composed
  horizontally, are the chartwise composition comparison followed by the comparison of
  Stacks 03LQ for the composite.  This is the content of the chart-to-slice compatibility for a
  morphism of charts; everything else in it is restriction-along-equal-functors bookkeeping.

## Implementation notes

Three facts about the chart constructions were established by measurement and are what makes
the statements below the shape they are.

First, `AlgebraicGeometry.Space.chartMap_comp` is a *definitional* equality: the morphism of
algebraic spaces represented by a composite of chart morphisms is literally the composite of the
represented morphisms, because `AlgebraicGeometry.Space.comparisonFunctor` is strictly
functorial on the relevant component.  Consequently the `CategoryTheory.eqToIso` in the
definition of `AlgebraicGeometry.Space.chartInverseImageComp` is the identity, which is
`AlgebraicGeometry.Space.chartInverseImageComp_eq`, and the chart-level bridge below needs no
transport.  `AlgebraicGeometry.Space.chartMap_comp_chartToSpace` is *not* definitional — it is
`CategoryTheory.Over.w`, a propositional field — so the corresponding simplification of
`AlgebraicGeometry.Space.chartRestrictionComp` is not available, and the other half of the
dictionary square does carry a genuine transport.

Second, the two readings of the composite of two chartwise restriction functors —
`j_f^* ⋙ j_g^*` and `j_{g ≫ f}^*` — are definitionally equal, but the unifier reaches that
conclusion only if it is led through it in two steps: through
`AlgebraicGeometry.Space.chartPostcompSheaf_comp_eq`, which is restriction along a *composite of
site functors* and holds by `rfl` cheaply, and then through
`AlgebraicGeometry.Space.smallEtalePostcomp_chartMap_comp`, which is strictness of the
Stacks 03LP tower and also holds by `rfl` cheaply.  Asked for in one step the same `rfl` exhausts
the heartbeat limit.  `AlgebraicGeometry.Space.chartPostcompSheaf_comp` is the two-step form, and
every statement here that has to name both readings of the composite goes through it.

Third, the comparison of Stacks 03LQ transports along an equality of morphisms of algebraic
spaces in the way one expects, which is
`AlgebraicGeometry.Space.smallToposMorphism_inverseImageIso_congr`; the proof is a `subst`, and
it is needed because the étaleness hypothesis is a `Prop` and therefore carried silently.

## What was built on the chart-level bridge

The chart-level bridge below is the *content* of the compatibility of the dictionary with the
composition isomorphisms for a morphism of charts.  The rest of that compatibility — the coherence
of the four `CategoryTheory.Functor.sheafPushforwardContinuousComp'` isomorphisms that
`AlgebraicGeometry.Space.chartPostcompSheafIso` is built from — and its companion for the
structure morphism of a chart, where the transport along
`AlgebraicGeometry.Space.chartMap_comp_chartToSpace` survives because that equality is not
definitional, are in
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartDictionaryCoherence`; and the equivalence of
categories of Stacks 03LS itself, `AlgebraicGeometry.Space.chartGlueingEquivalence`, is in
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartGlueingEquivalence`.

## References

* [Stacks Project, Tag 03LS](https://stacks.math.columbia.edu/tag/03LS)
* [Stacks Project, Tag 0GWK](https://stacks.math.columbia.edu/tag/0GWK)
* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Restriction along equal functors of sites -/

/-- Restriction of sheaves of `(u+1)`-types along two *equal* continuous functors of sites is
the same functor.  The two continuity instances need not agree, which is why this is not
`CategoryTheory.congrArg`: continuity is a `Prop`, so they are interchangeable, but the
dependency is still there. -/
theorem sheafPushforwardContinuous_eq_of_functor_eq {C D : Type (u + 1)} [Category.{u} C]
    [Category.{u} D] {F G : C ⥤ D} (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [F.IsContinuous J K] [G.IsContinuous J K] (h : F = G) :
    F.sheafPushforwardContinuous (Type (u + 1)) J K =
      G.sheafPushforwardContinuous (Type (u + 1)) J K := by
  subst h
  rfl

section Congr

variable {A C : AlgebraicSpaces B S hS}

/-- Postcomposition along two equal étale morphisms of algebraic spaces is the same functor of
small étale sites, and restriction along it is the same functor on sheaves. -/
theorem smallEtalePostcomp_sheafPushforwardContinuous_congr {k k' : A ⟶ C}
    (hk : IsEtale B S hS k.hom) (hk' : IsEtale B S hS k'.hom) (e : k = k') :
    (smallEtalePostcomp B S hS k hk).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B S hS A.1) (SmallEtale.topology B S hS C.1) =
      (smallEtalePostcomp B S hS k' hk').sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B S hS A.1) (SmallEtale.topology B S hS C.1) := by
  subst e
  rfl

/-- The comparison of Stacks 03LQ transports along an equality of étale morphisms of algebraic
spaces: the comparison for `k` read through the two induced equalities of functors is the
comparison for `k'`. -/
theorem smallToposMorphism_inverseImageIso_congr {k k' : A ⟶ C} (hk : IsEtale B S hS k.hom)
    (hk' : IsEtale B S hS k'.hom) (e : k = k')
    (h₁ : (smallToposMorphism B S hS k').inverseImage =
      (smallToposMorphism B S hS k).inverseImage) :
    eqToHom h₁ ≫ (smallToposMorphism_inverseImageIso B S hS k hk).hom =
      (smallToposMorphism_inverseImageIso B S hS k' hk').hom ≫
        eqToHom (smallEtalePostcomp_sheafPushforwardContinuous_congr B S hS hk' hk e.symm) := by
  subst e
  simp

/-- Postcomposition along étale morphisms of algebraic spaces composes strictly: this is
`AlgebraicGeometry.Space.smallEtalePostcomp` of the Stacks 03LP tower, restated here because the
module that carries it is not in the import closure of the chart constructions. -/
theorem smallEtalePostcomp_comp_eq {D : AlgebraicSpaces B S hS} (k : D ⟶ A) (l : A ⟶ C)
    (hk : IsEtale B S hS k.hom) (hl : IsEtale B S hS l.hom)
    (hkl : IsEtale B S hS (k ≫ l).hom) :
    smallEtalePostcomp B S hS k hk ⋙ smallEtalePostcomp B S hS l hl =
      smallEtalePostcomp B S hS (k ≫ l) hkl :=
  rfl

end Congr

variable (X : AlgebraicSpaces B S hS)

/-! ### The chartwise composite of restrictions -/

/-- The morphism of algebraic spaces represented by a composite of two morphisms of étale scheme
charts is étale.  This is `AlgebraicGeometry.Space.isEtale_chartMap` for the composite, read
through `AlgebraicGeometry.Space.chartMap_comp`. -/
theorem isEtale_chartMap_comp {W V U : SmallEtale B S hS X.1} (f : V ⟶ U) (g : W ⟶ V) :
    IsEtale B S hS (chartMap B S hS X g ≫ chartMap B S hS X f).hom := by
  rw [chartMap_comp]
  exact isEtale_chartMap B S hS X (g ≫ f)

/-- **Strictness of the Stacks 03LP tower at the charts.**  Postcomposition along the represented
morphism of a morphism of charts, then along that of another, is postcomposition along the
represented morphism of the composite — as an equality of functors of small étale sites, because
`AlgebraicGeometry.Space.chartMap_comp` is definitional. -/
theorem smallEtalePostcomp_chartMap_comp {W V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (g : W ⟶ V) :
    smallEtalePostcomp B S hS (chartMap B S hS X g) (isEtale_chartMap B S hS X g) ⋙
        smallEtalePostcomp B S hS (chartMap B S hS X f) (isEtale_chartMap B S hS X f) =
      smallEtalePostcomp B S hS (chartMap B S hS X (g ≫ f))
        (isEtale_chartMap B S hS X (g ≫ f)) :=
  smallEtalePostcomp_comp_eq B S hS _ _ _ _ _

/-- The composite of the two chartwise postcomposition functors is continuous.  It is an
instance, by `CategoryTheory.Functor.isContinuous_comp`, but instance search does not find the
intermediate topology on its own. -/
instance isContinuous_smallEtalePostcomp_chartMap_comp {W V U : SmallEtale B S hS X.1}
    (f : V ⟶ U) (g : W ⟶ V) :
    (smallEtalePostcomp B S hS (chartMap B S hS X g) (isEtale_chartMap B S hS X g) ⋙
        smallEtalePostcomp B S hS (chartMap B S hS X f)
          (isEtale_chartMap B S hS X f)).IsContinuous
      (SmallEtale.topology B S hS (chartSpace B S hS X W).1)
      (SmallEtale.topology B S hS (chartSpace B S hS X U).1) :=
  Functor.isContinuous_comp _ _ _ (SmallEtale.topology B S hS (chartSpace B S hS X V).1) _

/-- Restriction along one chartwise postcomposition after another is restriction along the
composite functor of sites.  This is `CategoryTheory.Functor.sheafPushforwardContinuousComp`,
which is the identity, written out at the chart data. -/
theorem chartPostcompSheaf_comp_eq {W V U : SmallEtale B S hS X.1} (f : V ⟶ U) (g : W ⟶ V) :
    (smallEtalePostcomp B S hS (chartMap B S hS X f)
          (isEtale_chartMap B S hS X f)).sheafPushforwardContinuous (Type (u + 1))
            (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
            (SmallEtale.topology B S hS (chartSpace B S hS X U).1) ⋙
        (smallEtalePostcomp B S hS (chartMap B S hS X g)
          (isEtale_chartMap B S hS X g)).sheafPushforwardContinuous (Type (u + 1))
            (SmallEtale.topology B S hS (chartSpace B S hS X W).1)
            (SmallEtale.topology B S hS (chartSpace B S hS X V).1) =
      (smallEtalePostcomp B S hS (chartMap B S hS X g) (isEtale_chartMap B S hS X g) ⋙
          smallEtalePostcomp B S hS (chartMap B S hS X f)
            (isEtale_chartMap B S hS X f)).sheafPushforwardContinuous (Type (u + 1))
            (SmallEtale.topology B S hS (chartSpace B S hS X W).1)
            (SmallEtale.topology B S hS (chartSpace B S hS X U).1) :=
  rfl

/-- **Restriction to the charts composes strictly.**  Restricting along a morphism of charts and
then along another is restricting along the composite, as an equality of functors on sheaves.

This is `AlgebraicGeometry.Space.chartPostcompSheaf_comp_eq` followed by
`AlgebraicGeometry.Space.smallEtalePostcomp_chartMap_comp`.  Both sides are definitionally equal,
but the two steps are what the unifier can afford: asked for in one step the same `rfl` exhausts
the heartbeat limit. -/
theorem chartPostcompSheaf_comp {W V U : SmallEtale B S hS X.1} (f : V ⟶ U) (g : W ⟶ V) :
    (smallEtalePostcomp B S hS (chartMap B S hS X f)
          (isEtale_chartMap B S hS X f)).sheafPushforwardContinuous (Type (u + 1))
            (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
            (SmallEtale.topology B S hS (chartSpace B S hS X U).1) ⋙
        (smallEtalePostcomp B S hS (chartMap B S hS X g)
          (isEtale_chartMap B S hS X g)).sheafPushforwardContinuous (Type (u + 1))
            (SmallEtale.topology B S hS (chartSpace B S hS X W).1)
            (SmallEtale.topology B S hS (chartSpace B S hS X V).1) =
      (smallEtalePostcomp B S hS (chartMap B S hS X (g ≫ f))
          (isEtale_chartMap B S hS X (g ≫ f))).sheafPushforwardContinuous (Type (u + 1))
            (SmallEtale.topology B S hS (chartSpace B S hS X W).1)
            (SmallEtale.topology B S hS (chartSpace B S hS X U).1) :=
  (chartPostcompSheaf_comp_eq B S hS X f g).trans
    (sheafPushforwardContinuous_eq_of_functor_eq
      (SmallEtale.topology B S hS (chartSpace B S hS X W).1)
      (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
      (smallEtalePostcomp_chartMap_comp B S hS X f g))

/-- Both steps of `AlgebraicGeometry.Space.chartPostcompSheaf_comp` are transports along
definitional equalities, so each of their `CategoryTheory.eqToHom`s is an identity. -/
theorem eqToHom_chartPostcompSheaf_comp_eq {W V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (g : W ⟶ V) : eqToHom (chartPostcompSheaf_comp_eq B S hS X f g) = 𝟙 _ :=
  eqToHom_refl _ _

/-- The second step of `AlgebraicGeometry.Space.chartPostcompSheaf_comp` is a transport along a
definitional equality, so its `CategoryTheory.eqToHom` is an identity. -/
theorem eqToHom_sheafPushforwardContinuous_smallEtalePostcomp_chartMap_comp
    {W V U : SmallEtale B S hS X.1} (f : V ⟶ U) (g : W ⟶ V) :
    eqToHom (sheafPushforwardContinuous_eq_of_functor_eq
        (SmallEtale.topology B S hS (chartSpace B S hS X W).1)
        (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
        (smallEtalePostcomp_chartMap_comp B S hS X f g)) = 𝟙 _ :=
  eqToHom_refl _ _

/-! ### The chartwise comparison carries no transport -/

/-- **The chartwise comparison of inverse images is the composition isomorphism of Stacks 03G2,
part (3), on the nose.**  The `CategoryTheory.eqToIso` that the definition of
`AlgebraicGeometry.Space.chartInverseImageComp` inserts to pass from
`chartMap g ≫ chartMap f` to `chartMap (g ≫ f)` is the identity, because
`AlgebraicGeometry.Space.chartMap_comp` is a definitional equality. -/
theorem chartInverseImageComp_eq {W V U : SmallEtale B S hS X.1} (f : V ⟶ U) (g : W ⟶ V) :
    chartInverseImageComp B S hS X f g =
      (smallToposMorphism_comp_inverseImage B S hS (chartMap B S hS X g)
        (chartMap B S hS X f)).symm :=
  Iso.ext (Category.comp_id _)

/-! ### The dictionary for a morphism of charts, with Stacks 03LQ factored out -/

/-- The restriction-along-equal-functors half of
`AlgebraicGeometry.Space.chartInverseImage_overMapPullbackIso`: restriction along chartwise
postcomposition, read through the comparison equivalence of Stacks 04M0 at the larger chart, is
the slice pullback read through the comparison equivalence at the smaller one.

Both sides are restriction along one of the two composites of functors of sites compared by
`AlgebraicGeometry.Space.chartLocalizationPostcompIso`, so this is a pair of
`CategoryTheory.Functor.sheafPushforwardContinuousComp'` isomorphisms and contains none of the
content of Stacks 03LQ. -/
def chartPostcompSheafIso {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    (chartSliceSheafEquiv B S hS X U).functor ⋙
        (smallEtalePostcomp B S hS (chartMap B S hS X f)
          (isEtale_chartMap B S hS X f)).sheafPushforwardContinuous (Type (u + 1))
            (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
            (SmallEtale.topology B S hS (chartSpace B S hS X U).1) ≅
      (SmallEtale.topology B S hS X.1).overMapPullback (Type (u + 1)) f ⋙
        (chartSliceSheafEquiv B S hS X V).functor :=
  haveI hu := isContinuous_chartLocalization_chartSpace B S hS X U
  haveI hv := isContinuous_chartLocalization_chartSpace B S hS X V
  haveI hfg : (SmallEtale.chartLocalization B S hS X.1 V ⋙ Over.map f).IsContinuous
      (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
      ((SmallEtale.topology B S hS X.1).over U) :=
    Functor.isContinuous_comp _ _ _ ((SmallEtale.topology B S hS X.1).over V) _
  (@Functor.sheafPushforwardContinuousComp' _ _ _ _ _ _ _ _ _
      (chartLocalizationPostcompIso B S hS X f) (Type (u + 1)) _
      (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
      (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
      ((SmallEtale.topology B S hS X.1).over U) _ hu hfg) ≪≫
    (@Functor.sheafPushforwardContinuousComp' _ _ _ _ _ _ _ _ _
      (Iso.refl (SmallEtale.chartLocalization B S hS X.1 V ⋙ Over.map f)) (Type (u + 1)) _
      (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
      ((SmallEtale.topology B S hS X.1).over V)
      ((SmallEtale.topology B S hS X.1).over U) hv _ hfg).symm

/-- **The dictionary for a morphism of charts, factored.**  The identification of the chartwise
inverse image with the slice pullback is the comparison of Stacks 03LQ, whiskered into the
comparison equivalence of Stacks 04M0, followed by
`AlgebraicGeometry.Space.chartPostcompSheafIso`.

This is how `AlgebraicGeometry.Space.chartInverseImage_overMapPullbackIso` is built, and the
factorisation separates the one part of it that carries content — the comparison of Stacks 03LQ,
to which the bridge of
`AlgebraicGeometry.Space.smallToposMorphism_inverseImageIso_comp` applies — from the part that
is restriction along equal functors of sites. -/
theorem chartInverseImage_overMapPullbackIso_eq {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    chartInverseImage_overMapPullbackIso B S hS X f =
      Functor.isoWhiskerLeft (chartSliceSheafEquiv B S hS X U).functor
          (smallToposMorphism_inverseImageIso B S hS (chartMap B S hS X f)
            (isEtale_chartMap B S hS X f)) ≪≫
        chartPostcompSheafIso B S hS X f :=
  rfl

/-! ### The chart-level bridge -/

/-- **The bridge of Stacks 03LQ against Stacks 03G2, part (3), at the étale scheme charts.**

For two composable morphisms of charts, the two comparisons of Stacks 03LQ identifying the
chartwise inverse images with restriction along chartwise postcomposition, composed
horizontally, equal the chartwise composition comparison
`AlgebraicGeometry.Space.chartInverseImageComp` followed by the comparison of Stacks 03LQ for the
composite morphism of charts.  Nothing is inserted on the restriction side, because
postcomposition composes strictly
(`AlgebraicGeometry.Space.smallEtalePostcomp_chartMap_comp`).

This is `AlgebraicGeometry.Space.smallToposMorphism_inverseImageIso_comp` at the represented
morphisms of the charts, together with
`AlgebraicGeometry.Space.chartInverseImageComp_eq`: the represented morphism of a composite of
chart morphisms is definitionally the composite of the represented morphisms, so the transport
that the general bridge would have to carry across
`AlgebraicGeometry.Space.chartMap_comp` is the identity.

It is the content of the compatibility of the chart-to-slice dictionary with the composition
isomorphisms for a morphism of charts; what that compatibility needs beyond it is the coherence
of the `CategoryTheory.Functor.sheafPushforwardContinuousComp'` isomorphisms of
`AlgebraicGeometry.Space.chartPostcompSheafIso`. -/
theorem chartInverseImageComp_inverseImageIso {W V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (g : W ⟶ V) :
    Functor.whiskerRight (smallToposMorphism_inverseImageIso B S hS (chartMap B S hS X f)
          (isEtale_chartMap B S hS X f)).hom (chartInverseImage B S hS X g) ≫
        Functor.whiskerLeft
          ((smallEtalePostcomp B S hS (chartMap B S hS X f)
            (isEtale_chartMap B S hS X f)).sheafPushforwardContinuous (Type (u + 1))
              (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
              (SmallEtale.topology B S hS (chartSpace B S hS X U).1))
          (smallToposMorphism_inverseImageIso B S hS (chartMap B S hS X g)
            (isEtale_chartMap B S hS X g)).hom =
      (chartInverseImageComp B S hS X f g).hom ≫
        (smallToposMorphism_inverseImageIso B S hS (chartMap B S hS X (g ≫ f))
          (isEtale_chartMap B S hS X (g ≫ f))).hom ≫
          eqToHom (smallEtalePostcomp_sheafPushforwardContinuous_congr B S hS
            (isEtale_chartMap B S hS X (g ≫ f))
            (isEtale_chartMap_comp B S hS X f g)
            (chartMap_comp B S hS X f g).symm) := by
  have hI : (smallToposMorphism B S hS
        (chartMap B S hS X g ≫ chartMap B S hS X f)).inverseImage =
      (smallToposMorphism B S hS (chartMap B S hS X (g ≫ f))).inverseImage :=
    congrArg (fun k => (smallToposMorphism B S hS k).inverseImage) (chartMap_comp B S hS X f g)
  have hc := smallToposMorphism_inverseImageIso_congr B S hS
    (isEtale_chartMap B S hS X (g ≫ f)) (isEtale_chartMap_comp B S hS X f g)
    (chartMap_comp B S hS X f g).symm hI
  have hcIC : (chartInverseImageComp B S hS X f g).hom =
      (smallToposMorphism_comp_inverseImage B S hS (chartMap B S hS X g)
        (chartMap B S hS X f)).inv ≫ eqToHom hI := rfl
  have h2 : eqToHom hI ≫ (smallToposMorphism_inverseImageIso B S hS
        (chartMap B S hS X (g ≫ f)) (isEtale_chartMap B S hS X (g ≫ f))).hom ≫
        eqToHom (smallEtalePostcomp_sheafPushforwardContinuous_congr B S hS
          (isEtale_chartMap B S hS X (g ≫ f)) (isEtale_chartMap_comp B S hS X f g)
          (chartMap_comp B S hS X f g).symm) =
      (smallToposMorphism_inverseImageIso B S hS
        (chartMap B S hS X g ≫ chartMap B S hS X f)
        (isEtale_chartMap_comp B S hS X f g)).hom := by
    rw [← Category.assoc, hc]
    simp
  refine ((Iso.eq_inv_comp _).mpr (smallToposMorphism_inverseImageIso_comp B S hS
    (chartMap B S hS X g) (chartMap B S hS X f) (isEtale_chartMap B S hS X g)
    (isEtale_chartMap B S hS X f) (isEtale_chartMap_comp B S hS X f g))).trans ?_
  refine (congrArg (fun t => (smallToposMorphism_comp_inverseImage B S hS
      (chartMap B S hS X g) (chartMap B S hS X f)).inv ≫ t) h2.symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact congrArg (fun t => t ≫ _) hcIC.symm

end AlgebraicGeometry.Space

end
