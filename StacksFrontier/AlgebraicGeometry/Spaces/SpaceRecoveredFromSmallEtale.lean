module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartGluedHomInduces
public import StacksFrontier.AlgebraicGeometry.Spaces.CofinalChartFactorsThroughAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.CofinalChartTwoIsoGluing
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposIsoLocallyRinged
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RecoveryOverBase

/-!
# Stacks 04KL: a morphism of small étale ringed topoi comes from a morphism of algebraic spaces

Let `X` and `Y` be algebraic spaces over a scheme `S` contained in a big fppf site `B`, and let
`ψ` be a locally ringed morphism of their small étale ringed topoi which is 2-compatible with
the structure morphisms to `AlgebraicGeometry.Space.baseSpace`.  This file assembles the two
gluing steps of the proof of [Stacks Project, Tag 04KL] into the conclusion that `ψ` is induced
by exactly one morphism of algebraic spaces `X ⟶ Y`, and deduces
`AlgebraicGeometry.Space.IsRecoveredFromSmallEtaleOver` at the base.  The full assertion
`AlgebraicGeometry.Space.IsRecoveredFromSmallEtale` is the base's
`AlgebraicGeometry.Space.isRecoveredFromSmallEtale_holds`, which the results below consume.

The two steps are already available:

* step 5, `AlgebraicGeometry.Space.exists_hom_induces_chartwise_affineCharts`, produces a
  morphism `l` of the underlying sheaves inducing `ψ` over every selected chart of `X` which
  factors through a chosen surjective étale scheme chart `b : h_A ⟶ X`;
* step 6, `AlgebraicGeometry.Space.inducesSmallEtaleRingedToposHom_of_cofinal`, descends
  chartwise 2-isomorphisms over a *cofinal* class of charts to a global one.

What joins them is `AlgebraicGeometry.Space.IsCofinalChartFamily.and`: the selected charts and
the charts factoring through `b` are each cofinal, and factoring through `b` is stable under
refinement, so their conjunction — which is exactly the class step 5 says something about — is
cofinal, and step 6 accepts it in place of "every chart".

Uniqueness is `AlgebraicGeometry.Space.eq_of_inducesCommonSmallEtaleRingedToposHom`, which is
[Stacks Project, Tag 04M6] and needs nothing assumed.  The quantification over the third
algebraic space in `AlgebraicGeometry.Space.IsRecoveredFromSmallEtale` collapses because
`AlgebraicGeometry.Space.baseSpace` is terminal, so the 2-compatibility hypothesis there is the
one proved here:
`AlgebraicGeometry.Space.isRecoveredFromSmallEtale_of_baseSpace` removes the rest.

## Main results

* `AlgebraicGeometry.Space.exists_inducesSmallEtaleRingedToposHom` — steps 5 and 6 together.
* `AlgebraicGeometry.Space.existsUnique_inducesSmallEtaleRingedToposHom` — with uniqueness.
* `AlgebraicGeometry.Space.isRecoveredFromSmallEtaleOver_baseSpace` — [Stacks Project, Tag 04KL]
  over the single base `AlgebraicGeometry.Space.baseSpace`; over an arbitrary third space it is
  the base's `AlgebraicGeometry.Space.isRecoveredFromSmallEtale_holds`.  Tag 04KL itself is the
  absolute statement, for algebraic spaces over `Spec ℤ` and with no 2-compatibility
  hypothesis, so it is *not* registered here.
* `AlgebraicGeometry.Space.existsUnique_spaceHom_twoIso_of_smallEtaleRingedToposIso'` — the
  clause of [Stacks Project, Tag 05YZ] about `f`, with the recovery supplied.

## References

* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
* [Stacks Project, Tag 04M6](https://stacks.math.columbia.edu/tag/04M6)
* [Stacks Project, Tag 05YZ](https://stacks.math.columbia.edu/tag/05YZ)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X Y : AlgebraicSpaces B S hS)

/-- **The chart of a composite chart, followed by a morphism of algebraic spaces.**  Both sides
are the morphism of algebraic spaces on the composite of the underlying presheaf maps. -/
theorem etaleChartToSpace_comp_homMk {A : BigFppfOver B S hS} (c : yoneda.obj A ⟶ X.1)
    (l : X.1 ⟶ Y.1) :
    etaleChartToSpace B S hS c ≫ (ObjectProperty.homMk l : X ⟶ Y) =
      (ObjectProperty.homMk (c ≫ l) : yonedaSpace B S hS A ⟶ Y) :=
  rfl

variable (ψ : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))

/-- **Steps 5 and 6 of the proof of [Stacks Project, Tag 04KL].**  A locally ringed morphism `ψ`
of the small étale ringed topoi of `X` and `Y` which is 2-compatible with the structure
morphisms to `AlgebraicGeometry.Space.baseSpace` is induced by a morphism of algebraic spaces
`X ⟶ Y`.

The morphism is the one step 5 glues from the chartwise morphisms
(`AlgebraicGeometry.Space.exists_hom_induces_chartwise_affineCharts`) along the surjective étale
scheme chart of `X` supplied by `AlgebraicGeometry.IsAlgebraicSpace.exists_atlas`.  That it
induces `ψ` globally is step 6
(`AlgebraicGeometry.Space.inducesSmallEtaleRingedToposHom_of_cofinal`) at the class of selected
charts factoring through that chart, which is cofinal by
`AlgebraicGeometry.Space.IsCofinalChartFamily.and`. -/
theorem exists_inducesSmallEtaleRingedToposHom (hψ : ψ.IsLocallyRinged)
    (hbase : RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
        (smallEtaleRingedToposHom B S hS (toBaseSpace B S hS Y)) ψ)
      (smallEtaleRingedToposHom B S hS (toBaseSpace B S hS X))) :
    ∃ k : X ⟶ Y, InducesSmallEtaleRingedToposHom B S hS k ψ := by
  obtain ⟨A, b, hsurj, haet⟩ := X.2.exists_atlas
  have hb : IsEtale B S hS b := (isEtale_iff_presheaf_of_yoneda B S hS b).2 haet
  obtain ⟨l, hl⟩ :=
    exists_hom_induces_chartwise_affineCharts B S hS X Y ψ hψ hbase A b hb hsurj
  refine ⟨ObjectProperty.homMk l, inducesSmallEtaleRingedToposHom_of_cofinal B S hS ψ
    (ObjectProperty.homMk l)
    (fun T c => HasSomeChartSection B S hS X.1
        (fun W : {W : SmallEtale B S hS Y.1 //
            IsAffine ((BigFppfOver.toScheme B S hS).obj
              ((SmallEtale.toOver B S hS Y.1).obj W))} =>
          ψ.toToposHom.inverseImage.obj (smallEtaleChartSheaf B S hS Y W.1)) T c ∧
      ∃ r : T ⟶ A, yoneda.map r ≫ b = c)
    (IsCofinalChartFamily.and B S hS
      (isCofinalChartFamily_inverseImage_smallEtaleChartSheaf_ringedToposHom B S hS ψ _
        (SmallEtale.coversTop_affineCharts B S hS Y.1))
      (isCofinalChartFamily_factorsThrough B S hS X A b hb hsurj)
      fun T R r c h => factorsThrough_comp B S hS X b r c h)
    ?_⟩
  intro T hT c hc hP
  obtain ⟨hPsel, r, hrc⟩ := hP
  subst hrc
  rw [etaleChartToSpace_comp_homMk, Category.assoc]
  exact hl T hT r hc hPsel

/-- **[Stacks Project, Tag 04KL] over the base.**  A locally ringed morphism of the small étale
ringed topoi of two algebraic spaces over `S` which is 2-compatible with the structure morphisms
to `AlgebraicGeometry.Space.baseSpace` is induced by *exactly one* morphism of algebraic spaces.

Existence is `AlgebraicGeometry.Space.exists_inducesSmallEtaleRingedToposHom` and uniqueness is
`AlgebraicGeometry.Space.eq_of_inducesCommonSmallEtaleRingedToposHom`, which is
[Stacks Project, Tag 04M6]. -/
theorem existsUnique_inducesSmallEtaleRingedToposHom (hψ : ψ.IsLocallyRinged)
    (hbase : RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
        (smallEtaleRingedToposHom B S hS (toBaseSpace B S hS Y)) ψ)
      (smallEtaleRingedToposHom B S hS (toBaseSpace B S hS X))) :
    ∃! k : X ⟶ Y, InducesSmallEtaleRingedToposHom B S hS k ψ := by
  obtain ⟨k, hk⟩ := exists_inducesSmallEtaleRingedToposHom B S hS X Y ψ hψ hbase
  exact ⟨k, hk, fun k' hk' => eq_of_inducesCommonSmallEtaleRingedToposHom B S hS k' k hk' hk⟩

/-- **A morphism of algebraic spaces to the base is the canonical one.**  The base, read as an
algebraic space over itself, is terminal among algebraic spaces over `S`. -/
theorem eq_toBaseSpace (p : X ⟶ baseSpace B S hS) : p = toBaseSpace B S hS X :=
  ObjectProperty.hom_ext _ ((isTerminal_yoneda_obj_base B S hS).hom_ext _ _)

/-- **[Stacks Project, Tag 04KL] over the single base
`AlgebraicGeometry.Space.baseSpace`.**  This is
`AlgebraicGeometry.Space.existsUnique_inducesSmallEtaleRingedToposHom`: the two structure
morphisms to the base are the canonical ones, because the base is terminal, so the
2-compatibility assumed there is the one assumed here. -/
theorem isRecoveredFromSmallEtaleOver_baseSpace :
    IsRecoveredFromSmallEtaleOver B S hS (baseSpace B S hS) := by
  intro P Q pP pQ χ hχ hcompat
  obtain ⟨t⟩ := hcompat
  rw [eq_toBaseSpace B S hS P pP] at t
  rw [eq_toBaseSpace B S hS Q pQ] at t
  exact existsUnique_inducesSmallEtaleRingedToposHom B S hS P Q χ hχ t

/-! ### Stacks 05YZ with the recovery supplied -/

/-- **[Stacks Project, Tag 05YZ], the clause about `f`.**  If `g` is a morphism of the small
étale ringed topoi of `X` and `Y` whose direct image is an equivalence and whose structure map
is an isomorphism, and `g` is 2-compatible with a pair of structure morphisms `pX : X ⟶ A`,
`pY : Y ⟶ A`, then there is exactly one morphism of algebraic spaces `f : X ⟶ Y` with `g`
2-isomorphic to the morphism of small étale ringed topoi of `f`.

This is `AlgebraicGeometry.Space.IsRecoveredFromSmallEtaleOver` at `A`, supplied by
`AlgebraicGeometry.Space.isRecoveredFromSmallEtale_holds`, applied to `g`: the hypothesis that
`g` is locally ringed is `AlgebraicGeometry.Space.isLocallyRinged_of_smallEtaleRingedToposIso`,
and the two 2-isomorphisms are read in the opposite direction from
`AlgebraicGeometry.Space.InducesSmallEtaleRingedToposHom`.

Only the source's clause about `f` is registered here; its further clause that `f` is an
isomorphism of algebraic spaces lies outside this statement.

The 2-compatibility `hbase` is not optional: the source states Stacks 05YZ for algebraic spaces
over `Spec(ℤ)`, where `f` is an absolute morphism, whereas `f : X ⟶ Y` here is a morphism over
`S`.  Without it the conclusion is false — see the σ-twist counterexample recorded with
`AlgebraicGeometry.Space.IsRecoveredFromSmallEtale`.  Since
`AlgebraicGeometry.Space.baseSpace` is terminal, `hbase` can always be asked of the structure
morphisms to the base itself. -/
@[stacks 05YZ "the clause about f ALONE: its existence and uniqueness, together with the \
2-isomorphism of (g, g sharp) with (f_small, f sharp) (Stacks 04IC).  Stacks 04KL over a \
base, which the existence needs, is isRecoveredFromSmallEtale_holds.  The source's \
further clause that f is an ISOMORPHISM of algebraic spaces lies outside this registration.  \
NARROWER than the source in one further respect: the source states 05YZ for spaces over \
Spec(Z), where f is an absolute morphism and no compatibility is asked of (g, g sharp), while \
f here is a morphism over S, so the 2-compatibility hbase is assumed in addition -- it is what \
Stacks 04SG supplies, and without it the conclusion is FALSE"]
theorem existsUnique_spaceHom_twoIso_of_smallEtaleRingedToposIso' {A : AlgebraicSpaces B S hS}
    (pX : X ⟶ A) (pY : Y ⟶ A)
    (g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
    [g.toToposHom.pushforward.IsEquivalence] [IsIso g.fSharp]
    (hbase : Nonempty (SmallEtaleTwoIso B S hS
      (smallEtaleComp B S hS (smallEtaleRingedToposHom B S hS pY) g)
      (smallEtaleRingedToposHom B S hS pX))) :
    ∃! f : X ⟶ Y, Nonempty (RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} g
      (smallEtaleRingedToposHom B S hS f)) := by
  obtain ⟨f, hf, huniq⟩ :=
    isRecoveredFromSmallEtaleOver_of_isRecoveredFromSmallEtale B S hS
      (isRecoveredFromSmallEtale_holds B S hS) A pX pY g
      (isLocallyRinged_of_smallEtaleRingedToposIso B S hS g) hbase
  obtain ⟨t⟩ := hf
  refine ⟨f, ⟨t.symm⟩, fun y hy => huniq y ?_⟩
  obtain ⟨s⟩ := hy
  exact ⟨s.symm⟩

end AlgebraicGeometry.Space

end
