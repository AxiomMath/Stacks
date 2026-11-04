module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardRelation

/-!
# The affine base case of the second step of the proof of Stacks 03M9: the geometry, completed

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of algebraic spaces over a
scheme `S` contained in a big fppf site `B`.  The second step of the proof of Stacks 03M9
begins, after `StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentPushforwardReduction.lean` has
reduced the lemma to an affine étale scheme chart `V` of `Y`, by choosing a surjective étale
`p : W ⟶ U` with `W` affine, where `U = V ×_Y X`, forming the relation `R = W ×_U W`, and
asserting that

`a = p ≫ f' : W ⟶ V`  and  `b = R ⟶ W ⟶ V`

are quasi-compact and quasi-separated morphisms — *"as `U` and `Y` are affine at this point"*.

`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentPushforwardRelation.lean` proves the clauses
about `R` and `b`, but it *carries* quasi-compactness and quasi-separatedness of `a` as
hypotheses, recording in its implementation notes that in the situation the second step has
arranged they are automatic because `W` and `V` are affine.  This file proves that, and
assembles the whole sentence: the geometric half of the second step of the proof of Stacks 03M9
holds unconditionally.

## Main definitions

There are no new definitions, and no new instance is registered.

## Main results

* `AlgebraicGeometry.Space.isQuasiCompact_yoneda_of_isAffine` and
  `AlgebraicGeometry.Space.isQuasiSeparated_yoneda_of_isAffine`: a morphism between presheaves
  represented by objects of the big fppf site with affine underlying schemes is quasi-compact in
  the sense of Stacks 03HE, and quasi-separated in the sense of Stacks 03HL, part (3).  The
  quasi-separated clause needs only the source to be affine.
* `AlgebraicGeometry.Space.exists_affine_chart_relation_quasiCompact_quasiSeparated` is the
  geometric half of the second step of the proof of Stacks 03M9, unconditionally: for an affine
  étale scheme chart `V` of `Y` there is an affine `W` with a surjective étale morphism onto
  `V ×_Y X` for which both `a : W ⟶ V` and `b : W ×_{V ×_Y X} W ⟶ V` are quasi-compact and
  quasi-separated.

## Implementation notes

**No `@[stacks]` attribute is carried and no part of Stacks 03M9 is proved here.**  What is
proved is a clause of the *proof* of that lemma, and the lemma itself is not reached: its
module-theoretic half — the exact sequence of Stacks 03M8, quasi-coherence of the direct image
along a quasi-compact quasi-separated morphism of schemes read on the small étale site
(Descent, Proposition 03LC, part (3)) and stability of quasi-coherence under kernels
(Stacks 03M1) — is not treated.  The two results about a morphism of represented presheaves are
likewise not the assertion of any tag: Stacks 03HE and 03HL are the definitions, and the
scheme-level facts they are fed are Mathlib's.

**How the two base cases are proved.**  Both reduce to the scheme level through the represented
reading of a morphism property.  Quasi-compactness of a morphism of presheaves follows from the
represented reading by Stacks 03HD, condition (1) implies condition (2)
(`AlgebraicGeometry.Space.isQuasiCompact_of_presheaf_quasiCompact`), and for a morphism of the
site the represented reading is the scheme-level property
(`AlgebraicGeometry.BigFppfOver.presheaf_inverseImage_yoneda_map_iff`), where a morphism of
affine schemes is affine and therefore quasi-compact by Mathlib's
`AlgebraicGeometry.isAffineHom_of_isAffine`.  Quasi-separatedness is quasi-compactness of the
relative diagonal, and for a morphism of the site out of an affine object the represented
reading of that is already available as
`AlgebraicGeometry.Space.diagonalProp_quasiCompact_yoneda_map_of_isAffine`; passing from the
represented reading to Stacks 03HL, part (3) is
`AlgebraicGeometry.Space.isQuasiSeparated_of_diagonalProp_quasiCompact`.

An arbitrary morphism of represented presheaves is `CategoryTheory.yoneda` of a morphism of the
site, by fullness of Yoneda, so the two results are stated for an arbitrary such morphism rather
than for one of the form `CategoryTheory.yoneda.map q`; that is the form the assembly below
needs, because the morphism it applies them to is a composite.

**Why the hypotheses are not vacuous.**  Affineness of the source is produced, not assumed, by
`AlgebraicGeometry.Space.exists_affine_etale_surjective_chart_chartBaseChange`, which is
Stacks 03H6 for the base change along an affine chart; affineness of the target is the
hypothesis that
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_iff_forall_affine` quantifies
over.  Neither of the two base cases holds without its affineness hypotheses — the
quasi-compactness clause fails to elaborate with either dropped, and the quasi-separatedness
clause with its one hypothesis dropped — so no implication below is vacuous.

The target of the base-change projection of
`AlgebraicGeometry.Space.chartBaseChangeProjection` is the presheaf represented by the object
of the site underlying the chart `V`, on the nose: that is why the composite `a` is a morphism
of represented presheaves with no transport.  The source `V ×_Y X` is in general only an
algebraic space, which is why `a` and not the projection itself is the morphism the two base
cases are applied to.

## References

* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 03HD](https://stacks.math.columbia.edu/tag/03HD)
* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 03HL](https://stacks.math.columbia.edu/tag/03HL)
* [Stacks Project, Tag 03KN](https://stacks.math.columbia.edu/tag/03KN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Morphisms of represented presheaves with affine underlying schemes -/

/-- **A morphism between presheaves represented by affine objects of the site is quasi-compact**,
in the sense of Stacks 03HE.

A morphism of affine schemes is affine, hence quasi-compact, so the represented reading of
quasi-compactness holds for it by
`AlgebraicGeometry.BigFppfOver.presheaf_inverseImage_yoneda_map_iff`; Stacks 03HD, condition (1)
implies condition (2) turns that into quasi-compactness in the sense of Stacks 03HE. -/
theorem isQuasiCompact_yoneda_of_isAffine {W V : BigFppfOver B S hS}
    (a : yoneda.obj W ⟶ yoneda.obj V)
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) :
    IsQuasiCompact B S hS a := by
  obtain ⟨q, rfl⟩ := (yoneda (C := BigFppfOver B S hS)).map_surjective a
  exact isQuasiCompact_of_presheaf_quasiCompact B S hS
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u}) q).2
      (have := hW; have := hV; inferInstance))

/-- **A morphism out of a presheaf represented by an affine object of the site is
quasi-separated**, in the sense of Stacks 03HL, part (3).

An affine scheme is a quasi-separated topological space, so every morphism of the site out of an
affine object has quasi-compact relative diagonal in the represented reading
(`AlgebraicGeometry.Space.diagonalProp_quasiCompact_yoneda_map_of_isAffine`), and the represented
reading implies Stacks 03HL, part (3).  No hypothesis on the target is needed. -/
theorem isQuasiSeparated_yoneda_of_isAffine {W V : BigFppfOver B S hS}
    (a : yoneda.obj W ⟶ yoneda.obj V)
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W)) :
    IsQuasiSeparated B S hS a := by
  obtain ⟨q, rfl⟩ := (yoneda (C := BigFppfOver B S hS)).map_surjective a
  exact isQuasiSeparated_of_diagonalProp_quasiCompact B S hS
    (diagonalProp_quasiCompact_yoneda_map_of_isAffine B S hS q hW)

/-! ### The geometric half of the second step of the proof of Stacks 03M9 -/

variable {X Y : AlgebraicSpaces B S hS}

/-- **The geometric half of the second step of the proof of Stacks 03M9, unconditionally.**  Let
`f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of algebraic spaces over `S` and let
`V` be an étale scheme chart of `Y` with affine underlying scheme.  Then the algebraic space
`U = V ×_Y X` admits a surjective étale morphism `p` from a presheaf represented by an affine
object `W` of the site such that, writing `a = p ≫ f'` for the composite to `V` and
`b = R ⟶ W ⟶ V` for the corresponding morphism out of the relation `R = W ×_U W`, both `a` and
`b` are quasi-compact and quasi-separated.

This is the source's sentence *"since `f` is quasi-compact we see that `X` is quasi-compact, thus
we may choose an affine scheme `U` and a surjective étale morphism `U ⟶ X`; as `X ⟶ Y` is
quasi-separated the morphism `R ⟶ U ×_Y U` is a quasi-compact monomorphism, hence `R` is a
quasi-compact separated scheme, and `a : U ⟶ Y` and `b : R ⟶ Y` are quasi-compact and
quasi-separated"*, with the roles of the source's `U` and `Y` played by `W` and `V`.

The chart `p` and the affineness of `W` are Stacks 03H6 for the base change along an affine
chart, `AlgebraicGeometry.Space.exists_affine_etale_surjective_chart_chartBaseChange`.  The two
clauses about `a` are the two base cases above, which apply because the target of the base-change
projection is the presheaf represented by the object of the site underlying `V`.  The two
clauses about `b` are `AlgebraicGeometry.Space.isQuasiCompact_selfPullback_comp` and
`AlgebraicGeometry.Space.isQuasiSeparated_selfPullback_comp`, whose hypotheses on `a` are exactly
what the two base cases supply; quasi-separatedness of the base-changed morphism, which the
first of those consumes, is Stacks 03KL, part (3) for an étale chart,
`AlgebraicGeometry.Space.isQuasiSeparated_chartBaseChangeProjection`.

Surjectivity and étaleness of `p` are not restated in the conclusion: nothing below uses them,
and the consumer that does — the exact sequence of Stacks 03M8 — takes them from the same
existence statement. -/
theorem exists_affine_chart_relation_quasiCompact_quasiSeparated (f : X ⟶ Y)
    (V : SmallEtale B S hS Y.1)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V)))
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom) :
    ∃ (W : BigFppfOver B S hS)
      (p : yoneda.obj W ⟶
        ((SpacesEtale.toSpaces B S hS X).obj (chartBaseChange B S hS f V)).1),
      IsAffine ((BigFppfOver.toScheme B S hS).obj W) ∧
      IsQuasiCompact B S hS (p ≫ (chartBaseChangeProjection B S hS f V).hom) ∧
      IsQuasiSeparated B S hS (p ≫ (chartBaseChangeProjection B S hS f V).hom) ∧
      IsQuasiCompact B S hS
        (pullback.fst p p ≫ p ≫ (chartBaseChangeProjection B S hS f V).hom) ∧
      IsQuasiSeparated B S hS
        (pullback.fst p p ≫ p ≫ (chartBaseChangeProjection B S hS f V).hom) := by
  obtain ⟨W, p, hWaff, _, _⟩ :=
    exists_affine_etale_surjective_chart_chartBaseChange B S hS f V hV hfqc
  have haqc : IsQuasiCompact B S hS (p ≫ (chartBaseChangeProjection B S hS f V).hom) :=
    isQuasiCompact_yoneda_of_isAffine B S hS _ hWaff hV
  have haqs : IsQuasiSeparated B S hS (p ≫ (chartBaseChangeProjection B S hS f V).hom) :=
    isQuasiSeparated_yoneda_of_isAffine B S hS _ hWaff
  refine ⟨W, p, hWaff, haqc, haqs, ?_, ?_⟩
  · exact isQuasiCompact_selfPullback_comp B S hS p
      (chartBaseChangeProjection B S hS f V).hom
      (isAlgebraicSpace_yoneda B S hS W) (isAlgebraicSpace_yoneda B S hS _)
      (isQuasiSeparated_chartBaseChangeProjection B S hS f V hfqs) haqc
  · exact isQuasiSeparated_selfPullback_comp B S hS p
      (chartBaseChangeProjection B S hS f V).hom
      (isAlgebraicSpace_yoneda B S hS W)
      ((SpacesEtale.toSpaces B S hS X).obj (chartBaseChange B S hS f V)).2
      (isAlgebraicSpace_yoneda B S hS _) haqs

end AlgebraicGeometry.Space

end
