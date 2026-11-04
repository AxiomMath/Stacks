module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInUniversalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiMainTheoremGeneral
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.CartesianSquareDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedQuasiFiniteEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties

/-!
# Extending an integral morphism across a quasi-compact open immersion

Let `j : V ⟶ Y` be a quasi-compact open immersion of algebraic spaces over a scheme `S` and let
`π : Z ⟶ V` be integral. Then `π` extends to an integral morphism over the whole of `Y`: there
is an integral `ν : Y' ⟶ Y` whose inverse image over `V` is `Z`, i.e. for which the square

```
Z  --f'-->  Y'
|            |
π            ν
v            v
V  ---j--->  Y
```

is cartesian. This is Stacks 0G2D, and it is the named input to the inductive step of Tag 09YB.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.exists_isIntegralHom_isPullback_of_isOpenImmersion` is the statement
  above.

## Implementation notes

**The construction is the source's.** `Y'` is the normalization of `Y` in `Z`, taken along the
composite `f = π ≫ j`, which is representable, quasi-compact and separated because `j` and `π`
are. It enters as `AlgebraicGeometry.Space.NormalizationInData`, the chart description of
Tag 0ABP, produced by `nonempty_normalizationInData_of_isQuasiCompact_isQuasiSeparated` in the
namespace `AlgebraicGeometry.Space.NormalizationGluing`, which glues the chart normalizations
along a surjective étale chart of `Y`. Integrality of `ν` is
`NormalizationInData.isIntegralHom_fromNorm_of_isQuasiCompact_isQuasiSeparated` in the namespace
`AlgebraicGeometry.Space`.

**Why the cartesian square is a descent and not a citation.** The source finishes with "the
final statement follows formally from Lemmas 0ABP and 0825": the inverse image of `V` in `Y'` is
the normalization of `V` in `V ×_Y Z = Z` because the normalization commutes with étale base
change, and that normalization is `Z` itself because `π` is integral. Both of those are
statements about the *normalization of an algebraic space*, and in this library the available
formulations of them — `AlgebraicGeometry.Space.normalizationInIsoOfIsIntegralHom` for Tag 0825
and the base-change lemmas of
`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationSmoothBaseChange` — are gated on the
anti-equivalence of Tag 081V, which has no inhabitant here, or on an undischarged universal
property. What the datum does record is the chart description of Tag 0ABP, so the two citations
are replaced by their chart content and then descended:

* over a *surjective étale scheme chart* `u : U ⟶ V` of `V`, which composed with `j` is an étale
  chart `w = u ≫ j` of `Y`, the chart base change of `f` is the chart base change of `π` —
  because `j` is a monomorphism — and is therefore an **integral morphism of schemes**. So
  Mathlib's Tag 03GP, `IsIso (Scheme.Hom.toNormalization)` for an integral morphism, says that
  the morphism `r : U ×_V Z ⟶ W'` of the chart description is an isomorphism. That is Tag 0825
  on the chart, and it makes the outer rectangle `U ×_V Z, U, Y', Y` cartesian, the inner square
  `W', U, Y', Y` of the chart description being Tag 0ABP.
* the square `U ×_V Z, U, Z, V` is cartesian by construction, and `u` is surjective and étale,
  so Tag 07VZ — `AlgebraicGeometry.Space.isPullback_right_of_isPullback_of_surjective_etale` —
  cancels the two and delivers the square `Z, V, Y', Y`.

No étale descent of isomorphisms is performed by hand; Tag 07VZ is exactly the cancellation of a
cartesian square against a surjective étale base change.

**Quasi-compactness of `j` is used and is the source's.** It is what makes `f = π ≫ j`
quasi-compact, and the relative normalization of a morphism of schemes — hence the chart
description — exists only for a quasi-compact quasi-separated morphism. The source records it in
the hypothesis "quasi-compact open immersion".

## References

* [Stacks Project, Tag 0G2D](https://stacks.math.columbia.edu/tag/0G2D)
* [Stacks Project, Tag 0ABP](https://stacks.math.columbia.edu/tag/0ABP)
* [Stacks Project, Tag 0825](https://stacks.math.columbia.edu/tag/0825)
* [Stacks Project, Tag 03GP](https://stacks.math.columbia.edu/tag/03GP)
* [Stacks Project, Tag 07VZ](https://stacks.math.columbia.edu/tag/07VZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {V Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 0G2D.** Let `j : V ⟶ Y` be a quasi-compact open immersion of algebraic spaces over
a scheme `S` and let `π : Z ⟶ V` be an integral morphism. Then there is an integral morphism
`ν : Y' ⟶ Y` of algebraic spaces over `S` such that `Z` is `V`-isomorphic to the inverse image
of `V` in `Y'`: the square formed by `π`, `j`, `ν` and the canonical morphism `Z ⟶ Y'` is
cartesian.

`Y'` is the normalization of `Y` in `Z`, and the cartesian square is obtained from the
chart description of that normalization by the cancellation of Tag 07VZ along a surjective étale
chart of `V`; see the implementation notes. -/
@[stacks 0G2D]
theorem exists_isIntegralHom_isPullback_of_isOpenImmersion
    (hZ : IsAlgebraicSpace B S hS Z) (hV : IsAlgebraicSpace B S hS V)
    (hY : IsAlgebraicSpace B S hS Y) (j : V ⟶ Y) (hj : IsOpenImmersion B S hS j)
    (hjqc : IsQuasiCompact B S hS j) (π : Z ⟶ V) (hπ : IsIntegralHom B S hS π) :
    ∃ (Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (ν : Y' ⟶ Y) (f' : Z ⟶ Y'),
      IsAlgebraicSpace B S hS Y' ∧ IsIntegralHom B S hS ν ∧ IsPullback f' π ν j := by
  obtain ⟨hrepπ, hpresπ⟩ := (isIntegralHom_iff_representable B S hS π hZ hV).1 hπ
  have hrep : yoneda.relativelyRepresentable (π ≫ j) :=
    MorphismProperty.comp_mem _ π j hrepπ hj.1
  -- `j` is a monomorphism, so `Z` is already the fibre product of `π ≫ j` and `j`.
  have hmj : Mono j := mono_of_isOpenImmersion B S hS j hj
  have hsqj : IsPullback (𝟙 Z) π (π ≫ j) j :=
    IsPullback.of_horiz_isIso_mono (CommSq.mk (by rw [Category.id_comp]))
  -- `f = π ≫ j` is quasi-compact and separated, hence quasi-separated.
  have hπqc : IsQuasiCompact B S hS π :=
    isQuasiCompact_of_isAffineHom' B S hS π hZ hV (isAffineHom_of_isIntegralHom π hπ)
  have hfqc : IsQuasiCompact B S hS (π ≫ j) :=
    isQuasiCompact_comp B S hS hV hY π j hπqc hjqc
  have hfsep : IsSeparated B S hS (π ≫ j) :=
    isSeparated_comp B S hS π j (isSeparated_of_isIntegralHom B S hS π hZ hV hπ)
      (isSeparated_of_mono j hmj)
  have hfqs : IsQuasiSeparated B S hS (π ≫ j) := isQuasiSeparated_of_isSeparated B S hS hfsep
  -- the normalization of `Y` in `Z`
  obtain ⟨N⟩ := NormalizationGluing.nonempty_normalizationInData_of_isQuasiCompact_isQuasiSeparated
    B S hS (π ≫ j) hZ hY hrep hfqc hfqs
  refine ⟨N.space, N.fromNorm, N.toNorm, N.isAlgebraicSpace,
    N.isIntegralHom_fromNorm_of_isQuasiCompact_isQuasiSeparated hZ hY hrep hfqc hfqs, ?_⟩
  -- a surjective étale scheme chart of `V`; composed with `j` it is an étale chart of `Y`
  obtain ⟨U, u, husurj, huet⟩ := hV.exists_atlas
  have huet' : IsEtale B S hS u := (isEtale_iff_presheaf_of_yoneda B S hS u).2 huet
  have hwet : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (u ≫ j) :=
    (isEtale_iff_presheaf_of_yoneda B S hS (u ≫ j)).1
      (isEtale_comp B S hS huet' (isEtale_of_isOpenImmersion B S hS hj))
  -- the chart base change of `f` along `u ≫ j`
  have hsq : IsPullback (hrep.fst (u ≫ j)) (yoneda.map (hrep.snd (u ≫ j))) (π ≫ j) (u ≫ j) :=
    hrep.isPullback (u ≫ j)
  have : QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd (u ≫ j))) :=
    NormalizationGluing.quasiCompact_hrep_snd_of_isQuasiCompact B S hS hrep hfqc (u ≫ j)
  have : QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd (u ≫ j))) :=
    NormalizationGluing.quasiSeparated_hrep_snd_of_isQuasiSeparated B S hS hrep hZ hY hfqs (u ≫ j)
  -- it is also the chart base change of `π` along `u`, because `j` is a monomorphism
  have hcomm : hrep.fst (u ≫ j) ≫ π = yoneda.map (hrep.snd (u ≫ j)) ≫ u := by
    refine (cancel_mono j).1 ?_
    rw [Category.assoc, Category.assoc]
    exact hsq.w
  have hleft : IsPullback (hrep.fst (u ≫ j)) (yoneda.map (hrep.snd (u ≫ j))) π u := by
    refine IsPullback.of_right ?_ hcomm hsqj
    simpa using hsq
  -- hence it is an integral morphism of schemes
  have hpint : _root_.AlgebraicGeometry.IsIntegralHom
      ((BigFppfOver.toScheme B S hS).map (hrep.snd (u ≫ j))) :=
    hpresπ.property u (hrep.fst (u ≫ j)) (hrep.snd (u ≫ j)) hleft
  -- the chart description of the normalization over the chart `u ≫ j`
  obtain ⟨W', q, b, r, e, hbq, hrb, hre, heq⟩ :=
    N.chart U (hrep.pullback (u ≫ j)) (u ≫ j) (hrep.snd (u ≫ j)) (hrep.fst (u ≫ j))
      hwet hsq
  -- `r` is an isomorphism: it is the canonical morphism to the relative normalization of an
  -- integral morphism of schemes, read through the identification `e`
  have : IsIso ((BigFppfOver.toScheme B S hS).map r) := by
    rw [show (BigFppfOver.toScheme B S hS).map r =
        ((BigFppfOver.toScheme B S hS).map (hrep.snd (u ≫ j))).toNormalization ≫ e.inv by
      rw [← hre, Category.assoc, e.hom_inv_id, Category.comp_id]]
    infer_instance
  have : IsIso r := isIso_of_reflects_iso r (BigFppfOver.toScheme B S hS)
  have hrq : r ≫ q = hrep.snd (u ≫ j) := by
    apply (BigFppfOver.toScheme B S hS).map_injective
    rw [Functor.map_comp, ← heq, ← Category.assoc, hre,
      Scheme.Hom.toNormalization_fromNormalization]
  -- so the outer rectangle is cartesian
  have houter := (IsPullback.of_horiz_isIso
    (P := yoneda.obj (hrep.pullback (u ≫ j))) (fst := yoneda.map r)
    (snd := yoneda.map (hrep.snd (u ≫ j))) (f := yoneda.map q) (g := 𝟙 (yoneda.obj U))
    (CommSq.mk (by rw [Category.comp_id, ← Functor.map_comp, hrq]))).paste_horiz hbq
  rw [hrb, Category.id_comp] at houter
  -- and Tag 07VZ cancels it against the left-hand square
  exact isPullback_right_of_isPullback_of_surjective_etale B S hS
    (isAlgebraicSpace_yoneda B S hS (hrep.pullback (u ≫ j)))
    (isAlgebraicSpace_yoneda B S hS U) hZ hV N.isAlgebraicSpace hY N.fac hleft houter
    ((presheafSurjective_iff_isSurjective_yoneda B S hS V hV U u).1 husurj) huet'

end AlgebraicGeometry.Space

end
