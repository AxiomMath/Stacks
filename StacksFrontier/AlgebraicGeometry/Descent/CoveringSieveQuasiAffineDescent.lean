module

public import StacksFrontier.AlgebraicGeometry.Descent.FlatChartStableOpen
public import StacksFrontier.AlgebraicGeometry.Descent.StableOpenQuasiFiniteDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafChartFromDiagonal

/-!
# Steps 3 and 4 of Stacks 02W8 for a flat chart, and Stacks 0265 from Stacks 0247

`AlgebraicGeometry.Space.coveringSieveBody_affineBase_of_representable` reduces the affine-base
body of `AlgebraicGeometry.Space.IsEffectiveDescentAlongCoveringSieve` to the third and fourth
steps of Stacks 02W8 for a *flat* chart. This file carries out those two steps, and composes
everything: the three conclusions of Stacks 0265 follow from Stacks 0247 in covering-sieve form
and from nothing else.

The third step is Stacks 02LR, that a quasi-compact separated locally quasi-finite morphism
locally of finite type is quasi-affine; it is proved, as
`AlgebraicGeometry.isSeparated_inf_quasiFinite_le_isQuasiAffineHom`, and it applies verbatim to
the flat chart, since what it is applied to is the composite of a quasi-compact open immersion of
the chart with the chart's other leg, and that leg carries the property of Stacks 02W8 whether
the chart is flat or étale. The fourth step is Stacks 0247, which remains the single hypothesis
of everything below.

## Main results

* `AlgebraicGeometry.Space.isRepresentable_openSubspaceOfPoints_of_flatChart`: **the third and
  fourth steps of Stacks 02W8 at one piece of the covering, for a flat chart.**
* `AlgebraicGeometry.Space.coveringSieveBody_affineBase_monomorphisms_inf_locallyOfFiniteType`:
  the affine-base body of the covering-sieve predicate at the monomorphisms locally of finite
  type, from Stacks 0247 in covering-sieve form.
* `isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft_of_isQuasiAffineHom`, in the
  namespace `AlgebraicGeometry.Space`: the full predicate at that property, with no cardinal
  hypothesis.
* `AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_of_quasiAffineDescent`,
  `AlgebraicGeometry.Space.surjective_toQuotientSheaf_of_quasiAffineDescent` and
  `AlgebraicGeometry.Space.etale_toQuotientSheaf_of_quasiAffineDescent`: **the three conclusions
  of Stacks 0265 from Stacks 0247 in covering-sieve form alone.**

## Implementation notes

*Why the carried hypothesis is the covering-sieve form of Stacks 0247 and not the
surjective-étale form.* Step 4 needs the representability half of Stacks 03I2 along the chart
produced by step 1, and that chart is flat, not étale.
`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale` quantifies over étale covering
morphisms and says nothing whatever about a flat one, so it cannot be used; the covering-sieve
predicate can, through
`AlgebraicGeometry.Space.presheaf_of_surjectiveFlatChart_of_coveringSieveDescent`, because a
single surjective flat morphism locally of finite presentation generates a covering sieve. The
covering-sieve predicate is the strictly stronger of the two, so this is a genuine strengthening
of the hypothesis relative to the étale argument, and it is the shape in which the source states
Stacks 0247: descent along an fppf *covering*, not along a single étale morphism.

*Why the hypothesis is not a disguise for the conclusion.* It is taken at
`AlgebraicGeometry.IsQuasiAffineHom`, and the conclusion is at
`MorphismProperty.monomorphisms Scheme.{u} ⊓ AlgebraicGeometry.LocallyOfFiniteType`. Neither
property contains the other — a monomorphism locally of finite type need not be quasi-compact,
hence need not be quasi-affine, and a quasi-affine morphism need not be a monomorphism — so
`AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_of_le`, which transfers the
predicate downwards along `≤`, relates them in neither direction. This is the same relation the
étale argument has between its hypothesis and its conclusion in
`StacksFrontier.AlgebraicGeometry.Descent.StableOpenQuasiFiniteDescent`.

*The cardinal situation.* `B.cutoff.IsRegular` is used nowhere on this path and cannot be: a
cardinal which is both a strong prelimit and regular is inaccessible, while
`AlgebraicGeometry.BigFppfSite.cutoff_isStrongPrelimit` and
`AlgebraicGeometry.BigFppfSite.aleph0_lt_cutoff_cof` are all the site guarantees. The glueing of
step 5 is paid for by the flat chart's size bound, the passage from affine to arbitrary base
objects by `AlgebraicGeometry.Scheme.size_le_of_mono` — which is why the conclusion is taken at a
property below the monomorphisms — and step 1 forms only finite index types.

## References

* [Stacks Project, Tag 0265](https://stacks.math.columbia.edu/tag/0265)
* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 02LR](https://stacks.math.columbia.edu/tag/02LR)
* [Stacks Project, Tag 0247](https://stacks.math.columbia.edu/tag/0247)
* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section StepsThreeFour

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The third and fourth steps of Stacks 02W8 at one piece of the covering, for a flat chart.**
Let `G` be a sheaf on the big fppf site of `S` carrying a morphism `π : G ⟶ yoneda.obj a`, and let
`g : yoneda.obj U ⟶ G` be a chart of `G` presented as a base change of a morphism `p : c ⟶ a` of
the site which is surjective, flat and locally of finite presentation, with `c` affine, and whose
other leg `ρ` is separated, locally quasi-finite and locally of finite type after every
represented base change. Let `W` be a set of points of `G` and suppose that the part of the chart
lying over the subfunctor `AlgebraicGeometry.Space.openSubspaceOfPoints` cut out by `W` is,
Cartesianly, an open `i : b ⟶ U` of the chart whose image is quasi-compact. Then that subfunctor
is representable.

This is `AlgebraicGeometry.Space.isRepresentable_openSubspaceOfPoints_of_isQuasiAffineHom` with
the surjective étale covering morphism weakened to a surjective flat one of finite presentation,
and the hypothesis changed accordingly from the surjective-étale form of Stacks 0247 to its
covering-sieve form.

The third step is untouched: Stacks 02LR applies to `i ≫ ρ₀`, which is separated, locally
quasi-finite and locally of finite type because `ρ₀` is and `i` is an open immersion, and
quasi-compact because `b` is a quasi-compact scheme and the affine `c` is a quasi-separated
space. The fourth step is the hypothesis `h0247`: the Cartesian square obtained by pasting `hsqb`
onto the presentation of the chart exhibits `yoneda.obj b` as a base change of
`openSubspaceOfPoints B S hS G W ⟶ yoneda.obj a` along `yoneda.map p`, so
`AlgebraicGeometry.Space.presheaf_of_surjectiveFlatChart_of_coveringSieveDescent` makes that
morphism representable, and its target is representable. -/
theorem isRepresentable_openSubspaceOfPoints_of_flatChart
    (h0247 : IsEffectiveDescentAlongCoveringSieve B S hS
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u}))
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G)
    {a c : BigFppfOver B S hS} (π : G ⟶ yoneda.obj a) (p : c ⟶ a)
    (hc : IsAffine ((BigFppfOver.toScheme B S hS).obj c))
    (hps : Surjective ((BigFppfOver.toScheme B S hS).map p))
    (hpf : Flat ((BigFppfOver.toScheme B S hS).map p))
    (hpp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map p))
    {U : BigFppfOver B S hS} {g : yoneda.obj U ⟶ G} {ρ : yoneda.obj U ⟶ yoneda.obj c}
    (sqg : IsPullback g ρ π (yoneda.map p))
    (hρ : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType :
        MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf ρ)
    {W : Set (points B S hS G)} {b : BigFppfOver B S hS} {i : b ⟶ U}
    (hi : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map i))
    (hbqc : IsCompact (Set.range ((BigFppfOver.toScheme B S hS).map i)))
    {k : yoneda.obj b ⟶ (openSubspaceOfPoints B S hS G W).toFunctor}
    (hsqb : IsPullback k (yoneda.map i) (openSubspaceOfPoints B S hS G W).ι g) :
    (openSubspaceOfPoints B S hS G W).toFunctor.IsRepresentable := by
  have _hc := hc
  have _hi := hi
  have _hqari := isQuasiAffineHom_respectsIso.{u}
  have _hsepbc :=
    isSeparated_inf_locallyQuasiFinite_inf_locallyOfFiniteType_isStableUnderBaseChange.{u}
  -- the morphism of the site underlying `ρ`, and the property it carries
  set ρ₀ : U ⟶ c := yoneda.preimage ρ
  have hρmap : yoneda.map ρ₀ = ρ := Functor.map_preimage _ _
  obtain ⟨⟨hsep, hqf⟩, hft⟩ :
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType :
        MorphismProperty Scheme.{u}) ((BigFppfOver.toScheme B S hS).map ρ₀) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ ρ₀).1 (hρmap ▸ hρ)
  have _hsep := hsep
  have _hqf := hqf
  have _hft := hft
  -- the open `b` is a quasi-compact scheme, so `i ≫ ρ₀` is a quasi-compact morphism
  have _hcs : CompactSpace ((BigFppfOver.toScheme B S hS).obj b) :=
    ⟨hi.base_open.isEmbedding.isCompact_iff.2 (by rwa [Set.image_univ])⟩
  have _hqsp : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj c) :=
    quasiSeparatedSpace_of_isAffine _
  -- the third step: Stacks 02LR applied to `i ≫ ρ₀`
  have hQA : _root_.AlgebraicGeometry.IsQuasiAffineHom
      ((BigFppfOver.toScheme B S hS).map (i ≫ ρ₀)) := by
    rw [Functor.map_comp]
    exact isSeparated_inf_quasiFinite_le_isQuasiAffineHom _
      ⟨⟨⟨inferInstance, inferInstance⟩, inferInstance⟩, inferInstance⟩
  have hQAp : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map i ≫ ρ) := by
    rw [← hρmap, ← Functor.map_comp]
    exact (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ (i ≫ ρ₀)).2 hQA
  -- the fourth step: the pasted square is the datum of the open subfunctor over `yoneda.obj a`
  have sqF : IsPullback k (yoneda.map i ≫ ρ)
      ((openSubspaceOfPoints B S hS G W).ι ≫ π) (yoneda.map p) := hsqb.paste_vert sqg
  have hpb := IsPullback.of_hasPullback
    ((openSubspaceOfPoints B S hS G W).ι ≫ π) (yoneda.map p)
  have hV : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
        (pullback.snd ((openSubspaceOfPoints B S hS G W).ι ≫ π) (yoneda.map p)) := by
    rw [← hpb.isoIsPullback_hom_snd _ _ sqF]
    exact MorphismProperty.RespectsIso.precomp _ _ _ hQAp
  exact Functor.isRepresentable_of_relativelyRepresentable_of_target_isRepresentable _
    (presheaf_of_surjectiveFlatChart_of_coveringSieveDescent h0247
      (isSheaf_openSubspaceOfPoints B S hS hG W)
      (BigFppfOver.isSheaf_yoneda_obj B S hS a)
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ p).2 hps)
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ p).2 hpf)
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ p).2 hpp) hV).rep

/-! ### The covering-sieve predicate at the monomorphisms locally of finite type -/

/-- **The affine-base body of the covering-sieve predicate at the monomorphisms locally of finite
type, from Stacks 0247 in covering-sieve form.** This is
`AlgebraicGeometry.Space.coveringSieveBody_affineBase_of_representable` — steps 1, 2 and 5 of
Stacks 02W8 — with its hypothesis discharged by
`AlgebraicGeometry.Space.isRepresentable_openSubspaceOfPoints_of_flatChart`, the third and fourth
steps.

The leg of the chart carries the monomorphisms locally of finite type, which lies below the
property of Stacks 02W8 by
`AlgebraicGeometry.monomorphisms_inf_locallyOfFiniteType_le_stacks02W8`; that is all the
third step needs of it. -/
theorem coveringSieveBody_affineBase_monomorphisms_inf_locallyOfFiniteType
    (h0247 : IsEffectiveDescentAlongCoveringSieve B S hS
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})) :
    ∀ ⦃X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (f : X ⟶ Y),
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) X →
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y →
      ∀ ⦃a : BigFppfOver B S hS⦄ (h : yoneda.obj a ⟶ Y) (T : Sieve a),
        IsAffine ((BigFppfOver.toScheme B S hS).obj a) →
        T ∈ BigFppfOver.topology B S hS a →
        (∀ ⦃b : BigFppfOver B S hS⦄ (q : b ⟶ a), T q →
          ((MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType).inverseImage
            (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f (yoneda.map q ≫ h))) →
        ((MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType).inverseImage
          (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f h) := by
  have _h1 := monomorphisms_inf_locallyOfFiniteType_isZariskiLocalAtTarget.{u}
  have _h2 := monomorphisms_inf_locallyOfFiniteType_descendsAlong_fppf.{u}
  refine coveringSieveBody_affineBase_of_representable ?_
  intro G hG a c π p ha hc hps hpf hpp U g ρ sqg hρ W b i k hi hbqc hsqb
  exact isRepresentable_openSubspaceOfPoints_of_flatChart h0247 hG π p hc hps hpf hpp sqg
    (MorphismProperty.relative_monotone
      (MorphismProperty.monotone_inverseImage (BigFppfOver.toScheme B S hS)
        monomorphisms_inf_locallyOfFiniteType_le_stacks02W8) _ hρ)
    hi hbqc hsqb

end StepsThreeFour

/-! ### Stacks 0265 from Stacks 0247 in covering-sieve form -/

open Stacks.Groupoids

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (U : BigFppfOver B S hS)
  [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  {R : Over S}
  (j : PreRelation R ((Over.post B.inclusion).obj U))
  [IsEtaleEquivalenceRelation j]
  (h0247 : IsEffectiveDescentAlongCoveringSieve B S hS
    (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u}))

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
include h0247 in
/-- **Effective descent along the covering sieves of the big fppf site of `S` at the
monomorphisms locally of finite type, from Stacks 0247 in covering-sieve form.** No cardinal
hypothesis and no hypothesis on the site's cutoff is used: the passage from affine to arbitrary
base objects is paid for by `AlgebraicGeometry.Scheme.size_le_of_mono`, which is available
because the property lies below the monomorphisms. -/
theorem isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft_of_isQuasiAffineHom :
    IsEffectiveDescentAlongCoveringSieve B S hS
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType) :=
  isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_locallyOfFiniteType_of_affineBase
    B S hS (coveringSieveBody_affineBase_monomorphisms_inf_locallyOfFiniteType h0247)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] in
include h0247 in
/-- **Stacks 0265, the algebraic-space property, from Stacks 0247 in covering-sieve form alone.**
The quotient sheaf of an étale equivalence relation on an object of the big fppf site of `S` is
an algebraic space over `S`. Stacks 0265 assumes the underlying scheme of `U` affine; the proof
does not use it.

It does **not** carry `@[stacks 0265]`: the hypothesis `h0247` is undischarged. What has been
removed, relative to
`AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_of_affineBase`, is the whole of Stacks
02W8 for this predicate — its five steps are now proved — leaving the one classical input the
source also leaves, effective descent of quasi-affine morphisms. -/
theorem isAlgebraicSpace_quotientSheaf_of_quasiAffineDescent :
    IsAlgebraicSpace B S hS
      (quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion) j).obj :=
  isAlgebraicSpace_quotientSheaf_of_diagDescent B S hS U j
    (isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft_of_isQuasiAffineHom
    B S hS h0247)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] in
include h0247 in
/-- **Stacks 0265, surjectivity of the quotient map, from Stacks 0247 in covering-sieve form
alone.** It does **not** carry `@[stacks 0265]`: the hypothesis `h0247` is undischarged. -/
theorem surjective_toQuotientSheaf_of_quasiAffineDescent :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
      (yonedaEquiv.symm
        ((toQuotientSheaf (BigFppfOver.topology B S hS)
          (Over.post B.inclusion) j).app (Opposite.op U)
          (𝟙 ((Over.post B.inclusion).obj U)))) :=
  surjective_toQuotientSheaf_of_diagDescent B S hS U j
    (isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft_of_isQuasiAffineHom
    B S hS h0247)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] in
include h0247 in
/-- **Stacks 0265, étaleness of the quotient map, from Stacks 0247 in covering-sieve form
alone.** It does **not** carry `@[stacks 0265]`: the hypothesis `h0247` is undischarged. -/
theorem etale_toQuotientSheaf_of_quasiAffineDescent :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
      (yonedaEquiv.symm
        ((toQuotientSheaf (BigFppfOver.topology B S hS)
          (Over.post B.inclusion) j).app (Opposite.op U)
          (𝟙 ((Over.post B.inclusion).obj U)))) :=
  etale_toQuotientSheaf_of_diagDescent B S hS U j
    (isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft_of_isQuasiAffineHom
    B S hS h0247)

end AlgebraicGeometry.Space

end
