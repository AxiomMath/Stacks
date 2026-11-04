module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineBaseQuasiCompactDescent
public import StacksFrontier.AlgebraicGeometry.Descent.FlatChartDescent
public import StacksFrontier.AlgebraicGeometry.Descent.StableQuasiCompactOpen

/-!
# Steps 2 and 5 of Stacks 02W8 for a covering sieve over an affine base

`AlgebraicGeometry.Space.coveringSieveBody_affineBase_of_affineFlatSource` reduces the body of
`AlgebraicGeometry.Space.IsEffectiveDescentAlongCoveringSieve` over an affine base object to the
same body with the covering sieve replaced by a *single* morphism `p : c ⟶ a` which is
surjective, flat, locally of finite presentation and quasi-compact with `c` affine — step 1 of
Descent, Lemma 02W3. This file carries out the second and the fifth steps of Stacks 02W8 for that
reduced body, leaving the third and fourth.

It is the covering-sieve counterpart of
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_representable_of_affineBase`,
and the proof is the same one: the hypothesis at `p` makes `X ×[Y] yoneda.obj c` representable by
Tag 03KC, hence exhibits a chart `g : yoneda.obj U ⟶ X ×[Y] yoneda.obj a` as a base change of
`yoneda.map p`; the saturations of the affine opens of `U` cut out open subfunctors of
`X ×[Y] yoneda.obj a` which are Cartesian over quasi-compact opens of `U`, which is step 2; and
the resulting Zariski covering is glued by Tag 01JJ, which is step 5.

## Main results

* `AlgebraicGeometry.Space.coveringSieveBody_affineFlatSource_of_representable`: **steps 2 and 5
  of Stacks 02W8 for the reduced body.** The body of
  `AlgebraicGeometry.Space.IsEffectiveDescentAlongCoveringSieve` at a single surjective flat
  quasi-compact morphism of finite presentation of affines follows from the third and fourth
  steps alone.
* `AlgebraicGeometry.Space.coveringSieveBody_affineBase_of_representable`: the same statement
  composed with step 1, so that what is left of Stacks 02W8 for the affine-base body of the
  covering-sieve predicate is its third and fourth steps.

## Implementation notes

*Why the chart is flat and not étale, and why that is enough.* The single morphism of step 1 is
built from the arrows of the covering sieve, which are only flat and locally of finite
presentation; no étale refinement of an fppf covering exists. Each of the four places where the
étale argument uses étaleness of the covering morphism has a flat form, collected in
`StacksFrontier.AlgebraicGeometry.Descent.FlatChartDescent`: the openness of step 2 is Stacks 01UA,
which asks only for flatness and local finite presentation; the uniform size bound of step 5 is
`AlgebraicGeometry.Space.exists_size_bound_of_flatChart`, which asks only for flatness and
surjectivity; and the transport of the property onto the descended morphism is fppf descent,
which asks for the conjunction `surjective ⊓ flat ⊓ locally of finite presentation` that `p`
carries by hypothesis.

*What quasi-compactness of `p` is for.* Exactly one thing: the first projection of the fibre
product of the chart with itself inside the site is a base change of `p`, hence quasi-compact,
which is what makes the saturation of a quasi-compact open quasi-compact in
`AlgebraicGeometry.Space.isCompact_preimage_image_pointsMap`. This is
`AlgebraicGeometry.Space.exists_isPullback_self_of_quasiCompact`, which never looks at
étaleness.

*The shape of the surviving hypothesis.* `H` below is stated for an arbitrary presheaf `G` with a
morphism to a representable and an arbitrary set of points, rather than for
`X ×[Y] yoneda.obj a` and the saturations this file feeds it; that is the shape in which
`AlgebraicGeometry.Space.isRepresentable_openSubspaceOfPoints_of_isQuasiAffineHom` — the étale
third-and-fourth step — is already proved, its own implementation notes recording that the set of
points is never used.

*No cardinal hypothesis.* The index type of the covering is the affine opens of the chart,
bounded by its size through `AlgebraicGeometry.Scheme.mk_affineOpens_le_size`, and the pieces are
bounded uniformly by the flat chart. Nothing is asked of the site's cutoff beyond
`AlgebraicGeometry.BigFppfSite.cutoff_isStrongPrelimit`; in particular `B.cutoff.IsRegular` is
not used.

## References

* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 02W3](https://stacks.math.columbia.edu/tag/02W3)
* [Stacks Project, Tag 03KC](https://stacks.math.columbia.edu/tag/03KC)
* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
* [Stacks Project, Tag 01UA](https://stacks.math.columbia.edu/tag/01UA)
-/

@[expose] public section

open Cardinal CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Steps 2 and 5 at a single surjective flat morphism of affines -/

/-- **Steps 2 and 5 of Stacks 02W8 for a covering sieve over an affine base, reduced to steps 3
and 4.** Let `P` be a property of morphisms of schemes which respects isomorphisms and descends
along the surjective flat morphisms of finite presentation, and suppose the following holds. For
every sheaf `G` on the big fppf site of `S` with a morphism `π : G ⟶ yoneda.obj a` to a
representable, every surjective flat morphism `p : c ⟶ a` of the site locally of finite
presentation with `a` and `c` affine, every chart `g : yoneda.obj U ⟶ G` presented as a base
change of `yoneda.map p` along `π` whose other leg carries `P`, and every set `W` of points of
`G` such that the part of the chart lying over the open subfunctor cut out by `W` is, Cartesianly,
an open `i : b ⟶ U` of the chart with quasi-compact image, that open subfunctor is
representable.

Then the body of `AlgebraicGeometry.Space.IsEffectiveDescentAlongCoveringSieve` holds whenever
the covering sieve has been replaced by a single morphism `p` which is surjective, flat, locally
of finite presentation and quasi-compact, with affine base and affine source — which is the
hypothesis of `AlgebraicGeometry.Space.coveringSieveBody_affineBase_of_affineFlatSource`.

The hypothesis `H` is the third and fourth steps of Stacks 02W8: Stacks 02LR, that a
quasi-compact separated locally quasi-finite morphism locally of finite type is quasi-affine,
which is proved as `AlgebraicGeometry.isSeparated_inf_quasiFinite_le_isQuasiAffineHom`, and
Stacks 0247, that quasi-affine morphisms descend effectively, which is not. -/
theorem coveringSieveBody_affineFlatSource_of_representable
    {P : MorphismProperty Scheme.{u}} [P.RespectsIso]
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    (H : ∀ ⦃G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄,
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) G →
      ∀ ⦃a c : BigFppfOver B S hS⦄ (π : G ⟶ yoneda.obj a) (p : c ⟶ a),
        IsAffine ((BigFppfOver.toScheme B S hS).obj a) →
        IsAffine ((BigFppfOver.toScheme B S hS).obj c) →
        Surjective ((BigFppfOver.toScheme B S hS).map p) →
        Flat ((BigFppfOver.toScheme B S hS).map p) →
        LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map p) →
        ∀ ⦃U : BigFppfOver B S hS⦄ (g : yoneda.obj U ⟶ G) (ρ : yoneda.obj U ⟶ yoneda.obj c),
          IsPullback g ρ π (yoneda.map p) →
          (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf ρ →
          ∀ (W : Set (points B S hS G)) (b : BigFppfOver B S hS) (i : b ⟶ U)
            (k : yoneda.obj b ⟶ (openSubspaceOfPoints B S hS G W).toFunctor),
            _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map i) →
            IsCompact (Set.range ((BigFppfOver.toScheme B S hS).map i)) →
            IsPullback k (yoneda.map i) (openSubspaceOfPoints B S hS G W).ι g →
            (openSubspaceOfPoints B S hS G W).toFunctor.IsRepresentable) :
    ∀ ⦃X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (f : X ⟶ Y),
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) X →
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y →
      ∀ ⦃a c : BigFppfOver B S hS⦄ (h : yoneda.obj a ⟶ Y) (p : c ⟶ a),
        IsAffine ((BigFppfOver.toScheme B S hS).obj a) →
        IsAffine ((BigFppfOver.toScheme B S hS).obj c) →
        Surjective ((BigFppfOver.toScheme B S hS).map p) →
        Flat ((BigFppfOver.toScheme B S hS).map p) →
        LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map p) →
        QuasiCompact ((BigFppfOver.toScheme B S hS).map p) →
        (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
          (pullback.snd f (yoneda.map p ≫ h)) →
        (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f h) := by
  intro X Y f hX hY a c h p ha hc hps hpf hpp hpqc hH
  have hbc := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (P.inverseImage (BigFppfOver.toScheme B S hS))
  have hri : MorphismProperty.RespectsIso
      ((P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf) := hbc.respectsIso
  -- the hypothesis at `p` is a descent datum whose total space is representable, by Tag 03KC
  have sq : IsPullback (pullback.fst f (yoneda.map p ≫ h))
      (pullback.snd f (yoneda.map p ≫ h)) f (yoneda.map p ≫ h) :=
    IsPullback.of_hasPullback _ _
  have _ : (pullback f (yoneda.map p ≫ h)).IsRepresentable :=
    Functor.isRepresentable_of_relativelyRepresentable_of_target_isRepresentable _ hH.rep
  set A := pullback f (yoneda.map p ≫ h) with hA
  have sq₂ := sq.of_right' (IsPullback.of_hasPullback f h)
  set ℓ := A.reprW.hom ≫ (IsPullback.of_hasPullback f h).lift
    (pullback.fst f (yoneda.map p ≫ h))
    (pullback.snd f (yoneda.map p ≫ h) ≫ yoneda.map p)
    (by rw [sq.w, Category.assoc]) with hℓ
  have sq₃ : IsPullback ℓ (A.reprW.hom ≫ pullback.snd f (yoneda.map p ≫ h))
      (pullback.snd f h) (yoneda.map p) :=
    sq₂.of_iso' A.reprW (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [hℓ]) (by simp) (by simp)
      (by simp)
  have hρ : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
      (A.reprW.hom ≫ pullback.snd f (yoneda.map p ≫ h)) :=
    MorphismProperty.RespectsIso.precomp _ _ _ hH
  -- the fibre product of the chart with itself, with quasi-compact first projection
  obtain ⟨D, π₁, π₂, sqD, hπ₁⟩ := exists_isPullback_self_of_quasiCompact hpqc sq₃
  -- step 2: the saturations of the affine opens of the chart, and their open subfunctors
  have hg := presheafIsOpenMap_of_isPullback_of_flat sq₃ hpf hpp
  have hFsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (pullback f h) :=
    BigFppfOver.isSheaf_pullback_yoneda_obj f h hX hY
  have hrepT : ∀ T : ((BigFppfOver.toScheme B S hS).obj A.reprX).affineOpens,
      (openSubspaceOfPoints B S hS (pullback f h)
        (pointsMap B S hS (yoneda.obj A.reprX) ℓ ''
          (pointsToScheme B S hS A.reprX ⁻¹' (T : Set _)))).toFunctor.IsRepresentable := by
    intro T
    obtain ⟨b, i, kb, hi, hirange, hsqb⟩ :=
      exists_isPullback_ι_openSubspaceOfPoints_image B S hS _ hg T.1.isOpen
    exact H hFsheaf (pullback.snd f h) p ha hc hps hpf hpp _ _ sq₃ hρ _ b i kb hi
      (hirange ▸ isCompact_preimage_image_pointsMap B S hS _ sqD hπ₁ T.1.isOpen T.2.isCompact)
      hsqb
  obtain ⟨ι, hι, W, k, hk, hksurj⟩ := exists_zariskiCover_affineOpens_of_chart B S hS _ hg
    (surjective_pointsMap_of_isPullback_of_surjective B S hS sq₃ hps) hrepT
  -- step 5: the covering glues, the pieces being bounded uniformly by the flat chart
  obtain ⟨μ, hμ, hbound⟩ := exists_size_bound_of_flatChart hps hpf sq₃
  have hrep : yoneda.relativelyRepresentable (pullback.snd f h) :=
    relativelyRepresentable_pullback_snd f h
      (isRepresentable_of_zariskiCover_of_size_le B S hS hFsheaf hι hμ W
        (fun i => hbound (W i) (k i) (hk i)) k hk hksurj)
  -- the property is recovered on the descended morphism by fppf descent along the flat chart
  exact presheaf_of_surjectiveFlatChart_of_descendsAlong hrep
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ p).2 hps)
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ p).2 hpf)
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ p).2 hpp) sq₂ hH

/-! ### Steps 1, 2 and 5 composed -/

/-- **Steps 1, 2 and 5 of Stacks 02W8 for the covering-sieve predicate over an affine base.** The
affine-base body of `AlgebraicGeometry.Space.IsEffectiveDescentAlongCoveringSieve` follows from
the third and fourth steps of Stacks 02W8 alone.

This is `AlgebraicGeometry.Space.coveringSieveBody_affineFlatSource_of_representable` composed
with `AlgebraicGeometry.Space.coveringSieveBody_affineBase_of_affineFlatSource`, which is step 1.
No cardinal hypothesis on the site is incurred by either: step 1 forms only finite index types,
and the glueing of step 5 is paid for by the size bound of the flat chart. -/
theorem coveringSieveBody_affineBase_of_representable
    {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtTarget P]
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    (H : ∀ ⦃G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄,
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) G →
      ∀ ⦃a c : BigFppfOver B S hS⦄ (π : G ⟶ yoneda.obj a) (p : c ⟶ a),
        IsAffine ((BigFppfOver.toScheme B S hS).obj a) →
        IsAffine ((BigFppfOver.toScheme B S hS).obj c) →
        Surjective ((BigFppfOver.toScheme B S hS).map p) →
        Flat ((BigFppfOver.toScheme B S hS).map p) →
        LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map p) →
        ∀ ⦃U : BigFppfOver B S hS⦄ (g : yoneda.obj U ⟶ G) (ρ : yoneda.obj U ⟶ yoneda.obj c),
          IsPullback g ρ π (yoneda.map p) →
          (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf ρ →
          ∀ (W : Set (points B S hS G)) (b : BigFppfOver B S hS) (i : b ⟶ U)
            (k : yoneda.obj b ⟶ (openSubspaceOfPoints B S hS G W).toFunctor),
            _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map i) →
            IsCompact (Set.range ((BigFppfOver.toScheme B S hS).map i)) →
            IsPullback k (yoneda.map i) (openSubspaceOfPoints B S hS G W).ι g →
            (openSubspaceOfPoints B S hS G W).toFunctor.IsRepresentable) :
    ∀ ⦃X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (f : X ⟶ Y),
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) X →
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y →
      ∀ ⦃a : BigFppfOver B S hS⦄ (h : yoneda.obj a ⟶ Y) (T : Sieve a),
        IsAffine ((BigFppfOver.toScheme B S hS).obj a) →
        T ∈ BigFppfOver.topology B S hS a →
        (∀ ⦃b : BigFppfOver B S hS⦄ (q : b ⟶ a), T q →
          (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
            (pullback.snd f (yoneda.map q ≫ h))) →
        (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f h) :=
  coveringSieveBody_affineBase_of_affineFlatSource
    (coveringSieveBody_affineFlatSource_of_representable H)

end AlgebraicGeometry.Space

end
