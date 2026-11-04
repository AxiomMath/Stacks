module

public import StacksFrontier.AlgebraicGeometry.Descent.ZariskiCoverSizeBound
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusRelative

/-!
# Reducing the base of a surjective étale descent datum to an affine object

`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale` quantifies over a morphism
`h : yoneda.obj a ⟶ Y` out of a representable presheaf and a surjective étale `q : c ⟶ a` of the
big fppf site of `S`. Step 1 of Stacks 02W8 replaces an arbitrary fppf covering by a single
faithfully flat morphism *of affines*; the single morphism is already built into the predicate,
and refining the source `c` is
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_refinement`. What is proved
here is the remaining half: the base object `a` may be assumed affine.

## Main results

* `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_affineBase`: **the
  affine-base reduction.** If the defining condition of
  `AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale` holds whenever the base object
  `a` is affine, then it holds for every object `a` of the site. The hypothesis is the predicate's
  own body with `IsAffine ((BigFppfOver.toScheme B S hS).obj a)` added, and nothing else is
  changed.

## Implementation notes

*The argument.* The affine opens of `a` are objects `V U` of the site with open immersions
`u U : V U ⟶ a` covering `a`, by
`AlgebraicGeometry.BigFppfOver.exists_affineOpen_restrict`. Over each of them the datum restricts:
the site has fibre products and `AlgebraicGeometry.BigFppfOver.toScheme` preserves them, so
`pullback.snd q (u U) : c ×[a] V U ⟶ V U` is again surjective and étale, and the base change of
`(m, r)` along it is a descent datum for `f` over `V U` whose projection still has `P` after every
represented base change, `CategoryTheory.MorphismProperty.relative` being stable under base change.
The affine-base hypothesis therefore applies over `V U`, and makes `X ×[Y] yoneda.obj (V U)`
representable by Tag 03KC. Those representing objects are open subfunctors of
`X ×[Y] yoneda.obj a` — each is a base change of `yoneda.map (u U)` — and are jointly locally
surjective onto it by
`AlgebraicGeometry.Space.isLocallySurjective_sigmaDesc_of_openCover`. That is exactly the Zariski
covering asked for by
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_zariskiCover_of_mk_lt_cutoff`,
which glues it.

*No cofinality bound, and no uniform size bound either.* The index type is the affine opens of
`a`, of cardinality at most `((BigFppfOver.toScheme B S hS).obj a).size < B.cutoff` by
`AlgebraicGeometry.Scheme.mk_affineOpens_le_size`; that is the only cardinal hypothesis the
glueing statement used here asks for, since
`AlgebraicGeometry.Space.exists_size_bound_of_descentDatum` extracts a uniform bound on the
pieces from the datum itself. Nothing is asked of the cofinality of `B.cutoff`, which is as well:
`AlgebraicGeometry.BigFppfSite.cutoff_isStrongPrelimit` is all that is known of it. The
obstruction recorded for the neighbouring statement in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfaeComplete` — that nothing bounds the index type
of an arbitrary Zariski covering — does not arise here, because the covering is not arbitrary: it
is produced from `a` itself.

## References

* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 02W3](https://stacks.math.columbia.edu/tag/02W3)
* [Stacks Project, Tag 03KC](https://stacks.math.columbia.edu/tag/03KC)
-/

@[expose] public section

open Cardinal CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The affine-base reduction for effective descent along surjective étale morphisms.**
Effective descent along the surjective étale morphisms of the big fppf site of `S` may be verified
over affine base objects only: if the defining condition of
`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale` holds for every datum whose base
object `a` is affine, then it holds for every datum.

The hypothesis `H` is the body of
`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale` with the single extra assumption
`IsAffine ((BigFppfOver.toScheme B S hS).obj a)`; no other quantifier is restricted and no other
hypothesis is added.

Together with
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_refinement`, which refines the
source of the covering morphism, this is step 1 of Stacks 02W8: the reduction to a single
faithfully flat morphism of affine schemes. -/
theorem isEffectiveDescentAlongSurjectiveEtale_of_affineBase
    {P : MorphismProperty Scheme.{u}}
    [P.RespectsIso] [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    (H : ∀ ⦃X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (f : X ⟶ Y),
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) X →
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y →
      ∀ ⦃a c : BigFppfOver B S hS⦄ (h : yoneda.obj a ⟶ Y) (q : c ⟶ a),
        IsAffine ((BigFppfOver.toScheme B S hS).obj a) →
        Surjective ((BigFppfOver.toScheme B S hS).map q) →
        Etale ((BigFppfOver.toScheme B S hS).map q) →
        ∀ ⦃A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (m : A ⟶ X) (r : A ⟶ yoneda.obj c),
          IsPullback m r f (yoneda.map q ≫ h) →
          (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf r →
          (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f h)) :
    IsEffectiveDescentAlongSurjectiveEtale B S hS P := by
  refine isEffectiveDescentAlongSurjectiveEtale_of_zariskiCover_of_mk_lt_cutoff ?_
  intro X Y f hX hY a c h q hqs hqe A m r sq hr
  have _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have hstable := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (P.inverseImage (BigFppfOver.toScheme B S hS))
  -- the affine opens of the base, as objects of the site
  choose V u hu hurange hVaff using fun U => BigFppfOver.exists_affineOpen_restrict B S hS a U
  have hucov : ∀ y : (BigFppfOver.toScheme B S hS).obj a,
      ∃ U, y ∈ Set.range ((BigFppfOver.toScheme B S hS).map (u U)) := by
    intro y
    have hy : y ∈ (⊤ : ((BigFppfOver.toScheme B S hS).obj a).Opens) := trivial
    rw [← iSup_affineOpens_eq_top] at hy
    obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    exact ⟨U, by rw [hurange U]; exact hU⟩
  -- over each affine open the datum restricts, and the affine-base hypothesis applies
  have key : ∀ U, ∃ (W : BigFppfOver B S hS) (pr : W ⟶ V U)
      (k : yoneda.obj W ⟶ pullback f h),
      IsPullback k (yoneda.map pr) (pullback.snd f h) (yoneda.map (u U)) := by
    intro U
    -- the restriction of the covering morphism, still surjective and étale
    have hsqsch : IsPullback ((BigFppfOver.toScheme B S hS).map (pullback.fst q (u U)))
        ((BigFppfOver.toScheme B S hS).map (pullback.snd q (u U)))
        ((BigFppfOver.toScheme B S hS).map q) ((BigFppfOver.toScheme B S hS).map (u U)) :=
      (IsPullback.of_hasPullback q (u U)).map (BigFppfOver.toScheme B S hS)
    -- the restriction of the datum
    have hbc : IsPullback (pullback.fst r (yoneda.map (pullback.fst q (u U))))
        (pullback.snd r (yoneda.map (pullback.fst q (u U)))) r
        (yoneda.map (pullback.fst q (u U))) := IsPullback.of_hasPullback _ _
    have heq : yoneda.map (pullback.fst q (u U)) ≫ yoneda.map q ≫ h =
        yoneda.map (pullback.snd q (u U)) ≫ yoneda.map (u U) ≫ h := by
      rw [← Category.assoc, ← Functor.map_comp, ← Category.assoc, ← Functor.map_comp,
        pullback.condition]
    have hdat : IsPullback (pullback.fst r (yoneda.map (pullback.fst q (u U))) ≫ m)
        (pullback.snd r (yoneda.map (pullback.fst q (u U)))) f
        (yoneda.map (pullback.snd q (u U)) ≫ yoneda.map (u U) ≫ h) := by
      rw [← heq]
      exact hbc.paste_horiz sq
    -- the affine-base hypothesis over `V U`
    have hH := H f hX hY (yoneda.map (u U) ≫ h) (pullback.snd q (u U)) (hVaff U)
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback hsqsch hqs)
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback hsqsch hqe) _ _ hdat
      (MorphismProperty.of_isPullback hbc hr)
    have _ : (pullback f (yoneda.map (u U) ≫ h)).IsRepresentable :=
      Functor.isRepresentable_of_relativelyRepresentable_of_target_isRepresentable
        (pullback.snd f (yoneda.map (u U) ≫ h)) hH.rep
    -- the representing object is an open subfunctor of `X ×[Y] yoneda.obj a`
    set e := (pullback f (yoneda.map (u U) ≫ h)).reprW with he
    have hsqR := (IsPullback.of_hasPullback f (yoneda.map (u U) ≫ h)).of_right'
      (IsPullback.of_hasPullback f h)
    refine ⟨_, yoneda.preimage (e.hom ≫ pullback.snd f (yoneda.map (u U) ≫ h)),
      e.hom ≫ (IsPullback.of_hasPullback f h).lift
        (pullback.fst f (yoneda.map (u U) ≫ h))
        (pullback.snd f (yoneda.map (u U) ≫ h) ≫ yoneda.map (u U))
        (by rw [(IsPullback.of_hasPullback f (yoneda.map (u U) ≫ h)).w, Category.assoc]), ?_⟩
    rw [Functor.map_preimage]
    exact hsqR.of_iso' e (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp)
      (by simp)
  choose W pr k hpb using key
  refine ⟨_, ((BigFppfOver.toScheme B S hS).obj a).mk_affineOpens_le_size.trans_lt
      a.left.property, W, k, fun U => isOpenImmersion_of_isPullback_yoneda_map B S hS (hu U)
      (hpb U), isLocallySurjective_sigmaDesc_of_openCover B S hS hu hucov hpb⟩

end AlgebraicGeometry.Space

end
