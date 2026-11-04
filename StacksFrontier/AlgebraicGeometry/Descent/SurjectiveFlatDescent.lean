module

public import StacksFrontier.AlgebraicGeometry.Descent.FlatChartDescent
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineFlatChartDescent

/-!
# Effective descent along a single surjective flat chart of the big fppf site

`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale` is effective fppf descent
restricted to the *one-element* coverings of the site given by a surjective étale morphism, and
`AlgebraicGeometry.Space.IsEffectiveDescentAlongCoveringSieve` is effective fppf descent along an
arbitrary covering sieve. Between the two sits the predicate this file introduces:
`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveFlat`, effective descent along the
one-element coverings given by a morphism which is surjective, flat and locally of finite
presentation. It is the shape in which a reduction to a single faithfully flat morphism —
Descent, Lemma 02W3 — delivers its covering, and it is what Stacks 046J consumes.

The point of the predicate is that it is obtainable at the property of Stacks 02W8 over an
*arbitrary* base object, which the covering-sieve predicate is not. The geometry is shared: both
reduce to the affine-base body
`AlgebraicGeometry.Space.coveringSieveBody_affineBase_isSeparated_inf_locallyQuasiFinite_inf_lft`,
which is unconditional. What separates them is the passage from an affine base object to a general
one. That passage glues the pieces descended over the affine opens of the base, and so needs one
cardinal below the site's cutoff bounding all of them. A covering sieve supplies no single
surjective morphism from which to read such a cardinal off, so for the covering-sieve predicate
the bound is a genuine debt, payable only in one of the three currencies of
`StacksFrontier.AlgebraicGeometry.Descent.AffineBaseCoveringSieveDescent` — a regular cutoff, a size
bound on the property, or containment in the monomorphisms — none of which the property of Stacks
02W8 has. A single flat morphism, on the other hand, pays for the bound by itself, through
`AlgebraicGeometry.Space.exists_size_bound_of_flatChart`, exactly as a single surjective étale
morphism does through `AlgebraicGeometry.Space.exists_size_bound_of_descentDatum`.

## Main definitions

* `AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveFlat`: morphisms with property `P`
  descend effectively along the surjective flat morphisms of the site locally of finite
  presentation. This is
  `AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale` with étaleness of the covering
  morphism replaced by flatness together with local finite presentation.

## Main results

* `AlgebraicGeometry.Space.exists_size_bound_of_flatDescentDatum`: **the uniform size bound is
  free for a descent datum along a surjective flat morphism.** One cardinal below the cutoff
  bounds the size of every object of the site representing an open subfunctor of the descended
  sheaf.
* `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveFlat_of_zariskiCover_of_mk_lt_cutoff`:
  **the glueing step with no size hypothesis on the pieces of the covering.**
* `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveFlat_of_affineBase`: **the affine-base
  reduction.** The defining condition need only be checked over affine base objects.
* `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveFlat_of_coveringSieveBody_affineBase`:
  the predicate follows from the affine-base body of the covering-sieve predicate, the one
  element of a one-element covering generating a covering sieve.
* `isEffectiveDescentAlongSurjectiveFlat_isSeparated_inf_locallyQuasiFinite_inf_lft`, in the
  `AlgebraicGeometry.Space` namespace: **Stacks 02W8 at its own property along a single surjective
  flat chart, over an arbitrary base object, unconditionally.**
* `AlgebraicGeometry.Space.presheaf_of_surjectiveFlatChart`: the representability half of Stacks
  03I2 for a flat chart, consuming the predicate of this file rather than the covering-sieve one.

## Implementation notes

*Why the four plumbing steps of the étale development collapse to two here.* The étale predicate
is proved at the property of Stacks 02W8 by composing four reductions — the glueing step
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_zariskiCover_of_mk_lt_cutoff`,
the affine-base reduction
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_affineBase`, the affine-source
refinement
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_affineBase_affineSource`, and
the composition
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_representable_of_affineBase`
which feeds the third and fourth steps of Stacks 02W8 — and only then discharging those two steps.
On the flat side the last two of those four are already done, in the covering-sieve shape and for
a flat chart: `AlgebraicGeometry.Space.coveringSieveBody_affineBase_of_representable` is steps 1,
2 and 5 over an affine base, including the affine-source refinement, and
`AlgebraicGeometry.Space.isRepresentable_openSubspaceOfPoints_of_affineFlatChart` is steps 3 and
4. Their composite at the property of Stacks 02W8 is
`AlgebraicGeometry.Space.coveringSieveBody_affineBase_isSeparated_inf_locallyQuasiFinite_inf_lft`.
So what is missing for the single-morphism flat predicate is only the first two reductions,
proved here, plus the observation that a surjective flat morphism locally of finite presentation
generates a covering sieve
(`AlgebraicGeometry.Space.sieve_generate_singleton_mem_topology_over_of_flat`) all of whose arrows
factor through it, hence carry the property by base change.

*Where the étale proofs use étaleness, and why flatness with local finite presentation suffices.*
The glueing step uses it only to produce the uniform size bound, through
`AlgebraicGeometry.Space.exists_size_bound_of_descentDatum`, whose flat counterpart
`AlgebraicGeometry.Space.exists_size_bound_of_flatChart` is already available with the bound
`max (2 ^ #U) (2 ^ U.size)`; and to feed
`AlgebraicGeometry.Space.presheaf_of_surjectiveEtaleChart_of_descendsAlong`, whose flat
counterpart is `AlgebraicGeometry.Space.presheaf_of_surjectiveFlatChart_of_descendsAlong`. The
affine-base reduction uses it only through stability under base change, which
`AlgebraicGeometry.Flat.isStableUnderBaseChange` and
`AlgebraicGeometry.locallyOfFinitePresentation_isStableUnderBaseChange` supply. Nothing in either
needs unramifiedness.

## References

* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 02W3](https://stacks.math.columbia.edu/tag/02W3)
* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
* [Stacks Project, Tag 03KC](https://stacks.math.columbia.edu/tag/03KC)
* [Stacks Project, Tag 046J](https://stacks.math.columbia.edu/tag/046J)
-/

@[expose] public section

open Cardinal CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u})

/-! ### The predicate -/

/-- Morphisms with property `P` *descend effectively along surjective flat morphisms locally of
finite presentation* of the big fppf site of `S` when the following holds. Let `f : X ⟶ Y` be a
morphism of presheaves with `X` and `Y` sheaves, let `h : yoneda.obj a ⟶ Y` be a morphism from a
representable presheaf, and let `q : c ⟶ a` be a morphism of the site whose underlying morphism
of schemes is surjective, flat and locally of finite presentation. If the base change of `f`
along `yoneda.map q ≫ h` is representable and has `P` after every representable base change, then
so is the base change of `f` along `h` itself.

This is `AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale` with étaleness of the
covering morphism replaced by the pair `AlgebraicGeometry.Flat`,
`AlgebraicGeometry.LocallyOfFinitePresentation`. The hypotheses on `q` are antecedents, so
enlarging the class of covering morphisms strengthens the predicate: an étale morphism is flat
and locally of finite presentation, so this asks for descent along more coverings than the étale
predicate does, not fewer.

It is in turn implied by `AlgebraicGeometry.Space.IsEffectiveDescentAlongCoveringSieve`, whose
coverings are arbitrary covering sieves rather than the one-element ones a single morphism
generates; the implication is the argument of
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveFlat_of_coveringSieveBody_affineBase`
without the affine-base step. Being the weaker of the two is what makes it obtainable at the
property of Stacks 02W8 over an arbitrary base object, which the covering-sieve predicate is not
without a cardinal hypothesis on the site.

The sheaf conditions on `X` and on `Y` cannot be dropped, for the reason recorded at
`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale`: without them the fibre product
`X ×[Y] yoneda.obj a` need not be a sheaf, and a presheaf which is not a sheaf is not
representable. -/
def IsEffectiveDescentAlongSurjectiveFlat : Prop :=
  ∀ ⦃X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (f : X ⟶ Y),
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) X →
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y →
    ∀ ⦃a c : BigFppfOver B S hS⦄ (h : yoneda.obj a ⟶ Y) (q : c ⟶ a),
      Surjective ((BigFppfOver.toScheme B S hS).map q) →
      Flat ((BigFppfOver.toScheme B S hS).map q) →
      LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map q) →
      ∀ ⦃A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (m : A ⟶ X) (r : A ⟶ yoneda.obj c),
        IsPullback m r f (yoneda.map q ≫ h) →
        (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf r →
        (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f h)

variable {B S hS P}

/-! ### The uniform size bound is free -/

/-- **A descent datum along a surjective flat morphism bounds the size of every representable open
subspace of the sheaf it descends to, uniformly.**

Let `f : X ⟶ Y` be a morphism of presheaves on the big fppf site of `S`, let
`h : yoneda.obj a ⟶ Y`, let `q : c ⟶ a` be surjective and flat on underlying schemes and let
`(m, r)` present a presheaf `A` as `X ×[Y] yoneda.obj c`, with `r` relatively representable — the
data of `AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveFlat`. Then there is a single
cardinal below the site's cutoff bounding the size of every object `V` of the site admitting an
open immersion `yoneda.obj V ⟶ X ×[Y] yoneda.obj a`.

This is `AlgebraicGeometry.Space.exists_size_bound_of_descentDatum` with étaleness of the covering
morphism weakened to flatness. The datum's total space `A` is representable by Tag 03KC, so the
morphism it cuts out to `X ×[Y] yoneda.obj a` is a flat chart from a representable presheaf, and
`AlgebraicGeometry.Space.exists_size_bound_of_flatChart` bounds the open subspaces of a presheaf
carrying one. Local finite presentation of `q` is not needed: the bound comes from Tag 03JH in its
flat form, which asks only for surjectivity and flatness. -/
theorem exists_size_bound_of_flatDescentDatum
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    {a c : BigFppfOver B S hS} (h : yoneda.obj a ⟶ Y) (q : c ⟶ a)
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqf : Flat ((BigFppfOver.toScheme B S hS).map q))
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (m : A ⟶ X) (r : A ⟶ yoneda.obj c)
    (sq : IsPullback m r f (yoneda.map q ≫ h))
    (hr : yoneda.relativelyRepresentable r) :
    ∃ μ : Cardinal.{u}, μ < B.cutoff ∧ ∀ (V : BigFppfOver B S hS)
      (k : yoneda.obj V ⟶ pullback f h), IsOpenImmersion B S hS k →
        ((BigFppfOver.toScheme B S hS).obj V).size ≤ μ := by
  have _ : A.IsRepresentable :=
    Functor.isRepresentable_of_relativelyRepresentable_of_target_isRepresentable r hr
  have sq₂ := sq.of_right' (IsPullback.of_hasPullback f h)
  have sq₃ : IsPullback
      (A.reprW.hom ≫ (IsPullback.of_hasPullback f h).lift m (r ≫ yoneda.map q)
        (by rw [sq.w, Category.assoc]))
      (A.reprW.hom ≫ r) (pullback.snd f h) (yoneda.map q) :=
    sq₂.of_iso' A.reprW (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp)
      (by simp)
  exact exists_size_bound_of_flatChart hqs hqf sq₃

/-! ### The glueing step -/

/-- **The glueing step of Stacks 02W8 for the surjective-flat predicate, with no size hypothesis
on the pieces of the covering.** Effective descent along the surjective flat morphisms of the big
fppf site of `S` locally of finite presentation follows from producing, for each descent datum, a
Zariski covering of the descended sheaf by representable open subfunctors whose index type has
cardinality below the site's cutoff — and nothing else.

This is
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_zariskiCover_of_mk_lt_cutoff`
for a flat covering morphism. The uniform bound on the pieces, which
`AlgebraicGeometry.isRepresentable_of_zariskiCover_of_size_le` asks for, is supplied from the
datum itself by `AlgebraicGeometry.Space.exists_size_bound_of_flatDescentDatum`; no cofinality of
the cutoff is used anywhere, which is what makes the statement usable, since
`AlgebraicGeometry.BigFppfSite.cutoff_isStrongPrelimit` is all that is known of the cutoff. -/
theorem isEffectiveDescentAlongSurjectiveFlat_of_zariskiCover_of_mk_lt_cutoff
    {P : MorphismProperty Scheme.{u}}
    [P.RespectsIso] [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    (H : ∀ ⦃X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (f : X ⟶ Y),
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) X →
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y →
      ∀ ⦃a c : BigFppfOver B S hS⦄ (h : yoneda.obj a ⟶ Y) (q : c ⟶ a),
        Surjective ((BigFppfOver.toScheme B S hS).map q) →
        Flat ((BigFppfOver.toScheme B S hS).map q) →
        LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map q) →
        ∀ ⦃A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (m : A ⟶ X) (r : A ⟶ yoneda.obj c),
          IsPullback m r f (yoneda.map q ≫ h) →
          (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf r →
          ∃ ι : Type u, #ι < B.cutoff ∧
            ∃ (W : ι → BigFppfOver B S hS) (k : ∀ i, yoneda.obj (W i) ⟶ pullback f h),
              (∀ i, IsOpenImmersion B S hS (k i)) ∧
                Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc k)) :
    IsEffectiveDescentAlongSurjectiveFlat B S hS P := by
  intro X Y f hX hY a c h q hqs hqf hqp A m r sq hr
  obtain ⟨μ, hμ, hbound⟩ := exists_size_bound_of_flatDescentDatum f h q hqs hqf m r sq hr.rep
  obtain ⟨ι, hι, W, k, hk, hksurj⟩ := H f hX hY h q hqs hqf hqp m r sq hr
  have hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (pullback f h) :=
    BigFppfOver.isSheaf_pullback_yoneda_obj f h hX hY
  have hrep : yoneda.relativelyRepresentable (pullback.snd f h) :=
    relativelyRepresentable_pullback_snd f h
      (isRepresentable_of_zariskiCover_of_size_le B S hS hF hι hμ W
        (fun i => hbound (W i) (k i) (hk i)) k hk hksurj)
  exact presheaf_of_surjectiveFlatChart_of_descendsAlong hrep
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ q).2 hqs)
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ q).2 hqf)
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ q).2 hqp)
    (sq.of_right' (IsPullback.of_hasPullback f h)) hr

/-! ### The affine-base reduction -/

/-- **The affine-base reduction for effective descent along surjective flat morphisms locally of
finite presentation.** Effective descent along those morphisms may be verified over affine base
objects only: if the defining condition of
`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveFlat` holds for every datum whose base
object `a` is affine, then it holds for every datum.

The hypothesis `H` is the body of
`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveFlat` with the single extra assumption
`IsAffine ((BigFppfOver.toScheme B S hS).obj a)`; no other quantifier is restricted and no other
hypothesis is added.

This is `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_affineBase` with
étaleness of the covering morphism replaced by flatness together with local finite presentation,
and the proof is the same. The datum restricts over each affine open `V U` of `a`, the restricted
covering morphism `pullback.snd q (u U)` being again surjective, flat and locally of finite
presentation by stability under base change; the affine-base hypothesis makes
`X ×[Y] yoneda.obj (V U)` representable by Tag 03KC; the representing objects are open
subfunctors of `X ×[Y] yoneda.obj a` and are jointly locally surjective onto it; and
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveFlat_of_zariskiCover_of_mk_lt_cutoff`
glues them. The index type is the affine opens of `a`, of cardinality at most
`((BigFppfOver.toScheme B S hS).obj a).size < B.cutoff`, and the uniform bound on the pieces is
free because the covering morphism is a single flat morphism. This last point is exactly what the
covering-sieve predicate cannot reproduce. -/
theorem isEffectiveDescentAlongSurjectiveFlat_of_affineBase
    {P : MorphismProperty Scheme.{u}}
    [P.RespectsIso] [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    (H : ∀ ⦃X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (f : X ⟶ Y),
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) X →
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y →
      ∀ ⦃a c : BigFppfOver B S hS⦄ (h : yoneda.obj a ⟶ Y) (q : c ⟶ a),
        IsAffine ((BigFppfOver.toScheme B S hS).obj a) →
        Surjective ((BigFppfOver.toScheme B S hS).map q) →
        Flat ((BigFppfOver.toScheme B S hS).map q) →
        LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map q) →
        ∀ ⦃A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (m : A ⟶ X) (r : A ⟶ yoneda.obj c),
          IsPullback m r f (yoneda.map q ≫ h) →
          (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf r →
          (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f h)) :
    IsEffectiveDescentAlongSurjectiveFlat B S hS P := by
  refine isEffectiveDescentAlongSurjectiveFlat_of_zariskiCover_of_mk_lt_cutoff ?_
  intro X Y f hX hY a c h q hqs hqf hqp A m r sq hr
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
    -- the restriction of the covering morphism, still surjective, flat and of finite presentation
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
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback hsqsch hqf)
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback hsqsch hqp) _ _ hdat
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
      (hpb U), ?_⟩
  exact isLocallySurjective_sigmaDesc_of_openCover B S hS hu hucov hpb

/-! ### From the affine-base body of the covering-sieve predicate -/

/-- **The one-element covering a single surjective flat morphism generates reduces the
surjective-flat predicate to the affine-base body of the covering-sieve predicate.** If the
defining condition of `AlgebraicGeometry.Space.IsEffectiveDescentAlongCoveringSieve` holds for
every covering sieve of an affine base object, then morphisms with `P` descend effectively along
every surjective flat morphism of the site locally of finite presentation, over every base
object.

Two things happen here. The affine base is reached by
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveFlat_of_affineBase`, which is available
for a single morphism precisely because the glueing it performs is paid for by that morphism's
own size bound. And over the affine base the one-element covering `{q}` generates a covering
sieve, by
`AlgebraicGeometry.Space.sieve_generate_singleton_mem_topology_over_of_flat`; every arrow of that
sieve factors as `u ≫ q`, so the base change of `f` along it is a base change of the base change
along `q`, which carries `P` because the leg `r` of the datum does and the two are two pullbacks
of one cospan.

The analogous statement for the covering-sieve predicate itself is *not* available over a general
base object: see
`AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_of_affineBase_of_isRegular` and its
two companions, each of which charges for the same passage. -/
theorem isEffectiveDescentAlongSurjectiveFlat_of_coveringSieveBody_affineBase
    {P : MorphismProperty Scheme.{u}}
    [P.RespectsIso] [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    (H : ∀ ⦃X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (f : X ⟶ Y),
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) X →
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y →
      ∀ ⦃a : BigFppfOver B S hS⦄ (h : yoneda.obj a ⟶ Y) (T : Sieve a),
        IsAffine ((BigFppfOver.toScheme B S hS).obj a) →
        T ∈ BigFppfOver.topology B S hS a →
        (∀ ⦃b : BigFppfOver B S hS⦄ (q : b ⟶ a), T q →
          (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
            (pullback.snd f (yoneda.map q ≫ h))) →
        (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f h)) :
    IsEffectiveDescentAlongSurjectiveFlat B S hS P := by
  refine isEffectiveDescentAlongSurjectiveFlat_of_affineBase ?_
  intro X Y f hX hY a c h q ha hqs hqf hqp A m r sq hr
  have hbc := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (P.inverseImage (BigFppfOver.toScheme B S hS))
  have hri : MorphismProperty.RespectsIso
      ((P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf) := hbc.respectsIso
  -- the datum's leg transports to the chosen fibre product
  have hQ : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
      (pullback.snd f (yoneda.map q ≫ h)) := by
    rw [← (IsPullback.of_hasPullback f (yoneda.map q ≫ h)).isoIsPullback_hom_snd _ _ sq]
    exact MorphismProperty.RespectsIso.precomp _ _ _ hr
  refine H f hX hY h _ ha
    (sieve_generate_singleton_mem_topology_over_of_flat B S hS q hqs hqf hqp) ?_
  rintro b w ⟨Z, u, v, hv, hfac⟩
  cases hv
  have hsqR := (IsPullback.of_hasPullback f (yoneda.map u ≫ yoneda.map q ≫ h)).of_right'
    (IsPullback.of_hasPullback f (yoneda.map q ≫ h))
  have key : ∀ l : yoneda.obj b ⟶ Y, l = yoneda.map w ≫ h →
      (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f l) →
      (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
        (pullback.snd f (yoneda.map w ≫ h)) := by
    intro l hl
    subst hl
    exact id
  refine key _ ?_ (MorphismProperty.of_isPullback hsqR hQ)
  rw [← hfac, Functor.map_comp, Category.assoc]

/-! ### Stacks 02W8 at its own property along a single surjective flat chart -/

/-- **Effective descent along a single surjective flat morphism of the site locally of finite
presentation, for the separated locally quasi-finite morphisms locally of finite type**, over an
arbitrary base object, unconditionally.

This is the property of Stacks 02W8 descended along the one-element fppf coverings, which is the
shape Stacks 046J consumes: that tag reduces to a covering `{F → G}` by a single surjective, flat
morphism locally of finite presentation, not to a general covering sieve.

All five steps of Stacks 02W8 are discharged. Steps 1, 2 and 5 over an affine base, together with
steps 3 and 4, are
`AlgebraicGeometry.Space.coveringSieveBody_affineBase_isSeparated_inf_locallyQuasiFinite_inf_lft`;
the passage from an affine base object to an arbitrary one is
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveFlat_of_affineBase`, whose glueing is
paid for by the size bound of the single flat covering morphism.

Compare
`isEffectiveDescentAlongCoveringSieve_isSeparated_inf_lqf_inf_lft_of_isRegular` in this namespace,
the same property in the covering-sieve shape, which carries a regularity hypothesis on the
site's cutoff. That hypothesis is not an artefact: a covering sieve supplies no single surjective
morphism whose size bounds the glueing, and the property of Stacks 02W8 admits no size bound of
its own, `∐_{i < κ} Spec A ⟶ Spec A` having it for every `κ`. Restricting to one-element
coverings is exactly what removes the hypothesis. -/
@[stacks 02W8 "effective descent along a single surjective flat chart of the site"]
theorem isEffectiveDescentAlongSurjectiveFlat_isSeparated_inf_locallyQuasiFinite_inf_lft
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    IsEffectiveDescentAlongSurjectiveFlat B S hS
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType :
        MorphismProperty Scheme.{u}) := by
  have _hzar :=
    isSeparated_inf_locallyQuasiFinite_inf_locallyOfFiniteType_isZariskiLocalAtTarget.{u}
  have _hdesc :=
    isSeparated_inf_locallyQuasiFinite_inf_locallyOfFiniteType_descendsAlong_fppf.{u}
  have _hbc :=
    isSeparated_inf_locallyQuasiFinite_inf_locallyOfFiniteType_isStableUnderBaseChange.{u}
  have _hri : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType :
        MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact isEffectiveDescentAlongSurjectiveFlat_of_coveringSieveBody_affineBase
    coveringSieveBody_affineBase_isSeparated_inf_locallyQuasiFinite_inf_lft

/-! ### The representability half of Stacks 03I2 for a flat chart -/

/-- **Stacks 03I2**, the representability half, reduced to effective descent for `P` along the
surjective flat morphisms of the site locally of finite presentation. A morphism from a sheaf to
a sheaf on the big fppf site of `S` whose base change along one chart of its target which is
surjective, flat and locally of finite presentation after every represented base change is
representable with `P` is itself representable with `P`.

This is `AlgebraicGeometry.Space.presheaf_of_surjectiveEtaleChart` for a flat chart, and it is
the companion of
`AlgebraicGeometry.Space.presheaf_of_surjectiveFlatChart_of_coveringSieveDescent` with the
hypothesis weakened from the covering-sieve predicate to the one-element-covering predicate of
this file. That weakening is the whole point: the covering-sieve hypothesis has no unconditional
discharge at the property of Stacks 02W8, whereas this one does, by
`isEffectiveDescentAlongSurjectiveFlat_isSeparated_inf_locallyQuasiFinite_inf_lft` in this
namespace.

The chart produces the covering morphism by
`AlgebraicGeometry.Space.exists_flat_isPullback_presheaf_of_chart`, and the datum consumed is the
chosen fibre product itself. The target is not required to be an algebraic space: only its sheaf
condition and the chart are used. -/
theorem presheaf_of_surjectiveFlatChart {P : MorphismProperty Scheme.{u}} [P.RespectsIso]
    (hdesc : IsEffectiveDescentAlongSurjectiveFlat B S hS P)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y) {f : X ⟶ Y}
    {U : BigFppfOver B S hS} {g : yoneda.obj U ⟶ Y}
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) g)
    (hfl : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Flat.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) g)
    (hfp : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) g)
    (hV : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f g)) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf f := by
  have : MorphismProperty.RespectsIso (P.inverseImage (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.RespectsIso.inverseImage _ _
  refine (MorphismProperty.presheaf_iff_forall_presheaf_pullback_snd _ f).2 fun a h ↦ ?_
  obtain ⟨c, q, hqs, hqf, hqp, hQ⟩ :=
    exists_flat_isPullback_presheaf_of_chart hs hfl hfp hV a h
  exact hdesc f hX hY h q hqs hqf hqp _ _
    (IsPullback.of_hasPullback f (yoneda.map q ≫ h)) hQ

end AlgebraicGeometry.Space

end
