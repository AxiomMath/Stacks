module

public import StacksCore.CategoryTheory.Pullback
public import StacksFrontier.AlgebraicGeometry.Size.AtlasOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveStepOne

/-!
# The glueing step of Stacks 02W8 under a size bound instead of a cofinality bound

Tag 01JJ for the big fppf site of `S` is proved in
`StacksFrontier.AlgebraicGeometry.Spaces.ZariskiGluingCover` in two shapes which differ only in the
cardinal hypothesis put on the covering.
`AlgebraicGeometry.isRepresentable_of_zariskiCover_of_lt_cof` asks
`#I < Cardinal.ord B.cutoff |>.cof`; the glueing it calls,
`AlgebraicGeometry.isRepresentable_of_openCharts`, asks instead the two bounds `#I < B.cutoff` and
a uniform `μ < B.cutoff` on the sizes of the charts. The second pair is the right hypothesis for a
covering produced by a geometric construction, and the cofinality form cannot replace it: the
cutoff of a big fppf site is only `Cardinal.IsStrongPrelimit`
(`AlgebraicGeometry.BigFppfSite.cutoff_isStrongPrelimit`), so nothing bounds its cofinality, while
a covering indexed by the affine opens of a chart `V` has index cardinality at most `V.size` by
`AlgebraicGeometry.Scheme.mk_affineOpens_le_size` and pieces of uniformly bounded size. This file
restates the glueing step and its three descent corollaries on that pair of bounds, leaving the
cofinality forms untouched.

For the surjective-étale predicate the uniform bound is not even a hypothesis. A descent datum
along a surjective étale `q : c ⟶ a` exhibits the descended sheaf `X ×[Y] yoneda.obj a` as
carrying a surjective étale chart from a *representable* presheaf — the datum's total space `A`
is representable because `A ⟶ yoneda.obj c` is relatively representable and `yoneda.obj c` is
representable — and
`AlgebraicGeometry.Space.size_le_of_isOpenImmersion_of_atlas` bounds every representable open
subspace of a presheaf carrying a surjective étale chart by `max (2 ^ #U) (2 ^ U.size)` for the
chart's source `U`, a bound which mentions only `U` and lies below the cutoff by strong
prelimitness. So for that predicate the glueing step needs nothing about the covering beyond
`#ι < B.cutoff`.

## Main results

* `AlgebraicGeometry.isRepresentable_of_zariskiCover_of_size_le`: **Tag 01JJ for the big fppf site
  of `S` under a uniform size bound.** A sheaf for the fppf topology carrying a Zariski covering by
  representable open subfunctors indexed by a type of cardinality below the cutoff, whose charts
  have size uniformly below the cutoff, is representable. This is the companion of
  `AlgebraicGeometry.isRepresentable_of_zariskiCover_of_lt_cof`, with no hypothesis on the
  cofinality of the cutoff and no nonemptiness hypothesis on the index type.
* `AlgebraicGeometry.Space.exists_size_bound_of_descentDatum`: **the uniform bound is free for a
  descent datum along a surjective étale morphism.** There is one cardinal below the cutoff
  bounding the size of *every* object of the site representing an open subfunctor of the descended
  sheaf.
* `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_zariskiCover_of_mk_lt_cutoff`:
  **the glueing step of Stacks 02W8 with no size hypothesis on the pieces of the covering.** It
  implies `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_zariskiCover`, since
  the cofinality of a cardinal is at most that cardinal.
* `isEffectiveDescentAlongCoveringSieve_of_zariskiCover_of_size_le` and
  `isEffectiveDescentAlongCoveringSieve_of_zariskiCover_of_isCovering_of_size_le`, both in the
  `AlgebraicGeometry.Space` namespace: the covering-sieve predicate under the same pair of
  bounds, in the two shapes of
  `StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveDescent` and
  `StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveStepOne`.
* `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_zariskiCover_of_size_le`: the
  surjective-étale predicate under the same pair of bounds, kept because it is the form the
  covering-sieve statements share and because it does not pay for the representability of the
  datum's total space.

## Implementation notes

*Why the uniform bound is not the cofinality bound in disguise.* The two hypotheses are
incomparable, and neither is a restatement of the other. `#ι < Cardinal.ord B.cutoff |>.cof`
implies `#ι < B.cutoff`, because the cofinality of an ordinal is at most its cardinality, and it
also implies a bound on the supremum of fewer than `cof` sizes, which is how
`AlgebraicGeometry.BigFppfSite.contains_of_openCover` uses it — but it is a condition on the index
type alone, so it is unobtainable for an index type as large as the affine opens of a chart when
the cutoff has small cofinality, which a strong prelimit may well have. The pair taken here
bounds the index type only by the cutoff itself, and asks in exchange for one cardinal bounding
all the pieces; a covering indexed by the affine opens of an object `V` of the site satisfies the
first half by `AlgebraicGeometry.Scheme.mk_affineOpens_le_size` together with `V.size < B.cutoff`,
exactly the idiom already used in
`AlgebraicGeometry.Space.exists_representing_over_of_holdsOnAffineBaseChange_of_isAlgebraicSpace`.

*What the covering-sieve statements still owe.* They cannot discharge the uniform bound the way
the surjective-étale one does, because a covering sieve hands over no single surjective morphism:
by `AlgebraicGeometry.BigFppfSite.exists_mem_of_mem_topology` it has, through each point, an arrow
which is flat and locally of finite presentation, and joint surjectivity is a property of the
chosen *family*, whose index type lives one universe up and whose coproduct in the site is exactly
what the cofinality of the cutoff would be needed for. So for those two the size bound is a real
hypothesis, to be supplied by the construction producing the covering.

## References

* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
* [Stacks Project, Tag 0AP4](https://stacks.math.columbia.edu/tag/0AP4)
* [Stacks Project, Tag 03KC](https://stacks.math.columbia.edu/tag/03KC)
-/

@[expose] public section

open Cardinal CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Tag 01JJ under a uniform size bound -/

section Gluing

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Tag 01JJ for the big fppf site of `S` under a uniform size bound.** A sheaf `F` for the fppf
topology of the big fppf category over `S` which admits a Zariski covering by representable open
subfunctors is representable, provided the index type has cardinality below the site's cutoff and
the charts have size uniformly below it.

This is the companion of `AlgebraicGeometry.isRepresentable_of_zariskiCover_of_lt_cof`, which is
kept: the two hypotheses are incomparable, and this one is the one a geometric construction
supplies, since a covering indexed by the affine opens of an object `V` of the site has index
cardinality at most `V.size < B.cutoff` by `AlgebraicGeometry.Scheme.mk_affineOpens_le_size` and
pieces which are open subschemes of a bounded object. The cofinality of the cutoff plays no part,
which matters because `AlgebraicGeometry.BigFppfSite.cutoff_isStrongPrelimit` is all that is known
about it.

Nothing is proved here that `AlgebraicGeometry.isRepresentable_of_openCharts` does not already
prove; this packages it with the sheaf presented as a presheaf together with its sheaf condition,
and the open immersions spelled with `AlgebraicGeometry.Space.IsOpenImmersion`, which is the shape
the descent predicates below consume. In particular the index type need not be nonempty: the
glueing of the empty family is the empty scheme, whose size is `ℵ₀`. -/
theorem isRepresentable_of_zariskiCover_of_size_le
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    {I : Type u} (hI : #I < B.cutoff) {μ : Cardinal.{u}} (hμ : μ < B.cutoff)
    (X : I → BigFppfOver B S hS)
    (hX : ∀ i, ((BigFppfOver.toScheme B S hS).obj (X i)).size ≤ μ)
    (f : ∀ i, yoneda.obj (X i) ⟶ F)
    (hf : ∀ i, Space.IsOpenImmersion B S hS (f i))
    (hsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc f)) :
    F.IsRepresentable :=
  isRepresentable_of_openCharts ⟨F, hF⟩ X f hf hI hμ hX hsurj

end Gluing

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The second projection of the fibre product of a morphism of presheaves with a representable
one is relatively representable as soon as that fibre product is representable.

This is the step by which the three glueing statements below turn representability of
`X ×[Y] yoneda.obj a` into the relative representability which
`AlgebraicGeometry.Space.presheaf_of_coveringSieve_of_descendsAlong` and
`AlgebraicGeometry.Space.presheaf_of_surjectiveEtaleChart_of_descendsAlong` ask for: the
projection factors as the inverse of the representing isomorphism followed by a morphism in the
image of `CategoryTheory.yoneda`, and both factors are relatively representable. -/
theorem relativelyRepresentable_pullback_snd
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) {a : BigFppfOver B S hS}
    (h : yoneda.obj a ⟶ Y) (hrep : (pullback f h).IsRepresentable) :
    yoneda.relativelyRepresentable (pullback.snd f h) := by
  set e := (pullback f h).reprW with he
  set p := yoneda.preimage (e.hom ≫ pullback.snd f h) with hp
  have hmap : yoneda.map p = e.hom ≫ pullback.snd f h := by rw [hp, Functor.map_preimage]
  have hfac : pullback.snd f h = e.inv ≫ yoneda.map p := by
    rw [hmap, Iso.inv_hom_id_assoc]
  rw [hfac]
  exact MorphismProperty.comp_mem _ _ _ (Functor.relativelyRepresentable.of_isIso _ _)
    (Functor.relativelyRepresentable.map yoneda p)

/-- A property of schemes which holds for `q` holds for `yoneda.map q` as a morphism of presheaves
on the big fppf site. -/
private theorem presheaf_inverseImage_yoneda_map_of {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange]
    {a c : BigFppfOver B S hS} (q : c ⟶ a) (hq : P ((BigFppfOver.toScheme B S hS).map q)) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map q) :=
  (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ q).2 hq

/-- The glueing of a Zariski covering of `pullback f h` by representable open subfunctors under a
uniform size bound makes the second projection relatively representable. -/
private theorem relativelyRepresentable_pullback_snd_of_zariskiCover
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) {a : BigFppfOver B S hS}
    (h : yoneda.obj a ⟶ Y) (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    {ι : Type u} {μ : Cardinal.{u}} (hι : #ι < B.cutoff) (hμ : μ < B.cutoff)
    (W : ι → BigFppfOver B S hS) (k : ∀ i, yoneda.obj (W i) ⟶ pullback f h)
    (hW : ∀ i, ((BigFppfOver.toScheme B S hS).obj (W i)).size ≤ μ)
    (hk : ∀ i, IsOpenImmersion B S hS (k i))
    (hksurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc k)) :
    yoneda.relativelyRepresentable (pullback.snd f h) :=
  relativelyRepresentable_pullback_snd f h
    (isRepresentable_of_zariskiCover_of_size_le B S hS
      (BigFppfOver.isSheaf_pullback_yoneda_obj f h hX hY) hι hμ W hW k hk hksurj)

/-! ### The covering-sieve predicate under a uniform size bound -/

/-- **Descent, Lemma 35.35.13 in the shape of
`AlgebraicGeometry.Space.IsEffectiveDescentAlongCoveringSieve`, under a uniform size bound.**
Effective descent along the covering sieves of the big fppf site of `S` follows from producing,
for each descent datum along a covering sieve, a Zariski covering of the descended sheaf by
representable open subfunctors whose index type has cardinality below the site's cutoff and whose
pieces have size uniformly below it.

This is `AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_of_zariskiCover` with the
cofinality bound on the index type replaced by the pair of bounds consumed by
`AlgebraicGeometry.isRepresentable_of_zariskiCover_of_size_le`. The two forms are kept side by
side: neither hypothesis implies the other, and this is the one a covering indexed by the affine
opens of a chart can meet. The nonemptiness hypothesis of the cofinality form is dropped, since
the glueing does not need it. -/
theorem isEffectiveDescentAlongCoveringSieve_of_zariskiCover_of_size_le
    {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtTarget P]
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    (H : ∀ ⦃X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (f : X ⟶ Y),
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) X →
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y →
      ∀ ⦃a : BigFppfOver B S hS⦄ (h : yoneda.obj a ⟶ Y) (T : Sieve a),
        T ∈ BigFppfOver.topology B S hS a →
        (∀ ⦃b : BigFppfOver B S hS⦄ (q : b ⟶ a), T q →
          (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
            (pullback.snd f (yoneda.map q ≫ h))) →
        ∃ (ι : Type u) (μ : Cardinal.{u}), #ι < B.cutoff ∧ μ < B.cutoff ∧
          ∃ (W : ι → BigFppfOver B S hS) (k : ∀ i, yoneda.obj (W i) ⟶ pullback f h),
            (∀ i, ((BigFppfOver.toScheme B S hS).obj (W i)).size ≤ μ) ∧
            (∀ i, IsOpenImmersion B S hS (k i)) ∧
              Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc k)) :
    IsEffectiveDescentAlongCoveringSieve B S hS P := by
  intro X Y f hX hY a h T hTmem hall
  obtain ⟨ι, μ, hι, hμ, W, k, hW, hk, hksurj⟩ := H f hX hY h T hTmem hall
  exact presheaf_of_coveringSieve_of_descendsAlong h
    (relativelyRepresentable_pullback_snd_of_zariskiCover f h hX hY hι hμ W k hW hk hksurj)
    hTmem hall

/-- **What is left of Stacks 02W8 for the covering sieves after step 1 and step 5, under a uniform
size bound.** This is
`AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_of_zariskiCover_of_isCovering` with
the cofinality bound replaced by the pair of bounds of
`AlgebraicGeometry.isRepresentable_of_zariskiCover_of_size_le`: the covering sieve is replaced by a
chosen covering family by step 1, through
`AlgebraicGeometry.BigFppfOver.exists_isCovering_of_mem_topology`, and the glueing is step 5.

It is the form in which the remaining steps of Stacks 02W8 are to be proved for this predicate.
The index-type half of the size hypothesis is free for the covering of step 2, whose index type is
the affine opens of the chart; the uniform bound on the pieces is not, and cannot be discharged
here, because a covering sieve supplies no single surjective morphism to play the part the
surjective étale chart plays in
`Space.isEffectiveDescentAlongSurjectiveEtale_of_zariskiCover_of_mk_lt_cutoff`. -/
theorem isEffectiveDescentAlongCoveringSieve_of_zariskiCover_of_isCovering_of_size_le
    {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtTarget P]
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    (H : ∀ ⦃X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (f : X ⟶ Y),
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) X →
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y →
      ∀ ⦃a : BigFppfOver B S hS⦄ (h : yoneda.obj a ⟶ Y)
        (E : PreZeroHypercover.{u + 1} a), BigFppfOver.IsCovering B S hS ⟨a, E⟩ →
        (∀ i, (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
          (pullback.snd f (yoneda.map (E.f i) ≫ h))) →
        ∃ (ι : Type u) (μ : Cardinal.{u}), #ι < B.cutoff ∧ μ < B.cutoff ∧
          ∃ (W : ι → BigFppfOver B S hS) (k : ∀ i, yoneda.obj (W i) ⟶ pullback f h),
            (∀ i, ((BigFppfOver.toScheme B S hS).obj (W i)).size ≤ μ) ∧
            (∀ i, IsOpenImmersion B S hS (k i)) ∧
              Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc k)) :
    IsEffectiveDescentAlongCoveringSieve B S hS P := by
  refine isEffectiveDescentAlongCoveringSieve_of_zariskiCover_of_size_le ?_
  intro X Y f hX hY a h T hTmem hall
  obtain ⟨E, hE, hET⟩ := BigFppfOver.exists_isCovering_of_mem_topology B S hS hTmem
  exact H f hX hY h E hE fun i ↦ hall (E.f i) (hET i)

/-! ### The surjective-étale predicate: the uniform bound is free -/

/-- **Descent, Lemma 35.35.13 in the shape of
`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale`, under a uniform size bound.**
This is `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_zariskiCover` with the
cofinality bound on the index type replaced by the pair of bounds consumed by
`AlgebraicGeometry.isRepresentable_of_zariskiCover_of_size_le`.

For this predicate the uniform bound is a consequence of the other hypotheses, by
`AlgebraicGeometry.Space.exists_size_bound_of_descentDatum`; the statement which exploits that is
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_zariskiCover_of_mk_lt_cutoff`,
and it is what a consumer should use. This intermediate form is kept because it is the shape the
covering-sieve statements above share, and because it asks nothing of the datum beyond what the
predicate already carries. -/
theorem isEffectiveDescentAlongSurjectiveEtale_of_zariskiCover_of_size_le
    {P : MorphismProperty Scheme.{u}}
    [P.RespectsIso] [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    (H : ∀ ⦃X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (f : X ⟶ Y),
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) X →
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y →
      ∀ ⦃a c : BigFppfOver B S hS⦄ (h : yoneda.obj a ⟶ Y) (q : c ⟶ a),
        Surjective ((BigFppfOver.toScheme B S hS).map q) →
        Etale ((BigFppfOver.toScheme B S hS).map q) →
        ∀ ⦃A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (m : A ⟶ X) (r : A ⟶ yoneda.obj c),
          IsPullback m r f (yoneda.map q ≫ h) →
          (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf r →
          ∃ (ι : Type u) (μ : Cardinal.{u}), #ι < B.cutoff ∧ μ < B.cutoff ∧
            ∃ (W : ι → BigFppfOver B S hS) (k : ∀ i, yoneda.obj (W i) ⟶ pullback f h),
              (∀ i, ((BigFppfOver.toScheme B S hS).obj (W i)).size ≤ μ) ∧
              (∀ i, IsOpenImmersion B S hS (k i)) ∧
                Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc k)) :
    IsEffectiveDescentAlongSurjectiveEtale B S hS P := by
  intro X Y f hX hY a c h q hqs hqe A m r sq hr
  obtain ⟨ι, μ, hι, hμ, W, k, hW, hk, hksurj⟩ := H f hX hY h q hqs hqe m r sq hr
  exact presheaf_of_surjectiveEtaleChart_of_descendsAlong
    (relativelyRepresentable_pullback_snd_of_zariskiCover f h hX hY hι hμ W k hW hk hksurj)
    (presheaf_inverseImage_yoneda_map_of q hqs) (presheaf_inverseImage_yoneda_map_of q hqe)
    (sq.of_right' (IsPullback.of_hasPullback f h)) hr

/-- **A descent datum along a surjective étale morphism bounds the size of every representable
open subspace of the sheaf it descends to, uniformly.**

Let `f : X ⟶ Y` be a morphism of presheaves on the big fppf site of `S`, let
`h : yoneda.obj a ⟶ Y`, let `q : c ⟶ a` be surjective and étale on underlying schemes and let
`(m, r)` present a presheaf `A` as `X ×[Y] yoneda.obj c`, with `r` relatively representable — the
data of `AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale`. Then there is a single
cardinal below the site's cutoff bounding the size of every object `V` of the site admitting an
open immersion `yoneda.obj V ⟶ X ×[Y] yoneda.obj a`.

Three facts combine. The total space `A` is representable, by Tag 03KC
(`CategoryTheory.Functor.isRepresentable_of_relativelyRepresentable_of_target_isRepresentable`)
applied to `r` over the representable `yoneda.obj c`; so its representing object `U` is an object
of the site, of size below the cutoff. The morphism `A ⟶ X ×[Y] yoneda.obj a` cut out by the datum
is a base change of `yoneda.map q`, hence surjective and étale after every represented base change,
so `X ×[Y] yoneda.obj a` carries a surjective étale chart out of `yoneda.obj U`. And
`AlgebraicGeometry.Space.size_le_of_isOpenImmersion_of_atlas` bounds every representable open
subspace of a presheaf carrying such a chart by `max (2 ^ #U) (2 ^ U.size)`, which mentions only
`U` and is below the cutoff by `AlgebraicGeometry.BigFppfSite.cutoff_isStrongPrelimit`.

Nothing here needs `X ×[Y] yoneda.obj a` to be a sheaf, an algebraic space, or representable —
which is the point, since its representability is what the glueing step is for. -/
theorem exists_size_bound_of_descentDatum
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    {a c : BigFppfOver B S hS} (h : yoneda.obj a ⟶ Y) (q : c ⟶ a)
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqe : Etale ((BigFppfOver.toScheme B S hS).map q))
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (m : A ⟶ X) (r : A ⟶ yoneda.obj c)
    (sq : IsPullback m r f (yoneda.map q ≫ h))
    (hr : yoneda.relativelyRepresentable r) :
    ∃ μ : Cardinal.{u}, μ < B.cutoff ∧ ∀ (V : BigFppfOver B S hS)
      (k : yoneda.obj V ⟶ pullback f h), IsOpenImmersion B S hS k →
        ((BigFppfOver.toScheme B S hS).obj V).size ≤ μ := by
  have _ : A.IsRepresentable :=
    Functor.isRepresentable_of_relativelyRepresentable_of_target_isRepresentable r hr
  -- the morphism from the datum's total space to the descended sheaf, and its Cartesian square
  have sq₂ := sq.of_right' (IsPullback.of_hasPullback f h)
  have sq₃ : IsPullback
      (A.reprW.hom ≫ (IsPullback.of_hasPullback f h).lift m (r ≫ yoneda.map q)
        (by rw [sq.w, Category.assoc]))
      (A.reprW.hom ≫ r) (pullback.snd f h) (yoneda.map q) :=
    sq₂.of_iso' A.reprW (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp)
      (by simp)
  have _ := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
  have _ := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
  refine ⟨max (2 ^ #((BigFppfOver.toScheme B S hS).obj A.reprX : Type u))
      (2 ^ ((BigFppfOver.toScheme B S hS).obj A.reprX).size),
    Scheme.max_two_pow_mk_two_pow_size_lt_of_isStrongPrelimit B.cutoff_isStrongPrelimit
      A.reprX.left.property, fun V k hk => ?_⟩
  exact size_le_of_isOpenImmersion_of_atlas B S hS
    (MorphismProperty.of_isPullback sq₃.flip (presheaf_inverseImage_yoneda_map_of q hqs))
    (MorphismProperty.of_isPullback sq₃.flip (presheaf_inverseImage_yoneda_map_of q hqe)) hk

/-- **The glueing step of Stacks 02W8 for the surjective-étale predicate, with no size hypothesis
on the pieces of the covering.** Effective descent along the surjective étale morphisms of the big
fppf site of `S` follows from producing, for each descent datum, a Zariski covering of the
descended sheaf by representable open subfunctors whose index type has cardinality below the
site's cutoff — and nothing else.

The uniform bound which
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_zariskiCover_of_size_le` asks
for is supplied by `AlgebraicGeometry.Space.exists_size_bound_of_descentDatum` from the datum
itself.

This implies `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_zariskiCover`,
because the cofinality of `Cardinal.ord B.cutoff` is at most `B.cutoff`; and the remaining
hypothesis is met by the covering of step 2 of Stacks 02W8, which is indexed by the affine opens
of the chart and so has index cardinality at most the chart's size, below the cutoff by
`AlgebraicGeometry.Scheme.mk_affineOpens_le_size`. No cofinality of the cutoff is used anywhere,
which is what makes the statement usable: `AlgebraicGeometry.BigFppfSite.cutoff_isStrongPrelimit`
is all that is known of the cutoff. -/
theorem isEffectiveDescentAlongSurjectiveEtale_of_zariskiCover_of_mk_lt_cutoff
    {P : MorphismProperty Scheme.{u}}
    [P.RespectsIso] [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    (H : ∀ ⦃X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (f : X ⟶ Y),
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) X →
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y →
      ∀ ⦃a c : BigFppfOver B S hS⦄ (h : yoneda.obj a ⟶ Y) (q : c ⟶ a),
        Surjective ((BigFppfOver.toScheme B S hS).map q) →
        Etale ((BigFppfOver.toScheme B S hS).map q) →
        ∀ ⦃A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (m : A ⟶ X) (r : A ⟶ yoneda.obj c),
          IsPullback m r f (yoneda.map q ≫ h) →
          (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf r →
          ∃ ι : Type u, #ι < B.cutoff ∧
            ∃ (W : ι → BigFppfOver B S hS) (k : ∀ i, yoneda.obj (W i) ⟶ pullback f h),
              (∀ i, IsOpenImmersion B S hS (k i)) ∧
                Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc k)) :
    IsEffectiveDescentAlongSurjectiveEtale B S hS P := by
  refine isEffectiveDescentAlongSurjectiveEtale_of_zariskiCover_of_size_le ?_
  intro X Y f hX hY a c h q hqs hqe A m r sq hr
  obtain ⟨μ, hμ, hbound⟩ := exists_size_bound_of_descentDatum f h q hqs hqe m r sq hr.rep
  obtain ⟨ι, hι, W, k, hk, hksurj⟩ := H f hX hY h q hqs hqe m r sq hr
  exact ⟨ι, μ, hι, hμ, W, k, fun i => hbound (W i) (k i) (hk i), hk, hksurj⟩

end Space

end AlgebraicGeometry

end
