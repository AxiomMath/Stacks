module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescent
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FppfApplication.FiniteDomination
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits

/-!
# Effective descent for small étale sheaves along a surjective flat morphism

Let `f : X ⟶ Y` be a morphism of a big étale site which is surjective, flat and locally of finite
presentation, so that `{X ⟶ Y}` is an fppf covering. [Stacks, Tag 0GF2] says that descent of small
étale sheaves is effective along `f`, that is, the canonical functor from sheaves on the small
étale site of `Y` to descent data for `{X ⟶ Y}` is an equivalence of categories. This file proves
it granted the locality of effective descent on the base and the integral branch of the dévissage
of [Stacks, Tag 0GF1], both carried as explicit hypotheses.

## Main definitions

* `AlgebraicGeometry.SmallEtaleSheafDescentZariskiLocal` is the locality of effective descent on
  the base: descent is effective along a morphism admitting a section over each member of an open
  covering of its target.
* `AlgebraicGeometry.SmallEtaleSheafDescentIntegralDevissage` is the integral branch of the
  dévissage of [Stacks, Tag 0GF1].
* `AlgebraicGeometry.FiniteDominationBySections` is the conclusion of [Stacks, Tag 0CP0] for the
  one-member covering `{f}`, transported into the big étale site.

## Main results

* `AlgebraicGeometry.finiteDominationBySections_of_isAffine` and
  `AlgebraicGeometry.finiteDominationBySections_of_compactSpace` discharge
  [Stacks, Tag 0CP0] in the site, over an affine base and over a quasi-compact quasi-separated
  base respectively.
* `AlgebraicGeometry.smallEtaleSheafDescentFunctor_isEquivalence_pullback_snd_of_sections` and
  `AlgebraicGeometry.smallEtaleSheafDescentFunctor_isEquivalence_pullback_snd_fst_comp_of_sections`
  state that descent is effective along the base changes of `f` along `g` and along
  `pullback.fst g g ≫ g`.
* `AlgebraicGeometry.smallEtaleSheafDescentFunctor_isEquivalence_of_fppf` and
  `AlgebraicGeometry.smallEtaleSheafDescentFunctor_isEquivalence_of_fppf_of_compactSpace` are
  [Stacks, Tag 0GF2] granted `AlgebraicGeometry.SmallEtaleSheafDescentZariskiLocal` and
  `AlgebraicGeometry.SmallEtaleSheafDescentIntegralDevissage` as hypotheses, over an affine base
  and over a quasi-compact quasi-separated base respectively.

## References

* [Stacks Project, Tag 0GF2](https://stacks.math.columbia.edu/tag/0GF2)
* [Stacks Project, Tag 0GF1](https://stacks.math.columbia.edu/tag/0GF1)
* [Stacks Project, Tag 0GEZ](https://stacks.math.columbia.edu/tag/0GEZ)
* [Stacks Project, Tag 0GEY](https://stacks.math.columbia.edu/tag/0GEY)
* [Stacks Project, Tag 0CP0](https://stacks.math.columbia.edu/tag/0CP0)
-/


@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Effective descent for small étale sheaves is local on the base.** Descent is effective
along a morphism `h : X ⟶ Z` of a big étale site which admits a section over each member of an
open covering of `Z`. -/
public abbrev SmallEtaleSheafDescentZariskiLocal (B : BigEtaleSite.{u}) : Prop :=
  ∀ {X Z : B.Scheme} (h : X ⟶ Z) {K : Type u} (W : K → B.Scheme) (j : ∀ c, W c ⟶ Z),
    (∀ c, IsOpenImmersion (B.inclusion.map (j c))) →
    (∀ z, ∃ c, z ∈ Set.range (B.inclusion.map (j c))) →
    (∀ c, ∃ s : W c ⟶ X, s ≫ h = j c) →
    (smallEtaleSheafDescentFunctor B h).IsEquivalence

/-- **The integral branch of the dévissage of [Stacks, Tag 0GF1].** Descent of small étale
sheaves along a morphism is effective once it is effective after base change along a surjective
integral morphism `g` and after base change along `pullback.fst g g ≫ g`. -/
public abbrev SmallEtaleSheafDescentIntegralDevissage (B : BigEtaleSite.{u}) : Prop :=
  ∀ {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Z ⟶ Y),
    Surjective (B.inclusion.map g) → IsIntegralHom (B.inclusion.map g) →
    (smallEtaleSheafDescentFunctor B (pullback.snd f g)).IsEquivalence →
    (smallEtaleSheafDescentFunctor B (pullback.snd f (pullback.fst g g ≫ g))).IsEquivalence →
    (smallEtaleSheafDescentFunctor B f).IsEquivalence

/-- **The conclusion of [Stacks, Tag 0CP0] for the one-member covering `{f}`, inside a big étale
site.** There are a surjective integral morphism `g : Z ⟶ Y` of the site and an open covering of
`Z` each member of which maps to `Y` through `f`. -/
public abbrev FiniteDominationBySections (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) :
    Prop :=
  ∃ (Z : B.Scheme) (g : Z ⟶ Y), Surjective (B.inclusion.map g) ∧
    IsIntegralHom (B.inclusion.map g) ∧
    ∃ (K : Type u) (W : K → B.Scheme) (j : ∀ c, W c ⟶ Z),
      (∀ c, IsOpenImmersion (B.inclusion.map (j c))) ∧
      (∀ z, ∃ c, z ∈ Set.range (B.inclusion.map (j c))) ∧
      ∀ c, ∃ t : W c ⟶ X, j c ≫ g = t ≫ f

/-- A family of morphisms of a big étale site which is jointly surjective on points stays jointly
surjective after base change along any morphism of the site. -/
public theorem exists_mem_range_inclusion_map_pullback_snd (B : BigEtaleSite.{u})
    {Z T : B.Scheme} {K : Type u} {W : K → B.Scheme} (j : ∀ c, W c ⟶ Z) (p : T ⟶ Z)
    (hj : ∀ z, ∃ c, z ∈ Set.range (B.inclusion.map (j c))) (t : B.inclusion.obj T) :
    ∃ c, t ∈ Set.range (B.inclusion.map (pullback.snd (j c) p)) := by
  obtain ⟨c, w, hw⟩ := hj (B.inclusion.map p t)
  have := preservesPullbacks_bigEtaleSiteInclusion B
  have hpb : IsPullback (B.inclusion.map (pullback.fst (j c) p))
      (B.inclusion.map (pullback.snd (j c) p)) (B.inclusion.map (j c)) (B.inclusion.map p) :=
    B.inclusion.map_isPullback (IsPullback.of_hasPullback (j c) p)
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback w t hw
  refine ⟨c, hpb.isoPullback.inv z, ?_⟩
  rwa [← Scheme.Hom.comp_apply, hpb.isoPullback_inv_snd]

/-- Granted the locality of effective descent on the base, if each
member `W c` of an open covering of `Z` maps to `Y` through `f : X ⟶ Y` over `g : Z ⟶ Y`, then
descent of small étale sheaves along the projection `X ×_Y Z ⟶ Z` is effective. -/
public theorem smallEtaleSheafDescentFunctor_isEquivalence_pullback_snd_of_sections
    (B : BigEtaleSite.{u}) (zariskiLocal : SmallEtaleSheafDescentZariskiLocal B)
    {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Z ⟶ Y) {K : Type u} {W : K → B.Scheme}
    (j : ∀ c, W c ⟶ Z) (hopen : ∀ c, IsOpenImmersion (B.inclusion.map (j c)))
    (hcover : ∀ z, ∃ c, z ∈ Set.range (B.inclusion.map (j c)))
    (hfac : ∀ c, ∃ t : W c ⟶ X, j c ≫ g = t ≫ f) :
    (smallEtaleSheafDescentFunctor B (pullback.snd f g)).IsEquivalence :=
  zariskiLocal (pullback.snd f g) W j hopen hcover fun c ↦ by
    obtain ⟨t, ht⟩ := hfac c
    exact ⟨pullback.lift t (j c) ht.symm, pullback.lift_snd _ _ _⟩

/-- Granted the locality of effective descent on the base, if each
member `W c` of an open covering of `Z` maps to `Y` through `f : X ⟶ Y` over `g : Z ⟶ Y`, then
descent of small étale sheaves along the projection `X ×_Y (Z ×_Y Z) ⟶ Z ×_Y Z` is effective. -/
public theorem smallEtaleSheafDescentFunctor_isEquivalence_pullback_snd_fst_comp_of_sections
    (B : BigEtaleSite.{u}) (zariskiLocal : SmallEtaleSheafDescentZariskiLocal B)
    {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Z ⟶ Y) {K : Type u} {W : K → B.Scheme}
    (j : ∀ c, W c ⟶ Z) (hopen : ∀ c, IsOpenImmersion (B.inclusion.map (j c)))
    (hcover : ∀ z, ∃ c, z ∈ Set.range (B.inclusion.map (j c)))
    (hfac : ∀ c, ∃ t : W c ⟶ X, j c ≫ g = t ≫ f) :
    (smallEtaleSheafDescentFunctor B (pullback.snd f (pullback.fst g g ≫ g))).IsEquivalence := by
  refine smallEtaleSheafDescentFunctor_isEquivalence_pullback_snd_of_sections B zariskiLocal f
    (pullback.fst g g ≫ g) (fun c ↦ pullback.snd (j c) (pullback.fst g g)) (fun c ↦ ?_)
    (fun v ↦ ?_) (fun c ↦ ?_)
  · have := preservesPullbacks_bigEtaleSiteInclusion B
    exact MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (B.inclusion.map_isPullback (IsPullback.of_hasPullback (j c) (pullback.fst g g)))
      (hopen c)
  · exact exists_mem_range_inclusion_map_pullback_snd B j (pullback.fst g g) hcover v
  · obtain ⟨t, ht⟩ := hfac c
    refine ⟨pullback.fst (j c) (pullback.fst g g) ≫ t, ?_⟩
    rw [Category.assoc, ← ht, ← Category.assoc, ← Category.assoc, pullback.condition]

/-- A finite surjective morphism `g : Z ⟶ Y` of finite presentation together with an open covering
of `Z` each member of which maps to `Y` through `f` gives
`AlgebraicGeometry.FiniteDominationBySections B f`. -/
public theorem finiteDominationBySections_of_exists (B : BigEtaleSite.{u}) {X Y : B.Scheme}
    (f : X ⟶ Y)
    (h : ∃ (Z : Scheme.{u}) (g : Z ⟶ B.inclusion.obj Y), Surjective g ∧ IsFinite g ∧
      FinitePresentation g ∧ ∃ (K : Type u) (U : K → Z.Opens), (⨆ c, U c) = ⊤ ∧
        ∀ c, ∃ t : (U c).toScheme ⟶ B.inclusion.obj X,
          (U c).ι ≫ g = t ≫ B.inclusion.map f) :
    FiniteDominationBySections B f := by
  obtain ⟨Z, g, hgsurj, hgfin, hgfp, K, U, hUtop, hUfac⟩ := h
  have hZ : Z.size < B.cutoff :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact g Y.property
  refine ⟨B.obj Z hZ, ObjectProperty.homMk g, hgsurj, (inferInstance : IsIntegralHom g), K,
    fun c ↦ B.obj (U c).toScheme (Scheme.size_lt_of_isOpenImmersion (U c).ι hZ),
    fun c ↦ ObjectProperty.homMk (U c).ι,
    fun c ↦ (inferInstance : IsOpenImmersion (U c).ι), fun z ↦ ?_, fun c ↦ ?_⟩
  · have hz : z ∈ ⨆ c, U c := by rw [hUtop]; exact Opens.mem_top z
    obtain ⟨c, hc⟩ := Opens.mem_iSup.mp hz
    refine ⟨c, ?_⟩
    change z ∈ Set.range (U c).ι
    rwa [Scheme.Opens.range_ι]
  · obtain ⟨t, ht⟩ := hUfac c
    exact ⟨ObjectProperty.homMk t, ObjectProperty.hom_ext _ ht⟩

/-- The one-member family `{f}` of a surjective, flat, locally finitely presented morphism of a
big étale site is an fppf covering. -/
private theorem ofArrows_inclusion_map_mem_fppfPrecoverage (B : BigEtaleSite.{u}) {X Y : B.Scheme}
    (f : X ⟶ Y) [Surjective (B.inclusion.map f)] [Flat (B.inclusion.map f)]
    [LocallyOfFinitePresentation (B.inclusion.map f)] :
    Presieve.ofArrows (fun _ : PUnit.{1} ↦ B.inclusion.obj X) (fun _ ↦ B.inclusion.map f) ∈
      Scheme.fppfPrecoverage (B.inclusion.obj Y) := by
  rw [Presieve.ofArrows_pUnit]
  exact Scheme.Hom.singleton_mem_fppfPrecoverage (B.inclusion.map f)

/-- **[Stacks, Tag 0CP0] for the one-member fppf covering `{f}` over an affine base, inside a big
étale site.** -/
public theorem finiteDominationBySections_of_isAffine (B : BigEtaleSite.{u}) {X Y : B.Scheme}
    (f : X ⟶ Y) [IsAffine (B.inclusion.obj Y)] [Surjective (B.inclusion.map f)]
    [Flat (B.inclusion.map f)] [LocallyOfFinitePresentation (B.inclusion.map f)] :
    FiniteDominationBySections B f := by
  have hmem := ofArrows_inclusion_map_mem_fppfPrecoverage B f
  obtain ⟨Z, g, hgfin, hgsurj, hgfp, K, U, hUtop, hUfac⟩ :=
    exists_finite_surjective_openCover_factorization_of_isAffine
      (fun _ : PUnit.{1} ↦ B.inclusion.obj X) (fun _ ↦ B.inclusion.map f) hmem
  exact finiteDominationBySections_of_exists B f
    ⟨Z, g, hgsurj, hgfin, hgfp, K, U, hUtop, fun c ↦ (hUfac c).choose_spec⟩

/-- **[Stacks, Tag 0CP0] for the one-member fppf covering `{f}` over a quasi-compact
quasi-separated base, inside a big étale site.** -/
public theorem finiteDominationBySections_of_compactSpace (B : BigEtaleSite.{u}) {X Y : B.Scheme}
    (f : X ⟶ Y)
    [CompactSpace (B.inclusion.obj Y)] [QuasiSeparatedSpace (B.inclusion.obj Y)]
    [Surjective (B.inclusion.map f)] [Flat (B.inclusion.map f)]
    [LocallyOfFinitePresentation (B.inclusion.map f)] :
    FiniteDominationBySections B f := by
  have hmem := ofArrows_inclusion_map_mem_fppfPrecoverage B f
  obtain ⟨Z, g, hgfin, hgsurj, hgfp, K, U, hUtop, hUfac⟩ :=
    exists_finite_surjective_openCover_factorization_of_mem_fppfPrecoverage
      (fun _ : PUnit.{1} ↦ B.inclusion.obj X) (fun _ ↦ B.inclusion.map f) hmem
  exact finiteDominationBySections_of_exists B f
    ⟨Z, g, hgsurj, hgfin, hgfp, K, U, hUtop, fun c ↦ (hUfac c).choose_spec⟩

/-- **The reduction of [Stacks, Tag 0GF2] to its two dévissage inputs.** Granted the locality of
effective descent on the base and the integral branch of the dévissage of [Stacks, Tag 0GF1],
descent of small étale sheaves is effective along a morphism dominated, in the sense of
[Stacks, Tag 0CP0], by a surjective integral morphism whose source carries an open covering
factoring through it. -/
public theorem smallEtaleSheafDescentFunctor_isEquivalence_of_finiteDomination
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    (zariskiLocal : SmallEtaleSheafDescentZariskiLocal B)
    (devissage : SmallEtaleSheafDescentIntegralDevissage B)
    (hdom : FiniteDominationBySections B f) :
    (smallEtaleSheafDescentFunctor B f).IsEquivalence := by
  obtain ⟨Z, g, hgsurj, hgint, K, W, j, hopen, hcover, hfac⟩ := hdom
  exact devissage f g hgsurj hgint
    (smallEtaleSheafDescentFunctor_isEquivalence_pullback_snd_of_sections B zariskiLocal
      f g j hopen hcover hfac)
    (smallEtaleSheafDescentFunctor_isEquivalence_pullback_snd_fst_comp_of_sections B
      zariskiLocal f g j hopen hcover hfac)

/-- **Effective descent for small étale sheaves along an fppf covering of an affine base.** Let
`f : X ⟶ Y` be a morphism of a big étale site which is surjective, flat and locally of finite
presentation — so that `{X ⟶ Y}` is an fppf covering — and let `Y` be affine. Granted the locality
of effective descent on the base (`zariskiLocal`) and the integral branch of the dévissage of
[Stacks, Tag 0GF1] (`devissage`), the canonical functor from sheaves on the small étale site of `Y`
to descent data for `{X ⟶ Y}` is an equivalence of categories. -/
public theorem smallEtaleSheafDescentFunctor_isEquivalence_of_fppf (B : BigEtaleSite.{u})
    {X Y : B.Scheme} (f : X ⟶ Y) [IsAffine (B.inclusion.obj Y)]
    [Surjective (B.inclusion.map f)] [Flat (B.inclusion.map f)]
    [LocallyOfFinitePresentation (B.inclusion.map f)]
    (zariskiLocal : SmallEtaleSheafDescentZariskiLocal B)
    (devissage : SmallEtaleSheafDescentIntegralDevissage B) :
    (smallEtaleSheafDescentFunctor B f).IsEquivalence :=
  smallEtaleSheafDescentFunctor_isEquivalence_of_finiteDomination B f zariskiLocal devissage
    (finiteDominationBySections_of_isAffine B f)

/-- **Effective descent for small étale sheaves along an fppf covering of a quasi-compact
quasi-separated base.** Let `f : X ⟶ Y` be a morphism of a big étale site which is surjective, flat
and locally of finite presentation, and let `Y` be quasi-compact and quasi-separated. Granted the
locality of effective descent on the base (`zariskiLocal`) and the integral branch of the dévissage
of [Stacks, Tag 0GF1] (`devissage`), the canonical functor from sheaves on the small étale site of
`Y` to descent data for `{X ⟶ Y}` is an equivalence of categories. -/
public theorem smallEtaleSheafDescentFunctor_isEquivalence_of_fppf_of_compactSpace
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [CompactSpace (B.inclusion.obj Y)] [QuasiSeparatedSpace (B.inclusion.obj Y)]
    [Surjective (B.inclusion.map f)] [Flat (B.inclusion.map f)]
    [LocallyOfFinitePresentation (B.inclusion.map f)]
    (zariskiLocal : SmallEtaleSheafDescentZariskiLocal B)
    (devissage : SmallEtaleSheafDescentIntegralDevissage B) :
    (smallEtaleSheafDescentFunctor B f).IsEquivalence :=
  smallEtaleSheafDescentFunctor_isEquivalence_of_finiteDomination B f zariskiLocal devissage
    (finiteDominationBySections_of_compactSpace B f)

end AlgebraicGeometry

end
