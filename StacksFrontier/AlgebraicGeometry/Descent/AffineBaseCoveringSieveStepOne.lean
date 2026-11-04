module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineBaseCoveringSieveDescent

/-!
# Replacing a covering sieve over an affine base by one surjective flat morphism of affines

Over an *affine* base object of the big fppf site, a descent problem along a covering sieve is
reduced to one along a single surjective, flat, quasi-compact morphism of finite presentation
between affine objects, as in step 1 of Stacks 02W8 and Descent, Lemma 02W3. The base is
quasi-compact, so finitely many arrows of the sieve with affine source have images covering it,
and their coproduct is an object of the site.

## Main results

* `AlgebraicGeometry.Space.exists_isPullback_restrict_of_presheaf`: the restriction step of a
  descent problem, isolated from any hypothesis on the base or on the covering. If the base
  change of `f : X ⟶ Y` along `yoneda.map u ≫ h` is representable with `P`, then the
  representing object is an open subfunctor of `X ×[Y] yoneda.obj a` over `u`, Cartesianly.
* `AlgebraicGeometry.BigFppfOver.exists_affine_mem_of_mem_topology`: through every point of the
  base of a covering sieve there passes an arrow of the sieve with *affine* source whose
  underlying morphism of schemes is flat and locally of finite presentation.
* `AlgebraicGeometry.Space.coveringSieveBody_affineBase_of_affineFlatSource`: **step 1 of
  Descent, Lemma 02W3 for the covering sieves, over an affine base.** If the body of
  `AlgebraicGeometry.Space.IsEffectiveDescentAlongCoveringSieve` holds for every problem whose
  base object is affine and whose covering sieve has been replaced by a *single* morphism `p`
  which is surjective, flat, locally of finite presentation and quasi-compact with affine
  source, then it holds for every problem over an affine base.

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

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The restriction step, with no hypothesis on the base -/

/-- **The restriction step of a descent problem.** Let `f : X ⟶ Y` be a morphism of presheaves on
the big fppf site of `S`, let `h : yoneda.obj a ⟶ Y` and let `u : V ⟶ a` be a morphism of the
site. If the base change of `f` along `yoneda.map u ≫ h` is representable with `P`, then there
are an object `W` of the site, a morphism `pr : W ⟶ V` with `P` and a morphism
`k : yoneda.obj W ⟶ X ×[Y] yoneda.obj a` making `yoneda.obj W` the base change of
`X ×[Y] yoneda.obj a ⟶ yoneda.obj a` along `yoneda.map u`. -/
theorem exists_isPullback_restrict_of_presheaf {P : MorphismProperty Scheme.{u}}
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    {a : BigFppfOver B S hS} (h : yoneda.obj a ⟶ Y)
    {V : BigFppfOver B S hS} (u : V ⟶ a)
    (hH : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
      (pullback.snd f (yoneda.map u ≫ h))) :
    ∃ (W : BigFppfOver B S hS) (pr : W ⟶ V) (k : yoneda.obj W ⟶ pullback f h),
      IsPullback k (yoneda.map pr) (pullback.snd f h) (yoneda.map u) ∧
        P ((BigFppfOver.toScheme B S hS).map pr) := by
  have _ : (pullback f (yoneda.map u ≫ h)).IsRepresentable :=
    Functor.isRepresentable_of_relativelyRepresentable_of_target_isRepresentable
      (pullback.snd f (yoneda.map u ≫ h)) hH.rep
  set e := (pullback f (yoneda.map u ≫ h)).reprW with he
  have hmap : yoneda.map (yoneda.preimage (e.hom ≫ pullback.snd f (yoneda.map u ≫ h))) =
      e.hom ≫ pullback.snd f (yoneda.map u ≫ h) := Functor.map_preimage _ _
  have hsqR := (IsPullback.of_hasPullback f (yoneda.map u ≫ h)).of_right'
    (IsPullback.of_hasPullback f h)
  refine ⟨_, yoneda.preimage (e.hom ≫ pullback.snd f (yoneda.map u ≫ h)),
    e.hom ≫ (IsPullback.of_hasPullback f h).lift
      (pullback.fst f (yoneda.map u ≫ h))
      (pullback.snd f (yoneda.map u ≫ h) ≫ yoneda.map u)
      (by rw [(IsPullback.of_hasPullback f (yoneda.map u ≫ h)).w, Category.assoc]), ?_, ?_⟩
  · rw [hmap]
    exact hsqR.of_iso' e (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp)
      (by simp)
  · exact hH.property (𝟙 (yoneda.obj V)) e.hom _
      (IsPullback.of_horiz_isIso ⟨by rw [hmap, Category.comp_id]⟩)

/-! ### Refining a covering sieve over an affine base to a single morphism of affines -/

/-- **An arrow of a covering sieve through a given point, with affine source.** Through every
point of the base of a covering sieve of the big fppf site of `S` there passes an arrow of the
sieve whose source is affine and whose underlying morphism of schemes is flat and locally of
finite presentation. -/
theorem _root_.AlgebraicGeometry.BigFppfOver.exists_affine_mem_of_mem_topology
    (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {a : BigFppfOver B S hS} {T : Sieve a}
    (hT : T ∈ BigFppfOver.topology B S hS a) (x : (BigFppfOver.toScheme B S hS).obj a) :
    ∃ (V : BigFppfOver B S hS) (v : V ⟶ a),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧ T v ∧
        Flat ((BigFppfOver.toScheme B S hS).map v) ∧
        LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map v) ∧
        x ∈ Set.range ((BigFppfOver.toScheme B S hS).map v).base := by
  obtain ⟨c, q, hqT, hqf, hqp, y, hy⟩ := BigFppfOver.exists_mem_of_mem_topology B S hS hT x
  have hytop : y ∈ (⊤ : ((BigFppfOver.toScheme B S hS).obj c).Opens) := trivial
  rw [← iSup_affineOpens_eq_top] at hytop
  obtain ⟨Uo, hUo⟩ := TopologicalSpace.Opens.mem_iSup.1 hytop
  obtain ⟨V, u, hu, hurange, hVaff⟩ := BigFppfOver.exists_affineOpen_restrict B S hS c Uo
  have _ := hu
  have _ := hqf
  have _ := hqp
  refine ⟨V, u ≫ q, hVaff, T.downward_closed hqT u, ?_, ?_, ?_⟩
  · rw [Functor.map_comp]; infer_instance
  · rw [Functor.map_comp]; infer_instance
  · have hyu : y ∈ Set.range ((BigFppfOver.toScheme B S hS).map u).base := by
      rw [hurange]; exact hUo
    obtain ⟨z, hz⟩ := hyu
    exact ⟨z, by rw [Functor.map_comp, Scheme.Hom.comp_apply, hz, hy]⟩

/-- **Step 1 of Descent, Lemma 02W3 for the covering sieves, over an affine base.** The body of
`AlgebraicGeometry.Space.IsEffectiveDescentAlongCoveringSieve` over an affine base object
follows from the same statement with the covering sieve replaced by a *single* morphism `p`
which is surjective, flat, locally of finite presentation and quasi-compact and whose source is
affine. -/
theorem coveringSieveBody_affineBase_of_affineFlatSource {P : MorphismProperty Scheme.{u}}
    [IsZariskiLocalAtTarget P]
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    (H : ∀ ⦃X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (f : X ⟶ Y),
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
        (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f h)) :
    ∀ ⦃X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (f : X ⟶ Y),
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) X →
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y →
      ∀ ⦃a : BigFppfOver B S hS⦄ (h : yoneda.obj a ⟶ Y) (T : Sieve a),
        IsAffine ((BigFppfOver.toScheme B S hS).obj a) →
        T ∈ BigFppfOver.topology B S hS a →
        (∀ ⦃b : BigFppfOver B S hS⦄ (q : b ⟶ a), T q →
          (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
            (pullback.snd f (yoneda.map q ≫ h))) →
        (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f h) := by
  classical
  intro X Y f hX hY a h T ha hTmem hall
  have _ := ha
  have _hfls : IsZariskiLocalAtSource (@Flat.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Flat)
  have _hfps : IsZariskiLocalAtSource (@LocallyOfFinitePresentation.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FinitePresentation)
  choose V v hVaff hvT hvflat hvlfp hvmem using
    fun x => BigFppfOver.exists_affine_mem_of_mem_topology B S hS hTmem x
  have hopen : ∀ x, IsOpen (Set.range ((BigFppfOver.toScheme B S hS).map (v x)).base) := by
    intro x
    have _ := hvflat x
    have _ := hvlfp x
    exact ((BigFppfOver.toScheme B S hS).map (v x)).isOpenMap.isOpen_range
  have hsub : (Set.univ : Set ((BigFppfOver.toScheme B S hS).obj a)) ⊆
      ⋃ x, Set.range ((BigFppfOver.toScheme B S hS).map (v x)).base :=
    fun x _ => Set.mem_iUnion.2 ⟨x, hvmem x⟩
  obtain ⟨t, ht⟩ := (CompactSpace.isCompact_univ
    (X := ((BigFppfOver.toScheme B S hS).obj a))).elim_finite_subcover _ hopen hsub
  have _ : ∀ x : {x // x ∈ t}, IsAffine ((BigFppfOver.toScheme B S hS).obj (V x.1)) :=
    fun x => hVaff x.1
  obtain ⟨c, inj, e, he, hdesc⟩ :=
    BigFppfOver.exists_coproduct_of_mk_le_aleph0 (σ := {x // x ∈ t})
      Cardinal.mk_le_aleph0 (fun x => V x.1)
  obtain ⟨p, hp⟩ := hdesc (fun x => v x.1)
  have hcaff : IsAffine ((BigFppfOver.toScheme B S hS).obj c) := IsAffine.of_isIso e.inv
  have _ := hcaff
  have key : e.hom ≫ (BigFppfOver.toScheme B S hS).map p =
      Sigma.desc fun x : {x // x ∈ t} => (BigFppfOver.toScheme B S hS).map (v x.1) := by
    refine Sigma.hom_ext _ _ fun x => ?_
    rw [← Category.assoc, he x, Sigma.ι_desc, ← Functor.map_comp, hp x]
  have hinj : ∀ x : {x // x ∈ t}, _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (inj x)) := by
    intro x
    rw [← he x]
    infer_instance
  have hinjcov : ∀ y : (BigFppfOver.toScheme B S hS).obj c,
      ∃ x, y ∈ Set.range ((BigFppfOver.toScheme B S hS).map (inj x)).base := by
    intro y
    obtain ⟨⟨x, w⟩, hxy⟩ : ∃ z : Σ x : {x // x ∈ t},
        ((BigFppfOver.toScheme B S hS).obj (V x.1) : Type u),
        AlgebraicGeometry.sigmaMk
            (fun x : {x // x ∈ t} => (BigFppfOver.toScheme B S hS).obj (V x.1)) z =
          e.inv.base y :=
      ⟨_, (AlgebraicGeometry.sigmaMk _).apply_symm_apply _⟩
    refine ⟨x, w, ?_⟩
    rw [← he x, Scheme.Hom.comp_apply, ← AlgebraicGeometry.sigmaMk_mk, hxy,
      ← Scheme.Hom.comp_apply, e.inv_hom_id]
    rfl
  have hpsurj : Surjective ((BigFppfOver.toScheme B S hS).map p) := by
    have _ : MorphismProperty.RespectsIso (@Surjective.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    have hsurj : Surjective (Sigma.desc fun x : {x // x ∈ t} =>
        (BigFppfOver.toScheme B S hS).map (v x.1)) := by
      refine Surjective.sigmaDesc_of_union_range_eq_univ (Set.eq_univ_of_univ_subset ?_)
      refine ht.trans (Set.iUnion₂_subset fun x hx => ?_)
      exact Set.subset_iUnion_of_subset ⟨x, hx⟩ (le_refl _)
    rw [← key] at hsurj
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @Surjective.{u}) e.hom _).mp hsurj
  have hpflat : Flat ((BigFppfOver.toScheme B S hS).map p) := by
    have _ : MorphismProperty.RespectsIso (@Flat.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    have hfl : Flat (Sigma.desc fun x : {x // x ∈ t} =>
        (BigFppfOver.toScheme B S hS).map (v x.1)) :=
      IsZariskiLocalAtSource.sigmaDesc fun x => hvflat x.1
    rw [← key] at hfl
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @Flat.{u}) e.hom _).mp hfl
  have hplfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map p) := by
    have _ : MorphismProperty.RespectsIso (@LocallyOfFinitePresentation.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    have hfp : LocallyOfFinitePresentation (Sigma.desc fun x : {x // x ∈ t} =>
        (BigFppfOver.toScheme B S hS).map (v x.1)) :=
      IsZariskiLocalAtSource.sigmaDesc fun x => hvlfp x.1
    rw [← key] at hfp
    exact (MorphismProperty.cancel_left_of_respectsIso
      (P := @LocallyOfFinitePresentation.{u}) e.hom _).mp hfp
  have hpqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map p) := by
    have _ : _root_.AlgebraicGeometry.IsAffineHom
      ((BigFppfOver.toScheme B S hS).map p) := inferInstance
    infer_instance
  have hpieces : ∀ x : {x // x ∈ t},
      (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
        (pullback.snd f (yoneda.map (inj x) ≫ yoneda.map p ≫ h)) := by
    intro x
    have key : ∀ g : yoneda.obj (V x.1) ⟶ Y, g = yoneda.map (inj x) ≫ yoneda.map p ≫ h →
        (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f g) →
        (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
          (pullback.snd f (yoneda.map (inj x) ≫ yoneda.map p ≫ h)) := by
      intro g hg
      subst hg
      exact id
    exact key _ (by rw [← Category.assoc, ← Functor.map_comp, hp x]) (hall (v x.1) (hvT x.1))
  choose W pr k hpb hPpr using fun x =>
    exists_isPullback_restrict_of_presheaf f (yoneda.map p ≫ h) (inj x) (hpieces x)
  have hFsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (pullback f (yoneda.map p ≫ h)) :=
    BigFppfOver.isSheaf_pullback_yoneda_obj f (yoneda.map p ≫ h) hX hY
  have hI : #{x // x ∈ t} < B.cutoff :=
    Cardinal.mk_le_aleph0.trans_lt B.aleph0_lt_cutoff
  have hμ : (Finset.univ.sup fun x : {x // x ∈ t} =>
      ((BigFppfOver.toScheme B S hS).obj (W x)).size) < B.cutoff := by
    refine (Finset.sup_lt_iff ?_).2 fun x _ => (W x).left.property
    exact lt_of_le_of_lt bot_le B.aleph0_lt_cutoff
  have hWμ : ∀ x, ((BigFppfOver.toScheme B S hS).obj (W x)).size ≤
      Finset.univ.sup fun x : {x // x ∈ t} =>
        ((BigFppfOver.toScheme B S hS).obj (W x)).size :=
    fun x => Finset.le_sup
      (f := fun x : {x // x ∈ t} => ((BigFppfOver.toScheme B S hS).obj (W x)).size)
      (Finset.mem_univ x)
  have hrep : (pullback f (yoneda.map p ≫ h)).IsRepresentable :=
    isRepresentable_of_zariskiCover_of_size_le B S hS hFsheaf hI hμ W hWμ k
      (fun x => isOpenImmersion_of_isPullback_yoneda_map B S hS (hinj x) (hpb x))
      (isLocallySurjective_sigmaDesc_of_openCover B S hS hinj hinjcov hpb)
  have hrestrict : ∀ ⦃b : BigFppfOver B S hS⦄ (q : b ⟶ c), (T.pullback p) q →
      (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
        (pullback.snd f (yoneda.map q ≫ yoneda.map p ≫ h)) := by
    intro b q hq
    have key : ∀ g : yoneda.obj b ⟶ Y, g = yoneda.map q ≫ yoneda.map p ≫ h →
        (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f g) →
        (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
          (pullback.snd f (yoneda.map q ≫ yoneda.map p ≫ h)) := by
      intro g hg
      subst hg
      exact id
    exact key _ (by rw [← Category.assoc, ← Functor.map_comp]) (hall (q ≫ p) hq)
  exact H f hX hY h p ha hcaff hpsurj hpflat hplfp hpqc
    (presheaf_of_coveringSieve_of_descendsAlong (yoneda.map p ≫ h)
      (relativelyRepresentable_pullback_snd f (yoneda.map p ≫ h) hrep)
      ((BigFppfOver.topology B S hS).pullback_stable p hTmem) hrestrict)

end AlgebraicGeometry.Space

end
