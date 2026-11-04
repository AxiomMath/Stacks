module

public import StacksFrontier.AlgebraicGeometry.Descent.ZariskiCoverSizeBound
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusRelative

/-!
# Reducing the base of a covering-sieve descent problem to an affine object

`AlgebraicGeometry.Space.IsEffectiveDescentAlongCoveringSieve` quantifies over a morphism
`h : yoneda.obj a ⟶ Y` out of a representable presheaf and a covering sieve `T` of the object `a`
of the big fppf site of `S`. This file shows that its defining condition need only be checked for
affine base objects `a`, provided the cutoff of the site is a regular cardinal, or the property `P`
does not raise size, or `P` lies below the monomorphisms.

## Main results

* `AlgebraicGeometry.Space.exists_isPullback_restrict_of_affineBase`: under the affine-base
  hypothesis, the projection `X ×[Y] yoneda.obj a ⟶ yoneda.obj a` becomes representable with `P`
  after base change along any morphism `u : V ⟶ a` of the site with `V` affine.
* `AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_of_affineBase_of_isRegular`: for a
  site whose cutoff is a regular cardinal, if the defining condition of
  `AlgebraicGeometry.Space.IsEffectiveDescentAlongCoveringSieve` holds whenever the base object is
  affine, then it holds for every base object.
* `AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_of_affineBase_of_size_le`: the
  same reduction for an arbitrary site, for a property `P` which does not raise the size of the
  source above `2 ^ 2 ^ size (target)`.
* `AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_of_affineBase_of_le_monomorphisms`:
  the same reduction for an arbitrary site, for a property `P` below the monomorphisms.

## References

* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 02W3](https://stacks.math.columbia.edu/tag/02W3)
* [Stacks Project, Tag 03KC](https://stacks.math.columbia.edu/tag/03KC)
* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
-/

@[expose] public section

open Cardinal CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Let `H` be the defining condition of
`AlgebraicGeometry.Space.IsEffectiveDescentAlongCoveringSieve` restricted to affine base objects,
and let a descent problem — a morphism of sheaves `f : X ⟶ Y`, a morphism `h : yoneda.obj a ⟶ Y`
and a covering sieve `T` of `a` along whose arrows the base change of `f` is representable with
`P` — be given. Then for every morphism `u : V ⟶ a` of the site whose source is affine, the base
change of `X ×[Y] yoneda.obj a ⟶ yoneda.obj a` along `yoneda.map u` is represented by a morphism
of the site with `P`. -/
theorem exists_isPullback_restrict_of_affineBase {P : MorphismProperty Scheme.{u}}
    (H : ∀ ⦃X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (f : X ⟶ Y),
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) X →
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y →
      ∀ ⦃a : BigFppfOver B S hS⦄ (h : yoneda.obj a ⟶ Y) (T : Sieve a),
        IsAffine ((BigFppfOver.toScheme B S hS).obj a) →
        T ∈ BigFppfOver.topology B S hS a →
        (∀ ⦃b : BigFppfOver B S hS⦄ (q : b ⟶ a), T q →
          (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
            (pullback.snd f (yoneda.map q ≫ h))) →
        (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f h))
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    {a : BigFppfOver B S hS} (h : yoneda.obj a ⟶ Y) {T : Sieve a}
    (hTmem : T ∈ BigFppfOver.topology B S hS a)
    (hall : ∀ ⦃b : BigFppfOver B S hS⦄ (q : b ⟶ a), T q →
      (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
        (pullback.snd f (yoneda.map q ≫ h)))
    {V : BigFppfOver B S hS} (u : V ⟶ a)
    (hVaff : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) :
    ∃ (W : BigFppfOver B S hS) (pr : W ⟶ V) (k : yoneda.obj W ⟶ pullback f h),
      IsPullback k (yoneda.map pr) (pullback.snd f h) (yoneda.map u) ∧
        P ((BigFppfOver.toScheme B S hS).map pr) := by
  have hrestrict : ∀ ⦃b : BigFppfOver B S hS⦄ (q : b ⟶ V), (T.pullback u) q →
      (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
        (pullback.snd f (yoneda.map q ≫ yoneda.map u ≫ h)) := by
    intro b q hq
    have key : ∀ g : yoneda.obj b ⟶ Y, g = yoneda.map q ≫ yoneda.map u ≫ h →
        (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f g) →
        (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
          (pullback.snd f (yoneda.map q ≫ yoneda.map u ≫ h)) := by
      intro g hg
      subst hg
      exact id
    exact key _ (by rw [Functor.map_comp, Category.assoc]) (hall (q ≫ u) hq)
  have hH := H f hX hY (yoneda.map u ≫ h) (T.pullback u) hVaff
    ((BigFppfOver.topology B S hS).pullback_stable u hTmem) hrestrict
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

/-- If a morphism of presheaves `π : F ⟶ yoneda.obj a` can be base changed along every morphism
from an affine object to `a`, then the affine opens of `a` give a cover of `a` by open immersions
over which `π` is represented. -/
private theorem exists_affineOpen_cover_isPullback {P : MorphismProperty Scheme.{u}}
    {a : BigFppfOver B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (π : F ⟶ yoneda.obj a)
    (hex : ∀ {V : BigFppfOver B S hS} (u : V ⟶ a),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
      ∃ (W : BigFppfOver B S hS) (pr : W ⟶ V) (k : yoneda.obj W ⟶ F),
        IsPullback k (yoneda.map pr) π (yoneda.map u) ∧
          P ((BigFppfOver.toScheme B S hS).map pr)) :
    ∃ (W : ((BigFppfOver.toScheme B S hS).obj a).affineOpens → BigFppfOver B S hS)
      (k : ∀ U, yoneda.obj (W U) ⟶ F), (∀ U, IsOpenImmersion B S hS (k U)) ∧
      Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc k) ∧
      ∀ U, ∃ (V : BigFppfOver B S hS) (u : V ⟶ a) (pr : W U ⟶ V),
        _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map u) ∧
          P ((BigFppfOver.toScheme B S hS).map pr) := by
  choose V u hu hurange hVaff using fun U => BigFppfOver.exists_affineOpen_restrict B S hS a U
  have hucov : ∀ y : (BigFppfOver.toScheme B S hS).obj a,
      ∃ U, y ∈ Set.range ((BigFppfOver.toScheme B S hS).map (u U)) := by
    intro y
    have hy : y ∈ (⊤ : ((BigFppfOver.toScheme B S hS).obj a).Opens) := trivial
    rw [← iSup_affineOpens_eq_top] at hy
    obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    exact ⟨U, by rw [hurange U]; exact hU⟩
  choose W pr k hpb hP using fun U => hex (u U) (hVaff U)
  exact ⟨W, k, fun U => isOpenImmersion_of_isPullback_yoneda_map B S hS (hu U) (hpb U),
    isLocallySurjective_sigmaDesc_of_openCover B S hS hu hucov hpb,
    fun U => ⟨V U, u U, pr U, hu U, hP U⟩⟩

/-- **Affine-base reduction for effective descent along covering sieves, regular cutoff.** If
the cutoff of the big fppf site of `S` is a regular cardinal and the defining condition of
`AlgebraicGeometry.Space.IsEffectiveDescentAlongCoveringSieve` holds for every problem whose base
object `a` is affine, then it holds for every problem. -/
theorem isEffectiveDescentAlongCoveringSieve_of_affineBase_of_isRegular
    {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtTarget P]
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    (hreg : B.cutoff.IsRegular)
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
    IsEffectiveDescentAlongCoveringSieve B S hS P := by
  refine isEffectiveDescentAlongCoveringSieve_of_zariskiCover ?_
  intro X Y f hX hY a h T hTmem hall
  obtain ⟨W, k, hk, hsurj, hW⟩ :=
    exists_affineOpen_cover_isPullback (pullback.snd f h)
      (exists_isPullback_restrict_of_affineBase H f hX hY h hTmem hall)
  refine ⟨_, ⟨⟨⊥, isAffineOpen_bot _⟩⟩,
    ((BigFppfOver.toScheme B S hS).obj a).mk_affineOpens_le_size.trans_lt
      (lt_of_lt_of_le a.left.property hreg.2),
    W, k, hk, hsurj⟩

/-- **Affine-base reduction for effective descent along covering sieves, size-bounded
property.** Let `P` be a property whose sources are bounded by `2 ^ 2 ^ size (target)`. If the
defining condition of `AlgebraicGeometry.Space.IsEffectiveDescentAlongCoveringSieve` holds at `P`
for every problem whose base object is affine, then it holds for every problem. -/
theorem isEffectiveDescentAlongCoveringSieve_of_affineBase_of_size_le
    {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtTarget P]
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    (hsize : ∀ {Z W : Scheme.{u}} (g : W ⟶ Z), P g →
      W.size ≤ (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ Z.size)
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
    IsEffectiveDescentAlongCoveringSieve B S hS P := by
  refine isEffectiveDescentAlongCoveringSieve_of_zariskiCover_of_size_le ?_
  intro X Y f hX hY a h T hTmem hall
  obtain ⟨W, k, hk, hsurj, hW⟩ :=
    exists_affineOpen_cover_isPullback (pullback.snd f h)
      (exists_isPullback_restrict_of_affineBase H f hX hY h hTmem hall)
  refine ⟨_, (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ ((BigFppfOver.toScheme B S hS).obj a).size,
    ((BigFppfOver.toScheme B S hS).obj a).mk_affineOpens_le_size.trans_lt a.left.property,
    B.cutoff_isStrongPrelimit (B.cutoff_isStrongPrelimit a.left.property), W, k, fun U => ?_,
    hk, hsurj⟩
  obtain ⟨V, u, pr, hu, hP⟩ := hW U
  exact (hsize _ hP).trans (power_le_power_left two_ne_zero
    (power_le_power_left two_ne_zero
      (Scheme.size_le_of_isOpenImmersion ((BigFppfOver.toScheme B S hS).map u))))

/-- **Affine-base reduction for effective descent along covering sieves, property below the
monomorphisms.** Let `P` be a property below the monomorphisms. If the defining condition of
`AlgebraicGeometry.Space.IsEffectiveDescentAlongCoveringSieve` holds at `P` for every problem
whose base object is affine, then it holds for every problem. -/
theorem isEffectiveDescentAlongCoveringSieve_of_affineBase_of_le_monomorphisms
    {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtTarget P]
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    (hPmono : P ≤ MorphismProperty.monomorphisms Scheme.{u})
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
    IsEffectiveDescentAlongCoveringSieve B S hS P := by
  refine isEffectiveDescentAlongCoveringSieve_of_affineBase_of_size_le (fun g hg => ?_) H
  have _ : Mono g := hPmono _ hg
  refine (Scheme.size_le_of_mono g).trans (max_le
    (power_le_power_left two_ne_zero (Scheme.mk_le_two_pow_size _)) ?_)
  exact (Cardinal.cantor _).le.trans (power_le_power_left two_ne_zero (Cardinal.cantor _).le)

end AlgebraicGeometry.Space

end
