module

public import StacksFrontier.AlgebraicGeometry.Descent.ClosedImmersionEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Descent.DescentDatumSaturation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Effective descent of immersions along a surjective étale chart

`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale B S hS P` is the geometric
hypothesis of Stacks 03I2. This file proves it for `P = AlgebraicGeometry.IsImmersion`, by
combining the cases of open immersions and of closed immersions
(`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion`).

The combination is the factorization of an immersion through the open subscheme on the coborder
of its image, performed *on the base*. The underlying locally closed subset of the datum descends
by `AlgebraicGeometry.Space.exists_isLocallyClosed_preimage_eq_range_of_isImmersion`: there is a
locally closed `V ⊆ a` with `q⁻¹ V` the image of the datum. Its coborder `W` is open, `V` is
closed in `W`, and — because a surjective étale morphism of schemes is open — `q⁻¹ W` is the
coborder of `q⁻¹ V`. So over the open subscheme `b₁` of `a` on `W` the datum is a
*closed*-immersion datum, and the closed-immersion case applies there; while the descended fibre
product over `a` coincides with the one over `b₁`, because every section of it already lands in
`W`.

## Main results

* `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isImmersion`: immersions
  descend effectively along surjective étale morphisms of the big fppf site.
* `AlgebraicGeometry.Space.isAlgebraicSpace_and_isImmersion_of_surjectiveEtaleChart`: a morphism
  from a sheaf to an algebraic space which becomes an immersion after base change along a
  surjective étale chart is an immersion, and its source is an algebraic space.
* `AlgebraicGeometry.Space.isImmersion_tfae_of_isAlgebraicSpace`: the equivalent
  characterizations of an immersion of algebraic spaces by its base changes.
* `AlgebraicGeometry.Space.invariantLocallyClosedSubschemeEquiv_of_isAlgebraicSpace`,
  `AlgebraicGeometry.Space.closed_iff_of_isAlgebraicSpace` and
  `AlgebraicGeometry.Space.open_iff_of_isAlgebraicSpace`: the canonical bijection between the
  invariant locally closed subschemes of a surjective étale chart and the locally closed
  subspaces of the algebraic space, and the two clauses saying that it preserves and reflects
  closedness and openness.

## Implementation notes

*Where the two halves meet.* The restricted problem lives over `b₁`, and two things have to be
matched up. On the datum side, the leg `w : v ⟶ c` of the given datum factors through the open
`c₁ = b₁ ×_a c` of the chart, by `AlgebraicGeometry.exists_comp_eq_of_isOpenImmersion`, and the
factorization `w₁ : v ⟶ c₁` is a closed immersion: it is an immersion by
`AlgebraicGeometry.IsImmersion.of_comp`, and its image is `(j₁ ≫ q)⁻¹ V`, which equals
`(j₁ ≫ q)⁻¹ (closure V)` because `j₁ ≫ q` lands in `W` and `closure V ∩ W = V`. On the
conclusion side, the comparison `X ×[Y] yoneda.obj b₁ ⟶ X ×[Y] yoneda.obj a` is a monomorphism,
being a base change of `yoneda.map i₁`, and it is split by the factorization of
`pullback.snd f h` through `yoneda.map i₁`, so it is an isomorphism. The factorization itself is
`AlgebraicGeometry.Space.range_subset_image_range` — every section of the descended fibre product
lands in the image of the datum, hence in `V`, hence in `W`.

*Why the datum square only has to be pasted.* The representing object of the datum is
`hr.rep.pullback (𝟙 _)`, and the square which presents it over `c₁` rather than over `c` is
obtained by pasting two squares onto `hr.rep.isPullback (𝟙 _)`: the square identifying
`yoneda.obj v` with its own base change along the *monomorphism* `yoneda.map j₁`, which is
Cartesian by `CategoryTheory.IsPullback.of_horiz_isIso_mono`, and the given descent square. No
fibre product has to be computed.

## References

* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
* [Stacks Project, Tag 03M4](https://stacks.math.columbia.edu/tag/03M4)
* [Stacks Project, Tag 07TW](https://stacks.math.columbia.edu/tag/07TW)
* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Effective descent of immersions along surjective étale morphisms.** Immersions of schemes
descend effectively along the surjective étale morphisms of the big fppf site of `S`: whenever a
morphism `f : X ⟶ Y` of sheaves becomes representable by an immersion after base change along a
surjective étale morphism `q : c ⟶ a` of the site, its base change along `h : yoneda.obj a ⟶ Y`
is already representable by an immersion.

The proof restricts the problem to the open subscheme of `a` on the coborder of the descended
subset, where the datum is a closed-immersion datum, and applies
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion`. -/
theorem isEffectiveDescentAlongSurjectiveEtale_isImmersion
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsImmersion.{u}) := by
  intro X Y f hX hY a c h q hqs hqe A m r sq hr
  have _hriI : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.IsImmersion.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hRIpre : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsImmersion.{u})
      (BigFppfOver.toScheme B S hS))).RespectsIso :=
    (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) _).respectsIso
  have _hcompI : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsImmersion.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderComposition :=
    ⟨fun g₁ g₂ hg₁ hg₂ => by
      have h₁ : _root_.AlgebraicGeometry.IsImmersion
          ((BigFppfOver.toScheme B S hS).map g₁) := hg₁
      have h₂ : _root_.AlgebraicGeometry.IsImmersion
          ((BigFppfOver.toScheme B S hS).map g₂) := hg₂
      have hcomp : _root_.AlgebraicGeometry.IsImmersion
          ((BigFppfOver.toScheme B S hS).map g₁ ≫
            (BigFppfOver.toScheme B S hS).map g₂) := inferInstance
      rwa [← Functor.map_comp] at hcomp⟩
  -- the descended locally closed subset of the base, and its coborder
  obtain ⟨V, hVlc, hVpre⟩ :=
    exists_isLocallyClosed_preimage_eq_range_of_isImmersion sq hqs hqe hr
  have hwimm : _root_.AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map
      (hr.rep.snd (𝟙 (yoneda.obj c)))) := hr.property_snd _
  obtain ⟨b₁, i₁, hi₁oi, hi₁range, hi₁univ⟩ := exists_restrict_bigFppfOver a
    ⟨coborder V, hVlc.isOpen_coborder⟩
  have hi₁range' : Set.range ((BigFppfOver.toScheme B S hS).map i₁).base =
      coborder V := hi₁range
  have hmonoy : ∀ {u v : BigFppfOver B S hS} (g : u ⟶ v),
      _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map g) →
        Mono (yoneda.map g) := fun g _ =>
    have : Mono g := (BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance
    inferInstance
  have hmonoyi := hmonoy i₁ hi₁oi
  -- the restricted chart
  set q₁ : Limits.pullback i₁ q ⟶ b₁ := pullback.fst i₁ q with hq₁def
  set j₁ : Limits.pullback i₁ q ⟶ c := pullback.snd i₁ q with hj₁def
  have psite : IsPullback q₁ j₁ i₁ q := IsPullback.of_hasPullback i₁ q
  have pmap : IsPullback ((BigFppfOver.toScheme B S hS).map q₁)
      ((BigFppfOver.toScheme B S hS).map j₁) ((BigFppfOver.toScheme B S hS).map i₁)
      ((BigFppfOver.toScheme B S hS).map q) := psite.map (BigFppfOver.toScheme B S hS)
  have hj₁oi : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map j₁) :=
    MorphismProperty.of_isPullback pmap hi₁oi
  have hq₁s : Surjective ((BigFppfOver.toScheme B S hS).map q₁) :=
    MorphismProperty.of_isPullback pmap.flip hqs
  have hq₁e : Etale ((BigFppfOver.toScheme B S hS).map q₁) :=
    MorphismProperty.of_isPullback pmap.flip hqe
  have hj₁range : Set.range ((BigFppfOver.toScheme B S hS).map j₁).base =
      ((BigFppfOver.toScheme B S hS).map q).base ⁻¹'
        Set.range ((BigFppfOver.toScheme B S hS).map i₁).base := by
    simpa using Scheme.image_preimage_eq_of_isPullback pmap Set.univ
  -- the leg of the datum factors through the restricted chart, as a closed immersion
  obtain ⟨w₁, hw₁⟩ := exists_comp_eq_of_isOpenImmersion j₁ hj₁oi
    (hr.rep.snd (𝟙 (yoneda.obj c))) (by
      rw [hj₁range, hi₁range', ← hVpre]
      exact Set.preimage_mono (Set.preimage_mono subset_coborder))
  have hcompimm : _root_.AlgebraicGeometry.IsImmersion
      ((BigFppfOver.toScheme B S hS).map w₁ ≫ (BigFppfOver.toScheme B S hS).map j₁) := by
    rw [← Functor.map_comp, hw₁]; exact hwimm
  have himm1 : _root_.AlgebraicGeometry.IsImmersion
      ((BigFppfOver.toScheme B S hS).map w₁) :=
    _root_.AlgebraicGeometry.IsImmersion.of_comp
      ((BigFppfOver.toScheme B S hS).map w₁) ((BigFppfOver.toScheme B S hS).map j₁)
  have hbase : ∀ y, ((BigFppfOver.toScheme B S hS).map j₁).base
      (((BigFppfOver.toScheme B S hS).map w₁).base y) =
      ((BigFppfOver.toScheme B S hS).map (hr.rep.snd (𝟙 (yoneda.obj c)))).base y := by
    intro y
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hw₁]
  have hrange1 : Set.range ((BigFppfOver.toScheme B S hS).map w₁).base =
      ((BigFppfOver.toScheme B S hS).map j₁).base ⁻¹'
        Set.range ((BigFppfOver.toScheme B S hS).map
          (hr.rep.snd (𝟙 (yoneda.obj c)))).base := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro x ⟨y, rfl⟩
      exact ⟨y, (hbase y).symm⟩
    · rintro x ⟨y, hy⟩
      exact ⟨y, ((BigFppfOver.toScheme B S hS).map j₁).isOpenEmbedding.injective
        ((hbase y).trans hy)⟩
  have hinW : ∀ x, ((BigFppfOver.toScheme B S hS).map q).base
      (((BigFppfOver.toScheme B S hS).map j₁).base x) ∈ coborder V := by
    intro x
    rw [← hi₁range']
    refine ⟨((BigFppfOver.toScheme B S hS).map q₁).base x, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Functor.map_comp, ← Functor.map_comp,
      psite.w]
  have hclosed1 : IsClosed (Set.range ((BigFppfOver.toScheme B S hS).map w₁).base) := by
    rw [hrange1, ← hVpre]
    have key : ((BigFppfOver.toScheme B S hS).map j₁).base ⁻¹'
        (((BigFppfOver.toScheme B S hS).map q).base ⁻¹' V) =
        ((BigFppfOver.toScheme B S hS).map j₁).base ⁻¹'
          (((BigFppfOver.toScheme B S hS).map q).base ⁻¹' closure V) := by
      refine Set.Subset.antisymm (fun x hx => subset_closure hx) fun x hx => ?_
      rw [Set.mem_preimage, Set.mem_preimage] at hx ⊢
      have hmem : ((BigFppfOver.toScheme B S hS).map q).base
          (((BigFppfOver.toScheme B S hS).map j₁).base x) ∈ closure V ∩ coborder V :=
        ⟨hx, hinW x⟩
      rwa [closure_inter_coborder] at hmem
    rw [key]
    exact (isClosed_closure.preimage ((BigFppfOver.toScheme B S hS).map q).continuous).preimage
      ((BigFppfOver.toScheme B S hS).map j₁).continuous
  have hci1 : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map w₁) :=
    _root_.AlgebraicGeometry.IsClosedImmersion.of_isPreimmersion _ hclosed1
  -- the restricted descent datum
  have osq : IsPullback (𝟙 (yoneda.obj (hr.rep.pullback (𝟙 (yoneda.obj c)))))
      (yoneda.map w₁) (yoneda.map (hr.rep.snd (𝟙 (yoneda.obj c)))) (yoneda.map j₁) :=
    haveI := hmonoy j₁ hj₁oi
    IsPullback.of_horiz_isIso_mono
      ⟨by rw [Category.id_comp, ← Functor.map_comp, hw₁]⟩
  have heq : yoneda.map q₁ ≫ (yoneda.map i₁ ≫ h) =
      yoneda.map j₁ ≫ yoneda.map q ≫ h := by
    rw [← Category.assoc, ← Functor.map_comp, psite.w, Functor.map_comp, Category.assoc]
  have dsq : IsPullback (hr.rep.fst (𝟙 (yoneda.obj c)) ≫ m) (yoneda.map w₁) f
      (yoneda.map q₁ ≫ (yoneda.map i₁ ≫ h)) := by
    have H := (osq.paste_horiz (hr.rep.isPullback (𝟙 (yoneda.obj c)))).paste_horiz sq
    rw [heq]
    simpa using H
  have hr₁ : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map w₁) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ w₁).2 hci1
  have hCI := isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion B S hS f hX hY
    (yoneda.map i₁ ≫ h) q₁ hq₁s hq₁e _ _ dsq hr₁
  -- every section of the descended fibre product lands in the coborder
  have hlr : Subfunctor.range (pullback.snd f h) ≤ Subfunctor.range (yoneda.map i₁) := by
    intro T s hs
    obtain ⟨x, rfl⟩ := hs
    have hsub := range_subset_image_range sq hr.rep hqs (yonedaEquiv.symm x)
      (yonedaEquiv_symm_comp_pullback_snd x)
    rw [← hVpre] at hsub
    obtain ⟨g, hg⟩ := hi₁univ ((pullback.snd f h).app T x)
      (hsub.trans ((Set.image_preimage_subset _ _).trans subset_coborder))
    exact ⟨g, hg⟩
  obtain ⟨l₁, hl₁⟩ : ∃ l₁ : Limits.pullback f h ⟶ yoneda.obj b₁,
      l₁ ≫ yoneda.map i₁ = pullback.snd f h := by
    have h1 : inv (Subfunctor.toRange (yoneda.map i₁)) ≫ yoneda.map i₁ =
        (Subfunctor.range (yoneda.map i₁)).ι :=
      (IsIso.inv_comp_eq _).2 (Subfunctor.toRange_ι (yoneda.map i₁)).symm
    refine ⟨Subfunctor.lift (pullback.snd f h) hlr ≫
      inv (Subfunctor.toRange (yoneda.map i₁)), ?_⟩
    rw [Category.assoc, h1, Subfunctor.lift_ι]
  -- so the two fibre products agree
  obtain ⟨θ, hθ⟩ : ∃ θ : Limits.pullback f (yoneda.map i₁ ≫ h) ⟶ Limits.pullback f h,
      IsPullback θ (pullback.snd f (yoneda.map i₁ ≫ h)) (pullback.snd f h)
        (yoneda.map i₁) :=
    ⟨_, (IsPullback.of_hasPullback f (yoneda.map i₁ ≫ h)).of_right'
      (IsPullback.of_hasPullback f h)⟩
  have hmonoθ : Mono θ :=
    MorphismProperty.of_isPullback (P := MorphismProperty.monomorphisms _) hθ.flip
      hmonoyi
  have hσθ : hθ.lift (𝟙 (Limits.pullback f h)) l₁
      (by rw [Category.id_comp, ← hl₁]) ≫ θ = 𝟙 _ := hθ.lift_fst _ _ _
  have hθiso : IsIso θ :=
    ⟨⟨hθ.lift (𝟙 (Limits.pullback f h)) l₁ (by rw [Category.id_comp, ← hl₁]),
      (cancel_mono θ).1 (by rw [Category.assoc, hσθ, Category.comp_id, Category.id_comp]),
      hσθ⟩⟩
  have himmP : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsImmersion.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
        (pullback.snd f (yoneda.map i₁ ≫ h) ≫ yoneda.map i₁) :=
    MorphismProperty.comp_mem _ _ _
      (MorphismProperty.relative_monotone
        (MorphismProperty.monotone_inverseImage (BigFppfOver.toScheme B S hS)
          (fun _ _ g hg => by
            have := hg; exact (inferInstance : _root_.AlgebraicGeometry.IsImmersion g))) _ hCI)
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ i₁).2
        (inferInstance :
          _root_.AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map i₁)))
  rw [show pullback.snd f h =
      inv θ ≫ (pullback.snd f (yoneda.map i₁ ≫ h) ≫ yoneda.map i₁) from
    by rw [← hθ.w, IsIso.inv_hom_id_assoc]]
  exact MorphismProperty.RespectsIso.precomp _ _ _ himmP

/-- Let `f : X ⟶ Y` be a morphism of presheaves on the big fppf site of `S` with `X` a sheaf and
`Y` an algebraic space over `S`. If some surjective étale chart `g` of `Y` makes the base change
of `f` an immersion, then `X` is an algebraic space over `S` and `f` is an immersion.

This is
`AlgebraicGeometry.Space.isAlgebraicSpace_and_presheaf_of_surjectiveEtaleChart_of_descent`
with its descent hypothesis supplied by
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isImmersion`. -/
theorem isAlgebraicSpace_and_isImmersion_of_surjectiveEtaleChart
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hY : IsAlgebraicSpace B S hS Y)
    {U : BigFppfOver B S hS} {g : yoneda.obj U ⟶ Y}
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) g)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) g)
    (hV : IsImmersion B S hS (pullback.snd f g)) :
    IsAlgebraicSpace B S hS X ∧ IsImmersion B S hS f :=
  have : MorphismProperty.RespectsIso (@_root_.AlgebraicGeometry.IsImmersion.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  isAlgebraicSpace_and_presheaf_of_surjectiveEtaleChart_of_descent
    (isEffectiveDescentAlongSurjectiveEtale_isImmersion B S hS) hX hY hs he hV

/-- A morphism of algebraic spaces over `S` is an immersion exactly when every one of its base
changes to a representable presheaf is, exactly when every one of its base changes to an affine
object of the site is, exactly when its base change along one surjective étale scheme chart of
the target is, and exactly when its base changes along the members of some Zariski covering of
the target are.

This is `AlgebraicGeometry.Space.isImmersion_tfae` with its hypothesis `hdesc` supplied by
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isImmersion`. -/
@[stacks 03M4 "immersions", ega "I 4.2.4" "(a) immersion case"]
theorem isImmersion_tfae_of_isAlgebraicSpace
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) :
    List.TFAE [
      IsImmersion B S hS f,
      (∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ G),
        IsImmersion B S hS (pullback.snd f g)),
      (∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ G),
        IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
          IsImmersion B S hS (pullback.snd f g)),
      (∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ G),
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) g ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) g ∧
        IsImmersion B S hS (pullback.snd f g)),
      (∃ (I : Type u) (U : I → Subfunctor G),
        IsZariskiCover B S hS I U ∧
        ∀ i, IsImmersion B S hS (pullback.snd f (U i).ι))
    ] :=
  isImmersion_tfae B S hS
    (isEffectiveDescentAlongSurjectiveEtale_isImmersion B S hS) hF hG f

/-! ### Invariant locally closed subschemes of a chart -/

section Invariant

variable (B S hS)
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : BigFppfOver B S hS}
    {φ : yoneda.obj U ⟶ X}
variable (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS))) φ)
variable (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS))) φ)

include hs he in
/-- For an algebraic space `X` over `S` with a surjective étale chart `φ : U ⟶ X`, the invariant
locally closed subschemes of `U` correspond bijectively to the locally closed subspaces of `X`,
and the bijection is characterised by pullback along `φ`.

This is `AlgebraicGeometry.Space.invariantLocallyClosedSubschemeEquiv` with its hypothesis
`hdesc` supplied by
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isImmersion`. -/
@[stacks 07TW "canonical bijection"]
noncomputable def invariantLocallyClosedSubschemeEquiv_of_isAlgebraicSpace
    (hX : IsAlgebraicSpace B S hS X) :
    {e : InvariantLocallyClosedSubscheme B S hS hs ≃
      LocallyClosedQuotientSubspace B S hS (X := X) //
      ∀ Z, ((e Z).1.preimage φ) = subschemePoints B S hS Z.1} :=
  invariantLocallyClosedSubschemeEquiv B S hS hs he
    (isEffectiveDescentAlongSurjectiveEtale_isImmersion B S hS) hX

include hs he in
/-- The subspace of `X` corresponding to an invariant subscheme of the chart is closed exactly when
that subscheme is closed in the chart.

This is `AlgebraicGeometry.Space.closed_iff` with its hypothesis `hdesc` supplied by
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isImmersion`. -/
@[stacks 07TW "closedness"]
theorem closed_iff_of_isAlgebraicSpace (hX : IsAlgebraicSpace B S hS X)
    (Z : InvariantLocallyClosedSubscheme B S hS hs) :
    IsClosedSubspace B S hS
        ((invariantLocallyClosedSubschemeEquiv_of_isAlgebraicSpace B S hS hs he hX).1 Z).1 ↔
      _root_.AlgebraicGeometry.IsClosedImmersion Z.1.arrow :=
  closed_iff B S hS hs he
    (isEffectiveDescentAlongSurjectiveEtale_isImmersion B S hS) hX Z

include hs he in
/-- The subspace of `X` corresponding to an invariant subscheme of the chart is open exactly when
that subscheme is open in the chart.

This is `AlgebraicGeometry.Space.open_iff` with its hypothesis `hdesc` supplied by
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isImmersion`. -/
@[stacks 07TW "openness"]
theorem open_iff_of_isAlgebraicSpace (hX : IsAlgebraicSpace B S hS X)
    (Z : InvariantLocallyClosedSubscheme B S hS hs) :
    IsOpenSubspace B S hS
        ((invariantLocallyClosedSubschemeEquiv_of_isAlgebraicSpace B S hS hs he hX).1 Z).1 ↔
      _root_.AlgebraicGeometry.IsOpenImmersion Z.1.arrow :=
  open_iff B S hS hs he
    (isEffectiveDescentAlongSurjectiveEtale_isImmersion B S hS) hX Z

end Invariant

end AlgebraicGeometry.Space

end
