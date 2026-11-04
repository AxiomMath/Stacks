module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.PropertyC
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.UniversallyOpen

/-!
# Property (C) with an affine dominating scheme

A morphism `f : X ⟶ Y` with property (C) — [Stacks, Tag 04DW], in this library
`Stacks.EtaleCohomology.HasPropertyC` — dominates every scheme étale over `X` by the base change
along `f` of a scheme étale over `Y`. The dominating scheme it produces is not affine, and the
proof of Tag 04DW builds it as a coproduct indexed by all the points of the dominated scheme, so
it is not even quasi-compact.

This file refines it: when the dominated scheme is quasi-compact, the dominating scheme can be
taken affine. This is the sentence "since `U` is quasi-compact we may replace `W` by a finite
disjoint union of affine opens, so that `W` is affine" of the second proof of
[Stacks, Tag 04DZ].

## The shape of the argument

The dominating scheme is covered by its affine opens, each of which is again étale over `Y`, and
base change along `f` carries that open covering to an open covering of the dominating base
change. The dominated scheme `U` receives each piece through a morphism which is étale, hence an
open map, so `U` is covered by the open images of the pieces; being quasi-compact it is covered
by finitely many of them. The coproduct of those finitely many affine opens is affine and étale
over `Y`, and its base change along `f` is the coproduct of their base changes, so the morphisms
to `U` assemble into one morphism out of it, which is surjective because its image is the union
of the chosen images.

## Main definitions

* `AlgebraicGeometry.pullbackMapOfComp`: the base change along `f` of a morphism of schemes over
  `Y`, as a morphism of fibre products with `X`. **This is a new definition.**

## Main results

* `AlgebraicGeometry.isPullback_pullbackMapOfComp`: base change along `f` of a morphism of
  schemes over `Y` is a fibre square, so it is an open immersion when the morphism is.
* `AlgebraicGeometry.nonempty_isColimit_cofanMk_pullback_sigma`: **base change along `f` turns a
  coproduct of schemes over `Y` into the coproduct of the base changes.**
* `Stacks.EtaleCohomology.exists_isAffine_etale_surjective_of_hasPropertyC`: **the affine
  refinement of property (C).** For a morphism with property (C) and a quasi-compact scheme `U`
  étale over `X`, the dominating scheme can be taken affine.

## Implementation notes

`AlgebraicGeometry.pullbackMapOfComp` carries the factorisation `t ≫ v = v'` as a hypothesis
rather than in its type, so that it applies to the coproduct inclusions, for which the
factorisation through `CategoryTheory.Limits.Sigma.desc` holds only propositionally. It
generalises the private `Stacks.EtaleCohomology.pullbackFactorMap` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.PropertyC`, which is the same construction
for a coproduct inclusion and which cannot be used from outside that file; the proof of
Tag 04DW there should be refactored onto this one.

Openness of the image of an étale morphism is used through
`AlgebraicGeometry.universallyOpen_of_flat_of_locallyOfFinitePresentation`, Stacks 01UA.

## References

* [Stacks Project, Tag 04DW](https://stacks.math.columbia.edu/tag/04DW)
* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
* [Stacks Project, Tag 01UA](https://stacks.math.columbia.edu/tag/01UA)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-! ### Base change of a morphism of schemes over the base -/

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {V V' : Scheme.{u}} {v : V ⟶ Y} {v' : V' ⟶ Y}
  (t : V' ⟶ V) (ht : t ≫ v = v')

/-- **The base change along `f` of a morphism of schemes over `Y`.** For `t : V' ⟶ V` with
`t ≫ v = v'` this is the induced morphism `X ×_Y V' ⟶ X ×_Y V`. -/
def pullbackMapOfComp : pullback f v' ⟶ pullback f v :=
  pullback.map f v' f v (𝟙 X) t (𝟙 Y) (by simp) (by simpa using ht.symm)

/-- The base change `pullbackMapOfComp f t ht` commutes with the projections to `X`. -/
@[reassoc (attr := simp)]
lemma pullbackMapOfComp_fst :
    pullbackMapOfComp f t ht ≫ pullback.fst f v = pullback.fst f v' := by
  show pullback.lift (pullback.fst f v') (pullback.snd f v' ≫ t) _ ≫ _ = _
  exact pullback.lift_fst _ _ _

/-- Composing `pullbackMapOfComp f t ht` with the projection to `V` is the projection to `V'`
followed by `t`. -/
@[reassoc (attr := simp)]
lemma pullbackMapOfComp_snd :
    pullbackMapOfComp f t ht ≫ pullback.snd f v = pullback.snd f v' ≫ t := by
  show pullback.lift (pullback.fst f v') (pullback.snd f v' ≫ t) _ ≫ _ = _
  exact pullback.lift_snd _ _ _

/-- **Base change along `f` of a morphism of schemes over `Y` is a fibre square.** The base
change `X ×_Y V' ⟶ X ×_Y V` of `t : V' ⟶ V`, together with the projection to `V'`, exhibits
`X ×_Y V'` as the fibre product of `X ×_Y V ⟶ V` with `t`. -/
theorem isPullback_pullbackMapOfComp :
    IsPullback (pullbackMapOfComp f t ht) (pullback.snd f v') (pullback.snd f v) t := by
  have hcomm := pullbackMapOfComp_snd f t ht
  apply IsPullback.of_isLimit
    (c := PullbackCone.mk (pullbackMapOfComp f t ht) (pullback.snd f v') hcomm)
  refine PullbackCone.IsLimit.mk hcomm
    (fun c => pullback.lift (c.fst ≫ pullback.fst f v) c.snd ?_) ?_ ?_ ?_
  · rw [Category.assoc, pullback.condition, ← Category.assoc, c.condition, Category.assoc, ht]
  · intro c
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullbackMapOfComp_fst, pullback.lift_fst]
    · rw [Category.assoc, pullbackMapOfComp_snd, ← Category.assoc, pullback.lift_snd,
        c.condition]
  · intro c
    exact pullback.lift_snd _ _ _
  · intro c m h₁ h₂
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, ← pullbackMapOfComp_fst f t ht, ← Category.assoc, h₁]
    · rw [pullback.lift_snd, h₂]

/-- The base change along `f` of an open immersion `t` is an open immersion. -/
instance isOpenImmersion_pullbackMapOfComp [IsOpenImmersion t] :
    IsOpenImmersion (pullbackMapOfComp f t ht) := by
  have : IsOpenImmersion (pullback.fst (pullback.snd f v) t) :=
    MorphismProperty.pullback_fst (pullback.snd f v) t inferInstance
  rw [← (isPullback_pullbackMapOfComp f t ht).isoPullback_hom_fst]
  infer_instance

/-- The image of the base change of an open immersion `t` is the preimage of the image of `t`. -/
lemma range_pullbackMapOfComp [IsOpenImmersion t] :
    Set.range (pullbackMapOfComp f t ht).base
      = (pullback.snd f v).base ⁻¹' Set.range t.base := by
  have h := isPullback_pullbackMapOfComp f t ht
  have e₁ : Set.range (pullbackMapOfComp f t ht).base
      = ((h.isoPullback.hom ≫ pullback.fst (pullback.snd f v) t).opensRange :
          Set (pullback f v : Scheme.{u})) :=
    congrArg (fun φ : pullback f v' ⟶ pullback f v => Set.range φ.base)
      h.isoPullback_hom_fst.symm
  rw [e₁, Scheme.Hom.opensRange_comp_of_isIso]
  exact IsOpenImmersion.range_pullbackFst (f := t) (g := pullback.snd f v)

/-- A point of `X ×_Y V` whose image in `V` lies in the image of the open immersion `t` lies in
the image of the base change of `t`. -/
private lemma mem_range_pullbackMapOfComp [IsOpenImmersion t]
    {p : (pullback f v : Scheme.{u})} {x : V'} (hx : t.base x = (pullback.snd f v).base p) :
    p ∈ Set.range (pullbackMapOfComp f t ht).base := by
  rw [range_pullbackMapOfComp]
  exact ⟨x, hx⟩

/-- The image of the base change of an open immersion `t`, as an open subscheme. -/
lemma opensRange_pullbackMapOfComp [IsOpenImmersion t] :
    (pullbackMapOfComp f t ht).opensRange = pullback.snd f v ⁻¹ᵁ t.opensRange :=
  TopologicalSpace.Opens.ext (range_pullbackMapOfComp f t ht)

/-! ### Base change of a coproduct -/

/-- **Base change along `f` turns a coproduct of schemes over `Y` into the coproduct of the base
changes.** The base changes of the coproduct inclusions exhibit `X ×_Y (∐ V)` as the coproduct of
the `X ×_Y V i`. -/
theorem nonempty_isColimit_cofanMk_pullback_sigma {ι : Type u} (W : ι → Scheme.{u})
    (wᵢ : ∀ i, W i ⟶ Y) (w : (∐ W) ⟶ Y) (hw : ∀ i, Sigma.ι W i ≫ w = wᵢ i) :
    Nonempty (IsColimit (Cofan.mk (pullback f w)
      (fun i => pullbackMapOfComp f (Sigma.ι W i) (hw i)))) := by
  classical
  refine nonempty_isColimit_cofanMk_of _ ?_ ?_
  · rw [eq_top_iff]
    intro p _
    obtain ⟨⟨i, x⟩, hx⟩ := (sigmaMk W).surjective ((pullback.snd f w).base p)
    have hx' : Sigma.ι W i x = (pullback.snd f w).base p := by
      rwa [← sigmaMk_mk]
    simp only [TopologicalSpace.Opens.iSup_mk, TopologicalSpace.Opens.mem_mk, Set.mem_iUnion]
    exact ⟨i, mem_range_pullbackMapOfComp f _ (hw i) hx'⟩
  · intro i j hij
    show Disjoint (pullbackMapOfComp f (Sigma.ι W i) (hw i)).opensRange
      (pullbackMapOfComp f (Sigma.ι W j) (hw j)).opensRange
    rw [opensRange_pullbackMapOfComp, opensRange_pullbackMapOfComp,
      ← TopologicalSpace.Opens.coe_disjoint]
    exact Disjoint.preimage (pullback.snd f w).base
      (TopologicalSpace.Opens.coe_disjoint.mpr (disjoint_opensRange_sigmaι W i j hij))

/-- Morphisms `aᵢ : X ×_Y W i ⟶ U` over `X` whose images cover `U` assemble into a surjection
`X ×_Y (∐ W) ⟶ U` over `X`. -/
theorem exists_surjective_sigmaDesc_of_forall_mem_range {U : Scheme.{u}} (g : U ⟶ X)
    {ι : Type u} (W : ι → Scheme.{u}) (wᵢ : ∀ i, W i ⟶ Y) (a : ∀ i, pullback f (wᵢ i) ⟶ U)
    (ha : ∀ i, a i ≫ g = pullback.fst f (wᵢ i)) (hcov : ∀ u, ∃ i, u ∈ Set.range (a i).base) :
    ∃ a' : pullback f (Sigma.desc wᵢ) ⟶ U,
      Surjective a' ∧ a' ≫ g = pullback.fst f (Sigma.desc wᵢ) := by
  have hw : ∀ i, Sigma.ι W i ≫ Sigma.desc wᵢ = wᵢ i := fun i => Sigma.ι_desc _ _
  obtain ⟨hcolim⟩ := nonempty_isColimit_cofanMk_pullback_sigma f W wᵢ _ hw
  have hfac : ∀ i, pullbackMapOfComp f (Sigma.ι W i) (hw i) ≫ hcolim.desc (Cofan.mk U a) = a i :=
    fun i => hcolim.fac (Cofan.mk U a) ⟨i⟩
  refine ⟨hcolim.desc (Cofan.mk U a), ⟨fun u => ?_⟩, hcolim.hom_ext fun ⟨i⟩ => ?_⟩
  · obtain ⟨i, x, hx⟩ := hcov u
    refine ⟨(pullbackMapOfComp f (Sigma.ι W i) (hw i)).base x, ?_⟩
    rwa [← Scheme.Hom.comp_apply, hfac]
  · show pullbackMapOfComp f (Sigma.ι W i) (hw i) ≫ hcolim.desc (Cofan.mk U a) ≫ g =
      pullbackMapOfComp f (Sigma.ι W i) (hw i) ≫ pullback.fst f (Sigma.desc wᵢ)
    rw [← Category.assoc, hfac, pullbackMapOfComp_fst, ha]

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

/-- If `h : X ×_Y V ⟶ U` is a surjective open map onto a quasi-compact `U`, then finitely many of
the base changes of the affine pieces of `V` already map onto `U`. -/
lemma exists_finset_affineCover_forall_mem_range {X Y V U : Scheme.{u}} (f : X ⟶ Y)
    (v : V ⟶ Y) (h : pullback f v ⟶ U) [Surjective h] (hh : IsOpenMap h.base)
    [CompactSpace U] :
    ∃ s : Finset V.affineCover.I₀, ∀ u, ∃ i ∈ s,
      u ∈ Set.range (pullbackMapOfComp f (V.affineCover.f i) (v := v) rfl ≫ h).base := by
  let mi : ∀ i, pullback f (V.affineCover.f i ≫ v) ⟶ pullback f v := fun i =>
    pullbackMapOfComp f (V.affineCover.f i) rfl
  have : ∀ i, IsOpenImmersion (mi i) := fun i => inferInstance
  have hO : ∀ i, IsOpen (Set.range (mi i ≫ h).base) := fun i => by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    exact hh _ (IsOpenImmersion.isOpen_range (mi i))
  have hcov : (Set.univ : Set U) ⊆ ⋃ i, Set.range (mi i ≫ h).base := by
    intro u _
    obtain ⟨p, rfl⟩ := h.surjective u
    obtain ⟨i, x, hx⟩ := V.affineCover.exists_eq ((pullback.snd f v).base p)
    obtain ⟨y, rfl⟩ := mem_range_pullbackMapOfComp f _ rfl hx
    exact Set.mem_iUnion.mpr ⟨i, y, by rw [Scheme.Hom.comp_apply]⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover _ hO hcov
  refine ⟨s, fun u => ?_⟩
  obtain ⟨i, hi, hu⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ u))
  exact ⟨i, hi, hu⟩

/-- **Property (C) with an affine dominating scheme.** Let `f : X ⟶ Y` have property (C) and let
`g : U ⟶ X` be étale with `U` quasi-compact. Then `U` is dominated, by a surjection of schemes
over `X`, by the base change along `f` of an **affine** scheme étale over `Y`.

The dominating scheme of `Stacks.EtaleCohomology.HasPropertyC` is covered by its affine opens,
each of which is again étale over `Y`; base change along `f` carries that covering to a covering
of the dominating base change, and the pieces map to `U` by étale, hence open, maps. As `U` is
quasi-compact finitely many of their images already cover it, and the coproduct of the
corresponding finitely many affine opens is an affine scheme étale over `Y` whose base change
along `f` is the coproduct of the pieces, so the pieces assemble into a surjection onto `U`.

This is the sentence "since `U` is quasi-compact we may replace `W` by finitely many affine
opens, so that `W` is affine" of the second proof of Stacks Project, Tag 04DZ. -/
theorem exists_isAffine_etale_surjective_of_hasPropertyC {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hC : HasPropertyC f) {U : Scheme.{u}} (g : U ⟶ X) (hg : Etale g) [CompactSpace U] :
    ∃ (W : Scheme.{u}) (w : W ⟶ Y), Etale w ∧ IsAffine W ∧
      ∃ a : pullback f w ⟶ U, Surjective a ∧ a ≫ g = pullback.fst f w := by
  classical
  obtain ⟨V, v, hv, h, hhsurj, hhcomm⟩ := hC g hg
  have : Etale h := by
    have : Etale (h ≫ g) := by
      rw [hhcomm]
      infer_instance
    exact Etale.of_comp (f := h) (g := g)
  obtain ⟨s, hs⟩ := exists_finset_affineCover_forall_mem_range f v h h.isOpenMap
  let W : ↥(s : Finset V.affineCover.I₀) → Scheme.{u} := fun i => V.affineCover.X i.1
  let wi : ∀ i, W i ⟶ Y := fun i => V.affineCover.f i.1 ≫ v
  let : IsZariskiLocalAtSource (@Etale.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Etale)
  have : ∀ i, IsAffine (W i) := fun i => inferInstance
  refine ⟨∐ W, Sigma.desc wi,
    IsZariskiLocalAtSource.sigmaDesc (P := @Etale.{u}) (fun i => inferInstance), inferInstance,
    exists_surjective_sigmaDesc_of_forall_mem_range f g W wi
      (fun i => pullbackMapOfComp f (V.affineCover.f i.1) (v := v) rfl ≫ h)
      (fun i => ?_) (fun u => ?_)⟩
  · rw [Category.assoc, hhcomm]
    exact pullbackMapOfComp_fst f (V.affineCover.f i.1) rfl
  · obtain ⟨i, hi, hu⟩ := hs u
    exact ⟨⟨i, hi⟩, hu⟩

end Stacks.EtaleCohomology

end

end
