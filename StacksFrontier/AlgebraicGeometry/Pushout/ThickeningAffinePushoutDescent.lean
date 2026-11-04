module

public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEtaleDescent
public import StacksFrontier.AlgebraicGeometry.C1573Port.Pushout.ThickeningAffineGluingRelation

/-!
# Being a thickening-and-affine pushout descends along étale surjections

Let `k : Z ⟶ Z'` be a thickening and `g : Z ⟶ Z₂` an affine morphism of schemes, with a
commutative square `k ≫ u₁ = g ≫ u₂` into a scheme `W` whose leg `u₂` is a thickening. If after
base change along an étale surjective morphism `W' ⟶ W` the square becomes a pushout, then it was
a pushout already.

The comparison morphism `m : Z' ⨿_Z Z₂ ⟶ W` out of the pushout of Stacks 07RT becomes an
isomorphism after the base change, because étale base change preserves the pushout (Stacks 07RX,
`Stacks.Pushout.C1573.isPushout_of_etale_of_isPullback`). It is therefore étale by fppf descent of
étaleness, and an étale morphism through which a thickening factors as a thickening is an
isomorphism.

## Main results

* `Stacks.Pushout.isPushout_of_isPushout_of_etale_surjective`.

## References

* [Stacks Project, Tag 07RT](https://stacks.math.columbia.edu/tag/07RT)
* [Stacks Project, Tag 07RX](https://stacks.math.columbia.edu/tag/07RX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Thickenings

universe u

namespace Stacks.Pushout

open _root_.AlgebraicGeometry

/-- A pullback square over `ρ` and `inc ≫ m` gives a pullback square over the base change of `m`. -/
private theorem exists_isPullback_lift {Q W W' E Zi : Scheme.{u}} (m : Q ⟶ W) (ρ : W' ⟶ W)
    (inc : Zi ⟶ Q) {v : E ⟶ W'} {q : E ⟶ Zi} (h : IsPullback v q ρ (inc ≫ m)) :
    ∃ u : E ⟶ pullback m ρ, u ≫ pullback.fst m ρ = q ≫ inc ∧ u ≫ pullback.snd m ρ = v ∧
      IsPullback u q (pullback.fst m ρ) inc := by
  have hu := pullback.lift_fst (q ≫ inc) v (by rw [Category.assoc, h.w])
  have hv := pullback.lift_snd (q ≫ inc) v (by rw [Category.assoc, h.w])
  exact ⟨_, hu, hv, IsPullback.of_right (by rwa [hv]) hu
    (IsPullback.of_hasPullback m ρ).flip⟩

/-- **A thickening-and-affine square which is a pushout étale locally is a pushout.** -/
theorem isPushout_of_isPushout_of_etale_surjective {Z Z' Z₂ W W' E₀ E₁ E₂ : Scheme.{u}}
    {k : Z ⟶ Z'} {g : Z ⟶ Z₂} {u₁ : Z' ⟶ W} {u₂ : Z₂ ⟶ W}
    (hk : IsThickening k) [IsAffineHom g] (hu₂ : IsThickening u₂) (hw : k ≫ u₁ = g ≫ u₂)
    (ρ : W' ⟶ W) [Etale ρ] [Surjective ρ]
    {v₁ : E₁ ⟶ W'} {v₂ : E₂ ⟶ W'} {q₁ : E₁ ⟶ Z'} {q₂ : E₂ ⟶ Z₂}
    (h₁ : IsPullback v₁ q₁ ρ u₁) (h₂ : IsPullback v₂ q₂ ρ u₂)
    {kE : E₀ ⟶ E₁} {gE : E₀ ⟶ E₂} {q₀ : E₀ ⟶ Z}
    (hc₁ : IsPullback kE q₀ q₁ k) (hc₂ : IsPullback gE q₀ q₂ g)
    (hE : IsPushout kE gE v₁ v₂) : IsPushout k g u₁ u₂ := by
  have : HasPushout k g := hasPushout_of_isThickening_of_isAffineHom' k g hk
  have hQ := IsPushout.of_hasPushout k g
  set m := pushout.desc u₁ u₂ hw with hm
  have hm₁ : pushout.inl k g ≫ m = u₁ := pushout.inl_desc _ _ _
  have hm₂ : pushout.inr k g ≫ m = u₂ := pushout.inr_desc _ _ _
  -- the base change of the pushout along `ρ`
  set π := pullback.fst m ρ with hπ
  set m' := pullback.snd m ρ with hm'
  have hright : IsPullback m' π ρ m := (IsPullback.of_hasPullback m ρ).flip
  have : Etale π := MorphismProperty.of_isPullback (IsPullback.of_hasPullback m ρ).flip
    inferInstance
  obtain ⟨u₁', hu₁'π, hu₁'m, hp₁⟩ := exists_isPullback_lift m ρ (pushout.inl k g) (by rwa [hm₁])
  obtain ⟨u₂', hu₂'π, hu₂'m, hp₂⟩ := exists_isPullback_lift m ρ (pushout.inr k g) (by rwa [hm₂])
  have hwE : kE ≫ u₁' = gE ≫ u₂' := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hu₁'π, hu₂'π, ← Category.assoc, hc₁.w,
        Category.assoc, pushout.condition, ← Category.assoc, ← hc₂.w, Category.assoc]
    · rw [Category.assoc, Category.assoc, hu₁'m, hu₂'m, hE.w]
  have hE' : IsPushout kE gE u₁' u₂' :=
    C1573.isPushout_of_etale_of_isPullback hk hQ π hp₁ hp₂ hc₁ hc₂ hwE
  -- the base change of `m` is an isomorphism, since both squares are pushouts of the same span
  have hm'iso : IsIso m' := by
    have h := hE'.isoIsPushout _ _ hE
    have : (hE'.isoIsPushout _ _ hE).hom = m' := by
      refine hE'.hom_ext ?_ ?_
      · rw [IsPushout.inl_isoIsPushout_hom, hu₁'m]
      · rw [IsPushout.inr_isoIsPushout_hom, hu₂'m]
    rw [← this]
    infer_instance
  -- hence `m` is étale, by fppf descent along `ρ`
  have : Etale m' := inferInstance
  have hρQ : ((@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation :
      MorphismProperty Scheme.{u})) ρ :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have :=
    AlgebraicGeometry.Space.etale_descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation
  have hme : Etale m :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Etale)
      (Q := (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}))
      hright hρQ ‹Etale m'›
  have hinr : IsThickening (pushout.inr k g) := isThickening_of_isPushout_of_isThickening hQ hk
  have hcomp : IsThickening (pushout.inr k g ≫ m) := by rw [hm₂]; exact hu₂
  have : IsIso m := C1573.isIso_of_etale_of_isThickening_comp m _ hcomp hinr
  exact hQ.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (asIso m) (by simp) (by simp)
    (by simpa using hm₁) (by simpa using hm₂)

end Stacks.Pushout
