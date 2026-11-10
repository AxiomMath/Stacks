module

public import StacksFrontier.Deformation.Artin.FormalObject.SquareZeroTowerLiftClasses
public import StacksFrontier.Deformation.Artin.Infinitesimal.RelativeLiftClasses

/-!
# Lift classes over the limit of a square-zero tower

Let `⋯ → R₁ → R₀ = A` be a tower of square-zero thickenings in the site, under a fixed augmented
ring, let `x` be an object over `Spec A` of a category fibred in groupoids satisfying (RS*), and
let `bₙ` be a system of lift classes of `x` over the levels `Rₙ`, compatible under the transition
maps. Assume that the lift classes of `x` over `A[∏ Mₙ]` are, through the projections, the
products of those over the `A[Mₙ]`, and that `x` lifts to the ring `R̃` of sequences with a
common base. Then some lift class of `x` over `R = lim Rₙ` restricts to every `bₙ`.

This is the conclusion of the proof of Stacks 0CYF. A lift class over `R̃` is first corrected so
that it restricts to the `bₙ` (`Deformation.Artin.SquareZeroTower.exists_classes_eq`); its
restriction to `A[∏ Mₙ]` is then trivial, and since `lim Rₙ = R̃ ×_{A[∏ Mₙ]} A` with
`R̃ → A[∏ Mₙ]` surjective with square-zero kernel, condition (RS*) over `A[∏ Mₙ]`
(`Deformation.Artin.AugmentedSiteRing.exists_classes_map_eq_of_isPullback`) descends it to the
limit.

## Main definitions

* `Deformation.Artin.SquareZeroTower.limitRing` — `lim Rₙ`, as an augmented ring under `R`.

## Main results

* `Deformation.Artin.SquareZeroTower.isPullback_limit` — `lim Rₙ = R̃ ×_{A[∏ Mₙ]} A`.
* `Deformation.Artin.SquareZeroTower.exists_limit_classes` — the lift class over the limit.

## References

* [Stacks Project, Tag 0CYF](https://stacks.math.columbia.edu/tag/0CYF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace Deformation.Artin.SquareZeroTower

open BasedSiteRing

section Ring

variable {R : ℕ → Type u} [∀ n, CommRing (R n)] (f : ∀ n, R (n + 1) →+* R n)
  (hf : ∀ n, Function.Surjective (f n)) (hsq : ∀ n, RingHom.ker (toBase f n) ^ 2 = ⊥)

/-- The inclusion `lim Rₙ → R̃`. -/
public def limitIncl : limit f →+* sameBase f :=
  Subring.inclusion (limit_le_sameBase f)

/-- The projection `lim Rₙ → R₀`. -/
public def limitBase : limit f →+* R 0 :=
  (Pi.evalRingHom R 0).comp (limit f).subtype

/-- The base of a sequence in `lim Rₙ`, viewed in `R̃`, is its projection to `R₀`. -/
theorem base_comp_limitIncl : (base f).comp (limitIncl f) = limitBase f := rfl

/-- On `lim Rₙ`, the difference map `R̃ → A[∏ Mₙ]` is the projection to `A` followed by the
inclusion `A → A[∏ Mₙ]`. -/
theorem difference_comp_limitIncl :
    (difference f hf hsq).comp (limitIncl f) =
      (TrivSqZeroExt.inlHom (R 0) (kernelProduct f hf hsq)).comp (limitBase f) :=
  RingHom.ext fun r => (difference_eq_inl_iff f hf hsq (limitIncl f r)).2 r.2

/-- **`lim Rₙ = R̃ ×_{A[∏ Mₙ]} A`.** The inverse limit is the fibre product of the difference map
`R̃ → A[∏ Mₙ]` and the inclusion `A → A[∏ Mₙ]`. -/
public theorem isPullback_limit :
    IsPullback (CommRingCat.ofHom (limitBase f)) (CommRingCat.ofHom (limitIncl f))
      (CommRingCat.ofHom (TrivSqZeroExt.inlHom (R 0) (kernelProduct f hf hsq)))
      (CommRingCat.ofHom (difference f hf hsq)) := by
  apply IsPullback.of_map_of_faithful (forget CommRingCat)
  apply (CategoryTheory.Limits.Types.isPullback_iff _ _ _ _).2
  refine ⟨?_, ?_, ?_⟩
  · rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    exact CommRingCat.hom_ext (difference_comp_limitIncl f hf hsq).symm
  · intro r s h
    have h₂ : ((limitIncl f r : sameBase f) : ∀ n, R n) = limitIncl f s :=
      congrArg Subtype.val h.2
    exact Subtype.ext h₂
  · intro a r h
    have h' : difference f hf hsq r = TrivSqZeroExt.inl a := h.symm
    have h₀ : base f r = a := congrArg TrivSqZeroExt.fst h'
    rw [← h₀] at h'
    exact ⟨⟨r, (difference_eq_inl_iff f hf hsq r).1 h'⟩, h₀, rfl⟩

end Ring

section Rings

variable {R : ℕ → Type u} [∀ n, CommRing (R n)] (f : ∀ n, R (n + 1) →+* R n)
  (hf : ∀ n, Function.Surjective (f n)) (hsq : ∀ n, RingHom.ker (toBase f n) ^ 2 = ⊥)
  {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {toS : Spec (.of (R 0)) ⟶ S} {hA : B.Contains (Spec (.of (R 0)))}
  (Λ : AugmentedSiteRing (R 0) B S hS toS hA) (β : ∀ n, Λ.ring →+* R n)
  (hβ : ∀ n, (f n).comp (β (n + 1)) = β n) (hβ0 : β 0 = Λ.aug)
  (hR : ∀ n, B.Contains (Spec (.of (R n))))

include hR in
/-- The spectrum of `lim Rₙ` lies in the site. -/
public theorem contains_limit : B.Contains (Spec (.of (limit f))) :=
  Scheme.size_Spec_lt_of_subring B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit (limit f)
    (contains_spec_pi B hR)

/-- The map from `R` to `lim Rₙ`, `r ↦ (β₀ r, β₁ r, …)`. -/
public def limitBaseMap : Λ.ring →+* limit f :=
  (RingHom.pi β).codRestrict (limit f) fun l n => by
    change f n (β (n + 1) l) = β n l
    rw [← RingHom.comp_apply, hβ]

/-- The inverse limit `lim Rₙ`, as an augmented ring under `R`. -/
public def limitRing : BasedSiteRing (R 0) B S hS toS hA Λ where
  toAugmentedSiteRing := AugmentedSiteRing.ofRing Λ (.of (limit f))
    (contains_limit f hR) (limitBase f) (limitBaseMap f Λ β hβ) (by
      ext l
      change β 0 l = Λ.aug l
      rw [hβ0])
  base := limitBaseMap f Λ β hβ
  fac := by
    ext l
    change β 0 l = Λ.aug l
    rw [hβ0]
  structure_fac := rfl

/-- The inclusion `lim Rₙ → R̃`. -/
public def limitMap :
    BasedSiteRing.RingMap (limitRing f Λ β hβ hβ0 hR) (sameBaseRing f Λ β hβ hβ0 hR) where
  hom := limitIncl f
  aug_fac := rfl
  base_fac := rfl

/-- The projection `lim Rₙ → R₀`. -/
public def limitAugMap :
    BasedSiteRing.RingMap (limitRing f Λ β hβ hβ0 hR) (level f Λ β hβ hβ0 hR 0) where
  hom := limitBase f
  aug_fac := rfl
  base_fac := by
    ext l
    rfl

/-- The projection `lim Rₙ → Rₙ`. -/
public abbrev limitProj (n : ℕ) :
    BasedSiteRing.RingMap (limitRing f Λ β hβ hβ0 hR) (level f Λ β hβ hβ0 hR n) :=
  (projMap f Λ β hβ hβ0 hR n).comp (limitMap f Λ β hβ hβ0 hR)

/-- The square of augmented rings `lim Rₙ → R̃ → A[∏ Mₙ]`, `lim Rₙ → A → A[∏ Mₙ]` commutes. -/
theorem inlMap_comp_limitAugMap :
    (inlMap f hf hsq Λ β hβ hβ0 hR).comp (limitAugMap f Λ β hβ hβ0 hR) =
      (differenceMap f hf hsq Λ β hβ hβ0 hR).comp (limitMap f Λ β hβ hβ0 hR) :=
  RingMap.ext (difference_comp_limitIncl f hf hsq).symm

variable {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} {x : X}
  {hx : p.obj x = algebraOver (R 0) B S hS toS hA} {hp : p.IsFiberedInGroupoids}

/-- **The lift over the limit, in the proof of Stacks 0CYF.** Assume (RS*) and that the lift
classes of `x` over `A[∏ Mₙ]` are, through the projections, the products of the lift classes over
the `A[Mₙ]`. Given a lift class over `R̃` and a system of lift classes `bₙ` over the levels `Rₙ`,
compatible under the transition maps, some lift class over `lim Rₙ` restricts to every `bₙ`. -/
public theorem exists_limit_classes (hRS : SatisfiesRSStar B S hS p hp)
    (hQ : Function.Bijective fun d : classes p x hx (productSquareZero f hf hsq Λ hR) =>
      fun n => BasedSiteRing.map p x hx hp (squareZeroProj f hf hsq Λ hR n) d)
    (ξ₀ : classes p x hx (sameBaseRing f Λ β hβ hβ0 hR))
    (b : ∀ n, classes p x hx (level f Λ β hβ hβ0 hR n))
    (hb : ∀ n, BasedSiteRing.map p x hx hp (transition f Λ β hβ hβ0 hR n) (b (n + 1)) = b n) :
    ∃ ξ : classes p x hx (limitRing f Λ β hβ hβ0 hR),
      ∀ n, BasedSiteRing.map p x hx hp (limitProj f Λ β hβ hβ0 hR n) ξ = b n := by
  obtain ⟨η, hη, hδ⟩ := exists_classes_eq f hf hsq Λ β hβ hβ0 hR hRS hQ ξ₀ b hb
  have hpb : IsPullback
      ((BigFppfOver.toScheme B S hS).map (limitAugMap f Λ β hβ hβ0 hR).toHom.right).appTop
      ((BigFppfOver.toScheme B S hS).map (limitMap f Λ β hβ hβ0 hR).toHom.right).appTop
      (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom (R 0) (kernelProduct f hf hsq)))).appTop
      (Spec.map (CommRingCat.ofHom (difference f hf hsq))).appTop := by
    apply (isPullback_limit f hf hsq).of_iso'
      (Scheme.ΓSpecIso (limitRing f Λ β hβ hβ0 hR).ring)
      (Scheme.ΓSpecIso (level f Λ β hβ hβ0 hR 0).ring)
      (Scheme.ΓSpecIso (sameBaseRing f Λ β hβ hβ0 hR).ring)
      (Scheme.ΓSpecIso (productSquareZero f hf hsq Λ hR).ring) <;>
      exact (Scheme.ΓSpecIso_naturality _).symm
  obtain ⟨ξ, hξ, -⟩ := AugmentedSiteRing.exists_classes_map_eq_of_isPullback hp hRS
    (differenceMap f hf hsq Λ β hβ hβ0 hR).toHom (difference f hf hsq) rfl
    (inlMap f hf hsq Λ β hβ hβ0 hR).toHom (TrivSqZeroExt.inlHom (R 0) (kernelProduct f hf hsq)) rfl
    ((differenceMap f hf hsq Λ β hβ hβ0 hR).comp (limitMap f Λ β hβ hβ0 hR)).toHom
    ((difference f hf hsq).comp (limitIncl f)) rfl
    (limitMap f Λ β hβ hβ0 hR).toHom (limitAugMap f Λ β hβ hβ0 hR).toHom
    (RingMap.toHom_comp _ _).symm
    (by rw [← RingMap.toHom_comp, inlMap_comp_limitAugMap])
    hpb (difference_surjective f hf hsq) (ker_difference_sq f hf hsq) η (b 0) hδ
  refine ⟨ξ, fun n => ?_⟩
  rw [map_comp]
  change BasedSiteRing.map p x hx hp (projMap f Λ β hβ hβ0 hR n)
    (AugmentedSiteRing.map p x hx hp (limitMap f Λ β hβ hβ0 hR).toHom ξ) = b n
  rw [hξ, hη]

end Rings

end Deformation.Artin.SquareZeroTower
