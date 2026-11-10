module

public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.AwayRing
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Local rings of a degreewise localization of graded rings

Let `φ : 𝒜 →+*ᵍ ℬ` be a degreewise localization away from a degree-zero element `g`
(`Stacks.GradedLocalization.IsAwayDegreewise`). Let `J` be a prime ideal of `ℬ` and `I = φ⁻¹ J`.
Then the induced map of local rings `A_I ⟶ B_J` is an isomorphism.

Geometrically: inverting `g` does not change the local ring at a point where `g` is invertible,
and every point of `Spec ℬ` is such a point.

## Main results

* `Stacks.GradedLocalization.IsAwayDegreewise.bijective_localRingHom`: the map of local rings
  `Localization.localRingHom` is bijective.
-/

@[expose] public section

open HomogeneousLocalization

universe u

namespace Stacks.GradedLocalization

variable {A B : Type u} {σ τ : Type*}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  {φ : 𝒜 →+*ᵍ ℬ} {g : A}

namespace IsAwayDegreewise

variable (I : Ideal A) [I.IsPrime] (J : Ideal B) [J.IsPrime]

omit [AddSubgroupClass σ A] [AddSubgroupClass τ B] [GradedRing 𝒜] [GradedRing ℬ] in
/-- The image of `g` avoids every prime ideal, being a unit. -/
public theorem map_mem_primeCompl (h : IsAwayDegreewise φ g) : φ g ∈ J.primeCompl :=
  fun hmem => Ideal.IsPrime.ne_top ‹_› (Ideal.eq_top_of_isUnit_mem J hmem h.isUnit_map)

omit [AddSubgroupClass σ A] [AddSubgroupClass τ B] [GradedRing 𝒜] [GradedRing ℬ] in
/-- An element of `𝒜` whose image is a power of `φ g` times something outside `J` lies outside
`I = φ⁻¹ J`. -/
public theorem mem_primeCompl_of_map_eq (h : IsAwayDegreewise φ g)
    (hIJ : I = J.comap φ.toRingHom) {s : A} {m : ℕ} {t : B} (ht : t ∈ J.primeCompl)
    (hs : φ s = φ g ^ m * t) : s ∈ I.primeCompl := by
  subst hIJ
  change φ s ∉ J
  rw [hs]
  exact J.primeCompl.mul_mem (J.primeCompl.pow_mem (h.map_mem_primeCompl J) m) ht

omit [AddSubgroupClass σ A] [AddSubgroupClass τ B] [GradedRing 𝒜] [GradedRing ℬ] in
/-- `g` itself lies outside `I = φ⁻¹ J`. -/
public theorem mem_primeCompl (h : IsAwayDegreewise φ g) (hIJ : I = J.comap φ.toRingHom) :
    g ∈ I.primeCompl :=
  h.mem_primeCompl_of_map_eq I J hIJ (h.map_mem_primeCompl J) (by rw [pow_zero, one_mul])

/-- Multiplying an element outside `I = f⁻¹ J` by a power of `g`, with `f g` a unit, keeps it
outside `I`. -/
private theorem pow_mul_mem_primeCompl {f : A →+* B} (hg : IsUnit (f g))
    (hIJ : I = J.comap f) (k : ℕ) {s : A} (hs : s ∈ I.primeCompl) : g ^ k * s ∈ I.primeCompl := by
  subst hIJ
  intro hmem
  simp only [SetLike.mem_coe, Ideal.mem_comap, map_mul, map_pow] at hmem
  exact hs ((Ideal.IsPrime.mem_or_mem ‹_› hmem).resolve_left fun h =>
    Ideal.IsPrime.ne_top ‹_› (Ideal.eq_top_of_isUnit_mem J h (hg.pow k)))

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- **The comparison of local rings is surjective.** -/
public theorem surjective_localRingHom (h : IsAwayDegreewise φ g)
    (hIJ : I = J.comap φ.toRingHom) :
    Function.Surjective (Localization.localRingHom I J φ.toRingHom hIJ) := by
  intro z
  induction z using Localization.induction_on with
  | H x =>
    obtain ⟨b, t⟩ := x
    obtain ⟨k, a, hak⟩ := h.exists_pow_mul_eq_map b
    obtain ⟨m, s, hms⟩ := h.exists_pow_mul_eq_map (t : B)
    have hs : s ∈ I.primeCompl := h.mem_primeCompl_of_map_eq I J hIJ t.2 hms
    refine ⟨Localization.mk (a * g ^ m)
      ⟨g ^ k * s, pow_mul_mem_primeCompl I J h.isUnit_map hIJ k hs⟩, ?_⟩
    rw [Localization.localRingHom_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [OneMemClass.coe_one, one_mul, map_mul, map_pow, GradedRingHom.coe_toRingHom,
      hak, hms]
    ring

/-- **The comparison of local rings is injective.** -/
public theorem injective_localRingHom (h : IsAwayDegreewise φ g)
    (hIJ : I = J.comap φ.toRingHom) :
    Function.Injective (Localization.localRingHom I J φ.toRingHom hIJ) := by
  have key : ∀ (a a' : A) (p p' : I.primeCompl),
      Localization.localRingHom I J φ.toRingHom hIJ (Localization.mk a p) =
        Localization.localRingHom I J φ.toRingHom hIJ (Localization.mk a' p') →
      (Localization.mk a p : Localization.AtPrime I) = Localization.mk a' p' := by
    intro a a' p p' hzw
    rw [Localization.localRingHom_mk, Localization.localRingHom_mk,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists] at hzw
    obtain ⟨c, hc⟩ := hzw
    obtain ⟨m, s, hms⟩ := h.exists_pow_mul_eq_map (c : B)
    have hs : s ∈ I.primeCompl := h.mem_primeCompl_of_map_eq I J hIJ c.2 hms
    have hzero : φ (s * ((p' : A) * a - (p : A) * a')) = 0 := by
      have hc' : (c : B) * (φ (p' : A) * φ a) = (c : B) * (φ (p : A) * φ a') := hc
      simp only [map_mul, map_sub, hms]
      grind
    obtain ⟨j, hj⟩ := h.exists_pow_mul_eq_zero hzero
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨⟨g ^ j * s, pow_mul_mem_primeCompl I J h.isUnit_map hIJ j hs⟩, by grind⟩
  intro z w
  induction z using Localization.induction_on with
  | H x =>
    induction w using Localization.induction_on with
    | H y => exact key x.1 y.1 x.2 y.2

/-- **The local rings of a degreewise localization agree with those of its source.** For a prime
`J` of `ℬ` and `I = φ⁻¹ J`, the induced map `A_I ⟶ B_J` is bijective. -/
public theorem bijective_localRingHom (h : IsAwayDegreewise φ g)
    (hIJ : I = J.comap φ.toRingHom) :
    Function.Bijective (Localization.localRingHom I J φ.toRingHom hIJ) :=
  ⟨h.injective_localRingHom I J hIJ, h.surjective_localRingHom I J hIJ⟩

end IsAwayDegreewise

end Stacks.GradedLocalization

end
