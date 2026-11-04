module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedEnvelopeFactorization

/-!
# The round trip of a completed retract is an augmentation-compatible endomorphism

Let `(A, I, γ)` and `(A', I', γ')` be divided power rings in which `p` is nilpotent modulo the
divided power ideal, write `Â`, `Â'` for their `p`-adic completions — divided power rings by
[Stacks, Tag 07KD] — and let

`a : Â → Â'`,  `b : Â' → Â`,  `a ∘ b = id_{Â'}`

be the retract of the first assertion of [Stacks, Lemma 60.17.5, Tag 07L5], with `a` the
completion of a divided power morphism `ρ : A → A'`.

The source's proof of [Stacks, Lemma 60.21.4, Tag 07LH] applies its factorization claim to the
endomorphism `b ∘ a` of `Â`, which asks of it two things that the retract alone does not say:
that it is a map of algebras over the base, and that it is **compatible with the augmentation**,
`Crystalline.IsAugmentationCompatible`.  This module proves both from the retract, under one
hypothesis on `ρ` and one on `b`.

## The augmentation

`Crystalline.IsAugmentationCompatible (b ∘ a)` is `(b ∘ a) z - z ∈ Î` for every `z`, which by
[Stacks, Tag 07KD] part (1) says that `b ∘ a` induces the identity on
`Â ⧸ Î = A ⧸ I` — the augmentation target.  The one input is

`hρI : ∀ u : A, ρ u ∈ I' → u ∈ I`,

that is, that `ρ⁻¹(I') = I`, the inclusion `⊆` being the content of `ρ` and `⊇` holding for any
divided power morphism.  Given it, the map `A ⧸ I → A' ⧸ I'` induced by `ρ` is injective, hence
so is the map `Â ⧸ Î → Â' ⧸ Î'` induced by `a`
(`Crystalline.completionToQuotient_eq_of_dpMorphism_apply_eq`), and `a ∘ b = id` then forces
`b ∘ a` to induce the identity: applying `a` to `(b ∘ a) z` gives `a z` on the nose.

So no hypothesis on `b` beyond the retract identity is needed for the augmentation, and none on
`ρ` beyond `hρI` — in particular the compatibility of `b` with the base plays no part.

## The base

For the algebra condition there is nothing to exploit: `a` is far from injective (for the
envelopes of two presentations it is surjective), so `a ((b ∘ a) z) = a z` says nothing about
`(b ∘ a) z` itself, and the retract identity is the only relation between `a` and `b`.  The
compatibility of `b ∘ a` with a base is therefore *equivalent* to the corresponding
compatibility of `b`, and that is what `Crystalline.map_algebraMap_comp_of_retract` assumes: a
ring map `sm : A₀ → A` and `sm' : A₀ → A'` with `ρ ∘ sm = sm'` and
`b (ι' (sm' y)) = ι (sm y)`.  For the two divided power envelopes of [Stacks, Tag 07L5] that
last hypothesis is the compatibility of the level splittings `θ_e` with the structure maps from
`A`, which is recorded by `Crystalline.exists_completedEnvelopeRetract`.

## References

* [Stacks Project, Tag 07KD](https://stacks.math.columbia.edu/tag/07KD)
* [Stacks Project, Lemma 60.17.5, Tag 07L5](https://stacks.math.columbia.edu/tag/07L5)
* [Stacks Project, Lemma 60.21.4, Tag 07LH](https://stacks.math.columbia.edu/tag/07LH)
-/

@[expose] public noncomputable section

namespace Crystalline

open DividedPowers

universe u

section RetractAugmentation

variable {A : Type u} [CommRing A] (I : Ideal A) (γ : DividedPowers I) {A' : Type u}
  [CommRing A'] (I' : Ideal A') (γ' : DividedPowers I') (p : ℕ)
  (hp : IsNilpotent (Ideal.Quotient.mk I (p : A)))
  (hp' : IsNilpotent (Ideal.Quotient.mk I' (p : A')))

/-! ### The reduction of the completion modulo its divided power ideal -/

/-- Two elements of `Â` congruent modulo the completed divided power ideal have the same image
in `A ⧸ I`, the completed ideal being the kernel of the reduction
`Crystalline.completionToQuotient` of [Stacks, Tag 07KD] part (1). -/
public theorem completionToQuotient_eq_of_sub_mem
    {z w : AdicCompletion (pAdicIdeal (A := A) p) A}
    (h : z - w ∈ completionIdeal I p hp) :
    completionToQuotient I p hp z = completionToQuotient I p hp w := by
  exact (RingHom.sub_mem_ker_iff _).1 h

/-- Conversely, two elements of `Â` with the same image in `A ⧸ I` are congruent modulo the
completed divided power ideal. -/
public theorem sub_mem_completionIdeal_of_completionToQuotient_eq
    {z w : AdicCompletion (pAdicIdeal (A := A) p) A}
    (h : completionToQuotient I p hp z = completionToQuotient I p hp w) :
    z - w ∈ completionIdeal I p hp := by
  exact (RingHom.sub_mem_ker_iff _).2 h

/-- **Every element of `Â` is congruent to one coming from `A` modulo the completed divided power
ideal.**  The reduction `Â → A ⧸ I` is surjective by [Stacks, Tag 07KD] part (1) and factors the
reduction of `A`, so a preimage in `A` of the class of `z` differs from `z` by an element of the
completed ideal. -/
public theorem exists_sub_algebraMap_mem_completionIdeal
    (z : AdicCompletion (pAdicIdeal (A := A) p) A) :
    ∃ u : A, z - algebraMap A (AdicCompletion (pAdicIdeal (A := A) p) A) u ∈
      completionIdeal I p hp := by
  obtain ⟨u, hu⟩ := Ideal.Quotient.mk_surjective (completionToQuotient I p hp z)
  refine ⟨u, sub_mem_completionIdeal_of_completionToQuotient_eq I p hp ?_⟩
  rw [completionToQuotient_algebraMap I p hp u, hu]

/-- A divided power morphism between the two completions carries the completed divided power
ideal into the completed divided power ideal, so it preserves congruence modulo them. -/
public theorem sub_mem_completionIdeal_map
    (a : DPMorphism (completedDividedPowers I γ p hp).1 (completedDividedPowers I' γ' p hp').1)
    {z w : AdicCompletion (pAdicIdeal (A := A) p) A} (h : z - w ∈ completionIdeal I p hp) :
    a.toRingHom z - a.toRingHom w ∈ completionIdeal I' p hp' := by
  rw [← map_sub]
  exact a.ideal_comp (Ideal.mem_map_of_mem _ h)

/-! ### The map induced on the augmentation targets by the completion of `ρ` -/

variable (a : DPMorphism (completedDividedPowers I γ p hp).1
    (completedDividedPowers I' γ' p hp').1) (rho : γ.DPMorphism γ')

/-- **The reduction of `a z` is the reduction of `ρ u` for any `u : A` representing `z`.**  This
is the statement that the map `A ⧸ I → A' ⧸ I'` induced by `ρ` is the map `Â ⧸ Î → Â' ⧸ Î'`
induced by `a`, read without naming either induced map: `a` preserves congruence modulo the
completed ideals, and on the image of `A` it is `ρ`. -/
public theorem completionToQuotient_dpMorphism_apply
    (haρ : ∀ x : A, a.toRingHom (algebraMap A (AdicCompletion (pAdicIdeal (A := A) p) A) x) =
      algebraMap A' (AdicCompletion (pAdicIdeal (A := A') p) A') (rho.toRingHom x))
    {z : AdicCompletion (pAdicIdeal (A := A) p) A} {u : A}
    (hu : z - algebraMap A (AdicCompletion (pAdicIdeal (A := A) p) A) u ∈
      completionIdeal I p hp) :
    completionToQuotient I' p hp' (a.toRingHom z) =
      Ideal.Quotient.mk I' (rho.toRingHom u) := by
  rw [completionToQuotient_eq_of_sub_mem I' p hp'
      (sub_mem_completionIdeal_map I γ I' γ' p hp hp' a hu), haρ u,
    completionToQuotient_algebraMap I' p hp' (rho.toRingHom u)]

/-- **The map `Â ⧸ Î → Â' ⧸ Î'` induced by `a` is injective**, provided the divided power ideal
`I` is the full preimage of `I'` under `ρ`.

The inclusion `I ⊆ ρ⁻¹(I')` holds for any divided power morphism; the hypothesis `hρI` is the
other one, and it is what makes the map `A ⧸ I → A' ⧸ I'` induced by `ρ` injective.  Since every
element of `Â` is congruent to one from `A` and `a` is `ρ` there, injectivity transfers. -/
public theorem completionToQuotient_eq_of_dpMorphism_apply_eq
    (haρ : ∀ x : A, a.toRingHom (algebraMap A (AdicCompletion (pAdicIdeal (A := A) p) A) x) =
      algebraMap A' (AdicCompletion (pAdicIdeal (A := A') p) A') (rho.toRingHom x))
    (hρI : ∀ u : A, rho.toRingHom u ∈ I' → u ∈ I)
    {z w : AdicCompletion (pAdicIdeal (A := A) p) A}
    (h : completionToQuotient I' p hp' (a.toRingHom z) =
      completionToQuotient I' p hp' (a.toRingHom w)) :
    completionToQuotient I p hp z = completionToQuotient I p hp w := by
  obtain ⟨u, hu⟩ := exists_sub_algebraMap_mem_completionIdeal I p hp z
  obtain ⟨v, hv⟩ := exists_sub_algebraMap_mem_completionIdeal I p hp w
  rw [completionToQuotient_dpMorphism_apply I γ I' γ' p hp hp' a rho haρ hu,
    completionToQuotient_dpMorphism_apply I γ I' γ' p hp hp' a rho haρ hv,
    Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← map_sub] at h
  rw [completionToQuotient_eq_of_sub_mem I p hp hu,
    completionToQuotient_eq_of_sub_mem I p hp hv,
    completionToQuotient_algebraMap I p hp u, completionToQuotient_algebraMap I p hp v,
    Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact hρI (u - v) h

/-! ### The round trip -/

variable (b : DPMorphism (completedDividedPowers I' γ' p hp').1
  (completedDividedPowers I γ p hp).1)

/-- **The round trip `b ∘ a` of a completed retract is compatible with the augmentation.**

This is the hypothesis `Crystalline.IsAugmentationCompatible` that the factorization of
[Stacks, Lemma 60.21.4, Tag 07LH] asks of its endomorphism `ρ` of `D`, proved for the
endomorphism `b ∘ a` of the first assertion of [Stacks, Lemma 60.17.5, Tag 07L5].

The proof is the injectivity of the map induced by `a` on the augmentation targets,
`Crystalline.completionToQuotient_eq_of_dpMorphism_apply_eq`, together with `a ∘ b = id`: the
latter gives `a ((b ∘ a) z) = a z` outright, and the former turns that into
`(b ∘ a) z ≡ z` modulo the completed divided power ideal, which is the assertion.

No compatibility of `b` with a base is used, and the only hypothesis on `ρ` is that `I` is the
full preimage of `I'`. -/
public theorem isAugmentationCompatible_comp_of_retract
    (hab : a.comp b = DPMorphism.id (completedDividedPowers I' γ' p hp').1)
    (haρ : ∀ x : A, a.toRingHom (algebraMap A (AdicCompletion (pAdicIdeal (A := A) p) A) x) =
      algebraMap A' (AdicCompletion (pAdicIdeal (A := A') p) A') (rho.toRingHom x))
    (hρI : ∀ u : A, rho.toRingHom u ∈ I' → u ∈ I) :
    IsAugmentationCompatible (b.comp a) := by
  intro z
  refine sub_mem_completionIdeal_of_completionToQuotient_eq I p hp
    (completionToQuotient_eq_of_dpMorphism_apply_eq I γ I' γ' p hp hp' a rho haρ hρI ?_)
  have hid : a.toRingHom (b.toRingHom (a.toRingHom z)) = a.toRingHom z :=
    congrArg (fun r : DPMorphism (completedDividedPowers I' γ' p hp').1
      (completedDividedPowers I' γ' p hp').1 ↦ r (a.toRingHom z)) hab
  exact congrArg (completionToQuotient I' p hp') hid

variable {A₀ : Type u} [CommRing A₀] (sm : A₀ →+* A) (sm' : A₀ →+* A')

/-- **The round trip `b ∘ a` is a map over the base as soon as `b` is.**

If `ρ ∘ sm = sm'` for ring maps `sm : A₀ → A`, `sm' : A₀ → A'` from a base — for the two divided
power envelopes of [Stacks, Lemma 60.17.5, Tag 07L5] this is the compatibility of the canonical
map `ρ` of [Stacks, Tag 07HB] with the structure maps — and if `b` carries the image of `sm'` in
`Â'` to the image of `sm` in `Â`, then `b ∘ a` fixes the image of `sm`.

The hypothesis on `b` cannot be dropped: `a ∘ b = id` gives no information about `b` off the
image of `a`, and `a` is not injective, so `a ((b ∘ a) ι(sm y)) = a (ι (sm y))` — which is all
the retract identity yields — does not identify `(b ∘ a) (ι (sm y))` with `ι (sm y)`. -/
public theorem map_algebraMap_comp_of_retract
    (haρ : ∀ x : A, a.toRingHom (algebraMap A (AdicCompletion (pAdicIdeal (A := A) p) A) x) =
      algebraMap A' (AdicCompletion (pAdicIdeal (A := A') p) A') (rho.toRingHom x))
    (hsm : rho.toRingHom.comp sm = sm')
    (hb : ∀ y : A₀, b.toRingHom
        (algebraMap A' (AdicCompletion (pAdicIdeal (A := A') p) A') (sm' y)) =
      algebraMap A (AdicCompletion (pAdicIdeal (A := A) p) A) (sm y)) (y : A₀) :
    (b.comp a).toRingHom
        (algebraMap A (AdicCompletion (pAdicIdeal (A := A) p) A) (sm y)) =
      algebraMap A (AdicCompletion (pAdicIdeal (A := A) p) A) (sm y) := by
  show b.toRingHom (a.toRingHom
    (algebraMap A (AdicCompletion (pAdicIdeal (A := A) p) A) (sm y))) = _
  rw [haρ (sm y), show rho.toRingHom (sm y) = sm' y from
    congrArg (fun r : A₀ →+* A' ↦ r y) hsm, hb y]

end RetractAugmentation

end Crystalline

end
