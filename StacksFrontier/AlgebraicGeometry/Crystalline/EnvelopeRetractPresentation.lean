module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedRetractAugmentation
public import StacksFrontier.AlgebraicGeometry.Crystalline.EnvelopeRetract

/-!
# The choice of presentation and the augmentations in the retract of Tag 07L5

In Situation [Stacks, Tag 07MD] let `A → P' → C` be ring maps with `A → P'` smooth and
`P' → C` surjective with kernel `J'`, and let `D'` be the `p`-adic completion of
`D_{P', γ}(J')`.

This module completes the first assertion of [Stacks, Lemma 60.17.5, Tag 07L5]: *there are a
choice of the data `A → P → C` as above and homomorphisms of divided power `A`-algebras*
`a : D → D'`, `b : D' → D` *compatible with the maps `D → C` and `D' → C` such that
`a ∘ b = id_{D'}`.*

`Crystalline.exists_completedEnvelopeRetract` of
`StacksFrontier.AlgebraicGeometry.Crystalline.EnvelopeRetract` produces `a`, `b` and
`a ∘ b = id` for an *arbitrary* surjection `q : P ↠ P'` of `A`-algebras.  Two clauses of the
source's assertion are not in it, and both are here:

* **the choice of the data.**  The source's proof opens "Choose a polynomial algebra
  `P = A[y_1, …, y_m]` over `A` and a surjection `P → P'`", which exists because `A → P'` is
  smooth, hence of finite presentation; `A → P → C` is then the composition.  That is
  `Crystalline.exists_mvPolynomial_surjection_of_smooth`.
* **the compatibility with the maps to `C`.**  The augmentation of a completed envelope is
  `Crystalline.completedEnvelopeAugmentation`, the composite of the reduction
  `D → D ⧸ I_D` of [Stacks, Tag 07KD] part (1) with the canonical identifications
  `D ⧸ I_D ≅ P ⧸ J ≅ C`.  Compatibility of `a` with the augmentations is
  `Crystalline.completedEnvelopeAugmentation_comp_of_dpMorphism`, and that of `b` then follows
  from `a ∘ b = id`.

## Main definitions

* `Crystalline.completedEnvelopeAugmentation` — the augmentation `D → C` of the `p`-adic
  completion of the divided power envelope of a surjective presentation.

## Main results

* `Crystalline.exists_mvPolynomial_surjection_of_smooth` — the choice of the polynomial
  presentation above a smooth one.
* `Crystalline.completedEnvelopeAugmentation_algebraMap` — the augmentation is `P → C` on the
  image of the presentation.
* `Crystalline.completedEnvelopeAugmentation_comp_of_dpMorphism` — a divided power morphism of
  completed envelopes lying over the canonical map `ρ` of [Stacks, Tag 07HB] is compatible with
  the two augmentations.
* `Crystalline.exists_presentation_completedEnvelopeRetract` — **the first assertion of
  [Stacks, Lemma 60.17.5, Tag 07L5] under exactly the source's hypotheses.**

## References

* [Stacks Project, Lemma 60.17.5, Tag 07L5](https://stacks.math.columbia.edu/tag/07L5)
* [Stacks Project, Tag 07HB](https://stacks.math.columbia.edu/tag/07HB)
* [Stacks Project, Tag 07KD](https://stacks.math.columbia.edu/tag/07KD)
-/

@[expose] public noncomputable section

namespace Crystalline

open DividedPowers

universe u v

section Presentation

/-- **The choice of the polynomial presentation of [Stacks, Lemma 60.17.5, Tag 07L5].**  A
smooth algebra is of finite presentation, so it is a quotient of a polynomial algebra in
finitely many variables; composing the surjection with `P' → C` presents `C` over the
polynomial algebra as well. -/
public theorem exists_mvPolynomial_surjection_of_smooth (A : Type u) [CommRing A]
    (P' : Type u) [CommRing P'] [Algebra A P'] [Algebra.Smooth A P'] :
    ∃ (m : ℕ) (q : MvPolynomial (Fin m) A →ₐ[A] P'), Function.Surjective q := by
  obtain ⟨m, q, hq, -⟩ :=
    Algebra.FinitePresentation.out (R := A) (A := P')
  exact ⟨m, q, hq⟩

end Presentation

section Augmentation

variable (s : AffineCrystallineSituation.{u, v}) {P : Type u} [CommRing P] [Algebra s.A P]

/-- The distinguished divided power ideal of `A` has zero image in `C`, so it is carried into
the kernel of any `A`-algebra map `P → C`. -/
public theorem ideal_map_le_presentationKernel (f : P →ₐ[s.A] s.C) :
    s.A.ideal.map (algebraMap s.A P) ≤ presentationKernel s f := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  change f (algebraMap s.A P x) = 0
  rw [f.commutes]
  have hx' : algebraMap s.A s.C x ∈ s.A.ideal.map (algebraMap s.A s.C) :=
    Ideal.mem_map_of_mem (algebraMap s.A s.C) hx
  rw [s.ideal_map_eq_bot] at hx'
  exact hx'

/-- The canonical identification `D_0 ⧸ I_{D_0} ≅ P ⧸ J` of the quotient of the divided power
envelope of `J = ker f` by its divided power ideal with the target of the presentation. -/
public def envelopeQuotientPresentationEquiv (f : P →ₐ[s.A] s.C) :
    (presentationEnvelope s f).object ⧸ (presentationEnvelope s f).object.ideal ≃+*
      P ⧸ presentationKernel s f :=
  (envelopeQuotientEquiv (algebraMap s.A P) (presentationKernel s f)
    (ideal_map_le_presentationKernel s f) (presentationEnvelope s f)).1

/-- The identification `D_0 ⧸ I_{D_0} ≅ P ⧸ J` is the identity on the image of `P`. -/
public theorem envelopeQuotientPresentationEquiv_mk (f : P →ₐ[s.A] s.C) (y : P) :
    envelopeQuotientPresentationEquiv s f (Ideal.Quotient.mk
        (presentationEnvelope s f).object.ideal
        ((presentationEnvelope s f).algebraMap.toRingHom y)) =
      Ideal.Quotient.mk (presentationKernel s f) y :=
  (envelopeQuotientEquiv (algebraMap s.A P) (presentationKernel s f)
    (ideal_map_le_presentationKernel s f) (presentationEnvelope s f)).2 y

/-- **The augmentation `D → C` of a completed divided power envelope.**

For a surjective presentation `f : P ↠ C` over `A` in the affine situation of
[Stacks, Tag 07MD], write `D_0 = D_{P, γ}(J)` for the divided power envelope of `J = ker f`
and `D` for its `p`-adic completion.  The augmentation is the composite of

* the reduction `D → D_0 ⧸ I_{D_0}` of [Stacks, Tag 07KD] part (1),
  `DividedPowers.completionToQuotient`;
* the canonical isomorphism `D_0 ⧸ I_{D_0} ≅ P ⧸ J` of
  `Crystalline.envelopeQuotientEquiv`;
* the isomorphism `P ⧸ ker f ≅ C` induced by the surjection `f`.

On the image of `P` it is `f` itself, which is
`Crystalline.completedEnvelopeAugmentation_algebraMap`. -/
public def completedEnvelopeAugmentation (f : P →ₐ[s.A] s.C) (hf : Function.Surjective f) :
    AdicCompletion (pAdicIdeal (A := (presentationEnvelope s f).object) s.p)
        (presentationEnvelope s f).object →+* s.C :=
  (RingHom.quotientKerEquivOfSurjective (f := f.toRingHom) hf).toRingHom.comp
    ((envelopeQuotientPresentationEquiv s f).toRingHom.comp
      (completionToQuotient (presentationEnvelope s f).object.ideal s.p
        (presentationEnvelope_prime_nilpotent s f hf)))

/-- The augmentation of a completed envelope reads off the class of an element modulo the
divided power ideal through the canonical identifications. -/
public theorem completedEnvelopeAugmentation_apply (f : P →ₐ[s.A] s.C)
    (hf : Function.Surjective f)
    (z : AdicCompletion (pAdicIdeal (A := (presentationEnvelope s f).object) s.p)
      (presentationEnvelope s f).object) :
    completedEnvelopeAugmentation s f hf z =
      RingHom.quotientKerEquivOfSurjective (f := f.toRingHom) hf
        (envelopeQuotientPresentationEquiv s f
          (completionToQuotient (presentationEnvelope s f).object.ideal s.p
            (presentationEnvelope_prime_nilpotent s f hf) z)) :=
  rfl

/-- **The augmentation of a completed envelope only depends on the class modulo the completed
divided power ideal**, being the reduction of [Stacks, Tag 07KD] part (1) followed by two
isomorphisms. -/
public theorem completedEnvelopeAugmentation_congr (f : P →ₐ[s.A] s.C)
    (hf : Function.Surjective f)
    {z w : AdicCompletion (pAdicIdeal (A := (presentationEnvelope s f).object) s.p)
      (presentationEnvelope s f).object}
    (h : completionToQuotient (presentationEnvelope s f).object.ideal s.p
        (presentationEnvelope_prime_nilpotent s f hf) z =
      completionToQuotient (presentationEnvelope s f).object.ideal s.p
        (presentationEnvelope_prime_nilpotent s f hf) w) :
    completedEnvelopeAugmentation s f hf z = completedEnvelopeAugmentation s f hf w :=
  congrArg (fun t : (presentationEnvelope s f).object ⧸
      (presentationEnvelope s f).object.ideal ↦
    RingHom.quotientKerEquivOfSurjective (f := f.toRingHom) hf
      (envelopeQuotientPresentationEquiv s f t)) h

/-- The augmentation of a completed divided power envelope agrees with `f` on the image of the
presentation `P`. -/
public theorem completedEnvelopeAugmentation_algebraMap (f : P →ₐ[s.A] s.C)
    (hf : Function.Surjective f) (y : P) :
    completedEnvelopeAugmentation s f hf
        (algebraMap (presentationEnvelope s f).object _
          ((presentationEnvelope s f).algebraMap.toRingHom y)) = f y := by
  rw [completedEnvelopeAugmentation_apply,
    completionToQuotient_algebraMap (presentationEnvelope s f).object.ideal s.p
      (presentationEnvelope_prime_nilpotent s f hf),
    envelopeQuotientPresentationEquiv_mk]
  exact RingHom.quotientKerEquivOfSurjective_apply_mk hf y

/-- An element of the completion congruent modulo the completed divided power ideal to the image
of a point of `P` has augmentation `f` of that point. -/
private theorem completedEnvelopeAugmentation_eq_of_sub_mem (f : P →ₐ[s.A] s.C)
    (hf : Function.Surjective f) {z : AdicCompletion
      (pAdicIdeal (A := (presentationEnvelope s f).object) s.p) (presentationEnvelope s f).object}
    {y : P}
    (h : z - algebraMap (presentationEnvelope s f).object _
        ((presentationEnvelope s f).algebraMap.toRingHom y) ∈
      completionIdeal (presentationEnvelope s f).object.ideal s.p
        (presentationEnvelope_prime_nilpotent s f hf)) :
    completedEnvelopeAugmentation s f hf z = f y := by
  rw [completedEnvelopeAugmentation_congr s f hf (completionToQuotient_eq_of_sub_mem _ _ _ h)]
  exact completedEnvelopeAugmentation_algebraMap s f hf y

/-- **Every class modulo the divided power ideal of an envelope comes from the presentation.**
The isomorphism `D_0 ⧸ I_{D_0} ≅ P ⧸ J` of `Crystalline.envelopeQuotientEquiv` carries the
image of `P` onto `P ⧸ J`, so the image of `P` already exhausts `D_0 ⧸ I_{D_0}`. -/
public theorem exists_sub_algebraMap_mem_envelopeIdeal (f : P →ₐ[s.A] s.C)
    (_hf : Function.Surjective f) (u : (presentationEnvelope s f).object) :
    ∃ y : P, u - (presentationEnvelope s f).algebraMap.toRingHom y ∈
      (presentationEnvelope s f).object.ideal := by
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective
    (envelopeQuotientPresentationEquiv s f
      (Ideal.Quotient.mk (presentationEnvelope s f).object.ideal u))
  refine ⟨y, ?_⟩
  rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  refine (envelopeQuotientPresentationEquiv s f).injective ?_
  rw [envelopeQuotientPresentationEquiv_mk, ← hy]

end Augmentation

/-- Congruence modulo the completed divided power ideal is transitive through a congruence
modulo `I` in the ring itself. -/
private theorem sub_algebraMap_mem_completionIdeal_of_sub_mem {R : Type u} [CommRing R]
    (I : Ideal R) (p : ℕ) (hp : IsNilpotent (Ideal.Quotient.mk I (p : R)))
    {z : AdicCompletion (pAdicIdeal (A := R) p) R} {u y : R}
    (hu : z - algebraMap R _ u ∈ completionIdeal I p hp) (hy : u - y ∈ I) :
    z - algebraMap R _ y ∈ completionIdeal I p hp := by
  have := Ideal.add_mem _ hu (algebraMap_mem_completionIdeal I p hp hy)
  rwa [map_sub, sub_add_sub_cancel] at this

section AugmentationRetract

variable (s : AffineCrystallineSituation.{u, v}) {P P' : Type u} [CommRing P] [Algebra s.A P]
  [CommRing P'] [Algebra s.A P']

/-- **A divided power morphism of completed envelopes lying over the canonical map `ρ` of
[Stacks, Tag 07HB] is compatible with the two augmentations to `C`.**

Let `q : P → P'` and `f' : P' ↠ C` be `A`-algebra maps, `f = f' ∘ q`, and let
`ρ : D_{P, γ}(J) → D_{P', γ}(J')` be a divided power morphism with
`ρ ∘ (P → D_{P, γ}(J)) = (P' → D_{P', γ}(J')) ∘ q`.  If `a` is a divided power morphism of the
`p`-adic completions which is `ρ` on the dense image, then the augmentation of the target
composed with `a` is the augmentation of the source.

The argument is the one of `Crystalline.completionToQuotient_dpMorphism_apply`: an element of
the completion is congruent modulo the completed divided power ideal to one coming from
`D_{P, γ}(J)`, which in turn is congruent modulo `I` to one coming from `P` by
`Crystalline.exists_sub_algebraMap_mem_envelopeIdeal`; there both sides are `f`. -/
public theorem completedEnvelopeAugmentation_comp_of_dpMorphism
    (q : P →ₐ[s.A] P') (f' : P' →ₐ[s.A] s.C) (hf' : Function.Surjective f')
    (hfq : Function.Surjective (f'.comp q))
    (rho : DividedPowers.DPMorphism
      (presentationEnvelope s (f'.comp q)).object.dividedPowers
      (presentationEnvelope s f').object.dividedPowers)
    (hrho : rho.toRingHom.comp (presentationEnvelope s (f'.comp q)).algebraMap.toRingHom =
      (presentationEnvelope s f').algebraMap.toRingHom.comp q.toRingHom)
    (a : (completedDividedPowers (presentationEnvelope s (f'.comp q)).object.ideal
          (presentationEnvelope s (f'.comp q)).object.dividedPowers s.p
          (presentationEnvelope_prime_nilpotent s (f'.comp q) hfq)).1.DPMorphism
        (completedDividedPowers (presentationEnvelope s f').object.ideal
          (presentationEnvelope s f').object.dividedPowers s.p
          (presentationEnvelope_prime_nilpotent s f' hf')).1)
    (ha : ∀ x : (presentationEnvelope s (f'.comp q)).object,
      a.toRingHom (algebraMap _ _ x) = algebraMap _ _ (rho.toRingHom x)) :
    (completedEnvelopeAugmentation s f' hf').comp a.toRingHom =
      completedEnvelopeAugmentation s (f'.comp q) hfq := by
  have hnil := presentationEnvelope_prime_nilpotent s (f'.comp q) hfq
  have hnil' := presentationEnvelope_prime_nilpotent s f' hf'
  ext z
  obtain ⟨u, hu⟩ := exists_sub_algebraMap_mem_completionIdeal
    (presentationEnvelope s (f'.comp q)).object.ideal s.p hnil z
  obtain ⟨y, hy⟩ := exists_sub_algebraMap_mem_envelopeIdeal s (f'.comp q) hfq u
  -- the source side
  have hsrc : completedEnvelopeAugmentation s (f'.comp q) hfq z = f' (q y) :=
    completedEnvelopeAugmentation_eq_of_sub_mem s (f'.comp q) hfq
      (sub_algebraMap_mem_completionIdeal_of_sub_mem _ _ hnil hu hy)
  -- the target side
  have htgt : completedEnvelopeAugmentation s f' hf' (a.toRingHom z) = f' (q y) := by
    have h1 := sub_mem_completionIdeal_map _ _ _ _ s.p hnil hnil' a hu
    rw [ha u] at h1
    have hmap : rho.toRingHom ((presentationEnvelope s (f'.comp q)).algebraMap.toRingHom y) =
        (presentationEnvelope s f').algebraMap.toRingHom (q y) :=
      DFunLike.congr_fun hrho y
    refine completedEnvelopeAugmentation_eq_of_sub_mem s f' hf'
      (sub_algebraMap_mem_completionIdeal_of_sub_mem _ _ hnil' h1 ?_)
    rw [← hmap, ← map_sub]
    exact rho.ideal_comp (Ideal.mem_map_of_mem _ hy)
  rw [RingHom.comp_apply, htgt, hsrc]

end AugmentationRetract

section FirstAssertion

/-- **The first assertion of [Stacks, Lemma 60.17.5, Tag 07L5].**

In Situation [Stacks, Tag 07MD] let `A → P' → C` be ring maps with `A → P'` smooth and
`P' → C` surjective with kernel `J'`, and let `D'` be the `p`-adic completion of
`D_{P', γ}(J')`.  Then there are a choice of the data `A → P → C` — a polynomial algebra
`P = A[y_1, …, y_m]` over `A` together with a surjection `P ↠ P'`, the map `P → C` being the
composition — and homomorphisms of divided power `A`-algebras

`a : D → D'`,  `b : D' → D`

between the `p`-adic completions, compatible with the maps `D → C` and `D' → C`, such that
`a ∘ b = id_{D'}`.

The three steps are each separate:

* the *choice of the data* is `Crystalline.exists_mvPolynomial_surjection_of_smooth`: a smooth
  algebra is of finite presentation, hence a quotient of a polynomial algebra in finitely many
  variables;
* the *retract* `a`, `b`, `a ∘ b = id` for a surjection `q : P ↠ P'` is
  `Crystalline.exists_completedEnvelopeRetract`, whose mathematics is the successive lifting of
  `P' → D' ⧸ (p)^e` through the reductions of the canonical map
  `ρ : D_{P, γ}(J) → D_{P', γ}(J')` of [Stacks, Tag 07HB], using the strong lifting property of
  [Stacks, Tag 07K4] for the smooth algebra `P'`;
* the *compatibility with the maps to `C`* is
  `Crystalline.completedEnvelopeAugmentation_comp_of_dpMorphism` for `a`, and for `b` it
  follows from that together with `a ∘ b = id_{D'}`: applying it to `b w` gives
  `(D → C) (b w) = (D' → C) (a (b w)) = (D' → C) w`.

Both `a` and `b` are maps over `A`, `a` because it is the completion of `ρ` and `ρ` is
compatible with the structure maps, `b` because the level splittings `θ_e` out of which it is
assembled are maps over `A`. -/
public theorem exists_presentation_completedEnvelopeRetract
    (s : AffineCrystallineSituation.{u, v}) (P' : Type u) [CommRing P'] [Algebra s.A P']
    [Algebra.Smooth (s.A : Type u) P'] (f' : P' →ₐ[s.A] s.C) (hf' : Function.Surjective f') :
    ∃ (m : ℕ) (q : MvPolynomial (Fin m) s.A →ₐ[s.A] P')
      (hfq : Function.Surjective (f'.comp q))
      (a : (completedDividedPowers (presentationEnvelope s (f'.comp q)).object.ideal
            (presentationEnvelope s (f'.comp q)).object.dividedPowers s.p
            (presentationEnvelope_prime_nilpotent s (f'.comp q) hfq)).1.DPMorphism
          (completedDividedPowers (presentationEnvelope s f').object.ideal
            (presentationEnvelope s f').object.dividedPowers s.p
            (presentationEnvelope_prime_nilpotent s f' hf')).1)
      (b : (completedDividedPowers (presentationEnvelope s f').object.ideal
            (presentationEnvelope s f').object.dividedPowers s.p
            (presentationEnvelope_prime_nilpotent s f' hf')).1.DPMorphism
          (completedDividedPowers (presentationEnvelope s (f'.comp q)).object.ideal
            (presentationEnvelope s (f'.comp q)).object.dividedPowers s.p
            (presentationEnvelope_prime_nilpotent s (f'.comp q) hfq)).1),
      Function.Surjective q ∧
        a.comp b = DividedPowers.DPMorphism.id _ ∧
        (∀ x : (s.A : Type u), a.toRingHom (algebraMap _ _
              ((presentationEnvelope s (f'.comp q)).structureMap.toRingHom x)) =
            algebraMap _ _ ((presentationEnvelope s f').structureMap.toRingHom x)) ∧
          (∀ x : (s.A : Type u), b.toRingHom (algebraMap _ _
                ((presentationEnvelope s f').structureMap.toRingHom x)) =
              algebraMap _ _
                ((presentationEnvelope s (f'.comp q)).structureMap.toRingHom x)) ∧
            (completedEnvelopeAugmentation s f' hf').comp a.toRingHom =
                completedEnvelopeAugmentation s (f'.comp q) hfq ∧
              (completedEnvelopeAugmentation s (f'.comp q) hfq).comp b.toRingHom =
                completedEnvelopeAugmentation s f' hf' := by
  obtain ⟨m, q, hq⟩ := exists_mvPolynomial_surjection_of_smooth (s.A : Type u) P'
  obtain ⟨rho, hrhostruct, hrhoalg, -, -, a, b, hab, ha, hbstruct⟩ :=
    exists_completedEnvelopeRetract s q f' hq hf'
  refine ⟨m, q, hf'.comp hq, a, b, hq, hab, ?_, hbstruct, ?_, ?_⟩
  · -- `a` is the completion of `ρ`, and `ρ` is a map over `A`
    intro x
    rw [ha ((presentationEnvelope s (f'.comp q)).structureMap.toRingHom x)]
    exact congrArg _ (DFunLike.congr_fun
      (congrArg DividedPowers.DPMorphism.toRingHom hrhostruct) x)
  · exact completedEnvelopeAugmentation_comp_of_dpMorphism s q f' hf' (hf'.comp hq) rho
      hrhoalg a ha
  · -- `(D → C) (b w) = (D' → C) (a (b w)) = (D' → C) w`
    have haug := completedEnvelopeAugmentation_comp_of_dpMorphism s q f' hf' (hf'.comp hq) rho
      hrhoalg a ha
    ext w
    have hw : a.toRingHom (b.toRingHom w) = w :=
      congrArg (fun r : DividedPowers.DPMorphism
          (completedDividedPowers (presentationEnvelope s f').object.ideal
            (presentationEnvelope s f').object.dividedPowers s.p
            (presentationEnvelope_prime_nilpotent s f' hf')).1
          (completedDividedPowers (presentationEnvelope s f').object.ideal
            (presentationEnvelope s f').object.dividedPowers s.p
            (presentationEnvelope_prime_nilpotent s f' hf')).1 ↦ r w) hab
    have h1 : completedEnvelopeAugmentation s f' hf' (a.toRingHom (b.toRingHom w)) =
        completedEnvelopeAugmentation s (f'.comp q) (hf'.comp hq) (b.toRingHom w) :=
      DFunLike.congr_fun haug (b.toRingHom w)
    rw [hw] at h1
    exact h1.symm

end FirstAssertion

end Crystalline

end
