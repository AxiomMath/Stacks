module

public import StacksFrontier.AlgebraicGeometry.Crystalline.EnvelopeRetractPairs
public import StacksFrontier.AlgebraicGeometry.Crystalline.EnvelopeRetractPresentation

/-!
# [Stacks, Lemma 60.17.5, Tag 07L5]: the retract and the equivalence of categories of pairs

In Situation [Stacks, Tag 07MD] let `A → P' → C` be ring maps with `A → P'` smooth and
`P' → C` surjective with kernel `J'`, and let `D'` be the `p`-adic completion of
`D_{P', γ}(J')`.  [Stacks, Lemma 60.17.5, Tag 07L5] says:

> Then there are a choice of the data `A → P → C` as above and homomorphisms of divided power
> `A`-algebras `a : D → D'`, `b : D' → D` compatible with the maps `D → C` and `D' → C` such
> that `a ∘ b = id_{D'}`.  These maps induce an equivalence of categories of pairs `(M, ∇)`
> satisfying (07JB), (07JC), (07JD), and (07JE) over `D` and pairs `(M', ∇')` satisfying
> (07JB), (07JC), (07JD), and (07JE) over `D'`.

`Crystalline.exists_presentation_retract_pairEquivalence` states and proves both assertions.

* The **data** `A → P → C` is a polynomial algebra `P = A[y_i]` in finitely many variables with a
  surjection `q : P ↠ P'`, which exists because `A → P'` is smooth.
* The **retract** `a`, `b`, `a ∘ b = id_{D'}`, with `a` and `b` divided power morphisms over `A`
  compatible with the augmentations to `C`, is `Crystalline.exists_completedEnvelopeRetract` and
  `Crystalline.completedEnvelopeAugmentation_comp_of_dpMorphism`.
* The **pairs over `D`** are `Crystalline.Pair` for the completed one-forms `Ω_D` of
  [Stacks, Tag 07J9] (`Crystalline.envelopeCompletionForms`), the universal differential
  `d : D → Ω_D` and the coordinates `d y_i`: a `p`-adically complete `D`-module with a connection
  `∇ : M → M ⊗̂_D Ω_D` which is integrable and topologically quasi-nilpotent.
* The **pairs over `D'`** are `Crystalline.RetractPair`, for the completed forms `Ω^*_{D'}` of
  `D'` with its universal differential: a `p`-adically complete `D'`-module with a connection
  `∇' : M' → M' ⊗̂_{D'} Ω_{D'}` whose curvature vanishes (integrability in the sense of Remark
  [Stacks, Tag 07I0]), topologically quasi-nilpotent in the sense the proof gives that condition
  over `D'`: "if this is true for `G(M', ∇')`".
* The **equivalence** has for functor the base change `F` along `a` and for quasi-inverse the
  base change `G` along `b` (`Crystalline.retractPairEquivalence`).
* The **last sentence** — the equivalence of [Stacks, Proposition 60.17.4, Tag 07JH] also holds
  for the corresponding functor towards the pairs over `D'` — is, abstractly, that a functor into
  the pairs over `D` is an equivalence exactly when its composite with `F` is
  (`Crystalline.isEquivalence_comp_retractForwardFunctor_iff`); for the functor of
  [Stacks, Tag 07JG] itself it is `...SmallSite.exists_presentation_retract_crystalPairEquivalence`
  (`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CrystalRetractPairs07L5.lean`), which
  restates the lemma in the situation of [Stacks, Section 60.17, Tag 07J7] with the presentation
  of the system of thickenings of [Stacks, Tag 07JN] chosen through `P'`.

## References

* [Stacks Project, Lemma 60.17.5, Tag 07L5](https://stacks.math.columbia.edu/tag/07L5)
* [Stacks Project, Tag 07MD](https://stacks.math.columbia.edu/tag/07MD)
* [Stacks Project, Tag 07J9](https://stacks.math.columbia.edu/tag/07J9)
-/

@[expose] public noncomputable section

open CategoryTheory
open DividedPowers

universe u v w w'

namespace Crystalline

/-! ### The completed envelope of a presentation -/

section Envelope

variable (s : AffineCrystallineSituation.{u, v}) {P : Type u} [CommRing P] [Algebra s.A P]
  (f : P →ₐ[s.A] s.C) (hf : Function.Surjective f)

/-- **The `p`-adic completion of the divided power envelope `D_{P,γ}(J)`** of a surjective
presentation `P → C` with kernel `J`, as a divided power ring: the completed divided power
structure of [Stacks, Tag 07KD] on the completion. -/
abbrev completedEnvelopeOfPresentation : DividedPowerRing.{u} :=
  ⟨AdicCompletion (pAdicIdeal (A := ((presentationEnvelope s f).object : Type u)) s.p)
      (presentationEnvelope s f).object,
    completionIdeal (presentationEnvelope s f).object.ideal s.p
      (presentationEnvelope_prime_nilpotent s f hf),
    (completedDividedPowers (presentationEnvelope s f).object.ideal
      (presentationEnvelope s f).object.dividedPowers s.p
      (presentationEnvelope_prime_nilpotent s f hf)).1⟩

/-- The `A`-algebra structure of the completed envelope, through the structure map
`A → D_{P,γ}(J)` followed by the completion. -/
@[instance_reducible]
def algebraCompletedEnvelopeOfPresentation :
    Algebra (s.A : Type u) (completedEnvelopeOfPresentation s f hf : Type u) :=
  ((algebraMap ((presentationEnvelope s f).object : Type u)
    (AdicCompletion (pAdicIdeal (A := ((presentationEnvelope s f).object : Type u)) s.p)
      (presentationEnvelope s f).object)).comp
      (presentationEnvelope s f).structureMap.toRingHom).toAlgebra

attribute [instance] algebraCompletedEnvelopeOfPresentation

end Envelope

/-! ### The augmentation and the divided power ideal -/

section Augmentation

variable (s : AffineCrystallineSituation.{u, v}) {P : Type u} [CommRing P] [Algebra s.A P]
  (f : P →ₐ[s.A] s.C) (hf : Function.Surjective f)

/-- **The divided power ideal of the completed envelope is the kernel of its augmentation**
to `C`. -/
theorem sub_mem_completionIdeal_of_augmentation_eq
    {x y : AdicCompletion (pAdicIdeal (A := ((presentationEnvelope s f).object : Type u)) s.p)
      (presentationEnvelope s f).object}
    (h : completedEnvelopeAugmentation s f hf x = completedEnvelopeAugmentation s f hf y) :
    x - y ∈ completionIdeal (presentationEnvelope s f).object.ideal s.p
      (presentationEnvelope_prime_nilpotent s f hf) := by
  rw [RingHom.mem_ker, map_sub, sub_eq_zero]
  simp only [completedEnvelopeAugmentation, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom] at h
  exact (envelopeQuotientPresentationEquiv s f).injective
    ((RingHom.quotientKerEquivOfSurjective (f := f.toRingHom) hf).injective h)

end Augmentation

/-! ### The lemma -/

section Lemma

variable (s : AffineCrystallineSituation.{u, v})

/-- **The retract for a polynomial presentation over a smooth one**: for a surjection
`q : A[x_i] ↠ P'` the completed envelopes are related by divided power morphisms `a`, `b` over
`A` with `a ∘ b = id`, compatible with the augmentations to `C`; then `b ∘ a` moves elements within
the divided power ideal. -/
theorem exists_retract_of_surjective {ι : Type u} [Fintype ι] (P' : Type u) [CommRing P']
    [Algebra s.A P'] [Algebra.Smooth (s.A : Type u) P'] (f' : P' →ₐ[s.A] s.C)
    (hf' : Function.Surjective f') (q : MvPolynomial ι s.A →ₐ[s.A] P')
    (hq : Function.Surjective q) :
    ∃ (a : DPMorphism (envelopeCompletion (presentationEnvelope s (f'.comp q)) s.p
          (presentationEnvelope_prime_nilpotent s (f'.comp q) (hf'.comp hq))).dividedPowers
        (completedEnvelopeOfPresentation s f' hf').dividedPowers)
      (b : DPMorphism (completedEnvelopeOfPresentation s f' hf').dividedPowers
        (envelopeCompletion (presentationEnvelope s (f'.comp q)) s.p
          (presentationEnvelope_prime_nilpotent s (f'.comp q) (hf'.comp hq))).dividedPowers),
      (∀ c : (s.A : Type u), a (algebraMap (s.A : Type u)
          (envelopeCompletion (presentationEnvelope s (f'.comp q)) s.p
            (presentationEnvelope_prime_nilpotent s (f'.comp q) (hf'.comp hq)) : Type u) c) =
          algebraMap (s.A : Type u) (completedEnvelopeOfPresentation s f' hf' : Type u) c) ∧
      (∀ c : (s.A : Type u), b (algebraMap (s.A : Type u)
          (completedEnvelopeOfPresentation s f' hf' : Type u) c) =
          algebraMap (s.A : Type u) (envelopeCompletion (presentationEnvelope s (f'.comp q)) s.p
            (presentationEnvelope_prime_nilpotent s (f'.comp q) (hf'.comp hq)) : Type u) c) ∧
      a.comp b = DPMorphism.id _ ∧
      (completedEnvelopeAugmentation s f' hf').comp a.toRingHom =
          completedEnvelopeAugmentation s (f'.comp q) (hf'.comp hq) ∧
      (completedEnvelopeAugmentation s (f'.comp q) (hf'.comp hq)).comp b.toRingHom =
          completedEnvelopeAugmentation s f' hf' := by
  obtain ⟨rho, hrhostruct, hrhoalg, -, -, a, b, hab, ha, hbstruct⟩ :=
    exists_completedEnvelopeRetract s q f' hq hf'
  have haug := completedEnvelopeAugmentation_comp_of_dpMorphism s q f' hf' (hf'.comp hq) rho
    hrhoalg a ha
  refine ⟨a, b, fun c ↦ ?_, hbstruct, hab, haug, ?_⟩
  · show a.toRingHom (algebraMap _ _ ((presentationEnvelope s (f'.comp q)).structureMap.toRingHom
      c)) = algebraMap _ _ ((presentationEnvelope s f').structureMap.toRingHom c)
    rw [ha ((presentationEnvelope s (f'.comp q)).structureMap.toRingHom c)]
    exact congrArg _ (DFunLike.congr_fun
      (congrArg DividedPowers.DPMorphism.toRingHom hrhostruct) c)
  · ext w
    have hw : a.toRingHom (b.toRingHom w) = w :=
      congrArg (fun r : DividedPowers.DPMorphism _ _ ↦ r w) hab
    have h1 := DFunLike.congr_fun haug (b.toRingHom w)
    rw [RingHom.comp_apply, hw] at h1
    exact h1.symm

/-- `Crystalline.exists_retract_of_surjective` for a presentation `g` equal to the composite
`f' ∘ q`, stated for `g` itself. -/
theorem exists_retract_of_comp_eq {ι : Type u} [Fintype ι] (P' : Type u) [CommRing P']
    [Algebra s.A P'] [Algebra.Smooth (s.A : Type u) P'] (f' : P' →ₐ[s.A] s.C)
    (hf' : Function.Surjective f') (q : MvPolynomial ι s.A →ₐ[s.A] P')
    (hq : Function.Surjective q) (g : MvPolynomial ι s.A →ₐ[s.A] s.C) (hgq : f'.comp q = g)
    (hg : Function.Surjective g) :
    ∃ (a : DPMorphism (envelopeCompletion (presentationEnvelope s g) s.p
          (presentationEnvelope_prime_nilpotent s g hg)).dividedPowers
        (completedEnvelopeOfPresentation s f' hf').dividedPowers)
      (b : DPMorphism (completedEnvelopeOfPresentation s f' hf').dividedPowers
        (envelopeCompletion (presentationEnvelope s g) s.p
          (presentationEnvelope_prime_nilpotent s g hg)).dividedPowers),
      (∀ c : (s.A : Type u), a (algebraMap (s.A : Type u)
          (envelopeCompletion (presentationEnvelope s g) s.p
            (presentationEnvelope_prime_nilpotent s g hg) : Type u) c) =
          algebraMap (s.A : Type u) (completedEnvelopeOfPresentation s f' hf' : Type u) c) ∧
      (∀ c : (s.A : Type u), b (algebraMap (s.A : Type u)
          (completedEnvelopeOfPresentation s f' hf' : Type u) c) =
          algebraMap (s.A : Type u) (envelopeCompletion (presentationEnvelope s g) s.p
            (presentationEnvelope_prime_nilpotent s g hg) : Type u) c) ∧
      a.comp b = DPMorphism.id _ ∧
      (completedEnvelopeAugmentation s f' hf').comp a.toRingHom =
          completedEnvelopeAugmentation s g hg ∧
      (completedEnvelopeAugmentation s g hg).comp b.toRingHom =
          completedEnvelopeAugmentation s f' hf' := by
  subst hgq
  exact exists_retract_of_surjective s P' f' hf' q hq

variable (P' : Type u) [CommRing P'] [Algebra s.A P'] [Algebra.Smooth (s.A : Type u) P']
  (f' : P' →ₐ[s.A] s.C) (hf' : Function.Surjective f')

/-- **The coordinates of the completed envelope of a polynomial presentation `g : A[x_i] ↠ C`**:
the completed one-forms `Ω_D` of [Stacks, Tag 07J9] with the universal differential
`d : D → Ω_D`, and the coordinates `x_i`, whose differentials are a basis of `Ω_D`. -/
abbrev polynomialEnvelopeCoordinates {ι : Type u} [Fintype ι] [DecidableEq ι]
    (g : MvPolynomial ι s.A →ₐ[s.A] s.C) (hg : Function.Surjective g) :
    CompletedCoordinateData s.p (envelopeCompletion (presentationEnvelope s g) s.p
      (presentationEnvelope_prime_nilpotent s g hg)) :=
  envelopeCoordinateData _ s.p _

/-- **[Stacks, Lemma 60.17.5, Tag 07L5].**  In Situation [Stacks, Tag 07MD], let `A → P' → C` be
ring maps with `A → P'` smooth and `P' → C` surjective with kernel `J'`, and let `D'` be the
`p`-adic completion of `D_{P', γ}(J')` (`Crystalline.completedEnvelopeOfPresentation`).  Then

* **(first assertion)** there are a choice of the data `A → P → C` — a polynomial algebra
  `P = A[x_i]` in finitely many variables with a surjection `q : P ↠ P'`, `P → C` being the
  composite — and homomorphisms of divided power `A`-algebras `a : D → D'`, `b : D' → D`
  between the `p`-adic completions of the divided power envelopes, compatible with the
  augmentations `D → C` and `D' → C`, with `a ∘ b = id_{D'}`;
* **(second assertion)** these maps induce an equivalence of categories between the pairs
  `(M, ∇)` over `D` satisfying (07JB)–(07JE) — `Crystalline.Pair` for the completed one-forms
  `Ω_D` with the coordinates `d x_i` — and the pairs `(M', ∇')` over `D'` satisfying them —
  `Crystalline.RetractPair` for the completed forms `Ω^*_{D'}`: `p`-adically complete, with a
  completed connection whose curvature vanishes, and topologically quasi-nilpotent in the sense
  the proof gives that condition over `D'`, on `G(M', ∇')`.  The functor is the base change `F`
  along `a` and its quasi-inverse the base change `G` along `b`;
* **(last sentence)** consequently a functor towards the pairs over `D` — in particular the
  functor of [Stacks, Proposition 60.17.4, Tag 07JH] — is an equivalence exactly when its
  composite with `F`, towards the pairs over `D'`, is one.  For the functor of
  [Stacks, Tag 07JG] on crystals this is
  `...SmallSite.exists_presentation_retract_crystalPairEquivalence`.

The proof of the second assertion is the source's: `F ∘ G ≅ 𝟭` because `a ∘ b = id`, and
`G ∘ F ≅ 𝟭` by the Taylor comparison `c_{id_D, b ∘ a}`, whose horizontality — which the source
omits — is `Crystalline.coordOp_taylorRoundTrip`. -/
@[stacks 07L5 "both assertions, under exactly the source's hypotheses: for A -> P' smooth and \
P' -> C surjective, there are a polynomial presentation q : A[x_i] ->> P' with finitely many \
variables and divided power A-algebra maps a : D -> D', b : D' -> D between the p-adically \
completed envelopes, compatible with the augmentations to C, with a . b = id; and an equivalence \
of categories between the pairs (M, nabla) over D satisfying 07JB-07JE (Crystalline.Pair over the \
completed one-forms of D in the coordinates d x_i) and the pairs (M', nabla') over D' satisfying \
07JB-07JE (Crystalline.RetractPair: p-adically complete, a completed connection over the \
completed forms of D' whose curvature vanishes, and 07JE read on the base change G(M', nabla') \
along b, as the proof defines it), whose functor is the base change along a and whose inverse is \
the base change along b; and, for the last sentence, a functor towards the pairs over D is an \
equivalence exactly when its composite with the base change towards D' is"]
theorem exists_presentation_retract_pairEquivalence :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (q : MvPolynomial ι s.A →ₐ[s.A] P')
      (hq : Function.Surjective q)
      (a : DPMorphism (envelopeCompletion (presentationEnvelope s (f'.comp q)) s.p
          (presentationEnvelope_prime_nilpotent s (f'.comp q) (hf'.comp hq))).dividedPowers
        (completedEnvelopeOfPresentation s f' hf').dividedPowers)
      (b : DPMorphism (completedEnvelopeOfPresentation s f' hf').dividedPowers
        (envelopeCompletion (presentationEnvelope s (f'.comp q)) s.p
          (presentationEnvelope_prime_nilpotent s (f'.comp q) (hf'.comp hq))).dividedPowers)
      (ha : ∀ c : (s.A : Type u), a (algebraMap (s.A : Type u)
          (envelopeCompletion (presentationEnvelope s (f'.comp q)) s.p
            (presentationEnvelope_prime_nilpotent s (f'.comp q) (hf'.comp hq)) : Type u) c) =
          algebraMap (s.A : Type u) (completedEnvelopeOfPresentation s f' hf' : Type u) c)
      (hb : ∀ c : (s.A : Type u), b (algebraMap (s.A : Type u)
          (completedEnvelopeOfPresentation s f' hf' : Type u) c) =
          algebraMap (s.A : Type u) (envelopeCompletion (presentationEnvelope s (f'.comp q)) s.p
            (presentationEnvelope_prime_nilpotent s (f'.comp q) (hf'.comp hq)) : Type u) c)
      (hab : ∀ x, a (b x) = x)
      (hρ : ∀ y, b (a y) - y ∈ (envelopeCompletion (presentationEnvelope s (f'.comp q)) s.p
          (presentationEnvelope_prime_nilpotent s (f'.comp q) (hf'.comp hq))).ideal),
      a.comp b = DPMorphism.id _ ∧
        (completedEnvelopeAugmentation s f' hf').comp a.toRingHom =
          completedEnvelopeAugmentation s (f'.comp q) (hf'.comp hq) ∧
        (completedEnvelopeAugmentation s (f'.comp q) (hf'.comp hq)).comp b.toRingHom =
          completedEnvelopeAugmentation s f' hf' ∧
        ∃ e : Pair.{u, u, u, u} s.p _
            (polynomialEnvelopeCoordinates s (f'.comp q) (hf'.comp hq)).forms
            (polynomialEnvelopeCoordinates s (f'.comp q) (hf'.comp hq)).dx
            (polynomialEnvelopeCoordinates s (f'.comp q) (hf'.comp hq)).diff ≌
          RetractPair (polynomialEnvelopeCoordinates s (f'.comp q) (hf'.comp hq))
            (envelopeRetractData _ s.p _ (completedEnvelopeOfPresentation s f' hf') a b ha hb
              hab hρ),
          e.functor = retractForwardFunctor _ (envelopeRetractData _ s.p _
            (completedEnvelopeOfPresentation s f' hf') a b ha hb hab hρ) ∧
          e.inverse = retractBackFunctor _ (envelopeRetractData _ s.p _
            (completedEnvelopeOfPresentation s f' hf') a b ha hb hab hρ) ∧
          ∀ {𝒞 : Type w} [Category.{w'} 𝒞] (Φ : 𝒞 ⥤ Pair.{u, u, u, u} s.p _
            (polynomialEnvelopeCoordinates s (f'.comp q) (hf'.comp hq)).forms
            (polynomialEnvelopeCoordinates s (f'.comp q) (hf'.comp hq)).dx
            (polynomialEnvelopeCoordinates s (f'.comp q) (hf'.comp hq)).diff),
            Φ.IsEquivalence ↔ (Φ ⋙ e.functor).IsEquivalence := by
  classical
  obtain ⟨m, q₀, hq₀⟩ := exists_mvPolynomial_surjection_of_smooth (s.A : Type u) P'
  set q : MvPolynomial (ULift.{u} (Fin m)) s.A →ₐ[s.A] P' :=
    q₀.comp (MvPolynomial.rename ULift.down) with hqdef
  have hq : Function.Surjective q :=
    hq₀.comp (MvPolynomial.rename_surjective _ ULift.down_surjective)
  obtain ⟨a, b, ha, hb, hab, haug, hbaug⟩ := exists_retract_of_surjective s P' f' hf' q hq
  have hab' : ∀ x, a (b x) = x := fun x ↦ congrArg (fun r : DPMorphism _ _ ↦ r x) hab
  have hρ : ∀ y, b (a y) - y ∈ (envelopeCompletion (presentationEnvelope s (f'.comp q)) s.p
      (presentationEnvelope_prime_nilpotent s (f'.comp q) (hf'.comp hq))).ideal := by
    intro y
    refine sub_mem_completionIdeal_of_augmentation_eq s (f'.comp q) (hf'.comp hq) ?_
    exact (DFunLike.congr_fun hbaug (a y)).trans (DFunLike.congr_fun haug y)
  exact ⟨ULift.{u} (Fin m), inferInstance, inferInstance, q, hq, a, b, ha, hb, hab', hρ, hab,
    haug, hbaug, retractPairEquivalence _ _, rfl, rfl,
    fun Φ ↦ isEquivalence_comp_retractForwardFunctor_iff _ _ Φ⟩

end Lemma


end Crystalline

end
