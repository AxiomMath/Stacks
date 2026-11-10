module

public import StacksFrontier.RingTheory.Etale.SquareStandardEtalePresentation

/-!
# The commutative-algebra core of Stacks 07SQ, in one statement

Let `(G i)` be a directed system of commutative rings with colimit `A`, and let `D` be an étale
`A`-algebra with `Spec D → Spec A` surjective. The proof of Stacks 07SQ needs all of steps (2),
(3) and (4) of its commutative-algebra half at a *single* stage: a stage `j` and a square family
`q` of polynomials over `G j` such that `G j → G j[x] ⧸ (q)` is étale, the induced map on spectra
is surjective, and `D` is the base change of `G j[x] ⧸ (q)` to `A`.

The individual steps are proved in
`StacksFrontier/RingTheory/Etale/DirectedColimitPresentation.lean` and
`StacksFrontier/RingTheory/Spectrum/Prime/DirectedColimit.lean`, but each produces its *own* stage
from its own hypothesis, and the hypotheses are stated in terms of a family of polynomials
already lifted to a stage rather than in terms of the étale algebra `D`. This file fuses them.

## Main results

* `MvPolynomial.exists_ge_etale_surjective_quotient_of_directed`: the fusion.

## Implementation notes

*Where the presentation comes from.* The core's étale step takes as its hypothesis the
invertibility of the Jacobian determinant of an explicit square family over a stage, not the
abstract étaleness of `D`. Producing such a family over `A` in the first place is the
substantial direction of Stacks 00U9, which is
`Algebra.exists_square_presentation_isUnit_detJacobian_of_etale` in
`StacksFrontier/RingTheory/Etale/SquareStandardEtalePresentation.lean`; the family is then lifted
to a stage by `MvPolynomial.exists_ge_forall_map_eq_square_of_directed`.

*Why the two stages are fused in this order.* The étale step and the surjectivity step each
take a family over a stage and return a later stage. Applying the étale step first, at the
stage where the family was lifted, and then the surjectivity step *at the stage the étale step
returned*, leaves only one transport to perform: étaleness must be carried forward from the
first returned stage to the second. That transport is free, because the family at the later
stage presents the base change — `MvPolynomial.nonempty_quotientSpanEquiv_tensor_of_le` — and
étaleness is stable under base change and transported by algebra isomorphisms. Running the two
steps independently from a common stage would instead require transporting *both* conclusions.

*The surjectivity step's commuting square.* That step is stated for a bare ring `D` equipped
with ring maps from `A` and from the stage's presentation making a square commute, rather than
for an identification of `D` with the presentation's base change, precisely because `D` is only
isomorphic to it. The map out of the presentation is built here by lifting
`MvPolynomial.map (φ j)` through the quotient — it carries the stage's relations to the
relations over `A`, by the cocone identity — and composing with the inverse of the isomorphism
supplied by the structure theorem.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 00U9](https://stacks.math.columbia.edu/tag/00U9)
* [Stacks Project, Tag 07RR](https://stacks.math.columbia.edu/tag/07RR)
-/

@[expose] public section

universe u v w w'

open MvPolynomial TensorProduct

namespace MvPolynomial

variable {ι : Type u} [Preorder ι] {G : ι → Type v} [∀ i, CommRing (G i)]
  {f : ∀ i j, i ≤ j → G i →+* G j} {A : Type w} [CommRing A] {φ : ∀ i, G i →+* A}

/-- **The commutative-algebra core of Stacks 07SQ, at a single stage.** Let `(G i)` be a
directed system of commutative rings whose colimit is `A`, expressed by the three clauses
`hφ`, `hsurj` and `hzero`, and let `D` be an étale `A`-algebra for which `Spec D → Spec A` is
surjective. Then beyond any prescribed stage there is a stage `j` and a family of `n`
polynomials `q` in `n` variables over `G j` such that

* `G j → G j[x₁, …, xₙ] ⧸ (q₁, …, qₙ)` is étale,
* the induced map `Spec (G j[x] ⧸ (q)) → Spec (G j)` is surjective, and
* `D` is `A`-isomorphic to `A[x] ⧸ (q)`, the relations read over `A`.

These are steps (2), (3) and (4) of the proof of Stacks 07SQ, delivered at one index: the
chart `Spec D = U` over the limit is presented, the presentation descends to a stage at which
it is still étale and still surjective, and the third clause records that the presentation at
the stage base-changes to the one over the limit. -/
theorem exists_ge_etale_surjective_quotient_of_directed [IsDirectedOrder ι]
    [DirectedSystem G fun i j h ↦ f i j h]
    (hφ : ∀ i j (h : i ≤ j) (x : G i), φ j (f i j h x) = φ i x)
    (hsurj : ∀ a : A, ∃ (i : ι) (x : G i), φ i x = a)
    (hzero : ∀ (i : ι) (x : G i), φ i x = 0 → ∃ (j : ι) (h : i ≤ j), f i j h x = 0)
    (D : Type w') [CommRing D] [Algebra A D] [Algebra.Etale A D]
    (hD : Function.Surjective (PrimeSpectrum.comap (algebraMap A D))) (i₀ : ι) :
    ∃ (n : ℕ) (j : ι) (_ : i₀ ≤ j) (q : Fin n → MvPolynomial (Fin n) (G j)),
      Algebra.Etale (G j) (MvPolynomial (Fin n) (G j) ⧸ Ideal.span (Set.range q)) ∧
        Function.Surjective (PrimeSpectrum.comap
          (algebraMap (G j) (MvPolynomial (Fin n) (G j) ⧸ Ideal.span (Set.range q)))) ∧
        Nonempty (D ≃ₐ[A] MvPolynomial (Fin n) A ⧸
          Ideal.span (Set.range fun k ↦ map (φ j) (q k))) := by
  classical
  have : Nonempty ι := ⟨i₀⟩
  -- Stacks 00U9: present `D` over `A` by a square family with invertible Jacobian.
  obtain ⟨n, g, hgunit, ⟨e⟩⟩ :=
    Algebra.exists_square_presentation_isUnit_detJacobian_of_etale A D
  -- Lift the relations to a stage.
  obtain ⟨j₀, hi₀, q₀, hq₀⟩ :=
    exists_ge_forall_map_eq_square_of_directed (f := f) hφ hsurj g i₀
  -- Mapping a lifted family further up the system and then to `A` still gives `g`.
  have hmap : ∀ {j j' : ι} (h : j ≤ j') (q : Fin n → MvPolynomial (Fin n) (G j)),
      (∀ k, map (φ j) (q k) = g k) → ∀ k, map (φ j') (map (f j j' h) (q k)) = g k :=
    fun h q hq k ↦ by rw [map_map_eq_of_comp hφ, hq]
  -- Step (3): the Jacobian determinant is still invertible at a later stage, so the
  -- presentation there is étale.
  obtain ⟨j₁, h₀₁, hetale₁⟩ :=
    exists_ge_etale_quotient_of_directed hφ hsurj hzero q₀ (by rwa [funext hq₀])
  set q₁ : Fin n → MvPolynomial (Fin n) (G j₁) := fun k ↦ map (f j₀ j₁ h₀₁) (q₀ k) with hq₁def
  have hq₁ : ∀ k, map (φ j₁) (q₁ k) = g k := hmap h₀₁ q₀ hq₀
  -- The map out of the stage's presentation into `D`, and the square it makes commute.
  have himg : Ideal.map
      (MvPolynomial.map (φ j₁) : MvPolynomial (Fin n) (G j₁) →+* MvPolynomial (Fin n) A)
      (Ideal.span (Set.range q₁)) = Ideal.span (Set.range g) := by
    rw [Ideal.map_span, ← Set.range_comp]
    exact congrArg (Ideal.span ∘ Set.range) (funext hq₁)
  have hker : ∀ a ∈ Ideal.span (Set.range q₁),
      ((Ideal.Quotient.mk (Ideal.span (Set.range g))).comp
        (MvPolynomial.map (φ j₁))) a = 0 := by
    intro a ha
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, ← himg]
    exact Ideal.mem_map_of_mem _ ha
  set L : (MvPolynomial (Fin n) (G j₁) ⧸ Ideal.span (Set.range q₁)) →+*
      (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range g)) :=
    Ideal.Quotient.lift _ _ hker with hLdef
  set θ : (MvPolynomial (Fin n) (G j₁) ⧸ Ideal.span (Set.range q₁)) →+* D :=
    (e.symm : _ →ₐ[A] D).toRingHom.comp L with hθdef
  have hcomm : (algebraMap A D).comp (φ j₁) = θ.comp
      (algebraMap (G j₁) (MvPolynomial (Fin n) (G j₁) ⧸ Ideal.span (Set.range q₁))) := by
    ext x
    change algebraMap A D (φ j₁ x)
      = e.symm (Ideal.Quotient.mk (Ideal.span (Set.range g)) (MvPolynomial.map (φ j₁) (C x)))
    rw [MvPolynomial.map_C]
    exact (e.symm.commutes (φ j₁ x)).symm
  -- Step (4): surjectivity on spectra at a yet later stage.
  obtain ⟨j₂, h₁₂, hsurj₂⟩ :=
    exists_ge_surjective_comap_quotient_of_directed hφ hsurj hzero q₁ (algebraMap A D) θ hcomm hD
  set q₂ : Fin n → MvPolynomial (Fin n) (G j₂) := fun k ↦ map (f j₁ j₂ h₁₂) (q₁ k) with hq₂def
  refine ⟨n, j₂, hi₀.trans (h₀₁.trans h₁₂), q₂, ?_, hsurj₂, ?_⟩
  · -- Étaleness is carried from `j₁` to `j₂`: the family there presents the base change.
    let := (f j₁ j₂ h₁₂).toAlgebra
    have := hetale₁
    obtain ⟨ebc⟩ := nonempty_quotientSpanEquiv_tensor_of_le (f := f) h₁₂ q₁
    exact Algebra.Etale.of_equiv ebc
  · -- The presentation at `j₂` still reads as the presentation of `D` over `A`.
    exact ⟨e.trans (Ideal.quotientEquivAlgOfEq A
      (congrArg (Ideal.span ∘ Set.range) (funext (hmap h₁₂ q₁ hq₁)))).symm⟩

end MvPolynomial

end
