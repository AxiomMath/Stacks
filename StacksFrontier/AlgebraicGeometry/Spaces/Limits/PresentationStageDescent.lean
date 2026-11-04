module

public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationBaseChangeSquare
public import StacksFrontier.RingTheory.Etale.DirectedColimitPresentation
public import StacksFrontier.RingTheory.Etale.DirectedColimitPresentationSupplement

/-!
# Descending a standard-étale presentation to a stage, along two colimit systems

The commutative-algebra heart of the proof of Stacks 07SQ is this. Let `(M i)` be a directed
system of rings with colimit `A`, let `(N i)` be a second one with colimit `B`, and let
`ψ i : M i →+* N i` be a compatible family inducing `ψ : A →+* B` — in the application `M i` is a
model of the global functions of the stage `X_i`, `N i` the regular functions of the chart `U_i`,
and `ψ i` restriction of global functions to the chart. Let

`B = A[x₁, …, xₙ] ⧸ (g₁, …, gₙ)`

be a standard-étale presentation of the colimit, in the sense that the Jacobian determinant is
invertible, presented through elements `h₁, …, hₙ` of `B` killing the `g_λ`, and suppose moreover
that `Spec B ⟶ Spec A` is surjective. Then *all of this descends to one stage*: there is an index
`j`, above any prescribed one, together with polynomials over `M j` whose images are the `g_λ`,
elements of `N j` whose images are the `h_ν` and which kill those polynomials, with invertible
Jacobian determinant and with `Spec (M j[x] ⧸ (g)) ⟶ Spec (M j)` surjective.

## Main results

* `AlgebraicGeometry.Space.exists_ge_presentationStageDescent`: the descent, as just described.

## Implementation notes

*Why the four clauses land at one index.* Each of them is descended by its own lemma of
`StacksFrontier.RingTheory.Etale.DirectedColimitPresentation`, and each produces an index of its own;
the clauses are then collected at the last of those indices. Three of the four transport upwards
for free — the images of the polynomials and of the elements are unchanged by a further transition
(`MvPolynomial.map_map_eq_of_comp` and the compatibility of the second system), the relations are
the image of a vanishing element under a ring homomorphism
(`AlgebraicGeometry.Space.eval₂_map_mt_eq_zero`), and invertibility of the Jacobian determinant is
carried along `AlgebraicGeometry.Space.presentationBaseChangeHom` because the determinant commutes
with base change (`MvPolynomial.map_detJacobian`). Surjectivity of the spectrum does *not*
transport upwards for free, so it is descended **last**, at the index the other three already hold
at; that is the only reason the order of the steps matters.

*Why the two systems are kept separate.* The polynomials live over the first system and the chosen
elements over the second, so a common stage has to be found for two different directed systems
indexed by the same poset; both are therefore taken as hypotheses in the elementwise form, exactly
the three clauses `Stacks.IsStagesColimit` supplies.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 00U9](https://stacks.math.columbia.edu/tag/00U9)
* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
-/

@[expose] public section

open MvPolynomial

universe u

namespace AlgebraicGeometry.Space

/-- The structure homomorphism of a presentation is the algebra map of the quotient. -/
theorem algebraMap_eq_presentationStructureHom {A : Type u} [CommRing A] {m : ℕ}
    (g : Fin m → MvPolynomial (Fin m) A) :
    algebraMap A (presentationAlgebra g) = presentationStructureHom g := rfl

/-- Evaluating a mapped polynomial at transported points transports the evaluation. -/
private theorem eval₂_map_eq_of_comp {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R']
    [CommRing S'] {ψ : R →+* S} {ψ' : R' →+* S'} {φ : R →+* R'} {φ' : S →+* S'}
    (hcomp : ψ'.comp φ = φ'.comp ψ) {m : ℕ} (g : MvPolynomial (Fin m) R) (h : Fin m → S) :
    MvPolynomial.eval₂ ψ' (fun k => φ' (h k)) (MvPolynomial.map φ g) =
      φ' (MvPolynomial.eval₂ ψ h g) := by
  rw [MvPolynomial.eval₂_map, hcomp, ← MvPolynomial.hom_eval₂]

section Descent

variable {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
  {M : ι → Type u} [∀ i, CommRing (M i)] {mt : ∀ i j, i ≤ j → M i →+* M j}
  [DirectedSystem M fun i j h => mt i j h]
  {Al : Type u} [CommRing Al] {mπ : ∀ i, M i →+* Al}
  {N : ι → Type u} [∀ i, CommRing (N i)] {nt : ∀ i j, i ≤ j → N i →+* N j}
  [DirectedSystem N fun i j h => nt i j h]
  {Bl : Type u} [CommRing Bl] {nπ : ∀ i, N i →+* Bl}
  (hm1 : ∀ i j (h : i ≤ j) (x : M i), mπ j (mt i j h x) = mπ i x)
  (hm2 : ∀ a : Al, ∃ (i : ι) (x : M i), mπ i x = a)
  (hm3 : ∀ (i : ι) (x : M i), mπ i x = 0 → ∃ (j : ι) (h : i ≤ j), mt i j h x = 0)
  (hn1 : ∀ i j (h : i ≤ j) (x : N i), nπ j (nt i j h x) = nπ i x)
  (hn2 : ∀ a : Bl, ∃ (i : ι) (x : N i), nπ i x = a)
  (hn3 : ∀ (i : ι) (x : N i), nπ i x = 0 → ∃ (j : ι) (h : i ≤ j), nt i j h x = 0)
  {ψ : ∀ i, M i →+* N i}
  (hψt : ∀ i j (h : i ≤ j) (x : M i), nt i j h (ψ i x) = ψ j (mt i j h x))
  {ψl : Al →+* Bl} (hψl : ∀ (i : ι) (x : M i), nπ i (ψ i x) = ψl (mπ i x))

section Transport

include hψt

omit [IsDirectedOrder ι] [Nonempty ι] [DirectedSystem M fun i j h => mt i j h]
  [DirectedSystem N fun i j h => nt i j h] in
/-- Transporting the relations of a presentation along a transition of the two systems. -/
theorem eval₂_map_mt_eq_zero {i j : ι} (hij : i ≤ j) {m : ℕ}
    {g : Fin m → MvPolynomial (Fin m) (M i)} {h : Fin m → N i}
    (hr : ∀ l, MvPolynomial.eval₂ (ψ i) h (g l) = 0) (l : Fin m) :
    MvPolynomial.eval₂ (ψ j) (fun k => nt i j hij (h k))
        (MvPolynomial.map (mt i j hij) (g l)) = 0 := by
  rw [eval₂_map_eq_of_comp (RingHom.ext fun x => (hψt i j hij x).symm), hr l, map_zero]

end Transport

include hm1 hm2 hm3 hn1 hn2 hn3 hψt hψl

/-- **The whole standard-étale presentation of the proof of Stacks 07SQ descends to a stage.** -/
theorem exists_ge_presentationStageDescent
    {m : ℕ} (gl : Fin m → MvPolynomial (Fin m) Al) (hl : Fin m → Bl)
    (hrel : ∀ l, MvPolynomial.eval₂ ψl hl (gl l) = 0)
    (hΔ : IsUnit (Ideal.Quotient.mk (Ideal.span (Set.range gl)) (detJacobian gl)))
    (hsurj : Function.Surjective (PrimeSpectrum.comap ψl)) (i₀ : ι) :
    ∃ (j : ι) (_ : i₀ ≤ j) (g : Fin m → MvPolynomial (Fin m) (M j)) (h : Fin m → N j)
      (_ : ∀ l, MvPolynomial.eval₂ (ψ j) h (g l) = 0),
      (∀ k, MvPolynomial.map (mπ j) (g k) = gl k) ∧ (∀ k, nπ j (h k) = hl k) ∧
        IsUnit (Ideal.Quotient.mk (Ideal.span (Set.range g)) (detJacobian g)) ∧
        Function.Surjective
          (PrimeSpectrum.comap (algebraMap (M j) (presentationAlgebra g))) := by
  classical
  -- transporting polynomials with the right image in the colimit keeps the image
  have hlift : ∀ {a b : ι} (hab : a ≤ b) (g : Fin m → MvPolynomial (Fin m) (M a)),
      (∀ k, MvPolynomial.map (mπ a) (g k) = gl k) →
        ∀ k, MvPolynomial.map (mπ b) (MvPolynomial.map (mt a b hab) (g k)) = gl k :=
    fun hab g hg k => by rw [MvPolynomial.map_map_eq_of_comp hm1, hg]
  -- the polynomials come from a stage
  obtain ⟨j1, hi0j1, g1, hg1⟩ :=
    MvPolynomial.exists_ge_forall_map_eq_square_of_directed hm1 hm2 gl i₀
  -- the chosen elements come from a later stage
  obtain ⟨j2, hj12, h2, hh2⟩ := Ring.exists_ge_forall_eq_of_directed hn1 hn2 hl j1
  -- both at the stage `j2`
  have hg2 := hlift hj12 g1 hg1
  -- the relations vanish at the colimit, hence at a later stage
  have hvan : ∀ l, nπ j2 (MvPolynomial.eval₂ (ψ j2) h2
      (MvPolynomial.map (mt j1 j2 hj12) (g1 l))) = 0 := by
    intro l
    rw [MvPolynomial.eval₂_comp_left,
      show (nπ j2).comp (ψ j2) = ψl.comp (mπ j2) from RingHom.ext (hψl j2),
      show (⇑(nπ j2) ∘ h2) = hl from funext hh2, ← MvPolynomial.eval₂_map, hg2 l, hrel l]
  obtain ⟨j3, hj23, hj3⟩ := Ring.exists_ge_forall_eq_zero_of_directed hn3
    (fun l => MvPolynomial.eval₂ (ψ j2) h2 (MvPolynomial.map (mt j1 j2 hj12) (g1 l))) hvan
  obtain ⟨g3, h3, hg3, hh3, hr3⟩ :
      ∃ (g3 : Fin m → MvPolynomial (Fin m) (M j3)) (h3 : Fin m → N j3),
        (∀ k, MvPolynomial.map (mπ j3) (g3 k) = gl k) ∧ (∀ k, nπ j3 (h3 k) = hl k) ∧
          (∀ l, MvPolynomial.eval₂ (ψ j3) h3 (g3 l) = 0) := by
    refine ⟨fun k => MvPolynomial.map (mt j2 j3 hj23)
        (MvPolynomial.map (mt j1 j2 hj12) (g1 k)),
      fun k => nt j2 j3 hj23 (h2 k), fun k => ?_, fun k => ?_, fun l => ?_⟩
    · exact hlift hj23 _ hg2 k
    · rw [hn1, hh2]
    · exact (eval₂_map_eq_of_comp (RingHom.ext fun x => (hψt j2 j3 hj23 x).symm) _ _).trans
        (hj3 l)
  -- the Jacobian determinant is invertible at a later stage
  have hΔ3 : IsUnit (Ideal.Quotient.mk
      (Ideal.span (Set.range fun k => MvPolynomial.map (mπ j3) (g3 k)))
      (detJacobian fun k => MvPolynomial.map (mπ j3) (g3 k))) := by
    rw [show (fun k => MvPolynomial.map (mπ j3) (g3 k)) = gl from funext hg3]
    exact hΔ
  obtain ⟨j4, hj34, hΔ4⟩ :=
    MvPolynomial.exists_ge_isUnit_detJacobian_of_directed hm1 hm2 hm3 g3 hΔ3
  -- the spectrum of the presentation is surjective at a later stage
  have hg4 := hlift hj34 g3 hg3
  have hrel4 : ∀ l, MvPolynomial.eval₂ (ψl.comp (mπ j4)) hl
      (MvPolynomial.map (mt j3 j4 hj34) (g3 l)) = 0 := by
    intro l
    rw [← MvPolynomial.eval₂_map, hg4 l, hrel l]
  obtain ⟨j5, hj45, hs5⟩ := MvPolynomial.exists_ge_surjective_comap_quotient_of_directed
    hm1 hm2 hm3 (fun k => MvPolynomial.map (mt j3 j4 hj34) (g3 k)) ψl
    (coordinateHom (fun k => MvPolynomial.map (mt j3 j4 hj34) (g3 k))
      (ψl.comp (mπ j4)) hl hrel4)
    (coordinateHom_comp_presentationStructureHom _ _ hl hrel4).symm hsurj
  -- everything at the stage `j5`
  refine ⟨j5, hi0j1.trans (hj12.trans (hj23.trans (hj34.trans hj45))),
    fun k => MvPolynomial.map (mt j4 j5 hj45)
      (MvPolynomial.map (mt j3 j4 hj34) (g3 k)),
    fun k => nt j4 j5 hj45 (nt j3 j4 hj34 (h3 k)), fun l => ?_, fun k => ?_, fun k => ?_,
    ?_, hs5⟩
  · exact eval₂_map_mt_eq_zero hψt hj45 (eval₂_map_mt_eq_zero hψt hj34 hr3) l
  · exact hlift hj45 _ hg4 k
  · rw [hn1, hn1, hh3]
  · have hmap := (hΔ4.map (presentationBaseChangeHom (mt j4 j5 hj45)
      (fun k => MvPolynomial.map (mt j3 j4 hj34) (g3 k))))
    rwa [presentationBaseChangeHom_mk, MvPolynomial.map_detJacobian] at hmap


end Descent

end AlgebraicGeometry.Space

end
