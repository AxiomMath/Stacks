module

public import StacksFrontier.RingTheory.Rig.Algebraization.RigSmoothAlgebraizationOfGRing
public import StacksFrontier.RingTheory.Rig.RigSmoothAlgEquiv
public import StacksFrontier.RingTheory.RigSmooth.ComparisonAlgHom
public import StacksFrontier.RingTheory.RigSmooth.PerturbationAlgEquiv

/-!
# Proposition 0GAT, with Lemma 0GAR discharged

`Rig.PerturbationStableQuotients` states Lemma 0GAR for any rig-smooth object `B` of the
category of Tag 0AL4 that is presented by a resolution `P^⊕t --K--> P^⊕m --g--> P`. The library's
Lemma 0GAR, `Rig.PerturbedPresentation.exists_algEquiv_of_perturbation`, states it for the
tautological object `P ⧸ g(P^⊕m)` instead, measures closeness by `CongruentModPow`, and writes
the presented ideal as `LinearMap.range g`. This file translates the second form into the first
and feeds it to the assembly of Proposition 0GAT,
`Rig.exists_finiteType_adicCompletion_algEquiv_of_isRigSmooth'`, which proves every other step
of the source's argument (Tags 0AJP, 0A02, 0AGV, 07PV, 0AH3, 0AH5 with Popescu's Theorem 07GC,
and 0GAS).

The translation has three parts:

* rig-smoothness moves from `B` to `P ⧸ g(P^⊕m)` along the given isomorphism, by
  `Rig.isRigSmooth_of_algEquiv`, which also bridges the universes of the two carriers;
* `Ideal.span (Set.range g)` is the ideal `LinearMap.range g`;
* coordinatewise membership in `(IP)ⁿ` gives `CongruentModPow`.

## Main results

* `Rig.perturbationStableQuotients` — Lemma 0GAR in the form `Rig.PerturbationStableQuotients`,
  for every ideal of every Noetherian ring.
* `Rig.exists_finiteType_adicCompletion_algEquiv_of_isGRing_of_isRigSmooth` — Proposition 0GAT,
  with no hypotheses beyond the source's.

## References

* [Stacks Project, Tag 0GAR](https://stacks.math.columbia.edu/tag/0GAR)
* [Stacks Project, Tag 0GAT](https://stacks.math.columbia.edu/tag/0GAT)
-/

@[expose] public section

universe u v

namespace Rig

open PerturbedPresentation

/-- For a linear map into the ring, the ideal spanned by its image is its range. -/
private theorem span_range_eq_range {R : Type*} [CommRing R] {m : ℕ}
    (g : (Fin m → R) →ₗ[R] R) :
    Ideal.span (Set.range g) = (LinearMap.range g : Ideal R) := by
  rw [← LinearMap.coe_range]
  exact Submodule.span_eq (LinearMap.range g)

/-- A map into the ring that is coordinatewise congruent modulo `Jⁿ` is congruent modulo
`Jⁿ` in the sense of `CongruentModPow`. -/
private theorem congruentModPow_of_forall_sub_mem {R : Type*} [CommRing R] (J : Ideal R)
    {L : Type*} [AddCommGroup L] [Module R L] (g g' : L →ₗ[R] R) (n : ℕ)
    (h : ∀ x, g x - g' x ∈ J ^ n) : CongruentModPow J g g' n := by
  rintro _ ⟨x, rfl⟩
  rw [smul_eq_mul, Ideal.mul_top]
  exact h x

/-- A map into `R^m` whose coordinates are congruent modulo `Jⁿ` is congruent modulo `Jⁿ` in
the sense of `CongruentModPow`. -/
private theorem congruentModPow_pi_of_forall_sub_mem {R : Type*} [CommRing R] (J : Ideal R)
    {L : Type*} [AddCommGroup L] [Module R L] {m : ℕ} (K K' : L →ₗ[R] (Fin m → R)) (n : ℕ)
    (h : ∀ x i, K x i - K' x i ∈ J ^ n) : CongruentModPow J K K' n := by
  rintro _ ⟨x, rfl⟩
  rw [pi_eq_sum_univ ((K - K') x)]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem_smul (by simpa using h x i) Submodule.mem_top

/-- **Lemma 0GAR, in the form consumed by Proposition 0GAT.** Let `I` be an ideal of a
Noetherian ring `A`, `P = A[x₁, …, x_r]^∧`, and `P^⊕t --K--> P^⊕m --g--> P → B → 0` a resolution
of a rig-smooth object `B` of the category of Tag 0AL4. Then there is an `n` such that every
complex `P^⊕t --K'--> P^⊕m --g'--> P` congruent to it modulo `(IP)ⁿ` presents an `A`-algebra
isomorphic to `B`.

This is `Rig.PerturbedPresentation.exists_algEquiv_of_perturbation` (Tag 0GAR), stated for the
tautological quotient `P ⧸ g(P^⊕m)`, transported to `B` along the given isomorphism. -/
public theorem perturbationStableQuotients (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) : PerturbationStableQuotients.{u, v} A I := by
  intro r m t B g K hK hpres hB
  obtain ⟨e⟩ := hpres
  let eg : (completedPolynomialAlgebra I r ⧸
      (LinearMap.range g : Ideal (completedPolynomialAlgebra I r))) ≃ₐ[A] B.carrier :=
    (Ideal.quotientEquivAlgOfEq A (span_range_eq_range g).symm).trans e
  have hB' : IsRigSmooth (quotientObj A I r (LinearMap.range g)) :=
    isRigSmooth_of_algEquiv (B := quotientObj A I r (LinearMap.range g)) eg hB
  obtain ⟨n₀, hn₀⟩ := exists_algEquiv_of_perturbation A I r K g hK.symm hB'
  refine ⟨n₀, fun g' K' hcomplex hgg' hKK' => ?_⟩
  obtain ⟨-, ⟨f⟩⟩ := hn₀ n₀ le_rfl K' g' hcomplex
    (congruentModPow_pi_of_forall_sub_mem _ K K' n₀ hKK')
    (congruentModPow_of_forall_sub_mem _ g g' n₀ hgg')
  exact ⟨eg.symm.trans (f.trans (Ideal.quotientEquivAlgOfEq A (span_range_eq_range g').symm))⟩

/-- **Stacks Project, Proposition 0GAT.** Let `I` be an ideal of a Noetherian G-ring `A` and
let `B` be an object of the category of Tag 0AL4. If `B` is rig-smooth over `(A, I)`, then
there is a finite type `A`-algebra `C` and an isomorphism `B ≅ C^∧` of `A`-algebras.

Every step of the source's proof is carried out:
`Rig.exists_finiteType_adicCompletion_algEquiv_of_isRigSmooth'` runs the presentation (Tag 0AJP),
its finite free resolution, the henselization `H` of `(A[x], I A[x])` with its G-ring property
(Tags 07PV, 0AH3) and completion `P` (Tag 0AGV), the approximation of the resolution's relations
over `H` (Tag 0AH5, with Popescu's Theorem 07GC and Tag 0AH2), and the final algebraization
(Tag 0GAS); Lemma 0GAR is `Rig.perturbationStableQuotients`. -/
@[stacks 0GAT]
public theorem exists_finiteType_adicCompletion_algEquiv_of_isGRing_of_isRigSmooth
    (A : Type u) [CommRing A] [IsNoetherianRing A] (hA : IsGRing A) (I : Ideal A)
    (B : AdicFiniteTypeAlgebra.{u, v} A I) (hB : IsRigSmooth B) :
    ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra A C),
      Algebra.FiniteType A C ∧
        Nonempty (B.carrier ≃ₐ[A] AdicCompletion (I.map (algebraMap A C)) C) :=
  exists_finiteType_adicCompletion_algEquiv_of_isRigSmooth' A hA I B hB
    (perturbationStableQuotients A I)

end Rig

end
