module

public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.ArtinRees.AssociatedGraded
public import StacksFrontier.RingTheory.Rig.PresentationGenerators
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Perturbing the equations of a presentation over a completed polynomial ring

Let `A` be a Noetherian ring, `I ⊆ A` an ideal, `r ≥ 0`, and let
`P = A[x₁, …, x_r]^∧` be the `I`-adic completion of a polynomial ring. Stacks 0GAR says that
if `B` is the cokernel of a resolution

```
P^⊕t --K--> P^⊕m --(g₁, …, g_m)--> P → B → 0
```

and `B` is rig-smooth over `(A, I)`, then there is an integer `n` such that every complex
`P^⊕t --K'--> P^⊕m --(g'₁, …, g'_m)--> P` with `gᵢ - g'ᵢ ∈ IⁿP` and `K - K' ∈ Iⁿ Mat(m × t, P)`
has `B ≅ B' = P/(g'₁, …, g'_m)` as `A`-algebras.

This file develops the part of that statement which does not depend on rig-smoothness, namely
step (B) of the source proof together with the two reductions it feeds, and the final
"these facts force the comparison map to be an isomorphism" argument, which the source leaves
to the reader.

A linear map `g : P^⊕m → P` is the tuple `(g₁, …, g_m)`, its range is the ideal
`(g₁, …, g_m)`, and the cokernel `P ⧸ LinearMap.range g` is the algebra `B`. The perturbation
hypotheses `gᵢ - g'ᵢ ∈ IⁿP` and `K - K' ∈ Iⁿ Mat(m × t, P)` are
`CongruentModPow J g g' n` and `CongruentModPow J K K' n` for `J = IP`: the range of the
difference lands in `Jⁿ · ⊤`, which for a finite free module is exactly the condition that
every coordinate of every difference lies in `Jⁿ`.

## Main results

* `Rig.PerturbedPresentation.exists_isArtinReesConstant_pair`: the two maps of the resolution
  admit a common Artin-Rees constant.
* `Rig.PerturbedPresentation.ker_eq_range_of_congruentModPow`: step (B) of the source proof,
  exactness half — for `n` past the Artin-Rees constant the perturbed complex is again exact,
  so it is a resolution of `B'`.
* `Rig.PerturbedPresentation.associatedGradedEquivOfCongruentModPow`: step (B) of the source
  proof, graded half — `Gr_I(B) ≅ Gr_I(B')`.
* `Rig.PerturbedPresentation.exists_perturbationBound`: the two halves of step (B) packaged as
  the integer `c₁ + 1` the proof calls for, over an arbitrary Noetherian ring with
  `J ≤ jacobson ⊥`.
* `Rig.PerturbedPresentation.range_sup_pow_eq_of_congruentModPow` and
  `Rig.PerturbedPresentation.reductionEquivOfCongruentModPow`: the perturbation does not change
  the quotient modulo `Jⁿ`, which is the canonical isomorphism `B/IⁿB ≅ B'/IⁿB'` of the source
  proof.
* `Rig.PerturbedPresentation.surjective_of_surjective_mod`: a comparison map between adically
  complete algebras that is surjective modulo `I` is surjective (Stacks 0315 part (1)).
* `Rig.PerturbedPresentation.injective_of_graded_injective`: a comparison map which is injective
  on the graded pieces of the `I`-adic filtration is injective, by Krull's intersection theorem
  (Stacks 00IP).
* `Rig.PerturbedPresentation.algEquivOfSurjectiveModOfGradedInjective`: the two previous results
  assembled into the algebra isomorphism `B ≃ₐ[A] B'`. The isomorphism *is* the given
  comparison map; no choice is made.
* `Rig.PerturbedPresentation.map_algebraMap_le_jacobson_bot` and
  `Rig.PerturbedPresentation.exists_perturbationBound_completedPolynomial`: the previous results
  transported to `P = A[x₁, …, x_r]^∧` with `J = IP`, where the hypotheses
  `IsNoetherianRing P` and `J ≤ jacobson ⊥` are discharged.

## Implementation notes

Everything here is the content of Stacks 0GAR that is available; the layers of the source proof
that are **not** reached, and why, are as follows.

* Step (A) of the source proof chooses `c ≥ 0` with `I^c` annihilating
  `Ext¹_B(NL^∧_{B/A}, N)` for all `B`-modules `N`. This is immediate from the definition of
  rig-smoothness (`Rig.IsRigSmooth`, Stacks 0GAI) but is of no use on its own, because its
  only consumer is Stacks 0GAQ.
* Stacks 0GAQ — the lifting of an `A`-algebra map `B → B'/IⁿB'` to an `A`-algebra map
  `B → B'`, for `B` rig-smooth — is **not formalized in this repository**: there is no
  declaration carrying that tag and no declaration of that shape. It is the only source of the
  comparison map `φ : B → B'`, so the construction of `φ` is out of reach, and with it the
  full statement of 0GAR.
* Step (C) of the source proof needs the invariants `d(Gr_I(B))` and `q(Gr_I(B))` of
  Stacks 0GA6. In this repository those invariants exist only as the fields `d` and `q₀` of the
  hypothesis structure `Situation` of
  `StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BoundQAndD`, and nothing
  proves that a `Situation` exists for a given pair `(A, I)`. So the two summands
  `q₀ + (d₀ + 1) c` and `2 (d₀ + 1) c + 1` of the integer `n` of 0GAR cannot be produced, and
  `exists_perturbationBound` produces only the summand `c₁ + 1` coming from step (B).
* Consequently `algEquivOfSurjectiveModOfGradedInjective` carries the comparison map `φ` and
  its two properties as explicit hypotheses rather than constructing them. Its graded
  hypothesis `hgraded` — that `φ` does not move an element of `Jᵉ` into `J'^(e+1)` unless it
  was already in `J^(e+1)`, i.e. that the induced maps `IᵉB/Iᵉ⁺¹B → IᵉB'/Iᵉ⁺¹B'` are
  injective — is the one step of the source's final paragraph that is *not* discharged here:
  the source deduces it from `Gr_I(B) ≅ Gr_I(B')` by Stacks 06RN, which needs `Gr_I(B)` to be
  a finite module over the Noetherian ring `Gr_I(P)`. Neither
  `IsNoetherianRing (AssociatedGraded.gradedRing J P)` nor the finiteness of
  `AssociatedGraded.gradedModule J B` over it is available, and
  `associatedGraded_coker_equiv_of_congr` (Stacks 07VF) delivers a
  `AssociatedGraded.GradedLinearEquiv`, i.e. an isomorphism of graded modules over
  `Gr_J(P)`, not an isomorphism of graded rings.

Other hypotheses carried by the declarations below, all of them discharged in the final
section for the ring `P` that 0GAR is about:

* `hJ : J ≤ (⊥ : Ideal R).jacobson`, required by `artinRees_stability` (Stacks 07VE) and by
  `associatedGraded_coker_equiv_of_congr` (Stacks 07VF);
* `[IsNoetherianRing R]`, required by the same two results;
* `hcomplex : g'.comp K' = 0`, the hypothesis that the perturbed maps still form a complex;
  this is part of the statement of 0GAR and is not implied by the congruences.

`surjective_of_surjective_mod` and `injective_of_graded_injective` are stated for an arbitrary
pair of `A`-algebras rather than for `P`-quotients, since neither uses the presentation.
Separation of `B` is taken in the elementary form `hsep` ("an element of every power of `J` is
zero") rather than as `IsHausdorff`, so that it can be supplied either by Krull's intersection
theorem or by completeness.

## References

* [Stacks Project, Tag 0GAR](https://stacks.math.columbia.edu/tag/0GAR)
* [Stacks Project, Tag 00IP](https://stacks.math.columbia.edu/tag/00IP)
* [Stacks Project, Tag 07VE](https://stacks.math.columbia.edu/tag/07VE)
* [Stacks Project, Tag 07VF](https://stacks.math.columbia.edu/tag/07VF)
* [Stacks Project, Tag 0315](https://stacks.math.columbia.edu/tag/0315)
* [Stacks Project, Tag 06RN](https://stacks.math.columbia.edu/tag/06RN)
-/

@[expose] public noncomputable section

universe u v

namespace Rig.PerturbedPresentation

/-! ### Step (B): the Artin-Rees input -/

section ArtinRees

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- The two maps `K : R^⊕t → R^⊕m` and `g : R^⊕m → R` of a finite free two-step complex admit a
common constant in the Artin-Rees lemma: the targets are finite modules, so each map has one,
and a constant may be enlarged. -/
public theorem exists_isArtinReesConstant_pair (J : Ideal R) {t m : ℕ}
    (K : (Fin t → R) →ₗ[R] (Fin m → R)) (g : (Fin m → R) →ₗ[R] R) :
    ∃ c : ℕ, IsArtinReesConstant J K c ∧ IsArtinReesConstant J g c := by
  obtain ⟨c₁, h₁⟩ := exists_isArtinReesConstant J K
  obtain ⟨c₂, h₂⟩ := exists_isArtinReesConstant J g
  exact ⟨max c₁ c₂, h₁.mono (le_max_left _ _), h₂.mono (le_max_right _ _)⟩

/-- **Step (B) of Stacks 0GAR, exactness half.** If `c` works for `K` and `g` in the Artin-Rees
lemma, the complex `R^⊕t --K--> R^⊕m --g--> R` is exact and the perturbed maps `K'`, `g'` form a
complex congruent to it modulo `Jⁿ` with `n ≥ c + 1`, then the perturbed complex is exact as
well; that is, `R^⊕t --K'--> R^⊕m --g'--> R → B' → 0` is again a resolution. -/
public theorem ker_eq_range_of_congruentModPow (J : Ideal R)
    (hJ : J ≤ (⊥ : Ideal R).jacobson) {t m : ℕ}
    {K K' : (Fin t → R) →ₗ[R] (Fin m → R)} {g g' : (Fin m → R) →ₗ[R] R} {c n : ℕ}
    (hn : c + 1 ≤ n) (hcomplex : g'.comp K' = 0)
    (hK : IsArtinReesConstant J K c) (hg : IsArtinReesConstant J g c)
    (hexact : LinearMap.ker g = LinearMap.range K)
    (hKK' : CongruentModPow J K K' n) (hgg' : CongruentModPow J g g' n) :
    LinearMap.ker g' = LinearMap.range K' :=
  (artinRees_stability J hJ K K' g g' c hcomplex hK hg hexact
    (hKK'.mono hn) (hgg'.mono hn)).2

/-- **Step (B) of Stacks 0GAR, graded half.** Under the hypotheses of
`ker_eq_range_of_congruentModPow`, the two cokernels `B = R ⧸ (g₁, …, g_m)` and
`B' = R ⧸ (g'₁, …, g'_m)` have isomorphic associated graded modules for the `J`-adic
filtration: `Gr_J(B) ≅ Gr_J(B')`. -/
public def associatedGradedEquivOfCongruentModPow (J : Ideal R)
    (hJ : J ≤ (⊥ : Ideal R).jacobson) {t m : ℕ}
    {K K' : (Fin t → R) →ₗ[R] (Fin m → R)} {g g' : (Fin m → R) →ₗ[R] R} {c n : ℕ}
    (hn : c + 1 ≤ n) (hcomplex : g'.comp K' = 0)
    (hK : IsArtinReesConstant J K c) (hg : IsArtinReesConstant J g c)
    (hexact : LinearMap.ker g = LinearMap.range K)
    (hKK' : CongruentModPow J K K' n) (hgg' : CongruentModPow J g g' n) :
    AssociatedGraded.GradedLinearEquiv J (R ⧸ LinearMap.range g) (R ⧸ LinearMap.range g') :=
  associatedGraded_coker_equiv_of_congr J hJ K g K' g' c hcomplex hK hg hexact
    (hKK'.mono hn) (hgg'.mono hn)

/-- `Jⁿ · R = Jⁿ`: the submodule of `R` cut out by the `n`-th power of `J` is that power. -/
private theorem pow_smul_top_eq_pow {R : Type u} [CommRing R] (J : Ideal R) (n : ℕ) :
    (J ^ n) • (⊤ : Submodule R R) = (J ^ n : Ideal R) := by
  simp

/-- The perturbation does not change the ideal modulo `Jⁿ`: if `g` and `g'` agree modulo `Jⁿ`
then `(g₁, …, g_m) + Jⁿ = (g'₁, …, g'_m) + Jⁿ`. This is what makes the canonical map
`B → B'/IⁿB'` of the source proof an isomorphism `B/IⁿB → B'/IⁿB'`. -/
public theorem range_sup_pow_eq_of_congruentModPow {R : Type u} [CommRing R] (J : Ideal R)
    {m n : ℕ} {g g' : (Fin m → R) →ₗ[R] R} (hgg' : CongruentModPow J g g' n) :
    (LinearMap.range g : Ideal R) ⊔ J ^ n = (LinearMap.range g' : Ideal R) ⊔ J ^ n := by
  have key : ∀ u u' : (Fin m → R) →ₗ[R] R, CongruentModPow J u u' n →
      (LinearMap.range u : Ideal R) ≤ (LinearMap.range u' : Ideal R) ⊔ J ^ n := by
    intro u u' h x hx
    obtain ⟨v, rfl⟩ := hx
    have hdiff : u v - u' v ∈ (J ^ n : Ideal R) := by
      rw [← pow_smul_top_eq_pow]
      have := h (LinearMap.mem_range_self (u - u') v)
      rwa [LinearMap.sub_apply] at this
    have hsum := Submodule.add_mem ((LinearMap.range u' : Ideal R) ⊔ J ^ n)
      (Submodule.mem_sup_left (LinearMap.mem_range_self u' v))
      (Submodule.mem_sup_right hdiff)
    rwa [add_sub_cancel] at hsum
  exact le_antisymm (sup_le (key g g' hgg') le_sup_right)
    (sup_le (key g' g hgg'.symm) le_sup_right)

/-- The canonical isomorphism `B/IⁿB ≅ B'/IⁿB'` of the proof of Stacks 0GAR, in the form
`R ⧸ ((g₁, …, g_m) + Jⁿ) ≅ R ⧸ ((g'₁, …, g'_m) + Jⁿ)`: both sides are the same quotient of `R`,
because the two ideals agree. It is an isomorphism of algebras over any base `A` under `R`. -/
public def reductionEquivOfCongruentModPow (A : Type v) [CommRing A] {R : Type u} [CommRing R]
    [Algebra A R] (J : Ideal R) {m n : ℕ} {g g' : (Fin m → R) →ₗ[R] R}
    (hgg' : CongruentModPow J g g' n) :
    (R ⧸ ((LinearMap.range g : Ideal R) ⊔ J ^ n)) ≃ₐ[A]
      (R ⧸ ((LinearMap.range g' : Ideal R) ⊔ J ^ n)) :=
  Ideal.quotientEquivAlgOfEq A (range_sup_pow_eq_of_congruentModPow J hgg')

/-- **The integer of step (B) of Stacks 0GAR.** Over a Noetherian ring `R` with
`J ≤ jacobson ⊥`, a resolution `R^⊕t --K--> R^⊕m --g--> R` determines an integer `n₀` such that
for every `n ≥ n₀` and every complex `R^⊕t --K'--> R^⊕m --g'--> R` congruent to it modulo `Jⁿ`:
the perturbed complex is exact, the two cokernels have isomorphic associated graded modules, and
the two ideals agree modulo `Jⁿ`.

This is the summand `c₁ + 1` of the integer `n` of 0GAR; see the implementation notes for the
summands coming from steps (A) and (C), which are not available. -/
public theorem exists_perturbationBound (J : Ideal R) (hJ : J ≤ (⊥ : Ideal R).jacobson)
    {t m : ℕ} (K : (Fin t → R) →ₗ[R] (Fin m → R)) (g : (Fin m → R) →ₗ[R] R)
    (hexact : LinearMap.ker g = LinearMap.range K) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (K' : (Fin t → R) →ₗ[R] (Fin m → R)) (g' : (Fin m → R) →ₗ[R] R),
      g'.comp K' = 0 → CongruentModPow J K K' n → CongruentModPow J g g' n →
        LinearMap.ker g' = LinearMap.range K' ∧
        Nonempty (AssociatedGraded.GradedLinearEquiv J
          (R ⧸ LinearMap.range g) (R ⧸ LinearMap.range g')) ∧
        (LinearMap.range g : Ideal R) ⊔ J ^ n = (LinearMap.range g' : Ideal R) ⊔ J ^ n := by
  obtain ⟨c, hK, hg⟩ := exists_isArtinReesConstant_pair J K g
  refine ⟨c + 1, fun n hn K' g' hcomplex hKK' hgg' => ⟨?_, ⟨?_⟩, ?_⟩⟩
  · exact ker_eq_range_of_congruentModPow J hJ hn hcomplex hK hg hexact hKK' hgg'
  · exact associatedGradedEquivOfCongruentModPow J hJ hn hcomplex hK hg hexact hKK' hgg'
  · exact range_sup_pow_eq_of_congruentModPow J hgg'

end ArtinRees

/-! ### From a comparison map to an isomorphism -/

section Comparison

variable {A : Type v} [CommRing A] {B B' : Type u} [CommRing B] [CommRing B']
  [Algebra A B] [Algebra A B'] (I : Ideal A)

/-- **Stacks 0315, part (1), in the form the proof of 0GAR uses it.** An `A`-algebra map
`φ : B → B'` whose reduction modulo `I` is surjective is surjective, provided `B` is
`IB`-precomplete and `B'` is `IB'`-Hausdorff. -/
public theorem surjective_of_surjective_mod (φ : B →ₐ[A] B')
    (hB : IsPrecomplete (I.map (algebraMap A B)) B)
    (hB' : IsHausdorff (I.map (algebraMap A B')) B')
    (hmod : Function.Surjective
      ((Ideal.Quotient.mk (I.map (algebraMap A B'))).comp (φ : B →+* B'))) :
    Function.Surjective φ := by
  have hmap : (I.map (algebraMap A B)).map (φ : B →+* B') = I.map (algebraMap A B') := by
    rw [Ideal.map_map]
    congr 1
    exact φ.comp_algebraMap
  have : IsPrecomplete (I.map (algebraMap A B)) B := hB
  have : IsHausdorff ((I.map (algebraMap A B)).map (φ : B →+* B')) B' := hmap ▸ hB'
  refine surjective_of_mk_map_comp_surjective (I := I.map (algebraMap A B)) (φ : B →+* B') ?_
  rw [hmap]
  exact hmod

/-- **The injectivity half of the final paragraph of the proof of Stacks 0GAR.** Let
`φ : B → B'` be a ring map, `J ⊆ B` an ideal and `J' = φ(J)B'`. Suppose that an element of `B`
lying in every power of `J` is zero (Krull's intersection theorem, Stacks 00IP, for `B`
separated in the `J`-adic topology), and that `φ` is injective on the graded pieces of the
`J`-adic filtration in the sense that `x ∈ Jᵉ` and `φ x ∈ J'ᵉ⁺¹` force `x ∈ Jᵉ⁺¹`. Then `φ` is
injective.

An element of the kernel lies in every power of `J` by induction on the exponent: it lies in
`J⁰ = B`, and if it lies in `Jᵉ` then its image, being `0`, lies in `J'ᵉ⁺¹`, so the graded
hypothesis puts it in `Jᵉ⁺¹`. -/
@[sga "3 VIIB 5.1.5" "(i)(b), special case"]
public theorem injective_of_graded_injective (φ : B →+* B') (J : Ideal B)
    (hsep : ∀ x : B, (∀ e : ℕ, x ∈ J ^ e) → x = 0)
    (hgraded : ∀ (e : ℕ) (x : B), x ∈ J ^ e → φ x ∈ (J.map φ) ^ (e + 1) → x ∈ J ^ (e + 1)) :
    Function.Injective φ := by
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro x hx
  refine hsep x fun e => ?_
  induction e with
  | zero => simp
  | succ e ih =>
    refine hgraded e x ih ?_
    rw [hx]
    exact Submodule.zero_mem _

/-- **The isomorphism `B ≃ₐ[A] B'` of Stacks 0GAR, given the comparison map.** An `A`-algebra
map `φ : B → B'` which is surjective modulo `I` and injective on the graded pieces of the
`I`-adic filtration is an isomorphism of `A`-algebras; the isomorphism is `φ` itself.

The hypotheses are exactly those the final paragraph of the source proof has available about the
map `φ` produced by Stacks 0GAQ. See the implementation notes for what is not discharged. -/
public def algEquivOfSurjectiveModOfGradedInjective (φ : B →ₐ[A] B')
    (hB : IsPrecomplete (I.map (algebraMap A B)) B)
    (hB' : IsHausdorff (I.map (algebraMap A B')) B')
    (hmod : Function.Surjective
      ((Ideal.Quotient.mk (I.map (algebraMap A B'))).comp (φ : B →+* B')))
    (hsep : ∀ x : B, (∀ e : ℕ, x ∈ (I.map (algebraMap A B)) ^ e) → x = 0)
    (hgraded : ∀ (e : ℕ) (x : B), x ∈ (I.map (algebraMap A B)) ^ e →
      φ x ∈ ((I.map (algebraMap A B)).map (φ : B →+* B')) ^ (e + 1) →
        x ∈ (I.map (algebraMap A B)) ^ (e + 1)) :
    B ≃ₐ[A] B' :=
  AlgEquiv.ofBijective φ
    ⟨injective_of_graded_injective (φ : B →+* B') (I.map (algebraMap A B)) hsep hgraded,
      surjective_of_surjective_mod I φ hB hB' hmod⟩

end Comparison

/-! ### The completed polynomial ring `P = A[x₁, …, x_r]^∧` -/

section CompletedPolynomial

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (r : ℕ)

omit [IsNoetherianRing A] in
/-- The structural map `A[x₁, …, x_r] → P` composed with `A → A[x₁, …, x_r]` is the structural
map `A → P`. -/
public theorem algebraMap_comp_C :
    (algebraMap (MvPolynomial (Fin r) A) (completedPolynomialAlgebra I r)).comp
        (MvPolynomial.C : A →+* MvPolynomial (Fin r) A)
      = algebraMap A (completedPolynomialAlgebra I r) := by
  ext a
  simp [AdicCompletion.algebraMap_apply]

/-- `P = A[x₁, …, x_r]^∧` is complete for the ideal `IP`, hence `IP ≤ jacobson ⊥` (Stacks
05GI). This is the hypothesis `hJ` of the results above, for the ring `P` that Stacks 0GAR is
about. -/
public theorem map_algebraMap_le_jacobson_bot :
    I.map (algebraMap A (completedPolynomialAlgebra I r)) ≤
      (⊥ : Ideal (completedPolynomialAlgebra I r)).jacobson := by
  have hmap :
      (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A)).map
          (algebraMap (MvPolynomial (Fin r) A) (completedPolynomialAlgebra I r))
        = I.map (algebraMap A (completedPolynomialAlgebra I r)) := by
    rw [Ideal.map_map, algebraMap_comp_C]
  have : IsAdicComplete (I.map (algebraMap A (completedPolynomialAlgebra I r)))
      (completedPolynomialAlgebra I r) := by
    rw [← hmap]
    exact AdicCompletion.isAdicComplete_self _
      (Ideal.fg_of_isNoetherianRing (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A)))
  exact IsAdicComplete.le_jacobson_bot _

/-- **Step (B) of Stacks 0GAR over `P = A[x₁, …, x_r]^∧`.** Given a resolution
`P^⊕t --K--> P^⊕m --(g₁, …, g_m)--> P → B → 0`, there is an integer `n₀` such that for every
`n ≥ n₀` and every complex `P^⊕t --K'--> P^⊕m --(g'₁, …, g'_m)--> P` with
`gᵢ - g'ᵢ ∈ IⁿP` and `K - K' ∈ Iⁿ Mat(m × t, P)`, the perturbed complex is again a resolution,
`Gr_I(B) ≅ Gr_I(B')`, and `B/IⁿB = B'/IⁿB'`.

This is `exists_perturbationBound` with both of its ring-level hypotheses discharged:
`P` is Noetherian by Stacks 0316 and `IP ≤ jacobson ⊥` by
`map_algebraMap_le_jacobson_bot`. The remaining summands of the integer `n` of 0GAR are not
available; see the implementation notes. -/
public theorem exists_perturbationBound_completedPolynomial {t m : ℕ}
    (K : (Fin t → completedPolynomialAlgebra I r) →ₗ[completedPolynomialAlgebra I r]
      (Fin m → completedPolynomialAlgebra I r))
    (g : (Fin m → completedPolynomialAlgebra I r) →ₗ[completedPolynomialAlgebra I r]
      completedPolynomialAlgebra I r)
    (hexact : LinearMap.ker g = LinearMap.range K) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ (K' : (Fin t → completedPolynomialAlgebra I r) →ₗ[completedPolynomialAlgebra I r]
          (Fin m → completedPolynomialAlgebra I r))
        (g' : (Fin m → completedPolynomialAlgebra I r) →ₗ[completedPolynomialAlgebra I r]
          completedPolynomialAlgebra I r),
      g'.comp K' = 0 →
      CongruentModPow (I.map (algebraMap A (completedPolynomialAlgebra I r))) K K' n →
      CongruentModPow (I.map (algebraMap A (completedPolynomialAlgebra I r))) g g' n →
        LinearMap.ker g' = LinearMap.range K' ∧
        Nonempty (AssociatedGraded.GradedLinearEquiv
          (I.map (algebraMap A (completedPolynomialAlgebra I r)))
          (completedPolynomialAlgebra I r ⧸ LinearMap.range g)
          (completedPolynomialAlgebra I r ⧸ LinearMap.range g')) ∧
        (LinearMap.range g : Ideal (completedPolynomialAlgebra I r)) ⊔
            (I.map (algebraMap A (completedPolynomialAlgebra I r))) ^ n
          = (LinearMap.range g' : Ideal (completedPolynomialAlgebra I r)) ⊔
            (I.map (algebraMap A (completedPolynomialAlgebra I r))) ^ n :=
  exists_perturbationBound _ (map_algebraMap_le_jacobson_bot A I r) K g hexact

end CompletedPolynomial

end Rig.PerturbedPresentation

end
