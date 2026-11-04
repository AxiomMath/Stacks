module

public import StacksFrontier.Algebra.Category.Ring.FinitePresentation
public import StacksFrontier.RingTheory.ApproximationProperty.Defs
public import StacksFrontier.RingTheory.Etale.FilteredColimit.Basic
public import StacksFrontier.RingTheory.Etale.IndEtaleFibres
public import StacksFrontier.RingTheory.GRing.Henselization
public import StacksFrontier.RingTheory.Henselian.EtaleLifting
public import StacksFrontier.RingTheory.Henselian.Henselization.Basic
public import StacksFrontier.RingTheory.Henselian.HenselizationCompletion
public import StacksFrontier.RingTheory.Regular.RegularRingHom
public import StacksFrontier.RingTheory.Rig.Henselization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Approximation in a henselization, and G-rings through henselization

Let `Λ` be a Noetherian ring, let `𝔪 ⊂ Λ` be a maximal ideal, let `R = Λ_𝔪^∧` be the completion
of the local ring `Λ_𝔪`, and let `H` be a henselization of `Λ_𝔪`. Stacks Example 07XI derives
from the conclusion of Lemma 07XH that every finite system of polynomial equations over `Λ`
with a solution in `R` has a solution in `H`, and then argues: "In other words, the approximation
property holds for `Λ_𝔪^h`. This implies that `Λ_𝔪^h` is a G-ring [...] which in turn implies
that `Λ_𝔪` is a G-ring." This file proves the first and the last of these three implications.
The middle one, from the approximation property to the G-ring property (the reference the source
leaves missing), is Rotthaus' theorem `IsLocalRing.HasApproximationProperty.isGRing` in
`StacksFrontier.RingTheory.ApproximationProperty.GRing`.

## Main results

* `Stacks.ApproximationProperty.hasApproximationProperty_of_forall_exists_solution`: if every
  finite system over `Λ` with a solution in `R` has a solution in `H`, then `H` has the
  approximation property of Stacks 07BX, for systems with coefficients in `H` and solutions in
  the completion of `H`.
* `Stacks.ApproximationProperty.isGRing_of_isGRing_isHenselization`: a Noetherian local ring
  whose henselization is a G-ring is a G-ring.
* `Stacks.ApproximationProperty.isGRing_atPrime_of_isGRing_isHenselization`: the case
  `A = Λ_𝔪` of the previous result.

## Implementation notes

*The approximation property.* Let `f_1, …, f_m` be polynomials over `H` with a common zero `x` in
the completion `Ĥ`. Since `H` is a filtered colimit of étale `Λ_𝔪`-algebras, the factorization
criterion of Stacks 07C3 puts all coefficients of the `f_j` into the image of an étale
`Λ_𝔪`-algebra `φ : E → H`. Choose a presentation `E = Λ_𝔪[Y_1, …, Y_s]/(G_l)` and put
`y = φ(Y) ∈ H^s`; then `f_j = Q_j(y, -)` for polynomials `Q_j` over `Λ_𝔪`. Clearing denominators,
the `G_l` and the `Q_j` become polynomials over `Λ`, and we add the congruences
`Y_k - a_k = Σ_l γ_l Z_{kl}`, where the `γ_l` generate `𝔪` and `a_k ∈ Λ` lifts the residue class
of `y_k` (possible because `κ(H) = Λ/𝔪`). This system over `Λ` is solved in `Ĥ` by `(y, x, z)`,
for suitable `z` in `H`, hence in `R` through the isomorphism `R ≅ Ĥ` of Stacks 06LJ. A solution
`(y', x', z')` in `H` gives a second map `φ' : E → H`, `Y ↦ y'`, which agrees with `φ` modulo
`𝔪_H` by the congruences. An étale algebra maps to a henselian local ring by at most one map with
a given reduction (Stacks 08HQ), so `φ' = φ`, that is `y' = y`, and `x'` solves the original
system.

*Descent of the G-ring property.* For `A → A^h` a henselization with `A^h` a G-ring: `A → A^h` is
regular, being a filtered colimit of étale, hence smooth, algebras with Noetherian fibres
(Stacks 07EP); `A^h → (A^h)^∧` is regular because `A^h` is a G-ring; so `A → (A^h)^∧` is regular
(Stacks 07QI). By Stacks 06LJ, `(A^h)^∧ ≅ A^∧` compatibly with the maps from `A`, hence
`A → A^∧` is regular, and a Noetherian local ring with regular completion map is a G-ring
(Stacks 07PT). This is the converse of Stacks 07QR for the henselization.

## References

* [Stacks Project, Tag 07XI](https://stacks.math.columbia.edu/tag/07XI)
* [Stacks Project, Tag 07BX](https://stacks.math.columbia.edu/tag/07BX)
* [Stacks Project, Tag 06LJ](https://stacks.math.columbia.edu/tag/06LJ)
* [Stacks Project, Tag 07C3](https://stacks.math.columbia.edu/tag/07C3)
* [Stacks Project, Tag 08HQ](https://stacks.math.columbia.edu/tag/08HQ)
* [Stacks Project, Tag 07EP](https://stacks.math.columbia.edu/tag/07EP)
* [Stacks Project, Tag 07QI](https://stacks.math.columbia.edu/tag/07QI)
* [Stacks Project, Tag 07PT](https://stacks.math.columbia.edu/tag/07PT)
* [Stacks Project, Tag 07QR](https://stacks.math.columbia.edu/tag/07QR)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing MvPolynomial

namespace Stacks.ApproximationProperty

/-! ### Bookkeeping for polynomial systems -/

/-- If every system over `Λ` with variables indexed by some `Fin n` and equations indexed by some
`Fin k` which is solvable in `R` is solvable in `H`, then the same holds for systems whose
variables and equations are indexed by arbitrary finite types. -/
private theorem exists_solution_of_finite {Λ R H : Type*} [CommRing Λ] [CommRing R]
    [CommRing H] [Algebra Λ R] [Algebra Λ H]
    (h : ∀ (n k : ℕ) (f : Fin k → MvPolynomial (Fin n) Λ) (a : Fin n → R),
      (∀ j, aeval a (f j) = 0) → ∃ b : Fin n → H, ∀ j, aeval b (f j) = 0)
    {σ κ : Type*} [Finite σ] [Finite κ] (f : κ → MvPolynomial σ Λ) (a : σ → R)
    (ha : ∀ j, aeval a (f j) = 0) :
    ∃ b : σ → H, ∀ j, aeval b (f j) = 0 := by
  obtain ⟨n, ⟨eσ⟩⟩ := Finite.exists_equiv_fin σ
  obtain ⟨k, ⟨eκ⟩⟩ := Finite.exists_equiv_fin κ
  obtain ⟨b, hb⟩ := h n k (fun j => rename eσ (f (eκ.symm j))) (a ∘ eσ.symm) fun j => by
    rw [aeval_rename]
    simpa [Function.comp_def] using ha (eκ.symm j)
  refine ⟨b ∘ eσ, fun j => ?_⟩
  have := hb (eκ j)
  rw [aeval_rename] at this
  simpa using this

/-- Clearing denominators: a polynomial over a localization `L = M⁻¹Λ` becomes a polynomial over
`Λ` after multiplication by an element of `M`, which is reflected in all evaluations. -/
private theorem exists_aeval_eq_mul {Λ L σ : Type*} [CommRing Λ] [CommRing L] [Algebra Λ L]
    (M : Submonoid Λ) [IsLocalization M L] (P : MvPolynomial σ L) :
    ∃ d ∈ M, ∃ P' : MvPolynomial σ Λ, ∀ {B : Type u} [CommRing B] [Algebra Λ B] [Algebra L B]
      [IsScalarTower Λ L B] (w : σ → B), aeval w P' = algebraMap Λ B d * aeval w P := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset M P.coeffs
  suffices ∃ P' : MvPolynomial σ Λ,
      MvPolynomial.map (algebraMap Λ L) P' = C (algebraMap Λ L b) * P by
    obtain ⟨P', hP⟩ := this
    refine ⟨b, b.2, P', fun w => ?_⟩
    rw [← aeval_map_algebraMap L, hP, map_mul, aeval_C, ← IsScalarTower.algebraMap_apply]
  rw [← Set.mem_range, mem_range_map_iff_coeffs_subset]
  intro c hc
  obtain ⟨v, -, rfl⟩ := mem_coeffs_iff.mp hc
  rw [coeff_C_mul]
  by_cases h0 : P.coeff v = 0
  · rw [h0, mul_zero]
    exact ⟨0, map_zero _⟩
  · obtain ⟨r, hr⟩ := hb (P.coeff v) (coeff_mem_coeffs v h0)
    exact ⟨r, by rw [hr, Algebra.smul_def]⟩

/-- Evaluating a polynomial in two families of variables at `(y, z)` is evaluating at `z` its
partial evaluation at `y`. -/
private theorem aeval_sumElim_eq {L H B : Type*} [CommRing L] [CommRing H] [CommRing B]
    [Algebra L H] [Algebra H B] [Algebra L B] [IsScalarTower L H B] {s n : Type*}
    (y : s → H) (z : n → B) (Q : MvPolynomial (s ⊕ n) L) :
    aeval (Sum.elim (algebraMap H B ∘ y) z) Q =
      aeval z (aeval (Sum.elim (C ∘ y) X) Q : MvPolynomial n H) := by
  have : (aeval (Sum.elim (algebraMap H B ∘ y) z) : MvPolynomial (s ⊕ n) L →ₐ[L] B) =
      ((aeval z).restrictScalars L).comp (aeval (Sum.elim (C ∘ y) X)) := by
    apply algHom_ext
    rintro (i | i) <;> simp
  exact DFunLike.congr_fun this Q

/-- A polynomial over `H` all of whose coefficients are polynomial expressions over `L` in
`y_1, …, y_s` is a polynomial over `L` in the `y_k` and the variables. -/
private theorem mem_range_aeval_sumElim {L H : Type*} [CommRing L] [CommRing H] [Algebra L H]
    {s n : Type*} (y : s → H) (f : MvPolynomial n H)
    (hf : ∀ v, f.coeff v ∈ Set.range (aeval (R := L) y)) :
    f ∈ (aeval (R := L) (Sum.elim (C ∘ y) X : s ⊕ n → MvPolynomial n H)).range := by
  classical
  set Θ := aeval (R := L) (Sum.elim (C ∘ y) X : s ⊕ n → MvPolynomial n H)
  have hC : ∀ c ∈ Set.range (aeval (R := L) y), C c ∈ Θ.range := by
    rintro _ ⟨p, rfl⟩
    refine ⟨rename Sum.inl p, ?_⟩
    change aeval _ (rename Sum.inl p) = _
    rw [aeval_rename]
    have : (Sum.elim (C ∘ y) X ∘ Sum.inl : s → MvPolynomial n H) =
        (IsScalarTower.toAlgHom L H (MvPolynomial n H)) ∘ y := by
      funext k
      simp [MvPolynomial.algebraMap_eq]
    rw [this]
    exact (comp_aeval_apply y (IsScalarTower.toAlgHom L H (MvPolynomial n H)) p).symm
  have hX : ∀ i, X i ∈ Θ.range := fun i => ⟨X (Sum.inr i), by simp [Θ]⟩
  rw [f.as_sum]
  refine Subalgebra.sum_mem _ fun v _ => ?_
  rw [monomial_eq]
  exact Subalgebra.mul_mem _ (hC _ (hf v))
    (Subalgebra.prod_mem _ fun i _ => Subalgebra.pow_mem _ (hX i) _)

/-! ### The approximation property of the henselization -/

section Approximation

variable (Λ : Type u) [CommRing Λ] [IsNoetherianRing Λ] (𝔪 : Ideal Λ) [𝔪.IsMaximal]
  (H : Type u) [CommRing H] [IsLocalRing H] [Algebra Λ H] [Algebra (Localization.AtPrime 𝔪) H]
  [IsScalarTower Λ (Localization.AtPrime 𝔪) H]
  [IsHenselization (Localization.AtPrime 𝔪) (ResidueField (Localization.AtPrime 𝔪)) H]

/-- The approximation property of `H`, given an isomorphism of the completions of `Λ_𝔪` and of
`H` over `Λ_𝔪`. -/
private theorem hasApproximationProperty_of_ringEquiv
    (h : ∀ (n k : ℕ) (f : Fin k → MvPolynomial (Fin n) Λ)
      (a : Fin n → AdicCompletion (maximalIdeal (Localization.AtPrime 𝔪))
        (Localization.AtPrime 𝔪)),
      (∀ j, aeval a (f j) = 0) → ∃ b : Fin n → H, ∀ j, aeval b (f j) = 0)
    (e : AdicCompletion (maximalIdeal (Localization.AtPrime 𝔪)) (Localization.AtPrime 𝔪) ≃+*
      AdicCompletion (maximalIdeal H) H)
    (he : ∀ r : Localization.AtPrime 𝔪,
      e (algebraMap _ (AdicCompletion (maximalIdeal (Localization.AtPrime 𝔪))
        (Localization.AtPrime 𝔪)) r) =
        algebraMap H (AdicCompletion (maximalIdeal H) H)
          (algebraMap (Localization.AtPrime 𝔪) H r)) :
    HasApproximationProperty H := by
  classical
  intro n m f x hx
  let L := Localization.AtPrime 𝔪
  let R := AdicCompletion (maximalIdeal L) L
  let Hc := AdicCompletion (maximalIdeal H) H
  have : HenselianLocalRing H := IsHenselization.henselian L (ResidueField L) (Rh := H)
  have : IsLocalHom (algebraMap L H) := IsHenselization.isLocalHom (L := ResidueField L)
  -- An étale stage `φ : E → H` containing every coefficient of the system.
  let T : Finset H := Finset.univ.biUnion fun j => (f j).coeffs
  obtain ⟨E, _, _, hE, g, φ, hgφ⟩ := Rig.ind_etale_factorization
    (IsHenselization.ind_etale_of_universe_le.{u, u, u} (R := L) (ResidueField L) (Rh := H))
    (MvPolynomial T L) (aeval fun t : T => (t : H))
  have hTφ : ∀ c ∈ T, c ∈ Set.range φ := fun c hc =>
    ⟨g (X ⟨c, hc⟩), by rw [← AlgHom.comp_apply, hgφ, aeval_X]⟩
  -- A presentation `π : L[Y_1, …, Y_s] → E` whose kernel is generated by `S`.
  obtain ⟨s, π, hπ, S, hS⟩ := Algebra.FinitePresentation.out (R := L) (A := E)
  let ψ : MvPolynomial (Fin s) L →ₐ[L] H := φ.comp π
  let y : Fin s → H := fun k => ψ (X k)
  have hψ : ψ = aeval y := aeval_unique ψ
  have hGy : ∀ l : S, aeval y (l : MvPolynomial (Fin s) L) = 0 := by
    intro l
    have hl : (l : MvPolynomial (Fin s) L) ∈ RingHom.ker π.toRingHom :=
      hS ▸ Ideal.subset_span l.2
    rw [← hψ]
    change φ (π l) = 0
    rw [show π l = 0 from hl, map_zero]
  -- The equations are polynomials over `L` in the `y_k` and the unknowns.
  have hcoeff : ∀ j v, (f j).coeff v ∈ Set.range (aeval (R := L) y) := by
    intro j v
    by_cases h0 : (f j).coeff v = 0
    · exact ⟨0, by rw [h0, map_zero]⟩
    · obtain ⟨e₀, he₀⟩ := hTφ _ (Finset.mem_biUnion.mpr
        ⟨j, Finset.mem_univ _, coeff_mem_coeffs v h0⟩)
      obtain ⟨p, rfl⟩ := hπ e₀
      exact ⟨p, by rw [← hψ, ← he₀]; rfl⟩
  choose Q hQ using fun j =>
    (AlgHom.mem_range _).mp (mem_range_aeval_sumElim y (f j) (hcoeff j))
  -- Generators `γ_l` of `𝔪`; they also generate the maximal ideal of `H`.
  obtain ⟨Γ, hΓ⟩ : 𝔪.FG := IsNoetherian.noetherian 𝔪
  have hmH : maximalIdeal H = Ideal.span (Set.range fun l : Γ => algebraMap Λ H l) := by
    rw [← IsHenselization.map_maximalIdeal (R := L) (L := ResidueField L) (Rh := H),
      ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq, ← hΓ, Ideal.map_span]
    congr 1
    ext c
    simp
  -- Lifts `a_k ∈ Λ` of the residues of the `y_k`, and `y_k - a_k = Σ_l z_{kl} γ_l`.
  have hres : ∀ k, ∃ a : Λ, y k - algebraMap Λ H a ∈ maximalIdeal H := by
    intro k
    obtain ⟨z, hz⟩ := (IsHenselization.residueField_map_bijective (R := L) (Rh := H)).2
      (residue H (y k))
    obtain ⟨a, ha⟩ := 𝔪.algebraMap_residueField_surjective z
    refine ⟨a, ?_⟩
    rw [← residue_eq_zero_iff, map_sub, sub_eq_zero, ← hz, ← ha,
      IsScalarTower.algebraMap_apply Λ L (ResidueField L), ResidueField.algebraMap_eq,
      ResidueField.map_residue, ← IsScalarTower.algebraMap_apply]
  choose a ha using hres
  have hz : ∀ k, ∃ z : Γ → H, ∑ l, z l * algebraMap Λ H l = y k - algebraMap Λ H (a k) := by
    intro k
    have hk := ha k
    rw [hmH] at hk
    obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun H).mp hk
    exact ⟨z, by simpa only [smul_eq_mul] using hz⟩
  choose z hz using hz
  -- Clear the denominators of the relations `G_l` and of the equations `Q_j`.
  choose dG hdG G' hG' using fun l : S =>
    exists_aeval_eq_mul 𝔪.primeCompl (l : MvPolynomial (Fin s) L)
  choose dQ hdQ Q' hQ' using fun j => exists_aeval_eq_mul 𝔪.primeCompl (Q j)
  have hunit : ∀ {d : Λ}, d ∈ 𝔪.primeCompl → ∀ c : H, algebraMap Λ H d * c = 0 → c = 0 := by
    intro d hd c
    rw [IsScalarTower.algebraMap_apply Λ L H]
    exact (IsLocalization.map_units L (⟨d, hd⟩ : 𝔪.primeCompl)).map _ |>.mul_right_eq_zero.mp
  -- The system over `Λ`: the relations of `E`, the equations, and the congruences
  -- `Y_k - a_k = Σ_l γ_l Z_{kl}`.
  let F : S ⊕ (Fin m ⊕ Fin s) → MvPolynomial (Fin s ⊕ (Fin n ⊕ (Fin s × Γ))) Λ :=
    Sum.elim (fun l => rename Sum.inl (G' l))
      (Sum.elim (fun j => rename (Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)) (Q' j))
        fun k => X (Sum.inl k) - C (a k) - ∑ l : Γ, C (l : Λ) * X (Sum.inr (Sum.inr (k, l))))
  -- Its solution `(y, x, z)` in the completion of `H`.
  let w : Fin s ⊕ (Fin n ⊕ (Fin s × Γ)) → Hc :=
    Sum.elim (fun k => algebraMap H Hc (y k))
      (Sum.elim x fun p => algebraMap H Hc (z p.1 p.2))
  have hw : ∀ i, aeval w (F i) = 0 := by
    rintro (l | j | k)
    · change aeval w (rename Sum.inl (G' l)) = 0
      rw [aeval_rename, hG' l]
      have : (w ∘ Sum.inl : Fin s → Hc) = fun k => IsScalarTower.toAlgHom L H Hc (y k) := rfl
      rw [this, ← comp_aeval_apply, hGy l, map_zero, mul_zero]
    · change aeval w (rename (Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)) (Q' j)) = 0
      rw [aeval_rename, hQ' j]
      have : (w ∘ Sum.elim Sum.inl (Sum.inr ∘ Sum.inl) : Fin s ⊕ Fin n → Hc) =
          Sum.elim (algebraMap H Hc ∘ y) x := by
        funext i
        rcases i with k | i <;> rfl
      rw [this, aeval_sumElim_eq, hQ j, hx j, mul_zero]
    · change aeval w (X (Sum.inl k) - C (a k) -
        ∑ l : Γ, C (l : Λ) * X (Sum.inr (Sum.inr (k, l)))) = 0
      calc _ = algebraMap H Hc
            (y k - algebraMap Λ H (a k) - ∑ l : Γ, algebraMap Λ H l * z k l) := by
            simp only [map_sub, map_sum, map_mul, aeval_X, aeval_C,
              IsScalarTower.algebraMap_apply Λ H Hc]
            rfl
        _ = 0 := by
          rw [← hz k, sub_eq_zero.mpr, map_zero]
          exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  -- Transport it to `R ≅ Ĥ` and solve the system in `H`.
  let eΛ : Hc →ₐ[Λ] R :=
    { e.symm.toRingHom with
      commutes' := fun c => by
        change e.symm (algebraMap Λ Hc c) = algebraMap Λ R c
        rw [RingEquiv.symm_apply_eq, IsScalarTower.algebraMap_apply Λ L R, he,
          ← IsScalarTower.algebraMap_apply Λ L H, ← IsScalarTower.algebraMap_apply Λ H Hc] }
  obtain ⟨b, hb⟩ := exists_solution_of_finite h F (fun i => eΛ (w i)) fun i => by
    rw [← comp_aeval_apply, hw i, map_zero]
  -- The new values `y'` of the `Y_k` define a second map `φ' : E → H`.
  let y' : Fin s → H := fun k => b (Sum.inl k)
  let x' : Fin n → H := fun i => b (Sum.inr (Sum.inl i))
  have hGy' : ∀ l : S, aeval y' (l : MvPolynomial (Fin s) L) = 0 := by
    intro l
    have h1 := hb (Sum.inl l)
    simp only [F, Sum.elim_inl, aeval_rename, hG' l] at h1
    exact hunit (hdG l) _ h1
  let φ' : E →ₐ[L] H := AlgHom.liftOfSurjective π hπ (aeval y') (by
    rw [← hS, Ideal.span_le]
    intro p hp
    exact hGy' ⟨p, hp⟩)
  have hφ' : ∀ p, φ' (π p) = aeval y' p := fun p => AlgHom.liftOfSurjective_apply π hπ _ _ p
  -- The congruences make `φ'` and `φ` agree modulo `𝔪_H`; by étale rigidity they are equal.
  have hcong : ∀ k, y' k - y k ∈ maximalIdeal H := by
    intro k
    have h1 : aeval b (X (Sum.inl k) - C (a k) -
        ∑ l : Γ, C (l : Λ) * X (Sum.inr (Sum.inr (k, l)))) = 0 := hb (Sum.inr (Sum.inr k))
    simp only [map_sub, map_sum, map_mul, aeval_X, aeval_C] at h1
    have h2 : y' k - algebraMap Λ H (a k) ∈ maximalIdeal H := by
      rw [sub_eq_zero.mp h1]
      refine Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ ?_
      rw [hmH]
      exact Ideal.subset_span ⟨l, rfl⟩
    simpa using Ideal.sub_mem _ h2 (ha k)
  have hφφ' : φ' = φ := by
    obtain ⟨φ₀, -, huniq⟩ := HenselianLocalRing.existsUnique_algHom_residue_of_etale
      (R := L) (A := E) (S := H) ((IsScalarTower.toAlgHom L H (ResidueField H)).comp φ)
    have h1 : φ = φ₀ := huniq φ fun _ => rfl
    have h2 : φ' = φ₀ := huniq φ' fun e₀ => by
      obtain ⟨p, rfl⟩ := hπ e₀
      have : (IsScalarTower.toAlgHom L H (ResidueField H)).comp (aeval y') =
          (IsScalarTower.toAlgHom L H (ResidueField H)).comp (aeval y) := by
        apply algHom_ext
        intro k
        simp only [AlgHom.comp_apply, aeval_X, IsScalarTower.toAlgHom_apply,
          ResidueField.algebraMap_eq]
        rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
        exact hcong k
      change residue H (φ' (π p)) = residue H (ψ p)
      rw [hφ' p, hψ]
      exact DFunLike.congr_fun this p
    rw [h1, h2]
  have hyy' : y' = y := by
    funext k
    have := hφ' (X k)
    rw [hφφ', aeval_X] at this
    exact this.symm
  -- Hence `x'` solves the original system.
  refine ⟨x', fun j => ?_⟩
  have h1 := hb (Sum.inr (Sum.inl j))
  simp only [F, Sum.elim_inl, Sum.elim_inr, aeval_rename, hQ' j] at h1
  replace h1 := hunit (hdQ j) _ h1
  have h2 : (b ∘ Sum.elim Sum.inl (Sum.inr ∘ Sum.inl) : Fin s ⊕ Fin n → H) =
      Sum.elim (algebraMap H H ∘ y) x' := by
    funext i
    rcases i with k | i
    · exact congrFun hyy' k
    · rfl
  rwa [h2, aeval_sumElim_eq, hQ j] at h1

/-- **Approximation in the henselization** (the step "in other words, the approximation property
holds for `Λ_𝔪^h`" of Stacks 07XI). Let `Λ` be a Noetherian ring, let `𝔪` be a maximal ideal of
`Λ`, and let `H` be a henselization of `Λ_𝔪`. If every finite system of polynomial equations
over `Λ` which has a solution in the completion `Λ_𝔪^∧` has a solution in `H`, then `H` has the
approximation property: every finite system of polynomial equations over `H` which has a
solution in the completion of `H` has a solution in `H`. -/
theorem hasApproximationProperty_of_forall_exists_solution
    (h : ∀ (n k : ℕ) (f : Fin k → MvPolynomial (Fin n) Λ)
      (a : Fin n → AdicCompletion (maximalIdeal (Localization.AtPrime 𝔪))
        (Localization.AtPrime 𝔪)),
      (∀ j, MvPolynomial.aeval a (f j) = 0) →
        ∃ b : Fin n → H, ∀ j, MvPolynomial.aeval b (f j) = 0) :
    IsLocalRing.HasApproximationProperty H := by
  obtain ⟨e, he⟩ := StacksDraft.exists_adicCompletion_ringEquiv_of_isHenselization
    (R := Localization.AtPrime 𝔪) (H := H)
  exact hasApproximationProperty_of_ringEquiv Λ 𝔪 H h e he

end Approximation

/-! ### G-rings and henselization -/

section GRing

/-- A filtered colimit of étale algebras which is a Noetherian ring is regular over the base
(Stacks 07EP, étale algebras being smooth). -/
private theorem isRegularRingHom_of_ind_etale {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [IsNoetherianRing B]
    (hi : (CommAlgCat.etale.{u} A).ind.{u} (CommAlgCat.of A B)) :
    IsRegularRingHom (algebraMap A B) := by
  obtain ⟨J, _, _, pres, hpres⟩ := hi
  obtain ⟨ι, _, _, _, F, _⟩ := IsFiltered.exists_directed J
  let pres' := pres.reindex F
  exact isRegularRingHom_of_filteredColimit_smooth pres'.diag pres'.cocone pres'.isColimit
    (fun i => by
      have : Algebra.Etale A (pres.diag.obj (F.obj i)) := hpres (F.obj i)
      change Algebra.Smooth A (pres.diag.obj (F.obj i))
      infer_instance)
    (fun p _ => p.isNoetherianRing_fiber B)

/-- **A local ring whose henselization is a G-ring is a G-ring** (the last step of Stacks 07XI;
compare Stacks 07QR for the converse). Let `A` be a Noetherian local ring and let `A^h` be its
henselization. If `A^h` is a G-ring, then so is `A`. -/
@[ega "IV 18.7.2" "special case"]
theorem isGRing_of_isGRing_isHenselization {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] {Ah : Type u} [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah]
    [IsLocalRing.IsHenselization A (ResidueField A) Ah] (h : IsGRing Ah) : IsGRing A := by
  have : IsNoetherianRing Ah := h.1
  let Ahc := AdicCompletion (maximalIdeal Ah) Ah
  have hAAh : IsRegularRingHom (algebraMap A Ah) := isRegularRingHom_of_ind_etale
    (IsHenselization.ind_etale_of_universe_le.{u, u, u} (R := A) (ResidueField A) (Rh := Ah))
  have hcomp := isRegularRingHom_comp (algebraMap A Ah) (algebraMap Ah Ahc) hAAh
    ((_root_.isGRing_iff_isRegularRingHom_completion Ah).mp h) fun p _ => by
      let : Algebra A Ahc := ((algebraMap Ah Ahc).comp (algebraMap A Ah)).toAlgebra
      exact p.isNoetherianRing_fiber Ahc
  obtain ⟨e, he⟩ := StacksDraft.exists_adicCompletion_ringEquiv_of_isHenselization
    (R := A) (H := Ah)
  have heq : e.symm.toRingHom.comp ((algebraMap Ah Ahc).comp (algebraMap A Ah)) =
      algebraMap A (AdicCompletion (maximalIdeal A) A) :=
    RingHom.ext fun r => e.symm_apply_eq.mpr (he r).symm
  exact (_root_.isGRing_iff_isRegularRingHom_completion A).mpr (heq ▸ hcomp.comp_ringEquiv e.symm)

/-- **The local ring `Λ_𝔪` is a G-ring if its henselization is** (the last step of Stacks 07XI,
in the setting of that example). Let `Λ` be a Noetherian ring, let `𝔪` be a maximal ideal of `Λ`,
and let `H` be a henselization of `Λ_𝔪`. If `H` is a G-ring, then so is `Λ_𝔪`. -/
@[ega "IV 18.7.2" "special case"]
theorem isGRing_atPrime_of_isGRing_isHenselization (Λ : Type u) [CommRing Λ]
    [IsNoetherianRing Λ] (𝔪 : Ideal Λ) [𝔪.IsMaximal] (H : Type u) [CommRing H] [IsLocalRing H]
    [Algebra (Localization.AtPrime 𝔪) H]
    [IsHenselization (Localization.AtPrime 𝔪) (ResidueField (Localization.AtPrime 𝔪)) H]
    (h : IsGRing H) : IsGRing (Localization.AtPrime 𝔪) :=
  isGRing_of_isGRing_isHenselization h

end GRing

end Stacks.ApproximationProperty

end
