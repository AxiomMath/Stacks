module

public import StacksFrontier.RingTheory.TateMap.ClaimMoves

/-!
# Naturality of the elementary moves under a change of coefficients

The elementary moves of localized square presentations (`Stacks.TateMap.lciGraphEquiv`,
`Stacks.TateMap.lciGlobalEquiv`, `Stacks.TateMap.lciMatrixEquiv`) are defined over any ring of
coefficients. For a ring map `ε : S → A` they commute with specializing the coefficients: if two
ring maps out of `S[x, 1/h]/(f)` and `A[x, 1/h']/(f')` agree on classes of polynomials up to
`ε`, so do their composites with the inverse moves.

## Main results

* `Stacks.TateMap.map_graphRelations`: specializing the graph relations.
* `Stacks.TateMap.lciGraphEquiv_symm_natural`, `Stacks.TateMap.lciGlobalEquiv_symm_natural`:
  naturality of the inverse moves.
-/

@[expose] public section

open MvPolynomial Stacks.Discriminant

universe u

namespace Stacks.TateMap

variable {S A : Type u} [CommRing S] [CommRing A] (ε : S →+* A)

section Graph

variable {n m N : ℕ} (e : Fin n ⊕ Fin m ≃ Fin N) (σ : Fin n ⊕ Fin m ≃ Fin N)
  (h : MvPolynomial (Fin n) S) (f : Fin n → MvPolynomial (Fin n) S)
  (ψ : Fin m → MvPolynomial (Fin n) S) (a : ℕ)

theorem map_graphIncl (p : MvPolynomial (Fin n) S) :
    MvPolynomial.map ε (graphIncl e p) = graphIncl e (MvPolynomial.map ε p) :=
  MvPolynomial.map_rename _ _ _

/-- Specializing the coefficients of the graph relations. -/
theorem map_graphRelations (k : Fin N) :
    MvPolynomial.map ε (graphRelations e σ h f ψ a k) =
      graphRelations e σ (MvPolynomial.map ε h) (fun i ↦ MvPolynomial.map ε (f i))
        (fun j ↦ MvPolynomial.map ε (ψ j)) a k := by
  obtain ⟨c, rfl⟩ := σ.surjective k
  rcases c with i | j
  · rw [graphRelations_inl, graphRelations_inl, map_graphIncl]
  · rw [graphRelations_inr, graphRelations_inr, map_sub, map_mul, map_pow, map_graphIncl,
      map_graphIncl, MvPolynomial.map_X]

variable {T : Type*} [CommRing T] {h' : MvPolynomial (Fin n) A}
  {f' : Fin n → MvPolynomial (Fin n) A}

/-- The inverse of a unit is carried to the inverse of its image. -/
theorem map_unit_inv_eq {R R' : Type*} [CommRing R] [CommRing R'] (χ : R →+* T)
    (χ' : R' →+* T) {x : R} {x' : R'} (hx : IsUnit x) (hx' : IsUnit x') (H : χ x = χ' x') :
    χ ((hx.unit⁻¹ : Rˣ) : R) = χ' ((hx'.unit⁻¹ : R'ˣ) : R') := by
  calc χ ((hx.unit⁻¹ : Rˣ) : R)
      = χ ((hx.unit⁻¹ : Rˣ) : R) * (χ' x' * χ' ((hx'.unit⁻¹ : R'ˣ) : R')) := by
        rw [← map_mul, IsUnit.mul_val_inv, map_one, mul_one]
    _ = χ (((hx.unit⁻¹ : Rˣ) : R) * x) * χ' ((hx'.unit⁻¹ : R'ˣ) : R') := by
        rw [map_mul, H, mul_assoc]
    _ = χ' ((hx'.unit⁻¹ : R'ˣ) : R') := by rw [IsUnit.val_inv_mul, map_one, one_mul]

/-- To compare `χ ∘ G ∘ μ` and `χ' ∘ G' ∘ μ' ∘ map ε` on all polynomials, it suffices to compare
them on constants and variables. -/
private theorem comp_natural_of_X {N : ℕ} {B B' M M' T : Type*} [CommRing B] [CommRing B']
    [CommRing M] [CommRing M'] [CommRing T] [Algebra S B] [Algebra A B'] [Algebra S M]
    [Algebra A M'] (χ : B →+* T) (χ' : B' →+* T) (G : M ≃ₐ[S] B) (G' : M' ≃ₐ[A] B')
    (μ : MvPolynomial (Fin N) S →ₐ[S] M) (μ' : MvPolynomial (Fin N) A →ₐ[A] M')
    (hC : ∀ c, χ (algebraMap S B c) = χ' (algebraMap A B' (ε c)))
    (hX : ∀ k, χ (G (μ (X k))) = χ' (G' (μ' (X k)))) (q : MvPolynomial (Fin N) S) :
    χ (G (μ q)) = χ' (G' (μ' (MvPolynomial.map ε q))) := by
  have : (χ.comp (G : M →+* B)).comp (μ : MvPolynomial (Fin N) S →+* M) =
      ((χ'.comp (G' : M' →+* B')).comp (μ' : MvPolynomial (Fin N) A →+* M')).comp
        (MvPolynomial.map ε) := by
    refine MvPolynomial.ringHom_ext (fun c ↦ ?_) fun k ↦ ?_
    · simpa [← MvPolynomial.algebraMap_eq] using hC c
    · simpa using hX k
  exact DFunLike.congr_fun this q

/-- **Naturality of adding graph variables.** If `χ` and `χ'` agree on classes of polynomials up
to `ε`, so do their composites with the inverses of the graph moves over `S` and over `A`. -/
theorem lciGraphEquiv_symm_natural (χ : localizedCompleteIntersection S n h f →+* T)
    (χ' : localizedCompleteIntersection A n (MvPolynomial.map ε h)
      (fun i ↦ MvPolynomial.map ε (f i)) →+* T)
    (H : ∀ p, χ (lciMk h f p) = χ' (lciMk _ _ (MvPolynomial.map ε p)))
    (q : MvPolynomial (Fin N) S) :
    χ ((lciGraphEquiv e σ h f ψ a).symm (lciMk _ _ q)) =
      χ' ((lciGraphEquiv e σ (MvPolynomial.map ε h) (fun i ↦ MvPolynomial.map ε (f i))
        (fun j ↦ MvPolynomial.map ε (ψ j)) a).symm (lciMk _ _ (MvPolynomial.map ε q))) := by
  set G := lciGraphEquiv e σ h f ψ a
  set G' := lciGraphEquiv e σ (MvPolynomial.map ε h) (fun i ↦ MvPolynomial.map ε (f i))
    (fun j ↦ MvPolynomial.map ε (ψ j)) a
  refine comp_natural_of_X ε χ χ' G.symm G'.symm (lciMk _ _) (lciMk _ _)
    (fun c ↦ by simpa [← MvPolynomial.algebraMap_eq] using H (C c)) (fun k ↦ ?_) q
  · rw [lciGraphEquiv_symm_lciMk, lciGraphEquiv_symm_lciMk, aeval_X, aeval_X]
    simp only [graphInvImage]
    rcases e.symm k with i | j
    · simpa using H (X i)
    · simp only [Sum.elim_inr, map_mul, map_pow]
      rw [H (ψ j), map_unit_inv_eq χ χ' (isUnit_lciMk h f) (isUnit_lciMk _ _) (H h)]

/-- Naturality of adding graph variables, for specialized data given up to equality. -/
theorem lciGraphEquiv_symm_natural' {h' : MvPolynomial (Fin n) A}
    {f' : Fin n → MvPolynomial (Fin n) A} {ψ' : Fin m → MvPolynomial (Fin n) A}
    (hh : MvPolynomial.map ε h = h') (hf : ∀ i, MvPolynomial.map ε (f i) = f' i)
    (hψ : ∀ j, MvPolynomial.map ε (ψ j) = ψ' j)
    (χ : localizedCompleteIntersection S n h f →+* T)
    (χ' : localizedCompleteIntersection A n h' f' →+* T)
    (H : ∀ p, χ (lciMk h f p) = χ' (lciMk _ _ (MvPolynomial.map ε p)))
    (q : MvPolynomial (Fin N) S) :
    χ ((lciGraphEquiv e σ h f ψ a).symm (lciMk _ _ q)) =
      χ' ((lciGraphEquiv e σ h' f' ψ' a).symm (lciMk _ _ (MvPolynomial.map ε q))) := by
  subst hh
  obtain rfl : (fun i ↦ MvPolynomial.map ε (f i)) = f' := funext hf
  obtain rfl : (fun j ↦ MvPolynomial.map ε (ψ j)) = ψ' := funext hψ
  exact lciGraphEquiv_symm_natural ε e σ h f ψ a χ χ' H q

end Graph

section Global

variable {n : ℕ} (H : MvPolynomial (Fin n) S) (f : Fin n → MvPolynomial (Fin n) S)
  {T : Type*} [CommRing T]

/-- Specializing the coefficients of the global relations. -/
theorem map_globalRelations (k : Fin (n + 1)) :
    MvPolynomial.map ε (globalRelations H f k) =
      globalRelations (MvPolynomial.map ε H) (fun i ↦ MvPolynomial.map ε (f i)) k := by
  rw [globalRelations, map_graphRelations]
  simp only [map_one]

theorem lciGlobalEquiv_symm_lciMk (q : MvPolynomial (Fin (n + 1)) S) :
    (lciGlobalEquiv H f).symm (lciMk _ _ q) =
      aeval (graphInvImage finSumFinEquiv H f (fun _ ↦ 1) 1) q := by
  rw [lciGlobalEquiv, AlgEquiv.symm_trans_apply]
  have : (lciEquivOfUnit (isUnit_lciMk_one_graphIncl H f) (lciMk_relation _ _)
      (by rw [map_one]; exact isUnit_one) (lciMk_relation _ _)).symm (lciMk _ _ q) =
      lciMk _ _ q := by
    rw [AlgEquiv.symm_apply_eq, lciEquivOfUnit_lciMk]
  rw [this, lciGraphEquiv_symm_lciMk]

/-- **Naturality of removing the localization.** -/
theorem lciGlobalEquiv_symm_natural (χ : localizedCompleteIntersection S n H f →+* T)
    (χ' : localizedCompleteIntersection A n (MvPolynomial.map ε H)
      (fun i ↦ MvPolynomial.map ε (f i)) →+* T)
    (hχ : ∀ p, χ (lciMk H f p) = χ' (lciMk _ _ (MvPolynomial.map ε p)))
    (q : MvPolynomial (Fin (n + 1)) S) :
    χ ((lciGlobalEquiv H f).symm (lciMk _ _ q)) =
      χ' ((lciGlobalEquiv (MvPolynomial.map ε H) (fun i ↦ MvPolynomial.map ε (f i))).symm
        (lciMk _ _ (MvPolynomial.map ε q))) := by
  refine comp_natural_of_X ε χ χ' (lciGlobalEquiv H f).symm
    (lciGlobalEquiv (MvPolynomial.map ε H) (fun i ↦ MvPolynomial.map ε (f i))).symm
    (lciMk _ _) (lciMk _ _) (fun c ↦ by simpa [← MvPolynomial.algebraMap_eq] using hχ (C c))
    (fun k ↦ ?_) q
  · rw [lciGlobalEquiv_symm_lciMk, lciGlobalEquiv_symm_lciMk, aeval_X,
      aeval_X]
    simp only [graphInvImage]
    rcases finSumFinEquiv.symm k with i | j
    · simpa using hχ (X i)
    · simp only [Sum.elim_inr, map_one, one_mul, pow_one]
      exact map_unit_inv_eq χ χ' (isUnit_lciMk H f) (isUnit_lciMk _ _) (hχ H)

/-- Naturality of removing the localization, for specialized data given up to equality. -/
theorem lciGlobalEquiv_symm_natural' {H' : MvPolynomial (Fin n) A}
    {f' : Fin n → MvPolynomial (Fin n) A} (hH : MvPolynomial.map ε H = H')
    (hf : ∀ i, MvPolynomial.map ε (f i) = f' i)
    (χ : localizedCompleteIntersection S n H f →+* T)
    (χ' : localizedCompleteIntersection A n H' f' →+* T)
    (hχ : ∀ p, χ (lciMk H f p) = χ' (lciMk _ _ (MvPolynomial.map ε p)))
    (q : MvPolynomial (Fin (n + 1)) S) :
    χ ((lciGlobalEquiv H f).symm (lciMk _ _ q)) =
      χ' ((lciGlobalEquiv H' f').symm (lciMk _ _ (MvPolynomial.map ε q))) := by
  subst hH
  obtain rfl : (fun i ↦ MvPolynomial.map ε (f i)) = f' := funext hf
  exact lciGlobalEquiv_symm_natural ε H f χ χ' hχ q

end Global

end Stacks.TateMap
