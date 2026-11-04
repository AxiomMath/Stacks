module

public import StacksFrontier.RingTheory.GeometricallyIrreducible.TFAE.Conditions
import StacksCore.Tactic.EgaSgaAttribute

/-! # Geometric irreducibility: natural irrationalities and rational function fields

This file proves the natural-irrationalities half of the atom (`E ⊗[K] M` is a domain when `K` is
separably algebraically closed in `M`), Lemma X on relative algebraic closedness over rational
function fields, and the comparison maps for `L(t)` used in the reduction of
`geomIrred_Lt_algClosedIn`. It is part of `StacksFrontier.RingTheory.GeometricallyIrreducible.TFAE`.
-/

@[expose] public section

open TensorProduct

universe u

-- needed: `geomIrred_atom_sepClosed_isDomain`'s `rw [AdjoinRoot.liftAlgHom_root]` after the
-- `change` only matches once defeq unfolds `AdjoinRoot`'s quotient wrapper.
set_option backward.isDefEq.respectTransparency false in
/-- **[ATOM-NI] Natural-irrationalities half of the atom.** If `K` is *separably algebraically
closed in* the field extension `M/K` (every `x : M` integral over `K` with separable minimal
polynomial lies in `K`, i.e. in the bottom subalgebra) and `E/K` is finite separable, then
`E ⊗[K] M` is a domain, indeed a field. *Proof.* By the primitive element theorem
`E = K[X]/(g)`, `g` separable irreducible; `E ⊗[K] M ≅ M[X]/(g)`; a monic factor `h | g` over `M`
has coefficients that are elementary symmetric functions of roots of `g` in `M̄`, hence separable
algebraic over `K` AND in `M`, so by hypothesis in `K`; thus `h ∈ K[X]` would split `g` over `K`,
contradicting irreducibility. So `g` stays irreducible over `M`, `M[X]/(g)` is a field. -/
@[ega "IV 4.3.2" "special case", ega "IV 6.7.4.1" "special case", sga "1 XIII 2.0.2" "special case"]
theorem geomIrred_atom_sepClosed_isDomain
    (K : Type u) [Field K] (E : Type u) [Field E] [Algebra K E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    (M : Type u) [Field M] [Algebra K M]
    (hSC : ∀ x : M, IsIntegral K x → (minpoly K x).Separable → x ∈ (⊥ : Subalgebra K M)) :
    IsDomain (E ⊗[K] M) := by
  -- a finite separable extension stays a domain after a base change in which K is separably
  -- algebraically closed).
  -- PROOF SKETCH (to fill): obtain `θ` primitive (`Field.exists_primitive_element`),
  -- `g := minpoly K θ` (monic via `minpoly.monic`, irreducible via `minpoly.irreducible`,
  -- separable via `Algebra.IsSeparable.isSeparable`). Identify `E ⊗[K] M ≅ M[X]/(g_M)`
  -- (`AdjoinRoot` + base change of the quotient). Show `g_M` irreducible over `M`: any monic
  -- proper factor `h` of `g_M` has coefficients separable-algebraic over `K` (roots of `g` in
  -- `AlgebraicClosure M`, `minpoly.dvd` + `Polynomial.Separable.of_dvd`; coefficients are signed
  -- elementary symmetric functions, `Multiset.prod_X_sub_C_coeff`) and in `M`, so by `hSC` in `K`;
  -- `Polynomial.map_injective` + monic division (`Polynomial.divModByMonic`) descends the
  -- factorization to `K[X]`, contradicting `minpoly.irreducible`. Then `(g_M)` maximal in the PID
  -- `M[X]` ⟹ `M[X]/(g_M)` a field ⟹ domain.
  -- local helper: a coefficient of `∏ (X - C t)` over a multiset lies in a subalgebra
  -- whenever all the `t` do (signed elementary symmetric functions).
  have coeff_prod_mem : ∀ (Ω : Type u) [Field Ω] [Algebra K Ω] (L : Subalgebra K Ω)
      (s : Multiset Ω), (∀ x ∈ s, x ∈ L) → ∀ k : ℕ,
      (Multiset.map (fun t => Polynomial.X - Polynomial.C t) s).prod.coeff k ∈ L := by
    intro Ω _ _ L s hs k
    induction s using Multiset.induction generalizing k with
    | empty =>
      simp only [Multiset.map_zero, Multiset.prod_zero]
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; simp
      · rw [Polynomial.coeff_one, ite_eq_right (by omega)]; exact L.zero_mem
    | cons a t ih =>
      have hat : a ∈ L := hs a (Multiset.mem_cons_self a t)
      have ht : ∀ x ∈ t, x ∈ L := fun x hx => hs x (Multiset.mem_cons_of_mem hx)
      rw [Multiset.map_cons, Multiset.prod_cons, sub_mul, Polynomial.coeff_sub]
      apply Subalgebra.sub_mem
      · cases k with
        | zero => rw [Polynomial.coeff_X_mul_zero]; exact L.zero_mem
        | succ j => rw [Polynomial.coeff_X_mul]; exact ih ht j
      · rw [Polynomial.coeff_C_mul]; exact L.mul_mem hat (ih ht k)
  -- local helper: a monic polynomial of positive degree all of whose monic proper
  -- divisors are units (degree `0`) is irreducible.
  have monic_irr : ∀ (p : Polynomial M), p.Monic → 1 ≤ p.natDegree →
      (∀ q : Polynomial M, q.Monic → q ∣ p → q.natDegree < p.natDegree → q.natDegree = 0) →
      Irreducible p := by
    intro p hp hd H
    have hp0 : p ≠ 0 := hp.ne_zero
    have hunit : ∀ (c : Polynomial M), c ≠ 0 → c.natDegree = 0 → IsUnit c := by
      intro c hc0 hcd
      rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree hc0, hcd]; rfl
    refine ⟨?_, ?_⟩
    · intro hu; have := Polynomial.natDegree_eq_zero_of_isUnit hu; omega
    · intro a b hab
      have ha0 : a ≠ 0 := by rintro rfl; rw [zero_mul] at hab; exact hp0 hab
      have hb0 : b ≠ 0 := by rintro rfl; rw [mul_zero] at hab; exact hp0 hab
      have hlc : a.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr ha0
      set a' := a * Polynomial.C (a.leadingCoeff)⁻¹ with ha'
      have ha'monic : a'.Monic := Polynomial.monic_mul_leadingCoeff_inv ha0
      have ha'dvd : a' ∣ p := ⟨b * Polynomial.C (a.leadingCoeff), by
        rw [hab, ha', mul_assoc, mul_comm (Polynomial.C (a.leadingCoeff)⁻¹), mul_assoc,
          ← Polynomial.C_mul, mul_inv_cancel₀ hlc, Polynomial.C_1, mul_one]⟩
      have hdeg : a'.natDegree = a.natDegree := by
        rw [ha', Polynomial.natDegree_mul ha0 (by simp [hlc])]; simp
      have hsum : a.natDegree + b.natDegree = p.natDegree := by
        rw [hab, Polynomial.natDegree_mul ha0 hb0]
      rcases lt_or_eq_of_le (show a.natDegree ≤ p.natDegree by omega) with hlt | heq
      · left
        have hh := H a' ha'monic ha'dvd (by omega)
        rw [hdeg] at hh; exact hunit a ha0 hh
      · right; exact hunit b hb0 (by omega)
  -- primitive element: `E = K(pb.gen)`, `g := minpoly K pb.gen`.
  set pb := Field.powerBasisOfFiniteOfSeparable K E with hpb
  set g := minpoly K pb.gen with hgdef
  have hθint : IsIntegral K pb.gen := Algebra.IsIntegral.isIntegral pb.gen
  have hgmonic : g.Monic := minpoly.monic hθint
  have hgirr : Irreducible g := minpoly.irreducible hθint
  have hgsep : g.Separable := Algebra.IsSeparable.isSeparable K pb.gen
  -- `g_M := g.map (algebraMap K M)` is irreducible over `M` (natural irrationalities).
  have hirr : Irreducible (g.map (algebraMap K M)) := by
    set gM := g.map (algebraMap K M) with hgM
    have hgMmonic : gM.Monic := hgmonic.map _
    have hgdeg : 1 ≤ g.natDegree := hgirr.natDegree_pos
    have hgMdeg : gM.natDegree = g.natDegree :=
      Polynomial.natDegree_map_eq_of_injective (algebraMap K M).injective g
    apply monic_irr gM hgMmonic (by omega)
    intro h hmonic hdvd hdeglt
    -- every root of `h` in `AlgebraicClosure M` is separable-algebraic over `K`
    have key : ∀ β : AlgebraicClosure M,
        (h.map (algebraMap M (AlgebraicClosure M))).IsRoot β → IsSeparable K β := by
      intro β hβ
      have hdvdΩ : (h.map (algebraMap M (AlgebraicClosure M))) ∣
          (g.map (algebraMap K (AlgebraicClosure M))) := by
        have heq : g.map (algebraMap K (AlgebraicClosure M))
            = gM.map (algebraMap M (AlgebraicClosure M)) := by
          rw [hgM, Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
        rw [heq]; exact Polynomial.map_dvd _ hdvd
      have hβg : (g.map (algebraMap K (AlgebraicClosure M))).eval β = 0 := by
        rcases hdvdΩ with ⟨w, hw⟩
        rw [hw, Polynomial.eval_mul]; rw [Polynomial.IsRoot] at hβ; rw [hβ, zero_mul]
      have haeval : (Polynomial.aeval β) g = 0 := by
        rw [Polynomial.aeval_def, ← Polynomial.eval_map]; exact hβg
      exact hgsep.of_dvd (minpoly.dvd K β haeval)
    -- hence every coefficient of `h` lies in the image of `K` (by `hSC`)
    have hcoeffK : ∀ k, h.coeff k ∈ Set.range (algebraMap K M) := by
      intro k
      have hsep : IsSeparable K (h.coeff k) := by
        set Ω := AlgebraicClosure M
        set hΩ := h.map (algebraMap M Ω) with hhΩ
        have hΩmonic : hΩ.Monic := hmonic.map _
        have hprod : hΩ = (Multiset.map (fun t => Polynomial.X - Polynomial.C t) hΩ.roots).prod :=
          (IsAlgClosed.splits hΩ).eq_prod_roots_of_monic hΩmonic
        have hmem : (algebraMap M Ω) (h.coeff k) ∈ (separableClosure K Ω).toSubalgebra := by
          rw [show (algebraMap M Ω) (h.coeff k) = hΩ.coeff k from (Polynomial.coeff_map _ _).symm,
            show hΩ.coeff k
                = (Multiset.map (fun t => Polynomial.X - Polynomial.C t) hΩ.roots).prod.coeff k
              from by rw [← hprod]]
          apply coeff_prod_mem Ω (separableClosure K Ω).toSubalgebra hΩ.roots _ k
          intro x hx
          rw [IntermediateField.mem_toSubalgebra, mem_separableClosure_iff]
          exact key x (by rw [Polynomial.mem_roots hΩmonic.ne_zero] at hx; exact hx)
        rw [IntermediateField.mem_toSubalgebra, mem_separableClosure_iff] at hmem
        unfold IsSeparable at hmem ⊢
        rwa [minpoly.algebraMap_eq (algebraMap M Ω).injective] at hmem
      have := hSC (h.coeff k) hsep.isIntegral hsep
      rw [Algebra.mem_bot] at this
      obtain ⟨c, hc⟩ := this; exact ⟨c, hc⟩
    -- lift `h` to `h0 : K[X]` and descend the factorization
    obtain ⟨h0, hh0⟩ : ∃ h0 : Polynomial K, h0.map (algebraMap K M) = h := by
      have : h ∈ Polynomial.lifts (algebraMap K M) := by
        rw [Polynomial.lifts_iff_coeff_lifts]; exact hcoeffK
      rw [Polynomial.mem_lifts] at this; exact this
    have hh0monic : h0.Monic :=
      Polynomial.monic_of_injective (algebraMap K M).injective (hh0 ▸ hmonic)
    have hh0deg : h0.natDegree = h.natDegree := by
      rw [← hh0, Polynomial.natDegree_map_eq_of_injective (algebraMap K M).injective]
    have hh0dvd : h0 ∣ g := by
      have : h0.map (algebraMap K M) ∣ gM := hh0 ▸ hdvd
      rwa [hgM, Polynomial.map_dvd_map _ (algebraMap K M).injective hh0monic] at this
    obtain ⟨w, hw⟩ := hh0dvd
    rcases hgirr.isUnit_or_isUnit hw with hu | hu
    · rw [← hh0deg]; exact Polynomial.natDegree_eq_zero_of_isUnit hu
    · exfalso
      have hwdeg : w.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
      have hgd : g.natDegree = h0.natDegree := by
        rw [hw, Polynomial.natDegree_mul hh0monic.ne_zero
          (by rintro rfl; simp only [mul_zero] at hw; exact hgirr.ne_zero hw), hwdeg, add_zero]
      omega
  -- `M[X]/(g_M)` is a field (hence a domain) since `g_M` is irreducible.
  have : Fact (Irreducible (g.map (algebraMap K M))) := ⟨hirr⟩
  have : IsDomain (AdjoinRoot (g.map (algebraMap K M))) := inferInstance
  -- `E ≃ₐ[K] AdjoinRoot g`
  have e1 : AdjoinRoot g ≃ₐ[K] E :=
    AdjoinRoot.equiv' g pb (by simp [hgdef]) (by simp [hgdef, minpoly.aeval])
  -- `M ⊗[K] AdjoinRoot g ≃ₐ[M] AdjoinRoot g_M`
  have Φ : M ⊗[K] AdjoinRoot g ≃ₐ[M] AdjoinRoot (g.map (algebraMap K M)) := by
    set gM := g.map (algebraMap K M) with hgM
    let f0 : AdjoinRoot g →ₐ[K] AdjoinRoot gM :=
      AdjoinRoot.liftAlgHom g (Algebra.ofId K _) (AdjoinRoot.root _) (by
        show (Polynomial.aeval (AdjoinRoot.root gM)) g = 0
        rw [AdjoinRoot.aeval_eq_of_algebra]; simp [hgM])
    have hf0root : f0 (AdjoinRoot.root g) = AdjoinRoot.root gM :=
      AdjoinRoot.liftAlgHom_root _ _ _ _
    let F : M ⊗[K] AdjoinRoot g →ₐ[M] AdjoinRoot gM :=
      Algebra.TensorProduct.lift (Algebra.ofId M _) f0 (fun x y => Commute.all _ _)
    have hFtmul : ∀ (a : M) (b : AdjoinRoot g),
        F (a ⊗ₜ[K] b) = (algebraMap M (AdjoinRoot gM)) a * f0 b := by
      intro a b; rfl
    have hGroot : (Polynomial.aeval (1 ⊗ₜ[K] AdjoinRoot.root g : M ⊗[K] AdjoinRoot g)) gM = 0 := by
      rw [hgM, Polynomial.aeval_map_algebraMap]
      have : (1 ⊗ₜ[K] AdjoinRoot.root g : M ⊗[K] AdjoinRoot g)
          = Algebra.TensorProduct.includeRight (AdjoinRoot.root g) := rfl
      rw [this, Polynomial.aeval_algHom_apply]; simp [AdjoinRoot.aeval_eq]
    let G : AdjoinRoot gM →ₐ[M] M ⊗[K] AdjoinRoot g :=
      AdjoinRoot.liftAlgHom gM (Algebra.ofId M _) (1 ⊗ₜ[K] AdjoinRoot.root g) hGroot
    have hGroot2 : G (AdjoinRoot.root gM) = 1 ⊗ₜ[K] AdjoinRoot.root g :=
      AdjoinRoot.liftAlgHom_root _ _ _ _
    have hGf0 : ∀ b : AdjoinRoot g, G (f0 b) = 1 ⊗ₜ[K] b := by
      have hext : (AlgHom.restrictScalars K G).comp f0
          = (Algebra.TensorProduct.includeRight : AdjoinRoot g →ₐ[K] M ⊗[K] AdjoinRoot g) := by
        apply AdjoinRoot.algHom_ext
        show G (f0 (AdjoinRoot.root g)) = Algebra.TensorProduct.includeRight (AdjoinRoot.root g)
        rw [hf0root, hGroot2]; rfl
      intro b
      exact congrFun (congrArg
        (fun (hh : AdjoinRoot g →ₐ[K] M ⊗[K] AdjoinRoot g) =>
          (hh : AdjoinRoot g → M ⊗[K] AdjoinRoot g))
        hext) b
    have hFr : F (1 ⊗ₜ[K] AdjoinRoot.root g) = AdjoinRoot.root gM := by
      rw [hFtmul, map_one, one_mul, hf0root]
    have hGa : ∀ a : M,
        G ((algebraMap M (AdjoinRoot gM)) a) = (a ⊗ₜ[K] 1 : M ⊗[K] AdjoinRoot g) := by
      intro a; rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]; simp
    refine AlgEquiv.ofAlgHom F G ?_ ?_
    · apply AdjoinRoot.algHom_ext
      show F (G (AdjoinRoot.root gM)) = AdjoinRoot.root gM
      rw [hGroot2, hFr]
    · apply Algebra.TensorProduct.ext'
      intro a b
      show G (F (a ⊗ₜ[K] b)) = a ⊗ₜ[K] b
      rw [hFtmul, map_mul, hGf0, hGa, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  -- assemble: `E ⊗[K] M ≃+* AdjoinRoot g_M`, a domain.
  let R : E ⊗[K] M ≃+* AdjoinRoot (g.map (algebraMap K M)) :=
    ((Algebra.TensorProduct.congr e1.symm (AlgEquiv.refl)).trans
      (Algebra.TensorProduct.comm K (AdjoinRoot g) M)).toRingEquiv.trans Φ.toRingEquiv
  exact MulEquiv.isDomain (AdjoinRoot (g.map (algebraMap K M))) R.toMulEquiv

/- **[LEMMAX] Lemma X (the genuine analytic hard core of Stacks 04KQ).**
*Relative algebraic closedness is preserved under adjoining transcendentals.* For fields
`L ⊆ E` with `L` (relatively) algebraically closed in `E` (hypothesis `hLE`), and a tuple of
indeterminates `σ`, the rational function field `L(t) = MvRatFunc σ L` is relatively algebraically
closed in `E(t) = MvRatFunc σ E`.

To avoid the absent and typeclass-fragile `Algebra (MvRatFunc σ L) (MvRatFunc σ E)`
instance, the
statement is phrased ring-theoretically: it takes the comparison ring hom `φ : MvRatFunc σ L →+*
MvRatFunc σ E` explicitly, together with the compatibility `hφ` pinning it down on the polynomial
subring (`φ` agrees with the coefficient inclusion `MvPolynomial.map (algebraMap L E)` after
localizing). "Algebraic over `L(t)`" is the existence of a nonzero `p : Polynomial (MvRatFunc σ L)`
with `eval₂ φ w p = 0`; the conclusion "`w ∈ L(t)`" is `w ∈ φ.range`.

*Proof.* Reduce to a single indeterminate and induct on `σ`, peeling one variable via
`MvPolynomial.finSuccEquiv`
/ iterated rational-function-field isos). Single variable: an element `η ∈ E[u]` integral over
`L[u]`
(clear denominators of the algebraic relation, then use that `E[u]` is a UFD hence integrally
closed)
specializes at every `λ ∈ L` to `η(λ) ∈ E` integral over `L`, hence in `L` (since `L` is
algebraically closed in `E`); as `L` is infinite, a polynomial over `E` taking values in `L` at all
of `L` has its coefficients in `L` (Vandermonde / Lagrange — "Sub-lemma F"), so `η ∈ L[u]`.
NO off-the-shelf Mathlib lemma (no `IsAlgClosedIn`-under-transcendental-extension API). This is the
single substantial standalone obligation; recommend its own AND decomposition along
(a) single-variable specialization core + Sub-lemma F (Vandermonde), and (b) the finite-`σ`
induction. -/

/-- **[LEMMAX-SUBF] Sub-lemma F (multivariate Vandermonde / Lagrange coefficient descent).**
Concrete, `φ`-free leaf: if a multivariate polynomial `η ∈ E[t]` takes values in the subfield
`L ⊆ E` (i.e. in `⊥ : Subalgebra L E`) at every `L`-point `a : σ → L`, then *all* its coefficients
lie in `L`. This is the multivariate Vandermonde/Lagrange interpolation argument, valid because `L`
is infinite, so an `E`-polynomial vanishing on all of `L^σ` minus its `L`-part is forced
to vanish.
This is the genuine concrete analytic kernel isolated from the `φ`/localization plumbing. -/
lemma geomIrred_lemmaX_subF
    (L E : Type u) [Field L] [Field E] [Algebra L E] [Infinite L]
    (σ : Type u) [Finite σ]
    (η : MvPolynomial σ E)
    (hval : ∀ a : σ → L, MvPolynomial.eval (fun i => algebraMap L E (a i)) η
              ∈ (⊥ : Subalgebra L E)) :
    -- true for infinite L; [Infinite L] is essential — fails over finite L, e.g. η=(x²+x)√2 over
    -- 𝔽₂(√2)).
    ∀ m, η.coeff m ∈ (⊥ : Subalgebra L E) := by
  classical
  -- Separation: an element of E lies in ⊥ iff every L-functional vanishing on ⊥ kills it.
  have hsep : ∀ x : E,
      (∀ f : E →ₗ[L] L, (∀ y ∈ (⊥ : Subalgebra L E).toSubmodule, f y = 0) → f x = 0) →
      x ∈ (⊥ : Subalgebra L E) := by
    intro x hx
    by_contra hxmem
    have hxW : x ∉ (⊥ : Subalgebra L E).toSubmodule := by
      rwa [Subalgebra.mem_toSubmodule]
    set W := (⊥ : Subalgebra L E).toSubmodule
    have hne : W.mkQ x ≠ 0 := by
      rwa [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    obtain ⟨g, hg⟩ := Module.Projective.exists_dual_ne_zero L hne
    have := hx (g.comp W.mkQ) (by
      intro y hy
      simp [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).mpr hy])
    apply hg
    simpa using this
  intro m
  apply hsep
  intro f hf
  -- The coefficient-wise pushforward F under f.
  let F : MvPolynomial σ E →ₗ[L] MvPolynomial σ L :=
    (AddMonoidAlgebra.coeffLinearEquiv L).symm.toLinearMap ∘ₗ
      Finsupp.mapRange.linearMap f ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv L).toLinearMap
  have hcoeff : ∀ (p : MvPolynomial σ E) (m : σ →₀ ℕ),
      MvPolynomial.coeff m (F p) = f (MvPolynomial.coeff m p) := by
    intro p m
    simp only [F, LinearMap.comp_apply, LinearEquiv.coe_coe, MvPolynomial.coeff,
      AddMonoidAlgebra.coeffLinearEquiv_apply, AddMonoidAlgebra.coeffLinearEquiv_symm_apply,
      AddMonoidAlgebra.coeff_ofCoeff, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply]
  have hC : ∀ e : E, F (MvPolynomial.C e) = MvPolynomial.C (f e) := by
    intro e
    apply MvPolynomial.ext; intro m
    rw [hcoeff, MvPolynomial.coeff_C, MvPolynomial.coeff_C, apply_ite f, map_zero]
  have hmul : ∀ (p : MvPolynomial σ E) (i : σ),
      F (p * MvPolynomial.X i) = F p * MvPolynomial.X i := by
    intro p i
    apply MvPolynomial.ext; intro m
    rw [hcoeff, MvPolynomial.coeff_mul_X', MvPolynomial.coeff_mul_X', hcoeff]
    split <;> simp
  -- eval-pushforward identity: eval a (F p) = f (eval (algebraMap∘a) p)
  have hpush : ∀ (p : MvPolynomial σ E) (a : σ → L),
      MvPolynomial.eval a (F p)
        = f (MvPolynomial.eval (fun i => algebraMap L E (a i)) p) := by
    intro p a
    induction p using MvPolynomial.induction_on with
    | C e => rw [hC]; simp
    | add p q hp hq =>
      rw [map_add, MvPolynomial.eval_add, MvPolynomial.eval_add, map_add, hp, hq]
    | mul_X p i hp =>
      rw [hmul, MvPolynomial.eval_mul, MvPolynomial.eval_mul, hp]
      simp only [MvPolynomial.eval_X]
      rw [show (MvPolynomial.eval (fun i => algebraMap L E (a i)) p) * (algebraMap L E (a i))
            = (a i) • (MvPolynomial.eval (fun i => algebraMap L E (a i)) p) by
            rw [Algebra.smul_def]; ring]
      rw [LinearMap.map_smul]
      simp [mul_comm]
  -- F η = 0 by funext over the infinite integral domain L
  have hFzero : F η = 0 := by
    apply MvPolynomial.funext
    intro a
    rw [hpush, map_zero]
    apply hf
    rw [Subalgebra.mem_toSubmodule]
    exact hval a
  -- conclude f (η.coeff m) = 0
  rw [← hcoeff, hFzero]
  simp

/-- **[LEMMAX-VIASUBF] Integral-reduction leaf, consuming Sub-lemma F.**
The `φ`/`eval₂` plumbing leaf: it carries the work of clearing denominators (turning the algebraic
relation over `L(t)` into integrality of a representative `η ∈ E[t]` over `L[t]`, using that `E[t]`
is a UFD hence integrally closed), specializing the variables at every `L`-point, and feeding the
resulting "values land in `L`" hypothesis into Sub-lemma F (`hF`) to descend the coefficients into
`L`, concluding `w ∈ φ.range`. It takes Sub-lemma F as the hypothesis `hF` (fully general in the
field pair, with `[Infinite L']`), so the burden of supplying `Infinite` for whichever specialized
field it applies F to lives here rather than being baked into the statement of `geomIrred_lemmaX`
(which makes NO infiniteness assumption on `L`). -/
lemma geomIrred_lemmaX_viaSubF
    (L E : Type u) [Field L] [Field E] [Algebra L E] [Infinite L]
    (hLE : ∀ z : E, IsAlgebraic L z → z ∈ (⊥ : Subalgebra L E))
    (σ : Type u) [Finite σ]
    (φ : MvRatFunc σ L →+* MvRatFunc σ E)
    (hφ : φ.comp (algebraMap (MvPolynomial σ L) (MvRatFunc σ L)) =
          (algebraMap (MvPolynomial σ E) (MvRatFunc σ E)).comp (MvPolynomial.map (algebraMap L E)))
    (w : MvRatFunc σ E)
    (hw : ∃ p : Polynomial (MvRatFunc σ L), p ≠ 0 ∧ Polynomial.eval₂ φ w p = 0)
    (hF : ∀ (L' E' : Type u) [Field L'] [Field E'] [Algebra L' E'] [Infinite L']
            (σ' : Type u) [Finite σ'] (η : MvPolynomial σ' E'),
            (∀ a : σ' → L', MvPolynomial.eval (fun i => algebraMap L' E' (a i)) η
                ∈ (⊥ : Subalgebra L' E')) →
            ∀ m, η.coeff m ∈ (⊥ : Subalgebra L' E')) :
    w ∈ φ.range := by
  classical
  -- Notation for the two fraction-ring inclusions.
  set ιL : MvPolynomial σ L →+* MvRatFunc σ L :=
    algebraMap (MvPolynomial σ L) (MvRatFunc σ L) with hιL
  set ιE : MvPolynomial σ E →+* MvRatFunc σ E :=
    algebraMap (MvPolynomial σ E) (MvRatFunc σ E) with hιE
  -- φ is injective (a nonzero ring hom out of a field), used at the end.
  have hφinj : Function.Injective φ := φ.injective
  -- Step 1+2 (denominator clearing + integral closure): there is a nonzero `b ∈ L[t]` and a
  -- representative `η ∈ E[t]` with `φ(ιL b) * w = ιE η`, i.e. `w = ιE η / φ(ιL b)`, and `η`
  -- specializes into `⊥` at every L-point (it is integral over the L[t]-image).
  obtain ⟨b, hb, η, hηw, hval⟩ :
      ∃ (b : MvPolynomial σ L), b ≠ 0 ∧ ∃ η : MvPolynomial σ E,
        φ (ιL b) * w = ιE η ∧
        ∀ a : σ → L, MvPolynomial.eval (fun i => algebraMap L E (a i)) η
            ∈ (⊥ : Subalgebra L E) := by
    obtain ⟨p, hp, hpeval⟩ := hw
    set g : Polynomial (MvPolynomial σ L) :=
      IsLocalization.integerNormalization (nonZeroDivisors (MvPolynomial σ L)) p with hgdef
    have hgne : g ≠ 0 := by
      rw [hgdef, Ne, IsFractionRing.integerNormalization_eq_zero_iff]; exact hp
    have hgeval : Polynomial.eval₂ (φ.comp ιL) w g = 0 :=
      IsLocalization.integerNormalization_eval₂_eq_zero
        (nonZeroDivisors (MvPolynomial σ L)) φ p hpeval
    set b : MvPolynomial σ L := g.leadingCoeff with hbdef
    have hbne : b ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hgne
    set f := φ.comp ιL with hfdef
    have hyint : f.IsIntegralElem (f b * w) :=
      RingHom.isIntegralElem_leadingCoeff_mul f g w hgeval
    obtain ⟨G, hGmonic, hGeval⟩ := hyint
    have hf2 : f = ιE.comp (MvPolynomial.map (algebraMap L E)) := by rw [hfdef, hιL, hιE, ← hφ]
    have hGeval2 : Polynomial.eval₂ ιE (f b * w)
        (G.map (MvPolynomial.map (algebraMap L E))) = 0 := by
      rw [Polynomial.eval₂_map, ← hf2]; exact hGeval
    have hyintE : ιE.IsIntegralElem (f b * w) :=
      ⟨G.map (MvPolynomial.map (algebraMap L E)), hGmonic.map _, hGeval2⟩
    have hyintE' : IsIntegral (MvPolynomial σ E) (f b * w) := hyintE
    rw [IsIntegrallyClosed.isIntegral_iff] at hyintE'
    obtain ⟨η, hη⟩ := hyintE'
    have hfb : f b = φ (ιL b) := by rw [hfdef]; rfl
    refine ⟨b, hbne, η, ?_, ?_⟩
    · rw [hfb] at hη; exact hη.symm
    · have hηroot : Polynomial.aeval η (G.map (MvPolynomial.map (algebraMap L E))) = 0 := by
        have hinj : Function.Injective ιE :=
          IsFractionRing.injective (MvPolynomial σ E) (MvRatFunc σ E)
        apply hinj
        rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂,
            (by simp : ιE.comp (algebraMap (MvPolynomial σ E) (MvPolynomial σ E)) = ιE), hη]
        exact hGeval2
      intro a
      set ev : MvPolynomial σ E →+* E := MvPolynomial.eval (fun i => algebraMap L E (a i)) with hev
      set evL : MvPolynomial σ L →+* L := MvPolynomial.eval a with hevL
      have hcomp : ev.comp (MvPolynomial.map (algebraMap L E)) = (algebraMap L E).comp evL := by
        apply MvPolynomial.ringHom_ext
        · intro r; simp [hev, hevL]
        · intro i; simp [hev, hevL]
      have hGmonic2 : (G.map evL).Monic := hGmonic.map evL
      have hroot : Polynomial.aeval (ev η) (G.map evL) = 0 := by
        rw [Polynomial.aeval_def] at hηroot ⊢
        have h1 : ev (Polynomial.eval₂ (algebraMap (MvPolynomial σ E) (MvPolynomial σ E)) η
            (G.map (MvPolynomial.map (algebraMap L E)))) = 0 := by rw [hηroot, map_zero]
        rw [Polynomial.hom_eval₂, Polynomial.eval₂_map] at h1
        rw [(by simp : ev.comp (algebraMap (MvPolynomial σ E) (MvPolynomial σ E)) = ev)] at h1
        rw [hcomp, ← Polynomial.eval₂_map] at h1
        exact h1
      have hIntegral : IsIntegral L (ev η) := ⟨G.map evL, hGmonic2, by rw [← hroot]; rfl⟩
      exact hLE _ hIntegral.isAlgebraic
  -- Step 4: feed Sub-lemma F (`hF`) at L' := L, E' := E, σ' := σ to descend coefficients into ⊥.
  have hcoeffs : ∀ m, η.coeff m ∈ (⊥ : Subalgebra L E) :=
    hF L E σ η hval
  -- Step 5: η descends to η₀ : MvPolynomial σ L with map(algebraMap L E) η₀ = η.
  have hr : ∀ m, η.coeff m ∈ Set.range (algebraMap L E) := by
    intro m; rw [← Algebra.mem_bot]; exact hcoeffs m
  set η₀ : MvPolynomial σ L :=
    AddMonoidAlgebra.ofCoeff
      (Finsupp.mapRange (Function.invFun (algebraMap L E)) (by simp [Function.invFun])
        (AddMonoidAlgebra.coeff η))
    with hη₀def
  have hmap : MvPolynomial.map (algebraMap L E) η₀ = η := by
    apply MvPolynomial.ext
    intro m
    rw [MvPolynomial.coeff_map]
    have hcm : MvPolynomial.coeff m η₀
        = Function.invFun (algebraMap L E) (MvPolynomial.coeff m η) := by
      rw [hη₀def]
      simp only [MvPolynomial.coeff, Finsupp.mapRange_apply]
    rw [hcm]
    exact Function.invFun_eq (hr m)
  -- ιE η = φ (ιL η₀) by hφ.
  have hηφ : ιE η = φ (ιL η₀) := by
    have hh := RingHom.congr_fun hφ η₀
    simp only [RingHom.comp_apply] at hh
    rw [hh, hmap]
  -- φ (ιL b) ≠ 0 since b ≠ 0 (ιL injective) and φ injective.
  have hbne : φ (ιL b) ≠ 0 := by
    have hιLb : ιL b ≠ 0 := by
      rw [hιL]; exact fun h => hb (IsFractionRing.injective (MvPolynomial σ L) (MvRatFunc σ L)
        (by rw [h, map_zero]))
    exact fun h => hιLb (hφinj (by rw [h, map_zero]))
  -- Conclude w = φ (ιL η₀ / ιL b) ∈ φ.range.
  refine ⟨ιL η₀ / ιL b, ?_⟩
  rw [map_div₀, ← hηφ]
  -- now goal: ιE η / φ (ιL b) = w
  field_simp
  exact hηw.symm

/-- Relative algebraic closedness transported to rational function fields: if every element of
`E` algebraic over `L` lies in `L`, then any `w ∈ MvRatFunc σ E` algebraic over
`MvRatFunc σ L`, along the coefficient-inclusion `φ`, lies in the range of `φ`. -/
theorem geomIrred_lemmaX
    (L E : Type u) [Field L] [Field E] [Algebra L E] [Infinite L]
    (hLE : ∀ z : E, IsAlgebraic L z → z ∈ (⊥ : Subalgebra L E))
    (σ : Type u) [Finite σ]
    (φ : MvRatFunc σ L →+* MvRatFunc σ E)
    (hφ : φ.comp (algebraMap (MvPolynomial σ L) (MvRatFunc σ L)) =
          (algebraMap (MvPolynomial σ E) (MvRatFunc σ E)).comp (MvPolynomial.map (algebraMap L E)))
    (w : MvRatFunc σ E)
    (hw : ∃ p : Polynomial (MvRatFunc σ L), p ≠ 0 ∧ Polynomial.eval₂ φ w p = 0) :
    w ∈ φ.range :=
  -- relative algebraic closedness, true for any fields L ⊆ E with L alg. closed in E).
  -- Reduce to two leaves — the concrete Vandermonde descent
  -- `geomIrred_lemmaX_subF`
  -- (Sub-lemma F) and the integral-reduction plumbing `geomIrred_lemmaX_viaSubF` that consumes it.
  geomIrred_lemmaX_viaSubF L E hLE σ φ hφ w hw
    (fun L' E' _ _ _ _ σ' _ η hval m => geomIrred_lemmaX_subF L' E' σ' η hval m)

/- **[ISO-EMB-GKF] The heavy injective comparison algebra hom.**
The genuine typeclass-tower-engineering content extracted from `geomIrred_Lt_comparison_data`:
build `φ : MvRatFunc σ L →+* MvRatFunc σ F`, the coefficient-inclusion lift, and
`eK : K ≃+* MvRatFunc σ L`
(the `L(t) = K` identification), and an INJECTIVE `L`-algebra hom `gKF : (K ⊗[L] F) →ₐ[L] MvRatFunc
σ F`
with `gKF (algebraMap K _ c) = φ (eK c)`, together with `hφ`. Isolated as its own
top-level lemma so
each block elaborates within budget (the assembled monolith exceeds the heartbeat/whnf limit under
`respectTransparency false`). NO mathematical kernel — pure fraction-ring/tensor/localization
plumbing. -/
/- **[CMP-P1]** φ/eK block of `geomIrred_Lt_comparison_gKF` (φ-side), isolated for elaboration
budget. -/
/-- The `φ` and `eK` half of `geomIrred_Lt_comparison_gKF`: the coefficient-inclusion
`φ : MvRatFunc σ L →+* MvRatFunc σ F` and the identification `eK : K ≃+* MvRatFunc σ L`, with
their compatibility with the polynomial algebra maps. -/
theorem geomIrred_cmp_P1
    (L : Type u) [Field L]
    (σ : Type u) [Finite σ]
    (K : Type u) [Field K] [Algebra L K]
    [Algebra (MvPolynomial σ L) K] [IsScalarTower L (MvPolynomial σ L) K]
    [IsFractionRing (MvPolynomial σ L) K]
    (F : Type u) [Field F] [Algebra L F] :
    ∃ (φ : MvRatFunc σ L →+* MvRatFunc σ F) (eK : K ≃+* MvRatFunc σ L),
      (φ.comp (algebraMap (MvPolynomial σ L) (MvRatFunc σ L)) =
        (algebraMap (MvPolynomial σ F) (MvRatFunc σ F)).comp (MvPolynomial.map (algebraMap L F))) ∧
      (∀ p : MvPolynomial σ L, φ (eK (algebraMap (MvPolynomial σ L) K p)) =
        (algebraMap (MvPolynomial σ F) (MvRatFunc σ F)) (MvPolynomial.map (algebraMap L F) p)) ∧
      (∀ c : L, φ (eK (algebraMap L K c)) = algebraMap L (MvRatFunc σ F) c) := by
  classical
  let eKalg : K ≃ₐ[MvPolynomial σ L] MvRatFunc σ L :=
    IsLocalization.algEquiv (nonZeroDivisors (MvPolynomial σ L)) K (MvRatFunc σ L)
  let eK : K ≃+* MvRatFunc σ L := eKalg.toRingEquiv
  let coeffincl : MvPolynomial σ L →+* MvRatFunc σ F :=
    (algebraMap (MvPolynomial σ F) (MvRatFunc σ F)).comp (MvPolynomial.map (algebraMap L F))
  have hcoeffinj : Function.Injective coeffincl := by
    show Function.Injective
      ((algebraMap (MvPolynomial σ F) (MvRatFunc σ F)).comp (MvPolynomial.map (algebraMap L F)))
    exact (IsFractionRing.injective (MvPolynomial σ F) (MvRatFunc σ F)).comp
      (MvPolynomial.map_injective _ (algebraMap L F).injective)
  let φ : MvRatFunc σ L →+* MvRatFunc σ F := IsFractionRing.lift hcoeffinj
  have hφcomp : φ.comp (algebraMap (MvPolynomial σ L) (MvRatFunc σ L)) = coeffincl :=
    IsLocalization.lift_comp _
  have hKbridge : ∀ p : MvPolynomial σ L,
      φ (eK (algebraMap (MvPolynomial σ L) K p)) = coeffincl p := by
    intro p
    have h1 : eK (algebraMap (MvPolynomial σ L) K p)
        = algebraMap (MvPolynomial σ L) (MvRatFunc σ L) p := eKalg.commutes p
    rw [h1]; exact RingHom.congr_fun hφcomp p
  have hLcomm : ∀ c : L, φ (eK (algebraMap L K c)) = algebraMap L (MvRatFunc σ F) c := by
    intro c
    rw [IsScalarTower.algebraMap_apply L (MvPolynomial σ L) K c, hKbridge]
    show (algebraMap (MvPolynomial σ F) (MvRatFunc σ F))
      (MvPolynomial.map (algebraMap L F) (algebraMap L (MvPolynomial σ L) c)) = _
    rw [MvPolynomial.algebraMap_eq, MvPolynomial.map_C,
      IsScalarTower.algebraMap_apply L F (MvRatFunc σ F) c,
      IsScalarTower.algebraMap_apply F (MvPolynomial σ F) (MvRatFunc σ F) (algebraMap L F c),
      MvPolynomial.algebraMap_eq]
  exact ⟨φ, eK, hφcomp, hKbridge, hLcomm⟩

/- **[CMP-P2]** the `gKF` `L`-algebra-hom block, isolated for elaboration budget. -/
/-- The `gKF` half: the `L`-algebra homomorphism `K ⊗[L] F →ₐ[L] MvRatFunc σ F` determined by
`φ`, `eK` and the structure map of `F`. -/
theorem geomIrred_cmp_P2
    (L : Type u) [Field L]
    (σ : Type u) [Finite σ]
    (K : Type u) [Field K] [Algebra L K]
    (F : Type u) [Field F] [Algebra L F]
    (φ : MvRatFunc σ L →+* MvRatFunc σ F)
    (eK : K ≃+* MvRatFunc σ L)
    (hLcomm : ∀ c : L, φ (eK (algebraMap L K c)) = algebraMap L (MvRatFunc σ F) c) :
    ∃ (gKF : (K ⊗[L] F) →ₐ[L] MvRatFunc σ F),
      (∀ c : K, gKF (algebraMap K (K ⊗[L] F) c) = φ (eK c)) ∧
      (∀ (k : K) (f : F), gKF (k ⊗ₜ[L] f) = φ (eK k) * algebraMap F (MvRatFunc σ F) f) := by
  classical
  let fK : K →ₐ[L] MvRatFunc σ F :=
    AlgHom.mk' (φ.comp (eK : K →+* MvRatFunc σ L)) (by
      intro c x
      show φ (eK (c • x)) = c • φ (eK x)
      rw [Algebra.smul_def, map_mul, map_mul, hLcomm, Algebra.smul_def])
  let fF : F →ₐ[L] MvRatFunc σ F := IsScalarTower.toAlgHom L F (MvRatFunc σ F)
  let gKF : (K ⊗[L] F) →ₐ[L] MvRatFunc σ F :=
    Algebra.TensorProduct.lift fK fF (fun x y => Commute.all _ _)
  have hgKF_tmul : ∀ (k : K) (f : F),
      gKF (k ⊗ₜ[L] f) = φ (eK k) * algebraMap F (MvRatFunc σ F) f := by
    intro k f
    rw [Algebra.TensorProduct.lift_tmul]
    rfl
  have hgKF_left : ∀ c : K, gKF (algebraMap K (K ⊗[L] F) c) = φ (eK c) := by
    intro c
    have hmap : (algebraMap K (K ⊗[L] F)) c = c ⊗ₜ[L] (1 : F) := by
      rw [Algebra.TensorProduct.algebraMap_apply]; simp
    rw [hmap, hgKF_tmul, map_one, mul_one]
  exact ⟨gKF, hgKF_left, hgKF_tmul⟩

/- **[CMP-P3]** the φ-independent localization block (`mygD`, `gLoc`), isolated for budget. -/
/-- The localization half, independent of `φ`: the maps `mygD` and `gLoc` out of
`MvPolynomial σ L ⊗[L] F` and its localization at `MvPolynomial σ L`. -/
theorem geomIrred_cmp_P3
    (L : Type u) [Field L]
    (σ : Type u) [Finite σ]
    (K : Type u) [Field K] [Algebra L K]
    [Algebra (MvPolynomial σ L) K] [IsScalarTower L (MvPolynomial σ L) K]
    [IsFractionRing (MvPolynomial σ L) K]
    (F : Type u) [Field F] [Algebra L F]
    [IsDomain (MvPolynomial σ L ⊗[L] F)] :
    ∃ (mygD : (MvPolynomial σ L ⊗[L] F) →+* MvRatFunc σ F)
      (gLoc : ((MvPolynomial σ L ⊗[L] F) ⊗[MvPolynomial σ L] K) →+* MvRatFunc σ F),
      (∀ (p : MvPolynomial σ L) (f : F), mygD (p ⊗ₜ[L] f) =
        (algebraMap (MvPolynomial σ F) (MvRatFunc σ F))
          (f • MvPolynomial.map (algebraMap L F) p)) ∧
      (gLoc.comp Algebra.TensorProduct.includeLeftRingHom = mygD) ∧
      Function.Injective gLoc := by
  classical
  let myequiv : (MvPolynomial σ L ⊗[L] F) ≃+* MvPolynomial σ F :=
    (Algebra.TensorProduct.comm L (MvPolynomial σ L) F).toRingEquiv.trans
      (MvPolynomial.algebraTensorAlgEquiv L F).toRingEquiv
  have hmyequiv_tmul : ∀ (p : MvPolynomial σ L) (f : F),
      myequiv (p ⊗ₜ[L] f) = f • MvPolynomial.map (algebraMap L F) p := by
    intro p f
    show (MvPolynomial.algebraTensorAlgEquiv L F)
      ((Algebra.TensorProduct.comm L (MvPolynomial σ L) F) (p ⊗ₜ[L] f)) = _
    rw [Algebra.TensorProduct.comm_tmul, MvPolynomial.algebraTensorAlgEquiv_tmul]
  let mygD : (MvPolynomial σ L ⊗[L] F) →+* MvRatFunc σ F :=
    (algebraMap (MvPolynomial σ F) (MvRatFunc σ F)).comp myequiv.toRingHom
  have hmygD_inj : Function.Injective mygD :=
    (IsFractionRing.injective (MvPolynomial σ F) (MvRatFunc σ F)).comp myequiv.injective
  have hmygD_tmul : ∀ (p : MvPolynomial σ L) (f : F),
      mygD (p ⊗ₜ[L] f) = (algebraMap (MvPolynomial σ F) (MvRatFunc σ F))
        (f • MvPolynomial.map (algebraMap L F) p) := by
    intro p f
    show (algebraMap (MvPolynomial σ F) (MvRatFunc σ F)) (myequiv (p ⊗ₜ[L] f)) = _
    rw [hmyequiv_tmul]
  have hinjRD : Function.Injective (algebraMap (MvPolynomial σ L) (MvPolynomial σ L ⊗[L] F)) := by
    have : Function.Injective (algebraMap L F) := (algebraMap L F).injective
    exact Algebra.TensorProduct.includeLeft_injective (R := L)
      (A := MvPolynomial σ L) (B := F) (S := MvPolynomial σ L) this
  have hMDle : Algebra.algebraMapSubmonoid (MvPolynomial σ L ⊗[L] F)
      (nonZeroDivisors (MvPolynomial σ L)) ≤ nonZeroDivisors (MvPolynomial σ L ⊗[L] F) := by
    rintro z ⟨m, hm, rfl⟩
    apply mem_nonZeroDivisors_of_ne_zero
    have hm0 : (m : MvPolynomial σ L) ≠ 0 := nonZeroDivisors.coe_ne_zero ⟨m, hm⟩
    intro h
    exact hm0 (hinjRD (by rw [map_zero]; exact h))
  have hunits : ∀ y : (Algebra.algebraMapSubmonoid (MvPolynomial σ L ⊗[L] F)
      (nonZeroDivisors (MvPolynomial σ L))), IsUnit (mygD (y : MvPolynomial σ L ⊗[L] F)) := by
    intro y
    refine isUnit_iff_ne_zero.mpr fun h0 => nonZeroDivisors.coe_ne_zero ⟨_, hMDle y.2⟩
      (hmygD_inj (by rw [h0, map_zero]))
  let gLoc : ((MvPolynomial σ L ⊗[L] F) ⊗[MvPolynomial σ L] K) →+* MvRatFunc σ F :=
    IsLocalization.lift (S := (MvPolynomial σ L ⊗[L] F) ⊗[MvPolynomial σ L] K) hunits
  have hgLoc_comp : gLoc.comp Algebra.TensorProduct.includeLeftRingHom = mygD :=
    IsLocalization.lift_comp _
  have hgLoc_inj : Function.Injective gLoc := by
    rw [IsLocalization.lift_injective_iff]
    intro x y
    exact ⟨fun hxy => congrArg mygD
        (IsLocalization.injective ((MvPolynomial σ L ⊗[L] F) ⊗[MvPolynomial σ L] K) hMDle hxy),
      fun hxy => congrArg _ (hmygD_inj hxy)⟩
  exact ⟨mygD, gLoc, hmygD_tmul, hgLoc_comp, hgLoc_inj⟩

/- **[CMP-P4]** the φ-independent equiv block (`efin`), isolated for budget. -/
/-- The identification `(MvPolynomial σ L ⊗[L] F) ⊗[MvPolynomial σ L] K ≃+* K ⊗[L] F`. -/
theorem geomIrred_cmp_P4
    (L : Type u) [Field L]
    (σ : Type u) [Finite σ]
    (K : Type u) [Field K] [Algebra L K]
    [Algebra (MvPolynomial σ L) K] [IsScalarTower L (MvPolynomial σ L) K]
    [IsFractionRing (MvPolynomial σ L) K]
    (F : Type u) [Field F] [Algebra L F] :
    ∃ (efin : ((MvPolynomial σ L ⊗[L] F) ⊗[MvPolynomial σ L] K) ≃+* (K ⊗[L] F)),
      (∀ (p : MvPolynomial σ L) (f : F) (k : K),
        efin ((p ⊗ₜ[L] f) ⊗ₜ[MvPolynomial σ L] k)
          = (algebraMap (MvPolynomial σ L) K p * k) ⊗ₜ[L] f) := by
  classical
  let efin : ((MvPolynomial σ L ⊗[L] F) ⊗[MvPolynomial σ L] K) ≃+* (K ⊗[L] F) :=
    (Algebra.TensorProduct.comm (MvPolynomial σ L) (MvPolynomial σ L ⊗[L] F) K).toRingEquiv.trans
      (Algebra.TensorProduct.cancelBaseChange L (MvPolynomial σ L) K K F).toRingEquiv
  have hefin_tmul : ∀ (p : MvPolynomial σ L) (f : F) (k : K),
      efin ((p ⊗ₜ[L] f) ⊗ₜ[MvPolynomial σ L] k)
        = (algebraMap (MvPolynomial σ L) K p * k) ⊗ₜ[L] f := by
    intro p f k
    show (Algebra.TensorProduct.cancelBaseChange L (MvPolynomial σ L) K K F)
      ((Algebra.TensorProduct.comm (MvPolynomial σ L) (MvPolynomial σ L ⊗[L] F) K)
        ((p ⊗ₜ[L] f) ⊗ₜ[MvPolynomial σ L] k)) = _
    rw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.cancelBaseChange_tmul,
      Algebra.smul_def, mul_comm]
  exact ⟨efin, hefin_tmul⟩

/-- The structural comparison used for `L(t)`: for `L` and `F` algebraically closed and `K` the
fraction field of `MvPolynomial σ L`, there are `φ`, `eK` and an injective
`gKF : (K ⊗[L] F) →ₐ[L] MvRatFunc σ F` compatible with them. -/
theorem geomIrred_Lt_comparison_gKF
    (L : Type u) [Field L] [IsAlgClosed L]
    (σ : Type u) [Finite σ]
    (K : Type u) [Field K] [Algebra L K]
    [Algebra (MvPolynomial σ L) K] [IsScalarTower L (MvPolynomial σ L) K]
    [IsFractionRing (MvPolynomial σ L) K]
    (F : Type u) [Field F] [Algebra L F] [IsAlgClosed F] :
    ∃ (φ : MvRatFunc σ L →+* MvRatFunc σ F)
      (eK : K ≃+* MvRatFunc σ L)
      (gKF : (K ⊗[L] F) →ₐ[L] MvRatFunc σ F),
      Function.Injective gKF ∧
      (φ.comp (algebraMap (MvPolynomial σ L) (MvRatFunc σ L)) =
        (algebraMap (MvPolynomial σ F) (MvRatFunc σ F)).comp (MvPolynomial.map (algebraMap L F))) ∧
      (∀ c : K, gKF (algebraMap K (K ⊗[L] F) c) = φ (eK c)) := by
  classical
  have hRdom : IsDomain (K ⊗[L] F) := geomIrred_fg_R_isDomain L σ K F
  have hDdom : IsDomain (MvPolynomial σ L ⊗[L] F) :=
    MulEquiv.isDomain (MvPolynomial σ F)
      ((Algebra.TensorProduct.comm L (MvPolynomial σ L) F).toRingEquiv.trans
        (MvPolynomial.algebraTensorAlgEquiv L F).toRingEquiv).toMulEquiv
  obtain ⟨φ, eK, hφcomp, hKbridge, hLcomm⟩ := geomIrred_cmp_P1 L σ K F
  obtain ⟨gKF, hgKF_left, hgKF_tmul⟩ := geomIrred_cmp_P2 L σ K F φ eK hLcomm
  obtain ⟨mygD, gLoc, hmygD_tmul, hgLoc_comp, hgLoc_inj⟩ := geomIrred_cmp_P3 L σ K F
  obtain ⟨efin, hefin_tmul⟩ := geomIrred_cmp_P4 L σ K F
  have hkey : ∀ d : (MvPolynomial σ L ⊗[L] F),
      gKF (efin (Algebra.TensorProduct.includeLeftRingHom d)) = mygD d := by
    intro d
    induction d using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, map_add, map_add, ha, hb]
    | tmul p f =>
      rw [show (Algebra.TensorProduct.includeLeftRingHom (p ⊗ₜ[L] f) :
            (MvPolynomial σ L ⊗[L] F) ⊗[MvPolynomial σ L] K)
            = (p ⊗ₜ[L] f) ⊗ₜ[MvPolynomial σ L] (1 : K) from rfl,
        hefin_tmul, mul_one, hgKF_tmul, hKbridge,
        hmygD_tmul, Algebra.smul_def, map_mul,
        IsScalarTower.algebraMap_apply F (MvPolynomial σ F) (MvRatFunc σ F) f, mul_comm]
  have hgKF_inj : Function.Injective gKF := by
    set G : ((MvPolynomial σ L ⊗[L] F) ⊗[MvPolynomial σ L] K) →+* MvRatFunc σ F :=
      gKF.toRingHom.comp (efin : ((MvPolynomial σ L ⊗[L] F) ⊗[MvPolynomial σ L] K) →+* (K ⊗[L] F))
      with hGdef
    have hGcomp : ∀ d : (MvPolynomial σ L ⊗[L] F),
        G (Algebra.TensorProduct.includeLeftRingHom d) = mygD d := by
      intro d
      rw [hGdef]
      show gKF (efin (Algebra.TensorProduct.includeLeftRingHom d)) = mygD d
      exact hkey d
    have hcompeq : G = gLoc := by
      apply IsLocalization.ringHom_ext
        (S := (MvPolynomial σ L ⊗[L] F) ⊗[MvPolynomial σ L] K)
        (Algebra.algebraMapSubmonoid (MvPolynomial σ L ⊗[L] F) (nonZeroDivisors (MvPolynomial σ L)))
      refine RingHom.ext fun d => ?_
      show G (algebraMap (MvPolynomial σ L ⊗[L] F)
          ((MvPolynomial σ L ⊗[L] F) ⊗[MvPolynomial σ L] K) d)
        = gLoc (algebraMap (MvPolynomial σ L ⊗[L] F)
          ((MvPolynomial σ L ⊗[L] F) ⊗[MvPolynomial σ L] K) d)
      exact (hGcomp d).trans (RingHom.congr_fun hgLoc_comp d).symm
    have h2 : Function.Injective G := by rw [hcompeq]; exact hgLoc_inj
    have h3 : Function.Injective (gKF ∘ efin) := by
      rw [hGdef] at h2; exact h2
    exact h3.of_comp_right efin.surjective
  exact ⟨φ, eK, gKF, hgKF_inj, hφcomp, hgKF_left⟩

/-- **[ISO-EMB] The structural comparison data for the `geomIrred_Lt_algClosedIn` reduction.**
Build the comparison ring hom `φ : MvRatFunc σ L →+* MvRatFunc σ F`, an INJECTIVE ring hom
`j : Frac(K ⊗[L] F) →+* MvRatFunc σ F`, and a ring equiv `eK : K ≃+* MvRatFunc σ L`, satisfying
`hφ` (φ agrees with the coefficient inclusion on the polynomial subring) and
`hcompat : ∀ c, φ (eK c) = j (algebraMap K _ c)`. The heavy injective `L`-algebra hom
`gKF : (K ⊗[L] F) →ₐ[L] MvRatFunc σ F` is supplied by `geomIrred_Lt_comparison_gKF`;
here we lift it
to the fraction field and assemble. NO new mathematical kernel; pure fraction-ring/tensor plumbing.
-/
theorem geomIrred_Lt_comparison_data
    (L : Type u) [Field L] [IsAlgClosed L]
    (σ : Type u) [Finite σ]
    (K : Type u) [Field K] [Algebra L K]
    [Algebra (MvPolynomial σ L) K] [IsScalarTower L (MvPolynomial σ L) K]
    [IsFractionRing (MvPolynomial σ L) K]
    (F : Type u) [Field F] [Algebra L F] [IsAlgClosed F] :
    ∃ (φ : MvRatFunc σ L →+* MvRatFunc σ F)
      (j : FractionRing (K ⊗[L] F) →+* MvRatFunc σ F)
      (eK : K ≃+* MvRatFunc σ L),
      Function.Injective j ∧
      (φ.comp (algebraMap (MvPolynomial σ L) (MvRatFunc σ L)) =
        (algebraMap (MvPolynomial σ F) (MvRatFunc σ F)).comp (MvPolynomial.map (algebraMap L F))) ∧
      (∀ c : K, φ (eK c) = j (algebraMap K (FractionRing (K ⊗[L] F)) c)) := by
  classical
  have hRdom : IsDomain (K ⊗[L] F) := geomIrred_fg_R_isDomain L σ K F
  obtain ⟨φ, eK, gKF, hgKF_inj, hφcomp, hgKF_left⟩ :=
    geomIrred_Lt_comparison_gKF L σ K F
  let j : FractionRing (K ⊗[L] F) →+* MvRatFunc σ F :=
    IsFractionRing.lift (A := K ⊗[L] F) (K := FractionRing (K ⊗[L] F)) hgKF_inj
  have hj_inj : Function.Injective j := j.injective
  have hj_alg : ∀ x : K ⊗[L] F,
      j (algebraMap (K ⊗[L] F) (FractionRing (K ⊗[L] F)) x) = gKF x :=
    IsFractionRing.lift_algebraMap hgKF_inj
  refine ⟨φ, j, eK, hj_inj, hφcomp, ?_⟩
  intro c
  have hjeq := hj_alg (algebraMap K (K ⊗[L] F) c)
  rw [← IsScalarTower.algebraMap_apply K (K ⊗[L] F) (FractionRing (K ⊗[L] F)) c] at hjeq
  rw [hjeq, hgKF_left]
