module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.GradedAlgebra.Basic
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.RingTheory.GradedAlgebra.IntegralClosure.GradedTwist

/-!
# Two-variable Laurent descent lemmas

The two-variable coefficient map `Φ₁`, the degree twist preserving integrality, descent of
integrality through a split finite free extension, the Selmer-polynomial unit lemmas,
transport of descent bundles, and the inner step `mqod_inner` of the monic-quotient
argument used in the proof that the integral closure of a graded ring is graded.
-/

@[expose] public section

universe u_1 u_2
variable {R : Type u_1} {S : Type u_2} [CommRing R] [CommRing S] [Algebra R S]
variable (ℛ : ℕ → AddSubgroup R) (𝒮 : ℕ → AddSubgroup S)
variable [GradedRing ℛ] [GradedRing 𝒮]

/- ============================================================================
   L3a — THE ANALYTIC KERNEL, v3 decomposition (real Stacks 077G argument).

   Branch-5's `core_resultant_bezout`/`isolate_monomial_via_unit` split is ABANDONED:
   `core_resultant_bezout` (`X^s−1` a unit mod `X^m−X^i−1`) is FALSE — counterexample
   `m=3,i=0,s=2` (`Res(X²−1,X³−2)=3`).

   The correct argument
   uses the multiplier `(t^m − t^n)` — a DIFFERENCE OF TWO DEGREES occurring in `w` —
   and makes it equal `−1` (a unit, trivially) by passing to the FINITE-FREE MONIC
   quotient `(LaurentPolynomial R)[U]/(U^m − U^n − 1)`.  There is NO "t^s−1 is a unit"
   claim, no resultant, no Vandermonde-determinant inversion.

   Structure (induction on `T`-support size of `w`, two-term peeling):
   • `laurent_twist_preserves_integral` (Sub-lemma A): the degree-twist σ : T ↦ t·T over
     the 2nd Laurent variable `t` preserves integrality along the lifted base map Ψ.
   • `two_term_isolate` (Sub-lemma B): combining `w` and `σ(w)` produces `w'` with strictly
     smaller `T`-support whose degree-`n` coefficient carries the factor `(t^n − t^m)`;
     and (multiplier-isolation) `(t^n − t^m)·(C (w n)·Tⁿ)` is integral over the 2-var base.
   • `monic_quotient_descent` (Sub-lemma C+D+E): from `(t^n − t^m)·(C z·Tⁿ)` integral over
     the 2-var base `(LaurentPolynomial R)[U;U⁻¹]`, pass to the finite-free monic quotient
     `(LaurentPolynomial R)[U]/(U^m − U^n − 1)` where the multiplier ↦ `−1`; strip the unit
     `−1`, descend (transitivity `RingHom.IsIntegral.trans`, 00GN) and project the monic
     relation onto the `Ū⁰`-summand (split finite extension) to land back over
     `LaurentPolynomial R = R[T;T⁻¹]`.
   ============================================================================ -/

/-- Two-variable base notation used by the v3 L3a sketch.  We adjoin a *second* Laurent
variable by working over `LaurentPolynomial R`, `LaurentPolynomial S` as the new
coefficient rings.  `Φ₂` is the coefficient base change one level up. -/
noncomputable abbrev Φ₁ : LaurentPolynomial R →+* LaurentPolynomial S :=
  AddMonoidAlgebra.mapRingHom ℤ (algebraMap R S)

open LaurentPolynomial in
/-- **(L3a-A) The degree-twist `σ : T ↦ t·T` preserves integrality.**

Work over the 2nd Laurent variable: the coefficient ring is `LaurentPolynomial S`
(call its variable `t`), and the outer Laurent ring is `(LaurentPolynomial S)[T;T⁻¹]`,
integral over `(LaurentPolynomial R)[T;T⁻¹]` along
`Ψ := AddMonoidAlgebra.mapRingHom ℤ Φ₁`.  There is a ring automorphism `σ` of
`(LaurentPolynomial S)[T;T⁻¹]` fixing the base `(LaurentPolynomial R)[T;T⁻¹]` (and the
coefficients), with `σ (C s · T^e) = C (t^e · s) · T^e` (substitution `T ↦ t·T`, where
`t = T (1) : LaurentPolynomial S` is a unit).  Such a base-fixing automorphism preserves
`Ψ`-integrality: apply `σ` to the monic relation, whose coefficients (in the image of `Ψ`)
are fixed by `σ`.

This sub-lemma is routine: existence of `σ` is the unit substitution `T ↦ t·T`
(`LaurentPolynomial`/`AddMonoidAlgebra` substitution), integral-stability is transport of
a monic relation along a base-fixing ring hom (`RingHom.IsIntegralElem` unfolding).  We
package only the consequence we need: `Ψ.IsIntegralElem x → Ψ.IsIntegralElem (σ x)`, where
`σ` is exhibited as `mulTwist`, the `T ↦ t·T` substitution. -/
theorem laurent_twist_preserves_integral
    (σ : (LaurentPolynomial S)[T;T⁻¹] ≃+* (LaurentPolynomial S)[T;T⁻¹])
    (hσbase : ∀ y : (LaurentPolynomial R)[T;T⁻¹],
        σ ((AddMonoidAlgebra.mapRingHom ℤ (Φ₁ (R := R) (S := S))) y)
          = (AddMonoidAlgebra.mapRingHom ℤ (Φ₁ (R := R) (S := S))) y)
    (x : (LaurentPolynomial S)[T;T⁻¹])
    (hx : (AddMonoidAlgebra.mapRingHom ℤ (Φ₁ (R := R) (S := S))).IsIntegralElem x) :
    (AddMonoidAlgebra.mapRingHom ℤ (Φ₁ (R := R) (S := S))).IsIntegralElem (σ x) := by
  -- Transport the monic relation for `x` along the ring (auto)morphism `σ`, which fixes
  -- every base coefficient `Ψ (cₖ)` by `hσbase`.  Unfold `RingHom.IsIntegralElem`
  -- (a monic `p` with `(p.map Ψ).eval₂ … x = 0`), apply `σ`, use `σ` ring-hom + `hσbase`.
  obtain ⟨p, hpmonic, hpeval⟩ := hx
  refine ⟨p, hpmonic, ?_⟩
  have hcomp : (σ.toRingHom.comp (AddMonoidAlgebra.mapRingHom ℤ (Φ₁ (R := R) (S := S))))
      = (AddMonoidAlgebra.mapRingHom ℤ (Φ₁ (R := R) (S := S))) := by
    refine RingHom.ext (fun y => ?_)
    simpa using hσbase y
  have := Polynomial.hom_eval₂ p (AddMonoidAlgebra.mapRingHom ℤ (Φ₁ (R := R) (S := S)))
    σ.toRingHom x
  rw [hpeval, map_zero, hcomp] at this
  exact this.symm

open LaurentPolynomial in
/-- **(L3a-C-D) Generic descent of integrality through a split ring-hom retraction.**

This is the irreducible "Sub-lemma D" of the v3 proof, stated abstractly so that the
finite-free monic-quotient extension `S[T;T⁻¹] ↪ S̃` of the descent step is just one
instance.  Setup: a base ring hom `f : A →+* B`, an extension `ι : B →+* B'` with a *ring
hom retraction* — actually only an `A`-linear (here `B`-linear, hence `A`-linear via `f`)
retraction is available, so we phrase it via an additive (in fact `A`-linear) projection
`π : B' → B` that is a left inverse of `ι` AND fixes the relevant powers.

Concretely we package exactly what the `Ū⁰`-summand projection of the free module supplies:
* `ι : B →+* B'` a ring hom (the split inclusion `B = (B)·Ū⁰ ↪ B' = ⊕_j B·Ū^j`);
* `e : A →+* A'`, `f' : A' →+* B'` the lifted base maps, with `f'.comp e = ι.comp f`
  (the base square commutes);
* `π : B' →+ B` additive, `A`-linear over `f`/`e` in the sense `∀ a y, π (f' (e a) * y)`… —
  we only need: `π (ι b) = b` for all `b` (retraction), `π` is additive, and `π` carries the
  base coefficients to the `Ū⁰`-coordinates `c₀ : A` with `f c₀ = π (f' c̃)`.
Conclusion: if `ι x` is integral over `A'` along `f'` AND the monic relation's coefficients'
`Ū⁰`-coordinates pull back through `f`, then `x` is integral over `A` along `f`.

We state the *consumable* form used by `monic_quotient_descent`: the hypotheses bundle the
projected monic relation directly.  This keeps the lemma honest (no hidden freeness) while
isolating the genuine linear-algebra content (`Basis.repr` of the free `B`-module `B'`). -/
theorem isIntegralElem_of_split_finite_free
    {A B A' B' : Type*} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (f : A →+* B) (f' : A' →+* B') (ι : B →+* B')
    -- `B'` is module-finite free over `B` with `ι` the inclusion of the `Ū⁰`-summand, and a
    -- `B`-linear coordinate projection `π : B' →+ B` (the `Ū⁰`-coordinate).  We avoid the
    -- `Module B B'` typeclass by stating exactly the two algebraic facts the descent needs:
    -- `π` retracts `ι` (`hπι`), and `π` is right-`ι B`-linear (`hπmul`: pulls an `ι b` factor
    -- out of `π`).  Together these are the content of "project onto the `Ū⁰`-summand".
    (π : B' →+ B) (hπι : ∀ b : B, π (ι b) = b)
    (hπmul : ∀ (cc : B') (b : B), π (cc * ι b) = π cc * b)
    -- the `Ū⁰`-coordinate of every base coefficient `ct ∈ A'` lands in the image of `f` after
    -- pushing forward; precisely, for every `ct : A'` there is `c₀ : A` with `f c₀ = π (f' ct)`.
    (hcoeff : ∀ ct : A', ∃ c₀ : A, f c₀ = π (f' ct))
    (x : B) (hint : f'.IsIntegralElem (ι x)) :
    f.IsIntegralElem x := by
  classical
  obtain ⟨p, hpmonic, hpeval⟩ := hint
  set N := p.natDegree with hN
  -- choice of `A`-coefficients pulling back each `π (f' (p.coeff i))`
  set cf : ℕ → A := fun i => if i = N then 1 else Classical.choose (hcoeff (p.coeff i)) with hcf
  -- key: `f (cf i) = π (f' (p.coeff i))` for every `i ≤ N`
  have hcfspec : ∀ i, i ≤ N → f (cf i) = π (f' (p.coeff i)) := by
    intro i hi
    rcases eq_or_ne i N with h | h
    · have hcoeffN : p.coeff i = 1 := by
        rw [h, hN, hpmonic.coeff_natDegree]
      simp only [hcf, ite_eq_left h, map_one, hcoeffN]
      have h1 : (1 : B') = ι 1 := (ι.map_one).symm
      rw [h1, hπι]
    · simp only [hcf, ite_eq_right h]
      exact Classical.choose_spec (hcoeff (p.coeff i))
  -- coefficient computation for the witness polynomial
  have hcoeffq : ∀ k,
      (∑ i ∈ Finset.range (N + 1),
        Polynomial.C (cf i) * Polynomial.X ^ i).coeff k
        = if k ≤ N then cf k else 0 := by
    intro k
    rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq (Finset.range (N + 1)) k]
    simp [Finset.mem_range]
  refine ⟨∑ i ∈ Finset.range (N + 1),
      Polynomial.C (cf i) * Polynomial.X ^ i, ?_, ?_⟩
  · -- the witness is monic of degree `N`
    apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one N
    · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro n hn
      rw [hcoeffq n]
      simp [Nat.not_le.mpr hn]
    · rw [hcoeffq N]
      simp only [le_refl, ite_true, hcf, ite_eq_left rfl]
  · -- the witness evaluates to zero at `x`
    rw [Polynomial.eval₂_finsetSum]
    simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow,
      Polynomial.eval₂_X]
    -- expand the integral relation as a finite sum
    rw [Polynomial.eval₂_eq_sum_range, ← hN] at hpeval
    -- apply `π` to the relation
    have hπ0 : π (∑ i ∈ Finset.range (N + 1), f' (p.coeff i) * ι x ^ i) = π 0 := by
      rw [hpeval]
    rw [map_zero, map_sum] at hπ0
    -- rewrite each term using `(ι x)^i = ι (x^i)` and `hπmul`
    have hterm : ∀ i ∈ Finset.range (N + 1),
        π (f' (p.coeff i) * ι x ^ i) = f (cf i) * x ^ i := by
      intro i hi
      rw [Finset.mem_range, Nat.lt_succ_iff] at hi
      rw [← map_pow, hπmul, hcfspec i hi]
    rw [Finset.sum_congr rfl hterm] at hπ0
    rw [hπ0]

/-- `Φ₁` sends the constant `C r` to `C (algebraMap R S r)`. -/
theorem Phi1_C (r : R) :
    (Φ₁ (R := R) (S := S)) (LaurentPolynomial.C r) = LaurentPolynomial.C (algebraMap R S r) := by
  ext k
  rw [AddMonoidAlgebra.coeff_mapRingHom]
  simp only [LaurentPolynomial.C_apply]; split <;> simp

/-- `Φ₁` fixes the monomials `T k`. -/
theorem Phi1_T (k : ℤ) :
    (Φ₁ (R := R) (S := S)) (LaurentPolynomial.T k) = LaurentPolynomial.T k := by
  ext k'
  rw [AddMonoidAlgebra.coeff_mapRingHom]
  simp only [LaurentPolynomial.T_apply]; split <;> simp

/-- Integrality along a composite `g ∘ h` implies integrality along `g`. -/
theorem isIntegralElem_precomp {A C B : Type*} [CommRing A] [CommRing C] [CommRing B]
    (g : C →+* B) (h : A →+* C) (y : B) (hy : (g.comp h).IsIntegralElem y) :
    g.IsIntegralElem y := by
  obtain ⟨p, hp, he⟩ := hy
  refine ⟨p.map h, hp.map h, ?_⟩
  rw [Polynomial.eval₂_map] at *
  convert he using 2

/-- If a unit `ub` satisfies the Selmer relation `ub ^ D = ub + 1` with `D = max d 2` and
`1 ≤ d`, then `ub ^ d - 1` is a unit. -/
theorem selmer_pow_sub_one_isUnit {B : Type*} [CommRing B] (ub : B) (d D : ℕ)
    (hd1 : 1 ≤ d) (hD : D = max d 2) (hsel : ub ^ D = ub + 1) (hub : IsUnit ub) :
    IsUnit (ub ^ d - 1) := by
  rcases eq_or_lt_of_le hd1 with hd | hd
  · have hd' : d = 1 := hd.symm
    have hD' : D = 2 := by rw [hD, hd']; rfl
    subst hd'
    rw [pow_one]
    have hmul : (ub - 1) * ub = 1 := by
      have h2 : (ub - 1) * ub = ub ^ 2 - ub := by ring
      rw [h2, ← hD', hsel]; ring
    exact ⟨⟨ub - 1, ub, hmul, by rw [mul_comm]; exact hmul⟩, rfl⟩
  · have hD' : D = d := by rw [hD]; omega
    rwa [← hD', hsel, add_sub_cancel_right]

/-- If `ub ^ |m - n| - 1` is a unit, then so is the difference `ub ^ n - ub ^ m` of the two
corresponding powers of the unit `ub`. -/
theorem mult_zpow_isUnit {B : Type*} [CommRing B] (ubU : Bˣ) (n m : ℤ)
    (hu : IsUnit ((ubU : B) ^ (m - n).natAbs - 1)) :
    IsUnit ((↑(ubU ^ n) : B) - ↑(ubU ^ m)) := by
  set d := (m - n).natAbs with hd
  have hfac : (↑(ubU ^ n) : B) - ↑(ubU ^ m) = ↑(ubU ^ m) * (↑(ubU ^ (n - m)) - 1) := by
    rw [mul_sub, mul_one, ← Units.val_mul, ← zpow_add]; congr 2; congr 1; ring
  rw [hfac]
  apply IsUnit.mul (Units.isUnit _)
  have hcases : n - m = (d : ℤ) ∨ n - m = -(d : ℤ) := by omega
  have hpow : (↑(ubU ^ (d : ℤ)) : B) = (ubU : B) ^ d := by rw [zpow_natCast]; rfl
  rcases hcases with h | h
  · rwa [h, hpow]
  · rw [h]
    have heq : (↑(ubU ^ (-(d:ℤ))) : B) - 1 = ↑(ubU ^ (d:ℤ))⁻¹ * (1 - ↑(ubU ^ (d:ℤ))) := by
      rw [mul_sub, mul_one, ← Units.val_mul,
        show (ubU ^ (d:ℤ))⁻¹ * ubU ^ (d:ℤ) = 1 by rw [inv_mul_cancel], zpow_neg]
      simp
    rw [heq, hpow, show (1 : B) - (ubU:B)^d = -((ubU:B)^d - 1) by ring]
    exact (Units.isUnit _).mul hu.neg

/-- The root of the Selmer polynomial `X ^ D - X - 1` satisfies `root ^ D = root + 1`. -/
theorem selmer_root_rel {K : Type*} [CommRing K] (D : ℕ)
    (g : Polynomial K) (hg : g = Polynomial.X ^ D - Polynomial.X - 1) :
    (AdjoinRoot.root g) ^ D = AdjoinRoot.root g + 1 := by
  have e1 : (AdjoinRoot.root g) ^ D - AdjoinRoot.root g - 1
      = AdjoinRoot.mk g (Polynomial.X ^ D - Polynomial.X - 1) := by
    rw [← AdjoinRoot.mk_X (f := g), map_sub, map_sub, map_pow, map_one]
  have h0 : (AdjoinRoot.root g) ^ D - AdjoinRoot.root g - 1 = 0 := by
    rw [e1, ← hg, AdjoinRoot.mk_self]
  linear_combination h0

/-- For `D ≥ 1` the root of the Selmer polynomial `X ^ D - X - 1` is a unit, with inverse
`root ^ (D - 1) - 1`. -/
theorem selmer_root_unit {K : Type*} [CommRing K] (D : ℕ) (hD : 1 ≤ D)
    (g : Polynomial K) (hg : g = Polynomial.X ^ D - Polynomial.X - 1) :
    IsUnit (AdjoinRoot.root g) := by
  set ub := AdjoinRoot.root g with hub
  have hrel : ub ^ D = ub + 1 := selmer_root_rel D g hg
  have hinv : ub * (ub ^ (D - 1) - 1) = 1 := by
    have h2 : ub * (ub ^ (D-1) - 1) = ub ^ D - ub := by
      rw [mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel hD]
    rw [h2]; have h3 : ub ^ D - ub = ub^D - ub - 1 + 1 := by ring
    rw [h3, show ub^D - ub - 1 = 0 from by rw [hrel]; ring, zero_add]
  exact ⟨⟨ub, ub ^ (D-1) - 1, hinv, by rw [mul_comm]; exact hinv⟩, rfl⟩

/-- Transport of a bundle of maps along ring isomorphisms of its two carriers: the integrality
and compatibility data are carried over from `(A'₀, B'₀)` to `(A', B')`. -/
theorem bundle_transport
    {MR MS : Type*} [CommRing MR] [CommRing MS] (Ψ : MR →+* MS)
    {A'₀ : Type*} {B'₀ : Type*} [CommRing A'₀] [CommRing B'₀]
    {A' : Type*} {B' : Type*} [CommRing A'] [CommRing B']
    (eqA : A'₀ ≃+* A') (eqB : B'₀ ≃+* B')
    (e₀ : MR →+* A'₀) (f'₀ : A'₀ →+* B'₀) (ι₀ : MS →+* B'₀) (π₀ : B'₀ →+ MS)
    (tgtV : MS)
    (h1 : f'₀.comp e₀ = ι₀.comp Ψ)
    (h2 : Function.Injective ι₀)
    (h3 : ∀ b : MS, π₀ (ι₀ b) = b)
    (h4 : ∀ (cc : B'₀) (b : MS), π₀ (cc * ι₀ b) = π₀ cc * b)
    (h5 : ∀ ct : A'₀, ∃ c₀ : MR, Ψ c₀ = π₀ (f'₀ ct))
    (h6 : f'₀.IsIntegralElem (ι₀ tgtV)) :
    ∃ (e : MR →+* A') (f' : A' →+* B') (ι : MS →+* B') (π : B' →+ MS),
      f'.comp e = ι.comp Ψ
        ∧ Function.Injective ι
        ∧ (∀ b : MS, π (ι b) = b)
        ∧ (∀ (cc : B') (b : MS), π (cc * ι b) = π cc * b)
        ∧ (∀ ct : A', ∃ c₀ : MR, Ψ c₀ = π (f' ct))
        ∧ f'.IsIntegralElem (ι (tgtV)) := by
  have hsymm : ∀ z : B'₀, eqB.symm.toAddMonoidHom (eqB z) = z := fun z => eqB.symm_apply_apply z
  have hsymmA : ∀ z : B', eqB.symm.toAddMonoidHom z = eqB.symm z := fun _ => rfl
  refine ⟨eqA.toRingHom.comp e₀,
    (eqB.toRingHom.comp f'₀).comp eqA.symm.toRingHom,
    eqB.toRingHom.comp ι₀,
    π₀.comp eqB.symm.toAddMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext x
    have : f'₀ (e₀ x) = ι₀ (Ψ x) := by rw [← RingHom.comp_apply, h1]; rfl
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.symm_apply_apply, this]
  · intro a b hab
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at hab
    exact h2 (eqB.injective hab)
  · intro b
    show π₀ (eqB.symm.toAddMonoidHom ((eqB.toRingHom.comp ι₀) b)) = b
    rw [show (eqB.toRingHom.comp ι₀) b = eqB (ι₀ b) from rfl, hsymm]
    exact h3 b
  · intro cc b
    show π₀ (eqB.symm.toAddMonoidHom (cc * (eqB.toRingHom.comp ι₀) b))
      = π₀ (eqB.symm.toAddMonoidHom cc) * b
    rw [show (eqB.toRingHom.comp ι₀) b = eqB (ι₀ b) from rfl, hsymmA, hsymmA]
    rw [map_mul, RingEquiv.symm_apply_apply]
    exact h4 (eqB.symm cc) b
  · intro ct
    obtain ⟨c₀, hc₀⟩ := h5 (eqA.symm ct)
    refine ⟨c₀, ?_⟩
    show Ψ c₀ = π₀ (eqB.symm.toAddMonoidHom (((eqB.toRingHom.comp f'₀).comp eqA.symm.toRingHom)
        ct))
    rw [show ((eqB.toRingHom.comp f'₀).comp eqA.symm.toRingHom) ct = eqB (f'₀ (eqA.symm ct)) from
        rfl,
      hsymm]
    exact hc₀
  · have h6' := h6.map eqB.toRingHom
    obtain ⟨p, hp, he⟩ := h6'
    refine ⟨p.map eqA.toRingHom, hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : ((eqB.toRingHom.comp f'₀).comp eqA.symm.toRingHom).comp eqA.toRingHom
          = eqB.toRingHom.comp f'₀ := by
      ext y; simp [RingEquiv.symm_apply_apply]
    rw [hcomp]
    exact he

/-- `Finsupp.mapRange.addMonoidHom` acts on a single monomial by applying the map to its
coefficient. -/
theorem mapAddHom_single {M N : Type*} [AddCommMonoid M] [AddCommMonoid N] (φ : M →+ N) (j : ℤ) (c
    : M) :
    (Finsupp.mapRange.addMonoidHom φ) (Finsupp.single j c) = Finsupp.single j (φ c) := by
  rw [Finsupp.mapRange.addMonoidHom_apply]
  exact Finsupp.mapRange_single

/-- The coefficient function of `AddMonoidAlgebra.single j c` is carried by
`Finsupp.mapRange.addMonoidHom φ` to that of `AddMonoidAlgebra.single j (φ c)`. -/
theorem mapAddHom_AMsingle {B M : Type*} [CommRing B] [CommRing M] (φ : B →+ M) (j : ℤ) (c : B) :
    (Finsupp.mapRange.addMonoidHom φ) (AddMonoidAlgebra.single j c).coeff
      = (AddMonoidAlgebra.single j (φ c)).coeff := by
  rw [AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_single,
    Finsupp.mapRange.addMonoidHom_apply]
  exact Finsupp.mapRange_single

/-- The Laurent-polynomial constant `C x` is the monomial `single 0 x`. -/
theorem LP_C_eq_single {K : Type*} [CommRing K] (x : K) :
    (LaurentPolynomial.C x : LaurentPolynomial K) = AddMonoidAlgebra.single 0 x := by
  ext k
  rw [LaurentPolynomial.C_apply]
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases hk : k = 0
  · subst hk; simp
  · rw [ite_eq_right hk, ite_eq_right (Ne.symm hk)]

/-- The tail `-X - 1` of the Selmer polynomial has degree less than `D ≥ 2`. -/
private theorem selmer_tail_degree_lt {K : Type*} [CommRing K] {D : ℕ} (hD : 2 ≤ D) :
    (-Polynomial.X - 1 : Polynomial K).degree < D := by
  refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt ?_ ?_)
  · rw [Polynomial.degree_neg]
    exact lt_of_le_of_lt Polynomial.degree_X_le (by exact_mod_cast hD)
  · exact lt_of_le_of_lt Polynomial.degree_one_le (by exact_mod_cast hD.trans_lt' two_pos)

/-- The coefficient of the image of `x` under `AddMonoidAlgebra.map φ` is the image of the
coefficient. -/
private theorem coeff_map_apply {A B : Type*} [Semiring A] [Semiring B] (φ : A →+ B)
    (x : AddMonoidAlgebra A ℤ) (k : ℤ) :
    (AddMonoidAlgebra.map φ x).coeff k = φ (x.coeff k) := by
  rw [AddMonoidAlgebra.coeff_map, Finsupp.mapRange_apply]

open LaurentPolynomial in
-- needed: a `rw` inside `mqod_inner` only matches its pattern when isDefEq ignores
-- transparency (the two sides differ by an unfolded semireducible definition).
set_option backward.isDefEq.respectTransparency false in
/-- The inner step of the quotient-of-differences argument: from integrality of
`C (T n - T m) * (C (C z) * T n)` one extracts the transport bundle used to conclude. -/
theorem mqod_inner
    (z : S) (n m : ℤ) (hnm : n ≠ m)
    (hint : (AddMonoidAlgebra.mapRingHom ℤ (Φ₁ (R := R) (S := S))).IsIntegralElem
        (C ((LaurentPolynomial.T n - LaurentPolynomial.T m : LaurentPolynomial S)) *
          (C (LaurentPolynomial.C z) * T n))) :
    ∃ (A'₀ B'₀ : Type (max u_1 u_2)) (_ : CommRing A'₀) (_ : CommRing B'₀)
      (e : (LaurentPolynomial R)[T;T⁻¹] →+* A'₀) (f' : A'₀ →+* B'₀)
      (ι : (LaurentPolynomial S)[T;T⁻¹] →+* B'₀)
      (π : B'₀ →+ (LaurentPolynomial S)[T;T⁻¹]),
      f'.comp e = ι.comp (AddMonoidAlgebra.mapRingHom ℤ (Φ₁ (R := R) (S := S)))
        ∧ Function.Injective ι
        ∧ (∀ b : (LaurentPolynomial S)[T;T⁻¹], π (ι b) = b)
        ∧ (∀ (cc : B'₀) (b : (LaurentPolynomial S)[T;T⁻¹]), π (cc * ι b) = π cc * b)
        ∧ (∀ ct : A'₀, ∃ c₀ : (LaurentPolynomial R)[T;T⁻¹],
            (AddMonoidAlgebra.mapRingHom ℤ (Φ₁ (R := R) (S := S))) c₀ = π (f' ct))
        ∧ f'.IsIntegralElem (ι (C (LaurentPolynomial.C z) * T n)) := by
  classical
  have hdpos : 1 ≤ (m - n).natAbs := by
    rw [Nat.one_le_iff_ne_zero, Int.natAbs_ne_zero, sub_ne_zero]; exact fun h => hnm h.symm
  set d : ℕ := (m - n).natAbs with hd
  set D : ℕ := max d 2 with hDdef
  have hD2 : 2 ≤ D := le_max_right _ _
  have hD1 : 1 ≤ D := le_trans (by norm_num) hD2
  set gR : Polynomial (LaurentPolynomial R) := Polynomial.X ^ D - Polynomial.X - 1 with hgR
  have hgRmonic : gR.Monic := by
    rw [hgR, show (Polynomial.X ^ D - Polynomial.X - 1 : Polynomial (LaurentPolynomial R))
          = Polynomial.X ^ D + (- Polynomial.X - 1) from by ring]
    exact Polynomial.monic_X_pow_add (selmer_tail_degree_lt hD2)
  have hgSeq : gR.map (Φ₁ (R := R) (S := S)) = Polynomial.X ^ D - Polynomial.X - 1 := by
    rw [hgR]; simp [Polynomial.map_sub, Polynomial.map_pow]
  set gS : Polynomial (LaurentPolynomial S) := gR.map (Φ₁ (R := R) (S := S)) with hgS
  have hgSmonic : gS.Monic := hgRmonic.map _
  have hgRdef : gR = Polynomial.X ^ D - Polynomial.X - 1 := hgR
  have hgSdef' : gS = Polynomial.X ^ D - Polynomial.X - 1 := hgSeq
  -- Rings
  set Atil := AdjoinRoot gR with hAtil
  set Btil := AdjoinRoot gS with hBtil
  -- root units
  have hurUnit : IsUnit (AdjoinRoot.root gR) := selmer_root_unit D hD1 gR hgRdef
  have hubUnit : IsUnit (AdjoinRoot.root gS) := selmer_root_unit D hD1 gS hgSdef'
  set urU : Atilˣ := hurUnit.unit with hurU
  set ubU : Btilˣ := hubUnit.unit with hubU
  have hurUval : (urU : Atil) = AdjoinRoot.root gR := hurUnit.unit_spec
  have hubUval : (ubU : Btil) = AdjoinRoot.root gS := hubUnit.unit_spec
  -- inner homs
  set ein : LaurentPolynomial R →+* Atil :=
    LaurentPolynomial.eval₂ ((AdjoinRoot.of gR).comp LaurentPolynomial.C) urU with hein
  set qin : LaurentPolynomial S →+* Btil :=
    LaurentPolynomial.eval₂ ((AdjoinRoot.of gS).comp LaurentPolynomial.C) ubU with hqin
  -- ftil
  have hwd : Polynomial.eval₂ ((AdjoinRoot.of gS).comp (Φ₁ (R := R) (S := S)))
      (AdjoinRoot.root gS) gR = 0 := by
    rw [← Polynomial.eval₂_map, ← hgS]; exact AdjoinRoot.eval₂_root gS
  set ftil : Atil →+* Btil :=
    AdjoinRoot.lift ((AdjoinRoot.of gS).comp (Φ₁ (R := R) (S := S))) (AdjoinRoot.root gS) hwd with
        hftil
  have hftilof : ftil.comp (AdjoinRoot.of gR) = (AdjoinRoot.of gS).comp (Φ₁ (R := R) (S := S)) :=
    AdjoinRoot.lift_comp_of hwd
  have hftilroot : ftil (AdjoinRoot.root gR) = AdjoinRoot.root gS := AdjoinRoot.lift_root hwd
  -- outer homs
  set e₀ : (LaurentPolynomial R)[T;T⁻¹] →+* AddMonoidAlgebra Atil ℤ :=
    AddMonoidAlgebra.mapRingHom ℤ (AdjoinRoot.of gR) with he₀
  set f'₀ : AddMonoidAlgebra Atil ℤ →+* AddMonoidAlgebra Btil ℤ :=
    AddMonoidAlgebra.mapRingHom ℤ ftil with hf'₀
  set ι₀ : (LaurentPolynomial S)[T;T⁻¹] →+* AddMonoidAlgebra Btil ℤ :=
    AddMonoidAlgebra.mapRingHom ℤ (AdjoinRoot.of gS) with hι₀
  -- projection: coord₀ then lift
  set coordR : Atil →ₗ[LaurentPolynomial R] LaurentPolynomial R :=
    (Polynomial.lcoeff (LaurentPolynomial R) 0).comp (AdjoinRoot.modByMonicHom hgRmonic) with
        hcoordR
  set coordS : Btil →ₗ[LaurentPolynomial S] LaurentPolynomial S :=
    (Polynomial.lcoeff (LaurentPolynomial S) 0).comp (AdjoinRoot.modByMonicHom hgSmonic) with
        hcoordS
  set π₀ : AddMonoidAlgebra Btil ℤ →+ (LaurentPolynomial S)[T;T⁻¹] :=
    AddMonoidHom.mk' (AddMonoidAlgebra.map coordS.toAddMonoidHom)
      (AddMonoidAlgebra.map_add _) with hπ₀
  -- coordS retraction and linearity (inner)
  have hcoordS_of : ∀ c : LaurentPolynomial S, coordS (AdjoinRoot.of gS c) = c := by
    intro c
    simp only [hcoordS, LinearMap.comp_apply]
    rw [show (AdjoinRoot.of gS c) = AdjoinRoot.mk gS (Polynomial.C c) from rfl,
      AdjoinRoot.modByMonicHom_mk]
    rcases subsingleton_or_nontrivial (LaurentPolynomial S) with hsub | hnt
    · exact Subsingleton.elim _ _
    · have hself : Polynomial.C c %ₘ gS = Polynomial.C c := by
        rw [Polynomial.modByMonic_eq_self_iff hgSmonic]
        refine lt_of_le_of_lt Polynomial.degree_C_le ?_
        show (0 : WithBot ℕ) < gS.degree
        rw [hgSdef', show (Polynomial.X ^ D - Polynomial.X - 1 : Polynomial (LaurentPolynomial S))
              = Polynomial.X ^ D + (- Polynomial.X - 1) from by ring]
        have hlt : (- Polynomial.X - 1 : Polynomial (LaurentPolynomial S)).degree
            < (Polynomial.X ^ D : Polynomial (LaurentPolynomial S)).degree := by
          rw [Polynomial.degree_X_pow]; exact selmer_tail_degree_lt hD2
        rw [Polynomial.degree_add_eq_left_of_degree_lt hlt, Polynomial.degree_X_pow]
        exact_mod_cast lt_of_lt_of_le (by norm_num : (0:ℕ) < 2) hD2
      rw [hself]; simp [Polynomial.lcoeff_apply]
  have hcoordS_lin : ∀ (x : Btil) (c : LaurentPolynomial S),
      coordS (x * AdjoinRoot.of gS c) = coordS x * c := by
    intro x c
    have hsmul : x * AdjoinRoot.of gS c = c • x := by
      rw [show AdjoinRoot.of gS c = algebraMap (LaurentPolynomial S) Btil c from rfl,
        Algebra.smul_def]; ring
    rw [hsmul, map_smul]; simp [smul_eq_mul, mul_comm]
  -- h1: base square
  have h1 : f'₀.comp e₀ = ι₀.comp (AddMonoidAlgebra.mapRingHom ℤ (Φ₁ (R := R) (S := S))) := by
    rw [hf'₀, he₀, hι₀, ← AddMonoidAlgebra.mapRingHom_comp,
      ← AddMonoidAlgebra.mapRingHom_comp, hftilof]
  -- h2: ι₀ injective
  have hofSinj : Function.Injective (AdjoinRoot.of gS) := by
    have : Function.LeftInverse coordS (AdjoinRoot.of gS) := hcoordS_of
    exact this.injective
  have h2 : Function.Injective ι₀ := by
    rw [hι₀]
    intro a b hab
    apply AddMonoidAlgebra.ext
    apply Finsupp.ext
    intro k
    have := congrArg (fun w => w.coeff k) hab
    simp only [AddMonoidAlgebra.coeff_mapRingHom] at this
    exact hofSinj this
  -- π₀ coefficient
  have hπ₀coeff : ∀ (x : AddMonoidAlgebra Btil ℤ) (k : ℤ), (π₀ x).coeff k = coordS (x.coeff k) := by
    intro x k
    exact coeff_map_apply coordS.toAddMonoidHom x k
  have hπ₀single : ∀ (j : ℤ) (y : Btil),
      π₀ (AddMonoidAlgebra.single j y) = AddMonoidAlgebra.single j (coordS y) := by
    intro j y
    ext k
    rw [hπ₀coeff]
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases hk : k = j
    · subst hk; simp
    · rw [ite_eq_right (Ne.symm hk), ite_eq_right (Ne.symm hk), map_zero]
  -- ι₀, f'₀ single
  have hι₀single : ∀ (j : ℤ) (c : LaurentPolynomial S),
      ι₀ (AddMonoidAlgebra.single j c) = AddMonoidAlgebra.single j (AdjoinRoot.of gS c) := by
    intro j c; rw [hι₀]; exact AddMonoidAlgebra.mapRingHom_single _ j c
  -- h3: retraction
  have h3 : ∀ b : (LaurentPolynomial S)[T;T⁻¹], π₀ (ι₀ b) = b := by
    intro b
    ext k
    rw [hπ₀coeff]
    have hk : (ι₀ b).coeff k = AdjoinRoot.of gS (b.coeff k) := by
      rw [hι₀, AddMonoidAlgebra.coeff_mapRingHom]
    rw [hk, hcoordS_of]
  -- h4: right linearity
  have h4 : ∀ (cc : AddMonoidAlgebra Btil ℤ) (b : (LaurentPolynomial S)[T;T⁻¹]),
      π₀ (cc * ι₀ b) = π₀ cc * b := by
    intro cc b
    induction cc using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add p q hp hq => rw [add_mul, map_add, map_add, hp, hq, add_mul]
    | single i x =>
      induction b using AddMonoidAlgebra.induction_linear with
      | zero => simp
      | add p q hp hq => rw [map_add, mul_add, map_add, mul_add, hp, hq]
      | single j c =>
        rw [hι₀single, AddMonoidAlgebra.single_mul_single, hπ₀single, hπ₀single,
          AddMonoidAlgebra.single_mul_single]
        congr 1
        exact hcoordS_lin x c
  -- coordR/coordS intertwining via ftil
  have hcoordRS : ∀ (y : Atil), Φ₁ (coordR y) = coordS (ftil y) := by
    intro y
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective y
    have hftilmk : ftil (AdjoinRoot.mk gR p) = AdjoinRoot.mk gS (p.map (Φ₁ (R := R) (S := S))) := by
      rw [hftil, AdjoinRoot.lift_mk, ← AdjoinRoot.aeval_eq (p.map (Φ₁ (R := R) (S := S))),
        Polynomial.aeval_def, Polynomial.eval₂_map]
      rfl
    rw [hcoordR, hcoordS, LinearMap.comp_apply, LinearMap.comp_apply, hftilmk,
      AdjoinRoot.modByMonicHom_mk, AdjoinRoot.modByMonicHom_mk, hgS,
      ← Polynomial.map_modByMonic _ hgRmonic]
    simp [Polynomial.lcoeff_apply, Polynomial.coeff_map]
  -- h5: coefficient pullback
  set πA : AddMonoidAlgebra Atil ℤ →+ (LaurentPolynomial R)[T;T⁻¹] :=
    AddMonoidHom.mk' (AddMonoidAlgebra.map coordR.toAddMonoidHom)
      (AddMonoidAlgebra.map_add _) with hπA
  have hπAcoeff : ∀ (x : AddMonoidAlgebra Atil ℤ) (k : ℤ),
      (πA x).coeff k = coordR (x.coeff k) := by
    intro x k
    exact coeff_map_apply coordR.toAddMonoidHom x k
  have h5 : ∀ ct : AddMonoidAlgebra Atil ℤ, ∃ c₀ : (LaurentPolynomial R)[T;T⁻¹],
      (AddMonoidAlgebra.mapRingHom ℤ (Φ₁ (R := R) (S := S))) c₀ = π₀ (f'₀ ct) := by
    intro ct
    refine ⟨πA ct, ?_⟩
    apply AddMonoidAlgebra.ext
    apply Finsupp.ext
    intro k
    rw [AddMonoidAlgebra.coeff_mapRingHom, hπ₀coeff, hπAcoeff]
    have hf'k : (f'₀ ct).coeff k = ftil (ct.coeff k) := by
      rw [hf'₀, AddMonoidAlgebra.coeff_mapRingHom]
    rw [hf'k]
    exact hcoordRS (ct.coeff k)
  -- conjunct 6: integral transport
  set q : (LaurentPolynomial S)[T;T⁻¹] →+* AddMonoidAlgebra Btil ℤ :=
    AddMonoidAlgebra.mapRingHom ℤ qin with hq
  set e' : (LaurentPolynomial R)[T;T⁻¹] →+* AddMonoidAlgebra Atil ℤ :=
    AddMonoidAlgebra.mapRingHom ℤ ein with he'
  -- ftil maps urU-zpow to ubU-zpow
  have hrtRpow : ∀ k : ℤ, (↑(ubU ^ k) : Btil) = ftil (↑(urU ^ k)) := by
    intro k
    have hmap : Units.map (ftil : Atil →* Btil) urU = ubU := by
      apply Units.ext; rw [Units.coe_map]; change ftil (urU : Atil) = (ubU : Btil)
      rw [hurUval, hubUval, hftilroot]
    rw [← hmap, ← map_zpow, Units.coe_map]; rfl
  -- inner square
  have hsq_inner : qin.comp (Φ₁ (R := R) (S := S)) = ftil.comp ein := by
    rw [hqin, hein]
    apply AddMonoidAlgebra.ringHom_ext
    · intro r
      show (LaurentPolynomial.eval₂ ((AdjoinRoot.of gS).comp LaurentPolynomial.C) ubU)
          ((Φ₁ (R := R) (S := S)) (LaurentPolynomial.C r)) = _
      rw [Phi1_C, LaurentPolynomial.eval₂_C]
      show _ = ftil ((LaurentPolynomial.eval₂ ((AdjoinRoot.of gR).comp LaurentPolynomial.C) urU)
          (LaurentPolynomial.C r))
      rw [LaurentPolynomial.eval₂_C]
      have hh := congrArg (fun w => w (LaurentPolynomial.C r)) hftilof
      simp only [RingHom.comp_apply] at hh ⊢
      rw [hh, RingHom.comp_apply, Phi1_C]
    · intro j
      show (LaurentPolynomial.eval₂ ((AdjoinRoot.of gS).comp LaurentPolynomial.C) ubU)
          ((Φ₁ (R := R) (S := S)) (LaurentPolynomial.T j)) = _
      rw [Phi1_T, LaurentPolynomial.eval₂_T]
      show _ = ftil ((LaurentPolynomial.eval₂ ((AdjoinRoot.of gR).comp LaurentPolynomial.C) urU)
          (LaurentPolynomial.T j))
      rw [LaurentPolynomial.eval₂_T]
      exact hrtRpow j
  have hsq : q.comp (AddMonoidAlgebra.mapRingHom ℤ (Φ₁ (R := R) (S := S))) = f'₀.comp e' := by
    rw [hq, he', hf'₀, ← AddMonoidAlgebra.mapRingHom_comp,
      ← AddMonoidAlgebra.mapRingHom_comp, hsq_inner]
  -- q and ι₀ agree on the target (target has no inner t in its coefficient)
  set target : (LaurentPolynomial S)[T;T⁻¹] := C (LaurentPolynomial.C z) * T n with htarget
  have htgtsingle : target = AddMonoidAlgebra.single n (LaurentPolynomial.C z) := by
    rw [htarget, ← LaurentPolynomial.single_eq_C_mul_T]
  have hqtgt : q target = AddMonoidAlgebra.single n (AdjoinRoot.of gS (LaurentPolynomial.C z)) := by
    rw [htgtsingle, hq, AddMonoidAlgebra.mapRingHom_single]
    congr 1; rw [hqin, LaurentPolynomial.eval₂_C]; rfl
  have hιtgt :
      ι₀ target = AddMonoidAlgebra.single n (AdjoinRoot.of gS (LaurentPolynomial.C z)) := by
    rw [htgtsingle, hι₀, AddMonoidAlgebra.mapRingHom_single]
  have htgt : q target = ι₀ target := by rw [hqtgt, hιtgt]
  -- multiplier
  set mult : (LaurentPolynomial S)[T;T⁻¹] :=
    C (LaurentPolynomial.T n - LaurentPolynomial.T m : LaurentPolynomial S) with hmult
  have hqmult : q mult = AddMonoidAlgebra.single 0 ((↑(ubU ^ n) : Btil) - ↑(ubU ^ m)) := by
    rw [hmult, hq]
    rw [LP_C_eq_single, AddMonoidAlgebra.mapRingHom_single]
    congr 1
    rw [hqin, map_sub, LaurentPolynomial.eval₂_T, LaurentPolynomial.eval₂_T]
  -- unit values over Atil and Btil
  have hubsel : (ubU : Btil) ^ D = (ubU : Btil) + 1 := by
    rw [hubUval]; exact selmer_root_rel D gS hgSdef'
  have hursel : (urU : Atil) ^ D = (urU : Atil) + 1 := by
    rw [hurUval]; exact selmer_root_rel D gR hgRdef
  have hpowunitB : IsUnit ((ubU : Btil) ^ d - 1) :=
    selmer_pow_sub_one_isUnit (ubU : Btil) d D hdpos hDdef hubsel (Units.isUnit ubU)
  have hpowunitA : IsUnit ((urU : Atil) ^ d - 1) :=
    selmer_pow_sub_one_isUnit (urU : Atil) d D hdpos hDdef hursel (Units.isUnit urU)
  set UmulB : Btilˣ := (mult_zpow_isUnit ubU n m hpowunitB).unit with hUmulB
  set UmulA : Atilˣ := (mult_zpow_isUnit urU n m hpowunitA).unit with hUmulA
  have hUmulBval : (UmulB : Btil) = (↑(ubU ^ n) : Btil) - ↑(ubU ^ m) := IsUnit.unit_spec _
  have hUmulAval : (UmulA : Atil) = (↑(urU ^ n) : Atil) - ↑(urU ^ m) := IsUnit.unit_spec _
  have hmapU : Units.map (ftil : Atil →* Btil) UmulA = UmulB := by
    apply Units.ext; rw [Units.coe_map]
    show ftil (UmulA : Atil) = (UmulB : Btil)
    rw [hUmulAval, hUmulBval, map_sub, ← hrtRpow, ← hrtRpow]
  set U0 : (AddMonoidAlgebra Btil ℤ)ˣ :=
    Units.map ((AddMonoidAlgebra.singleZeroRingHom : Btil →+* AddMonoidAlgebra Btil ℤ) : Btil →*
        AddMonoidAlgebra Btil ℤ) UmulB with hU0
  have hU0val : (U0 : AddMonoidAlgebra Btil ℤ) = AddMonoidAlgebra.single 0 (UmulB : Btil) := by
    rw [hU0, Units.coe_map]; rfl
  -- transport hint along q
  have hmap6 := hint.map q
  have hqmt : q (C (LaurentPolynomial.T n - LaurentPolynomial.T m : LaurentPolynomial S) *
      (C (LaurentPolynomial.C z) * T n)) = (U0 : AddMonoidAlgebra Btil ℤ) * ι₀ target := by
    rw [map_mul]
    show q mult * q target = _
    rw [hqmult, htgt, hιtgt, hU0val, hUmulBval]
  rw [hqmt, hsq] at hmap6
  have hf'int : f'₀.IsIntegralElem ((U0 : AddMonoidAlgebra Btil ℤ) * ι₀ target) :=
    isIntegralElem_precomp f'₀ e' _ hmap6
  -- range memberships
  have hf'single :
      ∀ a : Atil, f'₀ (AddMonoidAlgebra.single 0 a) = AddMonoidAlgebra.single 0 (ftil a) := by
    intro a
    rw [hf'₀, AddMonoidAlgebra.mapRingHom_single]
  have hUvaleq : ftil (UmulA : Atil) = (UmulB : Btil) := by
    have h := congrArg Units.val hmapU
    simpa [Units.coe_map] using h
  have : (U0 : AddMonoidAlgebra Btil ℤ) ∈ Set.range f'₀ := by
    refine ⟨AddMonoidAlgebra.single 0 (UmulA : Atil), ?_⟩
    rw [hf'single, hU0val, hUvaleq]
  have hUvalinv : ftil (↑UmulA⁻¹ : Atil) = (↑UmulB⁻¹ : Btil) := by
    rw [← hmapU]; exact (Units.coe_map_inv (ftil : Atil →* Btil) UmulA).symm
  have hUrange' : (↑U0⁻¹ : AddMonoidAlgebra Btil ℤ) ∈ Set.range f'₀ := by
    refine ⟨AddMonoidAlgebra.single 0 (↑UmulA⁻¹ : Atil), ?_⟩
    rw [hf'single, hUvalinv, hU0]
    exact (Units.coe_map_inv ((AddMonoidAlgebra.singleZeroRingHom : Btil →+* AddMonoidAlgebra Btil
        ℤ) : Btil →* AddMonoidAlgebra Btil ℤ) UmulB).symm
  have hf'tgt : f'₀.IsIntegralElem (ι₀ target) :=
    isIntegralElem_of_unit_mul f'₀ U0 hUrange' (ι₀ target) hf'int
  obtain ⟨e, f', ι, π, hb⟩ := bundle_transport (AddMonoidAlgebra.mapRingHom ℤ (Φ₁ (R := R) (S :=
      S)))
    (eqA := (ULift.ringEquiv (R := AddMonoidAlgebra Atil ℤ)).symm)
    (eqB := (ULift.ringEquiv (R := AddMonoidAlgebra Btil ℤ)).symm)
    (A' := ULift.{u_2} (AddMonoidAlgebra Atil ℤ)) (B' := ULift.{u_1} (AddMonoidAlgebra Btil ℤ))
    e₀ f'₀ ι₀ π₀ target h1 h2 h3 h4 h5 hf'tgt
  exact ⟨ULift.{u_2} (AddMonoidAlgebra Atil ℤ), ULift.{u_1} (AddMonoidAlgebra Btil ℤ),
    inferInstance, inferInstance, e, f', ι, π, hb⟩
