module

public import StacksFrontier.RingTheory.GeometricallyIrreducible.TFAE.RationalFunctionField
import StacksCore.Tactic.EgaSgaAttribute

/-! # Geometric irreducibility: the field main lemma and the equivalence

This file completes the field main lemma (the irreducibility kernel of Stacks 04KQ over an
algebraically closed base), proves the arrow `(4) ⇒ (1)` via a common overfield and descent of
irreducibility along injective flat base change, and states the equivalence of the four
conditions (`geometrically_irreducible_tfae`, Stacks Tag 037K). It is part of
`StacksFrontier.RingTheory.GeometricallyIrreducible.TFAE`.
-/

@[expose] public section

open TensorProduct

universe u

/-- **[ISO] Reduction of `geomIrred_Lt_algClosedIn` to Lemma X.**
Takes the full statement of `geomIrred_lemmaX` as a hypothesis `hX` and proves the
relative-algebraic-closedness of `K = L(t)` in `M = Frac(K ⊗[L] F)`. Given the structural
comparison
data (`geomIrred_Lt_comparison_data`: `φ`, the injective `K`-algebra hom `j : Frac(K⊗[L]F) →ₐ[K]
MvRatFunc σ F`, the identification `eK : K ≃+* MvRatFunc σ L`, with `hφ` and `hcompat`), the body
discharges Lemma X's `hLE` hypothesis (`L` is algebraically closed in `F`, immediate from
`[IsAlgClosed L]` via `IsAlgClosed.degree_eq_one_of_irreducible` + `minpoly.natDegree_eq_one_iff`),
transports `IsAlgebraic K y` to the `eval₂ φ (j y)`-witness form, mapping the minpoly's
coefficients
through `eK` and using `hcompat`), applies `hX` to land `j y ∈ φ.range`, and pulls back to `y ∈ ⊥`
via `eK` surjective + `j` injective. NO new mathematical kernel — pure plumbing. -/
theorem geomIrred_Lt_algClosedIn_ofLemmaX
    (L : Type u) [Field L] [IsAlgClosed L]
    (σ : Type u) [Finite σ]
    (K : Type u) [Field K] [Algebra L K]
    [Algebra (MvPolynomial σ L) K] [IsScalarTower L (MvPolynomial σ L) K]
    [IsFractionRing (MvPolynomial σ L) K]
    (F : Type u) [Field F] [Algebra L F] [IsAlgClosed F]
    (hX : ∀ (L' E' : Type u) [Field L'] [Field E'] [Algebra L' E'] [Infinite L'],
            (∀ z : E', IsAlgebraic L' z → z ∈ (⊥ : Subalgebra L' E')) →
            ∀ (σ' : Type u) [Finite σ']
              (φ : MvRatFunc σ' L' →+* MvRatFunc σ' E'),
              φ.comp (algebraMap (MvPolynomial σ' L') (MvRatFunc σ' L')) =
                (algebraMap (MvPolynomial σ' E') (MvRatFunc σ' E')).comp
                  (MvPolynomial.map (algebraMap L' E')) →
              ∀ (w : MvRatFunc σ' E'),
                (∃ p : Polynomial (MvRatFunc σ' L'), p ≠ 0 ∧ Polynomial.eval₂ φ w p = 0) →
                w ∈ φ.range) :
    ∀ y : FractionRing (K ⊗[L] F), IsAlgebraic K y →
      y ∈ (⊥ : Subalgebra K (FractionRing (K ⊗[L] F))) := by
  classical
  -- `L` is infinite (algebraically closed) — needed to apply `hX`.
  have : Infinite L := inferInstance
  -- Structural comparison data (the hard structural piece, isolated as a helper).
  obtain ⟨φ, j, eK, hjinj, hφ, hcompat⟩ :=
    geomIrred_Lt_comparison_data L σ K F
  -- Discharge Lemma X's `hLE`: `L` alg closed ⟹ relatively alg closed in `F`.
  have hLE : ∀ z : F, IsAlgebraic L z → z ∈ (⊥ : Subalgebra L F) := by
    intro z hz
    have hint : IsIntegral L z := hz.isIntegral
    have hirr : Irreducible (minpoly L z) := minpoly.irreducible hint
    have hdeg1 : (minpoly L z).degree = 1 := IsAlgClosed.degree_eq_one_of_irreducible L hirr
    have hnd : (minpoly L z).natDegree = 1 :=
      Polynomial.natDegree_eq_of_degree_eq_some hdeg1
    have hrange : z ∈ (algebraMap L F).range := minpoly.natDegree_eq_one_iff.mp hnd
    rw [Algebra.mem_bot]; exact hrange
  -- Main transport.
  intro y hy
  set w : MvRatFunc σ F := j y with hw_def
  -- Build the `eval₂ φ w`-witness from `IsAlgebraic K y`.
  obtain ⟨p₀, hp₀ne, hp₀root⟩ := hy
  -- map coefficients of `p₀ : Polynomial K` through `eK : K ≃+* MvRatFunc σ L`.
  set p : Polynomial (MvRatFunc σ L) := p₀.map (eK : K →+* MvRatFunc σ L) with hp_def
  have hpne : p ≠ 0 := by
    rw [hp_def, Ne, Polynomial.map_eq_zero_iff (eK : K →+* MvRatFunc σ L).injective]
    exact hp₀ne
  -- `eval₂ φ w p = j (aeval y p₀) = 0`.
  have hpeval : Polynomial.eval₂ φ w p = 0 := by
    have hcoeff : (φ : MvRatFunc σ L →+* MvRatFunc σ F).comp (eK : K →+* MvRatFunc σ L)
        = j.comp (algebraMap K (FractionRing (K ⊗[L] F))) := by
      ext c
      simp only [RingHom.comp_apply]
      exact hcompat c
    calc Polynomial.eval₂ φ w p
        = Polynomial.eval₂ (φ.comp (eK : K →+* MvRatFunc σ L)) w p₀ := by
          rw [hp_def, Polynomial.eval₂_map]
      _ = Polynomial.eval₂ (j.comp (algebraMap K (FractionRing (K ⊗[L] F)))) w p₀ := by
          rw [hcoeff]
      _ = j (Polynomial.eval₂ (algebraMap K (FractionRing (K ⊗[L] F))) y p₀) := by
          rw [hw_def, ← Polynomial.hom_eval₂]
      _ = j ((Polynomial.aeval y) p₀) := by rw [Polynomial.aeval_def]
      _ = j 0 := by rw [hp₀root]
      _ = 0 := map_zero _
  -- Apply Lemma X (`hX`) at `L' := L`, `E' := F`, `σ' := σ`.
  have hwrange : w ∈ φ.range := hX L F hLE σ φ hφ w ⟨p, hpne, hpeval⟩
  obtain ⟨k, hk⟩ := hwrange
  -- `eK` surjective: `k = eK c` for some `c : K`.
  obtain ⟨c, hc⟩ := eK.surjective k
  -- `j y = w = φ k = φ (eK c) = j (algebraMap K _ c)`, so `y = algebraMap K _ c ∈ ⊥`.
  have hjy : j y = j (algebraMap K (FractionRing (K ⊗[L] F)) c) := by
    rw [← hw_def, ← hk, ← hc, hcompat c]
  have hyc : y = algebraMap K (FractionRing (K ⊗[L] F)) c := hjinj hjy
  rw [Algebra.mem_bot]
  exact ⟨c, hyc.symm⟩

/-- **[SC-AC-CLOSED]** body wired to `geomIrred_Lt_algClosedIn_ofLemmaX` fed `geomIrred_lemmaX`. -/
theorem geomIrred_Lt_algClosedIn
    (L : Type u) [Field L] [IsAlgClosed L]
    (σ : Type u) [Finite σ]
    (K : Type u) [Field K] [Algebra L K]
    [Algebra (MvPolynomial σ L) K] [IsScalarTower L (MvPolynomial σ L) K]
    [IsFractionRing (MvPolynomial σ L) K]
    (F : Type u) [Field F] [Algebra L F] [IsAlgClosed F] :
    ∀ y : FractionRing (K ⊗[L] F), IsAlgebraic K y →
      y ∈ (⊥ : Subalgebra K (FractionRing (K ⊗[L] F))) :=
  -- Stacks 04KQ: L(t) algebraically closed in F(t)).
  geomIrred_Lt_algClosedIn_ofLemmaX L σ K F
    (fun L' E' _ _ _ _ hLE' σ' _ φ hφ w hw => geomIrred_lemmaX L' E' hLE' σ' φ hφ w hw)

/-- **[SC-AC-IRRED] The irreducibility kernel of Stacks 04KQ (`F` algebraically closed).**
The separable minimal polynomial `p = minpoly K x` of `x : M = Frac(K ⊗[L] F)` integral over `K`
stays irreducible when mapped to `M`. The body rests on the relative-algebraic-closedness
kernel `geomIrred_Lt_algClosedIn` above — it carries NO open goal of its own. Given that `x` (being
integral, hence algebraic over `K`) lies in `K = ⊥` by `geomIrred_Lt_algClosedIn`, its minimal
polynomial `p` has degree `1` (`minpoly.natDegree_eq_one_iff`), so `p.map` is a degree-1 monic
polynomial over the field `M`, hence irreducible (`irreducible_of_degree_eq_one`). -/
theorem geomIrred_atom_algClosed_irreducible
    (L : Type u) [Field L] [IsAlgClosed L]
    (σ : Type u) [Finite σ]
    (K : Type u) [Field K] [Algebra L K]
    [Algebra (MvPolynomial σ L) K] [IsScalarTower L (MvPolynomial σ L) K]
    [IsFractionRing (MvPolynomial σ L) K]
    (F : Type u) [Field F] [Algebra L F] [IsAlgClosed F]
    (x : FractionRing (K ⊗[L] F))
    (hx : IsIntegral K x) :
    Irreducible ((minpoly K x).map (algebraMap K (FractionRing (K ⊗[L] F)))) := by
  -- Keep `IsDomain (K ⊗[L] F)` in scope so `Field (FractionRing (K ⊗[L] F))` synthesizes
  -- canonically (avoids a `Ring`-instance whnf timeout).
  have hRdom : IsDomain (K ⊗[L] F) := geomIrred_fg_R_isDomain L σ K F
  -- x is algebraic over K, so by relative algebraic closedness x ∈ ⊥ = range(algebraMap K M)
  have hmem : x ∈ (⊥ : Subalgebra K (FractionRing (K ⊗[L] F))) :=
    geomIrred_Lt_algClosedIn L σ K F x hx.isAlgebraic
  have hrange : x ∈ (algebraMap K (FractionRing (K ⊗[L] F))).range := by
    rw [Algebra.mem_bot] at hmem
    exact hmem
  -- hence minpoly K x has natDegree 1
  have hpdeg : (minpoly K x).natDegree = 1 := minpoly.natDegree_eq_one_iff.mpr hrange
  -- p.map is degree-1 monic over the field M, hence irreducible
  have hpm : (minpoly K x).Monic := minpoly.monic hx
  have hmapdeg : ((minpoly K x).map (algebraMap K (FractionRing (K ⊗[L] F)))).natDegree = 1 := by
    rw [hpm.natDegree_map, hpdeg]
  have hmapne : (minpoly K x).map (algebraMap K (FractionRing (K ⊗[L] F))) ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hmapdeg
    exact zero_ne_one hmapdeg
  have hmapdeg' : ((minpoly K x).map (algebraMap K (FractionRing (K ⊗[L] F)))).degree = 1 := by
    rw [Polynomial.degree_eq_natDegree hmapne, hmapdeg]; rfl
  exact Polynomial.irreducible_of_degree_eq_one hmapdeg'

/-- **[SC-AC] The kernel with `F` algebraically closed.** Same statement as
`geomIrred_atom_sepClosedIn`
but with the extra hypothesis `[IsAlgClosed F]`. This is the analytic core of Stacks 04KQ
in
its cleanest setting: with `F` algebraically closed, `M = Frac(K ⊗[L] F) ≅ F(t)` (the rational
function field), `K = L(t) ⊆ F(t)`, and the claim "`L(t) = K` is separably algebraically closed in
`F(t) = M`" is the persistence of separable-algebraic closedness under the purely transcendental
extension `(·)(t)`.

FORMAL SKETCH: this body is COMPLETE modulo the irreducibility kernel
`geomIrred_atom_algClosed_irreducible` above — it carries NO open goal of its own. Given that the
separable minimal polynomial `p = minpoly K x` stays irreducible over `M`, the conclusion
`x ∈ K` is
elementary: `x ∈ M` is a root of `p.map`, so `(X - C x) ∣ p.map`; an irreducible `p.map` with a
degree-1 divisor is itself degree 1, so `(minpoly K x).natDegree = 1`, whence `x ∈ (algebraMap K
M).range = ⊥`
(`minpoly.natDegree_eq_one_iff`). -/
theorem geomIrred_atom_sepClosedIn_algClosed
    (L : Type u) [Field L] [IsAlgClosed L]
    (σ : Type u) [Finite σ]
    (K : Type u) [Field K] [Algebra L K]
    [Algebra (MvPolynomial σ L) K] [IsScalarTower L (MvPolynomial σ L) K]
    [IsFractionRing (MvPolynomial σ L) K]
    (F : Type u) [Field F] [Algebra L F] [IsAlgClosed F] :
    ∀ x : FractionRing (K ⊗[L] F), IsIntegral K x → (minpoly K x).Separable →
      x ∈ (⊥ : Subalgebra K (FractionRing (K ⊗[L] F))) := by
  -- Keep `IsDomain (K ⊗[L] F)` in scope so `Field (FractionRing (K ⊗[L] F))` synthesizes
  -- canonically (avoids a `Ring`-instance whnf timeout).
  have hRdom : IsDomain (K ⊗[L] F) := geomIrred_fg_R_isDomain L σ K F
  intro x hx _
  exact geomIrred_Lt_algClosedIn L σ K F x hx.isAlgebraic

/-- **[SC-RED] Reduction of `geomIrred_atom_sepClosedIn` to the `F`-algebraically-closed case.**
Given the conclusion for `AlgebraicClosure F` (hypothesis `hAC`), it holds for `F`. The reason:
`F → AlgebraicClosure F` is an injective `L`-algebra map, so (by flatness of `· ⊗[L] F̄`/`· ⊗[L] F`
over the field `L`) `K ⊗[L] F → K ⊗[L] AlgebraicClosure F` is an injective ring map between domains
(both domains by `geomIrred_fg_R_isDomain` [D]), extending to an injective `K`-algebra map of
fraction
fields `j : M = Frac(K ⊗[L] F) → M̄ = Frac(K ⊗[L] AlgebraicClosure F)`. For `x : M` integral over
`K`
with separable minimal polynomial, `j x` has the SAME minimal polynomial over `K` (it is a
`K`-algebra
embedding), so by `hAC`, `j x ∈ K` (range of `algebraMap K M̄`); since `j` is `K`-linear and
injective
and `algebraMap K M̄ = j ∘ algebraMap K M`, this forces `x ∈ K`. Mathlib bricks: flatness
`Module.Flat.lTensor_preserves_injective_linearMap`, `IsFractionRing.injective`/`liftAlgHom`,
`minpoly` invariance under `K`-algebra embeddings, `Algebra.mem_bot`. -/
theorem geomIrred_atom_sepClosedIn_reduce
    (L : Type u) [Field L] [IsAlgClosed L]
    (σ : Type u) [Finite σ]
    (K : Type u) [Field K] [Algebra L K]
    [Algebra (MvPolynomial σ L) K] [IsScalarTower L (MvPolynomial σ L) K]
    [IsFractionRing (MvPolynomial σ L) K]
    (F : Type u) [Field F] [Algebra L F]
    (hAC : ∀ x : FractionRing (K ⊗[L] AlgebraicClosure F),
      IsIntegral K x → (minpoly K x).Separable →
        x ∈ (⊥ : Subalgebra K (FractionRing (K ⊗[L] AlgebraicClosure F)))) :
    ∀ x : FractionRing (K ⊗[L] F), IsIntegral K x → (minpoly K x).Separable →
      x ∈ (⊥ : Subalgebra K (FractionRing (K ⊗[L] F))) := by
  set Fbar := AlgebraicClosure F with hFbar
  -- the L-algebra map F → F̄
  let f : F →ₐ[L] Fbar := IsScalarTower.toAlgHom L F Fbar
  have hfinj : Function.Injective f := (algebraMap F Fbar).injective
  -- the base-change map ι : K ⊗[L] F → K ⊗[L] F̄ (an L-algebra map)
  let ιL : (K ⊗[L] F) →ₐ[L] (K ⊗[L] Fbar) :=
    Algebra.TensorProduct.map (AlgHom.id L K) f
  -- ιL is compatible with the K-algebra structures (it fixes the left tensor factor)
  have hιcomm : ∀ c : K, ιL (algebraMap K (K ⊗[L] F) c) = algebraMap K (K ⊗[L] Fbar) c := by
    intro c
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply]
    change ιL (c ⊗ₜ[L] 1) = c ⊗ₜ[L] 1
    rw [Algebra.TensorProduct.map_tmul]
    simp
  -- both tensor products are domains
  have hdomF : IsDomain (K ⊗[L] F) := geomIrred_fg_R_isDomain L σ K F
  have hdomFbar : IsDomain (K ⊗[L] Fbar) := geomIrred_fg_R_isDomain L σ K Fbar
  -- ιL is injective (K is L-flat, f is injective; bridge to lTensor)
  have hlinj : Function.Injective (LinearMap.lTensor K f.toLinearMap) :=
    Module.Flat.lTensor_preserves_injective_linearMap f.toLinearMap hfinj
  have hιinj : Function.Injective ιL := fun _ _ hab => hlinj hab
  -- abbreviations for the fraction fields
  let M := FractionRing (K ⊗[L] F)
  let Mbar := FractionRing (K ⊗[L] Fbar)
  -- the composite K-algebra hom g : (K ⊗[L] F) →ₐ[K] M̄
  let g : (K ⊗[L] F) →ₐ[K] Mbar :=
    { toRingHom := (algebraMap (K ⊗[L] Fbar) Mbar).comp ιL.toRingHom
      commutes' := by
        intro c
        change algebraMap (K ⊗[L] Fbar) Mbar (ιL (algebraMap K (K ⊗[L] F) c))
          = algebraMap K Mbar c
        rw [hιcomm c, ← IsScalarTower.algebraMap_apply] }
  have hginj : Function.Injective g := by
    have h1 : Function.Injective (algebraMap (K ⊗[L] Fbar) Mbar) :=
      IsFractionRing.injective _ _
    exact h1.comp hιinj
  -- lift to a K-algebra map j : M →ₐ[K] M̄
  let j : M →ₐ[K] Mbar := IsFractionRing.liftAlgHom hginj
  have hjinj : Function.Injective j := j.toRingHom.injective
  intro x hx hsep
  -- j x is integral over K with the same minimal polynomial
  have hjxint : IsIntegral K (j x) := hx.map j
  have hmineq : minpoly K (j x) = minpoly K x := minpoly.algHom_eq j hjinj x
  have hjxsep : (minpoly K (j x)).Separable := by rw [hmineq]; exact hsep
  -- apply hAC
  have hmem : j x ∈ (⊥ : Subalgebra K Mbar) := hAC (j x) hjxint hjxsep
  rw [Algebra.mem_bot] at hmem
  obtain ⟨c, hc⟩ := hmem
  -- j x = algebraMap K M̄ c = j (algebraMap K M c)
  have : j x = j (algebraMap K M c) := by rw [j.commutes c]; exact hc.symm
  have hxc : x = algebraMap K M c := hjinj this
  rw [Algebra.mem_bot]
  exact ⟨c, hxc.symm⟩

/-- **[ATOM-SC] Stacks 04KQ — the genuine analytic kernel.** For `L` algebraically closed,
`K = L(t)` purely transcendental (presented as `Frac(MvPolynomial σ L)`), and any field `F/L`,
the field `K` is *separably algebraically closed in* `M = Frac(K ⊗[L] F)`: every `x : M` that is
integral over `K` with separable minimal polynomial already lies in `K`.
FORMAL SKETCH: this body is COMPLETE modulo the two helper lemmas above — it has NO open goal
of its own. It reduces the arbitrary-`F` statement to the `F`-algebraically-closed case
(`geomIrred_atom_sepClosedIn_algClosed`, the analytic core) via the injective-base-change reduction
`geomIrred_atom_sepClosedIn_reduce`, fed at `AlgebraicClosure F`. -/
theorem geomIrred_atom_sepClosedIn
    (L : Type u) [Field L] [IsAlgClosed L]
    (σ : Type u) [Finite σ]
    (K : Type u) [Field K] [Algebra L K]
    [Algebra (MvPolynomial σ L) K] [IsScalarTower L (MvPolynomial σ L) K]
    [IsFractionRing (MvPolynomial σ L) K]
    (F : Type u) [Field F] [Algebra L F] :
    ∀ x : FractionRing (K ⊗[L] F), IsIntegral K x → (minpoly K x).Separable →
      x ∈ (⊥ : Subalgebra K (FractionRing (K ⊗[L] F))) :=
  geomIrred_atom_sepClosedIn_reduce L σ K F
    (geomIrred_atom_sepClosedIn_algClosed L σ K (AlgebraicClosure F))

/-- **[ATOM] The hard analytic atom (Stacks 04KQ/05DS): `E ⊗[K] M` is a domain.** With `L`
algebraically closed, `K = L(t)` purely transcendental, `E/K` finite separable, `F/L` any field,
`R = K ⊗[L] F` the (Step 3a) domain and `M = Frac R`, the tensor `E ⊗[K] M` is an integral domain.
FORMAL SKETCH: this body is COMPLETE modulo the two helper lemmas above — it has NO open goal
of its own. It establishes the `IsDomain (K ⊗[L] F)` instance (so `M = Frac(K ⊗[L] F)` is a field)
via `geomIrred_fg_R_isDomain` [D], then closes by the natural-irrationalities lemma
`geomIrred_atom_sepClosed_isDomain` [ATOM-NI] fed with the separable-closedness lemma
`geomIrred_atom_sepClosedIn` [ATOM-SC]. -/
theorem geomIrred_fg_atom
    (L : Type u) [Field L] [IsAlgClosed L]
    (σ : Type u) [Finite σ]
    (K : Type u) [Field K] [Algebra L K]
    [Algebra (MvPolynomial σ L) K] [IsScalarTower L (MvPolynomial σ L) K]
    [IsFractionRing (MvPolynomial σ L) K]
    (E : Type u) [Field E] [Algebra L E] [Algebra K E] [IsScalarTower L K E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    (F : Type u) [Field F] [Algebra L F] :
    IsDomain (E ⊗[K] FractionRing (K ⊗[L] F)) := by
  have hRdom : IsDomain (K ⊗[L] F) := geomIrred_fg_R_isDomain L σ K F
  exact geomIrred_atom_sepClosed_isDomain K E (FractionRing (K ⊗[L] F))
    (geomIrred_atom_sepClosedIn L σ K F)

/-- Irreducibility of the spectrum transfers along a ring isomorphism. -/
private theorem irreducibleSpace_of_ringEquiv {A B : Type u} [CommRing A] [CommRing B]
    (e : B ≃+* A) (h : IrreducibleSpace (PrimeSpectrum A)) :
    IrreducibleSpace (PrimeSpectrum B) := by
  refine irreducibleSpace_of_denseRange_comap e.toRingHom ?_ h
  intro x hx
  rw [RingHom.mem_ker] at hx
  have hx0 : x = 0 := (map_eq_zero_iff _ e.injective).mp hx
  rw [hx0]; exact zero_mem _

/-- The finitely generated core: for `L` algebraically closed, `K` the fraction field of
`MvPolynomial σ L` and `E/K` finite separable, the space `Spec (E ⊗[L] F)` is irreducible for
every extension `F/L`. -/
@[ega "IV 4.3.2" "special case"]
theorem geomIrred_fg_core
    (L : Type u) [Field L] [IsAlgClosed L]
    (σ : Type u) [Finite σ]
    (K : Type u) [Field K] [Algebra L K]
    [Algebra (MvPolynomial σ L) K] [IsScalarTower L (MvPolynomial σ L) K]
    [IsFractionRing (MvPolynomial σ L) K]
    (E : Type u) [Field E] [Algebra L E] [Algebra K E] [IsScalarTower L K E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    (F : Type u) [Field F] [Algebra L F] :
    IrreducibleSpace (PrimeSpectrum (E ⊗[L] F)) := by
  -- The body below rests on the three auxiliary results above
  -- (`geomIrred_fg_R_isDomain` [D], `geomIrred_fg_baseChange_localization_ker` [J],
  -- `geomIrred_fg_atom` [ATOM]); it carries NO open goal of its own.
  -- Step 3a: R = K ⊗[L] F is a domain.
  have hRdom : IsDomain (K ⊗[L] F) := geomIrred_fg_R_isDomain L σ K F
  -- Atom: M = Frac R, E ⊗[K] M is a domain (so its Spec is irreducible).
  have hMdom : IsDomain (E ⊗[K] FractionRing (K ⊗[L] F)) := geomIrred_fg_atom L σ K E F
  -- Dense-image localization transfer: Spec(E ⊗[K] R) irreducible via R → M = Frac R.
  have hirr_R : IrreducibleSpace (PrimeSpectrum (E ⊗[K] (K ⊗[L] F))) :=
    irreducibleSpace_of_denseRange_comap
      (Algebra.TensorProduct.map (AlgHom.id K E)
        (IsScalarTower.toAlgHom K (K ⊗[L] F) (FractionRing (K ⊗[L] F)))).toRingHom
      (geomIrred_fg_baseChange_localization_ker K E (K ⊗[L] F) (FractionRing (K ⊗[L] F)))
      PrimeSpectrum.irreducibleSpace
  -- Transport along `cancelBaseChange`: E ⊗[K] (K ⊗[L] F) ≃ₐ[K] E ⊗[L] F.
  let e := Algebra.TensorProduct.cancelBaseChange L K K E F
  exact irreducibleSpace_of_ringEquiv e.symm.toRingEquiv hirr_R

/-- For `L` algebraically closed and `E/L` essentially of finite type, `Spec (E ⊗[L] F)` is
irreducible for every extension `F/L`. -/
@[ega "IV 4.3.2" "special case", ega "IV 4.4.4" "special case", ega "IV 4.4.5" "special case"]
theorem geomIrred_fields_fg
    (L : Type u) [Field L] [IsAlgClosed L]
    (E : Type u) [Field E] [Algebra L E] [Algebra.EssFiniteType L E]
    (F : Type u) [Field F] [Algebra L F] :
    IrreducibleSpace (PrimeSpectrum (E ⊗[L] F)) := by
  -- FORMAL SKETCH: this body is COMPLETE modulo `geomIrred_fg_presentation` and
  -- `geomIrred_fg_core` above; it carries NO open goal of its own. Obtain the separating
  -- transcendence basis + primitive element presentation, then close via the f.g. core.
  obtain ⟨σ, hσ, K, hK, hLK, hMK, hst1, hfr, hKE, hst2, hfd, hsep⟩ :=
    geomIrred_fg_presentation L E
  exact geomIrred_fg_core L σ K E F

/-- **Field Main Lemma** (the genuine analytic core). For `L` algebraically closed and any field
extensions `E/L`, `F/L`, `Spec (E ⊗[L] F)` is irreducible (Stacks 04KQ/05DS). Reduced to the
finitely generated case (`geomIrred_fields_fg`) via the filtered-colimit transfer
(`geomIrred_fields_colimit`). -/
@[ega "IV 4.3.2" "special case",
  ega "IV 4.3.3" "special case",
  ega "IV 4.4.4" "special case",
  ega "IV 4.4.5" "special case",
  ega "IV 4.5.8" "(i), special case"]
theorem geomIrred_kernel_fields
    (L : Type u) [Field L] [IsAlgClosed L]
    (E : Type u) [Field E] [Algebra L E]
    (F : Type u) [Field F] [Algebra L F] :
    IrreducibleSpace (PrimeSpectrum (E ⊗[L] F)) := by
  -- IsAlgClosed L hypothesis is essential — ℂ⊗_ℝℂ ≅ ℂ×ℂ is the failure mode for non-closed base).
  -- FORMAL SKETCH: this body is COMPLETE modulo `geomIrred_fields_colimit` and
  -- `geomIrred_fields_fg` above; it carries NO open goal of its own.
  apply geomIrred_fields_colimit L E F
  intro E' F' hE' hF'
  have := hE'
  exact geomIrred_fields_fg L E' F'

/-- **Residue-field reduction kernel bound (Lemma 1).** If `g : A →ₐ[L] E` has
`RingHom.ker g ≤ nilradical A`, then the `F`-base change `Algebra.TensorProduct.map g (id_F)` has
`RingHom.ker ≤ nilradical (A ⊗[L] F)`. (Equivalently its `PrimeSpectrum.comap` has dense range.)

Proof: `F` is free, hence flat, over the field `L`, so `· ⊗[L] F` is exact and
`ker (g ⊗ id_F) = (ker g) ⊗[L] F` (the image of `ker g ⊗ F` under `includeLeft`); since every
generator `x ⊗ f` with `x ∈ ker g ≤ nilradical A` is nilpotent in `A ⊗[L] F`, the kernel lands in
the nilradical. Mathlib bricks: `Module.Flat.lTensor_preserves_injective_linearMap` / exactness of
`lTensor`, `Algebra.TensorProduct.map`, `nilradical`/`IsNilpotent` of pure tensors with a
nilpotent left factor, `TensorProduct.induction_on`. ROUTINE/MODERATE. -/
theorem geomIrred_kernel_residue_denseRange
    (L : Type u) [Field L]
    (A : Type u) [CommRing A] [Algebra L A]
    (E : Type u) [CommRing E] [Algebra L E]
    (g : A →ₐ[L] E) (hgker : RingHom.ker g.toRingHom ≤ nilradical A)
    (F : Type u) [Field F] [Algebra L F] :
    RingHom.ker (Algebra.TensorProduct.map g (AlgHom.id L F)).toRingHom
      ≤ nilradical (A ⊗[L] F) := by
  -- ψ and rTensor agree as functions
  have heq : ∀ z : A ⊗[L] F, (Algebra.TensorProduct.map g (AlgHom.id L F)) z
      = (LinearMap.rTensor F g.toLinearMap) z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a f => simp [Algebra.TensorProduct.map_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  -- exact sequence ker g → A → E, tensored with flat F
  have hexA : Function.Exact (LinearMap.ker g.toLinearMap).subtype g.toLinearMap :=
    LinearMap.exact_subtype_ker_map g.toLinearMap
  have hexF : Function.Exact (LinearMap.rTensor F (LinearMap.ker g.toLinearMap).subtype)
      (LinearMap.rTensor F g.toLinearMap) :=
    Module.Flat.rTensor_exact F hexA
  -- the range of rTensor F (ker g).subtype lands in nilradical
  have hrange : ∀ y : (LinearMap.ker g.toLinearMap) ⊗[L] F,
      (LinearMap.rTensor F (LinearMap.ker g.toLinearMap).subtype) y ∈ nilradical (A ⊗[L] F) := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul w f =>
        rw [LinearMap.rTensor_tmul]
        -- (w : A) is in ker g ≤ nilradical, so nilpotent
        have hw : IsNilpotent ((w : A)) := by
          apply hgker
          rw [RingHom.mem_ker]
          exact w.property
        obtain ⟨n, hn⟩ := hw
        refine ⟨n, ?_⟩
        simp only [Submodule.coe_subtype]
        rw [Algebra.TensorProduct.tmul_pow, hn]
        simp
    | add a b ha hb =>
        rw [map_add]
        exact Ideal.add_mem _ ha hb
  intro z hz
  rw [RingHom.mem_ker] at hz
  have hz' : (LinearMap.rTensor F g.toLinearMap) z = 0 := by rw [← heq]; exact hz
  obtain ⟨y, hy⟩ := (hexF z).mp hz'
  rw [← hy]
  exact hrange y

/-- For `L` algebraically closed and `A` an `L`-algebra with irreducible spectrum,
`Spec (A ⊗[L] F)` is irreducible for every extension `F/L`. -/
@[ega "II 7.4.19" "partial",
  ega "IV 4.3.2" "special case",
  ega "IV 4.4.4" "affine k-schemes",
  ega "IV 4.4.5" "special case",
  ega "IV 4.5.1" "special case"]
theorem geomIrred_kernel_baseChange_algClosed
    (L : Type u) [Field L] [IsAlgClosed L]
    (A : Type u) [CommRing A] [Algebra L A]
    (hA : IrreducibleSpace (PrimeSpectrum A))
    (F : Type u) [Field F] [Algebra L F] :
    IrreducibleSpace (PrimeSpectrum (A ⊗[L] F)) := by
  -- The body below rests on the two auxiliary results `geomIrred_kernel_fields`
  -- and `geomIrred_kernel_residue_denseRange` above; it carries NO open goal of its own.
  -- Reduce `A` to the residue field `E = Frac(A ⧸ nilradical A)` at the generic point.
  have hp : (nilradical A).IsPrime :=
    (PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical).mp hA
  have : IsDomain (A ⧸ nilradical A) := Ideal.Quotient.isDomain _
  have : IsScalarTower L A (A ⧸ nilradical A) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower L (A ⧸ nilradical A) (FractionRing (A ⧸ nilradical A)) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- The `L`-algebra map `g : A → E = Frac(A ⧸ nilradical A)`, with `ker g ≤ nilradical A`.
  let g : A →ₐ[L] FractionRing (A ⧸ nilradical A) :=
    (IsScalarTower.toAlgHom L (A ⧸ nilradical A) (FractionRing (A ⧸ nilradical A))).comp
      (IsScalarTower.toAlgHom L A (A ⧸ nilradical A))
  have hgker : RingHom.ker g.toRingHom ≤ nilradical A := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    have hxq : (algebraMap A (A ⧸ nilradical A)) x = 0 :=
      IsFractionRing.injective (A ⧸ nilradical A) (FractionRing (A ⧸ nilradical A))
        (by rw [map_zero]; exact hx)
    have hmk : (Ideal.Quotient.mk (nilradical A)) x = 0 := hxq
    rwa [Ideal.Quotient.eq_zero_iff_mem] at hmk
  -- The base-change map `A ⊗[L] F → E ⊗[L] F` has dense Spec-image (kernel ≤ nilradical).
  have hker := geomIrred_kernel_residue_denseRange L A (FractionRing (A ⧸ nilradical A)) g hgker F
  -- `E ⊗[L] F` is irreducible (E a field over the algebraically closed L) by the field Main Lemma.
  have hEF : IrreducibleSpace
      (PrimeSpectrum (FractionRing (A ⧸ nilradical A) ⊗[L] F)) :=
    geomIrred_kernel_fields L (FractionRing (A ⧸ nilradical A)) F
  -- Transfer along the dense-image base-change map.
  exact irreducibleSpace_of_denseRange_comap
    (Algebra.TensorProduct.map g (AlgHom.id L F)).toRingHom hker hEF

/-- **Common overfield existence.** For two field extensions `L/k` and `k'/k` (all in `Type u`),
there is a field `F` carrying compatible `k`-algebra maps from `L` and `k'` (a compositum). Take
a maximal ideal `m` of the nonzero ring `L ⊗[k] k'` and set `F := (L ⊗[k] k') ⧸ m`, with the two
inclusions `L → F`, `k' → F` from `Algebra.TensorProduct.includeLeft/includeRight` composed with
the quotient map; the scalar towers over `k` hold by construction.

Lean inputs: `L ⊗[k] k' ≠ 0` (e.g.
`Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right`); `Ideal.exists_maximal`;
`Ideal.Quotient.field`; `(Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeLeftRingHom`
etc. for the algebra structures; `IsScalarTower.of_algebraMap_eq`. ROUTINE. -/
theorem geomIrred_common_overfield
    (k : Type u) [Field k] (L : Type u) [Field L] [Algebra k L]
    (k' : Type u) [Field k'] [Algebra k k'] :
    ∃ (F : Type u) (_ : Field F) (akF : Algebra k F) (aLF : Algebra L F)
      (ak'F : Algebra k' F),
      letI := akF; letI := aLF; letI := ak'F
      IsScalarTower k L F ∧ IsScalarTower k k' F := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (L ⊗[k] k')
  let : Field ((L ⊗[k] k') ⧸ m) := Ideal.Quotient.field m
  let akF : Algebra k ((L ⊗[k] k') ⧸ m) :=
    (Ideal.Quotient.mk m).comp (algebraMap k (L ⊗[k] k')) |>.toAlgebra
  let aLF : Algebra L ((L ⊗[k] k') ⧸ m) :=
    (Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeLeftRingHom |>.toAlgebra
  let ak'F : Algebra k' ((L ⊗[k] k') ⧸ m) :=
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeRight (R := k) (A := L) (B :=
        k')).toRingHom |>.toAlgebra
  refine ⟨(L ⊗[k] k') ⧸ m, inferInstance, akF, aLF, ak'F, ?_, ?_⟩
  · refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    change (Ideal.Quotient.mk m) (algebraMap k (L ⊗[k] k') x) = _
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
    rfl
  · refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    change (Ideal.Quotient.mk m) (algebraMap k (L ⊗[k] k') x) = _
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
    congr 1
    rw [Algebra.TensorProduct.algebraMap_apply]
    change (algebraMap k L x) ⊗ₜ[k] (1 : k') = (1 : L) ⊗ₜ[k] (algebraMap k k' x)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul]

/-- **Reassociation + kernel transport.** If `L` is algebraically closed, `Spec(R ⊗[k] L)` is
irreducible, and `F/L` is a field extension towering over `k`, then `Spec(R ⊗[k] F)` is
irreducible.

Proof: the base-change cancellation iso `Algebra.TensorProduct.cancelBaseChange k L F F R :
F ⊗[L] (L ⊗[k] R) ≃ₐ[F] F ⊗[k] R`, combined with `Algebra.TensorProduct.comm`, gives a ring iso
`(R ⊗[k] L) ⊗[L] F ≃+* R ⊗[k] F`. Apply `geomIrred_kernel_baseChange_algClosed` to
`A := R ⊗[k] L` (an `L`-algebra via the right tensor factor) and `F`, then transport
`IrreducibleSpace` along the induced `PrimeSpectrum` homeomorphism
(`PrimeSpectrum.comap` of a ring iso is a homeomorphism; `Homeomorph.irreducibleSpace_iff`).
The only nontrivial content is bookkeeping of the `L`-algebra structure on `R ⊗[k] L` and the
iso orientation. ROUTINE given the kernel. -/
@[ega "IV 4.4.4" "affine k-schemes",
  ega "IV 4.4.5" "special case",
  ega "IV 4.5.1" "special case",
  ega "IV 4.5.21" "special case",
  ega "IV 4.5.8" "(i), special case"]
theorem geomIrred_overfield_irreducible
    (k : Type u) [Field k] (R : Type u) [CommRing R] [Algebra k R]
    (L : Type u) [Field L] [IsAlgClosed L] [Algebra k L]
    (hL : IrreducibleSpace (PrimeSpectrum (R ⊗[k] L)))
    (F : Type u) [Field F] [Algebra k F] [Algebra L F] [IsScalarTower k L F] :
    IrreducibleSpace (PrimeSpectrum (R ⊗[k] F)) := by
  let : Algebra L (R ⊗[k] L) := Algebra.TensorProduct.rightAlgebra
  -- Apply the algebraically-closed kernel lemma with `A := R ⊗[k] L` (an `L`-algebra via the
  -- right tensor factor): `Spec((R ⊗[k] L) ⊗[L] F)` is irreducible.
  have hAF : IrreducibleSpace (PrimeSpectrum ((R ⊗[k] L) ⊗[L] F)) :=
    geomIrred_kernel_baseChange_algClosed L (R ⊗[k] L) hL F
  -- The kernel's output carries the tensor `CommSemiring` instance; coerce to the canonical
  -- `CommRing.toCommSemiring` instance (definitionally equal) so the transport lemma applies.
  have hAF' : IrreducibleSpace
      (@PrimeSpectrum ((R ⊗[k] L) ⊗[L] F) CommRing.toCommSemiring) := hAF
  -- The `L`-algebra commutativity `R ⊗[k] L ≃ₐ[L] L ⊗[k] R` (using the right `L`-structure).
  let ec : (R ⊗[k] L) ≃ₐ[L] (L ⊗[k] R) :=
    AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm k R L).toRingEquiv)
      (by
        intro l
        rw [Algebra.TensorProduct.right_algebraMap_apply]
        change (Algebra.TensorProduct.comm k R L) ((1 : R) ⊗ₜ[k] l) = _
        rw [Algebra.TensorProduct.comm_tmul]
        simp)
  -- The ring isomorphism `(R ⊗[k] L) ⊗[L] F ≃+* R ⊗[k] F`, built from `congr`, `comm` and
  -- `cancelBaseChange`.
  let e : ((R ⊗[k] L) ⊗[L] F) ≃+* (R ⊗[k] F) :=
    ((Algebra.TensorProduct.congr ec (AlgEquiv.refl (R := L) (A₁ := F)))).toRingEquiv.trans <|
    (Algebra.TensorProduct.comm L (L ⊗[k] R) F).toRingEquiv.trans <|
    (Algebra.TensorProduct.cancelBaseChange k L F F R).toRingEquiv.trans <|
    (Algebra.TensorProduct.comm k F R).toRingEquiv
  -- Transport irreducibility along `e.symm : R ⊗[k] F ≃+* (R ⊗[k] L) ⊗[L] F`.
  exact irreducibleSpace_of_ringEquiv e.symm hAF'

/-- **Descent of irreducibility along an injective flat ring map.** If `f : B →+* C` is injective
and flat and `Spec C` is irreducible, then `Spec B` is irreducible.

Proof: `Spec C` irreducible ⇒ `(nilradical C).IsPrime` and `C` nonzero
(`PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical`); `f` injective ⇒ `B` nonzero. For
uniqueness of the minimal prime of `B`: each minimal prime `p ∈ minimalPrimes B` is `f⁻¹(p')`
for some prime `p'` (`Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective`), and by
going-down for the flat map `f` (`RingHom.Flat` ⇒ `Algebra.HasGoingDown`) we may take `p'`
minimal; as `C` has a unique minimal prime (= `nilradical C`), `p = f⁻¹(nilradical C)` is forced,
so `B` has a unique minimal prime, i.e. `(nilradical B).IsPrime`. ROUTINE/MODERATE. -/
@[ega "IV 4.4.1" "special case"]
theorem geomIrred_descend_irreducible
    {B C : Type u} [CommRing B] [CommRing C] (f : B →+* C)
    (hinj : Function.Injective f)
    (hC : IrreducibleSpace (PrimeSpectrum C)) :
    IrreducibleSpace (PrimeSpectrum B) := by
  -- flat ring map: nonemptiness from f.domain_nontrivial; unique minimal prime via going-down
  -- (f.Flat ⟹ Algebra.HasGoingDown B C) +
  -- Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective).
  rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical] at hC ⊢
  -- For an injective ring map, `nilradical B = f⁻¹(nilradical C)`: if `f x` is nilpotent then
  -- `f (x ^ n) = (f x) ^ n = 0`, so `x ^ n = 0` by injectivity. Hence the preimage of the prime
  -- ideal `nilradical C` is prime.
  have hnil : nilradical B = Ideal.comap f (nilradical C) := by
    ext x
    simp only [mem_nilradical, Ideal.mem_comap]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, by rw [← map_pow, hn, map_zero]⟩
    · rintro ⟨n, hn⟩
      refine ⟨n, hinj ?_⟩
      rw [map_pow, hn, map_zero]
  rw [hnil]
  exact hC.comap f

/-- **Base-change map is injective and flat.** The `R`-base change
`ψ = Algebra.TensorProduct.map (AlgHom.id k R) (k' ↪ F)` of a field embedding `k' ↪ F` is
injective (flat base change of the injective `k' → F`, via
`Module.Flat.lTensor_preserves_injective_linearMap`) and flat (base change of the flat — indeed
free — field extension `k' → F`; `Module.Flat` of base change / `RingHom.Flat` of
`Algebra.TensorProduct.map`). ROUTINE. -/
@[ega "IV 4.4.1" "partial, special case", sga "6 X 7.15" "special case"]
theorem geomIrred_baseChange_map_injective_flat
    (k : Type u) [Field k] (R : Type u) [CommRing R] [Algebra k R]
    (k' : Type u) [Field k'] [Algebra k k']
    (F : Type u) [Field F] [Algebra k F] [Algebra k' F] [IsScalarTower k k' F] :
    Function.Injective
      ((Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k k' F)).toRingHom) ∧
    ((Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k k' F)).toRingHom).Flat
      := by
  -- base change of a free/flat module is flat; robust across edge cases R=0, k=k'=F,
  -- infinite ext).
  refine ⟨?_, ?_⟩
  · -- INJECTIVITY: `ψ` agrees with `LinearMap.lTensor R f` for `f = k' ↪ F`, and `f` is a split
    -- injection of `k`-vector spaces, so `lTensor R f` is injective.
    set f : k' →ₐ[k] F := IsScalarTower.toAlgHom k k' F with hf
    exact fun _ _ hab => Module.Flat.lTensor_preserves_injective_linearMap (M := R)
      f.toLinearMap (algebraMap k' F).injective hab
  · -- FLATNESS: `R ⊗[k] F ≅ (R ⊗[k] k') ⊗[k'] F` as `(R ⊗[k] k')`-modules, and the right-hand side
    -- is flat by base change of the flat (free) `k'`-module `F`.
    let algS : Algebra k' (R ⊗[k] k') :=
      (Algebra.TensorProduct.includeRight : k' →ₐ[k] R ⊗[k] k').toRingHom.toAlgebra
    have towS : IsScalarTower k k' (R ⊗[k] k') :=
      IsScalarTower.of_algebraMap_eq (fun x => by simp [algS, RingHom.algebraMap_toAlgebra])
    let algSF : Algebra (R ⊗[k] k') (R ⊗[k] F) :=
      (Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k k'
          F)).toRingHom.toAlgebra
    let algk'RF : Algebra k' (R ⊗[k] F) :=
      ((Algebra.TensorProduct.includeRight.comp (IsScalarTower.toAlgHom k k' F)) :
        k' →ₐ[k] R ⊗[k] F).toRingHom.toAlgebra
    have tow1 : IsScalarTower k k' (R ⊗[k] F) :=
      IsScalarTower.of_algebraMap_eq (fun x => by simp [algk'RF, RingHom.algebraMap_toAlgebra])
    have tow2 : IsScalarTower k' (R ⊗[k] k') (R ⊗[k] F) :=
      IsScalarTower.of_algebraMap_eq (fun x => by
        simp [algk'RF, algSF, algS, RingHom.algebraMap_toAlgebra,
          Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul])
    change Module.Flat (R ⊗[k] k') (R ⊗[k] F)
    have hbc : Module.Flat (R ⊗[k] k') ((R ⊗[k] k') ⊗[k'] F) :=
      Module.Flat.baseChange k' (R ⊗[k] k') F
    let g : F →ₐ[k'] (R ⊗[k] F) :=
      { (Algebra.TensorProduct.includeRight : F →ₐ[k] R ⊗[k] F).toRingHom with
        commutes' := fun r => by
          change (Algebra.TensorProduct.includeRight : F →ₐ[k] R ⊗[k] F) (algebraMap k' F r)
                = algebraMap k' (R ⊗[k] F) r
          simp [algk'RF, RingHom.algebraMap_toAlgebra] }
    let Φ : (R ⊗[k] k') ⊗[k'] F →ₐ[R ⊗[k] k'] (R ⊗[k] F) :=
      Algebra.TensorProduct.lift (Algebra.ofId (R ⊗[k] k') (R ⊗[k] F)) g
        (fun x y => Commute.all _ _)
    let Ψ : (R ⊗[k] F) →ₐ[k] (R ⊗[k] k') ⊗[k'] F :=
      Algebra.TensorProduct.lift
        (((Algebra.TensorProduct.includeLeft : (R ⊗[k] k') →ₐ[k'] (R ⊗[k] k') ⊗[k']
            F).restrictScalars k).comp
          (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] k'))
        ((Algebra.TensorProduct.includeRight : F →ₐ[k'] (R ⊗[k] k') ⊗[k'] F).restrictScalars k)
        (fun x y => mul_comm (G := (R ⊗[k] k') ⊗[k'] F) _ _)
    have keyΦ : ∀ (r : R) (a : k') (b : F), Φ ((r ⊗ₜ[k] a) ⊗ₜ[k'] b) = r ⊗ₜ[k] (a • b) := by
      intro r a b
      change (Algebra.ofId (R ⊗[k] k') (R ⊗[k] F)) (r ⊗ₜ[k] a) * g b = _
      rw [Algebra.ofId_apply]
      change (algebraMap (R ⊗[k] k') (R ⊗[k] F)) (r ⊗ₜ[k] a) * (1 ⊗ₜ[k] b) = _
      rw [RingHom.algebraMap_toAlgebra]
      change (Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k k' F)) (r ⊗ₜ[k]
          a) * (1 ⊗ₜ[k] b) = _
      rw [Algebra.TensorProduct.map_tmul]
      simp only [AlgHom.coe_id, id_eq, IsScalarTower.coe_toAlgHom']
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      simp [Algebra.smul_def]
    have keyΨ : ∀ (r : R) (y : F), Ψ (r ⊗ₜ[k] y) = (r ⊗ₜ[k] (1:k')) ⊗ₜ[k'] y := by
      intro r y
      change (((Algebra.TensorProduct.includeLeft : (R ⊗[k] k') →ₐ[k'] (R ⊗[k] k') ⊗[k']
          F).restrictScalars k).comp
          (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] k')) r
          * ((Algebra.TensorProduct.includeRight : F →ₐ[k'] (R ⊗[k] k') ⊗[k'] F).restrictScalars k)
              y = _
      change ((r ⊗ₜ[k] (1:k')) ⊗ₜ[k'] (1:F)) * ((1 : R ⊗[k] k') ⊗ₜ[k'] y) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    have hΨΦ : ∀ z, Ψ (Φ z) = z := by
      intro z
      induction z using TensorProduct.inductionOn with
      | add x y hx hy => rw [map_add, map_add, hx, hy]
      | tmul s b =>
        induction s using TensorProduct.inductionOn with
        | add x y hx hy =>
          rw [TensorProduct.add_tmul, map_add, map_add, hx, hy, ← TensorProduct.add_tmul]
        | tmul r a =>
          rw [keyΦ, keyΨ, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
          congr 1
          change (a • (r ⊗ₜ[k] (1:k'))) = r ⊗ₜ[k] a
          rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
          change (Algebra.TensorProduct.includeRight a) * (r ⊗ₜ[k] (1:k')) = _
          rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
            mul_one, one_mul]
    have hΦΨ : ∀ w, Φ (Ψ w) = w := by
      intro w
      induction w using TensorProduct.inductionOn with
      | add x y hx hy => rw [map_add, map_add, hx, hy]
      | tmul r b =>
        rw [keyΨ, keyΦ, one_smul]
    have hbij : Function.Bijective Φ :=
      ⟨Function.LeftInverse.injective hΨΦ, Function.RightInverse.surjective hΦΨ⟩
    let e : (R ⊗[k] k') ⊗[k'] F ≃ₗ[R ⊗[k] k'] (R ⊗[k] F) :=
      LinearEquiv.ofBijective Φ.toLinearMap hbij
    exact Module.Flat.of_linearEquiv e.symm

/-- The implication from the fourth to the first characterization of geometric
irreducibility. -/
@[ega "IV 4.4.1" "special case",
  ega "IV 4.4.4" "affine k-schemes",
  ega "IV 4.4.5" "special case",
  ega "IV 4.5.2" "(b) ⇒ (c)",
  ega "IV 4.5.6" "(i), special case"]
theorem geomIrred_step_4_1
    (k : Type u) [Field k] (R : Type u) [CommRing R] [Algebra k R]
    (h : GeomIrred4 k R) : GeomIrred1 k R := by
  -- The body below rests on the five auxiliary results above
  -- (`geomIrred_kernel_baseChange_algClosed`, `geomIrred_common_overfield`,
  -- `geomIrred_overfield_irreducible`, `geomIrred_descend_irreducible`,
  -- `geomIrred_baseChange_map_injective_flat`). It carries no open goal of its own.
  intro k' _ _
  -- Step A: build a common overfield `F` of `AlgebraicClosure k` and `k'`.
  obtain ⟨F, _, _, algLF, algk'F, htowerL, htowerk'⟩ :=
    geomIrred_common_overfield k (AlgebraicClosure k) k'
  let := algLF
  let := algk'F
  have := htowerL
  have := htowerk'
  -- Step B: `Spec(R ⊗[k] F)` is irreducible (kernel over the algebraically closed
  -- `AlgebraicClosure k`, transported through the base-change reassociation iso).
  have hF : IrreducibleSpace (PrimeSpectrum (R ⊗[k] F)) :=
    geomIrred_overfield_irreducible k R (AlgebraicClosure k) h F
  -- Step C: descend along the injective flat base change `R ⊗[k] k' → R ⊗[k] F`.
  obtain ⟨hinj, _⟩ := geomIrred_baseChange_map_injective_flat k R k' F
  exact geomIrred_descend_irreducible
    ((Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k k' F)).toRingHom)
    hinj hF

/-- **Stacks Tag 037K.** Let `k` be a field and `R` a commutative `k`-algebra. The four
conditions expressing geometric irreducibility of `R` over `k` are equivalent:

1. `Spec(R ⊗_k k')` is irreducible for every field extension `k'/k`;
2. `Spec(R ⊗_k k')` is irreducible for every finite separable field extension `k'/k`;
3. `Spec(R ⊗_k k^sep)` is irreducible;
4. `Spec(R ⊗_k k̄)` is irreducible.

The proof realizes the Stacks cycle `(1) ⇒ (2) ⇒ (3) ⇒ (4) ⇒ (1)` via `tfae_have`/`tfae_finish`.
`(1) ⇒ (2)` is the trivial instantiation; the three substantive arrows are the sub-lemmas
`geomIrred_step_2_3`, `geomIrred_step_3_4`, `geomIrred_step_4_1`. -/
@[ega "IV 4.4.1" "special case",
  ega "IV 4.4.4" "(4) ⇒ (1), special case",
  ega "IV 4.5.1" "special case",
  ega "IV 4.5.2" "(b) ⇔ (c), special case",
  ega "IV 4.5.21" "special case",
  ega "IV 4.5.9" "(a) ⇔ (b) for affine X"]
theorem geometrically_irreducible_tfae
    (k : Type u) [Field k] (R : Type u) [CommRing R] [Algebra k R] :
    [GeomIrred1 k R, GeomIrred2 k R, GeomIrred3 k R, GeomIrred4 k R].TFAE := by
  -- (1) ⇒ (2): a finite separable extension is in particular a field extension.
  tfae_have 1 → 2 := by intro h k' _ _ _ _; exact h k'
  -- (2) ⇒ (3): filtered-colimit + flat going-down argument.
  tfae_have 2 → 3 := geomIrred_step_2_3 k R
  -- (3) ⇒ (4): purely inseparable base change induces a Spec-homeomorphism.
  tfae_have 3 → 4 := geomIrred_step_3_4 k R
  -- (4) ⇒ (1): common-overfield embedding + base-change descent of the unique minimal prime.
  tfae_have 4 → 1 := geomIrred_step_4_1 k R
  tfae_finish
