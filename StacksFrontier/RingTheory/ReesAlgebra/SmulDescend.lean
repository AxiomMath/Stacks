module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import StacksFrontier.RingTheory.ReesAlgebra.SmulLift

/-!
# The lift of a splitting shifts the ideal filtration by its own degree

Let `A` be a commutative ring, `K ⊆ A` an ideal, `f : A →+* R` a ring map and `M` an
`R`-module. A linear functional `λ : K →ₗ[A] A` whose prescription `g · x ↦ λ(g) · x` respects
the relations lifts to an `R`-linear map `μ` on `K R · M`
(`Stacks.ReesAlgebra.exists_linearMap_of_kills_relations`). This file records what that lift
does to the smaller submodules `(K L) R · M`: it carries them into `L R · M`, for *every*
ideal `L` of `A`.

That is the step which makes one exponent serve the whole of [Stacks, Tag 0EH6]. Relation
killing — `Stacks.ReesAlgebra.KillsRelations` — is produced by [Stacks, Tag 0EIC] one module at
a time, so applying it to each term `F_m` of a coherent adic system gives an exponent depending
on `m`, and `m` is unbounded. The source avoids this by applying [Stacks, Tag 0EIC] once, to
the single finite module `N` over the completion supplied by [Stacks, Tag 087W], and reading
off the maps on the quotients `N / I ^ m N` by *descent*: a relation holding modulo
`I ^ (n d + m)` forces the combination of coefficients to vanish only modulo `I ^ m`, and that
shifted statement is a consequence of the one map `μ`, uniformly in `m`.

## Main definitions

* `Stacks.ReesAlgebra.KillsRelationsHom` — relation-killing along a ring map, which is the form
  a construction on a scheme consumes: the sections `Γ(X, W)` over an open carry no `Algebra A`
  instance, only the ring map `Stacks.Coherent.baseSectionHom` induced by the structure
  morphism `X ⟶ Spec A`.

## Main results

* `Stacks.ReesAlgebra.lift_mem_smul_of_mem_mul_smul` — the lift carries `(K L) R · M` into
  `L R · M`.
* `Stacks.ReesAlgebra.KillsRelationsHom.sum_mem_smul` — the shifted relation-killing statement
  in element form, from one exponent, for every ideal `L` at once.
* `Stacks.ReesAlgebra.exists_extendLinearMaps_killsRelationsHom` — [Stacks, Tag 0EIC] in that
  form.
* `Stacks.ReesAlgebra.exists_extendLinearMaps_killsRelationsHom_finset` — one exponent for a
  *finite* family of modules, obtained by applying the previous one to each in turn. This is
  what lets a finite affine cover of a Noetherian scheme be handled with a single exponent.
* `Stacks.ReesAlgebra.killsRelationsHom_of_compat` — relation-killing descends along a jointly
  injective family of additive maps compatible with the scalars, the targets being modules over
  whatever rings they like. Restriction maps, germ maps and the projections of an inverse limit
  are all of this shape.
* `Stacks.ReesAlgebra.KillsRelationsHom.of_isLocalizedModule` — relation-killing passes to a
  localization of the module, again without moving the exponent. On an affine scheme this is
  what carries the exponent found for the global sections to every affine open and every
  stalk.
* `Stacks.ReesAlgebra.killsRelationsHom_of_shift` — relation-killing for a module with jointly
  injective projections onto a tower whose levels kill relations after a shift. This is the
  passage to `Γ(lim F_n, W)`, whose relations are tested one level at a time.
* `Stacks.ReesAlgebra.sum_eq_zero_of_quotientTower` — the shifted statement itself, for a tower
  of quotients `M / I ^ (m + 1) M` of a module which kills relations. This is what makes the
  previous lemma applicable: the levels of the tower do *not* kill relations on their own, only
  after the shift, and the shift is exactly what the quotient presentation supplies.
* `Stacks.ReesAlgebra.sum_eq_zero_of_localizedTower` — and the shifted statement passes to a
  localization of the tower, again without moving the exponent. Chained with the previous lemma
  this is the whole of the uniformity: one exponent on an affine chart, read off the quotient
  presentation of the terms there, serves the sections over every basic open inside it.

## Implementation notes

The lift `μ` is only defined on `K R · M`, so the statement that it carries a submodule
somewhere has to carry the membership proof of the source as an argument; the proof is
irrelevant, so the induction is run on the submodule
`Submodule.map (K R · M).subtype (Submodule.comap μ (L R · M))` of `M`, whose members are
exactly the sections of `K R · M` that `μ` sends into `L R · M`.

`Stacks.ReesAlgebra.KillsRelations` is `Stacks.ReesAlgebra.KillsRelationsHom` at `algebraMap`,
definitionally (`Stacks.ReesAlgebra.killsRelationsHom_algebraMap`), so the two forms are freely
interchangeable and nothing is proved twice.

## References

* [Stacks Project, Tag 0EIC](https://stacks.math.columbia.edu/tag/0EIC)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
* [Stacks Project, Tag 0EH6](https://stacks.math.columbia.edu/tag/0EH6)
-/

@[expose] public noncomputable section

namespace Stacks.ReesAlgebra

universe u v w

section Descend

variable {A : Type u} [CommRing A] {R : Type v} [CommRing R]
  {M : Type w} [AddCommGroup M] [Module R M]

/-- **The lift of a linear functional on `K` shifts the filtration by `K`.**

If `μ` is an `R`-linear map on `K R · M` sending `g · x` to `λ(g) · x` for `g ∈ K`, then `μ`
carries a section of `(K L) R · M` into `L R · M`, for every ideal `L` of `A`. Indeed such a
section is a sum of products `f g • y` with `g ∈ K` and `y ∈ L R · M`, and `μ` sends that
product to `f (λ g) • y`, which stays in `L R · M`. -/
public lemma lift_mem_smul_of_mem_mul_smul (f : A →+* R) (K : Ideal A) (lam : ↥K →ₗ[A] A)
    (μ : ↥(Ideal.map f K • (⊤ : Submodule R M)) →ₗ[R] M)
    (hμ : ∀ (g : A) (hg : g ∈ K) (x : M)
      (hmem : f g • x ∈ Ideal.map f K • (⊤ : Submodule R M)),
      μ ⟨f g • x, hmem⟩ = f (lam ⟨g, hg⟩) • x)
    (L : Ideal A) {z : M}
    (hzKL : z ∈ Ideal.map f (K * L) • (⊤ : Submodule R M))
    (hz : z ∈ Ideal.map f K • (⊤ : Submodule R M)) :
    μ ⟨z, hz⟩ ∈ Ideal.map f L • (⊤ : Submodule R M) := by
  classical
  have hKL : Ideal.map f (K * L) • (⊤ : Submodule R M) =
      Ideal.map f K • (Ideal.map f L • (⊤ : Submodule R M)) := by
    rw [Ideal.map_mul, Submodule.mul_smul]
  have hsub : Ideal.map f K • (Ideal.map f L • (⊤ : Submodule R M)) ≤
      Submodule.map (Ideal.map f K • (⊤ : Submodule R M)).subtype
        (Submodule.comap μ (Ideal.map f L • (⊤ : Submodule R M))) := by
    refine Submodule.smul_le.2 fun c hc y hy => ?_
    refine Submodule.span_induction ?_ ?_ ?_ ?_
      (show c ∈ Ideal.span (f '' (K : Set A)) from hc)
    · rintro b ⟨g, hg, rfl⟩
      have hmem : f g • y ∈ Ideal.map f K • (⊤ : Submodule R M) :=
        Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hg) Submodule.mem_top
      refine ⟨⟨f g • y, hmem⟩, ?_, rfl⟩
      have hv : μ ⟨f g • y, hmem⟩ ∈ Ideal.map f L • (⊤ : Submodule R M) := by
        rw [hμ g hg y hmem]
        exact Submodule.smul_mem _ _ hy
      exact hv
    · rw [zero_smul]
      exact Submodule.zero_mem _
    · intro a b _ _ ha hb
      rw [add_smul]
      exact Submodule.add_mem _ ha hb
    · intro a b _ hb
      rw [smul_eq_mul, mul_smul]
      exact Submodule.smul_mem _ a hb
  obtain ⟨u, hu, hu2⟩ := hsub (hKL ▸ hzKL)
  rwa [show (⟨z, hz⟩ : ↥(Ideal.map f K • (⊤ : Submodule R M))) = u from Subtype.ext hu2.symm]

end Descend

/-! ### Relation-killing along a ring map -/

/-- **A splitting on `I ^ d` kills the relations of a module along a ring map `f : A →+* R`**
when, for every monomial `σ` and every degree `n`, the coefficient map
`Stacks.ReesAlgebra.extendCoeff` of its extension sends a vanishing combination
`∑ₖ f (gₖ) · xₖ = 0` with `gₖ ∈ (I ^ d) ^ n` to a vanishing combination.

This is `Stacks.ReesAlgebra.KillsRelations` with the scalars entering through an explicit ring
map instead of an `Algebra` instance, which is what a construction on a scheme consumes. -/
public def KillsRelationsHom {A : Type*} [CommRing A] {R : Type*} [CommRing R] (f : A →+* R)
    (M : Type*) [AddCommGroup M] [Module R M] (I : Ideal A) {r : ℕ} (d : ℕ)
    (ψ : Fin r → (I ^ d : Ideal A) →ₗ[A] A) : Prop :=
  ∀ (n : ℕ) (σ : Fin r →₀ ℕ) (p : ℕ) (g : Fin p → A)
    (hg : ∀ k, g k ∈ ((I ^ d : Ideal A) ^ n)) (x : Fin p → M),
    (∑ k, f (g k) • x k) = 0 →
    (∑ k, f (extendCoeff I d n ψ σ ⟨g k, hg k⟩) • x k) = 0

section Hom

variable {A : Type u} [CommRing A] {R : Type v} [CommRing R]
  {M : Type w} [AddCommGroup M] [Module R M]

/-- Relation-killing along `algebraMap` is relation-killing in the sense of
`Stacks.ReesAlgebra.KillsRelations`. -/
public lemma killsRelationsHom_algebraMap {B : Type v} [CommRing B] [Algebra A B]
    {N : Type w} [AddCommGroup N] [Module B N] (I : Ideal A) {r : ℕ} (d : ℕ)
    (ψ : Fin r → (I ^ d : Ideal A) →ₗ[A] A) :
    KillsRelationsHom (algebraMap A B) N I d ψ ↔ KillsRelations A B N I d ψ :=
  Iff.rfl

/-- The linear map asserted by relation-killing along a ring map: on `(I ^ d) ^ n R · M` it
sends `f g • x` to `f (Φ(g)_σ) • x`. It is unique by
`Stacks.ReesAlgebra.linearMap_ext_of_smul`. -/
public theorem KillsRelationsHom.exists_linearMap {f : A →+* R} {I : Ideal A} {r d : ℕ}
    {ψ : Fin r → (I ^ d : Ideal A) →ₗ[A] A} (h : KillsRelationsHom f M I d ψ)
    (n : ℕ) (σ : Fin r →₀ ℕ) :
    ∃ μ : ↥(Ideal.map f ((I ^ d : Ideal A) ^ n) • (⊤ : Submodule R M)) →ₗ[R] M,
      ∀ (g : A) (hg : g ∈ ((I ^ d : Ideal A) ^ n)) (x : M)
        (hmem : f g • x ∈ Ideal.map f ((I ^ d : Ideal A) ^ n) • (⊤ : Submodule R M)),
        μ ⟨f g • x, hmem⟩ = f (extendCoeff I d n ψ σ ⟨g, hg⟩) • x :=
  exists_linearMap_of_kills_relations f _ (extendCoeff I d n ψ σ) fun p g hg x => h n σ p g hg x

/-- Relation-killing along a ring map is inherited by a further enlargement of the exponent. -/
public lemma KillsRelationsHom.of_restrictsSplitting {f : A →+* R} {I : Ideal A} {r d e : ℕ}
    {hde : d ≤ e} {ψ : Fin r → (I ^ d : Ideal A) →ₗ[A] A}
    {χ : Fin r → (I ^ e : Ideal A) →ₗ[A] A}
    (h : KillsRelationsHom f M I d ψ) (hres : RestrictsSplitting I hde ψ χ) :
    KillsRelationsHom f M I e χ := by
  intro n σ p g hg x hsum
  have hgd : ∀ k, g k ∈ ((I ^ d : Ideal A) ^ n) := fun k => pow_pow_le_pow_pow I hde n (hg k)
  calc (∑ k, f (extendCoeff I e n χ σ ⟨g k, hg k⟩) • x k)
      = ∑ k, f (extendCoeff I d n ψ σ ⟨g k, hgd k⟩) • x k :=
        Finset.sum_congr rfl fun k _ => by
          rw [extendCoeff_of_restrictsSplitting I hde ψ χ hres n σ (g k) (hg k) (hgd k)]
    _ = 0 := h n σ p g hgd x hsum

/-- **Relation-killing with a shift.**

If the splitting `ψ` on `I ^ d` kills the relations of `M`, then for every ideal `L` of `A` the
coefficients of its extension carry a combination lying in `((I ^ d) ^ n L) R · M` to a
combination lying in `L R · M`. Taking `L = I ^ m` this says: a relation among elements of
`(I ^ d) ^ n` which holds modulo `I ^ (n d + m)` forces the corresponding combination of
coefficients to vanish modulo `I ^ m`.

The exponent `d` does not depend on `L`, which is exactly what [Stacks, Tag 0EH6] needs: one
application of [Stacks, Tag 0EIC] serves every term of the adic system at once. -/
public theorem KillsRelationsHom.sum_mem_smul {f : A →+* R} {I : Ideal A} {r d : ℕ}
    {ψ : Fin r → (I ^ d : Ideal A) →ₗ[A] A} (h : KillsRelationsHom f M I d ψ)
    (n : ℕ) (σ : Fin r →₀ ℕ) (L : Ideal A)
    {p : ℕ} (g : Fin p → A) (hg : ∀ k, g k ∈ ((I ^ d : Ideal A) ^ n)) (x : Fin p → M)
    (hsum : (∑ k, f (g k) • x k) ∈
      Ideal.map f (((I ^ d : Ideal A) ^ n) * L) • (⊤ : Submodule R M)) :
    (∑ k, f (extendCoeff I d n ψ σ ⟨g k, hg k⟩) • x k) ∈
      Ideal.map f L • (⊤ : Submodule R M) := by
  classical
  obtain ⟨μ, hμ⟩ := h.exists_linearMap n σ
  have hterm : ∀ k, f (g k) • x k ∈
      Ideal.map f ((I ^ d : Ideal A) ^ n) • (⊤ : Submodule R M) :=
    fun k => Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ (hg k)) Submodule.mem_top
  have hz : (∑ k, f (g k) • x k) ∈
      Ideal.map f ((I ^ d : Ideal A) ^ n) • (⊤ : Submodule R M) :=
    Submodule.sum_mem _ fun k _ => hterm k
  have hval : μ ⟨∑ k, f (g k) • x k, hz⟩ =
      ∑ k, f (extendCoeff I d n ψ σ ⟨g k, hg k⟩) • x k := by
    have hsplit : (⟨∑ k, f (g k) • x k, hz⟩ :
        ↥(Ideal.map f ((I ^ d : Ideal A) ^ n) • (⊤ : Submodule R M))) =
        ∑ k, (⟨f (g k) • x k, hterm k⟩ :
          ↥(Ideal.map f ((I ^ d : Ideal A) ^ n) • (⊤ : Submodule R M))) :=
      Subtype.ext (by rw [AddSubmonoidClass.coe_finset_sum])
    rw [hsplit, map_sum]
    exact Finset.sum_congr rfl fun k _ => hμ (g k) (hg k) (x k) (hterm k)
  rw [← hval]
  exact lift_mem_smul_of_mem_mul_smul f ((I ^ d : Ideal A) ^ n)
    (extendCoeff I d n ψ σ) μ hμ L hsum hz

/-- **Relation-killing descends along a jointly injective family of scalar-compatible additive
maps.**

The targets may be modules over any rings, the only requirement being that each `π i` carries
`f a • x` to `f' i a • π i x`. Restriction maps of a sheaf of modules, germ maps and the
projections of an inverse limit are all of this shape, and in each case joint injectivity is
the separatedness that the source of [Stacks, Tag 0EH6] uses without comment. -/
public lemma killsRelationsHom_of_compat (f : A →+* R) {I : Ideal A} {r d : ℕ}
    {ψ : Fin r → (I ^ d : Ideal A) →ₗ[A] A}
    {ι : Type*} {R' : ι → Type*} [∀ i, CommRing (R' i)]
    {M' : ι → Type*} [∀ i, AddCommGroup (M' i)] [∀ i, Module (R' i) (M' i)]
    (f' : ∀ i, A →+* R' i) (π : ∀ i, M →+ M' i)
    (hπ : ∀ (i : ι) (a : A) (x : M), π i (f a • x) = f' i a • π i x)
    (hinj : ∀ x : M, (∀ i, π i x = 0) → x = 0)
    (h : ∀ i, KillsRelationsHom (f' i) (M' i) I d ψ) :
    KillsRelationsHom f M I d ψ := by
  intro n σ p g hg x hsum
  refine hinj _ fun i => ?_
  have hmap : ∀ (c : Fin p → A) (y : Fin p → M),
      π i (∑ k, f (c k) • y k) = ∑ k, f' i (c k) • π i (y k) := by
    intro c y
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => hπ i (c k) (y k)
  have h1 : (∑ k, f' i (g k) • π i (x k)) = 0 := by
    rw [← hmap, hsum, map_zero]
  exact (hmap (fun k => extendCoeff I d n ψ σ ⟨g k, hg k⟩) x).trans
    (h i n σ p g hg (fun k => π i (x k)) h1)

/-- **Relation-killing passes back along a single injective scalar-compatible additive map.**
The one-map case of `Stacks.ReesAlgebra.killsRelationsHom_of_compat`, which is what an
isomorphism of modules over different rings supplies. -/
public lemma killsRelationsHom_of_injective (f : A →+* R) {I : Ideal A} {r d : ℕ}
    {ψ : Fin r → (I ^ d : Ideal A) →ₗ[A] A}
    {R' : Type*} [CommRing R'] {M' : Type*} [AddCommGroup M'] [Module R' M']
    (f' : A →+* R') (π : M →+ M')
    (hπ : ∀ (a : A) (x : M), π (f a • x) = f' a • π x)
    (hinj : Function.Injective π) (h : KillsRelationsHom f' M' I d ψ) :
    KillsRelationsHom f M I d ψ :=
  killsRelationsHom_of_compat f (fun _ : Unit => f') (fun _ => π) (fun _ => hπ)
    (fun x hx => hinj (by rw [hx (), map_zero])) fun _ => h

/-- A vanishing combination in a localization lifts, after a common denominator, to a vanishing
combination upstairs. -/
private lemma exists_lift_of_sum_smul_eq_zero {P Q : Type*} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] (S : Submonoid R) (loc : P →ₗ[R] Q) [IsLocalizedModule S loc]
    {p : ℕ} (c : Fin p → R) (z : Fin p → Q) (h : (∑ k, c k • z k) = 0) :
    ∃ (t : S) (y : Fin p → P), (∀ k, (t : R) • z k = loc (y k)) ∧ (∑ k, c k • y k) = 0 := by
  classical
  choose w hw using fun k => IsLocalizedModule.surj S loc (z k)
  set t₀ : S := ∏ k, (w k).2 with ht₀
  set y₀ : Fin p → P :=
    fun k => ((∏ j ∈ Finset.univ.erase k, (w j).2 : S) : R) • (w k).1 with hy₀
  have hsplit : ∀ k, (t₀ : R) • z k = loc (y₀ k) := by
    intro k
    have hprod : (∏ j ∈ Finset.univ.erase k, (w j).2) * (w k).2 = t₀ := by
      rw [ht₀, mul_comm]
      exact Finset.mul_prod_erase Finset.univ (fun j => (w j).2) (Finset.mem_univ k)
    have hw' : ((w k).2 : R) • z k = loc (w k).1 := by
      rw [← Submonoid.smul_def]; exact hw k
    rw [hy₀, map_smul, ← hw', ← mul_smul, ← Submonoid.coe_mul, hprod]
  have hzero : loc (∑ k, c k • y₀ k) = 0 := by
    rw [map_sum, ← smul_zero (t₀ : R), ← h, Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_smul, ← hsplit k, smul_comm]
  obtain ⟨u, hu⟩ := (IsLocalizedModule.eq_zero_iff (S := S) (f := loc)).1 hzero
  refine ⟨u * t₀, fun k => (u : R) • y₀ k, fun k => ?_, ?_⟩
  · rw [Submonoid.coe_mul, mul_smul, hsplit k]
    exact (map_smul loc (u : R) (y₀ k)).symm
  · rw [Submonoid.smul_def, Finset.smul_sum] at hu
    exact Eq.trans (Finset.sum_congr rfl fun k _ => smul_comm (c k) (u : R) (y₀ k)) hu

/-- A combination in a localization vanishes if its common-denominator lift vanishes upstairs. -/
private lemma sum_smul_eq_zero_of_lift {P Q : Type*} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] (S : Submonoid R) (loc : P →ₗ[R] Q) [IsLocalizedModule S loc]
    {p : ℕ} (c : Fin p → R) (a : Fin p → Q) (b : Fin p → P) (t : S)
    (ht : ∀ k, (t : R) • a k = loc (b k)) (h : (∑ k, c k • b k) = 0) : (∑ k, c k • a k) = 0 := by
  refine IsLocalizedModule.smul_injective loc t ?_
  change (t : S) • _ = (t : S) • (0 : Q)
  rw [Submonoid.smul_def, Submonoid.smul_def, smul_zero, Finset.smul_sum]
  calc (∑ k, (t : R) • c k • a k) = loc (∑ k, c k • b k) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun k _ => by rw [smul_comm, ht k, map_smul]
    _ = 0 := by rw [h, map_zero]

/-- **Relation-killing passes to a localization of the module.**

A relation in `M'` becomes, after clearing the denominators of its terms and then the one
denominator which says the cleared relation already holds, a relation in `M`; relation-killing
there gives a combination of coefficients which dies in `M'` after multiplication by a common
denominator, hence dies.

The exponent does not move, so a single exponent obtained on an affine scheme serves all of its
affine opens and all of its stalks at once — the sections of a quasi-coherent sheaf over a
smaller open, and its germs, being localizations of the sections over the whole. -/
public lemma KillsRelationsHom.of_isLocalizedModule {M' : Type*} [AddCommGroup M']
    [Module R M'] (S : Submonoid R) (loc : M →ₗ[R] M') [IsLocalizedModule S loc]
    {f : A →+* R} {I : Ideal A} {r d : ℕ} {ψ : Fin r → (I ^ d : Ideal A) →ₗ[A] A}
    (h : KillsRelationsHom f M I d ψ) :
    KillsRelationsHom f M' I d ψ := by
  intro n σ p g hg y hsum
  obtain ⟨t, z, ht, hz⟩ := exists_lift_of_sum_smul_eq_zero S loc (fun k => f (g k)) y hsum
  exact sum_smul_eq_zero_of_lift S loc _ y z t ht (h n σ p g hg z hz)

/-- **Relation-killing passes to a module which injects into a tower that kills relations after
a shift.**

Let `π m : M ⟶ P m` be jointly injective and compatible with maps `ρ m k : P (m + k) ⟶ P m`.
Suppose that at each level a relation in degree `n` among elements of `(I ^ d) ^ n`, holding in
`P (m + n d)`, forces the combination of coefficients to vanish after transport to `P m`. Then
`M` kills relations outright.

For [Stacks, Tag 0EH6] the module is `Γ(lim F_n, W)` and the tower is `Γ(F_m, W)`: a relation
in the limit is a relation at every level, and the shifted statement — available uniformly in
`m` by `Stacks.ReesAlgebra.KillsRelationsHom.sum_mem_smul` — gives the vanishing of the
coefficients one level at a time. -/
public lemma killsRelationsHom_of_shift (f : A →+* R) (I : Ideal A) {r : ℕ} (d : ℕ)
    (ψ : Fin r → (I ^ d : Ideal A) →ₗ[A] A)
    {P : ℕ → Type*} [∀ m, AddCommGroup (P m)] [∀ m, Module R (P m)]
    (π : ∀ m, M →ₗ[R] P m) (ρ : ∀ m k, P (m + k) →ₗ[R] P m)
    (hcomp : ∀ m k (y : M), ρ m k (π (m + k) y) = π m y)
    (hinj : ∀ y : M, (∀ m, π m y = 0) → y = 0)
    (hshift : ∀ (n : ℕ) (σ : Fin r →₀ ℕ) (m p : ℕ) (g : Fin p → A)
      (hg : ∀ k, g k ∈ ((I ^ d : Ideal A) ^ n)) (y : Fin p → P (m + n * d)),
      (∑ k, f (g k) • y k) = 0 →
      (∑ k, f (extendCoeff I d n ψ σ ⟨g k, hg k⟩) • ρ m (n * d) (y k)) = 0) :
    KillsRelationsHom f M I d ψ := by
  intro n σ p g hg x hsum
  refine hinj _ fun m => ?_
  have hlin : ∀ (c : Fin p → R) (y : Fin p → M) (l : ℕ),
      π l (∑ k, c k • y k) = ∑ k, c k • π l (y k) := by
    intro c y l
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => map_smul _ _ _
  have hrel : (∑ k, f (g k) • π (m + n * d) (x k)) = 0 := by
    rw [← hlin, hsum, map_zero]
  have hout := hshift n σ m p g hg (fun k => π (m + n * d) (x k)) hrel
  rw [hlin]
  refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) hout
  rw [hcomp]

/-- **The shifted statement, from a quotient presentation of the tower.**

Suppose each level of a tower `P` is the quotient `M / I ^ (m + 1) M` of a single module `M`
which kills relations, compatibly with the transition maps `ρ`. Then a relation in
`P (m + n d)` forces the combination of coefficients to vanish in `P m`, which is the
hypothesis `hshift` of `Stacks.ReesAlgebra.killsRelationsHom_of_shift`.

This is the descent [Stacks, Tag 0EH6] performs when it reads the maps
`Φ^n_m : I ^ (n c) F_m ⟶ ⨁_{|e| = n} F_{m - n c}` off the single map `Φ_N`: lift the relation
to `M`, where it then holds modulo `I ^ (m + n d + 1)`, and apply
`Stacks.ReesAlgebra.KillsRelationsHom.sum_mem_smul` with `L = I ^ (m + 1)`. The exponent `d`
does not move, so one application of [Stacks, Tag 0EIC] serves every level. -/
public lemma sum_eq_zero_of_quotientTower (f : A →+* R) {I : Ideal A} {r d : ℕ}
    {ψ : Fin r → (I ^ d : Ideal A) →ₗ[A] A} (h : KillsRelationsHom f M I d ψ)
    {P : ℕ → Type*} [∀ m, AddCommGroup (P m)] [∀ m, Module R (P m)]
    (q : ∀ m, M →ₗ[R] P m) (ρ : ∀ m k, P (m + k) →ₗ[R] P m)
    (hsurj : ∀ m, Function.Surjective (q m))
    (hker : ∀ m, LinearMap.ker (q m) = Ideal.map f (I ^ (m + 1)) • (⊤ : Submodule R M))
    (hcomp : ∀ m k (z : M), ρ m k (q (m + k) z) = q m z)
    (n : ℕ) (σ : Fin r →₀ ℕ) (m p : ℕ) (g : Fin p → A)
    (hg : ∀ k, g k ∈ ((I ^ d : Ideal A) ^ n)) (y : Fin p → P (m + n * d))
    (hrel : (∑ k, f (g k) • y k) = 0) :
    (∑ k, f (extendCoeff I d n ψ σ ⟨g k, hg k⟩) • ρ m (n * d) (y k)) = 0 := by
  classical
  choose x hx using fun k => hsurj (m + n * d) (y k)
  have hidx : ((I ^ d : Ideal A) ^ n) * I ^ (m + 1) = I ^ (m + n * d + 1) := by
    rw [← pow_mul, ← pow_add]
    exact congrArg (fun e => I ^ e) (by ring)
  have hzero : q (m + n * d) (∑ k, f (g k) • x k) = 0 := by
    rw [map_sum]
    refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) hrel
    rw [map_smul, hx k]
  have hmem : (∑ k, f (g k) • x k) ∈
      Ideal.map f (((I ^ d : Ideal A) ^ n) * I ^ (m + 1)) • (⊤ : Submodule R M) := by
    rw [hidx, ← hker (m + n * d)]
    exact hzero
  have hcoeff := h.sum_mem_smul n σ (I ^ (m + 1)) g hg x hmem
  rw [← hker m] at hcoeff
  have hq : (∑ k, f (extendCoeff I d n ψ σ ⟨g k, hg k⟩) • q m (x k)) = 0 := by
    have := LinearMap.mem_ker.mp hcoeff
    rwa [map_sum, Finset.sum_congr rfl (fun k _ => map_smul (q m) _ (x k))] at this
  refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) hq
  rw [← hx k, hcomp]

/-- **The shifted statement passes to a localization of the tower.**

If each level `Q m` is a localization of `P m` at one and the same submonoid `S`, compatibly
with the transition maps, and the shifted statement holds for `P`, then it holds for `Q`. The
exponent does not move, which is what lets the single exponent found on an affine chart serve
every basic open inside it: the sections of the terms over a basic open are the localizations of
their sections over the chart, while the sections of the *limit* are not. -/
public lemma sum_eq_zero_of_localizedTower (f : A →+* R) (I : Ideal A) {r : ℕ} (d : ℕ)
    (ψ : Fin r → (I ^ d : Ideal A) →ₗ[A] A)
    {P : ℕ → Type*} [∀ m, AddCommGroup (P m)] [∀ m, Module R (P m)]
    {Q : ℕ → Type*} [instQA : ∀ m, AddCommGroup (Q m)] [instQM : ∀ m, Module R (Q m)]
    (ρP : ∀ m k, P (m + k) →ₗ[R] P m) (ρQ : ∀ m k, Q (m + k) →ₗ[R] Q m)
    (S : Submonoid R) (loc : ∀ m, P m →ₗ[R] Q m) [instLoc : ∀ m, IsLocalizedModule S (loc m)]
    (hcomm : ∀ m k (y : P (m + k)), loc m (ρP m k y) = ρQ m k (loc (m + k) y))
    (hP : ∀ (n : ℕ) (σ : Fin r →₀ ℕ) (m p : ℕ) (g : Fin p → A)
      (hg : ∀ k, g k ∈ ((I ^ d : Ideal A) ^ n)) (y : Fin p → P (m + n * d)),
      (∑ k, f (g k) • y k) = 0 →
      (∑ k, f (extendCoeff I d n ψ σ ⟨g k, hg k⟩) • ρP m (n * d) (y k)) = 0)
    (n : ℕ) (σ : Fin r →₀ ℕ) (m p : ℕ) (g : Fin p → A)
    (hg : ∀ k, g k ∈ ((I ^ d : Ideal A) ^ n)) (z : Fin p → Q (m + n * d))
    (hrel : (∑ k, f (g k) • z k) = 0) :
    (∑ k, f (extendCoeff I d n ψ σ ⟨g k, hg k⟩) • ρQ m (n * d) (z k)) = 0 := by
  obtain ⟨t, y, ht, hy⟩ :=
    exists_lift_of_sum_smul_eq_zero S (loc (m + n * d)) (fun k => f (g k)) z hrel
  refine sum_smul_eq_zero_of_lift S (loc m) _ _ _ t (fun k => ?_)
    (hP n σ m p g hg y hy)
  rw [← map_smul, ht k, hcomm]

end Hom

/-- **The relation-killing form of [Stacks, Tag 0EIC] along a ring map.** After enlarging `c`
to a `d` and adjusting the splitting accordingly, the coefficient maps
`Stacks.ReesAlgebra.extendCoeff` of the extension kill every relation among the elements of
`(I ^ d) ^ n` acting on a finite module over a Noetherian ring receiving `A`.

The ring map is explicit because the ring the geometry supplies — the sections over an open, or
the `I`-adic completion of them — carries no `Algebra A` instance. -/
public theorem exists_extendLinearMaps_killsRelationsHom
    (A : Type u) (B : Type v) (N : Type w)
    [CommRing A] [CommRing B] [IsNoetherianRing B]
    [AddCommGroup N] [Module B N] [Module.Finite B N]
    (f : A →+* B) (I : Ideal A) {r : ℕ} (gen : Fin r → A)
    (hgen : I = Ideal.span (Set.range gen))
    (c : ℕ) (hc : 1 ≤ c)
    (φ : Fin r → (I ^ c : Ideal A) →ₗ[A] A)
    (hφ : ∀ g : (I ^ c : Ideal A), (∑ j, gen j * φ j g) = (g : A)) :
    ∃ d : ℕ, ∃ hcd : c ≤ d, ∃ ψ : Fin r → (I ^ d : Ideal A) →ₗ[A] A,
      RestrictsSplitting I hcd φ ψ ∧
      (∀ g : (I ^ d : Ideal A), (∑ j, gen j * ψ j g) = (g : A)) ∧
      KillsRelationsHom f N I d ψ := by
  let : Algebra A B := f.toAlgebra
  obtain ⟨d, hcd, ψ, hres, hsplit, hkill⟩ :=
    exists_extendLinearMaps_kills_relations A B N I gen hgen c hc φ hφ
  exact ⟨d, hcd, ψ, hres, hsplit, hkill⟩

/-- **One exponent for finitely many modules at once.**

Applying [Stacks, Tag 0EIC] to one module enlarges `c`; applying it again to the result enlarges
it further, and `Stacks.ReesAlgebra.KillsRelationsHom.of_restrictsSplitting` keeps what the
earlier applications proved. So for a *finite* family of finite modules over Noetherian rings
receiving `A` there is a single enlargement `d` of `c`, with a single adjusted splitting `ψ`,
killing the relations of every member of the family.

This is the step of [Stacks, Tag 0EH6] that passes from an affine chart to a general Noetherian
scheme. Such a scheme is covered by finitely many affine opens, each of which supplies an
exponent by `Stacks.Coherent.exists_killsRelationsHom_globalSections_base`, and taking the
maximum of them is legitimate precisely because the family is finite — which is why the
hypothesis here is a `Finset` and not an arbitrary index type. -/
public theorem exists_extendLinearMaps_killsRelationsHom_finset
    {A : Type u} [CommRing A] {ι : Type*} {B : ι → Type v} [∀ i, CommRing (B i)]
    [∀ i, IsNoetherianRing (B i)] {N : ι → Type w} [∀ i, AddCommGroup (N i)]
    [∀ i, Module (B i) (N i)] [∀ i, Module.Finite (B i) (N i)] (f : ∀ i, A →+* B i)
    (s : Finset ι) (I : Ideal A) {r : ℕ} (gen : Fin r → A)
    (hgen : I = Ideal.span (Set.range gen)) (c : ℕ) (hc : 1 ≤ c)
    (φ : Fin r → (I ^ c : Ideal A) →ₗ[A] A)
    (hφ : ∀ g : (I ^ c : Ideal A), (∑ j, gen j * φ j g) = (g : A)) :
    ∃ d : ℕ, ∃ hcd : c ≤ d, ∃ ψ : Fin r → (I ^ d : Ideal A) →ₗ[A] A,
      RestrictsSplitting I hcd φ ψ ∧
      (∀ g : (I ^ d : Ideal A), (∑ j, gen j * ψ j g) = (g : A)) ∧
      ∀ i ∈ s, KillsRelationsHom (f i) (N i) I d ψ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨c, le_rfl, φ, fun _ _ _ => rfl, hφ, by simp⟩
  | insert a t _ha ih =>
      obtain ⟨d, hcd, ψ, hres, hsplit, hkill⟩ := ih
      obtain ⟨e, hde, χ, hres', hsplit', hkill'⟩ :=
        exists_extendLinearMaps_killsRelationsHom A (B a) (N a) (f a) I gen hgen d
          (hc.trans hcd) ψ hsplit
      refine ⟨e, hcd.trans hde, χ, hres.trans hres', hsplit', fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hit
      · exact hkill'
      · exact (hkill i hit).of_restrictsSplitting hres'

/-- **Relation-killing with a shift**, for a module over an `A`-algebra. See
`Stacks.ReesAlgebra.KillsRelationsHom.sum_mem_smul`. -/
public theorem KillsRelations.sum_mem_smul {A : Type u} {B : Type v} {N : Type w}
    [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup N] [Module B N]
    {I : Ideal A} {r d : ℕ} {ψ : Fin r → (I ^ d : Ideal A) →ₗ[A] A}
    (h : KillsRelations A B N I d ψ) (n : ℕ) (σ : Fin r →₀ ℕ) (L : Ideal A)
    {p : ℕ} (g : Fin p → A) (hg : ∀ k, g k ∈ ((I ^ d : Ideal A) ^ n)) (x : Fin p → N)
    (hsum : (∑ k, algebraMap A B (g k) • x k) ∈
      Ideal.map (algebraMap A B) (((I ^ d : Ideal A) ^ n) * L) • (⊤ : Submodule B N)) :
    (∑ k, algebraMap A B (extendCoeff I d n ψ σ ⟨g k, hg k⟩) • x k) ∈
      Ideal.map (algebraMap A B) L • (⊤ : Submodule B N) :=
  KillsRelationsHom.sum_mem_smul
    ((killsRelationsHom_algebraMap (B := B) (N := N) I d ψ).2 h) n σ L g hg x hsum

end Stacks.ReesAlgebra

end
