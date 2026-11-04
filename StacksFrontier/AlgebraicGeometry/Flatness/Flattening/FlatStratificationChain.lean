module

public import StacksFrontier.AlgebraicGeometry.GenericFlatness.FlatStratificationAffine
public import StacksFrontier.RingTheory.Flat.BaseChangeFlatLocalizedModule
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The generic flatness stratification of Stacks 0ASY as a chain of ideals

The proof of Stacks 05U9 runs an induction over a generic flatness stratification

`Spec A = S₀ ⊇ S₁ ⊇ ⋯ ⊇ S_t = ∅`

of the base of a module `N`, where `S_i` is cut out by a finitely generated ideal `K_i ⊆ A`, the
first of which is contained in the nilradical, and where `N` is flat over each locally closed
stratum `S_i ∖ S_{i+1}`. This file packages that data as a structure
`Stacks.FlatStratification`, which `AlgebraicGeometry.exists_flat_stratification_ideals`
produces, and provides the two operations the induction needs.

* `Stacks.FlatStratification.quotient` **reindexes a stratification onto a quotient**: for an
  ideal `E ⊆ A` and an index `s ≤ t` whose ideal `K_s` becomes nilpotent in `A ⧸ E`, the ideals
  `K_s, K_{s+1}, …, K_t` extended to `A ⧸ E` are a stratification of `N ⧸ EN` over `A ⧸ E` of
  length `t - s`. Shortening the stratification is what makes the source's induction on `t` turn
  over: Claim 1 at `i > 0` is the proposition over `A ⧸ K_i`, where `s = i` and `E = K_i`, and
  "flatness modulo the powers of `J`" is the proposition over `A ⧸ Jⁿ`, where `s = 1` and
  `E ⊇ K₁ⁿ`.

* `Stacks.strataClosureIdeal` is **the ideal `J_i` of the source**: the scheme theoretic closure
  of the stratum `S_i ∖ S_{i+1}` inside `Spec A`. The stratum is the union of the basic opens
  `D(a) ∩ S_i` for `a` in a generating set of `K_{i+1}`, so the closure is cut out by the
  elements of `A` which die in each `(A ⧸ K_i)_a`.

## Main definitions

* `Stacks.FlatStratification`: the chain of ideals with its flatness clause.
* `Stacks.strataClosureIdeal`: the ideal of the scheme theoretic closure of a stratum.

## Main results

* `Stacks.exists_flatStratification`: Stacks 0ASY in this shape.
* `Stacks.exists_flatStratification_of_isLocalizedModule`: the same for a module which is only a
  localization of a finitely presented one, which is the shape Situation 0AT0 presents.
* `Stacks.FlatStratification.quotient`: the reindexing onto a quotient.
* `Stacks.le_strataClosureIdeal` and `Stacks.strataClosureIdeal_le_of_isPrime`: the closure
  ideal lies between `K_i` and every prime of the stratum. The second is what makes every prime
  of `A` contain a flattening ideal once Claim 1 is known.
* `Stacks.eq_zero_of_forall_pow_mul_eq_zero_quotient`: the stratum is scheme theoretically dense
  in the closed subscheme its closure ideal cuts out. This is the hypothesis `hdense` of
  `Stacks.flat_of_least_flattening_of_flat_away`, over `A ⧸ J_i`.

## Implementation notes

The flatness clause is the one of `AlgebraicGeometry.exists_flat_stratification_ideals`:
flatness of `L ⊗[A] N` for every localization `L` of `A ⧸ K_i` away from the image of an
`a ∈ K_{i+1}`. Stating the base change over `A` rather than over `A ⧸ K_i` is what makes the
reindexing possible: a localization of a *quotient* of `A ⧸ K_i` is not a localization of
`A ⧸ K_i`, so the clause is reached there by base change along `(A ⧸ K_i)_a → L`, and
`L ⊗[A] N` is insensitive to which quotient of `A` the ideals are read in.
`AlgebraicGeometry.flat_tensorQuotient_of_flat_tensor` converts to the form over `A ⧸ E` when a
consumer wants it.

The base ring `A` and the module `N` are in independent universes, and so is the index type of
the family cutting out a stratum. Only the localizations `L` of the flatness clause are tied to
the universe of `A`, which is where they live anyway: the model a consumer reaches for is
`Localization.Away (Ideal.Quotient.mk (ideal i.castSucc) a)`. The proof of Stacks 05U9 needs the
split, because the base there is the local ring `A` of Situation 0AT0 while the module is one
over a localized polynomial algebra over `A`, in a larger universe; the matching freedom on the
side that produces a stratification is in
`AlgebraicGeometry.exists_flat_stratification_ideals`, and on the side that consumes one it is
already in `Stacks.flat_of_least_flattening_of_flat_away`.

## References

* [Stacks Project, Tag 0ASY](https://stacks.math.columbia.edu/tag/0ASY)
* [Stacks Project, Tag 05U9](https://stacks.math.columbia.edu/tag/05U9)
-/

@[expose] public section

open TensorProduct

universe u v w

namespace Stacks

/-- **The generic flatness stratification of Stacks 0ASY, read as a chain of ideals of `A`.**
The ideal `ideal i` cuts out the closed subscheme `S_i` of `Spec A`; the chain ascends because
the subschemes descend, `ideal 0 ≤ nilradical A` says `S₀ ⊆ Spec A` is a thickening, and
`ideal (Fin.last t) = ⊤` says `S_t = ∅`. The module `N` is flat over each stratum
`S_i ∖ S_{i+1}`, read on the affine basic opens covering it. -/
structure FlatStratification (A : Type u) [CommRing A] (N : Type v) [AddCommGroup N]
    [Module A N] (t : ℕ) where
  /-- The ideal cutting out the `i`-th closed subscheme of the stratification. -/
  ideal : Fin (t + 1) → Ideal A
  /-- The first closed subscheme is a thickening of `Spec A`. -/
  base_le_nilradical : ideal 0 ≤ nilradical A
  /-- Each closed subscheme is cut out by a finitely generated ideal. -/
  fg : ∀ i, (ideal i).FG
  /-- The closed subschemes descend, so the ideals ascend. -/
  le_succ : ∀ i : Fin t, ideal i.castSucc ≤ ideal i.succ
  /-- The last closed subscheme is empty. -/
  eq_top : ideal (Fin.last t) = ⊤
  /-- `N` is flat over the stratum `S_i ∖ S_{i+1}`, read on the affine basic opens
  `(A ⧸ ideal i)_a` for `a ∈ ideal (i + 1)` which cover it. -/
  flat_away : ∀ (i : Fin t) (a : A), a ∈ ideal i.succ →
    ∀ (L : Type u) [CommRing L] [Algebra A L] [Algebra (A ⧸ ideal i.castSucc) L]
      [IsScalarTower A (A ⧸ ideal i.castSucc) L]
      [IsLocalization.Away (Ideal.Quotient.mk (ideal i.castSucc) a) L],
      Module.Flat L (L ⊗[A] N)

/-- **Stacks 0ASY as a `Stacks.FlatStratification`.** A finitely presented module over an
algebra of finite presentation carries a generic flatness stratification of its base.

This carries no tag: 0ASY is carried by `AlgebraicGeometry.exists_flat_stratification`, of which
`AlgebraicGeometry.exists_flat_stratification_ideals` is a restatement and this is a
repackaging. -/
@[ega "IV 6.9.3" "special case"]
theorem exists_flatStratification (A : Type u) [CommRing A] (B : Type u) [CommRing B]
    [Algebra A B] [Algebra.FinitePresentation A B] (N : Type v) [AddCommGroup N] [Module B N]
    [Module A N] [IsScalarTower A B N] [Module.FinitePresentation B N] :
    ∃ t : ℕ, Nonempty (FlatStratification A N t) := by
  obtain ⟨t, K, h0, hfg, hmono, htop, hflat⟩ :=
    AlgebraicGeometry.exists_flat_stratification_ideals (A := A) (B := B) N
  refine ⟨t, ⟨{ ideal := K
                base_le_nilradical := h0
                fg := hfg
                le_succ := hmono
                eq_top := htop
                flat_away := hflat }⟩⟩

/-- **Stacks 0ASY for a module which is a localization of a finitely presented one.** Let `B` be
an algebra of finite presentation over `A`, let `N₀` be a finitely presented `B`-module and let
`N` be the localization of `N₀` at a multiplicative subset `S` of `B`. Then `A` carries a
generic flatness stratification of `N`: the one of `N₀`, with its flatness clause transported
along the localization.

`Stacks.exists_flatStratification` does not apply to `N` directly, because `N` is a module over
`S⁻¹B`, which is not of finite presentation over `A`. This is the form the proof of Stacks 05U9
needs in Situation 0AT0, where the algebra is a localization at a prime of a polynomial algebra
`B = A[x₁, …, x_n]` and the module is a localization of a finitely presented `B`-module
(`AlgebraicGeometry.PureSpreadout.exists_finitePresentation_isLocalizedModule`): the
stratification is produced over the polynomial algebra, which *is* of finite presentation, and
`Module.Flat.tensor_of_isLocalizedModule_of_tower` moves the flatness clause
`Module.Flat L (L ⊗[A] N₀)` of each stratum to `Module.Flat L (L ⊗[A] N)`.

This carries no tag, for the reason given at `Stacks.exists_flatStratification`. -/
@[ega "IV 6.9.3" "special case"]
theorem exists_flatStratification_of_isLocalizedModule (A : Type u) [CommRing A] (B : Type u)
    [CommRing B] [Algebra A B] [Algebra.FinitePresentation A B] (N₀ : Type v) [AddCommGroup N₀]
    [Module B N₀] [Module A N₀] [IsScalarTower A B N₀] [Module.FinitePresentation B N₀]
    (N : Type w) [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    (S : Submonoid B) (φ : N₀ →ₗ[B] N) [IsLocalizedModule S φ] :
    ∃ t : ℕ, Nonempty (FlatStratification A N t) := by
  obtain ⟨t, ⟨T⟩⟩ := exists_flatStratification A B N₀
  refine ⟨t, ⟨{ ideal := T.ideal
                base_le_nilradical := T.base_le_nilradical
                fg := T.fg
                le_succ := T.le_succ
                eq_top := T.eq_top
                flat_away := fun i a ha L _ _ _ _ _ =>
                  Module.Flat.tensor_of_isLocalizedModule_of_tower S φ
                    (T.flat_away i a ha L) }⟩⟩

/-- **Base change of the flatness clause along a map of localizations.** If `L₀` is a
localization of `A ⧸ K` away from the image of `a` and `L` is any `A ⧸ K`-algebra in which that
image is invertible, flatness of `L₀ ⊗[A] N` over `L₀` gives flatness of `L ⊗[A] N` over `L`.

This is what lets a stratification be read on a quotient: a localization of a quotient of
`A ⧸ K` is not a localization of `A ⧸ K`, but it does receive the localization `L₀`. -/
theorem flat_tensor_of_localization_away {A : Type u} [CommRing A] {N : Type v} [AddCommGroup N]
    [Module A N] (K : Ideal A) (a : A)
    (L₀ : Type u) [CommRing L₀] [Algebra A L₀] [Algebra (A ⧸ K) L₀]
    [IsScalarTower A (A ⧸ K) L₀] [IsLocalization.Away (Ideal.Quotient.mk K a) L₀]
    (L : Type u) [CommRing L] [Algebra A L] [Algebra (A ⧸ K) L] [IsScalarTower A (A ⧸ K) L]
    (hunit : IsUnit (algebraMap (A ⧸ K) L (Ideal.Quotient.mk K a)))
    (h : Module.Flat L₀ (L₀ ⊗[A] N)) :
    Module.Flat L (L ⊗[A] N) := by
  let : Algebra L₀ L := (IsLocalization.lift
      (M := Submonoid.powers (Ideal.Quotient.mk K a)) (S := L₀)
      (g := algebraMap (A ⧸ K) L) (fun y => by
        obtain ⟨n, hn⟩ := y.2
        rw [← hn, map_pow]
        exact hunit.pow n)).toAlgebra
  have : IsScalarTower A L₀ L := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply A (A ⧸ K) L₀, IsScalarTower.algebraMap_apply A (A ⧸ K) L]
    exact (IsLocalization.lift_eq _ _).symm
  have := h
  exact Module.Flat.of_linearEquiv
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A L₀ L L N).symm

/-- **The flatness clause of a stratification, read over a quotient.** Let `K ⊆ K₁` be the two
ideals of a stratum, let `E` be any ideal of `A`, and suppose `N` is flat over every
localization of `A ⧸ K` away from an element of `K₁`. Then `N ⧸ EN` is flat over every
localization of `(A ⧸ E) ⧸ KE` away from an element of the extension of `K₁`. -/
theorem flat_tensorQuotient_of_flat_away {A : Type u} [CommRing A] {N : Type v} [AddCommGroup N]
    [Module A N] (E K K₁ : Ideal A) (a' : A ⧸ E) (ha' : a' ∈ K₁.map (Ideal.Quotient.mk E))
    (hK : ∀ a ∈ K₁, ∀ (L₀ : Type u) [CommRing L₀] [Algebra A L₀] [Algebra (A ⧸ K) L₀]
      [IsScalarTower A (A ⧸ K) L₀] [IsLocalization.Away (Ideal.Quotient.mk K a) L₀],
      Module.Flat L₀ (L₀ ⊗[A] N))
    (L : Type u) [CommRing L] [Algebra (A ⧸ E) L]
    [Algebra ((A ⧸ E) ⧸ K.map (Ideal.Quotient.mk E)) L]
    [IsScalarTower (A ⧸ E) ((A ⧸ E) ⧸ K.map (Ideal.Quotient.mk E)) L]
    [IsLocalization.Away (Ideal.Quotient.mk (K.map (Ideal.Quotient.mk E)) a') L] :
    Module.Flat L (L ⊗[A ⧸ E] (N ⧸ (E • (⊤ : Submodule A N)))) := by
  obtain ⟨a, ha, hamk⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp ha'
  let : Algebra A L := ((algebraMap (A ⧸ E) L).comp (algebraMap A (A ⧸ E))).toAlgebra
  have : IsScalarTower A (A ⧸ E) L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hcomm : ∀ x : A, algebraMap A L x = algebraMap ((A ⧸ E) ⧸ K.map (Ideal.Quotient.mk E)) L
      (Ideal.Quotient.mk (K.map (Ideal.Quotient.mk E)) (Ideal.Quotient.mk E x)) := fun x =>
    (IsScalarTower.algebraMap_apply (A ⧸ E) ((A ⧸ E) ⧸ K.map (Ideal.Quotient.mk E)) L
      (Ideal.Quotient.mk E x)).trans (by rw [Ideal.Quotient.algebraMap_eq])
  have hkill : ∀ x ∈ K, algebraMap A L x = 0 := fun x hx => by
    rw [hcomm, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hx), map_zero]
  let : Algebra (A ⧸ K) L := (Ideal.Quotient.lift K (algebraMap A L) hkill).toAlgebra
  have : IsScalarTower A (A ⧸ K) L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hunit : IsUnit (algebraMap (A ⧸ K) L (Ideal.Quotient.mk K a)) := by
    have h4 : algebraMap (A ⧸ K) L (Ideal.Quotient.mk K a) =
        algebraMap ((A ⧸ E) ⧸ K.map (Ideal.Quotient.mk E)) L
          (Ideal.Quotient.mk (K.map (Ideal.Quotient.mk E)) a') := by
      rw [← hamk]
      exact hcomm a
    rw [h4]
    exact IsLocalization.Away.algebraMap_isUnit _
  exact AlgebraicGeometry.flat_tensorQuotient_of_flat_tensor E N
    (flat_tensor_of_localization_away K a (Localization.Away (Ideal.Quotient.mk K a)) L hunit
      (hK a ha (Localization.Away (Ideal.Quotient.mk K a))))

namespace FlatStratification

variable {A : Type u} [CommRing A] {N : Type v} [AddCommGroup N] [Module A N] {t : ℕ}

/-- The chain of ideals of a stratification ascends. -/
theorem monotone (S : FlatStratification A N t) : Monotone S.ideal :=
  Fin.monotone_iff_le_succ.mpr S.le_succ

/-- The first ideal of a stratification is nilpotent: it is finitely generated and contained in
the nilradical. -/
theorem isNilpotent_ideal_zero (S : FlatStratification A N t) : IsNilpotent (S.ideal 0) :=
  (Ideal.FG.isNilpotent_iff_le_nilradical (S.fg 0)).mpr S.base_le_nilradical

/-- The first ideal of a stratification is contained in every prime of `A`. -/
theorem ideal_zero_le_of_isPrime (S : FlatStratification A N t) (p : Ideal A) [hp : p.IsPrime] :
    S.ideal 0 ≤ p :=
  S.base_le_nilradical.trans (nilradical_le_prime p)

/-- **The generic flatness stratification of a quotient.** Let `E ⊆ A` be an ideal and let
`s ≤ t` be an index whose ideal `K_s` becomes nilpotent in `A ⧸ E`. Then the extensions of
`K_s, K_{s+1}, …, K_t` to `A ⧸ E` form a generic flatness stratification of `N ⧸ EN` over
`A ⧸ E`, of length `t - s`.

This is the induction step of the proof of Stacks 05U9: it shortens the stratification by `s`,
so a proposition proved by induction on the length may be applied over `A ⧸ E`. -/
def quotient (S : FlatStratification A N t) (E : Ideal A) (s : ℕ) (hs : s ≤ t)
    (hnil : (S.ideal ⟨s, by omega⟩).map (Ideal.Quotient.mk E) ≤ nilradical (A ⧸ E)) :
    FlatStratification (A ⧸ E) (N ⧸ (E • (⊤ : Submodule A N))) (t - s) where
  ideal j := (S.ideal ⟨s + j.val, by have := j.isLt; omega⟩).map (Ideal.Quotient.mk E)
  base_le_nilradical := le_trans (le_of_eq (congrArg (Ideal.map (Ideal.Quotient.mk E))
    (congrArg S.ideal (Fin.ext (show s + (0 : Fin (t - s + 1)).val = s by simp))))) hnil
  fg j := (S.fg _).map _
  le_succ j := Ideal.map_mono (S.monotone (by simp [Fin.le_def]))
  eq_top := by
    have h : S.ideal ⟨s + (Fin.last (t - s)).val, by simp only [Fin.val_last]; omega⟩ = ⊤ := by
      rw [← S.eq_top]
      exact congrArg S.ideal (Fin.ext (by simp only [Fin.val_last]; omega))
    rw [h, Ideal.map_top]
  flat_away j a' ha' L _ _ _ _ _ := by
    have hjt : s + j.val < t := by have := j.isLt; omega
    have e : (⟨s + (Fin.castSucc j).val, by have := j.isLt; omega⟩ : Fin (t + 1)) =
        Fin.castSucc (⟨s + j.val, hjt⟩ : Fin t) := Fin.ext rfl
    have e1 : (⟨s + (Fin.succ j).val, by have := j.isLt; omega⟩ : Fin (t + 1)) =
        Fin.succ (⟨s + j.val, hjt⟩ : Fin t) := Fin.ext rfl
    have key := S.flat_away ⟨s + j.val, hjt⟩
    rw [← e, ← e1] at key
    exact flat_tensorQuotient_of_flat_away E _ _ a' ha' key L

end FlatStratification

/-! ### The scheme theoretic closure of a stratum -/

variable {A : Type u} [CommRing A]

/-- **The ideal `J_i` of the proof of Stacks 05U9.** For an ideal `K ⊆ A` and a family `g` of
elements of `A`, this is the ideal of the scheme theoretic closure in `Spec A` of the open
`⋃ i D(g i)` of the closed subscheme `Spec (A ⧸ K)`: an element of `A` lies in it exactly when
it dies in each `(A ⧸ K)_{g i}`.

With `K = K_i` the ideal of `S_i` and `g` a generating family of `K_{i+1}`, the open is the
stratum `S_i ∖ S_{i+1}` and this is the ideal `J_i` for which the source states Claim 1. -/
def strataClosureIdeal (K : Ideal A) {ι : Type w} (g : ι → A) : Ideal A where
  carrier := {x : A | ∀ i, ∃ n : ℕ, g i ^ n * x ∈ K}
  add_mem' := by
    rintro x y hx hy i
    obtain ⟨n, hn⟩ := hx i
    obtain ⟨m, hm⟩ := hy i
    refine ⟨n + m, ?_⟩
    rw [show g i ^ (n + m) * (x + y) = g i ^ m * (g i ^ n * x) + g i ^ n * (g i ^ m * y) by
      ring]
    exact K.add_mem (K.mul_mem_left _ hn) (K.mul_mem_left _ hm)
  zero_mem' := fun i => ⟨0, by simp⟩
  smul_mem' := by
    rintro c x hx i
    obtain ⟨n, hn⟩ := hx i
    refine ⟨n, ?_⟩
    rw [smul_eq_mul, mul_left_comm]
    exact K.mul_mem_left _ hn

/-- Membership in the closure ideal of a stratum, by definition. -/
theorem mem_strataClosureIdeal_iff (K : Ideal A) {ι : Type w} (g : ι → A) (x : A) :
    x ∈ strataClosureIdeal K g ↔ ∀ i, ∃ n : ℕ, g i ^ n * x ∈ K :=
  Iff.rfl

/-- The closed subscheme cut out by the closure ideal of a stratum contains the stratum: the
ideal of the stratum is contained in its closure ideal. -/
theorem le_strataClosureIdeal (K : Ideal A) {ι : Type w} (g : ι → A) :
    K ≤ strataClosureIdeal K g :=
  fun x hx i => ⟨0, by simpa using hx⟩

/-- **Every point of the stratum lies on its scheme theoretic closure.** A prime containing the
ideal of the stratum but not every element of the family contains the closure ideal.

With `K = K_i` and `g` generating `K_{i+1}`, this says that a prime in `S_i ∖ S_{i+1}` contains
`J_i`, which is what makes Claim 1 at that index a flattening ideal inside that prime. -/
theorem strataClosureIdeal_le_of_isPrime {K : Ideal A} {ι : Type w} {g : ι → A} {p : Ideal A}
    (hp : p.IsPrime) (hKp : K ≤ p) {i : ι} (hgi : g i ∉ p) :
    strataClosureIdeal K g ≤ p := by
  intro x hx
  obtain ⟨n, hn⟩ := hx i
  exact (hp.mem_or_mem (hKp hn)).resolve_left fun h => hgi (hp.mem_of_pow_mem n h)

/-- **The stratum is scheme theoretically dense in the closed subscheme its closure ideal cuts
out.** An element of `A ⧸ J` killed by a power of each `g i` is zero, where
`J = strataClosureIdeal K g`.

This is the hypothesis `hdense` of `Stacks.flat_of_least_flattening_of_flat_away`, read over
`A ⧸ J`. -/
theorem eq_zero_of_forall_pow_mul_eq_zero_quotient (K : Ideal A) {ι : Type w} (g : ι → A)
    (x : A ⧸ strataClosureIdeal K g)
    (hx : ∀ i, ∃ n : ℕ, (Ideal.Quotient.mk (strataClosureIdeal K g) (g i)) ^ n * x = 0) :
    x = 0 := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.Quotient.eq_zero_iff_mem]
  intro i
  obtain ⟨n, hn⟩ := hx i
  rw [← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hn
  obtain ⟨m, hm⟩ := hn i
  exact ⟨m + n, by rwa [pow_add, mul_assoc]⟩

end Stacks

end
