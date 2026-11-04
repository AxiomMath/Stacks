module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import StacksFrontier.RingTheory.AdicCompletion.SmulTopPow

/-!
# The adic completion of a module does not depend on which ring is acting

Let `I` be an ideal of `R`, let `S` be an `R`-algebra and let `M` carry compatible actions of `R`
and `S`.  Then `M` has two adic towers: `M ⧸ Iⁿ • ⊤` over `R`, and `M ⧸ Jⁿ • ⊤` over `S` for
`J = I S`.  `smul_top_pow_eq_restrictScalars_module` says the two filtrations are the *same*
submodules of `M`, read through restriction of scalars, and `quotEquivMapPowModule` identifies
the levels by the identity on residue classes.  This module carries that identification up to
the completions, giving

`AdicCompletion I M ≃ₗ[R] AdicCompletion J M`.

`StacksFrontier/RingTheory/AdicCompletion/QuotEquivMapPow.lean` does this for `M = S` itself, where
the point is that only the second completion carries a ring structure.  Here the point is
different: when `M` is built from modules over two different rings — a tensor product
`N ⊗[R] Ω` with `Ω` an `S`-module, say — the natural ring to complete over is not determined,
and a comparison stated over one of them has to be read over the other.  That is what the
completed tensor products of a base change need, since `Crystalline.CompletedTensor` completes
along `(p)` of whichever ring is in its spelling.

## Main definitions

* `adicCompletionLinearEquivMapModule` — **the comparison
  `AdicCompletion I M ≃ₗ[R] AdicCompletion J M`.**

## Main results

* `transitionMap_quotEquivMapPowModule` — the level identifications commute with the transition
  maps of the two towers, which is what makes them agree as inverse limits.
* `adicCompletionLinearEquivMapModule_val` — level `n` of the comparison is
  `quotEquivMapPowModule`, so it is the identity on residue classes.
* `adicCompletionLinearEquivMapModule_of` — the comparison fixes the canonical image of `M`.
-/

@[expose] public section

/-- The level identifications of the two adic towers of `M` commute with the transition maps:
both sides send the class of `y` to the class of `y`. -/
theorem transitionMap_quotEquivMapPowModule {R : Type*} [CommRing R] (I : Ideal R) (S : Type*)
    [CommRing S] [Algebra R S] (M : Type*) [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] {J : Ideal S} (hJ : J = I.map (algebraMap R S)) {m n : ℕ} (hmn : m ≤ n)
    (x : M ⧸ (I ^ n • (⊤ : Submodule R M))) :
    AdicCompletion.transitionMap J M hmn (quotEquivMapPowModule I S M hJ n x) =
      quotEquivMapPowModule I S M hJ m (AdicCompletion.transitionMap I M hmn x) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

/-- **The two adic completions of `M` agree.**  For `J = I S` the `I`-adic completion of `M` as
an `R`-module is `R`-linearly isomorphic to its `J`-adic completion as an `S`-module, because the
two filtrations `Iⁿ • ⊤` and `Jⁿ • ⊤` are the same submodules of `M`. -/
def adicCompletionLinearEquivMapModule {R : Type*} [CommRing R] (I : Ideal R) (S : Type*)
    [CommRing S] [Algebra R S] (M : Type*) [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] {J : Ideal S} (hJ : J = I.map (algebraMap R S)) :
    AdicCompletion I M ≃ₗ[R] AdicCompletion J M where
  __ := Equiv.subtypeEquiv
    (Equiv.piCongrRight fun n ↦ (quotEquivMapPowModule I S M hJ n).toEquiv) fun v ↦ by
    refine ⟨fun hv _ _ hmn ↦ ?_, fun hv _ _ hmn ↦ ?_⟩
    · change AdicCompletion.transitionMap _ M hmn (quotEquivMapPowModule I S M hJ _ (v _))
        = quotEquivMapPowModule I S M hJ _ (v _)
      rw [transitionMap_quotEquivMapPowModule, hv hmn]
    · refine (quotEquivMapPowModule I S M hJ _).injective ?_
      rw [← transitionMap_quotEquivMapPowModule]
      exact hv hmn
  map_add' x y := Subtype.ext (funext fun n ↦
    map_add (quotEquivMapPowModule I S M hJ n) (x.val n) (y.val n))
  map_smul' r x := Subtype.ext (funext fun n ↦
    map_smul (quotEquivMapPowModule I S M hJ n) r (x.val n))

/-- Level `n` of `adicCompletionLinearEquivMapModule` is `quotEquivMapPowModule`. -/
theorem adicCompletionLinearEquivMapModule_val {R : Type*} [CommRing R] (I : Ideal R)
    (S : Type*) [CommRing S] [Algebra R S] (M : Type*) [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] {J : Ideal S} (hJ : J = I.map (algebraMap R S))
    (x : AdicCompletion I M) (n : ℕ) :
    (adicCompletionLinearEquivMapModule I S M hJ x).val n =
      quotEquivMapPowModule I S M hJ n (x.val n) := rfl

/-- **The comparison fixes the canonical image of `M`.** -/
theorem adicCompletionLinearEquivMapModule_of {R : Type*} [CommRing R] (I : Ideal R)
    (S : Type*) [CommRing S] [Algebra R S] (M : Type*) [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] {J : Ideal S} (hJ : J = I.map (algebraMap R S)) (y : M) :
    adicCompletionLinearEquivMapModule I S M hJ (AdicCompletion.of I M y) =
      AdicCompletion.of J M y :=
  AdicCompletion.ext fun _ ↦ rfl
