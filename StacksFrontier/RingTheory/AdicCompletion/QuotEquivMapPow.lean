module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import StacksFrontier.RingTheory.AdicCompletion.SmulTopPow

/-!
# The module tower and the ring tower of an adic completion agree

For an `R`-algebra `U` and an ideal `I` of `R`, `quotEquivMapPow` identifies the `n`-th step of the
tower computing the `I`-adic completion of `U` as a module with the `n`-th step of the tower
computing the `IU`-adic completion of `U` as a ring. This identification is the identity on
residue classes and commutes with the transition maps of the two towers, so the two completions
are `R`-linearly isomorphic.

## Main definitions

* `adicCompletionLinearEquivMap`: the `R`-linear isomorphism between the `I`-adic completion of
  the module `U` and the `IU`-adic completion of the ring `U`.
-/

@[expose] public section

/-- `quotEquivMapPow` sends the residue class of `x` modulo `Iⁿ • ⊤` to its residue class modulo
`(IU)ⁿ`. -/
theorem quotEquivMapPow_mk {R : Type*} [CommRing R] (I : Ideal R) (U : Type*)
    [CommRing U] [Algebra R U] (n : ℕ) (x : U) :
    quotEquivMapPow I U n (Submodule.Quotient.mk x) = Ideal.Quotient.mk _ x := rfl

/-- `quotEquivMapPow` commutes with the transition maps of the two towers. -/
theorem transitionMap_quotEquivMapPow {R : Type*} [CommRing R] (I : Ideal R) (U : Type*)
    [CommRing U] [Algebra R U] {m n : ℕ} (hmn : m ≤ n)
    (x : U ⧸ (I ^ n • (⊤ : Submodule R U))) :
    AdicCompletion.transitionMap (I.map (algebraMap R U)) U hmn (quotEquivMapPow I U n x)
      = quotEquivMapPow I U m (AdicCompletion.transitionMap I U hmn x) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

/-- The `I`-adic completion of the module `U` is `R`-linearly isomorphic to the `IU`-adic
completion of the ring `U`. -/
def adicCompletionLinearEquivMap {R : Type*} [CommRing R] (I : Ideal R) (U : Type*)
    [CommRing U] [Algebra R U] :
    AdicCompletion I U ≃ₗ[R] AdicCompletion (I.map (algebraMap R U)) U where
  __ := Equiv.subtypeEquiv (Equiv.piCongrRight fun n ↦ (quotEquivMapPow I U n).toEquiv) fun v ↦ by
    refine ⟨fun hv _ _ hmn ↦ ?_, fun hv _ _ hmn ↦ ?_⟩
    · change AdicCompletion.transitionMap _ U hmn (quotEquivMapPow I U _ (v _))
        = quotEquivMapPow I U _ (v _)
      rw [transitionMap_quotEquivMapPow, hv hmn]
    · exact (quotEquivMapPow I U _).injective
        (by rw [← transitionMap_quotEquivMapPow]; exact hv hmn)
  map_add' x y := Subtype.ext (funext fun n ↦ map_add (quotEquivMapPow I U n) (x.val n) (y.val n))
  map_smul' r x := Subtype.ext (funext fun n ↦ map_smul (quotEquivMapPow I U n) r (x.val n))

/-- Level `n` of `adicCompletionLinearEquivMap` is `quotEquivMapPow`. -/
theorem adicCompletionLinearEquivMap_val {R : Type*} [CommRing R] (I : Ideal R) (U : Type*)
    [CommRing U] [Algebra R U] (x : AdicCompletion I U) (n : ℕ) :
    (adicCompletionLinearEquivMap I U x).val n = quotEquivMapPow I U n (x.val n) := rfl
