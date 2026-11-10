module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDividedPowerForms
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CompletedFormsShapeLinear
public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.CompletionLevelReindex

/-!
# A completed map is bijective as soon as its deep levels are

A semilinear map `g : P → Q` with `σ(I) ⊆ J` induces maps `P ⧸ Iⁿ P → Q ⧸ Jⁿ Q` on the levels
and a map of adic completions. The levels of an adic completion below `N` are determined by the
level `N` through the transition maps, so the completed map is bijective as soon as the level
maps are bijective for all `n ≥ N`.

A linear equivalence over `R` between modules on which the `R`-action factors through a quotient
`S` of `R` is also a linear equivalence over `S`.

## Main results

* `Crystalline.adicCompletionMapₛₗ_bijective_of_le` — **a completed semilinear map is bijective
  as soon as the maps it induces on the levels `n ≥ N` are.**
* `Crystalline.linearEquivOfSurjectiveTower` — a linear equivalence over `R` between modules on
  which the action factors through a quotient `S` of `R`, read as a linear equivalence over `S`.

## References

* [Stacks Project, Lemma 60.20.1, Tag 07KK](https://stacks.math.columbia.edu/tag/07KK)
* [Stacks Project, Lemma 60.21.4, Tag 07LH](https://stacks.math.columbia.edu/tag/07LH)
-/

@[expose] public noncomputable section

namespace Crystalline

open DividedPowers

/-! ### Bijectivity of a completed map from bijectivity of its deep levels -/

section Levelwise

variable {R S : Type*} [CommRing R] [CommRing S] {P Q : Type*} [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module S Q] {σ : R →+* S} {I : Ideal R} {Jd : Ideal S}

/-- **A completed semilinear map is bijective as soon as the maps it induces on the levels
`n ≥ N` are.** -/
public theorem adicCompletionMapₛₗ_bijective_of_le (g : P →ₛₗ[σ] Q) (h : I.map σ ≤ Jd) (N : ℕ)
    (hlev : ∀ n : ℕ, N ≤ n → Function.Bijective (adicQuotientMap g h n)) :
    Function.Bijective (adicCompletionMapₛₗ g h) := by
  classical
  have hdown : ∀ (x : AdicCompletion I P) (n : ℕ),
      x.val n = AdicCompletion.transitionMap I P (le_max_left n N) (x.val (max n N)) :=
    fun x n ↦ (x.property (le_max_left n N)).symm
  refine ⟨fun x y hxy ↦ AdicCompletion.ext fun n ↦ ?_, fun z ↦ ?_⟩
  · have hval : ∀ m : ℕ, N ≤ m → x.val m = y.val m := by
      intro m hm
      exact (hlev m hm).1 (congrArg (fun w : AdicCompletion Jd Q ↦ w.val m) hxy)
    rw [hdown x n, hdown y n, hval (max n N) (le_max_right n N)]
  · choose pre hpre using fun m : {m : ℕ // N ≤ m} ↦ (hlev m.1 m.2).2 (z.val m.1)
    have hz : ∀ (a b : ℕ) (hab : a ≤ b) (hNb : N ≤ b),
        adicQuotientMap g h a (AdicCompletion.transitionMap I P hab (pre ⟨b, hNb⟩)) = z.val a := by
      intro a b hab hNb
      rw [← adicQuotientMap_transition g h hab, hpre ⟨b, hNb⟩]
      exact z.property hab
    refine ⟨⟨fun n ↦ AdicCompletion.transitionMap I P (le_max_left n N)
      (pre ⟨max n N, le_max_right n N⟩), ?_⟩, AdicCompletion.ext fun n ↦ ?_⟩
    · intro m n hmn
      have hkey : ∀ (a b : ℕ) (hab : a ≤ b) (hNa : N ≤ a) (hNb : N ≤ b),
          AdicCompletion.transitionMap I P hab (pre ⟨b, hNb⟩) = pre ⟨a, hNa⟩ :=
          fun a b hab hNa hNb ↦ (hlev a hNa).1 ((hz a b hab hNb).trans (hpre ⟨a, hNa⟩).symm)
      have htrans : ∀ {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (y : P ⧸ I ^ c • (⊤ : Submodule R P)),
          AdicCompletion.transitionMap I P hab (AdicCompletion.transitionMap I P hbc y) =
            AdicCompletion.transitionMap I P (hab.trans hbc) y := by
        intro a b c hab hbc y
        induction y using Submodule.Quotient.induction_on with
        | _ w => rw [adicTransitionMap_mk, adicTransitionMap_mk, adicTransitionMap_mk]
      have hmax : max m N ≤ max n N := max_le_max hmn le_rfl
      change AdicCompletion.transitionMap I P hmn
          (AdicCompletion.transitionMap I P (le_max_left n N)
            (pre ⟨max n N, le_max_right n N⟩)) =
        AdicCompletion.transitionMap I P (le_max_left m N) (pre ⟨max m N, le_max_right m N⟩)
      rw [htrans hmn (le_max_left n N), ← hkey (max m N) (max n N) hmax (le_max_right m N)
        (le_max_right n N), htrans (le_max_left m N) hmax]
    · exact hz n _ _ _

end Levelwise

/-! ### A linear equivalence read over a quotient of the base -/

section Descend

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  {X Y : Type*} [AddCommGroup X] [Module R X] [Module S X] [IsScalarTower R S X]
  [AddCommGroup Y] [Module R Y] [Module S Y] [IsScalarTower R S Y]

/-- **A linear equivalence over `R` between two modules whose `R`-action factors through a
quotient `S`, read as a linear equivalence over `S`.** -/
public def linearEquivOfSurjectiveTower (hsur : Function.Surjective (algebraMap R S))
    (e : X ≃ₗ[R] Y) : X ≃ₗ[S] Y where
  toFun := e
  invFun := e.symm
  map_add' := e.map_add
  map_smul' s x := by
    obtain ⟨r, rfl⟩ := hsur s
    simp only [RingHom.id_apply, IsScalarTower.algebraMap_smul]
    exact e.map_smul r x
  left_inv := e.left_inv
  right_inv := e.right_inv

/-- The `S`-linear equivalence `linearEquivOfSurjectiveTower hsur e` acts as `e`. -/
@[simp] public theorem linearEquivOfSurjectiveTower_apply
    (hsur : Function.Surjective (algebraMap R S)) (e : X ≃ₗ[R] Y) (x : X) :
    linearEquivOfSurjectiveTower (S := S) hsur e x = e x := rfl

/-- The inverse of `linearEquivOfSurjectiveTower hsur e` acts as `e.symm`. -/
@[simp] public theorem linearEquivOfSurjectiveTower_symm_apply
    (hsur : Function.Surjective (algebraMap R S)) (e : X ≃ₗ[R] Y) (y : Y) :
    (linearEquivOfSurjectiveTower (S := S) hsur e).symm y = e.symm y := rfl

end Descend

end Crystalline

end
