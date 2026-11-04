module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.CompletedPthRootExtension

/-!
# Tag 07N1 over the `p`-adic completions, with `D`-linear maps

`StacksFrontier/AlgebraicGeometry/Crystalline/Differentials/CompletedPthRootExtension.lean` proves
the conclusion of [Stacks, Lemma 60.25.3, Tag 07N1] for the `p`-adic completions of the two de
Rham complexes of the extension `B ⟶ B' = B[z]⟨ξ⟩/(ξ - (z^p - λ))`, but with `ê`, `ĥ` and `k̂`
merely **additive**: `Crystalline.PAdicCompletion.mapAddHom` completes an additive map by asking
nothing of the scalar actions, and correspondingly yields no linearity.

This module removes that defect.  The source's `e_M^•` is `D`-linear, being built from the
`D`-linear continuous `θ`, and so are its two homotopies; and
`Crystalline.exists_homotopyInverse_baseChangeDeRhamMap_baseLinear` now produces the uncompleted
`e`, `h` and `k` together with their `B`-linearity.  A `B`-linear map completes by Mathlib's
`AdicCompletion.map`, which is linear over the completed ring
`D = AdicCompletion (p) B`, and
`Crystalline.PAdicCompletion.mapAddHom_eq_adicCompletionMap` identifies its underlying additive
map with the additive completion.  So every identity of
`Crystalline.exists_completedHomotopyInverse_pthRootExtension_dividedPowerDifferentials` is
available verbatim for the linear maps.

## How the completions are taken

Every term of both complexes is completed along `(p) ⊆ B`.  For the complex of the extension
that is the same object as the completion along `(p) ⊆ B'` — the level is the subgroup `pⁿ ·`
whichever ring the ideal is read in, which is
`Crystalline.PAdicCompletion.coe_pow_smul_top_eq` — and it is the reading that matters here,
because it is over `B` that the terms are modules and over `D` that the completed maps are
linear.  It is also the source's reading: the complexes of [Stacks, Tag 07N1] are
`M ⊗^∧_D Ω^•_D` and `M ⊗^∧_D Ω^•_{D'}`, completed tensor products over `D`.

## Relation to the tag

What is completed here is the module of divided power differentials of the uncompleted `B'`, for a
module with an ordinary connection over `B`.  [Stacks, Tag 07N1] itself — for a module with a
completed connection and the completed forms of the completed ring `D'` — is
`Crystalline.PthRootExtension.exists_homotopyInverse_completedPthRootExtension` of
`StacksFrontier/AlgebraicGeometry/Crystalline/Differentials/PthRootCompletedTheorem.lean`.

## Main definitions

* `Crystalline.PthRootExtension.completedPrimeTerm` — the degree-`q` term of the completed de
  Rham complex of the extension, completed along `(p) ⊆ B` so that it is a `D`-module.
* `Crystalline.PthRootExtension.completedPrimeDifferential`,
  `Crystalline.PthRootExtension.completedComparison` — its differential and the completed
  comparison `ĉ_M^•`, both additive.

## Main results

* `Crystalline.PAdicCompletion.completedLinear` and
  `Crystalline.PAdicCompletion.completedLinear_toAddMonoidHom` — the completion of a `B`-linear
  map, linear over `D`, and the identification of its underlying additive map with the additive
  completion.
* `Crystalline.exists_completedLinearHomotopyInverse_pthRootExtension_dividedPowerDifferentials`
  — **the conclusion of [Stacks, Tag 07N1] for the `p`-adic completions, with `ê`, `ĥ` and `k̂`
  linear over the completed base `D`.**

## References

* [Stacks Project, Lemma 60.25.3, Tag 07N1](https://stacks.math.columbia.edu/tag/07N1)
* [Stacks Project, Lemma 60.25.2, Tag 07Q7](https://stacks.math.columbia.edu/tag/07Q7)
* [Stacks Project, Lemma 60.20.1, Tag 07KK](https://stacks.math.columbia.edu/tag/07KK)
-/

@[expose] public noncomputable section

open DividedPowers Stacks.DeRham.DifferentialDescent

open scoped TensorProduct

universe u w

namespace Crystalline

namespace PAdicCompletion

/-! ### The completion of a linear map, linear over the completed ring -/

section LinearCompletion

variable (p : ℕ) (R : Type*) [CommRing R] {X : Type*} [AddCommGroup X] [Module R X]
  {Y : Type*} [AddCommGroup Y] [Module R Y]

/-- **The `p`-adic completion of an `R`-linear map, linear over the completed ring.**  This is
Mathlib's `AdicCompletion.map`, named here because it is the linear refinement of
`Crystalline.PAdicCompletion.mapAddHom`: that construction completes a merely additive map and
produces a merely additive one, whereas on a linear map the completion is linear over
`AdicCompletion (p) R`. -/
abbrev completedLinear (f : X →ₗ[R] Y) :
    AdicCompletion (pAdicIdeal (A := R) p) X →ₗ[AdicCompletion (pAdicIdeal (A := R) p) R]
      AdicCompletion (pAdicIdeal (A := R) p) Y :=
  AdicCompletion.map (pAdicIdeal (A := R) p) f

/-- **The underlying additive map of the linear completion is the additive completion.**  So
every identity proved for `Crystalline.PAdicCompletion.mapAddHom` of a linear map is an identity
about `Crystalline.PAdicCompletion.completedLinear` of it. -/
theorem completedLinear_toAddMonoidHom (f : X →ₗ[R] Y) :
    (completedLinear p R f).toAddMonoidHom = mapAddHom p R R f.toAddMonoidHom :=
  (mapAddHom_eq_adicCompletionMap p R f).symm

/-- **The additive completion of an `R`-linear map commutes with the action of the completed
ring.**  This is `Crystalline.PAdicCompletion.completedLinear_toAddMonoidHom` read as the scalar
law, which is what bundles the additive completion back up as a linear map. -/
theorem mapAddHom_smul_of_linear (f : X →ₗ[R] Y)
    (r : AdicCompletion (pAdicIdeal (A := R) p) R)
    (x : AdicCompletion (pAdicIdeal (A := R) p) X) :
    mapAddHom p R R f.toAddMonoidHom (r • x) = r • mapAddHom p R R f.toAddMonoidHom x := by
  rw [mapAddHom_eq_adicCompletionMap]
  exact (AdicCompletion.map (pAdicIdeal (A := R) p) f).map_smul r x

end LinearCompletion

end PAdicCompletion

/-! ### An additive map with the scalar law, read as a linear map -/

section LinearOfAddHom

variable {R : Type*} [CommRing R] {X Y : Type*} [AddCommGroup X] [Module R X]
  [AddCommGroup Y] [Module R Y]

/-- An additive map which commutes with the action of `R`, read as an `R`-linear map. -/
def linearOfAddHom (f : X →+ Y) (hf : ∀ (r : R) (x : X), f (r • x) = r • f x) : X →ₗ[R] Y where
  toFun := f
  map_add' := f.map_add
  map_smul' := hf

/-- The additive map underlying `linearOfAddHom f hf` is `f`. -/
theorem linearOfAddHom_toAddMonoidHom (f : X →+ Y)
    (hf : ∀ (r : R) (x : X), f (r • x) = r • f x) :
    (linearOfAddHom (R := R) f hf).toAddMonoidHom = f :=
  rfl

/-- The additive `p`-adic completion of an additive map with the scalar law, read as a linear
map over the completed ring. -/
private def completedLinearOfAddHom (p : ℕ) (f : X →+ Y)
    (hf : ∀ (r : R) (x : X), f (r • x) = r • f x) :
    AdicCompletion (pAdicIdeal (A := R) p) X →ₗ[AdicCompletion (pAdicIdeal (A := R) p) R]
      AdicCompletion (pAdicIdeal (A := R) p) Y :=
  linearOfAddHom (PAdicCompletion.mapAddHom p R R f)
    (PAdicCompletion.mapAddHom_smul_of_linear p R (linearOfAddHom f hf))

end LinearOfAddHom

namespace PthRootExtension

/-! ### The complex of the extension, completed along `(p) ⊆ B` -/

section CompletedOverBase

variable (A : Type u) [CommRing A] (B : DividedPowerRing.{u}) [Algebra A (B : Type u)] (p : ℕ)
  (lam : (B : Type u)) (hp : p ≠ 0) (M : Type w) [AddCommGroup M] [Module (B : Type u) M]

/-- **The degree-`q` term `M' ⊗^∧_D Ω^q_{B'/A,γ'}` of the completed de Rham complex of the
extension**, the completion of `M' ⊗_{B'} Ω^q_{B'/A,γ'}` along `(p) ⊆ B`.  By
`Crystalline.PAdicCompletion.coe_pow_smul_top_eq` the levels are the subgroups `pⁿ ·` whichever
of `B` and `B'` the ideal `(p)` is read in, so this is the `p`-adic completion of the term; the
reading over `B` is the one that makes it a module over `D`. -/
abbrev completedPrimeTerm (q : ℕ) : Type (max u w) :=
  AdicCompletion (pAdicIdeal (A := (B : Type u)) p) (primeDeRhamTerm A B p lam hp M q)

/-- **The differential of the completed de Rham complex of the extension**, the `p`-adic
completion of `Crystalline.PthRootExtension.primeDeRhamDifferential`.  It is additive and not
`D`-linear: the de Rham differential is `A`-linear and the Leibniz rule forbids more. -/
abbrev completedPrimeDifferential (S' : SourceDeRham A (primeRing B p lam))
    (nabla : Connection A (B : Type u) (baseFormsProjection A B) M) (q : ℕ) :
    completedPrimeTerm A B p lam hp M q →+ completedPrimeTerm A B p lam hp M (q + 1) :=
  PAdicCompletion.mapAddHom p (B : Type u) (B : Type u)
    (primeDeRhamDifferential A B p lam hp M S' nabla q)

/-- **The completed comparison `ĉ_M^•`**, the `p`-adic completion of the canonical map of de Rham
complexes of [Stacks, Lemma 60.6.9, Tag 07HW]. -/
abbrev completedComparison
    (c : ∀ q : ℕ,
      RestrictScalars A (B : Type u) (baseDeRhamTerm A B M q) →ₗ[A]
        RestrictScalars A (primeRing B p lam) (primeDeRhamTerm A B p lam hp M q))
    (q : ℕ) :
    completedBaseDeRhamTerm A B p M q →+ completedPrimeTerm A B p lam hp M q :=
  PAdicCompletion.mapAddHom p (B : Type u) (B : Type u)
    (restrictScalarsUnderlyingAddHom (c q))

end CompletedOverBase

end PthRootExtension

open PthRootExtension

/-! ### Tag 07N1 for the uncompleted extension, with the base-linearity -/

/-- **Tag 07N1 for the uncompleted extension `B → B[z]⟨ξ⟩/(ξ - (z^p - λ))`, with the
`B`-linearity of `e`, of the homotopy `h` and of the homotopy `k`.**  This is
`Crystalline.exists_homotopyInverse_pthRootExtension_dividedPowerDifferentials` together with
the three scalar laws that
`Crystalline.exists_homotopyInverse_baseChangeDeRhamMap_baseLinear` supplies, and it is what
makes the three completed maps linear over the completed base `D` rather than merely additive:
`e` is `B`-linear because the source's `θ` is, `h` because it is `θ ⊗ 1` read through two
`B'`-linear maps, and `k` because it is zero. -/
theorem exists_homotopyInverse_pthRootExtension_dividedPowerDifferentials_baseLinear
    {A : Type u} {M : Type w} [CommRing A]
    (B : DividedPowerRing.{u}) (p : ℕ) (lam : (B : Type u)) (hp : p ≠ 0)
    [Algebra A (B : Type u)]
    [Nontrivial (XiAlg B)] [Fact p.Prime]
    [Algebra (IntegersAtPrime p) (B : Type u)]
    [AddCommGroup M] [Module (B : Type u) M]
    (S : SourceDeRham A (B : Type u))
    (S' : SourceDeRham A (primeRing B p lam))
    (nabla : Connection A (B : Type u) (baseFormsProjection A B) M)
    (hintegrable : Connection.IsIntegrable S (baseFormsProjection A B) (Submodule.mkQ_surjective _)
      (baseFormsGenerationHypothesis A B S) nabla)
    (c : ∀ q : ℕ,
      RestrictScalars A (B : Type u) (M ⊗[(B : Type u)] (⋀[(B : Type u)]^q (baseForms A B))) →ₗ[A]
        RestrictScalars A (primeRing B p lam)
          ((primeRing B p lam ⊗[(B : Type u)] M)
            ⊗[primeRing B p lam]
              (⋀[primeRing B p lam]^q (primeForms A B p lam hp))))
    (hc_wedge : ∀ (q : ℕ) (m : M) (omega : Fin q → (baseForms A B)),
      c q (m ⊗ₜ[(B : Type u)] exteriorPower.ιMulti (B : Type u) q omega) =
        (1 ⊗ₜ[(B : Type u)] m) ⊗ₜ[primeRing B p lam]
          exteriorPower.ιMulti (primeRing B p lam) q ((primeFormsComparison A B p lam hp) ∘ omega))
    (hc_comm : ∀ (q : ℕ) (x : M ⊗[(B : Type u)] (⋀[(B : Type u)]^q (baseForms A B))),
      c (q + 1)
          ((extendedConnection S (baseFormsProjection A B) (Submodule.mkQ_surjective _)
            (baseFormsGenerationHypothesis A B S) nabla).toLinearMap q x) =
        (extendedConnection S' (primeFormsProjection A B p lam hp) (Submodule.mkQ_surjective _)
          (primeFormsGenerationHypothesis A B p lam hp S')
          (Connection.baseChange (primeFormsComparison A B p lam hp) nabla
            (primeFormsComparison_dividedPowerDifferential A B p lam hp))).toLinearMap q (c q x)) :
    ∃ e : ∀ q : ℕ,
      RestrictScalars A (primeRing B p lam)
          ((primeRing B p lam ⊗[(B : Type u)] M)
            ⊗[primeRing B p lam]
              (⋀[primeRing B p lam]^q (primeForms A B p lam hp))) →ₗ[A]
        RestrictScalars A (B : Type u) (M ⊗[(B : Type u)] (⋀[(B : Type u)]^q (baseForms A B))),
      (∀ (q : ℕ) (x : RestrictScalars A (primeRing B p lam)
          ((primeRing B p lam ⊗[(B : Type u)] M)
            ⊗[primeRing B p lam]
              (⋀[primeRing B p lam]^q (primeForms A B p lam hp)))),
          e (q + 1)
              ((extendedConnection S' (primeFormsProjection A B p lam hp)
                (Submodule.mkQ_surjective _) (primeFormsGenerationHypothesis A B p lam hp S')
                (Connection.baseChange (primeFormsComparison A B p lam hp) nabla
                  (primeFormsComparison_dividedPowerDifferential A B p lam hp))).toLinearMap
                q x) =
            (extendedConnection S (baseFormsProjection A B) (Submodule.mkQ_surjective _)
              (baseFormsGenerationHypothesis A B S) nabla).toLinearMap
              q (e q x)) ∧
        (∀ (q : ℕ) (b : (B : Type u)) (y : RestrictScalars A (primeRing B p lam)
            ((primeRing B p lam ⊗[(B : Type u)] M)
              ⊗[primeRing B p lam]
                (⋀[primeRing B p lam]^q (primeForms A B p lam hp)))),
            e q (RestrictScalars.lsmul A (primeRing B p lam)
                ((primeRing B p lam ⊗[(B : Type u)] M)
                  ⊗[primeRing B p lam]
                    (⋀[primeRing B p lam]^q (primeForms A B p lam hp)))
                (algebraMap (B : Type u) (primeRing B p lam) b) y) =
              RestrictScalars.lsmul A (B : Type u)
                (M ⊗[(B : Type u)] (⋀[(B : Type u)]^q (baseForms A B))) b (e q y)) ∧
        (∃ h : ∀ q : ℕ,
            RestrictScalars A (primeRing B p lam)
                ((primeRing B p lam ⊗[(B : Type u)] M)
                  ⊗[primeRing B p lam]
                    (⋀[primeRing B p lam]^(q + 1) (primeForms A B p lam hp))) →ₗ[A]
              RestrictScalars A (primeRing B p lam)
                ((primeRing B p lam ⊗[(B : Type u)] M)
                  ⊗[primeRing B p lam]
                    (⋀[primeRing B p lam]^q (primeForms A B p lam hp))),
          (∀ x : RestrictScalars A (primeRing B p lam)
              ((primeRing B p lam ⊗[(B : Type u)] M)
                ⊗[primeRing B p lam]
                  (⋀[primeRing B p lam]^0 (primeForms A B p lam hp))),
              h 0 ((extendedConnection S' (primeFormsProjection A B p lam hp)
                (Submodule.mkQ_surjective _) (primeFormsGenerationHypothesis A B p lam hp S')
                (Connection.baseChange (primeFormsComparison A B p lam hp) nabla
                  (primeFormsComparison_dividedPowerDifferential A B p lam hp))).toLinearMap
                0 x) =
                RestrictScalars.lsmul A (primeRing B p lam)
                    ((primeRing B p lam ⊗[(B : Type u)] M)
                      ⊗[primeRing B p lam]
                        (⋀[primeRing B p lam]^0 (primeForms A B p lam hp)))
                    (algebraMap (B : Type u) (primeRing B p lam)
                      ((p : ℕ) : (B : Type u))) x -
                  c 0 (e 0 x)) ∧
            (∀ (q : ℕ)
                (x : RestrictScalars A (primeRing B p lam)
                  ((primeRing B p lam ⊗[(B : Type u)] M)
                    ⊗[primeRing B p lam]
                      (⋀[primeRing B p lam]^(q + 1) (primeForms A B p lam hp)))),
              (show RestrictScalars A (primeRing B p lam)
                  ((primeRing B p lam ⊗[(B : Type u)] M)
                    ⊗[primeRing B p lam]
                      (⋀[primeRing B p lam]^(q + 1) (primeForms A B p lam hp))) from
                (extendedConnection S' (primeFormsProjection A B p lam hp)
                  (Submodule.mkQ_surjective _)
                  (primeFormsGenerationHypothesis A B p lam hp S')
                  (Connection.baseChange (primeFormsComparison A B p lam hp) nabla
                    (primeFormsComparison_dividedPowerDifferential A B p lam hp))).toLinearMap
                    q (h q x)) +
                  h (q + 1)
                    ((extendedConnection S' (primeFormsProjection A B p lam hp)
                      (Submodule.mkQ_surjective _) (primeFormsGenerationHypothesis A B p lam hp S')
                      (Connection.baseChange (primeFormsComparison A B p lam hp) nabla
                        (primeFormsComparison_dividedPowerDifferential A B p lam hp))).toLinearMap
                      (q + 1) x) =
                RestrictScalars.lsmul A (primeRing B p lam)
                    ((primeRing B p lam ⊗[(B : Type u)] M)
                      ⊗[primeRing B p lam]
                        (⋀[primeRing B p lam]^(q + 1) (primeForms A B p lam hp)))
                    (algebraMap (B : Type u) (primeRing B p lam)
                      ((p : ℕ) : (B : Type u))) x -
                  c (q + 1) (e (q + 1) x)) ∧
            (∀ (q : ℕ) (b : (B : Type u))
                (y : RestrictScalars A (primeRing B p lam)
                  ((primeRing B p lam ⊗[(B : Type u)] M)
                    ⊗[primeRing B p lam]
                      (⋀[primeRing B p lam]^(q + 1) (primeForms A B p lam hp)))),
              h q (RestrictScalars.lsmul A (primeRing B p lam)
                  ((primeRing B p lam ⊗[(B : Type u)] M)
                    ⊗[primeRing B p lam]
                      (⋀[primeRing B p lam]^(q + 1) (primeForms A B p lam hp)))
                  (algebraMap (B : Type u) (primeRing B p lam) b) y) =
                RestrictScalars.lsmul A (primeRing B p lam)
                  ((primeRing B p lam ⊗[(B : Type u)] M)
                    ⊗[primeRing B p lam]
                      (⋀[primeRing B p lam]^q (primeForms A B p lam hp)))
                  (algebraMap (B : Type u) (primeRing B p lam) b) (h q y))) ∧
        (∃ k : ∀ q : ℕ,
            RestrictScalars A (B : Type u)
                (M ⊗[(B : Type u)] (⋀[(B : Type u)]^(q + 1) (baseForms A B))) →ₗ[A]
              RestrictScalars A (B : Type u)
                (M ⊗[(B : Type u)] (⋀[(B : Type u)]^q (baseForms A B))),
          (∀ x : RestrictScalars A (B : Type u)
              (M ⊗[(B : Type u)] (⋀[(B : Type u)]^0 (baseForms A B))),
              k 0 ((extendedConnection S (baseFormsProjection A B) (Submodule.mkQ_surjective _)
                (baseFormsGenerationHypothesis A B S) nabla).toLinearMap
                0 x) =
                RestrictScalars.lsmul A (B : Type u)
                  (M ⊗[(B : Type u)] (⋀[(B : Type u)]^0 (baseForms A B)))
                  ((p : ℕ) : (B : Type u)) x - e 0 (c 0 x)) ∧
            (∀ (q : ℕ) (x : RestrictScalars A (B : Type u)
                (M ⊗[(B : Type u)] (⋀[(B : Type u)]^(q + 1) (baseForms A B)))),
              (extendedConnection S (baseFormsProjection A B) (Submodule.mkQ_surjective _)
                (baseFormsGenerationHypothesis A B S) nabla).toLinearMap
                  q (k q x) +
                k (q + 1)
                  ((extendedConnection S (baseFormsProjection A B) (Submodule.mkQ_surjective _)
                    (baseFormsGenerationHypothesis A B S) nabla).toLinearMap
                    (q + 1) x) =
                RestrictScalars.lsmul A (B : Type u)
                    (M ⊗[(B : Type u)] (⋀[(B : Type u)]^(q + 1) (baseForms A B)))
                    ((p : ℕ) : (B : Type u)) x -
                  e (q + 1) (c (q + 1) x)) ∧
            (∀ (q : ℕ) (b : (B : Type u))
                (x : RestrictScalars A (B : Type u)
                  (M ⊗[(B : Type u)] (⋀[(B : Type u)]^(q + 1) (baseForms A B)))),
              k q (RestrictScalars.lsmul A (B : Type u)
                  (M ⊗[(B : Type u)] (⋀[(B : Type u)]^(q + 1) (baseForms A B))) b x) =
                RestrictScalars.lsmul A (B : Type u)
                  (M ⊗[(B : Type u)] (⋀[(B : Type u)]^q (baseForms A B))) b (k q x))) :=
  let hpz := partialZValues_of_isDpowDifferential (baseFormsProjection A B)
    (pthRootDzDecomposition A B p lam hp)
    (primeFormsComparison_dividedPowerDifferential A B p lam hp) hp
    (isDpowDifferential_dividedPowerDifferentials B p lam hp)
  exists_homotopyInverse_baseChangeDeRhamMap_baseLinear S S'
    (baseFormsProjection A B) (primeFormsProjection A B p lam hp)
    (Submodule.mkQ_surjective _) (baseFormsGenerationHypothesis A B S)
    (Submodule.mkQ_surjective _) (primeFormsGenerationHypothesis A B p lam hp S')
    (primeFormsComparison A B p lam hp)
    (primeFormsComparison_dividedPowerDifferential A B p lam hp)
    nabla hintegrable c hc_wedge hc_comm ((p : ℕ) : (B : Type u)) (zElt B p lam)
    (theta B p lam hp) (pthRootDzDecomposition A B p lam hp)
    (targetD_natCast (baseFormsProjection A B) p)
    (fun f ↦ partialZ_theta B p lam hp hpz f)
    (universallyInjective_toPrimeRing B p lam hp)
    (fun f ↦ ⟨epsilon B p lam hp f, (smul_sub_theta_partialZ B p lam hp hpz f).symm⟩)
    (dOne_remainder_mem B p lam (baseFormsProjection A B)
      (pthRootDzDecomposition A B p lam hp)
      (primeFormsComparison_dividedPowerDifferential A B p lam hp) hp
      (dOneValues_of_isDpowDifferential (baseFormsProjection A B)
        (pthRootDzDecomposition A B p lam hp)
        (primeFormsComparison_dividedPowerDifferential A B p lam hp)
        (isDpowDifferential_dividedPowerDifferentials B p lam hp)))

/-! ### Tag 07N1 over the completions, with `D`-linear maps -/

/-- **Tag 07N1 for the `p`-adic completions of the de Rham complexes of the extension
`B → B[z]⟨ξ⟩/(ξ - (z^p - λ))`, with `ê`, `ĥ` and `k̂` linear over the completed base `D`.**

With the hypotheses of
`Crystalline.exists_homotopyInverse_pthRootExtension_dividedPowerDifferentials` and nothing
beyond them, the `p`-adic completion `ĉ_M^•` of the canonical map of de Rham complexes admits a
`D`-linear map `ê_M^•` of the completed complexes in the opposite direction which commutes with
the completed differentials, together with `D`-linear homotopies `ĥ` and `k̂` exhibiting
`ĉ ∘ ê` and `ê ∘ ĉ` as homotopic to multiplication by `p`.

The three maps are `Mathlib`'s `AdicCompletion.map` of the `B`-linear `e`, `h` and `k` produced
by `Crystalline.exists_homotopyInverse_baseChangeDeRhamMap_baseLinear`, hence linear over
`D = AdicCompletion (p) B`; their underlying additive maps are the additive completions, by
`Crystalline.PAdicCompletion.completedLinear_toAddMonoidHom`, so the three identities are the
images of the uncompleted ones under one additive functor exactly as before.

The differentials stay additive, as they must: the de Rham differential is `A`-linear and the
Leibniz rule forbids `D`-linearity.

The tag itself, for the completed forms of the completed ring `D'`, is
`Crystalline.PthRootExtension.exists_homotopyInverse_completedPthRootExtension`. -/
theorem exists_completedLinearHomotopyInverse_pthRootExtension_dividedPowerDifferentials
    {A : Type u} {M : Type w} [CommRing A]
    (B : DividedPowerRing.{u}) (p : ℕ) (lam : (B : Type u)) (hp : p ≠ 0)
    [Algebra A (B : Type u)]
    [Nontrivial (XiAlg B)] [Fact p.Prime]
    [Algebra (IntegersAtPrime p) (B : Type u)]
    [AddCommGroup M] [Module (B : Type u) M]
    (S : SourceDeRham A (B : Type u))
    (S' : SourceDeRham A (primeRing B p lam))
    (nabla : Connection A (B : Type u) (baseFormsProjection A B) M)
    (hintegrable : Connection.IsIntegrable S (baseFormsProjection A B)
      (Submodule.mkQ_surjective _) (baseFormsGenerationHypothesis A B S) nabla)
    (c : ∀ q : ℕ,
      RestrictScalars A (B : Type u) (M ⊗[(B : Type u)] (⋀[(B : Type u)]^q (baseForms A B))) →ₗ[A]
        RestrictScalars A (primeRing B p lam)
          ((primeRing B p lam ⊗[(B : Type u)] M)
            ⊗[primeRing B p lam]
              (⋀[primeRing B p lam]^q (primeForms A B p lam hp))))
    (hc_wedge : ∀ (q : ℕ) (m : M) (omega : Fin q → (baseForms A B)),
      c q (m ⊗ₜ[(B : Type u)] exteriorPower.ιMulti (B : Type u) q omega) =
        (1 ⊗ₜ[(B : Type u)] m) ⊗ₜ[primeRing B p lam]
          exteriorPower.ιMulti (primeRing B p lam) q
            ((primeFormsComparison A B p lam hp) ∘ omega))
    (hc_comm : ∀ (q : ℕ) (x : M ⊗[(B : Type u)] (⋀[(B : Type u)]^q (baseForms A B))),
      c (q + 1)
          ((extendedConnection S (baseFormsProjection A B) (Submodule.mkQ_surjective _)
            (baseFormsGenerationHypothesis A B S) nabla).toLinearMap q x) =
        (extendedConnection S' (primeFormsProjection A B p lam hp) (Submodule.mkQ_surjective _)
          (primeFormsGenerationHypothesis A B p lam hp S')
          (Connection.baseChange (primeFormsComparison A B p lam hp) nabla
            (primeFormsComparison_dividedPowerDifferential A B p lam hp))).toLinearMap q
          (c q x)) :
    ∃ ehat : ∀ q : ℕ,
      completedPrimeTerm A B p lam hp M q →ₗ[completedBaseRing B p]
        completedBaseDeRhamTerm A B p M q,
      (∀ q : ℕ, (ehat (q + 1)).toAddMonoidHom.comp
            (completedPrimeDifferential A B p lam hp M S' nabla q) =
          (completedBaseDeRhamDifferential A B p M S nabla q).comp
            (ehat q).toAddMonoidHom) ∧
        (∃ hhat : ∀ q : ℕ,
            completedPrimeTerm A B p lam hp M (q + 1) →ₗ[completedBaseRing B p]
              completedPrimeTerm A B p lam hp M q,
          ((hhat 0).toAddMonoidHom.comp
                (completedPrimeDifferential A B p lam hp M S' nabla 0) =
              (p : ℕ) • AddMonoidHom.id (completedPrimeTerm A B p lam hp M 0) -
                (completedComparison A B p lam hp M c 0).comp (ehat 0).toAddMonoidHom) ∧
            ∀ q : ℕ,
              (completedPrimeDifferential A B p lam hp M S' nabla q).comp
                    (hhat q).toAddMonoidHom +
                  (hhat (q + 1)).toAddMonoidHom.comp
                    (completedPrimeDifferential A B p lam hp M S' nabla (q + 1)) =
                (p : ℕ) • AddMonoidHom.id (completedPrimeTerm A B p lam hp M (q + 1)) -
                  (completedComparison A B p lam hp M c (q + 1)).comp
                    (ehat (q + 1)).toAddMonoidHom) ∧
        (∃ khat : ∀ q : ℕ,
            completedBaseDeRhamTerm A B p M (q + 1) →ₗ[completedBaseRing B p]
              completedBaseDeRhamTerm A B p M q,
          ((khat 0).toAddMonoidHom.comp
                (completedBaseDeRhamDifferential A B p M S nabla 0) =
              (p : ℕ) • AddMonoidHom.id (completedBaseDeRhamTerm A B p M 0) -
                (ehat 0).toAddMonoidHom.comp (completedComparison A B p lam hp M c 0)) ∧
            ∀ q : ℕ,
              (completedBaseDeRhamDifferential A B p M S nabla q).comp
                    (khat q).toAddMonoidHom +
                  (khat (q + 1)).toAddMonoidHom.comp
                    (completedBaseDeRhamDifferential A B p M S nabla (q + 1)) =
                (p : ℕ) • AddMonoidHom.id (completedBaseDeRhamTerm A B p M (q + 1)) -
                  (ehat (q + 1)).toAddMonoidHom.comp
                    (completedComparison A B p lam hp M c (q + 1))) :=
  Exists.elim (exists_homotopyInverse_pthRootExtension_dividedPowerDifferentials_baseLinear
      B p lam hp S S' nabla hintegrable c hc_wedge hc_comm) fun e he ↦
    Exists.elim he.2.2.1 fun hcal hh ↦
      Exists.elim he.2.2.2 fun kcal hk ↦
        ⟨fun q ↦ completedLinearOfAddHom (R := (B : Type u)) p
            (restrictScalarsUnderlyingAddHom (e q))
            (fun b y ↦ (congrArg (restrictScalarsUnderlyingAddHom (e q))
              (IsScalarTower.algebraMap_smul (primeRing B p lam) b y).symm).trans
                (he.2.1 q b y)),
          fun q ↦ PAdicCompletion.mapAddHom_comp_eq_comp p (B : Type u) (B : Type u)
            (B : Type u) (B : Type u)
            (primeDeRhamDifferential A B p lam hp M S' nabla q)
            (restrictScalarsUnderlyingAddHom (e (q + 1)))
            (restrictScalarsUnderlyingAddHom (e q)) (baseDeRhamDifferential A B M S nabla q)
            (AddMonoidHom.ext fun y ↦ he.1 q y),
          ⟨fun q ↦ completedLinearOfAddHom (R := (B : Type u)) p
              (restrictScalarsUnderlyingAddHom (hcal q))
              (fun b y ↦ ((congrArg (restrictScalarsUnderlyingAddHom (hcal q))
                  (IsScalarTower.algebraMap_smul (primeRing B p lam) b y).symm).trans
                    (hh.2.2 q b y)).trans
                (IsScalarTower.algebraMap_smul (primeRing B p lam) b _)),
            PAdicCompletion.mapAddHom_comp_eq_nsmul_sub p (B : Type u) (B : Type u)
              (B : Type u) p (primeDeRhamDifferential A B p lam hp M S' nabla 0)
              (restrictScalarsUnderlyingAddHom (hcal 0))
              (restrictScalarsUnderlyingAddHom (e 0))
              (restrictScalarsUnderlyingAddHom (c 0))
              (underlyingAddHom_comp_eq_nsmul_sub p
                (algebraMap (B : Type u) (primeRing B p lam) ((p : ℕ) : (B : Type u)))
                (restrictScalars_lsmul_algebraMap_natCast A (B : Type u) (primeRing B p lam) p)
                _ (hcal 0) (e 0) (c 0) hh.1),
            fun q ↦ PAdicCompletion.mapAddHom_add_comp_eq_nsmul_sub p (B : Type u) (B : Type u)
              (B : Type u) (B : Type u) p (restrictScalarsUnderlyingAddHom (hcal q))
              (primeDeRhamDifferential A B p lam hp M S' nabla q)
              (primeDeRhamDifferential A B p lam hp M S' nabla (q + 1))
              (restrictScalarsUnderlyingAddHom (hcal (q + 1)))
              (restrictScalarsUnderlyingAddHom (e (q + 1)))
              (restrictScalarsUnderlyingAddHom (c (q + 1)))
              (underlyingAddHom_add_comp_eq_nsmul_sub p
                (algebraMap (B : Type u) (primeRing B p lam) ((p : ℕ) : (B : Type u)))
                (restrictScalars_lsmul_algebraMap_natCast A (B : Type u) (primeRing B p lam) p)
                (hcal q) _ _ (hcal (q + 1)) (e (q + 1)) (c (q + 1)) (hh.2.1 q))⟩,
          ⟨fun q ↦ completedLinearOfAddHom (R := (B : Type u)) p
              (restrictScalarsUnderlyingAddHom (kcal q)) (fun b x ↦ hk.2.2 q b x),
            PAdicCompletion.mapAddHom_comp_eq_nsmul_sub p (B : Type u) (B : Type u)
              (B : Type u) p (baseDeRhamDifferential A B M S nabla 0)
              (restrictScalarsUnderlyingAddHom (kcal 0))
              (restrictScalarsUnderlyingAddHom (c 0))
              (restrictScalarsUnderlyingAddHom (e 0))
              (underlyingAddHom_comp_eq_nsmul_sub p ((p : ℕ) : (B : Type u))
                (restrictScalars_lsmul_natCast A (B : Type u) p) _ (kcal 0) (c 0) (e 0) hk.1),
            fun q ↦ PAdicCompletion.mapAddHom_add_comp_eq_nsmul_sub p (B : Type u) (B : Type u)
              (B : Type u) (B : Type u) p (restrictScalarsUnderlyingAddHom (kcal q))
              (baseDeRhamDifferential A B M S nabla q)
              (baseDeRhamDifferential A B M S nabla (q + 1))
              (restrictScalarsUnderlyingAddHom (kcal (q + 1)))
              (restrictScalarsUnderlyingAddHom (c (q + 1)))
              (restrictScalarsUnderlyingAddHom (e (q + 1)))
              (underlyingAddHom_add_comp_eq_nsmul_sub p ((p : ℕ) : (B : Type u))
                (restrictScalars_lsmul_natCast A (B : Type u) p) (kcal q) _ _ (kcal (q + 1))
                (c (q + 1)) (e (q + 1)) (hk.2.1 q))⟩⟩

end Crystalline

end
