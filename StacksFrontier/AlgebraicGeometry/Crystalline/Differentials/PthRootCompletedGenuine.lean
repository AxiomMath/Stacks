module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.PthRootCompletedLinear
public import
    StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.CompletionComparisonLevelwise
public import
    StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.CompletionComparisonDegreewise

/-!
# Tag 07N1 with the divided power differentials of the completed ring

In the situation of [Stacks, Lemma 60.25.3, Tag 07N1] the target of the comparison is the completed
de Rham complex `M ⊗̂_D Ω^•_{D'}` of the ring

`D' = (D[z]⟨ξ⟩ / (ξ - (z^p - λ)))^∧`,

whose `Ω_{D'}` is the `p`-adic completion of the module of divided power differentials **of `D'`
itself**.  What
`Crystalline.exists_completedLinearHomotopyInverse_pthRootExtension_dividedPowerDifferentials`
produces is the same conclusion with the differentials of the *uncompleted* extension
`B' = B[z]⟨ξ⟩/(ξ - (z^p - λ))` completed instead.  This module closes that gap.

## How

The structure map `B' → D'` is a divided power morphism, so by [Stacks, Tag 07KJ] it induces a
canonical map of de Rham complexes

`Φ^• : M' ⊗_{B'} Ω^•_{B'/A,γ'} ⟶ M'' ⊗_{D'} Ω^•_{D'/A,γ̂'}`

which commutes with the two extended connection differentials — that commutation is part of
`Crystalline.existsUnique_baseChangeDeRhamMap` and needs nothing new.  The content is that `Φ^•`
becomes an **isomorphism after `p`-adic completion**, and that is [Stacks, Lemma 60.20.1, Tag 07KK]
in every exterior degree:

* in degree one, `Ω_{B'/A,γ'} → Ω_{D'/A,γ̂'}` is bijective modulo `pⁿ` for every deep `n`
  (`Crystalline.bijective_levelMap_completionDifferentialsBaseChange`);
* exterior powers and a tensor factor preserve that
  (`Crystalline.bijective_reduceModIdeal_exteriorPowerMap`,
  `Crystalline.bijective_reduceModIdeal_lTensor`);
* extending scalars from `B'` to `D'` changes nothing at any level
  (`Crystalline.bijective_reduceModIdeal_tensorUnit`);
* and bijectivity at all deep levels makes the completion bijective
  (`Crystalline.PAdicCompletion.bijective_mapAddHom_of_levelMap`).

Transporting `ê`, `ĥ` and `k̂` along the resulting isomorphism then gives the conclusion for the
genuine objects: `ê` becomes `ê ∘ Φ̂⁻¹`, the homotopy `ĥ` on the target side becomes
`Φ̂ ∘ ĥ ∘ Φ̂⁻¹`, and the homotopy `k̂` on the source side is unchanged.

## Main definitions

* `Crystalline.PthRootExtension.completedPrimeDPRing` — the ring `D'` with its divided power ideal
  `Ĵ'` and divided powers `γ̂'` of [Stacks, Tag 07KD].
* `Crystalline.PthRootExtension.genuinePrimeForms` — `Ω_{D'/A,γ̂'}`.
* `Crystalline.PthRootExtension.genuineFormsComparison` — the comparison `ψ'' : Ω_{B'} ⟶ Ω_{D'}`.

## References

* [Stacks Project, Lemma 60.25.3, Tag 07N1](https://stacks.math.columbia.edu/tag/07N1)
* [Stacks Project, Lemma 60.19.1, Tag 07KD](https://stacks.math.columbia.edu/tag/07KD)
* [Stacks Project, Lemma 60.20.1, Tag 07KK](https://stacks.math.columbia.edu/tag/07KK)
* [Stacks Project, Remark 60.17.4, Tag 07KJ](https://stacks.math.columbia.edu/tag/07KJ)
-/

@[expose] public noncomputable section

open DividedPowers Stacks.DeRham.DifferentialDescent

open scoped TensorProduct

universe u w

namespace Crystalline

namespace PthRootExtension

section Setting

variable (A : Type u) [CommRing A] (B : DividedPowerRing.{u}) [Algebra A (B : Type u)]
  (p : ℕ) (lam : (B : Type u)) (hp : p ≠ 0)

include hp in
/-- **`p` is nilpotent modulo the divided power ideal `J'` of the extension** as soon as it is
nilpotent modulo that of `B`: a power of `p` lying in `J` has its image in `J'`, because the
structure map `B → B'` is a divided power morphism. -/
theorem isNilpotent_mk_primeIdeal
    (hpnil : IsNilpotent (Ideal.Quotient.mk B.ideal ((p : ℕ) : (B : Type u)))) :
    IsNilpotent (Ideal.Quotient.mk (primeIdeal B p lam)
      ((p : ℕ) : primeRing B p lam)) := by
  obtain ⟨n, hn⟩ := hpnil
  refine ⟨n, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  have hcast : ((p : ℕ) : primeRing B p lam) ^ n =
      algebraMap (B : Type u) (primeRing B p lam) (((p : ℕ) : (B : Type u)) ^ n) := by
    rw [map_pow, map_natCast]
  rw [hcast]
  refine (isDPMorphism_algebraMap_primeDividedPowers B p lam hp).ideal_comp
    (Ideal.mem_map_of_mem _ ?_)
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow]
  exact hn

/-- The ring `D'` of [Stacks, Tag 07N1]: the `p`-adic completion of
`B[z]⟨ξ⟩/(ξ - (z^p - λ))`. -/
abbrev completedPrimeRingSelf : Type u :=
  AdicCompletion (pAdicIdeal (A := primeRing B p lam) p) (primeRing B p lam)

variable (hpnil : IsNilpotent (Ideal.Quotient.mk B.ideal ((p : ℕ) : (B : Type u))))

include hp hpnil in
/-- The divided power ideal `Ĵ'` of `D'`, the kernel of `D' → B'/J'`. -/
abbrev completedPrimeIdeal : Ideal (completedPrimeRingSelf B p lam) :=
  DividedPowers.completionIdeal (primeIdeal B p lam) p
    (isNilpotent_mk_primeIdeal B p lam hp hpnil)

include hp hpnil in
/-- The divided powers `γ̂'` on `Ĵ'`, extending `γ'` by [Stacks, Tag 07KD]. -/
abbrev completedPrimeDividedPowers :
    DividedPowers (completedPrimeIdeal B p lam hp hpnil) :=
  (DividedPowers.completedDividedPowers (primeIdeal B p lam)
    (primeDividedPowers B p lam hp) p (isNilpotent_mk_primeIdeal B p lam hp hpnil)).1

include hp hpnil in
/-- The ring `D'` as a divided power ring `(D', Ĵ', γ̂')`. -/
abbrev completedPrimeDPRing : DividedPowerRing.{u} :=
  .of (completedPrimeRingSelf B p lam) (completedPrimeIdeal B p lam hp hpnil)
    (completedPrimeDividedPowers B p lam hp hpnil)

include hp hpnil in
/-- **`Ω_{D'/A,γ̂'}`, the divided power differentials of the completed ring `D'`.**  Its `p`-adic
completion is the module `Ω_{D'}` of [Stacks, Tag 07N1]. -/
abbrev genuinePrimeForms : Type u :=
  dividedPowerDifferentials (A := A) (completedPrimeDividedPowers B p lam hp hpnil)

include hp hpnil in
/-- The quotient map onto `Ω_{D'/A,γ̂'}`. -/
abbrev genuinePrimeFormsProjection :
    Ω[completedPrimeRingSelf B p lam⁄A] →ₗ[completedPrimeRingSelf B p lam]
      genuinePrimeForms A B p lam hp hpnil :=
  (dividedPowerDifferentialRelations (A := A)
    (completedPrimeDividedPowers B p lam hp hpnil)).mkQ

include hp hpnil in
/-- The projection onto `Ω_{D'/A,γ̂'}` satisfies the generation hypothesis of Tag 07HY, so the de
Rham differential descends to it. -/
theorem genuinePrimeFormsGenerationHypothesis
    (S'' : SourceDeRham A (completedPrimeRingSelf B p lam)) :
    S''.GenerationHypothesis (genuinePrimeFormsProjection A B p lam hp hpnil) :=
  dividedPowerDifferentials_generationHypothesis
    (completedPrimeDPRing B p lam hp hpnil) S''

include hp hpnil in
/-- **The comparison `ψ'' : Ω_{B'/A,γ'} ⟶ Ω_{D'/A,γ̂'}`** of divided power one-forms along the
structure map `B' → D'`, semilinear over it. -/
def genuineFormsComparison :
    primeForms A B p lam hp →ₛₗ[algebraMap (primeRing B p lam)
        (completedPrimeRingSelf B p lam)]
      genuinePrimeForms A B p lam hp hpnil where
  toFun := completionDifferentialsMap (A := A) (primeIdeal B p lam)
    (primeDividedPowers B p lam hp) p (isNilpotent_mk_primeIdeal B p lam hp hpnil)
  map_add' := (completionDifferentialsMap (A := A) (primeIdeal B p lam)
    (primeDividedPowers B p lam hp) p
    (isNilpotent_mk_primeIdeal B p lam hp hpnil)).map_add
  map_smul' r omega :=
    (completionDifferentialsMap_smul (A := A) (primeIdeal B p lam)
        (primeDividedPowers B p lam hp) p
        (isNilpotent_mk_primeIdeal B p lam hp hpnil) r omega).trans
      (congrArg (fun c ↦ c • completionDifferentialsMap (A := A) (primeIdeal B p lam)
          (primeDividedPowers B p lam hp) p
          (isNilpotent_mk_primeIdeal B p lam hp hpnil) omega)
        (algebraMap_pAdicCompletion_eq_of p r)).symm

include hp hpnil in
/-- The comparison `ψ''` is compatible with the two universal divided power differentials, which
is the hypothesis of [Stacks, Tag 07KJ]. -/
theorem genuineFormsComparison_dividedPowerDifferential (r : primeRing B p lam) :
    genuineFormsComparison A B p lam hp hpnil
        (primeFormsProjection A B p lam hp (KaehlerDifferential.D A (primeRing B p lam) r)) =
      genuinePrimeFormsProjection A B p lam hp hpnil
        (KaehlerDifferential.D A (completedPrimeRingSelf B p lam)
          (algebraMap (primeRing B p lam) (completedPrimeRingSelf B p lam) r)) := by
  show completionDifferentialsMap (A := A) (primeIdeal B p lam)
    (primeDividedPowers B p lam hp) p (isNilpotent_mk_primeIdeal B p lam hp hpnil)
      (dividedPowerDifferential (A := A) (primeDividedPowers B p lam hp) r) =
    dividedPowerDifferential (A := A) (completedPrimeDividedPowers B p lam hp hpnil)
      (algebraMap (primeRing B p lam) (completedPrimeRingSelf B p lam) r)
  rw [completionDifferentialsMap_d, algebraMap_pAdicCompletion_eq_of]

include hp hpnil in
/-- The comparison `ψ''` carries the universal divided power differential of `r` to that of its
image in `D'`. -/
theorem genuineFormsComparison_d (r : primeRing B p lam) :
    genuineFormsComparison A B p lam hp hpnil
        (dividedPowerDifferential (A := A) (primeDividedPowers B p lam hp) r) =
      dividedPowerDifferential (A := A) (completedPrimeDividedPowers B p lam hp hpnil)
        (algebraMap (primeRing B p lam) (completedPrimeRingSelf B p lam) r) := by
  exact genuineFormsComparison_dividedPowerDifferential A B p lam hp hpnil r

end Setting

/-! ### The terms of the genuine complex -/

section Terms

variable (A : Type u) [CommRing A] (B : DividedPowerRing.{u}) [Algebra A (B : Type u)]
  (p : ℕ) (lam : (B : Type u)) (hp : p ≠ 0)
  (hpnil : IsNilpotent (Ideal.Quotient.mk B.ideal ((p : ℕ) : (B : Type u))))
  (M : Type w) [AddCommGroup M] [Module (B : Type u) M]

/-- The module `M` base changed to `D'`, in the iterated presentation
`D' ⊗_{B'} (B' ⊗_B M)` the base-change machinery of [Stacks, Tag 07KJ] uses. -/
abbrev genuinePrimeModule : Type (max u w) :=
  completedPrimeRingSelf B p lam ⊗[primeRing B p lam]
    (primeRing B p lam ⊗[(B : Type u)] M)

include hp hpnil in
/-- **The degree-`q` term `M ⊗_D Ω^q_{D'/A,γ̂'}` of the genuine de Rham complex of `D'`**, whose
`p`-adic completion is the degree-`q` term of the target complex of [Stacks, Tag 07N1]. -/
abbrev genuinePrimeDeRhamTerm (q : ℕ) : Type (max u w) :=
  genuinePrimeModule B p lam M ⊗[completedPrimeRingSelf B p lam]
    (⋀[completedPrimeRingSelf B p lam]^q (genuinePrimeForms A B p lam hp hpnil))

include hp hpnil in
/-- **The degree-`q` term `M ⊗̂_D Ω^q_{D'}` of the target complex of [Stacks, Tag 07N1]**, the
`p`-adic completion of the preceding one. -/
abbrev completedGenuinePrimeDeRhamTerm (q : ℕ) : Type (max u w) :=
  AdicCompletion (pAdicIdeal (A := completedPrimeRingSelf B p lam) p)
    (genuinePrimeDeRhamTerm A B p lam hp hpnil M q)

include hp hpnil in
/-- **The comparison `Ω_{B/A,δ} ⟶ Ω_{D'/A,γ̂'}`**, the composite of the comparison along
`B → B'` with the comparison along `B' → D'`. -/
def genuineComposedComparison :
    baseForms A B →ₛₗ[algebraMap (B : Type u) (completedPrimeRingSelf B p lam)]
      genuinePrimeForms A B p lam hp hpnil where
  toFun := fun omega ↦ genuineFormsComparison A B p lam hp hpnil
    (primeFormsComparison A B p lam hp omega)
  map_add' omega omega' := by
    rw [map_add, map_add]
  map_smul' b omega := by
    rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ,
      IsScalarTower.algebraMap_apply (B : Type u) (primeRing B p lam)
        (completedPrimeRingSelf B p lam) b]

/-- The composed comparison of one-forms as a formula. -/
@[simp]
theorem genuineComposedComparison_apply (omega : baseForms A B) :
    genuineComposedComparison A B p lam hp hpnil omega =
      genuineFormsComparison A B p lam hp hpnil
        (primeFormsComparison A B p lam hp omega) :=
  rfl

include hp hpnil in
/-- The composite comparison is compatible with the two universal divided power differentials,
which is the hypothesis of [Stacks, Tag 07KJ] for the composite. -/
theorem genuineComposedComparison_dividedPowerDifferential (b : (B : Type u)) :
    genuineComposedComparison A B p lam hp hpnil
        (baseFormsProjection A B (KaehlerDifferential.D A (B : Type u) b)) =
      genuinePrimeFormsProjection A B p lam hp hpnil
        (KaehlerDifferential.D A (completedPrimeRingSelf B p lam)
          (algebraMap (B : Type u) (completedPrimeRingSelf B p lam) b)) := by
  show genuineFormsComparison A B p lam hp hpnil (primeFormsComparison A B p lam hp
      (dividedPowerDifferential (A := A) B.dividedPowers b)) =
    dividedPowerDifferential (A := A) (completedPrimeDividedPowers B p lam hp hpnil)
      (algebraMap (B : Type u) (completedPrimeRingSelf B p lam) b)
  rw [primeFormsComparison_dividedPowerDifferential A B p lam hp b,
    genuineFormsComparison_d A B p lam hp hpnil
      (algebraMap (B : Type u) (primeRing B p lam) b),
    ← IsScalarTower.algebraMap_apply (B : Type u) (primeRing B p lam)
      (completedPrimeRingSelf B p lam) b]

end Terms

/-! ### The comparison along `B' → D'` is an isomorphism after completion -/

section Bijectivity

variable (A : Type u) [CommRing A] (B : DividedPowerRing.{u}) [Algebra A (B : Type u)]
  (p : ℕ) (lam : (B : Type u)) (hp : p ≠ 0)
  (hpnil : IsNilpotent (Ideal.Quotient.mk B.ideal ((p : ℕ) : (B : Type u))))
  (M : Type w) [AddCommGroup M] [Module (B : Type u) M]

include hp hpnil in
/-- **The canonical degreewise map to the genuine complex becomes an isomorphism after `p`-adic
completion.**

This is `Crystalline.bijective_mapAddHom_of_tmul_ιMulti` — [Stacks, Lemma 60.20.1, Tag 07KK] in
every exterior degree and after tensoring — read for the divided power ring
`B' = B[z]⟨ξ⟩/(ξ - (z^p - λ))` and the module `B' ⊗_B M`. -/
theorem bijective_mapAddHom_of_wedge [Fact p.Prime]
    [Algebra (DividedPowers.IntegersAtPrime p) A] (q : ℕ)
    (Phi : primeDeRhamTerm A B p lam hp M q →+
      genuinePrimeDeRhamTerm A B p lam hp hpnil M q)
    (hwedge : ∀ (w : primeRing B p lam ⊗[(B : Type u)] M)
        (omega : Fin q → primeForms A B p lam hp),
      Phi (w ⊗ₜ[primeRing B p lam] exteriorPower.ιMulti (primeRing B p lam) q omega) =
        ((1 : completedPrimeRingSelf B p lam) ⊗ₜ[primeRing B p lam] w)
          ⊗ₜ[completedPrimeRingSelf B p lam]
            exteriorPower.ιMulti (completedPrimeRingSelf B p lam) q
              (genuineFormsComparison A B p lam hp hpnil ∘ omega)) :
    Function.Bijective (PAdicCompletion.mapAddHom p (primeRing B p lam)
      (completedPrimeRingSelf B p lam) Phi) :=
  bijective_mapAddHom_of_tmul_ιMulti (A := A) (primeIdeal B p lam)
    (primeDividedPowers B p lam hp) p (isNilpotent_mk_primeIdeal B p lam hp hpnil)
    (primeRing B p lam ⊗[(B : Type u)] M) q Phi hwedge

end Bijectivity

end PthRootExtension

end Crystalline

end
