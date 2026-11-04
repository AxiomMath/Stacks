module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.CompletedPthRootExtension

/-!
# The reverse map of Tag 07N1 through the named integrating homotopy

For the divided power ring `B' = B[z]⟨ξ⟩/(ξ - (z^p - λ))` over a divided power ring `B`, and a
`B`-module `M` with an integrable connection,
`Crystalline.exists_homotopyInverse_baseChangeDeRhamMap`
at `a = p` produces a reverse map `e_M^•` of the canonical map of de Rham complexes
`c_M^• : M ⊗_B Ω^•_{B/A,γ} ⟶ M' ⊗_{B'} Ω^•_{B'/A,γ'}` and two homotopies, all existentially.
This module states the same conclusion with the homotopy on the target named:
`Crystalline.PthRootExtension.pthRootHomotopy`, the integrating homotopy built from the operator
`θ` of the proof of [Stacks, Lemma 60.25.3, Tag 07N1].  Then `c_M^• ∘ e_M^• = p - d h - h d`
and `e_M^• ∘ c_M^• = p`, and since `c_M^•` is injective and `h` is natural in `M`, the reverse
maps of the members of an inverse system of modules are compatible.  That is what the passage to
the `p`-adic completions consumes.

## Main definitions

* `Crystalline.PthRootExtension.pthRootHomotopy` — the integrating homotopy of the extension,
  as an additive map on the terms of the de Rham complex of `B'`.

## Main results

* `Crystalline.PthRootExtension.pthRootHomotopy_naturality` — it is natural in the module.
* `Crystalline.PthRootExtension.injective_pthRootComparison` — the canonical map `c_M^•` is
  injective.
* `Crystalline.PthRootExtension.exists_reverse_pthRootExtension` — the reverse map, with
  `e ∘ c = p` and `c ∘ e = p - d h - h d`.

## References

* [Stacks Project, Lemma 60.25.3, Tag 07N1](https://stacks.math.columbia.edu/tag/07N1)
* [Stacks Project, Lemma 60.25.2, Tag 07Q7](https://stacks.math.columbia.edu/tag/07Q7)
-/

@[expose] public noncomputable section

open DividedPowers Stacks.DeRham.DifferentialDescent

open scoped TensorProduct

universe u w

namespace Crystalline

namespace PthRootExtension

variable (A : Type u) [CommRing A] (B : DividedPowerRing.{u}) [Algebra A (B : Type u)] (p : ℕ)
  (lam : (B : Type u)) (hp : p ≠ 0)

/-- The extension of a connection `∇` on a `B`-module to the de Rham complex of `B`. -/
abbrev baseExtended (M : Type w) [AddCommGroup M] [Module (B : Type u) M]
    (S : SourceDeRham A (B : Type u))
    (nabla : Connection A (B : Type u) (baseFormsProjection A B) M) :=
  extendedConnection S (baseFormsProjection A B) (Submodule.mkQ_surjective _)
    (baseFormsGenerationHypothesis A B S) nabla

/-- The extension of the base change of `∇` to the de Rham complex of `B'`. -/
abbrev primeExtended (M : Type w) [AddCommGroup M] [Module (B : Type u) M]
    (S' : SourceDeRham A (primeRing B p lam))
    (nabla : Connection A (B : Type u) (baseFormsProjection A B) M) :=
  extendedConnection S' (primeFormsProjection A B p lam hp) (Submodule.mkQ_surjective _)
    (primeFormsGenerationHypothesis A B p lam hp S') (primeConnection A B p lam hp M nabla)

/-- **The integrating homotopy of the extension `B → B'`** in degree `q`: it extracts the
coefficient of `dz` through the decomposition `Ω¹_{B'/A,γ'} = (B' ⊗_B Ω¹_{B/A,γ}) ⊕ B' dz` and
applies the operator `θ` of the proof of [Stacks, Tag 07N1] to it. -/
abbrev pthRootHomotopy [Nontrivial (XiAlg B)] (M : Type w) [AddCommGroup M]
    [Module (B : Type u) M] (q : ℕ) :
    RestrictScalars A (primeRing B p lam) (primeDeRhamTerm A B p lam hp M (q + 1)) →ₗ[A]
      RestrictScalars A (primeRing B p lam) (primeDeRhamTerm A B p lam hp M q) :=
  integratingHomotopyMap (A := A) (primeFormsProjection A B p lam hp)
    (primeFormsComparison A B p lam hp) (zElt B p lam) (pthRootDzDecomposition A B p lam hp)
    (theta B p lam hp) M q

/-- The map induced on the terms of the de Rham complex of `B'` by a `B`-linear map of modules. -/
abbrev primeTermMap {M N : Type w} [AddCommGroup M] [Module (B : Type u) M] [AddCommGroup N]
    [Module (B : Type u) N] (φ : M →ₗ[(B : Type u)] N) (q : ℕ) :
    primeDeRhamTerm A B p lam hp M q →ₗ[primeRing B p lam] primeDeRhamTerm A B p lam hp N q :=
  TensorProduct.map (φ.baseChange (primeRing B p lam)) LinearMap.id

/-- The map induced on the terms of the de Rham complex of `B` by a `B`-linear map of modules. -/
abbrev baseTermMap {M N : Type w} [AddCommGroup M] [Module (B : Type u) M] [AddCommGroup N]
    [Module (B : Type u) N] (φ : M →ₗ[(B : Type u)] N) (q : ℕ) :
    baseDeRhamTerm A B M q →ₗ[(B : Type u)] baseDeRhamTerm A B N q :=
  TensorProduct.map φ LinearMap.id

/-- **The integrating homotopy is natural in the module.** -/
theorem pthRootHomotopy_naturality [Nontrivial (XiAlg B)] {M N : Type w} [AddCommGroup M]
    [Module (B : Type u) M] [AddCommGroup N] [Module (B : Type u) N] (φ : M →ₗ[(B : Type u)] N)
    (q : ℕ) (y : primeDeRhamTerm A B p lam hp M (q + 1)) :
    pthRootHomotopy A B p lam hp N q (primeTermMap A B p lam hp φ (q + 1) y) =
      primeTermMap A B p lam hp φ q (pthRootHomotopy A B p lam hp M q y) :=
  integratingHomotopyMap_naturality (A := A) (primeFormsProjection A B p lam hp)
    (primeFormsComparison A B p lam hp) (zElt B p lam) (pthRootDzDecomposition A B p lam hp)
    (theta B p lam hp) φ q y

/-- **The canonical map `c_M^•` of the extension is injective**, the extension being split. -/
theorem injective_pthRootComparison [Nontrivial (XiAlg B)] (M : Type w) [AddCommGroup M]
    [Module (B : Type u) M] (q : ℕ)
    (c : RestrictScalars A (B : Type u) (baseDeRhamTerm A B M q) →ₗ[A]
      RestrictScalars A (primeRing B p lam) (primeDeRhamTerm A B p lam hp M q))
    (hc : ∀ (m : M) (omega : Fin q → baseForms A B),
      c (m ⊗ₜ[(B : Type u)] exteriorPower.ιMulti (B : Type u) q omega) =
        (1 ⊗ₜ[(B : Type u)] m) ⊗ₜ[primeRing B p lam]
          exteriorPower.ιMulti (primeRing B p lam) q ((primeFormsComparison A B p lam hp) ∘ omega))
              :
    Function.Injective c :=
  injective_of_dzDecomposition (primeFormsProjection A B p lam hp)
    (primeFormsComparison A B p lam hp) (zElt B p lam) (pthRootDzDecomposition A B p lam hp)
    (universallyInjective_toPrimeRing B p lam hp) q c hc

/-- **Tag 07N1 for the uncompleted extension, with the homotopy on the target named.**  For a
`B`-module `M` with an integrable connection and the canonical map `c_M^•` of de Rham complexes
(pinned by its values on wedges and its commuting with the differentials), there is a
`B`-linear map of complexes `e_M^•` in the opposite direction with `e_M^• ∘ c_M^• = p` and
`c_M^• ∘ e_M^• = p - d h - h d` for the integrating homotopy `h` of the extension.  This is
`Crystalline.exists_homotopyInverse_baseChangeDeRhamMap_integrating` at `a = p`, with the
operator `θ` and all of the computations of the proof of [Stacks, Tag 07N1] supplied. -/
theorem exists_reverse_pthRootExtension [Nontrivial (XiAlg B)] [Fact p.Prime]
    [Algebra (IntegersAtPrime p) (B : Type u)] (M : Type w) [AddCommGroup M]
    [Module (B : Type u) M]
    (S : SourceDeRham A (B : Type u)) (S' : SourceDeRham A (primeRing B p lam))
    (nabla : Connection A (B : Type u) (baseFormsProjection A B) M)
    (hintegrable : Connection.IsIntegrable S (baseFormsProjection A B) (Submodule.mkQ_surjective _)
      (baseFormsGenerationHypothesis A B S) nabla)
    (c : ∀ q : ℕ,
      RestrictScalars A (B : Type u) (baseDeRhamTerm A B M q) →ₗ[A]
        RestrictScalars A (primeRing B p lam) (primeDeRhamTerm A B p lam hp M q))
    (hc_wedge : ∀ (q : ℕ) (m : M) (omega : Fin q → (baseForms A B)),
      c q (m ⊗ₜ[(B : Type u)] exteriorPower.ιMulti (B : Type u) q omega) =
        (1 ⊗ₜ[(B : Type u)] m) ⊗ₜ[primeRing B p lam]
          exteriorPower.ιMulti (primeRing B p lam) q ((primeFormsComparison A B p lam hp) ∘ omega))
    (hc_comm : ∀ (q : ℕ) (x : M ⊗[(B : Type u)] (⋀[(B : Type u)]^q (baseForms A B))),
      c (q + 1) ((baseExtended A B M S nabla).toLinearMap q x) =
        (primeExtended A B p lam hp M S' nabla).toLinearMap q (c q x)) :
    ∃ e : ∀ q : ℕ,
      RestrictScalars A (primeRing B p lam) (primeDeRhamTerm A B p lam hp M q) →ₗ[A]
        RestrictScalars A (B : Type u) (baseDeRhamTerm A B M q),
      (∀ (q : ℕ) (x : RestrictScalars A (primeRing B p lam) (primeDeRhamTerm A B p lam hp M q)),
        e (q + 1) ((primeExtended A B p lam hp M S' nabla).toLinearMap q x) =
          (baseExtended A B M S nabla).toLinearMap q (e q x)) ∧
      (∀ (q : ℕ) (b : (B : Type u))
          (y : RestrictScalars A (primeRing B p lam) (primeDeRhamTerm A B p lam hp M q)),
        e q (RestrictScalars.lsmul A (primeRing B p lam) (primeDeRhamTerm A B p lam hp M q)
            (algebraMap (B : Type u) (primeRing B p lam) b) y) =
          RestrictScalars.lsmul A (B : Type u) (baseDeRhamTerm A B M q) b (e q y)) ∧
      (∀ (q : ℕ) (x : RestrictScalars A (B : Type u) (baseDeRhamTerm A B M q)),
        e q (c q x) = RestrictScalars.lsmul A (B : Type u) (baseDeRhamTerm A B M q)
          ((p : ℕ) : (B : Type u)) x) ∧
      (∀ x : RestrictScalars A (primeRing B p lam) (primeDeRhamTerm A B p lam hp M 0),
        pthRootHomotopy A B p lam hp M 0 ((primeExtended A B p lam hp M S' nabla).toLinearMap 0 x) =
          RestrictScalars.lsmul A (primeRing B p lam) (primeDeRhamTerm A B p lam hp M 0)
              (algebraMap (B : Type u) (primeRing B p lam) ((p : ℕ) : (B : Type u))) x -
            c 0 (e 0 x)) ∧
      ∀ (q : ℕ)
        (x : RestrictScalars A (primeRing B p lam) (primeDeRhamTerm A B p lam hp M (q + 1))),
        (show RestrictScalars A (primeRing B p lam) (primeDeRhamTerm A B p lam hp M (q + 1)) from
            (primeExtended A B p lam hp M S' nabla).toLinearMap q
              (pthRootHomotopy A B p lam hp M q x)) +
            pthRootHomotopy A B p lam hp M (q + 1)
              ((primeExtended A B p lam hp M S' nabla).toLinearMap (q + 1) x) =
          RestrictScalars.lsmul A (primeRing B p lam) (primeDeRhamTerm A B p lam hp M (q + 1))
              (algebraMap (B : Type u) (primeRing B p lam) ((p : ℕ) : (B : Type u))) x -
            c (q + 1) (e (q + 1) x) :=
  let hpz := partialZValues_of_isDpowDifferential (baseFormsProjection A B)
    (pthRootDzDecomposition A B p lam hp)
    (primeFormsComparison_dividedPowerDifferential A B p lam hp) hp
    (isDpowDifferential_dividedPowerDifferentials B p lam hp)
  exists_homotopyInverse_baseChangeDeRhamMap_integrating
    S S' (baseFormsProjection A B) (primeFormsProjection A B p lam hp)
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


end PthRootExtension

end Crystalline
