module

public import StacksFrontier.AlgebraicGeometry.ProperAmpleCohomology.CohomologyFinite
public import StacksFrontier.AlgebraicGeometry.ProperAmpleCohomology.SerreFiniteness

/-!
# Cohomology of a coherent module on a proper scheme with an ample invertible module, whole

[Stacks, Tag 0B5T] is a five-part statement, and this file states all five parts at once, in the
tag's own setting, so that the tag sits on a declaration asserting the whole of it.

Let `R` be a Noetherian ring, `f : X ⟶ Spec R` a proper morphism, `ℒ` an ample invertible
`𝒪_X`-module and `ℱ` a coherent `𝒪_X`-module. Then

1. the graded ring `A = ⨁_{d ≥ 0} H⁰(X, ℒ ^⊗ d)` is a finitely generated `R`-algebra;
2. there are an `r ≥ 0`, integers `d₁, …, d_r` and a surjection `⨁_{j} ℒ ^⊗ dⱼ ↠ ℱ`;
3. `H ᵖ(X, ℱ)` is a finite `R`-module for every `p`;
4. `H ᵖ(X, ℱ ⊗ ℒ ^⊗ d) = 0` for `p > 0` and all `d` large enough;
5. for every `k ∈ ℤ` the graded `A`-module `⨁_{d ≥ k} H⁰(X, ℱ ⊗ ℒ ^⊗ d)` is a finite `A`-module.

## How each clause is spelled

* **(1)** `A` is `Stacks.GradedSections.sectionRing ℒ = ⨁_{n ≥ 0} (𝟙_ X.Modules ⟶ ℒ ^⊗ n)`, the
  graded ring of [Stacks, Tag 01CV]; its summands are the global sections `H⁰(X, ℒ ^⊗ n)`, read
  as morphisms out of the monoidal unit (`Stacks.SectionRingGeometric`
  `.schemeGlobalSectionsAddEquiv` is the comparison with `Γ(ℒ ^⊗ n, ⊤)`). Its `R`-algebra
  structure is `Stacks.SectionRingZero.sectionRingZeroHom X ℒ`, the degree-zero inclusion
  `Γ(X, ⊤) →+* A`, composed with the ring map `R →+* Γ(X, ⊤)` that `f` induces on global
  functions; "finitely generated `R`-algebra" is `RingHom.FiniteType` of that composite.
* **(2)** The index `j` ranges over a type `ι` with `Finite ι` — the source's `r` is
  `Nat.card ι`, and `r = 0` is the empty type — the exponents are a function `d : ι → ℤ`, the
  direct sum is a `CategoryTheory.Limits.Bicone` together with a proof that it is a biproduct,
  and "surjection" is `Epi`. This is the shape clause (8) of [Stacks, Tag 01Q3] is formalized at.
* **(3)** `H ᵖ(X, ℱ)` is `Stacks.AlgebraicGeometry.GradedProperCohomology.cohomologyOf X p ℱ`,
  a module over `Γ(X, ⊤)`, and the `R`-module structure is restriction of scalars along the same
  ring map `R →+* Γ(X, ⊤)`.
* **(4)** One exponent `d₀` serves every positive degree at once, which is more than the source
  asks for.
* **(5)** `⨁_{d ≥ k} H⁰(X, ℱ ⊗ ℒ ^⊗ d)` is `Stacks.TwistedSections.twistModule (ℱ ⊗ ℒ ^⊗ k) ℒ`,
  whose degree-`m` summand is `H⁰(X, (ℱ ⊗ ℒ ^⊗ k) ⊗ ℒ ^⊗ m)`; as `m` runs over `ℕ` the source's
  degree `d = k + m` runs over the integers `≥ k`. Its `A`-module structure is the graded module
  of [Stacks, Tag 01CV], `Stacks.TwistedSections.instModule`.

## The route

Clauses (2) and (4) are proved in `./Basic.lean`, clause (3) in `./CohomologyFinite.lean` from
[Stacks, Tag 02O6], and clauses (1) and (5) in `./SerreFiniteness.lean` from the Serre bootstrap
of `./TwistGeneration.lean`. The source proves (1), (3), (4) and (5) by embedding `X` in
`ℙⁿ_R` and citing clause (5) of [Stacks, Tag 01YS]; none of the four goes through a projective
space here.

## Main results

* `Stacks.AlgebraicGeometry.ProperAmpleCohomology.coherent_proper_ample`: **[Stacks, Tag 0B5T]**,
  all five clauses.

## References

* [Stacks Project, Tag 0B5T](https://stacks.math.columbia.edu/tag/0B5T)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open Stacks.SheafOfModules.TensorSheafification
open Stacks.TensorPowers Stacks.GradedSections Stacks.TwistedSections
open Stacks.SectionRingGeometric Stacks.SectionRingZero
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.GradedProperCohomology (cohomologyOf specAlgebraRingHom)

universe u

namespace Stacks.AlgebraicGeometry.ProperAmpleCohomology

section Scheme

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive
  HasDerivedCategory.standard

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

/-- **[Stacks, Tag 0B5T].** Let `R` be a Noetherian ring, let `f : X ⟶ Spec R` be proper, let `ℒ`
be an ample invertible `𝒪_X`-module and let `ℱ` be a coherent `𝒪_X`-module. Then all five of the
tag's assertions hold:

1. the graded ring `A = ⨁_{d ≥ 0} H⁰(X, ℒ ^⊗ d)` is a finitely generated `R`-algebra;
2. there are a finite index type `ι`, exponents `d : ι → ℤ` and a surjection
   `⨁_{j ∈ ι} ℒ ^⊗ dⱼ ↠ ℱ`;
3. `H ᵖ(X, ℱ)` is a finite `R`-module for every `p`;
4. there is a `d₀` with `H ᵖ(X, ℱ ⊗ ℒ ^⊗ d) = 0` for every `d ≥ d₀` and every `p > 0`;
5. for every `k ∈ ℤ` the graded `A`-module `⨁_{d ≥ k} H⁰(X, ℱ ⊗ ℒ ^⊗ d)` is a finite `A`-module.

See the module documentation for the spelling of each clause. The five components are
`ringHomFiniteType_sectionRing`, `exists_epi_biproduct_tensorPowModule_of_isAmple`,
`moduleFinite_cohomology_of_isProper`, `exists_isZero_Hgroup_tensorPowTwist` and
`moduleFinite_twistModule`. -/
@[stacks 0B5T "all five clauses: the section ring is a finitely generated R-algebra, a finite \
direct sum of tensor powers of L surjects onto F, the cohomology of F is a finite R-module in \
every degree, the higher cohomology of the high twists of F vanishes, and the graded module of \
twisted sections in degrees at least k is a finite module over the section ring"]
theorem coherent_proper_ample {X : Scheme.{u}} {R : Type u} [CommRing R] [IsNoetherianRing R]
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] (F L : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] [Stacks.Ample.IsInvertibleModule X L]
    (hL : Stacks.Ample.IsAmple X L) :
    RingHom.FiniteType
        ((sectionRingZeroHom X L).comp (specAlgebraRingHom R f)) ∧
      (∃ (ι : Type u) (_ : Finite ι) (d : ι → ℤ)
        (b : Bicone fun j : ι => Stacks.Ample.tensorPowModule X L (d j)) (_ : b.IsBilimit)
        (p : b.pt ⟶ F), Epi p) ∧
      (∀ p : ℕ, Module.Finite R
        ((ModuleCat.restrictScalars (specAlgebraRingHom R f)).obj (cohomologyOf X p F))) ∧
      (∃ d₀ : ℕ, ∀ d p : ℕ, d₀ ≤ d → 0 < p →
        IsZero (Hgroup X.ringCatSheaf ⊤ p
          (Stacks.RelativeVeryAmple.tensorModules X F
            (Stacks.Ample.tensorPowModule X L (d : ℤ))))) ∧
      (∀ k : ℤ, Module.Finite (sectionRing L)
        (twistModule (F ⊗ Stacks.Ample.tensorPowModule X L k) L)) :=
  ⟨ringHomFiniteType_sectionRing f L hL,
    exists_epi_biproduct_tensorPowModule_of_isAmple F L hL,
    fun p => moduleFinite_cohomology_of_isProper f F p,
    exists_isZero_Hgroup_tensorPowTwist f F L hL,
    fun k => moduleFinite_twistModule f F L hL k⟩

end Scheme

end Stacks.AlgebraicGeometry.ProperAmpleCohomology

end
