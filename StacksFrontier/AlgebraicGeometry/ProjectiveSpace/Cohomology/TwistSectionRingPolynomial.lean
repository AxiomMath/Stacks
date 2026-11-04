module

public import StacksFrontier.AlgebraicGeometry.ProjTwistSectionRing.Bijectivity
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TwistGlobalSectionsPolynomial

/-!
# `⨁_{k ≥ 0} Γ(ℙⁿ_R, 𝒪(k)) = R[T₀, …, Tₙ]` as graded rings

Let `R` be a commutative ring, `n ≥ 0`, and `S = R[T₀, …, Tₙ]` with its grading by total degree,
so that `ℙⁿ_R = Proj S`. The canonical graded ring homomorphism of [Stacks, Tag 01MP]

`S →+* ⨁_{k ≥ 0} Γ(ℙⁿ_R, 𝒪(k))`,

which in degree `k` sends a homogeneous polynomial `a` to the section `a / 1`, is an
**isomorphism**. Its degreewise bijectivity is
`Stacks.ProjectiveSpace.Cohomology.bijective_degreeSection_mvPolynomial`; what is added here is
that the degreewise bijections assemble, so that the identification is one of graded *rings* — in
particular of graded `S`-modules — and not merely of `R`-modules in each degree.

This is the identification the source uses without stating it, under the name "our computations
in Section [Stacks, Tag 01XS]": it is the base case of the sandwich in the proof of
[Stacks, Tag 01YS] clause (5), where the module
`N_k = ⨁_{d ≥ k} H⁰(ℙⁿ_R, ⨁_j 𝒪(d_j + d))` is identified with `⨁_j S(d_j)` for `k` small, and
hence is finite over `S`.

## Main definitions

* `Stacks.ProjectiveSpace.Cohomology.polynomialSectionsRingEquiv`: **the graded ring isomorphism
  `R[T₀, …, Tₙ] ≅ ⨁_{k ≥ 0} Γ(ℙⁿ_R, 𝒪(k))`.**

## Main results

* `Stacks.ProjectiveSpace.Cohomology.coe_polynomialSectionsRingEquiv`: the isomorphism *is* the
  canonical ring map of [Stacks, Tag 01MP], not a map built to be an isomorphism.
* `Stacks.ProjectiveSpace.Cohomology.polynomialSectionsRingEquiv_apply_homogeneous`: on a
  homogeneous polynomial of degree `k` it is the canonical section, landed in the degree-`k`
  summand — so the isomorphism is graded.
* `Stacks.ProjectiveSpace.Cohomology.moduleFinite_polynomialTwistSectionRing`: the graded section
  ring is a finite `S`-module, `S` acting through the isomorphism.

## What is not claimed

No `stacks` attribute is attached, and none fits. [Stacks, Tag 01MP] is the construction of the
graded ring map and says nothing about bijectivity; [Stacks, Tag 01XT] computes
`H^q(ℙⁿ_R, 𝒪(d))` *as `R`-modules*, in each degree separately, and its own multiplicative
refinement [Stacks, Tag 01XV] is about multiplication by a homogeneous `f` on the monomial Čech
model, not about the section ring. The source states the graded identification nowhere as a
lemma: the proof of [Stacks, Tag 01YS] clause (5) cites "our computations in Section
[Stacks, Tag 01XS]" for it. So this is untagged infrastructure.

Nothing here proves [Stacks, Tag 01YS] clause (5): the sandwich also needs the truncation
`⨁_{d ≥ k}` and the shift `S(d_j)` of the identification, and the finiteness transfer along the
surjection, none of which is done here.

## References

* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
* [Stacks Project, Tag 01XS](https://stacks.math.columbia.edu/tag/01XS)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite DirectSum
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.ProjTwistSectionRing
open AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

namespace Stacks.ProjectiveSpace.Cohomology

/-- **`⨁_{k ≥ 0} Γ(ℙⁿ_R, 𝒪(k)) = R[T₀, …, Tₙ]` as graded rings.** -/
def polynomialSectionsRingEquiv (R : Type u) [CommRing R] (n : ℕ) :
    letI := gradedRing (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    MvPolynomial (Fin (n + 1)) R ≃+*
      (⨁ k : ℕ, twistGlobalSections (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) k) :=
  sectionsRingEquiv (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    (fun k => bijective_degreeSection_mvPolynomial R n k)

/-- The isomorphism is the canonical ring map of [Stacks, Tag 01MP]. -/
theorem coe_polynomialSectionsRingEquiv (R : Type u) [CommRing R] (n : ℕ) :
    letI := gradedRing (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    (polynomialSectionsRingEquiv R n : MvPolynomial (Fin (n + 1)) R →
        (⨁ k : ℕ, twistGlobalSections (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) k))
      = sectionsRingHom (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) := rfl

/-- On a homogeneous polynomial of degree `k` the isomorphism is the canonical section, in the
degree-`k` summand: the isomorphism is graded. -/
theorem polynomialSectionsRingEquiv_apply_homogeneous (R : Type u) [CommRing R] (n k : ℕ)
    (a : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R k) :
    letI := gradedRing (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    polynomialSectionsRingEquiv R n (a : MvPolynomial (Fin (n + 1)) R)
      = DirectSum.of (twistGlobalSections (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) k
        (degreeSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) k a) :=
  sectionsRingHom_apply_homogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) k a

/-- **The graded section ring `⨁_{k ≥ 0} Γ(ℙⁿ_R, 𝒪(k))` is a finite `S`-module**, for
`S = R[T₀, …, Tₙ]` acting through the canonical ring map of [Stacks, Tag 01MP]: the map is
surjective, so the section ring is generated by `1`. This is the `r = 1`, `d₁ = 0` case of the
identification `N_k = ⨁_j S(d_j)` that opens the sandwich in the proof of [Stacks, Tag 01YS]
clause (5). -/
theorem moduleFinite_polynomialTwistSectionRing (R : Type u) [CommRing R] (n : ℕ) :
    letI := gradedRing (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    letI := (sectionsRingHom (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).toModule
    Module.Finite (MvPolynomial (Fin (n + 1)) R)
      (⨁ k : ℕ, twistGlobalSections
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) k) := by
  let := gradedRing (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
  let := (sectionsRingHom (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).toModule
  refine Module.Finite.of_surjective
    ({ toFun := sectionsRingHom (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
       map_add' := map_add _
       map_smul' := fun s x => by
         simp [RingHom.toModule_smul, smul_eq_mul] } :
      MvPolynomial (Fin (n + 1)) R →ₗ[MvPolynomial (Fin (n + 1)) R]
        (⨁ k : ℕ, twistGlobalSections
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) k))
    (bijective_sectionsRingHom (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (fun k => bijective_degreeSection_mvPolynomial R n k)).surjective

end Stacks.ProjectiveSpace.Cohomology

end
