module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TwistSectionsBijective

/-!
# The graded ring of twisted sections on the projective line is the polynomial ring

Let `𝒮 : ℕ → σ` be a nonnegative grading of a commutative ring `S` and let `X = Proj 𝒮`.
Equation [Stacks, Tag 01MP] is the canonical graded ring map `S ⟶ ⨁_{n ≥ 0} Γ(X, 𝒪(n))`,
`Stacks.AlgebraicGeometry.ProjTwistSectionRing.sectionsRingHom`; it is assembled out of the
degreewise section maps `AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSectionHom`, and it is
a *ring* map because those are multiplicative across degrees
(`Stacks.AlgebraicGeometry.ProjTwistSectionRing.mul_degreeSection`).

The assembled map is the componentwise direct sum of the degreewise maps composed with the
decomposition of `S` into homogeneous pieces, so it is **bijective as soon as every degreewise
map is**. For `𝐏¹_k = Proj k[T₀, T₁]` over a field every degreewise map is bijective, by
`Stacks.ProjectiveSpace.Cohomology.bijective_degreeSection_line`, so the canonical map is a ring
isomorphism

`k[T₀, T₁] ≅ ⨁_{d ≥ 0} Γ(𝐏¹_k, 𝒪(d))`.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistSectionRing.sumSectionsRingHom_toAddMonoidHom` — the
  assembled map is the componentwise direct sum of the degreewise section maps.
* `Stacks.AlgebraicGeometry.ProjTwistSectionRing.bijective_sectionsRingHom_of_bijective` — **the
  canonical map of Equation 01MP is bijective as soon as it is bijective in each degree.**
* `Stacks.ProjectiveSpace.Cohomology.bijective_sectionsRingHom_line` — **it is bijective for the
  projective line over a field.**
* `Stacks.ProjectiveSpace.Cohomology.sectionsRingEquivLine` — **hence `k[T₀, T₁]` is the graded
  ring `⨁_d Γ(𝐏¹_k, 𝒪(d))`**, as rings.

## References

* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
-/


@[expose] public noncomputable section

open DirectSum
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading)
open Stacks.AlgebraicGeometry.ProjTwistSections
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistGlobalSections degreeSection degreeSectionHom
  degreeSectionHom_apply)

universe u w

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.AlgebraicGeometry.ProjTwistSectionRing

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- **The assembled map is the componentwise direct sum of the degreewise section maps.** -/
public theorem sumSectionsRingHom_toAddMonoidHom : letI := gradedRing 𝒮
    (sumSectionsRingHom 𝒮).toAddMonoidHom =
      DirectSum.map (fun n => degreeSectionHom 𝒮 n) := by
  let := gradedRing 𝒮
  refine DirectSum.addHom_ext fun n a => ?_
  rw [DirectSum.map_of]
  exact sumSectionsRingHom_of 𝒮 n a

/-- **The canonical graded ring map of Equation [Stacks, Tag 01MP] is bijective as soon as it is
bijective in every degree.** -/
public theorem bijective_sectionsRingHom_of_bijective
    (h : ∀ n, Function.Bijective (degreeSection 𝒮 n)) : letI := gradedRing 𝒮
    Function.Bijective (sectionsRingHom 𝒮) := by
  let := gradedRing 𝒮
  have hmap : Function.Bijective (DirectSum.map (fun n => degreeSectionHom 𝒮 n)) :=
    ⟨(DirectSum.map_injective _).2 fun n => (h n).injective,
      (DirectSum.map_surjective _).2 fun n => (h n).surjective⟩
  have hsum : Function.Bijective (sumSectionsRingHom 𝒮) := by
    have hfun : (sumSectionsRingHom 𝒮 : (⨁ n : ℕ, 𝒮 n) → _) =
        DirectSum.map (fun n => degreeSectionHom 𝒮 n) :=
      funext fun x => DFunLike.congr_fun (sumSectionsRingHom_toAddMonoidHom 𝒮) x
    rw [hfun]
    exact hmap
  have hcomp : (sectionsRingHom 𝒮 : S → _) =
      (sumSectionsRingHom 𝒮) ∘ (DirectSum.decompose 𝒮) := rfl
  rw [hcomp]
  exact hsum.comp (DirectSum.decompose 𝒮).bijective

end Stacks.AlgebraicGeometry.ProjTwistSectionRing

namespace Stacks.ProjectiveSpace.Cohomology

open Stacks.AlgebraicGeometry.ProjTwistSectionRing

/-- **The canonical graded ring map `k[T₀, T₁] ⟶ ⨁_d Γ(𝐏¹_k, 𝒪(d))` is bijective** for a field
`k`. -/
public theorem bijective_sectionsRingHom_line (k : Type u) [Field k] :
    letI := gradedRing (polyGrading k 1)
    Function.Bijective (sectionsRingHom (polyGrading k 1)) :=
  bijective_sectionsRingHom_of_bijective (polyGrading k 1) (bijective_degreeSection_line k)

/-- **`k[T₀, T₁]` is the graded ring of twisted sections on the projective line.**

For `k` a field the canonical map of Equation [Stacks, Tag 01MP] is a ring isomorphism
`k[T₀, T₁] ≅ ⨁_{d ≥ 0} Γ(𝐏¹_k, 𝒪(d))`. It carries the degree-`d` homogeneous polynomials onto
the degree-`d` summand by
`Stacks.AlgebraicGeometry.ProjTwistSectionRing.sectionsRingHom_apply_homogeneous`, so it is an
isomorphism of *graded* rings, and being a ring map it matches the multiplication
`Γ(𝒪(d)) × Γ(𝒪(e)) ⟶ Γ(𝒪(d + e))` with the multiplication of binary forms. -/
public def sectionsRingEquivLine (k : Type u) [Field k] :
    letI := gradedRing (polyGrading k 1)
    MvPolynomial (Fin (1 + 1)) k ≃+*
      (⨁ d : ℕ, twistGlobalSections (polyGrading k 1) d) :=
  letI := gradedRing (polyGrading k 1)
  RingEquiv.ofBijective (sectionsRingHom (polyGrading k 1)) (bijective_sectionsRingHom_line k)

end Stacks.ProjectiveSpace.Cohomology

end
