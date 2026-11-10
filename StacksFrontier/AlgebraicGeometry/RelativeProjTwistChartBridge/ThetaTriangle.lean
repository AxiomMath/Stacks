module

public import StacksFrontier.AlgebraicGeometry.RelativeProjTwistChartBridge.ThetaTagShape

/-!
# The characterising triangle of Lemma 01O1

Let `r = r_{d, ℒ, ψ}` be the morphism of [Stacks, Tag 01O1] attached to a quadruple
`(f : T → S, d, ℒ, ψ)` over an arbitrary base
(`StacksFrontier.AlgebraicGeometry.RelativeProjTwistChartBridge.ThetaTagShape`).
The `θ`-assertion of
the tag is an isomorphism of `ℤ`-graded `𝒪_T`-algebras

`θ : r^*(⨁_{n ∈ ℤ} 𝒪_{Proj_S(𝒜)}(nd)) ⟶ ⨁_{n ∈ ℤ} ℒ^{⊗ n}`

with `ψ = θ ∘ ψ_univ`, uniquely determined by that equation. This file states the commutativity of
that triangle as a property of the quadruple, with the degree-one identification `α : r^*𝒪(d) ≅ ℒ`
quantified, and derives every assertion of the tag from it.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge.TriangleCommutes`: the commutativity of
  Lemma 01O1's characterising triangle, with the degree-one datum quantified.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge.degreeOne_triangle_iff`: the degree-one
  instance of the triangle is exactly the statement that `α` carries the tag's second leg to the
  quadruple's `ψ`.
* `Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge.tag01O1_of_triangleCommutes`: if the
  triangle commutes at the canonical `r`, then `r` is a morphism over `S` and there is an
  isomorphism `θ` of sheaves of `ℤ`-graded `𝒪_T`-algebras onto `⨁_n ℒ^{⊗ n}` satisfying
  `ψ_univ ≫ θ = ψ` in every integer degree, unique among homomorphisms of graded algebras with that
  property.

## References

* [Stacks Project, Tag 01O1](https://stacks.math.columbia.edu/tag/01O1)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01N9](https://stacks.math.columbia.edu/tag/01N9)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.AlgebraicGeometry.RelativeVeroneseTwists

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge

variable {S T : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {d : ℕ} {f : T ⟶ S}

/-! ### The degree-one instance of the triangle -/

/-- **The degree-one instance of Lemma 01O1's triangle says exactly that `α` carries the tag's
second leg to the quadruple's `ψ`**, read through the identification `ℒ^{⊗ 1} ≅ ℒ` of the
quadruple. -/
theorem degreeOne_triangle_iff (D : TwistData A) (r : T ⟶ (relativeProj A).scheme)
    (hg : ∀ t : T, r.base t ∈ (relativeProj A).degreeOpen d)
    (hr : r ≫ (relativeProj A).toBase = f)
    (P : Quadruple f (situationAlgebra A) (d : ℤ))
    (α : (pullbackTwistVeronese D (d : ℤ) r).piece 1 ≅ P.L) :
    (D.psiLegVeronese r hr (d : ℤ) 1 ≫
          (laurentComparisonOfDegreeOpen D d r hg α).hom.app 1 = P.twisting.app 1)
      ↔ D.psiLegVeronese r hr (d : ℤ) 1 ≫ α.hom = P.twisting.app 1 ≫ P.oneIso.hom := by
  have hβ : (laurentComparisonOfDegreeOpen D d r hg α).hom.app 1 ≫ P.oneIso.hom = α.hom :=
    GradedLaurentRecognition.pieceIso_one_comp_oneIsoL _ _ α _ _
  rw [← hβ, ← Category.assoc, Iso.cancel_iso_hom_right]

/-! ### The triangle as a property of the quadruple alone -/

/-- **The commutativity of Lemma 01O1's characterising triangle**, with the degree-one datum
quantified rather than carried: there is an identification `α : r^*𝒪(d) ≅ ℒ` of the degree-one
pieces for which the tag's own second leg
`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.psiLegVeronese` — the homogeneous-section
map `ψ_univ` of [Stacks, Tag 01NR], transposed across `π^* ⊣ π_*` and base-changed along `r` —
followed by the recognition isomorphism built out of `α`, is the quadruple's own `ψ` in every
nonnegative degree. -/
def TriangleCommutes (D : TwistData A) (d : ℕ) (r : T ⟶ (relativeProj A).scheme)
    (hg : ∀ t : T, r.base t ∈ (relativeProj A).degreeOpen d)
    (hr : r ≫ (relativeProj A).toBase = f)
    (P : Quadruple f (situationAlgebra A) (d : ℤ)) : Prop :=
  ∃ α : (pullbackTwistVeronese D (d : ℤ) r).piece 1 ≅ P.L,
    ∀ n : ℕ, D.psiLegVeronese r hr (d : ℤ) (n : ℤ) ≫
      (laurentComparisonOfDegreeOpen D d r hg α).hom.app (n : ℤ) = P.twisting.app (n : ℤ)

/-! ### The whole of Lemma 01O1 on the triangle alone -/

/-- **[Stacks, Tag 01O1], at the tag's own morphism and the tag's own second leg, on the
commutativity of the characterising triangle alone.**

In Situation 01NN, for a quadruple `(f : T → S, d, ℒ, ψ)` of Section 01NS with `d ≥ 1`, let
`r = r_{d, ℒ, ψ}` be the morphism `thetaMorphism`. If Lemma 01O1's triangle commutes at `r` —
that is, if `TriangleCommutes` holds — then

1. `r` is a morphism over `S`;
2. there is an isomorphism of sheaves of `ℤ`-graded `𝒪_T`-algebras
   `θ : r^*(⨁_{n ∈ ℤ} 𝒪_{Proj_S(𝒜)}(nd)) ≅ ⨁_{n ∈ ℤ} ℒ^{⊗ n}`;
3. `ψ_univ ≫ θ = ψ` in **every** integer degree, not only the nonnegative ones the hypothesis
   mentions; and
4. `θ` is the unique homomorphism of sheaves of graded algebras with that property. -/
theorem tag01O1_of_triangleCommutes (D : TwistData A) (hd : 0 < d)
    (P : Quadruple f (situationAlgebra A) (d : ℤ))
    (htri : TriangleCommutes D d (thetaMorphism hd P) (thetaMorphism_mem_degreeOpen hd P)
      (thetaMorphism_comp_toBase hd P) P) :
    thetaMorphism hd P ≫ (relativeProj A).toBase = f ∧
      ∃ θ : pullbackTwistVeronese D (d : ℤ) (thetaMorphism hd P) ≅ laurent P.L,
        (∀ n : ℤ, D.psiLegVeronese (thetaMorphism hd P) (thetaMorphism_comp_toBase hd P)
              (d : ℤ) n ≫ θ.hom.app n = P.twisting.app n) ∧
          ∃! Θ : pullbackTwistVeronese D (d : ℤ) (thetaMorphism hd P) ⟶ laurent P.L,
            ∀ n : ℤ, D.psiLegVeronese (thetaMorphism hd P) (thetaMorphism_comp_toBase hd P)
              (d : ℤ) n ≫ Θ.app n = P.twisting.app n :=
  ⟨thetaMorphism_comp_toBase hd P,
    existsUnique_theta_psiLeg D hd (thetaMorphism hd P) (thetaMorphism_mem_degreeOpen hd P)
      (thetaMorphism_comp_toBase hd P) P htri⟩

end Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge

end
