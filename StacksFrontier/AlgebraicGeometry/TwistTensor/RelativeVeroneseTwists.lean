module

public import StacksFrontier.AlgebraicGeometry.GluedTwistAlgebra.Assemble
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.GradedAlgebra
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ThetaUnique
public import StacksFrontier.AlgebraicGeometry.TwistMapsInvertible.Multiplication
public import StacksFrontier.AlgebraicGeometry.TwistTensor.GradedVeronese

/-!
# The `d`-divisible glued twists on a relative projective spectrum, and the source of `θ`

Let `S` be a scheme and `𝒜` a quasi-coherent, nonnegatively graded `𝒪_S`-algebra — Situation 01NN.
[Stacks, Tag 01NR] produces the sheaf of `ℤ`-graded algebras `⨁_{n ∈ ℤ} 𝒪_{Proj_S(𝒜)}(n)` of the
glued twists, as a `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData`; one exists for every
`𝒜`, by `Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra`.

For an integer `d` this file forms the two objects [Stacks, Tag 01O1] names:

* `⨁_{n ∈ ℤ} 𝒪_{Proj_S(𝒜)}(nd)`, the `d`-th Veronese regrading of the glued twists, and
* `r^*(⨁_{n ∈ ℤ} 𝒪_{Proj_S(𝒜)}(nd))`, its pullback along a morphism `r : T ⟶ Proj_S(𝒜)`,

which is the source of the comparison `θ` of that tag.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeVeroneseTwists.twistVeronese`: `⨁_{n ∈ ℤ} 𝒪(nd)`, the
  `d`-divisible glued twists on `Proj_S(𝒜)` as a sheaf of `ℤ`-graded algebras.
* `Stacks.AlgebraicGeometry.RelativeVeroneseTwists.pullbackTwistVeronese`:
  `r^*(⨁_{n ∈ ℤ} 𝒪(nd))`, the source of Lemma 01O1's `θ`, for a morphism `r : T ⟶ Proj_S(𝒜)`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeVeroneseTwists.twistVeronese_piece` and
  `Stacks.AlgebraicGeometry.RelativeVeroneseTwists.pullbackTwistVeronese_piece`: the degree-`n`
  pieces are `𝒪(nd)` and `r^*𝒪(nd)`.
* `Stacks.AlgebraicGeometry.RelativeVeroneseTwists.isIso_mulSheaf_twistVeronese`: the
  multiplications `𝒪(nd) ⊗ 𝒪(md) ⟶ 𝒪((n + m)d)` of the `d`-divisible glued twists are
  isomorphisms, for a graded algebra generated in degree one.
* `Stacks.AlgebraicGeometry.RelativeVeroneseTwists.isInvertible_twistVeronese_piece`: every
  `𝒪(nd)` is invertible, under the same hypothesis.
* `Stacks.AlgebraicGeometry.RelativeVeroneseTwists.existsUnique_theta_pullbackTwistVeronese`:
  Lemma 01O1's `θ`-assertion — the existence of `θ`, the commutativity of the characterising
  triangle and the uniqueness of `θ` — stated with the tag's own source `r^*(⨁_n 𝒪(nd))`, given a
  comparison of that source with a source on which some isomorphism solves the triangle.

## References

* [Stacks Project, Tag 01O1](https://stacks.math.columbia.edu/tag/01O1)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

open AlgebraicGeometry Stacks.RingedSpace
open Stacks.AlgebraicGeometry.GradedVeronese
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjTwists

universe u

namespace Stacks.AlgebraicGeometry.RelativeVeroneseTwists

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} (D : TwistData A) (d : ℤ)

/-- **The `d`-divisible glued twists `⨁_{n ∈ ℤ} 𝒪_{Proj_S(𝒜)}(nd)`** on a relative projective
spectrum, as a sheaf of `ℤ`-graded algebras: the `d`-th Veronese regrading of the graded algebra of
the twists of [Stacks, Tag 01NR]. -/
def twistVeronese :
    SheafOfModules.GradedAlgebra.{u, u}
      (structureRingSheaf (relativeProj A).scheme.toRingedSpace) :=
  veronese D.algebra d

/-- **The degree-`n` piece of `⨁_{n ∈ ℤ} 𝒪(nd)` is `𝒪(nd)`**, on the nose. -/
theorem twistVeronese_piece (n : ℤ) :
    (twistVeronese D d).piece n = D.algebra.piece (n * d) := rfl

/-- **The multiplications `𝒪(nd) ⊗ 𝒪(md) ⟶ 𝒪((n + m)d)` of the `d`-divisible glued twists are
isomorphisms**, for a quasi-coherent graded algebra generated in degree one over every affine open
of the base. -/
theorem isIso_mulSheaf_twistVeronese
    (hgen : ∀ U : S.Opens, IsAffineOpen U →
      Algebra.adjoin (A.grading U 0) ((A.grading U 1 : Set (A.sectionRing U))) = ⊤)
    (n m : ℤ) :
    IsIso (SheafOfModules.GradedAlgebra.mulSheaf (twistVeronese D d) n m) :=
  isIso_veronese_mulSheaf D.algebra d n m
    (Stacks.AlgebraicGeometry.TwistMapsInvertible.twistData_isIso_mulSheaf D hgen (n * d) (m * d))

/-- **Every `d`-divisible glued twist `𝒪(nd)` is invertible**, for a quasi-coherent graded algebra
generated in degree one over every affine open of the base. -/
theorem isInvertible_twistVeronese_piece
    (hgen : ∀ U : S.Opens, IsAffineOpen U →
      Algebra.adjoin (A.grading U 0) ((A.grading U 1 : Set (A.sectionRing U))) = ⊤)
    (n : ℤ) :
    Stacks.SheafOfModules.IsInvertible (relativeProj A).scheme.toRingedSpace.presheaf
      (isSheafStruct (relativeProj A).scheme) ((twistVeronese D d).piece n) :=
  Stacks.AlgebraicGeometry.TwistMapsInvertible.twistData_stacksIsInvertible D hgen (n * d)

/-! ### The source of `θ` -/

variable {T : Scheme.{u}} (g : T ⟶ (relativeProj A).scheme)

/-- **`r^*(⨁_{n ∈ ℤ} 𝒪_{Proj_S(𝒜)}(nd))`, the source of the comparison `θ` of [Stacks, Tag
01O1]**: the pullback along `r : T ⟶ Proj_S(𝒜)` of the `d`-divisible glued twists, as a sheaf of
`ℤ`-graded `𝒪_T`-algebras. -/
def pullbackTwistVeronese :
    SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf T.toRingedSpace) :=
  Stacks.RingedSpace.pullbackGradedAlgebra (ringedSpaceHom g) (twistVeronese D d)

/-- **The degree-`n` piece of `r^*(⨁_n 𝒪(nd))` is `r^*𝒪(nd)`**, on the nose. -/
theorem pullbackTwistVeronese_piece (n : ℤ) :
    (pullbackTwistVeronese D d g).piece n =
      (pullbackFunctor (ringedSpaceHom g)).obj (D.algebra.piece (n * d)) := rfl

/-! ### Lemma 01O1's `θ`-assertion at the tag's own source -/

variable {S' : Scheme.{u}} {f : T ⟶ S'}
  {B : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S'.toRingedSpace)} {e : ℤ}

/-- **Stacks Project, Tag 01O1.** *The comparison `θ`, its characterising triangle and its
uniqueness, at the tag's own source `r^*(⨁_{n ∈ ℤ} 𝒪_{Proj_S(𝒜)}(nd))`.*

Let `(f : T → S, d, ℒ, ψ)` be a quadruple, let `r : T ⟶ Proj_S(𝒜)` be a morphism — for the tag,
`r_{d, ℒ, ψ}` — and let `v_n : f^*𝒜_{nd} ⟶ r^*𝒪(nd)` be a degreewise family, the second leg of the
tag's triangle. Given an isomorphism `θ : ℛ ≅ ⨁_n ℒ^{⊗ n}` of graded algebras solving the triangle
on some source `ℛ` with its own second leg `u`, and a comparison `c : r^*(⨁_n 𝒪(nd)) ≅ ℛ` of graded
algebras carrying `v` to `u`, there is an isomorphism

`θ' : r^*(⨁_{n ∈ ℤ} 𝒪_{Proj_S(𝒜)}(nd)) ≅ ⨁_{n ∈ ℤ} ℒ^{⊗ n}`

of sheaves of `ℤ`-graded `𝒪_T`-algebras solving the triangle, and it is the unique homomorphism of
graded algebras that does. -/
theorem existsUnique_theta_pullbackTwistVeronese (P : Quadruple f B e)
    (v : ∀ n : ℤ, (pullbackFunctor (ringedSpaceHom f)).obj (B.piece (n * e)) ⟶
      (pullbackTwistVeronese D d g).piece n)
    (R : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf T.toRingedSpace))
    (u : ∀ n : ℤ, (pullbackFunctor (ringedSpaceHom f)).obj (B.piece (n * e)) ⟶ R.piece n)
    (c : pullbackTwistVeronese D d g ≅ R) (hc : ∀ n : ℤ, v n ≫ c.hom.app n = u n)
    {θ : R ≅ laurent P.L} (hθ : ∀ n : ℤ, u n ≫ θ.hom.app n = P.twisting.app n) :
    ∃ θ' : pullbackTwistVeronese D d g ≅ laurent P.L,
      (∀ n : ℤ, v n ≫ θ'.hom.app n = P.twisting.app n) ∧
        ∃! Θ : pullbackTwistVeronese D d g ⟶ laurent P.L,
          ∀ n : ℤ, v n ≫ Θ.app n = P.twisting.app n :=
  Quadruple.existsUnique_theta_of_sourceIso P R u v c hc hθ

end Stacks.AlgebraicGeometry.RelativeVeroneseTwists

end
