module

public import StacksFrontier.AlgebraicGeometry.RelativeProjTwistChartBridge.TwistQuadruple
public import StacksFrontier.AlgebraicGeometry.GluedTwistAlgebra.Assemble

/-!
# Lemma 01O1: the comparison `θ` of the twists along `r_{d, ℒ, ψ}`

In Situation 01NN, let `(f : T → S, d, ℒ, ψ)` be a quadruple and `r = r_{d, ℒ, ψ}` the associated
`S`-morphism into `Proj_S(𝒜)`. [Stacks, Tag 01O1] asserts an isomorphism of `ℤ`-graded
`𝒪_T`-algebras

`θ : r^*(⨁_{n ∈ ℤ} 𝒪(nd)) ⟶ ⨁_{n ∈ ℤ} ℒ^{⊗ n}`

with `ψ = θ ∘ ψ_univ`, uniquely determined by that equation.

## The proof

The source proves the lemma by identifying the universal element of `F_d(U_d)` with the
quadruple `(U_d → S, d, 𝒪(d)|_{U_d}, ψ_univ)` built from the glued twists of [Stacks, Tag 01NR].
Here the identification is made at `T` itself: the twists along `r` give a quadruple
`...RelativeProjTwistChartBridge.twistQuadruple` over `f`, whose twisting is the second leg of the
triangle followed by the recognition comparison
`r^*(⨁_n 𝒪(nd)) ≅ ⨁_n (r^*𝒪(d))^{⊗ n}`, and
`...RelativeProjTwistChartBridge.homDegreeOpen_twistQuadruple` says that the representation of
`F_d` by `U_d` sends its class to the factorization of `r` through `U_d` — chart by chart this is
the comparison with the absolute universal family of [Stacks, Tag 01N9] in
`StacksFrontier.AlgebraicGeometry.RelativeProjTwistChartBridge.TwistQuadrupleChart`. Since `r` is by
definition the morphism the class of the given quadruple defines, the injectivity of that
representation makes the two quadruples strictly equivalent, and `θ` is the recognition
comparison followed by the strict equivalence. Uniqueness is
`...RelativeProjTwistChartBridge.tag01O1_of_triangleCommutes`.

## Main results

* `...RelativeProjTwistChartBridge.tag01O1_of_twistData`: the lemma for every twist datum of
  [Stacks, Tag 01NR].
* `...RelativeProjTwistChartBridge.tag01O1`: **[Stacks, Tag 01O1]**, at the twists of [Stacks,
  Tag 01NR] constructed by `...GluedTwistAlgebra.twistDataOfGradedAlgebra`, with `r` identified
  as the morphism the representation of `F` of [Stacks, Tag 01NZ] attaches to the quadruple
  (`...RelativeProjTwistChartBridge.thetaMorphism_eq_homEquiv_symm`).

## References

* [Stacks Project, Tag 01O1](https://stacks.math.columbia.edu/tag/01O1)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
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

/-- **Lemma 01O1 for an arbitrary twist datum of [Stacks, Tag 01NR].** For a quadruple
`(f : T → S, d, ℒ, ψ)` with `d ≥ 1` and `r = r_{d, ℒ, ψ}`:

1. `r` is a morphism over `S`;
2. there is an isomorphism of sheaves of `ℤ`-graded `𝒪_T`-algebras
   `θ : r^*(⨁_{n ∈ ℤ} 𝒪(nd)) ≅ ⨁_{n ∈ ℤ} ℒ^{⊗ n}`, preserving the unit;
3. `ψ = θ ∘ ψ_univ` in every integer degree; and
4. every homomorphism of graded algebras with that property is `θ`. -/
theorem tag01O1_of_twistData (D : TwistData A) (hd : 0 < d)
    (P : Quadruple f (situationAlgebra A) (d : ℤ)) :
    thetaMorphism hd P ≫ (relativeProj A).toBase = f ∧
      ∃ θ : pullbackTwistVeronese D (d : ℤ) (thetaMorphism hd P) ≅ laurent P.L,
        SheafOfModules.GradedAlgebra.oneHom
              (pullbackTwistVeronese D (d : ℤ) (thetaMorphism hd P)) ≫ θ.hom.app 0 =
            SheafOfModules.GradedAlgebra.oneHom (laurent P.L) ∧
          (∀ n : ℤ, D.psiLegVeronese (thetaMorphism hd P) (thetaMorphism_comp_toBase hd P)
              (d : ℤ) n ≫ θ.hom.app n = P.twisting.app n) ∧
          ∀ Θ : pullbackTwistVeronese D (d : ℤ) (thetaMorphism hd P) ⟶ laurent P.L,
            (∀ n : ℤ, D.psiLegVeronese (thetaMorphism hd P) (thetaMorphism_comp_toBase hd P)
              (d : ℤ) n ≫ Θ.app n = P.twisting.app n) → Θ = θ.hom := by
  have := isInvertible_pullbackTwistVeronese_piece_one_of_mem_degreeOpen D d
    (thetaMorphism hd P) (thetaMorphism_mem_degreeOpen hd P)
  set Q := twistQuadruple D d (thetaMorphism hd P) (thetaMorphism_mem_degreeOpen hd P)
    (thetaMorphism_comp_toBase hd P) with hQ
  have h1 : Fd.homDegreeOpen A (relativeProj A) hd (Fd.mk f Q) =
      Fd.homDegreeOpen A (relativeProj A) hd (Fd.mk f P) :=
    homDegreeOpen_twistQuadruple D d (thetaMorphism hd P) (thetaMorphism_mem_degreeOpen hd P) hd
      (thetaMorphism_comp_toBase hd P) _ rfl
  have h2 : Fd.mk f Q = Fd.mk f P := Fd.homDegreeOpen_injective A (relativeProj A) hd T h1
  obtain ⟨γ, hγ⟩ :=
    (Quadruple.strictlyEquivalent_iff_exists_hom Q P).mp ((Fd.mk_eq_mk_iff Q P).mp h2)
  have hθ : ∀ n : ℤ, D.psiLegVeronese (thetaMorphism hd P) (thetaMorphism_comp_toBase hd P)
      (d : ℤ) n ≫ (twistRecognition D d (thetaMorphism hd P)
        (thetaMorphism_mem_degreeOpen hd P) ≪≫ γ).hom.app n = P.twisting.app n := by
    intro n
    exact (Category.assoc _ _ _).symm.trans (hγ n)
  obtain ⟨hf, θ', -, Θ₀, -, huniq⟩ := tag01O1_of_triangleCommutes D hd P
    (triangleCommutes_of_gradedIso D (thetaMorphism hd P) P (thetaMorphism_mem_degreeOpen hd P)
      (thetaMorphism_comp_toBase hd P) _ hθ)
  refine ⟨hf, twistRecognition D d (thetaMorphism hd P) (thetaMorphism_mem_degreeOpen hd P) ≪≫ γ,
    ?_, hθ, fun Θ hΘ => (huniq Θ hΘ).trans (huniq _ hθ).symm⟩
  have hR : SheafOfModules.GradedAlgebra.oneHom
        (pullbackTwistVeronese D (d : ℤ) (thetaMorphism hd P)) ≫
      (twistRecognition D d (thetaMorphism hd P) (thetaMorphism_mem_degreeOpen hd P)).hom.app 0 =
      SheafOfModules.GradedAlgebra.oneHom (laurent Q.L) :=
    GradedLaurentRecognition.oneHom_comp_gradedIso_app_zero _ _ _ _ _
  have hγ1 : SheafOfModules.GradedAlgebra.oneHom (laurent Q.L) ≫ γ.hom.app 0 =
      SheafOfModules.GradedAlgebra.oneHom (laurent P.L) := by
    refine (congrArg (· ≫ γ.hom.app 0) Q.twisting.app_one.symm).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (Stacks.PullbackGradedAlgebra.pullbackOne (ringedSpaceHom f)
      (situationAlgebra A) ≫ ·) (Category.assoc _ _ _)).trans ?_
    refine (congrArg (fun z => Stacks.PullbackGradedAlgebra.pullbackOne (ringedSpaceHom f)
      (situationAlgebra A) ≫ (pullbackFunctor (ringedSpaceHom f)).map
        (eqToHom (congrArg (situationAlgebra A).piece (by ring : (0 : ℤ) = 0 * (d : ℤ)))) ≫ z)
      (hγ 0)).trans ?_
    exact P.twisting.app_one
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ γ.hom.app 0) hR).trans hγ1)

/-- **Stacks Project, Tag 01O1.** In Situation 01NN — `S` a scheme and `𝒜` a quasi-coherent
graded `𝒪_S`-algebra — let `(f : T → S, d, ℒ, ψ)` be a quadruple of Section 01NS, so `d ≥ 1`, and
let `r = r_{d, ℒ, ψ} : T → Proj_S(𝒜)` be the associated morphism
(`...RelativeProjTwistChartBridge.thetaMorphism`: the morphism into `U_d` that the class of the
quadruple defines, followed by `U_d ⊆ Proj_S(𝒜)`). Write `𝒪(n)` for the twists of `Proj_S(𝒜)`
with their homogeneous-section map `ψ_univ` (`...GluedTwistAlgebra.twistDataOfGradedAlgebra`).
Then

1. `r` is the morphism the representability of `F` attaches to the quadruple: the image of its
   class in `F(T)` under the representation
   `...RelativeProjQcohSheaf.relativeProjRepresentableByFunctorUnconditional` of the functor `F`
   of the display 01NX by `Proj_S(𝒜)`, which is the representation of [Stacks, Tag 01NZ];
2. `r` is a morphism over `S`;
3. there is an isomorphism of sheaves of `ℤ`-graded `𝒪_T`-algebras
   `θ : r^*(⨁_{n ∈ ℤ} 𝒪(nd)) ≅ ⨁_{n ∈ ℤ} ℒ^{⊗ n}`, which preserves the unit;
4. the triangle commutes: `ψ = θ ∘ ψ_univ` in every degree, the maps out of
   `𝒜^{(d)}` being read through the adjunction `f^* ⊣ f_*`, so that `ψ_univ` becomes
   `...RelativeProjTwists.TwistData.psiLegVeronese`; and
5. the triangle determines `θ`: any homomorphism of graded algebras
   `r^*(⨁_n 𝒪(nd)) ⟶ ⨁_n ℒ^{⊗ n}` making it commute is `θ`. -/
@[stacks 01O1 "for a quadruple (f : T -> S, d, L, psi) with associated morphism \
r : T -> Proj_S(A), the morphism the representation of F by Proj_S(A) attaches to the class of \
the quadruple: r lies over S, and there is an isomorphism theta of Z-graded O_T-algebras \
from r^*((+)_n O(nd)) to (+)_n L^(x)n, preserving the unit, with psi = theta o psi_univ in every \
degree, and every homomorphism of graded algebras with psi = Theta o psi_univ is theta"]
theorem tag01O1 (hd : 0 < d) (P : Quadruple f (situationAlgebra A) (d : ℤ)) :
    thetaMorphism hd P =
        (relativeProjRepresentableByFunctorUnconditional A).homEquiv.symm
          (RelativeProjInvertibleMorphism.F.toLim A (F.mk f (by exact_mod_cast hd) P)) ∧
    thetaMorphism hd P ≫ (relativeProj A).toBase = f ∧
      ∃ θ : pullbackTwistVeronese (GluedTwistAlgebra.twistDataOfGradedAlgebra A) (d : ℤ)
          (thetaMorphism hd P) ≅ laurent P.L,
        SheafOfModules.GradedAlgebra.oneHom
              (pullbackTwistVeronese (GluedTwistAlgebra.twistDataOfGradedAlgebra A) (d : ℤ)
                (thetaMorphism hd P)) ≫ θ.hom.app 0 =
            SheafOfModules.GradedAlgebra.oneHom (laurent P.L) ∧
          (∀ n : ℤ, (GluedTwistAlgebra.twistDataOfGradedAlgebra A).psiLegVeronese
              (thetaMorphism hd P) (thetaMorphism_comp_toBase hd P) (d : ℤ) n ≫ θ.hom.app n =
                P.twisting.app n) ∧
          ∀ Θ : pullbackTwistVeronese (GluedTwistAlgebra.twistDataOfGradedAlgebra A) (d : ℤ)
              (thetaMorphism hd P) ⟶ laurent P.L,
            (∀ n : ℤ, (GluedTwistAlgebra.twistDataOfGradedAlgebra A).psiLegVeronese
              (thetaMorphism hd P) (thetaMorphism_comp_toBase hd P) (d : ℤ) n ≫ Θ.app n =
                P.twisting.app n) → Θ = θ.hom :=
  ⟨thetaMorphism_eq_homEquiv_symm hd P,
    tag01O1_of_twistData (GluedTwistAlgebra.twistDataOfGradedAlgebra A) hd P⟩

end Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge

end
