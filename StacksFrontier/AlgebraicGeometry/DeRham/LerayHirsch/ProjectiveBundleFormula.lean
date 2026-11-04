module

public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.LerayHirschTheorem
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.ProjectiveBundleRankZero
import StacksCore.Tactic.StacksAttribute

/-!
# The projective bundle formula for de Rham cohomology

Let `g : X ⟶ S` be a morphism of schemes, `ℰ` a locally free `𝒪_X`-module of constant rank `r`
and `p : P = 𝐏(ℰ) ⟶ X` its projective bundle. [Stacks, Tag 0FMT]: the map
`⨁_{i = 0}^{r - 1} H^*_{dR}(X/S) ⟶ H^*_{dR}(P/S)`, `(a_i) ↦ ∑ c₁^{dR}(𝒪_P(1))^i ∪ p^*a_i`,
is an isomorphism. In every degree `k` it is the map
`⨁_{i < r} H^{k - 2i}_{dR}(X/S) ⟶ H^k_{dR}(P/S)`, and this file proves it bijective.

## The argument

The source's: locally on `X` the bundle is `ℙ^{r-1}`, so `p` is proper and smooth
(Section 0FMG; `Stacks.ProjectiveBundleFibre.smooth_projectiveBundleToBase`), and the fibre
classes of `c₁^{dR}(𝒪_P(1))^i`, `i < r`, form a basis of the de Rham cohomology of every fibre
`ℙ^{r-1}_{κ(y)}` (Tag 0FMJ; `Stacks.ProjectiveBundleDeRham.exists_basis_fibreClassOverS_classPow`),
so Proposition 0FMR applies. In rank zero the bundle is empty and both sides vanish.

## Main results

* `Stacks.ProjectiveBundleDeRham.bijective_sum_cup_projectiveBundle`: **[Stacks, Tag 0FMT]**, for
  `Stacks.RelativeProj.projectiveBundle`.
* `Stacks.ProjectiveBundleDeRham.bijective_sum_cup_bundle`: the same for `Stacks.Chow.bundle`.

## References

* [Stacks Project, Tag 0FMT](https://stacks.math.columbia.edu/tag/0FMT)
* [Stacks Project, Tag 0FMR](https://stacks.math.columbia.edu/tag/0FMR)
* [Stacks Project, Tag 0FMJ](https://stacks.math.columbia.edu/tag/0FMJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.RelativeProj (projectiveBundle projectiveBundleToBase)
open scoped Stacks.StandardDerivedModel

universe u

namespace Stacks.ProjectiveBundleDeRham

variable {X S : Scheme.{u}} (g : X ⟶ S) (E : X.Modules) [E.IsQuasicoherent]

/-- **[Stacks, Tag 0FMT], the projective bundle formula for de Rham cohomology.** Let
`g : X ⟶ S` be a morphism of schemes, `ℰ` a quasi-coherent `𝒪_X`-module, locally free of constant
rank `r`, and `p : P = 𝐏(ℰ) ⟶ X` its projective bundle. Then for every `k` the map
`⨁_{i = 0}^{r - 1} H^{k - 2i}_{dR}(X/S) ⟶ H^k_{dR}(P/S)`,
`(a_0, …, a_{r-1}) ↦ ∑_i c₁^{dR}(𝒪_P(1))^i ∪ p^*(a_i)`, is bijective. -/
@[stacks 0FMT "the projective bundle formula: for E locally free of constant rank r on X over S \
and p : P = P(E) -> X, the map (+)_{i = 0, ..., r - 1} H^*_dR(X/S) -> H^*_dR(P/S), \
(a_i) |-> sum c_1^dR(O_P(1))^i cup p^*(a_i), is an isomorphism, i.e. bijective in every degree k"]
theorem bijective_sum_cup_projectiveBundle (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (k : ℤ) :
    Function.Bijective (fun a : ∀ i : Fin r, SheafOfModules.deRhamCohomology
        (Scheme.Hom.deRhamAlgebras g)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras g))
        (k - ((2 * (i : ℕ) : ℕ) : ℤ)) =>
      ∑ i : Fin r, (eqToHom (congrArg (SheafOfModules.deRhamCohomology
          (Scheme.Hom.deRhamAlgebras (projectiveBundleToBase X E ≫ g))
          (SheafOfModules.deRhamDifferential
            (Scheme.Hom.deRhamAlgebras (projectiveBundleToBase X E ≫ g))))
          (add_sub_cancel ((2 * (i : ℕ) : ℕ) : ℤ) k))).hom
        (SheafOfModules.deRhamCohomologyCup _ _ ((2 * (i : ℕ) : ℕ) : ℤ)
          (k - ((2 * (i : ℕ) : ℕ) : ℤ))
          (DeRhamLerayHirsch.classPow (projectiveBundleToBase X E ≫ g) 2
            (DeRhamLerayHirsch.projectiveBundleChernClass g E) i)
          (DeRhamKatzOdaCech.deRhamPullbackModule (projectiveBundleToBase X E) g
            (k - ((2 * (i : ℕ) : ℕ) : ℤ)) (a i)))) := by
  rcases r with _ | n
  · exact bijective_sum_cup_of_rank_zero g E k
  · have := Stacks.ProjectiveBundleFibre.smooth_projectiveBundleToBase E n
    have := Stacks.ProjectiveBundleFibre.isProper_projectiveBundleToBase_of_rank E n
    have hb := exists_basis_fibreClassOverS_classPow g E n
    -- [Stacks, Tag 0FMR]: the Leray--Hirsch morphism is an isomorphism.
    have : IsIso (DeRhamLerayHirsch.lerayHirschMorphism (projectiveBundleToBase X E) g
        (fun i : Fin (n + 1) => 2 * (i : ℕ))
        (fun i => DeRhamLerayHirsch.classPow (projectiveBundleToBase X E ≫ g) 2
          (DeRhamLerayHirsch.projectiveBundleChernClass g E) i)) :=
      DeRhamLerayHirsch.isIso_lerayHirschMorphism (projectiveBundleToBase X E) g _ _ hb
    exact DeRhamLerayHirsch.bijective_sum_deRhamCohomologyCup_of_isIso _ g
      (fun i : Fin (n + 1) => 2 * (i : ℕ)) _ k

/-- **[Stacks, Tag 0FMT] for the presentation `Stacks.Chow.bundle`** of the projective bundle, in
which the bundle objects of the Chern class formalism are stated: for every `k` the map
`(a_i)_{i < r} ↦ ∑_i c₁^{dR}(𝒪(1))^i ∪ π^*(a_i)` is bijective, `𝒪(1) = Stacks.Chow.bundleTwist`. -/
theorem bijective_sum_cup_bundle (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (k : ℤ) :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E r
    Function.Bijective (fun a : ∀ i : Fin r, SheafOfModules.deRhamCohomology
        (Scheme.Hom.deRhamAlgebras g)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras g))
        (k - ((2 * (i : ℕ) : ℕ) : ℤ)) =>
      ∑ i : Fin r, (eqToHom (congrArg (SheafOfModules.deRhamCohomology
          (Scheme.Hom.deRhamAlgebras (Stacks.Chow.bundleProj E ≫ g))
          (SheafOfModules.deRhamDifferential
            (Scheme.Hom.deRhamAlgebras (Stacks.Chow.bundleProj E ≫ g))))
          (add_sub_cancel ((2 * (i : ℕ) : ℕ) : ℤ) k))).hom
        (SheafOfModules.deRhamCohomologyCup _ _ ((2 * (i : ℕ) : ℕ) : ℤ)
          (k - ((2 * (i : ℕ) : ℕ) : ℤ))
          (SheafOfModules.deRhamCohomologyPow _ _ 2
            (Stacks.DeRhamBaseChange.deRhamFirstChernClassPicard (Stacks.Chow.bundleProj E ≫ g)
              (Stacks.WeilCohomology.picardClassOf _ (Stacks.Chow.bundleTwist E)
                (Stacks.ProjectiveBundleSplitting.isInvertible_tautologicalTwist E
                  (Stacks.Chow.bundlePieces E)))) i)
          (DeRhamKatzOdaCech.deRhamPullbackModule (Stacks.Chow.bundleProj E) g
            (k - ((2 * (i : ℕ) : ℕ) : ℤ)) (a i)))) := by
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E r
  have h := bijective_sum_cup_of_iso (projectiveBundleToBase X E) g
    (Stacks.RelativeProj.bundlePresentationIso E).hom
    (bundlePresentationIso_hom_comp_projectiveBundleToBase E) (fun i : Fin r => 2 * (i : ℕ)) _ k
    (bijective_sum_cup_projectiveBundle g E r k)
  simp only [DeRhamLerayHirsch.classPow,
    Stacks.DeRhamBaseChange.deRhamPullbackSquare_deRhamCohomologyPow,
    deRhamPullbackSquare_projectiveBundleChernClass] at h
  exact h

end Stacks.ProjectiveBundleDeRham
