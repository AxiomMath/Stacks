module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.ProjectiveBundleCoordinates

/-!
# The projective bundle formula for Hodge cohomology gives axiom (A3)

Let `k` be a field, `s : X ⟶ Spec k` a scheme over `k`, `ℰ` a finite locally free `𝒪_X`-module
of rank `r + 1`, `p : P = 𝐏(ℰ) ⟶ X` its projective bundle and `π = p ≫ s`. Let
`ξ = c₁^{Hodge}(𝒪_P(1)) ∈ H^1(P, Ω^1_{P/k}) ⊂ H^2_{Hodge}(P/k)`. The projective bundle formula
for Hodge cohomology says that for every `n` the map
`∏_{i ≤ r} H^{n - 2i}_{Hodge}(X/k) ⟶ H^n_{Hodge}(P/k)`, `(a_i) ↦ ∑ ξ^i ∪ p^*(a_i)`
is bijective.

This file shows that this statement, for all `X`, `ℰ` and `r`, gives axiom (A3) of Weil
Cohomology Theories, Section 0FID, for the data (D0), (D1), (D2') of Hodge cohomology,
`Stacks.HodgeWeil.hodgeFirstChernClassData`.

## Main definitions

* `Stacks.HodgeWeil.hodgeBundleClass`: the class `c₁^{Hodge}(𝒪_P(1))` of total degree `2` in
  `H^*_{Hodge}(P/k)`.

## Main results

* `Stacks.HodgeWeil.tateTwistCoordinates_hodgeFirstChernClassData_bundleClass`: the class
  `c₁^H(𝒪_P(1))` of the Hodge data, read through the identity coordinate of the twist, is
  `c₁^{Hodge}(𝒪_P(1))`; through the coordinate of the Tate line it is
  `λ • c₁^{Hodge}(𝒪_P(1))` with `λ = Stacks.HodgeWeil.hodgeTateScalar k ≠ 0`.
* `Stacks.HodgeWeil.bijective_degreewiseMap_bundleClassU_of_bijective`: the degreewise map
  of axiom (A3) for one bundle is bijective once that of the projective bundle formula is.
* `Stacks.HodgeWeil.hodge_projectiveBundleAxiom_of_bijective_degreewiseMap`: axiom (A3) for Hodge
  cohomology from the projective bundle formula for Hodge cohomology.

## References

* [Stacks Project, Section 0FID](https://stacks.math.columbia.edu/tag/0FID)
* [Stacks Project, Remark 0FWE](https://stacks.math.columbia.edu/tag/0FWE)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.WeilCohomology
open Stacks.WeilCohomology.SmoothProjectiveScheme

universe u

namespace Stacks.HodgeWeil

variable {k : Type u} [Field k]

section Scheme

variable {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) (E : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- **The class `ξ = c₁^{Hodge}(𝒪_P(1))`** of the projective bundle `P = 𝐏(ℰ)` over `k`, in
`H^1(P, Ω^1_{P/k})` placed in total degree `2` of `H^*_{Hodge}(P/k)`. -/
def hodgeBundleClass : hodgeAlgebra (formsAlgebras (Stacks.Chow.bundleProj E ≫ s)) :=
  DirectSum.of (hodgePiece (formsAlgebras (Stacks.Chow.bundleProj E ≫ s))) 2
    (DirectSum.of (fun i : HodgeBidegreeInt 2 =>
        (AlgebraicGeometry.SheafOfModules.hodgeCohomologyComponent
          (formsAlgebras (Stacks.Chow.bundleProj E ≫ s)) i.1.1 (i.1.2 : ℤ) : Type u))
      bidegreeOneOne
      (hodgeFirstChernClassModule (Stacks.Chow.bundleProj E ≫ s)
        (picardClassOf (Stacks.Chow.bundle E) (Stacks.Chow.bundleTwist E)
          (Stacks.Chow.isInvertible_bundleTwist E))))

/-- `c₁^{Hodge}(𝒪_P(1))` lies in `H^2_{Hodge}(P/k)`. -/
theorem hodgeBundleClass_mem :
    letI := hodgeAlgebraAlgebra (formsAlgebras (Stacks.Chow.bundleProj E ≫ s))
      (hodgeScalarsOverField (Stacks.Chow.bundleProj E ≫ s))
    hodgeBundleClass s E ∈ hodgeGrade (formsAlgebras (Stacks.Chow.bundleProj E ≫ s))
      (hodgeScalarsOverField (Stacks.Chow.bundleProj E ≫ s)) 2 :=
  of_mem_hodgeGrade _ _ 2 _

end Scheme

section Axiom

variable (X : (SmoothProjectiveScheme k).FullSubcategory) (E : ((toScheme k).obj X).Modules)
  (r : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)]

/-- **The class `c₁^H(𝒪_P(1))` of the Hodge data, read through the identity coordinate of the
twist, is `c₁^{Hodge}(𝒪_P(1))`.** -/
theorem tateTwistCoordinates_hodgeFirstChernClassData_bundleClass :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
    tateTwistCoordinates (LinearEquiv.refl k k) 1 ((hodgeFirstChernClassData k).bundleClass X E r) =
      hodgeBundleClass X.obj.hom E := by
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
  have e₀ : (hodgeFirstChernClassData k).bundleClass X E r =
      hodgeFirstChernClassTw (bundle X E r) (picardClassOf (Stacks.Chow.bundle E)
        (Stacks.Chow.bundleTwist E) (Stacks.Chow.isInvertible_bundleTwist E)) := rfl
  have e₁ := (Stacks.DeRhamWeil.untwist (k := k) (hodgeAlgebraOf (bundle X E r)) 1).apply_symm_apply
    (DirectSum.of (hodgePiece (formsAlgebras (bundle X E r).obj.hom)) 2
      (hodgeFirstChernClassPiece (bundle X E r) (picardClassOf (Stacks.Chow.bundle E)
        (Stacks.Chow.bundleTwist E) (Stacks.Chow.isInvertible_bundleTwist E))))
  have e₂ : hodgeFirstChernClassPiece (bundle X E r) (picardClassOf (Stacks.Chow.bundle E)
        (Stacks.Chow.bundleTwist E) (Stacks.Chow.isInvertible_bundleTwist E)) =
      DirectSum.of (fun i : HodgeBidegreeInt 2 =>
        (AlgebraicGeometry.SheafOfModules.hodgeCohomologyComponent
          (formsAlgebras (bundle X E r).obj.hom) i.1.1 (i.1.2 : ℤ) : Type u))
        bidegreeOneOne (hodgeFirstChernClassModule (bundle X E r).obj.hom
          (picardClassOf (Stacks.Chow.bundle E) (Stacks.Chow.bundleTwist E)
            (Stacks.Chow.isInvertible_bundleTwist E))) :=
    AddMonoidHom.comp_apply _ _ _
  have e₃ : DirectSum.of (hodgePiece (formsAlgebras (bundle X E r).obj.hom)) 2
      (DirectSum.of (fun i : HodgeBidegreeInt 2 =>
        (AlgebraicGeometry.SheafOfModules.hodgeCohomologyComponent
          (formsAlgebras (bundle X E r).obj.hom) i.1.1 (i.1.2 : ℤ) : Type u))
        bidegreeOneOne (hodgeFirstChernClassModule (bundle X E r).obj.hom
          (picardClassOf (Stacks.Chow.bundle E) (Stacks.Chow.bundleTwist E)
            (Stacks.Chow.isInvertible_bundleTwist E)))) = hodgeBundleClass X.obj.hom E := rfl
  refine (congrArg (tateTwistCoordinates (LinearEquiv.refl k k) 1) e₀).trans ?_
  refine e₁.trans ?_
  refine (congrArg (DirectSum.of (hodgePiece (formsAlgebras (bundle X E r).obj.hom)) 2) e₂).trans ?_
  exact e₃

/-- **The degreewise map of axiom (A3) for one projective bundle** is bijective once the
degreewise map `(a_i) ↦ ∑ ξ^i ∪ p^*(a_i)` of the projective bundle formula for Hodge cohomology
is, `ξ` being `c₁^{Hodge}(𝒪_P(1))`. -/
theorem bijective_degreewiseMap_bundleClassU_of_bijective (n : ℤ)
    (h :
      letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
        E (r + 1)
      letI := hodgeAlgebraAlgebra (formsAlgebras X.obj.hom) (hodgeScalarsOverField X.obj.hom)
      letI := hodgeAlgebraAlgebra (formsAlgebras (Stacks.Chow.bundleProj E ≫ X.obj.hom))
        (hodgeScalarsOverField (Stacks.Chow.bundleProj E ≫ X.obj.hom))
      letI := hodgeGradedAlgebra (formsAlgebras X.obj.hom) (hodgeScalarsOverField X.obj.hom)
      letI := hodgeGradedAlgebra (formsAlgebras (Stacks.Chow.bundleProj E ≫ X.obj.hom))
        (hodgeScalarsOverField (Stacks.Chow.bundleProj E ≫ X.obj.hom))
      Function.Bijective (Stacks.WeilDeRham.degreewiseMap
        (hodgeGrade (formsAlgebras X.obj.hom) (hodgeScalarsOverField X.obj.hom))
        (hodgeGrade (formsAlgebras (Stacks.Chow.bundleProj E ≫ X.obj.hom))
          (hodgeScalarsOverField (Stacks.Chow.bundleProj E ≫ X.obj.hom)))
        (hodgeAlgebraPullbackOverBase_mem_hodgeGrade (Stacks.Chow.bundleProj E) (specScalars k)
          X.obj.hom (Stacks.Chow.bundleProj E ≫ X.obj.hom) (Category.comp_id _).symm)
        (hodgeBundleClass_mem X.obj.hom E) (r + 1) n)) :
    Function.Bijective (Stacks.WeilDeRham.degreewiseMap ((hodgeFirstChernClassData k).grade X)
      ((hodgeFirstChernClassData k).grade (bundle X E r))
      ((hodgeFirstChernClassData k).pull_grade (bundleProj X E r))
      ((hodgeFirstChernClassData k).bundleClassU_mem X E r) (r + 1) n) := by
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
  have hc := tateTwistCoordinates_hodgeFirstChernClassData_bundleClass X E r
  have hc_mem : tateTwistCoordinates (LinearEquiv.refl k k) 1
      ((hodgeFirstChernClassData k).bundleClass X E r) ∈
        (hodgeFirstChernClassData k).grade (bundle X E r) 2 := by
    rw [hc]
    exact hodgeBundleClass_mem X.obj.hom E
  have aux : ∀ (ξ : hodgeAlgebraOf (bundle X E r))
      (hξ : ξ ∈ (hodgeFirstChernClassData k).grade (bundle X E r) 2),
      ξ = hodgeTateScalar k • tateTwistCoordinates (LinearEquiv.refl k k) 1
        ((hodgeFirstChernClassData k).bundleClass X E r) →
      Function.Bijective (Stacks.WeilDeRham.degreewiseMap ((hodgeFirstChernClassData k).grade X)
        ((hodgeFirstChernClassData k).grade (bundle X E r))
        ((hodgeFirstChernClassData k).pull_grade (bundleProj X E r)) hξ (r + 1) n) := by
    rintro _ hξ rfl
    refine (bijective_degreewiseMap_smul_iff
      ((hodgeFirstChernClassData k).pull_grade (bundleProj X E r)) hc_mem (hodgeTateScalar k)
      (hodgeTateScalar_ne_zero k) hξ (r + 1) n).2 ?_
    revert hc_mem
    rw [hc]
    exact fun _ => h
  exact aux _ _ (hodge_κ_one _ _)

end Axiom

variable (k) in
/-- **Axiom (A3) for Hodge cohomology from the projective bundle formula for Hodge
cohomology.** If for every scheme `s : X ⟶ Spec k`, every finite locally free `𝒪_X`-module `ℰ`
of rank `r + 1` with projective bundle `p : P = 𝐏(ℰ) ⟶ X` and every degree `n` the map
`∏_{i ≤ r} H^{n - 2i}_{Hodge}(X/k) ⟶ H^n_{Hodge}(P/k)`, `(a_i) ↦ ∑ ξ^i ∪ p^*(a_i)` with
`ξ = c₁^{Hodge}(𝒪_P(1))`, is bijective, then the data of Hodge cohomology satisfy axiom (A3). -/
theorem hodge_projectiveBundleAxiom_of_bijective_degreewiseMap
    (h : ∀ (X : Scheme.{u}) (s : X ⟶ Spec (.of k)) (E : X.Modules) (r : ℕ)
      [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)] (n : ℤ),
      letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
        E (r + 1)
      letI := hodgeAlgebraAlgebra (formsAlgebras s) (hodgeScalarsOverField s)
      letI := hodgeAlgebraAlgebra (formsAlgebras (Stacks.Chow.bundleProj E ≫ s))
        (hodgeScalarsOverField (Stacks.Chow.bundleProj E ≫ s))
      letI := hodgeGradedAlgebra (formsAlgebras s) (hodgeScalarsOverField s)
      letI := hodgeGradedAlgebra (formsAlgebras (Stacks.Chow.bundleProj E ≫ s))
        (hodgeScalarsOverField (Stacks.Chow.bundleProj E ≫ s))
      Function.Bijective (Stacks.WeilDeRham.degreewiseMap
        (hodgeGrade (formsAlgebras s) (hodgeScalarsOverField s))
        (hodgeGrade (formsAlgebras (Stacks.Chow.bundleProj E ≫ s))
          (hodgeScalarsOverField (Stacks.Chow.bundleProj E ≫ s)))
        (hodgeAlgebraPullbackOverBase_mem_hodgeGrade (Stacks.Chow.bundleProj E) (specScalars k)
          s (Stacks.Chow.bundleProj E ≫ s) (Category.comp_id _).symm)
        (hodgeBundleClass_mem s E) (r + 1) n)) :
    (hodgeFirstChernClassData k).ProjectiveBundleAxiom :=
  Stacks.WeilDeRham.projectiveBundleAxiom_of_degreewise _ fun X E r _ n =>
    bijective_degreewiseMap_bundleClassU_of_bijective X E r n (h _ X.obj.hom E r n)

end Stacks.HodgeWeil

end
