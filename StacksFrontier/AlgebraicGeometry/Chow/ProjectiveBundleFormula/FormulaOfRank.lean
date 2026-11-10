module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Formula
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.ChernClassesOfRank
public import StacksCore.Tactic.StacksAttribute

/-!
# The projective space bundle formula at every rank

Let `(S, δ)` be a base situation of chapter 42, `X` locally of finite type over `S`, `ℰ` a
finite locally free `𝒪_X`-module of rank `r` and `(π : P ⟶ X, 𝒪_P(1))` the projective bundle of
`ℰ`. [Stacks, Tag 02TX] asserts that the map

  `⨁_{i = 0}^{r - 1} A_{k + i}(X) ⟶ A_{k + r - 1}(P),  (α_i) ↦ ∑_i c₁(𝒪_P(1))^i ∩ π^*α_i`

is an isomorphism. For `r = n + 1` this is `Stacks.Chow.projectiveBundle_formula`; for `r = 0`
the source is the empty direct sum and `P` is empty, so its Chow groups vanish.

## Main definitions

* `Stacks.Chow.projectiveBundleFormulaMap` — the map of Stacks 02TX, for a module of rank `r`.
* `Stacks.Chow.projectiveBundleFormulaEquiv` — the same map as an additive isomorphism.

## Main results

* `Stacks.Chow.bijective_projectiveBundleFormulaMap` — **Stacks 02TX.**

## References

* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}} (E : X.Modules) (r : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
  (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **The summand `c₁(𝒪_P(1))^i ∩ π^*(-) : A_{k+i}(X) ⟶ A_{k+r-1}(P)`** of the map of Stacks 02TX,
for the projective bundle `π : P ⟶ X` of a module of rank `r` and `i < r`; here `π^*` is the flat
pullback along `π`, of relative dimension `r - 1`. -/
def projectiveBundleFormulaTerm (k : ℤ) (i : Fin r) :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E r
    chowGroup C sX (k + (i : ℕ)) →+ chowGroup C (bundleProj E ≫ sX) (k + r - 1) :=
  letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E r
  letI := flat_bundleProj_ofRank E r
  letI := locallyOfFiniteType_bundleProj_ofRank E r
  (capPow C (bundleProj E ≫ sX) (bundleTwistCap E C sX) i (k + (i : ℕ) + ((r - 1 : ℕ) : ℤ))
      (k + r - 1) (by have := i.isLt; omega)).comp
    (bundlePullback C sX (bundleProj E ≫ sX) (bundleProj E) rfl (r - 1)
      (relativeDimension_bundleProj_ofRank E r) (k + (i : ℕ)))

/-- **The map of Stacks 02TX**, for the projective bundle `π : P ⟶ X` of a module of rank `r`:
`⨁_{i = 0}^{r - 1} A_{k+i}(X) ⟶ A_{k+r-1}(P)`, `(α_i) ↦ ∑_i c₁(𝒪_P(1))^i ∩ π^*α_i`. -/
def projectiveBundleFormulaMap (k : ℤ) :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E r
    (∀ i : Fin r, chowGroup C sX (k + (i : ℕ))) →+ chowGroup C (bundleProj E ≫ sX) (k + r - 1) :=
  ∑ i : Fin r, (projectiveBundleFormulaTerm E r C sX k i).comp (Pi.evalAddMonoidHom _ i)

/-- The map `Stacks.Chow.projectiveBundleFormulaMap` sends `β` to
`∑_i c₁(𝒪_P(1))^i ∩ π^*(β i)`. -/
theorem projectiveBundleFormulaMap_apply (k : ℤ) (β : ∀ i : Fin r, chowGroup C sX (k + (i : ℕ))) :
    projectiveBundleFormulaMap E r C sX k β =
      ∑ i : Fin r, projectiveBundleFormulaTerm E r C sX k i (β i) := by
  simp [projectiveBundleFormulaMap]

section Succ

variable (n : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)]

/-- In rank `n + 1` the summands of the map of Stacks 02TX are those of `Stacks.Chow.bundleMap`,
up to the identification `A_{k+n}(P) = A_{k+(n+1)-1}(P)`. -/
theorem projectiveBundleFormulaTerm_succ (k : ℤ) (i : Fin (n + 1))
    (x : chowGroup C sX (k + (i : ℕ))) :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
      (n + 1)
    letI := flat_bundleProj E n
    letI := locallyOfFiniteType_bundleProj E n
    projectiveBundleFormulaTerm E (n + 1) C sX k i x =
      chowGroupCast C (bundleProj E ≫ sX) (by push_cast; ring)
        (bundleTerm C sX (bundleProj E ≫ sX) (bundleProj E) rfl n
          (relativeDimension_bundleProj E n) (invCap C (bundleProj E ≫ sX) (bundleTwist E)) k
          i x) := by
  dsimp only [projectiveBundleFormulaTerm, bundleTerm, AddMonoidHom.coe_comp,
    Function.comp_apply]
  rw [chowGroupCast_capPow]
  rfl

/-- In rank `n + 1` the map of Stacks 02TX is `Stacks.Chow.bundleMap`, up to the identification
`A_{k+n}(P) = A_{k+(n+1)-1}(P)`. -/
theorem projectiveBundleFormulaMap_succ (k : ℤ)
    (β : ∀ i : Fin (n + 1), chowGroup C sX (k + (i : ℕ))) :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
      (n + 1)
    letI := flat_bundleProj E n
    letI := locallyOfFiniteType_bundleProj E n
    projectiveBundleFormulaMap E (n + 1) C sX k β =
      chowGroupCast C (bundleProj E ≫ sX) (by push_cast; ring)
        (bundleMap C sX (bundleProj E ≫ sX) (bundleProj E) rfl n
          (relativeDimension_bundleProj E n) (invCap C (bundleProj E ≫ sX) (bundleTwist E)) k
          β) := by
  rw [projectiveBundleFormulaMap_apply]
  simp only [bundleMap, AddMonoidHom.finsetSum_apply, AddMonoidHom.coe_comp, Function.comp_apply,
    Pi.evalAddMonoidHom_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ projectiveBundleFormulaTerm_succ E C sX n k i (β i)

end Succ

/-- **The projective space bundle formula.** Let `X` be locally of finite type over the
base `S` of chapter 42, `ℰ` a finite locally free `𝒪_X`-module of rank `r` and
`(π : P ⟶ X, 𝒪_P(1))` its projective bundle. Then the map
`⨁_{i = 0}^{r - 1} A_{k+i}(X) ⟶ A_{k+r-1}(P)`, `(α_i) ↦ ∑_i c₁(𝒪_P(1))^i ∩ π^*α_i`, is an
isomorphism, for every `k`. -/
@[stacks 02TX, sga "7 XVII 5.3" "more general"]
theorem bijective_projectiveBundleFormulaMap (k : ℤ) :
    Function.Bijective (projectiveBundleFormulaMap E r C sX k) := by
  rcases r with _ | n
  · let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E 0
    have := subsingleton_chowGroup_bundle_of_rank_zero E C sX (k + ((0 : ℕ) : ℤ) - 1)
    refine ⟨fun β γ _ ↦ funext fun i ↦ i.elim0, fun y ↦ ⟨fun i ↦ i.elim0, Subsingleton.elim _ _⟩⟩
  · let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
      (n + 1)
    let := flat_bundleProj E n
    let := locallyOfFiniteType_bundleProj E n
    have h : ⇑(projectiveBundleFormulaMap E (n + 1) C sX k) =
        ⇑(chowGroupCast C (bundleProj E ≫ sX) (by push_cast; ring)) ∘
          (bundleMap C sX (bundleProj E ≫ sX) (bundleProj E) rfl n
            (relativeDimension_bundleProj E n) (invCap C (bundleProj E ≫ sX) (bundleTwist E)) k) :=
      funext (projectiveBundleFormulaMap_succ E C sX n k)
    rw [h]
    exact (AddEquiv.bijective _).comp (projectiveBundle_formula E n C sX k)

/-- **The projective space bundle formula as an isomorphism**:
`⨁_{i = 0}^{r - 1} A_{k+i}(X) ≃ A_{k+r-1}(P)` for the projective bundle of a module of rank `r`,
the forward map being `Stacks.Chow.projectiveBundleFormulaMap`. -/
def projectiveBundleFormulaEquiv (k : ℤ) :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E r
    (∀ i : Fin r, chowGroup C sX (k + (i : ℕ))) ≃+ chowGroup C (bundleProj E ≫ sX) (k + r - 1) :=
  AddEquiv.ofBijective (projectiveBundleFormulaMap E r C sX k)
    (bijective_projectiveBundleFormulaMap E r C sX k)

/-- The isomorphism `Stacks.Chow.projectiveBundleFormulaEquiv` acts as
`Stacks.Chow.projectiveBundleFormulaMap`. -/
@[simp]
theorem projectiveBundleFormulaEquiv_apply (k : ℤ)
    (β : ∀ i : Fin r, chowGroup C sX (k + (i : ℕ))) :
    projectiveBundleFormulaEquiv E r C sX k β = projectiveBundleFormulaMap E r C sX k β :=
  rfl

end Stacks.Chow

end
