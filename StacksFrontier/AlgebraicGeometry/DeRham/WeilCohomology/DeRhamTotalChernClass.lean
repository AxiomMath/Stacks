module

public import StacksFrontier.AlgebraicGeometry.DeRham.WeilCohomology.DeRhamBundleFormulaBridge
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.ProjectiveBundleFormula
import StacksCore.Tactic.StacksAttribute

/-!
# The de Rham total Chern class (Tag 0FW9)

There is a unique rule which assigns to every quasi-compact and quasi-separated scheme `X` a total
Chern class `c^{dR} : K₀(Vect(X)) ⟶ ∏_{i ≥ 0} H^{2i}_{dR}(X/𝐙)` with

1. `c^{dR}(α + β) = c^{dR}(α) c^{dR}(β)`,
2. `c^{dR}(f^*α) = f^*c^{dR}(α)` for `f : X' ⟶ X`,
3. `c^{dR}([ℒ]) = 1 + c₁^{dR}(ℒ)` for `ℒ` invertible.

The proof is the source's: the category of quasi-compact and quasi-separated schemes with
`A(X) = ⨁_i H^{2i}_{dR}(X/𝐙)` satisfies the axioms of Section 0FI4
(`Stacks.DeRhamChern.sourceChernSetup` and its three clause theorems), the projective bundle
formula being Proposition 0FMT; Proposition 0FI5 then gives the unique rule.

## Main results

* `Stacks.DeRhamChern.bijective_sum_cup_bundle_picardClassOf`: Proposition 0FMT on
  `Stacks.Chow.bundle`, for any proof that `𝒪(1)` is invertible.
* `Stacks.DeRhamChern.bundleFormula_qcqs`: axiom (4) over any base, from Proposition 0FMT.
* `Stacks.DeRhamChern.deRhamSourceChernSetup`: the de Rham situation over `𝐙`.
* `Stacks.DeRhamChern.existsUnique_deRhamTotalChernClass`: **Tag 0FW9**.

## References

* [Stacks Project, Tag 0FW9](https://stacks.math.columbia.edu/tag/0FW9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.WeilCohomology Stacks.DeRhamBaseChange

universe u

attribute [local instance] Stacks.Cohomology.Generators.picardGroupAddCommGroup

namespace Stacks.DeRhamChern

/-- **The projective bundle formula of Proposition 0FMT on `Stacks.Chow.bundle`, for any witness
of the invertibility of `𝒪(1)`.** For `g : X ⟶ S`, `ℰ` locally free of constant rank `r` on `X` and
every `k`, the map `(a_i)_{i < r} ↦ ∑_i c₁^{dR}(𝒪(1))^i ∪ π^*(a_i)`,
`⨁_{i < r} H^{k - 2i}_{dR}(X/S) ⟶ H^k_{dR}(𝐏(ℰ)/S)`, is bijective; the first Chern class of
`𝒪(1) = Stacks.Chow.bundleTwist ℰ` is read from its Picard class
`Stacks.WeilCohomology.picardClassOf` at the invertibility proof `hL`. -/
theorem bijective_sum_cup_bundle_picardClassOf {X S : Scheme.{u}} (g : X ⟶ S) (E : X.Modules)
    (r : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (k : ℤ) :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E r
    ∀ hL : AlgebraicGeometry.SheafOfModules.IsInvertible (Stacks.Chow.bundle E).presheaf
        (Stacks.Chow.bundle E).ringCatSheaf.2 (Stacks.Chow.bundleTwist E),
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
              (deRhamFirstChernClassPicard (Stacks.Chow.bundleProj E ≫ g)
                (picardClassOf _ (Stacks.Chow.bundleTwist E) hL)) i)
            (DeRhamKatzOdaCech.deRhamPullbackModule (Stacks.Chow.bundleProj E) g
              (k - ((2 * (i : ℕ) : ℕ) : ℤ)) (a i)))) := by
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E r
  have := Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
  intro hL
  have e : picardClassOf _ (Stacks.Chow.bundleTwist E) hL = picardClassOf _
      (Stacks.Chow.bundleTwist E) (Stacks.ProjectiveBundleSplitting.isInvertible_tautologicalTwist E
        (Stacks.Chow.bundlePieces E)) := rfl
  rw [e]
  with_reducible exact Stacks.ProjectiveBundleDeRham.bijective_sum_cup_bundle g E r k

/-- **Axiom (4) of Section 45.12 for the de Rham situation** on quasi-compact and quasi-separated
schemes over any base `B`, from the de Rham projective bundle formula (Proposition 0FMT). -/
theorem bundleFormula_qcqs (B : Scheme.{u}) (X : (QCQSScheme B).FullSubcategory)
    (E : (((QCQSScheme B).ι ⋙ Over.forget B).obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)) :
    Function.Bijective fun a : Fin (r + 1) → evenDeRhamRing ((QCQSScheme B).ι.obj X).hom =>
      ∑ i : Fin (r + 1),
        c₁ (QCQSScheme B).ι (QCQSScheme.bundleObject X E r hE).toBundleDatum.bundle
            (QCQSScheme.bundleObject X E r hE).toBundleDatum.twistClass ^ (i : ℕ) *
          pull (QCQSScheme B).ι (QCQSScheme.bundleObject X E r hE).toBundleDatum.proj (a i) :=
  bundleFormula_of_degreewise X E r hE fun n =>
    bijective_sum_cup_bundle_picardClassOf X.obj.hom E (r + 1) ((2 * n : ℕ) : ℤ) _

/-- **The de Rham situation of the proof of Tag 0FW9**: quasi-compact and quasi-separated schemes
with `A(X) = ⨁_i H^{2i}_{dR}(X/𝐙)`. -/
abbrev deRhamSourceChernSetup :=
  sourceChernSetup (Spec (CommRingCat.of ℤ)) (bundleFormula_qcqs (Spec (CommRingCat.of ℤ)))

/-- There is a unique rule which assigns to every quasi-compact and quasi-separated scheme `X` a
total Chern class `c^{dR} : K₀(Vect(X)) ⟶ ∏_{i ≥ 0} H^{2i}_{dR}(X/𝐙)`, read by components
`c X α i ∈ H^{2i}_{dR}(X/𝐙)` in the even-degree ring, such that `c(α + β) = c(α) c(β)` (and
`c(0) = 1`), `c(f^*α) = f^*c(α)` and `c([ℒ]) = 1 + c₁^{dR}(ℒ)`
(`Stacks.DeRhamChern.IsDeRhamTotalChernClass`). -/
@[stacks 0FW9 "there is a unique rule assigning to every quasi-compact and quasi-separated \
scheme X a total Chern class c^dR : K_0(Vect(X)) -> prod_{i >= 0} H^{2i}_dR(X/Z) with \
(1) c^dR(alpha + beta) = c^dR(alpha) c^dR(beta), (2) c^dR(f^*alpha) = f^*c^dR(alpha) for every \
morphism f : X -> X' of quasi-compact and quasi-separated schemes, \
(3) c^dR([L]) = 1 + c_1^dR(L) for L in Pic(X)"]
theorem existsUnique_deRhamTotalChernClass :
    ∃! c : ∀ X : (QCQSScheme (Spec (CommRingCat.of ℤ))).FullSubcategory,
        VectorBundleKZero ((QCQSScheme (Spec (CommRingCat.of ℤ))).ι.obj X).left → ℕ →
          evenDeRhamRing ((QCQSScheme (Spec (CommRingCat.of ℤ))).ι.obj X).hom,
      IsDeRhamTotalChernClass (QCQSScheme (Spec (CommRingCat.of ℤ))).ι c :=
  existsUnique_isDeRhamTotalChernClass_of_bundleFormula _
    (bundleFormula_qcqs (Spec (CommRingCat.of ℤ)))

end Stacks.DeRhamChern

end
