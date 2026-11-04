module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AdicQuotientComparisonCounterexample
import StacksCore.Tactic.StacksAttribute

/-!
# The comparison of the derived completion with the derived limit of the reductions

Let `(𝒞, 𝒪)` be a ringed site, `ℐ ⊂ 𝒪` a sheaf of ideals of finite type and `K ↦ K^∧` the
derived completion functor of [Stacks, Tag 099F]
(`AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete`). This file states
[Stacks, Tag 0CQH]:

* for `n ≥ 1` the object `K ⊗^𝐋_𝒪 𝒪/ℐⁿ` is derived complete, being annihilated by powers of
  local sections of `ℐ`;
* hence the canonical map `K ⟶ K ⊗^𝐋_𝒪 𝒪/ℐⁿ` factors canonically as
  `K ⟶ K^∧ ⟶ K ⊗^𝐋_𝒪 𝒪/ℐⁿ`;
* these factorizations are compatible for varying `n`, and give a comparison map
  `K^∧ ⟶ R lim (K ⊗^𝐋_𝒪 𝒪/ℐⁿ)`;
* in general this comparison map is not an isomorphism.

## Main results

* `AlgebraicGeometry.RingedSite.isDerivedComplete_derivedTensor_adicQuotient_of_isFiniteType`
* `AlgebraicGeometry.RingedSite.existsUnique_derivedCompletion_factorization_adicQuotient`
* `AlgebraicGeometry.RingedSite.derivedCompletionAdicFactor_comp_map`
* `AlgebraicGeometry.RingedSite.exists_derivedCompletionComparison`
* `AlgebraicGeometry.RingedSite.exists_not_isIso_derivedCompletionComparison`

## Implementation notes

The canonical map `K ⟶ K ⊗^𝐋_𝒪 𝒪/ℐⁿ` is `AlgebraicGeometry.RingedSite.adicQuotientReduction`,
the unit law `K ≅ K ⊗^𝐋_𝒪 𝒪[0]` followed by the projection `𝒪 ⟶ 𝒪/ℐⁿ`. The derived limit is
determined only up to non-unique isomorphism and is presented, as
`CategoryTheory.Pretriangulated.IsDerivedLimit` does, as the base `L` of a distinguished Milnor
triangle `L ⟶ ∏ₙ Tₙ ⟶ ∏ₙ Tₙ ⟶ L[1]` of the tower `Tₙ = K ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹`; a comparison map is a
map `K^∧ ⟶ L` whose composites with the projections are the factorizations. The comparison map is
not unique, and the failure is proved for every such map. The witness is the one-point ringed
site of `A = k[X] ⋉ k[X, X⁻¹]/k[X]`, with `ℐ = (X)` and `K = (𝒪/ℐ)[0]`
(`AlgebraicGeometry.RingedSite.not_isIso_derivedCompletionComparison_shiftIdealization`).

The first assertion holds for every sheaf of ideals and every `n`
(`AlgebraicGeometry.RingedSite.isDerivedComplete_derivedTensor_adicQuotient`); the others are
proved for an arbitrary left adjoint of the inclusion in `AdicQuotientFactorization.lean`, and
are stated here at the source's hypothesis, with the left adjoint of [Stacks, Tag 099F].

## References

* [Stacks Project, Tag 0CQH](https://stacks.math.columbia.edu/tag/0CQH)
* [Stacks Project, Tag 099F](https://stacks.math.columbia.edu/tag/099F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance] hasProductsOfShape_nat_derivedCategory_ringSheaf

section FiniteType

variable (X : RingedSite.{u, u, u})
  (I : SheafOfModules.Submodule
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))

/-- **[Stacks, Tag 0CQH], the derived completeness of the reductions.** For `ℐ` of finite type,
`K ⊗^𝐋_𝒪 𝒪/ℐⁿ` is derived complete along `ℐ`: multiplication by `fⁿ`, for a local section `f`
of `ℐ` over `U`, is zero on its restriction to `U`. The source states this for `n ≥ 1`; it holds
for every `n`, `𝒪/ℐ⁰` being zero. -/
@[stacks 0CQH "first assertion: `K ⊗^𝐋_𝒪 𝒪/ℐⁿ` is derived complete for `n ≥ 1`"]
theorem isDerivedComplete_derivedTensor_adicQuotient_of_isFiniteType
    [I.toSheafOfModules.IsFiniteType]
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (n : ℕ) :
    IsDerivedComplete.{u, u, u, u} X I
      (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj
        (adicQuotientObj X I n)) :=
  isDerivedComplete_derivedTensor_adicQuotient X I K n

end FiniteType

/-- **[Stacks, Tag 0CQH], the comparison map is not an isomorphism in general.** There are a
ringed site `(𝒞, 𝒪)`, a sheaf of ideals `ℐ` of finite type and `K ∈ D(𝒪)` such that no
comparison map `K^∧ ⟶ R lim (K ⊗^𝐋_𝒪 𝒪/ℐⁿ)` — no map `c` into a derived limit `L` of the
reduction tower whose composites with the projections are the factorizations — is an
isomorphism. The witness is the one-point ringed site of `k[X] ⋉ k[X, X⁻¹]/k[X]` for `k = ℤ`,
with `ℐ = (X)` and `K = (𝒪/ℐ)[0]`. -/
@[stacks 0CQH "fifth assertion: in general the comparison map is not an isomorphism"]
theorem exists_not_isIso_derivedCompletionComparison :
    ∃ (X : RingedSite.{u, u, u})
      (I : SheafOfModules.Submodule
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
      (_ : I.toSheafOfModules.IsFiniteType)
      (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))),
      ∀ (L : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
        (p : L ⟶ ∏ᶜ fun n : ℕ => (adicReductionTower X I K).obj ⟨n⟩)
        (δ : (∏ᶜ fun n : ℕ => (adicReductionTower X I K).obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧)
        (c : (derivedCompletion X I).obj K ⟶ L),
        Triangle.mk p (Pi.lift fun n : ℕ =>
            Pi.π (fun n : ℕ => (adicReductionTower X I K).obj ⟨n⟩) n -
            Pi.π (fun n : ℕ => (adicReductionTower X I K).obj ⟨n⟩) (n + 1) ≫
              (adicReductionTower X I K).map (homOfLE (Nat.le_succ n)).op) δ ∈
          distTriang
            (DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) →
        (∀ n : ℕ, c ≫ p ≫ Pi.π (fun n : ℕ => (adicReductionTower X I K).obj ⟨n⟩) n =
          derivedCompletionAdicFactor X I K (n + 1)) →
        ¬ IsIso c :=
  ⟨Stacks.PointRingedSite.site (Stacks.ShiftIdealization.Ring (ULift.{u} ℤ)),
    Stacks.PointRingedSite.idealX _ (Stacks.ShiftIdealization.x (ULift.{u} ℤ)), inferInstance,
    adicQuotientObj _ (Stacks.PointRingedSite.idealX _ (Stacks.ShiftIdealization.x _)) 1,
    fun _ _ _ c htri _ =>
      not_isIso_derivedCompletionComparison_shiftIdealization (ULift.{u} ℤ) htri c⟩

end AlgebraicGeometry.RingedSite
