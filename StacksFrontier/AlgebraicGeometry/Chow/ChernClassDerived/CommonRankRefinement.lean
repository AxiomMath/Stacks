module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.DerivedChernClasses

/-!
# Comparing total classes on a common refinement of two rank decompositions

Let `Y` be locally of finite type over the base of chapter 42 of the Stacks Project and let
`𝓔₁^•`, `𝓔₂^•` be locally bounded complexes of finite locally free `𝒪_Y`-modules. The classes
`c(𝓔^•)` and the alternating rank class of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.DerivedChernClasses` are glued over the rank
loci of the complex they are attached to (Stacks 0FDZ), so an identity relating classes of *two*
complexes cannot be read on either decomposition alone: it has to be read on the common
refinement, the loci where `𝓔₁^•` has constant ranks `ρ` and `𝓔₂^•` has constant ranks `σ`.

## Main results

* `Stacks.Chow.eq_of_res_eq_of_constantRanks`: two total classes of `Y` are equal as soon as
  they agree after restriction along every morphism over which both complexes have constant
  ranks.

## References

* [Stacks Project, Tag 0ESZ](https://stacks.math.columbia.edu/tag/0ESZ)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  {P₁ P₂ : CochainComplex Y.Modules ℤ} (h₁ : IsLocallyBoundedFiniteLocallyFree P₁)
  (h₂ : IsLocallyBoundedFiniteLocallyFree P₂)

include h₁ h₂ in
/-- **Two total classes agreeing wherever two complexes have constant ranks are equal.** If `c` and
`d` agree after restriction along every morphism locally of finite type `g : Z ⟶ Y` over which the
termwise pullbacks of `P₁` and `P₂` have constant ranks, then `c = d`. -/
theorem eq_of_res_eq_of_constantRanks {c d : TotalChowClass C sY}
    (H : ∀ (Z : Scheme.{u}) (g : Z ⟶ Y) (_ : LocallyOfFiniteType g) (ρ σ : ℤ →₀ ℕ),
      (∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((pullbackComplex g P₁).X n) (ρ n)) →
      (∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((pullbackComplex g P₂).X n) (σ n)) →
      TotalChowClass.res g rfl c = TotalChowClass.res g rfl d) :
    c = d := by
  refine TotalChowClass.eq_of_res_eq (isClopenDecomposition_complexRankLoci h₁) fun ρ ↦ ?_
  refine TotalChowClass.eq_of_res_eq
    ((isClopenDecomposition_complexRankLoci h₂).preimage (complexRankLoci h₁ ρ).ι) fun σ ↦ ?_
  rw [TotalChowClass.res_res, TotalChowClass.res_res]
  set W := (complexRankLoci h₁ ρ).ι ⁻¹ᵁ complexRankLoci h₂ σ
  have hρg : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((pullbackComplex (W.ι ≫ (complexRankLoci h₁ ρ).ι) P₁).X n) (ρ.down n) := fun n ↦
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      ((Scheme.Modules.pullbackComp W.ι (complexRankLoci h₁ ρ).ι).app (P₁.X n))
      (isFiniteLocallyFreeOfRank_pullbackComplex_X
        (pullbackComplex (complexRankLoci h₁ ρ).ι P₁) W.ι ρ.down
        (isFiniteLocallyFreeOfRank_complexRankLocus h₁ ρ.down) n)
  have hσg : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((pullbackComplex (W.ι ≫ (complexRankLoci h₁ ρ).ι) P₂).X n) (σ.down n) :=
    isFiniteLocallyFreeOfRank_pullbackComplex_preimage_complexRankLocus h₂
      (complexRankLoci h₁ ρ).ι σ.down
  exact H W.toScheme (W.ι ≫ (complexRankLoci h₁ ρ).ι) inferInstance ρ.down σ.down hρg hσg

end Stacks.Chow

end
