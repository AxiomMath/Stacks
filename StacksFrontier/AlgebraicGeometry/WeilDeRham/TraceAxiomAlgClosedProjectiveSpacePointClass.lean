module

public import StacksFrontier.AlgebraicGeometry.WeilDeRham.TraceAxiomAlgClosedKunneth
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.TraceAxiomAlgClosedProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.DiagonalProduct

/-!
# The cycle class of a rational point of `ℙ^d_k`

Let data (D0), (D1), (D2') satisfy the axioms (A1) and (A3) of Section 45.14 of the Stacks
Project, let `ch^H` be a cohomological Chern character of Tag 0FIE (a rule `ch` with
`h : 𝔇.IsCohomologicalChernCharacter ch`) and `γ` the cycle class map of Lemma 0FIF
(`Stacks.WeilCohomology.FirstChernClassData.IsCohomologicalChernCharacter.codimensionCycleClass`,
on `CH^*(X) ⊗ 𝐐` `…IsCohomologicalChernCharacter.cycleClassMap`). For a `k`-rational point `y`
of `ℙ^d_k`,

  `γ([y]) = d! · ch^H_d(𝒪(1))`   in `H^{2d}(ℙ^d_k)(d)`.

## Main results

* `Stacks.WeilDeRham.codimensionToRationalChow_pointChowClass`: the class in `CH_*(X) ⊗ 𝐐` of
  the class `[y] ∈ CH^d(X)` of a rational point is `1 ⊗ y_*[Spec k]`.
* `Stacks.WeilDeRham.codimensionCycleClass_pointChowClass_projectiveSpace`:
  `γ([y]) = d! · ch^H_d(𝒪(1))` on `ℙ^d_k`.

## References

* [Stacks Project, Tag 0FWD](https://stacks.math.columbia.edu/tag/0FWD)
* [Stacks Project, Tag 0FIF](https://stacks.math.columbia.edu/tag/0FIF)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.WeilCohomology Stacks.WeilCohomology.SmoothProjectiveScheme
open scoped TensorProduct
open Stacks.Chow

universe u w

namespace Stacks.WeilDeRham

variable {k : Type u} [Field k] {F : Type w} [Field F]

section Graded

variable {X : (SmoothProjectiveScheme k).FullSubcategory}

variable [CharZero F] {𝔇 : FirstChernClassData k F}
  {ch : ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
    VectorBundleKZero ((toScheme k).obj X) → ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n}
  (h : 𝔇.IsCohomologicalChernCharacter ch) (hA1 : 𝔇.CoproductAxiom)
  (hA3 : 𝔇.ProjectiveBundleAxiom)

end Graded

/-! ### The class of a rational point -/

section Point

/-- For `X` pure of dimension `d` and a rational point `y`, the class in `CH_*(X) ⊗ 𝐐` of
`[y] ∈ CH^d(X)` is `1 ⊗ y_*[Spec k]`, in dimension `0`. -/
theorem codimensionToRationalChow_pointChowClass {X : (SmoothProjectiveScheme k).FullSubcategory}
    {d : ℕ} (hX : RelativeDimension X.obj.hom d) (y : Spec (.of k) ⟶ (toScheme k).obj X)
    (hy : y ≫ X.obj.hom = 𝟙 _) :
    haveI : IsSeparated X.obj.hom := (SmoothProjectiveScheme.isProjective X).isSeparated
    haveI : IsProper y := isProper_of_comp_eq_id hy
    codimensionToRationalChow k X.obj.hom d (pointChowClass y hy d) =
      DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) X.obj.hom j) 0
        ((1 : ℚ) ⊗ₜ properChowPushforward (fieldChowSituation k) (𝟙 _) X.obj.hom y hy 0
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ 0)
          (fundamentalChowClass (fieldChowSituation k) (𝟙 _) 0)) := by
  refine (codimensionToRationalChow_chowCodimPushforward_chowCodimFundamental
    (pointHom y hy) (isNonemptyEquidimensional_point (k := k)).relativeDimension hX
    (zero_add d)).trans ?_
  rw [rationalFundamentalClass_eq_of_relativeDimension k _
      (isNonemptyEquidimensional_point (k := k)).relativeDimension,
    rationalProperChowPushforward_of_tmul]
  rfl

end Point

/-! ### The class of a rational point of `ℙ^d_k` -/

section ProjectiveSpace

/-- For a `k`-rational point `y` of `ℙ^d_k`, `γ([y]) = d! · ch^H_d(𝒪(1))` in `H^{2d}(ℙ^d_k)(d)`,
where `γ` is the cycle class map of the cohomological Chern character `ch^H = ch`. -/
theorem codimensionCycleClass_pointChowClass_projectiveSpace [CharZero F]
    {𝔇 : FirstChernClassData k F}
    {ch : ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
      VectorBundleKZero ((toScheme k).obj X) → ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n}
    (h : 𝔇.IsCohomologicalChernCharacter ch) (hA1 : 𝔇.CoproductAxiom)
    (hA3 : 𝔇.ProjectiveBundleAxiom) (d : ℕ)
    (y : Spec (.of k) ⟶ (toScheme k).obj (projectiveSpace k d))
    (hy : y ≫ (projectiveSpace k d).obj.hom = 𝟙 _) :
    h.codimensionCycleClass (projectiveSpace k d) d (pointChowClass y hy d) =
      d.factorial • ch (projectiveSpace k d) (projectiveSpaceTwistClass k d) d := by
  have : IsSeparated (projectiveSpace k d).obj.hom :=
    (SmoothProjectiveScheme.isProjective _).isSeparated
  have : IsProper y := isProper_of_comp_eq_id hy
  refine h.codimensionCycleClass_eq_nsmul hA1 hA3 (projectiveSpace k d) d _ _ d.factorial ?_
  rw [codimensionToRationalChow_pointChowClass (relativeDimension_projectiveSpace k d) y hy,
    rationalChernCharacterComponentCap_tmul, one_smul]
  have hpt := rationalChowCap_chernCharacter_twistingSheaf_eq_point k d y hy
  refine Eq.trans ?_ (congrArg (fun v => d.factorial • v) hpt).symm
  have key : ∀ P : chowGroup (fieldChowSituation k) (projectiveSpace k d).obj.hom 0,
      DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k)
          (projectiveSpace k d).obj.hom j) 0 ((1 : ℚ) ⊗ₜ P) =
        d.factorial • DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k)
          (projectiveSpace k d).obj.hom j) 0 (((d.factorial : ℚ)⁻¹) ⊗ₜ P) := fun P => by
    rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul ℚ, TensorProduct.smul_tmul', smul_eq_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero d))]
  exact key _

end ProjectiveSpace

end Stacks.WeilDeRham

end
