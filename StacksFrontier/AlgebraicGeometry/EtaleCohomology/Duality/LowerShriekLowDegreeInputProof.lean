module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.PoincareDualityFibrationInputs
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ElementaryFibrationLowerShriek
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ProperCurveHigherDirectImageLisse
public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityPullbackDegree

/-!
# The low-degree direct images with compact support of an elementary fibration

Let `k` be an algebraically closed field, `ℓ` a prime invertible in `k`, `S` affine and smooth
over `k`, and `f : U → S` an elementary fibration: `f = f̄ ∘ j` with `f̄ : X̄ → S` smooth
projective of relative dimension one with geometrically irreducible fibres and `j` the complement
of a closed `Z ⊂ X̄` finite étale and surjective over `S`. Then, for every compactification of
`f`, `R⁰ f_! ℤ/ℓ = 0` and `R¹ f_! ℤ/ℓ` is locally constant of finite type
(`Stacks.EtaleCohomology.lowerShriekLowDegreeInput`, which proves
`Stacks.EtaleCohomology.LowerShriekLowDegreeInput`).

* `R⁰ = 0`: the long exact sequence of `0 → j_! j⁻¹ F → F → i_* i⁻¹ F → 0` under `Rf̄_*`, `f̄⁻¹`
  being full and `(i ≫ f̄)⁻¹` faithful
  (`Stacks.EtaleCohomology.isZero_lowerShriekHomology_zero_of_factorization`);
* `R¹` (indeed every `Rᵠ`) is locally constant of finite type: the same triangle, `Rᵠ f̄_* ℤ/ℓ`
  being locally constant of finite type by [Stacks, Tag 0GKV], case (a)
  (`isFiniteTypeLocallyConstant_homology_derivedDirectImage_inverseImage_unitSheaf`)
  and `(i ≫ f̄)_*` preserving local constancy (Tag 095B)
  (`Stacks.EtaleCohomology.isFiniteTypeLocallyConstant_lowerShriekHomology_of_factorization`).

The algebraic closedness of `k` is not used; it is part of the setting of the proposition.

This is an input of the fibration step of Poincaré duality in the proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

The statement consumes `Rf_!`, defined in the standard model `HasDerivedCategory.standard` of the
derived category.

## Main results

* `Stacks.EtaleCohomology.lowerShriekLowDegreeInput`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

open ExtensionTorsor

attribute [local instance] HasDerivedCategory.standard

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- **`R⁰ f_! ℤ/ℓ = 0` and `R¹ f_! ℤ/ℓ` is locally constant of finite type** for an elementary
fibration `f : U → S` over `S` affine and smooth over `k`, `ℓ` invertible in `k`, and any
compactification of `f`. -/
theorem lowerShriekLowDegreeInput : LowerShriekLowDegreeInput ℓ k := by
  intro hℓ U S q f e _ _ hf jf
  have hp : ℓ.Prime := Fact.out
  have : NeZero ℓ := ⟨hp.ne_zero⟩
  have : Smooth q := SmoothOfRelativeDimension.smooth e q
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian q
  have : IsNoetherian S := ⟨⟩
  obtain ⟨Xbar, Z, j, fbar, i, hj, hjf, hsm, hproj, hgi, hi, -, hrange, hfin, het, hsurj⟩ :=
    hf.exists_compactification
  have := hj
  have := hsm
  have := hgi
  have := hi
  have := hfin
  have := het
  have := hsurj
  have : IsProper fbar := isProper_of_isProjectiveMorphism fbar hproj
  have : Smooth fbar := SmoothOfRelativeDimension.smooth 1 fbar
  have : GeometricallyConnected fbar :=
    TopTrace.geometricallyConnected_of_geometricallyIrreducible fbar
  have : IsSeparated f := by rw [← hjf]; infer_instance
  have : LocallyOfFiniteType f := by rw [← hjf]; infer_instance
  have : QuasiCompact f := by
    have : CompactSpace Xbar := ⟨by
      simpa using QuasiCompact.isCompact_preimage (f := fbar) Set.univ isOpen_univ isCompact_univ⟩
    have : IsLocallyNoetherian Xbar := LocallyOfFiniteType.isLocallyNoetherian fbar
    have : IsNoetherian Xbar := ⟨⟩
    have : TopologicalSpace.NoetherianSpace U := j.isOpenEmbedding.isInducing.noetherianSpace
    rw [← hjf]
    infer_instance
  have hij : Set.range j.base = (Set.range i.base)ᶜ := by rw [hrange, compl_compl]
  have hℓS : IsUnit ((ℓ : ℕ) : Γ(S, ⊤)) := isUnit_natCast_sections k q hℓ
  have hdim : ∀ s : S, topologicalKrullDim (fbar.fiber s) ≤ 1 := fun s =>
    topologicalKrullDim_fiber_le_of_smoothOfRelativeDimension 1 fbar s
  have hG : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod ℓ) S.smallEtaleTopology
      (unitSheaf (X := S) ℓ) := by
    have : Finite (ULift.{u + 1} (ZMod ℓ)) := inferInstance
    exact Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_constantSheaf S.smallEtaleTopology
      (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)))
      ((ModuleCat.isFG_iff _).2 Module.Finite.of_finite)
  exact ⟨isZero_lowerShriekHomology_zero_of_factorization ℓ f j fbar hjf i hij jf
      (unitSheaf (X := S) ℓ),
    isFiniteTypeLocallyConstant_lowerShriekHomology_of_factorization ℓ f j fbar hjf i hij jf
      (unitSheaf (X := S) ℓ) hG
      (isFiniteTypeLocallyConstant_homology_derivedDirectImage_inverseImage_unitSheaf fbar hdim ℓ
        hℓS) 1⟩

end Stacks.EtaleCohomology

end
