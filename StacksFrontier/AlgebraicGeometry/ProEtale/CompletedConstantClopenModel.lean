module

public import StacksFrontier.AlgebraicGeometry.ProEtale.CompletedConstantBaseCase
public import StacksFrontier.AlgebraicGeometry.ProEtale.CompletedConstantClopenPieces

/-!
# A sheaf with locally constant reduction is completed constant on a clopen decomposition

Let `X` be an affine weakly contractible scheme, `Λ` a Noetherian ring and `I ⊆ Λ` an ideal.
If `F` is a sheaf of `Λ`-modules on `X_proét` such that `F[-a]` has bounded locally constant
reduction in `[a, a]` (`AlgebraicGeometry.ProEtale.HasBoundedLocallyConstantReduction`), then `X`
is a finite disjoint union of opens `U i` such that each restriction `F|_{U i}` is the completed
constant sheaf `\underline{M_i}^∧` of a finite projective `Λ^∧`-module `M_i`.

## Main results

* `AlgebraicGeometry.ProEtale.exists_clopenDecomposition_inverseImage_iso`: such a sheaf is
  completed constant, with finite projective value, on the members of a finite decomposition of
  `X` into disjoint opens.

## References

* [Stacks Project, Tag 09C3](https://stacks.math.columbia.edu/tag/09C3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

universe u w

namespace AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard Sheaf.monoidalCategory
  Stacks.ModuleSheaf.derivedMonoidal Stacks.ModuleSheaf.derivedSymmetric
  SheafOfModules.hasSheafify_commRingCat Stacks.hasSheafCompose_forget₂_commRingCat

variable (X : Scheme.{u}) (Λ : Type (max (u + 1) w)) [CommRing Λ] (I : Ideal Λ)
  [IsNoetherianRing Λ]

/-- Let `X` be an affine weakly contractible scheme and `F` a sheaf of `Λ`-modules on `X_proét`
such that `F[-a]` has bounded locally constant reduction in `[a, a]`: `F` is derived complete,
`F ⊗_Λ^L \underline{Λ/I}` has Tor amplitude in degree `0` and `F ⊗ \underline{Λ/I}` is locally
constant of finite type. Then `X` is a finite disjoint union of opens `U i` such that the
restriction of `F` to each `U i` is the completed constant sheaf `\underline{M_i}^∧` of a finite
projective `Λ^∧`-module `M_i`. -/
theorem exists_clopenDecomposition_inverseImage_iso [IsAffine X]
    (hX : ProetaleWContractible.IsWeaklyContractibleObj X)
    {F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)} {a : ℤ}
    (hF : HasBoundedLocallyConstantReduction X Λ I
      ((DerivedCategory.singleFunctor _ a).obj F) a a) :
    ∃ (n : ℕ) (U : Fin n → X.Opens), Pairwise (fun i j => Disjoint (U i) (U j)) ∧
      ⨆ i, U i = ⊤ ∧ ∀ i, ∃ M : ModuleCat.{max (u + 1) w} (AdicCompletion I Λ),
        Module.Finite (AdicCompletion I Λ) M ∧ Module.Projective (AdicCompletion I Λ) M ∧
        Nonempty ((proetaleModuleInverseImage.{u, max (u + 1) w, w} (U i).ι Λ).obj F ≅
          completedConstantSheaf (U i).toScheme Λ I
            ((restrictToCoefficients.{max (u + 1) w, max (u + 1) w} Λ I).obj M)) := by
  obtain ⟨n, U, hdisj, hcov, hclopen, hconst⟩ :=
    exists_opens_isConstantFGOver_of_isFiniteTypeLocallyConstantModuleSheaf X Λ hX _ (hF.2.2.2 a)
  refine ⟨n, U, hdisj, hcov, fun i => ?_⟩
  let Fi := (proetaleModuleInverseImage.{u, max (u + 1) w, w} (U i).ι Λ).obj F
  obtain ⟨haff, hwc⟩ := isAffine_and_isWContractible_of_isClopen
    (ProetaleWContractible.isWContractible_of_isWeaklyContractible X hX) (U i) (hclopen i)
  rcases isEmpty_or_nonempty (U i).toScheme with hU | hU
  · exact ⟨ModuleCat.of _ (Fin 0 → AdicCompletion I Λ), inferInstance, inferInstance,
      ⟨(Scheme.ProEt.isZero_sheaf_of_isEmpty _).iso (Scheme.ProEt.isZero_sheaf_of_isEmpty _)⟩⟩
  · obtain ⟨Mbar, hfin, ⟨c⟩⟩ :=
      exists_constantSheaf_iso_proetaleModuleInverseImage_of_isConstantFGOver (U i).ι (hconst i)
    obtain ⟨t⟩ := nonempty_proetaleModuleInverseImage_tensor_iso I F (U i).ι a
    let e : Fi ⊗ quotientConstantSheaf (U i).toScheme Λ I ≅
        (constantSheaf (Scheme.ProEt.topology (U i).toScheme) (ModuleCat.{max (u + 1) w} Λ)).obj
          Mbar := t ≪≫ c.symm
    exact exists_iso_completedConstantSheaf_of_reduction_iso Λ I Fi
      (isDerivedComplete_singleFunctor_zero_proetaleModuleInverseImage I hF.1 (U i).ι)
      (fun N hN => hF.isZero_homology_tensor_proetaleModuleInverseImage I (U i).ι N hN) Mbar
      (smul_eq_zero_of_tensor_quotientConstantSheaf_iso I Fi Mbar e) e
      (surjective_app_mk_id_reduction_of_isWContractible I hwc Fi)

end AlgebraicGeometry.ProEtale
