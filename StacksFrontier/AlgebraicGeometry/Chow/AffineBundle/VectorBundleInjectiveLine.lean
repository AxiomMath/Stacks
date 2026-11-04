module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.VectorBundleChowInjective
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.VectorBundleAffineSpaceBundle
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.BranchChowInjective
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleCorankOneDivisor
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionZeroScheme
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafPullback
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional

/-!
# Injectivity of flat pullback along a vector bundle, one line at a time

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `Y` be locally of
finite type over `S` and let `0 ⟶ ℒ ⟶ ℱ ⟶ 𝒬 ⟶ 0` be a short exact sequence of quasi-coherent
`𝒪_Y`-modules with `ℒ` invertible and `𝒬` finite locally free of rank `r`, so that `ℱ` has rank
`r + 1`. The vector bundle `𝐕(𝒬)` sits in `𝐕(ℱ)` as an effective Cartier divisor
(`AlgebraicGeometry.Scheme.Modules.isEffectiveCartierDivisor_ker_vectorBundleMap`) which is flat
over `Y`, that is, a relative effective Cartier divisor on `𝐕(ℱ)/Y`. By Stacks 02TR the Gysin
map of that divisor retracts the flat pullback along `𝐕(ℱ) ⟶ Y` onto the flat pullback along
`𝐕(𝒬) ⟶ Y`. Hence if the latter is injective, so is the former.

## Main results

* `Stacks.Chow.flatPullbackChow_injective_vectorBundleToBase_of_line` — the step above.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  {L F Q : Y.Modules} [L.IsQuasicoherent] [F.IsQuasicoherent] [Q.IsQuasicoherent]
  (a : L ⟶ F) (b : F ⟶ Q) (w : a ≫ b = 0) (hS : (ShortComplex.mk a b w).ShortExact) (r : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1]
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Q r]
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F (r + 1)]

include hS in
/-- **Injectivity of flat pullback along `𝐕(ℱ) ⟶ Y` from injectivity along `𝐕(𝒬) ⟶ Y`**, for a
short exact sequence `0 ⟶ ℒ ⟶ ℱ ⟶ 𝒬 ⟶ 0` with `ℒ` of rank one and `𝒬` of rank `r`. -/
theorem flatPullbackChow_injective_vectorBundleToBase_of_line
    (hQ : letI := locallyOfFiniteType_vectorBundleToBase Q r
      letI := flat_vectorBundleToBase Q r
      ∀ k : ℤ, Function.Injective (flatPullbackChowOfRelativeDimension C
        (Scheme.Modules.vectorBundleToBase Y Q ≫ sY) sY (Scheme.Modules.vectorBundleToBase Y Q)
        rfl r (relativeDimension_vectorBundleToBase Q r) k))
    (m : ℤ) :
    letI := locallyOfFiniteType_vectorBundleToBase F (r + 1)
    letI := flat_vectorBundleToBase F (r + 1)
    Function.Injective (flatPullbackChowOfRelativeDimension C
      (Scheme.Modules.vectorBundleToBase Y F ≫ sY) sY (Scheme.Modules.vectorBundleToBase Y F)
      rfl (r + 1) (relativeDimension_vectorBundleToBase F (r + 1)) m) := by
  let := locallyOfFiniteType_vectorBundleToBase F (r + 1)
  let := flat_vectorBundleToBase F (r + 1)
  let := locallyOfFiniteType_vectorBundleToBase Q r
  let := flat_vectorBundleToBase Q r
  have : Epi b := hS.epi_g
  have := Scheme.Modules.isClosedImmersion_vectorBundleMap_of_epi b
  set ι := (Scheme.Modules.vectorBundleMap Y b).left with hι
  set D : (Scheme.Modules.vectorBundle Y F).IdealSheafData := ι.ker with hD_def
  have hDc : Stacks.Divisors.IsEffectiveCartierDivisor D :=
    Scheme.Modules.isEffectiveCartierDivisor_ker_vectorBundleMap a b w hS r
  -- the divisor is the vector bundle of the quotient
  have hfac : ι.toImage ≫ D.subschemeι = ι := ι.toImage_imageι
  have hDp : D.subschemeι ≫ Scheme.Modules.vectorBundleToBase Y F =
      inv ι.toImage ≫ Scheme.Modules.vectorBundleToBase Y Q := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, hfac, hι]
    exact Scheme.Modules.vectorBundleMap_left_comp Y b
  have : Flat (D.subschemeι ≫ Scheme.Modules.vectorBundleToBase Y F) := by
    rw [hDp]; infer_instance
  have : LocallyOfFiniteType (inv ι.toImage ≫ Scheme.Modules.vectorBundleToBase Y Q) := by
    rw [← hDp]; infer_instance
  have hq : AlgebraicGeometry.RelativeDimension
      (D.subschemeι ≫ Scheme.Modules.vectorBundleToBase Y F) r := by
    have h := AlgebraicGeometry.RelativeDimension.comp_isOpenImmersion (inv ι.toImage)
      (Scheme.Modules.vectorBundleToBase Y Q) (relativeDimension_vectorBundleToBase Q r)
    convert h using 1
  have := Stacks.Divisors.isInvertible_divisorSheaf D
  set s := Stacks.Divisors.sectionsOfTop (Stacks.Divisors.divisorSheaf D)
    (Stacks.Divisors.divisorSheafGlobalSection D) with hs_def
  have hDs : Stacks.Divisors.zeroScheme (Scheme.Modules.vectorBundle Y F)
      (Stacks.Divisors.divisorSheaf D) (s.eval (.op ⊤)) = D := by
    rw [hs_def, Stacks.Divisors.sectionsOfTop_eval_top]
    exact Stacks.Divisors.zeroScheme_canonicalSection D
  have hinjD : ∀ k : ℤ, Function.Injective (flatPullbackChowOfRelativeDimension C
      (D.subschemeι ≫ Scheme.Modules.vectorBundleToBase Y F ≫ sY) sY
      (D.subschemeι ≫ Scheme.Modules.vectorBundleToBase Y F)
      (by rw [Category.assoc]) r hq k) := by
    intro k
    have hebase : inv ι.toImage ≫ (Scheme.Modules.vectorBundleToBase Y Q ≫ sY) =
        D.subschemeι ≫ Scheme.Modules.vectorBundleToBase Y F ≫ sY := by
      rw [← Category.assoc, ← hDp, Category.assoc]
    exact flatPullbackChow_injective_of_isIso_comp C _ (Scheme.Modules.vectorBundleToBase Y Q ≫ sY)
      sY (inv ι.toImage) (Scheme.Modules.vectorBundleToBase Y Q) _ hDp.symm hebase rfl
      (by rw [Category.assoc]) r (relativeDimension_vectorBundleToBase Q r) hq k
      (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
      (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
      (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _) (hQ k)
  exact flatPullbackChow_injective_of_relativeEffectiveCartier C
    (Scheme.Modules.vectorBundleToBase Y F ≫ sY) sY
    (Scheme.Modules.vectorBundleToBase Y F) rfl r
    (relativeDimension_vectorBundleToBase F (r + 1)) (Stacks.Divisors.divisorSheaf D) s D hDs
    ⟨hDc, inferInstance⟩ hq hinjD m

end Stacks.Chow

end
