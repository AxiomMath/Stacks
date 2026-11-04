module

public import StacksFrontier.AlgebraicGeometry.Blowup.ProjectiveSpaceEmbeddingTwist
public import StacksFrontier.AlgebraicGeometry.Picard.DiagonalFibreDivisor
public import StacksFrontier.AlgebraicGeometry.PicardGroup.PullbackHom

/-!
# A tensor inverse of an ideal sheaf pulls back to `𝒪(-1)` on an affine blowup

Let `R` be a ring, `I ⊆ R` an ideal and `X' = Proj(⨁_{d ≥ 0} Iᵈ)` the blowup of `Spec R` in `I`,
with exceptional divisor `E`.  Let `f : X' ⟶ T` be a morphism of schemes, let `D` be a closed
subscheme of `T` whose inverse image along `f` is `E`, and let `M` be an `𝒪_T`-module with
`M ⊗ 𝓘_D ≅ 𝒪_T`.  Then `f^*M ≅ 𝒪_{X'}(-1)`.

Indeed `𝓘_D` is invertible, so `D` is an effective Cartier divisor, `M` is invertible and
`[M] = -[𝓘_D]` in `Pic(T)`.  Pulling back is a homomorphism of Picard groups, and the ideal
sheaf of `D` pulls back to the ideal sheaf `𝓘_E` of `f⁻¹(D) = E`, so
`[f^*M] = -[𝓘_E] = [𝒪_{X'}(E)] = [𝒪_{X'}(-1)]`, the last equality being the affine case of
part (3) of Stacks 02OS.

## Main results

* `Stacks.Blowup.nonempty_pullback_iso_twistingSheaf_neg_one_of_tensor_iso_unit`.

## References

* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf)

universe u

namespace Stacks.Blowup

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- **A tensor inverse of an ideal sheaf pulls back to `𝒪(-1)` on the affine blowup.**  Let
`f : Proj(⨁ Iᵈ) ⟶ T` be a morphism of schemes and `D ⊆ T` a closed subscheme whose inverse image
along `f` is the exceptional divisor of the blowup of `Spec R` in `I`.  If an `𝒪_T`-module `M`
satisfies `M ⊗ 𝓘_D ≅ 𝒪_T`, then `f^*M ≅ 𝒪(-1)`. -/
theorem nonempty_pullback_iso_twistingSheaf_neg_one_of_tensor_iso_unit {T : Scheme.{u}}
    (f : AlgebraicGeometry.Proj (reesGrading I) ⟶ T) (D : T.IdealSheafData)
    (hD : D.comap f = (Scheme.IdealSheafData.ofIdealTop
      (Ideal.comap (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom I)).comap (toSpec I))
    (M : T.Modules)
    (e : ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨T.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ T.presheaf (forget₂ CommRingCat RingCat)
          T.ringCatIsSheaf⟩).obj M).obj (Stacks.Divisors.negativeTwist' D) ≅
      _root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        T.presheaf T.ringCatIsSheaf)) :
    Nonempty ((Scheme.Modules.pullback f).obj M ≅ twistingSheaf (reesGrading I) (-1)) := by
  set E : (AlgebraicGeometry.Proj (reesGrading I)).IdealSheafData :=
    (Scheme.IdealSheafData.ofIdealTop
      (Ideal.comap (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom I)).comap (toSpec I) with hE
  have hEc : Stacks.Divisors.IsEffectiveCartierDivisor E :=
    isEffectiveCartierDivisor_comap_toSpec_ofIdealTop I
  -- the ideal sheaf of `D` is invertible, so `D` is an effective Cartier divisor
  have hN : Stacks.SheafOfModules.IsInvertible T.presheaf T.ringCatIsSheaf
      (Stacks.Divisors.negativeTwist' D) :=
    (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit _).mpr
      ⟨M, ⟨Stacks.SheafOfModules.tensorSheafBraiding _ _ _ _ ≪≫ e⟩⟩
  have hDc : Stacks.Divisors.IsEffectiveCartierDivisor D :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp hN
  have hM : Stacks.SheafOfModules.IsInvertible T.presheaf T.ringCatIsSheaf M :=
    (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit _).mpr ⟨_, ⟨e⟩⟩
  have hMN : Stacks.SheafOfModules.IsInvertible T.presheaf T.ringCatIsSheaf
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨T.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ T.presheaf (forget₂ CommRingCat RingCat)
          T.ringCatIsSheaf⟩).obj M).obj (Stacks.Divisors.negativeTwist' D)) :=
    have := hM
    have := hN
    Stacks.SheafOfModules.isInvertible_tensorSheaf _ _ _ _
  -- `[M] = -[𝓘_D]` in `Pic(T)`
  have hsum : T.picardClass M hM + T.picardClass _ hN = 0 :=
    (T.picardClass_tensorSheaf M _ hM hN hMN).trans ((T.picardClass_eq_zero_iff _ hMN).mpr ⟨e⟩)
  have hclass : T.picardClass M hM = -T.picardClass _ hN := eq_neg_of_add_eq_zero_left hsum
  -- pull back along `f`
  have hfM : Stacks.SheafOfModules.IsInvertible (AlgebraicGeometry.Proj (reesGrading I)).presheaf
      (AlgebraicGeometry.Proj (reesGrading I)).ringCatIsSheaf ((Scheme.Modules.pullback f).obj M) :=
    Stacks.RingedSpace.modulePullback_isInvertible_of f.toLRSHom.toShHom M hM
  have hl : Stacks.SheafOfModules.pullbackPicardHom f (T.picardClass M hM) =
      (AlgebraicGeometry.Proj (reesGrading I)).picardClass
        ((Scheme.Modules.pullback f).obj M) hfM :=
    Stacks.SheafOfModules.pullbackPicardHom_picardClass f M hM
  have hr : Stacks.SheafOfModules.pullbackPicardHom f (-T.picardClass _ hN) =
      -(AlgebraicGeometry.Proj (reesGrading I)).picardClass
        (Stacks.Divisors.negativeTwist' E) (Stacks.Hilbert.isInvertible_negativeTwist' E hEc) :=
    (map_neg _ _).trans (congrArg Neg.neg
      ((Stacks.SheafOfModules.pullbackPicardHom_picardClass f _ hN).trans
        (Stacks.Hilbert.pullbackPicardClass_negativeTwist' f D E hD hDc hEc)))
  have h1 : (AlgebraicGeometry.Proj (reesGrading I)).picardClass
      ((Scheme.Modules.pullback f).obj M) hfM =
      -(AlgebraicGeometry.Proj (reesGrading I)).picardClass
        (Stacks.Divisors.negativeTwist' E) (Stacks.Hilbert.isInvertible_negativeTwist' E hEc) :=
    hl.symm.trans ((congrArg (Stacks.SheafOfModules.pullbackPicardHom f) hclass).trans hr)
  -- `-[𝓘_E] = [𝒪(E)] = [𝒪(-1)]`
  have := hEc
  have h3 : (AlgebraicGeometry.Proj (reesGrading I)).picardClass
      (Stacks.Divisors.negativeTwist' E) (Stacks.Hilbert.isInvertible_negativeTwist' E hEc) =
      -Stacks.Divisors.picardClass E :=
    Stacks.Divisors.negativeTwistPicardClass_eq_neg E
  have h4 : Stacks.Divisors.picardClass E =
      (AlgebraicGeometry.Proj (reesGrading I)).picardClass (twistingSheaf (reesGrading I) (-1))
        (isInvertible_blowUpTwist I (-1)) :=
    ((AlgebraicGeometry.Proj (reesGrading I)).picardClass_eq_iff _ _ _ _).mpr
      ⟨invertibleSheafComapToSpecIsoTwistingSheafNegOne I⟩
  exact ((AlgebraicGeometry.Proj (reesGrading I)).picardClass_eq_iff _ _ _ _).mp
    (h1.trans ((congrArg Neg.neg h3).trans ((neg_neg _).trans h4)))

end Stacks.Blowup

end
