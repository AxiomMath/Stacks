module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportSmoothModelGalois
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapTwistOpenRestriction

/-!
# The restriction of the Galois twist on the smooth model to `X_k̄`

Let `X` be a geometrically connected smooth curve over a field `k`, `j : X ⟶ X̄` a
compactification over `k`, `k̄` an algebraically closed extension of `k` and `C` the smooth
projective model of `X_k̄`, with the open immersion `j_C : X_k̄ ⟶ C` and the morphism
`q : C ⟶ X̄`.  For a sheaf `F` of `Λ`-modules on `X` put `H = q^{-1}(j_! F)` and
`G = F|_{X_k̄}`.  This file identifies `j_C^{-1} H` with `G`
(`Stacks.EtaleCohomology.geometricSmoothModelInverseImageRestrictionIso`), canonically: through
`j_C ≫ q = pr ≫ j`, the composition isomorphisms of inverse images and `j^{-1} j_! F ≅ F`.  Under
it the restriction to `X_k̄` of the self-map twist of `H` along `s̃_σ` is the self-map twist of `G`
along `s_σ = id_X × Spec σ`
(`Stacks.EtaleCohomology.geometricSmoothModelInverseImageRestrictionIso_selfMapTwist`), the
restriction being taken through `j_C^{-1} (s̃_σ)_* ≅ (s_σ)_* j_C^{-1}`
(`Stacks.EtaleCohomology.restrictionIntegralDirectImageIso`) on the cartesian square
`j_C ≫ s̃_σ = s_σ ≫ j_C` (`Stacks.EtaleCohomology.isPullback_geometricSmoothModelGaloisAut_j`).

## Main definitions

* `Stacks.EtaleCohomology.geometricSmoothModelInverseImageRestrictionIso`.

## Main results

* `Stacks.EtaleCohomology.isPullback_geometricSmoothModelGaloisAut_j`.
* `Stacks.EtaleCohomology.geometricSmoothModelInverseImageRestrictionIso_selfMapTwist`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
  [GeometricallyConnected f] (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] (Λ : Type) [Ring Λ]

/-- `j_C ≫ q = pr ≫ j`: the open immersion of `X_k̄` into the smooth model followed by
`q : C ⟶ X̄` is the projection `X_k̄ ⟶ X` followed by `j`. -/
public lemma geometricSmoothModel_j_comp_proj :
    (geometricSmoothModel f j kbar).j ≫ geometricSmoothModelProj f j kbar =
      pullback.fst f (specAlgebraMap k kbar) ≫ j.immersion := by
  rw [geometricSmoothModelProj, geometricSmoothModel_j_fb_assoc,
    compactificationFieldBaseChange_immersion_comp_fst]

/-- `id_X × Spec σ` is an automorphism of `X_k̄`. -/
public instance isIso_galoisBaseChange_curve (σ : kbar ≃ₐ[k] kbar) :
    IsIso (galoisBaseChange (Over.mk f) kbar σ) :=
  ⟨⟨galoisBaseChange (Over.mk f) kbar σ⁻¹,
    by rw [← galoisBaseChange_mul, mul_inv_cancel, galoisBaseChange_one],
    by rw [← galoisBaseChange_mul, inv_mul_cancel, galoisBaseChange_one]⟩⟩

/-- **The square `j_C ≫ s̃_σ = s_σ ≫ j_C` is cartesian**, both horizontal maps being
isomorphisms. -/
public theorem isPullback_geometricSmoothModelGaloisAut_j (σ : kbar ≃ₐ[k] kbar) :
    IsPullback (P := pullback f (specAlgebraMap k kbar)) (X := pullback f (specAlgebraMap k kbar))
      (galoisBaseChange (Over.mk f) kbar σ) (geometricSmoothModel f j kbar).j
      (geometricSmoothModel f j kbar).j (geometricSmoothModelGaloisAut f j kbar σ) :=
  IsPullback.of_horiz_isIso ⟨(geometricSmoothModelGaloisAut_j f j kbar σ).symm⟩

/-- **`j_C^{-1} q^{-1}(j_! F) ≅ F|_{X_k̄}`** (ii.4a), with `j_C^{-1}` the restriction along the
open immersion `j_C : X_k̄ ⟶ C`: `Stacks.EtaleCohomology.selfMapTwistOpenRestrictionIso` for the
square `pr ≫ j = j_C ≫ q`, built from the comparison of restriction with inverse image, the
composition isomorphisms of inverse images and `j^{-1} j_! F ≅ F`. -/
public def geometricSmoothModelInverseImageRestrictionIso (F : EtaleModules.{u, 0} Λ X) :
    (etaleModuleRestriction.{u, 0} Λ (geometricSmoothModel f j kbar).j).obj
        ((etaleModuleInverseImage.{u, 0} Λ (geometricSmoothModelProj f j kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) ≅
      (etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj F :=
  selfMapTwistOpenRestrictionIso Λ (geometricSmoothModel f j kbar).j
    (geometricSmoothModelProj f j kbar) (pullback.fst f (specAlgebraMap k kbar)) j.immersion
    (geometricSmoothModel_j_comp_proj f j kbar).symm
    ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)
    (inverseImageExtensionByZeroIso Λ j.immersion F)

/-- **The restriction to `X_k̄` of the twist of `q^{-1}(j_! F)` along `s̃_σ` is the twist of
`F|_{X_k̄}` along `s_σ = id_X × Spec σ`** (ii.4b): `j_C^{-1}` of the twist, followed by
`j_C^{-1} (s̃_σ)_* ≅ (s_σ)_* j_C^{-1}` (`Stacks.EtaleCohomology.restrictionIntegralDirectImageIso`
on the cartesian square of `Stacks.EtaleCohomology.isPullback_geometricSmoothModelGaloisAut_j`),
is the twist of `F|_{X_k̄}`, through
`Stacks.EtaleCohomology.geometricSmoothModelInverseImageRestrictionIso`. -/
public theorem geometricSmoothModelInverseImageRestrictionIso_selfMapTwist (σ : kbar ≃ₐ[k] kbar)
    (F : EtaleModules.{u, 0} Λ X) :
    (etaleModuleRestriction.{u, 0} Λ (geometricSmoothModel f j kbar).j).map
        ((selfMapTwist.{u, 0} Λ (geometricSmoothModelProj f j kbar)
          (geometricSmoothModelGaloisAut f j kbar σ)
          (geometricSmoothModelGaloisAut_comp_proj f j kbar σ)).app
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) ≫
      (restrictionIntegralDirectImageIso Λ (geometricSmoothModel f j kbar).j
        (geometricSmoothModel f j kbar).j (galoisBaseChange (Over.mk f) kbar σ)
        (geometricSmoothModelGaloisAut f j kbar σ)
        (isPullback_geometricSmoothModelGaloisAut_j f j kbar σ)).inv.app
          ((etaleModuleInverseImage.{u, 0} Λ (geometricSmoothModelProj f j kbar)).obj
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) ≫
      (etaleModuleDirectImage.{u, 0} Λ (X := pullback f (specAlgebraMap k kbar))
          (Y := pullback f (specAlgebraMap k kbar)) (galoisBaseChange (Over.mk f) kbar σ)).map
        (geometricSmoothModelInverseImageRestrictionIso f j kbar Λ F).hom =
    (geometricSmoothModelInverseImageRestrictionIso f j kbar Λ F).hom ≫
      (selfMapTwist.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))
        (galoisBaseChange (Over.mk f) kbar σ) (galoisBaseChange_comp_fst (Over.mk f) kbar σ)).app
          F :=
  selfMapTwistOpenRestrictionIso_selfMapTwist Λ (geometricSmoothModel f j kbar).j
    (geometricSmoothModelProj f j kbar) (pullback.fst f (specAlgebraMap k kbar)) j.immersion
    (geometricSmoothModel_j_comp_proj f j kbar).symm
    ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)
    (inverseImageExtensionByZeroIso Λ j.immersion F) (geometricSmoothModelGaloisAut f j kbar σ)
    (geometricSmoothModelGaloisAut_comp_proj f j kbar σ) (galoisBaseChange (Over.mk f) kbar σ)
    (galoisBaseChange_comp_fst (Over.mk f) kbar σ)
    (isPullback_geometricSmoothModelGaloisAut_j f j kbar σ)

end Stacks.EtaleCohomology

end
