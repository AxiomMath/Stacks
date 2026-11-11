module

public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.RestrictedIdealTensor
public import StacksFrontier.AlgebraicGeometry.SheafPicardGroup.Basic
public import StacksFrontier.AlgebraicGeometry.Surfaces.NegativeCurveFormalNeighborhoodGenusOne

/-!
# The powers of the conormal sheaf are the tensor powers of the conormal sheaf

Let `D` be an effective Cartier divisor on a scheme `X`, with subscheme `C`. The restrictions
`𝒪_X(-D ^ (n + 1))|_C` are the tensor powers of the conormal sheaf `L = 𝒪_X(-D)|_C`, up to
isomorphism: `i^*ℐ_I ⊗ i^*ℐ_J ≅ i^*ℐ_{I · J}`
(`Stacks.Divisors.restrictedIdealTensorMulIso`). Read in the monoid of isomorphism classes of
`𝒪_C`-modules (`Stacks.SheafPicardGroup.ClassMonoid`), the class of `𝒪_X(-D ^ (n + 1))|_C` is the
`(n + 1)`-st power of the class of `L`.

Consequently an isomorphism `L ≅ 𝒪_C(p)` alone produces the whole family
`𝒪_X(-D ^ (n + 1))|_C ≅ 𝒪_C(p) ^⊗ (n + 1)` that
`AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodRing_of_genusOne` consumes, and so
`AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodRing_of_genusOne_of_iso` takes only
that one isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory TopologicalSpace Stacks.Divisors
open AlgebraicGeometry.GenusOne
open Stacks.TensorPowers (natTensorPow)

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]

omit [IsEffectiveCartierDivisor D] in
/-- The class of a restricted product ideal sheaf is the product of the classes:
`i^*ℐ_I ⊗ i^*ℐ_J ≅ i^*ℐ_{I · J}` (`Stacks.Divisors.restrictedIdealTensorMulIso`). -/
public theorem mk_pullback_negativeTwist_mul (I J : X.IdealSheafData)
    [IsEffectiveCartierDivisor J] :
    Stacks.SheafPicardGroup.mk D.subscheme.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf D.subscheme)
        ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (I * J))) =
      Stacks.SheafPicardGroup.mk D.subscheme.presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf D.subscheme)
          ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist I)) *
        Stacks.SheafPicardGroup.mk D.subscheme.presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf D.subscheme)
          ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist J)) :=
  (Stacks.SheafPicardGroup.mk_eq_mk_of_iso _ _
    (restrictedIdealTensorMulIso D I J inferInstance)).symm.trans
    (Stacks.SheafPicardGroup.mk_tensorSheaf _ _ _ _)

omit [IsEffectiveCartierDivisor D] in
/-- Equal ideal sheaves have restricted ideal sheaves of the same class. -/
private theorem mk_pullback_negativeTwist_congr {I J : X.IdealSheafData} (h : I = J) :
    Stacks.SheafPicardGroup.mk D.subscheme.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf D.subscheme)
        ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist I)) =
      Stacks.SheafPicardGroup.mk D.subscheme.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf D.subscheme)
        ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist J)) := by
  subst h; rfl

/-- **The class of `𝒪_X(-D ^ (n + 1))|_C` is the `(n + 1)`-st power of the class of the conormal
sheaf**, in the monoid of isomorphism classes of `𝒪_C`-modules. -/
public theorem mk_pullback_negativeTwist_pow (n : ℕ) :
    Stacks.SheafPicardGroup.mk D.subscheme.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf D.subscheme)
        ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (n + 1)))) =
      Stacks.SheafPicardGroup.mk D.subscheme.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf D.subscheme)
        ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist D)) ^ (n + 1) := by
  induction n with
  | zero =>
    exact (mk_pullback_negativeTwist_congr D (pow_one D)).trans (pow_one _).symm
  | succ n ih =>
    exact ((mk_pullback_negativeTwist_congr D (pow_succ D (n + 1))).trans
      (mk_pullback_negativeTwist_mul D (D ^ (n + 1)) D)).trans
      ((congrArg (· * _) ih).trans (pow_succ _ (n + 1)).symm)

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-- **An isomorphism `L ≅ M` of the conormal sheaf with an `𝒪_C`-module gives isomorphisms
`𝒪_X(-D ^ (n + 1))|_C ≅ M ^⊗ (n + 1)` for every `n`.** -/
public theorem nonempty_pullback_negativeTwist_pow_iso (M : D.subscheme.Modules)
    (ψ : (Scheme.Modules.pullback D.subschemeι).obj (negativeTwist D) ≅ M) (n : ℕ) :
    Nonempty ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (n + 1))) ≅
      natTensorPow M (n + 1)) := by
  refine (Stacks.SheafPicardGroup.mk_eq_mk_iff D.subscheme.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf D.subscheme)).1 ?_
  refine (mk_pullback_negativeTwist_pow D n).trans ?_
  refine (congrArg (· ^ (n + 1)) (Stacks.SheafPicardGroup.mk_eq_mk_of_iso _ _ ψ)).trans ?_
  exact (Stacks.SheafPicardGroup.mk_natTensorPow _ _ M (n + 1)).symm

section GenusOne

variable {k : Type u} [Field k] {X : Scheme.{u}} {D : X.IdealSheafData}
  [IsEffectiveCartierDivisor D] [D.subscheme.Over (Spec (.of k))]
  [IsProper (D.subscheme ↘ Spec (.of k))] [SmoothOfRelativeDimension 1 (D.subscheme ↘ Spec (.of k))]

/-- **The formal neighbourhood of a curve of genus one with conormal bundle `𝒪(p)`, from the one
isomorphism `𝒪_X(-D)|_C ≅ 𝒪_C(p)`.** Let `D` be an effective Cartier divisor on a scheme `X`
whose subscheme `C` is a proper smooth curve of genus one over `k` with `H⁰(C, 𝒪_C) = k`, let `p`
be a `k`-point of `C`, and suppose the conormal sheaf of `C` is `𝒪_C(p)`. Then the ring
`lim Γ(Cₙ, 𝒪)` of compatible functions on the thickenings of `C` is a complete Noetherian local
domain of Krull dimension `2`. -/
public theorem formalNeighborhoodRing_of_genusOne_of_iso
    (h0 : Module.finrank k (structureSheafCohomology (D.subscheme ↘ Spec (.of k)) 0) = 1)
    (hg : genus (D.subscheme ↘ Spec (.of k)) = 1) (p : Spec (.of k) ⟶ D.subscheme)
    (hp : p ≫ (D.subscheme ↘ Spec (.of k)) = 𝟙 _)
    [IsEffectiveCartierDivisor (vanishingIdeal
      (⟨{point p}, isClosed_point (D.subscheme ↘ Spec (.of k)) p hp⟩ : Closeds D.subscheme) ^ 1)]
    (ψ : (Scheme.Modules.pullback D.subschemeι).obj (negativeTwist D) ≅
      pointDivisorSheaf p hp 1) :
    IsNoetherianCompleteLocalRing (formalNeighborhoodRing D) ∧
      ringKrullDim (formalNeighborhoodRing D) = 2 ∧ IsDomain (formalNeighborhoodRing D) :=
  formalNeighborhoodRing_of_genusOne h0 hg p hp
    (fun n => (nonempty_pullback_negativeTwist_pow_iso D _ ψ n).some)

end GenusOne

end AlgebraicGeometry.Scheme.IdealSheafData

end
