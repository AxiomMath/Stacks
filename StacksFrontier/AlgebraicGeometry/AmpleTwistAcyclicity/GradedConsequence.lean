module

public import StacksFrontier.AlgebraicGeometry.AmpleTwistAcyclicity.Basic
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.Basic

/-!
# Uniform vanishing of twisted cohomology of graded pieces

For `f : X ⟶ Spec A` proper over a Noetherian ring, `F` a quasi-coherent graded module of finite
type over a finitely generated graded `A`-algebra and `L` ample, there is a `d₀` with
`H^p(X, F_n ⊗ L^{⊗d}) = 0` for all `p > 0`, all `d ≥ d₀` and all graded degrees `n` at once.

## Main results

* `Stacks.AlgebraicGeometry.GradedProperCohomology.exists_isZero_pieceTwistCohomology'`: the
  uniform vanishing, given a base change `X'` over `Spec B` and the comparison `hcmp` of the
  vanishing on `X'` with that of the graded pieces on `X`.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 02O1](https://stacks.math.columbia.edu/tag/02O1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Ample Stacks.RelativeVeryAmple
open scoped AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.GradedProperCohomology

attribute [local instance] HasDerivedCategory.standard

variable {X : Scheme.{u}}
  {𝓑 : _root_.SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf}

/-- Let `A` be a Noetherian ring, `B` a finitely generated graded `A`-algebra, `f : X ⟶ Spec A`
proper, and `F` a quasi-coherent graded `𝓑`-module of finite type. For `L` an ample invertible
`𝒪_X`-module there is a `d₀` such that `H^p(X, F_n ⊗ L^{⊗d})` vanishes for every `p > 0`, every
`d ≥ d₀` and every graded degree `n`.

It takes as hypotheses a proper `f' : X' ⟶ Spec B` with an affine `π : X' ⟶ X` and a coherent
`F'` on `X'`, and the comparison `hcmp`: vanishing of `H^p(X', F' ⊗ π^*L^{⊗d})` implies vanishing
of `H^p(X, F_n ⊗ L^{⊗d})` for every `n`. -/
theorem exists_isZero_pieceTwistCohomology'
    (A : Type u) [CommRing A] [IsNoetherianRing A] {B : Type u} [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [_root_.GradedAlgebra 𝒜] [Algebra.FiniteType A B]
    (f : X ⟶ Spec (.of A)) [IsProper f]
    (F : _root_.SheafOfModules.GradedModule 𝓑)
    (hqc : ∀ n : ℤ, (pieceModule F n).IsQuasicoherent)
    (hft : Stacks.Coherent.IsFiniteTypeOnAffine F)
    (L : X.Modules) [IsInvertibleModule X L] (hL : IsAmple X L)
    {X' : Scheme.{u}} (f' : X' ⟶ Spec (.of B)) [IsProper f']
    (π : X' ⟶ X) [_root_.AlgebraicGeometry.IsAffineHom π]
    (F' : X'.Modules) [F'.IsCoherent]
    (hcmp : ∀ p d : ℕ,
      IsZero ((ModuleCat.restrictScalars f'.appTop.hom).obj
          (cohomologyOf X' p
            (tensorModules X' F'
              (tensorPowModule X' (Stacks.AmpleLocallyClosed.pullbackModule π L) (d : ℤ))))) →
        ∀ n : ℤ, IsZero (cohomologyOf X p (pieceTwist F L n (d : ℤ)))) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ p : ℕ, 0 < p → ∀ n : ℤ,
      IsZero (cohomologyOf X p (pieceTwist F L n (d : ℤ))) :=
  exists_isZero_pieceTwistCohomology A 𝒜 f F hqc hft L hL
    Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.vanishingOverAffineBase.{u} f' π F' hcmp

end Stacks.AlgebraicGeometry.GradedProperCohomology

end
