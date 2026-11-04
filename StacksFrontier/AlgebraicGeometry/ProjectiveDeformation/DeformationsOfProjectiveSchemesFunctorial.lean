module

public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.DeformationsOfProjectiveSchemes
public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.FunctorialityTwist
import StacksCore.Tactic.StacksAttribute

/-!
# Deformations of projective schemes, with functoriality

[Stacks, Tag 0D4F] in full: `exists_uniform_degreeBound_canonical` (clauses (1)–(5) with the
canonical `𝒜'`, `r'` and `θ'`, and the base change of `𝒜'` along a morphism of deformations an
isomorphism) together with the compatibility of `r'` and `θ'` with every morphism of admissible
deformations (`canonicalProjHom_comp_projBaseChangeHom`, `canonicalTwistMap_comp_polarization`):
the construction of `𝒜'`, `r'` and `θ'` is functorial in the data `(X', S', i, i', f', ℒ')`.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveDeformation.exists_uniform_degreeBound_functorial`.

## References

* [Stacks Project, Tag 0D4F](https://stacks.math.columbia.edu/tag/0D4F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Ample
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.ChartTransRelativeProj

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveDeformation

open PolarizedFamily PolarizedFamily.AdmissibleDeformation

-- The derived category of `exists_uniform_degreeBound_canonical`, as in the file stating it.
attribute [local instance 10000] HasDerivedCategory.standard

/-- **Deformations of projective schemes** ([Stacks, Tag 0D4F]).  Let `(f : X ⟶ S, ℒ)` be a
polarized family: `f` proper, flat and of finite presentation, `S` quasi-compact, `ℒ` invertible
and ample relative to `f`.  There is a positive `d₀` such that for every admissible deformation
`(X', S', i, i', f', ℒ')` of it — a cartesian square over a thickening `S ⊂ S'` with `f'` proper,
flat and of finite presentation, and `ℒ'` invertible with `ℒ ≅ (i')^* ℒ'`:

1. `R^p (f')_* (ℒ')^{⊗ d} = 0` for all `p > 0` and `d ≥ d₀`;
2. `𝒜'_d = (f')_* (ℒ')^{⊗ d}` is finite locally free for `d ≥ d₀`;
3. `𝒜' = 𝒪_{S'} ⊕ ⨁_{d ≥ d₀} 𝒜'_d` (`truncatedSectionAlgebra`) is a quasi-coherent graded
   `𝒪_{S'}`-algebra with these pieces, its comparison `𝒜' ⟶ ⨁_{d ≥ 0} 𝒜'_d`
   (`sectionAlgebraComparison`) is an isomorphism in every degree `≥ d₀`, and `𝒜'` is of finite
   presentation over every affine open of `S'`;
4. the canonical morphism `r' : X' ⟶ Proj_{S'}(𝒜')` (`canonicalProjHom`) is an isomorphism over
   `S'`;
5. the canonical map `θ' : (r')^* 𝒪_{Proj_{S'}(𝒜')}(1) ⟶ ℒ'` (`canonicalTwistMap`) is an
   isomorphism;

and the formation of each `𝒜'_d`, `d ≥ d₀`, commutes with arbitrary base change.

**Functoriality.** For every morphism `φ : D₁ ⟶ D₂` of admissible deformations (a cartesian
square `g' : X'₁ ⟶ X'₂` over `g : S'₁ ⟶ S'₂` compatible with the immersions of the family, with
polarization `g'^* ℒ'₂ ≅ ℒ'₁`):

* `𝒜'` is functorial: the homomorphism of graded algebras `g^* 𝒜'(D₂) ⟶ 𝒜'(D₁)` obtained by
  pulling sections back (`algebraPullbackHom`) is an isomorphism in every degree;
* `r'` is functorial: with `M : Proj_{S'₁}(𝒜'(D₁)) ⟶ Proj_{S'₂}(𝒜'(D₂))` the morphism it induces
  followed by the base change morphism of [Stacks, Tag 01O3] (`projBaseChangeHom`),
  `r'₁ ≫ M = g' ≫ r'₂`;
* `θ'` is functorial: `g'^* θ'₂` followed by the polarization equals, through
  `g'^* (r'₂)^* ≅ (r'₁ ≫ M)^* ≅ (r'₁)^* M^*`, the inverse image along `r'₁` of the map of Serre
  twists `M^* 𝒪(1) ⟶ 𝒪(1)` of [Stacks, Tags 01O3, 07ZJ] (`projBaseChangeTwistMap`) followed by
  `θ'₁`. -/
@[stacks 0D4F]
public theorem exists_uniform_degreeBound_functorial (P : PolarizedFamily.{u}) :
    ∃ (d₀ : ℕ) (hd₀ : 0 < d₀), (∀ D : P.AdmissibleDeformation,
      (∀ d : ℕ, d₀ ≤ d → ∀ p : ℤ, 0 < p →
          IsZero (((Scheme.Modules.pushforward D.f').rightDerivedPlus p).obj
            (tensorPowModule D.X' D.L' (d : ℤ)))) ∧
        (∀ d : ℕ, d₀ ≤ d →
          _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
            (R := D.S'.ringCatSheaf) (D.sectionPiece d)) ∧
        (D.IsTruncatedSectionAlgebraWithComparison d₀ (D.truncatedSectionAlgebra d₀ hd₀) ∧
          (∀ d : ℕ, d₀ ≤ d → IsIso ((D.sectionAlgebraComparison d₀ hd₀).app (d : ℤ))) ∧
          (∀ U : D.S'.Opens, IsAffineOpen U →
            RingHom.FinitePresentation ((D.truncatedSectionAlgebra d₀ hd₀).strHom U))) ∧
        (IsIso (D.canonicalProjHom d₀ hd₀) ∧
          D.canonicalProjHom d₀ hd₀ ≫ (relativeProj (D.truncatedSectionAlgebra d₀ hd₀)).toBase =
            D.f') ∧
        IsIso (D.canonicalTwistMap d₀ hd₀) ∧
        ∀ d : ℕ, d₀ ≤ d → ∀ (T Y : Scheme.{u}) (h : T ⟶ D.S') (fT : Y ⟶ T) (h' : Y ⟶ D.X')
          (hsq : IsPullback h' fT D.f' h),
          IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans hsq.w).app
            (tensorPowModule D.X' D.L' (d : ℤ)))) ∧
      ∀ (D₁ D₂ : P.AdmissibleDeformation) (φ : Hom D₁ D₂),
        ∃ hiso : ∀ n : ℤ, IsIso ((algebraPullbackHom φ d₀ hd₀).app n),
          D₁.canonicalProjHom d₀ hd₀ ≫ projBaseChangeHom φ d₀ hd₀ hiso =
            φ.total ≫ D₂.canonicalProjHom d₀ hd₀ ∧
          (Scheme.Modules.pullback φ.total).map (D₂.canonicalTwistMap d₀ hd₀) ≫
              φ.polarization.hom =
            (Scheme.Modules.pullbackComp φ.total (D₂.canonicalProjHom d₀ hd₀)).hom.app _ ≫
              (Scheme.Modules.pullbackCongr
                (canonicalProjHom_comp_projBaseChangeHom φ d₀ hd₀ hiso).symm).hom.app _ ≫
              (Scheme.Modules.pullbackComp (D₁.canonicalProjHom d₀ hd₀)
                (projBaseChangeHom φ d₀ hd₀ hiso)).inv.app _ ≫
              (Scheme.Modules.pullback (D₁.canonicalProjHom d₀ hd₀)).map
                (projBaseChangeTwistMap φ d₀ hd₀ hiso) ≫
              D₁.canonicalTwistMap d₀ hd₀ := by
  obtain ⟨d₀, hd₀, hD, hφ⟩ := exists_uniform_degreeBound_canonical P
  exact ⟨d₀, hd₀, hD, fun D₁ D₂ φ => ⟨hφ D₁ D₂ φ,
    canonicalProjHom_comp_projBaseChangeHom φ d₀ hd₀ (hφ D₁ D₂ φ),
    canonicalTwistMap_comp_polarization φ d₀ hd₀ (hφ D₁ D₂ φ)⟩⟩

end Stacks.AlgebraicGeometry.ProjectiveDeformation

end
