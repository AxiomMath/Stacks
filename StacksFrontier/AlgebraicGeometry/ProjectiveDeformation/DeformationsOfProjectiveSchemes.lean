module

public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.CanonicalIdentification
public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.Functoriality
public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.SectionAlgebraFinitePresentation
public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.TwistIdentification

/-!
# Deformations of projective schemes

[Stacks, Tag 0D4F]: let `f : X ⟶ S` be proper, flat and of finite presentation over a
quasi-compact base, and `ℒ` an invertible `𝒪_X`-module ample relative to `f`.  There is a `d₀`
such that for every cartesian square

```
X --i'--> X'
|f        |f'
v         v
S --i --> S'
```

with `S ⊂ S'` a thickening and `f'` proper, flat and of finite presentation, and every invertible
`𝒪_{X'}`-module `ℒ'` with `ℒ ≅ (i')^* ℒ'`:

1. `R^p (f')_* (ℒ')^{⊗ d} = 0` for all `p > 0` and `d ≥ d₀`;
2. `𝒜'_d = (f')_* (ℒ')^{⊗ d}` is finite locally free for `d ≥ d₀`;
3. `𝒜' = 𝒪_{S'} ⊕ ⨁_{d ≥ d₀} 𝒜'_d` is a quasi-coherent `𝒪_{S'}`-algebra of finite presentation;
4. there is an isomorphism `r' : X' ⟶ Proj_{S'}(𝒜')` over `S'`; and
5. `(r')^* 𝒪(1) ≅ ℒ'`.

The polarized family is `Stacks.AlgebraicGeometry.ProjectiveDeformation.PolarizedFamily` and the
data `(X', S', i, i', f', ℒ')` is a `PolarizedFamily.AdmissibleDeformation`; `d₀` depends on the
family only.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveDeformation.exists_uniform_degreeBound_of_deformations`.
* `Stacks.AlgebraicGeometry.ProjectiveDeformation.exists_uniform_degreeBound_canonical`.

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

-- The derived category of `UniformDegreeBound.lean`, whose results the proofs below use.
attribute [local instance 10000] HasDerivedCategory.standard

/-- **Deformations of projective schemes** ([Stacks, Tag 0D4F]).  Let `(f : X ⟶ S, ℒ)` be a
polarized family: `f` proper, flat and of finite presentation, `S` quasi-compact, `ℒ` invertible
and ample relative to `f`.  There is a positive `d₀` such that for every admissible deformation
`(X', S', i, i', f', ℒ')` of it — a cartesian square over a thickening `S ⊂ S'` with `f'` proper,
flat and of finite presentation, and `ℒ'` invertible with `ℒ ≅ (i')^* ℒ'`:

1. `R^p (f')_* (ℒ')^{⊗ d} = 0` for all `p > 0` and `d ≥ d₀`;
2. `𝒜'_d = (f')_* (ℒ')^{⊗ d}` is finite locally free for `d ≥ d₀`;
3. there is a quasi-coherent graded `𝒪_{S'}`-algebra `𝒜' = 𝒪_{S'} ⊕ ⨁_{d ≥ d₀} 𝒜'_d`, with its
   comparison into `⨁_{d ≥ 0} 𝒜'_d` (an isomorphism in degrees `≥ d₀`), of finite presentation
   over every affine open;
4. there is an isomorphism `r' : X' ⟶ Proj_{S'}(𝒜')` over `S'`; and
5. `r'` pulls `𝒪_{Proj_{S'}(𝒜')}(1)` back to `ℒ'`;

and the formation of each `𝒜'_d`, `d ≥ d₀`, commutes with arbitrary base change.

The isomorphisms of (4) and (5) are only asserted to exist here; the registered form, with the
canonical `r'` and `θ'` and their functoriality, is `exists_uniform_degreeBound_functorial`. -/
public theorem exists_uniform_degreeBound_of_deformations (P : PolarizedFamily.{u}) :
    ∃ d₀ : ℕ, 0 < d₀ ∧ ∀ D : P.AdmissibleDeformation,
      (∀ d : ℕ, d₀ ≤ d → ∀ p : ℤ, 0 < p →
          IsZero (((Scheme.Modules.pushforward D.f').rightDerivedPlus p).obj
            (tensorPowModule D.X' D.L' (d : ℤ)))) ∧
        (∀ d : ℕ, d₀ ≤ d →
          _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
            (R := D.S'.ringCatSheaf) (D.sectionPiece d)) ∧
        (∃ A : SheafGradedAlgebra D.S', D.IsTruncatedSectionAlgebraWithComparison d₀ A ∧
          (∀ U : D.S'.Opens, IsAffineOpen U → RingHom.FinitePresentation (A.strHom U)) ∧
          ∃ r : D.X' ⟶ (relativeProj A).scheme, IsIso r ∧
            r ≫ (relativeProj A).toBase = D.f' ∧
            ∀ hcoc : IsNestedCocycle A 1,
              Nonempty ((Scheme.Modules.pullback r).obj (gluedTwist A 1 hcoc) ≅ D.L')) ∧
        ∀ d : ℕ, d₀ ≤ d → ∀ (T Y : Scheme.{u}) (h : T ⟶ D.S') (fT : Y ⟶ T) (h' : Y ⟶ D.X')
          (hsq : IsPullback h' fT D.f' h),
          IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans hsq.w).app
            (tensorPowModule D.X' D.L' (d : ℤ))) := by
  obtain ⟨d₀, hd₀, hvan⟩ := exists_uniform_isZero_higherDirectImage P
  refine ⟨d₀, hd₀, fun D => ?_⟩
  have hflf : ∀ d : ℕ, d₀ ≤ d →
      _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        (R := D.S'.ringCatSheaf) (D.sectionPiece d) := fun d hd =>
    isFiniteLocallyFree_sectionPiece_of_isZero D d (hvan D d hd)
  have hA := D.isTruncatedSectionAlgebraWithComparison_truncatedSectionAlgebra d₀ hd₀
  obtain ⟨r, hr, hrf, htw⟩ := relativeProjTwistIdentification relativeAmpleTwistIdentification P D
    d₀ hd₀ D.isRelativelyAmple_L' _ hA
  exact ⟨hvan D, hflf,
    ⟨D.truncatedSectionAlgebra d₀ hd₀, hA,
      truncatedSectionAlgebraFinitePresentationOf P D d₀ hd₀ D.isRelativelyAmple_L' hflf,
      r, hr, hrf, htw⟩,
    fun d hd _ _ h fT h' hsq =>
      isIso_baseChange_sectionPiece_of_isZero D d (hvan D d hd) h fT h' hsq⟩

/-- **Deformations of projective schemes** ([Stacks, Tag 0D4F]), with the canonical `r'` and
`θ'`.  Let `(f : X ⟶ S, ℒ)` be a polarized family: `f` proper, flat and of finite presentation,
`S` quasi-compact, `ℒ` invertible and ample relative to `f`.  There is a positive `d₀` such that
for every admissible deformation `(X', S', i, i', f', ℒ')` of it — a cartesian square over a
thickening `S ⊂ S'` with `f'` proper, flat and of finite presentation, and `ℒ'` invertible with
`ℒ ≅ (i')^* ℒ'`:

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

**Functoriality.** For every morphism of admissible deformations `D₁ ⟶ D₂` (a cartesian square
`X'₁ ⟶ X'₂` over `g : S'₁ ⟶ S'₂` compatible with the immersions of the family, with
`g'^* ℒ'₂ ≅ ℒ'₁`), the homomorphism of graded algebras `g^* 𝒜'(D₂) ⟶ 𝒜'(D₁)` obtained by pulling
sections back (`algebraPullbackHom`) is an isomorphism in every degree.

The registered form, which adds the functoriality of `r'` and `θ'`, is
`exists_uniform_degreeBound_functorial`. -/
public theorem exists_uniform_degreeBound_canonical (P : PolarizedFamily.{u}) :
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
      ∀ (D₁ D₂ : P.AdmissibleDeformation) (φ : Hom D₁ D₂) (n : ℤ),
        IsIso ((algebraPullbackHom φ d₀ hd₀).app n) := by
  obtain ⟨d₀, hd₀, hD⟩ := exists_uniform_degreeBound_of_deformations P
  refine ⟨d₀, hd₀, fun D => ?_, fun D₁ D₂ φ n =>
    isIso_algebraPullbackHom_app φ d₀ hd₀ (hD D₂).1 n⟩
  obtain ⟨hvan, hflf, -, hbc⟩ := hD D
  exact ⟨hvan, hflf,
    ⟨D.isTruncatedSectionAlgebraWithComparison_truncatedSectionAlgebra d₀ hd₀,
      D.isIso_sectionAlgebraComparison_app d₀ hd₀,
      truncatedSectionAlgebraFinitePresentationOf P D d₀ hd₀ D.isRelativelyAmple_L' hflf⟩,
    ⟨inferInstance, D.canonicalProjHom_comp_toBase d₀ hd₀⟩, inferInstance, hbc⟩

end Stacks.AlgebraicGeometry.ProjectiveDeformation

end
