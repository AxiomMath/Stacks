module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexUniqueness
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexRestrictLE

/-!
# Two relative dualizing complexes are uniquely isomorphic

Let `f : X ⟶ S` be flat and locally of finite presentation and let `W ⊆ X ×_S X` be an open
through which the relative diagonal factors as a closed immersion `Δ : X ⟶ W`. If `(K, ξ)` and
`(L, η)` are relative dualizing complexes for `f` (Stacks 0E2T), there is a unique isomorphism
`α : K ≅ L` sending `ξ` to `η`, i.e. with `ξ ≫ L pr₁^*α|_W = η` (Stacks 0E2W).

The proof is the source's. On an affine open `U` of `X` mapping into an affine open of `S`
there is an isomorphism `K|_U ≅ L|_U` by Stacks 0E2U and 0E2D; rescaled by a unit of
`Γ(U, 𝒪_X)` it sends `ξ|_U` to `η|_U`, and it is the only such isomorphism since the
automorphisms of `K|_U` are the units of `Γ(U, 𝒪_X)` (Stacks 0E2V). These isomorphisms agree on
smaller charts by uniqueness, so they glue by Stacks 0D66 (`Ext^i(K|_U, K|_U) = 0` for `i < 0`, by
Stacks 0E2V), and the glued isomorphism sends `ξ` to `η` because it does so locally.

## Main results

* `AlgebraicGeometry.Scheme.Hom.IsRelativeDualizingComplex.existsUnique_iso`: **Stacks 0E2W.**

## References

* [Stacks Project, Lemma 48.28.4 (Tag 0E2W)](https://stacks.math.columbia.edu/tag/0E2W)
-/

@[expose] public noncomputable section

open CategoryTheory StrictlyPerfect

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.Scheme.Hom.IsRelativeDualizingComplex

variable {X S : Scheme.{u}} {f : X ⟶ S} [Flat f] [LocallyOfFinitePresentation f]

/-- **Stacks 0E2W.** Let `f : X ⟶ S` be flat and locally of finite presentation, and let `W` be an
open of `X ×_S X` through which the relative diagonal factors as a closed immersion
`Δ : X ⟶ W`. If `(K, ξ)` and `(L, η)` are relative dualizing complexes on `X/S` relative to `W`
(Stacks 0E2T), then there is a unique isomorphism `α : K ≅ L` sending `ξ` to `η`, that is with
`ξ ≫ L pr₁^*α|_W = η`. -/
@[stacks 0E2W]
theorem existsUnique_iso {D : DiagonalOpen f}
    {K L : DerivedCategory (OXMod.{u, u} X.toRingedSpace)}
    {ξ : D.diagonalObject ⟶ D.derivedPullbackProj K}
    {η : D.diagonalObject ⟶ D.derivedPullbackProj L}
    (hK : IsRelativeDualizingComplex f
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace f.base)) D K ξ)
    (hL : IsRelativeDualizingComplex f
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace f.base)) D L η) :
    ∃! α : K ≅ L, ξ ≫ D.derivedPullbackProjMap α.hom = η :=
  existsUnique_iso_of_restrict hK hL (fun U M ζ => D.restrictXiProj U M ζ)
    (fun U _ => hK.restrictProj U) (fun U _ => hL.restrictProj U)
    (fun U _ _ ζ φ => D.restrictXiProj_comp_derivedPullbackProjMap U ζ φ)
    (fun {_ _} hVU {_ _} ζM ζN φ h =>
      D.restrictXiProj_comp_derivedPullbackProjMap_of_le hVU ζM ζN φ h)

end AlgebraicGeometry.Scheme.Hom.IsRelativeDualizingComplex

end
