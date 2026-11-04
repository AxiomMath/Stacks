module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationResolutionTerms
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HomComplexAcyclicColumns

/-!
# The Hom complex out of the resolution of Stacks 0D78 into an acyclic complex

Let `S` be a simplicial-site situation, `a` an augmentation of `S` towards a site `(D, K)` and
`G` an abelian sheaf on `(D, K)`. Stacks 0D78 resolves `a⁻¹G` on the total site by the complex
`… ⟶ g_{1!}(a_1⁻¹G) ⟶ g_{0!}(a_0⁻¹G)`. This module computes the Hom complex out of that
resolution, placed in non-positive degrees, into a complex `W` of abelian sheaves on the total
site: by adjunction its `p`-th column is the Hom complex `Hom(a_p⁻¹G, W^•|_{C_p})` on the
component site of simplicial degree `p`, so if `W` is acyclic and restricts to a K-injective
complex on every component, the whole Hom complex is acyclic.

The complex `W` is *not* assumed K-injective on the total site, which is the point: in the
application `W` is the cone of a K-injective resolution of `a⁻¹I`, and its restrictions are
K-injective because restriction preserves K-injectivity (Stacks 09WH) while `W` itself need not
be.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.Augmentation.resolutionColumnIso`: the `p`-th column of
  the double complex `Hom(P_p, W^q)` of the resolution of Stacks 0D78 is
  `Hom(a_p⁻¹G, W^•|_{C_p})`.

## Main results

* `CategoryTheory.SimplicialSiteSituation.Augmentation.acyclic_homComplex_resolution`: the Hom
  complex out of the resolution of Stacks 0D78 into an acyclic complex with K-injective
  restrictions is acyclic.

## Implementation notes

The column identification is `CochainComplex.coyonedaComplexAdjIso` at the adjunction
`g_{p!} ⊣ g_p^{-1}`, preceded by the degreewise identification
`(resolution S D K a G).degreeIso` of the terms of the resolution with
`g_{p!}(a_p⁻¹G)`; the pattern is the one of
`CategoryTheory.SimplicialSiteSituation.integerResolutionColumnIso` for the integral resolution
of Stacks 09WI.

Acyclicity of the restriction of `W` is `HomologicalComplex.Acyclic.map`, restriction to a
component being exact by Stacks 09WG (7).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation.Augmentation

attribute [local instance] HasDerivedCategory.standard

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K) (G : Sheaf K Ab.{u})

/-- **The `p`-th column of the double complex `Hom(P_p, W^q)` of the resolution of Stacks 0D78 is
the Hom complex `Hom(a_p⁻¹G, W^•|_{C_p})`** on the component site of simplicial degree `p`. -/
def resolutionColumnIso (p : ℕ) (W : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ) :
    CochainComplex.coyonedaComplex
        (((AlgebraicTopology.alternatingFaceMapComplex (Sheaf S.totalTopology Ab.{u})).obj
          (resolution S D K a G).simplicial).X p) W ≅
      CochainComplex.coyonedaComplex ((componentInverseImageAb S D K a ⦋p⦌).obj G)
        (((restrictAb S ⦋p⦌).mapHomologicalComplex (ComplexShape.up ℤ)).obj W) := by
  refine ?_ ≪≫ CochainComplex.coyonedaComplexAdjIso (componentAdjunctionAb S ⦋p⦌)
    ((componentInverseImageAb S D K a ⦋p⦌).obj G) W
  exact ((NatIso.mapHomologicalComplex
    (preadditiveCoyoneda.mapIso ((resolution S D K a G).degreeIso p).op)
    (ComplexShape.up ℤ)).app W).symm

/-- **The Hom complex out of the resolution of Stacks 0D78 into an acyclic complex whose
restrictions to the components are K-injective is acyclic.** -/
theorem acyclic_homComplex_resolution
    (W : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ) (hW : W.Acyclic)
    (hWp : ∀ p : SimplexCategory, CochainComplex.IsKInjective
      (((restrictAb S p).mapHomologicalComplex (ComplexShape.up ℤ)).obj W)) :
    (CochainComplex.HomComplex
      (((AlgebraicTopology.alternatingFaceMapComplex (Sheaf S.totalTopology Ab.{u})).obj
        (resolution S D K a G).simplicial).extend ComplexShape.embeddingDownNat) W).Acyclic := by
  refine CochainComplex.acyclic_homComplex_extend_of_acyclic_coyonedaComplex _ W fun p i => ?_
  have := hWp ⦋p⦌
  exact (CochainComplex.acyclic_coyonedaComplex_of_isKInjective_of_acyclic
    ((componentInverseImageAb S D K a ⦋p⦌).obj G) _
    (HomologicalComplex.Acyclic.map (restrictAb S ⦋p⦌) hW) i).of_iso
    (resolutionColumnIso S D K a G p W).symm

end CategoryTheory.SimplicialSiteSituation.Augmentation

end
