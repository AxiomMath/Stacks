module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplex
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectObjectCanonical

/-!
# Relative dualizing complexes at a genuine family of derived tensor products

The definition of a relative dualizing complex (Stacks 0E2T) reads `S`-perfectness (Stacks 0DI0)
against a family `Dten` of certified derived tensor products on the open subspaces of
`(X, f⁻¹𝒪_S)`. When the family is genuine — its underived tensor products are the tensor
products of sheaves of modules — `S`-perfectness is the condition of Stacks 0DI0 itself, so being
a relative dualizing complex does not depend on which genuine family is used: it is the condition
at the canonical family.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isRelativeDualizingComplex_iff_canonicalFamily`: at a genuine
  family, being a relative dualizing complex is being one at the canonical family.

## References

* [Stacks Project, Definition 48.28.1 (Tag 0E2T)](https://stacks.math.columbia.edu/tag/0E2T)
* [Stacks Project, Definition 36.35.1 (Tag 0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
-/

@[expose] public noncomputable section

open CategoryTheory StrictlyPerfect

universe d' u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S)
  [HasDerivedCategory.{d'}
    (OXMod.{u, u} (RingedSpace.inverseImage S.toRingedSpace f.base))]
  [∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
    HasDerivedCategory.{d'}
      (OXMod.{u, u} ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict
        U.isOpenEmbedding))]

/-- **A relative dualizing complex at a genuine family is one at the canonical family**, and
conversely: both conditions read `S`-perfectness as Stacks 0DI0. -/
theorem isRelativeDualizingComplex_iff_canonicalFamily [Flat f] [LocallyOfFinitePresentation f]
    (Dten : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{d', u}
        ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding))
    (hD : IsGenuineRelativeTensorFamily f Dten) (D : DiagonalOpen f)
    (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (ξ : D.diagonalObject ⟶ D.derivedPullbackProj K) :
    IsRelativeDualizingComplex f Dten D K ξ ↔
      IsRelativeDualizingComplex f
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily.{d', u}
          (RingedSpace.inverseImage S.toRingedSpace f.base)) D K ξ := by
  rw [isRelativeDualizingComplex_iff, isRelativeDualizingComplex_iff,
    isPerfectRelativeTo_iff_isRelativelyPerfect f Dten hD,
    isPerfectRelativeTo_canonicalFamily_iff]

end AlgebraicGeometry.Scheme.Hom

end
