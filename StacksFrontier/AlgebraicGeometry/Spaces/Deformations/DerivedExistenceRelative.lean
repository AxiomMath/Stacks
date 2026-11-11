module

public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDefinition

/-!
# The data of the generalized derived existence theorem, with no flatness

Stacks 0DIR proposes a generalization of the derived Grothendieck existence theorem 0DIQ: an
inverse system of rings `(Aₙ)` with surjective transitions whose kernels are locally nilpotent,
`A = lim Aₙ`, an algebraic space `X` separated and of finite presentation over `A`,
`Xₙ = X ×_{Spec A} Spec Aₙ`, objects `Kₙ ∈ D(𝒪_{Xₙ})` pseudo-coherent relative to `Aₙ`, each
supported on a closed subset of `|Xₙ|` proper over `Aₙ`, and isomorphisms `Liₙ^* Kₙ₊₁ ≅ Kₙ`. The
proposed outcome is a `K ∈ D(𝒪_X)` pseudo-coherent relative to `A` with `Ljₙ^* K ≅ Kₙ`
compatibly.

This file records exactly these data, with no flatness of `X` over `A`. For `X` flat over `A` the
conclusion is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/Deformations/DerivedExistenceSupported.lean`; without
flatness it fails (`Stacks.Examples.DerivedExistenceNotFlat`).

## Main definitions

* `AlgebraicGeometry.Space.RelativeDerivedExistenceSystem`: the data.

## Implementation notes

`Liₙ^*` is the derived pullback `AlgebraicGeometry.Space.transitionDerivedPullback` along the
transition morphism `Xₙ ⟶ Xₙ₊₁` of the underived fibre products. Relative pseudo-coherence is
`AlgebraicGeometry.Space.IsRelativelyPseudoCoherent` (Stacks 0CSY) for the projection
`Xₙ ⟶ Spec Aₙ`, which asks the `Kₙ` to lie in `D_QCoh`; the field `quasicoherent` records that.

## References

* [Stacks Project, Tag 0DIR](https://stacks.math.columbia.edu/tag/0DIR)
* [Stacks Project, Tag 0DIQ](https://stacks.math.columbia.edu/tag/0DIQ)
* [Stacks Project, Tag 0CSY](https://stacks.math.columbia.edu/tag/0CSY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- **The data of the generalized derived existence theorem proposed in Stacks 0DIR**, with no
flatness: an inverse system of rings `(Aₙ)` with surjective transitions whose kernels are locally
nilpotent, an algebraic space `X` separated and of finite presentation over `A = lim Aₙ`, objects
`Kₙ ∈ D_QCoh(𝒪_{Xₙ})` pseudo-coherent relative to `Spec Aₙ`, each supported on a closed subset of
`|Xₙ|` proper over `Spec Aₙ`, and maps `Liₙ^* Kₙ₊₁ ⟶ Kₙ` that are isomorphisms. -/
structure RelativeDerivedExistenceSystem where
  /-- The inverse system of rings `(Aₙ)`. -/
  system : ℕᵒᵖ ⥤ CommRingCat.{u}
  /-- Its consecutive transition maps are surjective. -/
  transition_surjective (n : ℕ) :
    Function.Surjective (system.map (homOfLE (Nat.le_succ n)).op).hom
  /-- The kernels of those transition maps are locally nilpotent. -/
  transition_locallyNilpotent (n : ℕ) :
    (RingHom.ker (system.map (homOfLE (Nat.le_succ n)).op).hom).LocallyNilpotent
  /-- The big fppf site in which the algebraic spaces are taken. -/
  B : BigFppfSite.{u}
  /-- The inverse-limit base `Spec A` belongs to the site. -/
  containsLimitBase : B.Contains (limitBase system)
  /-- Every affine base `Spec Aₙ` belongs to the site. -/
  containsBaseAt (n : ℕ) : B.Contains (baseAt system n)
  /-- The algebraic space `X` over `Spec A`. -/
  X : Over (schemeSpace (limitBaseObject system B containsLimitBase))
  /-- `X` is separated over `Spec A`. -/
  separated : IsSeparated B (limitBase system) containsLimitBase X.hom.hom
  /-- `X` is of finite presentation over `Spec A`. -/
  finitePresentation :
    IsFinitePresentation B (limitBase system) containsLimitBase X.hom.hom
  /-- The object `Kₙ` of `D(𝒪_{Xₙ})`. -/
  K (n : ℕ) : derivedCategoryAt system B containsLimitBase containsBaseAt X n
  /-- Each `Kₙ` lies in `D_QCoh(𝒪_{Xₙ})`. -/
  quasicoherent (n : ℕ) :
    QcohDerived B (limitBase system) containsLimitBase
      (spaceAt system B containsLimitBase containsBaseAt X n) (K n)
  /-- Each `Kₙ` is pseudo-coherent relative to `Spec Aₙ`. -/
  relativelyPseudoCoherent (n : ℕ) :
    IsRelativelyPseudoCoherent B (limitBase system) containsLimitBase
      (spaceAt system B containsLimitBase containsBaseAt X n).1
      (spaceAt system B containsLimitBase containsBaseAt X n).2
      (spaceBaseProjection system B containsLimitBase containsBaseAt X n).hom
      (isLocallyOfFiniteType_spaceBaseProjection system B containsLimitBase containsBaseAt X
        (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B (limitBase system)
          containsLimitBase finitePresentation.1) n)
      ⟨K n, quasicoherent n⟩
  /-- The closed subset `Zₙ ⊆ |Xₙ|` supporting `Kₙ`. -/
  support (n : ℕ) :
    Set (points B (limitBase system) containsLimitBase
      (spaceAt system B containsLimitBase containsBaseAt X n).1)
  /-- `Zₙ` is closed. -/
  isClosed_support (n : ℕ) : IsClosed (support n)
  /-- `Zₙ` is proper over `Spec Aₙ`. -/
  isProperOver_support (n : ℕ) :
    IsProperOver B (limitBase system) containsLimitBase
      (spaceAt system B containsLimitBase containsBaseAt X n).2
      (schemeSpace (baseObjectAt system B containsLimitBase containsBaseAt n)).2
      (spaceBaseProjection system B containsLimitBase containsBaseAt X n).hom
      (isLocallyOfFiniteType_spaceBaseProjection system B containsLimitBase containsBaseAt X
        (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B (limitBase system)
          containsLimitBase finitePresentation.1) n)
      (support n) (isClosed_support n)
  /-- `Kₙ` is supported on `Zₙ`. -/
  supported (n : ℕ) :
    CohomologySupportedOn B (limitBase system) containsLimitBase
      (spaceAt system B containsLimitBase containsBaseAt X n).1
      (spaceAt system B containsLimitBase containsBaseAt X n).2 (support n) (K n)
  /-- The comparison map `Liₙ^* Kₙ₊₁ ⟶ Kₙ`, the adjoint of the map `Kₙ₊₁ ⟶ Riₙ,* Kₙ`. -/
  φ (n : ℕ) :
    (transitionDerivedPullback system B containsLimitBase containsBaseAt X n).obj (K (n + 1)) ⟶
      K n
  /-- The comparison map is an isomorphism `Kₙ₊₁ ⊗^L 𝒪_{Xₙ} ≅ Kₙ`. -/
  φ_isIso (n : ℕ) : IsIso (φ n)

end AlgebraicGeometry.Space

end
