module

public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceRelative
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceSupported

/-!
# The generalized derived existence theorem with relatively pseudo-coherent `Kₙ`

Stacks 0DIR asks the objects `Kₙ ∈ D(𝒪_{Xₙ})` to be pseudo-coherent relative to `Aₙ`, which is
how `AlgebraicGeometry.Space.RelativeDerivedExistenceSystem` records them, while
`AlgebraicGeometry.Space.SupportedDerivedExistenceSystem` asks them to be pseudo-coherent on
`Xₙ`. When `X` is flat over `A`, every `Xₙ = X ×_{Spec A} Spec Aₙ` is flat and of finite
presentation over `Spec Aₙ`, so the two conditions agree (Stacks 0DII). This file turns the data
of the remark, together with flatness of `X`, into a `SupportedDerivedExistenceSystem`, and
restates the existence theorem for the remark's data.

## Main definitions

* `AlgebraicGeometry.Space.RelativeDerivedExistenceSystem.toSupported`: the
  `SupportedDerivedExistenceSystem` of a `RelativeDerivedExistenceSystem` with `X` flat over `A`.

## Main results

* `AlgebraicGeometry.Space.RelativeDerivedExistenceSystem.isPseudoCoherentOn_K_of_isFlat`: for
  `X` flat over `A`, each `Kₙ` is pseudo-coherent on `Xₙ` (Stacks 0DII).
* `…exists_isRelativelyPseudoCoherent_stageDerivedPullback_iso_of_isFlat`, in the namespace
  `AlgebraicGeometry.Space.RelativeDerivedExistenceSystem`: the existence theorem for `Kₙ`
  pseudo-coherent relative to `Aₙ` and `X` flat over `A`.

## Implementation notes

The conclusions are stated with `D(𝒪_X)`, the derived pullbacks `Ljₙ^*` along `Xₙ ⟶ X` and the
composition isomorphisms `Ljₙ^* ≅ Liₙ^* Ljₙ₊₁^*` of `D.toSupported hflat`. These are built from
the rings, the site and the space `X` alone, which `toSupported` takes from `D` unchanged, so
they are the objects of the remark for the data `D`; the hypothesis `hflat` only names the
structure through which they are reached. The objects `Kₙ` and maps `φₙ` are `D`'s own.

## References

* [Stacks Project, Tag 0DIR](https://stacks.math.columbia.edu/tag/0DIR)
* [Stacks Project, Tag 0DII](https://stacks.math.columbia.edu/tag/0DII)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] pointTopology

namespace RelativeDerivedExistenceSystem

variable (D : RelativeDerivedExistenceSystem.{u})

/-- **Each `Kₙ` is pseudo-coherent on `Xₙ`** when `X` is flat over `A`: the projection
`Xₙ ⟶ Spec Aₙ` is then flat and of finite presentation, so pseudo-coherence relative to `Aₙ` is
pseudo-coherence on `Xₙ` (Stacks 0DII). -/
theorem isPseudoCoherentOn_K_of_isFlat
    (hflat : IsFlat D.B (limitBase D.system) D.containsLimitBase D.X.hom.hom) (n : ℕ) :
    IsPseudoCoherentOn D.system D.B D.containsLimitBase D.containsBaseAt D.X n (D.K n) :=
  (isRelativelyPseudoCoherent_iff_isPseudoCoherent D.B (limitBase D.system) D.containsLimitBase
    (spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
    (isFlat_spaceBaseProjection _ _ _ _ _ hflat n)
    (isFinitePresentation_spaceBaseProjection _ _ _ _ _ D.finitePresentation n).1
    ⟨D.K n, D.quasicoherent n⟩).1 (D.relativelyPseudoCoherent n)

/-- The `AlgebraicGeometry.Space.SupportedDerivedExistenceSystem` of the data of Stacks 0DIR with
`X` flat over `A`: the same rings, space, objects, supports and comparison maps, the
pseudo-coherence of each `Kₙ` on `Xₙ` coming from its pseudo-coherence relative to `Aₙ`
(`isPseudoCoherentOn_K_of_isFlat`). -/
def toSupported (hflat : IsFlat D.B (limitBase D.system) D.containsLimitBase D.X.hom.hom) :
    SupportedDerivedExistenceSystem.{u} where
  system := D.system
  transition_surjective := D.transition_surjective
  transition_locallyNilpotent := D.transition_locallyNilpotent
  B := D.B
  containsLimitBase := D.containsLimitBase
  containsBaseAt := D.containsBaseAt
  X := D.X
  separated := D.separated
  flat := hflat
  finitePresentation := D.finitePresentation
  K := D.K
  pseudoCoherent := D.isPseudoCoherentOn_K_of_isFlat hflat
  φ := D.φ
  φ_isIso := D.φ_isIso
  support := D.support
  isClosed_support := D.isClosed_support
  isProperOver_support := D.isProperOver_support
  supported := D.supported

/-- **The generalized derived existence theorem for the data of Stacks 0DIR, `X` flat over `A`.**
Let `(Aₙ)`, `X` separated and of finite presentation over `A = lim Aₙ`, and `Kₙ ∈ D_QCoh(𝒪_{Xₙ})`
pseudo-coherent relative to `Aₙ`, supported on closed subsets of `|Xₙ|` proper over `Aₙ`, with
isomorphisms `φₙ : Liₙ^* Kₙ₊₁ ≅ Kₙ`, be as in the remark, and let `X` be flat over `A`. Then there
is `K ∈ D_QCoh(𝒪_X)`, pseudo-coherent relative to `A`, with isomorphisms `ψₙ : Ljₙ^* K ≅ Kₙ` such
that `ψₙ = (Ljₙ^* ≅ Liₙ^* Ljₙ₊₁^*) ≫ Liₙ^* ψₙ₊₁ ≫ φₙ`. The source's further clause that `K` is
supported on a closed subset of `|X|` proper over `A` is false; see the module
`StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceSupported`. -/
theorem exists_isRelativelyPseudoCoherent_stageDerivedPullback_iso_of_isFlat
    (hflat : IsFlat D.B (limitBase D.system) D.containsLimitBase D.X.hom.hom) :
    ∃ (K : (D.toSupported hflat).limitDerivedCategory)
      (ψ : ∀ n : ℕ, ((D.toSupported hflat).stageDerivedPullback n).obj K ≅ D.K n)
      (hK : QcohDerived D.B (limitBase D.system) D.containsLimitBase D.X.left K),
      IsRelativelyPseudoCoherent D.B (limitBase D.system) D.containsLimitBase D.X.left.1
          D.X.left.2 D.X.hom.hom
          (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation D.B (limitBase D.system)
            D.containsLimitBase D.finitePresentation.1) ⟨K, hK⟩ ∧
        ∀ n : ℕ, (ψ n).hom = ((D.toSupported hflat).stageDerivedPullbackCompIso n).inv.app K ≫
          (transitionDerivedPullback D.system D.B D.containsLimitBase D.containsBaseAt D.X n).map
            (ψ (n + 1)).hom ≫ D.φ n :=
  (D.toSupported hflat).exists_isRelativelyPseudoCoherent_stageDerivedPullback_iso

end RelativeDerivedExistenceSystem

end AlgebraicGeometry.Space

end
