module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomFpqcDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.ReprFpqcFullness
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams

/-!
# Stacks 08K3, the two halves of the exactness together

`StacksFrontier/AlgebraicGeometry/Quot/RelativeHomFpqcDescent.lean` proves the gluing half of the
full-faithfulness clause of Stacks 04W8 in the shape the relative Hom functor of Stacks 08JT
consumes, as
`AlgebraicGeometry.Space.existsUnique_restrictPullbackHom_eq_of_isFpqcCovering`, and the two
halves of the descent statement of Stacks 08K3 separately.  This file puts the two halves
together as the exactness of the diagram the source displays, registers Stacks 08K3 at the
source's hypotheses, and names the gluing half after the predicate it proves.

## Main results

* `AlgebraicGeometry.Space.gluesModuleHomAlongFpqcCovering`: **the gluing half of
  Stacks 04W8** in the form of
  `AlgebraicGeometry.Space.GluesModuleHomAlongFpqcCovering`, with no hypothesis — the name of
  the predicate for the theorem that proves it.
* `AlgebraicGeometry.Space.restrictPullbackHom_eq_restrictForm`: the restriction of a
  homomorphism of inverse images is the restricted reading of
  `StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/FpqcChartFullness.lean`.
* `AlgebraicGeometry.Space.HomSituation.tripleRestrictionsAgree_iff_existsUnique_sourceHom`:
  **Stacks 08K3**, the exactness of
  `Hom(F, G)(T) → ∏_i Hom(F_i, G_i)(T) ⇉ ∏_{ijk} Hom(F_{ijk}, G_{ijk})(T)`.

## References

* [Stacks Project, Tag 08K3](https://stacks.math.columbia.edu/tag/08K3)
* [Stacks Project, Tag 08JT](https://stacks.math.columbia.edu/tag/08JT)
* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
* [Stacks Project, Tag 03Y9](https://stacks.math.columbia.edu/tag/03Y9)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The gluing half of the full-faithfulness clause of Stacks 04W8**, under the name of the
predicate it proves: a family of homomorphisms of the inverse images of two quasi-coherent
modules along an fpqc covering, agreeing on the overlaps, comes from a unique homomorphism. -/
alias gluesModuleHomAlongFpqcCovering := existsUnique_restrictPullbackHom_eq_of_isFpqcCovering

/-- The restriction of a homomorphism of inverse images along a further morphism is its
restricted reading through the comparison of Stacks 03LU. -/
alias restrictPullbackHom_eq_restrictForm := restrictPullbackHom_eq_restrictForm_of_comp_eq

namespace HomSituation

variable (s : HomSituation B S hS) {I : Type v} {Xi : I → AlgebraicSpaces B S hS}
  (a : ∀ i, Xi i ⟶ s.X) (T : s.SchemesOver) {K : I → I → Type v}
  {Xijk : ∀ i j, K i j → AlgebraicSpaces B S hS}
  (b : ∀ i j (k : K i j), Xijk i j k ⟶ overlapSpace a i j)

/-- **Stacks 08K3.**  In Situation 08JT let `{X_i ⟶ X}` be an fppf covering and for all `i`, `j`
let `{X_{ijk} ⟶ X_i ×_X X_j}` be an fppf covering, and write `F_i`, `G_i`, `F_{ijk}`,
`G_{ijk}` for the pullbacks of `F` and `G`.  For every scheme `T` over the base, the diagram
`Hom(F, G)(T) ⟶ ∏_i Hom(F_i, G_i)(T) ⇉ ∏_{ijk} Hom(F_{ijk}, G_{ijk})(T)` presents the first
arrow as the equalizer of the other two: a family `(α i)` of homomorphisms over the base
changes `X_{i, T}` is taken to the same element by the two parallel arrows exactly when it is
the image of a unique `β : F_T ⟶ G_T`.

The backward direction says that the first arrow lands in the equalizer; together with it the
forward direction says that the first arrow is injective and its image is the equalizer.

This is the proof of the source.  The base changes `{X_{i, T} ⟶ X_T}` and
`{X_{ijk, T} ⟶ X_{i, T} ×_{X_T} X_{j, T}}` are fppf, hence fpqc, coverings (Stacks 03Y9);
Stacks 04W8 applied to the second, in the form of its faithfulness half, reduces the condition
to the overlaps themselves, and applied to the first, in the form
`AlgebraicGeometry.Space.gluesModuleHomAlongFpqcCovering`, produces the unique global
homomorphism.  The base-changed modules `F_T`, `G_T` are quasi-coherent by Stacks 03GA. -/
@[stacks 08K3]
theorem tripleRestrictionsAgree_iff_existsUnique_sourceHom
    (ha : IsFppfCovering B S hS (fun i ↦ (Xi i).1) fun i ↦ (a i).hom)
    (hb : ∀ i j, IsFppfCovering B S hS (fun k ↦ (Xijk i j k).1) fun k ↦ (b i j k).hom)
    (α : ∀ i, (modulePullback B S hS (s.memberToSource a T i)).obj s.F ⟶
      (modulePullback B S hS (s.memberToSource a T i)).obj s.G) :
    s.TripleRestrictionsAgree a T b α ↔
      ∃! β : s.homAt T, ∀ i, restrictPullbackHom (s.memberInclusion a T i)
        (s.memberInclusion_comp a T i) (s.toModuleHom β) = α i := by
  refine ⟨fun hα ↦ ?_, fun ⟨β, hβ, _⟩ ↦ ?_⟩
  · exact s.existsUnique_sourceHom_of_tripleRestrictionsAgree a T b
      (QuasiCoherentDescent.reprFpqcHomInjective.{u, v} B S hS) ha hb α hα
  · have hα : α = fun i ↦ restrictPullbackHom (s.memberInclusion a T i)
        (s.memberInclusion_comp a T i) (s.toModuleHom β) := funext fun i ↦ (hβ i).symm
    subst hα
    exact s.tripleRestrictionsAgree_restrict a T b β

end HomSituation

end AlgebraicGeometry.Space

end
