module

public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.ProjectiveLineEulerBound
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.FibreAmple

/-!
# A numerical criterion for non-projectivity

This is the last step of the non-projectivity half of Hironaka's example (the source of
[Stacks, Tag 08J1]), isolated from the geometry. Let `f : V ⟶ Y` be a morphism of schemes and
let `L` and `M` be closed subschemes of two fibres of `f` over `k`-points of `Y`, each isomorphic
over `k` to `ℙ¹_k`. If for *every* invertible module `H` on `V` the Euler characteristics of the
restrictions of `H` to `L` and to `M` add up to `2`, then `f` is not projective.

Indeed a projective `f` carries an invertible module `H` which is ample on every closed subscheme
of every fibre (`AlgebraicGeometry.IsProjective.exists_isAmple_pullback_of_isPullback`), and an
ample invertible module on a scheme isomorphic to `ℙ¹_k` has Euler characteristic at least `2`
(`AlgebraicGeometry.two_le_eulerSum_of_isAmple_of_iso_projectiveLine`), so the sum would be at
least `4`.

In Hironaka's example `L = L₀` lies in the fibre over `P` and `M = M₀'` in the fibre over `Q`,
and the relation `χ(H|L₀) + χ(H|M₀') = 2` is the Euler-characteristic form of the rational
equivalence `L₀ + M₀' ∼ 0` of the source: it comes from the constancy of `χ` in the four flat
families of curves over the two conics and from the nodal decomposition of the two special
fibres.

## Main results

* `Stacks.Examples.HironakaNotProjective.not_isProjective_of_eulerSum_add_eq_two`.

## References

* [Stacks Project, Tag 08J1](https://stacks.math.columbia.edu/tag/08J1)
* [Stacks Project, Tag 0B5X](https://stacks.math.columbia.edu/tag/0B5X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic (eulerSum)
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.Examples.HironakaNotProjective

/-- **A numerical obstruction to projectivity.** Let `L` and `M` be closed subschemes of the fibres
of `f` over two `k`-points, each isomorphic over `k` to `ℙ¹_k`. If the Euler characteristics of
the restrictions of every invertible module on `V` to `L` and to `M` add up to `2`, then `f` is
not projective: an invertible module ample on the fibres would have Euler characteristic at least
`2` on each of them. -/
theorem not_isProjective_of_eulerSum_add_eq_two {V Y : Scheme.{u}} (f : V ⟶ Y)
    (k : Type u) [Field k]
    {y₁ y₂ : Spec (.of k) ⟶ Y} {Z₁ Z₂ : Scheme.{u}} {q₁ : Z₁ ⟶ V} {q₂ : Z₂ ⟶ V}
    {g₁ : Z₁ ⟶ Spec (.of k)} {g₂ : Z₂ ⟶ Spec (.of k)}
    (h₁ : IsPullback q₁ g₁ f y₁) (h₂ : IsPullback q₂ g₂ f y₂)
    {L M : Scheme.{u}} (j₁ : L ⟶ Z₁) [IsClosedImmersion j₁] (j₂ : M ⟶ Z₂) [IsClosedImmersion j₂]
    (e₁ : L ≅ AlgebraicGeometry.Proj (polyGrading k 1))
    (he₁ : e₁.hom ≫ projToSpecCoeff k 1 = j₁ ≫ g₁)
    (e₂ : M ≅ AlgebraicGeometry.Proj (polyGrading k 1))
    (he₂ : e₂.hom ≫ projToSpecCoeff k 1 = j₂ ≫ g₂)
    (hrel : ∀ (H : V.Modules) [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 H],
      eulerSum k (j₁ ≫ g₁) ((Scheme.Modules.pullback j₁).obj ((Scheme.Modules.pullback q₁).obj H)) +
        eulerSum k (j₂ ≫ g₂)
          ((Scheme.Modules.pullback j₂).obj ((Scheme.Modules.pullback q₂).obj H)) = 2) :
    ¬ IsProjective f := by
  intro hf
  obtain ⟨H, hH, hamp⟩ := hf.exists_isAmple_pullback_of_isPullback
  obtain ⟨_, -, hL⟩ := hamp k y₁ q₁ g₁ h₁
  obtain ⟨_, -, hM⟩ := hamp k y₂ q₂ g₂ h₂
  have a₁ := two_le_eulerSum_of_isAmple_of_iso_projectiveLine (j₁ ≫ g₁) e₁ he₁ _ (hL j₁)
  have a₂ := two_le_eulerSum_of_isAmple_of_iso_projectiveLine (j₂ ≫ g₂) e₂ he₂ _ (hM j₂)
  have := hrel H
  omega

end Stacks.Examples.HironakaNotProjective

end
