module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomFpqcDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.ReprFpqcFullness
public import StacksFrontier.AlgebraicGeometry.Quot.PicardDescent.Theta
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeIsomFpqcSheaf

/-!
# The full-faithfulness clause of Stacks 04W8 in the forms the relative Isom functor and the
coherent stack consume

`StacksFrontier/AlgebraicGeometry/Quot/RelativeHomFpqcDescent.lean` proves the sheaf property of the
relative Hom functor (Stacks 08JV) from
`AlgebraicGeometry.Space.existsUnique_restrictPullbackHom_eq_of_isFpqcCovering`, proved there,
and
`StacksFrontier/AlgebraicGeometry/Quot/RelativeIsom.lean` proves the sheaf property of the relative
Isom functor (Stacks 08K8) over `AlgebraicGeometry.Space.ReflectsIsoAlongFpqcCovering`.  Both are
the full-faithfulness clause of Stacks 04W8 read in a particular shape, and that clause is a
theorem:
`AlgebraicGeometry.Space.QuasiCoherentDescent.exists_modulePullback_map_eq_of_isFpqcCovering`
together with `AlgebraicGeometry.Space.QuasiCoherentDescent.reprFpqcHomSurjective` (fullness)
and `AlgebraicGeometry.Space.QuasiCoherentDescent.modulePullback_map_injective_of_isFpqcCovering`
(faithfulness).  This file discharges the hypothesis of Stacks 08K8, and records the gluing of
morphisms with uniqueness in the form of Stacks 04W3.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.existsUnique_modulePullback_map_eq`: **a family of
  morphisms of the inverse images of two quasi-coherent modules along an fpqc covering, satisfying
  the pairwise condition of Stacks 04W3, is the family of inverse images of a unique morphism.**
* `AlgebraicGeometry.Space.reflectsIsoAlongFpqcCovering`: the hypothesis of Stacks 08K8,
  discharged.

## References

* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
* [Stacks Project, Tag 08JV](https://stacks.math.columbia.edu/tag/08JV)
* [Stacks Project, Tag 08K8](https://stacks.math.columbia.edu/tag/08K8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuasiCoherentDescent

/-- **Fpqc descent of morphisms of quasi-coherent modules, with uniqueness.**  For an fpqc
covering `(c i : Z i ⟶ W)` of algebraic spaces and two quasi-coherent `𝒪_W`-modules, a family of
morphisms of their inverse images satisfying the pairwise condition of Stacks 04W3 is the family
of inverse images of a unique morphism of the modules.

Existence is the fullness half of Stacks 04W8 with its represented case discharged,
`…exists_modulePullback_map_eq_of_isFpqcCovering` and `…reprFpqcHomSurjective`; uniqueness is
the faithfulness half, `…modulePullback_map_injective_of_isFpqcCovering`. -/
theorem existsUnique_modulePullback_map_eq {I : Type v} {W : AlgebraicSpaces B S hS}
    (Zi : I → AlgebraicSpaces B S hS) (c : ∀ i, Zi i ⟶ W)
    (hc : IsFpqcCovering B S hS fun i => (c i).hom)
    {M N : Modules.{u, u} B S hS W.1 W.2} (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite)
    (w : ∀ i, (modulePullback B S hS (c i)).obj M ⟶ (modulePullback B S hS (c i)).obj N)
    (hw : IsPairwiseCompatible B S hS Zi c w) :
    ∃! φ : M ⟶ N, ∀ i, (modulePullback B S hS (c i)).map φ = w i := by
  obtain ⟨φ, hφ⟩ := exists_modulePullback_map_eq_of_isFpqcCovering B S hS
    (reprFpqcHomSurjective.{u, v} B S hS) Zi c hc w hw hM hN
  refine ⟨φ, hφ, fun ψ hψ => ?_⟩
  exact modulePullback_map_injective_of_isFpqcCovering B S hS
    (reprFpqcHomInjective.{u, v} B S hS) Zi c hc ψ φ fun i => (hψ i).trans (hφ i).symm

/-- **The pairwise condition of Stacks 04W3 from the agreement of the restricted readings on the
pairwise fibre products.**  This is
`AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalComparison_naturality_of_restrictForm_eq`
at each pair of members, the common factorization being the composite through the first
projection. -/
theorem isPairwiseCompatible_of_restrictForm_eq {I : Type v} {W : AlgebraicSpaces B S hS}
    (Zi : I → AlgebraicSpaces B S hS) (c : ∀ i, Zi i ⟶ W)
    {M N : Modules.{u, u} B S hS W.1 W.2}
    (w : ∀ i, (modulePullback B S hS (c i)).obj M ⟶ (modulePullback B S hS (c i)).obj N)
    (hw : ∀ i j, restrictForm B S hS (pairFst B S hS Zi c i j) (c i)
        (pairFst B S hS Zi c i j ≫ c i) rfl (w i) =
      restrictForm B S hS (pairSnd B S hS Zi c i j) (c j)
        (pairFst B S hS Zi c i j ≫ c i) (pair_condition B S hS Zi c i j).symm (w j)) :
    IsPairwiseCompatible B S hS Zi c w := fun i j =>
  canonicalComparison_naturality_of_restrictForm_eq B S hS (pairFst B S hS Zi c i j)
    (pairSnd B S hS Zi c i j) (c i) (c j) (pairFst B S hS Zi c i j ≫ c i) rfl
    (pair_condition B S hS Zi c i j).symm (pair_condition B S hS Zi c i j) (w i) (w j) (hw i j)

end QuasiCoherentDescent

end AlgebraicGeometry.Space

end
