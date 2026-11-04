module

public import StacksFrontier.AlgebraicGeometry.FiniteMorphismProjective.ChartAlgebra
public import StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso
public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.CoefficientBaseChangeCartesian
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Comparison

/-!
# The comparison of the two models of projective space is natural in the coefficient ring

`StacksFrontier/AlgebraicGeometry/ProjModelStructureMap/CoefficientBaseChangeCartesian.lean` builds
`Stacks.ProjectiveCohomology.projModelIso`, the isomorphism between `Proj R[T₀, …, Tₙ]` and the
library's model `AlgebraicGeometry.projectiveSpaceOverRing n R`, for an arbitrary coefficient
ring. That file records the two components of the comparison — the structure morphism and the
projection to the integral model — but says nothing about how the comparison varies with the
coefficient ring. This file supplies that: for every ring homomorphism `f : R →+* S` the square

```
Proj S[T₀, …, Tₙ]  ---- projModelIso S ---->  ℙⁿ_S
       |                                        |
  projModelMap f                   projectiveSpaceOverRingMap f
       v                                        v
Proj R[T₀, …, Tₙ]  ---- projModelIso R ---->  ℙⁿ_R
```

commutes.

The proof is the universal property of the library's model, which is a pullback of the integral
model over the terminal scheme: two morphisms into it agree as soon as their two components agree.
On the structure-morphism component the square is
`Stacks.ProjectiveCohomology.projModelMap_comp_projModelToSpec` together with
`AlgebraicGeometry.projectiveSpaceOverMap_fst`; on the integral-model component it is the
functoriality of `Stacks.ProjectiveCohomology.projModelMap` together with
`AlgebraicGeometry.projectiveSpaceOverMap_snd`, the functoriality being
`AlgebraicGeometry.Proj.map_comp` and the fact that the integers are initial among rings.

## Main results

* `Stacks.ProjectiveCohomology.projModelMap_comp`: **functoriality of the morphism of polynomial
  models** induced by a ring homomorphism of coefficients.
* `Stacks.ProjectiveCohomology.projModelMap_comp_projModelIso_hom`: **the comparison is natural
  in the coefficient ring.**

## Implementation notes

`AlgebraicGeometry.Proj.map` takes the containment of irrelevant ideals as a second, proof-valued
argument whose type mentions the first. Rewriting the first argument underneath it is therefore a
dependent rewrite; `Stacks.ProjectiveCohomology.Proj_map_congr` does it once, by substituting the
equality of graded homomorphisms and appealing to proof irrelevance, so that no consumer has to
build a motive by hand.

## References

* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open HomogeneousIdeal Graded

universe v u

namespace Stacks.ProjectiveCohomology

/-- `AlgebraicGeometry.Proj.map` depends on its containment of irrelevant ideals only through
proof irrelevance, so equal graded ring homomorphisms induce equal morphisms. -/
theorem Proj_map_congr {A B σ τ : Type v} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (g₁ g₂ : 𝒜 →+*ᵍ ℬ) (h₁ : ℬ₊ ≤ 𝒜₊.map g₁) (h₂ : ℬ₊ ≤ 𝒜₊.map g₂) (h : g₁ = g₂) :
    AlgebraicGeometry.Proj.map g₁ h₁ = AlgebraicGeometry.Proj.map g₂ h₂ := by
  subst h
  rfl

attribute [local instance] MvPolynomial.gradedAlgebra

section Functoriality

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]

/-- `Stacks.ProjectiveCohomology.polyGradedMap` is functorial in the coefficient ring:
`MvPolynomial.map` of a composite is the composite of the `MvPolynomial.map`s. -/
theorem polyGradedMap_comp (σ : Type) (f : R →+* S) (g : S →+* T) :
    (polyGradedMap σ g).comp (polyGradedMap σ f) = polyGradedMap σ (g.comp f) :=
  GradedRingHom.ext fun p => MvPolynomial.map_map (σ := σ) f g p

/-- **Functoriality of the morphism of polynomial models.** -/
theorem projModelMap_comp (n : ℕ) (f : R →+* S) (g : S →+* T) :
    projModelMap n g ≫ projModelMap n f = projModelMap n (g.comp f) :=
  (AlgebraicGeometry.Proj.map_comp (polyGradedMap (Fin (n + 1)) f)
        (polyGradedMap (Fin (n + 1)) g) _ _).symm.trans
    (Proj_map_congr _ _ _ _ (polyGradedMap_comp R S T (Fin (n + 1)) f g))

/-- The integers are initial among commutative rings, so a ring homomorphism out of `R`
composed with the structure map of `R` over the integral model is the structure map of the
target. -/
theorem comp_fromULiftInt (f : R →+* S) : f.comp (fromULiftInt R) = fromULiftInt S :=
  RingHom.ext fun x => map_intCast f x.down

end Functoriality

section Natural

variable (R S : Type u) [CommRing R] [CommRing S]

/-- The projection of the polynomial model to the integral model is natural in the coefficient
ring. -/
theorem projModelMap_comp_projModelMap_fromULiftInt (n : ℕ) (f : R →+* S) :
    projModelMap n f ≫ projModelMap n (fromULiftInt R) = projModelMap n (fromULiftInt S) :=
  (projModelMap_comp (ULift.{u} ℤ) R S n (fromULiftInt R) f).trans
    (congrArg (projModelMap n) (comp_fromULiftInt R S f))

/-- **The comparison of the two models of projective `n`-space is natural in the coefficient
ring.** For every ring homomorphism `f : R →+* S` the comparison carries
`Stacks.ProjectiveCohomology.projModelMap` to
`AlgebraicGeometry.projectiveSpaceOverRingMap`.

This is what pairs the comparison with base change: `projModelIso` was built from the cartesian
square of `Stacks.ProjectiveCohomology.isPullback_projModelToSpec`, which says that the library's
model over `S` is the base change of the one over `R`, and this says that the comparison is
compatible with that base change. -/
theorem projModelMap_comp_projModelIso_hom (n : ℕ) (f : R →+* S) :
    projModelMap n f ≫ (projModelIso R n).hom =
      (projModelIso S n).hom ≫
        AlgebraicGeometry.projectiveSpaceOverRingMap n (CommRingCat.ofHom f) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, projModelIso_hom_structureMorphism,
      AlgebraicGeometry.projectiveSpaceOverRingMap,
      AlgebraicGeometry.projectiveSpaceOverMap_fst, ← Category.assoc,
      projModelIso_hom_structureMorphism]
    exact projModelMap_comp_projModelToSpec n f
  · rw [Category.assoc, Category.assoc, projModelIso_hom_toIntegralAtUniverse,
      AlgebraicGeometry.projectiveSpaceOverRingMap,
      AlgebraicGeometry.projectiveSpaceOverMap_snd, projModelIso_hom_toIntegralAtUniverse]
    exact projModelMap_comp_projModelMap_fromULiftInt R S n f

end Natural

/-! ### The coordinate-pinned comparison is the model comparison -/

section PolynomialComparison

open Stacks.AlgebraicGeometry.ProjPolyChart Stacks.AlgebraicGeometry.RelativeProj

variable (R S : Type u) [CommRing R] [CommRing S]

/-- The coefficient homomorphism of the coordinate-pinned comparison is the graded homomorphism
induced by the structure map of `R` over the integral model: both are `MvPolynomial.map` of the
unique ring homomorphism out of `ULift ℤ`. -/
theorem integralGradedHom_eq_polyGradedMap (n : ℕ) :
    integralGradedHom R n = polyGradedMap (Fin (n + 1)) (fromULiftInt R) :=
  GradedRingHom.ext fun _ => rfl

/-- The containment of irrelevant ideals for the comparison's coefficient homomorphism. -/
theorem irrelevant_le_map_integralGradedHom (n : ℕ) :
    (polyGrading R n)₊ ≤ (polyGrading (ULift.{u} ℤ) n)₊.map (integralGradedHom R n) :=
  (integralGradedHom_eq_polyGradedMap R n).symm ▸
    irrelevant_le_map_polyGradedMap (Fin (n + 1)) (fromULiftInt R)

/-- The structure morphism of the polynomial model used by the coordinate-pinned comparison is
the one used by the model comparison: the two spellings of the identification of `R` with the
degree-zero part of the total-degree grading agree. -/
theorem projToSpecCoeff_eq_projModelToSpec (n : ℕ) :
    projToSpecCoeff R n = projModelToSpec R n := by
  rw [projToSpecCoeff, projModelToSpec_eq, polyDegreeZeroHom_eq_ofHom_algebraMap,
    Stacks.FiniteMorphismProjective.projZeroRingHom'_comp_algebraMap]

/-- The morphism to the integral model used by the coordinate-pinned comparison is
`Stacks.ProjectiveCohomology.projModelMap` at the structure map of `R` over the integral model.
The comparison's morphism is the everywhere-defined induced morphism of Tag 01MY, which under
Mathlib's containment of irrelevant ideals is Mathlib's `AlgebraicGeometry.Proj.map`. -/
theorem coordinateProjMap_eq_projModelMap (n : ℕ) :
    coordinateProjMap R n (integralGradedHom R n)
        (mapDomain_integralGradedHom_eq_top R n) =
      projModelMap n (fromULiftInt R) :=
  (mapHomOfTop_eq_map (polyGrading (ULift.{u} ℤ) n) (polyGrading R n) (integralGradedHom R n)
        (irrelevant_le_map_integralGradedHom R n)
        (mapDomain_integralGradedHom_eq_top R n)).trans
    (Proj_map_congr _ _ _ _ (integralGradedHom_eq_polyGradedMap R n))

/-- **The coordinate-pinned comparison of the two models of projective `n`-space is the model
comparison.** Both are morphisms into the library's model, which is a pullback, and their two
components agree. -/
theorem projCompare_eq_projModelIso_hom (n : ℕ) :
    projCompare R n = (projModelIso R n).hom := by
  refine pullback.hom_ext ?_ ?_
  · rw [projCompare_fst, projModelIso_hom_structureMorphism, projToSpecCoeff_eq_projModelToSpec]
  · rw [projCompare_snd, projModelIso_hom_toIntegralAtUniverse,
      coordinateProjMap_eq_projModelMap]

/-- The inverse of the isomorphism bundled in
`Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison` is the model comparison. -/
theorem polynomialComparison_iso_inv (n : ℕ) :
    (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison R n).iso.inv =
      (projModelIso R n).hom :=
  projCompare_eq_projModelIso_hom R n

/-- **The coordinate-pinned comparison is natural in the coefficient ring.** -/
theorem projModelMap_comp_polynomialComparison_iso_inv (n : ℕ) (f : R →+* S) :
    projModelMap n f ≫
        (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison R n).iso.inv =
      (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison S n).iso.inv ≫
        AlgebraicGeometry.projectiveSpaceOverRingMap n (CommRingCat.ofHom f) := by
  rw [polynomialComparison_iso_inv, polynomialComparison_iso_inv]
  exact projModelMap_comp_projModelIso_hom R S n f

end PolynomialComparison

end Stacks.ProjectiveCohomology

end
