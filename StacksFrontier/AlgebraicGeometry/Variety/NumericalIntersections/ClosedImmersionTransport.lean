/-
Copyright (c) 2026 Stacks Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.Pullback
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.ChowDegree
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward.ComponentDegree

/-!
# Intersection numbers along a closed immersion of an integral scheme

Let `X` be proper over a field `k`, `j : Y ⟶ X` a closed immersion with `Y` integral of dimension
`d`, and `𝓛_1, …, 𝓛_d` invertible `𝒪_X`-modules. The intersection number of the `𝓛_i` against the
closed subscheme cut out by `ker j` is the intersection number on `Y` itself of the pullbacks
`j^*𝓛_i`:

`(𝓛_1 ⋯ 𝓛_d · j(Y)) = (j^*𝓛_1 ⋯ j^*𝓛_d · Y)`.

This is [Stacks, Tag 0BET] for `j` with `Z = Y`: the scheme-theoretic image of `j` is the closed
subscheme `ker j`, onto which `j` is an isomorphism, so the degree is one.

## Main results

* `AlgebraicGeometry.intersectionNumber_subschemeι_ker_eq`: the formula above.
* `AlgebraicGeometry.intersectionNumber_pullback_of_isIso`: the same for an isomorphism `j`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k]

/-- The intersection number depends on the structure morphism only through its value. -/
theorem intersectionNumber_congr_structure {X Z : Scheme.{u}} {f f' : X ⟶ Spec (.of k)}
    [IsProper f] [IsProper f'] (hf : f = f') (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ)
    (hd : topologicalKrullDim Z ≤ (d : WithBot ℕ∞)) (L : Fin d → X.Modules)
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L q)] :
    intersectionNumber k f i d hd L = intersectionNumber k f' i d hd L := by
  subst hf
  rfl

/-- The intersection number depends on the closed immersion only through its value. -/
theorem intersectionNumber_congr_immersion {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProper f] {i i' : Z ⟶ X} [IsClosedImmersion i] [IsClosedImmersion i'] (h : i = i')
    (d : ℕ) (hd : topologicalKrullDim Z ≤ (d : WithBot ℕ∞)) (L : Fin d → X.Modules)
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L q)] :
    intersectionNumber k f i d hd L = intersectionNumber k f i' d hd L := by
  subst h
  rfl

/-- The degree of an isomorphism of integral schemes is one. -/
theorem degreeOver_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [IsIso f] [LocallyOfFiniteType f] [IsDominant f] : degreeOver f = 1 := by
  let : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).toAlgebra
  rw [degreeOver_eq_finrank f rfl, Stacks.Chow.finrank_functionField_eq_residueDegree f,
    residueDegree_eq_one_of_isIso_stalkMap f (genericPoint X)]

/-- **Intersection numbers along a closed immersion of an integral scheme are computed on the
source**: `(𝓛_1 ⋯ 𝓛_d · j(Y)) = (j^*𝓛_1 ⋯ j^*𝓛_d · Y)`. -/
theorem intersectionNumber_subschemeι_ker_eq {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProper f] (j : Y ⟶ X) [IsClosedImmersion j] [IsIntegral Y] (d : ℕ)
    (hY : topologicalKrullDim Y = (d : WithBot ℕ∞))
    (hker : topologicalKrullDim j.ker.subscheme ≤ (d : WithBot ℕ∞)) (L : Fin d → X.Modules)
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L q)] :
    haveI : IsProper (j ≫ f) := inferInstance
    intersectionNumber k (j ≫ f) (𝟙 Y) d hY.le (fun q => (Scheme.Modules.pullback j).obj (L q)) =
      intersectionNumber k f j.ker.subschemeι d hker L := by
  have hiso : IsIso j.toImage :=
    IsClosedImmersion.isIso_of_ker_eq j j.imageι j.toImage j.toImage_imageι
      (Scheme.IdealSheafData.ker_subschemeι j.ker).symm
  have hcomp : (𝟙 Y ≫ j) = j := Category.id_comp j
  have himdim : topologicalKrullDim (𝟙 Y ≫ j).image = (d : WithBot ℕ∞) := by
    rw [hcomp]
    exact (IsHomeomorph.topologicalKrullDim_eq j.toImage
      j.toImage.homeomorph.isHomeomorph).symm.trans hY
  have hpull := intersectionNumber_pullback_eq_degreeOver_mul k (j ≫ f) f j rfl (𝟙 Y) d hY L
    himdim
  have : IsIso (𝟙 Y ≫ j).toImage := by
    have key : ∀ g : Y ⟶ X, g = j → IsIso g.toImage := by
      rintro g rfl; exact hiso
    exact key _ hcomp
  have : IsIntegral (𝟙 Y ≫ j).image := Stacks.Chow.isIntegral_image (𝟙 Y ≫ j)
  have : IsDominant (𝟙 Y ≫ j).toImage := (isDominant_iff _).mpr
    (Function.Surjective.denseRange (𝟙 Y ≫ j).toImage.homeomorph.surjective)
  rw [degreeOver_of_isIso, Nat.cast_one, one_mul] at hpull
  rw [hpull]
  exact intersectionNumber_congr_ideal k f (by rw [hcomp]) d _ _ L

end AlgebraicGeometry
