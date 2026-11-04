module

public import StacksFrontier.CategoryTheory.Triangulated.RightAdjointCoproducts
public import StacksFrontier.CategoryTheory.Triangulated.CompactObjects
import all StacksFrontier.CategoryTheory.Triangulated.CompactObjects
import all StacksFrontier.CategoryTheory.Triangulated.RightAdjointCoproducts

/-!
# Right adjoints preserving a direct sum of a family

Let `L ⊣ R` be an adjunction with `L : D ⥤ C` additive, where `D` is pretriangulated, `C` is
preadditive and both have coproducts, and let `E` be a compact weak generator of `D`. If the images
under `L` of the shifts of `E` are compact against the direct sum of a family, then `R` preserves
the direct sum of that family.

This module extends `StacksFrontier.CategoryTheory.Triangulated.RightAdjointCoproducts`.

## Main results

* `CategoryTheory.Pretriangulated.preservesColimit_discrete_of_bijective_cofanMap`: `R` preserves
  the direct sum of a family against which the images of the shifts of `E` are compact.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Pretriangulated

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
  [HasShift C ℤ] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D] [HasCoproducts.{w} C] [HasCoproducts.{w} D]
  {L : D ⥤ C} {R : C ⥤ D} [L.Additive] [R.Additive] [L.CommShift ℤ]

omit [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [L.CommShift ℤ] in
/-- **A right adjoint preserves the direct sum of a family against which the images of the shifts
of a compact weak generator are compact.** Let `L ⊣ R` with `L` additive, let `E` be a compact
weak generator of the target of `R`, and let `family` be a family in the source of `R` such that
the compactness map of `L A` against `∐ family` is bijective for every shift `A` of `E`. Then `R`
preserves the direct sum of `family`. -/
theorem preservesColimit_discrete_of_bijective_cofanMap (adj : L ⊣ R) (E : D)
    (hE : (ObjectProperty.singleton E).IsWeakTriangulatedGenerator)
    (hcompact : IsCompactObject.{w} E) {I : Type w} [DecidableEq I] (family : I → C)
    (hmap : ∀ A : D, (ObjectProperty.singleton E).shiftClosure ℤ A →
      Function.Bijective (cofanMap (L.obj A) (Limits.Sigma.ι family))) :
    PreservesColimit (Discrete.functor family) R := by
  let compactD : ObjectProperty D := IsCompactObject.{w}
  have : ObjectProperty.IsClosedUnderIsomorphisms (IsCompactObject.{w, _, _} (C := D)) :=
    (isClosedUnderIsomorphisms_isTriangulated_isSaturated_and_isIdempotentComplete_isCompactObject
      (D := D)).1
  have : ObjectProperty.IsTriangulated (IsCompactObject.{w, _, _} (C := D)) :=
    (isClosedUnderIsomorphisms_isTriangulated_isSaturated_and_isIdempotentComplete_isCompactObject
      (D := D)).2.1
  let comparison := sigmaComparison R family
  have hbij : ∀ A : D, ((ObjectProperty.singleton E).shiftClosure ℤ) A →
      Function.Bijective
        (fun map : A ⟶ ∐ (fun i => R.obj (family i)) => map ≫ comparison) := by
    intro A hA
    have hmapA := hmap A hA
    obtain ⟨original, degree, iso, horiginal⟩ := hA
    rw [ObjectProperty.singleton_iff] at horiginal
    subst horiginal
    have hACompact : IsCompactObject.{w} A :=
      compactD.prop_of_iso iso.symm (compactD.le_shift degree _ hcompact)
    have hsource := bijective_cofanMap A hACompact
      (Limits.Sigma.ι (fun i => R.obj (family i))) (coproductIsCoproduct _)
    have htarget := bijective_cofanMap_of_adjunction_of_bijective adj A
      (Limits.Sigma.ι family) hmapA
    have hsquare :
        (fun map : A ⟶ ∐ (fun i => R.obj (family i)) => map ≫ comparison) ∘
            cofanMap A (Limits.Sigma.ι (fun i => R.obj (family i))) =
          cofanMap A (fun i => R.map (Limits.Sigma.ι family i)) := by
      funext element
      have hnatural := cofanMap_naturality A
        (Limits.Sigma.ι (fun i => R.obj (family i)))
        (fun i => R.map (Limits.Sigma.ι family i)) (fun i => 𝟙 _) comparison
        (fun i => by simp [comparison]) element
      have hidentity : (DirectSum.map fun i =>
          Preadditive.rightComp A (𝟙 (R.obj (family i)))) element = element := by
        ext i
        simp [DirectSum.map_apply, Preadditive.rightComp]
      rw [hidentity] at hnatural
      exact hnatural.symm
    exact (Function.Bijective.of_comp_iff _ hsource).1 (hsquare ▸ htarget)
  have hiso : IsIso comparison :=
    isIso_of_rightOrthogonal_eq_zero hE comparison
      (fun {A} hA η => ⟨(hbij A hA).2 η |>.choose, ((hbij A hA).2 η).choose_spec.symm⟩)
      (fun {A} hA ζ hζ => (hbij A hA).1 (by simpa using hζ))
  exact PreservesCoproduct.of_iso_comparison _ _

end CategoryTheory.Pretriangulated

end
