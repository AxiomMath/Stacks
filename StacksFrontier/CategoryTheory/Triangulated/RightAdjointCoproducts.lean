module

public import StacksFrontier.CategoryTheory.Triangulated.CompactObjects
import all StacksFrontier.CategoryTheory.Triangulated.CompactObjects

/-!
# A right adjoint commutes with direct sums when its left adjoint preserves compactness

Let `L ⊣ R` be an adjunction of exact functors between pre-triangulated categories with direct
sums, and suppose the target `D` of `R` has a compact weak generator `E` whose image `L E` is
again compact. Then `R` commutes with direct sums.

This is the formal device behind [Stacks, Tag 08DZ]: derived direct image `Rf_*` along a
quasi-compact, quasi-separated morphism of schemes commutes with direct sums because its left
adjoint `Lf^*` carries a compact generator of `D_QCoh(𝒪_Y)` to a compact object of
`D_QCoh(𝒪_X)`. Nothing geometric is used here, and no choice of model of a derived category is
made.

## Main results

* `CategoryTheory.Pretriangulated.preservesColimitsOfShape_discrete_of_isCompactObject_map` — the
  statement above, one index type at a time.
* `CategoryTheory.Pretriangulated.preservesCoproducts_of_isCompactObject_map` — the same for all
  index types at once, in the shape in which Brown representability consumes it.

## Implementation notes

The proof is the standard one. Direct sums are preserved exactly when the canonical comparison
morphism `∐ᵢ R Xᵢ ⟶ R (∐ᵢ Xᵢ)` is invertible, and a weak generator detects invertibility
(`CategoryTheory.Pretriangulated.isIso_of_rightOrthogonal_eq_zero`); so it suffices to see that
postcomposition with the comparison is bijective on morphisms out of each shift `E⟦n⟧`. Both
sides of that square are compactness maps in the sense of
`CategoryTheory.Pretriangulated.cofanMap`: the source side is the compactness of `E⟦n⟧`, and the
target side is the compactness of `L (E⟦n⟧) ≅ (L E)⟦n⟧` read through the adjunction bijections,
which is `CategoryTheory.Pretriangulated.bijective_cofanMap_of_adjunction`. The square commutes by
naturality of the compactness map in the family, with the identity as its componentwise map.

Compactness of `E⟦n⟧` and of `L (E⟦n⟧)` are obtained from compactness of `E` and of `L E` by the
closure properties of the compact objects
(`isClosedUnderIsomorphisms_isTriangulated_isSaturated_and_isIdempotentComplete_isCompactObject`),
using that `L` commutes with the shift to identify `L (E⟦n⟧)` with `(L E)⟦n⟧`.

## References

* [Stacks Project, Tag 08DZ](https://stacks.math.columbia.edu/tag/08DZ)
* [Stacks Project, Tag 0A8G](https://stacks.math.columbia.edu/tag/0A8G)
* [Amnon Neeman, *The Grothendieck duality theorem via Bousfield's techniques and Brown
  representability*, Example 4.2][Neeman-Grothendieck]
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

/-- **A right adjoint commutes with direct sums as soon as its left adjoint preserves the
compactness of a weak generator.** Let `L ⊣ R` with `L` additive and compatible with the shift,
let `E` be a compact weak generator of the target of `R`, and suppose `L E` is compact. Then `R`
preserves direct sums indexed by any type of the universe in which compactness is tested. -/
theorem preservesColimitsOfShape_discrete_of_isCompactObject_map (adj : L ⊣ R) (E : D)
    (hE : (ObjectProperty.singleton E).IsWeakTriangulatedGenerator)
    (hcompact : IsCompactObject.{w} E) (hmap : IsCompactObject.{w} (L.obj E)) (I : Type w) :
    PreservesColimitsOfShape (Discrete I) R := by
  classical
  let compactC : ObjectProperty C := IsCompactObject.{w}
  let compactD : ObjectProperty D := IsCompactObject.{w}
  obtain ⟨_, _, -⟩ :=
    isClosedUnderIsomorphisms_isTriangulated_isSaturated_and_isIdempotentComplete_isCompactObject
      (D := C)
  obtain ⟨_, _, -⟩ :=
    isClosedUnderIsomorphisms_isTriangulated_isSaturated_and_isIdempotentComplete_isCompactObject
      (D := D)
  refine ⟨fun {diagram} => ?_⟩
  let family := diagram.obj ∘ Discrete.mk
  let comparison := sigmaComparison R family
  have hbij : ∀ A : D, ((ObjectProperty.singleton E).shiftClosure ℤ) A →
      Function.Bijective
        (fun map : A ⟶ ∐ (fun i => R.obj (family i)) => map ≫ comparison) := by
    rintro A ⟨original, degree, iso, horiginal⟩
    rw [ObjectProperty.singleton_iff] at horiginal
    subst horiginal
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
      exact hnatural.symm.trans (congrArg _ hidentity)
    exact (Function.Bijective.of_comp_iff _ (bijective_cofanMap A
      (compactD.prop_of_iso iso.symm (compactD.le_shift degree _ hcompact)) _
      (coproductIsCoproduct _))).1 (hsquare ▸ bijective_cofanMap_of_adjunction adj A
        (compactC.prop_of_iso (L.mapIso iso ≪≫ (L.commShiftIso degree).app E).symm
          (compactC.le_shift degree _ hmap)) _ (coproductIsCoproduct family))
  have hiso : IsIso comparison :=
    isIso_of_rightOrthogonal_eq_zero hE comparison
      (fun {A} hA η => ((hbij A hA).2 η).imp fun _ h => h.symm)
      (fun {A} hA ζ hζ => (hbij A hA).1 (by simpa using hζ))
  have : PreservesColimit (Discrete.functor family) R :=
    PreservesCoproduct.of_iso_comparison _ _
  exact preservesColimit_of_iso_diagram _ Discrete.natIsoFunctor.symm

/-- **A right adjoint commutes with all direct sums as soon as its left adjoint preserves the
compactness of a weak generator** — the previous statement for every index type at once, which is
the shape Brown representability ([Stacks, Tag 0A8G]) asks for. -/
theorem preservesCoproducts_of_isCompactObject_map (adj : L ⊣ R) (E : D)
    (hE : (ObjectProperty.singleton E).IsWeakTriangulatedGenerator)
    (hcompact : IsCompactObject.{w} E) (hmap : IsCompactObject.{w} (L.obj E)) :
    ∀ I : Type w, PreservesColimitsOfShape (Discrete I) R :=
  preservesColimitsOfShape_discrete_of_isCompactObject_map adj E hE hcompact hmap

end CategoryTheory.Pretriangulated

end
