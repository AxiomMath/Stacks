module

public import StacksFrontier.CategoryTheory.Triangulated.CompactObjects
import all StacksFrontier.CategoryTheory.Triangulated.CompactObjects

/-!
# Right adjoints commuting with direct sums, via a compact generating family

Let `L ⊣ R` be an adjunction of exact functors between pre-triangulated categories with direct
sums, and suppose the target `D` of `R` has a weakly generating family `E i` of compact objects
whose images `L (E i)` are again compact. Then `R` commutes with direct sums.

This is `CategoryTheory.Pretriangulated.preservesColimitsOfShape_discrete_of_isCompactObject_map`
for a generating *family* rather than a single generator. It is the form in which compact
generation is available for `D_QCoh(𝒪_X)` of a quasi-compact quasi-separated scheme
(`Stacks.Duality.QcqsGeneration.isCompactlyGenerated_quasiCoherentDerivedCategory`, the
compactly generated form of [Stacks, Tag 09IS]).

## Main results

In the namespace `CategoryTheory.Pretriangulated`:

* `preservesColimitsOfShape_discrete_of_isCompactObject_map_ofObj`
* `preservesCoproducts_of_isCompactlyGenerated_of_isCompactObject_map`
  — the same for every index type at once, from `IsCompactlyGenerated`.

## Implementation notes

The proof is that of the single-generator statement: the comparison `∐ᵢ R Xᵢ ⟶ R (∐ᵢ Xᵢ)` is
invertible as soon as postcomposition with it is bijective on morphisms out of each `(E i)⟦n⟧`
(`CategoryTheory.Pretriangulated.isIso_of_rightOrthogonal_eq_zero`), and both sides of that
square are compactness maps.

## References

* [Stacks Project, Tag 0A9R](https://stacks.math.columbia.edu/tag/0A9R)
* [Stacks Project, Tag 09SQ](https://stacks.math.columbia.edu/tag/09SQ)
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
compactness of a weakly generating family.** Let `L ⊣ R` with `L` additive and compatible with the
shift, let `E` be a family of compact objects of the target of `R` which is a weak generator, and
suppose every `L (E i)` is compact. Then `R` preserves direct sums indexed by any type of the
universe in which compactness is tested. -/
theorem preservesColimitsOfShape_discrete_of_isCompactObject_map_ofObj (adj : L ⊣ R)
    {ι : Type*} (E : ι → D) (hE : (ObjectProperty.ofObj E).IsWeakTriangulatedGenerator)
    (hcompact : ∀ i, IsCompactObject.{w} (E i)) (hmap : ∀ i, IsCompactObject.{w} (L.obj (E i)))
    (I : Type w) : PreservesColimitsOfShape (Discrete I) R := by
  classical
  let compactC : ObjectProperty C := IsCompactObject.{w}
  let compactD : ObjectProperty D := IsCompactObject.{w}
  obtain ⟨_, _, -⟩ :=
    isClosedUnderIsomorphisms_isTriangulated_isSaturated_and_isIdempotentComplete_isCompactObject
      (D := C)
  obtain ⟨_, _, -⟩ :=
    isClosedUnderIsomorphisms_isTriangulated_isSaturated_and_isIdempotentComplete_isCompactObject
      (D := D)
  constructor
  intro diagram
  let family := diagram.obj ∘ Discrete.mk
  let comparison := sigmaComparison R family
  have hbij : ∀ A : D, ((ObjectProperty.ofObj E).shiftClosure ℤ) A →
      Function.Bijective
        (fun map : A ⟶ ∐ (fun i => R.obj (family i)) => map ≫ comparison) := by
    rintro A ⟨original, degree, iso, horiginal⟩
    obtain ⟨i, rfl⟩ := (ObjectProperty.ofObj_iff E original).1 horiginal
    have hACompact : IsCompactObject.{w} A :=
      compactD.prop_of_iso iso.symm (compactD.le_shift degree _ (hcompact i))
    have hmapCompact : IsCompactObject.{w} (L.obj A) :=
      compactC.prop_of_iso (L.mapIso iso ≪≫ (L.commShiftIso degree).app (E i)).symm
        (compactC.le_shift degree _ (hmap i))
    have hsource := bijective_cofanMap A hACompact
      (Limits.Sigma.ι (fun i => R.obj (family i))) (coproductIsCoproduct _)
    have htarget := bijective_cofanMap_of_adjunction adj A hmapCompact
      (Limits.Sigma.ι family) (coproductIsCoproduct family)
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
  have : PreservesColimit (Discrete.functor family) R :=
    PreservesCoproduct.of_iso_comparison _ _
  exact preservesColimit_of_iso_diagram _ Discrete.natIsoFunctor.symm

/-- **In a compactly generated category, a right adjoint commutes with all direct sums as soon as
its left adjoint carries compact objects to compact objects.** -/
theorem preservesCoproducts_of_isCompactlyGenerated_of_isCompactObject_map (adj : L ⊣ R)
    (hD : IsCompactlyGenerated.{w} D)
    (hmap : ∀ K : D, IsCompactObject.{w} K → IsCompactObject.{w} (L.obj K)) :
    ∀ I : Type w, PreservesColimitsOfShape (Discrete I) R := by
  obtain ⟨ι, E, hEc, hE⟩ := hD
  exact preservesColimitsOfShape_discrete_of_isCompactObject_map_ofObj adj E hE hEc
    fun i => hmap _ (hEc i)

end CategoryTheory.Pretriangulated

end
