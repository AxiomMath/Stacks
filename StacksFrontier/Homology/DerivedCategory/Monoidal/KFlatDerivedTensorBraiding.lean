module

public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatDerivedBraiding
public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatDerivedComparison

/-!
# The commutativity constraint of `D(A)` through the K-flat comparison

`CochainComplex.KFlatMonoidal.derivedTensorIso` identifies the tensor product of
`CochainComplex.KFlatMonoidal.derivedMonoidal` at the images of two K-flat complexes with the
image of their total tensor product.  This file supplies the clause of Stacks Tag 0FPT that
`StacksFrontier/CategoryTheory/Sites/Cohomology/Monoidal/DerivedTensorReseat.lean` records as
absent: **the commutativity constraint of `D(A)` is, through that comparison, the braiding of
`Comp(A)`** — for complexes of modules, the Koszul symmetry.

## Main results

* `CochainComplex.KFlatMonoidal.braiding_comp_kFlatHomotopyMu`: in the full monoidal
  subcategory of K-flat objects of `K(A)`, the braiding followed by the tensorator of the
  first localization is that tensorator followed by the image of the braiding of `Comp(A)`.
* `CochainComplex.KFlatMonoidal.derivedTensorIso_braiding`: the square above, in `D(A)`.

## Implementation notes

The two localizations are handled one at a time.  Over the second,
`CochainComplex.KFlatMonoidal.derived_braiding_hom` computes the braiding of `D(A)` at the
images of two K-flat objects of `K(A)` as the conjugate of the braiding of those objects by
the tensorator; over the first, `CochainComplex.KFlatMonoidal.homotopy_braiding_hom` does the
same for `K(A)` and `Comp(A)`, and `CochainComplex.KFlatMonoidal.ι_map_braiding` carries it
into the full subcategory.  What remains is the two `Q` versus `Qh ∘ quotient` bridges, across
which the braiding moves by its own naturality on the left and by the naturality of
`DerivedCategory.quotientCompQhIso` on the right.

The assembly is done in term mode through the generic lemmas of
`StacksFrontier/CategoryTheory/Category/CompositionChains.lean`, for the reason recorded in
`StacksFrontier/Homology/DerivedCategory/Monoidal/KFlatDerivedComparison.lean`: the factors of
the composite are typed both at `DerivedCategory A` and at the type synonym
`CategoryTheory.LocalizedMonoidal`, and a single `rfl` over the whole composite is a
definitional equality the kernel cannot check inside its heartbeat budget, whereas each step
on its own is immediate.

## References

* [The Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Localization CochainComplex.KFlatBifunctor

universe w v u

namespace CochainComplex.KFlatMonoidal

variable (A : Type u) [Category.{v} A] [Abelian A] [MonoidalCategory A]
  [(curriedTensor A).Additive] [∀ X : A, ((curriedTensor A).obj X).Additive]
  [∀ (X₁ X₂ : GradedObject ℤ A), GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X₁)]
  [∀ X₂ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

attribute [local instance] homotopyMonoidal homotopySymmetric

variable [HasDerivedCategory.{w} A] [SymmetricCategory (CochainComplex A ℤ)]
  [(kFlatQ (curriedTensor A)).IsLocalization (kFlatQuasiIso (curriedTensor A))]
  [(kFlatQLeft (curriedTensor A)).IsLocalization (kFlatQuasiIsoLeft (curriedTensor A))]
  (hres : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
    KFlat (curriedTensor A) P ∧ QuasiIso f)

attribute [local instance] derivedLocalizedTensorLifting derivedBifunctorLiftingKFlatQ

/-! ### The two localizations, one at a time -/

omit [HasDerivedCategory A]
  [(kFlatQ (curriedTensor A)).IsLocalization (kFlatQuasiIso (curriedTensor A))]
  [(kFlatQLeft (curriedTensor A)).IsLocalization (kFlatQuasiIsoLeft (curriedTensor A))] in
/-- **In the full monoidal subcategory of K-flat objects of `K(A)`, the braiding followed by
the tensorator of the first localization is that tensorator followed by the image of the
braiding of `Comp(A)`.**  The subcategory is full, so this is
`CochainComplex.KFlatMonoidal.homotopy_braiding_hom` with the inverse tensorator cancelled. -/
theorem braiding_comp_kFlatHomotopyMu {K L : CochainComplex A ℤ}
    (hK : KFlat (curriedTensor A) K) (hL : KFlat (curriedTensor A) L) :
    (β_ (kFlatObjOf (curriedTensor A) K hK) (kFlatObjOf (curriedTensor A) L hL)).hom ≫
        (kFlatHomotopyMu A hL hK).hom =
      (kFlatHomotopyMu A hK hL).hom ≫
        ObjectProperty.homMk
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (β_ K L).hom) :=
  (kFlatObjects (curriedTensor A)).ι.map_injective
    (comp_iso_hom_of_eq_comp_comp_inv (homotopyMu A L K) (homotopy_braiding_hom A K L))

omit [(kFlatQ (curriedTensor A)).IsLocalization (kFlatQuasiIso (curriedTensor A))]
  [(kFlatQLeft (curriedTensor A)).IsLocalization (kFlatQuasiIsoLeft (curriedTensor A))] in
/-- The tensorator of the first localization and the right-hand `Q` versus `Qh ∘ quotient`
bridge, transported across the braiding: the first by
`CochainComplex.KFlatMonoidal.braiding_comp_kFlatHomotopyMu`, the second by naturality of
`DerivedCategory.quotientCompQhIso`. -/
theorem kFlatQ_map_braiding_comp_kFlatHomotopyMu {K L : CochainComplex A ℤ}
    (hK : KFlat (curriedTensor A) K) (hL : KFlat (curriedTensor A) L) :
    (kFlatQ (curriedTensor A)).map
          (β_ (kFlatObjOf (curriedTensor A) K hK)
            (kFlatObjOf (curriedTensor A) L hL)).hom ≫
        (kFlatQ (curriedTensor A)).map (kFlatHomotopyMu A hL hK).hom ≫
          (derivedQIso A (L ⊗ K)).hom =
      (kFlatQ (curriedTensor A)).map (kFlatHomotopyMu A hK hL).hom ≫
        (derivedQIso A (K ⊗ L)).hom ≫ DerivedCategory.Q.map (β_ K L).hom := by
  refine comp_chain_one_square ?_
    ((DerivedCategory.quotientCompQhIso A).hom.naturality (β_ K L).hom)
  rw [← Functor.map_comp, braiding_comp_kFlatHomotopyMu A hK hL, Functor.map_comp]
  rfl

/-! ### The commutativity constraint through the comparison -/

omit [(kFlatQLeft (curriedTensor A)).IsLocalization (kFlatQuasiIsoLeft (curriedTensor A))] in
/-- **[Stacks, Tag 0FPT], the commutativity constraint of `D(A)` is the braiding of
`Comp(A)`.**  For K-flat complexes `K` and `L` the comparison
`CochainComplex.KFlatMonoidal.derivedTensorIso` of the tensor product of `D(A)` with the image
of the total tensor product of complexes carries the commutativity constraint of `D(A)` to the
braiding of `Comp(A)` — for complexes of modules, the Koszul symmetry. -/
theorem derivedTensorIso_braiding {K L : CochainComplex A ℤ}
    (hK : KFlat (curriedTensor A) K) (hL : KFlat (curriedTensor A) L) :
    letI := derivedMonoidal A hres
    letI := derivedSymmetric A hres
    (β_ (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)).hom ≫
        (derivedTensorIso A hres hL hK).hom =
      (derivedTensorIso A hres hK hL).hom ≫ DerivedCategory.Q.map (β_ K L).hom :=
  let := derivedMonoidal A hres
  let := derivedSymmetric A hres
  comp_congr_both
    (derivedTensorIso_hom_tensorHom A hres hL hK)
    (derivedTensorIso_hom_tensorHom A hres hK hL)
    (comp_chain_braiding_four
      (BraidedCategory.braiding_naturality (derivedQIso A K).inv (derivedQIso A L).inv).symm
      (comp_iso_hom_of_eq_comp_comp_inv _
        (derived_braiding_hom A hres (kFlatObjOf (curriedTensor A) K hK)
          (kFlatObjOf (curriedTensor A) L hL)))
      (kFlatQ_map_braiding_comp_kFlatHomotopyMu A hK hL))

end CochainComplex.KFlatMonoidal

end
