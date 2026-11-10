module

public import Mathlib.CategoryTheory.Localization.Resolution
public import StacksFrontier.CategoryTheory.Triangulated.Localization
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.TensorPreservesQuasiIso
import StacksCore.Tactic.StacksAttribute

/-!
# K-flat complexes form a triangulated subcategory of the homotopy category

Let `(C, O)` be a ringed site. The K-flat complexes of `O`-modules, viewed as objects of the
homotopy category `K(Mod(O))`, form a full pre-triangulated subcategory: the zero complex is
K-flat, K-flatness is stable under shifts, and in a distinguished triangle two K-flat vertices
force the third. The last of these is Stacks 07A3.

The argument is the one in the source: for each fixed acyclic complex `M` the functor
`K ↦ Tot(M ⊗_O K)` on `K(Mod(O))` is exact (Stacks 06YM), so the preimage under it of the
acyclic objects is a triangulated subcategory, and K-flatness of `K` is exactly membership of
`K` in all of those preimages. An intersection of triangulated subcategories inherits each of
the three closure properties, which is how they are checked here, one acyclic `M` at a time.

## Main definitions

* `Stacks.SheafOfModules.kFlatObjects`: K-flatness as a property of objects of the homotopy
  category, with `Stacks.SheafOfModules.kFlatObjects_as` unfolding it.
* `Stacks.SheafOfModules.kFlatQuasiIso`: the quasi-isomorphisms between K-flat complexes.
* `Stacks.SheafOfModules.kFlatLocalizer`: the inclusion of the K-flat complexes, as a morphism
  of localizers from the quasi-isomorphisms between K-flat complexes to the
  quasi-isomorphisms of `K(Mod(O))`.

## Main results

* `Stacks.SheafOfModules.kFlatObjects_isTriangulated`: the K-flat objects form a
  pre-triangulated subcategory. The two-out-of-three part is Stacks 07A3.
* `Stacks.SheafOfModules.kFlatObjects_isClosedUnderIsomorphisms`: K-flatness of an object of
  the homotopy category is invariant under isomorphism.
* `Stacks.SheafOfModules.quasiIso_isSaturated_and_isCompatibleWithTriangulation`: the
  quasi-isomorphisms of `K(Mod(O))` are a saturated multiplicative system compatible with the
  triangulated structure.

## Implementation notes

The functor `K ↦ Tot(M ⊗_O K)` on the homotopy category is
`Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi`, with the fixed complex `M` in the left
  tensor slot,
which is the slot `Stacks.SheafOfModules.IsKFlat` quantifies over; its exactness is
`Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi_isTriangulated` and its commutation with the
  shift is
`Stacks.SheafOfModules.Tensor.Reduction.bifunctorXi`, both of which have to be introduced as local
  instances
before the subcategory API applies.

That the quasi-isomorphisms are saturated and compatible with the triangulated structure is
obtained from the degree-zero homology functor of the homotopy category, by the general
criterion for the class of morphisms a homological functor inverts
(Stacks 05R5, formalized as
`CategoryTheory.Functor.isSaturated_and_isCompatibleWithTriangulation`).

`kFlatLocalizer` exists so that the comparison of the localization of the K-flat complexes
with the derived category can be stated; that it is a localized equivalence needs the
existence of K-flat resolutions and so is proved elsewhere.

## References

* [Stacks Project, Tag 07A3](https://stacks.math.columbia.edu/tag/07A3)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
* [Stacks Project, Tag 05R5](https://stacks.math.columbia.edu/tag/05R5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v w

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{w})
  [HasSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The quasi-isomorphisms of `K(Mod(O))` form a saturated multiplicative system compatible
with the triangulated structure, being the morphisms inverted by all the shifts of the
degree-zero homology functor. -/
theorem quasiIso_isSaturated_and_isCompatibleWithTriangulation :
    MorphismProperty.IsSaturated
        (HomotopyCategory.quasiIso
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) (ComplexShape.up ℤ)) ∧
      MorphismProperty.IsCompatibleWithTriangulation
        (HomotopyCategory.quasiIso
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) (ComplexShape.up ℤ)) := by
  let A := SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} R)
  let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
  let H := HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) 0
  have hS : ∀ ⦃X Y : HomotopyCategory A (ComplexShape.up ℤ)⦄ (f : X ⟶ Y),
      W f ↔ ∀ i : ℤ, IsIso (H.map (f⟦i⟧')) := by
    intro X Y f
    let _ : H.ShiftSequence ℤ := Functor.ShiftSequence.tautological H ℤ
    dsimp [W]
    rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
    exact H.mem_homologicalKernel_trW_iff f
  exact Functor.isSaturated_and_isCompatibleWithTriangulation H W hS

variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} R)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)]

/-- The homotopy category of cochain complexes of sheaves of modules on the ringed site. -/
abbrev HomotopyModules :=
  HomotopyCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} R))
    (ComplexShape.up ℤ)

/-- K-flatness as a property of objects of the homotopy category. -/
def kFlatObjects : ObjectProperty (HomotopyModules.{u, v, w} R) :=
  fun K ↦ IsKFlat R K.as

/-- `kFlatObjects` holds of an object of the homotopy category exactly when the underlying
complex is K-flat. -/
theorem kFlatObjects_as (K : HomotopyModules.{u, v, w} R) :
    kFlatObjects R K ↔ IsKFlat R K.as :=
  Iff.rfl

/-- For a fixed acyclic complex `M`, the objects `K` of the homotopy category with
`Tot(M ⊗_O K)` acyclic. K-flatness is membership in all of these. It is an abbreviation so
that, once the exactness of `Tot(M ⊗_O -)` is in scope, the pre-triangulated subcategory API
for a preimage applies to it directly. -/
abbrev acyclicTensorPreimage
    (M : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ) :
    ObjectProperty (HomotopyModules.{u, v, w} R) :=
  (HomotopyCategory.subcategoryAcyclic
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R))).inverseImage
    (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi (Stacks.SheafOfModules.Tensor.sheafTensor
      R) M)

/-- For every complex `M`, the objects with `Tot(M ⊗_O K)` acyclic form a triangulated
subcategory, as the preimage of the acyclic objects under an exact functor. -/
private theorem acyclicTensorPreimage_isTriangulated
    (M : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ) :
    (acyclicTensorPreimage.{u, v, w} R M).IsTriangulated := by
  let _ := Stacks.SheafOfModules.Tensor.Reduction.bifunctorXi
    (Stacks.SheafOfModules.Tensor.sheafTensor R) M
  let _ := Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi_isTriangulated
    (Stacks.SheafOfModules.Tensor.sheafTensor R) M
  infer_instance

/-- K-flatness of an object of the homotopy category is membership in every
`acyclicTensorPreimage M`, for `M` acyclic. -/
theorem kFlatObjects_iff (K : HomotopyModules.{u, v, w} R) :
    kFlatObjects R K ↔
      ∀ M : CochainComplex
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ,
          M.Acyclic → acyclicTensorPreimage R M K := by
  constructor
  · intro hK M hM
    change HomotopyCategory.subcategoryAcyclic _
      ((HomotopyCategory.quotient _ _).obj
        (((Stacks.SheafOfModules.Tensor.tensorComplex R).obj M).obj K.as))
    exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 (hK M hM)
  · exact fun hK M hM ↦
      (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1 (hK M hM)

/-- K-flatness of an object of the homotopy category is invariant under isomorphism: an
isomorphism of the homotopy category is a homotopy equivalence, and acyclicity of the total
tensor complex is invariant under it. -/
instance kFlatObjects_isClosedUnderIsomorphisms :
    (kFlatObjects.{u, v, w} R).IsClosedUnderIsomorphisms where
  of_iso {K K'} e hK := by
    rw [kFlatObjects_iff] at hK ⊢
    intro M hM
    let _ := Stacks.SheafOfModules.Tensor.Reduction.bifunctorXi
      (Stacks.SheafOfModules.Tensor.sheafTensor R) M
    let _ := Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi_isTriangulated
      (Stacks.SheafOfModules.Tensor.sheafTensor R) M
    exact (acyclicTensorPreimage R M).prop_of_iso e (hK M hM)

/-- The K-flat complexes form a pre-triangulated subcategory of the homotopy category: the
zero complex is K-flat, K-flatness is stable under shifts, and in a distinguished triangle
two K-flat vertices force the third. The last assertion is Stacks 07A3. -/
@[stacks 07A3 "two out of three in a distinguished triangle"]
theorem kFlatObjects_isTriangulated : (kFlatObjects.{u, v, w} R).IsTriangulated := by
  refine { exists_zero := ?_, isStableUnderShiftBy := ?_, ext₂' := ?_ }
  · have hZ : IsZero ((HomotopyCategory.quotient _ _).obj
        (HomologicalComplex.zero :
          CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ)) :=
      (HomotopyCategory.quotient _ _).map_isZero HomologicalComplex.isZero_zero
    refine ⟨_, hZ, ?_⟩
    rw [kFlatObjects_iff]
    intro M _
    have := acyclicTensorPreimage_isTriangulated R M
    exact (acyclicTensorPreimage R M).prop_of_isZero hZ
  · intro n
    refine ⟨fun K hK ↦ ?_⟩
    change kFlatObjects R (K⟦n⟧)
    rw [kFlatObjects_iff] at hK ⊢
    intro M hM
    have := acyclicTensorPreimage_isTriangulated R M
    exact (acyclicTensorPreimage R M).le_shift n K (hK M hM)
  · intro T hT h₁ h₃
    apply (kFlatObjects R).le_isoClosure
    rw [kFlatObjects_iff] at h₁ h₃ ⊢
    intro M hM
    have := acyclicTensorPreimage_isTriangulated R M
    exact (acyclicTensorPreimage R M).ext_of_isTriangulatedClosed₂ T hT (h₁ M hM) (h₃ M hM)

attribute [instance] kFlatObjects_isTriangulated

/-- The quasi-isomorphisms between K-flat complexes. -/
abbrev kFlatQuasiIso :
    MorphismProperty (kFlatObjects.{u, v, w} R).FullSubcategory :=
  (HomotopyCategory.quasiIso
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) (ComplexShape.up
        ℤ)).inverseImage
    (kFlatObjects R).ι

/-- The inclusion of the K-flat complexes into the homotopy category, as a morphism of
localizers. -/
def kFlatLocalizer :
    LocalizerMorphism (kFlatQuasiIso.{u, v, w} R)
      (HomotopyCategory.quasiIso
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) (ComplexShape.up ℤ)) where
  functor := (kFlatObjects R).ι
  map _ _ _ hf := hf

end Stacks.SheafOfModules

end
