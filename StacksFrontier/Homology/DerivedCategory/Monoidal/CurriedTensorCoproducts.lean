module

public import StacksFrontier.Homology.DerivedCategory.Monoidal.CurriedTensorCommShift
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaQCohCoproducts
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorCoproducts

/-!
# `K ⊗ -` on cochain complexes commutes with direct sums

Let `A` be a monoidal category with the hypotheses under which `CochainComplex A ℤ` is monoidal.
If direct sums indexed by `J` exist in `A` and `M ⊗ -` preserves them for every object `M`, then
`K ⊗ -` preserves them for every *complex* `K`.

This is the hypothesis
`[∀ P : CochainComplex A ℤ, PreservesColimitsOfShape (Discrete J) (tensorLeft P)]` that
`CochainComplex.KFlatMonoidal.preservesColimitsOfShape_tensorLeft` takes, and the point of this
file is to discharge it from a condition on `A` alone. The existing route to that hypothesis goes
through `CochainComplex.internalHomAdjunction`, i.e. through `[MonoidalClosed A]`; a category of
diagrams `Cᵒᵖ ⥤ Mod R` with the pointwise tensor product is *not* monoidal closed — its internal
hom is an end over the slice, not the pointwise one — so for such coefficients that route is
unavailable and this one is the only one.

## Main results

* `CochainComplex.KFlatMonoidal.preservesColimitsOfShape_discrete_tensorLeft_cochainComplex`:
  **`K ⊗ -` on `Comp(A)` preserves direct sums**, from the same statement for the objects of `A`.
* `CochainComplex.KFlatMonoidal.preservesColimitsOfShape_discrete_derivedMonoidal_tensorLeft`
  and `…_tensorRight`: **the derived tensor product of Tag 0FPT preserves direct sums in each
  variable**, with the complex-level hypothesis of
  `CochainComplex.KFlatMonoidal.preservesColimitsOfShape_tensorLeft` discharged, so that the
  only conditions left are on `A`. The `tensorRight` form is what a dévissage of Stacks 08QB in
  the first variable asks of the two functors it compares; it is obtained from the `tensorLeft`
  form along the commutativity constraint `CochainComplex.KFlatMonoidal.derivedSymmetric`, which
  is why the symmetry of `Comp(A)` -- and not merely its braiding -- is assumed there.

## Implementation notes

The tensor product of complexes is `HomologicalComplex.Monoidal.tensorObj`, which is
`HomologicalComplex.mapBifunctor` for `CategoryTheory.MonoidalCategory.curriedTensor`, and
`tensorLeft K` is therefore the same functor as
`(curriedTensor A).map₂HomologicalComplex _ _ _` evaluated at `K` — on objects because both are
`mapBifunctor K - (curriedTensor A) _`, and on morphisms because `K ◁ g` is
`HomologicalComplex.Monoidal.tensorHom (𝟙 K) g`, which is `mapBifunctorMap (𝟙 K) g`, the action
of `map₂HomologicalComplex`. So the content is the lemma
`preservesColimitsOfShape_map₂HomologicalComplex_obj` of the namespace
`Stacks.Cohomology.ProjectionFormulaQCohCoproducts`: the double complex preserves the colimit
degreewise, and so does totalisation.

`HasCoproducts.{0} A` is asked for because the total complex of a bicomplex is assembled from
coproducts over the fibres of `ComplexShape.up ℤ`'s addition, which are types in `Type 0`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex.KFlatBifunctor

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

/-- **`K ⊗ -` on `Comp(A)` is the total complex of the tensor bifunctor in its second
variable.** Both sides send `L` to `HomologicalComplex.mapBifunctor K L (curriedTensor A) _` and
`g` to `HomologicalComplex.mapBifunctorMap (𝟙 K) g`, so the two functors are equal. -/
theorem tensorLeft_eq_map₂HomologicalComplex_obj (K : CochainComplex A ℤ) :
    tensorLeft K =
      ((curriedTensor A).map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj K :=
  rfl

/-- **`K ⊗ -` on cochain complexes of `A` preserves direct sums** as soon as `M ⊗ -` does for
every object `M` of `A`. The tensor product of complexes is the total complex of the tensor
bifunctor applied degreewise, and both of those steps preserve the colimit:
`preservesColimitsOfShape_map₂HomologicalComplex_obj` of the namespace
`Stacks.Cohomology.ProjectionFormulaQCohCoproducts`.

This discharges the one hypothesis of
`CochainComplex.KFlatMonoidal.preservesColimitsOfShape_tensorLeft` which is not about `A` alone,
for coefficients where `A` is not monoidal closed. -/
theorem preservesColimitsOfShape_discrete_tensorLeft_cochainComplex
    (J : Type*) [HasCoproducts.{0} A] [HasColimitsOfShape (Discrete J) A]
    [∀ M : A, PreservesColimitsOfShape (Discrete J) (tensorLeft M)]
    (K : CochainComplex A ℤ) :
    PreservesColimitsOfShape (Discrete J) (tensorLeft K) := by
  rw [tensorLeft_eq_map₂HomologicalComplex_obj]
  open Stacks.Cohomology in
  exact ProjectionFormulaQCohCoproducts.preservesColimitsOfShape_map₂HomologicalComplex_obj
    (curriedTensor A) K

section Derived

variable [HasDerivedCategory.{w} A] [SymmetricCategory (CochainComplex A ℤ)]
  (hres : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
    CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) P ∧ QuasiIso f)
  (J : Type*) [HasCoproducts.{0} A] [HasColimitsOfShape (Discrete J) A]
  [∀ M : A, PreservesColimitsOfShape (Discrete J) (tensorLeft M)]
  [HasColimitsOfShape (Discrete J) (CochainComplex A ℤ)]
  [PreservesColimitsOfShape (Discrete J) (DerivedCategory.Q (C := A))]

include hres in
/-- **`K ⊗^L -` on `D(A)` preserves direct sums**, for the monoidal structure of Tag 0FPT, under
a condition on `A` alone: that `M ⊗ -` preserves them for each object `M`.

`CochainComplex.KFlatMonoidal.preservesColimitsOfShape_tensorLeft` is the statement with the
complex-level preservation as a hypothesis; the hypothesis is discharged here by
`preservesColimitsOfShape_discrete_tensorLeft_cochainComplex`. -/
theorem preservesColimitsOfShape_discrete_derivedMonoidal_tensorLeft
    (K : DerivedCategory A) :
    letI := kFlatQ_isLocalization (curriedTensor A) hres
    letI := derivedMonoidal A hres
    PreservesColimitsOfShape (Discrete J) (tensorLeft K) := by
  let : ∀ P : CochainComplex A ℤ, PreservesColimitsOfShape (Discrete J) (tensorLeft P) :=
    fun P ↦ preservesColimitsOfShape_discrete_tensorLeft_cochainComplex A J P
  exact preservesColimitsOfShape_tensorLeft A hres K J

include hres in
/-- **`- ⊗^L K` on `D(A)` preserves direct sums**, for the monoidal structure of Tag 0FPT. The
commutativity constraint `CochainComplex.KFlatMonoidal.derivedSymmetric` identifies it with
`K ⊗^L -`, so this is
`preservesColimitsOfShape_discrete_derivedMonoidal_tensorLeft` transported along
`CategoryTheory.BraidedCategory.tensorLeftIsoTensorRight`.

This is the variable the first-variable dévissage of Stacks 08QB reads the comparison in: there
the second complex is arbitrary, so the fixed factor sits on the right. -/
theorem preservesColimitsOfShape_discrete_derivedMonoidal_tensorRight
    (K : DerivedCategory A) :
    letI := kFlatQ_isLocalization (curriedTensor A) hres
    letI := derivedMonoidal A hres
    PreservesColimitsOfShape (Discrete J) (tensorRight K) := by
  let := kFlatQ_isLocalization (curriedTensor A) hres
  let := derivedMonoidal A hres
  let := derivedSymmetric A hres
  let := preservesColimitsOfShape_discrete_derivedMonoidal_tensorLeft A hres J K
  exact preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight K)

end Derived

end CochainComplex.KFlatMonoidal

end
