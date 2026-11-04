module

public import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import StacksFrontier.CategoryTheory.Monoidal.Reseat
public import StacksFrontier.CategoryTheory.Monoidal.Rigid

/-!
# Duals and tensor–hom adjunctions across a re-seating

`CategoryTheory.MonoidalCategory.reseat` moves a monoidal structure onto a prescribed tensor
bifunctor.  A category can carry two such re-seatings of *one* monoidal structure, along two
prescribed bifunctors that are themselves isomorphic — this happens on the derived category of
a ringed site, which has two independently chosen derived tensor products — and then a
statement proved for one re-seating has to be read for the other.

Two such transfers are recorded here.

* An exact pairing for one re-seating is an exact pairing for the other: the identity functor is
  monoidal from either re-seating to the common underlying structure
  (`CategoryTheory.MonoidalCategory.reseatMonoidal`), so `CategoryTheory.ExactPairing.map`
  carries the pairing up to that structure and `CategoryTheory.ExactPairing.ofFullyFaithful`
  brings it down to the other.  No comparison of the two re-seatings is needed, because both
  sit over the same monoidal structure.
* Tensoring on the right by a fixed object, for a re-seating along `T`, *is* `T.flip` at that
  object, so a right adjoint of the flip of an isomorphic bifunctor is a right adjoint of it:
  `CategoryTheory.Adjunction.ofNatIsoLeft` at the flipped comparison.

## Main definitions

* `CategoryTheory.MonoidalCategory.reseatExactPairing`: the transfer of an exact pairing.
* `CategoryTheory.MonoidalCategory.reseatTensorRightAdjunction`: the transfer of an adjunction
  whose left adjoint is tensoring on the right.

## Main results

* `CategoryTheory.MonoidalCategory.tensorRight_reseat`: tensoring on the right for a re-seating
  is the flip of the prescribed bifunctor.
* `CategoryTheory.MonoidalCategory.reseatTensorRightAdjunction_counit_app` and
  `reseatTensorRightAdjunction_homEquiv`: its counit and its hom-set bijection.

## Implementation notes

The underlying monoidal structure is an **explicit** argument `M` throughout rather than an
instance.  The situation this file is for is one where neither the underlying structure nor
either re-seating is an instance — the derived category of a ringed site carries all three and
declares none — so every statement has to name the one it means, and a hypothesis
`[MonoidalCategory C]` would simply fail to be synthesized at every call site.
-/

@[expose] public noncomputable section

universe v u

namespace CategoryTheory.MonoidalCategory

open Category

variable {C : Type u} [Category.{v} C] {T T₁ T₂ : C ⥤ C ⥤ C} {U : C}

/-- **An exact pairing for one re-seating is an exact pairing for another.**  Both re-seatings
are re-seatings of the same monoidal structure `M` along the same unit comparison, so the
identity functor is monoidal from each of them to `M`; the pairing is carried up along the
first and reflected down along the second. -/
@[instance_reducible]
def reseatExactPairing (M : MonoidalCategory C) (e₁ : @curriedTensor C _ M ≅ T₁)
    (e₂ : @curriedTensor C _ M ≅ T₂) (ε : @tensorUnit C _ M.toMonoidalCategoryStruct ≅ U)
    (X Y : C) (h : @ExactPairing C _ (@reseat C _ M _ _ e₁ ε) X Y) :
    @ExactPairing C _ (@reseat C _ M _ _ e₂ ε) X Y :=
  letI := M
  letI hup : ExactPairing X Y :=
    @ExactPairing.map C C _ _ (reseat e₁ ε) _ (𝟭 C) (reseatMonoidal e₁ ε) X Y h
  @ExactPairing.ofFullyFaithful C C _ _ (reseat e₂ ε) _ (𝟭 C) (reseatMonoidal e₂ ε)
    inferInstance inferInstance X Y hup

/-- **Tensoring on the right for a re-seated structure is the flip of the prescribed
bifunctor.**  Both send `A` to `(T.obj A).obj B` and `f` to `(T.map f).app B`. -/
theorem tensorRight_reseat (M : MonoidalCategory C) (e : @curriedTensor C _ M ≅ T)
    (ε : @tensorUnit C _ M.toMonoidalCategoryStruct ≅ U) (B : C) :
    @tensorRight C _ (@reseat C _ M _ _ e ε) B = T.flip.obj B := rfl

/-- **An adjunction whose left adjoint is the flip of a bifunctor is an adjunction for the
re-seated tensor product**, as soon as the two bifunctors are isomorphic: tensoring on the right
for the re-seating along `T₂` is `T₂.flip` at the object, and the comparison of left adjoints is
the flip of the comparison of bifunctors. -/
def reseatTensorRightAdjunction (M : MonoidalCategory C) (e₂ : @curriedTensor C _ M ≅ T₂)
    (ε : @tensorUnit C _ M.toMonoidalCategoryStruct ≅ U) (φ : T₁ ≅ T₂) (B : C) {H : C ⥤ C}
    (adj : T₁.flip.obj B ⊣ H) : @tensorRight C _ (@reseat C _ M _ _ e₂ ε) B ⊣ H :=
  Adjunction.ofNatIsoLeft adj (((flipFunctor C C C).mapIso φ).app B)

/-- The counit of `CategoryTheory.MonoidalCategory.reseatTensorRightAdjunction` is the inverse
comparison followed by the counit of the given adjunction. -/
theorem reseatTensorRightAdjunction_counit_app (M : MonoidalCategory C)
    (e₂ : @curriedTensor C _ M ≅ T₂) (ε : @tensorUnit C _ M.toMonoidalCategoryStruct ≅ U)
    (φ : T₁ ≅ T₂) (B : C) {H : C ⥤ C} (adj : T₁.flip.obj B ⊣ H) (Z : C) :
    (reseatTensorRightAdjunction M e₂ ε φ B adj).counit.app Z =
      (φ.inv.app (H.obj Z)).app B ≫ adj.counit.app Z := by
  rw [reseatTensorRightAdjunction, Adjunction.ofNatIsoLeft_counit]
  rfl

/-- The hom-set bijection of `CategoryTheory.MonoidalCategory.reseatTensorRightAdjunction` is
the comparison followed by the hom-set bijection of the given adjunction. -/
theorem reseatTensorRightAdjunction_homEquiv (M : MonoidalCategory C)
    (e₂ : @curriedTensor C _ M ≅ T₂) (ε : @tensorUnit C _ M.toMonoidalCategoryStruct ≅ U)
    (φ : T₁ ≅ T₂) (B : C) {H : C ⥤ C} (adj : T₁.flip.obj B ⊣ H) (A Z : C)
    (f : (T₂.obj A).obj B ⟶ Z) :
    (reseatTensorRightAdjunction M e₂ ε φ B adj).homEquiv A Z f =
      adj.homEquiv A Z ((φ.hom.app A).app B ≫ f) := by
  rw [reseatTensorRightAdjunction, Adjunction.homEquiv_ofNatIsoLeft_apply]
  rfl

end CategoryTheory.MonoidalCategory

end
