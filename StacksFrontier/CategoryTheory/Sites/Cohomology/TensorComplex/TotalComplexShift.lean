module

public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Adjunction.Additive
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.TotalComplex

/-!
# The total tensor-product complex and the shift of its second factor

Let `X` be a ringed site and let `A`, `Z` be complexes of `O`-modules. This file identifies

`Tot(A ⊗_O Z⟦k⟧) ≅ Tot(A ⊗_O Z)⟦k⟧`.

Nothing of the construction is new: `Mathlib` already has the corresponding statement for the
total complex of a bifunctor, `CochainComplex.mapBifunctorShift₂Iso`, signs and all — on the
summand `(F.obj (K₁.X p)).obj (K₂.X q)` the comparison is multiplication by `(p * k).negOnePow`,
and `ι_mapBifunctorShift₂Iso_hom_f` records that. What this file does is carry that statement
across the two functors separating `tensorTotal` from a bare `mapBifunctor`: the total tensor
complex of this development is the *degreewise sheafification* of the `mapBifunctor` of the
*underlying presheaf complexes*.

Both of those functors are additive, and an additive functor's action on cochain complexes
commutes with the shift — `CategoryTheory.Functor.mapCochainComplexShiftIso`, whose components
are identities, the content being only that the functor commutes with multiplication by `-1`.
So the comparison is a composite of three steps: move the shift out of the underlying presheaf
complex of the second factor, apply Mathlib's comparison, and move the shift out of the
sheafification. The first two steps happen entirely at the presheaf level and are packaged
together as `underlyingTensorShiftIso₂`, so that the passage through the sheafification unit
has to be made only once.

## Main definitions

* `AlgebraicGeometry.RingedSite.underlyingTensorShiftIso₂`: the presheaf-level comparison
  `mapBifunctor A' (underlying complex of Z⟦k⟧) ≅ (mapBifunctor A' Z')⟦k⟧`.
* `AlgebraicGeometry.RingedSite.tensorTotalShiftIso₂`: the isomorphism above.

## Main results

* `AlgebraicGeometry.RingedSite.ι_underlyingTensorShiftIso₂_hom_f`: the presheaf-level
  comparison on the `(t, r)` summand is `(t * k).negOnePow` times the inclusion of the
  `(t, r + k)` summand. This is the whole numerical content of the file.
* `AlgebraicGeometry.RingedSite.tensorTotalSection_eq_unit_ι`: the local pure tensor is the
  sheafification unit applied to a summand inclusion. This is the crossing between the two
  layers in which the morphisms being compared are pinned — pure tensors on one side, summand
  inclusions on the other — and it holds by definition.

## Implementation notes

The additivity of sheafification is not available from `Mathlib` as an instance; it is obtained
from the sheafification adjunction by `CategoryTheory.Adjunction.left_adjoint_additive` and
registered here as `AlgebraicGeometry.RingedSite.sheafificationAdditive`. Registering it, rather
than introducing it by `letI` at each use, is what makes the instance appearing inside
`tensorTotalShiftIso₂` the same term as the one synthesised when a lemma about
`mapCochainComplexShiftIso` is applied to it. The additivity of the pointwise tensor product in
each variable, which `Mathlib`'s comparison also needs, is not assumed: it is proved beside the
rest of that structure, as
`AlgebraicGeometry.RingedSite.curriedTensorAdditive` and
`AlgebraicGeometry.RingedSite.curriedTensorObjAdditive`, and switched on here with the other
file-local instances of the monoidal structure.

This isomorphism is stated for the shift and not for the sign-free reindexing
`CochainComplex.reindexBy`, because Mathlib's input is stated for the shift. The translation
between the two is `CochainComplex.reindexByIsoShift`, which is where the sign is paid.

## References

* [Stacks Project, Lemma 20.26.4 (Tag 06YS)](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms
  curriedTensorAdditive curriedTensorObjAdditive

variable (X : RingedSite.{u, u, u})

/-- The degreewise sheafification of presheaves of modules is additive, being a left adjoint.
`Mathlib` does not register this, and the proofs below need the instance to be *one* term rather
than one `letI` per use, so it is registered here. -/
instance sheafificationAdditive :
    (PresheafOfModules.sheafification
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).Additive :=
  letI : (SheafOfModules.forget.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).Additive :=
    SheafOfModules.instAdditivePresheafOfModulesObjFunctorOppositeRingCatIsSheafForget
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).left_adjoint_additive

/-- **The local pure tensor is the sheafification unit applied to a summand inclusion.** This is
true by definition; it is stated because the two descriptions belong to different layers, and
every computation comparing a morphism pinned on pure tensors with one pinned on summand
inclusions has to cross between them at some point. Having the crossing as a lemma means the
abbreviation `tensorTotalSection` need not be unfolded by hand at each step. -/
lemma tensorTotalSection_eq_unit_ι
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C) (t r : ℤ)
    (a : (A.X t).val.obj (op U)) (b : (B.X r).val.obj (op U)) :
    tensorTotalSection X A B U t r a b =
      ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
          ((HomologicalComplex.mapBifunctor (underlyingPresheafComplex X A)
            (underlyingPresheafComplex X B)
            (MonoidalCategory.curriedTensor
              (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
            (ComplexShape.up ℤ)).X (t + r))).app (op U)
        ((HomologicalComplex.ιMapBifunctor (underlyingPresheafComplex X A)
          (underlyingPresheafComplex X B)
          (MonoidalCategory.curriedTensor
            (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
          (ComplexShape.up ℤ) t r (t + r) rfl).app (op U)
            (a ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)] b)) :=
  rfl

section PresheafLevel

variable (A Z : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
  (k : ℤ)

/-- **Step one of the comparison, at the presheaf level.** Taking underlying presheaves commutes
with the shift — degreewise it does nothing at all — so the tensor bicomplex built from the
underlying complex of `Z⟦k⟧` agrees with the one built from the shift of the underlying complex
of `Z`. This is that agreement, after passage to total complexes. -/
def mapBifunctorUnderlyingShiftIso :
    HomologicalComplex.mapBifunctor (underlyingPresheafComplex X A)
        (underlyingPresheafComplex X ((CategoryTheory.shiftFunctor
          (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
            k).obj Z))
        (MonoidalCategory.curriedTensor
          (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
        (ComplexShape.up ℤ) ≅
      HomologicalComplex.mapBifunctor (underlyingPresheafComplex X A)
        ((CategoryTheory.shiftFunctor
          (CochainComplex
            (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) ℤ) k).obj
          (underlyingPresheafComplex X Z))
        (MonoidalCategory.curriedTensor
          (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
        (ComplexShape.up ℤ) :=
  letI : (SheafOfModules.forget.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).Additive :=
    SheafOfModules.instAdditivePresheafOfModulesObjFunctorOppositeRingCatIsSheafForget
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  HomologicalComplex₂.total.mapIso
    ((((MonoidalCategory.curriedTensor
        (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
        ).mapBifunctorHomologicalComplex _ _).obj
      (underlyingPresheafComplex X A)).mapIso
        (((SheafOfModules.forget
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapCochainComplexShiftIso k).app Z))
    (ComplexShape.up ℤ)

/-- Step one is the functoriality of the total tensor complex in its second variable, applied
to the comparison between taking underlying presheaves and shifting. Written in this form it is
reached by `HomologicalComplex.ι_mapBifunctorMap`, which is how it is pushed past a summand
inclusion. -/
lemma mapBifunctorUnderlyingShiftIso_hom :
    (mapBifunctorUnderlyingShiftIso X A Z k).hom =
      HomologicalComplex.mapBifunctorMap (𝟙 (underlyingPresheafComplex X A))
        (letI : (SheafOfModules.forget.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).Additive :=
          SheafOfModules.instAdditivePresheafOfModulesObjFunctorOppositeRingCatIsSheafForget
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
         (((SheafOfModules.forget
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapCochainComplexShiftIso k).app Z).hom)
        (MonoidalCategory.curriedTensor
          (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
        (ComplexShape.up ℤ) := by
  simp [mapBifunctorUnderlyingShiftIso, HomologicalComplex.mapBifunctorMap]

/-- **The presheaf-level comparison** `Tot(A' ⊗ (Z⟦k⟧)') ≅ Tot(A' ⊗ Z')⟦k⟧`: step one, which
only renames the second factor, followed by Mathlib's comparison, which carries the sign. -/
def underlyingTensorShiftIso₂ :
    HomologicalComplex.mapBifunctor (underlyingPresheafComplex X A)
        (underlyingPresheafComplex X ((CategoryTheory.shiftFunctor
          (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
            k).obj Z))
        (MonoidalCategory.curriedTensor
          (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
        (ComplexShape.up ℤ) ≅
      (CategoryTheory.shiftFunctor
        (CochainComplex
          (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) ℤ) k).obj
        (HomologicalComplex.mapBifunctor (underlyingPresheafComplex X A)
          (underlyingPresheafComplex X Z)
          (MonoidalCategory.curriedTensor
            (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
          (ComplexShape.up ℤ)) :=
  mapBifunctorUnderlyingShiftIso X A Z k ≪≫
    CochainComplex.mapBifunctorShift₂Iso (underlyingPresheafComplex X A)
      (underlyingPresheafComplex X Z)
      (MonoidalCategory.curriedTensor
        (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)) k

/-- **The presheaf-level comparison on a summand.** On the summand of index `(t, r)` the
comparison is `(t * k).negOnePow` times the inclusion of the summand of index `(t, r + k)`:
the two summands are the same object, and both reindexings of the target are identities, so
the only content is Mathlib's sign. -/
lemma ι_underlyingTensorShiftIso₂_hom_f (t r : ℤ) :
    HomologicalComplex.ιMapBifunctor (underlyingPresheafComplex X A)
        (underlyingPresheafComplex X ((CategoryTheory.shiftFunctor
          (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
            k).obj Z))
        (MonoidalCategory.curriedTensor
          (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
        (ComplexShape.up ℤ) t r (t + r) rfl ≫
          (underlyingTensorShiftIso₂ X A Z k).hom.f (t + r) =
      (t * k).negOnePow •
        HomologicalComplex.ιMapBifunctor (underlyingPresheafComplex X A)
          (underlyingPresheafComplex X Z)
          (MonoidalCategory.curriedTensor
            (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
          (ComplexShape.up ℤ) t (r + k) (t + r + k) (by dsimp; omega) := by
  rw [underlyingTensorShiftIso₂]
  simp only [Iso.trans_hom, HomologicalComplex.comp_f, mapBifunctorUnderlyingShiftIso_hom]
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc]
  dsimp only [CategoryTheory.Functor.comp_obj]
  rw [CochainComplex.ι_mapBifunctorShift₂Iso_hom_f _ _ _ _ t r (t + r) rfl (r + k)
    (t + r + k) rfl rfl]
  simp

end PresheafLevel

/-- **The total tensor-product complex commutes with the shift of its second factor.** The
presheaf-level comparison `underlyingTensorShiftIso₂`, carried across the degreewise
sheafification — which is additive, and so commutes with the shift. -/
def tensorTotalShiftIso₂
    (A Z : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (k : ℤ) :
    tensorTotal X A ((CategoryTheory.shiftFunctor
        (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
          k).obj Z) ≅
      (CategoryTheory.shiftFunctor
        (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) k).obj
        (tensorTotal X A Z) :=
  ((PresheafOfModules.sheafification
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).mapHomologicalComplex
      (ComplexShape.up ℤ)).mapIso (underlyingTensorShiftIso₂ X A Z k) ≪≫
  ((PresheafOfModules.sheafification
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).mapCochainComplexShiftIso k).app _

end AlgebraicGeometry.RingedSite

end
