module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.CategoryTheory.Shift.Localization
public import Mathlib.CategoryTheory.Triangulated.Functor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery

/-!
# Descending a tensor product with a K-flat complex to the derived category

Let `F : A ⥤ B ⥤ D` be a bifunctor between additive categories which is additive in each
variable, and let `G` be a cochain complex in `B`. Taking total complexes gives a functor
`Tot(- ⊗ G) : CochainComplex A ℤ ⥤ CochainComplex D ℤ`, and Stacks 06YM descends it to an exact
functor of triangulated categories `K(A) ⥤ K(D)` on homotopy categories.

By Stacks 06YP, if `G` is **K-flat**, meaning that `Tot(K ⊗ G)` is acyclic whenever `K` is
acyclic, then that functor sends quasi-isomorphisms to quasi-isomorphisms, so it descends further
to the derived categories. The descended functor is obtained as
`CategoryTheory.Localization.lift`, hence comes with an *isomorphism*
`Qh ⋙ derivedTensor F G ≅ bifunctorPhiR F G ⋙ Qh` and is determined up to unique isomorphism by
it.

Everything here is stated for an arbitrary bifunctor between arbitrary categories; the derived
tensor product of sheaves of modules on a ringed site (Stacks 06YU) is the case
`F := Stacks.SheafOfModules.Tensor.sheafTensor R`.

## Main definitions

* `Stacks.DerivedTensor.totRight F G` is `Tot(- ⊗ G) : CochainComplex A ℤ ⥤ CochainComplex D ℤ`.
* `Stacks.DerivedTensor.IsKFlat F G` is K-flatness of `G` relative to `F` (Stacks 06Y9/06YN):
  `Tot(K ⊗ G)` is acyclic for every acyclic `K`.
* `Stacks.DerivedTensor.derivedTensor F G` is the induced functor
  `DerivedCategory A ⥤ DerivedCategory D`.
* `Stacks.DerivedTensor.derivedTensorIso F G` is the isomorphism
  `Qh ⋙ derivedTensor F G ≅ bifunctorPhiR F G ⋙ Qh` exhibiting it as that induced functor.
* `Stacks.DerivedTensor.derivedTensorQIso F G` is the resulting isomorphism
  `Q ⋙ derivedTensor F G ≅ totRight F G ⋙ Q` at the level of complexes.

## Main results

* `Stacks.DerivedTensor.acyclic_map`, `Stacks.DerivedTensor.trW_map` and
  `Stacks.DerivedTensor.isInvertedBy_quasiIso` are Stacks 06YP: tensoring with a K-flat complex
  preserves acyclicity, hence preserves the class of quasi-isomorphisms.
* `Stacks.DerivedTensor.derivedTensor` carries a `Functor.CommShift ℤ` and is
  `Functor.IsTriangulated`: it is an exact functor of triangulated categories.
* `Stacks.DerivedTensor.derivedTensorUniq`: any functor on derived categories lifting
  `bifunctorPhiR F G ⋙ Qh` is canonically isomorphic to `derivedTensor F G`.
* `Stacks.DerivedTensor.isKFlat_of_isZero`: a zero complex is K-flat.

## Implementation notes

The commutation-with-shift datum of the homotopy-level functor is Stacks 06YM's
`Stacks.SheafOfModules.Tensor.Reduction.bifunctorXiR`, which is a `def` rather than an `instance`;
it is made a local instance here so that `Functor.IsTriangulated` and the `CommShift` of
composites are found by instance search. The `Functor.IsTriangulated` statement of Stacks 06YM is
phrased with a `letI` of that datum, so recording the local instance by name — rather than
introducing a `letI` fvar — is what makes the two spellings syntactically equal.

The shift datum of the descended functor is Mathlib's `Functor.commShiftOfLocalization`.

## References

* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
* [Stacks Project, Tag 06YN](https://stacks.math.columbia.edu/tag/06YN)
* [Stacks Project, Tag 06YP](https://stacks.math.columbia.edu/tag/06YP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.SheafOfModules.Tensor.Reduction

universe v₁ u₁ v₂ u₂ v₃ u₃

attribute [local instance] Stacks.SheafOfModules.Tensor.Reduction.bifunctorXiR

namespace Stacks.DerivedTensor

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {D : Type u₃} [Category.{v₃} D] [Abelian A] [Preadditive B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
  (G : CochainComplex B ℤ)

/-- `Tot(- ⊗ G)`, the total complex of the double complex `(p, q) ↦ F(K^p, G^q)` with the Koszul
sign convention, as a functor of the left factor. This is Stacks 06YM's bifunctor on complexes
with its right argument fixed at `G`. -/
abbrev totRight : CochainComplex A ℤ ⥤ CochainComplex D ℤ :=
  (F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)).flip.obj G

/-- `G` is **K-flat** relative to the bifunctor `F` when `Tot(K ⊗ G)` is acyclic for every
acyclic cochain complex `K`. This is Stacks 06YN, read for the bifunctor `F` in place of a
tensor product of sheaves of modules. -/
class IsKFlat : Prop where
  /-- Tensoring an acyclic complex with a K-flat complex gives an acyclic complex. -/
  acyclic_totRight : ∀ K : CochainComplex A ℤ, K.Acyclic → ((totRight F G).obj K).Acyclic

/-- A zero complex is K-flat: tensoring with it gives a zero complex, because
`Tot(K ⊗ -)` is additive in its second argument. -/
theorem isKFlat_of_isZero (hG : IsZero G) : IsKFlat F G where
  acyclic_totRight K _ := by
    have := map₂HomologicalComplex_obj_additive F K
    exact HomologicalComplex.acyclic_of_isZero _
      (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj K).map_isZero hG)

/-- Stacks 06YM's descended functor `K(A) ⥤ K(D)` is an exact functor of triangulated
categories, for the commutation-with-shift datum
`Stacks.SheafOfModules.Tensor.Reduction.bifunctorXiR`. -/
instance isTriangulated_bifunctorPhiR : (bifunctorPhiR F G).IsTriangulated :=
  bifunctorPhiR_isTriangulated F G

variable {F G}

/-- If `G` is K-flat then the homotopy-level functor `Tot(- ⊗ G)` sends acyclic objects of `K(A)`
to acyclic objects of `K(D)`. -/
lemma acyclic_map [IsKFlat F G] (X : HomotopyCategory A (ComplexShape.up ℤ))
    (hX : HomotopyCategory.subcategoryAcyclic A X) :
    HomotopyCategory.subcategoryAcyclic D ((bifunctorPhiR F G).obj X) := by
  obtain ⟨K, ⟨e⟩⟩ : ∃ K : CochainComplex A ℤ,
      Nonempty ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K ≅ X) :=
    ⟨X.as, ⟨Iso.refl _⟩⟩
  have hK : K.Acyclic := by
    rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
    exact (HomotopyCategory.subcategoryAcyclic A).prop_of_iso e.symm hX
  refine (HomotopyCategory.subcategoryAcyclic D).prop_of_iso
    ((bifunctorPhiR F G).mapIso e) ?_
  refine (HomotopyCategory.subcategoryAcyclic D).prop_of_iso
    ((bifunctorPhiRFactors F G).app K).symm ?_
  exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2
    (IsKFlat.acyclic_totRight K hK)

/-- If `G` is K-flat then the homotopy-level functor `Tot(- ⊗ G)` preserves the class of
morphisms whose cone is acyclic. -/
lemma trW_map [IsKFlat F G] {X Y : HomotopyCategory A (ComplexShape.up ℤ)} (f : X ⟶ Y)
    (hf : (HomotopyCategory.subcategoryAcyclic A).trW f) :
    (HomotopyCategory.subcategoryAcyclic D).trW ((bifunctorPhiR F G).map f) := by
  rw [ObjectProperty.trW_iff] at hf
  obtain ⟨Z, g, h, hT, hZ⟩ := hf
  exact ObjectProperty.trW.mk _ ((bifunctorPhiR F G).map_distinguished _ hT)
    (acyclic_map Z hZ)

section

variable [HasDerivedCategory A] [HasDerivedCategory D]

omit [HasDerivedCategory A] in
/-- If `G` is K-flat then `Tot(- ⊗ G)` followed by the localisation inverts the quasi-isomorphisms
of `K(A)`, so it factors through the derived category. -/
lemma isInvertedBy_quasiIso [IsKFlat F G] :
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).IsInvertedBy
      (bifunctorPhiR F G ⋙ DerivedCategory.Qh) := fun _ _ f hf => by
  rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic] at hf
  exact Localization.inverts DerivedCategory.Qh
    (HomotopyCategory.subcategoryAcyclic D).trW _ (trW_map f hf)

variable (F G)

/-- **The derived tensor product with a K-flat complex.** The functor
`DerivedCategory A ⥤ DerivedCategory D` induced by `Tot(- ⊗ G)` for a K-flat complex `G`,
obtained from the universal property of the localisation `Qh` at the quasi-isomorphisms. -/
def derivedTensor [IsKFlat F G] : DerivedCategory A ⥤ DerivedCategory D :=
  Localization.lift (bifunctorPhiR F G ⋙ DerivedCategory.Qh) isInvertedBy_quasiIso
    DerivedCategory.Qh

/-- `derivedTensor F G` lifts `Tot(- ⊗ G)` through the localisation. -/
instance liftingDerivedTensor [IsKFlat F G] :
    Localization.Lifting DerivedCategory.Qh (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
      (bifunctorPhiR F G ⋙ DerivedCategory.Qh) (derivedTensor F G) := by
  dsimp only [derivedTensor]
  infer_instance

/-- The isomorphism exhibiting `derivedTensor F G` as the functor induced by `Tot(- ⊗ G)`: the
square relating the two localisations commutes up to a canonical isomorphism. -/
def derivedTensorIso [IsKFlat F G] :
    DerivedCategory.Qh ⋙ derivedTensor F G ≅ bifunctorPhiR F G ⋙ DerivedCategory.Qh :=
  Localization.Lifting.iso DerivedCategory.Qh
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) _ _

/-- The commutation-with-shift datum of `derivedTensor F G`, descended from Stacks 06YM's datum
`Stacks.SheafOfModules.Tensor.Reduction.bifunctorXiR` through the localisation. -/
instance commShiftDerivedTensor [IsKFlat F G] : (derivedTensor F G).CommShift ℤ :=
  Functor.commShiftOfLocalization DerivedCategory.Qh
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ℤ
    (bifunctorPhiR F G ⋙ DerivedCategory.Qh) (derivedTensor F G)

/-- The lifting isomorphism is compatible with the shifts. -/
instance commShiftDerivedTensorIso [IsKFlat F G] :
    NatTrans.CommShift (derivedTensorIso F G).hom ℤ := by
  dsimp only [derivedTensorIso]
  infer_instance

/-- **`- ⊗ G` is an exact functor of triangulated categories.** For sheaves of modules on a ringed
site this is the case `F := Stacks.SheafOfModules.Tensor.sheafTensor R`. -/
@[stacks 06YU "exact functor of triangulated categories"]
instance isTriangulated_derivedTensor [IsKFlat F G] : (derivedTensor F G).IsTriangulated :=
  Functor.isTriangulated_of_precomp_iso (derivedTensorIso F G)

/-- **Uniqueness of the construction.** Any functor on derived categories that lifts
`Tot(- ⊗ G)` through the localisation is canonically isomorphic to `derivedTensor F G`. -/
def derivedTensorUniq [IsKFlat F G] (L : DerivedCategory A ⥤ DerivedCategory D)
    [Localization.Lifting DerivedCategory.Qh (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
      (bifunctorPhiR F G ⋙ DerivedCategory.Qh) L] :
    L ≅ derivedTensor F G :=
  Localization.liftNatIso DerivedCategory.Qh (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
    (bifunctorPhiR F G ⋙ DerivedCategory.Qh) (bifunctorPhiR F G ⋙ DerivedCategory.Qh)
    L (derivedTensor F G) (Iso.refl _)

/-- **The derived tensor product is computed by the total tensor complex.** On the image of a
cochain complex in the derived category, `derivedTensor F G` is `Tot(- ⊗ G)`, naturally in the
complex. -/
def derivedTensorQIso [IsKFlat F G] :
    DerivedCategory.Q ⋙ derivedTensor F G ≅ totRight F G ⋙ DerivedCategory.Q :=
  Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (derivedTensorIso F G) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (bifunctorPhiRFactors F G) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso D)

/-- The value of `derivedTensor F G` on the image of a cochain complex `K` is the image of the
total complex `Tot(K ⊗ G)`. -/
def derivedTensorObjIso [IsKFlat F G] (K : CochainComplex A ℤ) :
    (derivedTensor F G).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((totRight F G).obj K) :=
  (derivedTensorQIso F G).app K

end

end Stacks.DerivedTensor

end
