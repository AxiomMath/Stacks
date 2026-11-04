module

public import StacksFrontier.AlgebraicGeometry.Crystalline.FirstOrderIdealBraidedSections
public import StacksFrontier.AlgebraicGeometry.Crystalline.SecondOrderIdealBraidedSections
public import StacksFrontier.CategoryTheory.Monoidal.ReseatConstraints

/-!
# The symmetry constraint on local pure tensors, and the canonical maps of [Stacks, Tag 07J6]

`Crystalline.monoidalCategorySchemeModules` is the monoidal structure on the modules over a
scheme whose tensor product is the sheafification of the objectwise tensor product; it is
obtained from the localized structure by `CategoryTheory.MonoidalCategory.reseat`, and its
braiding `Crystalline.braidedCategorySchemeModules` is the localized braiding conjugated by the
re-seating isomorphism.  This module proves that this braiding **exchanges the two factors of a
local pure tensor**, `schemeModules_braiding_tmul`, which no earlier file of the library could:
earlier computations of the canonical maps of [Stacks, Tag 07J6] were carried out after
precomposing with the braiding, to cancel it.

With that rule, the two canonical maps of the tag are computed on local pure tensors in their
own order:

* `firstOrderThickeningTensorInr_projectionFormulaMap_tmul`: `F_T` tensored with the inclusion of
  the ideal of the diagonal, followed by the projection-formula map at `p₀`, carries `x ⊗ ω` to
  `(0, ω) · p₀^* x`;
* `secondOrderThickeningTensorTopInr_projectionFormulaMap_tmul`: the degree-two analogue carries
  `x ⊗ η` to `(0, 0, 0, η) · q₀^* x`.

## Main results

* `CategoryTheory.MonoidalCategory.reseatBraided_braiding_hom` — the braiding of a re-seated
  structure is the given braiding conjugated by the re-seating isomorphism.
* `SheafOfModules.sheafTensor_braiding_hom` — the braiding of the re-seated tensor product of
  sheaves of modules is the sheafification of the braiding of presheaves of modules.
* `Crystalline.schemeModules_braiding_tmul` — **the braiding exchanges the two factors of a local
  pure tensor.**

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
-/

@[expose] public section

open CategoryTheory MonoidalCategory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

universe v u

namespace CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {T : C ⥤ C ⥤ C} {U : C}

/-- **The braiding of a re-seated monoidal structure** is the given braiding conjugated by the
re-seating isomorphism `X ⊗ Y ≅ (T.obj X).obj Y`. -/
alias reseatBraided_braiding_hom := CategoryTheory.MonoidalCategory.reseat_braiding

/-- The braiding of the re-seated symmetric structure, as for
`CategoryTheory.MonoidalCategory.reseatBraided_braiding_hom`. -/
alias reseatSymmetric_braiding_hom := CategoryTheory.MonoidalCategory.reseatSymmetric_braiding

end CategoryTheory.MonoidalCategory

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v}) [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

attribute [local instance] Stacks.SheafOfModules.Tensor.ringSheafPresheafMonoidalCategory
  _root_.SheafOfModules.monoidalCategory
  _root_.SheafOfModules.sheafification_monoidal _root_.SheafOfModules.symmetricCategory

/-- The braiding of presheaves of modules at the ring-sheaf spelling. -/
@[instance_reducible]
noncomputable def presheafBraidedRingSheaf :
    BraidedCategory (PresheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj) :=
  (inferInstance :
    BraidedCategory (PresheafOfModules.{max u v} (R.obj ⋙ forget₂ CommRingCat RingCat)))

attribute [local instance] presheafBraidedRingSheaf

/-- **The braiding of the re-seated tensor product of sheaves of modules is the sheafification of
the braiding of the underlying presheaves of modules.**  The re-seated braiding is the localized
one conjugated by `SheafOfModules.sheafTensorIso`, and sheafification is a braided functor into
the localized structure (`CategoryTheory.Localization.Monoidal.β_hom_app`). -/
theorem sheafTensor_braiding_hom
    (M N : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    (@BraidedCategory.braiding _ _ (monoidalCategorySheafTensor R)
      (symmetricCategorySheafTensor R).toBraidedCategory M N).hom =
    ((PresheafOfModules.sheafification
      (R := Stacks.SheafOfModules.Tensor.ringSheaf (R))
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (R)).obj))).map
      (β_ ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj M)
        ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj N)).hom := by
  rw [symmetricCategorySheafTensor, reseatSymmetric_braiding_hom]
  show (sheafTensorIso R M N).inv ≫ (β_ M N).hom ≫ (sheafTensorIso R N M).hom = _
  let : (J.W.inverseImage (PresheafOfModules.toPresheaf
      (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).IsMonoidal :=
    Stacks.SheafOfModules.isMonoidal_localIso (𝒪 := R.obj)
  have hb : (β_ (((PresheafOfModules.sheafification
          (R := Stacks.SheafOfModules.Tensor.ringSheaf (R))
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (R)).obj))).obj
        ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj M))
      (((PresheafOfModules.sheafification
          (R := Stacks.SheafOfModules.Tensor.ringSheaf (R))
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (R)).obj))).obj
        ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj N))).hom =
      Functor.LaxMonoidal.μ ((PresheafOfModules.sheafification
          (R := Stacks.SheafOfModules.Tensor.ringSheaf (R))
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (R)).obj)))
          ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj M)
          ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj N) ≫
        ((PresheafOfModules.sheafification
          (R := Stacks.SheafOfModules.Tensor.ringSheaf (R))
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (R)).obj))).map
          (β_ ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj M)
            ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj N)).hom ≫
        Functor.OplaxMonoidal.δ ((PresheafOfModules.sheafification
          (R := Stacks.SheafOfModules.Tensor.ringSheaf (R))
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (R)).obj)))
          ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj N)
          ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj M) :=
    Localization.Monoidal.β_hom_app
      (L := PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj))
      (W := J.W.inverseImage (PresheafOfModules.toPresheaf
        (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)) (ε := Iso.refl _)
      ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj M)
      ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj N)
  have hn := BraidedCategory.braiding_naturality (counitIso R M).inv (counitIso R N).inv
  simp only [sheafTensorIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    tensorIso_hom, tensorIso_inv, Functor.Monoidal.μIso_hom, Functor.Monoidal.μIso_inv,
    Category.assoc]
  rw [← reassoc_of% hn, tensorHom_comp_tensorHom_assoc, Iso.hom_inv_id, Iso.hom_inv_id,
    tensorHom_id, id_whiskerRight, Category.id_comp, hb, Category.assoc, Category.assoc,
    Functor.Monoidal.δ_μ, Category.comp_id, Functor.Monoidal.δ_μ_assoc]

end SheafOfModules

namespace Crystalline

attribute [local instance] monoidalCategorySchemeModules braidedCategorySchemeModules

/-- **The symmetry constraint of `Mod(𝒪_X)` exchanges the two factors of a local pure tensor**,
for the monoidal structure `Crystalline.monoidalCategorySchemeModules` on the modules over a
scheme.  The braiding is the sheafification of the braiding of presheaves of modules
(`SheafOfModules.sheafTensor_braiding_hom`), and the unit of the sheafification is natural. -/
theorem schemeModules_braiding_tmul (X : Scheme.{u}) (M N : X.Modules) (U : (Opens X)ᵒᵖ)
    (a : M.val.obj U) (b : N.val.obj U) :
    (β_ M N).hom.val.app U (Stacks.PullbackTensorCoherence.tmul X.toRingedSpace M N U a b) =
      Stacks.PullbackTensorCoherence.tmul X.toRingedSpace N M U b a := by
  let := Stacks.SheafOfModules.Tensor.ringSheafPresheafMonoidalCategory X.sheaf
  let := SheafOfModules.presheafBraidedRingSheaf X.sheaf
  have h := SheafOfModules.sheafTensor_braiding_hom X.sheaf M N
  have hu : ∀ x, (((PresheafOfModules.sheafification
          (R := Stacks.SheafOfModules.Tensor.ringSheaf (X.sheaf))
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (X.sheaf)).obj))).map
        (β_ ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).obj M)
          ((SheafOfModules.forget
            (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).obj N)).hom).val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj)).unit.app
            ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).obj M ⊗
              (SheafOfModules.forget
                (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).obj N)).app U x) =
      ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj)).unit.app
            ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).obj N ⊗
              (SheafOfModules.forget
                (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).obj M)).app U
        ((β_ ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).obj M)
          ((SheafOfModules.forget
            (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).obj N)).hom.app U x) :=
    fun x ↦ (congrArg (fun φ ↦ φ.app U x)
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj)).unit.naturality
        (β_ ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).obj M)
          ((SheafOfModules.forget
            (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).obj N)).hom)).symm
  refine (congrArg (fun φ ↦ φ.val.app U
    (Stacks.PullbackTensorCoherence.tmul X.toRingedSpace M N U a b)) h).trans ?_
  exact hu (a ⊗ₜ b)

variable (T : DividedPowerScheme.{u}) (Y : Scheme.{u}) (f : T.scheme ⟶ Y) (N : T.scheme.Modules)

/-- **The degree-one canonical map of [Stacks, Tag 07J6] on a local pure tensor, in its own
order**: `N` tensored with the inclusion `ω ↦ (0, ω)` of the ideal of the diagonal, followed by
the projection-formula map at `p₀`, carries `x ⊗ ω` to `(0, ω) · p₀^* x`. -/
theorem firstOrderThickeningTensorInr_projectionFormulaMap_tmul (W : (Opens ↑T.scheme)ᵒᵖ)
    (x : N.val.obj W) (ω : (dpDifferentialsSheaf T Y f).val.obj W) :
    (firstOrderThickeningProjectionFormulaMap T Y f N).val.app W
        ((firstOrderThickeningTensorInr T Y f N).val.app W
          (Stacks.PullbackTensorCoherence.tmul T.scheme.toRingedSpace N
            (dpDifferentialsSheaf T Y f) W x ω)) =
      firstOrderIdealScalar T Y f W ω •
        Stacks.RingedSpace.pullbackUnit
          (firstOrderThickeningProjHom T Y f).toLRSHom.toShHom N W x := by
  have h := congrArg (fun φ ↦ φ.val.app W
      (Stacks.PullbackTensorCoherence.tmul T.scheme.toRingedSpace N
        (dpDifferentialsSheaf T Y f) W x ω))
    (whiskerLeft_inrSheaf_comp_firstOrderThickeningProjectionFormulaMap T Y f N)
  refine h.trans ?_
  refine (Stacks.SheafOfModules.comp_val_app_apply _ _ W _).trans ?_
  rw [schemeModules_braiding_tmul]
  exact firstOrderBraidedProjectionFormula_tmul T Y f N W ω x

/-- **The degree-two canonical map of [Stacks, Tag 07J6] on a local pure tensor, in its own
order**: `N` tensored with the inclusion `η ↦ (0, 0, 0, η)` of the top summand of `𝒪_{T''}`,
followed by the projection-formula map at `q₀`, carries `x ⊗ η` to `(0, 0, 0, η) · q₀^* x`. -/
theorem secondOrderThickeningTensorTopInr_projectionFormulaMap_tmul (W : (Opens ↑T.scheme)ᵒᵖ)
    (x : N.val.obj W) (η : (dpSecondExteriorPower T Y f).val.obj W) :
    (secondOrderThickeningProjectionFormulaMap T Y f N).val.app W
        ((secondOrderThickeningTensorTopInr T Y f N).val.app W
          (Stacks.PullbackTensorCoherence.tmul T.scheme.toRingedSpace N
            (dpSecondExteriorPower T Y f) W x η)) =
      secondOrderIdealScalar T Y f W η •
        Stacks.RingedSpace.pullbackUnit
          (secondOrderThickeningQ₀Hom T Y f).toLRSHom.toShHom N W x := by
  have h := congrArg (fun φ ↦ φ.val.app W
      (Stacks.PullbackTensorCoherence.tmul T.scheme.toRingedSpace N
        (dpSecondExteriorPower T Y f) W x η))
    (whiskerLeft_topInrSheaf_comp_secondOrderThickeningProjectionFormulaMap T Y f N)
  refine h.trans ?_
  refine (Stacks.SheafOfModules.comp_val_app_apply _ _ W _).trans ?_
  rw [schemeModules_braiding_tmul]
  exact secondOrderBraidedProjectionFormula_tmul T Y f N W η x

end Crystalline

end
