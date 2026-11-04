module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExteriorSymmetricConstruction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.Sectionwise
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UnitFinitePresentationSite

/-!
# Degree zero of the symmetric algebra of a sheaf of modules

The degree-zero homogeneous piece of the symmetric algebra of a sheaf of modules is the
structure sheaf, for *every* sheaf of modules: a degree-zero element of `Sym_R(M)` is the image
of a unique scalar. This is the symmetric counterpart of
`SheafOfModules.sheafifiedTensorPieceZeroIso` and
`SheafOfModules.sheafifiedExteriorPieceZeroIso`, which were already available while the
symmetric one was not.

Together with the global presentation of the structure sheaf,
`Stacks.SheafOfModules.Site.unitPresentation`, the degree-zero identification gives a
presentation of `Sym⁰` of an arbitrary sheaf of modules, which is the degree-zero case of
clause (5) of Tag 01CK — the one degree the presentation sequences of Tag 01CJ, which start at
degree one, cannot reach.

## Main definitions

* `PresheafOfModules.symmetricAlgebraPieceZeroIso`: the degree-zero piece of the sectionwise
  symmetric algebra is the structure presheaf.
* `SheafOfModules.sheafifiedSymmetricPieceZeroIso`: **the degree-zero identification**
  `Sym⁰(F) ≅ O`.
* `SheafOfModules.sheafifiedSymmetricPieceZeroPresentation`: a global presentation of
  `Sym⁰(F)`, transported from `Stacks.SheafOfModules.Site.unitPresentation`.

## Main results

* `SymmetricAlgebra.algebraMap_algebraMapInv_of_mem_symmetricPowerInt_zero`: a degree-zero
  element of the symmetric algebra is the image of the scalar that
  `SymmetricAlgebra.algebraMapInv` names.
* `SymmetricAlgebra.algebraMapInv_mapₛₗ_of_mem_symmetricPowerInt_zero`: **base change on degree
  zero is the ring homomorphism itself**, which is what makes the degree-zero piece of the
  sectionwise symmetric algebra the structure presheaf *naturally*.

## Implementation notes

**No `@[stacks]` tag.** The degree-zero identification is part of the data of the symmetric
algebra rather than a numbered clause of a tag, exactly as for its tensor and exterior
counterparts.

## References

* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite

universe v u w

/-! ## Degree zero of the symmetric algebra of a module -/

namespace SymmetricAlgebra

variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

/-- The image of a scalar lies in degree zero. -/
theorem algebraMap_mem_symmetricPowerInt_zero (r : R) :
    algebraMap R (SymmetricAlgebra R M) r ∈ SymPow.symmetricPowerInt 0 R M :=
  (SymPow.symmetricPowerInt_zero_eq_one R M).symm ▸ Submodule.mem_one.mpr ⟨r, rfl⟩

/-- A degree-zero element of the symmetric algebra is the image of a scalar, and
`SymmetricAlgebra.algebraMapInv` names that scalar. -/
theorem algebraMap_algebraMapInv_of_mem_symmetricPowerInt_zero {x : SymmetricAlgebra R M}
    (hx : x ∈ SymPow.symmetricPowerInt 0 R M) :
    algebraMap R (SymmetricAlgebra R M) (algebraMapInv x) = x := by
  rw [SymPow.symmetricPowerInt_zero_eq_one] at hx
  obtain ⟨r, rfl⟩ := Submodule.mem_one.1 hx
  exact congrArg (algebraMap R (SymmetricAlgebra R M)) (algebraMap_leftInverse M r)

/-- **Base change on degree zero is the ring homomorphism itself**, read through
`SymmetricAlgebra.algebraMapInv`. This is what makes the degree-zero piece of the sectionwise
symmetric algebra the structure presheaf. -/
theorem algebraMapInv_mapₛₗ_of_mem_symmetricPowerInt_zero {S : Type*} [CommRing S] {N : Type*}
    [AddCommGroup N] [Module S N] (φ : R →+* S) (u : M →ₛₗ[φ] N) {x : SymmetricAlgebra R M}
    (hx : x ∈ SymPow.symmetricPowerInt 0 R M) :
    algebraMapInv (mapₛₗ φ u x) = φ (algebraMapInv x) := by
  conv_lhs => rw [← algebraMap_algebraMapInv_of_mem_symmetricPowerInt_zero R M hx]
  rw [mapₛₗ_algebraMap, algebraMap_leftInverse]

end SymmetricAlgebra

/-! ## Degree zero of the sectionwise symmetric algebra -/

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  (F : PresheafOfModules.{w} (O ⋙ forget₂ _ RingCat))

/-- **Degree zero of the sectionwise symmetric algebra, on sections, is the base ring.** A
degree-zero element is the image of a unique scalar, which `SymmetricAlgebra.algebraMapInv`
names. -/
noncomputable def symmetricAlgebraPieceZeroEquiv (X : Cᵒᵖ) :
    (symPowInt (0 : ℤ) F).obj X ≃ₗ[(O ⋙ forget₂ _ RingCat).obj X]
      ((O ⋙ forget₂ _ RingCat).obj X) where
  toFun x := SymmetricAlgebra.algebraMapInv (symPowIntVal x)
  map_add' x y := map_add _ _ _
  map_smul' r x := by
    change SymmetricAlgebra.algebraMapInv (r • symPowIntVal x) = _
    rw [map_smul]
    rfl
  invFun r := ⟨algebraMap _ _ r, SymmetricAlgebra.algebraMap_mem_symmetricPowerInt_zero _ _ r⟩
  left_inv x := Subtype.ext
    (SymmetricAlgebra.algebraMap_algebraMapInv_of_mem_symmetricPowerInt_zero _ _
      (x : ↥(SymPow.symmetricPowerInt (0 : ℤ) _ _)).2)
  right_inv r := SymmetricAlgebra.algebraMap_leftInverse _ r

/-- **The degree-zero piece of the sectionwise symmetric algebra is the structure presheaf.**
Naturality is `SymmetricAlgebra.algebraMapInv_mapₛₗ_of_mem_symmetricPowerInt_zero`: base change
on degree zero is the ring homomorphism. -/
noncomputable def symmetricAlgebraPieceZeroIso :
    symPowInt (0 : ℤ) F ≅ unit (O ⋙ forget₂ CommRingCat.{w} RingCat.{w}) := by
  refine isoMk (fun X => (symmetricAlgebraPieceZeroEquiv F X).toModuleIso) ?_
  intro X Y f
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  exact SymmetricAlgebra.algebraMapInv_mapₛₗ_of_mem_symmetricPowerInt_zero _ _ _
    (F.restrictₛₗ f) (x : ↥(SymPow.symmetricPowerInt (0 : ℤ) _ _)).2

/-- The degree-zero identification of the sectionwise symmetric algebra, on sections. -/
@[simp]
theorem symmetricAlgebraPieceZeroIso_hom_apply (X : Cᵒᵖ)
    (x : (symPowInt (0 : ℤ) F).obj X) :
    Hom.app (symmetricAlgebraPieceZeroIso F).hom X x =
      SymmetricAlgebra.algebraMapInv (symPowIntVal x) := rfl

end PresheafOfModules

namespace SheafOfModules

section Free

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

variable [HasSheafify J AddCommGrpCat.{w}]

end Free

/-! ## Degree zero of the symmetric algebra of a sheaf of modules -/

section Sheafified

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (F : SheafOfModules.{w} (toRingCat J Osharp))

/-- **The degree-zero identification `Sym⁰(F) ≅ O`**: degree zero of the sectionwise symmetric
algebra is the structure presheaf, whose sheafification is the structure sheaf. Unlike the
degree-one identification `SheafOfModules.sheafifiedSymmetricPieceOneIso`, which is `F` itself,
this one is independent of `F`. -/
noncomputable def sheafifiedSymmetricPieceZeroIso :
    (sheafifiedSymmetricAlgebra J F).piece 0 ≅ SheafOfModules.unit (toRingCat J Osharp) :=
  (PresheafOfModules.sheafification (𝟙 (toRingCat J Osharp).obj)).mapIso
      (PresheafOfModules.symmetricAlgebraPieceZeroIso F.val) ≪≫
    PresheafOfModules.sheafifyCounitIso (𝟙 (toRingCat J Osharp).obj)
      (SheafOfModules.unit (toRingCat J Osharp))

/-- **A global presentation of `Sym⁰(F)`, for an arbitrary sheaf of modules `F`.** This is the
degree-zero case of clause (5) of Tag 01CK: the presentation sequences of Tag 01CJ exist only in
degrees `≥ 1`, and in degree zero the symmetric piece is the structure sheaf. -/
noncomputable def sheafifiedSymmetricPieceZeroPresentation [HasSheafify J AddCommGrpCat.{w}] :
    ((sheafifiedSymmetricAlgebra J F).piece 0).Presentation :=
  Presentation.ofIsIso (sheafifiedSymmetricPieceZeroIso J F).inv
    Stacks.SheafOfModules.Site.unitPresentation

end Sheafified

end SheafOfModules

end
