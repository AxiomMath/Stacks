module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasicoherentTransport

/-!
# The counit of the affine derived Spec–Γ adjunction, from generation

Let `R` be a commutative ring and let `AlgebraicGeometry.derivedTildeQuasicoherentAdjunction` be
the adjunction `derivedTilde R ⊣ derivedGlobalSectionsQuasicoherent R` between `D(R)` and
`D_QCoh(𝒪_{Spec R})` of [Stacks, Tag 06Z0]. An object of `D_QCoh(𝒪_{Spec R})` receives only zero
morphisms from the shifts of `derivedTilde R (R[0]) = 𝒪_{Spec R}[0]` if and only if its derived
global sections vanish, so the orthogonality hypothesis of the affine case of [Stacks, Tag 09IS] is
conservativity of `RΓ(Spec R, -)` on `D_QCoh(𝒪_{Spec R})`. When `derivedTilde R` is fully faithful:

> the counit of the affine derived Spec–Γ adjunction is invertible
> ⟺ `RΓ(Spec R, -)` is conservative on `D_QCoh(𝒪_{Spec R})`
> ⟺ `𝒪_{Spec R}[0]` generates `D_QCoh(𝒪_{Spec R})`, the affine case of [Stacks, Tag 09IS].

## Main results

* `AlgebraicGeometry.rightOrthogonal_shiftClosure_derivedTildeUnit_iff_isZero`: an object of
  `D_QCoh(𝒪_{Spec R})` is right orthogonal to the shifts of `𝒪_{Spec R}[0]` if and only if its
  derived global sections vanish.
* `AlgebraicGeometry.isZero_of_isZero_derivedGlobalSectionsQuasicoherent_of_isIso_counit`: an
  object at which the counit is invertible and whose derived global sections vanish is zero.
* `AlgebraicGeometry.isIso_derivedTildeQuasicoherentAdjunction_counit_app_of_isZero`: if
  `derivedTilde R` is fully faithful and derived global sections is conservative, the counit is
  invertible.
* `AlgebraicGeometry.isIso_derivedTildeQuasicoherentAdjunction_counit_iff_isZero`: if
  `derivedTilde R` is fully faithful, the counit is invertible if and only if derived global
  sections is conservative.
* `AlgebraicGeometry.isIso_derivedTildeQuasicoherentAdjunction_counit_iff_rightOrthogonal`: if
  `derivedTilde R` is fully faithful, the counit is invertible if and only if `𝒪_{Spec R}[0]`
  generates `D_QCoh(𝒪_{Spec R})`.
* `AlgebraicGeometry.essSurj_derivedTilde_of_isZero`: if `derivedTilde R` is fully faithful and
  derived global sections is conservative, `derivedTilde R` is essentially surjective.
* `AlgebraicGeometry.derivedTilde_isEquivalence_of_isIso_unit_of_isZero`: if the unit of
  `AlgebraicGeometry.derivedTildeGlobalSectionsAdjunction` is invertible and derived global
  sections is conservative, `derivedTilde R` is an equivalence.

## References

* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
* [Stacks Project, Tag 09IS](https://stacks.math.columbia.edu/tag/09IS)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated Opposite

universe u

namespace AlgebraicGeometry

variable (R : CommRingCat.{u})

/-! ### Generation and conservativity are the same condition -/

/-- If `RΓ(Spec R, Y)` is zero, then every morphism `derivedTilde R M ⟶ Y` is zero. -/
theorem eq_zero_of_isZero_derivedGlobalSectionsQuasicoherent
    {Y : (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).FullSubcategory}
    (h : IsZero ((derivedGlobalSectionsQuasicoherent R).obj Y))
    {M : DerivedCategory (ModuleCat.{u} R)} (s : (derivedTilde R).obj M ⟶ Y) : s = 0 :=
  ((derivedTildeQuasicoherentAdjunction R).homEquiv M Y).injective (h.eq_of_tgt _ _)

/-- An object `Y` of `D_QCoh(𝒪_{Spec R})` receives only zero morphisms from the shifts of
`derivedTilde R (R[0]) = 𝒪_{Spec R}[0]` if and only if `RΓ(Spec R, Y) = 0`. -/
theorem rightOrthogonal_shiftClosure_derivedTildeUnit_iff_isZero
    (Y : (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).FullSubcategory) :
    ((ofObj fun _ : PUnit.{u + 1} => (derivedTilde R).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
          (ModuleCat.of R R))).shiftClosure ℤ).rightOrthogonal Y ↔
      IsZero ((derivedGlobalSectionsQuasicoherent R).obj Y) := by
  rw [CategoryTheory.Pretriangulated.rightOrthogonal_shiftClosure_ofObj_iff]
  refine ⟨fun hY => ?_, fun h i a f => ?_⟩
  · refine Stacks.Duality.isZero_of_rightOrthogonal_shiftClosure_derivedUnit R _
      ((CategoryTheory.Pretriangulated.rightOrthogonal_shiftClosure_ofObj_iff _ _).2
        fun i a g => ?_)
    have h : ((derivedTildeQuasicoherentAdjunction R).homEquiv _ Y).symm g = 0 :=
      (Preadditive.IsIso.comp_left_eq_zero (((derivedTilde R).commShiftIso a).inv.app
        (Stacks.Duality.singleGenerator (ModuleCat.of R R) i)) _).1 (hY i a _)
    rw [← ((derivedTildeQuasicoherentAdjunction R).homEquiv _ Y).apply_symm_apply g, h,
      Adjunction.homAddEquiv_zero]
  · rw [← cancel_epi (((derivedTilde R).commShiftIso a).hom.app
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))), comp_zero]
    exact eq_zero_of_isZero_derivedGlobalSectionsQuasicoherent R h _

/-! ### The counit from conservativity -/

/-- If the counit of `AlgebraicGeometry.derivedTildeQuasicoherentAdjunction` is invertible at `Y`
and `RΓ(Spec R, Y) = 0`, then `Y = 0`. -/
theorem isZero_of_isZero_derivedGlobalSectionsQuasicoherent_of_isIso_counit
    (Y : (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).FullSubcategory)
    (hc : IsIso ((derivedTildeQuasicoherentAdjunction R).counit.app Y))
    (h : IsZero ((derivedGlobalSectionsQuasicoherent R).obj Y)) :
    IsZero Y :=
  have := hc
  ((derivedTilde R).map_isZero h).of_iso
    (asIso ((derivedTildeQuasicoherentAdjunction R).counit.app Y)).symm

/-- If `derivedTilde R` is fully faithful and every object of `D_QCoh(𝒪_{Spec R})` with vanishing
derived global sections vanishes, then the counit of
`AlgebraicGeometry.derivedTildeQuasicoherentAdjunction` is invertible at every object. -/
theorem isIso_derivedTildeQuasicoherentAdjunction_counit_app_of_isZero
    [(derivedTilde R).Full] [(derivedTilde R).Faithful]
    (hcons : ∀ Y : (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).FullSubcategory,
      IsZero ((derivedGlobalSectionsQuasicoherent R).obj Y) → IsZero Y)
    (E : (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).FullSubcategory) :
    IsIso ((derivedTildeQuasicoherentAdjunction R).counit.app E) := by
  obtain ⟨T, g, δ, hT⟩ :=
    distinguished_cocone_triangle ((derivedTildeQuasicoherentAdjunction R).counit.app E)
  refine (Triangle.isZero₃_iff_isIso₁ _ hT).1 (hcons T ?_)
  refine Triangle.isZero₃_of_isIso₁ _
    ((derivedGlobalSectionsQuasicoherent R).map_distinguished _ hT) ?_
  exact (inferInstance : IsIso ((derivedGlobalSectionsQuasicoherent R).map
    ((derivedTildeQuasicoherentAdjunction R).counit.app E)))

/-- If `derivedTilde R` is fully faithful, the counit of
`AlgebraicGeometry.derivedTildeQuasicoherentAdjunction` is invertible at every object if and only
if every object of `D_QCoh(𝒪_{Spec R})` with vanishing derived global sections vanishes. -/
theorem isIso_derivedTildeQuasicoherentAdjunction_counit_iff_isZero
    [(derivedTilde R).Full] [(derivedTilde R).Faithful] :
    (∀ E : (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).FullSubcategory,
      IsIso ((derivedTildeQuasicoherentAdjunction R).counit.app E)) ↔
    ∀ Y : (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).FullSubcategory,
      IsZero ((derivedGlobalSectionsQuasicoherent R).obj Y) → IsZero Y :=
  ⟨fun hc Y h =>
    isZero_of_isZero_derivedGlobalSectionsQuasicoherent_of_isIso_counit R Y (hc Y) h,
   fun hcons => isIso_derivedTildeQuasicoherentAdjunction_counit_app_of_isZero R hcons⟩

/-- If `derivedTilde R` is fully faithful, the counit of
`AlgebraicGeometry.derivedTildeQuasicoherentAdjunction` is invertible at every object if and only
if every object of `D_QCoh(𝒪_{Spec R})` receiving only zero morphisms from the shifts of
`derivedTilde R (R[0]) = 𝒪_{Spec R}[0]` is zero. -/
theorem isIso_derivedTildeQuasicoherentAdjunction_counit_iff_rightOrthogonal
    [(derivedTilde R).Full] [(derivedTilde R).Faithful] :
    (∀ E : (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).FullSubcategory,
      IsIso ((derivedTildeQuasicoherentAdjunction R).counit.app E)) ↔
    ∀ Y : (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).FullSubcategory,
      ((ofObj fun _ : PUnit.{u + 1} => (derivedTilde R).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
            (ModuleCat.of R R))).shiftClosure ℤ).rightOrthogonal Y → IsZero Y := by
  rw [isIso_derivedTildeQuasicoherentAdjunction_counit_iff_isZero]
  exact forall_congr' fun Y =>
    imp_congr (rightOrthogonal_shiftClosure_derivedTildeUnit_iff_isZero R Y).symm Iff.rfl

/-- If `derivedTilde R` is fully faithful and every object of `D_QCoh(𝒪_{Spec R})` with vanishing
derived global sections vanishes, then `derivedTilde R` is essentially surjective. -/
theorem essSurj_derivedTilde_of_isZero
    [(derivedTilde R).Full] [(derivedTilde R).Faithful]
    (hcons : ∀ Y : (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).FullSubcategory,
      IsZero ((derivedGlobalSectionsQuasicoherent R).obj Y) → IsZero Y) :
    (derivedTilde R).EssSurj where
  mem_essImage E :=
    have := isIso_derivedTildeQuasicoherentAdjunction_counit_app_of_isZero R hcons E
    (derivedTildeQuasicoherentAdjunction R).mem_essImage_of_counit_isIso E

/-- Derived sheafification `D(R) ⥤ D_QCoh(𝒪_{Spec R})` is an equivalence if the unit of
`AlgebraicGeometry.derivedTildeGlobalSectionsAdjunction` is invertible at every object and every
object of `D_QCoh(𝒪_{Spec R})` with vanishing derived global sections vanishes. -/
theorem derivedTilde_isEquivalence_of_isIso_unit_of_isZero
    (hu : ∀ M : DerivedCategory (ModuleCat.{u} R),
      IsIso ((derivedTildeGlobalSectionsAdjunction R).val.unit.app M))
    (hcons : ∀ Y : (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).FullSubcategory,
      IsZero ((derivedGlobalSectionsQuasicoherent R).obj Y) → IsZero Y) :
    (derivedTilde R).IsEquivalence :=
  have hff := derivedTildeFullyFaithfulOfIsIsoUnit R hu
  have := hff.full
  have := hff.faithful
  ⟨hff.faithful, hff.full, essSurj_derivedTilde_of_isZero R hcons⟩

end AlgebraicGeometry

end
