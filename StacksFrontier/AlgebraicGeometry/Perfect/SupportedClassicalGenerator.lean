module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Perfect.ClassicalGeneratorOfPerfectComplexes
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.SupportedDirectSums
public import StacksFrontier.Homology.DerivedCategory.Bridge.Basic
public import StacksFrontier.Homology.Perfect.ModelIndependence
public import StacksFrontier.Homology.Perfect.Characterizing
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.SupportedPerfectGenerator

/-!
# A perfect generator of `D_{QCoh,T}(𝒪_X)` classically generates `D_{perf,T}(𝒪_X)`

[Stacks, Remark 0GEG]: let `X` be a quasi-compact and quasi-separated scheme and `T ⊆ X` a closed
subset with `X ∖ T` quasi-compact. `D_{QCoh,T}(𝒪_X)` has direct sums; it has a perfect object `G`
generating it ([Stacks, Tag 0A9A]); and any such `G` is a classical generator of
`D_{perf,T}(𝒪_X)`, which follows from the direct sums, [Stacks, Tag 0A9B] and
[Derived Categories, Tag 09SR]. This is the supported analogue of [Stacks, Remark 0GEF],
`PerfectClassicalGenerator.triangEnvelope_eq_perfectObjects_of_isWeakTriangulatedGenerator` in the
namespace `Stacks.Duality`.

All declarations below are in the namespace `Stacks.Duality.SupportedClassicalGenerator`.

## Main definitions

* `perfectSupported`: `D_{perf,T}(𝒪_X)` as a property of the objects of `D_{QCoh,T}(𝒪_X)`.
* `supportedModelEquiv`: the comparison of `D_{QCoh,T}(𝒪_X)` at two models of the derived
  category, a triangulated equivalence.

## Main results

* `hasCoproducts_and_exists_perfect_generator_and_triangEnvelope_eq_perfectSupported`:
  **[Stacks, Remark 0GEG]**, all three assertions, at an arbitrary model.
* `triangEnvelope_eq_perfectSupported_of_isWeakTriangulatedGenerator`: the classical generation.
* `exists_perfectSupported_isWeakTriangulatedGenerator`: the existence of a perfect generator.

## Implementation notes

**The model.** Compactness and [Stacks, Tag 09SR] need direct sums indexed by the morphism
universe, which exist only at the locally small model `SheafOfModules.hasDerivedCategory`; that is
where the argument runs (`..._locallySmall`). The statements of the remark do not depend on the
model: `supportedModelEquiv` restricts `StacksDraft.DerivedModel.modelEquiv` to `D_{QCoh,T}`, it
is triangulated, and it preserves perfectness (`isPerfect_supportedModelEquiv_functor_obj_iff`) and
weak generators (`isWeakTriangulatedGenerator_singleton_obj_of_isEquivalence`), so both the
classical generation and the existence are transported to an arbitrary model.

**Which part of [Stacks, Tag 0A9B] is used.** Only *perfect ⟹ compact* in `D_{QCoh,T}(𝒪_X)`
(`isCompactObject_of_isPerfect_quasiCoherentSupported`); `⟨G⟩ ≤ D_{perf,T}` comes from the
thickness of the perfect objects, as in the proof of [Stacks, Remark 0GEF].

## References

* [Stacks Project, Tag 0GEG](https://stacks.math.columbia.edu/tag/0GEG)
* [Stacks Project, Tag 0A9A](https://stacks.math.columbia.edu/tag/0A9A)
* [Stacks Project, Tag 0A9B](https://stacks.math.columbia.edu/tag/0A9B)
* [Stacks Project, Tag 09SR](https://stacks.math.columbia.edu/tag/09SR)
* [Stacks Project, Tag 0GEF](https://stacks.math.columbia.edu/tag/0GEF)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.ObjectProperty StacksDraft.DerivedModel
open scoped ZeroObject

universe w z u

namespace Stacks.Duality.SupportedClassicalGenerator

/-! ### Weak generators along an equivalence -/

section Generator

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  [HasShift C ℤ] [HasShift D ℤ] (F : C ⥤ D) [F.IsEquivalence] [F.CommShift ℤ]

/-- **A weak generator is carried to a weak generator by an equivalence commuting with the
shift.** If `K` is a nonzero object of `D`, then `F⁻¹ K` is nonzero, so it receives a nonzero
morphism `G ⟶ (F⁻¹ K)⟦n⟧`, whose image under `F` followed by the identifications
`F((F⁻¹ K)⟦n⟧) ≅ (F F⁻¹ K)⟦n⟧ ≅ K⟦n⟧` is a nonzero morphism `F G ⟶ K⟦n⟧`. -/
theorem isWeakTriangulatedGenerator_singleton_obj_of_isEquivalence {G : C}
    (hG : (ObjectProperty.singleton G).IsWeakTriangulatedGenerator) :
    (ObjectProperty.singleton (F.obj G)).IsWeakTriangulatedGenerator := by
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint F
  rw [isWeakTriangulatedGenerator_iff] at hG ⊢
  intro K hK
  obtain ⟨E, hE, n, f, hf⟩ :=
    hG _ fun h => hK (IsZero.of_full_of_faithful_of_isZero F.inv K h)
  obtain rfl : G = E := (ObjectProperty.singleton_iff G E).1 hE
  let i : F.obj ((F.inv.obj K)⟦n⟧) ≅ K⟦n⟧ :=
    (F.commShiftIso n).app _ ≪≫ (shiftFunctor D n).mapIso (F.asEquivalence.counitIso.app K)
  refine ⟨F.obj G, (ObjectProperty.singleton_iff _ _).2 rfl, n, F.map f ≫ i.hom,
    fun h0 => hf ?_⟩
  have hmap : F.map f = 0 := by
    rwa [← cancel_mono i.hom, zero_comp]
  exact F.map_injective (by rw [hmap, Functor.map_zero])

end Generator

/-! ### `D_{QCoh,T}(𝒪_X)` does not depend on the model of the derived category -/

section Model

variable (X : Scheme.{u}) (T : Set X)
  (h₁ : HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf))
  (h₂ : HasDerivedCategory.{z} (SheafOfModules.{u} X.ringCatSheaf))

/-- **Membership in `D_{QCoh,T}(𝒪_X)` is independent of the model**: an object of the derived
category at one model has quasi-coherent cohomology supported on `T` exactly when its comparison
to the other model does, the comparison commuting with cohomology. -/
theorem quasiCoherentSupported_modelEquiv_functor_obj_iff
    (K : @DerivedCategory (SheafOfModules.{u} X.ringCatSheaf) _ _ h₁) :
    @quasiCoherentSupported X T h₂ ((modelEquiv h₁ h₂).functor.obj K) ↔
      @quasiCoherentSupported X T h₁ K :=
  and_congr (derivedCategoryB_modelEquiv_functor_obj_iff _ h₁ h₂ K)
    (derivedCategoryB_modelEquiv_functor_obj_iff _ h₁ h₂ K)

/-- **The comparison of `D_{QCoh,T}(𝒪_X)` at two models of the derived category**: the
comparison equivalence `StacksDraft.DerivedModel.modelEquiv` restricts to the subcategories of
complexes with quasi-coherent cohomology supported on `T`. -/
def supportedModelEquiv :
    @QuasiCoherentSupportedDerivedCategory X T h₁ ≌
      @QuasiCoherentSupportedDerivedCategory X T h₂ :=
  (modelEquiv h₁ h₂).congrFullSubcategory
    (funext fun K ↦ propext (quasiCoherentSupported_modelEquiv_functor_obj_iff X T h₁ h₂ K))

/-- The functor of `supportedModelEquiv` commutes with the shift. -/
instance supportedModelEquiv_functor_commShift :
    (supportedModelEquiv X T h₁ h₂).functor.CommShift ℤ :=
  inferInstanceAs (((@quasiCoherentSupported X T h₂).lift
    ((@quasiCoherentSupported X T h₁).ι ⋙ (modelEquiv h₁ h₂).functor)
    fun K => (quasiCoherentSupported_modelEquiv_functor_obj_iff X T h₁ h₂ K.obj).2 K.2).CommShift ℤ)

/-- The inverse of `supportedModelEquiv` commutes with the shift. -/
instance supportedModelEquiv_inverse_commShift :
    (supportedModelEquiv X T h₁ h₂).inverse.CommShift ℤ :=
  inferInstanceAs (((@quasiCoherentSupported X T h₁).lift
    ((@quasiCoherentSupported X T h₂).ι ⋙ (modelEquiv h₁ h₂).inverse)
    fun K => (quasiCoherentSupported_modelEquiv_functor_obj_iff X T h₁ h₂ _).1
      ((@quasiCoherentSupported X T h₂).prop_of_iso
        ((modelEquiv h₁ h₂).counitIso.app K.obj).symm K.2)).CommShift ℤ)

/-- The functor of `supportedModelEquiv` is triangulated. -/
theorem supportedModelEquiv_functor_isTriangulated :
    letI := shiftFunctor_additive h₁
    letI := shiftFunctor_additive h₂
    (supportedModelEquiv X T h₁ h₂).functor.IsTriangulated :=
  let := shiftFunctor_additive h₁
  let := shiftFunctor_additive h₂
  ObjectProperty.isTriangulated_lift _ _ _

/-- The inverse of `supportedModelEquiv` is triangulated. -/
theorem supportedModelEquiv_inverse_isTriangulated :
    letI := shiftFunctor_additive h₁
    letI := shiftFunctor_additive h₂
    (supportedModelEquiv X T h₁ h₂).inverse.IsTriangulated :=
  let := shiftFunctor_additive h₁
  let := shiftFunctor_additive h₂
  ObjectProperty.isTriangulated_lift _ _ _

/-- **Perfectness is independent of the model**: an object of `D_{QCoh,T}(𝒪_X)` is perfect at one
model exactly when its comparison to the other is, both being represented by the same complex. -/
theorem isPerfect_supportedModelEquiv_functor_obj_iff
    (K : @QuasiCoherentSupportedDerivedCategory X T h₁) :
    @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace h₂
        ((supportedModelEquiv X T h₁ h₂).functor.obj K).obj ↔
      @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace h₁ K.obj := by
  let Q₁ := @DerivedCategory.Q (SheafOfModules.{u} X.ringCatSheaf) _ _ h₁
  let e₁ : Q₁.obj (Q₁.objPreimage K.obj) ≅ K.obj := Q₁.objObjPreimageIso K.obj
  let e₂ := (modelCompQIso h₁ h₂).symm.app (Q₁.objPreimage K.obj) ≪≫
    (modelEquiv h₁ h₂).functor.mapIso e₁
  exact (Stacks.Cohomology.PerfectComplexes.isPerfect_iff_of_model h₁ h₂ e₁ e₂).symm

end Model

/-! ### `D_{perf,T}(𝒪_X)` inside `D_{QCoh,T}(𝒪_X)` -/

section Perfect

variable (X : Scheme.{u}) (T : Set X)

/-- **`D_{perf,T}(𝒪_X)`** as a property of the objects of `D_{QCoh,T}(𝒪_X)`: the objects whose
underlying object of `D(𝒪_X)` is perfect ([Stacks, Tag 08CM]). A perfect object has
quasi-coherent cohomology, so these are exactly the perfect objects of `D(𝒪_X)` with cohomology
supported on `T`. The model of the derived category is the instance argument. -/
def perfectSupported [h : HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)] :
    ObjectProperty (QuasiCoherentSupportedDerivedCategory X T) :=
  fun K => @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace h K.obj

variable {X T}

/-- The inclusion of `D_{QCoh,T}(𝒪_X)` into `D(𝒪_X)`, at the locally small model. -/
private abbrev ιT := (quasiCoherentSupported.{u, u} X T).ι

/-- The zero object of `D_{QCoh,T}(𝒪_X)` lies in `D_{perf,T}(𝒪_X)`. -/
theorem perfectSupported_zero :
    perfectSupported.{u} X T (0 : QuasiCoherentSupportedDerivedCategory.{u} X T) :=
  Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
    ((ιT (X := X) (T := T)).map_isZero (isZero_zero _)).isoZero.symm
    Stacks.Cohomology.PerfectTriangulatedSubcategory.isPerfect_zero

/-- `D_{perf,T}(𝒪_X)` is stable under the shifts `K ↦ K⟦n⟧`. -/
theorem perfectSupported_shift {K : QuasiCoherentSupportedDerivedCategory.{u} X T}
    (hK : perfectSupported.{u} X T K) (n : ℤ) : perfectSupported.{u} X T (K⟦n⟧) :=
  Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
    (((ιT (X := X) (T := T)).commShiftIso n).app K).symm
    (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_shift hK n)

/-- In a distinguished triangle of `D_{QCoh,T}(𝒪_X)` whose second and third objects are perfect,
the first object is perfect. -/
theorem perfectSupported_obj₁_of_distinguished
    (S : Triangle (QuasiCoherentSupportedDerivedCategory.{u} X T)) (hS : S ∈ distTriang _)
    (h₂ : perfectSupported.{u} X T S.obj₂) (h₃ : perfectSupported.{u} X T S.obj₃) :
    perfectSupported.{u} X T S.obj₁ :=
  Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₁_of_distinguished
    _ (ιT.map_distinguished S hS) h₂ h₃

/-- In a distinguished triangle of `D_{QCoh,T}(𝒪_X)` whose first and third objects are perfect,
the second object is perfect. -/
theorem perfectSupported_obj₂_of_distinguished
    (S : Triangle (QuasiCoherentSupportedDerivedCategory.{u} X T)) (hS : S ∈ distTriang _)
    (h₁ : perfectSupported.{u} X T S.obj₁) (h₃ : perfectSupported.{u} X T S.obj₃) :
    perfectSupported.{u} X T S.obj₂ :=
  Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₂_of_distinguished
    _ (ιT.map_distinguished S hS) h₁ h₃

/-- In a distinguished triangle of `D_{QCoh,T}(𝒪_X)` whose first and second objects are perfect,
the third object is perfect. -/
theorem perfectSupported_obj₃_of_distinguished
    (S : Triangle (QuasiCoherentSupportedDerivedCategory.{u} X T)) (hS : S ∈ distTriang _)
    (h₁ : perfectSupported.{u} X T S.obj₁) (h₂ : perfectSupported.{u} X T S.obj₂) :
    perfectSupported.{u} X T S.obj₃ :=
  Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₃_of_distinguished
    _ (ιT.map_distinguished S hS) h₁ h₂

/-- The direct sum `K ⊞ L` of two perfect objects of `D_{QCoh,T}(𝒪_X)` is perfect. -/
theorem perfectSupported_biprod (K L : QuasiCoherentSupportedDerivedCategory.{u} X T)
    (hK : perfectSupported.{u} X T K) (hL : perfectSupported.{u} X T L) :
    perfectSupported.{u} X T (K ⊞ L) :=
  perfectSupported_obj₂_of_distinguished (binaryBiproductTriangle K L)
    (binaryBiproductTriangle_distinguished K L) hK hL

/-- A retract of a perfect object of `D_{QCoh,T}(𝒪_X)` is perfect. -/
theorem perfectSupported_of_retract {A B : QuasiCoherentSupportedDerivedCategory.{u} X T}
    (r : Retract A B) (hB : perfectSupported.{u} X T B) : perfectSupported.{u} X T A := by
  have hir : (ιT (X := X) (T := T)).map r.i ≫ (ιT (X := X) (T := T)).map r.r = 𝟙 A.obj := by
    rw [← Functor.map_comp, r.retract]
    exact (ιT (X := X) (T := T)).map_id A
  exact Stacks.Cohomology.PerfectDirectSummands.isPerfect_of_retract _ _ hir hB

/-- If `K ⊞ L` is a perfect object of `D_{QCoh,T}(𝒪_X)`, then so are `K` and `L`. -/
theorem perfectSupported_of_biprod (K L : QuasiCoherentSupportedDerivedCategory.{u} X T)
    (h : perfectSupported.{u} X T (K ⊞ L)) :
    perfectSupported.{u} X T K ∧ perfectSupported.{u} X T L :=
  ⟨perfectSupported_of_retract
      { i := biprod.inl, r := biprod.fst, retract := biprod.inl_fst } h,
    perfectSupported_of_retract
      { i := biprod.inr, r := biprod.snd, retract := biprod.inr_snd } h⟩

end Perfect

/-! ### Weak generation in the vanishing form -/

/-- A single object `G` is a weak generator ([Stacks, Tag 09SJ](3)) as soon as every object `K`
receiving only zero morphisms from the shifts `G⟦n⟧` is zero: a morphism into `K` out of an object
of the shift closure of `G` is a morphism out of some `G⟦n⟧` up to an isomorphism. -/
theorem isWeakTriangulatedGenerator_singleton_of_forall_shift_hom_eq_zero {C : Type*}
    [Category C] [Preadditive C] [HasShift C ℤ] {G : C}
    (h : ∀ K : C, (∀ (n : ℤ) (f : G⟦n⟧ ⟶ K), f = 0) → IsZero K) :
    (ObjectProperty.singleton G).IsWeakTriangulatedGenerator := fun K hK =>
  h K fun n f => hK f ⟨G, n, Iso.refl _, (ObjectProperty.singleton_iff _ _).2 rfl⟩

/-! ### The classical generator at the locally small model -/

section LocallySmall

variable (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] (T : Set X)

/-- **A perfect object of `D_{QCoh,T}(𝒪_X)` is compact there**, the implication
*perfect ⟹ compact* of [Stacks, Tag 0A9B], at the locally small model, for `X` quasi-compact and
quasi-separated and any subset `T`. It is compact in `D_QCoh(𝒪_X)` ([Stacks, Tag 09M1],
`Stacks.Duality.QcqsPerfect.isCompactObject_of_isPerfect`), and the inclusion of
`D_{QCoh,T}(𝒪_X)` into `D_QCoh(𝒪_X)` is fully faithful and preserves direct sums. -/
theorem isCompactObject_of_isPerfect_quasiCoherentSupported
    (K : QuasiCoherentSupportedDerivedCategory.{u} X T)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K.obj) :
    IsCompactObject.{u} K :=
  Stacks.Duality.SupportedGeneration.isCompactObject_quasiCoherentSupported_of_isCompactObject
    X T K (Stacks.Duality.QcqsPerfect.isCompactObject_of_isPerfect X _ hK)

/-- **[Stacks, Tag 0GEG], the classical generation, at the locally small model.** A perfect weak
generator `G` of `D_{QCoh,T}(𝒪_X)` has triangulated envelope `D_{perf,T}(𝒪_X)`.

`D_{QCoh,T}(𝒪_X)` has direct sums, `G` and every perfect object of it are compact
(`isCompactObject_of_isPerfect_quasiCoherentSupported`), and the perfect objects form a thick
subcategory; so [Stacks, Tag 09SR] identifies `⟨G⟩` with the compact objects, which are the
perfect ones, through
`ObjectProperty.triangEnvelope_eq_of_le_isCompactObject_of_isWeakTriangulatedGenerator`. -/
theorem triangEnvelope_eq_perfectSupported_of_isWeakTriangulatedGenerator_locallySmall
    (G : QuasiCoherentSupportedDerivedCategory.{u} X T) (hG : perfectSupported.{u} X T G)
    (hgen : (ObjectProperty.singleton G).IsWeakTriangulatedGenerator) :
    (ObjectProperty.singleton G).triangEnvelope = perfectSupported.{u} X T :=
  have := Stacks.Duality.Supported.hasCoproducts_quasiCoherentSupportedDerivedCategory X T
  have : IsCompactObject.{u} G := isCompactObject_of_isPerfect_quasiCoherentSupported X T G hG
  ObjectProperty.triangEnvelope_eq_of_le_isCompactObject_of_isWeakTriangulatedGenerator G
    (perfectSupported.{u} X T) perfectSupported_biprod
    (fun S hS => perfectSupported_obj₁_of_distinguished S hS)
    (fun S hS => perfectSupported_obj₂_of_distinguished S hS)
    (fun S hS => perfectSupported_obj₃_of_distinguished S hS)
    perfectSupported_of_biprod (fun n => perfectSupported_shift hG n)
    (isCompactObject_of_isPerfect_quasiCoherentSupported X T) hgen

end LocallySmall

/-! ### At an arbitrary model -/

section AnyModel

variable (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] (T : Set X)
  [h : HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]

/-- **[Stacks, Tag 0GEG], the classical generation.** Let `G` be a perfect object of
`D_{QCoh,T}(𝒪_X)` which generates it. Then `G` is a classical generator of `D_{perf,T}(𝒪_X)`: the
smallest strictly full, saturated, triangulated subcategory of `D_{QCoh,T}(𝒪_X)` containing `G` is
the subcategory of perfect objects. Stated at an arbitrary model of the derived category and
deduced from the locally small model through the comparison `supportedModelEquiv`, which is a
triangulated equivalence preserving perfectness and weak generators. -/
theorem triangEnvelope_eq_perfectSupported_of_isWeakTriangulatedGenerator
    (G : QuasiCoherentSupportedDerivedCategory X T) (hG : perfectSupported X T G)
    (hgen : (ObjectProperty.singleton G).IsWeakTriangulatedGenerator) :
    (ObjectProperty.singleton G).triangEnvelope = perfectSupported X T := by
  let s := SheafOfModules.hasDerivedCategory X.ringCatSheaf
  let e := supportedModelEquiv X T h s
  let := shiftFunctor_additive h
  have := supportedModelEquiv_functor_isTriangulated X T h s
  have := supportedModelEquiv_inverse_isTriangulated X T h s
  have hcore := triangEnvelope_eq_perfectSupported_of_isWeakTriangulatedGenerator_locallySmall X T
    (e.functor.obj G) ((isPerfect_supportedModelEquiv_functor_obj_iff X T h s G).2 hG)
    (isWeakTriangulatedGenerator_singleton_obj_of_isEquivalence e.functor hgen)
  ext K
  rw [← StacksDraft.Perfect.triangEnvelope_map_iff e G K, hcore]
  exact isPerfect_supportedModelEquiv_functor_obj_iff X T h s K

/-- **[Stacks, Tag 0GEG], existence** ("by Lemma 0A9A there is at least one of these"): for `T`
closed with quasi-compact complement, `D_{QCoh,T}(𝒪_X)` has a perfect object which generates it.
At the locally small model this is [Stacks, Tag 0A9A],
`Stacks.Duality.SupportedGeneration.exists_isPerfect_isWeakGenerator_quasiCoherentSupported`; it is
carried to an arbitrary model by the inverse of `supportedModelEquiv`. -/
theorem exists_perfectSupported_isWeakTriangulatedGenerator (hT : IsClosed T)
    (hTc : IsCompact (Tᶜ : Set X)) :
    ∃ G : QuasiCoherentSupportedDerivedCategory X T,
      perfectSupported X T G ∧ (ObjectProperty.singleton G).IsWeakTriangulatedGenerator := by
  obtain ⟨G₀, hG₀, -, hgen₀⟩ :=
    Stacks.Duality.SupportedGeneration.exists_isPerfect_isWeakGenerator_quasiCoherentSupported
      X T hT hTc
  let s := SheafOfModules.hasDerivedCategory X.ringCatSheaf
  let e := supportedModelEquiv X T h s
  refine ⟨e.inverse.obj G₀, ?_, isWeakTriangulatedGenerator_singleton_obj_of_isEquivalence
    e.inverse (isWeakTriangulatedGenerator_singleton_of_forall_shift_hom_eq_zero hgen₀)⟩
  exact (isPerfect_supportedModelEquiv_functor_obj_iff X T h s _).1
    (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
      ((@quasiCoherentSupported X T s).ι.mapIso (e.counitIso.app G₀).symm) hG₀)

/-- **[Stacks, Remark 0GEG].** Let `X` be a quasi-compact and quasi-separated scheme and let
`T ⊆ X` be a closed subset such that `X ∖ T` is quasi-compact. Then

1. `D_{QCoh,T}(𝒪_X)` has direct sums;
2. there is a perfect object `G` of `D_{QCoh,T}(𝒪_X)` which is a generator for
   `D_{QCoh,T}(𝒪_X)` (by [Stacks, Tag 0A9A]);
3. every such `G` is a classical generator for `D_{perf,T}(𝒪_X)`: the smallest strictly full,
   saturated, triangulated subcategory of `D_{QCoh,T}(𝒪_X)` containing `G` is the subcategory
   `perfectSupported X T` of objects perfect in `D(𝒪_X)`.

Generators are weak generators in the sense of [Stacks, Tag 09SJ](3) and the classical
generation is equality with `CategoryTheory.ObjectProperty.triangEnvelope`. Everything is stated
at an arbitrary model of the derived category. The direct sums are indexed by the universe of
`𝒪_X`-modules; the source's argument uses them, with [Stacks, Tag 0A9B] and
[Stacks, Tag 09SR], at the locally small model, where the morphisms of `D(𝒪_X)` lie in that
universe too. -/
@[stacks 0GEG]
theorem hasCoproducts_and_exists_perfect_generator_and_triangEnvelope_eq_perfectSupported
    (hT : IsClosed T) (hTc : IsCompact (Tᶜ : Set X)) :
    HasCoproducts.{u} (QuasiCoherentSupportedDerivedCategory X T) ∧
      (∃ G : QuasiCoherentSupportedDerivedCategory X T,
        perfectSupported X T G ∧ (ObjectProperty.singleton G).IsWeakTriangulatedGenerator) ∧
      ∀ G : QuasiCoherentSupportedDerivedCategory X T, perfectSupported X T G →
        (ObjectProperty.singleton G).IsWeakTriangulatedGenerator →
          (ObjectProperty.singleton G).triangEnvelope = perfectSupported X T :=
  ⟨Stacks.Duality.Supported.hasCoproducts_quasiCoherentSupportedDerivedCategory X T,
    exists_perfectSupported_isWeakTriangulatedGenerator X T hT hTc,
    triangEnvelope_eq_perfectSupported_of_isWeakTriangulatedGenerator X T⟩

end AnyModel

end Stacks.Duality.SupportedClassicalGenerator

end
