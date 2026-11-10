module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.AffineSupportedPerfectGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectSupportedExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RepresentedAffineLiftStep
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedLiftTransport
public import StacksFrontier.Homology.DerivedCategory.Bridge.Basic
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonExactFunctor
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategoryModel
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentCompactDualizable
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange

/-!
# The affine inputs of Stacks 0AEC on algebraic spaces

Let `V` be an affine algebraic space. This file carries the two affine statements of
`StacksFrontier/AlgebraicGeometry/Duality/CompactGeneration/AffineSupportedPerfectGenerator.lean`
from the affine scheme `V₀` with `V ≅ h_{V₀}` to the small étale site of `V`, through the
equivalence `ε^* : D_QCoh(𝒪_{V₀}) ⥤ D_QCoh(𝒪_V)` of Stacks 071Q, as the proof of Stacks 0AEC
does ("by Derived Categories of Schemes, Lemma 0A9A", "by Derived Categories of Schemes, Lemma
09IR ... using Remark 08GH").

## Main definitions

* `AlgebraicGeometry.Space.IsSupportedPerfectGenerator`: `P` is a perfect object supported on `T`
  generating `D_{QCoh,T}(𝒪_Y)` in the sense of Stacks 0AEC.
* `AlgebraicGeometry.Space.RestrictBijectiveAgainst`: restriction along an étale morphism is
  bijective on morphisms into the objects supported on a set and orthogonal to a perfect object.

## Main results

* `CategoryTheory.eq_zero_of_map_eq_zero_of_full`: a triangulated functor which is full on a
  triangulated subcategory and detects its zero objects is faithful on it.
* `AlgebraicGeometry.Space.bijective_representedDerivedAssociatedModule_map`: `ε^*` is fully
  faithful on `D_QCoh`.
* `AlgebraicGeometry.Space.exists_isPerfect_bijective_representedDerivedPullback`: the restriction
  statement on a represented affine algebraic space.
* `AlgebraicGeometry.Space.isSupportedPerfectGenerator_of_iso` and
  `AlgebraicGeometry.Space.restrictBijectiveAgainst_of_iso`: invariance under isomorphism.
* `AlgebraicGeometry.Space.exists_isSupportedPerfectGenerator_of_isAffineSpace`: Stacks 0AEC for
  an affine algebraic space.
* `AlgebraicGeometry.Space.restrictBijectiveAgainst_edsSnd`: the restriction statement on the
  affine member of an elementary distinguished square.

## Implementation notes

The scheme-level statements are at the locally small model of `D(𝒪_{V₀})`, the global instance;
`ε^*` is defined at the standard model, so they are carried across by the model comparison
`StacksDraft.DerivedModel.modelEquiv` and its compatibility with restriction,
`StacksDraft.DerivedModel.mapDerivedCategoryCompModelEquivIso`. The derived categories of the
algebraic spaces are at the standard model, the one `D_QCoh(𝒪_X)` is defined at.

## References

* [Stacks Project, Tag 0AEC](https://stacks.math.columbia.edu/tag/0AEC)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject

universe u

namespace CategoryTheory

/-- **A triangulated functor which is full on a triangulated subcategory and detects its zero
objects kills no nonzero morphism of it.** Let `g : X ⟶ Y` with `F g = 0`, and complete `g` to a
distinguished triangle `X ⟶ Y ⟶ Z ⟶ X[1]`. Then `F(Y ⟶ Z)` is a split monomorphism, its
retraction is `F r` by fullness, `F` of the cone of `Y ⟶ Z ⟶ Y` vanishes, so that cone vanishes and
`Y ⟶ Z` is a split monomorphism; hence `g = 0`. -/
theorem eq_zero_of_map_eq_zero_of_full {C D : Type*} [Category C] [Category D]
    [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ] [Preadditive C]
    [Preadditive D] [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D] (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (P : ObjectProperty C) [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    (hfull : ∀ X Y : C, P X → P Y → ∀ f : F.obj X ⟶ F.obj Y, ∃ g : X ⟶ Y, F.map g = f)
    (hrefl : ∀ X : C, P X → IsZero (F.obj X) → IsZero X)
    {X Y : C} (hX : P X) (hY : P Y) (g : X ⟶ Y) (hg : F.map g = 0) : g = 0 := by
  obtain ⟨Z, h, k, hT⟩ := distinguished_cocone_triangle g
  have hZ : P Z := ObjectProperty.ext_of_isTriangulatedClosed₃ P _ hT hX hY
  have hFT := F.map_distinguished _ hT
  -- `F h` is a split monomorphism
  obtain ⟨r', hr'⟩ := Triangle.yoneda_exact₂ _ hFT (𝟙 (F.obj Y)) (by
    change F.map g ≫ 𝟙 _ = 0
    rw [hg, zero_comp])
  obtain ⟨r, rfl⟩ := hfull Z Y hZ hY r'
  have hhr : F.map (h ≫ r) = 𝟙 _ := by
    rw [Functor.map_comp]
    exact hr'.symm
  -- `h ≫ r` is an isomorphism
  obtain ⟨W, a, b, hT'⟩ := distinguished_cocone_triangle (h ≫ r)
  have hW : P W := ObjectProperty.ext_of_isTriangulatedClosed₃ P _ hT' hY hY
  have hFW : IsZero (F.obj W) :=
    Triangle.isZero₃_of_isIso₁ _ (F.map_distinguished _ hT') (by
      change IsIso (F.map (h ≫ r))
      rw [hhr]
      infer_instance)
  have hiso : IsIso (h ≫ r) := (Triangle.isZero₃_iff_isIso₁ _ hT').1 (hrefl W hW hFW)
  have hgh : g ≫ h = 0 := comp_distTriang_mor_zero₁₂ _ hT
  rw [← cancel_mono (h ≫ r), ← Category.assoc, hgh, zero_comp, zero_comp]

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] HasDerivedCategory.standard smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective smallEtaleRingedSite_hasSheafify_over
  smallEtaleRingedSite_wEqualsLocallyBijective_over

attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback

/-- `ε^*` on a represented algebraic space is a triangulated functor. -/
instance isTriangulated_representedDerivedAssociatedModule (T : BigFppfOver B S hS) :
    (representedDerivedAssociatedModule B S hS T).IsTriangulated := by
  let := HasDerivedCategory.standard ((BigFppfOver.toScheme B S hS).obj T).Modules
  exact inferInstanceAs ((representedAssociatedModule B S hS T
    (isAlgebraicSpace_yoneda B S hS T)).mapDerivedCategory).IsTriangulated

/-- **`ε^*` is fully faithful on `D_QCoh`** (Stacks 071Q): it is bijective on morphisms between
objects with quasi-coherent cohomology. Fullness is
`AlgebraicGeometry.Space.exists_representedDerivedAssociatedModule_map_eq`; faithfulness follows
from it and the detection of zero objects,
`AlgebraicGeometry.Space.nonempty_iso_of_representedDerivedAssociatedModule_iso`, by
`CategoryTheory.eq_zero_of_map_eq_zero_of_full`. -/
theorem bijective_representedDerivedAssociatedModule_map (T : BigFppfOver B S hS) :
    letI := HasDerivedCategory.standard ((BigFppfOver.toScheme B S hS).obj T).Modules
    ∀ ω ω' : DerivedCategory ((BigFppfOver.toScheme B S hS).obj T).Modules,
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj ω).IsQuasicoherent) →
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj ω').IsQuasicoherent) →
      Function.Bijective
        (fun g : ω ⟶ ω' => (representedDerivedAssociatedModule B S hS T).map g) := by
  let := HasDerivedCategory.standard ((BigFppfOver.toScheme B S hS).obj T).Modules
  intro ω ω' hω hω'
  let X := (BigFppfOver.toScheme B S hS).obj T
  let P := DerivedCategoryB.derivedCategoryB (A := X.Modules)
    (SheafOfModules.isQuasicoherent X.ringCatSheaf)
  have : P.IsClosedUnderIsomorphisms :=
    DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms _
    (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre X)
  have : P.IsTriangulated := DerivedCategoryB.derivedCategoryB_isTriangulated _
    (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre X)
  have hfull : ∀ A A' : DerivedCategory X.Modules, P A → P A' →
      ∀ f : (representedDerivedAssociatedModule B S hS T).obj A ⟶
        (representedDerivedAssociatedModule B S hS T).obj A',
        ∃ g : A ⟶ A', (representedDerivedAssociatedModule B S hS T).map g = f :=
    fun A A' hA hA' f => exists_representedDerivedAssociatedModule_map_eq B S hS T A A' hA hA' f
  have hrefl : ∀ A : DerivedCategory X.Modules, P A →
      IsZero ((representedDerivedAssociatedModule B S hS T).obj A) → IsZero A := by
    intro A hA hzero
    obtain ⟨e⟩ := nonempty_iso_of_representedDerivedAssociatedModule_iso B S hS T A 0 hA
      (fun i => (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_isZero
        ((DerivedCategory.homologyFunctor X.Modules i).map_isZero (isZero_zero _)))
      (hzero.iso ((representedDerivedAssociatedModule B S hS T).map_isZero (isZero_zero _)))
    exact (isZero_zero _).of_iso e
  refine ⟨fun a b hab => ?_, fun f => hfull ω ω' hω hω' f⟩
  have h0 := CategoryTheory.eq_zero_of_map_eq_zero_of_full
    (representedDerivedAssociatedModule B S hS T) P hfull hrefl hω hω' (a - b) (by
      rw [Functor.map_sub]
      exact sub_eq_zero.2 hab)
  exact sub_eq_zero.1 h0

/-- **`D_B` is preserved by the inverse of the comparison of two models.** -/
theorem derivedCategoryB_modelEquiv_inverse_obj {A : Type*} [Category A] [Abelian A]
    (P : ObjectProperty A) [P.IsClosedUnderIsomorphisms] (h₁ h₂ : HasDerivedCategory A)
    (K : @DerivedCategory A _ _ h₂) (hK : @DerivedCategoryB.derivedCategoryB A _ _ h₂ P K) :
    @DerivedCategoryB.derivedCategoryB A _ _ h₁ P
      ((StacksDraft.DerivedModel.modelEquiv h₁ h₂).inverse.obj K) := by
  refine (StacksDraft.DerivedModel.derivedCategoryB_modelEquiv_functor_obj_iff P h₁ h₂ _).1 ?_
  let := h₂
  exact fun n => P.prop_of_iso ((DerivedCategory.homologyFunctor A n).mapIso
    ((StacksDraft.DerivedModel.modelEquiv h₁ h₂).counitIso.app K)).symm (hK n)

/-- A morphism `g : K⟦n⟧ ⟶ F` vanishes if its image under a shift-commuting functor, injective on
that hom-set, does so after reading through an isomorphism of the targets. -/
private theorem eq_zero_of_shift_map_of_injective {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [HasShift C ℤ] [HasShift D ℤ] (Φ : C ⥤ D) [Φ.CommShift ℤ]
    [Φ.PreservesZeroMorphisms] {K F : C} {F' : D} (e : Φ.obj F ≅ F') (n : ℤ) (g : K⟦n⟧ ⟶ F)
    (hΦ : Function.Injective (Φ.map : (K⟦n⟧ ⟶ F) → _))
    (h : (Φ.commShiftIso n).inv.app K ≫ Φ.map g ≫ e.hom = 0) : g = 0 := by
  apply hΦ
  rw [Φ.map_zero]
  calc Φ.map g = (Φ.commShiftIso n).hom.app K ≫
        ((Φ.commShiftIso n).inv.app K ≫ Φ.map g ≫ e.hom) ≫ e.inv := by simp
    _ = 0 := by rw [h]; simp

/-- Transport of an object `G` of `D_QCoh` of the space, orthogonal to `ε^* K₀`, back along `ε^*`:
`G ≅ ε^* G₀` for a `G₀` supported as `G` and orthogonal to `K₀`. -/
private theorem exists_represented_model_orthogonal (V₀ : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V₀)]
    (T₀ : Set ((BigFppfOver.toScheme B S hS).obj V₀)) :
    letI := HasDerivedCategory.standard ((BigFppfOver.toScheme B S hS).obj V₀).Modules
    ∀ K₀ : DerivedCategory ((BigFppfOver.toScheme B S hS).obj V₀).Modules,
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj K₀).IsQuasicoherent) →
      ∀ G : DerivedCategory
          (Modules.{u, u} B S hS (yoneda.obj V₀) (isAlgebraicSpace_yoneda B S hS V₀)),
        DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj V₀)
              (isAlgebraicSpace_yoneda B S hS V₀)).O))) G →
        CohomologySupportedOn B S hS (yoneda.obj V₀) (isAlgebraicSpace_yoneda B S hS V₀)
          ((pointsEquivScheme B S hS V₀) ⁻¹' T₀) G →
        (∀ (n : ℤ) (g : ((representedDerivedAssociatedModule B S hS V₀).obj K₀)⟦n⟧ ⟶ G),
          g = 0) →
        ∃ G₀ : DerivedCategory ((BigFppfOver.toScheme B S hS).obj V₀).Modules,
          (∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj G₀).IsQuasicoherent) ∧
          Nonempty ((representedDerivedAssociatedModule B S hS V₀).obj G₀ ≅ G) ∧
          AlgebraicGeometry.CohomologySupportedOn
            ((BigFppfOver.toScheme B S hS).obj V₀).ringCatSheaf T₀ G₀ ∧
          ∀ (n : ℤ) (g : K₀⟦n⟧ ⟶ G₀), g = 0 := by
  let hstd := HasDerivedCategory.standard ((BigFppfOver.toScheme B S hS).obj V₀).Modules
  intro K₀ hK₀q G hGq hGs hG
  obtain ⟨G₀, hG₀q, ⟨eG⟩⟩ := exists_representedDerivedAssociatedModule_iso B S hS V₀ G hGq
  have hG₀s := cohomologySupportedOn_of_representedDerivedAssociatedModule B S hS V₀ G₀ hG₀q T₀
    (cohomologySupportedOn_of_iso' B S hS
      (Y := ⟨yoneda.obj V₀, isAlgebraicSpace_yoneda B S hS V₀⟩) eG.symm hGs)
  refine ⟨G₀, hG₀q, ⟨eG⟩, hG₀s, fun n g => ?_⟩
  have := @DerivedCategoryB.derivedCategoryB_isTriangulated _ _ _ hstd _
    (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre
      ((BigFppfOver.toScheme B S hS).obj V₀))
  have hK₀n : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj (K₀⟦n⟧)).IsQuasicoherent :=
    ObjectProperty.le_shift (@DerivedCategoryB.derivedCategoryB _ _ _ hstd
      (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj V₀).ringCatSheaf)) n K₀
      hK₀q
  exact eq_zero_of_shift_map_of_injective (representedDerivedAssociatedModule B S hS V₀) eG n g
    (bijective_representedDerivedAssociatedModule_map B S hS V₀ _ G₀ hK₀n hG₀q).1 (hG n _)

/-- The model-comparison step of the affine inputs: if `G₀` at the standard model is orthogonal to
the image of `K` at the locally small model, then its image back is quasi-coherent and supported
as `G₀`, and orthogonal to `K`. -/
private theorem inverse_obj_orthogonal {Y : Scheme.{u}} (T : Set Y)
    (hL hstd : HasDerivedCategory Y.Modules) (KL : @DerivedCategory _ _ _ hL)
    (G₀ : @DerivedCategory _ _ _ hstd)
    (hq : @DerivedCategoryB.derivedCategoryB _ _ _ hstd
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf) G₀)
    (hs : @DerivedCategoryB.derivedCategoryB _ _ _ hstd
      (Stacks.Duality.supportedModules Y.ringCatSheaf T) G₀)
    (h : ∀ (n : ℤ) (g : ((StacksDraft.DerivedModel.modelEquiv hL hstd).functor.obj KL)⟦n⟧ ⟶ G₀),
      g = 0) :
    @DerivedCategoryB.derivedCategoryB _ _ _ hL (SheafOfModules.isQuasicoherent Y.ringCatSheaf)
      ((StacksDraft.DerivedModel.modelEquiv hL hstd).inverse.obj G₀) ∧
    @DerivedCategoryB.derivedCategoryB _ _ _ hL (Stacks.Duality.supportedModules Y.ringCatSheaf T)
      ((StacksDraft.DerivedModel.modelEquiv hL hstd).inverse.obj G₀) ∧
    ∀ (n : ℤ) (g : KL⟦n⟧ ⟶ (StacksDraft.DerivedModel.modelEquiv hL hstd).inverse.obj G₀), g = 0 :=
  ⟨derivedCategoryB_modelEquiv_inverse_obj (SheafOfModules.isQuasicoherent Y.ringCatSheaf) hL hstd
      G₀ hq,
    derivedCategoryB_modelEquiv_inverse_obj (Stacks.Duality.supportedModules Y.ringCatSheaf T) hL
      hstd G₀ hs, fun n g =>
    eq_zero_of_shift_map_of_injective (StacksDraft.DerivedModel.modelEquiv hL hstd).functor
      ((StacksDraft.DerivedModel.modelEquiv hL hstd).counitIso.app G₀) n g
      (StacksDraft.DerivedModel.modelEquiv hL hstd).functor.map_injective (h n _)⟩

/-! ### The restriction statement on a represented affine algebraic space -/

section Represented

variable (V₀ : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V₀)]
  (O : ((BigFppfOver.toScheme B S hS).obj V₀).Opens)

/-- **The restriction statement of the proof of Stacks 0AEC on a represented affine algebraic
space.** Let `V₀` have affine underlying scheme, `O ⊆ V₀` a quasi-compact open and `T₀ ⊆ V₀`
closed with `V₀ ∖ ((V₀ ∖ O) ∩ T₀)` quasi-compact. On the small étale site of `h_{V₀}` there is a
perfect `K` supported over `(V₀ ∖ O) ∩ T₀` such that for every `G` in `D_QCoh(𝒪_{h_{V₀}})`
supported over `T₀` with `Hom(K[n], G) = 0` for all `n`, and every `A` in
`D_QCoh(𝒪_{h_{V₀}})`, restriction `Hom(A, G) ⟶ Hom(A|_{h_O}, G|_{h_O})` is bijective.

This is
`Stacks.Duality.AffineSupportedGenerator.exists_isPerfect_bijective_restrict_of_isAffine` on the
scheme `V₀`, carried to the standard model by `StacksDraft.DerivedModel.modelEquiv` and to the
small étale site by `ε^*`, which is fully faithful on `D_QCoh` and compatible with restriction to
`O`. -/
theorem exists_isPerfect_bijective_representedDerivedPullback
    (hO : IsCompact (O : Set ((BigFppfOver.toScheme B S hS).obj V₀)))
    (T₀ : Set ((BigFppfOver.toScheme B S hS).obj V₀)) (hT₀ : IsClosed T₀)
    (hc : IsCompact ((O : Set ((BigFppfOver.toScheme B S hS).obj V₀))ᶜ ∩ T₀)ᶜ) :
    ∃ K : DerivedCategory
        (Modules.{u, u} B S hS (yoneda.obj V₀) (isAlgebraicSpace_yoneda B S hS V₀)),
      (smallEtaleRingedSite B S hS (yoneda.obj V₀)
        (isAlgebraicSpace_yoneda B S hS V₀)).IsPerfect K ∧
      CohomologySupportedOn B S hS (yoneda.obj V₀) (isAlgebraicSpace_yoneda B S hS V₀)
        ((pointsEquivScheme B S hS V₀) ⁻¹' ((O : Set _)ᶜ ∩ T₀)) K ∧
      ∀ G : DerivedCategory
          (Modules.{u, u} B S hS (yoneda.obj V₀) (isAlgebraicSpace_yoneda B S hS V₀)),
        DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj V₀)
              (isAlgebraicSpace_yoneda B S hS V₀)).O))) G →
        CohomologySupportedOn B S hS (yoneda.obj V₀) (isAlgebraicSpace_yoneda B S hS V₀)
          ((pointsEquivScheme B S hS V₀) ⁻¹' T₀) G →
        (∀ (n : ℤ) (g : K⟦n⟧ ⟶ G), g = 0) →
        ∀ A : DerivedCategory
            (Modules.{u, u} B S hS (yoneda.obj V₀) (isAlgebraicSpace_yoneda B S hS V₀)),
          DerivedCategoryB.derivedCategoryB
            (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
              ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj V₀)
                (isAlgebraicSpace_yoneda B S hS V₀)).O))) A →
          Function.Bijective (fun x : A ⟶ G => (representedDerivedPullback B S hS
            (openIncl B S hS V₀ O) (isEtale_representedSpaceMap_openIncl B S hS V₀ O)).map x) := by
  let Y := (BigFppfOver.toScheme B S hS).obj V₀
  obtain ⟨KL, hKp, hKs, hdet⟩ :=
    Stacks.Duality.AffineSupportedGenerator.exists_isPerfect_bijective_restrict_of_isAffine Y O hO
      T₀ hT₀ hc
  let hL := Scheme.Modules.hasDerivedCategory Y
  let hstd := HasDerivedCategory.standard Y.Modules
  let hLO := Scheme.Modules.hasDerivedCategory O.toScheme
  let hstdO := HasDerivedCategory.standard O.toScheme.Modules
  let me := StacksDraft.DerivedModel.modelEquiv hL hstd
  let meO := StacksDraft.DerivedModel.modelEquiv hLO hstdO
  let ε := representedDerivedAssociatedModule B S hS V₀
  let ε' := representedDerivedAssociatedModule B S hS (openObj B S hS V₀ O)
  let K₀ := me.functor.obj KL
  have hK₀p : @Stacks.Cohomology.PerfectComplexes.IsPerfect Y.toRingedSpace hstd K₀ :=
    (Stacks.Duality.isPerfect_modelEquiv_functor_obj_iff Y.toRingedSpace hL hstd KL).2 hKp
  have hK₀q : ∀ i : ℤ, ((@DerivedCategory.homologyFunctor _ _ _ hstd i).obj K₀).IsQuasicoherent :=
    PerfectApproximation.isQuasicoherent_homology_of_isPerfect _ K₀ hK₀p
  have hK₀s : AlgebraicGeometry.CohomologySupportedOn Y.ringCatSheaf ((O : Set Y)ᶜ ∩ T₀) K₀ :=
    (StacksDraft.DerivedModel.derivedCategoryB_modelEquiv_functor_obj_iff
      (Stacks.Duality.supportedModules Y.ringCatSheaf ((O : Set Y)ᶜ ∩ T₀)) hL hstd KL).2 hKs
  refine ⟨ε.obj K₀, isPerfect_representedDerivedAssociatedModule B S hS V₀ K₀ hK₀p,
    cohomologySupportedOn_representedDerivedAssociatedModule B S hS V₀ K₀ hK₀q _ hK₀s, ?_⟩
  intro G hGq hGs hG A hAq
  obtain ⟨G₀, hG₀q, ⟨eG⟩, hG₀s, hG₀K⟩ :=
    exists_represented_model_orthogonal B S hS V₀ _ K₀ hK₀q G hGq hGs hG
  obtain ⟨A₀, hA₀q, ⟨eA⟩⟩ := exists_representedDerivedAssociatedModule_iso B S hS V₀ A hAq
  have hεb := bijective_representedDerivedAssociatedModule_map B S hS V₀
  have hε'b := bijective_representedDerivedAssociatedModule_map B S hS (openObj B S hS V₀ O)
  let Gl := me.inverse.obj G₀
  let Al := me.inverse.obj A₀
  obtain ⟨hGLq, hGLs, hGLK⟩ := inverse_obj_orthogonal _ hL hstd KL G₀ hG₀q hG₀s hG₀K
  have hALq :=
    derivedCategoryB_modelEquiv_inverse_obj (SheafOfModules.isQuasicoherent Y.ringCatSheaf) hL hstd
      A₀ hA₀q
  have hR := hdet Gl hGLq hGLs hGLK Al
  have σ : @Stacks.Duality.OpenImmersion.derivedRestrict _ _ O.ι _ hLO hL ⋙ meO.functor ⋙ ε' ≅
      (me.functor ⋙ ε) ⋙ representedDerivedPullback B S hS (openIncl B S hS V₀ O)
        (isEtale_representedSpaceMap_openIncl B S hS V₀ O) := by
    let := hstd
    let := hstdO
    have : Flat ((BigFppfOver.toScheme B S hS).map (openIncl B S hS V₀ O)) :=
      inferInstanceAs (Flat O.ι)
    let σrep : Stacks.Duality.OpenImmersion.derivedRestrict O.ι ⋙ ε' ≅
        ε ⋙ representedDerivedPullback B S hS (openIncl B S hS V₀ O)
          (isEtale_representedSpaceMap_openIncl B S hS V₀ O) :=
      Functor.isoWhiskerRight (Scheme.Modules.derivedRestrictIsoDerivedPullback O.ι) ε' ≪≫
        (representedDerivedAssociatedModulePullbackIso B S hS (openIncl B S hS V₀ O)
          (isEtale_representedSpaceMap_openIncl B S hS V₀ O)).symm
    let σm := StacksDraft.DerivedModel.mapDerivedCategoryCompModelEquivIso
        (Scheme.Modules.restrictFunctor O.ι) hL hLO hstdO ≪≫
      (StacksDraft.DerivedModel.modelEquivCompMapDerivedCategoryIso
        (Scheme.Modules.restrictFunctor O.ι) hL hstd hstdO).symm
    exact (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight σm ε' ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft me.functor σrep ≪≫
      (Functor.associator _ _ _).symm
  have hmeA : ∀ i : ℤ, ((@DerivedCategory.homologyFunctor _ _ _ hstd i).obj
      (me.functor.obj Al)).IsQuasicoherent := fun i =>
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
      ((@DerivedCategory.homologyFunctor _ _ _ hstd i).mapIso (me.counitIso.app A₀)).symm (hA₀q i)
  have hmeG : ∀ i : ℤ, ((@DerivedCategory.homologyFunctor _ _ _ hstd i).obj
      (me.functor.obj Gl)).IsQuasicoherent := fun i =>
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
      ((@DerivedCategory.homologyFunctor _ _ _ hstd i).mapIso (me.counitIso.app G₀)).symm (hG₀q i)
  have hRA := Stacks.Duality.OpenImmersion.derivedCategoryB_derivedRestrict O.ι Al hALq
  have hRG := Stacks.Duality.OpenImmersion.derivedCategoryB_derivedRestrict O.ι Gl hGLq
  have hmeRA := (StacksDraft.DerivedModel.derivedCategoryB_modelEquiv_functor_obj_iff
    (SheafOfModules.isQuasicoherent O.toScheme.ringCatSheaf) hLO hstdO _).2 hRA
  have hmeRG := (StacksDraft.DerivedModel.derivedCategoryB_modelEquiv_functor_obj_iff
    (SheafOfModules.isQuasicoherent O.toScheme.ringCatSheaf) hLO hstdO _).2 hRG
  refine CategoryTheory.bijective_map_of_iso_comp (me.functor ⋙ ε) (meO.functor ⋙ ε')
    (@Stacks.Duality.OpenImmersion.derivedRestrict _ _ O.ι _ hLO hL) _ σ (A₀ := Al) (G₀ := Gl)
    ((hεb _ _ hmeA hmeG).comp (me.fullyFaithfulFunctor.map_bijective _ _))
    ((hε'b _ _ hmeRA hmeRG).comp (meO.fullyFaithfulFunctor.map_bijective _ _)) hR
    (ε.mapIso (me.counitIso.app A₀) ≪≫ eA) (ε.mapIso (me.counitIso.app G₀) ≪≫ eG)

end Represented

/-! ### The two properties, and their invariance under isomorphism -/

section Properties

/-- `D_{QCoh,T}(𝒪_Y)` **is generated by `P`**, in the sense of Stacks 0AEC: `P` is a perfect object
of `D(𝒪_Y)` supported on `T`, and an object `E` of `D(𝒪_Y)` with quasi-coherent cohomology
supported on `T` with `Hom(P[n], E) = 0` for all `n ∈ ℤ` is zero. -/
def IsSupportedPerfectGenerator (Y : AlgebraicSpaces B S hS) (T : Set (points B S hS Y.1))
    (P : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)) : Prop :=
  (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect P ∧
    CohomologySupportedOn B S hS Y.1 Y.2 T P ∧
    ∀ E : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2),
      DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))) E →
      CohomologySupportedOn B S hS Y.1 Y.2 T E → (∀ (n : ℤ) (g : P⟦n⟧ ⟶ E), g = 0) → IsZero E

/-- **Restriction along `j : Z ⟶ Y` is bijective against the objects supported on `Ts` that are
orthogonal to a perfect object supported on `Cs`.** There is a perfect `K` on `Y` supported on
`Cs` such that for every `G` in `D_QCoh(𝒪_Y)` supported on `Ts` with `Hom(K[n], G) = 0` for all
`n`, and every `A` in `D_QCoh(𝒪_Y)`, restriction `Hom(A, G) ⟶ Hom(A|_Z, G|_Z)` is bijective. -/
def RestrictBijectiveAgainst {Y Z : AlgebraicSpaces B S hS} (j : Z ⟶ Y)
    (hj : IsEtale B S hS j.hom) (Ts Cs : Set (points B S hS Y.1)) : Prop :=
  ∃ K : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2),
    (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect K ∧
    CohomologySupportedOn B S hS Y.1 Y.2 Cs K ∧
    ∀ G : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2),
      DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))) G →
      CohomologySupportedOn B S hS Y.1 Y.2 Ts G → (∀ (n : ℤ) (g : K⟦n⟧ ⟶ G), g = 0) →
      ∀ A : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2),
        DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))) A →
        Function.Bijective (fun x : A ⟶ G =>
          (etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory.map x)

/-- Pulling back along `e.inv` the inverse image along `e.hom` of a set of points gives the set
back. -/
theorem pointsMap_inv_preimage_hom_preimage {Y Y' : AlgebraicSpaces B S hS} (e : Y ≅ Y')
    (T' : Set (points B S hS Y'.1)) :
    pointsMap B S hS Y'.1 e.inv.hom ⁻¹' (pointsMap B S hS Y.1 e.hom.hom ⁻¹' T') = T' := by
  have h : e.inv.hom ≫ e.hom.hom = 𝟙 Y'.1 := congrArg (fun φ => φ.hom) e.inv_hom_id
  rw [← Set.preimage_comp, ← pointsMap_comp, h, pointsMap_id, Set.preimage_id]

/-- A morphism `g : K⟦n⟧ ⟶ F` vanishes as soon as its image under a faithful functor commuting
with shifts does, read through a given isomorphism of the targets. -/
theorem eq_zero_of_shift_map {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] [HasShift C ℤ] [HasShift D ℤ] (Φ : C ⥤ D) [Φ.CommShift ℤ] [Φ.Faithful]
    [Φ.PreservesZeroMorphisms] {K F : C} {F' : D} (e : Φ.obj F ≅ F') (n : ℤ) (g : K⟦n⟧ ⟶ F)
    (h : (Φ.commShiftIso n).inv.app K ≫ Φ.map g ≫ e.hom = 0) : g = 0 :=
  eq_zero_of_shift_map_of_injective Φ e n g Φ.map_injective h

/-- **Being a supported perfect generator is invariant under isomorphism.** -/
theorem isSupportedPerfectGenerator_of_iso {Y Y' : AlgebraicSpaces B S hS} (e : Y ≅ Y')
    (T' : Set (points B S hS Y'.1)) (P' : DerivedCategory (Modules.{u, u} B S hS Y'.1 Y'.2))
    (h : IsSupportedPerfectGenerator B S hS Y' T' P') :
    IsSupportedPerfectGenerator B S hS Y (pointsMap B S hS Y.1 e.hom.hom ⁻¹' T')
      ((etaleModulePullback.{u, u} B S hS e.hom
        (isEtale_of_isIso B S hS e.hom.hom)).mapDerivedCategory.obj P') := by
  obtain ⟨hP, hPs, hdet⟩ := h
  have he : IsEtale B S hS e.hom.hom := isEtale_of_isIso B S hS e.hom.hom
  have he' : IsEtale B S hS e.inv.hom := isEtale_of_isIso B S hS e.inv.hom
  let EY := Stacks.DerivedQCoh.Equivalence.mapDerivedCategory
    (etaleModulePullbackEquivalence B S hS e)
  refine ⟨isPerfect_etaleModulePullback_standard B S hS e.hom he P' hP,
    cohomologySupportedOn_etaleModulePullback B S hS e.hom he _ P' hPs, fun E hE hEs hEP => ?_⟩
  let E' := EY.inverse.obj E
  have hE' := derivedQuasicoherent_etaleModulePullback B S hS e.inv he' E hE
  have hE's : CohomologySupportedOn B S hS Y'.1 Y'.2 T' E' := by
    have := cohomologySupportedOn_etaleModulePullback B S hS e.inv he' _ E hEs
    rwa [pointsMap_inv_preimage_hom_preimage] at this
  have hz : IsZero E' := hdet E' hE' hE's fun n g =>
    eq_zero_of_shift_map EY.functor (EY.counitIso.app E) n g (hEP n _)
  exact (EY.functor.map_isZero hz).of_iso (EY.counitIso.app E).symm

/-- **Restriction bijectivity is invariant under isomorphism.** Given a square
`eZ ≫ j' = j ≫ eY` with `eZ`, `eY` isomorphisms, the property of `j'` at `Ts'`, `Cs'` gives the
property of `j` at their inverse images. -/
theorem restrictBijectiveAgainst_of_iso {Y Z Y' Z' : AlgebraicSpaces B S hS} (j : Z ⟶ Y)
    (hj : IsEtale B S hS j.hom) (j' : Z' ⟶ Y') (hj' : IsEtale B S hS j'.hom) (eZ : Z ≅ Z')
    (eY : Y ≅ Y') (hcomm : eZ.hom ≫ j' = j ≫ eY.hom) (Ts' Cs' : Set (points B S hS Y'.1))
    (h : RestrictBijectiveAgainst B S hS j' hj' Ts' Cs') :
    RestrictBijectiveAgainst B S hS j hj (pointsMap B S hS Y.1 eY.hom.hom ⁻¹' Ts')
      (pointsMap B S hS Y.1 eY.hom.hom ⁻¹' Cs') := by
  obtain ⟨K', hK', hK's, hdet⟩ := h
  have heZ : IsEtale B S hS eZ.hom.hom := isEtale_of_isIso B S hS eZ.hom.hom
  have heY : IsEtale B S hS eY.hom.hom := isEtale_of_isIso B S hS eY.hom.hom
  have heY' : IsEtale B S hS eY.inv.hom := isEtale_of_isIso B S hS eY.inv.hom
  let EZ := Stacks.DerivedQCoh.Equivalence.mapDerivedCategory
    (etaleModulePullbackEquivalence B S hS eZ)
  let EY := Stacks.DerivedQCoh.Equivalence.mapDerivedCategory
    (etaleModulePullbackEquivalence B S hS eY)
  let R₀ := (etaleModulePullback.{u, u} B S hS j' hj').mapDerivedCategory
  let R := (etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory
  have hjj : IsEtale B S hS (eZ.hom ≫ j').hom := hcomm ▸ isEtale_comp B S hS hj heY
  let FZ := (etaleModulePullbackEquivalence B S hS eZ).functor
  let FY := (etaleModulePullbackEquivalence B S hS eY).functor
  let ι : etaleModulePullback.{u, u} B S hS j' hj' ⋙ FZ ≅
      FY ⋙ etaleModulePullback.{u, u} B S hS j hj :=
    etaleModulePullbackCompIso B S hS eZ.hom j' heZ hj' hjj ≪≫
      etaleModulePullbackCongr B S hS hjj (isEtale_comp B S hS hj heY) hcomm ≪≫
      (etaleModulePullbackCompIso B S hS j eY.hom hj heY _).symm
  let σ : R₀ ⋙ EZ.functor ≅ EY.functor ⋙ R :=
    (Functor.mapDerivedCategoryComp (etaleModulePullback.{u, u} B S hS j' hj') FZ).symm ≪≫
      Stacks.DerivedGlueing.mapDerivedCategoryCongr ι ≪≫
      Functor.mapDerivedCategoryComp FY (etaleModulePullback.{u, u} B S hS j hj)
  refine ⟨EY.functor.obj K',
    isPerfect_etaleModulePullback_standard B S hS eY.hom heY K' hK',
    cohomologySupportedOn_etaleModulePullback B S hS eY.hom heY _ K' hK's,
    fun G hG hGs hGK A hA => ?_⟩
  let G' := EY.inverse.obj G
  let A' := EY.inverse.obj A
  have hG' := derivedQuasicoherent_etaleModulePullback B S hS eY.inv heY' G hG
  have hA' := derivedQuasicoherent_etaleModulePullback B S hS eY.inv heY' A hA
  have hG's : CohomologySupportedOn B S hS Y'.1 Y'.2 Ts' G' := by
    have := cohomologySupportedOn_etaleModulePullback B S hS eY.inv heY' _ G hGs
    rwa [pointsMap_inv_preimage_hom_preimage] at this
  have hb := hdet G' hG' hG's (fun n g =>
    eq_zero_of_shift_map EY.functor (EY.counitIso.app G) n g (hGK n _)) A' hA'
  exact CategoryTheory.bijective_map_of_iso_comp EY.functor EZ.functor R₀ R σ
    (EY.fullyFaithfulFunctor.map_bijective _ _) (EZ.fullyFaithfulFunctor.map_bijective _ _) hb
    (EY.counitIso.app A) (EY.counitIso.app G)

end Properties

/-! ### The affine cases -/

section Affine

attribute [local instance] pointTopology

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_supportedPerfectGeneratorAffine
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **Stacks 0AEC on a represented affine algebraic space** (the case of an affine scheme of
Stacks 0A9A, carried to the small étale site). -/
theorem exists_isSupportedPerfectGenerator_represented (V₀ : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V₀)]
    (C₀ : Set ((BigFppfOver.toScheme B S hS).obj V₀)) (hC₀ : IsClosed C₀) (hC₀c : IsCompact C₀ᶜ) :
    ∃ P, IsSupportedPerfectGenerator B S hS ⟨yoneda.obj V₀, isAlgebraicSpace_yoneda B S hS V₀⟩
      ((pointsEquivScheme B S hS V₀) ⁻¹' C₀) P := by
  let Y := (BigFppfOver.toScheme B S hS).obj V₀
  obtain ⟨KL, hKp, hKs, hdet⟩ :=
    Stacks.Duality.AffineSupportedGenerator.exists_isPerfect_detecting_of_isAffine Y C₀ hC₀ hC₀c
  let hL := Scheme.Modules.hasDerivedCategory Y
  let hstd := HasDerivedCategory.standard Y.Modules
  let me := StacksDraft.DerivedModel.modelEquiv hL hstd
  let ε := representedDerivedAssociatedModule B S hS V₀
  let K₀ := me.functor.obj KL
  have hK₀p : @Stacks.Cohomology.PerfectComplexes.IsPerfect Y.toRingedSpace hstd K₀ :=
    (Stacks.Duality.isPerfect_modelEquiv_functor_obj_iff Y.toRingedSpace hL hstd KL).2 hKp
  have hK₀q : ∀ i : ℤ, ((@DerivedCategory.homologyFunctor _ _ _ hstd i).obj K₀).IsQuasicoherent :=
    PerfectApproximation.isQuasicoherent_homology_of_isPerfect _ K₀ hK₀p
  have hK₀s : AlgebraicGeometry.CohomologySupportedOn Y.ringCatSheaf C₀ K₀ :=
    (StacksDraft.DerivedModel.derivedCategoryB_modelEquiv_functor_obj_iff
      (Stacks.Duality.supportedModules Y.ringCatSheaf C₀) hL hstd KL).2 hKs
  refine ⟨ε.obj K₀, isPerfect_representedDerivedAssociatedModule B S hS V₀ K₀ hK₀p,
    cohomologySupportedOn_representedDerivedAssociatedModule B S hS V₀ K₀ hK₀q _ hK₀s, ?_⟩
  intro E hEq hEs hE
  obtain ⟨E₀, hE₀q, ⟨eE⟩, hE₀s, hE₀K⟩ :=
    exists_represented_model_orthogonal B S hS V₀ _ K₀ hK₀q E hEq hEs hE
  obtain ⟨hElq, hEls, hElK⟩ := inverse_obj_orthogonal _ hL hstd KL E₀ hE₀q hE₀s hE₀K
  have hzL : IsZero (me.inverse.obj E₀) := hdet _ hElq hEls hElK
  have hz₀ : IsZero E₀ := (me.functor.map_isZero hzL).of_iso (me.counitIso.app E₀).symm
  exact (ε.map_isZero hz₀).of_iso eE.symm

/-- The closed set of points of an affine scheme `V₀` corresponding, through an isomorphism
`V ≅ h_{V₀}`, to the inverse image along `a : V ⟶ X` of a closed `T ⊆ |X|` with quasi-compact open
complement: it is closed, has quasi-compact complement, and its preimage in `|V|` is
`a⁻¹(T)`. -/
theorem exists_schemeSet_of_iso {X V : AlgebraicSpaces B S hS} (a : V ⟶ X)
    {V₀ : BigFppfOver B S hS} (hV₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj V₀))
    (e : V ≅ ⟨yoneda.obj V₀, isAlgebraicSpace_yoneda B S hS V₀⟩) (T : Set (points B S hS X.1))
    (hT : IsClosed T)
    (hTqc : IsQuasiCompact B S hS
      ((openSubspacesOrderIso B S hS X.1 X.2).symm ⟨Tᶜ, hT.isOpen_compl⟩).1.ι) :
    ∃ Z : Set ((BigFppfOver.toScheme B S hS).obj V₀), IsClosed Z ∧ IsCompact Zᶜ ∧
      pointsMap B S hS V.1 e.hom.hom ⁻¹' ((pointsEquivScheme B S hS V₀) ⁻¹' Z) =
        pointsMap B S hS V.1 a.hom ⁻¹' T := by
  let Zs' : Set (points B S hS (yoneda.obj V₀)) :=
    pointsMap B S hS (yoneda.obj V₀) e.inv.hom ⁻¹' (pointsMap B S hS V.1 a.hom ⁻¹' T)
  let Z : Set ((BigFppfOver.toScheme B S hS).obj V₀) := (pointsEquivScheme B S hS V₀).symm ⁻¹' Zs'
  have hZ' : (pointsEquivScheme B S hS V₀) ⁻¹' Z = Zs' := by
    ext p
    simp [Z]
  have hZs'c : IsClosed Zs' :=
    (hT.preimage (continuous_pointsMap B S hS _)).preimage (continuous_pointsMap B S hS _)
  refine ⟨Z, hZs'c.preimage (schemePointsHomeomorph B S hS V₀).symm.continuous, ?_, ?_⟩
  · let G := (openSubspacesOrderIso B S hS X.1 X.2).symm ⟨Tᶜ, hT.isOpen_compl⟩
    have h₁ := isCompact_preimage_range_of_isQuasiCompact B S hS X.2
      (isAlgebraicSpace_yoneda B S hS V₀) (isQuasiCompactSpace_yoneda_of_isAffine B S hS V₀ hV₀)
      (e.inv.hom ≫ a.hom) G.1 G.2 hTqc
    rw [range_openSubspacesOrderIso_symm B S hS X.1 X.2 T hT, pointsMap_comp,
      Set.preimage_comp] at h₁
    have h₂ := h₁.image (schemePointsHomeomorph B S hS V₀).continuous
    convert h₂ using 1
    ext x
    simp only [Z, Zs', Set.mem_compl_iff, Set.mem_preimage, Set.mem_image]
    refine ⟨fun hx => ⟨(pointsEquivScheme B S hS V₀).symm x, hx, Equiv.apply_symm_apply _ _⟩, ?_⟩
    rintro ⟨p, hp, rfl⟩
    have hp' : (pointsEquivScheme B S hS V₀).symm ((schemePointsHomeomorph B S hS V₀) p) = p :=
      (pointsEquivScheme B S hS V₀).symm_apply_apply p
    rw [hp']
    simpa only [pointsMap_comp, Function.comp_apply] using hp
  · rw [hZ']
    exact pointsMap_inv_preimage_hom_preimage B S hS e.symm _

/-- **Stacks 0AEC on an affine algebraic space.** For an affine algebraic space `V` with a
morphism `a : V ⟶ X`, and `T ⊆ |X|` closed with `X ∖ T ⟶ X` quasi-compact,
`D_{QCoh, a⁻¹T}(𝒪_V)` is generated by a single perfect object. -/
theorem exists_isSupportedPerfectGenerator_of_isAffineSpace {X V : AlgebraicSpaces B S hS}
    (a : V ⟶ X) (hV : IsAffineSpace B S hS V.1) (T : Set (points B S hS X.1)) (hT : IsClosed T)
    (hTqc : IsQuasiCompact B S hS
      ((openSubspacesOrderIso B S hS X.1 X.2).symm ⟨Tᶜ, hT.isOpen_compl⟩).1.ι) :
    ∃ P, IsSupportedPerfectGenerator B S hS V (pointsMap B S hS V.1 a.hom ⁻¹' T) P := by
  obtain ⟨V₀, hV₀, ⟨i⟩⟩ := hV
  let e : V ≅ ⟨yoneda.obj V₀, isAlgebraicSpace_yoneda B S hS V₀⟩ := ObjectProperty.isoMk _ i
  obtain ⟨Z, hZ, hZc, hset⟩ := exists_schemeSet_of_iso B S hS a hV₀ e T hT hTqc
  obtain ⟨P', hP'⟩ := exists_isSupportedPerfectGenerator_represented B S hS V₀ Z hZ hZc
  rw [← hset]
  exact ⟨_, isSupportedPerfectGenerator_of_iso B S hS e _ P' hP'⟩

/-- **The restriction statement of Stacks 0AEC on the affine member of an elementary
distinguished square.** Let `(U ⊆ W, f : V ⟶ W)` be an elementary distinguished square with `V`
affine and `U ×_W V` quasi-compact, and `T ⊆ |W|` closed with `W ∖ T ⟶ W` quasi-compact. There is
a perfect `K` on `V` supported on `f⁻¹(T) ∩ f⁻¹(|W| ∖ |U|)` such that restriction to `U ×_W V`
is bijective on `Hom(A, G)` for every `A` in `D_QCoh(𝒪_V)` and every `G` in `D_QCoh(𝒪_V)` supported
on `f⁻¹(T)` with `Hom(K[n], G) = 0` for all `n`. -/
theorem restrictBijectiveAgainst_edsSnd {W : AlgebraicSpaces B S hS}
    {Ve : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Uo : Subfunctor W.1} {fV : Ve ⟶ W.1}
    (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV) (hVaff : IsAffineSpace B S hS Ve)
    (hUVqc : IsQuasiCompactSpace B S hS (edsInter B S hS hsq).1)
    (T : Set (points B S hS W.1)) (hT : IsClosed T)
    (hTqc : IsQuasiCompact B S hS
      ((openSubspacesOrderIso B S hS W.1 W.2).symm ⟨Tᶜ, hT.isOpen_compl⟩).1.ι) :
    RestrictBijectiveAgainst B S hS (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq)
      (pointsMap B S hS (edsEtale B S hS hsq).1 (edsEtaleHom B S hS hsq).hom ⁻¹' T)
      (pointsMap B S hS (edsEtale B S hS hsq).1 (edsEtaleHom B S hS hsq).hom ⁻¹' T ∩
        edsEtalePreimageComplementPoints B S hS hsq) := by
  obtain ⟨V₀, hV₀, O, hO, eV, eI, hcomm⟩ := exists_eds_represented B S hS hsq hVaff hUVqc
  have := hV₀
  obtain ⟨T₀, hT₀, hT₀c, hset⟩ :=
    exists_schemeSet_of_iso B S hS (edsEtaleHom B S hS hsq) hV₀ eV T hT hTqc
  have hc : IsCompact ((O : Set ((BigFppfOver.toScheme B S hS).obj V₀))ᶜ ∩ T₀)ᶜ := by
    rw [Set.compl_inter, compl_compl]
    exact hO.union hT₀c
  obtain ⟨K, hK, hKs, hdet⟩ :=
    exists_isPerfect_bijective_representedDerivedPullback B S hS V₀ O hO T₀ hT₀ hc
  have h := restrictBijectiveAgainst_of_iso B S hS (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq)
    (representedSpaceMap B S hS (openIncl B S hS V₀ O))
    (isEtale_representedSpaceMap_openIncl B S hS V₀ O) eI eV hcomm _ _ ⟨K, hK, hKs, hdet⟩
  rw [hset] at h
  obtain ⟨K', hK', hK's, hdet'⟩ := h
  refine ⟨K', hK', hK's.mono B S hS _ _ fun v hv => ⟨?_, ?_⟩, hdet'⟩
  · rw [← hset]
    exact hv.2
  · -- a point of `V` over `|U|` comes from `U ×_W V`, whose image in `V₀` lies in `O`
    rintro ⟨u, hu⟩
    obtain ⟨w, -, hw⟩ := exists_points_of_isPullback B S hS
      (IsPullback.of_hasPullback (edsOpenHom B S hS hsq).hom (edsEtaleHom B S hS hsq).hom) u v hu
    apply hv.1
    let w' : points B S hS (edsInter B S hS hsq).1 := w
    have hc' := congrArg (fun φ => pointsMap B S hS (edsInter B S hS hsq).1 φ.hom w') hcomm
    simp only [ObjectProperty.FullSubcategory.comp_hom, pointsMap_comp, Function.comp_apply] at hc'
    change pointsMap B S hS _ (edsSnd B S hS hsq).hom w' = v at hw
    rw [← hw, ← hc']
    change pointsEquivScheme B S hS V₀ (pointsMap B S hS _
      (yoneda.map (openIncl B S hS V₀ O)) _) ∈ (O : Set _)
    rw [pointsEquivScheme_pointsMap_yoneda_map]
    exact (pointsEquivScheme B S hS (openObj B S hS V₀ O) _).2

end Affine

end AlgebraicGeometry.Space

end
