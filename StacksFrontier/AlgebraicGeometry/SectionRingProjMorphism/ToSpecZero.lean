module

public import StacksFrontier.AlgebraicGeometry.SectionRingProjImmersion.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# The canonical morphism to `Proj Γ_*(X, L)` over `Spec Γ(X, 𝒪_X)`

Let `X` be a scheme, `L` an ample invertible `𝒪_X`-module, `S = Γ_*(X, L)` its graded section
ring and `r : X ⟶ Proj S` the canonical morphism `Stacks.SectionRingProjMorphism.projHomOfIsAmple`
of Stacks Tag 01PZ. This file identifies the degree-zero part `S₀` with `Γ(X, 𝒪_X)`, shows that
the triangle

`r ≫ Proj.toSpecZero = X.toSpecΓ ≫ Spec (S₀ ≅ Γ(X, 𝒪_X))`

commutes, and deduces that `r` is an isomorphism when `X ⟶ Spec Γ(X, 𝒪_X)` is universally closed.

## Main definitions

* `Stacks.SectionRingProjMorphism.ToSpecZero.unitTrivialization`: the trivialization of the
  monoidal unit of `X.Modules` over `⊤`, with the section attached to `𝟙 (𝟙_)` as its basis.
* `Stacks.SectionRingProjMorphism.ToSpecZero.unitSec`: that same morphism `𝟙 (𝟙_)` read as a
  homogeneous element of degree zero of `Γ_*(X, L)`.
* `Stacks.SectionRingProjMorphism.ToSpecZero.degZeroRingHom`: the comparison
  `(Γ_*(X, L))₀ →+* Γ(X, 𝒪_X)`, the ratio by the unit section.

## Main results

* `Stacks.SectionRingProjMorphism.ToSpecZero.nvOpen_unitSec`: the unit section vanishes
  nowhere, `X_1 = X`.
* `Stacks.SectionRingProjMorphism.ToSpecZero.bijective_degZeroRingHom`: the comparison is
  bijective.
* `Stacks.SectionRingProjMorphism.ToSpecZero.chartRingMap_fromZero`: on a degree-zero fraction
  `c / 1` the chart ring map at a homogeneous `a` of positive degree is the restriction of the
  comparison to `X_a`.
* `Stacks.SectionRingProjMorphism.ToSpecZero.projHomOfIsAmple_toSpecZero`: the triangle
  `r ≫ Proj.toSpecZero = X.toSpecΓ ≫ Spec (degZeroRingHom)`.
* `Stacks.SectionRingProjMorphism.ToSpecZero.universallyClosed_toSpecΓ`: for a universally closed
  morphism to an affine scheme, `X ⟶ Spec Γ(X, 𝒪_X)` is universally closed.
* `Stacks.SectionRingProjMorphism.ToSpecZero.isIso_projHomOfIsAmple`: if `X ⟶ Spec Γ(X, 𝒪_X)`
  is universally closed then `r` is an isomorphism.

## References

* [Stacks Project, Tag 01PZ](https://stacks.math.columbia.edu/tag/01PZ)
* [Stacks Project, Tag 01Q1](https://stacks.math.columbia.edu/tag/01Q1)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01W6](https://stacks.math.columbia.edu/tag/01W6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open Stacks.GradedSections (powSections sectionRing)
open Stacks.AmpleFiniteAvoidance (nvOpen nvLocus grading)
open Stacks.SectionProduct (globalSection)
open Stacks.SectionRingChartMap
open Stacks.TensorPowerTrivialize (trivEquiv resTop)
open Stacks.TensorPowers (natTensorPow)
open Stacks.SectionExtension (powSec)

universe u

namespace Stacks.SectionRingProjMorphism.ToSpecZero

section Monoidal

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

/-! ### The monoidal unit is the structure sheaf, sectionwise -/

/-- The monoidal unit of `X.Modules` is isomorphic to the structure sheaf of `X`, as a sheaf of
modules over itself. -/
noncomputable def unitTensorIso (X : Scheme.{u}) :
    𝟙_ X.Modules ≅ SheafOfModules.unit X.ringCatSheaf :=
  AlgebraicGeometry.SheafOfModules.unitIso X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X)

/-- The isomorphism between the sections of the monoidal unit over an open and the functions on
that open, the image of `Stacks.SectionRingProjMorphism.ToSpecZero.unitTensorIso` under
evaluation at the open. -/
noncomputable def unitSectionsIso (X : Scheme.{u}) (W : X.Opens) :
    (𝟙_ X.Modules).val.obj (op W) ≅ (SheafOfModules.unit X.ringCatSheaf).val.obj (op W) :=
  (Scheme.Modules.toPresheafOfModules X ⋙
    PresheafOfModules.evaluation X.ringCatSheaf.obj (op W)).mapIso (unitTensorIso X)

/-- The trivialization of the monoidal unit of `X.Modules` over all of `X` whose map over an open
is `Stacks.SectionRingProjMorphism.ToSpecZero.unitSectionsIso`. -/
noncomputable def unitTrivialization (X : Scheme.{u}) :
    Stacks.SheafDescent.Trivialization X.presheaf (𝟙_ X.Modules).val ⊤ where
  θ W _ := (unitSectionsIso X W).toLinearEquiv
  θ_naturality _ h' m := congrFun (congrArg (fun f => DFunLike.coe (ModuleCat.Hom.hom f))
    ((unitTensorIso X).hom.val.naturality h'.op)) m

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- The unit of the section ring, `1 ∈ Γ(X, L ^⊗ 0) = Γ(X, 𝒪_X)`, as a homogeneous element of
degree zero: the identity of the monoidal unit. -/
noncomputable def unitSec (L : X.Modules) : powSections L 0 := 𝟙 (𝟙_ X.Modules)

/-- The unit section vanishes nowhere: `X_1 = X`. -/
theorem nvOpen_unitSec : nvOpen L (unitSec L) = ⊤ := by
  refine TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun x => ?_)
  rw [Stacks.AmpleFiniteAvoidance.coe_nvOpen]
  change x ∈ Stacks.Ample.nonvanishingLocus (natTensorPow L 0) _
  rw [Stacks.Ample.mem_nonvanishingLocus_iff]
  exact Stacks.NonvanishingOpen.notMem_maximalSmul_germ_basis (unitTrivialization X) trivial

/-- Every open lies inside the nonvanishing open of the unit section. -/
theorem le_nvOpen_unitSec {V : X.Opens} : V ≤ nvOpen L (unitSec L) :=
  (nvOpen_unitSec L).ge.trans' le_top

omit [Stacks.Ample.IsInvertibleModule X L] in
/-- Restricting a global section to `⊤` changes nothing. -/
theorem resTop_top {M : X.Modules} (u : Γ(M, ⊤)) : resTop M u ⊤ = u := by
  change M.presheaf.map _ u = u
  rw [Subsingleton.elim (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)) (𝟙 _)]
  simp

omit [Stacks.Ample.IsInvertibleModule X L] in
/-- The unit section is idempotent for the product of the section ring. -/
theorem mul_unitSec : Stacks.GradedSections.mul (unitSec L) (unitSec L) = unitSec L := by
  change unitSec L ≫ Stacks.GradedSections.mulMap (unitSec L) 0 = unitSec L
  rw [Stacks.GradedSections.mulMap_zero]
  exact Category.comp_id _

omit [Stacks.Ample.IsInvertibleModule X L] in
/-- The unit section is a right unit for the product of the section ring. -/
theorem mul_unitSec_right {d : ℕ} (a : powSections L d) :
    Stacks.GradedSections.mul a (unitSec L) = a := by
  change unitSec L ≫ Stacks.GradedSections.mulMap a 0 = a
  rw [Stacks.GradedSections.mulMap_zero]
  exact Category.id_comp _

omit [Stacks.Ample.IsInvertibleModule X L] in
/-- The unit section names the unit of the section ring. -/
theorem of_unitSec : DirectSum.of (powSections L) 0 (unitSec L) = 1 := by
  change _ = DirectSum.of (powSections L) 0 GradedMonoid.GOne.one
  rw [Stacks.GradedSections.gOne_def]
  rfl

/-! ### The degree-zero part of the section ring is the functions on `X` -/

/-- The comparison `(Γ_*(X, L))₀ →+* Γ(X, 𝒪_X)`, dividing a homogeneous element of degree zero
by the unit section. -/
noncomputable def degZeroRingHom : (grading L 0) →+* Γ(X, ⊤) where
  toFun c := ratioR L (unitSec L) (le_nvOpen_unitSec L) (c : sectionRing L)
  map_one' := by
    change ratioR L (unitSec L) (le_nvOpen_unitSec L) ((1 : grading L 0) : sectionRing L) = 1
    rw [show ((1 : grading L 0) : sectionRing L) = 1 from rfl, ← of_unitSec L, ratioR_of_self]
  map_mul' c c' := by
    change ratioR L (unitSec L) _ (((c * c' : grading L 0)) : sectionRing L) = _
    rw [show (((c * c' : grading L 0)) : sectionRing L)
        = (c : sectionRing L) * (c' : sectionRing L) from rfl,
      ← ratioR_mul L (unitSec L) (unitSec L) (le_nvOpen_unitSec L) (le_nvOpen_unitSec L)
        (le_nvOpen_unitSec L) c.2 c'.2]
    exact ratioR_congr L rfl (Stacks.GradedSections.mul (unitSec L) (unitSec L)) (unitSec L) _ _
      (congrArg (DirectSum.of (powSections L) 0) (mul_unitSec L)) _
  map_zero' := map_zero _
  map_add' c c' := map_add _ _ _

/-- The comparison `Stacks.SectionRingProjMorphism.ToSpecZero.degZeroRingHom` is bijective. -/
theorem bijective_degZeroRingHom : Function.Bijective (degZeroRingHom L) := by
  have key : ⇑(degZeroRingHom L) =
      (trivEquiv (natTensorPow L 0) (globalSection X _ (unitSec L)) (le_nvOpen_unitSec L)).symm ∘
        (globalSection X (natTensorPow L 0)) ∘
        ⇑(Stacks.ExternalGrading.summandEquiv (powSections L) 0).symm := by
    funext c
    change ratioR L (unitSec L) (le_nvOpen_unitSec L) (c : sectionRing L) = _
    rw [ratioR_apply]
    change (trivEquiv _ _ _).symm (resTop _ (globalSection X _ ((c : sectionRing L) 0)) ⊤) = _
    rw [resTop_top]
    rfl
  rw [key]
  exact Function.Bijective.comp (LinearEquiv.bijective _)
    (Function.Bijective.comp
      (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X (natTensorPow L 0)).bijective
      (Stacks.ExternalGrading.summandEquiv (powSections L) 0).symm.bijective)

/-! ### The chart ring map in degree zero -/

/-- The ratio is compatible with restriction: computed on a smaller open, it is the restriction
of the ratio computed on the larger one. -/
theorem res_ratio {j : ℕ} (g : powSections L j) {V W : X.Opens} (hg : V ≤ nvOpen L g)
    (hg' : W ≤ nvOpen L g) (hWV : W ≤ V) (s : powSections L j) :
    X.presheaf.map (homOfLE hWV).op (ratio L g hg s) = ratio L g hg' s := by
  refine (ratio_unique L g hg' s _ ?_).symm
  have h := congrArg (fun t => (natTensorPow L j).presheaf.map (homOfLE hWV).op t)
    (ratio_smul_resTop L g hg s)
  simpa only [Stacks.TensorPowerTrivialize.map_smul_resTop,
    Stacks.TensorPowerTrivialize.res_resTop] using h.symm

/-- The chart ring map at `a` sends the fraction `c / 1`, with `c` homogeneous of degree zero, to
the restriction to `X_a` of the function `degZeroRingHom L c`. -/
theorem chartRingMap_fromZero {d : ℕ} (a : powSections L d) (c : grading L 0) :
    chartRingMap L a (le_refl (nvOpen L a))
        (HomogeneousLocalization.fromZeroRingHom (grading L)
          (Submonoid.powers (DirectSum.of (powSections L) d a)) c)
      = X.presheaf.map (homOfLE (le_top : nvOpen L a ≤ ⊤)).op (degZeroRingHom L c) := by
  have h0 : ((c : sectionRing L)) ∈ grading L (0 • d) := by simpa only [zero_smul] using c.2
  have hmk : HomogeneousLocalization.fromZeroRingHom (grading L)
        (Submonoid.powers (DirectSum.of (powSections L) d a)) c
      = HomogeneousLocalization.Away.mk (grading L)
          (Stacks.ExternalGrading.of_mem_summand d a) 0 (c : sectionRing L) h0 := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.Away.val_mk]
    change Localization.mk (c : sectionRing L) 1 = _
    congr 1
  rw [hmk, chartRingMap_mk, chartFamily_apply, numMapR_def]
  have hof : DirectSum.of (powSections L) (d * 1) (powSec L a 1)
      = DirectSum.of (powSections L) d a := by
    rw [of_powSec_eq_pow, pow_one]
  rw [ratioR_congr L (by omega : d * 1 = d) (powSec L a 1) a _ (le_refl (nvOpen L a)) hof]
  have hmulcongr : ratioR L (Stacks.GradedSections.mul a (unitSec L))
        (le_of_eq (congrArg (nvOpen L) (mul_unitSec_right L a)).symm)
      = ratioR L a (le_refl (nvOpen L a)) :=
    DFunLike.ext _ _ fun z =>
      ratioR_congr L rfl (Stacks.GradedSections.mul a (unitSec L)) a _ (le_refl (nvOpen L a))
        (congrArg (DirectSum.of (powSections L) d) (mul_unitSec_right L a)) z
  rw [← hmulcongr, ratioR_mul L a (unitSec L) (le_refl (nvOpen L a)) (le_nvOpen_unitSec L) _
    (Stacks.ExternalGrading.of_mem_summand d a) c.2, ratioR_of_self, one_mul, ratioR_apply,
    ← res_ratio L (unitSec L) (le_nvOpen_unitSec L) (le_nvOpen_unitSec L) le_top]
  rfl

/-! ### The triangle over `Spec (Γ_*(X, L))₀` -/

/-- For `L` ample, the composite of the canonical morphism `r : X ⟶ Proj Γ_*(X, L)` with the
structure morphism `AlgebraicGeometry.Proj.toSpecZero` is the canonical morphism
`X ⟶ Spec Γ(X, 𝒪_X)` followed by `Spec` of
`Stacks.SectionRingProjMorphism.ToSpecZero.degZeroRingHom`. -/
theorem projHomOfIsAmple_toSpecZero (hL : Stacks.Ample.IsAmple X L) :
    projHomOfIsAmple L hL ≫ Proj.toSpecZero (grading L)
      = X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (degZeroRingHom L)) := by
  refine (X.openCoverOfIsOpenCover (fun c : PosSection L => nvOpen L c.val)
      (nvUnion_eq_top_of_isAmple L hL)).hom_ext _ _ fun c => ?_
  obtain ⟨d, hd, a⟩ := c
  change (nvOpen L a).ι ≫ _ = (nvOpen L a).ι ≫ _
  rw [← Category.assoc, Stacks.SectionRingProjImmersion.ι_comp_projHomOfIsAmple L hL a hd,
    ← Stacks.SectionRingChartOpen.chartHomOn_self L a hd,
    Stacks.SectionRingChartOpen.chartHomOn_val L a hd (le_refl _), Category.assoc,
    Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp,
    ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top_assoc, ← Spec.map_comp]
  congr 1
  exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext (chartRingMap_fromZero L a)))

/-! ### Universal closedness makes the canonical morphism an isomorphism -/

/-- If `X` admits a universally closed morphism to an affine scheme, then `X ⟶ Spec Γ(X, 𝒪_X)`
is universally closed. -/
theorem universallyClosed_toSpecΓ {S : Scheme.{u}} (f : X ⟶ S) [UniversallyClosed f]
    [IsAffine S] : UniversallyClosed X.toSpecΓ := by
  have := AlgebraicGeometry.universallyClosed_respectsIso
  have : UniversallyClosed (X.toSpecΓ ≫ Spec.map f.appTop) := by
    rwa [← Scheme.toSpecΓ_naturality,
      MorphismProperty.cancel_right_of_respectsIso (P := @UniversallyClosed)]
  exact .of_comp_of_isSeparated _ (Spec.map f.appTop)

/-- For `L` ample, the canonical morphism `X ⟶ Proj Γ_*(X, L)` is an isomorphism as soon as
`X ⟶ Spec Γ(X, 𝒪_X)` is universally closed. -/
theorem isIso_projHomOfIsAmple (hL : Stacks.Ample.IsAmple X L)
    (h : UniversallyClosed X.toSpecΓ) : IsIso (projHomOfIsAmple L hL) := by
  have hiso : IsIso (Spec.map (CommRingCat.ofHom (degZeroRingHom L))) := by
    have : IsIso (CommRingCat.ofHom (degZeroRingHom L)) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr (bijective_degZeroRingHom L)
    infer_instance
  have := AlgebraicGeometry.universallyClosed_respectsIso
  have h1 : UniversallyClosed (projHomOfIsAmple L hL ≫ Proj.toSpecZero (grading L)) := by
    rwa [projHomOfIsAmple_toSpecZero,
      MorphismProperty.cancel_right_of_respectsIso (P := @UniversallyClosed)]
  have hoi := Stacks.SectionRingProjImmersion.isOpenImmersion_projHomOfIsAmple L hL
  have h2 : UniversallyClosed (projHomOfIsAmple L hL) :=
    UniversallyClosed.of_comp_of_isSeparated _ (Proj.toSpecZero (grading L))
  have hclosed : IsClosed (Set.range (projHomOfIsAmple L hL).base) := by
    simpa only [Set.image_univ] using (projHomOfIsAmple L hL).isClosedMap _ isClosed_univ
  have hdense := Stacks.SectionRingProjImmersion.denseRange_projHomOfIsAmple L hL
  refine AlgebraicGeometry.isIso_of_isOpenImmersion_of_opensRange_eq_top _
    (TopologicalSpace.Opens.ext ?_)
  rw [Scheme.Hom.coe_opensRange, TopologicalSpace.Opens.coe_top, ← hclosed.closure_eq]
  exact hdense.closure_range

end Monoidal

end Stacks.SectionRingProjMorphism.ToSpecZero

end
