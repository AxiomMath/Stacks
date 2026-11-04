module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.ExceptionalComponentsMeet
public import StacksFrontier.AlgebraicGeometry.Curves.Models.MinimalModelExistence
public import StacksFrontier.AlgebraicGeometry.Curves.Models.MinimalModelNumericalType
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ModelGenericFibreIso
public import StacksFrontier.AlgebraicGeometry.Scheme.ClosureOfOpenSubscheme
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveOpenImmersion
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.FactorizationBirationalMaps

/-!
# Uniqueness of the minimal model

Let `R` be a discrete valuation ring with fraction field `K` and let `C` be a smooth projective
curve over `K` with `H⁰(C, 𝒪_C) = K` and genus `> 0`. This file proves [Stacks, Tag 0C6B]: there
is a unique minimal model of `C`.

## The argument

Existence is [Stacks, Tag 0C2W], `Stacks.Models.exists_isMinimalModel`. For uniqueness let `X` and
`Y` be minimal models. The identifications of their generic fibres with `C` give a birational map
`X ⇢ Y` over `R`, which [Stacks, Tag 0C5H] dominates by a sequence of blowups `Z ⟶ X` at closed
points together with a morphism `h : Z ⟶ Y`; by [Stacks, Tag 0C5R] `h` is again a sequence of
blowups at closed points, so we are in the source's diagram
`X = X₀ ← X₁ ← ⋯ ← Xₙ = Z → ⋯ → Y₀ = Y`.

*The claim.* Every exceptional curve of the first kind `E` on a stage `Yᵢ` is contracted to a point
in `Y` (`exists_isModel_and_const_on_exceptionalCurve_of_pointBlowupChain`). On `Y` there is none;
at a blowup, `E` is either the new exceptional curve, or meets it — impossible by
[Stacks, Tag 0C6A], since `g > 0` — or is disjoint from it, and then descends
(`exists_isExceptionalCurveOfFirstKind_of_disjoint`).

*The induction.* Peeling the blowups of `Z ⟶ X` one at a time, the exceptional curve of each is
contracted by `h`, so `h` factors through the blowup by [Stacks, Tag 0C5J], and the factor is a
sequence of blowups by [Stacks, Tag 0C5R]
(`exists_comp_eq_of_pointBlowupChain_of_isMinimalModel`). At the end `h` factors through
`Z ⟶ X` by a morphism `φ : X ⟶ Y` over `R`, which is a sequence of blowups; as `X` contains no
exceptional curve, `φ` is an isomorphism. It is compatible with the identifications with `C`
because `h` agrees with the birational map over the generic fibre, and it is unique because a
morphism of models is determined on the dense generic fibre.

## Main results

* `Stacks.Models.exists_isModel_and_const_on_exceptionalCurve_of_pointBlowupChain` — the claim.
* `Stacks.Models.existsUnique_iso_of_isMinimalModel` — two minimal models are uniquely isomorphic.
* `Stacks.Models.exists_isMinimalModel_and_existsUnique_iso` — [Stacks, Tag 0C6B].

## References

* [Stacks Project, Tag 0C6B](https://stacks.math.columbia.edu/tag/0C6B)
* [Stacks Project, Tag 0C6A](https://stacks.math.columbia.edu/tag/0C6A)
* [Stacks Project, Tag 0C5R](https://stacks.math.columbia.edu/tag/0C5R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.ResolutionOfSurfaces

universe u

namespace Stacks.Models

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-! ### Transporting exceptional curves -/

/-- An exceptional curve of the first kind is carried along an isomorphism. -/
theorem hasExceptionalCurveOfFirstKind_of_iso {X W : Scheme.{u}} (i : X ≅ W)
    (h : W.HasExceptionalCurveOfFirstKind) : X.HasExceptionalCurveOfFirstKind := by
  obtain ⟨k, hk, D, e, hE⟩ := h
  exact ⟨k, hk, D.comap i.hom, _,
    Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.comap (j := i.hom) (hE := hE)
      (h := fun x _ => (Scheme.homeoOfIso i).surjective x)⟩

/-- A point blowup is an isomorphism away from its centre. -/
private theorem isIso_pointBlowUpToBase_restrict_compl {V : Scheme.{u}} [IsLocallyNoetherian V]
    {v : V} (hv : IsClosed ({v} : Set V)) :
    IsIso (pointBlowUpToBase hv ∣_ ⟨({v} : Set V)ᶜ, hv.isOpen_compl⟩) :=
  isIso_blowUp_restrict_compl_support (Scheme.IdealSheafData.vanishingIdeal ⟨{v}, hv⟩)

/-- If `π` is an isomorphism over the open `U` and the support of `D` lies over `U`, then the
transport of `D` to `U` along `π` has the same image in the target as `D`. -/
private theorem image_support_comap_inv_restrict {X V : Scheme.{u}} (π : X ⟶ V) (U : V.Opens)
    [IsIso (π ∣_ U)] (D : X.IdealSheafData) (hD : (D.support : Set X) ⊆ (π ⁻¹ᵁ U : Set X)) :
    U.ι.base '' (((D.comap (π ⁻¹ᵁ U).ι).comap (asIso (π ∣_ U)).inv).support : Set U) =
      π.base '' D.support := by
  apply subset_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    refine ⟨(π ⁻¹ᵁ U).ι ((asIso (π ∣_ U)).inv y), ?_, ?_⟩
    · rwa [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
        Set.mem_preimage, Scheme.IdealSheafData.support_comap,
        TopologicalSpace.Closeds.coe_preimage, Set.mem_preimage] at hy
    · have h₂ := morphismRestrict_base_coe π U ((asIso (π ∣_ U)).inv y)
      change ((π ∣_ U) ((asIso (π ∣_ U)).inv y)).1 = _ at h₂
      rw [show (π ∣_ U) ((asIso (π ∣_ U)).inv y) = y from
        (Scheme.homeoOfIso (asIso (π ∣_ U))).apply_symm_apply _] at h₂
      exact h₂.symm
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨(asIso (π ∣_ U)).hom ⟨x, hD hx⟩, ?_, morphismRestrict_base_coe π U ⟨x, hD hx⟩⟩
    have hinv : (asIso (π ∣_ U)).inv ((asIso (π ∣_ U)).hom ⟨x, hD hx⟩) = ⟨x, hD hx⟩ :=
      (Scheme.homeoOfIso (asIso (π ∣_ U))).symm_apply_apply _
    rwa [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
      Set.mem_preimage, hinv, Scheme.IdealSheafData.support_comap,
      TopologicalSpace.Closeds.coe_preimage]

/-- The closure of an exceptional curve of the first kind on an open subscheme is one on the whole
scheme, when it stays inside the open subscheme. -/
private theorem exists_isExceptionalCurveOfFirstKind_closureIdeal {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] {I : U.IdealSheafData} {k : Type u} [Field k]
    {e : projectiveLineProj k ≅ I.subscheme} (hE : I.IsExceptionalCurveOfFirstKind k e)
    (h : ((Stacks.IdealSheaf.closureIdeal j I).support : Set X) ⊆ Set.range j.base) :
    ∃ e' : projectiveLineProj k ≅ (Stacks.IdealSheaf.closureIdeal j I).subscheme,
      (Stacks.IdealSheaf.closureIdeal j I).IsExceptionalCurveOfFirstKind k e' := by
  have : IsIntegral I.subscheme :=
    AlgebraicGeometry.isIntegral_subscheme_of_iso_projectiveLineProj I k e
  obtain ⟨e', hE'⟩ : ∃ e' : projectiveLineProj k ≅
      ((Stacks.IdealSheaf.closureIdeal j I).comap j).subscheme,
      ((Stacks.IdealSheaf.closureIdeal j I).comap j).IsExceptionalCurveOfFirstKind k e' := by
    rw [Stacks.IdealSheaf.closureIdeal_comap]
    exact ⟨e, hE⟩
  exact ⟨_, Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.of_comap (j := j) (h := h)
    (hE := hE')⟩

/-- **An exceptional curve disjoint from the exceptional curve of a point blowup descends.** If
`D` is an exceptional curve of the first kind on the blowup of `V` at a closed point `v`, disjoint
from the exceptional curve of the blowup, then its image in `V` is again an exceptional curve of
the first kind. -/
theorem exists_isExceptionalCurveOfFirstKind_of_disjoint {V : Scheme.{u}} [IsLocallyNoetherian V]
    {v : V}
    (hv : IsClosed ({v} : Set V)) {D : (pointBlowUp hv).IdealSheafData} {k : Type u} [Field k]
    {e : projectiveLineProj k ≅ D.subscheme} (hE : D.IsExceptionalCurveOfFirstKind k e)
    (hdisj : ∀ x ∈ (D.support : Set (pointBlowUp hv)), pointBlowUpToBase hv x ≠ v) :
    ∃ (D' : V.IdealSheafData) (e' : projectiveLineProj k ≅ D'.subscheme),
      D'.IsExceptionalCurveOfFirstKind k e' ∧
        ∀ x ∈ (D.support : Set (pointBlowUp hv)),
          pointBlowUpToBase hv x ∈ (D'.support : Set V) := by
  set π := pointBlowUpToBase hv
  let Vo : V.Opens := ⟨({v} : Set V)ᶜ, hv.isOpen_compl⟩
  have : IsIso (π ∣_ Vo) := isIso_pointBlowUpToBase_restrict_compl hv
  have hDO : (D.support : Set (pointBlowUp hv)) ⊆ Set.range (π ⁻¹ᵁ Vo).ι.base := by
    rwa [Scheme.Opens.range_ι]
  have hEV := Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.comap
    (j := (asIso (π ∣_ Vo)).inv)
    (hE := Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.comap (j := (π ⁻¹ᵁ Vo).ι)
      (hE := hE) (h := hDO))
    (h := fun x _ => (Scheme.homeoOfIso (asIso (π ∣_ Vo)).symm).surjective x)
  have himg := image_support_comap_inv_restrict π Vo D hdisj
  have hD'supp : ((Stacks.IdealSheaf.closureIdeal Vo.ι
      ((D.comap (π ⁻¹ᵁ Vo).ι).comap (asIso (π ∣_ Vo)).inv)).support : Set V) ⊆
        Set.range Vo.ι.base := by
    intro x hx
    rw [Stacks.IdealSheaf.closureIdeal_support] at hx
    replace hx := Closeds.mem_closure.1 hx
    rw [himg, (π.isClosedMap _ D.support.isClosed).closure_eq] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [Scheme.Opens.range_ι]
    exact hdisj y hy
  obtain ⟨e', hE'⟩ := exists_isExceptionalCurveOfFirstKind_closureIdeal Vo.ι hEV hD'supp
  refine ⟨_, e', hE', fun x hx => ?_⟩
  rw [Stacks.IdealSheaf.closureIdeal_support]
  refine Closeds.mem_closure.2 ?_
  rw [himg]
  exact subset_closure ⟨x, hx, rfl⟩

/-- **[Stacks, Tag 0C6A] for two distinct meeting exceptional curves.** Two distinct exceptional
curves of the first kind on a regular proper model which meet force the curve to have genus zero:
both are components of the special fibre. -/
theorem genus_eq_zero_of_isExceptionalCurveOfFirstKind_of_ne (S : RegularProperModelSituation.{u})
    {D₁ D₂ : S.X.IdealSheafData} {k₁ k₂ : Type u} [Field k₁] [Field k₂]
    {e₁ : projectiveLineProj k₁ ≅ D₁.subscheme} {e₂ : projectiveLineProj k₂ ≅ D₂.subscheme}
    (h₁ : D₁.IsExceptionalCurveOfFirstKind k₁ e₁) (h₂ : D₂.IsExceptionalCurveOfFirstKind k₂ e₂)
    (hne : D₁ ≠ D₂) (hmeet : Nonempty (D₁ ⊔ D₂).subscheme) : genus S.C_to_K = 0 := by
  classical
  obtain ⟨Z₁, rfl⟩ := S.exists_eq_specialFiberComponentIdeal_of_iso_projectiveLineProj D₁ k₁ e₁
  obtain ⟨Z₂, rfl⟩ := S.exists_eq_specialFiberComponentIdeal_of_iso_projectiveLineProj D₂ k₂ e₂
  exact S.genus_eq_zero_of_isExceptionalCurveOfFirstKind (fun h => hne (by rw [h])) h₁ h₂ hmeet

/-- A point lies in the support of the exceptional curve of a point blowup iff it lies over the
point. -/
private theorem mem_support_exceptionalIdeal_iff {V : Scheme.{u}} {v : V}
    (hv : IsClosed ({v} : Set V)) {x : pointBlowUp hv} :
    x ∈ ((exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal
      (⟨{v}, hv⟩ : Closeds V))).support : Set (pointBlowUp hv)) ↔ pointBlowUpToBase hv x = v := by
  rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]
  exact Iff.rfl

/-- A point of the support of the exceptional curve of a point blowup lies over the point. -/
theorem pointBlowUpToBase_eq_of_mem_support {V : Scheme.{u}} {v : V} (hv : IsClosed ({v} : Set V))
    {x : pointBlowUp hv}
    (hx : x ∈ ((exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal
      (⟨{v}, hv⟩ : Closeds V))).support : Set (pointBlowUp hv))) :
    pointBlowUpToBase hv x = v :=
  (mem_support_exceptionalIdeal_iff hv).1 hx

/-- A point of the support of `D` is a point of the closed subscheme `D`. -/
private theorem subschemeι_mem_support {X : Scheme.{u}} (D : X.IdealSheafData) (z : D.subscheme) :
    D.subschemeι z ∈ (D.support : Set X) := by
  rw [← Scheme.IdealSheafData.range_subschemeι]
  exact ⟨z, rfl⟩

/-- A morphism constant on a closed subscheme `D` takes the constant value on the support of `D`. -/
private theorem apply_eq_of_mem_support {X Y : Scheme.{u}} {D : X.IdealSheafData} {g : X ⟶ Y}
    {y : Y} (hy : ∀ z : D.subscheme, g (D.subschemeι z) = y) {x : X}
    (hx : x ∈ (D.support : Set X)) : g x = y := by
  rw [← Scheme.IdealSheafData.range_subschemeι] at hx
  obtain ⟨z, rfl⟩ := hx
  exact hy z

/-- The blowup of an integral regular surface at a closed point with two-dimensional local ring
carries its exceptional curve as an exceptional curve of the first kind. -/
private theorem exists_isExceptionalCurveOfFirstKind_exceptionalIdeal_of_isIntegralRegularSurface
    {V : Scheme.{u}} (hV : IsIntegralRegularSurface V) {w : V} (hw : IsClosed ({w} : Set V))
    (hdim : ringKrullDim (V.presheaf.stalk w) = 2) :
    ∃ e : projectiveLineProj (IsLocalRing.ResidueField (V.presheaf.stalk w)) ≅
        (exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds V))).subscheme,
      Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind
        (exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds V)))
        (IsLocalRing.ResidueField (V.presheaf.stalk w)) e :=
  Stacks.Blowup.exists_isExceptionalCurveOfFirstKind_exceptionalIdeal_vanishingIdeal w hw
    (AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hV.isRegular w) hdim

/-- Exceptional curves of the first kind contracted by `g` are contracted by `π ≫ g` for an
isomorphism `π`. -/
private theorem exists_const_comp_of_isIso {W V Y : Scheme.{u}} (π : W ⟶ V) [IsIso π] (g : V ⟶ Y)
    (hg : ∀ (D : V.IdealSheafData) (k : Type u) [Field k] (e : projectiveLineProj k ≅ D.subscheme),
      D.IsExceptionalCurveOfFirstKind k e → ∃ y : Y, ∀ z : D.subscheme, g (D.subschemeι z) = y)
    {D : W.IdealSheafData} {k : Type u} [Field k] {e : projectiveLineProj k ≅ D.subscheme}
    (hE : D.IsExceptionalCurveOfFirstKind k e) :
    ∃ y : Y, ∀ z : D.subscheme, (π ≫ g) (D.subschemeι z) = y := by
  obtain ⟨y, hy⟩ := hg (D.comap (inv π)) k _
    (Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.comap (j := inv π) (hE := hE)
      (h := fun x _ => (Scheme.homeoOfIso (asIso (inv π))).surjective x))
  refine ⟨y, fun z => ?_⟩
  have hmem : π (D.subschemeι z) ∈ ((D.comap (inv π)).support : Set V) := by
    rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
      Set.mem_preimage, ← Scheme.Hom.comp_apply, IsIso.hom_inv_id]
    exact subschemeι_mem_support D z
  rw [Scheme.Hom.comp_apply]
  exact apply_eq_of_mem_support hy hmem

/-- **Exceptional curves on a point blowup not meeting its exceptional curve are contracted.**
If `g` contracts every exceptional curve of the first kind on `V`, then `pointBlowUpToBase hw ≫ g`
contracts every exceptional curve of the first kind on the blowup of `V` at `w` which is either the
exceptional curve `E` of the blowup or disjoint from it. -/
private theorem exists_const_comp_pointBlowUpToBase {V Y : Scheme.{u}} [IsLocallyNoetherian V]
    {w : V} (hw : IsClosed ({w} : Set V)) (g : V ⟶ Y)
    (hg : ∀ (D : V.IdealSheafData) (k : Type u) [Field k] (e : projectiveLineProj k ≅ D.subscheme),
      D.IsExceptionalCurveOfFirstKind k e → ∃ y : Y, ∀ z : D.subscheme, g (D.subschemeι z) = y)
    {D : (pointBlowUp hw).IdealSheafData} {k : Type u} [Field k]
    {e : projectiveLineProj k ≅ D.subscheme} (hE : D.IsExceptionalCurveOfFirstKind k e)
    (hmeet : D ≠ exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds V)) →
      ¬ Nonempty (D ⊔ exceptionalIdeal
        (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds V))).subscheme) :
    ∃ y : Y, ∀ z : D.subscheme, (pointBlowUpToBase hw ≫ g) (D.subschemeι z) = y := by
  classical
  set E := exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds V))
    with hEdef
  by_cases hDE : D = E
  · refine ⟨g w, fun z => ?_⟩
    have hzE : D.subschemeι z ∈ (E.support : Set (pointBlowUp hw)) := by
      rw [← hDE]
      exact subschemeι_mem_support D z
    rw [Scheme.Hom.comp_apply]
    exact congrArg g (pointBlowUpToBase_eq_of_mem_support hw hzE)
  have hdisj : ∀ x ∈ (D.support : Set (pointBlowUp hw)), pointBlowUpToBase hw x ≠ w := by
    intro x hx hxw
    apply hmeet hDE
    have hxE : x ∈ (E.support : Set (pointBlowUp hw)) :=
      (mem_support_exceptionalIdeal_iff hw).2 hxw
    have : x ∈ ((D ⊔ E).support : Set (pointBlowUp hw)) := by
      rw [Scheme.IdealSheafData.support_sup]
      exact ⟨hx, hxE⟩
    rw [← Scheme.IdealSheafData.range_subschemeι] at this
    obtain ⟨z, -⟩ := this
    exact ⟨z⟩
  obtain ⟨D', e'', hE'', hmap⟩ := exists_isExceptionalCurveOfFirstKind_of_disjoint hw hE hdisj
  obtain ⟨y, hy⟩ := hg D' k e'' hE''
  refine ⟨y, fun z => ?_⟩
  rw [Scheme.Hom.comp_apply]
  exact apply_eq_of_mem_support hy (hmap _ (subschemeι_mem_support D z))

/-! ### Exceptional curves on a blowup of a minimal model of positive genus -/

/-- **The claim in the proof of [Stacks, Tag 0C6B].** Let `Y` be a minimal model of a curve of
positive genus and let `q : W ⟶ Y` be a sequence of blowups at closed points. Then every stage is
a regular proper model, and `q` contracts every exceptional curve of the first kind on `W` to a
point.

By induction on the sequence. On `Y` itself there is no exceptional curve. At a blowup
`Bl_w W ⟶ W` an exceptional curve `D` is either the exceptional curve `E` of the blowup, which goes
to `w`, or meets `E` — impossible, by [Stacks, Tag 0C6A], as the genus is positive — or is disjoint
from `E`, and then its image in `W` is an exceptional curve, contracted by induction. -/
theorem exists_isModel_and_const_on_exceptionalCurve_of_pointBlowupChain {C Y : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsCurve K c] [Smooth c] (hg : 0 < genus c)
    (q₀ : Y ⟶ Spec (.of R)) (eY : C ≅ pullback q₀ (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hY : IsMinimalModel c q₀ eY) {T : Set Y} {W : Scheme.{u}} {q : W ⟶ Y}
    (hq : PointBlowupChain Y T W q) :
    (∃ eW : C ≅ pullback (q ≫ q₀) (Spec.map (CommRingCat.ofHom (algebraMap R K))),
      IsModel c (q ≫ q₀) eW ∧ IsProper (q ≫ q₀) ∧ IsRegular W) ∧
    ∀ (D : W.IdealSheafData) (k : Type u) [Field k] (e : projectiveLineProj k ≅ D.subscheme),
      D.IsExceptionalCurveOfFirstKind k e → ∃ y : Y, ∀ z : D.subscheme, q (D.subschemeι z) = y := by
  classical
  have := hY.isIso_globalSections
  have := hY.isProper
  have hproj := hY.curveProjective
  induction hq with
  | refl =>
    refine ⟨?_, fun D k _ e hE =>
      (hY.not_hasExceptionalCurveOfFirstKind ⟨k, inferInstance, D, e, hE⟩).elim⟩
    rw [Category.id_comp]
    exact ⟨eY, hY.isModel, hY.isProper, hY.regular⟩
  | @step V qV hqV w hw hwT ih =>
    obtain ⟨⟨eV, hmodV, hpropV, hregV⟩, ihE⟩ := ih
    have hVsurf := isIntegralRegularSurface_of_isModel c hproj (qV ≫ q₀) eV hmodV hregV
    obtain ⟨e', hmod', hprop', hreg', -⟩ :=
      exists_isModel_pointBlowUp c hproj (qV ≫ q₀) eV hmodV hregV hw
    let π := pointBlowUpToBase hw
    refine ⟨?_, fun D k _ e hE => ?_⟩
    · rw [Category.assoc]
      exact ⟨e', hmod', hprop', hreg'⟩
    have := hVsurf.isIntegral
    have := hVsurf.isNoetherian
    rcases Stacks.ResolutionOfSurfaces.isIso_pointBlowUpToBase_or_ringKrullDim_stalk_eq_two hVsurf
      w hw with hiso | hdim2
    · exact exists_const_comp_of_isIso π qV ihE hE
    obtain ⟨eE, hEE⟩ :=
      exists_isExceptionalCurveOfFirstKind_exceptionalIdeal_of_isIntegralRegularSurface hVsurf hw
        hdim2
    have : IsProper (π ≫ qV ≫ q₀) := hprop'
    exact exists_const_comp_pointBlowUpToBase hw qV ihE hE fun hDE hmeet => hg.ne' <|
      genus_eq_zero_of_isExceptionalCurveOfFirstKind_of_ne
        (regularProperModelSituation c hproj (π ≫ qV ≫ q₀) e' hmod' hreg') hE hEE hDE hmeet

/-- **A sequence of blowups contracting its exceptional curves factors through a point blowup.**
Let `h` be a sequence of blowups of `Y` from the blowup of an integral regular surface `V` at a
closed point with two-dimensional local ring, such that every sequence of blowups of `Y` contracts
its exceptional curves. Then `h` factors through the blowup by [Stacks, Tag 0C5J], compatibly with
morphisms to a base. -/
private theorem exists_comp_eq_pointBlowUpToBase_of_factorsAsPointBlowups {V Y S : Scheme.{u}}
    (hV : IsIntegralRegularSurface V) {w : V} (hw : IsClosed ({w} : Set V))
    (hdim : ringKrullDim (V.presheaf.stalk w) = 2)
    (hclaim : ∀ {T : Set Y} {W : Scheme.{u}} {q : W ⟶ Y}, PointBlowupChain Y T W q →
      ∀ (D : W.IdealSheafData) (k : Type u) [Field k] (e : projectiveLineProj k ≅ D.subscheme),
        D.IsExceptionalCurveOfFirstKind k e → ∃ y : Y, ∀ z : D.subscheme, q (D.subschemeι z) = y)
    {h : pointBlowUp hw ⟶ Y} (hfac : FactorsAsPointBlowups Y Set.univ (pointBlowUp hw) h)
    (q₀ : Y ⟶ S) (g : V ⟶ S) (hover : h ≫ q₀ = pointBlowUpToBase hw ≫ g) :
    ∃ h' : V ⟶ Y, pointBlowUpToBase hw ≫ h' = h ∧ h' ≫ q₀ = g := by
  have := hV.isNoetherian
  obtain ⟨eE, hEE⟩ :=
    exists_isExceptionalCurveOfFirstKind_exceptionalIdeal_of_isIntegralRegularSurface hV hw hdim
  obtain ⟨W', f', hchain, ei, rfl⟩ := hfac
  have hconst := exists_const_comp_of_isIso ei.hom f' (hclaim hchain) hEE
  have hcontr : IsContractionOfExceptionalCurve (exceptionalIdeal
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds V))) (pointBlowUpToBase hw) :=
    isContractionOfExceptionalCurve_blowUpToBase w hw
      (AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hV.isRegular w) hdim
  obtain ⟨h', hh', -⟩ := existsUnique_comp_eq_of_isContractionOfExceptionalCurve _ _ hcontr _
    hconst
  obtain ⟨y₀, hy₀⟩ := hconst
  obtain ⟨χ, -, huniq⟩ := existsUnique_comp_eq_of_isContractionOfExceptionalCurve _ _ hcontr
    ((ei.hom ≫ f') ≫ q₀) ⟨q₀ y₀, fun z => by rw [Scheme.Hom.comp_apply, hy₀ z]⟩
  refine ⟨h', hh', ?_⟩
  rw [huniq (h' ≫ q₀) (show pointBlowUpToBase hw ≫ h' ≫ q₀ = (ei.hom ≫ f') ≫ q₀ by
    rw [← Category.assoc, hh']), huniq g hover.symm]

/-- A morphism whose composite with a separated morphism is proper is proper. -/
private theorem isProper_of_comp_eq {X Y S : Scheme.{u}} {f : X ⟶ Y} {q : Y ⟶ S} {g : X ⟶ S}
    [IsSeparated q] [IsProper g] (h : f ≫ q = g) : IsProper f := by
  subst h
  exact IsProper.of_comp f q

/-- **The induction of the proof of [Stacks, Tag 0C6B].** Let `Y` be a minimal model of a curve of
positive genus, `X` an integral regular surface proper over `R`, and `pZ : Z ⟶ X` a sequence of
blowups at closed points. A morphism `h : Z ⟶ Y` over `R` which is birational and a sequence of
blowups factors through `pZ`.

At each blowup of the sequence the exceptional curve is contracted by `h`, by the claim
`exists_isModel_and_const_on_exceptionalCurve_of_pointBlowupChain`, so `h` factors through the
blowup by [Stacks, Tag 0C5J], and the factor is again a sequence of blowups by
[Stacks, Tag 0C5R]. -/
theorem exists_comp_eq_of_pointBlowupChain_of_isMinimalModel {C X Y : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsCurve K c] [Smooth c]
    (q₀ : Y ⟶ Spec (.of R)) (eY : C ≅ pullback q₀ (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hY : IsMinimalModel c q₀ eY)
    (hclaim : ∀ {T : Set Y} {W : Scheme.{u}} {q : W ⟶ Y}, PointBlowupChain Y T W q →
      ∀ (D : W.IdealSheafData) (k : Type u) [Field k] (e : projectiveLineProj k ≅ D.subscheme),
        D.IsExceptionalCurveOfFirstKind k e → ∃ y : Y, ∀ z : D.subscheme, q (D.subschemeι z) = y)
    (p₀ : X ⟶ Spec (.of R)) [IsProper p₀]
    (hX : IsIntegralRegularSurface X) {T : Set X} {Z : Scheme.{u}} {pZ : Z ⟶ X}
    (hp : PointBlowupChain X T Z pZ) :
    ∀ h : Z ⟶ Y, FactorsAsPointBlowups Y Set.univ Z h → IsBirational h →
      h ≫ q₀ = pZ ≫ p₀ → ∃ φ : X ⟶ Y, pZ ≫ φ = h := by
  classical
  have := hY.isIso_globalSections
  have := hY.isProper
  have hYsurf := isIntegralRegularSurface_of_isModel c hY.curveProjective q₀ eY hY.isModel
    hY.regular
  have := hYsurf.isIntegral
  induction hp with
  | refl => exact fun h _ _ _ => ⟨h, Category.id_comp h⟩
  | @step V qV hqV w hw hwT ih =>
    intro h hfac hbir hover
    obtain ⟨hVsurf, hqVprop⟩ :=
      isIntegralRegularSurface_and_isProper_of_pointBlowupChain_unconditional hqV hX
    have := hVsurf.isIntegral
    have := hVsurf.isNoetherian
    have := (isIntegralRegularSurface_blowUp_vanishingIdeal_singleton V w hw hVsurf).isIntegral
    let π := pointBlowUpToBase hw
    have hπbir : IsBirational π := isBirational_blowUpToBase _
      (vanishingIdeal_singleton_ne_bot hVsurf.topologicalKrullDim_eq w hw)
    rcases Stacks.ResolutionOfSurfaces.isIso_pointBlowUpToBase_or_ringKrullDim_stalk_eq_two hVsurf
      w hw with hiso | hdim2
    · obtain ⟨W', f', hchain, ei, hei⟩ := hfac
      have hfac' : FactorsAsPointBlowups Y Set.univ V (inv π ≫ h) :=
        ⟨W', f', hchain, asIso (inv π) ≪≫ ei, by simp [hei]⟩
      have hbir' : IsBirational (inv π ≫ h) :=
        (isBirational_of_isOpenImmersion (inv π)).comp hbir
      have hover' : (inv π ≫ h) ≫ q₀ = qV ≫ p₀ := by
        rw [Category.assoc, hover]
        simp [π]
      obtain ⟨φ, hφ⟩ := ih (inv π ≫ h) hfac' hbir' hover'
      refine ⟨φ, ?_⟩
      rw [Category.assoc, hφ]
      simp [π]
    · obtain ⟨h', hh', hover'⟩ := exists_comp_eq_pointBlowUpToBase_of_factorsAsPointBlowups
        hVsurf hw hdim2 hclaim hfac q₀ (qV ≫ p₀) (hover.trans (Category.assoc _ _ _))
      have hprop' : IsProper h' := isProper_of_comp_eq hover'
      have hbir' : IsBirational h' := isBirational_of_comp_left π h' hπbir (hh' ▸ hbir)
      obtain ⟨φ, hφ⟩ := ih h' (factorsAsPointBlowups_of_isProper_of_isBirational h' hYsurf hVsurf
        hprop' hbir') hbir' hover'
      exact ⟨φ, by rw [Category.assoc, hφ, hh']⟩

/-! ### Morphisms of models -/

/-- **Morphisms of models are determined by the curve.** Two morphisms between models of `C` over
`R`, both compatible with the structure morphisms and with the identifications of the generic
fibres, agree when the source is integral and the target separated over `R`: they agree on the
generic fibre, which is dense. -/
theorem eq_of_comp_eq_of_genericFiber {C X Y : Scheme.{u}} [Nonempty C] (p : X ⟶ Spec (.of R))
    (q : Y ⟶ Spec (.of R)) [IsSeparated q] [IsIntegral X]
    (eX : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (eY : C ≅ pullback q (Spec.map (CommRingCat.ofHom (algebraMap R K)))) {φ₁ φ₂ : X ⟶ Y}
    (h₁ : φ₁ ≫ q = p) (h₂ : φ₂ ≫ q = p)
    (c₁ : eX.hom ≫ pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ φ₁ =
      eY.hom ≫ pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (c₂ : eX.hom ≫ pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ φ₂ =
      eY.hom ≫ pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :
    φ₁ = φ₂ := by
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
    genericFiberSpec_isOpenImmersion
  set j := pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  have : IsDominant j :=
    ⟨j.opensRange.2.dense ⟨j (eX.hom (Classical.arbitrary C)), _, rfl⟩⟩
  refine ext_of_isDominant_of_isSeparated q (h₁.trans h₂.symm) j ?_
  rw [← cancel_epi eX.hom, c₁, c₂]

/-- A sequence of blowups at closed points of an integral regular surface whose source contains no
exceptional curve of the first kind is an isomorphism: each blowup at a point with
two-dimensional local ring produces one. -/
theorem isIso_of_pointBlowupChain_of_not_hasExceptionalCurveOfFirstKind {Y : Scheme.{u}}
    (hY : IsIntegralRegularSurface Y) {T : Set Y} {W : Scheme.{u}} {f : W ⟶ Y}
    (hf : PointBlowupChain Y T W f) (hW : ¬ W.HasExceptionalCurveOfFirstKind) : IsIso f := by
  induction hf with
  | refl => infer_instance
  | @step V g hg w hw hwT ih =>
    obtain ⟨hVsurf, -⟩ :=
      isIntegralRegularSurface_and_isProper_of_pointBlowupChain_unconditional hg hY
    have := hVsurf.isNoetherian
    rcases Stacks.ResolutionOfSurfaces.isIso_pointBlowUpToBase_or_ringKrullDim_stalk_eq_two hVsurf
      w hw with hiso | hdim2
    · exact IsIso.comp_isIso' hiso
        (ih fun h => hW (hasExceptionalCurveOfFirstKind_of_iso (asIso (pointBlowUpToBase hw)) h))
    · obtain ⟨eE, hEE⟩ :=
        exists_isExceptionalCurveOfFirstKind_exceptionalIdeal_of_isIntegralRegularSurface hVsurf hw
          hdim2
      exact (hW ⟨_, inferInstance, _, eE, hEE⟩).elim

/-- A sequence of blowups whose source contains no exceptional curve is an isomorphism. -/
theorem isIso_of_factorsAsPointBlowups_of_not_hasExceptionalCurveOfFirstKind {X Y : Scheme.{u}}
    (hY : IsIntegralRegularSurface Y) {f : X ⟶ Y} (hf : FactorsAsPointBlowups Y Set.univ X f)
    (hX : ¬ X.HasExceptionalCurveOfFirstKind) : IsIso f := by
  obtain ⟨W, g, hg, e, rfl⟩ := hf
  have : IsIso g := isIso_of_pointBlowupChain_of_not_hasExceptionalCurveOfFirstKind hY hg
    fun h => hX (hasExceptionalCurveOfFirstKind_of_iso e h)
  infer_instance

/-! ### Uniqueness -/

local notation "ιRK" => Spec.map (CommRingCat.ofHom (algebraMap R K))

/-- The partial isomorphism between two models of `C` given by the identifications of their
generic fibres with `C`. -/
def modelPartialIso {C X Y : Scheme.{u}} [Nonempty C] [IsIntegral X] [IsIntegral Y]
    (p : X ⟶ Spec (.of R)) (q : Y ⟶ Spec (.of R)) (eX : C ≅ pullback p ιRK)
    (eY : C ≅ pullback q ιRK) : X.PartialIso Y :=
  haveI : IsOpenImmersion ιRK := genericFiberSpec_isOpenImmersion
  { source := (pullback.fst p ιRK).opensRange
    dense_source := (pullback.fst p ιRK).opensRange.2.dense
      ⟨pullback.fst p ιRK (eX.hom (Classical.arbitrary C)), _, rfl⟩
    target := (pullback.fst q ιRK).opensRange
    dense_target := (pullback.fst q ιRK).opensRange.2.dense
      ⟨pullback.fst q ιRK (eY.hom (Classical.arbitrary C)), _, rfl⟩
    iso := (pullback.fst p ιRK).isoOpensRange.symm ≪≫ eX.symm ≪≫ eY ≪≫
      (pullback.fst q ιRK).isoOpensRange }

/-- The identification of the generic fibre of the source with the domain of
`modelPartialIso`. -/
def modelPartialIsoToDomain {C X Y : Scheme.{u}} [Nonempty C] [IsIntegral X] [IsIntegral Y]
    (p : X ⟶ Spec (.of R)) (q : Y ⟶ Spec (.of R)) (eX : C ≅ pullback p ιRK)
    (eY : C ≅ pullback q ιRK) :
    pullback p ιRK ⟶ (modelPartialIso p q eX eY).toPartialMap.domain.toScheme :=
  haveI : IsOpenImmersion ιRK := genericFiberSpec_isOpenImmersion
  (pullback.fst p ιRK).isoOpensRange.hom

/-- The morphism `modelPartialIsoToDomain` is an isomorphism. -/
instance {C X Y : Scheme.{u}} [Nonempty C] [IsIntegral X] [IsIntegral Y]
    (p : X ⟶ Spec (.of R)) (q : Y ⟶ Spec (.of R)) (eX : C ≅ pullback p ιRK)
    (eY : C ≅ pullback q ιRK) : IsIso (modelPartialIsoToDomain p q eX eY) :=
  haveI : IsOpenImmersion ιRK := genericFiberSpec_isOpenImmersion
  inferInstanceAs (IsIso (pullback.fst p ιRK).isoOpensRange.hom)

/-- Composing `modelPartialIsoToDomain` with the inclusion of the domain of `modelPartialIso`
is the projection from the generic fibre of the source. -/
theorem modelPartialIsoToDomain_ι {C X Y : Scheme.{u}} [Nonempty C] [IsIntegral X]
    [IsIntegral Y] (p : X ⟶ Spec (.of R)) (q : Y ⟶ Spec (.of R)) (eX : C ≅ pullback p ιRK)
    (eY : C ≅ pullback q ιRK) :
    modelPartialIsoToDomain p q eX eY ≫ (modelPartialIso p q eX eY).toPartialMap.domain.ι =
      pullback.fst p ιRK :=
  have : IsOpenImmersion ιRK := genericFiberSpec_isOpenImmersion
  Scheme.Hom.isoOpensRange_hom_ι _

/-- On the generic fibre of the source, `modelPartialIso` is the identification of generic fibres
`eX.inv ≫ eY.hom` followed by the projection to the target model. -/
theorem modelPartialIsoToDomain_hom {C X Y : Scheme.{u}} [Nonempty C] [IsIntegral X]
    [IsIntegral Y] (p : X ⟶ Spec (.of R)) (q : Y ⟶ Spec (.of R)) (eX : C ≅ pullback p ιRK)
    (eY : C ≅ pullback q ιRK) :
    modelPartialIsoToDomain p q eX eY ≫ (modelPartialIso p q eX eY).toPartialMap.hom =
      eX.inv ≫ eY.hom ≫ pullback.fst q ιRK := by
  have : IsOpenImmersion ιRK := genericFiberSpec_isOpenImmersion
  show (pullback.fst p ιRK).isoOpensRange.hom ≫ ((pullback.fst p ιRK).isoOpensRange.symm ≪≫
    eX.symm ≪≫ eY ≪≫ (pullback.fst q ιRK).isoOpensRange).hom ≫
      (pullback.fst q ιRK).opensRange.ι = _
  simp [Scheme.Hom.isoOpensRange_hom_ι]

/-- The partial isomorphism between two models of `C` is a partial map over `R`. -/
private theorem modelPartialIso_hom_comp {C X Y : Scheme.{u}} [Nonempty C] [IsIntegral X]
    [IsIntegral Y] (c : C ⟶ Spec (.of K)) (p : X ⟶ Spec (.of R)) (q : Y ⟶ Spec (.of R))
    (eX : C ≅ pullback p ιRK) (eY : C ≅ pullback q ιRK) (hX : IsModel c p eX)
    (hY : IsModel c q eY) :
    (modelPartialIso p q eX eY).toPartialMap.hom ≫ q =
      (modelPartialIso p q eX eY).toPartialMap.domain.ι ≫ p := by
  have : IsOpenImmersion ιRK := genericFiberSpec_isOpenImmersion
  rw [← cancel_epi (modelPartialIsoToDomain p q eX eY),
    reassoc_of% modelPartialIsoToDomain_hom p q eX eY,
    reassoc_of% modelPartialIsoToDomain_ι p q eX eY]
  have key : eX.inv ≫ eY.hom ≫ pullback.snd q ιRK = pullback.snd p ιRK := by
    rw [hY.2.2.2, ← hX.2.2.2, Iso.inv_hom_id_assoc]
  rw [pullback.condition, pullback.condition, reassoc_of% key]

/-- A morphism of models through which a resolution of `modelPartialIso` factors is compatible
with the identifications of the generic fibres with `C`. -/
private theorem comp_eq_of_resolves_modelPartialIso {C X Y Z : Scheme.{u}} [Nonempty C]
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z] (c : C ⟶ Spec (.of K)) (p : X ⟶ Spec (.of R))
    (q : Y ⟶ Spec (.of R)) [IsSeparated q] (eX : C ≅ pullback p ιRK) (eY : C ≅ pullback q ιRK)
    (hX : IsModel c p eX) (hY : IsModel c q eY) {pZ : Z ⟶ X} (hpZ : Function.Surjective pZ.base)
    {h : Z ⟶ Y}
    (hagree : pullback.fst pZ (modelPartialIso p q eX eY).toPartialMap.domain.ι ≫ h =
      pullback.snd pZ (modelPartialIso p q eX eY).toPartialMap.domain.ι ≫
        (modelPartialIso p q eX eY).toPartialMap.hom)
    {φ : X ⟶ Y} (hφ : pZ ≫ φ = h) (hφq : φ ≫ q = p) :
    eX.hom ≫ pullback.fst p ιRK ≫ φ = eY.hom ≫ pullback.fst q ιRK := by
  have : IsOpenImmersion ιRK := genericFiberSpec_isOpenImmersion
  have : IsDominant (pullback.snd pZ (modelPartialIso p q eX eY).toPartialMap.domain.ι) := by
    refine ⟨Function.Surjective.denseRange fun u => ?_⟩
    obtain ⟨z, hz⟩ := hpZ ((modelPartialIso p q eX eY).toPartialMap.domain.ι u)
    obtain ⟨t, -, ht⟩ := Scheme.Pullback.exists_preimage_pullback z u hz
    exact ⟨t, ht⟩
  have hUι : (modelPartialIso p q eX eY).toPartialMap.domain.ι ≫ φ =
      (modelPartialIso p q eX eY).toPartialMap.hom := by
    refine ext_of_isDominant_of_isSeparated q ?_
      (pullback.snd pZ (modelPartialIso p q eX eY).toPartialMap.domain.ι) ?_
    · rw [Category.assoc, hφq]
      exact (modelPartialIso_hom_comp c p q eX eY hX hY).symm
    · rw [← hagree, ← Category.assoc, ← pullback.condition, Category.assoc, hφ]
  calc eX.hom ≫ pullback.fst p ιRK ≫ φ
      = eX.hom ≫ modelPartialIsoToDomain p q eX eY ≫
          (modelPartialIso p q eX eY).toPartialMap.domain.ι ≫ φ := by
        rw [reassoc_of% modelPartialIsoToDomain_ι p q eX eY]
    _ = eY.hom ≫ pullback.fst q ιRK := by
        rw [hUι, modelPartialIsoToDomain_hom, Iso.hom_inv_id_assoc]

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- Two morphisms from a reduced scheme to `Spec R` agree if they agree after a dominant
morphism. -/
private theorem comp_eq_of_comp_eq_of_isDominant {X Y Z : Scheme.{u}} [IsReduced X] (pZ : Z ⟶ X)
    [IsDominant pZ] {φ : X ⟶ Y} {h : Z ⟶ Y} {p : X ⟶ Spec (.of R)} {q : Y ⟶ Spec (.of R)}
    (hφ : pZ ≫ φ = h) (hS : h ≫ q = pZ ≫ p) : φ ≫ q = p := by
  refine ext_of_isDominant_of_isSeparated
    (Spec.map (CommRingCat.ofHom ((Int.castRingHom R).comp
      (ULift.ringEquiv.{0, u} (R := ℤ)).toRingHom))) ?_ pZ ?_
  · exact specULiftZIsTerminal.hom_ext _ _
  · rw [← Category.assoc, hφ, hS]

/-- **Two minimal models are uniquely isomorphic as models, granted that every blowup of the
second contracts its exceptional curves.** If every exceptional curve of the first kind on every
sequence of blowups at closed points of `Y` is contracted to a point in `Y`, there is exactly one
isomorphism of models `X ≅ Y`. For a curve of positive genus the hypothesis is the claim of
[Stacks, Tag 0C6B]; for genus zero its failure is what [Stacks, Tag 0CDA] exploits. -/
theorem existsUnique_iso_of_isMinimalModel_of_const {C X Y : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsCurve K c] [Smooth c] (p : X ⟶ Spec (.of R))
    (q : Y ⟶ Spec (.of R))
    (eX : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (eY : C ≅ pullback q (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hX : IsMinimalModel c p eX) (hY : IsMinimalModel c q eY)
    (hclaim : ∀ {T : Set Y} {W : Scheme.{u}} {f : W ⟶ Y}, PointBlowupChain Y T W f →
      ∀ (D : W.IdealSheafData) (k : Type u) [Field k] (e : projectiveLineProj k ≅ D.subscheme),
        D.IsExceptionalCurveOfFirstKind k e → ∃ y : Y, ∀ z : D.subscheme, f (D.subschemeι z) = y) :
    ∃! φ : X ≅ Y, φ.hom ≫ q = p ∧
      eX.hom ≫ pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ φ.hom =
        eY.hom ≫ pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  classical
  have := hX.isIso_globalSections
  have := hX.isProper
  have := hY.isProper
  have hproj := hX.curveProjective
  have hXs := isIntegralRegularSurface_of_isModel c hproj p eX hX.isModel hX.regular
  have hYs := isIntegralRegularSurface_of_isModel c hproj q eY hY.isModel hY.regular
  have := hXs.isIntegral
  have := hYs.isIntegral
  have := hXs.isNoetherian
  let : X.Over (Spec (.of R)) := ⟨p⟩
  let : Y.Over (Spec (.of R)) := ⟨q⟩
  have : IsProper (Y ↘ Spec (.of R)) := (inferInstance : IsProper q)
  have hover : (modelPartialIso p q eX eY).toPartialMap.IsOver (Spec (.of R)) :=
    Scheme.PartialMap.isOver_iff.mpr (modelPartialIso_hom_comp c p q eX eY hX.isModel hY.isModel)
  obtain ⟨T, Z, pZ, h, -, -, -, hchain, hS, hagree⟩ :=
    exists_pointBlowupChain_resolving_partialMap_of_isNoetherian (S := Spec (.of R))
      (fun x => AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hXs.isRegular x)
      (fun x => ringKrullDim_stalk_le_two hXs x) (modelPartialIso p q eX eY).toPartialMap
  obtain ⟨hZs, hpZprop⟩ :=
    isIntegralRegularSurface_and_isProper_of_pointBlowupChain_unconditional hchain hXs
  have := hZs.isIntegral
  have hpZbir : IsBirational pZ :=
    isBirational_of_pointBlowupChain_of_isIntegralRegularSurface hchain hXs
  have hpZsurj : Function.Surjective pZ.base :=
    surjective_of_pointBlowupChain_of_isIntegralRegularSurface hchain hXs
  have hhbir : IsBirational h :=
    isBirational_of_resolves_partialIso (modelPartialIso p q eX eY) pZ h hpZbir hagree
  have hS' : h ≫ q = pZ ≫ p := hS
  obtain ⟨φ, hφ⟩ := exists_comp_eq_of_pointBlowupChain_of_isMinimalModel c q eY hY hclaim p hXs
    hchain h (factorsAsPointBlowups_of_isProper_of_isBirational h hYs hZs
      (isProper_of_comp_eq hS') hhbir) hhbir hS'
  have : Surjective pZ := ⟨hpZsurj⟩
  have hφq : φ ≫ q = p := comp_eq_of_comp_eq_of_isDominant pZ hφ hS'
  have hφbir : IsBirational φ := isBirational_of_comp_left pZ φ hpZbir (hφ ▸ hhbir)
  have : IsIso φ := isIso_of_factorsAsPointBlowups_of_not_hasExceptionalCurveOfFirstKind hYs
    (factorsAsPointBlowups_of_isProper_of_isBirational φ hYs hXs (isProper_of_comp_eq hφq) hφbir)
    hX.not_hasExceptionalCurveOfFirstKind
  have hcompat := comp_eq_of_resolves_modelPartialIso c p q eX eY hX.isModel hY.isModel hpZsurj
    hagree hφ hφq
  exact ⟨asIso φ, ⟨hφq, hcompat⟩, fun ψ ⟨hψq, hψc⟩ =>
    Iso.ext (eq_of_comp_eq_of_genericFiber p q eX eY hψq hφq hψc hcompat)⟩

/-- **Any two minimal models of a curve of positive genus are uniquely isomorphic as models.**
This is the uniqueness half of [Stacks, Tag 0C6B]: there is exactly one isomorphism `X ≅ Y` over
`R` identifying the two embeddings of the generic fibre `C`. -/
theorem existsUnique_iso_of_isMinimalModel {C X Y : Scheme.{u}} (c : C ⟶ Spec (.of K))
    [IsCurve K c] [Smooth c] (hg : 0 < genus c) (p : X ⟶ Spec (.of R)) (q : Y ⟶ Spec (.of R))
    (eX : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (eY : C ≅ pullback q (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hX : IsMinimalModel c p eX) (hY : IsMinimalModel c q eY) :
    ∃! φ : X ≅ Y, φ.hom ≫ q = p ∧
      eX.hom ≫ pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ φ.hom =
        eY.hom ≫ pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
  existsUnique_iso_of_isMinimalModel_of_const c p q eX eY hX hY fun hchain =>
    (exists_isModel_and_const_on_exceptionalCurve_of_pointBlowupChain c hg q eY hY hchain).2

/-- **Stacks Project, Tag 0C6B.** Let `C` be a smooth projective curve over `K` with
`H⁰(C, 𝒪_C) = K` and genus `> 0`. There is a unique minimal model for `C`: a minimal model exists,
and any two minimal models are isomorphic by a unique isomorphism of models, that is, over `R`
and compatible with the identifications of their generic fibres with `C`. -/
@[stacks 0C6B]
theorem exists_isMinimalModel_and_existsUnique_iso {C : Scheme.{u}} (c : C ⟶ Spec (.of K))
    [IsCurve K c] [Smooth c] (hproj : Stacks.HProjective.IsHProjective c)
    (hH0 : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)) (hg : 0 < genus c) :
    (∃ (X : Scheme.{u}) (p : X ⟶ Spec (.of R))
      (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
      IsMinimalModel c p e) ∧
    ∀ {X Y : Scheme.{u}} (p : X ⟶ Spec (.of R)) (q : Y ⟶ Spec (.of R))
      (eX : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K))))
      (eY : C ≅ pullback q (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
      IsMinimalModel c p eX → IsMinimalModel c q eY →
        ∃! φ : X ≅ Y, φ.hom ≫ q = p ∧
          eX.hom ≫ pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ φ.hom =
            eY.hom ≫ pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
  ⟨exists_isMinimalModel c hproj hH0, fun p q eX eY hX hY =>
    existsUnique_iso_of_isMinimalModel c hg p q eX eY hX hY⟩

end Stacks.Models

end
