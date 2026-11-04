module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesFibered
public import StacksFrontier.AlgebraicGeometry.Quot.StackOfSpacesLimitPreservingUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.ClosedImmersionMorphismDescent
import StacksFrontier.CategoryTheory.FiberedCategory.HomLift

/-!
# The stack of curves is limit preserving

The stack `Curves` of families of curves over the big fppf site of `Spec(ℤ)` is limit preserving
in the sense of Stacks 07XL: for an inverse system of affine schemes `Tᵢ` of the site with limit
`T`, the comparison `colim Curves_{Tᵢ} ⥤ Curves_T` is an equivalence of categories. This is the
content of Stacks 0D55, which is not registered here; it is proved as an unregistered helper
in the form of the hypothesis `hlim` of
`AlgebraicGeometry.isSmoothOverIntegers_nodal_of_isLimitPreserving` and its companions.

The proof is the source's. The embedding (0D50) of `Curves` into the stack
`Spaces'_{fp, flat, proper}` of finitely presented, flat and proper families of algebraic spaces is
fully faithful, and its image consists of the families whose structure morphism has relative
dimension at most one. The larger stack is limit preserving (Stacks 0D1I,
`AlgebraicGeometry.isLimitPreserving_cartesianProperFlatFiberedCategory`), so morphisms of
families of curves descend, and so do the equalities between them. An object of `Curves_T` is the
base change of a finitely presented, flat and proper family over some `Tᵢ`, and the bound on the
relative dimension descends to a later stage by Stacks 0D4K.

The comparison being an equivalence is read through the three stage-descent conditions
`Deformation.Artin.DescentObj`, `Deformation.Artin.DescentHom` and `Deformation.Artin.DescentEq`.

## Main results

* `AlgebraicGeometry.C1590Private.descentEq_of_comp` and
  `AlgebraicGeometry.C1590Private.descentHom_of_comp`: descent of equalities and of morphisms
  pass to a full subcategory stable under pullback.
* `AlgebraicGeometry.C1590Private.propertyDescendsUnderConvention_relativeDimensionLE`:
  Stacks 0D4K in the form `AlgebraicGeometry.Space.PropertyDescendsUnderConvention`.
* `AlgebraicGeometry.C1590Private.descentObj_curvesProjectionOver`: descent of families of
  curves to a stage.
* `AlgebraicGeometry.C1590Private.isLimitPreserving_curvesFiberedCategory`: the stack of curves
  is limit preserving.

## Implementation notes

An object of a fibre `p.Fiber V` is a subtype element `⟨a, (h : p.obj a = V)⟩`. The fibre of
`F ⋙ q` and that of `q` are compared by reading `⟨a, h⟩` as `⟨F.obj a, h⟩`, which needs the
subtype under `Functor.Fiber` to be visible at instance transparency; `Functor.Fiber` is therefore
made locally `implicit_reducible`, as in
`StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStageDescent`.

## References

* [Stacks Project, Tag 0D55](https://stacks.math.columbia.edu/tag/0D55)
* [Stacks Project, Tag 0D1I](https://stacks.math.columbia.edu/tag/0D1I)
* [Stacks Project, Tag 0D4K](https://stacks.math.columbia.edu/tag/0D4K)
* [Stacks Project, Tag 0D50](https://stacks.math.columbia.edu/tag/0D50)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.C1590Private

attribute [local implicit_reducible] Functor.Fiber

/-! ### Stage descent along a full subcategory -/

section Transfer

open Deformation.Artin

variable {C : Type*} [Category C] {X : Type*} [Category X] {Y : Type*} [Category Y]
  (F : X ⥤ Y) (q : Y ⥤ C)

/-- An object of the fibre of `F ⋙ q`, read in the fibre of `q`. -/
abbrev fiberImage {V : C} (x : (F ⋙ q).Fiber V) : q.Fiber V :=
  ⟨F.obj x.1, x.2⟩

variable {I : Type*} [Category I] (D : I ⥤ C) (c : Cone D) [F.Full] [F.Faithful]
  [(F ⋙ q).IsFibered]

omit [F.Full] in
/-- **Descent of equalities passes to a full subcategory.** Let `F : X ⥤ Y` be fully faithful and
`F ⋙ q` fibred. If `q` is fibred in groupoids and equalities of vertical morphisms descend for
`q`, they descend for `F ⋙ q`. -/
theorem descentEq_of_comp (hq : q.IsFiberedInGroupoids) (h : DescentEq q D c) :
    DescentEq (F ⋙ q) D c := by
  intro i xi yi x δ hδ ψ ψ' hψ hψ' hδψ
  have hδ' := (isHomLift_comp_iff F q _ δ).1 hδ
  have hψF := (isHomLift_comp_iff F q _ ψ).1 hψ
  have hψ'F := (isHomLift_comp_iff F q _ ψ').1 hψ'
  obtain ⟨k, s, xk, dx, hdx, heq⟩ := h i (fiberImage F q xi) (fiberImage F q yi)
    (fiberImage F q x) (F.map δ) hδ' (F.map ψ) (F.map ψ') hψF hψ'F
    (by rw [← F.map_comp, ← F.map_comp, hδψ])
  let a := IsPreFibered.pullbackObj (p := F ⋙ q) xi.2 (D.map s)
  let da : a ⟶ xi.1 := IsPreFibered.pullbackMap (p := F ⋙ q) xi.2 (D.map s)
  have hda : q.IsHomLift (D.map s) (F.map da) := (isHomLift_comp_iff F q _ da).1 inferInstance
  have := hq.isStronglyCartesian_homLift (D.map s) dx
  refine ⟨k, s, ⟨a, IsPreFibered.pullbackObj_proj xi.2 (D.map s)⟩, da,
    inferInstance, F.map_injective ?_⟩
  rw [F.map_comp, F.map_comp, ← IsCartesian.fac q (D.map s) dx (F.map da), Category.assoc,
    Category.assoc, heq]

/-- **Descent of morphisms passes to a full subcategory.** Let `F : X ⥤ Y` be fully faithful and
`F ⋙ q` fibred. If `q` is fibred in groupoids and vertical morphisms descend for `q`, they descend
for `F ⋙ q`. -/
theorem descentHom_of_comp (hq : q.IsFiberedInGroupoids) (h : DescentHom q D c) :
    DescentHom (F ⋙ q) D c := by
  intro i xi yi x y δ ε hδ hε φ hφ
  have hδ' := (isHomLift_comp_iff F q _ δ).1 hδ
  have hε' := (isHomLift_comp_iff F q _ ε).1 hε
  have hφ' := (isHomLift_comp_iff F q _ φ).1 hφ
  obtain ⟨k, s, xk, yk, dx, dy, δk, ψ, hdx, hdy, hδk, hψ, h₁, h₂⟩ :=
    h i (fiberImage F q xi) (fiberImage F q yi) (fiberImage F q x) (fiberImage F q y)
      (F.map δ) (F.map ε) hδ' hε' (F.map φ) hφ'
  let ax := IsPreFibered.pullbackObj (p := F ⋙ q) xi.2 (D.map s)
  let dax : ax ⟶ xi.1 := IsPreFibered.pullbackMap (p := F ⋙ q) xi.2 (D.map s)
  let ay := IsPreFibered.pullbackObj (p := F ⋙ q) yi.2 (D.map s)
  let day : ay ⟶ yi.1 := IsPreFibered.pullbackMap (p := F ⋙ q) yi.2 (D.map s)
  have : q.IsHomLift (D.map s) (F.map dax) := (isHomLift_comp_iff F q _ dax).1 inferInstance
  have : q.IsHomLift (D.map s) (F.map day) := (isHomLift_comp_iff F q _ day).1 inferInstance
  have := hq.isStronglyCartesian_homLift (D.map s) dx
  have := hq.isStronglyCartesian_homLift (D.map s) (F.map dax)
  have := hq.isStronglyCartesian_homLift (D.map s) (F.map day)
  let mx : F.obj ax ⟶ xk.1 := IsCartesian.map q (D.map s) dx (F.map dax)
  let nx : xk.1 ⟶ F.obj ax := IsCartesian.map q (D.map s) (F.map dax) dx
  let ny : yk.1 ⟶ F.obj ay := IsCartesian.map q (D.map s) (F.map day) dy
  have hnm : nx ≫ mx = 𝟙 xk.1 := by
    have : q.IsHomLift (𝟙 (D.obj k)) (𝟙 xk.1) := IsHomLift.id xk.2
    apply IsCartesian.ext q (D.map s) dx
    simp only [Category.assoc, mx, nx, IsCartesian.fac, Category.id_comp]
  have hnx : nx ≫ F.map dax = dx := IsCartesian.fac q (D.map s) (F.map dax) dx
  have hny : ny ≫ F.map day = dy := IsCartesian.fac q (D.map s) (F.map day) dy
  refine ⟨k, s, ⟨ax, IsPreFibered.pullbackObj_proj xi.2 (D.map s)⟩,
    ⟨ay, IsPreFibered.pullbackObj_proj yi.2 (D.map s)⟩, dax, day,
    F.preimage (δk ≫ nx), F.preimage (mx ≫ ψ ≫ ny), inferInstance, inferInstance,
    (isHomLift_comp_iff F q _ _).2 (by rw [F.map_preimage]; infer_instance),
    (isHomLift_comp_iff F q _ _).2 (by rw [F.map_preimage]; infer_instance),
    F.map_injective ?_, F.map_injective ?_⟩
  · rw [F.map_comp, F.map_preimage, Category.assoc, hnx, h₁]
  · simp only [F.map_comp, F.map_preimage, Category.assoc]
    rw [hny, reassoc_of% hnm, h₂]

end Transfer

/-! ### Descent of the bound on the relative dimension -/

section RelativeDimension

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Being locally of finite type with relative dimension at most `d` is stable under base change
between algebraic spaces (part (1) of Stacks 04NS). -/
theorem baseChangeStable_relativeDimensionLE (d : ℕ) :
    StackOfSpacesLimit.BaseChangeStable (B := B) (S := S) (hS := hS)
      (fun f => Space.IsLocallyOfFiniteType B S hS f ∧
        Space.HasRelativeDimensionLE d B S hS f) :=
  fun {_ _ _ _ g' _ _ _} hX' hX hY' hY sq hf =>
    ⟨StackOfSpacesLimit.baseChangeStable_isLocallyOfFiniteType hX' hX hY' hY sq hf.1,
      fun x' => by
        obtain ⟨e, he, hrel⟩ := hf.2 (Space.pointsMap B S hS _ g' x')
        exact ⟨e, he, (Space.hasRelativeDimensionAt_iff_of_isPullback B S hS sq hX hY' hY hf.1
          x' e).1 hrel⟩⟩

/-- **Stacks 0D4K, under the convention of Section 70.2**, in the form
`AlgebraicGeometry.Space.PropertyDescendsUnderConvention`: for a morphism `f₀ : X₀ ⟶ B_{i₀}`
locally of finite type whose base change to the limit has relative dimension at most `d`, the
base change to some stage is locally of finite type with relative dimension at most `d`. -/
theorem propertyDescendsUnderConvention_relativeDimensionLE (hZ : B.Contains (⊤_ Scheme.{u}))
    (d : ℕ) :
    Space.PropertyDescendsUnderConvention B S hS hZ
      (fun f => Space.IsLocallyOfFiniteType B S hS f ∧ Space.HasRelativeDimensionLE d B S hS f)
      (fun f => Space.IsLocallyOfFiniteType B S hS f) :=
  Space.propertyDescendsUnderConvention_of_situation (baseChangeStable_relativeDimensionLE d)
    fun _ _ _ _ D hconv hP hH => by
      obtain ⟨i, hi, hdim⟩ :=
        D.exists_hasRelativeDimensionLE_mapAt_of_siteContainsBaseChangeLimits hconv d hP.2 hH
      exact ⟨i, hi, D.isLocallyOfFiniteType_mapAt hH i hi, hdim⟩

end RelativeDimension

/-! ### Descent of families of curves -/

section Curves

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- A finitely presented, flat and proper family whose structure morphism has relative dimension
at most one, read as a family of curves. Its image under the inclusion of Stacks 0D50 is the
family itself, by `AlgebraicGeometry.C1590Private.curvesToCartesianProperFlat_obj_curveFamily`. -/
def curveFamily (y : CartesianProperFlatSpaces B integerBase hZ)
    (hy : Space.HasRelativeDimensionLE 1 B integerBase hZ y.toBase) : CurveFamily B hZ where
  base := y.base
  total := y.obj.obj.left
  toBase := ObjectProperty.homMk y.toBase
  flat := y.isFlat_toBase
  proper := y.isProper_toBase
  finitePresentation := y.isFinitePresentation_toBase
  relativeDimensionLE := hy

/-- The image of `curveFamily B hZ y hy` under `curvesToCartesianProperFlat B hZ` is `y`. -/
theorem curvesToCartesianProperFlat_obj_curveFamily
    (y : CartesianProperFlatSpaces B integerBase hZ)
    (hy : Space.HasRelativeDimensionLE 1 B integerBase hZ y.toBase) :
    (curvesToCartesianProperFlat B hZ).obj (curveFamily B hZ y hy) = y :=
  rfl

/-- The inclusion of families of curves into the cartesian proper flat spaces is full. -/
private instance {B : BigFppfSite.{u}} {hZ : B.Contains integerBase} :
    (curvesToCartesianProperFlat B hZ).Full := curvesToCartesianProperFlat_full B hZ

/-- The inclusion of families of curves into the cartesian proper flat spaces is faithful. -/
private instance {B : BigFppfSite.{u}} {hZ : B.Contains integerBase} :
    (curvesToCartesianProperFlat B hZ).Faithful :=
  curvesToCartesianProperFlat_faithful B hZ

/-- The inclusion of families of curves, composed with the projection, is fibred. -/
private instance {B : BigFppfSite.{u}} {hZ : B.Contains integerBase} :
    (curvesToCartesianProperFlat B hZ ⋙ cartesianProperFlatProjection B integerBase hZ).IsFibered :=
  (curvesFiberedCategory B hZ).2.isFibered

variable {B hZ} {J : Type u} [Category.{u} J] [IsCofiltered J]
  (D : J ⥤ BigAffineFppf B integerBase hZ) {c : Cone D}
  (hc : IsLimit ((BigAffineFppf.toScheme B integerBase hZ).mapCone c))

include hc in
/-- **Descent of the bound on the relative dimension to a stage.** Let `X` be the base change to
the limit `T` of a finitely presented morphism `fi : Xᵢ ⟶ Tᵢ`. If `X ⟶ T` is locally of finite
type with relative dimension at most one, so is the base change of `fi` to some later stage. -/
private theorem exists_stage_hasRelativeDimensionLE_one_of_isPullback {i : J}
    {X Xi : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B integerBase hZ X)
    (hXi : IsAlgebraicSpace B integerBase hZ Xi) {a : X ⟶ Xi}
    {h : X ⟶ yoneda.obj ((BigAffineFppf.inclusion B integerBase hZ).obj c.pt)}
    {fi : Xi ⟶ (StackOfSpacesLimit.sys D).obj i}
    (sq : IsPullback a h fi
      (yoneda.map ((BigAffineFppf.inclusion B integerBase hZ).map (c.π.app i))))
    (hfi : Space.IsFinitePresentation B integerBase hZ fi)
    (hh : Space.IsLocallyOfFiniteType B integerBase hZ h)
    (hrel : Space.HasRelativeDimensionLE 1 B integerBase hZ h) :
    ∃ (j : J) (e : j ⟶ i),
      Space.IsLocallyOfFiniteType B integerBase hZ
        (pullback.snd fi ((StackOfSpacesLimit.sys D).map e)) ∧
      Space.HasRelativeDimensionLE 1 B integerBase hZ
        (pullback.snd fi ((StackOfSpacesLimit.sys D).map e)) := by
  let P : ∀ {X Y : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u}, (X ⟶ Y) → Prop := fun f =>
    Space.IsLocallyOfFiniteType B integerBase hZ f ∧
      Space.HasRelativeDimensionLE 1 B integerBase hZ f
  have hP : StackOfSpacesLimit.BaseChangeStable @P := baseChangeStable_relativeDimensionLE 1
  have hL := StackOfSpacesLimit.isAlgebraicSpace_limit_sys D hc
  let eT := StackOfSpacesLimit.limitIso D hc
  have hsq₀ : IsPullback (𝟙 _) (h ≫ eT.hom) h eT.inv := IsPullback.of_horiz_isIso ⟨by simp⟩
  have hPxL : P (h ≫ eT.hom) :=
    hP hX hX hL (isAlgebraicSpace_yoneda B integerBase hZ _) hsq₀ ⟨hh, hrel⟩
  have hPL : P (pullback.snd fi (limit.π (StackOfSpacesLimit.sys D) i)) :=
    StackOfSpacesLimit.of_isPullback_same hP (StackOfSpacesLimit.isPullback_limit D hc sq)
      (IsPullback.of_hasPullback fi (limit.π (StackOfSpacesLimit.sys D) i))
      (isAlgebraicSpace_pullback B integerBase hZ _ _ hXi hL
        (StackOfSpacesLimit.isAlgebraicSpace_yoneda_affine B integerBase hZ _)) hX hL hPxL
  exact StackOfSpacesLimit.exists_stage_prop B.contains_terminal D hc
    (propertyDescendsUnderConvention_relativeDimensionLE B.contains_terminal 1) hP
    StackOfSpacesLimit.baseChangeStable_isLocallyOfFiniteType i fi hXi hfi
    (Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B integerBase hZ hfi.1) hPL

include hc in
/-- **Descent of families of curves to a stage** (`Deformation.Artin.DescentObj`). A family of
curves over the limit `T` of an affine inverse system `Tᵢ` is the pullback of a family of curves
over some `Tᵢ`. By Stacks 0D1I it is the pullback of a finitely presented, flat and proper family
over some `Tᵢ`, and by Stacks 0D4K the relative dimension of that family is at most one after
base change to a later stage. -/
theorem descentObj_curvesProjectionOver :
    Deformation.Artin.DescentObj (curvesProjectionOver B hZ)
      (D ⋙ BigAffineFppf.inclusion B integerBase hZ)
      ((BigAffineFppf.inclusion B integerBase hZ).mapCone c) := by
  let F := curvesToCartesianProperFlat B hZ
  let ι := BigAffineFppf.inclusion B integerBase hZ
  have hq := cartesianProperFlatProjection_isFiberedInGroupoids B integerBase hZ
  intro x
  obtain ⟨⟨V, Xt, h, hfl, hpr, hfp, hrel⟩, hV⟩ := x
  obtain rfl : V = ι.obj c.pt := hV
  let x₀ : CurveFamily B hZ := ⟨_, Xt, h, hfl, hpr, hfp, hrel⟩
  let h₀ : Xt.obj ⟶ yoneda.obj (ι.obj c.pt) := h.hom
  obtain ⟨i, xi, δ, hδ⟩ := StackOfSpacesLimit.descentObj B.contains_terminal D hc
    (Space.modelsDescendUnderConvention B integerBase hZ B.contains_terminal)
    (Space.propertyDescendsUnderConvention_isFlat B integerBase hZ B.contains_terminal)
    (Space.propertyDescendsUnderConvention_isProper B integerBase hZ B.contains_terminal)
    ⟨F.obj x₀, rfl⟩
  obtain ⟨⟨⟨⟨⟨Xi, hXi⟩, Vi, fi⟩, hPi⟩⟩, hVi⟩ := xi
  obtain rfl : Vi = ι.obj (D.obj i) := hVi
  let xi₀ : CartesianProperFlatSpaces B integerBase hZ := ⟨⟨⟨⟨Xi, hXi⟩, _, fi⟩, hPi⟩⟩
  have hδ' : (cartesianProperFlatProjection B integerBase hZ).IsHomLift (ι.map (c.π.app i)) δ :=
    hδ
  have hδr : δ.hom.hom.right = ι.map (c.π.app i) :=
    @CartesianProperFlatSpaces.hom_right_eq _ _ _ _ _ _ δ hδ
  have sqδ : IsPullback δ.hom.hom.left.hom h₀ fi
      (yoneda.map (ι.map (c.π.app i))) := by
    have := CartesianProperFlatSpaces.isPullback_hom δ
    rwa [hδr] at this
  -- The bound on the relative dimension, read over the limit of the represented presheaves.
  obtain ⟨j, e, hPj⟩ := exists_stage_hasRelativeDimensionLE_one_of_isPullback D hc Xt.property
    hXi sqδ hPi.1
    (Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B integerBase hZ hfp.1) hrel
  -- The base change to the stage `j` is a family of curves.
  let xj := CartesianProperFlatSpaces.baseChange xi₀ (ι.map (D.map e))
  let Cj := curveFamily B hZ xj hPj.2
  have : (cartesianProperFlatProjection B integerBase hZ).IsStronglyCartesian (ι.map (D.map e))
      (CartesianProperFlatSpaces.baseChangeHom xi₀ (ι.map (D.map e))) :=
    hq.isStronglyCartesian_homLift _ _
  have hw : ι.map (c.π.app i) = ι.map (c.π.app j) ≫ ι.map (D.map e) := by
    rw [← Functor.map_comp, c.w e]
  let δj : F.obj x₀ ⟶ F.obj Cj :=
    IsStronglyCartesian.map (cartesianProperFlatProjection B integerBase hZ) (ι.map (D.map e))
      (CartesianProperFlatSpaces.baseChangeHom xi₀ (ι.map (D.map e))) hw δ
  have hδj : (cartesianProperFlatProjection B integerBase hZ).IsHomLift (ι.map (c.π.app j)) δj :=
    IsStronglyCartesian.map_isHomLift (cartesianProperFlatProjection B integerBase hZ)
      (ι.map (D.map e)) (CartesianProperFlatSpaces.baseChangeHom xi₀ (ι.map (D.map e))) hw δ
  refine ⟨j, ⟨Cj, rfl⟩, F.preimage δj, ?_⟩
  show (F ⋙ cartesianProperFlatProjection B integerBase hZ).IsHomLift (ι.map (c.π.app j))
    (F.preimage δj)
  exact (isHomLift_comp_iff F (cartesianProperFlatProjection B integerBase hZ) _ _).2
    (by rwa [F.map_preimage])

include hc in
/-- **Descent of equalities of morphisms of families of curves** (`Deformation.Artin.DescentEq`),
from the corresponding statement for finitely presented, flat and proper families (Stacks 07SK)
through the full inclusion of Stacks 0D50. -/
theorem descentEq_curvesProjectionOver :
    Deformation.Artin.DescentEq (curvesProjectionOver B hZ)
      (D ⋙ BigAffineFppf.inclusion B integerBase hZ)
      ((BigAffineFppf.inclusion B integerBase hZ).mapCone c) := by
  exact descentEq_of_comp (curvesToCartesianProperFlat B hZ)
    (cartesianProperFlatProjection B integerBase hZ) _ _
    (cartesianProperFlatProjection_isFiberedInGroupoids B integerBase hZ)
    (StackOfSpacesLimit.descentEq B.contains_terminal D hc
      (Space.equalitiesDescendUnderConvention B integerBase hZ B.contains_terminal))

include hc in
/-- **Descent of morphisms of families of curves** (`Deformation.Artin.DescentHom`), from the
corresponding statement for finitely presented, flat and proper families (Stacks 07SK) through
the full inclusion of Stacks 0D50. -/
theorem descentHom_curvesProjectionOver :
    Deformation.Artin.DescentHom (curvesProjectionOver B hZ)
      (D ⋙ BigAffineFppf.inclusion B integerBase hZ)
      ((BigAffineFppf.inclusion B integerBase hZ).mapCone c) := by
  exact descentHom_of_comp (curvesToCartesianProperFlat B hZ)
    (cartesianProperFlatProjection B integerBase hZ) _ _
    (cartesianProperFlatProjection_isFiberedInGroupoids B integerBase hZ)
    (StackOfSpacesLimit.descentHom B.contains_terminal D hc
      (Space.morphismsDescendUnderConvention B integerBase hZ B.contains_terminal)
      (Space.equalitiesDescendUnderConvention B integerBase hZ B.contains_terminal))

variable (B hZ)

/-- **The stack of curves is limit preserving** (Stacks 0D55, unregistered here): for every
inverse system of affine schemes of the big fppf site of `Spec(ℤ)` whose limit of underlying
schemes is `T`, the canonical comparison `colim Curves_{Tᵢ} ⥤ Curves_T` of Stacks 07XL is an
equivalence of categories.

This is literally the hypothesis `hlim` of
`AlgebraicGeometry.isSmoothOverIntegers_nodal_of_isLimitPreserving` and its companions, at index
categories in the universe of the schemes. -/
theorem isLimitPreserving_curvesFiberedCategory :
    Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B integerBase hZ
      (curvesFiberedCategory B hZ) := by
  intro I _ _ D c hc
  have hp := (curvesFiberedCategory B hZ).2
  have : (curvesFiberedCategory B hZ).val.p.IsFibered := hp.isFibered
  exact
    { faithful := Deformation.Artin.faithful_of_descentEq _ hp _ _
        (descentEq_curvesProjectionOver D hc)
      full := Deformation.Artin.full_of_descentHom _ hp _ _
        (descentHom_curvesProjectionOver D hc)
      essSurj := Deformation.Artin.essSurj_of_descentObj _ hp _ _
        (descentObj_curvesProjectionOver D hc) }

end Curves

end AlgebraicGeometry.C1590Private

end
