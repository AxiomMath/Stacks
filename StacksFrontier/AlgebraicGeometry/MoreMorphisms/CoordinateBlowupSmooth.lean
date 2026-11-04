module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.AffineCharts
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CoordinateBlowup

/-!
# Smoothness of the blowup of affine space along a coordinate affine subspace

Fix a commutative ring `R` and integers `m, n ≥ 0`. Write affine `(m + n)`-space over `R` as
`Spec A` with `A = R[x₁, …, x_m, y₁, …, y_n]`, the polynomial ring on `Fin m ⊕ Fin n`, and let
`Z = 𝔸^m_R ⟶ 𝔸^{m+n}_R` be the closed immersion of
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/CoordinateSubspace.lean`, which sets the last `n`
coordinates to zero. This file proves that the blowup of `𝔸^{m+n}_R` in the ideal sheaf of `Z` is
smooth over `R`, which is the second assertion of Stacks Tag 0H1H.

The ring-theoretic content — that each standard affine chart of the blowup is a polynomial ring
over `R` on the variables `x₁, …, x_m`, the pivot `y_i` and the ratios `t_j = y_j/y_i` — is
`Stacks.MoreMorphisms.coordinateChart_equiv_polynomial` in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/CoordinateBlowup.lean`. What is added here is the
geometry: the standard charts attached to a *generating family* of the ideal already cover the
blowup, the structure morphism of a chart over the base is `Spec` of the canonical map of
`Γ(X, U)` into its blowup algebra, and smoothness is local at the source.

## Main definitions

* `Stacks.Blowup.exists_ringEquiv_affineBlowupAlgebra` transports an affine blowup algebra along
  an isomorphism of the base ring and a compatible isomorphism of the localizations.
* `AlgebraicGeometry.blowupChartι` is the standard affine chart `Spec Γ(X, U)[ℐ(U)/a]` of the
  blowup of a scheme, as a morphism into the blowup.
* `Stacks.MoreMorphisms.coordinateIdeal` is the ideal sheaf of the coordinate affine subspace.

## Main results

* `AlgebraicGeometry.exists_mem_range_blowupChartι`: the charts attached to a generating family of
  `ℐ(U)` already cover the part of the blowup lying over `U`. The covering statement
  `AlgebraicGeometry.blownUpAffine_chart_cover` ranges over *every* section of `ℐ(U)`, which is
  not enough here: for a section that is not one of the `y_i` the chart is an open subscheme of
  the blowup with no polynomial presentation, so smoothness on it is a consequence of the theorem
  rather than an input to it.
* `AlgebraicGeometry.blowupChartι_comp_blowUpToBase`: the chart's structure morphism.
* `Stacks.MoreMorphisms.coordinateBlowupChart_smooth`: each standard chart of the coordinate
  blowup is smooth over `R`.
* `Stacks.MoreMorphisms.blowUp_smooth_of_pos` and `Stacks.MoreMorphisms.blowUp_smooth`: the
  coordinate blowup is smooth over `R`.

## Implementation notes

The blowup here is `AlgebraicGeometry.blowUp`, the relative `Proj` of the Rees algebra sheaf of
`StacksFrontier/AlgebraicGeometry/Blowup/ReesAlgebra/BlowUp.lean`; its charts are the ones of
`StacksFrontier/AlgebraicGeometry/Blowup/ReesAlgebra/AffineCharts.lean`. (The repository carries a
second, independently glued blowup, `Stacks.Blowup.blowUp` in
`StacksFrontier/AlgebraicGeometry/Blowup/ReesSheafData.lean`, with its own chart layer in
`StacksFrontier/AlgebraicGeometry/Blowup/AffineChart.lean`. The two are isomorphic but not equal,
and nothing here uses the second.)

Three facts about the graded ring of local sections of the Rees algebra are what make the
generating-family covering statement work, and all three are proved by mapping to `Γ(X, U)`
through `AlgebraicGeometry.reesToBase`, which is injective on each homogeneous piece: the
degree-one element attached to a section is zero on zero, additive, and semilinear over the base.
The base ring of the graded ring is its own degree-zero part, so the semilinearity has to be
stated through `AlgebraicGeometry.reesSituation.sectionRingBaseMap` rather than as a scalar
action.

`Stacks.MoreMorphisms.blowUp_smooth` carries the hypothesis `0 < n` because the statement of
Tag 0H1H does; it is **not used**, and `Stacks.MoreMorphisms.blowUp_smooth_of_pos` is the same
theorem without it. Nothing has migrated into another hypothesis: for `n = 0` the ideal sheaf is
zero, the Rees algebra is concentrated in degree zero, its irrelevant ideal is `0`, and so the
blowup is empty and the statement is vacuous — which is exactly how the covering statement
discharges it, the index type `Fin 0` being empty.

## References

* [Stacks Project, Tag 0H1H](https://stacks.math.columbia.edu/tag/0H1H)
* [Stacks Project, Tag 052Q](https://stacks.math.columbia.edu/tag/052Q)
* [Stacks Project, Tag 0804](https://stacks.math.columbia.edu/tag/0804)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.RelativeProj.Situation

universe u v

/-! ### Smoothness of a polynomial algebra -/

namespace Stacks.MoreMorphisms

/-- `Spec` of a smooth ring map is a smooth morphism of schemes. -/
public theorem smooth_specMap {A B : CommRingCat.{u}} (f : A ⟶ B)
    (hf : f.hom.Smooth) : Smooth (Spec.map f) :=
  (HasRingHomProperty.Spec_iff (P := @Smooth) (Q := RingHom.Smooth)).mpr hf

/-- A polynomial ring on finitely many variables is smooth over its coefficient ring. -/
public theorem smooth_mvPolynomial_C (A : Type u) [CommRing A] (σ : Type v) [Finite σ] :
    (MvPolynomial.C : A →+* MvPolynomial σ A).Smooth :=
  RingHom.smooth_algebraMap.mpr ⟨inferInstance, inferInstance⟩

/-- A ring map identifying the target with a polynomial ring on finitely many variables over the
source, compatibly with the coefficient inclusion, is smooth. -/
public theorem smooth_of_mvPolynomial_ringEquiv {A B : Type u} [CommRing A] [CommRing B]
    (σ : Type v) [Finite σ] (f : A →+* B) (F : B ≃+* MvPolynomial σ A)
    (hF : ∀ r, F (f r) = MvPolynomial.C r) : f.Smooth := by
  rw [show f = (F.symm : MvPolynomial σ A →+* B).comp MvPolynomial.C from
    RingHom.ext fun r ↦ (RingEquiv.eq_symm_apply F).mpr (hF r)]
  exact RingHom.Smooth.comp (smooth_mvPolynomial_C A σ)
    (RingHom.Smooth.of_bijective F.symm.bijective)

end Stacks.MoreMorphisms

/-! ### Transport of the affine blowup algebra along an isomorphism -/

namespace Stacks.Blowup

variable {S₀ S₁ L₀ L₁ : Type*} [CommRing S₀] [CommRing S₁] [CommRing L₀] [CommRing L₁]
  [Algebra S₀ L₀] [Algebra S₁ L₁] (ψ : S₀ ≃+* S₁) (Λ : L₀ ≃+* L₁) (b : S₀) (J : Ideal S₀)

/-- A compatible ring isomorphism sends the algebra generated by a set into a subalgebra of the
target once it does so on the generators. -/
private theorem map_mem_of_mem_adjoin (φ : S₀ ≃+* S₁) (f : L₀ ≃+* L₁)
    (hf : ∀ x : S₀, f (algebraMap S₀ L₀ x) = algebraMap S₁ L₁ (φ x)) (T : Set L₀)
    (A : Subalgebra S₁ L₁) (hT : ∀ z ∈ T, f z ∈ A) {x : L₀} (hx : x ∈ Algebra.adjoin S₀ T) :
    f x ∈ A := by
  induction hx using Algebra.adjoin_induction with
  | mem z hz => exact hT z hz
  | algebraMap r =>
    rw [hf]
    exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | mul x y _ _ hx hy => simpa using mul_mem hx hy

section
variable (hΛ : ∀ x : S₀, Λ (algebraMap S₀ L₀ x) = algebraMap S₁ L₁ (ψ x))
  [IsLocalization.Away b L₀] [IsLocalization.Away (ψ b) L₁]

include hΛ in
/-- A compatible pair of ring isomorphisms carries the fraction `y / b` to `ψ y / ψ b`. -/
public theorem map_mk'_of_ringEquiv (y : S₀) :
    Λ (IsLocalization.mk' L₀ y ⟨b, Submonoid.mem_powers b⟩) =
      IsLocalization.mk' L₁ (ψ y) ⟨ψ b, Submonoid.mem_powers (ψ b)⟩ := by
  rw [IsLocalization.eq_mk'_iff_mul_eq, ← hΛ y, ← hΛ b, ← map_mul]
  exact congrArg Λ (IsLocalization.mk'_spec L₀ y ⟨b, Submonoid.mem_powers b⟩)

include hΛ in
/-- A compatible pair of ring isomorphisms carries the affine blowup algebra into the affine
blowup algebra of the transported data. -/
public theorem mapsTo_affineBlowupAlgebra {x : L₀} (hx : x ∈ affineBlowupAlgebra J b L₀) :
    Λ x ∈ affineBlowupAlgebra (J.map (ψ : S₀ →+* S₁)) (ψ b) L₁ := by
  refine map_mem_of_mem_adjoin ψ Λ hΛ _ _ ?_ hx
  rintro z ⟨y, hy, rfl⟩
  rw [map_mk'_of_ringEquiv ψ Λ b hΛ]
  exact Algebra.subset_adjoin ⟨ψ y, Ideal.mem_map_of_mem _ hy, rfl⟩

include hΛ in
/-- The same statement for the inverse isomorphisms. -/
public theorem mapsTo_symm_affineBlowupAlgebra {w : L₁}
    (hw : w ∈ affineBlowupAlgebra (J.map (ψ : S₀ →+* S₁)) (ψ b) L₁) :
    Λ.symm w ∈ affineBlowupAlgebra J b L₀ := by
  refine map_mem_of_mem_adjoin ψ.symm Λ.symm (fun x ↦ Λ.symm_apply_eq.mpr ?_) _ _ ?_ hw
  · rw [hΛ, ψ.apply_symm_apply]
  · rintro z ⟨y', hy', rfl⟩
    obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_of_equiv ψ y').mp hy'
    rw [← map_mk'_of_ringEquiv ψ Λ b hΛ, RingEquiv.symm_apply_apply]
    exact Algebra.subset_adjoin ⟨y, hy, rfl⟩

include hΛ in
/-- **Transport of the affine blowup algebra.** An isomorphism of the base ring together with a
compatible isomorphism of the localizations induces an isomorphism of the affine blowup
algebras, given on elements by the isomorphism of the localizations. -/
public theorem exists_ringEquiv_affineBlowupAlgebra :
    ∃ E : affineBlowupAlgebra J b L₀ ≃+*
        affineBlowupAlgebra (J.map (ψ : S₀ →+* S₁)) (ψ b) L₁,
      ∀ x : affineBlowupAlgebra J b L₀, (E x : L₁) = Λ (x : L₀) := by
  refine ⟨RingEquiv.ofBijective
    (((Λ : L₀ →+* L₁).comp (affineBlowupAlgebra J b L₀).val.toRingHom).codRestrict _
      fun x ↦ mapsTo_affineBlowupAlgebra ψ Λ b J hΛ x.2) ⟨?_, ?_⟩, fun _ ↦ rfl⟩
  · exact fun x y hxy ↦ Subtype.ext (Λ.injective (congrArg Subtype.val hxy))
  · rintro ⟨w, hw⟩
    exact ⟨⟨Λ.symm w, mapsTo_symm_affineBlowupAlgebra ψ Λ b J hΛ hw⟩,
      Subtype.ext (Λ.apply_symm_apply w)⟩

end

/-- The transport statement with the target data given up to equality, which is how it is met in
practice: the ideal and the element on the far side arrive from an unrelated construction. -/
public theorem exists_ringEquiv_affineBlowupAlgebra' (J' : Ideal S₁) (a : S₁)
    [IsLocalization.Away b L₀] [IsLocalization.Away a L₁]
    (hΛ : ∀ x : S₀, Λ (algebraMap S₀ L₀ x) = algebraMap S₁ L₁ (ψ x))
    (hJ' : J' = J.map (ψ : S₀ →+* S₁)) (ha : a = ψ b) :
    ∃ E : affineBlowupAlgebra J b L₀ ≃+* affineBlowupAlgebra J' a L₁,
      ∀ x : affineBlowupAlgebra J b L₀, (E x : L₁) = Λ (x : L₀) := by
  subst hJ' ha
  exact exists_ringEquiv_affineBlowupAlgebra ψ Λ b J hΛ

end Stacks.Blowup

/-! ### The charts attached to a generating family of the ideal cover the blowup -/

namespace AlgebraicGeometry

variable {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens)

/-- The structure map of the graded ring of local sections lands in degree zero. -/
public theorem sectionRingBaseMap_mem_grading_zero (r : X.presheaf.obj (op U.1)) :
    (reesSituation I).sectionRingBaseMap U.1 r ∈
      (reesSituation I).sectionRingGrading U.1 0 := by
  show (reesSituation I).sectionRingBaseMap U.1 r ∈
    Set.range (DirectSum.of ((reesSituation I).sectionPieces U.1) 0)
  rw [relativeProj_sectionRingBaseMap_apply (reesSituation I) U.1 r]
  exact ⟨_, rfl⟩

/-- The map to the base is a retraction of the structure map.

This is the form that takes the section in the structure presheaf `Γ(X, U)`;
`AlgebraicGeometry.reesToBase_sectionRingBaseMap` is the same statement with the section taken in
the sheaf of rings `X.ringCatSheaf`. The two types are definitionally equal but not
interchangeable for `rewrite`, which unifies at reducible transparency only, so both spellings
are kept. -/
public theorem reesToBase_sectionRingBaseMap' (r : X.presheaf.obj (op U.1)) :
    reesToBase I U ((reesSituation I).sectionRingBaseMap U.1 r) = r := by
  let r' : X.ringCatSheaf.obj.obj (op U.1) := r
  show reesToBase I U ((reesSituation I).sectionRingBaseMap U.1 r') = r
  let P := (reesAlgebraData I).algebra.piece 0
  let M := P.val.obj (op U.1)
  let _ : Module (X.ringCatSheaf.obj.obj (op U.1)) M := M.isModule
  rw [relativeProj_sectionRingBaseMap_apply (reesSituation I) U.1 r', reesToBase_of]
  show ((reesAlgebraData I).pieceEquiv (0 : ℤ) (by omega) U
    (r' • (reesAlgebraData I).algebra.one.eval (op U.1)) :
    X.presheaf.obj (.op U.1)) = r
  rw [(reesAlgebraData I).pieceEquiv_smul, (reesAlgebraData I).pieceEquiv_one]
  simp [r']

/-- Two homogeneous elements of degree one with the same image in the base agree. -/
public theorem eq_of_mem_grading_one {x y : (reesSituation I).sectionRing U.1}
    (hx : x ∈ (reesSituation I).sectionRingGrading U.1 1)
    (hy : y ∈ (reesSituation I).sectionRingGrading U.1 1)
    (h : reesToBase I U x = reesToBase I U y) : x = y :=
  sub_eq_zero.mp (reesToBase_injective_on_grade I U 1 (x - y)
    (((reesSituation I).sectionRingGrading U.1 1).sub_mem hx hy)
    (by rw [map_sub, h, sub_self]))

/-- The degree-one element attached to the zero section is zero. -/
public theorem reesDegreeOne_zero (h : (0 : X.presheaf.obj (op U.1)) ∈ I.ideal U) :
    (reesDegreeOne I U ⟨0, h⟩).1 = 0 := by
  refine eq_of_mem_grading_one I U (reesDegreeOne I U ⟨0, h⟩).2 (zero_mem _) ?_
  rw [reesToBase_degreeOne, map_zero]

/-- The degree-one element attached to a section is additive in the section. -/
public theorem reesDegreeOne_add (a b : I.ideal U) :
    (reesDegreeOne I U (a + b)).1 =
      (reesDegreeOne I U a).1 + (reesDegreeOne I U b).1 := by
  refine eq_of_mem_grading_one I U (reesDegreeOne I U (a + b)).2
    (((reesSituation I).sectionRingGrading U.1 1).add_mem
      (reesDegreeOne I U a).2 (reesDegreeOne I U b).2) ?_
  rw [reesToBase_degreeOne, map_add, reesToBase_degreeOne, reesToBase_degreeOne]
  rfl

/-- The degree-one element attached to a section is semilinear over the base. -/
public theorem reesDegreeOne_smul (c : X.presheaf.obj (op U.1)) (a : I.ideal U) :
    (reesDegreeOne I U (c • a)).1 =
      (reesSituation I).sectionRingBaseMap U.1 c * (reesDegreeOne I U a).1 := by
  refine eq_of_mem_grading_one I U (reesDegreeOne I U (c • a)).2 ?_ ?_
  · simpa using SetLike.mul_mem_graded
      (sectionRingBaseMap_mem_grading_zero I U c) (reesDegreeOne I U a).2
  · rw [reesToBase_degreeOne, map_mul, reesToBase_sectionRingBaseMap', reesToBase_degreeOne]
    rfl

/-- An ideal of the graded ring of local sections that contains the degree-one elements of a
generating family of `I` contains every degree-one element. -/
public theorem reesDegreeOne_mem_of_span {ι : Type*} (g : ι → X.presheaf.obj (op U.1))
    (hg : ∀ j, g j ∈ I.ideal U)
    (hspan : (I.ideal U : Ideal (X.presheaf.obj (op U.1))) ≤ Ideal.span (Set.range g))
    (J : Ideal ((reesSituation I).sectionRing U.1))
    (hJ : ∀ j, (reesDegreeOne I U ⟨g j, hg j⟩).1 ∈ J)
    (a : I.ideal U) : (reesDegreeOne I U a).1 ∈ J := by
  have hle : Ideal.span (Set.range g) ≤ I.ideal U :=
    Ideal.span_le.mpr (Set.range_subset_iff.mpr hg)
  have key : ∀ x ∈ Ideal.span (Set.range g), ∀ h : x ∈ I.ideal U,
      (reesDegreeOne I U ⟨x, h⟩).1 ∈ J := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact fun _ ↦ hJ j
    | zero =>
      intro h
      rw [reesDegreeOne_zero I U h]
      exact zero_mem _
    | add x y hx hy ihx ihy =>
      intro _
      rw [show (⟨x + y, _⟩ : I.ideal U) = (⟨x, hle hx⟩ : I.ideal U) + ⟨y, hle hy⟩ from rfl,
        reesDegreeOne_add]
      exact add_mem (ihx (hle hx)) (ihy (hle hy))
    | smul c x hx ih =>
      intro _
      rw [show (⟨c • x, _⟩ : I.ideal U) = c • (⟨x, hle hx⟩ : I.ideal U) from rfl,
        reesDegreeOne_smul]
      exact J.mul_mem_left _ (ih (hle hx))
  exact key a.1 (hspan a.2) a.2

/-- Every point of the Rees projective spectrum lies off the vanishing locus of the degree-one
element of some member of a generating family of the ideal. -/
public theorem exists_reesDegreeOne_span_not_mem {ι : Type*} (g : ι → X.presheaf.obj (op U.1))
    (hg : ∀ j, g j ∈ I.ideal U)
    (hspan : (I.ideal U : Ideal (X.presheaf.obj (op U.1))) ≤ Ideal.span (Set.range g))
    (x : Proj ((reesSituation I).sectionRingGrading U.1)) :
    ∃ j, (reesDegreeOne I U ⟨g j, hg j⟩).1 ∉ x.asHomogeneousIdeal := by
  by_contra! h
  apply x.not_irrelevant_le
  rw [HomogeneousIdeal.irrelevant_le]
  exact rees_homogeneous_mem_ideal I U _ (reesDegreeOne_mem_of_span I U g hg hspan _ h)

end AlgebraicGeometry

/-! ### The affine chart of a blowup as a morphism of schemes -/

namespace AlgebraicGeometry

variable {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens)

/-- The chart of the blowup over an affine open `U` of the base is an open immersion: it is the
base change of the inclusion of `U` along the structure morphism of the blowup. -/
public instance isOpenImmersion_relativeProjChart :
    IsOpenImmersion (relativeProjChart (reesSituation I) U) :=
  MorphismProperty.of_isPullback (relativeProjChart_isPullback (reesSituation I) U).flip
    inferInstance

variable (a : I.ideal U)

/-- The affine chart of the blowup attached to an affine open `U` of the base and a section
`a ∈ I(U)`: the spectrum of the affine blowup algebra `Γ(X, U)[I(U)/a]`, as an open subscheme of
the blowup. -/
public noncomputable def blowupChartι :
    Spec (.of (affineBlowupAlgebra (I.ideal U) (a : X.presheaf.obj (op U.1))
      (Localization.Away (a : X.presheaf.obj (op U.1))))) ⟶ blowUp I :=
  (affineBlowupStandardOpenIso I U a).hom ≫
    (Proj.basicOpen ((reesSituation I).sectionRingGrading U.1)
      (reesDegreeOne I U a).1).ι ≫ relativeProjChart (reesSituation I) U

/-- The affine chart of the blowup is an open immersion: it is an isomorphism onto a basic open
of the chart over `U`, followed by the inclusion of that basic open and of the chart. -/
public instance isOpenImmersion_blowupChartι : IsOpenImmersion (blowupChartι I U a) := by
  rw [blowupChartι]
  infer_instance

/-- The chart's structure morphism to the base is `Spec` of the canonical map of `Γ(X, U)` into
its blowup algebra, followed by the inclusion of `U`. -/
public theorem blowupChartι_comp_blowUpToBase :
    blowupChartι I U a ≫ blowUpToBase I =
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.obj (op U.1))
        (affineBlowupAlgebra (I.ideal U) (a : X.presheaf.obj (op U.1))
          (Localization.Away (a : X.presheaf.obj (op U.1)))))) ≫ U.2.fromSpec := by
  rw [blowupChartι]
  simp only [Category.assoc]
  rw [show relativeProjChart (reesSituation I) U ≫ blowUpToBase I =
      projInclusionToOpen (reesSituation I) U.1 U.2 ≫ U.1.ι from
      (relativeProjChart_isPullback (reesSituation I) U).w,
    ← IsAffineOpen.isoSpec_inv_ι U.2, reassoc_of% (affineBlowupStandardOpenIso_over I U a)]

/-- **The charts attached to a generating family of `I(U)` cover the part of the blowup lying
over `U`.** -/
public theorem exists_mem_range_blowupChartι {ι : Type*} (g : ι → X.presheaf.obj (op U.1))
    (hg : ∀ j, g j ∈ I.ideal U)
    (hspan : (I.ideal U : Ideal (X.presheaf.obj (op U.1))) ≤ Ideal.span (Set.range g))
    (x : blowUp I) (hx : blowUpToBase I x ∈ U.1) :
    ∃ (j : ι) (y : _), blowupChartι I U ⟨g j, hg j⟩ y = x := by
  obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback
    (relativeProjChart_isPullback (reesSituation I) U) x ⟨blowUpToBase I x, hx⟩ rfl
  obtain ⟨j, hj⟩ := exists_reesDegreeOne_span_not_mem I U g hg hspan z
  have hcomp : (affineBlowupStandardOpenIso I U ⟨g j, hg j⟩).inv ≫
      blowupChartι I U ⟨g j, hg j⟩ =
      (Proj.basicOpen ((reesSituation I).sectionRingGrading U.1)
        (reesDegreeOne I U ⟨g j, hg j⟩).1).ι ≫ relativeProjChart (reesSituation I) U := by
    rw [blowupChartι, Iso.inv_hom_id_assoc]
  refine ⟨j, (affineBlowupStandardOpenIso I U ⟨g j, hg j⟩).inv
    ⟨z, (Proj.mem_basicOpen _ _ _).mpr hj⟩, ?_⟩
  refine Eq.trans (Scheme.Hom.comp_apply _ _ _).symm ?_
  rwa [hcomp]

end AlgebraicGeometry

/-! ### The blowup of affine space along a coordinate affine subspace is smooth -/

namespace Stacks.MoreMorphisms

open MvPolynomial

variable (R : Type u) [CommRing R] (m n : ℕ)

/-- The ideal sheaf of the coordinate affine subspace. -/
public noncomputable def coordinateIdeal :
    (Spec (.of (MvPolynomial (Fin m ⊕ Fin n) R))).IdealSheafData :=
  (coordinateEmbedding R m n).ker

/-- The identification of the global sections of affine `(m + n)`-space with its coordinate
ring. -/
public noncomputable abbrev gammaEquiv :
    MvPolynomial (Fin m ⊕ Fin n) R ≃+*
      Γ(Spec (.of (MvPolynomial (Fin m ⊕ Fin n) R)), ⊤) :=
  (Scheme.ΓSpecIso (.of (MvPolynomial (Fin m ⊕ Fin n) R))).symm.commRingCatIsoToRingEquiv

/-- Affine `(m + n)`-space, as an affine open of itself. -/
public noncomputable abbrev topAffineOpen :
    (Spec (.of (MvPolynomial (Fin m ⊕ Fin n) R))).affineOpens :=
  ⟨⊤, isAffineOpen_top _⟩

/-- The coordinate embedding is quasi-compact, being a closed immersion. -/
public instance : QuasiCompact (coordinateEmbedding R m n) := by
  have : IsClosedImmersion (coordinateEmbedding R m n) :=
    coordinateEmbedding_isClosedImmersion R m n
  infer_instance

/-- The coordinate projection read on global sections. -/
public theorem gammaEquiv_coordinateEmbedding_appTop
    (x : Γ(Spec (.of (MvPolynomial (Fin m ⊕ Fin n) R)), ⊤)) :
    (Scheme.ΓSpecIso (.of (MvPolynomial (Fin m) R))).hom
        (((coordinateEmbedding R m n).appTop).hom x) =
      coordinateProjection R m n ((gammaEquiv R m n).symm x) :=
  congrArg (fun f : (CommRingCat.of Γ(Spec (.of (MvPolynomial (Fin m ⊕ Fin n) R)), ⊤)) ⟶
      (CommRingCat.of (MvPolynomial (Fin m) R)) => CommRingCat.Hom.hom f x)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (coordinateProjection R m n)))

/-- On global sections the ideal sheaf of the coordinate affine subspace is the ideal of the last
`n` coordinates. -/
public theorem coordinateIdeal_ideal_top :
    (coordinateIdeal R m n).ideal (topAffineOpen R m n) =
      (coordinateRingIdeal R m n).map (gammaEquiv R m n : _ →+* _) := by
  have hinj := (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (.of (MvPolynomial (Fin m) R))).hom).1
  rw [coordinateIdeal, Scheme.Hom.ker_apply, Ideal.map_comap_of_equiv (gammaEquiv R m n)]
  ext x
  rw [RingHom.mem_ker, Ideal.mem_comap, coordinateEmbedding_ker_eq_span, RingHom.mem_ker,
    ← gammaEquiv_coordinateEmbedding_appTop R m n x]
  refine ⟨fun h => ?_, fun h => hinj (h.trans (map_zero _).symm)⟩
  rw [show ((coordinateEmbedding R m n).appTop).hom x = 0 from h, map_zero]

variable (i : Fin n)

/-- The `i`-th of the last `n` coordinates, read as a global section of affine space. -/
public noncomputable abbrev coordinateSection :
    Γ(Spec (.of (MvPolynomial (Fin m ⊕ Fin n) R)), ⊤) :=
  gammaEquiv R m n (X (Sum.inr i))

/-- The `i`-th of the last `n` coordinates is a global section of the ideal sheaf of the
coordinate affine subspace. -/
public theorem coordinateSection_mem :
    coordinateSection R m n i ∈ (coordinateIdeal R m n).ideal (topAffineOpen R m n) := by
  rw [coordinateIdeal_ideal_top]
  exact Ideal.mem_map_of_mem _ (X_inr_mem_coordinateRingIdeal R m n i)

/-- The `i`-th of the last `n` coordinates, as a section of the ideal sheaf of the centre. -/
public noncomputable abbrev coordinateIdealSection :
    (coordinateIdeal R m n).ideal (topAffineOpen R m n) :=
  ⟨coordinateSection R m n i, coordinateSection_mem R m n i⟩

/-- The comparison of the two localizations of the two presentations of the coordinate ring. -/
public noncomputable abbrev chartLocalizationEquiv :
    Localization.Away (X (Sum.inr i) : MvPolynomial (Fin m ⊕ Fin n) R) ≃+*
      Localization.Away (coordinateSection R m n i) :=
  IsLocalization.ringEquivOfRingEquiv _ _ (gammaEquiv R m n)
    (Submonoid.map_powers (gammaEquiv R m n) (X (Sum.inr i)))

/-- **The `i`-th standard chart of the coordinate blowup is a polynomial affine space.** This is
`Stacks.MoreMorphisms.coordinateChart_equiv_polynomial`, transported to the presentation of the
chart that the blowup of a scheme uses, where the base is the ring of global sections. -/
public theorem exists_coordinateChartEquiv :
    ∃ F : affineBlowupAlgebra ((coordinateIdeal R m n).ideal (topAffineOpen R m n))
        (coordinateSection R m n i) (Localization.Away (coordinateSection R m n i)) ≃+*
        MvPolynomial (coordinateChartVariables m n i) R,
      ∀ r : R, F (algebraMap _ _ (gammaEquiv R m n (C r))) = C r := by
  obtain ⟨E, hE⟩ := Stacks.Blowup.exists_ringEquiv_affineBlowupAlgebra'
    (gammaEquiv R m n) (chartLocalizationEquiv R m n i)
    (X (Sum.inr i) : MvPolynomial (Fin m ⊕ Fin n) R) (coordinateRingIdeal R m n)
    ((coordinateIdeal R m n).ideal (topAffineOpen R m n)) (coordinateSection R m n i)
    (fun x => IsLocalization.ringEquivOfRingEquiv_eq _ x)
    (coordinateIdeal_ideal_top R m n) rfl
  obtain ⟨e, he, -, -, -⟩ := coordinateChart_equiv_polynomial R m n i
  refine ⟨E.symm.trans e, fun r => ?_⟩
  have hkey : E (algebraMap (MvPolynomial (Fin m ⊕ Fin n) R)
      (coordinateChartAlgebra R m n i) (C r)) =
      algebraMap _ _ (gammaEquiv R m n (C r)) := by
    refine Subtype.ext ?_
    rw [hE, Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap]
    exact IsLocalization.ringEquivOfRingEquiv_eq _ (C r)
  rw [RingEquiv.trans_apply, (RingEquiv.symm_apply_eq E).mpr hkey.symm,
    show algebraMap (MvPolynomial (Fin m ⊕ Fin n) R)
        (coordinateChartAlgebra R m n i) (C r) =
        algebraMap R (coordinateChartAlgebra R m n i) r from
      (IsScalarTower.algebraMap_apply R (MvPolynomial (Fin m ⊕ Fin n) R)
        (coordinateChartAlgebra R m n i) r).symm]
  exact he r

end Stacks.MoreMorphisms

namespace Stacks.MoreMorphisms

open MvPolynomial

variable (R : Type u) [CommRing R] (m n : ℕ)

/-- **The `i`-th standard chart of the coordinate blowup is smooth over the base ring.** -/
public theorem coordinateBlowupChart_smooth (i : Fin n) :
    Smooth (blowupChartι (coordinateIdeal R m n) (topAffineOpen R m n)
        (coordinateIdealSection R m n i) ≫ blowUpToBase (coordinateIdeal R m n) ≫
      Spec.map (CommRingCat.ofHom (C : R →+* MvPolynomial (Fin m ⊕ Fin n) R))) := by
  obtain ⟨F, hF⟩ := exists_coordinateChartEquiv R m n i
  rw [← Category.assoc, blowupChartι_comp_blowUpToBase, Category.assoc,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp, ← Spec.map_comp]
  exact smooth_specMap _ (smooth_of_mvPolynomial_ringEquiv _ _ F hF)

/-- The last `n` coordinates generate the ideal sheaf of the centre on global sections. -/
public theorem coordinateIdeal_ideal_top_le_span :
    (coordinateIdeal R m n).ideal (topAffineOpen R m n) ≤
      Ideal.span (Set.range fun i : Fin n => coordinateSection R m n i) := by
  rw [coordinateIdeal_ideal_top, coordinateRingIdeal, Ideal.map_span, ← Set.range_comp]
  exact le_of_eq (by rfl)

/-- The standard charts of the coordinate blowup cover it. -/
public theorem exists_mem_range_coordinateBlowupChart
    (x : blowUp (coordinateIdeal R m n)) :
    ∃ (i : Fin n) (y : _), blowupChartι (coordinateIdeal R m n) (topAffineOpen R m n)
      (coordinateIdealSection R m n i) y = x :=
  exists_mem_range_blowupChartι (coordinateIdeal R m n) (topAffineOpen R m n)
    (fun i : Fin n => coordinateSection R m n i) (coordinateSection_mem R m n)
    (coordinateIdeal_ideal_top_le_span R m n) x trivial

/-- **Stacks Project, Tag 0H1H.** The blowup of affine `(m + n)`-space along the coordinate
affine `m`-subspace is smooth over the base ring. No positivity hypothesis on `n` is needed: for
`n = 0` the centre is all of affine space, the ideal sheaf is zero and the blowup is empty. -/
public theorem blowUp_smooth_of_pos :
    Smooth (blowUpToBase (coordinateIdeal R m n) ≫
      Spec.map (CommRingCat.ofHom (C : R →+* MvPolynomial (Fin m ⊕ Fin n) R))) := by
  have _ := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Smooth) (Q := RingHom.Smooth)
  exact IsZariskiLocalAtSource.of_openCover (P := @Smooth)
    (𝒰 := Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) (Fin n) _
      (fun i => blowupChartι (coordinateIdeal R m n) (topAffineOpen R m n)
        (coordinateIdealSection R m n i))
      (exists_mem_range_coordinateBlowupChart R m n))
    (fun i ↦ coordinateBlowupChart_smooth R m n i)

/-- **Stacks Project, Tag 0H1H.** The blowup of affine `(m + n)`-space along the coordinate
affine `m`-subspace is smooth over the base ring.

The hypothesis `0 < n` is the one the source carries and is not used; see
`Stacks.MoreMorphisms.blowUp_smooth_of_pos` for the same statement without it. -/
@[stacks 0H1H "smoothness of the blowup"]
public theorem blowUp_smooth (_hn : 0 < n) :
    Smooth (blowUpToBase (coordinateIdeal R m n) ≫
      Spec.map (CommRingCat.ofHom (C : R →+* MvPolynomial (Fin m ⊕ Fin n) R))) :=
  blowUp_smooth_of_pos R m n

end Stacks.MoreMorphisms

end
