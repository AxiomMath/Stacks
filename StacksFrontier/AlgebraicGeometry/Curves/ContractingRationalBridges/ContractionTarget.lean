module

public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.StructurePushforward
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.Dimension
public import StacksFrontier.AlgebraicGeometry.ProperLimitStage.Basic
public import StacksFrontier.AlgebraicGeometry.Pushout.Dominant
public import StacksFrontier.AlgebraicGeometry.Pushout.FiniteType
public import StacksFrontier.AlgebraicGeometry.Pushout.Separation
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DegreeDivisibility

/-!
# The target of a contraction of a rational bridge

Let `k` be a field, let `X` be a proper scheme over `k` of dimension one with `H⁰(X, 𝒪_X) = k`
and at-worst-nodal singularities, let `C ⊆ X` be a rational bridge (Tag 0E3M) and let
`c : X ⟶ Y` be a contraction of `C`. This file equips `Y` with a structure morphism over `k`
compatible with `c` and proves that `Y` is again proper over `k` of dimension one with only
constant global functions.

## Main results

* `Stacks.Curves.isFinite_spec_map_bridgeSectionsStructureMap` — `k' = Γ(C, 𝒪_C)` is a finite
  extension of the ground field.
* `Stacks.Curves.exists_isProper_structureMorphism_contraction_bridge` — `Y` carries a structure
  morphism `g : Y ⟶ Spec k` with `c ≫ g` the structure morphism of `X`, and `g` is proper with
  `topologicalKrullDim Y = 1` and `H⁰(Y, 𝒪_Y) = k`.

## The argument

The target of a contraction is a pushout of `X'` along the collapse `C ∩ X' ⟶ Spec k'`, so it is
the pushout constructed in `StacksFrontier/AlgebraicGeometry/Pushout/Gluing.lean` up to the
comparison isomorphism `CategoryTheory.IsPushout.isoIsPushout`; the structure morphism is the one
of that construction, `AlgebraicGeometry.pushoutToBase`, transported along the comparison.

* separatedness and local finiteness of type over `k` are [Stacks, Tag 0E26] and
  [Stacks, Tag 0E27] for that construction, `AlgebraicGeometry.pushoutToBase_isSeparated` and
  `AlgebraicGeometry.pushoutToBase_locallyOfFiniteType`, whose hypotheses on the three schemes
  being glued hold because `X'` and `C ∩ X'` are closed subschemes of `X` and because `k'/k` is
  finite;
* universal closedness is descended along the surjection `a = c|_{X'}`, which is [Stacks, Tag
  03GN]: `AlgebraicGeometry.isProper_of_comp_surjective`;
* the dimension is that of `X'`, because `a` is integral and surjective ([Stacks, Tag 0ECG],
  `AlgebraicGeometry.topologicalKrullDim_eq_of_isIntegralHom_of_surjective`), and `X'` has
  dimension one;
* `H⁰(Y, 𝒪_Y) = k` because `c` is an isomorphism on global functions
  (`Stacks.Curves.isIso_appTop_of_isContractionOfRationalBridge`) and `c ≫ g` is the structure
  morphism of `X`, which has only constant global functions.

## References

* [Stacks Project, Tag 0E3M](https://stacks.math.columbia.edu/tag/0E3M)
* [Stacks Project, Tag 0E25](https://stacks.math.columbia.edu/tag/0E25)
* [Stacks Project, Tag 0E26](https://stacks.math.columbia.edu/tag/0E26)
* [Stacks Project, Tag 0E27](https://stacks.math.columbia.edu/tag/0E27)
* [Stacks Project, Tag 0ECG](https://stacks.math.columbia.edu/tag/0ECG)
* [Stacks Project, Tag 03GN](https://stacks.math.columbia.edu/tag/03GN)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Curves

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))]
  [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]

omit [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)] in
/-- **The field of global functions on a rational bridge is a finite extension of the ground
field.** The bridge is proper over `k` and its ring of global functions is a field
(`AlgebraicGeometry.isField_of_universallyClosed`), so
`AlgebraicGeometry.finite_appTop_of_universallyClosed_of_isField` applies. -/
theorem isFinite_spec_map_bridgeSectionsStructureMap
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) :
    IsFinite (Spec.map (bridgeSectionsStructureMap (k := k) C)) := by
  have := hC.isIntegral
  have hfield : IsField Γ(C.subscheme, ⊤) :=
    isField_of_universallyClosed k (C.subschemeι ≫ (X ↘ Spec (.of k)))
  have h₁ : ((C.subschemeι ≫ (X ↘ Spec (.of k))).appTop).hom.Finite :=
    finite_appTop_of_universallyClosed_of_isField k
      (C.subschemeι ≫ (X ↘ Spec (.of k))) hfield
  have h₂ : ((Scheme.ΓSpecIso (.of k)).inv).hom.Finite :=
    RingHom.Finite.of_surjective _ fun x ↦ ⟨(Scheme.ΓSpecIso (.of k)).hom.hom x, by simp⟩
  rw [IsFinite.SpecMap_iff]
  exact h₁.comp h₂

/-- **The target of a contraction of a rational bridge is a proper one-dimensional scheme over
the ground field with only constant global functions.** This is the clause of
[Stacks, Tag 0E3M] that reads "`Y` is also a proper scheme over `k` having dimension `1` and
`H⁰(Y, 𝒪_Y) = k`"; the structure morphism is produced here, since a contraction is not given
with one. -/
theorem exists_isProper_structureMorphism_contraction_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} {hC : IsRationalBridge k X C} {Y : Scheme.{u}} {c : X ⟶ Y}
    (hc : IsContractionOfRationalBridge hC c) :
    ∃ g : Y ⟶ Spec (.of k), c ≫ g = X ↘ Spec (.of k) ∧ IsProper g ∧
      topologicalKrullDim Y = 1 ∧ IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop) := by
  have := hC.isIntegral
  obtain ⟨hbot, a, b, hpo, hac, hbc⟩ := id hc
  have : IsFinite (Scheme.IdealSheafData.inclusion (I := C)
      (J := intersectionWithComplementaryCurveIdeal C) le_sup_left ≫ C.subscheme.toSpecΓ) :=
    isFinite_intersection_toSpec_bridgeSections hdim hnodal hC
  let : Field Γ(C.subscheme, ⊤) :=
    (isField_of_universallyClosed k (C.subschemeι ≫ (X ↘ Spec (.of k)))).toField
  have : Unique (PrimeSpectrum (Γ(C.subscheme, ⊤) : Type u)) := PrimeSpectrum.instUnique
  have : Nonempty (intersectionWithComplementaryCurve C) := nonempty_intersection_bridge hC
  have hdom : IsSchemeTheoreticallyDominant
      (Scheme.IdealSheafData.inclusion (I := C)
        (J := intersectionWithComplementaryCurveIdeal C) le_sup_left ≫
        C.subscheme.toSpecΓ) := by
    have : Subsingleton (Spec Γ(C.subscheme, ⊤) : Type u) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum (Γ(C.subscheme, ⊤) : Type u)))
    exact IsSchemeTheoreticallyDominant.of_isDominant _
  let s : PushoutAlongClosedImmersionAndIntegralSituation.{u} :=
    { S := Spec (.of k)
      X := complementaryCurve C
      Y := Spec Γ(C.subscheme, ⊤)
      Z := intersectionWithComplementaryCurve C
      pX := complementaryCurveι C ≫ (X ↘ Spec (.of k))
      pY := Spec.map (bridgeSectionsStructureMap C)
      pZ := (intersectionWithComplementaryCurveIdeal C).subschemeι ≫ (X ↘ Spec (.of k))
      i := Scheme.IdealSheafData.inclusion (I := complementaryCurveIdeal C)
        (J := intersectionWithComplementaryCurveIdeal C) le_sup_right
      j := Scheme.IdealSheafData.inclusion (I := C)
        (J := intersectionWithComplementaryCurveIdeal C) le_sup_left ≫ C.subscheme.toSpecΓ
      i_over := by
        rw [← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
      j_over := by
        rw [Category.assoc, toSpecΓ_comp_bridgeSectionsStructureMap, ← Category.assoc,
          Scheme.IdealSheafData.inclusion_subschemeι]
      fiber_preimage_subset_affine := fiber_preimage_subset_affine_bridge hdim hnodal hC }
  have hpos : IsPushout s.i s.j a b := hpo
  let e : pushoutScheme s ≅ Y :=
    (pushoutAlongClosedImmersionAndIntegral s).isPushout.isoIsPushout s.X s.Y hpos
  have hia : pushoutInl s ≫ e.hom = a :=
    IsPushout.inl_isoIsPushout_hom s.X s.Y
      (pushoutAlongClosedImmersionAndIntegral s).isPushout hpos
  have hib : pushoutInr s ≫ e.hom = b :=
    IsPushout.inr_isoIsPushout_hom s.X s.Y
      (pushoutAlongClosedImmersionAndIntegral s).isPushout hpos
  have hae : a ≫ e.inv = pushoutInl s := by
    rw [← hia, Category.assoc, e.hom_inv_id, Category.comp_id]
  have hbe : b ≫ e.inv = pushoutInr s := by
    rw [← hib, Category.assoc, e.hom_inv_id, Category.comp_id]
  have hinl : pushoutInl s ≫ pushoutToBase s = s.pX := by simp [pushoutToBase]
  have hinr : pushoutInr s ≫ pushoutToBase s = s.pY := by simp [pushoutToBase]
  set g : Y ⟶ Spec (.of k) := e.inv ≫ pushoutToBase s with hgdef
  have hg : ∀ {T : Scheme.{u}} (v : T ⟶ pushoutScheme s) (u : T ⟶ Y), v ≫ e.hom = u →
      u ≫ g = v ≫ pushoutToBase s := by
    rintro T v _ rfl
    simp [hgdef]
  have hag : a ≫ g = s.pX := (hg _ _ hia).trans hinl
  have hbg : b ≫ g = s.pY := (hg _ _ hib).trans hinr
  have hcg : c ≫ g = X ↘ Spec (.of k) := by
    refine (isPushout_subscheme_of_inf_eq_bot C (complementaryCurveIdeal C) hbot).hom_ext ?_ ?_
    · rw [← Category.assoc, hac, hag]
    · rw [← Category.assoc, hbc, Category.assoc, hbg]
      exact toSpecΓ_comp_bridgeSectionsStructureMap C
  have hsurj : Surjective (complementaryCurveι C ≫ c) := by
    have h₁ : Surjective (pushoutInl s ≫ e.hom) := inferInstance
    rw [hia, ← hac] at h₁
    exact h₁
  refine ⟨g, hcg, ?_, ?_, ?_⟩
  · have : IsSeparated s.pX :=
      show IsSeparated (complementaryCurveι C ≫ (X ↘ Spec (.of k))) from inferInstance
    have : IsSeparated s.pY :=
      show IsSeparated (Spec.map (bridgeSectionsStructureMap (k := k) C)) from
        IsSeparated.of_isAffineHom _
    have : LocallyOfFiniteType s.pX :=
      show LocallyOfFiniteType (complementaryCurveι C ≫ (X ↘ Spec (.of k))) from inferInstance
    have : LocallyOfFiniteType s.pZ :=
      show LocallyOfFiniteType ((intersectionWithComplementaryCurveIdeal C).subschemeι ≫
        (X ↘ Spec (.of k))) from inferInstance
    have : IsFinite (Spec.map (bridgeSectionsStructureMap (k := k) C)) :=
      isFinite_spec_map_bridgeSectionsStructureMap hC
    have : LocallyOfFiniteType s.pY :=
      show LocallyOfFiniteType (Spec.map (bridgeSectionsStructureMap (k := k) C)) from
        inferInstance
    have : IsLocallyNoetherian s.S :=
      show IsLocallyNoetherian (Spec (CommRingCat.of k)) from inferInstance
    have : UniversallyClosed ((complementaryCurveι C ≫ c) ≫ g) := by
      rw [Category.assoc, hcg]
      infer_instance
    exact isProper_of_comp_surjective (complementaryCurveι C ≫ c) g
  · have : IsIntegralHom (complementaryCurveι C ≫ c) :=
      isIntegralHom_complementaryCurveι_comp_contraction hdim hnodal hc
    rw [← topologicalKrullDim_eq_of_isIntegralHom_of_surjective (complementaryCurveι C ≫ c)]
    exact topologicalKrullDim_complementaryCurve_eq_one
      (equidimensional_of_isIso_globalSections_of_dimension_one k (X ↘ Spec (.of k)) hdim)
      hdim hnodal C hC.complementaryCurve_nonempty
  · have := isIso_appTop_of_isContractionOfRationalBridge hdim hnodal hc
    have h : ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop) ≫ c.appTop =
        (Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop := by
      rw [Category.assoc, ← Scheme.Hom.comp_appTop, hcg]
    have : IsIso (((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop) ≫ c.appTop) := by
      rw [h]; infer_instance
    exact IsIso.of_isIso_comp_right ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop) c.appTop

end Stacks.Curves

end
