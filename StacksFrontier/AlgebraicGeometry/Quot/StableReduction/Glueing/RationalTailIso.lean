module

public import StacksFrontier.AlgebraicGeometry.Quot.StableCurveFamilies
public import StacksFrontier.AlgebraicGeometry.Quot.StableReduction.Glueing.IdealSheafMapIso
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GeometricGenusNormalizationBound
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.SeparableDegreeFibres
public import StacksFrontier.AlgebraicGeometry.ProperGeomConnected.Basic

/-!
# Rational tails and bridges under isomorphisms

Let `θ : X ⟶ X'` be an isomorphism of schemes over a field `k`. The direct image `C ↦ C.map θ`
of ideal sheaves carries rational tails of `X` to rational tails of `X'`, and rational bridges to
rational bridges. Moreover, a rational tail (or bridge) of a scheme over `k'` is still one when
the scheme is regarded over `k` along an isomorphism of fields `Spec k' ≅ Spec k`. Together these
show that the fibre condition `AlgebraicGeometry.HasGenusTwoNoRationalTailNoRationalBridge` only
depends on the scheme over the field up to isomorphism.

## Main results

* `AlgebraicGeometry.complementaryCurveIdeal_map_of_isIso`: the closure of the complement is
  compatible with the direct image along an isomorphism.
* `AlgebraicGeometry.isRationalTail_map_of_isIso` and
  `AlgebraicGeometry.isRationalBridge_map_of_isIso`: invariance under an isomorphism of schemes
  over the same field.
* `AlgebraicGeometry.HasGenusTwoNoRationalTailNoRationalBridge.of_iso`: invariance of the fibre
  condition under an isomorphism of schemes lying over an isomorphism of fields.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

open Scheme.IdealSheafData in
/-- Along an isomorphism `θ`, the ideal sheaf of the closure of the complement of the direct
image of `C` is the direct image of the ideal sheaf of the closure of the complement of `C`. -/
theorem complementaryCurveIdeal_map_of_isIso {X X' : Scheme.{u}} (θ : X ⟶ X') [IsIso θ]
    (C : X.IdealSheafData) :
    complementaryCurveIdeal (C.map θ) = (complementaryCurveIdeal C).map θ := by
  have hr : Set.range (Scheme.Opens.ι C.support.compl ≫ θ) =
      Set.range (Scheme.Opens.ι (C.map θ).support.compl) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
      Scheme.Opens.range_ι, TopologicalSpace.Closeds.coe_compl,
      TopologicalSpace.Closeds.coe_compl, coe_support_map_of_isIso]
    exact Set.image_compl_eq θ.homeomorph.bijective
  rw [complementaryCurveIdeal, complementaryCurveIdeal, map_ker,
    ← IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hr, Scheme.Hom.ker_comp_of_isIso]

open Scheme.IdealSheafData in
/-- Along an isomorphism `θ`, the ideal sheaf of the intersection with the closure of the
complement is compatible with the direct image. -/
theorem intersectionWithComplementaryCurveIdeal_map_of_isIso {X X' : Scheme.{u}} (θ : X ⟶ X')
    [IsIso θ] (C : X.IdealSheafData) :
    intersectionWithComplementaryCurveIdeal (C.map θ) =
      (intersectionWithComplementaryCurveIdeal C).map θ := by
  rw [intersectionWithComplementaryCurveIdeal, intersectionWithComplementaryCurveIdeal,
    map_sup_of_isIso, complementaryCurveIdeal_map_of_isIso]

/-- A homeomorphism of schemes carries irreducible components to irreducible components. -/
theorem image_mem_irreducibleComponents_of_isIso {X X' : Scheme.{u}} (θ : X ⟶ X') [IsIso θ]
    {Z : Set X} (hZ : Z ∈ irreducibleComponents X) : θ '' Z ∈ irreducibleComponents X' :=
  image_mem_irreducibleComponents_of_isPreirreducible_fiber θ θ.continuous
    θ.homeomorph.isOpenMap
    (fun _ => (Set.subsingleton_singleton.preimage θ.homeomorph.injective).isPreirreducible)
    θ.homeomorph.surjective hZ

/-- The support of the direct image of an integral irreducible component along an isomorphism is
again an irreducible component. -/
private theorem support_map_mem_irreducibleComponents_of_isIso {X X' : Scheme.{u}} (θ : X ⟶ X')
    [IsIso θ] {C : X.IdealSheafData} (hirr : (C.support : Set X) ∈ irreducibleComponents X) :
    ((C.map θ).support : Set X') ∈ irreducibleComponents X' := by
  rw [Scheme.IdealSheafData.coe_support_map_of_isIso]
  exact image_mem_irreducibleComponents_of_isIso θ hirr

/-- The complementary curve of the direct image along an isomorphism is nonempty if that of the
original ideal sheaf is. -/
private theorem nonempty_complementaryCurve_map_of_isIso {X X' : Scheme.{u}} (θ : X ⟶ X')
    [IsIso θ] {C : X.IdealSheafData} (hne : Nonempty (complementaryCurve C)) :
    Nonempty (complementaryCurve (C.map θ)) := by
  show Nonempty (complementaryCurveIdeal (C.map θ)).subscheme
  rw [complementaryCurveIdeal_map_of_isIso]
  exact ⟨((complementaryCurveIdeal C).subschemeMapIso θ).hom hne.some⟩

open Scheme.IdealSheafData in
/-- **Rational tails are invariant under isomorphisms over the ground field.** If `θ : X ⟶ X'`
is an isomorphism of schemes over `k`, with `X` proper over `k`, the direct image along `θ` of a
rational tail of `X` is a rational tail of `X'`. -/
theorem isRationalTail_map_of_isIso {k : Type u} [Field k] {X X' : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (f' : X' ⟶ Spec (.of k)) (θ : X ⟶ X') [IsIso θ] (hθ : θ ≫ f' = f)
    [IsProper f] (C : X.IdealSheafData) (hC : @IsRationalTail k _ X ⟨f⟩ C) :
    @IsRationalTail k _ X' ⟨f'⟩ (C.map θ) := by
  obtain ⟨hint, hirr, hne, x, hx, hI, hΓ, hg⟩ := hC
  let e := C.subschemeMapIso θ
  have hpt : (C.map θ).subschemeι (e.hom x) = θ (C.subschemeι x) :=
    C.subschemeι_subschemeMapIso_hom_apply θ x
  have hcl : IsClosed ({(C.map θ).subschemeι (e.hom x)} : Set X') := by
    rw [hpt, ← Set.image_singleton]
    exact isClosed_image_of_iso (asIso θ) hx
  refine ⟨IsIntegral.of_isIso e.hom, ?_, ?_, e.hom x, hcl, ?_, ?_, ?_⟩
  · exact support_map_mem_irreducibleComponents_of_isIso θ hirr
  · exact nonempty_complementaryCurve_map_of_isIso θ hne
  · rw [intersectionWithComplementaryCurveIdeal_map_of_isIso, hI, map_vanishingIdeal]
    congr 1
    ext1
    rw [TopologicalSpace.Closeds.coe_closure, TopologicalSpace.Closeds.coe_mk,
      TopologicalSpace.Closeds.coe_mk, Set.image_singleton, ← hpt]
    exact hcl.closure_eq
  · have := hΓ
    have : IsIso ((C.map θ).subscheme.Γevaluation (e.hom x) ≫ e.hom.residueFieldMap x) := by
      have : IsIso e.hom.appTop := inferInstanceAs (IsIso (e.hom.app ⊤))
      rw [Scheme.Γevaluation_naturality e.hom x]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (e.hom.residueFieldMap x)
  · show genus ((C.map θ).subschemeι ≫ f') = 0
    have heq : (C.map θ).subschemeι ≫ f' = e.symm.hom ≫ (C.subschemeι ≫ f) := by
      rw [← cancel_epi e.hom, ← hθ]
      simp [e]
    rw [heq, genus_comp_iso_eq k (C.subschemeι ≫ f) e.symm]
    exact hg

open Scheme.IdealSheafData in
/-- Along an isomorphism `θ`, the degree of the inclusion of closed subschemes `I ⊆ C` (the
dimension of the global functions on `I` over those on `C`) is unchanged by the direct image. -/
theorem finrank_inclusion_map_of_isIso {X X' : Scheme.{u}} (θ : X ⟶ X') [IsIso θ]
    (C I : X.IdealSheafData) (h : C ≤ I) (I' : X'.IdealSheafData) (hI' : I' = I.map θ)
    (h' : C.map θ ≤ I') :
    (letI : Algebra Γ((C.map θ).subscheme, ⊤) Γ(I'.subscheme, ⊤) :=
        (Scheme.IdealSheafData.inclusion h').appTop.hom.toAlgebra;
      Module.finrank Γ((C.map θ).subscheme, ⊤) Γ(I'.subscheme, ⊤)) =
      (letI : Algebra Γ(C.subscheme, ⊤) Γ(I.subscheme, ⊤) :=
          (Scheme.IdealSheafData.inclusion h).appTop.hom.toAlgebra;
        Module.finrank Γ(C.subscheme, ⊤) Γ(I.subscheme, ⊤)) := by
  subst hI'
  let eC := C.subschemeMapIso θ
  let eI := I.subschemeMapIso θ
  have hsq : eI.hom ≫ Scheme.IdealSheafData.inclusion h' =
      Scheme.IdealSheafData.inclusion h ≫ eC.hom := by
    rw [← cancel_mono (C.map θ).subschemeι]
    simp [eC, eI]
  have : IsIso eC.hom.appTop := inferInstanceAs (IsIso (eC.hom.app ⊤))
  have : IsIso eI.hom.appTop := inferInstanceAs (IsIso (eI.hom.app ⊤))
  let : Algebra Γ((C.map θ).subscheme, ⊤) Γ((I.map θ).subscheme, ⊤) :=
    (Scheme.IdealSheafData.inclusion h').appTop.hom.toAlgebra
  let : Algebra Γ(C.subscheme, ⊤) Γ(I.subscheme, ⊤) :=
    (Scheme.IdealSheafData.inclusion h).appTop.hom.toAlgebra
  refine Algebra.finrank_eq_of_equiv_equiv (asIso eC.hom.appTop).commRingCatIsoToRingEquiv
    (asIso eI.hom.appTop).commRingCatIsoToRingEquiv ?_
  have := congrArg (fun φ => φ.appTop.hom) hsq
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] at this
  exact this.symm

open Scheme.IdealSheafData in
/-- **Rational bridges are invariant under isomorphisms over the ground field.** If
`θ : X ⟶ X'` is an isomorphism of proper schemes over `k`, the direct image along `θ` of a
rational bridge of `X` is a rational bridge of `X'`. The definition of a rational bridge only
uses the structure morphism through properness, so no compatibility of `θ` with the structure
morphisms is needed. -/
theorem isRationalBridge_map_of_isIso {k : Type u} [Field k] {X X' : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (f' : X' ⟶ Spec (.of k)) (θ : X ⟶ X') [IsIso θ]
    [hf : IsProper f] [hf' : IsProper f'] (C : X.IdealSheafData)
    (hC : @IsRationalBridge k _ X ⟨f⟩ hf C) : @IsRationalBridge k _ X' ⟨f'⟩ hf' (C.map θ) := by
  obtain ⟨hint, hirr, hne, hfin, hg⟩ := hC
  let e := C.subschemeMapIso θ
  have := hint
  have : IsIntegral (C.map θ).subscheme := IsIntegral.of_isIso e.hom
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · exact support_map_mem_irreducibleComponents_of_isIso θ hirr
  · exact nonempty_complementaryCurve_map_of_isIso θ hne
  · exact (finrank_inclusion_map_of_isIso θ C _ le_sup_left _
      (intersectionWithComplementaryCurveIdeal_map_of_isIso θ C) le_sup_left).trans hfin
  · let : Field Γ(C.subscheme, ⊤) :=
      (isField_of_universallyClosed k (C.subschemeι ≫ f)).toField
    let : Field Γ((C.map θ).subscheme, ⊤) :=
      (isField_of_universallyClosed k ((C.map θ).subschemeι ≫ f')).toField
    have : IsProper C.subscheme.toSpecΓ :=
      Stacks.AlgebraicGeometry.ProperGeomConnected.isProper_toSpecΓ (C.subschemeι ≫ f)
    have : IsIso e.inv.appTop := inferInstanceAs (IsIso (e.inv.app ⊤))
    have hpb : IsPullback e.inv (C.map θ).subscheme.toSpecΓ C.subscheme.toSpecΓ
        (Spec.map e.inv.appTop) :=
      IsPullback.of_horiz_isIso ⟨Scheme.toSpecΓ_naturality e.inv⟩
    exact (genus_eq_of_isPullback Γ(C.subscheme, ⊤) Γ((C.map θ).subscheme, ⊤) e.inv.appTop.hom
      e.inv _ _ hpb).trans hg

/-- A rational tail of a proper scheme over `k'` stays one when the scheme is regarded over `k`
along an isomorphism `Spec k' ≅ Spec k`, and conversely. -/
theorem isRationalTail_comp_isIso_iff {k k' : Type u} [Field k] [Field k'] {X : Scheme.{u}}
    (f' : X ⟶ Spec (.of k')) (φ : CommRingCat.of k ⟶ CommRingCat.of k') [IsIso φ]
    [IsProper f'] (C : X.IdealSheafData) :
    @IsRationalTail k _ X ⟨f' ≫ Spec.map φ⟩ C ↔ @IsRationalTail k' _ X ⟨f'⟩ C := by
  have hg : genus (C.subschemeι ≫ f' ≫ Spec.map φ) = genus (C.subschemeι ≫ f') := by
    have : IsProper (C.subschemeι ≫ f' ≫ Spec.map φ) := inferInstance
    exact (genus_eq_of_isPullback k k' φ.hom (𝟙 _) (C.subschemeι ≫ f') _
      (IsPullback.of_horiz_isIso ⟨by simp⟩)).symm
  simp only [isRationalTail_iff]
  show _ ∧ _ ∧ _ ∧ (∃ x hx, _ ∧ _ ∧ genus (C.subschemeι ≫ f' ≫ Spec.map φ) = 0) ↔
    _ ∧ _ ∧ _ ∧ (∃ x hx, _ ∧ _ ∧ genus (C.subschemeι ≫ f') = 0)
  rw [hg]

/-- A rational bridge of a proper scheme over `k'` stays one when the scheme is regarded over
`k` along a morphism `Spec k' ⟶ Spec k`: the definition only involves the field structure of
the global functions on the bridge. -/
theorem isRationalBridge_comp_iff {k k' : Type u} [Field k] [Field k'] {X : Scheme.{u}}
    (f' : X ⟶ Spec (.of k')) (φ : CommRingCat.of k ⟶ CommRingCat.of k')
    [hf : IsProper (f' ≫ Spec.map φ)] [hf' : IsProper f'] (C : X.IdealSheafData) :
    @IsRationalBridge k _ X ⟨f' ≫ Spec.map φ⟩ hf C ↔ @IsRationalBridge k' _ X ⟨f'⟩ hf' C :=
  Iff.rfl

end AlgebraicGeometry

end
