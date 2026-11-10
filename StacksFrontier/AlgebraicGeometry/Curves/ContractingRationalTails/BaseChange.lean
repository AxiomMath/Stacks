module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ZeroCycleDegreeFormula
public import StacksFrontier.AlgebraicGeometry.CurveEulerBridge.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.CanonicalContraction.Existence
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.BaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.GeometricallyIntegral
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.RiemannRoch
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper

/-!
# Rational tails after extension of the ground field

Let `X` be a proper one-dimensional scheme over a field `k` with `H⁰(X, 𝒪_X) = k` and
at-worst-nodal singularities, and let `C ⊆ X` be a rational tail. For every field extension
`K/k` the inverse image `C_K` of `C` in `X_K` is a finite disjoint union of rational tails of
`X_K`; this is [Stacks, Tag 0E3I].

The field `k' = H⁰(C, 𝒪_C)` is the residue field at the attaching point `x`, a finite separable
extension of `k`, and `C` is geometrically integral over `k'`
(`Stacks.Curves.geometricallyIntegral_toSpecΓ_of_isRationalTail`). So `K ⊗_k k'` is a finite
product of fields `K'_i`, and `C_K = ∐ C ×_{k'} K'_i` with every piece integral. Each piece is a
one-dimensional irreducible component of `X_K` of genus zero, by flat base change of cohomology.
Its intersection with the closure of its complement is the base change of `C ∩ X' = {x}` along
the piece, and `{x} ⟶ Spec k'` is an isomorphism, so that intersection is the single reduced
point `Spec K'_i`, at which the global functions `K'_i` of the piece are the residue field.

## Main results

* `AlgebraicGeometry.exists_iso_sigma_isRationalTail_baseChange`: **[Stacks, Tag 0E3I]**.
* `AlgebraicGeometry.exists_isIso_Γevaluation_of_isIso_inclusion_comp`: a closed subscheme
  meeting the closure of its complement in a copy of `Spec k'` meets it in one reduced point.
* `AlgebraicGeometry.isIso_inclusion_comp_toSpecΓ_of_isRationalTail`: the attaching point of a
  rational tail maps isomorphically to the spectrum of its field of global functions.
* `AlgebraicGeometry.genus_eq_zero_of_genus_eq_zero`: vanishing of the genus of a proper scheme
  over a field does not depend on the field.

## Implementation notes

The decomposition is stated as in [Stacks, Tag 0E65] for rational bridges: an isomorphism from
the coproduct of the pieces to `C_K` commuting with their closed immersions into `X_K`, so that
the pieces are disjoint as closed subschemes and not merely abstractly.

## References

* [Stacks Project, Tag 0E3I](https://stacks.math.columbia.edu/tag/0E3I)
* [Stacks Project, Tag 0E3H](https://stacks.math.columbia.edu/tag/0E3H)
* [Stacks Project, Tag 0BY9](https://stacks.math.columbia.edu/tag/0BY9)
* [Stacks Project, Tag 081I](https://stacks.math.columbia.edu/tag/081I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open Stacks.Curves

universe u

namespace AlgebraicGeometry

/-- **Vanishing of the genus does not depend on the field.** For a scheme proper over a field
`k` of genus zero, the first cohomology of the structure sheaf is finite-dimensional over `k`
and hence zero, so the genus over any other field structure is zero as well. -/
theorem genus_eq_zero_of_genus_eq_zero {k k' : Type u} [Field k] [Field k'] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (g : X ⟶ Spec (.of k')) (h : genus f = 0) :
    genus g = 0 := by
  have := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k f
  have hfin := finiteDimensional_cohomologyOverField_of_isProper k f
    (SheafOfModules.unit X.ringCatSheaf) 1
  have hsub : Subsingleton (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1) :=
    Module.finrank_zero_iff.mp ((finrank_cohomologyOverField_one_unit_eq_genus k f).trans h)
  have hsub' : Subsingleton (cohomologyOverField k' g (SheafOfModules.unit X.ringCatSheaf) 1) :=
    hsub
  rw [← finrank_cohomologyOverField_one_unit_eq_genus k' g]
  exact Module.finrank_zero_of_subsingleton

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- **The attaching point of a rational tail is `Spec` of the field of global functions.** The
reduced attaching point is `Spec κ(x)`, and `Γ(C, 𝒪_C) ⟶ κ(x)` is an isomorphism, so the composite
of the inclusion of the attaching point with `C ⟶ Spec Γ(C, 𝒪_C)` is an isomorphism. -/
theorem isIso_inclusion_comp_toSpecΓ_of_isRationalTail {C : X.IdealSheafData}
    (hC : IsRationalTail k X C) :
    IsIso (Scheme.IdealSheafData.inclusion
        (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C) ≫
      C.subscheme.toSpecΓ) := by
  let x := hC.attachingPoint
  let γ : Spec (C.subscheme.residueField x) ⟶ X := C.subscheme.fromSpecResidueField x ≫ C.subschemeι
  have : IsClosedImmersion (C.subscheme.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp (isClosed_singleton_attachingPoint_subscheme hC)
  have hγ : γ.ker = intersectionWithComplementaryCurveIdeal C :=
    (ker_fromSpecResidueField_attachingPoint_comp_subschemeι hC).trans
      hC.intersectionWithComplementaryCurveIdeal_eq.symm
  have key : ∀ J : X.IdealSheafData, γ.ker = J →
      ∃ e : Spec (C.subscheme.residueField x) ≅ J.subscheme, e.hom ≫ J.subschemeι = γ := by
    rintro _ rfl
    exact ⟨asIso γ.toImage, γ.toImage_imageι⟩
  obtain ⟨e, he⟩ := key _ hγ
  let iC := Scheme.IdealSheafData.inclusion
    (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C)
  have heC : e.hom ≫ iC = C.subscheme.fromSpecResidueField x := by
    apply (cancel_mono C.subschemeι).1
    rw [Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι, he]
  have : IsIso (C.subscheme.Γevaluation x) := hC.isIso_Γevaluation_attachingPoint
  have : IsIso (C.subscheme.fromSpecResidueField x ≫ C.subscheme.toSpecΓ) := by
    have h2 : C.subscheme.fromSpecResidueField x ≫ C.subscheme.toSpecΓ =
        inv (Spec.map (inv (C.subscheme.Γevaluation x))) := by
      refine IsIso.eq_inv_of_hom_inv_id ?_
      rw [← Category.assoc]
      exact fromSpecResidueField_comp_toSpecΓ_of_isIso_Γevaluation (X := C.subscheme) x
    rw [h2]
    infer_instance
  have : IsIso (e.hom ≫ iC ≫ C.subscheme.toSpecΓ) := by
    rw [← Category.assoc, heC]
    infer_instance
  exact IsIso.of_isIso_comp_left e.hom _

/-- **A closed subscheme meeting the closure of its complement in a copy of `Spec k'` meets it
in one reduced point.** Let `C ⊆ X` be a closed subscheme, let `C ⟶ Spec k'` induce
`k' ≅ Γ(C, 𝒪_C)` for a field `k'`, and suppose the intersection `C ∩ X'` with the closure of the
complement maps isomorphically to `Spec k'`. Then `C ∩ X'` is the reduced point `{x}` for a
closed point `x` of `C`, and `Γ(C, 𝒪_C) ⟶ κ(x)` is an isomorphism; these are two of the defining
conditions of a rational tail. -/
theorem exists_isIso_Γevaluation_of_isIso_inclusion_comp {Y : Scheme.{u}} (C : Y.IdealSheafData)
    (k' : Type u) [Field k'] (f' : C.subscheme ⟶ Spec (.of k'))
    [IsIso ((Scheme.ΓSpecIso (.of k')).inv ≫ f'.appTop)]
    [IsIso (Scheme.IdealSheafData.inclusion
      (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C) ≫ f')] :
    ∃ (x : C.subscheme) (hx : IsClosed ({C.subschemeι x} : Set Y)),
      intersectionWithComplementaryCurveIdeal C =
          Scheme.IdealSheafData.vanishingIdeal ⟨{C.subschemeι x}, hx⟩ ∧
        IsIso (C.subscheme.Γevaluation x) := by
  let ID := intersectionWithComplementaryCurveIdeal C
  let iD := Scheme.IdealSheafData.inclusion (le_sup_left : C ≤ ID)
  have : IsIntegral ID.subscheme := IsIntegral.of_isIso (inv (iD ≫ f'))
  have : Subsingleton ID.subscheme :=
    ⟨fun a b => (iD ≫ f').isOpenEmbedding.injective (Subsingleton.elim _ _)⟩
  let pt : ID.subscheme := (inv (iD ≫ f')).base (IsLocalRing.closedPoint k')
  have hsupp : (ID.support : Set Y) = {ID.subschemeι pt} := by
    rw [← ID.range_subschemeι]
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨pt, rfl⟩, ?_⟩
    rintro _ ⟨a, rfl⟩
    rw [Subsingleton.elim a pt]
  have hxy : C.subschemeι (iD pt) = ID.subschemeι pt := by
    rw [← Scheme.IdealSheafData.inclusion_subschemeι (le_sup_left : C ≤ ID)]
    rfl
  have hy : IsClosed ({C.subschemeι (iD pt)} : Set Y) := by
    rw [hxy, ← hsupp]
    exact ID.support.isClosed
  have hID : ID = Scheme.IdealSheafData.vanishingIdeal ⟨{C.subschemeι (iD pt)}, hy⟩ := by
    refine (Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme ID ID.support
      rfl).trans ?_
    congr 1
    ext1
    change (ID.support : Set Y) = {C.subschemeι (iD pt)}
    rw [hsupp, hxy]
  have : IsIso f'.appTop :=
    IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of k')).inv f'.appTop
  have : IsIso iD.appTop := by
    have : IsIso (f'.appTop ≫ iD.appTop) := by
      rw [← Scheme.Hom.comp_appTop]
      exact inferInstanceAs (IsIso (Scheme.Γ.map (iD ≫ f').op))
    exact IsIso.of_isIso_comp_left f'.appTop iD.appTop
  have : IsIso (ID.subscheme.Γevaluation pt) :=
    Stacks.Chow.isIso_Γevaluation_of_isIntegral_of_subsingleton pt
  have : IsIso (iD.residueFieldMap pt) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (bijective_residueFieldMap_of_isClosedImmersion iD pt)
  have hΓ : IsIso (C.subscheme.Γevaluation (iD pt)) := by
    have : IsIso (C.subscheme.Γevaluation (iD pt) ≫ iD.residueFieldMap pt) := by
      rw [Scheme.Γevaluation_naturality]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (iD.residueFieldMap pt)
  exact ⟨iD pt, hy, hID, hΓ⟩

/-- **[Stacks, Tag 0E3I].** Let `X` be a proper scheme over a field `k` of dimension one with
`H⁰(X, 𝒪_X) = k` and at-worst-nodal singularities, and let `C ⊆ X` be a rational tail. For every
field extension `K/k` the base change `C_K ⊆ X_K` is a finite disjoint union of rational tails
of `X_K`: there are finitely many rational tails `Dᵢ` of `X_K` and an isomorphism
`∐ᵢ Dᵢ ≅ C_K` compatible with the closed immersions into `X_K`. -/
@[stacks 0E3I]
theorem exists_iso_sigma_isRationalTail_baseChange
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : HasAtWorstNodalSingularities k X)
    (C : X.IdealSheafData) (hC : IsRationalTail k X C) :
    let g : Spec (.of K) ⟶ Spec (.of k) :=
      Spec.map (CommRingCat.ofHom (algebraMap k K))
    let Y := (pullback (X ↘ Spec (.of k)) g : Scheme.{u})
    let p : Y ⟶ X := pullback.fst (X ↘ Spec (.of k)) g
    letI : Y.Over (Spec (.of K)) := ⟨pullback.snd (X ↘ Spec (.of k)) g⟩
    ∃ (ι : Type u) (_ : Finite ι) (D : ι → Y.IdealSheafData)
        (_ : ∀ i, IsRationalTail K Y (D i))
        (e : (∐ fun i ↦ (D i).subscheme) ≅ (C.comap p).subscheme),
      e.hom ≫ (C.comap p).subschemeι =
        Sigma.desc (fun i ↦ (D i).subschemeι) := by
  intro g Y p
  let : Y.Over (Spec (.of K)) := ⟨pullback.snd (X ↘ Spec (.of k)) g⟩
  have : IsIntegral C.subscheme := hC.isIntegral
  let A := Γ(C.subscheme, ⊤)
  let : Field A := (isField_of_universallyClosed k (C.subschemeι ≫ (X ↘ Spec (.of k)))).toField
  obtain ⟨ι, hι, L, hL, φ, D, cD, fDbase, jd, hjdo, b, hb, hD_integral, hSupport,
      hD_complementaryCurve_nonempty, hDbase, hcD, hjd⟩ :=
    exists_iso_sigma_baseChange_of_geometricallyIntegral k K X hdim C
      (topologicalKrullDim_subscheme_eq_one_of_isRationalTail k X hdim C hC)
      hC.complementaryCurve_nonempty
      (isSeparable_globalSections_of_isRationalTail k X hdim hnodal C hC)
      (geometricallyIntegral_toSpecΓ_of_isRationalTail k X hdim hnodal C hC)
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : Flat p := MorphismProperty.of_isPullback
    (IsPullback.of_hasPullback (X ↘ Spec (.of k)) g).flip
    (Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance))
  have : IsProper C.subscheme.toSpecΓ :=
    Stacks.AlgebraicGeometry.ProperGeomConnected.isProper_toSpecΓ
      (C.subschemeι ≫ (X ↘ Spec (.of k)))
  have : IsIso ((Scheme.ΓSpecIso (.of A)).inv ≫ C.subscheme.toSpecΓ.appTop) := by
    dsimp [A]
    rw [Scheme.toSpecΓ_appTop]
    infer_instance
  let (i : ι) : Algebra A (L i) := (φ i).hom.toAlgebra
  have hDbase_iso (i : ι) : IsIso ((Scheme.ΓSpecIso (.of (L i))).inv ≫ (fDbase i).appTop) :=
    isIso_globalSections_baseChange A (L i) (cD i) (fDbase i) C.subscheme.toSpecΓ (hDbase i)
  have : IsIso (Scheme.IdealSheafData.inclusion
      (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C) ≫ C.subscheme.toSpecΓ) :=
    isIso_inclusion_comp_toSpecΓ_of_isRationalTail hC
  have hD_tail (i : ι) : IsRationalTail K Y (D i) := by
    let ID := intersectionWithComplementaryCurveIdeal (D i)
    let iD := Scheme.IdealSheafData.inclusion (le_sup_left : D i ≤ ID)
    have := hjdo i
    obtain ⟨r, hr⟩ := intersectionWithComplementaryCurve_isPullback_general
      C (D i) p (jd i) (hjd i) (cD i) (hcD i)
    have hsq : IsPullback r (iD ≫ fDbase i) (Scheme.IdealSheafData.inclusion
        (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C) ≫ C.subscheme.toSpecΓ)
        (Spec.map (φ i)) := hr.flip.paste_vert (hDbase i)
    have : IsIso (iD ≫ fDbase i) := hsq.isIso_snd_of_isIso
    obtain ⟨x, hy, hID, hΓ⟩ :=
      exists_isIso_Γevaluation_of_isIso_inclusion_comp (D i) (L i) (fDbase i)
    have : IsProper (fDbase i) := MorphismProperty.of_isPullback (hDbase i) inferInstance
    have hgenus : genus ((D i).subschemeι ≫ (Y ↘ Spec (.of K))) = 0 :=
      genus_eq_zero_of_genus_eq_zero (fDbase i) _
        ((genus_baseChange A (L i) (cD i) (fDbase i) C.subscheme.toSpecΓ (hDbase i)).trans
          (genus_eq_zero_of_genus_eq_zero (C.subschemeι ≫ (X ↘ Spec (.of k))) _
            hC.genus_eq_zero))
    exact ⟨hD_integral i, hSupport i, hD_complementaryCurve_nonempty i, x, hy, hID, hΓ, hgenus⟩
  exact ⟨ι, hι, D, hD_tail, b, hb⟩

end AlgebraicGeometry

end
