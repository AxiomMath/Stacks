module

public import Mathlib.RingTheory.Algebraic.Cardinality
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyCompactPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactOpenGaloisDescent

/-!
# Geometric connectedness is tested by finite separable extensions

An algebraic space `X` over a field `k` is geometrically connected exactly when the base change
`X_{k'}` is connected for every *finite separable* extension `k'/k`.

## Main results

* `AlgebraicGeometry.Space.contains_spec_of_isAlgebraic`: the spectrum of an algebraic extension
  of a field inside the chosen big fppf site again lies in that site.
* `AlgebraicGeometry.Space.FieldValuedPoint.mem_obj_iff_class_mem_range`: a field-valued point
  lies in an open subspace exactly when the point it represents does.
* `AlgebraicGeometry.Space.isIntegralHom_yoneda_map`: a morphism of the site whose underlying
  morphism of schemes is integral represents an integral morphism of algebraic spaces.
* `AlgebraicGeometry.Space.isOpenMap_pointsOfRelocalizeRestrict_fieldExtensionMap` and
  `AlgebraicGeometry.Space.isClosedMap_pointsOfRelocalizeRestrict_fieldExtensionMap`: the
  projection `|X_K| → |X_E|` of a base change along a field extension is an open map, and a
  closed map when the extension is integral.
* `AlgebraicGeometry.Space.isGeometricallyConnected_iff_connectedSpace_finite_separable`: an
  algebraic space over a field `k` is geometrically connected if and only if its base change to
  every finite separable extension of `k` is connected.

## References

* [Stacks Project, Tag 0A17](https://stacks.math.columbia.edu/tag/0A17)
* [Stacks Project, Tag 0A13](https://stacks.math.columbia.edu/tag/0A13)
* [Stacks Project, Tag 0A15](https://stacks.math.columbia.edu/tag/0A15)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 04NN](https://stacks.math.columbia.edu/tag/04NN)
* [Stacks Project, Tag 06DN](https://stacks.math.columbia.edu/tag/06DN)
* [Stacks Project, Tag 0415](https://stacks.math.columbia.edu/tag/0415)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### Algebraic extensions inside the chosen big fppf site -/

/-- The spectrum of an algebraic extension of a field whose spectrum lies in the chosen big fppf
site again lies in that site. -/
theorem contains_spec_of_isAlgebraic (B : BigFppfSite.{u}) (k K : Type u) [Field k] [Field K]
    [Algebra k K] [Algebra.IsAlgebraic k K] (hk : B.Contains (Spec (.of k))) :
    B.Contains (Spec (.of K)) :=
  Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hk
    (by simpa [max_comm] using Algebra.IsAlgebraic.cardinalMk_le_max k K)

/-! ### Field-valued points of an open subspace -/

section OpenSubspace

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A field-valued point lies in an open subspace exactly when the point it represents does. -/
theorem FieldValuedPoint.mem_obj_iff_class_mem_range
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F) (V : Subfunctor F)
    (hV : IsOpenSubspace B S hS V) (p : FieldValuedPoint B S hS F) :
    p.value ∈ V.obj (op p.siteObject) ↔
      p.class B S hS F ∈ Set.range (pointsMap B S hS V.toFunctor V.ι) := by
  refine ⟨fun hp ↦ ⟨(⟨p.carrier, p.contained, p.toBase, ⟨p.value, hp⟩⟩ :
    FieldValuedPoint B S hS V.toFunctor).class B S hS V.toFunctor, rfl⟩, fun hp ↦ ?_⟩
  obtain ⟨f, hf⟩ := (factorsThrough_openSubspace_iff_points B S hS hF
    (isAlgebraicSpace_yoneda B S hS p.siteObject) V hV (yonedaEquiv.symm p.value)).2 (by
      rintro _ ⟨z, rfl⟩
      rwa [FieldValuedPoint.pointsMap_eq_class])
  have hval := congrArg yonedaEquiv hf
  rw [yonedaEquiv_comp, Equiv.apply_symm_apply] at hval
  exact hval ▸ (yonedaEquiv f).property

/-- Every point of an open subset of the point space of an algebraic space over `S` has a
quasi-compact open subspace whose point set contains it and is contained in that open subset. -/
theorem exists_isQuasiCompactSpace_isOpenSubspace_range_subset
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (U : Set (points B S hS F)) (hU : IsOpen U) (x : points B S hS F) (hx : x ∈ U) :
    ∃ V : Subfunctor F, IsOpenSubspace B S hS V ∧ IsQuasiCompactSpace B S hS V.toFunctor ∧
      x ∈ Set.range (pointsMap B S hS V.toFunctor V.ι) ∧
      Set.range (pointsMap B S hS V.toFunctor V.ι) ⊆ U := by
  obtain ⟨W, ⟨hWopen, hWcompact, hxW⟩, hWU⟩ :=
    (hasBasis_nhds_isOpen_isCompact B S hS F hF x).mem_iff.mp (hU.mem_nhds hx)
  obtain ⟨V, hV, hVrange⟩ := exists_isOpenSubspace_range_pointsMap_eq B S hS hF W hWopen
  refine ⟨V, hV, ?_, by rwa [hVrange], by rwa [hVrange]⟩
  refine (isQuasiCompactSpace_iff_compactSpace_points B S hS V.toFunctor hV.1).2 ⟨?_⟩
  refine (isEmbedding_pointsMap_of_isImmersion B S hS hF V.ι
    (isImmersion_of_isOpenImmersion B S hS hV.2)).isCompact_iff.mpr ?_
  rwa [Set.image_univ, hVrange]

end OpenSubspace

/-! ### Integral morphisms between represented presheaves -/

/-- A morphism of the big fppf site of `S` whose underlying morphism of schemes is integral
represents an integral morphism of algebraic spaces over `S`. -/
theorem isIntegralHom_yoneda_map (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V : BigFppfOver B S hS} (φ : U ⟶ V)
    (hφ : _root_.AlgebraicGeometry.IsIntegralHom ((BigFppfOver.toScheme B S hS).map φ)) :
    IsIntegralHom B S hS (yoneda.map φ) :=
  (isIntegralHom_iff_representable B S hS (yoneda.map φ)
      (isAlgebraicSpace_yoneda B S hS U) (isAlgebraicSpace_yoneda B S hS V)).2
    ⟨Functor.relativelyRepresentable.map yoneda φ,
      (presheaf_yoneda_map_iff B S hS
        (P := @_root_.AlgebraicGeometry.IsIntegralHom.{u}) inferInstance φ).2 hφ⟩

/-! ### The projection of a base change along a field extension -/

section Projection

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (E K : Type u) [Field E] [Field K] [Algebra E K]
  (hE : B.Contains (Spec (.of E))) (hK : B.Contains (Spec (.of K)))
  (F : (BigFppfOver B (Spec (.of E)) hE)ᵒᵖ ⥤ Type u)

/-- The structure morphism of the spectrum of a field extension `K/E`, read as a morphism of
presheaves on the big fppf site over `Spec E` with target the representable presheaf of the
terminal object of the slice. -/
private noncomputable abbrev fieldExtensionToTerminal :
    yoneda.obj (Over.mk (fieldExtensionMap B E K hE hK)) ⟶
      yoneda.obj (Over.mk (𝟙 (B.obj hE))) :=
  OverShriek.toYonedaMkId (yoneda.obj (Over.mk (fieldExtensionMap B E K hE hK)))

/-- The base change of `F` to `K`, viewed again over `E`, is the product of `F` with
`Spec K`. -/
private theorem isPullback_counit_fieldExtensionMap :
    IsPullback (OverShriek.relocalizeRestrictCounit (fieldExtensionMap B E K hE hK) F)
      (OverShriek.relocalizeToYoneda (fieldExtensionMap B E K hE hK)
        ((OverShriek.relocalizeRestrict (fieldExtensionMap B E K hE hK)).obj F))
      (OverShriek.toYonedaMkId F) (fieldExtensionToTerminal B E K hE hK) :=
  OverShriek.isPullback_relocalizeRestrictCounit (fieldExtensionMap B E K hE hK) F
    (fun W ↦ OverShriek.subsingleton_yoneda_obj_mkId W) _ _

/-- The point space of the base change of `F` to `K` and that of the product of `F` with
`Spec K` over `Spec E` are homeomorphic. -/
private noncomputable def pointsProductHomeo
    (hF : IsAlgebraicSpace B (Spec (.of E)) hE F) :
    points B (Spec (.of K)) hK
        ((OverShriek.relocalizeRestrict (fieldExtensionMap B E K hE hK)).obj F) ≃ₜ
      points B (Spec (.of E)) hE
        (pullback (OverShriek.toYonedaMkId F) (fieldExtensionToTerminal B E K hE hK)) :=
  (relocalizedPointsHomeo B (Spec (.of K)) (Spec (.of E)) hK hE
      (fieldExtensionMap B E K hE hK) _
      (isAlgebraicSpace_relocalizeRestrict B (Spec (.of K)) (Spec (.of E)) hK hE
        (fieldExtensionMap B E K hE hK) F hF)).trans
    (pointsHomeomorphOfIso B (Spec (.of E)) hE
      (isPullback_counit_fieldExtensionMap B E K hE hK F).isoPullback)

/-- On points, restriction to the smaller base `Spec E` is the first projection of the product
of `F` with `Spec K`, up to the homeomorphism identifying the two point spaces. -/
private theorem pointsOfRelocalizeRestrict_eq_pointsMap_fst
    (hF : IsAlgebraicSpace B (Spec (.of E)) hE F) :
    pointsOfRelocalizeRestrict B (Spec (.of K)) (Spec (.of E)) hK hE
        (fieldExtensionMap B E K hE hK) F =
      pointsMap B (Spec (.of E)) hE _
          (pullback.fst (OverShriek.toYonedaMkId F) (fieldExtensionToTerminal B E K hE hK)) ∘
        pointsProductHomeo B E K hE hK F hF := by
  funext a
  have h₁ := congrFun (pointsOfRelocalizeRestrict_eq B (Spec (.of K)) (Spec (.of E)) hK hE
    (fieldExtensionMap B E K hE hK) F) a
  rw [Function.comp_apply] at h₁
  have h₂ := congrFun (pointsMap_comp B (Spec (.of E)) hE
      ((OverShriek.relocalizePresheafFunctor (fieldExtensionMap B E K hE hK)).obj
        ((OverShriek.relocalizeRestrict (fieldExtensionMap B E K hE hK)).obj F))
      (isPullback_counit_fieldExtensionMap B E K hE hK F).isoPullback.hom
      (pullback.fst (OverShriek.toYonedaMkId F) (fieldExtensionToTerminal B E K hE hK)))
    (relocalizedPointsMap B (Spec (.of K)) (Spec (.of E)) hK hE
      (fieldExtensionMap B E K hE hK)
      ((OverShriek.relocalizeRestrict (fieldExtensionMap B E K hE hK)).obj F) a)
  rw [(isPullback_counit_fieldExtensionMap B E K hE hK F).isoPullback_hom_fst,
    Function.comp_apply] at h₂
  exact h₁.trans h₂

/-- Restriction along a field extension is an open map on points. -/
theorem isOpenMap_pointsOfRelocalizeRestrict_fieldExtensionMap
    (hF : IsAlgebraicSpace B (Spec (.of E)) hE F) :
    IsOpenMap (pointsOfRelocalizeRestrict B (Spec (.of K)) (Spec (.of E)) hK hE
      (fieldExtensionMap B E K hE hK) F) := by
  rw [pointsOfRelocalizeRestrict_eq_pointsMap_fst B E K hE hK F hF]
  exact IsOpenMap.comp (universallyOpen_to_field B (Spec (.of E)) hE
    (isAlgebraicSpace_yoneda B (Spec (.of E)) hE (Over.mk (fieldExtensionMap B E K hE hK)))
    (k := E) (Iso.refl _) (fieldExtensionToTerminal B E K hE hK) F hF
    (OverShriek.toYonedaMkId F)) (pointsProductHomeo B E K hE hK F hF).isOpenMap

/-- Restriction along an integral field extension is a closed map on points. -/
theorem isClosedMap_pointsOfRelocalizeRestrict_fieldExtensionMap [Algebra.IsIntegral E K]
    (hF : IsAlgebraicSpace B (Spec (.of E)) hE F) :
    IsClosedMap (pointsOfRelocalizeRestrict B (Spec (.of K)) (Spec (.of E)) hK hE
      (fieldExtensionMap B E K hE hK) F) := by
  have hint : _root_.AlgebraicGeometry.IsIntegralHom
      ((BigFppfOver.toScheme B (Spec (.of E)) hE).map
        (Over.homMk (fieldExtensionMap B E K hE hK) (Category.comp_id _) :
          (Over.mk (fieldExtensionMap B E K hE hK) : BigFppfOver B (Spec (.of E)) hE) ⟶
            Over.mk (𝟙 (B.obj hE)))) := by
    have hmap : (BigFppfOver.toScheme B (Spec (.of E)) hE).map
        (Over.homMk (fieldExtensionMap B E K hE hK) (Category.comp_id _) :
          (Over.mk (fieldExtensionMap B E K hE hK) : BigFppfOver B (Spec (.of E)) hE) ⟶
            Over.mk (𝟙 (B.obj hE))) =
        Spec.map (CommRingCat.ofHom (algebraMap E K)) :=
      map_fieldExtensionMap B E K hE hK
    rw [hmap, _root_.AlgebraicGeometry.IsIntegralHom.SpecMap_iff]
    exact algebraMap_isIntegral_iff.mpr inferInstance
  have hτ : fieldExtensionToTerminal B E K hE hK =
      yoneda.map (Over.homMk (fieldExtensionMap B E K hE hK) (Category.comp_id _) :
        (Over.mk (fieldExtensionMap B E K hE hK) : BigFppfOver B (Spec (.of E)) hE) ⟶
          Over.mk (𝟙 (B.obj hE))) := by
    ext W x
    exact (OverShriek.subsingleton_yoneda_obj_mkId W).elim _ _
  rw [pointsOfRelocalizeRestrict_eq_pointsMap_fst B E K hE hK F hF]
  exact IsClosedMap.comp (universallyClosed_of_isIntegralHom B (Spec (.of E)) hE
    (isAlgebraicSpace_yoneda B (Spec (.of E)) hE (Over.mk (fieldExtensionMap B E K hE hK)))
    (isAlgebraicSpace_yoneda B (Spec (.of E)) hE (Over.mk (𝟙 (B.obj hE))))
    (hτ ▸ isIntegralHom_yoneda_map B (Spec (.of E)) hE _ hint) F hF
    (OverShriek.toYonedaMkId F)) (pointsProductHomeo B E K hE hK F hF).isClosedMap

end Projection

/-! ### Stacks 0A17 -/

section FiniteSeparable

attribute [local instance] pointTopology

/-- A clopen subset of the source of an open and closed map onto a connected space which
contains the whole fibre through one of its points is everything. -/
private theorem isClopen_eq_univ_of_fibre_subset {Y Z : Type*} [TopologicalSpace Y]
    [TopologicalSpace Z] [ConnectedSpace Z] {p : Y → Z} (hpOpen : IsOpenMap p)
    (hpClosed : IsClosedMap p) {U : Set Y} (hU : IsClopen U) (x : Y)
    (hfibre : ∀ y, p y = p x → y ∈ U) : U = Set.univ := by
  have himage : IsClopen (p '' Uᶜ) :=
    ⟨hpClosed _ hU.compl.isClosed, hpOpen _ hU.compl.isOpen⟩
  rcases (connectedSpace_iff_clopen.mp (inferInstance : ConnectedSpace Z)).2 _ himage with
    hempty | hfull
  · simpa using congrArg (fun s : Set Y ↦ sᶜ) (Set.image_eq_empty.mp hempty)
  · obtain ⟨y, hy, hxy⟩ : p x ∈ p '' Uᶜ := hfull.symm ▸ Set.mem_univ _
    exact absurd (hfibre y hxy) hy

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A subfunctor whose preimage along the isomorphism induced by an equality of presheaves is an
open subspace is itself an open subspace. -/
private theorem isOpenSubspace_of_preimage_eqToHom_eq
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F = G) (A : Subfunctor F) (W : Subfunctor G)
    (hW : IsOpenSubspace B S hS W) (hWA : Subfunctor.preimage W (eqToHom e) = A) :
    IsOpenSubspace B S hS A := by
  cases e
  simp only [eqToHom_refl, Subfunctor.preimage_id] at hWA
  subst hWA
  exact hW

/-- The point set of a subfunctor is the preimage of the point set of its preimage along the
isomorphism induced by an equality of presheaves. -/
private theorem range_pointsMap_eq_preimage_of_preimage_eqToHom_eq
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F = G) (A : Subfunctor F) (W : Subfunctor G)
    (hWA : Subfunctor.preimage W (eqToHom e) = A) :
    Set.range (pointsMap B S hS W.toFunctor W.ι) =
      pointsMap B S hS G (eqToIso e).inv ⁻¹'
        Set.range (pointsMap B S hS A.toFunctor A.ι) := by
  cases e
  simp only [eqToHom_refl, Subfunctor.preimage_id] at hWA
  subst hWA
  change _ = pointsMap B S hS F (𝟙 F) ⁻¹' _
  rw [pointsMap_id, Set.preimage_id]

/-- The point set of the base change of an open subspace is the preimage of its point set. -/
private theorem range_pointsMap_relocalizeRestrictSubfunctor (S' : Scheme.{u})
    (hS' : B.Contains S') (g : B.obj hS ⟶ B.obj hS')
    {F : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S' hS' F)
    (V : Subfunctor F) (hV : IsOpenSubspace B S' hS' V)
    (hRV : IsOpenSubspace B S hS (OverShriek.relocalizeRestrictSubfunctor g V)) :
    Set.range (pointsMap B S hS (OverShriek.relocalizeRestrictSubfunctor g V).toFunctor
        (OverShriek.relocalizeRestrictSubfunctor g V).ι) =
      pointsOfRelocalizeRestrict B S S' hS hS' g F ⁻¹'
        Set.range (pointsMap B S' hS' V.toFunctor V.ι) := by
  ext x
  induction x using Quot.inductionOn with
  | h p =>
    rw [Set.mem_preimage, pointsOfRelocalizeRestrict_class,
      ← FieldValuedPoint.mem_obj_iff_class_mem_range B S hS
        (isAlgebraicSpace_relocalizeRestrict B S S' hS hS' g F hF) _ hRV p,
      ← FieldValuedPoint.mem_obj_iff_class_mem_range B S' hS' hF V hV]
    rfl

/-- If the base change of `X` to every finite separable extension of `k` has a connected space of
points, then so does its base change to a separable closure `K` of `k`. -/
private theorem connectedSpace_relocalizeRestrict_of_forall_finite_separable
    (k K : Type u) [Field k] [Field K] [Algebra k K] [IsSepClosure k K]
    (hk : B.Contains (Spec (.of k))) (hK : B.Contains (Spec (.of K)))
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (h : ∀ (E : Type u) [Field E] [Algebra k E] [FiniteDimensional k E]
      [Algebra.IsSeparable k E] (hE : B.Contains (Spec (.of E))),
      ConnectedSpace (points B (Spec (.of E)) hE
        ((OverShriek.relocalizeRestrict (fieldExtensionMap B k E hk hE)).obj X))) :
    ConnectedSpace (points B (Spec (.of K)) hK
      ((OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).obj X)) := by
  classical
  have halg : Algebra.IsAlgebraic k K := Algebra.IsSeparable.isAlgebraic k K
  have hXK : IsAlgebraicSpace B (Spec (.of K)) hK
      ((OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).obj X) :=
    isAlgebraicSpace_relocalizeRestrict B (Spec (.of K)) (Spec (.of k)) hK hk
      (fieldExtensionMap B k K hk hK) X hX
  have hne : Nonempty (points B (Spec (.of K)) hK
      ((OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).obj X)) := by
    have hkk : ConnectedSpace (points B (Spec (.of k)) hk
      ((OverShriek.relocalizeRestrict (fieldExtensionMap B k k hk hk)).obj X)) := h k hk
    obtain ⟨x⟩ := (inferInstance : Nonempty (points B (Spec (.of k)) hk
      ((OverShriek.relocalizeRestrict (fieldExtensionMap B k k hk hk)).obj X)))
    obtain ⟨y, -⟩ := surjective_pointsOfRelocalizeRestrict_fieldExtension B k K hk hK
      (fieldExtensionMap B k K hk hK) X
      (pointsOfRelocalizeRestrict B (Spec (.of k)) (Spec (.of k)) hk hk
        (fieldExtensionMap B k k hk hk) X x)
    exact ⟨y⟩
  refine connectedSpace_iff_clopen.mpr ⟨hne, fun U hU ↦ or_iff_not_imp_left.mpr fun hUempty ↦ ?_⟩
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hUempty
  obtain ⟨W, hW, hWqc, hxW, hWU⟩ :=
    exists_isQuasiCompactSpace_isOpenSubspace_range_subset B (Spec (.of K)) hK hXK U hU.isOpen
      x hx
  obtain ⟨E, hEfin, hE, V, hV, hVqc, hdesc⟩ :=
    exists_finite_subextension_descending_isQuasiCompact_open B k K hk hK X hX W hW hWqc
  have _ : FiniteDimensional k E := hEfin
  have _ : Algebra.IsSeparable k E := Algebra.isSeparable_tower_bot_of_isSeparable k E K
  have _ : Algebra.IsIntegral E K := Algebra.IsIntegral.tower_top k
  have hXE : IsAlgebraicSpace B (Spec (.of E)) hE
      ((OverShriek.relocalizeRestrict (fieldExtensionMap B k E hk hE)).obj X) :=
    isAlgebraicSpace_relocalizeRestrict B (Spec (.of E)) (Spec (.of k)) hE hk
      (fieldExtensionMap B k E hk hE) X hX
  have _ : ConnectedSpace (points B (Spec (.of E)) hE
    ((OverShriek.relocalizeRestrict (fieldExtensionMap B k E hk hE)).obj X)) := h E hE
  have hA : IsOpenSubspace B (Spec (.of K)) hK
      (OverShriek.relocalizeRestrictSubfunctor (fieldExtensionMap B E K hE hK) V) :=
    isOpenSubspace_of_preimage_eqToHom_eq B (Spec (.of K)) hK
      (relocalizeRestrict_fieldExtensionMap_comp B k E K hk hE hK X) _ W hW hdesc
  set p := pointsOfRelocalizeRestrict B (Spec (.of K)) (Spec (.of E)) hK hE
      (fieldExtensionMap B E K hE hK)
      ((OverShriek.relocalizeRestrict (fieldExtensionMap B k E hk hE)).obj X) ∘
    pointsMap B (Spec (.of K)) hK
      ((OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).obj X)
      (eqToIso (relocalizeRestrict_fieldExtensionMap_comp B k E K hk hE hK X)).inv with hpdef
  have hpOpen : IsOpenMap p :=
    (isOpenMap_pointsOfRelocalizeRestrict_fieldExtensionMap B E K hE hK _ hXE).comp
      (pointsHomeomorphOfIso B (Spec (.of K)) hK
        (eqToIso (relocalizeRestrict_fieldExtensionMap_comp B k E K hk hE hK X)).symm).isOpenMap
  have hpClosed : IsClosedMap p :=
    (isClosedMap_pointsOfRelocalizeRestrict_fieldExtensionMap B E K hE hK _ hXE).comp
      (pointsHomeomorphOfIso B (Spec (.of K)) hK
        (eqToIso
          (relocalizeRestrict_fieldExtensionMap_comp B k E K hk hE hK X)).symm).isClosedMap
  have hWrange : Set.range (pointsMap B (Spec (.of K)) hK W.toFunctor W.ι) =
      p ⁻¹' Set.range (pointsMap B (Spec (.of E)) hE V.toFunctor V.ι) := by
    rw [hpdef, Set.preimage_comp,
      ← range_pointsMap_relocalizeRestrictSubfunctor B (Spec (.of K)) hK (Spec (.of E)) hE
        (fieldExtensionMap B E K hE hK) hXE V hV hA]
    exact range_pointsMap_eq_preimage_of_preimage_eqToHom_eq B (Spec (.of K)) hK
      (relocalizeRestrict_fieldExtensionMap_comp B k E K hk hE hK X) _ W hdesc
  refine isClopen_eq_univ_of_fibre_subset hpOpen hpClosed hU x fun y hy ↦ hWU ?_
  rw [hWrange] at hxW ⊢
  simpa only [Set.mem_preimage, hy] using hxW

/-- Let `k` be a field and let `X` be an algebraic space over `k`. Then `X` is
geometrically connected over `k` if and only if the base change `X_{k'}` has a connected space of
points for every finite separable field extension `k'/k` whose spectrum lies in the chosen big
fppf site. -/
@[stacks 0A17, ega "IV 8.4.5", ega "IV 4.5.18" "more general"]
theorem isGeometricallyConnected_iff_connectedSpace_finite_separable (B : BigFppfSite.{u})
    (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X) :
    IsGeometricallyConnected B k hk X ↔
      ∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K]
        [Algebra.IsSeparable k K] (hK : B.Contains (Spec (.of K))),
        ConnectedSpace (points B (Spec (.of K)) hK
          ((OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).obj X)) := by
  refine ⟨fun hgc K _ _ _ _ hK ↦ hgc K hK, fun h ↦ ?_⟩
  have halg : Algebra.IsAlgebraic k (SeparableClosure k) :=
    Algebra.IsSeparable.isAlgebraic k (SeparableClosure k)
  have hK : B.Contains (Spec (.of (SeparableClosure k))) :=
    contains_spec_of_isAlgebraic B k (SeparableClosure k) hk
  exact (isGeometricallyConnected_iff_connectedSpace_sepClosure B k (SeparableClosure k) hk hK
      X hX).2
    (connectedSpace_relocalizeRestrict_of_forall_finite_separable B k (SeparableClosure k) hk
      hK X hX h)

end FiniteSeparable

end AlgebraicGeometry.Space

end
