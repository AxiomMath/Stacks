module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.AssociatedNumericalType
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ExceptionalComponentsMeet
public import StacksFrontier.AlgebraicGeometry.Curves.Models.MinimalModel
public import StacksFrontier.AlgebraicGeometry.Curves.Models.RationalPointSpecialFibre
public import StacksFrontier.AlgebraicGeometry.Curves.Models.InseparableModel.ComponentGenus
public import StacksFrontier.AlgebraicGeometry.NodalContraction.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Dimension.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.GlobalFunctionsConstant
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ContractionMorphism
public import StacksFrontier.Topology.Dimension.DimensionLEOne
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.SchemeIsoDegree
public import StacksFrontier.AlgebraicGeometry.Picard.CurveDegreeHom
public import StacksFrontier.AlgebraicGeometry.ProperGeomConnected.Basic
public import StacksFrontier.AlgebraicGeometry.ProjCoherentCohomologyFinite.Basic

/-!
# Exceptional curves of the first kind on a regular proper model

In the situation of [Stacks, Tag 0C61] let `X ⟶ Spec(R)` be a regular proper model. This file
proves that an exceptional curve of the first kind `E ⊆ X` is one of the irreducible components
`Cᵢ` of the special fibre `X_k`, taken with its reduced structure, and that then `gᵢ = 0` and
`(Cᵢ · Cᵢ) = -[κᵢ : k]`, that is `i` is a minus-one index of the numerical type associated to `X`.
Consequently a regular proper model whose associated numerical type is minimal is a minimal model:
this is the implication (2) ⇒ (1) of [Stacks, Tag 0CA6].

## Main results

The first four results are in the namespace `Stacks.Models.RegularProperModelSituation`.

* `exists_eq_specialFiberComponentIdeal_of_iso_projectiveLineProj`:
  a closed subscheme of `X` presented as a projective line over a field is a component of `X_k`.
* `isMinusOneIndex_associatedNumericalType_of_isExceptionalCurveOfFirstKind`:
  an exceptional component of the first kind is a minus-one index of the associated numerical type.
* `isMinimalModel_of_isMinimal_associatedNumericalType`:
  a regular proper model with minimal associated numerical type is a minimal model.
* `isExceptionalCurveOfFirstKind_specialFiberComponentIdeal_of_iso`:
  conversely, a component with `(Cᵢ · Cᵢ) = -[κᵢ : k]` which is a projective line over some field
  is an exceptional curve of the first kind. This is the geometric half of (1) ⇒ (2) of
  [Stacks, Tag 0CA6]; the other half, that such a component of genus zero is a projective line,
  is [Stacks, Tag 0C6U].
* `AlgebraicGeometry.invertibleCurveDegree_eq_finrank_globalSections_mul_toSpecΓ`: the degree over
  `k` is `[Γ(X, 𝒪_X) : k]` times the degree over the field `Γ(X, 𝒪_X)`.
* `AlgebraicGeometry.invertibleCurveDegree_twistingSheaf_projectiveLineProj`: `deg 𝒪(d) = d` on
  `𝐏¹_κ`.

## The argument

Let `E` be presented as `𝐏¹_κ`. The global functions of `𝐏¹_κ` are `κ`, so the composite
`E ⟶ X ⟶ Spec(R)` factors through the one-point space `Spec(κ)`; its image is a single point, which
is closed because `E ⟶ Spec(R)` is proper, hence is the closed point. So `E ⊆ X_k`. The generic
point of `E` lies on some component `Cᵢ`, so `E ⊆ Cᵢ`. Inside the irreducible curve `Cᵢ` a closed
irreducible proper subset is a single point, while `E ≅ 𝐏¹_κ` is one-dimensional, so `E = Cᵢ` as
sets, and since `E` is reduced it is `Cᵢ` with its reduced structure. Finally `H¹(𝐏¹_κ, 𝒪) = 0`
gives `gᵢ = 0`, and the self-intersection of an exceptional component is
`(Cᵢ · Cᵢ) = -[κᵢ : k] + g_{Cᵢ/k}`
(`RegularProperModelSituation.specialFiberIntersectionMatrix_self_eq_neg_weight_add_genus`).

For the converse direction, the normal sheaf `𝒪_X(Cᵢ)|_{Cᵢ}` of a component presented as `𝐏¹_κ`
pulls back to a twist `𝒪(d)` ([Stacks, Tag 0BXJ]); its degree over `k` is `(Cᵢ · Cᵢ)`, so by the
tower law its degree over `κᵢ`, which is also its degree over `κ`, is `(Cᵢ · Cᵢ)/[κᵢ : k]`. When
`(Cᵢ · Cᵢ) = -[κᵢ : k]` this is `-1`, and `d = deg 𝒪(d) = -1`.

## References

* [Stacks Project, Tag 0CA6](https://stacks.math.columbia.edu/tag/0CA6)
* [Stacks Project, Tag 0C2V](https://stacks.math.columbia.edu/tag/0C2V)
* [Stacks Project, Section 0C2I](https://stacks.math.columbia.edu/tag/0C2I)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

open Stacks.AlgebraicGeometry.ProjPolyChart (projToSpecCoeff)

attribute [local instance] Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff

/-- The canonical morphism `X ⟶ Spec Γ(X, 𝒪_X)` induces the identity on global sections. -/
private theorem ΓSpecIso_inv_comp_toSpecΓ_appTop (X : Scheme.{u}) :
    (Scheme.ΓSpecIso (.of Γ(X, ⊤))).inv ≫ X.toSpecΓ.appTop = 𝟙 Γ(X, ⊤) := by
  rw [Scheme.toSpecΓ_appTop]
  exact (Scheme.ΓSpecIso Γ(X, ⊤)).inv_hom_id

/-- For an isomorphism `e : Y ≅ X`, the composite `Y ⟶ X ⟶ Spec Γ(X, 𝒪_X)` induces an isomorphism
on global sections. -/
private theorem isIso_ΓSpecIso_inv_comp_appTop_hom_comp_toSpecΓ {X Y : Scheme.{u}} (e : Y ≅ X) :
    IsIso ((Scheme.ΓSpecIso (.of Γ(X, ⊤))).inv ≫ (e.hom ≫ X.toSpecΓ).appTop) := by
  have : IsIso e.hom.appTop :=
    ⟨e.inv.appTop, by rw [← Scheme.Hom.comp_appTop, e.inv_hom_id]; simp,
      by rw [← Scheme.Hom.comp_appTop, e.hom_inv_id]; simp⟩
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ΓSpecIso_inv_comp_toSpecΓ_appTop]
  infer_instance

/-- The structure morphism of the projective line over a field `κ` induces an isomorphism from `κ`
onto the global sections. -/
private theorem isIso_ΓSpecIso_inv_comp_appTop_projToSpecCoeff (κ : Type u) [Field κ] :
    IsIso ((Scheme.ΓSpecIso (.of κ)).inv ≫ (projToSpecCoeff κ 1).appTop) :=
  (ConcreteCategory.isIso_iff_bijective _).2
    (Stacks.ProjectiveSpace.Cohomology.bijective_coeffToGlobalSections κ 1)

/-- **The tower law for the degree of an invertible module.** Let `X` be proper of dimension at
most one over a field `k`, and suppose the global functions `κ = Γ(X, 𝒪_X)` form a field. Then
the degree over `k` of an invertible module is `[κ : k]` times its degree over `κ`, the latter
taken along the canonical morphism `X ⟶ Spec(κ)`. Both degrees are formed from the same
cohomology groups, on which `k` acts through `κ`. -/
theorem invertibleCurveDegree_eq_finrank_globalSections_mul_toSpecΓ (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [IsProper X.toSpecΓ]
    (hdim : topologicalKrullDim X ≤ 1) (hκ : IsField Γ(X, ⊤)) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    letI : Field Γ(X, ⊤) := hκ.toField
    letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    invertibleCurveDegree k f hdim L =
      (Module.finrank k Γ(X, ⊤) : ℤ) * invertibleCurveDegree Γ(X, ⊤) X.toSpecΓ hdim L := by
  let : Field Γ(X, ⊤) := hκ.toField
  let : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  have hcompat : ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom =
      ((Scheme.ΓSpecIso (.of Γ(X, ⊤))).inv ≫ X.toSpecΓ.appTop).hom.comp
        (algebraMap k Γ(X, ⊤)) := by
    rw [ΓSpecIso_inv_comp_toSpecΓ_appTop, RingHom.algebraMap_toAlgebra]
    ext x
    rfl
  have hv : ∀ (K : Type u) [Field K] (g : X ⟶ Spec (.of K)) [IsProper g] (F : X.Modules) (m : ℕ),
      2 ≤ m → IsZero (cohomologyOverField K g F m) :=
    fun K _ g _ F m hm => isZero_cohomologyOverField_of_topologicalKrullDim_le K g F (d := 1)
      (by exact_mod_cast hdim) (by omega)
  rw [invertibleCurveDegree_eq_sub_of_isZero k f hdim L (hv k f L) (hv k f _),
    invertibleCurveDegree_eq_sub_of_isZero Γ(X, ⊤) X.toSpecΓ hdim L (hv _ _ L) (hv _ _ _)]
  have hfr := finrank_cohomologyOverField_eq_finrank_mul k Γ(X, ⊤) f X.toSpecΓ hcompat
  rw [hfr L 0, hfr L 1, hfr (SheafOfModules.unit X.ringCatSheaf) 0,
    hfr (SheafOfModules.unit X.ringCatSheaf) 1]
  push_cast
  ring

/-- If `X ⟶ Spec(k)` induces an isomorphism `k ≅ Γ(X, 𝒪_X)` onto a field of global functions, the
degree over `k` of an invertible module equals its degree over `Γ(X, 𝒪_X)`. -/
private theorem invertibleCurveDegree_eq_toSpecΓ_of_isIso (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsProper X.toSpecΓ] (hdim : topologicalKrullDim X ≤ 1)
    (hκ : IsField Γ(X, ⊤)) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] :
    letI : Field Γ(X, ⊤) := hκ.toField
    invertibleCurveDegree k f hdim L = invertibleCurveDegree Γ(X, ⊤) X.toSpecΓ hdim L := by
  let : Field Γ(X, ⊤) := hκ.toField
  rw [invertibleCurveDegree_eq_finrank_globalSections_mul_toSpecΓ k f hdim hκ L,
    finrank_globalSections_eq_one_of_isIso k f]
  simp

/-- The degree of an invertible module is unchanged by pullback along an isomorphism. -/
private theorem invertibleCurveDegree_pullback_of_isIso (k : Type u) [Field k] {X Y : Scheme.{u}}
    (e : Y ⟶ X) [IsIso e] (f : X ⟶ Spec (.of k)) [IsProper f] [IsProper (e ≫ f)]
    (hX : topologicalKrullDim X ≤ 1) (hY : topologicalKrullDim Y ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      ((Scheme.Modules.pullback e).obj L)] :
    invertibleCurveDegree k (e ≫ f) hY ((Scheme.Modules.pullback e).obj L) =
      invertibleCurveDegree k f hX L := by
  unfold invertibleCurveDegree
  congr 1
  · exact finsum_congr fun n => by rw [finrank_cohomologyOverField_pullback k e f L n]
  · exact finsum_congr fun n => by rw [finrank_cohomologyOverField_unit_pushforward k e f n]

/-- The projective line over a field is one-dimensional. -/
theorem topologicalKrullDim_projectiveLineProj (κ : Type u) [Field κ] :
    topologicalKrullDim (projectiveLineProj κ) = 1 := by
  simpa using Stacks.ProjectiveSpace.topologicalKrullDim_proj_fin κ (r := 2) two_pos

/-- **The twist `𝒪(d)` on the projective line over a field has degree `d`.** The degree is a
homomorphism on the Picard group, and so is `d ↦ [𝒪(d)]`; their composite `ℤ ⟶ ℤ` takes `-1` to
`deg 𝒪(-1) = χ(𝒪(-1)) - χ(𝒪) = 0 - 1 = -1`, the twist `𝒪(-1)` having no cohomology. -/
theorem invertibleCurveDegree_twistingSheaf_projectiveLineProj (κ : Type u) [Field κ] (d : ℤ) :
    @invertibleCurveDegree κ _ _ (projToSpecCoeff κ 1) _
      (topologicalKrullDim_projectiveLineProj κ).le
      (ProjectiveSpectrum.Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin 2) κ) d)
      (Stacks.PicardUFD.isInvertible_twistingSheaf κ 1 d) = d := by
  set hdim := (topologicalKrullDim_projectiveLineProj κ).le
  let φ : ℤ →+ ℤ := (invertibleCurveDegreeHom κ (projToSpecCoeff κ 1) hdim).comp
    (Stacks.PicardUFD.twistPicardHom κ 1)
  have hφ : ∀ m : ℤ, φ m = @invertibleCurveDegree κ _ _ (projToSpecCoeff κ 1) _ hdim
      (ProjectiveSpectrum.Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin 2) κ) m)
      (Stacks.PicardUFD.isInvertible_twistingSheaf κ 1 m) := fun m =>
    invertibleCurveDegreeHom_picardClass κ (projToSpecCoeff κ 1) hdim _ _
  have hneg : φ (-1) = -1 := by
    rw [hφ]
    have hvan : ∀ q, Module.finrank κ (cohomologyOverField κ (projToSpecCoeff κ 1)
        (ProjectiveSpectrum.Proj.twistingSheaf
          (MvPolynomial.homogeneousSubmodule (Fin 2) κ) (-1)) q) = 0 := fun q => by
      have := ModuleCat.subsingleton_of_isZero
        (Stacks.Models.isZero_cohomologyOverField_twistingSheaf_neg_one κ q)
      exact Module.finrank_zero_of_subsingleton
    have := isIso_ΓSpecIso_inv_comp_appTop_projToSpecCoeff κ
    rw [Stacks.Models.invertibleCurveDegree_eq_neg_finrank_globalSections_add_genus κ
      (projToSpecCoeff κ 1) hdim _ hvan,
      finrank_globalSections_eq_one_of_isIso κ (projToSpecCoeff κ 1),
      Stacks.Curves.genus_projToSpecCoeff_one]
    simp
  have h1 : φ 1 = 1 := by
    have := map_neg φ 1
    omega
  rw [← hφ, show d = d • (1 : ℤ) by simp, map_zsmul, h1]

end AlgebraicGeometry

namespace Stacks.Models

/-- In the spectrum of a local ring, two closed points are equal. -/
private theorem eq_of_isClosed_singleton_of_isLocalRing {R : Type u} [CommRing R]
    [IsLocalRing R] {p q : PrimeSpectrum R} (hp : IsClosed ({p} : Set (PrimeSpectrum R)))
    (hq : IsClosed ({q} : Set (PrimeSpectrum R))) : p = q :=
  PrimeSpectrum.ext ((IsLocalRing.eq_maximalIdeal
    ((PrimeSpectrum.isClosed_singleton_iff_isMaximal p).1 hp)).trans
    (IsLocalRing.eq_maximalIdeal ((PrimeSpectrum.isClosed_singleton_iff_isMaximal q).1 hq)).symm)

/-- If a closed map takes a single value, its range is that one point, which is closed. -/
private theorem range_eq_singleton_and_isClosed_singleton_of_isClosedMap {α β : Type*}
    [TopologicalSpace α] [TopologicalSpace β] {f : α → β} (hf : IsClosedMap f) (a : α)
    (h : ∀ b, f b = f a) : Set.range f = {f a} ∧ IsClosed ({f a} : Set β) := by
  have hrange : Set.range f = {f a} :=
    Set.eq_singleton_iff_unique_mem.2 ⟨⟨a, rfl⟩, by rintro _ ⟨b, rfl⟩; exact h b⟩
  exact ⟨hrange, hrange ▸ hf.isClosed_range⟩

namespace RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})

open Stacks.AlgebraicGeometry.ProjPolyChart (projToSpecCoeff) in
/-- **A closed subscheme of the model presented as a projective line lies in the special fibre.**
The composite `E ⟶ X ⟶ Spec(R)` factors through `Spec(κ)`, the global functions of `𝐏¹_κ` being
`κ`, so its image is one point; that point is closed, the composite being proper, hence it is
the closed point of `Spec(R)`. -/
theorem range_subschemeι_subset_range_specialFiberι_of_iso_projectiveLineProj
    (D : S.X.IdealSheafData) (κ : Type u) [Field κ] (e : projectiveLineProj κ ≅ D.subscheme) :
    Set.range D.subschemeι.base ⊆ Set.range S.specialFiberι.base := by
  obtain ⟨ψ, hψ⟩ := exists_comp_eq_of_isIso_ΓSpecIso_inv_comp_appTop (projToSpecCoeff κ 1)
    (isIso_ΓSpecIso_inv_comp_appTop_projToSpecCoeff κ) (e.hom ≫ D.subschemeι ≫ S.X_to_R)
  set q := D.subschemeι ≫ S.X_to_R
  have hq : q = e.inv ≫ projToSpecCoeff κ 1 ≫ Spec.map ψ := by
    rw [← hψ, Iso.inv_hom_id_assoc]
  have hconst : ∀ a b : D.subscheme, q.base a = q.base b := by
    intro a b
    rw [hq]
    simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply]
    exact congrArg _ (Subsingleton.elim _ _)
  have : IsIntegral (projectiveLineProj κ) :=
    Stacks.AlgebraicGeometry.ProjPolyChart.isIntegral_proj κ 1
  obtain ⟨x₀⟩ : Nonempty (projectiveLineProj κ) := inferInstance
  have hpcl := (range_eq_singleton_and_isClosed_singleton_of_isClosedMap q.isClosedMap
    (e.hom.base x₀) fun b => hconst b _).2
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k))) :=
    IsClosedImmersion.spec_of_surjective _ S.surjective_algebraMap_residueField
  obtain ⟨pt⟩ : Nonempty (Spec (.of S.k)) := inferInstance
  obtain ⟨hrange₀, hq₀cl⟩ := range_eq_singleton_and_isClosed_singleton_of_isClosedMap
    (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k))).isClosedEmbedding.isClosedMap pt
    fun z => congrArg _ (Subsingleton.elim z pt)
  rintro _ ⟨a, rfl⟩
  change D.subschemeι.base a ∈ Set.range (pullback.fst S.X_to_R _).base
  rw [Scheme.Pullback.range_fst S.X_to_R (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k))),
    Set.mem_preimage, hrange₀]
  exact (hconst a _).trans (eq_of_isClosed_singleton_of_isLocalRing hpcl hq₀cl)

/-- **A component of the special fibre containing a closed subscheme presented as a projective
line is contained in it.** Suppose the support of `D` is the closure of a point `η` of the
component `C_Z`, and is contained in the support of `C_Z`. The preimage of the support of `D` in
the irreducible curve `C_Z` is closed and irreducible; were it proper, it would be at most a point,
whereas the projective line has more than one point. -/
private theorem coe_support_specialFiberComponentIdeal_subset_of_iso_projectiveLineProj
    (D : S.X.IdealSheafData) (κ : Type u) [Field κ] (e : projectiveLineProj κ ≅ D.subscheme)
    (Z : irreducibleComponents S.specialFiber) {η : S.X}
    (hDsupp : ((D.support : Closeds S.X) : Set S.X) = closure {η})
    (hηZ : η ∈ S.specialFiberι.base '' (Z.1 : Set _))
    (hle : ((D.support : Closeds S.X) : Set S.X) ⊆ (S.specialFiberComponentIdeal Z).support) :
    (((S.specialFiberComponentIdeal Z).support : Closeds S.X) : Set S.X) ⊆ D.support := by
  set CZ := S.specialFiberComponentIdeal Z
  set T : Set CZ.subscheme := CZ.subschemeι.base ⁻¹' (D.support : Set S.X)
  have hTcl : IsClosed T := D.support.isClosed.preimage CZ.subschemeι.base.hom.continuous
  obtain ⟨z₀, hz₀⟩ : η ∈ Set.range CZ.subschemeι.base := by
    rwa [CZ.range_subschemeι, S.coe_support_specialFiberComponentIdeal Z]
  have hT : T = closure {z₀} := by
    rw [CZ.subschemeι.isClosedEmbedding.isEmbedding.closure_eq_preimage_closure_image,
      Set.image_singleton, hz₀, ← hDsupp]
  have hTirr : IsIrreducible T := hT ▸ isIrreducible_singleton.closure
  have : IsIntegral CZ.subscheme :=
    S.toRegularModelSituation.isIntegral_specialFiberComponentIdeal Z
  have : IrreducibleSpace CZ.subscheme := irreducibleSpace_of_isIntegral _
  by_cases hTu : T = Set.univ
  · rw [← CZ.range_subschemeι]
    rintro _ ⟨z, rfl⟩
    exact (hTu ▸ Set.mem_univ z : z ∈ T)
  · exfalso
    have hss := Stacks.Topology.Dimension.subsingleton_of_isIrreducible_of_ne_univ
      (S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent Z) hTcl hTirr hTu
    refine AlgebraicGeometry.ExceptionalCurveContraction.not_subsingleton_projectiveLineProj
      (e := e) ⟨fun a b => e.hom.homeomorph.injective ?_⟩
    apply D.subschemeι.isClosedEmbedding.injective
    have hmem : ∀ c : projectiveLineProj κ,
        ∃ z ∈ T, CZ.subschemeι.base z = D.subschemeι.base (e.hom.base c) := fun c => by
      have hc : D.subschemeι.base (e.hom.base c) ∈ (D.support : Set S.X) :=
        D.range_subschemeι ▸ ⟨_, rfl⟩
      obtain ⟨z, hz⟩ : D.subschemeι.base (e.hom.base c) ∈ Set.range CZ.subschemeι.base := by
        rw [CZ.range_subschemeι]
        exact hle hc
      exact ⟨z, show CZ.subschemeι.base z ∈ (D.support : Set S.X) from hz ▸ hc, hz⟩
    obtain ⟨za, hzaT, hza⟩ := hmem a
    obtain ⟨zb, hzbT, hzb⟩ := hmem b
    change D.subschemeι.base (e.hom.base a) = D.subschemeι.base (e.hom.base b)
    rw [← hza, ← hzb, hss hzaT hzbT]

/-- **A closed subscheme of the model presented as a projective line over a field is an
irreducible component of the special fibre**, with its reduced induced structure.

It lies in the special fibre
(`range_subschemeι_subset_range_specialFiberι_of_iso_projectiveLineProj`), so its generic point
lies on a component `C_Z` and the subscheme is contained in `C_Z`. In the irreducible curve
`C_Z` a closed irreducible proper subset is a single point, whereas the projective line has more
than one point; so the two supports agree, and a reduced closed subscheme is determined by its
support. -/
theorem exists_eq_specialFiberComponentIdeal_of_iso_projectiveLineProj
    (D : S.X.IdealSheafData) (κ : Type u) [Field κ] (e : projectiveLineProj κ ≅ D.subscheme) :
    ∃ Z : irreducibleComponents S.specialFiber, D = S.specialFiberComponentIdeal Z := by
  have := isIntegral_subscheme_of_iso_projectiveLineProj D κ e
  set η := D.subschemeι.base (genericPoint D.subscheme) with hη
  obtain ⟨y, hy⟩ :=
    S.range_subschemeι_subset_range_specialFiberι_of_iso_projectiveLineProj D κ e ⟨_, rfl⟩
  let Z : irreducibleComponents S.specialFiber :=
    ⟨irreducibleComponent y, irreducibleComponent_mem_irreducibleComponents y⟩
  refine ⟨Z, ?_⟩
  set CZ := S.specialFiberComponentIdeal Z
  have hCZ : ((CZ.support : Closeds S.X) : Set S.X) = S.specialFiberι.base '' (Z.1 : Set _) :=
    S.coe_support_specialFiberComponentIdeal Z
  have hDsupp : ((D.support : Closeds S.X) : Set S.X) = closure {η} := by
    rw [← D.range_subschemeι, hη, ← Set.image_singleton,
      D.subschemeι.isClosedEmbedding.closure_image_eq, genericPoint_closure, Set.image_univ]
  have hηZ : η ∈ S.specialFiberι.base '' (Z.1 : Set _) := ⟨y, mem_irreducibleComponent, hy⟩
  have hle : ((D.support : Closeds S.X) : Set S.X) ⊆ CZ.support := by
    rw [hDsupp, hCZ]
    exact closure_minimal (Set.singleton_subset_iff.2 hηZ)
      (S.isClosed_image_specialFiberComponent Z)
  have hsupp : D.support = Closeds.closure (S.specialFiberι.base '' (Z.1 : Set _)) := by
    apply SetLike.coe_injective
    rw [Closeds.coe_closure, (S.isClosed_image_specialFiberComponent Z).closure_eq, ← hCZ]
    exact hle.antisymm
      (S.coe_support_specialFiberComponentIdeal_subset_of_iso_projectiveLineProj D κ e Z
        hDsupp hηZ hle)
  exact Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme D _ hsupp

section DecidableComponents

variable [DecidableEq (irreducibleComponents S.specialFiber)]

/-- **An exceptional component of the first kind is a minus-one index of the numerical type
associated to `X`**: if the component `C_Z` is an exceptional curve of the first kind, presented
as `𝐏¹_κ`, then `g_Z = 0` and `(C_Z · C_Z) = -[κ_Z : k]`. The genus vanishes because
`H¹(𝐏¹_κ, 𝒪) = 0`, over `κ_Z` and over `k` alike, and the self-intersection of an exceptional
component is `-[κ_Z : k] + g_{C_Z/k}`. -/
theorem isMinusOneIndex_associatedNumericalType_of_isExceptionalCurveOfFirstKind
    (n : ℕ) (e : Fin n ≃ irreducibleComponents S.specialFiber)
    (Z : irreducibleComponents S.specialFiber) (κ : Type u) [Field κ]
    {ε : projectiveLineProj κ ≅ (S.specialFiberComponentIdeal Z).subscheme}
    (hE : (S.specialFiberComponentIdeal Z).IsExceptionalCurveOfFirstKind κ ε) :
    (S.associatedNumericalType n e).IsMinusOneIndex (e.symm Z) := by
  refine ⟨?_, ?_⟩
  · rw [associatedNumericalType_componentGenus, e.apply_symm_apply]
    let := (S.isField_and_finite_globalSections_specialFiberComponent Z).1.toField
    exact_mod_cast (Stacks.Curves.genus_eq_zero_of_iso_projectiveLine ε.symm _ :
      S.specialFiberComponentGenus Z = 0)
  · rw [associatedNumericalType_intersection, associatedNumericalType_weight, e.apply_symm_apply,
      S.specialFiberIntersectionMatrix_self_eq_neg_weight_add_genus Z κ hE,
      Stacks.Curves.genus_eq_zero_of_iso_projectiveLine ε.symm]
    simp

/-- **[Stacks, Tag 0CA6], (2) ⇒ (1).** In the situation of [Stacks, Tag 0C61], if the numerical
type associated to `X` is minimal, then `X` is a minimal model: an exceptional curve of the first
kind on `X` would be a component of the special fibre and a minus-one index of that numerical
type. -/
theorem isMinimalModel_of_isMinimal_associatedNumericalType
    (n : ℕ) (e : Fin n ≃ irreducibleComponents S.specialFiber)
    (h : (S.associatedNumericalType n e).IsMinimal) :
    IsMinimalModel S.C_to_K S.X_to_R S.genericFiberIso := by
  refine S.isMinimalModel fun ⟨κ, hκ, D, ε, hE⟩ => ?_
  let := hκ
  obtain ⟨Z, rfl⟩ := S.exists_eq_specialFiberComponentIdeal_of_iso_projectiveLineProj D κ ε
  exact h ⟨e.symm Z,
    S.isMinusOneIndex_associatedNumericalType_of_isExceptionalCurveOfFirstKind n e Z κ hE⟩

attribute [local instance] Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff

omit [DecidableEq (irreducibleComponents S.specialFiber)] in
/-- The restriction of `𝒪_X(C_Z)` to the component `C_Z` is invertible. -/
private theorem isInvertible_pullback_invertibleSheaf'_specialFiberComponentIdeal
    (Z : irreducibleComponents S.specialFiber) :
    Stacks.SheafOfModules.IsInvertible (S.specialFiberComponentIdeal Z).subscheme.presheaf
      (structureSheafRing (S.specialFiberComponentIdeal Z).subscheme.toRingedSpace).property
      ((Scheme.Modules.pullback (S.specialFiberComponentIdeal Z).subschemeι).obj
        (Stacks.Divisors.invertibleSheaf' (S.specialFiberComponentIdeal Z))) :=
  (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).2
    (isInvertible_restrict (S.specialFiberComponentIdeal Z) _
      (Stacks.Divisors.isTensorInvertible_invertibleSheaf (S.specialFiberComponentIdeal Z)))

/-- **The self-intersection of a component presented as a projective line.** If the component
`C_Z` is presented as `𝐏¹_κ`, then `(C_Z · C_Z)` is `[κ_Z : k]` times the degree over `κ` of the
pullback of `𝒪_X(C_Z)|_{C_Z}` to `𝐏¹_κ`: by the tower law the degree over `k` is `[κ_Z : k]` times
the degree over `κ_Z`, and the global functions of `𝐏¹_κ` are `κ`, so the degrees over `κ_Z` and
over `κ` of the pullback agree. -/
private theorem specialFiberIntersectionMatrix_self_eq_weight_mul_invertibleCurveDegree
    (Z : irreducibleComponents S.specialFiber) (κ : Type u) [Field κ]
    (e : projectiveLineProj κ ≅ (S.specialFiberComponentIdeal Z).subscheme)
    [AlgebraicGeometry.SheafOfModules.IsInvertible (projectiveLineProj κ).presheaf
      (projectiveLineProj κ).ringCatSheaf.2 ((Scheme.Modules.pullback e.hom).obj
        ((Scheme.Modules.pullback (S.specialFiberComponentIdeal Z).subschemeι).obj
          (Stacks.Divisors.invertibleSheaf' (S.specialFiberComponentIdeal Z))))] :
    S.specialFiberIntersectionMatrix Z Z = (S.specialFiberComponentWeight Z : ℤ) *
      invertibleCurveDegree κ (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff κ 1)
        (topologicalKrullDim_projectiveLineProj κ).le ((Scheme.Modules.pullback e.hom).obj
          ((Scheme.Modules.pullback (S.specialFiberComponentIdeal Z).subschemeι).obj
            (Stacks.Divisors.invertibleSheaf' (S.specialFiberComponentIdeal Z)))) := by
  set g := S.specialFiberComponentToSpec Z
  have hdimC := S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent Z
  have hdimP := (topologicalKrullDim_projectiveLineProj κ).le
  set M := (Scheme.Modules.pullback (S.specialFiberComponentIdeal Z).subschemeι).obj
    (Stacks.Divisors.invertibleSheaf' (S.specialFiberComponentIdeal Z))
  have hM : AlgebraicGeometry.SheafOfModules.IsInvertible
      (S.specialFiberComponentIdeal Z).subscheme.presheaf
      (S.specialFiberComponentIdeal Z).subscheme.ringCatSheaf.2 M :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).1
      (S.isInvertible_pullback_invertibleSheaf'_specialFiberComponentIdeal Z)
  set P := (Scheme.Modules.pullback e.hom).obj M
  obtain ⟨hκC, -⟩ := S.isField_and_finite_globalSections_specialFiberComponent Z
  let : Field Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) := hκC.toField
  have hκP : IsField Γ(projectiveLineProj κ, ⊤) :=
    AlgebraicGeometry.ExceptionalCurveContraction.isField_sections_projectiveLineProj (e := e)
  let : Field Γ(projectiveLineProj κ, ⊤) := hκP.toField
  have : IsProper (S.specialFiberComponentIdeal Z).subscheme.toSpecΓ :=
    Stacks.AlgebraicGeometry.ProperGeomConnected.isProper_toSpecΓ g
  have : IsProper (projectiveLineProj κ).toSpecΓ :=
    Stacks.AlgebraicGeometry.ProperGeomConnected.isProper_toSpecΓ
      (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff κ 1)
  have h1 : S.specialFiberIntersectionMatrix Z Z = invertibleCurveDegree S.k g hdimC M :=
    S.specialFiberIntersectionMatrix_eq_componentDegree Z Z
  have h2 : invertibleCurveDegree S.k g hdimC M = (S.specialFiberComponentWeight Z : ℤ) *
      invertibleCurveDegree Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤)
        (S.specialFiberComponentIdeal Z).subscheme.toSpecΓ hdimC M :=
    invertibleCurveDegree_eq_finrank_globalSections_mul_toSpecΓ S.k g hdimC hκC M
  have h3 := invertibleCurveDegree_pullback_of_isIso
    Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) e.hom
    (S.specialFiberComponentIdeal Z).subscheme.toSpecΓ hdimC hdimP M
  have := isIso_ΓSpecIso_inv_comp_appTop_hom_comp_toSpecΓ e
  have h4 := invertibleCurveDegree_eq_toSpecΓ_of_isIso
    Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤)
    (e.hom ≫ (S.specialFiberComponentIdeal Z).subscheme.toSpecΓ) hdimP hκP P
  have := isIso_ΓSpecIso_inv_comp_appTop_projToSpecCoeff κ
  have h5 := invertibleCurveDegree_eq_toSpecΓ_of_isIso κ
    (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff κ 1) hdimP hκP P
  rw [h1, h2, ← h3, h4, ← h5]

open Stacks.AlgebraicGeometry.ProjPolyChart (projToSpecCoeff) in
/-- **A component with `(C_Z · C_Z) = -[κ_Z : k]` which is a projective line is an exceptional
curve of the first kind.** Let the component `C_Z` of the special fibre be presented as `𝐏¹_κ`
for some field `κ`. It is an effective Cartier divisor on `X` ([Stacks, Tag 0C5Z]), and its normal
sheaf `𝒪_X(C_Z)|_{C_Z}` ([Stacks, Tag 0B3P]) pulls back to some twist `𝒪(d)` on `𝐏¹_κ`
([Stacks, Tag 0BXJ]). The degree of `𝒪_X(C_Z)|_{C_Z}` over `k` is `(C_Z · C_Z) = -[κ_Z : k]`,
hence its degree over the field `κ_Z` of global functions is `-1`; the global functions of `𝐏¹_κ`
are `κ`, so this is also the degree over `κ` of the pullback, which is `d`. So `d = -1`. -/
theorem isExceptionalCurveOfFirstKind_specialFiberComponentIdeal_of_iso
    (Z : irreducibleComponents S.specialFiber)
    (hN : S.specialFiberIntersectionMatrix Z Z = -(S.specialFiberComponentWeight Z : ℤ))
    (κ : Type u) [Field κ]
    (e : projectiveLineProj κ ≅ (S.specialFiberComponentIdeal Z).subscheme) :
    (S.specialFiberComponentIdeal Z).IsExceptionalCurveOfFirstKind κ e := by
  refine ⟨S.isEffectiveCartierDivisor_specialFiberComponent Z, ?_⟩
  obtain ⟨d, ⟨φ⟩⟩ :=
    AlgebraicGeometry.ExceptionalCurveContraction.exists_iso_twistingSheaf_pullback (e := e)
      (Stacks.Divisors.invertibleSheaf' (S.specialFiberComponentIdeal Z))
  suffices hd : d = -1 by
    subst hd
    exact ⟨(RingedSpaceModuleAdjunction.modulePullback e.hom.toLRSHom.toShHom).mapIso
      (Stacks.Divisors.normalSheafIsoInvertibleSheaf (S.specialFiberComponentIdeal Z)) ≪≫ φ⟩
  have hdimP := (topologicalKrullDim_projectiveLineProj κ).le
  have := S.isInvertible_pullback_invertibleSheaf'_specialFiberComponentIdeal Z
  have hP : AlgebraicGeometry.SheafOfModules.IsInvertible (projectiveLineProj κ).presheaf
      (projectiveLineProj κ).ringCatSheaf.2 ((Scheme.Modules.pullback e.hom).obj
        ((Scheme.Modules.pullback (S.specialFiberComponentIdeal Z).subschemeι).obj
          (Stacks.Divisors.invertibleSheaf' (S.specialFiberComponentIdeal Z)))) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).1
      (Stacks.Modules.isInvertible_pullback e.hom _)
  have h6 := (@invertibleCurveDegree_eq_of_iso κ _ _ (projToSpecCoeff κ 1) _ hdimP _ _ hP
    (Stacks.PicardUFD.isInvertible_twistingSheaf κ 1 d) φ).trans
    (invertibleCurveDegree_twistingSheaf_projectiveLineProj κ d)
  have hw := S.specialFiberComponentWeight_pos Z
  rw [S.specialFiberIntersectionMatrix_self_eq_weight_mul_invertibleCurveDegree Z κ e, h6] at hN
  have hmul : (S.specialFiberComponentWeight Z : ℤ) * (d + 1) = 0 := by
    linear_combination hN
  rcases mul_eq_zero.1 hmul with h | h <;> omega

end DecidableComponents

end RegularProperModelSituation

end Stacks.Models

end
