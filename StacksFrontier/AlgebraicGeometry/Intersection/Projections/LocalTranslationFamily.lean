module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceOfModuleFamily
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.LocalTranslationChart
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyConstantScheme
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyIrreducibleFamily
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.SingularGoodEndomorphism

/-!
# The scheme-theoretic fibre of a family of translates at an invertible point

Let `W` and `V` be finite-dimensional vector spaces over an algebraically closed field `k` and let
`Λ : Wᵛ → End(V)` be a linear map: a family of endomorphisms of `V` parametrised by the closed
points `[μ]` of `𝐏(W)`, the endomorphism over `[μ]` being `Λ(μ)` up to a scalar. Let `C ⊆ 𝐏(V)`
be a closed subvariety and let `M ⊆ 𝐏(W) × 𝐏(V)` be a closed subset whose fibre over every closed
point `[μ]` with `Λ(μ)` invertible is the translate `r_{Λ(μ)}(C)`. If `Λ(μ₀)` is a nonzero scalar
multiple of the identity, then **the scheme-theoretic fibre of `M` (with its reduced structure)
over `[μ₀]` is `C` with its reduced structure**:

`(vanishingIdeal M).comap σ_{[μ₀]} = vanishingIdeal C`.

This is clause (2) of Tag 0B1T, `C'_0 = C` scheme theoretically, for the family of translates of
`C` along a line through `[id_V]`.

## The argument

Near `[μ₀]` the family is an *isomorphism*: on the affine chart `D₊(w₀) = Spec Sym_k(W)_(w₀)`
around `[μ₀]`, shrunk to the locus `Spec R` where the determinant of the family is invertible,
the endomorphisms `Λ(μ)` assemble into an invertible `R`-linear endomorphism `G` of `R ⊗_k V`,
which acts on `𝐏_R(R ⊗_k V) = Spec R ×_k 𝐏(V)` by an automorphism `Φ` over `Spec R`
(`AlgebraicGeometry.ProjectiveSpaceOfModule.map`). Its fibre over the `k`-point of `Spec R` lying
over `[μ]` is the automorphism of `𝐏(V)` given by `Λ(μ)`
(`AlgebraicGeometry.ProjectiveSpaceOfModule.pointSection_comp_map`), so on closed points, and
hence — `𝐏_R(R ⊗_k V)` being a Jacobson scheme — everywhere, the part of `M` over `Spec R` is the
image under `Φ` of the constant family `Spec R × C`. Pulling ideal sheaves back along open
immersions and isomorphisms preserves vanishing ideals, and the reduced structure on the constant
family is the pullback of the reduced structure on `C`
(`AlgebraicGeometry.ProjectiveSpaceOfModule.comap_vanishingIdeal_lineProductPoint`); the fibre of
`Φ` over the point of `[μ₀]` is the identity, `Λ(μ₀)` being scalar. The ideal sheaf of the fibre
of `M` is therefore the ideal sheaf of the fibre of the constant family, which is that of `C`.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.comap_vanishingIdeal_of_isOpenImmersion`: pulling a
  vanishing ideal back along an open immersion gives the vanishing ideal of the preimage.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.comap_vanishingIdeal_lineProductSection_of_translate`:
  **the scheme-theoretic fibre of a family of translates at an invertible scalar point.**

## References

* [Stacks Project, Tag 0B1T](https://stacks.math.columbia.edu/tag/0B1T)
* [Stacks Project, Tag 0B2W](https://stacks.math.columbia.edu/tag/0B2W)
* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace TensorProduct

universe u

namespace AlgebraicGeometry

/-- **Pulling a vanishing ideal back along an open immersion gives the vanishing ideal of the
preimage.** The pulled-back closed subscheme is an open subscheme of the reduced one, hence
reduced, and its support is the preimage. -/
public theorem Scheme.IdealSheafData.comap_vanishingIdeal_of_isOpenImmersion {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (Z : Closeds Y) :
    (Scheme.IdealSheafData.vanishingIdeal Z).comap f =
      Scheme.IdealSheafData.vanishingIdeal ⟨f.base ⁻¹' Z, Z.isClosed.preimage f.continuous⟩ := by
  have : IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
    inferInstanceAs (IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme)
  have : IsReduced (pullback f (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι) :=
    isReduced_of_isOpenImmersion (pullback.snd f _)
  have : IsReduced ((Scheme.IdealSheafData.vanishingIdeal Z).comap f).subscheme :=
    ObjectProperty.prop_of_iso IsReduced
      ((Scheme.IdealSheafData.vanishingIdeal Z).comapIso f).symm inferInstance
  refine Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ ?_
  refine Closeds.ext ?_
  rw [Scheme.IdealSheafData.support_comap]
  change f.base ⁻¹' ((Scheme.IdealSheafData.vanishingIdeal Z).support : Set Y) = _
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

namespace ProjectiveSpaceOfModule

variable {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]

/-! ### A family of endomorphisms written in coordinates -/

section FamilyEnd

variable {ι : Type*} [Fintype ι] (A : ι → V →ₗ[k] V)

/-- The `S`-linear endomorphism `∑ᵢ rᵢ · (Aᵢ ⊗ S)` of `S ⊗_k V`. -/
public def familyEnd (S : Type u) [CommRing S] [Algebra k S] (r : ι → S) :
    S ⊗[k] V →ₗ[S] S ⊗[k] V :=
  ∑ i, r i • (A i).baseChange S

/-- Specialisation at a `k`-point commutes with finite sums of endomorphisms. -/
public theorem specializeEnd_sum {S : Type u} [CommRing S] [Algebra k S] (lam : S →ₐ[k] k)
    {κ : Type*} (s : Finset κ) (G : κ → S ⊗[k] V →ₗ[S] S ⊗[k] V) :
    specializeEnd lam (∑ i ∈ s, G i) = ∑ i ∈ s, specializeEnd lam (G i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    ext v
    simp [specializeEnd_apply]
  | insert a s has ih => rw [Finset.sum_insert has, Finset.sum_insert has, specializeEnd_add, ih]

/-- The specialisation of the family at a point is the combination of the `Aᵢ` with the values
of the coefficients. -/
public theorem specializeEnd_familyEnd {S : Type u} [CommRing S] [Algebra k S] (lam : S →ₐ[k] k)
    (r : ι → S) : specializeEnd lam (familyEnd A S r) = ∑ i, lam (r i) • A i := by
  rw [familyEnd, specializeEnd_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [specializeEnd_smul, specializeEnd_baseChange]

variable [FiniteDimensional k V]

/-- The determinant of the family is natural in the coefficient ring. -/
public theorem map_det_familyEnd {S S' : Type u} [CommRing S] [Algebra k S] [CommRing S']
    [Algebra k S'] (φ : S →ₐ[k] S') (r : ι → S) :
    φ (LinearMap.det (familyEnd A S r)) = LinearMap.det (familyEnd A S' (fun i => φ (r i))) := by
  classical
  set e := Module.finBasis k V with he
  have hmat : ∀ (T : Type u) [CommRing T] [Algebra k T] (t : ι → T),
      LinearMap.toMatrix (Algebra.TensorProduct.basis T e) (Algebra.TensorProduct.basis T e)
          (familyEnd A T t) =
        ∑ i, t i • (LinearMap.toMatrix e e (A i)).map (algebraMap k T) := by
    intro T _ _ t
    rw [familyEnd, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, LinearMap.toMatrix_baseChange]
  rw [← LinearMap.det_toMatrix (Algebra.TensorProduct.basis S e),
    ← LinearMap.det_toMatrix (Algebra.TensorProduct.basis S' e), hmat, hmat, AlgHom.map_det]
  congr 1
  ext a b
  simp [Matrix.sum_apply, AlgHom.mapMatrix_apply]

omit [FiniteDimensional k V] in
/-- Over the ground field the family is the base change of the combination of the `Aᵢ`. -/
public theorem familyEnd_self (s : ι → k) :
    familyEnd A k s = (∑ i, s i • A i).baseChange k := by
  rw [familyEnd]
  ext v
  simp [LinearMap.baseChange_tmul, TensorProduct.tmul_sum, TensorProduct.tmul_smul]

/-- Over the ground field the determinant of the family is the determinant of the combination of
the `Aᵢ`. -/
public theorem det_familyEnd_self (s : ι → k) :
    LinearMap.det (familyEnd A k s) = LinearMap.det (∑ i, s i • A i) := by
  rw [familyEnd_self, LinearMap.det_baseChange, Algebra.algebraMap_self, RingHom.id_apply]

end FamilyEnd

/-! ### `k`-points of a ring of finite type -/

/-- **A closed point of `Spec T`, for `T` of finite type over an algebraically closed field `k`,
is named by a `k`-algebra map `T → k`.** -/
public theorem exists_algHom_of_isClosed [IsAlgClosed k] (T : Type u) [CommRing T] [Algebra k T]
    [LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k T)))]
    (t : Spec (.of T)) (ht : IsClosed ({t} : Set (Spec (.of T)))) :
    ∃ χ : T →ₐ[k] k, ∀ x, (Spec.map (CommRingCat.ofHom χ.toRingHom)).base x = t := by
  set p := pointOfClosedPoint (Spec.map (CommRingCat.ofHom (algebraMap k T))) t ht with hp
  set χ₀ : CommRingCat.of T ⟶ CommRingCat.of k := Spec.preimage p with hχ₀
  have hcomp : CommRingCat.ofHom (algebraMap k T) ≫ χ₀ = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hχ₀, Spec.map_preimage, Spec.map_id, hp, pointOfClosedPoint_comp]
  have hc : ∀ c : k, χ₀.hom (algebraMap k T c) = c := by
    intro c
    have h := congrArg (fun φ : CommRingCat.of k ⟶ CommRingCat.of k => φ.hom c) hcomp
    simpa using h
  refine ⟨AlgHom.mk χ₀.hom hc, fun x => ?_⟩
  have h : Spec.map (CommRingCat.ofHom (AlgHom.mk χ₀.hom hc).toRingHom) = p := by
    rw [← Spec.map_preimage p]
    rfl
  rw [h, hp, pointOfClosedPoint_apply]

/-! ### Translations by invertible maps -/

/-- A unit multiple of an invertible endomorphism is invertible. -/
public theorem isUnit_units_smul (c : kˣ) {f : V →ₗ[k] V} (hf : IsUnit f) :
    IsUnit ((c : k) • f) := by
  rw [Algebra.smul_def]
  exact (c.isUnit.map (algebraMap k (Module.End k V))).mul hf

/-- **The image of a subset under the projective transformation of an invertible map** is its
image under the automorphism of `𝐏(V)` the map induces. -/
public theorem endProjectionImage_units (u : LinearMap.GeneralLinearGroup k V)
    (S : Set (projectiveSpaceOfModule k V)) :
    endProjectionImage k V (u : V →ₗ[k] V) S = (map k V u).base '' S := by
  have htop : endDomain k V (u : V →ₗ[k] V) = ⊤ := mapDomain_eq_top k V u
  rw [endProjectionImage, endProjection_eq_ι_comp_map, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.image_comp, Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι, htop]
  simp

/-- A point lies in the image of `S` under the automorphism of `u` exactly when the automorphism
of `u⁻¹` carries it into `S`. -/
public theorem mem_image_map_iff (u : LinearMap.GeneralLinearGroup k V)
    (S : Set (projectiveSpaceOfModule k V)) (y : projectiveSpaceOfModule k V) :
    y ∈ (map k V u).base '' S ↔ (map k V u⁻¹).base y ∈ S := by
  have h1 : ∀ z, (map k V u⁻¹).base ((map k V u).base z) = z := fun z => by
    rw [← Scheme.Hom.comp_apply, map_comp_map_inv]
    rfl
  have h2 : ∀ z, (map k V u).base ((map k V u⁻¹).base z) = z := fun z => by
    rw [← Scheme.Hom.comp_apply, map_inv_comp_map]
    rfl
  exact ⟨by rintro ⟨z, hz, rfl⟩; rwa [h1], fun hy => ⟨_, hy, h2 y⟩⟩

/-! ### The family of translations over the chart at `w₀`

Fix a linear map `Λ : Wᵛ → End(V)` and a vector `w₀ ∈ W`. Writing `bᵢ` for the chosen basis of
`W` and `tᵢ = bᵢ / w₀` for the affine coordinates on the chart at `w₀`, the endomorphism
`∑ᵢ tᵢ · Λ(bᵢ*)` of `R₀ ⊗_k V`, `R₀ = Sym_k(W)_(w₀)`, specialises at the point `[μ]` to
`μ(w₀)⁻¹ · Λ(μ)`. Inverting its determinant `δ` gives the ring `R = R₀[δ⁻¹]` over which it is
invertible. -/

section Translation

variable [FiniteDimensional k V] {W : Type u} [AddCommGroup W] [Module k W]
  [FiniteDimensional k W] (Λ : Module.Dual k W →ₗ[k] (V →ₗ[k] V)) (w₀ : W)

/-- The endomorphisms `Λ(bᵢ*)` attached to the dual of the chosen basis of `W`. -/
public def transCoeffEnd (i : Fin (Module.finrank k W)) : V →ₗ[k] V :=
  Λ ((Module.finBasis k W).coord i)

/-- The affine coordinates `bᵢ / w₀`. -/
public def transCoord (i : Fin (Module.finrank k W)) : chartRing k W w₀ :=
  chartCoord k W w₀ (Module.finBasis k W i)

/-- The determinant `δ` of the family over the chart at `w₀`. -/
public def transDet : chartRing k W w₀ :=
  LinearMap.det (familyEnd (transCoeffEnd Λ) (chartRing k W w₀) (transCoord w₀))

/-- **The ring `R = Sym_k(W)_(w₀)[δ⁻¹]`** over which the family is invertible. -/
public abbrev transRing : Type u := Localization.Away (transDet Λ w₀)

/-- **The family of translations over `Spec R`**, an `R`-linear endomorphism of `R ⊗_k V`. -/
public def transEnd : transRing Λ w₀ ⊗[k] V →ₗ[transRing Λ w₀] transRing Λ w₀ ⊗[k] V :=
  familyEnd (transCoeffEnd Λ) (transRing Λ w₀)
    (fun i => algebraMap (chartRing k W w₀) (transRing Λ w₀) (transCoord w₀ i))

/-- The determinant of the family of translations over `Spec R` is the image of `δ`. -/
public theorem det_transEnd :
    LinearMap.det (transEnd Λ w₀) =
      algebraMap (chartRing k W w₀) (transRing Λ w₀) (transDet Λ w₀) :=
  (map_det_familyEnd (transCoeffEnd Λ)
    (IsScalarTower.toAlgHom k (chartRing k W w₀) (transRing Λ w₀)) (transCoord w₀)).symm

/-- The family of translations is invertible over `R`, its determinant `δ` having been inverted. -/
public theorem isUnit_transEnd : IsUnit (transEnd Λ w₀) := by
  rw [LinearMap.isUnit_iff_isUnit_det, det_transEnd]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- The family of translations, as an invertible map. -/
public def transGL : LinearMap.GeneralLinearGroup (transRing Λ w₀) (transRing Λ w₀ ⊗[k] V) :=
  (isUnit_transEnd Λ w₀).unit

/-- The underlying endomorphism of `transGL` is the family of translations. -/
@[simp]
public theorem coe_transGL :
    ((transGL Λ w₀ : LinearMap.GeneralLinearGroup _ _) : _ →ₗ[transRing Λ w₀] _) =
      transEnd Λ w₀ := rfl

/-- **The chart `Spec R ⟶ 𝐏(W)`**, the standard chart at `w₀` restricted to the locus where the
family is invertible. -/
public def transChart : Spec (.of (transRing Λ w₀)) ⟶ projectiveSpaceOfModule k W :=
  Spec.map (CommRingCat.ofHom (algebraMap (chartRing k W w₀) (transRing Λ w₀))) ≫ chartι k W w₀

/-- The chart `Spec R ⟶ 𝐏(W)` is an open immersion. -/
public instance isOpenImmersion_transChart : IsOpenImmersion (transChart Λ w₀) := by
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (chartRing k W w₀) (transRing Λ w₀)))) :=
    IsOpenImmersion.of_isLocalization (transDet Λ w₀)
  unfold transChart
  infer_instance

omit [FiniteDimensional k V] in
/-- The chart `Spec R ⟶ 𝐏(W)` lies over `Spec k`. -/
@[reassoc]
public theorem transChart_comp_toSpec :
    transChart Λ w₀ ≫ projectiveSpaceOfModuleToSpec k W =
      Spec.map (CommRingCat.ofHom (algebraMap k (transRing Λ w₀))) := by
  rw [transChart, Category.assoc, chartι_comp_toSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq]

/-- The ring `R` is of finite type over `k`, its spectrum being an open subscheme of `𝐏(W)`. -/
public instance locallyOfFiniteType_transRing [Nontrivial W] :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k (transRing Λ w₀)))) := by
  rw [← transChart_comp_toSpec]
  have := isProper_projectiveSpaceOfModuleToSpec k W
  infer_instance

/-- A point of the chart over `[μ]` has affine coordinates `μ(bᵢ) / μ(w₀)`. -/
private theorem apply_transCoord {W : Type u} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (w₀ : W) (χ₀ : chartRing k W w₀ →ₐ[k] k) {μ : Module.Dual k W} (hμ : μ ≠ 0) (hw₀ : μ w₀ ≠ 0)
    (x : Spec (.of k))
    (hx₀ : (chartι k W w₀).base ((Spec.map (CommRingCat.ofHom χ₀.toRingHom)).base x) =
      linearFunctionalPoint k W μ hμ) (i : Fin (Module.finrank k W)) :
    χ₀ (transCoord w₀ i) = (μ w₀)⁻¹ * μ (Module.finBasis k W i) := by
  rw [eq_inv_mul_iff_mul_eq₀ hw₀, mul_comm]
  exact apply_chartCoord_mul χ₀ hμ x hx₀ (Module.finBasis k W i)

/-- Coefficients `a * μ(bᵢ)` recombine the values `Λ(bᵢ*)` into `a • Λ(μ)`. -/
private theorem sum_smul_apply_coord {W : Type u} [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] {U : Type*} [AddCommGroup U] [Module k U] (L : Module.Dual k W →ₗ[k] U)
    (μ : Module.Dual k W) (a : k) (c : Fin (Module.finrank k W) → k)
    (hc : ∀ i, c i = a * μ (Module.finBasis k W i)) :
    ∑ i, c i • L ((Module.finBasis k W).coord i) = a • L μ := by
  simp_rw [hc, mul_smul, ← Finset.smul_sum]
  congr 1
  simp_rw [← map_smul, ← map_sum, Module.Basis.sum_dual_apply_smul_coord]

omit [FiniteDimensional k V] in
/-- **The specialisation of the family at a point lying over `[μ]`** is `μ(w₀)⁻¹ · Λ(μ)`, and
`μ(w₀) ≠ 0`. -/
public theorem specializeEnd_transEnd (χ : transRing Λ w₀ →ₐ[k] k) {μ : Module.Dual k W}
    (hμ : μ ≠ 0) (x : Spec (.of k))
    (hx : (transChart Λ w₀).base ((Spec.map (CommRingCat.ofHom χ.toRingHom)).base x) =
      linearFunctionalPoint k W μ hμ) :
    μ w₀ ≠ 0 ∧ specializeEnd χ (transEnd Λ w₀) = (μ w₀)⁻¹ • Λ μ := by
  set χ₀ : chartRing k W w₀ →ₐ[k] k :=
    χ.comp (IsScalarTower.toAlgHom k (chartRing k W w₀) (transRing Λ w₀)) with hχ₀
  have hx₀ : (chartι k W w₀).base ((Spec.map (CommRingCat.ofHom χ₀.toRingHom)).base x) =
      linearFunctionalPoint k W μ hμ := by
    rw [← hx, transChart, hχ₀]
    rfl
  have hw₀ : μ w₀ ≠ 0 := by
    intro h0
    have hmem : linearFunctionalPoint k W μ hμ ∈ Set.range (chartι k W w₀).base :=
      ⟨_, hx₀⟩
    rw [range_chartι] at hmem
    exact hmem ((linearFunctionalPoint_ι_mem k W μ hμ w₀).mpr h0)
  refine ⟨hw₀, ?_⟩
  rw [transEnd, specializeEnd_familyEnd]
  exact sum_smul_apply_coord Λ _ _ _ fun i => apply_transCoord w₀ χ₀ hμ hw₀ x hx₀ i

/-- **The point of `Spec R` over `[μ]`**, for `μ(w₀) ≠ 0` and `Λ(μ)` invertible. -/
public theorem exists_transPoint [IsAlgClosed k] [Nontrivial W] {μ : Module.Dual k W}
    (hμ : μ ≠ 0) (hw₀ : μ w₀ ≠ 0) (hΛ : IsUnit (Λ μ)) :
    ∃ χ : transRing Λ w₀ →ₐ[k] k, ∀ x : Spec (.of k),
      (transChart Λ w₀).base ((Spec.map (CommRingCat.ofHom χ.toRingHom)).base x) =
        linearFunctionalPoint k W μ hμ := by
  -- the point of the chart over `[μ]`
  have hmem : linearFunctionalPoint k W μ hμ ∈ Set.range (chartι k W w₀).base := by
    rw [range_chartι]
    exact fun h => hw₀ ((linearFunctionalPoint_ι_mem k W μ hμ w₀).mp h)
  obtain ⟨q, hq⟩ := hmem
  have hqc : IsClosed ({q} : Set (Spec (.of (chartRing k W w₀)))) := by
    have hpre : (chartι k W w₀).base ⁻¹' {linearFunctionalPoint k W μ hμ} = {q} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun hz => (chartι k W w₀).isOpenEmbedding.injective (hz.trans hq.symm),
        by rintro rfl; exact hq⟩
    rw [← hpre]
    exact (linearFunctionalPoint_isClosed k W μ hμ).preimage (chartι k W w₀).continuous
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k (chartRing k W w₀)))) := by
    rw [← chartι_comp_toSpec]
    have := isProper_projectiveSpaceOfModuleToSpec k W
    infer_instance
  obtain ⟨χ₀, hχ₀⟩ := exists_algHom_of_isClosed (k := k) (chartRing k W w₀) q hqc
  have hx₀ : ∀ x, (chartι k W w₀).base ((Spec.map (CommRingCat.ofHom χ₀.toRingHom)).base x) =
      linearFunctionalPoint k W μ hμ := fun x => by rw [hχ₀ x, hq]
  -- `χ₀` does not kill the determinant
  have hdet : IsUnit (χ₀ (transDet Λ w₀)) := by
    rw [transDet, map_det_familyEnd (transCoeffEnd Λ) χ₀, det_familyEnd_self]
    obtain ⟨x⟩ : Nonempty (Spec (.of k)) := ⟨IsLocalRing.closedPoint k⟩
    have hsum : ∑ i, χ₀ (transCoord w₀ i) • transCoeffEnd Λ i = (μ w₀)⁻¹ • Λ μ :=
      sum_smul_apply_coord Λ _ _ _ (apply_transCoord w₀ χ₀ hμ hw₀ x (hx₀ x))
    rw [hsum, LinearMap.det_smul]
    refine (IsUnit.mul ((isUnit_iff_ne_zero.mpr (inv_ne_zero hw₀)).pow _) ?_)
    exact (LinearMap.isUnit_iff_isUnit_det (Λ μ)).mp hΛ
  -- the extension to `R`
  set χ : transRing Λ w₀ →+* k := Localization.awayLift χ₀.toRingHom (transDet Λ w₀) hdet
    with hχ
  have hχalg : ∀ y, χ (algebraMap (chartRing k W w₀) (transRing Λ w₀) y) = χ₀ y := fun y =>
    IsLocalization.lift_eq _ y
  have hcomm : ∀ c : k, χ (algebraMap k (transRing Λ w₀) c) = algebraMap k k c := fun c => by
    rw [IsScalarTower.algebraMap_apply k (chartRing k W w₀) (transRing Λ w₀), hχalg]
    exact χ₀.commutes c
  refine ⟨AlgHom.mk χ hcomm, fun x => ?_⟩
  have hcomp : Spec.map (CommRingCat.ofHom (AlgHom.mk χ hcomm : transRing Λ w₀ →ₐ[k] k).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (chartRing k W w₀) (transRing Λ w₀))) =
      Spec.map (CommRingCat.ofHom χ₀.toRingHom) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hχalg
  rw [transChart, ← Scheme.Hom.comp_apply, ← Category.assoc, hcomp]
  exact hx₀ x

/-! ### The embedding of `Spec R ×_k 𝐏(V)` into `𝐏(W) ×_k 𝐏(V)` -/

variable [Nontrivial V] [Nontrivial W]

/-- **The open embedding `𝐏_R(R ⊗_k V) = Spec R ×_k 𝐏(V) ⟶ 𝐏(W) ×_k 𝐏(V)`**, the base change of
the chart along the projection to `𝐏(W)`. -/
public def transEmb :
    projectiveSpaceOfModule (transRing Λ w₀) (transRing Λ w₀ ⊗[k] V) ⟶ lineProduct k V W :=
  pullback.lift (projectiveSpaceOfModuleToSpec _ _ ≫ transChart Λ w₀)
    (Stacks.ProjectiveSpaceBaseChange.map k (transRing Λ w₀) V) (by
      rw [Category.assoc, transChart_comp_toSpec]
      exact ((Stacks.ProjectiveSpaceBaseChange.isPullback_projectiveSpaceOfModuleToSpec k
        (transRing Λ w₀) V).w).symm)

omit [FiniteDimensional k V] [Nontrivial V] [Nontrivial W] in
/-- The embedding `transEmb` followed by the projection to `𝐏(W)` is the chart `Spec R ⟶ 𝐏(W)`
after the structure morphism. -/
@[reassoc]
public theorem transEmb_comp_lineProductLine :
    transEmb Λ w₀ ≫ lineProductLine k V W =
      projectiveSpaceOfModuleToSpec _ _ ≫ transChart Λ w₀ :=
  pullback.lift_fst _ _ _

omit [FiniteDimensional k V] [Nontrivial V] [Nontrivial W] in
/-- The embedding `transEmb` followed by the projection to `𝐏(V)` is the base change map
`𝐏_R(R ⊗_k V) ⟶ 𝐏(V)`. -/
@[reassoc]
public theorem transEmb_comp_lineProductPoint :
    transEmb Λ w₀ ≫ lineProductPoint k V W =
      Stacks.ProjectiveSpaceBaseChange.map k (transRing Λ w₀) V :=
  pullback.lift_snd _ _ _

omit [FiniteDimensional k V] [Nontrivial V] [Nontrivial W] in
/-- The embedding `transEmb` is the base change of the chart `Spec R ⟶ 𝐏(W)` along the projection
`𝐏(W) ×_k 𝐏(V) ⟶ 𝐏(W)`. -/
public theorem isPullback_transEmb :
    IsPullback (transEmb Λ w₀) (projectiveSpaceOfModuleToSpec _ _) (lineProductLine k V W)
      (transChart Λ w₀) := by
  refine IsPullback.of_right (h₁₂ := lineProductPoint k V W)
    (v₁₃ := projectiveSpaceOfModuleToSpec k V) (h₂₂ := projectiveSpaceOfModuleToSpec k W)
    ?_ (transEmb_comp_lineProductLine Λ w₀) (IsPullback.of_hasPullback _ _).flip
  rw [transEmb_comp_lineProductPoint, transChart_comp_toSpec]
  exact Stacks.ProjectiveSpaceBaseChange.isPullback_projectiveSpaceOfModuleToSpec k
    (transRing Λ w₀) V

/-- The embedding `transEmb` is an open immersion, as a base change of one. -/
public instance isOpenImmersion_transEmb : IsOpenImmersion (transEmb Λ w₀) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_transEmb Λ w₀).flip
    (isOpenImmersion_transChart Λ w₀)

omit [FiniteDimensional k V] [Nontrivial V] [Nontrivial W] in
/-- The structure morphism of `𝐏_R(R ⊗_k V)` over `k`, read through the base change to `𝐏(V)`. -/
public theorem transEmb_comp_lineProductToSpec :
    transEmb Λ w₀ ≫ lineProductToSpec k V W =
      Stacks.ProjectiveSpaceBaseChange.map k (transRing Λ w₀) V ≫
        projectiveSpaceOfModuleToSpec k V := by
  rw [← transEmb_comp_lineProductPoint, Category.assoc, lineProductToSpec, pullback.condition]

omit [FiniteDimensional k V] [Nontrivial V] [Nontrivial W] in
/-- The structure morphism of `𝐏_R(R ⊗_k V)` over `k`, read through `Spec R`. -/
public theorem transEmb_comp_lineProductToSpec' :
    transEmb Λ w₀ ≫ lineProductToSpec k V W =
      projectiveSpaceOfModuleToSpec (transRing Λ w₀) (transRing Λ w₀ ⊗[k] V) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (transRing Λ w₀))) := by
  rw [lineProductToSpec, transEmb_comp_lineProductLine_assoc, transChart_comp_toSpec]

omit [FiniteDimensional k V] [Nontrivial V] in
/-- **The section of `𝐏_R(R ⊗_k V)` at a point of `Spec R` is the section of `𝐏(W) ×_k 𝐏(V)` at
its image point.** -/
public theorem pointSection_comp_transEmb [IsAlgClosed k] (χ : transRing Λ w₀ →ₐ[k] k)
    (lam : projectiveSpaceOfModule k W) (hlam : IsClosed ({lam} : Set _))
    (h : (transChart Λ w₀).base
      ((Spec.map (CommRingCat.ofHom χ.toRingHom)).base (IsLocalRing.closedPoint k)) = lam) :
    pointSection χ ≫ transEmb Λ w₀ = lineProductSection k V W lam hlam := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, transEmb_comp_lineProductLine, pointSection_comp_toSpec_assoc,
      lineProductSection_comp_lineProductLine]
    congr 1
    refine ext_of_apply_closedPoint_eq (projectiveSpaceOfModuleToSpec k W) ?_
      (pointOfClosedPoint_comp _ _ _) ?_
    · rw [Category.assoc, transChart_comp_toSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      convert Spec.map_id (CommRingCat.of k)
      ext c
      exact χ.commutes c
    · exact (Scheme.Hom.comp_apply _ _ _).trans (h.trans (pointOfClosedPoint_apply _ _ _ _).symm)
  · rw [Category.assoc, transEmb_comp_lineProductPoint, pointSection_comp_baseChangeMap,
      lineProductSection_comp_lineProductPoint]

end Translation

/-! ### The scheme-theoretic fibre -/

section Fibre

variable [IsAlgClosed k] [FiniteDimensional k V] [Nontrivial V] {W : Type u} [AddCommGroup W]
  [Module k W] [FiniteDimensional k W] [Nontrivial W]

variable (Λ : Module.Dual k W →ₗ[k] (V →ₗ[k] V)) (w₀ : W)

/-- **Every closed point of `𝐏_R(R ⊗_k V)` lies on the section over a `k`-point of `Spec R`**,
that `k`-point lying over a closed point `[μ]` of `𝐏(W)`. -/
public theorem exists_eq_pointSection
    (z : projectiveSpaceOfModule (transRing Λ w₀) (transRing Λ w₀ ⊗[k] V))
    (hz : IsClosed ({z} : Set _)) :
    ∃ (χ : transRing Λ w₀ →ₐ[k] k) (μ : Module.Dual k W) (hμ : μ ≠ 0),
      (∀ x, (transChart Λ w₀).base ((Spec.map (CommRingCat.ofHom χ.toRingHom)).base x) =
        linearFunctionalPoint k W μ hμ) ∧
      z = (pointSection (V := V) χ).base
        ((Stacks.ProjectiveSpaceBaseChange.map k (transRing Λ w₀) V).base z) := by
  have : LocallyOfFiniteType (projectiveSpaceOfModuleToSpec k V) := by
    have := isProper_projectiveSpaceOfModuleToSpec k V
    infer_instance
  have : LocallyOfFiniteType (projectiveSpaceOfModuleToSpec k W) := by
    have := isProper_projectiveSpaceOfModuleToSpec k W
    infer_instance
  have htz := isClosed_singleton_image_of_isClosed_singleton
    (projectiveSpaceOfModuleToSpec (transRing Λ w₀) (transRing Λ w₀ ⊗[k] V))
    (transEmb Λ w₀ ≫ lineProductToSpec k V W)
    (Spec.map (CommRingCat.ofHom (algebraMap k (transRing Λ w₀))))
    (transEmb_comp_lineProductToSpec' Λ w₀).symm z hz
  obtain ⟨χ, hχ⟩ := exists_algHom_of_isClosed (k := k) (transRing Λ w₀) _ htz
  have hlam := isClosed_singleton_image_of_isClosed_singleton (transChart Λ w₀)
    (Spec.map (CommRingCat.ofHom (algebraMap k (transRing Λ w₀))))
    (projectiveSpaceOfModuleToSpec k W) (transChart_comp_toSpec Λ w₀) _ htz
  obtain ⟨μ, hμ, hμeq⟩ := exists_eq_linearFunctionalPoint k W _ hlam
  refine ⟨χ, μ, hμ, fun x => by rw [hχ x, hμeq], ?_⟩
  refine (transEmb Λ w₀).isOpenEmbedding.injective ?_
  have hyc := isClosed_singleton_image_of_isClosed_singleton
    (Stacks.ProjectiveSpaceBaseChange.map k (transRing Λ w₀) V)
    (transEmb Λ w₀ ≫ lineProductToSpec k V W) (projectiveSpaceOfModuleToSpec k V)
    (transEmb_comp_lineProductToSpec Λ w₀).symm z hz
  have hσc := isClosed_singleton_image_of_isClosed_singleton (pointSection (V := V) χ)
    (projectiveSpaceOfModuleToSpec k V) (transEmb Λ w₀ ≫ lineProductToSpec k V W) (by
      rw [transEmb_comp_lineProductToSpec, pointSection_comp_baseChangeMap_assoc]) _ hyc
  refine eq_of_isClosed_singleton_of_proj_eq (projectiveSpaceOfModuleToSpec k W)
    (projectiveSpaceOfModuleToSpec k V)
    (isClosed_singleton_image_of_isClosed_singleton (transEmb Λ w₀)
      (transEmb Λ w₀ ≫ lineProductToSpec k V W) (lineProductToSpec k V W) rfl z hz)
    (isClosed_singleton_image_of_isClosed_singleton (transEmb Λ w₀)
      (transEmb Λ w₀ ≫ lineProductToSpec k V W) (lineProductToSpec k V W) rfl _ hσc) ?_ ?_
  · obtain ⟨x0⟩ : Nonempty (Spec (.of k)) := inferInstance
    calc (lineProductLine k V W).base ((transEmb Λ w₀).base z)
        = (transEmb Λ w₀ ≫ lineProductLine k V W).base z := rfl
      _ = (transChart Λ w₀).base ((Spec.map (CommRingCat.ofHom χ.toRingHom)).base x0) := by
          rw [transEmb_comp_lineProductLine, Scheme.Hom.comp_apply, hχ x0]
      _ = (projectiveSpaceOfModuleToSpec k V ≫ Spec.map (CommRingCat.ofHom χ.toRingHom) ≫
            transChart Λ w₀).base
            ((Stacks.ProjectiveSpaceBaseChange.map k (transRing Λ w₀) V).base z) := by
          rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
          congr 2
          exact Subsingleton.elim _ _
      _ = (pointSection χ ≫ transEmb Λ w₀ ≫ lineProductLine k V W).base
            ((Stacks.ProjectiveSpaceBaseChange.map k (transRing Λ w₀) V).base z) := by
          rw [transEmb_comp_lineProductLine, pointSection_comp_toSpec_assoc]
      _ = _ := rfl
  · calc (lineProductPoint k V W).base ((transEmb Λ w₀).base z)
        = (transEmb Λ w₀ ≫ lineProductPoint k V W).base z := rfl
      _ = (pointSection χ ≫ transEmb Λ w₀ ≫ lineProductPoint k V W).base
            ((Stacks.ProjectiveSpaceBaseChange.map k (transRing Λ w₀) V).base z) := by
          rw [transEmb_comp_lineProductPoint, pointSection_comp_baseChangeMap]
          rfl
      _ = _ := rfl

omit [Nontrivial V] in
/-- **Membership in the two sets, at a point of a section.** -/
public theorem pointSection_mem_iff
    (C : Set (projectiveSpaceOfModule k V)) (M : Set (lineProduct k V W))
    (hfib : ∀ (μ : Module.Dual k W) (hμ : μ ≠ 0), IsUnit (Λ μ) →
      lineProductFibre k V W (linearFunctionalPoint k W μ hμ)
          (linearFunctionalPoint_isClosed k W μ hμ) M =
        endProjectionImage k V (Λ μ) C)
    (χ : transRing Λ w₀ →ₐ[k] k) {μ : Module.Dual k W} (hμ : μ ≠ 0)
    (hχμ : ∀ x, (transChart Λ w₀).base ((Spec.map (CommRingCat.ofHom χ.toRingHom)).base x) =
        linearFunctionalPoint k W μ hμ) (y : projectiveSpaceOfModule k V) :
    (transEmb Λ w₀).base ((pointSection χ).base y) ∈ M ↔
      (Stacks.ProjectiveSpaceBaseChange.map k (transRing Λ w₀) V).base
        ((map (transRing Λ w₀) (transRing Λ w₀ ⊗[k] V) (transGL Λ w₀)⁻¹).base
          ((pointSection χ).base y)) ∈ C := by
  obtain ⟨hw₀, hspec⟩ := specializeEnd_transEnd Λ w₀ χ hμ (IsLocalRing.closedPoint k) (hχμ _)
  have hu' : ((specializeGL χ (transGL Λ w₀) : LinearMap.GeneralLinearGroup k V) :
      V →ₗ[k] V) = (μ w₀)⁻¹ • Λ μ := hspec
  have hΛu : Λ μ = ((Units.mk0 (μ w₀) hw₀ : kˣ) : k) •
      ((specializeGL χ (transGL Λ w₀) : LinearMap.GeneralLinearGroup k V) : V →ₗ[k] V) := by
    rw [hu', Units.val_mk0, smul_smul, mul_inv_cancel₀ hw₀, one_smul]
  have hΛunit : IsUnit (Λ μ) :=
    hΛu ▸ isUnit_units_smul (Units.mk0 (μ w₀) hw₀) (specializeGL χ (transGL Λ w₀)).isUnit
  have hfibμ := hfib μ hμ hΛunit
  rw [hΛu, endProjectionImage_smul, endProjectionImage_units] at hfibμ
  have hσJ := pointSection_comp_transEmb Λ w₀ χ (linearFunctionalPoint k W μ hμ)
    (linearFunctionalPoint_isClosed k W μ hμ) (hχμ _)
  rw [← Scheme.Hom.comp_apply (pointSection χ) (transEmb Λ w₀), hσJ,
    ← Scheme.Hom.comp_apply (pointSection χ), pointSection_comp_map, Scheme.Hom.comp_apply,
    ← Scheme.Hom.comp_apply (pointSection χ), pointSection_comp_baseChangeMap]
  change y ∈ lineProductFibre k V W _ (linearFunctionalPoint_isClosed k W μ hμ) M ↔ _
  rw [hfibμ, mem_image_map_iff, map_inv]
  rfl

/-- **Near an invertible point the family of translates is the translate of the constant
family.** If the fibre of the closed set `M ⊆ 𝐏(W) × 𝐏(V)` over every closed point `[μ]` with
`Λ(μ)` invertible is `r_{Λ(μ)}(C)`, then over the chart `Spec R` at `w₀` the set `M` is the
image of `Spec R × C` under the family of automorphisms `map G`, read through the inverse
family. -/
public theorem transEmb_preimage_eq
    (C : Set (projectiveSpaceOfModule k V)) (hC : IsClosed C)
    (M : Set (lineProduct k V W)) (hM : IsClosed M)
    (hfib : ∀ (μ : Module.Dual k W) (hμ : μ ≠ 0), IsUnit (Λ μ) →
      lineProductFibre k V W (linearFunctionalPoint k W μ hμ)
          (linearFunctionalPoint_isClosed k W μ hμ) M =
        endProjectionImage k V (Λ μ) C) :
    (transEmb Λ w₀).base ⁻¹' M =
      (map (transRing Λ w₀) (transRing Λ w₀ ⊗[k] V) (transGL Λ w₀)⁻¹).base ⁻¹'
        ((Stacks.ProjectiveSpaceBaseChange.map k (transRing Λ w₀) V).base ⁻¹' C) := by
  have : JacobsonSpace (projectiveSpaceOfModule (transRing Λ w₀) (transRing Λ w₀ ⊗[k] V)) :=
    LocallyOfFiniteType.jacobsonSpace (transEmb Λ w₀ ≫ lineProductToSpec k V W)
  have hS1 : IsClosed ((transEmb Λ w₀).base ⁻¹' M) := hM.preimage (transEmb Λ w₀).continuous
  have hS2 := (hC.preimage (Stacks.ProjectiveSpaceBaseChange.map k (transRing Λ w₀) V).continuous
    ).preimage (map (transRing Λ w₀) (transRing Λ w₀ ⊗[k] V) (transGL Λ w₀)⁻¹).continuous
  refine (hS1.closure_eq.symm.trans ?_).trans hS2.closure_eq
  rw [← JacobsonSpace.closure_inter_closedPoints_eq_closure hS1.isLocallyClosed,
    ← JacobsonSpace.closure_inter_closedPoints_eq_closure hS2.isLocallyClosed]
  congr 1
  ext z
  simp only [Set.mem_inter_iff, mem_closedPoints_iff, Set.mem_preimage]
  refine and_congr_left fun hz => ?_
  obtain ⟨χ, μ, hμ, hχμ, hzσ⟩ := exists_eq_pointSection Λ w₀ z hz
  rw [hzσ]
  exact pointSection_mem_iff Λ w₀ C M hfib χ hμ hχμ _

/-- **The scheme-theoretic fibre of a family of translates at a scalar point.** Let
`Λ : Wᵛ → End(V)` be linear, `C ⊆ 𝐏(V)` a closed subvariety and `M ⊆ 𝐏(W) × 𝐏(V)` a closed subset
whose fibre over every closed point `[μ]` with `Λ(μ)` invertible is `r_{Λ(μ)}(C)`. If `Λ(μ₀)` is
a nonzero multiple of the identity, the scheme-theoretic fibre of `M` with its reduced structure
over `[μ₀]` is `C` with its reduced structure. -/
public theorem comap_vanishingIdeal_lineProductSection_of_translate
    (Λ : Module.Dual k W →ₗ[k] (V →ₗ[k] V))
    (C : Set (projectiveSpaceOfModule k V)) (hC : IsClosed C) (hCirr : IsIrreducible C)
    (M : Set (lineProduct k V W)) (hM : IsClosed M)
    (hfib : ∀ (μ : Module.Dual k W) (hμ : μ ≠ 0), IsUnit (Λ μ) →
      lineProductFibre k V W (linearFunctionalPoint k W μ hμ)
          (linearFunctionalPoint_isClosed k W μ hμ) M =
        endProjectionImage k V (Λ μ) C)
    {μ₀ : Module.Dual k W} (hμ₀ : μ₀ ≠ 0) (c : kˣ) (hc : Λ μ₀ = (c : k) • LinearMap.id) :
    (Scheme.IdealSheafData.vanishingIdeal (⟨M, hM⟩ : Closeds (lineProduct k V W))).comap
        (lineProductSection k V W (linearFunctionalPoint k W μ₀ hμ₀)
          (linearFunctionalPoint_isClosed k W μ₀ hμ₀)) =
      Scheme.IdealSheafData.vanishingIdeal (⟨C, hC⟩ : Closeds (projectiveSpaceOfModule k V)) := by
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : W, μ₀ w₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hμ₀ (LinearMap.ext h)
  have hΛ₀ : IsUnit (Λ μ₀) := by
    rw [hc]
    exact isUnit_units_smul c isUnit_one
  obtain ⟨χ₀, hχ₀⟩ := exists_transPoint Λ w₀ hμ₀ hw₀ hΛ₀
  set R := transRing Λ w₀ with hR
  set bR := Stacks.ProjectiveSpaceBaseChange.map k R V with hbR
  set G := transGL Λ w₀ with hG
  have : IsIso (map R (R ⊗[k] V) G⁻¹) :=
    ⟨⟨map R (R ⊗[k] V) G, map_inv_comp_map G, map_comp_map_inv G⟩⟩
  -- the fibre of the inverse family over the point of `[μ₀]` is the identity
  have hspec₀ : map k V (specializeGL χ₀ G⁻¹) = 𝟙 _ := by
    obtain ⟨-, hspec⟩ := specializeEnd_transEnd Λ w₀ χ₀ hμ₀ (IsLocalRing.closedPoint k)
      (hχ₀ _)
    have h1 : map k V (specializeGL χ₀ G) = 𝟙 _ := by
      refine map_eq_id_of_eq_smul_id k V _ ((Units.mk0 (μ₀ w₀) hw₀)⁻¹ * c) ?_
      rw [coe_specializeGL, hG, coe_transGL, hspec, hc, smul_smul, Units.val_mul,
        Units.val_inv_eq_inv_val,
        Units.val_mk0]
    have h2 := map_comp_map_inv (specializeGL χ₀ G)
    rwa [h1, Category.id_comp, ← map_inv] at h2
  have hσJ := pointSection_comp_transEmb Λ w₀ χ₀ (linearFunctionalPoint k W μ₀ hμ₀)
    (linearFunctionalPoint_isClosed k W μ₀ hμ₀) (hχ₀ _)
  have hset := transEmb_preimage_eq Λ w₀ C hC M hM hfib
  -- the constant family pulled back to the chart
  have hconst : (Scheme.IdealSheafData.vanishingIdeal
        (⟨C, hC⟩ : Closeds (projectiveSpaceOfModule k V))).comap bR =
      Scheme.IdealSheafData.vanishingIdeal
        ⟨bR.base ⁻¹' C, hC.preimage bR.continuous⟩ := by
    rw [hbR, ← transEmb_comp_lineProductPoint, Scheme.IdealSheafData.comap_comp,
      comap_vanishingIdeal_lineProductPoint k V W C hC hCirr,
      Scheme.IdealSheafData.comap_vanishingIdeal_of_isOpenImmersion]
    rfl
  rw [← hσJ, Scheme.IdealSheafData.comap_comp,
    Scheme.IdealSheafData.comap_vanishingIdeal_of_isOpenImmersion]
  have hcl : (⟨(transEmb Λ w₀).base ⁻¹'
        ((⟨M, hM⟩ : Closeds (lineProduct k V W)) : Set (lineProduct k V W)),
        hM.preimage (transEmb Λ w₀).continuous⟩ : Closeds _) =
      ⟨(map R (R ⊗[k] V) G⁻¹).base ⁻¹'
          ((⟨bR.base ⁻¹' C, hC.preimage bR.continuous⟩ : Closeds _) : Set _),
        (hC.preimage bR.continuous).preimage (map R (R ⊗[k] V) G⁻¹).continuous⟩ :=
    Closeds.ext hset
  rw [hcl, ← Scheme.IdealSheafData.comap_vanishingIdeal_of_isOpenImmersion (map R (R ⊗[k] V) G⁻¹)
      ⟨bR.base ⁻¹' C, hC.preimage bR.continuous⟩,
    ← Scheme.IdealSheafData.comap_comp, pointSection_comp_map, hspec₀, Category.id_comp, ← hconst,
    ← Scheme.IdealSheafData.comap_comp, pointSection_comp_baseChangeMap,
    Scheme.IdealSheafData.comap_id]

end Fibre

end ProjectiveSpaceOfModule

end AlgebraicGeometry

end
