module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationGeneration.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationGeneration.GeometryAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOpenRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SpaceRationalFunctionChart
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseOpenChartSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenCover

/-!
# A finite affine chart cover of a representable space with affine overlaps

Let `P` be an algebraic space isomorphic to the presheaf represented by an object `O` of the
site whose scheme is quasi-compact and in which the intersection of two affine opens is affine
(for instance an open subscheme of an affine scheme).  Then `P` carries a
`AlgebraicGeometry.Space.FiniteAffineChartCover`: the chart `e⁻¹ : yoneda O ⟶ P` is terminal in
the small étale site of `P`, finitely many affine opens `Oₖ` cover `O`, the charts they cut out
are the members of the covering, and the charts cut out by the intersections `Oₖ ∩ Oₗ` are the
overlaps.  A chart mapping to two members has its points in the points of both, which are the
points of the overlap because `e⁻¹` is injective on points, so it factors through the overlap
chart, an open immersion chart; the two triangles commute because the structure morphisms of the
members are monomorphisms.

## Main results

* `AlgebraicGeometry.Space.nonempty_finiteAffineChartCover_of_iso`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Two morphisms into an étale chart whose structure morphism is a monomorphism agree. -/
theorem SmallEtale.hom_ext_of_mono {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Y Z : SmallEtale B S hS F} (hZ : Mono Z.1.hom) (a b : Y ⟶ Z) : a = b := by
  apply ObjectProperty.hom_ext
  apply CostructuredArrow.hom_ext
  apply yoneda.map_injective
  exact (cancel_mono Z.1.hom).1 ((CostructuredArrow.w a.hom).trans (CostructuredArrow.w b.hom).symm)

/-- An isomorphism of presheaves is injective on points. -/
theorem pointsMap_injective_of_iso {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G) :
    Function.Injective (pointsMap B S hS F e.hom) := by
  intro x y h
  have h₁ : ∀ z, pointsMap B S hS F (e.hom ≫ e.inv) z = z := fun z => by
    rw [e.hom_inv_id]
    exact congrFun (pointsMap_id B S hS F) z
  rw [← h₁ x, ← h₁ y, pointsMap_comp_apply, pointsMap_comp_apply, h]

/-- A chart mapping to the open charts of `U` and `V` of a chart injective on points has its
points in the points of the open chart of `U ⊓ V`. -/
theorem range_pointsMap_subset_openChart_inf {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (C : SmallEtale B S hS F)
    (hinj : Function.Injective (pointsMap B S hS (yoneda.obj C.obj.left) C.1.hom))
    {U V : (chartScheme C).Opens} {Y : SmallEtale B S hS F}
    (a : Y ⟶ openChart B S hS F C U) (b : Y ⟶ openChart B S hS F C V) :
    Set.range (pointsMap B S hS _ Y.1.hom) ⊆
      Set.range (pointsMap B S hS _ (openChart B S hS F C (U ⊓ V)).1.hom) := by
  rintro _ ⟨y, rfl⟩
  have key : ∀ {W : (chartScheme C).Opens} (c : Y ⟶ openChart B S hS F C W),
      pointsMap B S hS _ Y.1.hom y ∈
        Set.range (pointsMap B S hS _ (openChart B S hS F C W).1.hom) := fun c => by
    rw [← CostructuredArrow.w c.hom, pointsMap_comp_apply]
    exact ⟨_, rfl⟩
  have h₁ := key a
  have h₂ := key b
  rw [range_pointsMap_openChart] at h₁ h₂ ⊢
  obtain ⟨p, hp, hpe⟩ := h₁
  obtain ⟨q, hq, hqe⟩ := h₂
  obtain rfl : p = q := hinj (hpe.trans hqe.symm)
  exact ⟨_, ⟨hp, hq⟩, hpe⟩

/-- The open charts cut out of the chart `e⁻¹` of a representable presheaf by a family of opens
covering its scheme cover the presheaf. -/
theorem coversTop_openChart_isoChart {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {O : BigFppfOver B S hS} (e : F ≅ yoneda.obj O) {ι : Type*}
    (U : ι → (chartScheme (isoChart B S hS e.symm)).Opens) (hU : ∀ x, ∃ k, x ∈ U k) :
    (SmallEtale.topology B S hS F).CoversTop
      fun k => openChart B S hS F (isoChart B S hS e.symm) (U k) := by
  intro Y
  rw [SmallEtale.mem_topology_iff_exists_mem_range]
  intro x
  let g := toIsoChartSymm B S hS e Y
  obtain ⟨k, hk⟩ := hU (chartSchemeMap g x)
  refine ⟨openChart B S hS F Y (chartSchemeMap g ⁻¹ᵁ U k),
    openChartInclusion B S hS F Y _,
    (Sieve.mem_ofObjects_iff _ _).2 ⟨k, ⟨openChartRestrict B S hS F g (U k)⟩⟩, ?_⟩
  rw [toScheme_map_toOver_map_openChartInclusion]
  exact (Scheme.Opens.range_ι (chartSchemeMap g ⁻¹ᵁ U k)).symm ▸ hk

/-- **A finite affine chart cover with affine overlaps of a representable space.** -/
theorem nonempty_finiteAffineChartCover_of_iso (P : AlgebraicSpaces B S hS)
    {O : BigFppfOver B S hS} (eP : P.1 ≅ yoneda.obj O)
    (hO : CompactSpace ((BigFppfOver.toScheme B S hS).obj O))
    (hsep : ∀ U V : ((BigFppfOver.toScheme B S hS).obj O).Opens,
      IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V)) :
    Nonempty (FiniteAffineChartCover B S hS P) := by
  classical
  let C := isoChart B S hS eP.symm
  have hC : IsOpenImmersion B S hS C.1.hom := isOpenImmersion_of_isIso B S hS eP.inv
  have : CompactSpace (chartScheme C) := hO
  have hcpt : IsCompact (X := chartScheme C)
      ((⊤ : (chartScheme C).Opens) : Set (chartScheme C)) := by
    rw [TopologicalSpace.Opens.coe_top]
    exact isCompact_univ
  obtain ⟨s, hs, htop⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.1 hcpt
  have := hs.to_subtype
  obtain ⟨n, ⟨eqv⟩⟩ := Finite.exists_equiv_fin s
  let U : Fin n → (chartScheme C).Opens := fun k => ((eqv.symm k).1 : (chartScheme C).Opens)
  have hU : ∀ k, IsAffineOpen (U k) := fun k => (eqv.symm k).1.2
  let T : Fin n → SmallEtale B S hS P.1 := fun k => openChart B S hS P.1 C (U k)
  have hTimm : ∀ k, IsOpenImmersion B S hS (T k).1.hom := fun k =>
    isOpenImmersion_openChart C hC (U k)
  refine ⟨{
    ι := Fin n
    finite := inferInstance
    T := T
    isAffine := hU
    coversTop := coversTop_openChart_isoChart B S hS eP U fun x => by
      have hx : x ∈ (⊤ : (chartScheme C).Opens) := trivial
      rw [htop] at hx
      simp only [TopologicalSpace.Opens.mem_iSup] at hx
      obtain ⟨i, hi, hxi⟩ := hx
      exact ⟨eqv ⟨i, hi⟩, by simpa [U] using hxi⟩
    T₂ := fun k l => openChart B S hS P.1 C (U k ⊓ U l)
    p₁ := fun k l => openChartHomOfLE B S hS P.1 C inf_le_left
    p₂ := fun k l => openChartHomOfLE B S hS P.1 C inf_le_right
    isAffine₂ := fun k l => hsep _ _ (hU k) (hU l)
    factor := ?_ }⟩
  intro k l Y a b
  obtain ⟨σ, hσ⟩ := exists_hom_of_range_pointsMap_subset _ (isOpenImmersion_openChart C hC _)
    Y.1.hom (range_pointsMap_subset_openChart_inf B S hS C
      (pointsMap_injective_of_iso B S hS eP.symm) a b)
  exact ⟨ObjectProperty.homMk (CostructuredArrow.homMk σ hσ),
    SmallEtale.hom_ext_of_mono B S hS (mono_of_presheaf_isOpenImmersion (hTimm k)) _ _,
    SmallEtale.hom_ext_of_mono B S hS (mono_of_presheaf_isOpenImmersion (hTimm l)) _ _⟩

end AlgebraicGeometry.Space

end
