module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReasonableEtaleCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.UniversallyBoundedFibresOpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.VeryReasonableAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.FppfCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoverAffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparated
public import StacksFrontier.CategoryTheory.Sites.Representable.CoproductYonedaDesc

/-!
# A Zariski locally quasi-separated algebraic space is very reasonable

Stacks 03JX relates nine conditions on an algebraic space `X` over a scheme `S`. We prove the
implication `(ζ) ⇒ (ε)`: an algebraic space which is Zariski locally quasi-separated — covered
by open subspaces which are quasi-separated over the terminal scheme, the space being viewed
over the terminal scheme through `AlgebraicGeometry.Space.viewOverIntegers` — admits a jointly
surjective family of étale charts by schemes whose two self-intersection projections are
quasi-compact.

## Main results

* `AlgebraicGeometry.Space.compactSpace_of_isQuasiSeparatedOver`: for a presheaf on the big
  fppf site of the terminal scheme which is quasi-separated over it, the represented fibre
  product of two charts with quasi-compact schemes is again quasi-compact.
* `AlgebraicGeometry.Space.isVeryReasonableSpace_of_isAbsolutelyZariskiLocallyQuasiSeparated`:
  **Stacks 03JX, `(ζ) ⇒ (ε)`.**

## References

* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03FY](https://stacks.math.columbia.edu/tag/03FY)
* [Stacks Project, Tag 03IE](https://stacks.math.columbia.edu/tag/03IE)
* [Stacks Project, Tag 03IH](https://stacks.math.columbia.edu/tag/03IH)
* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
* [Stacks Project, Tag 03KE](https://stacks.math.columbia.edu/tag/03KE)
* [Stacks Project, Tag 073B](https://stacks.math.columbia.edu/tag/073B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Spaces

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

/- Pullbacks of presheaves on the big fppf site, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) : HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

local instance (priority := high) {Y Z W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : Y ⟶ W)
    (g : Z ⟶ W) : HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit (cospan f g)

/-! ### Quasi-compactness of a self-intersection over the terminal scheme -/

/-- **A morphism from a quasi-compact algebraic space to a quasi-separated one is
quasi-compact, on charts, over the terminal scheme.** For a presheaf `X` on the big fppf site
of the terminal scheme which is quasi-separated over it, the represented fibre product of two
charts whose schemes are quasi-compact is again quasi-compact. -/
theorem compactSpace_of_isQuasiSeparatedOver
    {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (hXqs : IsQuasiSeparatedOver B (⊤_ Scheme.{u}) hZ X)
    {A W Q : BigFppfOver B (⊤_ Scheme.{u}) hZ} {c : yoneda.obj A ⟶ X} {g : yoneda.obj W ⟶ X}
    {q₁ : Q ⟶ A} {q₂ : Q ⟶ W}
    (hsq : IsPullback (yoneda.map q₁) (yoneda.map q₂) c g)
    (hA : CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj A))
    (hW : CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj W)) :
    CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj Q) := by
  have _ : HasBinaryProducts (BigFppfOver B (⊤_ Scheme.{u}) hZ) :=
    CategoryTheory.Over.ConstructProducts.over_binaryProduct_of_pullback
  have hdiag := isPullback_diag_prodMap hsq
  set i := prodComparison (yoneda : BigFppfOver B (⊤_ Scheme.{u}) hZ ⥤ _) A W with hi
  have _ : IsIso i := by rw [hi]; infer_instance
  have hlift : yoneda.map (prod.lift q₁ q₂) ≫ i =
      prod.lift (yoneda.map q₁) (yoneda.map q₂) := by
    refine prod.hom_ext ?_ ?_ <;> simp [hi, ← Functor.map_comp]
  have hfinal : IsPullback (yoneda.map q₁ ≫ c) (yoneda.map (prod.lift q₁ q₂)) (diag X)
      (i ≫ prod.map c g) := isPullback_of_iso_right (by rw [hlift]; exact hdiag)
  have hqc := hXqs.property _ _ _ hfinal
  have hprod : CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (A ⨯ W)) :=
    compactSpace_of_isPullback_hom B hZ
      (CategoryTheory.Over.isPullback_of_binaryFan_isLimit (BinaryFan.mk prod.fst prod.snd)
        (prodIsProd _ _)) hA hW
  exact @QuasiCompact.compactSpace_of_compactSpace _ _
    ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (prod.lift q₁ q₂)) hqc hprod

/-! ### Charts viewed over the terminal scheme -/

/-- The morphism of the big fppf site from `S` to the terminal scheme along which
`AlgebraicGeometry.Space.viewOverIntegers` relocalizes. -/
private noncomputable abbrev integersHom : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩

/-- A chart of a presheaf on the big fppf site of `S`, viewed as a chart of the presheaf over
the terminal scheme: the relocalized morphism, read through the comparison
`Λ h_A ≅ h_{j A}` of Stacks 03I4 part (2). -/
private noncomputable abbrev viewChartOverIntegers
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {A : BigFppfOver B S hS} (c : yoneda.obj A ⟶ X) :
    yoneda.obj ((Over.map (integersHom B S hS hZ)).obj A) ⟶ viewOverIntegers B S hS hZ X :=
  ((OverShriek.relocalizeYonedaIso (integersHom B S hS hZ)).app A).inv ≫
    (OverShriek.relocalizePresheafFunctor (integersHom B S hS hZ)).map c

/-- Precomposing a chart with a morphism of the site commutes with viewing it over the
terminal scheme. -/
private theorem viewChartOverIntegers_yoneda_map_comp
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {A A' : BigFppfOver B S hS} (m : A' ⟶ A)
    (c : yoneda.obj A ⟶ X) :
    viewChartOverIntegers B S hS hZ (yoneda.map m ≫ c) =
      yoneda.map ((Over.map (integersHom B S hS hZ)).map m) ≫
        viewChartOverIntegers B S hS hZ c := by
  have hnat := (OverShriek.relocalizeYonedaIso (integersHom B S hS hZ)).inv.naturality m
  simp only [viewChartOverIntegers, Functor.map_comp, ← Category.assoc]
  exact congrArg
    (fun z ↦ z ≫ (OverShriek.relocalizePresheafFunctor (integersHom B S hS hZ)).map c)
    hnat.symm

/-- Viewing a cartesian square of charts over the terminal scheme leaves it cartesian. -/
private theorem isPullback_viewChartOverIntegers
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {A W Q : BigFppfOver B S hS}
    {c : yoneda.obj A ⟶ X} {g : yoneda.obj W ⟶ X} {q₁ : Q ⟶ A} {q₂ : Q ⟶ W}
    (hsq : IsPullback (yoneda.map q₁) (yoneda.map q₂) c g) :
    IsPullback (yoneda.map ((Over.map (integersHom B S hS hZ)).map q₁))
      (yoneda.map ((Over.map (integersHom B S hS hZ)).map q₂))
      (viewChartOverIntegers B S hS hZ c) (viewChartOverIntegers B S hS hZ g) := by
  set hiso := OverShriek.relocalizeYonedaIso (integersHom B S hS hZ) with hisodef
  refine (hsq.map (OverShriek.relocalizePresheafFunctor (integersHom B S hS hZ))).of_iso
    (hiso.app Q) (hiso.app A) (hiso.app W) (Iso.refl _) ?_ ?_ ?_ ?_
  · exact hiso.hom.naturality q₁
  · exact hiso.hom.naturality q₂
  · simp [viewChartOverIntegers, hisodef]
  · simp [viewChartOverIntegers, hisodef]

/-! ### Refining an affine atlas by the members of the covering -/

/-- Quasi-compactness of both self-intersection projections of an affine étale chart whose
view over the terminal scheme factors through a quasi-separated open subspace. -/
private theorem isQuasiCompact_pullback_fst_snd_of_factorsThrough
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {A : BigFppfOver B S hS} (hA : IsAffine ((BigFppfOver.toScheme B S hS).obj A))
    (c : yoneda.obj A ⟶ X) (Y : Subfunctor (viewOverIntegers B S hS hZ X))
    (hYqs : IsQuasiSeparatedOver B (⊤_ Scheme.{u}) hZ Y.toFunctor)
    (hfac : ∃ ξ : yoneda.obj ((Over.map (integersHom B S hS hZ)).obj A) ⟶ Y.toFunctor,
      ξ ≫ Y.ι = viewChartOverIntegers B S hS hZ c) :
    IsQuasiCompact B S hS (pullback.fst c c) ∧ IsQuasiCompact B S hS (pullback.snd c c) := by
  have _ : HasBinaryProducts (BigFppfOver B S hS) :=
    CategoryTheory.Over.ConstructProducts.over_binaryProduct_of_pullback
  obtain ⟨ξ, hξ⟩ := hfac
  have hrep : yoneda.relativelyRepresentable c := hX.diagonal_representable.of_diag c
  have hsq : IsPullback (yoneda.map (hrep.fst' c)) (yoneda.map (hrep.snd c)) c c :=
    hrep.isPullback' c
  have hsqZ := isPullback_viewChartOverIntegers B S hS hZ hsq
  rw [← hξ] at hsqZ
  have hsqY : IsPullback (yoneda.map ((Over.map (integersHom B S hS hZ)).map (hrep.fst' c)))
      (yoneda.map ((Over.map (integersHom B S hS hZ)).map (hrep.snd c))) ξ ξ :=
    IsPullback.of_isLimit
      (PullbackCone.isLimitOfFactors (ξ ≫ Y.ι) (ξ ≫ Y.ι) Y.ι ξ ξ rfl rfl
        (PullbackCone.mk _ _ hsqZ.w) hsqZ.isLimit)
  have hAc : CompactSpace ((BigFppfOver.toScheme B S hS).obj A) := inferInstance
  have hQc : CompactSpace ((BigFppfOver.toScheme B S hS).obj (hrep.pullback c)) :=
    compactSpace_of_isQuasiSeparatedOver B hZ hYqs hsqY hAc hAc
  have hqc : ∀ q : hrep.pullback c ⟶ A, IsQuasiCompact B S hS (yoneda.map q) := fun q ↦
    isQuasiCompact_of_presheaf_quasiCompact B S hS
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ _).2
        (quasiCompact_of_compactSpace_of_isAffine _ hA hQc))
  exact ⟨isQuasiCompact_of_domainIso B S hS hsq.isoPullback hsq.isoPullback_hom_fst (hqc _),
    isQuasiCompact_of_domainIso B S hS hsq.isoPullback hsq.isoPullback_hom_snd (hqc _)⟩

/-! ### Selecting the affine opens -/

/-- Around every point of a chart of an algebraic space over `S` there is an affine open of
the chart whose view over the terminal scheme factors through a member of a given Zariski
covering of the space viewed over the terminal scheme. -/
private theorem exists_affineOpen_factorsThrough_of_isZariskiCover
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {Jz : Type u} (Y : Jz → Subfunctor (viewOverIntegers B S hS hZ X))
    (hYcov : IsZariskiCover B (⊤_ Scheme.{u}) hZ Jz Y)
    (A : BigFppfOver B S hS) (c : yoneda.obj A ⟶ X)
    (y : (BigFppfOver.toScheme B S hS).obj A) :
    ∃ (O : ((BigFppfOver.toScheme B S hS).obj A).Opens) (j : Jz),
      IsAffineOpen O ∧ y ∈ O ∧
        ∃ ξ : yoneda.obj ((Over.map (integersHom B S hS hZ)).obj (openObj B S hS A O)) ⟶
            (Y j).toFunctor,
          ξ ≫ (Y j).ι = viewChartOverIntegers B S hS hZ
            (yoneda.map (openIncl B S hS A O) ≫ c) := by
  classical
  have hLX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (viewOverIntegers B S hS hZ X) :=
    isAlgebraicSpace_relocalize B (B.obj hS) (B.obj hZ) (integersHom B S hS hZ) X hX
  have hYpoints := (isZariskiCover_iff_iUnion_points B (⊤_ Scheme.{u}) hZ
    (viewOverIntegers B S hS hZ X) hLX Jz Y hYcov.1).1 hYcov
  choose V hVopen hVmem using fun j : Jz ↦
    (isOpen_pointTopology_iff B (⊤_ Scheme.{u}) hZ
      (Set.range (pointsMap B (⊤_ Scheme.{u}) hZ (Y j).toFunctor (Y j).ι))).1
      (isOpen_range_pointsMap_of_isOpenImmersion B (⊤_ Scheme.{u}) hZ _ (hYcov.1 j).2)
      ((Over.map (integersHom B S hS hZ)).obj A) (viewChartOverIntegers B S hS hZ c)
  obtain ⟨p, hp⟩ := exists_fieldValuedPoint_schemePoint_eq B (⊤_ Scheme.{u}) hZ
    ((Over.map (integersHom B S hS hZ)).obj A) y
  have hmem : pointsMap B (⊤_ Scheme.{u}) hZ _ (viewChartOverIntegers B S hS hZ c)
      (p.class B (⊤_ Scheme.{u}) hZ _) ∈
      ⋃ j, Set.range (pointsMap B (⊤_ Scheme.{u}) hZ (Y j).toFunctor (Y j).ι) := by
    rw [hYpoints]
    exact Set.mem_univ _
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hmem
  have hyV : y ∈ V j := by
    rw [← hp]
    exact (hVmem j p).1 hj
  obtain ⟨O, hOaff, hyO, hOsub⟩ :=
    _root_.AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
      (X := (BigFppfOver.toScheme B S hS).obj A) (x := y) (U := ⟨V j, hVopen j⟩) hyV
  refine ⟨O, j, hOaff, hyO, ?_⟩
  refine (factorsThrough_openSubspace_iff_points B (⊤_ Scheme.{u}) hZ hLX
    (isAlgebraicSpace_yoneda B (⊤_ Scheme.{u}) hZ _) (Y j) (hYcov.1 j) _).2 ?_
  rw [viewChartOverIntegers_yoneda_map_comp, pointsMap_comp]
  rintro z ⟨w, rfl⟩
  obtain ⟨q, rfl⟩ := Quot.exists_rep w
  refine (hVmem j (FieldValuedPoint.map B (⊤_ Scheme.{u}) hZ _
    (yoneda.map ((Over.map (integersHom B S hS hZ)).map (openIncl B S hS A O))) q)).2 ?_
  rw [schemePoint_map_yoneda]
  exact hOsub (schemePoint B (⊤_ Scheme.{u}) hZ
    ((Over.map (integersHom B S hS hZ)).obj (openObj B S hS A O)) q).2

/-! ### The implication `(ζ) ⇒ (ε)` -/

/-- A Zariski locally quasi-separated algebraic space over `S` is very reasonable: it admits a
jointly surjective family of étale charts by schemes whose two self-intersection projections
are quasi-compact. -/
@[stacks 03JX "(zeta) implies (epsilon)"]
theorem isVeryReasonableSpace_of_isAbsolutelyZariskiLocallyQuasiSeparated
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (hζ : IsAbsolutelyZariskiLocallyQuasiSeparated B S hS hZ X) :
    IsVeryReasonableSpace B S hS X := by
  classical
  obtain ⟨Jz, Y, hYcov, hYqs⟩ := hζ
  obtain ⟨Ai, Xa, hXacov, hatlas⟩ := exists_zariski_cover_affine_etale_atlas B S hS X hX
  refine isVeryReasonableSpace_of_isZariskiCover B S hS X Ai Xa hXacov fun a ↦ ?_
  obtain ⟨Ua, fa, -, hUaAff, hfaSurj, hfaEt, -, -⟩ := hatlas a
  choose O j hOaff hyO hfac using
    exists_affineOpen_factorsThrough_of_isZariskiCover B S hS hZ hX Y hYcov Ua
      (fa ≫ (Xa a).ι)
  refine ⟨(BigFppfOver.toScheme B S hS).obj Ua, fun y ↦ openObj B S hS Ua (O y),
    fun y ↦ yoneda.map (openIncl B S hS Ua (O y)) ≫ fa, ?_, ?_⟩
  · have hcovSieve : Sieve.generate (Presieve.ofArrows
        (fun y ↦ openObj B S hS Ua (O y)) (fun y ↦ openIncl B S hS Ua (O y))) ∈
          BigFppfOver.topology B S hS Ua := by
      refine generate_ofArrows_mem_topology_of_openCover B S hS _ _ (fun y ↦ ?_) fun y ↦ ?_
      · exact inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion (O y).ι)
      · exact ⟨y, ⟨y, hyO y⟩, by rw [toScheme_map_openIncl]; rfl⟩
    have h1 : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
        (coprodYonedaDesc (fun y ↦ openObj B S hS Ua (O y)) Ua
          fun y ↦ openIncl B S hS Ua (O y)) :=
      isLocallySurjective_coprodYonedaDesc _ _ _ _ hcovSieve
    simp only [coprodYonedaDesc] at h1
    have h2 : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) fa :=
      isLocallySurjective_of_surjective_etale B S hS fa hfaSurj hfaEt
    have h4 : (Sigma.desc fun y ↦ yoneda.map (openIncl B S hS Ua (O y))) ≫ fa =
        Sigma.desc fun y ↦ yoneda.map (openIncl B S hS Ua (O y)) ≫ fa :=
      Sigma.hom_ext _ _ fun y ↦ by rw [← Category.assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc]
    rw [← h4]
    infer_instance
  · intro y
    have hOaffObj : IsAffine ((BigFppfOver.toScheme B S hS).obj
        (openObj B S hS Ua (O y))) := by
      rw [toScheme_obj_openObj]
      exact hOaff y
    set g := yoneda.map (openIncl B S hS Ua (O y)) ≫ fa with hg
    have hEt : (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf g :=
      etale_comp_of_scheme B S hS (openIncl B S hS Ua (O y)) fa
        (inferInstanceAs (_root_.AlgebraicGeometry.Etale (O y).ι)) hfaEt
    have hqc := isQuasiCompact_pullback_fst_snd_of_factorsThrough B S hS hZ hX hOaffObj
      (g ≫ (Xa a).ι) (Y (j y)) (hYqs (j y)) (by rw [hg, Category.assoc]; exact hfac y)
    have hpb := IsPullback.of_isLimit (pullbackIsPullbackOfCompMono g g (Xa a).ι)
    exact ⟨isEtale_of_presheaf_etale B S hS hEt,
      isQuasiCompact_of_domainIso B S hS hpb.isoPullback.symm hpb.isoPullback_inv_fst hqc.1,
      isQuasiCompact_of_domainIso B S hS hpb.isoPullback.symm hpb.isoPullback_inv_snd hqc.2⟩

end AlgebraicGeometry.Space

end
