module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SingleDegreeFreeGeometricPoint

/-!
# Spreading out a geometric fibre with cohomology in one degree

Let `E` be a perfect object of `D(𝒪_X)` for an algebraic space `X`, and let `c : Spec k ⟶ X` be
the morphism defined by a geometric point. If the global sections of the cohomology sheaves of
`Lc^*E` vanish outside one degree `i`, then `E` is free of some finite rank `n` placed in degree
`i` on an étale chart through the image of the point.

This is `AlgebraicGeometry.Space.pointsMap_mem_singleDegreeFreePoints` with the hypothesis that
`Lc^*E` is free placed in degree `i` replaced by the vanishing of the other cohomology: on the
spectrum of an algebraically closed field the global sections functor is exact, so the complex of
global sections of a strictly perfect model of `Lc^*E` has cohomology only in degree `i`, which is
the input of `StacksDraft.Perfect.exists_away_homotopyEquiv_single_of_finrank_homology`. The rank
`n` is the dimension of that cohomology.

## Main results

* `AlgebraicGeometry.Space.exists_mem_singleDegreeFreePoints_of_isZero_homModule_homology`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X : AlgebraicSpaces B S hS}

/-- **A perfect complex whose geometric fibre has cohomology in one degree is free in that degree
near the point.** Let `E` be perfect on `X`, let `p` be a geometric point of an algebraic space,
and let `c` be a morphism to `X` from the spectrum of the field of `p` such that the global
sections of `Hʲ(Lc^*E)` vanish for every `j ≠ i`. Then for some `n` the image of `p` in `X` lies
in the image of an étale chart on which `E` is free of rank `n` placed in degree `i`. -/
theorem exists_mem_singleDegreeFreePoints_of_isZero_homModule_homology
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E) (i : ℤ)
    (p : GeometricPoint B S hS F)
    (c : (⟨yoneda.obj p.val.siteObject, isAlgebraicSpace_yoneda B S hS p.val.siteObject⟩ :
      AlgebraicSpaces B S hS) ⟶ X)
    (hz : ∀ j, j ≠ i → IsZero ((homModule (SheafOfModules.unit _)
      (Stacks.SheafOfModules.unitEndRingHom.{u}
        (structureSheaf B S hS (yoneda.obj p.val.siteObject)
          (isAlgebraicSpace_yoneda B S hS p.val.siteObject))
        (isTerminal_idChart B S hS p.val.siteObject))).obj
      ((DerivedCategory.homologyFunctor _ j).obj
        ((smallEtaleDerivedModulePullback B S hS c).obj E)))) :
    ∃ n : ℕ, pointsMap B S hS _ c.hom (GeometricPoint.tautological B S hS p).image ∈
      singleDegreeFreePoints B S hS E i n := by
  classical
  let K := p.val.siteObject
  let x : GeometricPoint B S hS X.1 :=
    ⟨FieldValuedPoint.map B S hS _ c.hom (GeometricPoint.tautological B S hS p).val, p.property⟩
  obtain ⟨N, A, hAret, ⟨a, b, hAa, hAb⟩, ⟨eA⟩⟩ :=
    exists_smallEtaleNeighborhood_hasStrictlyPerfectModel B S hS E hE x
  let V := N.chart
  let TV := (SmallEtale.toOver B S hS X.1).obj V
  let bm : (⟨yoneda.obj K, isAlgebraicSpace_yoneda B S hS K⟩ : AlgebraicSpaces B S hS) ⟶
      ⟨yoneda.obj TV, isAlgebraicSpace_yoneda B S hS TV⟩ :=
    representedSpaceMap B S hS N.point
  have hbm : bm ≫ chartToSpace B S hS X V = c := by
    refine InducedCategory.hom_ext (yonedaEquiv.injective ?_)
    change yonedaEquiv (yoneda.map N.point ≫ V.obj.hom) = yonedaEquiv c.hom
    rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    exact N.point_comp
  have : (modulePullback B S hS bm).Additive := modulePullback_additive bm
  have := hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS bm
  obtain ⟨e1⟩ := @nonempty_smallEtaleDerivedModulePullback_obj_Q_iso_modulePullback _ _ _ _
    ⟨yoneda.obj TV, isAlgebraicSpace_yoneda B S hS TV⟩ bm A b hAb
    (fun j ↦ isFlat_of_isRetractOfFiniteFree B S hS _ (hAret j))
  let eQ : (DerivedCategory.Q).obj
      (((modulePullback B S hS bm).mapHomologicalComplex (ComplexShape.up ℤ)).obj A) ≅
      (smallEtaleDerivedModulePullback B S hS c).obj E :=
    e1.symm ≪≫ (smallEtaleDerivedModulePullback B S hS bm).mapIso eA.symm ≪≫
      (smallEtaleDerivedModulePullbackCompIso B S hS bm (chartToSpace B S hS X V)).app E ≪≫
      (smallEtaleDerivedModulePullbackCongr B S hS hbm).app E
  let OV := structureSheaf B S hS (yoneda.obj TV) (isAlgebraicSpace_yoneda B S hS TV)
  let hTV := isTerminal_idChart B S hS TV
  let ρV := Stacks.SheafOfModules.unitEndRingHom.{u} OV hTV
  have hρV := Stacks.SheafOfModules.bijective_unitEndRingHom.{u} OV hTV
  let OK := structureSheaf B S hS (yoneda.obj K) (isAlgebraicSpace_yoneda B S hS K)
  let hTK := isTerminal_idChart B S hS K
  let ρK := Stacks.SheafOfModules.unitEndRingHom.{u} OK hTK
  have hρK := Stacks.SheafOfModules.bijective_unitEndRingHom.{u} OK hTK
  let L := ((homModule _ ρV).mapHomologicalComplex (ComplexShape.up ℤ)).obj A
  have : CochainComplex.IsStrictlyGE L a := (CochainComplex.isStrictlyGE_iff L a).2
    fun j hj ↦ (homModule _ ρV).map_isZero (A.isZero_of_isStrictlyGE a j hj)
  have : CochainComplex.IsStrictlyLE L b := (CochainComplex.isStrictlyLE_iff L b).2
    fun j hj ↦ (homModule _ ρV).map_isZero (A.isZero_of_isStrictlyLE b j hj)
  let ψ := baseChangeRingHom.{u}
      (C := Modules.{u, u} B S hS (yoneda.obj TV) (isAlgebraicSpace_yoneda B S hS TV))
      (D := Modules.{u, u} B S hS (yoneda.obj K) (isAlgebraicSpace_yoneda B S hS K))
      (ρ := ρV) ρK hρK (modulePullback B S hS bm) (hF := modulePullback_additive bm)
      (modulePullbackUnitIso B S hS bm)
  have hψ : ∀ t, ψ t = ((BigFppfOver.toScheme B S hS).map N.point).appTop t :=
    baseChangeRingHom_representedSpaceMap B S hS (T' := K) (T := TV) N.point
  let : Field (OK.obj.obj (op (idChart B S hS K))) :=
    (isField_structureSheaf_idChart B S hS p.val).toField
  let ebc := homModuleBaseChangeComplexIso (ρ := ρV) ρK hρK (modulePullback B S hS bm)
    (hF := modulePullback_additive bm) (modulePullbackUnitIso B S hS bm) hρV A hAret
  let n : ℕ := Module.finrank (OK.obj.obj (op (idChart B S hS K)))
    ((((ModuleCat.extendScalars.{u, u, u + 1} ψ).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L).homology i)
  have hdim : ∀ j, Module.finrank (OK.obj.obj (op (idChart B S hS K)))
      ((((ModuleCat.extendScalars.{u, u, u + 1} ψ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L).homology j) = if j = i then n else 0 := fun j ↦ by
    split_ifs with hj
    · rw [hj]
    · have := Stacks.SheafOfModules.projective_unit_of_mem OK hTK
        (fun _ hR ↦ idChart_mem_of_mem_geometricPoint B S hS p hR)
      let G := homModule (SheafOfModules.unit _) ρK
      let eH := (HomologicalComplex.homologyFunctor _ _ j).mapIso ebc ≪≫
        (StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso G
          (ComplexShape.up ℤ) j).app _ ≪≫
        G.mapIso (((DerivedCategory.homologyFunctorFactors _ j).app _).symm ≪≫
          (DerivedCategory.homologyFunctor _ j).mapIso eQ)
      have hsub : Subsingleton ((((ModuleCat.extendScalars.{u, u, u + 1} ψ).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L).homology j) :=
        ModuleCat.subsingleton_of_isZero ((hz j hj).of_iso eH)
      exact Module.finrank_zero_of_subsingleton
  obtain ⟨g, hg, ⟨eg⟩⟩ :=
    StacksDraft.Perfect.exists_away_homotopyEquiv_single_of_finrank_homology.{u, u + 1} ψ L a b
      (fun j ↦ (homModule_finite_projective hρV (hAret j)).1)
      (fun j ↦ (homModule_finite_projective hρV (hAret j)).2) i n hdim
  let g' : Γ(chartScheme V, ⊤) := g
  let W : (chartScheme V).Opens := (chartScheme V).basicOpen g'
  have hpre : (BigFppfOver.toScheme B S hS).map N.point ⁻¹ᵁ W = ⊤ :=
    (Scheme.preimage_basicOpen_top _ g').trans
      ((congrArg _ (hψ g).symm).trans (Scheme.basicOpen_of_isUnit _ (isUnit_iff_ne_zero.2 hg)))
  have hw : chartPoint B S hS X.1 N ∈ W :=
    show IsLocalRing.closedPoint p.val.carrier ∈ (BigFppfOver.toScheme B S hS).map N.point ⁻¹ᵁ W
      from hpre ▸ trivial
  let N' := chartOpenNeighborhood B S hS N W hw
  let ι := (chartOpenNeighborhoodHom B S hS N W hw).hom
  have hk : (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map ι) ⁻¹ᵁ W = ⊤ :=
    W.ι_preimage_self
  obtain ⟨eθ⟩ := StacksDraft.Perfect.nonempty_homotopyEquiv_single_of_isUnit.{u, u + 1} L g i n eg
    _ (isUnit_baseChangeRingHom_of_preimage_basicOpen B S hS ι g hk)
  exact ⟨n, N'.chart, ⟨_, chartFieldValuedPoint_pointsMap N'⟩,
    isFreeOfRankInDegree_of_homotopyEquiv_homModule B S hS E ι A hAret b hAb eA i n eθ⟩

end AlgebraicGeometry.Space

end
