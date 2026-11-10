module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalSiteSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOpenNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartPointLifts
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SingleDegreeFreeLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackKFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleGeometricPointSite
public import StacksFrontier.Homology.Perfect.SingleDegreeFibreOverField

/-!
# Free fibres of a perfect complex spread out to free étale neighbourhoods

Let `E` be a perfect object of `D(𝒪_X)` for an algebraic space `X`, and let `x̄` be a geometric
point of `X`. If the derived pullback of `E` to the spectrum of the field of `x̄` is free of rank
`r` placed in degree `i`, then so is the derived restriction of `E` to an étale chart through
the image of `x̄`.

## Main results

* `AlgebraicGeometry.Space.exists_smallEtaleNeighborhood_hasStrictlyPerfectModel`: a perfect
  object has a strictly perfect model on a small étale neighbourhood of every geometric point.
* `AlgebraicGeometry.Space.isField_structureSheaf_idChart`: the global functions on the
  spectrum of the field of a geometric point form a field.
* `AlgebraicGeometry.Space.baseChangeRingHom_representedSpaceMap`: on global functions, the
  pullback of modules along a morphism of represented spaces is pullback of functions.
* `AlgebraicGeometry.Space.finrank_homology_homModule_of_Q_iso_single`: fibre dimensions of a
  complex which is free in one degree at a geometric point.
* `AlgebraicGeometry.Space.isFreeOfRankInDegree_of_homotopyEquiv_homModule`: freeness on a chart
  from a homotopy equivalence of complexes of global sections.
* `AlgebraicGeometry.Space.pointsMap_mem_singleDegreeFreePoints`: the main statement above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X : AlgebraicSpaces B S hS}

/-- **A perfect object has a strictly perfect model on a small étale neighbourhood of every
geometric point**: the charts carrying a strictly perfect model cover the final object, and a
geometric point lifts through a covering family. -/
theorem exists_smallEtaleNeighborhood_hasStrictlyPerfectModel
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (x : GeometricPoint B S hS X.1) :
    ∃ N : SmallEtaleNeighborhood x, HasStrictlyPerfectModel B S hS
      ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X N.chart)).obj E) := by
  let ι := {V : SmallEtale B S hS X.1 // HasStrictlyPerfectModel B S hS
    ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj E)}
  have hcov : (SmallEtale.topology B S hS X.1).CoversTop (fun V : ι => V.1) := by
    intro U
    obtain ⟨R, hR, hP⟩ := exists_hasStrictlyPerfectModel_chart_of_isPerfect E hE U
    refine GrothendieckTopology.superset_covering _ ?_ hR
    rintro W g ⟨Z, k, g', hg', rfl⟩
    exact ⟨⟨Z, hP g' hg'⟩, ⟨k⟩⟩
  obtain ⟨i, t', ht'⟩ := SmallEtale.exists_geometricPoint_lift_of_coversTop B S hS X.2 hcov x
  obtain ⟨⟨k, ck, tk, vk⟩, hk⟩ := x
  obtain ⟨⟨k', ck', tk', vk'⟩, hk'⟩ := t'
  simp only [FieldValuedPoint.map, FieldValuedPoint.mk.injEq] at ht'
  obtain ⟨rfl, hf, htb, hv⟩ := ht'
  cases hf
  cases htb
  exact ⟨⟨i.1, vk', eq_of_heq hv⟩, i.2⟩

/-- The global functions on the spectrum of the field of a field-valued point form a field. -/
theorem isField_structureSheaf_idChart {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (x : FieldValuedPoint B S hS F) :
    IsField ((structureSheaf B S hS (yoneda.obj x.siteObject)
      (isAlgebraicSpace_yoneda B S hS x.siteObject)).obj.obj
        (op (idChart B S hS x.siteObject))) :=
  (Scheme.ΓSpecIso (CommRingCat.of x.carrier)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField x.carrier)

/-- The ring map induced on endomorphisms of the structure sheaves by the pullback of modules
along the morphism of represented algebraic spaces attached to `g : T' ⟶ T` is pullback of
global functions along `g`. -/
theorem baseChangeRingHom_representedSpaceMap {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (a : (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)).obj.obj
      (op (idChart B S hS T))) :
    baseChangeRingHom.{u}
      (C := Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
      (D := Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T'))
      (R := (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)).obj.obj
        (op (idChart B S hS T)))
      (R' := (structureSheaf B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')).obj.obj
        (op (idChart B S hS T')))
      (ρ := Stacks.SheafOfModules.unitEndRingHom.{u}
        (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
        (isTerminal_idChart B S hS T))
      (Stacks.SheafOfModules.unitEndRingHom.{u}
        (structureSheaf B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T'))
        (isTerminal_idChart B S hS T'))
      (Stacks.SheafOfModules.bijective_unitEndRingHom.{u}
        (structureSheaf B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T'))
        (isTerminal_idChart B S hS T'))
      (modulePullback B S hS (representedSpaceMap B S hS g))
      (hF := modulePullback_additive (representedSpaceMap B S hS g))
      (modulePullbackUnitIso B S hS (representedSpaceMap B S hS g)) a =
      ((BigFppfOver.toScheme B S hS).map g).appTop a :=
  baseChangeRingHom_modulePullback B S hS (representedSpaceMap B S hS g)
    ⟨idChart B S hS T', idChart B S hS T, g,
      (Category.id_comp _).trans (Category.comp_id _).symm⟩
    (isTerminal_idChart B S hS T) (isTerminal_idChart B S hS T') a

/-- **Fibre dimensions at a geometric point.** On the spectrum of the field of a geometric
point, global sections are exact; so if a complex `K` of modules is isomorphic in the derived
category to `𝒪^{⊕n}` placed in degree `i`, the complex of global sections `Hom(𝒪, K)` has
cohomology of dimension `n` in degree `i` and zero in every other degree. -/
theorem finrank_homology_homModule_of_Q_iso_single {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : GeometricPoint B S hS F)
    (K : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj p.val.siteObject, isAlgebraicSpace_yoneda B S hS p.val.siteObject⟩)) ℤ)
    (i : ℤ) (n : ℕ)
    (e : (DerivedCategory.Q).obj K ≅ (DerivedCategory.singleFunctor _ i).obj
      (SheafOfModules.free (R := ringedToposStructureRingSheaf B S hS
        ⟨yoneda.obj p.val.siteObject, isAlgebraicSpace_yoneda B S hS p.val.siteObject⟩)
        (ULift.{u} (Fin n)))) (j : ℤ) :
    Module.finrank ((structureSheaf B S hS (yoneda.obj p.val.siteObject)
        (isAlgebraicSpace_yoneda B S hS p.val.siteObject)).obj.obj
          (op (idChart B S hS p.val.siteObject)))
      ((((homModule (SheafOfModules.unit _) (Stacks.SheafOfModules.unitEndRingHom.{u}
        (structureSheaf B S hS (yoneda.obj p.val.siteObject)
          (isAlgebraicSpace_yoneda B S hS p.val.siteObject))
        (isTerminal_idChart B S hS p.val.siteObject))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K).homology j) = if j = i then n else 0 := by
  let O := structureSheaf B S hS (yoneda.obj p.val.siteObject)
    (isAlgebraicSpace_yoneda B S hS p.val.siteObject)
  let hT := isTerminal_idChart B S hS p.val.siteObject
  let ρ := Stacks.SheafOfModules.unitEndRingHom.{u} O hT
  let : Field (O.obj.obj (op (idChart B S hS p.val.siteObject))) :=
    (isField_structureSheaf_idChart B S hS p.val).toField
  have :=
    Stacks.SheafOfModules.projective_unit_of_mem O hT
      (fun _ hR ↦ idChart_mem_of_mem_geometricPoint B S hS p hR)
  let G := homModule _ ρ
  let eH : (((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology j) ≅
      G.obj ((DerivedCategory.homologyFunctor _ j).obj
        ((DerivedCategory.singleFunctor _ i).obj
          (SheafOfModules.free (R := ringedToposStructureRingSheaf B S hS
            ⟨yoneda.obj p.val.siteObject, isAlgebraicSpace_yoneda B S hS p.val.siteObject⟩)
            (ULift.{u} (Fin n))))) :=
    (StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso G
        (ComplexShape.up ℤ) j).app K ≪≫
      G.mapIso (((DerivedCategory.homologyFunctorFactors _ j).app K).symm ≪≫
        (DerivedCategory.homologyFunctor _ j).mapIso e)
  rw [eH.toLinearEquiv.finrank_eq]
  split_ifs with hj
  · subst hj
    let eF := (DerivedCategory.singleFunctorCompHomologyFunctorIso _ j).app
        (SheafOfModules.free (R := ringedToposStructureRingSheaf B S hS
          ⟨yoneda.obj p.val.siteObject, isAlgebraicSpace_yoneda B S hS p.val.siteObject⟩)
          (ULift.{u} (Fin n))) ≪≫
      Stacks.SheafOfModules.freeULiftFinIsoBiproduct O n
    exact (G.mapIso eF).toLinearEquiv.finrank_eq.trans
      ((homModuleFiniteFreeEquiv (Stacks.SheafOfModules.bijective_unitEndRingHom.{u} O hT)
        n).finrank_eq.trans (Module.finrank_fin_fun _))
  · have hz : IsZero ((DerivedCategory.homologyFunctor _ j).obj
        ((DerivedCategory.singleFunctor _ i).obj
          (SheafOfModules.free (R := ringedToposStructureRingSheaf B S hS
            ⟨yoneda.obj p.val.siteObject, isAlgebraicSpace_yoneda B S hS p.val.siteObject⟩)
            (ULift.{u} (Fin n))))) := by
      rcases lt_or_gt_of_ne hj with hlt | hlt
      · exact DerivedCategory.isZero_of_isGE (C := SheafOfModules.{u}
          (ringedToposStructureRingSheaf B S hS
            ⟨yoneda.obj p.val.siteObject, isAlgebraicSpace_yoneda B S hS p.val.siteObject⟩))
          _ i j hlt
      · exact DerivedCategory.isZero_of_isLE (C := SheafOfModules.{u}
          (ringedToposStructureRingSheaf B S hS
            ⟨yoneda.obj p.val.siteObject, isAlgebraicSpace_yoneda B S hS p.val.siteObject⟩))
          _ i j hlt
    have := ModuleCat.subsingleton_of_isZero (G.map_isZero hz)
    exact Module.finrank_zero_of_subsingleton

/-- The morphism of represented algebraic spaces attached to a morphism of étale charts is the
one represented by the underlying morphism of schemes. -/
theorem chartMap_eq_representedSpaceMap {V V' : SmallEtale B S hS X.1} (k : V' ⟶ V) :
    chartMap B S hS X k = representedSpaceMap B S hS ((SmallEtale.toOver B S hS X.1).map k) :=
  rfl

/-- Along a morphism of étale charts `k : V' ⟶ V` whose underlying morphism of schemes maps into
the principal open `D(g)`, the function `g` pulls back to a unit; read through the ring map
induced by the pullback of modules on the endomorphisms of the structure sheaves. -/
theorem isUnit_baseChangeRingHom_of_preimage_basicOpen {V V' : SmallEtale B S hS X.1}
    (k : V' ⟶ V)
    (g : (structureSheaf B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V))
      (isAlgebraicSpace_yoneda B S hS _)).obj.obj
        (op (idChart B S hS ((SmallEtale.toOver B S hS X.1).obj V))))
    (hk : (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map k) ⁻¹ᵁ
      (chartScheme V).basicOpen (show Γ(chartScheme V, ⊤) from g) = ⊤) :
    IsUnit (baseChangeRingHom.{u}
      (C := Modules.{u, u} B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V))
        (isAlgebraicSpace_yoneda B S hS _))
      (D := Modules.{u, u} B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V'))
        (isAlgebraicSpace_yoneda B S hS _))
      (R := (structureSheaf B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V))
        (isAlgebraicSpace_yoneda B S hS _)).obj.obj
          (op (idChart B S hS ((SmallEtale.toOver B S hS X.1).obj V))))
      (R' := (structureSheaf B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V'))
        (isAlgebraicSpace_yoneda B S hS _)).obj.obj
          (op (idChart B S hS ((SmallEtale.toOver B S hS X.1).obj V'))))
      (ρ := Stacks.SheafOfModules.unitEndRingHom.{u}
        (structureSheaf B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V))
          (isAlgebraicSpace_yoneda B S hS _)) (isTerminal_idChart B S hS _))
      (Stacks.SheafOfModules.unitEndRingHom.{u}
        (structureSheaf B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V'))
          (isAlgebraicSpace_yoneda B S hS _)) (isTerminal_idChart B S hS _))
      (Stacks.SheafOfModules.bijective_unitEndRingHom.{u}
        (structureSheaf B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V'))
          (isAlgebraicSpace_yoneda B S hS _)) (isTerminal_idChart B S hS _))
      (modulePullback B S hS
        (representedSpaceMap B S hS ((SmallEtale.toOver B S hS X.1).map k)))
      (hF := modulePullback_additive
        (representedSpaceMap B S hS ((SmallEtale.toOver B S hS X.1).map k)))
      (modulePullbackUnitIso B S hS
        (representedSpaceMap B S hS ((SmallEtale.toOver B S hS X.1).map k))) g) := by
  rw [baseChangeRingHom_representedSpaceMap]
  have h := (Scheme.preimage_basicOpen_top _ _).symm.trans hk
  exact RingedSpace.isUnit_of_isUnit_germ _ ⊤ _ fun z hz =>
    (RingedSpace.mem_basicOpen _ _ z hz).1 (h.ge hz)

/-- **Freeness on a chart from a homotopy equivalence of global sections.** Let `A` be a strictly
perfect model of `E` on an étale chart `V`, and let `k : V' ⟶ V` be a morphism of charts. If the
complex of global sections of `A`, base changed to `V'`, is homotopy equivalent to `𝒪(V')^n`
placed in degree `i`, then `E` is free of rank `n` in degree `i` on `V'`. -/
theorem isFreeOfRankInDegree_of_homotopyEquiv_homModule
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    {V V' : SmallEtale B S hS X.1} (k : V' ⟶ V)
    (A : CochainComplex (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (chartSpace B S hS X V))) ℤ)
    (hA : ∀ j, IsRetractOfFiniteFree (SheafOfModules.unit
      (ringedToposStructureRingSheaf B S hS (chartSpace B S hS X V))) (A.X j))
    (b : ℤ) (hAb : A.IsStrictlyLE b)
    (eA : (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj E ≅
      (DerivedCategory.Q).obj A) (i : ℤ) (n : ℕ)
    (e : HomotopyEquiv
      (((ModuleCat.extendScalars.{u, u, u + 1} (baseChangeRingHom.{u}
        (C := Modules.{u, u} B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V))
          (isAlgebraicSpace_yoneda B S hS _))
        (D := Modules.{u, u} B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V'))
          (isAlgebraicSpace_yoneda B S hS _))
        (ρ := Stacks.SheafOfModules.unitEndRingHom.{u}
          (structureSheaf B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V))
            (isAlgebraicSpace_yoneda B S hS _)) (isTerminal_idChart B S hS _))
        (Stacks.SheafOfModules.unitEndRingHom.{u}
          (structureSheaf B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V'))
            (isAlgebraicSpace_yoneda B S hS _)) (isTerminal_idChart B S hS _))
        (Stacks.SheafOfModules.bijective_unitEndRingHom.{u}
          (structureSheaf B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V'))
            (isAlgebraicSpace_yoneda B S hS _)) (isTerminal_idChart B S hS _))
        (modulePullback B S hS
          (representedSpaceMap B S hS ((SmallEtale.toOver B S hS X.1).map k)))
        (hF := modulePullback_additive
          (representedSpaceMap B S hS ((SmallEtale.toOver B S hS X.1).map k)))
        (modulePullbackUnitIso B S hS
          (representedSpaceMap B S hS
            ((SmallEtale.toOver B S hS X.1).map k))))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          (((homModule _ (Stacks.SheafOfModules.unitEndRingHom.{u}
            (structureSheaf B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V))
              (isAlgebraicSpace_yoneda B S hS _))
                (isTerminal_idChart B S hS _))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj A))
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj
        (ModuleCat.of ((structureSheaf B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V'))
            (isAlgebraicSpace_yoneda B S hS _)).obj.obj
              (op (idChart B S hS ((SmallEtale.toOver B S hS X.1).obj V'))))
          (ULift.{u + 1} (Fin n → (structureSheaf B S hS
            (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V'))
              (isAlgebraicSpace_yoneda B S hS _)).obj.obj
                (op (idChart B S hS ((SmallEtale.toOver B S hS X.1).obj V')))))))) :
    IsFreeOfRankInDegree
      ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V')).obj E) i n := by
  let TV := (SmallEtale.toOver B S hS X.1).obj V
  let TV' := (SmallEtale.toOver B S hS X.1).obj V'
  let ιm : (⟨yoneda.obj TV', isAlgebraicSpace_yoneda B S hS TV'⟩ : AlgebraicSpaces B S hS) ⟶
      ⟨yoneda.obj TV, isAlgebraicSpace_yoneda B S hS TV⟩ :=
    representedSpaceMap B S hS ((SmallEtale.toOver B S hS X.1).map k)
  let OV := structureSheaf B S hS (yoneda.obj TV) (isAlgebraicSpace_yoneda B S hS TV)
  let ρV := Stacks.SheafOfModules.unitEndRingHom.{u} OV (isTerminal_idChart B S hS TV)
  have hρV := Stacks.SheafOfModules.bijective_unitEndRingHom.{u} OV (isTerminal_idChart B S hS TV)
  let OV' := structureSheaf B S hS (yoneda.obj TV') (isAlgebraicSpace_yoneda B S hS TV')
  let ρV' := Stacks.SheafOfModules.unitEndRingHom.{u} OV' (isTerminal_idChart B S hS TV')
  have hρV' := Stacks.SheafOfModules.bijective_unitEndRingHom.{u} OV'
    (isTerminal_idChart B S hS TV')
  let Fk := modulePullback B S hS ιm
  have : Fk.Additive := modulePullback_additive ιm
  let eBC := homModuleBaseChangeComplexIso (ρ := ρV) ρV' hρV' Fk (hF := modulePullback_additive ιm)
    (modulePullbackUnitIso B S hS ιm) hρV A hA
  let G' := homModule _ ρV'
  let Fr := SheafOfModules.free (R := ringedToposStructureRingSheaf B S hS
    ⟨yoneda.obj TV', isAlgebraicSpace_yoneda B S hS TV'⟩) (ULift.{u} (Fin n))
  let eF : ModuleCat.of (OV'.obj.obj (op (idChart B S hS TV')))
      (ULift.{u + 1} (Fin n → OV'.obj.obj (op (idChart B S hS TV')))) ≅ G'.obj Fr :=
    (ULift.moduleEquiv.trans (homModuleFiniteFreeEquiv hρV' n).symm).toModuleIso ≪≫
      G'.mapIso (Stacks.SheafOfModules.freeULiftFinIsoBiproduct OV' n).symm
  let eS := (HomologicalComplex.single _ (ComplexShape.up ℤ) i).mapIso eF ≪≫
    ((HomologicalComplex.singleMapHomologicalComplex G' (ComplexShape.up ℤ) i).app Fr).symm
  have eH := (HomotopyEquiv.ofIso eBC.symm).trans (e.trans (HomotopyEquiv.ofIso eS))
  have hA' : ∀ j, IsRetractOfFiniteFree (SheafOfModules.unit _)
      (((Fk.mapHomologicalComplex (ComplexShape.up ℤ)).obj A).X j) := fun j ↦
    IsRetractOfFiniteFree.map (F := Fk) (modulePullbackUnitIso B S hS ιm) (hA j)
  have hSg : ∀ j, IsRetractOfFiniteFree (SheafOfModules.unit _)
      (((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj Fr).X j) := by
    intro j
    by_cases hj : j = i
    · subst hj
      exact (isRetractOfFiniteFree_biproduct _ n).of_iso
        ((Stacks.SheafOfModules.freeULiftFinIsoBiproduct OV' n).symm ≪≫
          (HomologicalComplex.singleObjXSelf _ _ Fr).symm)
    · exact ⟨0, 0, 0, (HomologicalComplex.isZero_single_obj_X _ i Fr j hj).eq_of_src _ _⟩
  obtain ⟨h⟩ := nonempty_homotopyEquiv_of_homModule hρV' hA' hSg eH
  have := hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS ιm
  obtain ⟨e1⟩ := @nonempty_smallEtaleDerivedModulePullback_obj_Q_iso_modulePullback _ _ _ _
    ⟨yoneda.obj TV, isAlgebraicSpace_yoneda B S hS TV⟩ ιm A b hAb
    (fun j ↦ isFlat_of_isRetractOfFiniteFree B S hS _ (hA j))
  have hcomp : ιm ≫ chartToSpace B S hS X V = chartToSpace B S hS X V' :=
    chartMap_comp_chartToSpace B S hS X k
  exact ⟨n, rfl, ⟨((smallEtaleDerivedModulePullbackCompIso B S hS ιm
      (chartToSpace B S hS X V)).app E ≪≫
        (smallEtaleDerivedModulePullbackCongr B S hS hcomp).app E).symm ≪≫
    (smallEtaleDerivedModulePullback B S hS ιm).mapIso eA ≪≫ e1 ≪≫
    ((DerivedCategory.quotientCompQhIso _).app _).symm ≪≫
    DerivedCategory.Qh.mapIso (HomotopyCategory.isoOfHomotopyEquiv h) ≪≫
    (DerivedCategory.quotientCompQhIso _).app _ ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ _ i).app Fr).symm⟩⟩

/-- `AlgebraicGeometry.Space.hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy` for a source
written as a pair `⟨F, hF⟩`: instance search does not see through the reducible unfolding of such
a source to the projections the general instance is stated with. -/
instance hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy_mkSource
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}
    {Y : AlgebraicSpaces B S hS} (f : (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ Y) :
    (smallEtaleModulePullbackOnHomotopy B S hS f).HasLeftDerivedFunctor
      (smallEtaleModuleQuasiIso B S hS Y) :=
  hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS f

/-- **A perfect complex which is free in one degree at a geometric point is free in that degree
on an étale chart through the image of the point.** Let `E` be perfect on `X`, let `p` be a
geometric point of an algebraic space, and let `c` be a morphism to `X` from the spectrum of the
field of `p` along which `Lc^*E` is free of rank `r` placed in degree `i`. Then the image of `p`
in `X` lies in the image of an étale chart on which `E` is free of rank `r` in degree `i`. -/
theorem pointsMap_mem_singleDegreeFreePoints {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E) (i r : ℤ)
    (p : GeometricPoint B S hS F)
    (c : (⟨yoneda.obj p.val.siteObject, isAlgebraicSpace_yoneda B S hS p.val.siteObject⟩ :
      AlgebraicSpaces B S hS) ⟶ X)
    (hc : IsFreeOfRankInDegree ((smallEtaleDerivedModulePullback B S hS c).obj E) i r) :
    pointsMap B S hS _ c.hom (GeometricPoint.tautological B S hS p).image ∈
      singleDegreeFreePoints B S hS E i r := by
  classical
  let K := p.val.siteObject
  obtain ⟨n, hn, ⟨ec⟩⟩ := hc
  -- the image geometric point and a neighbourhood with a strictly perfect model
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
  -- the pullback of the model to the point is free in degree `i`
  have := hAb
  have : (modulePullback B S hS bm).Additive := modulePullback_additive bm
  have := hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS bm
  obtain ⟨e1⟩ := @nonempty_smallEtaleDerivedModulePullback_obj_Q_iso_modulePullback _ _ _ _
    ⟨yoneda.obj TV, isAlgebraicSpace_yoneda B S hS TV⟩ bm A b hAb
    (fun j ↦ isFlat_of_isRetractOfFiniteFree B S hS _ (hAret j))
  let eQ : (DerivedCategory.Q).obj
      (((modulePullback B S hS bm).mapHomologicalComplex (ComplexShape.up ℤ)).obj A) ≅
      (DerivedCategory.singleFunctor _ i).obj
        (SheafOfModules.free (R := ringedToposStructureRingSheaf B S hS
          ⟨yoneda.obj K, isAlgebraicSpace_yoneda B S hS K⟩) (ULift.{u} (Fin n))) :=
    e1.symm ≪≫ (smallEtaleDerivedModulePullback B S hS bm).mapIso eA.symm ≪≫
      (smallEtaleDerivedModulePullbackCompIso B S hS bm (chartToSpace B S hS X V)).app E ≪≫
      (smallEtaleDerivedModulePullbackCongr B S hS hbm).app E ≪≫ ec
  -- global sections over the chart and over the point
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
  have hdim : ∀ j, Module.finrank (OK.obj.obj (op (idChart B S hS K)))
      ((((ModuleCat.extendScalars.{u, u, u + 1} ψ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L).homology j) = if j = i then n else 0 := fun j ↦
    ((HomologicalComplex.homologyFunctor _ _ j).mapIso ebc).toLinearEquiv.finrank_eq.trans
      (finrank_homology_homModule_of_Q_iso_single B S hS p _ i n eQ j)
  obtain ⟨g, hg, ⟨eg⟩⟩ :=
    StacksDraft.Perfect.exists_away_homotopyEquiv_single_of_finrank_homology.{u, u + 1} ψ L a b
      (fun j ↦ (homModule_finite_projective hρV (hAret j)).1)
      (fun j ↦ (homModule_finite_projective hρV (hAret j)).2) i n hdim
  -- the principal open `D(g)` of the chart
  have hgu : IsUnit (ψ g) := isUnit_iff_ne_zero.2 hg
  let g' : Γ(chartScheme V, ⊤) := g
  let W : (chartScheme V).Opens := (chartScheme V).basicOpen g'
  have hpre : (BigFppfOver.toScheme B S hS).map N.point ⁻¹ᵁ W = ⊤ :=
    (Scheme.preimage_basicOpen_top _ g').trans
      ((congrArg _ (hψ g).symm).trans (Scheme.basicOpen_of_isUnit _ hgu))
  have hw : chartPoint B S hS X.1 N ∈ W := by
    have : IsLocalRing.closedPoint p.val.carrier ∈
        (BigFppfOver.toScheme B S hS).map N.point ⁻¹ᵁ W :=
      hpre ▸ trivial
    exact this
  let N' := chartOpenNeighborhood B S hS N W hw
  let ι := (chartOpenNeighborhoodHom B S hS N W hw).hom
  let TV' := (SmallEtale.toOver B S hS X.1).obj N'.chart
  let ιm : (⟨yoneda.obj TV', isAlgebraicSpace_yoneda B S hS TV'⟩ : AlgebraicSpaces B S hS) ⟶
      ⟨yoneda.obj TV, isAlgebraicSpace_yoneda B S hS TV⟩ :=
    representedSpaceMap B S hS ((SmallEtale.toOver B S hS X.1).map ι)
  have hk : (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map ι) ⁻¹ᵁ
      (chartScheme V).basicOpen (show Γ(chartScheme V, ⊤) from g) = ⊤ :=
    W.ι_preimage_self
  obtain ⟨eθ⟩ := StacksDraft.Perfect.nonempty_homotopyEquiv_single_of_isUnit.{u, u + 1} L g i n eg
    _ (isUnit_baseChangeRingHom_of_preimage_basicOpen B S hS ι g hk)
  have hfree := isFreeOfRankInDegree_of_homotopyEquiv_homModule B S hS E ι A hAret b hAb eA i n eθ
  exact ⟨N'.chart, ⟨_, chartFieldValuedPoint_pointsMap N'⟩, hn ▸ hfree⟩

end AlgebraicGeometry.Space

end
