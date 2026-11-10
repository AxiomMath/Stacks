module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.BottomRankChartModel
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.BottomRankFitting
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.BottomRankLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SingleDegreeFreeGeometricPoint
public import StacksFrontier.CategoryTheory.Preadditive.HomModuleComplexLift
public import StacksFrontier.Homology.Perfect.FibreVanishingBelowOverField

/-!
# Bottom models on affine étale charts

Let `E` be a perfect object of `D(𝒪_X)` for an algebraic space `X`, and suppose that
`H^j(Lf^*E) = 0` for every morphism `f : Y → X` and every `j < a`. Then every point of `X` lies
in the image of an affine étale chart `V` on which the derived restriction of `E` has a bottom
model in degree `a` (`AlgebraicGeometry.Space.BottomModel`): a bounded complex of finite free
modules, zero below degree `a`, whose differential out of degree `a` is a matrix over `𝒪(V)`.

The proof is [stacks 0BYP] on the ring of a chart carrying a strictly perfect model: the fibre
of the complex of global sections at the point has no cohomology below `a`, so the complex is
homotopy equivalent on a principal open `D(g)` to a bounded complex of finite free modules
concentrated in degrees `≥ a`, which lifts to a complex of free sheaves.

## Main results

* `AlgebraicGeometry.Space.isZero_homology_homModule_of_isZero_homology`: on the spectrum of
  the field of a geometric point, global sections commute with cohomology.
* `AlgebraicGeometry.Space.BottomModel.exists_of_iso_free`: a bounded complex of free modules
  zero below `a` representing `K` is a bottom model.
* `AlgebraicGeometry.Space.nonempty_bottomModel_of_homotopyEquiv_homModule`: a bottom model on
  a chart from a homotopy equivalence of complexes of global sections.
* `AlgebraicGeometry.Space.exists_smallEtale_bottomModel`: the main statement above.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A bounded complex of free modules zero below `a` representing `K` is a bottom model**,
the matrix of its differential out of degree `a` being read off through a surjection
`ψ : R → End 𝒪_Y`. -/
theorem BottomModel.exists_of_iso_free {Y : AlgebraicSpaces B S hS}
    {K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))} {a b : ℤ}
    {R : Type u} [CommRing R] (ψ : R →+* End (ringedToposUnit Y)) (hψ : Function.Surjective ψ)
    (d : ℤ → ℕ) (P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ)
    (eX : ∀ i, P.X i ≅ freeObjMatrixKernelSplitting (ringedToposUnit Y) (d i))
    (hPa : P.IsStrictlyGE a) (hPb : P.IsStrictlyLE b) (e : K ≅ (DerivedCategory.Q).obj P) :
    ∃ M : Matrix (Fin (d (a + 1))) (Fin (d a)) R, Nonempty (BottomModel K a ψ M) := by
  obtain ⟨M, hM⟩ := exists_matrixHom_eq_matrixKernelSplitting hψ
    ((eX a).inv ≫ P.d a (a + 1) ≫ (eX (a + 1)).hom)
  exact ⟨M, ⟨{
    P := P
    retract := fun j => (isRetractOfFiniteFree_biproduct _ (d j)).of_iso (eX j).symm
    b := b
    isStrictlyLE := hPb
    isStrictlyGE := hPa
    e₀ := eX a
    e₁ := eX (a + 1)
    hd := hM.symm
    iso := e }⟩⟩

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X : AlgebraicSpaces B S hS}

/-- **On the spectrum of the field of a geometric point, global sections commute with
cohomology**: if the cohomology in degree `j` of a complex `K` of modules vanishes, so does the
cohomology in degree `j` of the complex of global sections `Hom(𝒪, K)`. -/
theorem isZero_homology_homModule_of_isZero_homology {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : GeometricPoint B S hS F)
    (K : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj p.val.siteObject, isAlgebraicSpace_yoneda B S hS p.val.siteObject⟩)) ℤ)
    (j : ℤ) (h : IsZero ((DerivedCategory.homologyFunctor _ j).obj ((DerivedCategory.Q).obj K))) :
    IsZero ((((homModule (SheafOfModules.unit _) (Stacks.SheafOfModules.unitEndRingHom.{u}
        (structureSheaf B S hS (yoneda.obj p.val.siteObject)
          (isAlgebraicSpace_yoneda B S hS p.val.siteObject))
        (isTerminal_idChart B S hS p.val.siteObject))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K).homology j) := by
  let O := structureSheaf B S hS (yoneda.obj p.val.siteObject)
    (isAlgebraicSpace_yoneda B S hS p.val.siteObject)
  let hT := isTerminal_idChart B S hS p.val.siteObject
  have :=
    Stacks.SheafOfModules.projective_unit_of_mem O hT
      (fun _ hR ↦ idChart_mem_of_mem_geometricPoint B S hS p hR)
  let G := homModule _ (Stacks.SheafOfModules.unitEndRingHom.{u} O hT)
  exact (G.map_isZero (h.of_iso ((DerivedCategory.homologyFunctorFactors _ j).app K).symm)).of_iso
    ((StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso G
      (ComplexShape.up ℤ) j).app K)

/-- A complex whose terms vanish wherever those of a complex bounded in `[a, b]` do is bounded in
`[a, b]`. -/
private theorem isStrictlyGE_and_isStrictlyLE_of_isZero_X {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] {K : CochainComplex C ℤ} {L : CochainComplex D ℤ}
    (h : ∀ i, IsZero (K.X i) → IsZero (L.X i)) {a b : ℤ} (hKa : K.IsStrictlyGE a)
    (hKb : K.IsStrictlyLE b) : L.IsStrictlyGE a ∧ L.IsStrictlyLE b :=
  ⟨(CochainComplex.isStrictlyGE_iff L a).2 fun j hj => h j (K.isZero_of_isStrictlyGE a j hj),
    (CochainComplex.isStrictlyLE_iff L b).2 fun j hj => h j (K.isZero_of_isStrictlyLE b j hj)⟩

/-- **A bottom model on a chart from a homotopy equivalence of global sections.** Let `A` be a
strictly perfect model of `E` on an étale chart `V`, and let `k : V' ⟶ V` be a morphism of
charts. If the complex of global sections of `A`, base changed to `V'`, is homotopy equivalent to
a complex of finite free `𝒪(V')`-modules concentrated in degrees `[a, b]`, then `E` has a bottom
model in degree `a` on `V'`. -/
theorem nonempty_bottomModel_of_homotopyEquiv_homModule
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    {V V' : SmallEtale B S hS X.1} (k : V' ⟶ V)
    (A : CochainComplex (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (chartSpace B S hS X V))) ℤ)
    (hA : ∀ j, IsRetractOfFiniteFree (SheafOfModules.unit
      (ringedToposStructureRingSheaf B S hS (chartSpace B S hS X V))) (A.X j))
    (b₀ : ℤ) (hAb : A.IsStrictlyLE b₀)
    (eA : (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj E ≅
      (DerivedCategory.Q).obj A) (a b : ℤ) (d : ℤ → ℕ)
    (P : CochainComplex (ModuleCat.{u + 1} ((structureSheaf B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V'))
        (isAlgebraicSpace_yoneda B S hS _)).obj.obj
          (op (idChart B S hS ((SmallEtale.toOver B S hS X.1).obj V'))))) ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    (hPX : ∀ i, Nonempty (P.X i ≅ ModuleCat.of ((structureSheaf B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V'))
        (isAlgebraicSpace_yoneda B S hS _)).obj.obj
          (op (idChart B S hS ((SmallEtale.toOver B S hS X.1).obj V'))))
      (ULift.{u + 1} (Fin (d i) → (structureSheaf B S hS
        (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V'))
          (isAlgebraicSpace_yoneda B S hS _)).obj.obj
            (op (idChart B S hS ((SmallEtale.toOver B S hS X.1).obj V')))))))
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
            (ComplexShape.up ℤ)).obj A)) P) :
    ∃ (m n : ℕ) (M : Matrix (Fin m) (Fin n) ((structureSheaf B S hS
        (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V'))
          (isAlgebraicSpace_yoneda B S hS _)).obj.obj
            (op (idChart B S hS ((SmallEtale.toOver B S hS X.1).obj V'))))),
      Nonempty (BottomModel
        (Y := ⟨yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V'),
          isAlgebraicSpace_yoneda B S hS _⟩)
        ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V')).obj E) a
        (Stacks.SheafOfModules.unitEndRingHom.{u}
          (structureSheaf B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V'))
            (isAlgebraicSpace_yoneda B S hS _)) (isTerminal_idChart B S hS _)) M) := by
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
  have eBC := homModuleBaseChangeComplexIso (ρ := ρV) ρV' hρV' Fk (hF := modulePullback_additive ιm)
    (modulePullbackUnitIso B S hS ιm) hρV A hA
  let O' := SheafOfModules.unit
    (ringedToposStructureRingSheaf B S hS ⟨yoneda.obj TV', isAlgebraicSpace_yoneda B S hS TV'⟩)
  have eF : ∀ i, (homModule O' ρV').obj (freeObjMatrixKernelSplitting O' (d i)) ≅ P.X i := fun i =>
    ((homModuleFiniteFreeEquiv hρV' (d i)).trans ULift.moduleEquiv.symm).toModuleIso ≪≫
      (hPX i).some.symm
  have hfree : ∀ i, IsRetractOfFiniteFree O' (freeObjMatrixKernelSplitting O' (d i)) := fun i =>
    isRetractOfFiniteFree_biproduct O' (d i)
  let Fr := homModuleLiftComplex hρV' P (fun i => freeObjMatrixKernelSplitting O' (d i)) hfree eF
  obtain ⟨hFrGE, hFrLE⟩ := isStrictlyGE_and_isStrictlyLE_of_isZero_X
    (fun _ => isZero_homModuleLiftComplex_X hρV' P _ hfree eF) (K := P) ‹_› ‹_›
  have eH := (HomotopyEquiv.ofIso eBC.symm).trans
    (e.trans (HomotopyEquiv.ofIso (homModuleLiftComplexIso hρV' P _ hfree eF).symm))
  have hA' : ∀ j, IsRetractOfFiniteFree (SheafOfModules.unit _)
      (((Fk.mapHomologicalComplex (ComplexShape.up ℤ)).obj A).X j) := fun j ↦
    IsRetractOfFiniteFree.map (F := Fk) (modulePullbackUnitIso B S hS ιm) (hA j)
  obtain ⟨h⟩ := nonempty_homotopyEquiv_of_homModule hρV' hA' hfree eH
  have e1 := Nonempty.some <|
    @nonempty_smallEtaleDerivedModulePullback_obj_Q_iso_modulePullback _ _ _ _
    ⟨yoneda.obj TV, isAlgebraicSpace_yoneda B S hS TV⟩ ιm A b₀ hAb
    (fun j ↦ isFlat_of_isRetractOfFiniteFree B S hS _ (hA j))
  have hcomp : ιm ≫ chartToSpace B S hS X V = chartToSpace B S hS X V' :=
    chartMap_comp_chartToSpace B S hS X k
  have eK : (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V')).obj E ≅
      (DerivedCategory.Q).obj Fr :=
    ((smallEtaleDerivedModulePullbackCompIso B S hS ιm (chartToSpace B S hS X V)).app E ≪≫
        (smallEtaleDerivedModulePullbackCongr B S hS hcomp).app E).symm ≪≫
      (smallEtaleDerivedModulePullback B S hS ιm).mapIso eA ≪≫ e1 ≪≫
      ((DerivedCategory.quotientCompQhIso _).app _).symm ≪≫
      DerivedCategory.Qh.mapIso (HomotopyCategory.isoOfHomotopyEquiv h) ≪≫
      (DerivedCategory.quotientCompQhIso _).app _
  obtain ⟨M, hM⟩ := BottomModel.exists_of_iso_free
    (Y := ⟨yoneda.obj TV', isAlgebraicSpace_yoneda B S hS TV'⟩) ρV' hρV'.2 d Fr
    (fun i => Iso.refl _) hFrGE hFrLE eK
  exact ⟨_, _, M, by convert hM using 3⟩

set_option maxHeartbeats 800000 in
-- the statement nests several base changes of sheaves of modules, and the closing
-- `convert h3 using 6 <;> rfl` unifies them
/-- **No fibre cohomology below `a` at a geometric point.** Let `A` be a strictly perfect model of
`E` on the chart of a small étale neighbourhood `N` of a geometric point. If `H^j(Lf^*E) = 0` for
all `f` and all `j < a`, then the complex of global sections of `A`, base changed to the field of
the geometric point, has no cohomology in degrees `j < a`. -/
theorem isZero_homology_baseChange_homModule
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) (a : ℤ)
    (hvan : ∀ (Y : AlgebraicSpaces B S hS) (f : Y ⟶ X) (j : ℤ), j < a →
      IsZero (BottomRankLocus.pullbackHomology E j f))
    (x : GeometricPoint B S hS X.1) (N : SmallEtaleNeighborhood x)
    (A : CochainComplex (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (chartSpace B S hS X N.chart))) ℤ)
    (hAret : ∀ j, IsRetractOfFiniteFree (SheafOfModules.unit
      (ringedToposStructureRingSheaf B S hS (chartSpace B S hS X N.chart))) (A.X j))
    (b₀ : ℤ) (hAb : A.IsStrictlyLE b₀)
    (eA : (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X N.chart)).obj E ≅
      (DerivedCategory.Q).obj A) (j : ℤ) (hj : j < a) :
    IsZero ((((ModuleCat.extendScalars.{u, u, u + 1} (baseChangeRingHom.{u}
        (C := Modules.{u, u} B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj N.chart))
          (isAlgebraicSpace_yoneda B S hS _))
        (D := Modules.{u, u} B S hS (yoneda.obj x.val.siteObject)
          (isAlgebraicSpace_yoneda B S hS _))
        (ρ := Stacks.SheafOfModules.unitEndRingHom.{u}
          (structureSheaf B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj N.chart))
            (isAlgebraicSpace_yoneda B S hS _)) (isTerminal_idChart B S hS _))
        (Stacks.SheafOfModules.unitEndRingHom.{u}
          (structureSheaf B S hS (yoneda.obj x.val.siteObject)
            (isAlgebraicSpace_yoneda B S hS _)) (isTerminal_idChart B S hS _))
        (Stacks.SheafOfModules.bijective_unitEndRingHom.{u}
          (structureSheaf B S hS (yoneda.obj x.val.siteObject)
            (isAlgebraicSpace_yoneda B S hS _)) (isTerminal_idChart B S hS _))
        (modulePullback B S hS
          (representedSpaceMap B S hS (T := (SmallEtale.toOver B S hS X.1).obj N.chart) N.point))
        (hF := modulePullback_additive
          (representedSpaceMap B S hS (T := (SmallEtale.toOver B S hS X.1).obj N.chart) N.point))
        (modulePullbackUnitIso B S hS
          (representedSpaceMap B S hS (T := (SmallEtale.toOver B S hS X.1).obj N.chart)
            N.point)))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((homModule _ (Stacks.SheafOfModules.unitEndRingHom.{u}
            (structureSheaf B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj N.chart))
              (isAlgebraicSpace_yoneda B S hS _))
                (isTerminal_idChart B S hS _))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj A)).homology j) := by
  let K := x.val.siteObject
  let V := N.chart
  let TV := (SmallEtale.toOver B S hS X.1).obj V
  let bm : (⟨yoneda.obj K, isAlgebraicSpace_yoneda B S hS K⟩ : AlgebraicSpaces B S hS) ⟶
      ⟨yoneda.obj TV, isAlgebraicSpace_yoneda B S hS TV⟩ :=
    representedSpaceMap B S hS N.point
  have : (modulePullback B S hS bm).Additive := modulePullback_additive bm
  have e1 := Nonempty.some <|
    @nonempty_smallEtaleDerivedModulePullback_obj_Q_iso_modulePullback _ _ _ _
    ⟨yoneda.obj TV, isAlgebraicSpace_yoneda B S hS TV⟩ bm A b₀ hAb
    (fun j ↦ isFlat_of_isRetractOfFiniteFree B S hS _ (hAret j))
  have eQ : (DerivedCategory.Q).obj
      (((modulePullback B S hS bm).mapHomologicalComplex (ComplexShape.up ℤ)).obj A) ≅
      (smallEtaleDerivedModulePullback B S hS (bm ≫ chartToSpace B S hS X V)).obj E :=
    e1.symm ≪≫ (smallEtaleDerivedModulePullback B S hS bm).mapIso eA.symm ≪≫
      (smallEtaleDerivedModulePullbackCompIso B S hS bm (chartToSpace B S hS X V)).app E
  let OV := structureSheaf B S hS (yoneda.obj TV) (isAlgebraicSpace_yoneda B S hS TV)
  have hρV := Stacks.SheafOfModules.bijective_unitEndRingHom.{u} OV (isTerminal_idChart B S hS TV)
  let OK := structureSheaf B S hS (yoneda.obj K) (isAlgebraicSpace_yoneda B S hS K)
  let ρK := Stacks.SheafOfModules.unitEndRingHom.{u} OK (isTerminal_idChart B S hS K)
  have hρK := Stacks.SheafOfModules.bijective_unitEndRingHom.{u} OK (isTerminal_idChart B S hS K)
  have h0 : IsZero (BottomRankLocus.pullbackHomology E j (bm ≫ chartToSpace B S hS X V)) :=
    hvan _ _ j hj
  have h1 : IsZero ((DerivedCategory.homologyFunctor _ j).obj ((DerivedCategory.Q).obj
      (((modulePullback B S hS bm).mapHomologicalComplex (ComplexShape.up ℤ)).obj A))) :=
    h0.of_iso ((DerivedCategory.homologyFunctor _ j).mapIso eQ)
  have h2 : IsZero ((((homModule _ ρK).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((modulePullback B S hS bm).mapHomologicalComplex (ComplexShape.up ℤ)).obj A)).homology j) :=
    isZero_homology_homModule_of_isZero_homology B S hS x _ j h1
  have h3 := h2.of_iso (HomologicalComplex.homologyMapIso
    (homModuleBaseChangeComplexIso ρK hρK (modulePullback B S hS bm)
      (hF := modulePullback_additive bm) (modulePullbackUnitIso B S hS bm) hρV A hAret) j)
  convert h3 using 6 <;> rfl

/-- **Bottom models on a principal open of a neighbourhood.** Let `A` be a strictly perfect model
of `E` on the chart of a small étale neighbourhood `N` of a geometric point, and let `g` be a
function on the chart which is a unit at the point. If the complex of global sections of `A` is
homotopy equivalent, after base change to every algebra in which `g` is a unit, to a complex of
finite free modules concentrated in degrees `[a, b]` of given ranks, then the image of the point
lies in the image of an affine étale chart on which `E` has a bottom model in degree `a`. -/
theorem exists_bottomModel_of_isUnit
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) (a : ℤ)
    (x : GeometricPoint B S hS X.1) (N : SmallEtaleNeighborhood x)
    [IsAffine (chartScheme N.chart)]
    (A : CochainComplex (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (chartSpace B S hS X N.chart))) ℤ)
    (hAret : ∀ j, IsRetractOfFiniteFree (SheafOfModules.unit
      (ringedToposStructureRingSheaf B S hS (chartSpace B S hS X N.chart))) (A.X j))
    (b₀ : ℤ) (hAb : A.IsStrictlyLE b₀)
    (eA : (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X N.chart)).obj E ≅
      (DerivedCategory.Q).obj A)
    (g : Γ(chartScheme N.chart, ⊤))
    (hg : IsUnit (((BigFppfOver.toScheme B S hS).map N.point).appTop g)) (d : ℤ → ℕ) (b : ℤ)
    (hcont : ∀ {R'' : Type u} [CommRing R'']
      (θ : (structureSheaf B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj N.chart))
        (isAlgebraicSpace_yoneda B S hS _)).obj.obj
          (op (idChart B S hS ((SmallEtale.toOver B S hS X.1).obj N.chart))) →+* R''),
      IsUnit (θ g) → ∃ P'' : CochainComplex (ModuleCat.{u + 1} R'') ℤ,
        P''.IsStrictlyGE a ∧ P''.IsStrictlyLE b ∧
        (∀ i, Nonempty (P''.X i ≅ ModuleCat.of R'' (ULift.{u + 1} (Fin (d i) → R'')))) ∧
        Nonempty (HomotopyEquiv
          (((ModuleCat.extendScalars.{u, u, u + 1} θ).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
            (((homModule _ (Stacks.SheafOfModules.unitEndRingHom.{u}
              (structureSheaf B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj N.chart))
                (isAlgebraicSpace_yoneda B S hS _))
                  (isTerminal_idChart B S hS _))).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj A)) P'')) :
    ∃ V : SmallEtale B S hS X.1,
      x.image ∈ Set.range (pointsMap B S hS (yoneda.obj V.1.left) V.1.hom) ∧
      IsAffine (chartScheme V) ∧
      ∃ (m n : ℕ) (M : Matrix (Fin m) (Fin n) Γ(chartScheme V, ⊤)),
        Nonempty (BottomModel
          (Y := ⟨yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V),
            isAlgebraicSpace_yoneda B S hS _⟩)
          ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj E) a
          (Stacks.SheafOfModules.unitEndRingHom.{u}
            (structureSheaf B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V))
              (isAlgebraicSpace_yoneda B S hS _)) (isTerminal_idChart B S hS _)) M) := by
  let W : (chartScheme N.chart).Opens := (chartScheme N.chart).basicOpen g
  have hpre : (BigFppfOver.toScheme B S hS).map N.point ⁻¹ᵁ W = ⊤ :=
    (Scheme.preimage_basicOpen_top _ g).trans (Scheme.basicOpen_of_isUnit _ hg)
  have hw : chartPoint B S hS X.1 N ∈ W :=
    show IsLocalRing.closedPoint x.val.carrier ∈ (BigFppfOver.toScheme B S hS).map N.point ⁻¹ᵁ W
      from hpre ▸ trivial
  let N' := chartOpenNeighborhood B S hS N W hw
  let ι := (chartOpenNeighborhoodHom B S hS N W hw).hom
  have hk : (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map ι) ⁻¹ᵁ
      (chartScheme N.chart).basicOpen g = ⊤ :=
    W.ι_preimage_self
  obtain ⟨P'', hP''a, hP''b, hP''X, he''⟩ :=
    hcont _ (isUnit_baseChangeRingHom_of_preimage_basicOpen B S hS ι g hk)
  obtain ⟨m, n, M, hM⟩ :=
    nonempty_bottomModel_of_homotopyEquiv_homModule B S hS E ι A hAret b₀ hAb eA a b d P''
      hP''X he''.some
  have haff : IsAffineOpen W := (isAffineOpen_top (chartScheme N.chart)).basicOpen g
  refine ⟨N'.chart, ⟨_, chartFieldValuedPoint_pointsMap N'⟩, haff, m, n, M, ?_⟩
  convert hM using 3

/-- **Bottom models near a geometric point.** Let `N` be a small étale neighbourhood of a
geometric point of `X` whose chart is affine and carries a strictly perfect model of `E`. If
`H^j(Lf^*E) = 0` for all `f` and all `j < a`, then the image of the geometric point lies in the
image of an affine étale chart on which `E` has a bottom model in degree `a`. -/
theorem exists_bottomModel_of_smallEtaleNeighborhood
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) (a : ℤ)
    (hvan : ∀ (Y : AlgebraicSpaces B S hS) (f : Y ⟶ X) (j : ℤ), j < a →
      IsZero (BottomRankLocus.pullbackHomology E j f))
    (x : GeometricPoint B S hS X.1) (N : SmallEtaleNeighborhood x)
    [IsAffine (chartScheme N.chart)]
    (A : CochainComplex (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (chartSpace B S hS X N.chart))) ℤ)
    (hAret : ∀ j, IsRetractOfFiniteFree (SheafOfModules.unit
      (ringedToposStructureRingSheaf B S hS (chartSpace B S hS X N.chart))) (A.X j))
    (a₀ b₀ : ℤ) (hAa : A.IsStrictlyGE a₀) (hAb : A.IsStrictlyLE b₀)
    (eA : (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X N.chart)).obj E ≅
      (DerivedCategory.Q).obj A) :
    ∃ V : SmallEtale B S hS X.1,
      x.image ∈ Set.range (pointsMap B S hS (yoneda.obj V.1.left) V.1.hom) ∧
      IsAffine (chartScheme V) ∧
      ∃ (m n : ℕ) (M : Matrix (Fin m) (Fin n) Γ(chartScheme V, ⊤)),
        Nonempty (BottomModel
          (Y := ⟨yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V),
            isAlgebraicSpace_yoneda B S hS _⟩)
          ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj E) a
          (Stacks.SheafOfModules.unitEndRingHom.{u}
            (structureSheaf B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V))
              (isAlgebraicSpace_yoneda B S hS _)) (isTerminal_idChart B S hS _)) M) := by
  let K := x.val.siteObject
  let TV := (SmallEtale.toOver B S hS X.1).obj N.chart
  let OV := structureSheaf B S hS (yoneda.obj TV) (isAlgebraicSpace_yoneda B S hS TV)
  let ρV := Stacks.SheafOfModules.unitEndRingHom.{u} OV (isTerminal_idChart B S hS TV)
  have hρV := Stacks.SheafOfModules.bijective_unitEndRingHom.{u} OV (isTerminal_idChart B S hS TV)
  let OK := structureSheaf B S hS (yoneda.obj K) (isAlgebraicSpace_yoneda B S hS K)
  let ρK := Stacks.SheafOfModules.unitEndRingHom.{u} OK (isTerminal_idChart B S hS K)
  have hρK := Stacks.SheafOfModules.bijective_unitEndRingHom.{u} OK (isTerminal_idChart B S hS K)
  let L := ((homModule _ ρV).mapHomologicalComplex (ComplexShape.up ℤ)).obj A
  obtain ⟨_, _⟩ := isStrictlyGE_and_isStrictlyLE_of_isZero_X (K := A) (L := L)
    (fun _ => (homModule _ ρV).map_isZero) hAa hAb
  let ψ := repTheta (T := K) (U := TV) N.point
  have hz := isZero_homology_baseChange_homModule B S hS E a hvan x N A hAret b₀ hAb eA
  let : Field (OK.obj.obj (op (idChart B S hS K))) :=
    (isField_structureSheaf_idChart B S hS x.val).toField
  obtain ⟨g, hg, d, b, hcont⟩ :=
    StacksDraft.Perfect.exists_homotopyEquiv_free_of_isZero_homology_lt.{u, u + 1} ψ L a₀ b₀
      (fun j ↦ (homModule_finite_projective hρV (hAret j)).1)
      (fun j ↦ (homModule_finite_projective hρV (hAret j)).2) a hz
  have hgu : IsUnit (((BigFppfOver.toScheme B S hS).map N.point).appTop g) := by
    have h1 : IsUnit (repTheta (T := K) (U := TV) N.point g) := isUnit_iff_ne_zero.2 hg
    rwa [repTheta_apply] at h1
  exact exists_bottomModel_of_isUnit B S hS E a x N A hAret b₀ hAb eA g hgu d b hcont

/-- **Bottom models on affine étale charts.** Let `E` be a perfect object of `D(𝒪_X)` such that
`H^j(Lf^*E) = 0` for every morphism `f : Y → X` and every `j < a`. Then every point of `X` lies in
the image of an affine étale chart `V` on which `E` has a bottom model in degree `a`: a bounded
complex of finite free modules zero below `a` whose differential `𝒪^n ⟶ 𝒪^m` out of degree `a`
is a matrix over `𝒪(V)`. -/
theorem exists_smallEtale_bottomModel
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E) (a : ℤ)
    (hvan : ∀ (Y : AlgebraicSpaces B S hS) (f : Y ⟶ X) (j : ℤ), j < a →
      IsZero (BottomRankLocus.pullbackHomology E j f))
    (x : points B S hS X.1) :
    ∃ V : SmallEtale B S hS X.1,
      x ∈ Set.range (pointsMap B S hS (yoneda.obj V.1.left) V.1.hom) ∧
      IsAffine (chartScheme V) ∧
      ∃ (m n : ℕ) (M : Matrix (Fin m) (Fin n) Γ(chartScheme V, ⊤)),
        Nonempty (BottomModel
          (Y := ⟨yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V),
            isAlgebraicSpace_yoneda B S hS _⟩)
          ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj E) a
          (Stacks.SheafOfModules.unitEndRingHom.{u}
            (structureSheaf B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V))
              (isAlgebraicSpace_yoneda B S hS _)) (isTerminal_idChart B S hS _)) M) := by
  obtain ⟨x, rfl⟩ := (geometricPoints_large_enough B S hS _ _ X.2 X.2).1 x
  obtain ⟨N₀, hN₀⟩ := exists_smallEtaleNeighborhood_hasStrictlyPerfectModel B S hS E hE x
  obtain ⟨W₀, hW₀, hxW₀, -⟩ := exists_isAffineOpen_mem_and_subset
    (show chartPoint B S hS X.1 N₀ ∈ (⊤ : (chartScheme N₀.chart).Opens) from trivial)
  let N₁ := chartOpenNeighborhood B S hS N₀ W₀ hxW₀
  obtain ⟨A, hAret, ⟨a₀, b₀, hAa, hAb⟩, ⟨eA⟩⟩ :=
    hN₀.chartRestriction (chartOpenNeighborhoodHom B S hS N₀ W₀ hxW₀).hom
  have : IsAffine (chartScheme N₁.chart) := hW₀
  exact exists_bottomModel_of_smallEtaleNeighborhood B S hS E a hvan x N₁ A hAret a₀ b₀ hAa hAb eA

end AlgebraicGeometry.Space

end
