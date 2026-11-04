module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeModuleBiproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeOnSiteChartCover
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatDerivedPushforwardFibreSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperFlatDerivedPushforwardFieldFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SingleDegreeFreeGeometricPointVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SingleDegreeRankOpenSubspaceExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedIsoLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackTopDegree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OverFiniteFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionColimits

/-!
# `Rf_*𝒪_X` in degrees zero and one

Let `f : X ⟶ Y` be a proper, flat morphism of finite presentation of algebraic spaces such that
`k = H⁰(X_k, 𝒪_{X_k})` for every morphism `Spec k ⟶ Y` from the spectrum of a field, and such that
the cohomology `Hʲ(X_k, 𝒪_{X_k})` of every such fibre vanishes in degrees `j ≥ 2`. This is the
situation of a family of curves in the proof of Stacks 0E1J. Then:

* étale locally on `Y`, `Rf_*𝒪_X ≅ 𝒪_Y ⊕ P` with `P` étale locally free of finite rank placed in
  degree `1` (`AlgebraicGeometry.Space.exists_coversTop_derivedModulePushforward_iso_biprod`);
* `Rf_*𝒪_X` has no cohomology above degree `1`
  (`AlgebraicGeometry.Space.isLE_derivedModulePushforward_structureModule_one`);
* `R¹f_*𝒪_X = H¹(Rf_*𝒪_X)` is finite locally free
  (`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_homology_one_derivedModulePushforward`);
* its formation commutes with arbitrary base change
  (`AlgebraicGeometry.Space.nonempty_modulePullback_homology_one_derivedModulePushforward_iso`).

This is the argument of the source's proof of Stacks 0E1J: by Stacks 0E6B (b) we have
`Rf_*𝒪_X = 𝒪_Y ⊕ P` étale locally with `P` perfect, represented by a strictly perfect complex in
degrees `≥ 1`; by cohomology and base change (Stacks 0CTM) the derived fibre of `P` at a geometric
point has the cohomology `Hʲ(X_k, 𝒪)` in degrees `j ≥ 1`, hence is concentrated in degree `1`; so
`P` is free placed in degree `1` near every geometric point (the local structure of a perfect
complex with a fibre in one degree, Stacks 0BCD). The base change statement is the top-degree
case of right t-exactness of `Lg^*` (Stacks 0EX3 (c)) together with Stacks 0CTM.

## References

* [Stacks Project, Tag 0E1J](https://stacks.math.columbia.edu/tag/0E1J)
* [Stacks Project, Tag 0E6B](https://stacks.math.columbia.edu/tag/0E6B)
* [Stacks Project, Tag 0CTM](https://stacks.math.columbia.edu/tag/0CTM)
* [Stacks Project, Tag 0BCD](https://stacks.math.columbia.edu/tag/0BCD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

-- global `HasDerivedCategory` instances in scope here (`Homology/DerivedCategory/LocallySmall` and
-- others) compete with the standard model in which the derived functors used here are stated
attribute [-instance] AlgebraicGeometry.RingedSpace.hasDerivedCategoryOXMod
  Stacks.ModulesOnACategory.QuasiCoherentEquivalence.derivedPresheafCategory
  AlgebraicGeometry.SmallEtale.hasDerivedCategory_smallEtaleRingedSite
  Stacks.DerivedQCoh.hasDerivedCategoryQuasicoherent

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives
attribute [local instance] isGrothendieckAbelian_modules

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Finite free modules -/

/-- **A free module of rank `n` is finite locally free of rank `n`** (Stacks 0409): over every
object of the small étale site it is the coproduct of `n` copies of the structure sheaf, the
restriction to a slice preserving finite coproducts. -/
theorem isFiniteLocallyFreeOfRank_free_ulift_fin {Z : AlgebraicSpaces B S hS} (n : ℕ) :
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS Z.1 Z.2)
      (SheafOfModules.free (R := ringedToposStructureRingSheaf B S hS Z) (ULift.{u} (Fin n)))
      n := by
  let R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O
  refine RingedSite.IsFiniteLocallyFreeOfRank.of_iso _ _
    (Stacks.SheafOfModules.freeULiftFinIsoBiproduct (smallEtaleRingedSite B S hS Z.1 Z.2).O n).symm
    ?_
  refine (RingedSite.isFiniteLocallyFreeOfRank_iff_exists_cover_isColimit _ _ n).2
    ⟨ULift.{u + 1} (smallEtaleRingedSite B S hS Z.1 Z.2).C, fun i => i.down,
      Stacks.SheafOfModules.coversTop_ulift_self _, fun i => ⟨fun k =>
        (SheafOfModules.overFunctor R i.down).map
          (biproduct.ι (fun _ : Fin n => SheafOfModules.unit R) k), ⟨?_⟩⟩⟩
  have : PreservesColimit (Discrete.functor (fun _ : Fin n => SheafOfModules.unit R))
      (SheafOfModules.overFunctor.{u} R i.down) :=
    preservesCoproduct_of_preservesBiproduct _
  exact isColimitCofanMkObjOfIsColimit (SheafOfModules.overFunctor R i.down) _ _
    (biproduct.isColimit (fun _ : Fin n => SheafOfModules.unit R))

/-- **A free module of finite rank is finite locally free.** -/
theorem isFiniteLocallyFreeOnSite_free_ulift_fin {Z : AlgebraicSpaces B S hS} (n : ℕ) :
    SheafOfModules.IsFiniteLocallyFreeOnSite
      (SheafOfModules.free (R := ringedToposStructureRingSheaf B S hS Z) (ULift.{u} (Fin n))) :=
  (isFiniteLocallyFreeOfRank_free_ulift_fin n).isFiniteLocallyFreeOnSite

/-! ### The derived fibres of a strictly perfect complex in degrees `≥ 1` -/

/-- **The derived pullback of a strictly perfect complex placed in degrees `≥ 1` has no cohomology
below degree `1`**, for a morphism to an algebraic space from a represented one: the terms are
flat, so the derived pullback is computed degreewise, and the pullback complex is still zero in
degrees `< 1`. Stated with `Hom(𝒪, -)` in the form in which
`AlgebraicGeometry.Space.exists_mem_singleDegreeFreePoints_of_isZero_homModule_homology` reads
it. -/
theorem isZero_homModule_homology_smallEtaleDerivedModulePullback_Q_of_lt
    {Z : AlgebraicSpaces B S hS} (P : CochainComplex (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS Z)) ℤ)
    (hP : IsStrictlyPerfect.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O) P)
    [P.IsStrictlyGE 1] {W : BigFppfOver B S hS}
    (c : (⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ : AlgebraicSpaces B S hS) ⟶ Z)
    (j : ℤ) (hj : j < 1) :
    IsZero ((CategoryTheory.homModule (SheafOfModules.unit _)
      (Stacks.SheafOfModules.unitEndRingHom.{u}
        (structureSheaf B S hS (yoneda.obj W) (isAlgebraicSpace_yoneda B S hS W))
        (isTerminal_idChart B S hS W))).obj
      ((DerivedCategory.homologyFunctor _ j).obj
        ((smallEtaleDerivedModulePullback B S hS c).obj (DerivedCategory.Q.obj P)))) := by
  obtain ⟨r, hr⟩ := hP.bounded.bddAbove
  have hLE : P.IsStrictlyLE r := by
    refine (CochainComplex.isStrictlyLE_iff P r).2 fun i hi => ?_
    by_contra h'
    exact absurd (hr h') (by omega)
  obtain ⟨e₁⟩ := nonempty_smallEtaleDerivedModulePullback_obj_Q_iso_modulePullback c P r
    fun i => Stacks.SheafOfModules.isFlat_X_of_isStrictlyPerfect_general hP i
  have : (modulePullback B S hS c).Additive := modulePullback_additive c
  let K₁ := ((modulePullback B S hS c).mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  have hM : IsZero ((DerivedCategory.homologyFunctor _ j).obj (DerivedCategory.Q.obj K₁)) :=
    ((K₁.sc j).isZero_homology_of_isZero_X₂
      ((modulePullback B S hS c).map_isZero (P.isZero_of_isStrictlyGE 1 j hj))).of_iso
      ((DerivedCategory.homologyFunctorFactors _ j).app K₁)
  exact Functor.map_isZero _ (hM.of_iso ((DerivedCategory.homologyFunctor _ j).mapIso e₁))

/-- A summand of a biproduct whose image under a functor vanishes has vanishing image. -/
private theorem isZero_obj_of_isZero_obj_biprod {C D : Type*} [Category C] [Preadditive C]
    [Category D] [HasZeroMorphisms D] (G : C ⥤ D) {A E : C} [HasBinaryBiproduct A E]
    (h : IsZero (G.obj (A ⊞ E))) : IsZero (G.obj E) := by
  have hid : 𝟙 (G.obj E) = G.map (biprod.inr : E ⟶ A ⊞ E) ≫ G.map biprod.snd := by
    rw [← G.map_comp, biprod.inr_snd, G.map_id]
  rw [IsZero.iff_id_eq_zero, hid, h.eq_of_src (G.map biprod.snd) 0, comp_zero]

/-! ### The chart-level structure of `Rf_*𝒪_X` -/

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsProper B S hS f.hom)
  (hfl : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
  (h : ∀ p : FieldValuedPoint B S hS Y.1, Function.Bijective (algebraMap p.carrier
      (globalFunctions B (Spec (.of p.carrier)) p.contained
        (fibreOverFieldValuedPoint B S hS f.hom p))))
  (hvan : ∀ (p : FieldValuedPoint B S hS Y.1) (j : ℕ), 2 ≤ j →
    IsZero (((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (AlgebraicSpaces.fiberProduct B S hS f
          (ObjectProperty.homMk (yonedaEquiv.symm p.value) : schemeSpace p.siteObject ⟶ Y)).1
        (AlgebraicSpaces.fiberProduct B S hS f
          (ObjectProperty.homMk (yonedaEquiv.symm p.value) :
            schemeSpace p.siteObject ⟶ Y)).2).O)).rightDerived j).obj
      (structureSheafModule B S hS (AlgebraicSpaces.fiberProduct B S hS f
          (ObjectProperty.homMk (yonedaEquiv.symm p.value) : schemeSpace p.siteObject ⟶ Y)))))

include hf hfl hfp hvan in
/-- **Above degree `1`, the derived fibre of `Rf_*𝒪_X` at a field-valued point vanishes**, read
through an intermediate algebraic space `Z ⟶ Y` at a field-valued point `t` of `Z`. -/
theorem isZero_homModule_homology_smallEtaleDerivedModulePullback_comp_of_two_le
    {Z : AlgebraicSpaces B S hS} (c₀ : Z ⟶ Y) (t : FieldValuedPoint B S hS Z.1)
    (j : ℕ) (hj : 2 ≤ j) :
    IsZero ((CategoryTheory.homModule (SheafOfModules.unit _)
      (Stacks.SheafOfModules.unitEndRingHom.{u}
        (structureSheaf B S hS (yoneda.obj t.siteObject)
          (isAlgebraicSpace_yoneda B S hS t.siteObject))
        (isTerminal_idChart B S hS t.siteObject))).obj
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
          (ringedToposStructureRingSheaf B S hS
            ⟨yoneda.obj t.siteObject, isAlgebraicSpace_yoneda B S hS t.siteObject⟩)) (j : ℤ)).obj
        ((smallEtaleDerivedModulePullback B S hS
          (ObjectProperty.homMk (yonedaEquiv.symm t.value) :
            (⟨yoneda.obj t.siteObject, isAlgebraicSpace_yoneda B S hS t.siteObject⟩ :
              AlgebraicSpaces B S hS) ⟶ Z)).obj
          ((smallEtaleDerivedModulePullback B S hS c₀).obj
            ((derivedModulePushforward B S hS f).obj
              ((DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _))))))) := by
  let c : (⟨yoneda.obj t.siteObject, isAlgebraicSpace_yoneda B S hS t.siteObject⟩ :
      AlgebraicSpaces B S hS) ⟶ Z := ObjectProperty.homMk (yonedaEquiv.symm t.value)
  let p : FieldValuedPoint B S hS Y.1 := FieldValuedPoint.map B S hS _ c₀.hom t
  have hcp : c ≫ c₀ =
      (ObjectProperty.homMk (yonedaEquiv.symm p.value) : schemeSpace p.siteObject ⟶ Y) :=
    InducedCategory.hom_ext (yonedaEquiv_symm_naturality_right _ c₀.hom t.value)
  exact (isZero_homModule_homology_smallEtaleDerivedModulePullback_derivedModulePushforward
    f hf hfl hfp p j (hvan p j hj)).of_iso ((CategoryTheory.homModule _ _).mapIso
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
          (ringedToposStructureRingSheaf B S hS (schemeSpace p.siteObject))) (j : ℤ)).mapIso
        ((smallEtaleDerivedModulePullbackCompIso B S hS c c₀).app _ ≪≫
          (smallEtaleDerivedModulePullbackCongr B S hS hcp).app _)))

include hf hfl hfp hvan in
/-- **A summand `Q(P)` of the derived restriction of `Rf_*𝒪_X` to `Z ⟶ Y`, with `P` strictly
perfect in degrees `≥ 1`, has derived fibres concentrated in degree `1`.** -/
theorem isZero_homModule_homology_smallEtaleDerivedModulePullback_Q_of_iso_biprod
    {Z : AlgebraicSpaces B S hS} (c₀ : Z ⟶ Y)
    (P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)) ℤ)
    (hP : IsStrictlyPerfect.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O) P)
    [P.IsStrictlyGE 1]
    (A : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)))
    (e : (smallEtaleDerivedModulePullback B S hS c₀).obj ((derivedModulePushforward B S hS f).obj
        ((DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _))) ≅
      A ⊞ DerivedCategory.Q.obj P)
    (t : FieldValuedPoint B S hS Z.1) (j : ℤ) (hj : j ≠ 1) :
    IsZero ((CategoryTheory.homModule (SheafOfModules.unit _)
      (Stacks.SheafOfModules.unitEndRingHom.{u}
        (structureSheaf B S hS (yoneda.obj t.siteObject)
          (isAlgebraicSpace_yoneda B S hS t.siteObject))
        (isTerminal_idChart B S hS t.siteObject))).obj
      ((DerivedCategory.homologyFunctor _ j).obj
        ((smallEtaleDerivedModulePullback B S hS
          (ObjectProperty.homMk (yonedaEquiv.symm t.value) :
            (⟨yoneda.obj t.siteObject, isAlgebraicSpace_yoneda B S hS t.siteObject⟩ :
              AlgebraicSpaces B S hS) ⟶ Z)).obj (DerivedCategory.Q.obj P)))) := by
  let G := smallEtaleDerivedModulePullback B S hS
      (ObjectProperty.homMk (yonedaEquiv.symm t.value) :
        (⟨yoneda.obj t.siteObject, isAlgebraicSpace_yoneda B S hS t.siteObject⟩ :
          AlgebraicSpaces B S hS) ⟶ Z) ⋙ DerivedCategory.homologyFunctor _ j ⋙
    CategoryTheory.homModule (SheafOfModules.unit _) (Stacks.SheafOfModules.unitEndRingHom.{u}
      (structureSheaf B S hS (yoneda.obj t.siteObject)
        (isAlgebraicSpace_yoneda B S hS t.siteObject))
      (isTerminal_idChart B S hS t.siteObject))
  change IsZero (G.obj (DerivedCategory.Q.obj P))
  rcases lt_or_gt_of_ne hj with hj | hj
  · exact isZero_homModule_homology_smallEtaleDerivedModulePullback_Q_of_lt P hP _ j hj
  · obtain ⟨j, rfl⟩ : ∃ m : ℕ, j = (m : ℤ) := ⟨j.toNat, by omega⟩
    have hK : IsZero (G.obj ((smallEtaleDerivedModulePullback B S hS c₀).obj
        ((derivedModulePushforward B S hS f).obj
          ((DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _))))) :=
      isZero_homModule_homology_smallEtaleDerivedModulePullback_comp_of_two_le f hf hfl hfp
        hvan c₀ t j (by omega)
    exact isZero_obj_of_isZero_obj_biprod G (A := A) (hK.of_iso (G.mapIso e.symm))

include hf hfl hfp hvan in
/-- On an étale chart `V ⟶ Y` over which `Rf_*𝒪_X ≅ 𝒪_V ⊕ P` with `P` strictly perfect in
degrees `≥ 1` (Stacks 0E6B (b)), `P` is free of finite rank placed in degree `1` on the members
of a covering of `V`: its derived fibres at geometric points are concentrated in degree `1`, by
Stacks 0CTM and the vanishing of `Hʲ(X_k, 𝒪)` for `j ≥ 2`. -/
theorem exists_iso_biprod_and_coversTop_isFreeOfRankInDegree_of_chart
    (V : SmallEtale B S hS Y.1)
    (P : CochainComplex (Modules.{u, u} B S hS (chartSpace B S hS Y V).1
        (chartSpace B S hS Y V).2) ℤ)
    (hP : IsStrictlyPerfect.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
          (chartSpace B S hS Y V).1 (chartSpace B S hS Y V).2).O)) P) (hP1 : P.IsStrictlyGE 1)
    (e : (etaleModulePullback.{u, u} B S hS (chartToSpace B S hS Y V)
          (isEtale_chartToSpace B S hS Y V)).mapDerivedCategory.obj
          ((derivedModulePushforward B S hS f).obj
            ((DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _))) ≅
        (etaleModulePullback.{u, u} B S hS (chartToSpace B S hS Y V)
          (isEtale_chartToSpace B S hS Y V)).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _)) ⊞
          DerivedCategory.Q.obj P) :
    ∃ P : DerivedCategory (SheafOfModules.{u}
        (ringedToposStructureRingSheaf B S hS (chartSpace B S hS Y V))),
      Nonempty ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS Y V)).obj
          ((derivedModulePushforward B S hS f).obj
            ((DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _))) ≅
        (DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _) ⊞ P) ∧
      ∃ (κ : Type (u + 1)) (W : κ → SmallEtale B S hS (chartSpace B S hS Y V).1),
        (SmallEtale.topology B S hS (chartSpace B S hS Y V).1).CoversTop W ∧ ∀ k,
          ∃ n : ℕ, IsFreeOfRankInDegree ((smallEtaleDerivedModulePullback B S hS
            (chartToSpace B S hS (chartSpace B S hS Y V) (W k))).obj P) 1 n := by
  let K := (derivedModulePushforward B S hS f).obj
    ((DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _))
  let c₀ := chartToSpace B S hS Y V
  have hc₀ := isEtale_chartToSpace B S hS Y V
  -- `P` read in the spelling `SheafOfModules (ringedToposStructureRingSheaf _)` of the chart's
  -- modules, the one in which the derived category instances of this file are found
  let P' : CochainComplex (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (chartSpace B S hS Y V))) ℤ := P
  let E := DerivedCategory.Q.obj P'
  have hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS (chartSpace B S hS Y V).1
      (chartSpace B S hS Y V).2) E :=
    RingedSite.isPerfect_Q_obj_of_isStrictlyPerfect _ P hP
  -- the restriction of `Rf_*𝒪_X` to the chart, with both summands read in the same spelling
  let W₀ : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (chartSpace B S hS Y V))) :=
    (etaleModulePullback.{u, u} B S hS c₀ hc₀).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _))
  let e₀ : (smallEtaleDerivedModulePullback B S hS c₀).obj K ≅ W₀ ⊞ E :=
    (smallEtaleDerivedModulePullbackIsoEtale B S hS c₀ hc₀).app K ≪≫ e
  let A := (DerivedCategory.singleFunctor (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (chartSpace B S hS Y V))) 0).obj
        (SheafOfModules.unit _)
  let w : W₀ ≅ A :=
    ((smallEtaleDerivedModulePullbackIsoEtale B S hS c₀ hc₀).app _).symm ≪≫
      smallEtaleDerivedModulePullbackUnitIso c₀
  let e' : (smallEtaleDerivedModulePullback B S hS c₀).obj K ≅ A ⊞ E :=
    e₀ ≪≫ biprod.mapIso w (Iso.refl E)
  refine ⟨E, ⟨e'⟩, ?_⟩
  -- `P` is free placed in degree one near every geometric point of the chart
  let Free : SmallEtale B S hS (chartSpace B S hS Y V).1 → Prop := fun W =>
    ∃ n : ℕ, IsFreeOfRankInDegree ((smallEtaleDerivedModulePullback B S hS
      (chartToSpace B S hS (chartSpace B S hS Y V) W)).obj E) 1 n
  refine ⟨{W // Free W}, fun W => W.1, SmallEtale.coversTop_of_forall_mem_range B S hS fun x => ?_,
    fun W => W.2⟩
  obtain ⟨t, rfl⟩ := (geometricPoints_large_enough B S hS _ _ (chartSpace B S hS Y V).2
    (chartSpace B S hS Y V).2).1 x
  let c : (⟨yoneda.obj t.val.siteObject, isAlgebraicSpace_yoneda B S hS t.val.siteObject⟩ :
      AlgebraicSpaces B S hS) ⟶ chartSpace B S hS Y V :=
    ObjectProperty.homMk (yonedaEquiv.symm t.val.value)
  have : P'.IsStrictlyGE 1 := hP1
  obtain ⟨n, W, hW, hfree⟩ :=
    exists_mem_singleDegreeFreePoints_of_isZero_homModule_homology B S hS E hE 1 t c
      fun j hj => isZero_homModule_homology_smallEtaleDerivedModulePullback_Q_of_iso_biprod
        f hf hfl hfp hvan c₀ P' hP A e' t.val j hj
  refine ⟨⟨W, n, hfree⟩, ?_⟩
  have htaut := pointsMap_yonedaEquiv_symm_comp_tautological t (𝟙 _)
  rw [Category.comp_id, pointsMap_id] at htaut
  have hpt : pointsMap B S hS _ c.hom (GeometricPoint.tautological B S hS t).image = t.image :=
    htaut
  rwa [hpt] at hW

include hf hfl hfp h hvan in
/-- **`Rf_*𝒪_X ≅ 𝒪_Y ⊕ P` étale locally, with `P` étale locally free placed in degree `1`.**
There is a family of étale charts `Vᵢ ⟶ Y` covering `Y`, and on each an object `Pᵢ` with
`L(Vᵢ ⟶ Y)^* Rf_*𝒪_X ≅ 𝒪_{Vᵢ} ⊕ Pᵢ`, together with a family of étale charts `Wᵢₖ ⟶ Vᵢ`
covering `Vᵢ` on each of which `Pᵢ` is free of finite rank placed in degree `1`. -/
theorem exists_coversTop_derivedModulePushforward_iso_biprod :
    ∃ (ι : Type (u + 1)) (V : ι → SmallEtale B S hS Y.1),
      (SmallEtale.topology B S hS Y.1).CoversTop V ∧ ∀ i,
        ∃ P : DerivedCategory (SheafOfModules.{u}
            (ringedToposStructureRingSheaf B S hS (chartSpace B S hS Y (V i)))),
          Nonempty ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS Y (V i))).obj
              ((derivedModulePushforward B S hS f).obj
                ((DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _))) ≅
            (DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _) ⊞ P) ∧
          ∃ (κ : Type (u + 1)) (W : κ → SmallEtale B S hS (chartSpace B S hS Y (V i)).1),
            (SmallEtale.topology B S hS (chartSpace B S hS Y (V i)).1).CoversTop W ∧ ∀ k,
              ∃ n : ℕ, IsFreeOfRankInDegree ((smallEtaleDerivedModulePullback B S hS
                (chartToSpace B S hS (chartSpace B S hS Y (V i)) (W k))).obj P) 1 n := by
  classical
  -- Stacks 0E6B (b), in the strictly perfect form of its proof
  have H := fun V : SmallEtale B S hS Y.1 =>
    isPerfect_derivedModulePushforward_and_isIso_baseChange_of_isFlat
      (pullback.snd f (chartToSpace B S hS Y V))
      ((isProper_isStableUnderBaseChange B S hS).of_isPullback
        (IsPullback.of_hasPullback f (chartToSpace B S hS Y V)) hf)
      ((isFlat_isStableUnderBaseChange B S hS).of_isPullback
        (IsPullback.of_hasPullback f (chartToSpace B S hS Y V)) hfl)
      ((isFinitePresentation_isStableUnderBaseChange (B := B) (S := S) (hS := hS)).of_isPullback
        (IsPullback.of_hasPullback f (chartToSpace B S hS Y V)) hfp)
      _ (isPerfect_unit (pullback f (chartToSpace B S hS Y V)))
  let K := (derivedModulePushforward B S hS f).obj
    ((DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _))
  let Good : SmallEtale B S hS Y.1 → Prop := fun V =>
    ∃ P : CochainComplex (Modules.{u, u} B S hS (chartSpace B S hS Y V).1
        (chartSpace B S hS Y V).2) ℤ,
      IsStrictlyPerfect.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
          (chartSpace B S hS Y V).1 (chartSpace B S hS Y V).2).O)) P ∧ P.IsStrictlyGE 1 ∧
      Nonempty ((etaleModulePullback.{u, u} B S hS (chartToSpace B S hS Y V)
          (isEtale_chartToSpace B S hS Y V)).mapDerivedCategory.obj K ≅
        (etaleModulePullback.{u, u} B S hS (chartToSpace B S hS Y V)
          (isEtale_chartToSpace B S hS Y V)).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _)) ⊞
          DerivedCategory.Q.obj P)
  have hcov : (SmallEtale.topology B S hS Y.1).CoversTop (fun V : {V // Good V} => V.1) := by
    intro U
    obtain ⟨R, hR, hP⟩ := exists_presieve_isStrictlyPerfect_iso_etaleRestrict_of_baseChange B S hS f
      hf hfl hfp h (fun V => (H V).1) (fun V _ _ g _ f' i sq => (H V).2 _ f' i sq) U
    refine GrothendieckTopology.superset_covering _ ?_ hR
    rintro W g ⟨Z, k, g', hg', rfl⟩
    exact ⟨⟨Z, hP g' hg'⟩, ⟨k⟩⟩
  exact ⟨{V // Good V}, fun V => V.1, hcov, fun ⟨V, P, hP, hP1, ⟨e⟩⟩ =>
    exists_iso_biprod_and_coversTop_isFreeOfRankInDegree_of_chart f hf hfl hfp hvan V P hP hP1 e⟩

/-- A biproduct whose first summand is a zero object is its second summand. -/
private def biprodIsoSndOfIsZeroFst {C : Type*} [Category C] [Preadditive C] {A A' : C}
    [HasBinaryBiproduct A A'] (hA : IsZero A) : A ⊞ A' ≅ A' where
  hom := biprod.snd
  inv := biprod.inr
  hom_inv_id := biprod.hom_ext' _ _ (hA.eq_of_src _ _) (by simp)
  inv_hom_id := by simp

/-- For `f` étale, the étale pullback of a cohomology object of `K` is the same cohomology
object of `Lf^*K`. -/
private def etaleModulePullbackHomologyIso {Z Z' : AlgebraicSpaces B S hS} (f : Z ⟶ Z')
    (hf : IsEtale B S hS f.hom)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z'))) (j : ℤ) :
    (etaleModulePullback.{u, u} B S hS f hf).obj ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z')) j).obj K) ≅
      (DerivedCategory.homologyFunctor (SheafOfModules.{u}
        (ringedToposStructureRingSheaf B S hS Z)) j).obj
        ((smallEtaleDerivedModulePullback B S hS f).obj K) :=
  ((modulePullbackIsoEtaleModulePullback B S hS f hf).app _).symm ≪≫
    (smallEtaleDerivedModulePullbackHomologyIsoOfIsEtale f hf K j).symm

/-- Cohomology of a biproduct in a derived category is the biproduct of the cohomologies. -/
private def homologyBiprodIso {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (A P : DerivedCategory C) (j : ℤ) :
    (DerivedCategory.homologyFunctor C j).obj (A ⊞ P) ≅
      (DerivedCategory.homologyFunctor C j).obj A ⊞ (DerivedCategory.homologyFunctor C j).obj P :=
  haveI := preservesBinaryBiproduct_of_preservesBiproduct (DerivedCategory.homologyFunctor C j) A P
  (DerivedCategory.homologyFunctor C j).mapBiprod A P

/-! ### Consequences: the cohomology of `Rf_*𝒪_X` -/

include hf hfl hfp h hvan in
/-- **`Rf_*𝒪_X` has no cohomology above degree `1`**: `Rⁱf_*𝒪_X = 0` for `i ≥ 2`. -/
theorem isLE_derivedModulePushforward_structureModule_one :
    ((derivedModulePushforward B S hS f).obj
      ((DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _))).IsLE 1 := by
  obtain ⟨ι, V, hV, hP⟩ := exists_coversTop_derivedModulePushforward_iso_biprod f hf hfl hfp h hvan
  refine isLE_of_isLE_smallEtaleDerivedModulePullback_chartToSpace B S hS hV _ 1 fun i => ?_
  obtain ⟨P, ⟨e⟩, κ, W, hW, hfree⟩ := hP i
  have hPLE : P.IsLE 1 := by
    refine isLE_of_isLE_smallEtaleDerivedModulePullback_chartToSpace B S hS hW _ 1 fun k => ?_
    obtain ⟨n, m, -, ⟨e'⟩⟩ := hfree k
    exact DerivedCategory.TStructure.t.isLE_of_iso e'.symm 1
  rw [DerivedCategory.isLE_iff]
  intro j hj
  let A := (DerivedCategory.singleFunctor (SheafOfModules.{u}
    (ringedToposStructureRingSheaf B S hS (chartSpace B S hS Y (V i)))) 0).obj
      (SheafOfModules.unit _)
  exact IsZero.of_iso ((biprod_isZero_iff _ _).2
    ⟨DerivedCategory.isZero_of_isLE A 0 j (by omega), DerivedCategory.isZero_of_isLE P 1 j hj⟩)
    ((DerivedCategory.homologyFunctor _ j).mapIso e ≪≫ homologyBiprodIso A P j)

include hf hfl hfp h hvan in
/-- **`R¹f_*𝒪_X` is finite locally free** (Stacks 03DL (2)). -/
theorem isFiniteLocallyFreeOnSite_homology_one_derivedModulePushforward :
    SheafOfModules.IsFiniteLocallyFreeOnSite ((DerivedCategory.homologyFunctor _ 1).obj
      ((derivedModulePushforward B S hS f).obj
        ((DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _)))) := by
  obtain ⟨ι, V, hV, hP⟩ := exists_coversTop_derivedModulePushforward_iso_biprod f hf hfl hfp h hvan
  refine isFiniteLocallyFreeOnSite_of_coversTop_etaleModulePullback hV _ fun i => ?_
  obtain ⟨P, ⟨e⟩, κ, W, hW, hfree⟩ := hP i
  let a := chartToSpace B S hS Y (V i)
  have ha := isEtale_chartToSpace B S hS Y (V i)
  let A := (DerivedCategory.singleFunctor (SheafOfModules.{u}
    (ringedToposStructureRingSheaf B S hS (chartSpace B S hS Y (V i)))) 0).obj
      (SheafOfModules.unit _)
  let e₁ := etaleModulePullbackHomologyIso a ha _ 1 ≪≫
    (DerivedCategory.homologyFunctor _ 1).mapIso e ≪≫ homologyBiprodIso A P 1 ≪≫
    biprodIsoSndOfIsZeroFst (C := SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (chartSpace B S hS Y (V i))))
      (DerivedCategory.isZero_of_isLE A 0 1 (by omega))
  refine SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso e₁.symm ?_
  refine isFiniteLocallyFreeOnSite_of_coversTop_etaleModulePullback hW _ fun k => ?_
  obtain ⟨n, m, -, ⟨e'⟩⟩ := hfree k
  let e₂ := etaleModulePullbackHomologyIso _ (isEtale_chartToSpace B S hS _ (W k)) P 1 ≪≫
    (DerivedCategory.homologyFunctor _ 1).mapIso e' ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 1).app _
  exact SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso e₂.symm
    (isFiniteLocallyFreeOnSite_free_ulift_fin m)

include hf hfl hfp h hvan in
/-- **The formation of `R¹f_*𝒪_X` commutes with arbitrary base change.** For every cartesian
square of algebraic spaces with `f' : X' ⟶ Y'` the base change of `f` along `g : Y' ⟶ Y`,
`g^*(R¹f_*𝒪_X) ≅ R¹f'_*𝒪_{X'}`. -/
theorem nonempty_modulePullback_homology_one_derivedModulePushforward_iso
    {X' Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) :
    Nonempty ((modulePullback B S hS g).obj ((DerivedCategory.homologyFunctor _ 1).obj
        ((derivedModulePushforward B S hS f).obj
          ((DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _)))) ≅
      (DerivedCategory.homologyFunctor _ 1).obj ((derivedModulePushforward B S hS f').obj
        ((DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _)))) := by
  obtain ⟨e₁⟩ := nonempty_homology_smallEtaleDerivedModulePullback_iso_of_isLE g _ 1
    (isLE_derivedModulePushforward_structureModule_one f hf hfl hfp h hvan)
  let e₂ := @asIso _ _ _ _ _ ((isPerfect_derivedModulePushforward_and_isIso_baseChange_of_isFlat
      f hf hfl hfp _ (isPerfect_unit X)).2 g f' g' sq) ≪≫
    (derivedModulePushforward B S hS f').mapIso (smallEtaleDerivedModulePullbackUnitIso g')
  exact ⟨e₁.symm ≪≫ (DerivedCategory.homologyFunctor _ 1).mapIso e₂⟩

end AlgebraicGeometry.Space

end
