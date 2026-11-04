module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatteningFiniteType.BlowupOfScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationDomination.ChartFlatness
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformFlatClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableClosedSubspaceIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.StrictTransformFinitePresentationFromFlat

/-!
# The strict transform of a scheme over a scheme, as algebraic spaces

Let `g : V ⟶ Q` be a morphism of schemes of the site and `K` an ideal sheaf on `Q`, and suppose
the scheme blowup `Bl_K Q ⟶ Q` is the blowup of the algebraic space of `Q` in the closed subspace
cut out by `K`.  If the scheme strict transform of `V` is flat and locally of finite presentation
over `Bl_K Q`, so is the strict transform of the space of `V` in the sense of Stacks 0862: the
image of the scheme strict transform in the fibre product of algebraic spaces is a closed
subspace, flat over the blowup and containing the complement of the exceptional preimage, so it
is the strict transform (`AlgebraicGeometry.Space.strictTransformSubfunctor_eq_of_isFlat`).

## Main results

* `AlgebraicGeometry.Space.isFlat_and_isLocallyOfFinitePresentation_strictTransform_schemeSpaceMap`

## References

* [Stacks Project, Tag 0862](https://stacks.math.columbia.edu/tag/0862)
* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Chart

variable {V Q : BigFppfOver B S hS} (g : V ⟶ Q)
  (K : ((BigFppfOver.toScheme B S hS).obj Q).IdealSheafData)

/-- The closed subspace of `V ×_Q Bl_K Q` cut out by the scheme strict transform of `V`. -/
noncomputable abbrev chartStrictTransform :
    ClosedSubspaces B S hS (yoneda.obj (blowUpChartObj g K)) :=
  closedSubspaceOfIdeal (blowUpChartObj g K)
    (Stacks.StrictTransform.ideal ((BigFppfOver.toScheme B S hS).map g)
      (_root_.AlgebraicGeometry.blowUpToBase K) (_root_.AlgebraicGeometry.exceptionalIdeal K))

/-- A property of scheme morphisms, étale local on the source and target and stable under
composition with étale morphisms of algebraic spaces, of `strictTransformToBlowUp` passes to the
inclusion of the scheme strict transform into `V ×_Q Bl_K Q` followed by the projection to the
blowup. -/
theorem holdsOnEveryEtaleChart_chartStrictTransform_ι_comp {P : MorphismProperty Scheme.{u}}
    (hP : IsEtaleLocalOnSourceAndTarget P)
    (hcomp : ∀ {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G) (c : G ⟶ H), IsIso a →
      IsAlgebraicSpace B S hS F → IsAlgebraicSpace B S hS G → IsAlgebraicSpace B S hS H →
        HoldsOnEveryEtaleChart B S hS P c → HoldsOnEveryEtaleChart B S hS P (a ≫ c))
    (h : P (strictTransformToBlowUp ((BigFppfOver.toScheme B S hS).map g) K)) :
    HoldsOnEveryEtaleChart B S hS P
      ((chartStrictTransform g K).1.ι ≫ yoneda.map (blowUpChartSnd g K)) := by
  set j := closedSubschemeOverι B S hS (blowUpChartObj g K)
    (Stacks.StrictTransform.ideal ((BigFppfOver.toScheme B S hS).map g)
      (_root_.AlgebraicGeometry.blowUpToBase K)
      (_root_.AlgebraicGeometry.exceptionalIdeal K)) with hjdef
  have : Mono j := (BigFppfOver.toScheme B S hS).mono_of_mono_map
    (inferInstanceAs (Mono (Stacks.StrictTransform.ideal ((BigFppfOver.toScheme B S hS).map g)
      (_root_.AlgebraicGeometry.blowUpToBase K)
      (_root_.AlgebraicGeometry.exceptionalIdeal K)).subschemeι))
  have hmono : Mono (yoneda.map j) := Functor.map_mono yoneda j
  have hiso : IsIso (Subfunctor.toRange (yoneda.map j)) := inferInstance
  have hι : (Subfunctor.range (yoneda.map j)).ι = inv (Subfunctor.toRange (yoneda.map j)) ≫
      yoneda.map j := (IsIso.eq_inv_comp _).2 (Subfunctor.toRange_ι _).symm
  have h' : P ((BigFppfOver.toScheme B S hS).map (j ≫ blowUpChartSnd g K)) := by
    rw [Functor.map_comp]
    exact h
  show HoldsOnEveryEtaleChart B S hS P
    ((Subfunctor.range (yoneda.map j)).ι ≫ yoneda.map (blowUpChartSnd g K))
  rw [hι, Category.assoc, ← Functor.map_comp]
  exact hcomp _ _ inferInstance (chartStrictTransform g K).2.1
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS _)
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS _)
    (holdsOnEveryEtaleChart_yoneda_map B S hS hP _ h')


/-- **The strict transform of the space of a scheme `V` over the space of a scheme `Q`, along the
scheme blowup of `Q` in `K`, is flat and locally of finite presentation over the blowup as soon
as the scheme strict transform is.**  The image of the scheme strict transform in the fibre
product of algebraic spaces is a closed subspace flat over the blowup and containing the
complement of the exceptional preimage, hence is the strict transform. -/
theorem isFlat_and_isLocallyOfFinitePresentation_strictTransform_schemeSpaceMap
    (hb : IsBlowupAlong B S hS (closedSubspaceOfIdeal Q K) (schemeSpaceMap (blowUpObjHom Q K)))
    (hflat : Flat (strictTransformToBlowUp ((BigFppfOver.toScheme B S hS).map g) K))
    (hlfp : LocallyOfFinitePresentation
      (strictTransformToBlowUp ((BigFppfOver.toScheme B S hS).map g) K)) :
    IsFlat B S hS (strictTransformSpaceToBlowUp B S hS (schemeSpaceMap g)
        (schemeSpaceMap (blowUpObjHom Q K))
        ((closedSubspaceOfIdeal Q K).1.preimage (schemeSpaceMap (blowUpObjHom Q K)).hom)).hom ∧
      IsLocallyOfFinitePresentation B S hS (strictTransformSpaceToBlowUp B S hS
        (schemeSpaceMap g) (schemeSpaceMap (blowUpObjHom Q K))
        ((closedSubspaceOfIdeal Q K).1.preimage (schemeSpaceMap (blowUpObjHom Q K)).hom)).hom := by
  set b := schemeSpaceMap (blowUpObjHom Q K) with hbdef
  set Z := closedSubspaceOfIdeal Q K with hZdef
  have hsqY : IsPullback (yoneda.map (blowUpChartFst g K)) (yoneda.map (blowUpChartSnd g K))
      (yoneda.map g) (yoneda.map (blowUpObjHom Q K)) := (isPullback_blowUpChart g K).map yoneda
  set φ := hsqY.isoPullback with hφdef
  have hφs : φ.hom ≫ pullback.snd (yoneda.map g) (yoneda.map (blowUpObjHom Q K)) =
      yoneda.map (blowUpChartSnd g K) := hsqY.isoPullback_hom_snd
  set Zc := chartStrictTransform g K with hZcdef
  let P := strictTransformPullback B S hS (schemeSpaceMap g) b
  have hCh := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (blowUpChartObj g K)
  let C : ClosedSubspaces B S hS P.1 :=
    ⟨Zc.1.preimage φ.inv, isClosedSubspace_preimage B S hS φ.inv Zc.1 hCh P.2 Zc.2⟩
  have hsqC := Subfunctor.isPullback_preimage φ.inv Zc.1
  have hti : IsIso (Zc.1.fromPreimage φ.inv) := hsqC.isIso_fst_of_isIso
  have hCeq : C.1.ι ≫ (strictTransformPullbackToBlowUp B S hS (schemeSpaceMap g) b).hom =
      Zc.1.fromPreimage φ.inv ≫ (Zc.1.ι ≫ yoneda.map (blowUpChartSnd g K)) := by
    show (Zc.1.preimage φ.inv).ι ≫ pullback.snd (yoneda.map g) (yoneda.map (blowUpObjHom Q K)) = _
    rw [← hφs]
    simp only [← Category.assoc]
    rw [Subfunctor.fromPreimage_ι]
    simp
  have hCalg : IsAlgebraicSpace B S hS C.1.toFunctor := C.2.1
  have hBl := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (blowUpObj Q K)
  have hflatC : IsFlat B S hS
      (C.1.ι ≫ (strictTransformPullbackToBlowUp B S hS (schemeSpaceMap g) b).hom) := by
    rw [hCeq]
    exact isFlat_comp B S hS hCalg Zc.2.1 hBl _ _
      (isFlat_of_isEtale B S hS (isEtale_of_isIso B S hS (Zc.1.fromPreimage φ.inv)))
      (holdsOnEveryEtaleChart_chartStrictTransform_ι_comp g K Flat.isEtaleLocalOnSourceAndTarget
        (fun a c _ hF hG hH hc => isFlat_comp B S hS hF hG hH a c
          (isFlat_of_isEtale B S hS (isEtale_of_isIso B S hS a)) hc) hflat)
  have hlfpC : IsLocallyOfFinitePresentation B S hS
      (C.1.ι ≫ (strictTransformPullbackToBlowUp B S hS (schemeSpaceMap g) b).hom) := by
    rw [hCeq]
    exact isLocallyOfFinitePresentation_comp B S hS hCalg Zc.2.1 hBl _ _
      (isLocallyOfFinitePresentation_of_isEtale B S hS
        (isEtale_of_isIso B S hS (Zc.1.fromPreimage φ.inv)))
      (holdsOnEveryEtaleChart_chartStrictTransform_ι_comp g K
        LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget
        (fun a c _ hF hG hH hc => isLocallyOfFinitePresentation_comp B S hS hF hG hH a c
          (isLocallyOfFinitePresentation_of_isEtale B S hS (isEtale_of_isIso B S hS a)) hc) hlfp)
  -- the complement of the exceptional preimage lies in `C`
  obtain ⟨J, hJ⟩ : ∃ J : ((BigFppfOver.toScheme B S hS).obj (blowUpChartObj g K)).IdealSheafData,
      J = Stacks.StrictTransform.ideal ((BigFppfOver.toScheme B S hS).map g)
        (_root_.AlgebraicGeometry.blowUpToBase K) (_root_.AlgebraicGeometry.exceptionalIdeal K) :=
    ⟨_, rfl⟩
  obtain ⟨O', hO'def⟩ : ∃ O' : ((BigFppfOver.toScheme B S hS).obj (blowUpChartObj g K)).Opens,
      O' = Stacks.StrictTransform.exceptionalComplement ((BigFppfOver.toScheme B S hS).map g)
        (_root_.AlgebraicGeometry.blowUpToBase K) (_root_.AlgebraicGeometry.exceptionalIdeal K) :=
    ⟨_, rfl⟩
  have hZcJ : Zc.1 = Subfunctor.range (yoneda.map (closedSubschemeOverι B S hS _ J)) := by
    subst hJ
    rfl
  have h1 : Subfunctor.range (yoneda.map (openSubHom (blowUpChartObj g K) O')) ≤ Zc.1 := by
    have hj : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map
        (closedSubschemeOverι B S hS (blowUpChartObj g K) J)) := by
      rw [toScheme_map_closedSubschemeOverι]
      exact inferInstanceAs (AlgebraicGeometry.IsClosedImmersion J.subschemeι)
    rw [hZcJ]
    refine (range_yoneda_map_le_iff_ker_le B S hS _ _ hj).2 ?_
    have hk : ((BigFppfOver.toScheme B S hS).map
        (closedSubschemeOverι B S hS (blowUpChartObj g K) J)).ker = J := by
      rw [toScheme_map_closedSubschemeOverι]
      exact Scheme.IdealSheafData.ker_subschemeι J
    rw [hk, toScheme_map_openSubHom B S hS, hJ, hO'def, Stacks.StrictTransform.ideal_eq_ker_ι]
    exact le_rfl
  have h2 : (exceptionalPreimageComplement B S hS (schemeSpaceMap g) b Z).1.preimage φ.hom ≤
      Subfunctor.range (yoneda.map (openSubHom (blowUpChartObj g K) O')) := by
    rw [← openSubspaceOfPoints_preimage_pointsToScheme]
    refine le_of_range_pointsMap_ι_subset B S hS
      (isOpenSubspace_openSubspaceOfPoints_preimage_pointsToScheme _ O') ?_
    rw [range_pointsMap_ι_openSubspaceOfPoints]
    intro x hx0
    have hx : pointsMap B S hS _ φ.hom x ∈ subspacePointSet B S hS P.1
        (exceptionalPreimageComplement B S hS (schemeSpaceMap g) b Z).1 :=
      (Set.ext_iff.mp (range_pointsMap_preimage_ι B S hS φ.hom
        (exceptionalPreimageComplement B S hS (schemeSpaceMap g) b Z).1) x).1 hx0
    rw [subspacePointSet_openComplement] at hx
    have e1 := Set.ext_iff.mp (range_pointsMap_preimage_ι B S hS
      (pullback.snd (yoneda.map g) (yoneda.map (blowUpObjHom Q K))) (Z.1.preimage b.hom))
      (pointsMap B S hS _ φ.hom x)
    have e2 := Set.ext_iff.mp (range_pointsMap_preimage_ι B S hS b.hom Z.1)
      (pointsMap B S hS _ (pullback.snd (yoneda.map g) (yoneda.map (blowUpObjHom Q K)))
        (pointsMap B S hS _ φ.hom x))
    have hm : φ.hom ≫ pullback.snd (yoneda.map g) (yoneda.map (blowUpObjHom Q K)) ≫
        yoneda.map (blowUpObjHom Q K) = yoneda.map (blowUpChartSnd g K ≫ blowUpObjHom Q K) := by
      rw [← Category.assoc, hφs, ← Functor.map_comp]
    have hx2 : (BigFppfOver.toScheme B S hS).map (blowUpChartSnd g K ≫ blowUpObjHom Q K)
        (pointsToScheme B S hS _ x) ∉ (K.support : Set _) := by
      intro h
      refine hx (e1.2 (e2.2 ?_))
      have key : pointsMap B S hS _ (yoneda.map (blowUpObjHom Q K))
          (pointsMap B S hS _ (pullback.snd (yoneda.map g) (yoneda.map (blowUpObjHom Q K)))
            (pointsMap B S hS _ φ.hom x)) =
          pointsMap B S hS _ (yoneda.map (blowUpChartSnd g K ≫ blowUpObjHom Q K)) x := by
        rw [← hm]
        simp only [pointsMap_comp, Function.comp_apply]
      show pointsMap B S hS _ (yoneda.map (blowUpObjHom Q K))
          (pointsMap B S hS _ (pullback.snd (yoneda.map g) (yoneda.map (blowUpObjHom Q K)))
            (pointsMap B S hS _ φ.hom x)) ∈
        subspacePointSet B S hS (yoneda.obj Q) (closedSubspaceOfIdeal Q K).1
      rw [key, subspacePointSet_closedSubspaceOfIdeal]
      show pointsToScheme B S hS Q (pointsMap B S hS _
        (yoneda.map (blowUpChartSnd g K ≫ blowUpObjHom Q K)) x) ∈ (K.support : Set _)
      rw [pointsToScheme_pointsMap]
      exact h
    rw [Functor.map_comp] at hx2
    show pointsToScheme B S hS _ x ∈ (O' : Set _)
    rw [hO'def]
    simp only [Stacks.StrictTransform.exceptionalComplement, Scheme.IdealSheafData.support_comap]
    exact hx2
  have hC : (exceptionalPreimageComplement B S hS (schemeSpaceMap g) b Z).1 ≤ C.1 := by
    intro T x hx
    refine h1 _ (h2 _ ?_)
    show φ.hom.app T (φ.inv.app T x) ∈
      (exceptionalPreimageComplement B S hS (schemeSpaceMap g) b Z).1.obj T
    have hid : φ.hom.app T (φ.inv.app T x) = x :=
      congrFun (congrArg (fun α => α.app T) φ.inv_hom_id) x
    rw [hid]
    exact hx
  have hST := strictTransformSubfunctor_eq_of_isFlat B S hS (schemeSpaceMap g) b Z hb C hC hflatC
  show IsFlat B S hS ((strictTransformSubfunctor B S hS (schemeSpaceMap g) b
      (Z.1.preimage b.hom)).ι ≫
      (strictTransformPullbackToBlowUp B S hS (schemeSpaceMap g) b).hom) ∧
    IsLocallyOfFinitePresentation B S hS ((strictTransformSubfunctor B S hS (schemeSpaceMap g) b
      (Z.1.preimage b.hom)).ι ≫
      (strictTransformPullbackToBlowUp B S hS (schemeSpaceMap g) b).hom)
  rw [hST]
  exact ⟨hflatC, hlfpC⟩

end Chart

end AlgebraicGeometry.Space

end
