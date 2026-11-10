module

public import StacksFrontier.AlgebraicGeometry.Spaces.InverseImageHomChartComp
public import StacksFrontier.AlgebraicGeometry.Spaces.InverseImageHomChartExt
public import StacksFrontier.AlgebraicGeometry.Spaces.InverseImageStructureSheafMap
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionQuotientAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningHomFromInverseImage

/-!
# Chart components of the partner-chart ring maps

The identification `𝒪_T(V) ≅ (i⁻¹𝒪_T)(Z ×_T V)` of
`AlgebraicGeometry.Space.inverseImageRingChartIso`, for a thickening `i : Z ⟶ T`, is the chart
component (`AlgebraicGeometry.Space.inverseImageHomChartRingHom`) of the identity of `i⁻¹𝒪_T`
at the cartesian chart `Z ×_T V`. Through it, the ring maps of partner charts attached to a map
`φ : i₂⁻¹𝒪_{T₂} ⟶ i₁⁻¹𝒪_{T₁}` are read off the chart components of `φ`, and the composition law
of Stacks 03G8 for chart components computes them on the structure maps.

## Main results

* `AlgebraicGeometry.Space.inverseImageRingChartIso_hom_app_eq_inverseImageHomChartRingHom`:
  `𝒪_T(V) ≅ (i⁻¹𝒪_T)(Z ×_T V)` is the chart component of the identity of `i⁻¹𝒪_T`.
* `AlgebraicGeometry.Space.inverseImageRingChartIso_hom_app_chartPullback`: pullback of
  functions from a chart of a base `D`, read in `i⁻¹𝒪_T`, is a chart component of
  `(i ≫ p)⁻¹𝒪_D ⟶ i⁻¹𝒪_T`.
* `AlgebraicGeometry.Space.inverseImageRingChartIso_hom_app_thickeningChartRingHom`: the
  partner-chart ring map through the chart components of `φ`.
* `AlgebraicGeometry.Space.thickeningChartRingHom_base_of_inverseImageStructureSheafMap`: if `φ`
  is compatible with the maps from `(Z ⟶ D)⁻¹𝒪_D`, the partner-chart ring maps lie over `D`.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **`𝒪_T(V) ≅ (i⁻¹𝒪_T)(Z ×_T V)` is the chart component of the identity** of `i⁻¹𝒪_T` at
the cartesian chart `Z ×_T V`: both are the unit of `i⁻¹ ⊣ i_*` read at the base-changed chart. -/
theorem inverseImageRingChartIso_hom_app_eq_inverseImageHomChartRingHom
    {Z T : AlgebraicSpaces B S hS} (i : Z ⟶ T) (hci : IsClosedImmersion B S hS i.hom)
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf i.hom)
    (V : SmallEtale B S hS T.1) (x : (smallEtaleRingedTopos B S hS T).O.obj.obj (op V)) :
    (inverseImageRingChartIso B S hS i hci hsurj (smallEtaleRingedTopos B S hS T).O).hom.app
        (op V) x =
      inverseImageHomChartRingHom B S hS i
        ((smallEtaleInverseImageRing B S hS i).obj (smallEtaleRingedTopos B S hS T).O) (𝟙 _) V
        (chartBaseChangeArrow B S hS i hci.rep V) x := by
  let := (smallBaseChange_isMorphismOfSites B S hS i hci.rep).toIsContinuous
  refine Eq.trans ?_ (inverseImageHomChartRingHom_eq_directImageChartProjection B S hS i _
    (𝟙 _) V (chartBaseChangeArrow B S hS i hci.rep V) x).symm
  have hu := MorphismOfTopoi.ringAdjunction_homEquiv_forget
    (smallEtaleRingedToposHom B S hS i).toToposHom (smallEtaleRingedTopos B S hS T).O
    ((smallEtaleInverseImageRing B S hS i).obj (smallEtaleRingedTopos B S hS T).O) (𝟙 _)
  refine Eq.trans ?_ (directImageChartProjection_smallEtaleRingedToposHom_representable B S hS i
    hci.rep ((sheafCompose (SmallEtale.topology B S hS Z.1) (forget CommRingCat.{u})).obj
      ((smallEtaleInverseImageRing B S hS i).obj (smallEtaleRingedTopos B S hS T).O)) V
    (((smallEtaleRingedToposHom B S hS i).toToposHom.adj.homEquiv _ _
      ((sheafCompose (SmallEtale.topology B S hS Z.1) (forget CommRingCat.{u})).map
        (𝟙 ((smallEtaleInverseImageRing B S hS i).obj
          (smallEtaleRingedTopos B S hS T).O)))).hom.app (op V) x))
  refine Eq.trans ?_ (congrArg (fun m => ((smallEtaleRingedToposHom_representable B S hS i
    hci.rep).hom.app _).hom.app (op V) (m.hom.app (op V) x)) hu)
  refine Eq.trans ?_ (congrArg (fun m => m.hom.app (op V)
    (((sheafCompose (SmallEtale.topology B S hS T.1) (forget CommRingCat.{u})).map
      ((smallEtaleRingedToposHom B S hS i).toToposHom.ringAdjunction.homEquiv _
        ((smallEtaleInverseImageRing B S hS i).obj (smallEtaleRingedTopos B S hS T).O)
        (𝟙 _))).hom.app (op V) x))
    (smallEtaleRingedToposHom_representableRing_forget B S hS i hci.rep
      ((smallEtaleInverseImageRing B S hS i).obj (smallEtaleRingedTopos B S hS T).O)))
  have hid : (smallEtaleRingedToposHom B S hS i).toToposHom.ringAdjunction.homEquiv
      (smallEtaleRingedTopos B S hS T).O
      ((smallEtaleInverseImageRing B S hS i).obj (smallEtaleRingedTopos B S hS T).O)
      (𝟙 ((smallEtaleRingedToposHom B S hS i).toToposHom.inverseImageRing.obj
        (smallEtaleRingedTopos B S hS T).O)) =
      (smallEtaleRingedToposHom B S hS i).toToposHom.ringAdjunction.unit.app
        (smallEtaleRingedTopos B S hS T).O :=
    Adjunction.homEquiv_id _ _
  rw [hid]
  rfl

/-- **Pullback of functions from a chart of the base, read in the inverse image along a
thickening, is a chart component of the comparison map.** For a thickening `u : Z ⟶ T`, a
morphism `p : T ⟶ D`, a chart `W` of `D` and a chart `V` of `T` above `T ×_D W`, pulling a
function back from `W` to `V` and reading it in `(u⁻¹𝒪_T)(Z ×_T V)` is the chart component, at
`Z ×_T V`, of the map `(u ≫ p)⁻¹𝒪_D ⟶ u⁻¹𝒪_T` (the composition law of Stacks 03G8). -/
theorem inverseImageRingChartIso_hom_app_chartPullback {Z T D : AlgebraicSpaces B S hS}
    (u : Z ⟶ T) (hci : IsClosedImmersion B S hS u.hom)
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf u.hom)
    (p : T ⟶ D) (W : SmallEtale B S hS D.1)
    (j : StructuredArrow (op (chartBaseChange B S hS p W)) (comparisonFunctor B S hS T).op)
    (x : (smallEtaleRingedTopos B S hS D).O.obj.obj (op W)) :
    (inverseImageRingChartIso B S hS u hci hsurj (smallEtaleRingedTopos B S hS T).O).hom.app
        j.right (chartPullback B S hS p W j x) =
      inverseImageHomChartRingHom B S hS (u ≫ p)
        ((smallEtaleInverseImageRing B S hS u).obj (smallEtaleRingedTopos B S hS T).O)
        (inverseImageStructureSheafMap B S hS u p) W
        (StructuredArrow.mk ((chartBaseChangeComp B S hS u p W j).op ≫
          (chartBaseChangeArrow B S hS u hci.rep j.right.unop).hom)) x := by
  refine (inverseImageRingChartIso_hom_app_eq_inverseImageHomChartRingHom B S hS u hci hsurj
    j.right.unop _).trans ?_
  refine (inverseImageHomChartRingHom_compInverseImage B S hS u p _ (𝟙 _) W j
    (chartBaseChangeArrow B S hS u hci.rep j.right.unop) x).symm.trans ?_
  refine congrArg (fun ψ => inverseImageHomChartRingHom B S hS (u ≫ p) _ ψ W _ x) ?_
  exact congrArg (_ ≫ ·) (Category.comp_id _)

/-- **A transported ring map on sections, abstractly.** For functors `Φ : A ⥤ A₂`,
`b₁ : A ⥤ Z`, `b₂ : A₂ ⥤ Z` with `ε : Φ ⋙ b₂ ≅ b₁`, presheaves of commutative rings identified
by `ι₁ : O₁ ≅ b₁ᵒᵖ ⋙ P₁` and `ι₂ : O₂ ≅ b₂ᵒᵖ ⋙ P₂`, and `φ : P₂ ⟶ P₁`, the transported map
`Φᵒᵖ ⋙ O₂ ⟶ O₁` read through `ι₁` is `ι₂`, then `φ`, then restriction along `ε⁻¹`. Stated for
abstract categories so that it is matched up to definitional unfolding at concrete sheaves. -/
theorem transport_app_apply {A A₂ Zc : Type*} [Category A] [Category A₂] [Category Zc]
    (Φ : A ⥤ A₂) (b₁ : A ⥤ Zc) (b₂ : A₂ ⥤ Zc) (ε : Φ ⋙ b₂ ≅ b₁)
    (O₁ : Aᵒᵖ ⥤ CommRingCat.{u}) (O₂ : A₂ᵒᵖ ⥤ CommRingCat.{u}) (P₁ P₂ : Zcᵒᵖ ⥤ CommRingCat.{u})
    (ι₁ : O₁ ≅ b₁.op ⋙ P₁) (ι₂ : O₂ ≅ b₂.op ⋙ P₂) (φ : P₂ ⟶ P₁) (V : A)
    (x : O₂.obj (op (Φ.obj V))) :
    ι₁.hom.app (op V) ((Functor.whiskerLeft Φ.op ι₂.hom ≫ Functor.whiskerLeft (Φ ⋙ b₂).op φ ≫
        Functor.whiskerRight (NatTrans.op ε.inv) P₁ ≫ ι₁.inv).app (op V) x) =
      P₁.map (ε.inv.app V).op (φ.app (op (b₂.obj (Φ.obj V))) (ι₂.hom.app (op (Φ.obj V)) x)) := by
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.op_app, CommRingCat.comp_apply, Functor.op_obj, Functor.comp_obj]
  exact ConcreteCategory.congr_hom (ι₁.inv_hom_id_app (op V)) _

variable {Z T₁ T₂ : AlgebraicSpaces B S hS} {i₁ : Z ⟶ T₁} {i₂ : Z ⟶ T₂}
  (hi₁ : IsThickeningHom B S hS i₁) (hi₂ : IsThickeningHom B S hS i₂)
  (φ : (smallEtaleInverseImageRing B S hS i₂).obj (smallEtaleRingedTopos B S hS T₂).O ⟶
    (smallEtaleInverseImageRing B S hS i₁).obj (smallEtaleRingedTopos B S hS T₁).O)

/-- **The partner-chart ring map through the chart components of `φ`**: read in
`(i₁⁻¹𝒪_{T₁})(Z ×_{T₁} V)`, the ring map `Γ(V') ⟶ Γ(V)` is the chart component of `φ` at the
cartesian chart `Z ×_{T₂} V'`, restricted along `Z ×_{T₁} V ≅ Z ×_{T₂} V'`. -/
theorem inverseImageRingChartIso_hom_app_thickeningChartRingHom (V : SmallEtale B S hS T₁.1)
    (x : (smallEtaleRingedTopos B S hS T₂).O.obj.obj
      (op ((thickeningChartTransfer B S hS hi₁ hi₂).obj V))) :
    (inverseImageRingChartIso B S hS i₁ hi₁.isClosedImmersion hi₁.surjective
        (smallEtaleRingedTopos B S hS T₁).O).hom.app (op V)
        ((thickeningChartRingHom B S hS hi₁ hi₂ φ).app (op V) x) =
      ((smallEtaleInverseImageRing B S hS i₁).obj (smallEtaleRingedTopos B S hS T₁).O).obj.map
        ((thickeningChartTransferIso B S hS hi₁ hi₂).inv.app V).op
        (inverseImageHomChartRingHom B S hS i₂
          ((smallEtaleInverseImageRing B S hS i₁).obj (smallEtaleRingedTopos B S hS T₁).O) φ
          ((thickeningChartTransfer B S hS hi₁ hi₂).obj V)
          (chartBaseChangeArrow B S hS i₂ hi₂.isClosedImmersion.rep
            ((thickeningChartTransfer B S hS hi₁ hi₂).obj V)) x) := by
  have h1 := inverseImageRingChartIso_hom_app_eq_inverseImageHomChartRingHom B S hS i₂
    hi₂.isClosedImmersion hi₂.surjective ((thickeningChartTransfer B S hS hi₁ hi₂).obj V) x
  have h2 := inverseImageHomChartRingHom_comp B S hS i₂ _ (𝟙 _) φ
    ((thickeningChartTransfer B S hS hi₁ hi₂).obj V)
    (chartBaseChangeArrow B S hS i₂ hi₂.isClosedImmersion.rep
      ((thickeningChartTransfer B S hS hi₁ hi₂).obj V)) x
  refine (transport_app_apply (thickeningChartTransfer B S hS hi₁ hi₂)
    (smallBaseChange B S hS i₁ hi₁.isClosedImmersion.rep)
    (smallBaseChange B S hS i₂ hi₂.isClosedImmersion.rep)
    (thickeningChartTransferIso B S hS hi₁ hi₂)
    (smallEtaleRingedTopos B S hS T₁).O.obj (smallEtaleRingedTopos B S hS T₂).O.obj
    ((smallEtaleInverseImageRing B S hS i₁).obj (smallEtaleRingedTopos B S hS T₁).O).obj
    ((smallEtaleInverseImageRing B S hS i₂).obj (smallEtaleRingedTopos B S hS T₂).O).obj
    (inverseImageRingChartIso B S hS i₁ hi₁.isClosedImmersion hi₁.surjective
      (smallEtaleRingedTopos B S hS T₁).O)
    (inverseImageRingChartIso B S hS i₂ hi₂.isClosedImmersion hi₂.surjective
      (smallEtaleRingedTopos B S hS T₂).O)
    φ.hom V x).trans (congrArg _ ?_)
  rw [h1]
  exact h2.symm.trans (congrArg (fun ψ => inverseImageHomChartRingHom B S hS i₂ _ ψ _ _ x)
    (Category.id_comp φ))

/-- The chart diagram `V ⟶ D` of a chart `V` of `T` over a morphism `p : T ⟶ D` to a scheme,
the chart of `D` being `D` itself. -/
abbrev schemeTargetChartDiagram {T : AlgebraicSpaces B S hS} {D : BigFppfOver B S hS}
    (p : T.1 ⟶ yoneda.obj D) (V : SmallEtale B S hS T.1) :
    ChartDiagram B S hS T.1 (schemeSpace D).1 p where
  U := V
  V := selfChart B S hS D
  g := yoneda.preimage (V.1.hom ≫ p)
  comm := by
    rw [Functor.map_preimage]
    exact (Category.comp_id _).symm

/-- A morphism to a scheme, as a morphism of algebraic spaces. -/
abbrev schemeSpaceHom {T : AlgebraicSpaces B S hS} {D : BigFppfOver B S hS}
    (p : T.1 ⟶ yoneda.obj D) : T ⟶ schemeSpace D :=
  ObjectProperty.homMk p

/-- The index of the chart `V` above `T ×_D D`, for a morphism `p : T ⟶ D` to a scheme. -/
abbrev schemeTargetChartIndex {T : AlgebraicSpaces B S hS} {D : BigFppfOver B S hS}
    (p : T.1 ⟶ yoneda.obj D) (V : SmallEtale B S hS T.1) :
    StructuredArrow (op (chartBaseChange B S hS (schemeSpaceHom B S hS p) (selfChart B S hS D)))
      (comparisonFunctor B S hS T).op :=
  StructuredArrow.mk (Y := op V)
    (chartLift B S hS (schemeSpaceHom B S hS p) (schemeTargetChartDiagram B S hS p V)).op

/-- The index of the cartesian chart `Z ×_T V` above `Z ×_D D`, for a thickening `u : Z ⟶ T`
and a morphism `p : T ⟶ D` to a scheme. -/
abbrev schemeTargetCompIndex {Z T : AlgebraicSpaces B S hS} {D : BigFppfOver B S hS}
    (u : Z ⟶ T) (hu : yoneda.relativelyRepresentable u.hom) (p : T.1 ⟶ yoneda.obj D)
    (V : SmallEtale B S hS T.1) :
    StructuredArrow (op (chartBaseChange B S hS (u ≫ schemeSpaceHom B S hS p)
      (selfChart B S hS D))) (comparisonFunctor B S hS Z).op :=
  StructuredArrow.mk (Y := op ((smallBaseChange B S hS u hu).obj V))
    ((chartBaseChangeComp B S hS u (schemeSpaceHom B S hS p) (selfChart B S hS D)
      (schemeTargetChartIndex B S hS p V)).op ≫ (chartBaseChangeArrow B S hS u hu V).hom)

/-- `yoneda.map` of a composite with a preimage under `yoneda`. -/
private theorem yoneda_map_comp_preimage {C : Type*} [Category C] {X Y D : C}
    (f : X ⟶ Y) (g : yoneda.obj Y ⟶ yoneda.obj D) :
    yoneda.map (f ≫ yoneda.preimage g) = yoneda.map f ≫ g :=
  (Functor.map_comp yoneda _ _).trans (congrArg _ (Functor.map_preimage yoneda _))

/-- The chart map of `AlgebraicGeometry.Space.schemeTargetChartIndex` is the map `V ⟶ D`. -/
private theorem chartBaseChangeMap_schemeTargetChartIndex {T : AlgebraicSpaces B S hS}
    {D : BigFppfOver B S hS} (p : T.1 ⟶ yoneda.obj D) (V : SmallEtale B S hS T.1) :
    chartBaseChangeMap B S hS (schemeSpaceHom B S hS p) (selfChart B S hS D)
      (schemeTargetChartIndex B S hS p V) = yoneda.preimage (V.1.hom ≫ p) :=
  chartBaseChangeMap_indexOfChartDiagram B S hS _ (schemeTargetChartDiagram B S hS p V)

variable {D : BigFppfOver B S hS} (p₁ : T₁.1 ⟶ yoneda.obj D) (p₂ : T₂.1 ⟶ yoneda.obj D)
  (hq : i₂ ≫ schemeSpaceHom B S hS p₂ = i₁ ≫ schemeSpaceHom B S hS p₁)

include hq in
/-- The two charts `Z ×_{T₁} V ⟶ D`, through `V` and through the partner chart `V'`, agree. -/
theorem chartBaseChangeMap_schemeTargetCompIndex_eq (V : SmallEtale B S hS T₁.1) :
    chartBaseChangeMap B S hS (i₂ ≫ schemeSpaceHom B S hS p₂) (selfChart B S hS D)
        (StructuredArrow.mk (Y := op ((smallBaseChange B S hS i₁ hi₁.isClosedImmersion.rep).obj V))
          ((schemeTargetCompIndex B S hS i₂ hi₂.isClosedImmersion.rep p₂
            ((thickeningChartTransfer B S hS hi₁ hi₂).obj V)).hom ≫
            ((comparisonFunctor B S hS Z).map
              ((thickeningChartTransferIso B S hS hi₁ hi₂).inv.app V)).op)) =
      chartBaseChangeMap B S hS (i₁ ≫ schemeSpaceHom B S hS p₁) (selfChart B S hS D)
        (schemeTargetCompIndex B S hS i₁ hi₁.isClosedImmersion.rep p₁ V) := by
  let V' := (thickeningChartTransfer B S hS hi₁ hi₂).obj V
  let e := (thickeningChartTransferIso B S hS hi₁ hi₂).inv.app V
  have h0 := chartBaseChangeMap_comp B S hS (i₂ ≫ schemeSpaceHom B S hS p₂)
    (selfChart B S hS D) (j₁ := schemeTargetCompIndex B S hS i₂ hi₂.isClosedImmersion.rep p₂ V')
    (j₂ := StructuredArrow.mk
      (Y := op ((smallBaseChange B S hS i₁ hi₁.isClosedImmersion.rep).obj V))
      ((schemeTargetCompIndex B S hS i₂ hi₂.isClosedImmersion.rep p₂ V').hom ≫
        ((comparisonFunctor B S hS Z).map e).op)) (StructuredArrow.homMk e.op rfl)
  have h1 := chartBaseChangeMap_comp_chart B S hS i₂ (schemeSpaceHom B S hS p₂)
    (selfChart B S hS D) (schemeTargetChartIndex B S hS p₂ V')
    (chartBaseChangeArrow B S hS i₂ hi₂.isClosedImmersion.rep V')
  have h2 := chartBaseChangeMap_comp_chart B S hS i₁ (schemeSpaceHom B S hS p₁)
    (selfChart B S hS D) (schemeTargetChartIndex B S hS p₁ V)
    (chartBaseChangeArrow B S hS i₁ hi₁.isClosedImmersion.rep V)
  refine h0.trans ((congrArg (_ ≫ ·) h1).trans (Eq.trans ?_ h2.symm))
  rw [chartBaseChangeMap_schemeTargetChartIndex, chartBaseChangeMap_schemeTargetChartIndex]
  change (SmallEtale.toOver B S hS Z.1).map e ≫
      chartBaseChangeMap B S hS i₂ V'
        (chartBaseChangeArrow B S hS i₂ hi₂.isClosedImmersion.rep V') ≫
        yoneda.preimage (V'.1.hom ≫ p₂) =
    chartBaseChangeMap B S hS i₁ V (chartBaseChangeArrow B S hS i₁ hi₁.isClosedImmersion.rep V) ≫
      yoneda.preimage (V.1.hom ≫ p₁)
  rw [chartBaseChangeMap_chartBaseChangeArrow, chartBaseChangeMap_chartBaseChangeArrow]
  apply yoneda.map_injective
  refine (Functor.map_comp yoneda _ _).trans (((congrArg (_ ≫ ·)
    (yoneda_map_comp_preimage (hi₂.isClosedImmersion.rep.snd V'.1.hom) (V'.1.hom ≫ p₂))).trans
    ?_).trans
    (yoneda_map_comp_preimage (hi₁.isClosedImmersion.rep.snd V.1.hom) (V.1.hom ≫ p₁)).symm)
  have hew : yoneda.map ((SmallEtale.toOver B S hS Z.1).map e) ≫
      hi₂.isClosedImmersion.rep.fst V'.1.hom = hi₁.isClosedImmersion.rep.fst V.1.hom :=
    CostructuredArrow.w e.hom
  have hq' : i₂.hom ≫ p₂ = i₁.hom ≫ p₁ := congrArg (fun g => g.hom) hq
  rw [← Category.assoc (yoneda.map (hi₂.isClosedImmersion.rep.snd V'.1.hom)),
    ← hi₂.isClosedImmersion.rep.w, ← Category.assoc (yoneda.map (hi₁.isClosedImmersion.rep.snd _)),
    ← hi₁.isClosedImmersion.rep.w]
  simp only [Category.assoc]
  rw [hq']
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ i₁.hom ≫ p₁) hew)

/-- Pullback of functions from `D` to a chart `V` of `T`, at the index
`AlgebraicGeometry.Space.schemeTargetChartIndex`, is pullback along `V ⟶ D`. -/
theorem chartPullback_schemeTargetChartIndex {T : AlgebraicSpaces B S hS}
    {D : BigFppfOver B S hS} (p : T.1 ⟶ yoneda.obj D) (V : SmallEtale B S hS T.1)
    (x : (smallEtaleRingedTopos B S hS (schemeSpace D)).O.obj.obj (op (selfChart B S hS D))) :
    chartPullback B S hS (schemeSpaceHom B S hS p) (selfChart B S hS D)
        (schemeTargetChartIndex B S hS p V) x =
      ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (V.1.hom ≫ p))).appTop x := by
  unfold chartPullback
  rw [chartBaseChangeMap_schemeTargetChartIndex]
  rfl

include hq in
/-- **The partner-chart ring maps lie over the base `D`, from the sheaf-level compatibility.**
If `φ` is compatible with the maps from `(Z ⟶ D)⁻¹𝒪_D` (the composition law of Stacks 03G8),
then `Γ(D) ⟶ Γ(V') ⟶ Γ(V)` is `Γ(D) ⟶ Γ(V)` on every étale chart `V` of `T₁`: this is the
hypothesis `hbase` of `AlgebraicGeometry.Space.exists_hom_of_thickeningChartSiteHom`. -/
theorem thickeningChartRingHom_base_of_inverseImageStructureSheafMap
    (hφ : inverseImageStructureSheafMap B S hS i₂ (schemeSpaceHom B S hS p₂) ≫ φ =
      eqToHom (congrArg (inverseImageStructureSheaf B S hS) hq) ≫
        inverseImageStructureSheafMap B S hS i₁ (schemeSpaceHom B S hS p₁))
    (V : SmallEtale B S hS T₁.1) :
    ((BigFppfOver.toScheme B S hS).map (yoneda.preimage
        (((thickeningChartTransfer B S hS hi₁ hi₂).obj V).1.hom ≫ p₂))).appTop ≫
      (thickeningChartRingHom B S hS hi₁ hi₂ φ).app (op V) =
    ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (V.1.hom ≫ p₁))).appTop := by
  ext x
  apply ((inverseImageRingChartIso B S hS i₁ hi₁.isClosedImmersion hi₁.surjective
    (smallEtaleRingedTopos B S hS T₁).O).app (op V)).commRingCatIsoToRingEquiv.injective
  change ((inverseImageRingChartIso B S hS i₁ hi₁.isClosedImmersion hi₁.surjective
      (smallEtaleRingedTopos B S hS T₁).O).app (op V)).hom
      ((thickeningChartRingHom B S hS hi₁ hi₂ φ).app (op V)
        (((BigFppfOver.toScheme B S hS).map (yoneda.preimage
          (((thickeningChartTransfer B S hS hi₁ hi₂).obj V).1.hom ≫ p₂))).appTop x)) =
      ((inverseImageRingChartIso B S hS i₁ hi₁.isClosedImmersion hi₁.surjective
        (smallEtaleRingedTopos B S hS T₁).O).app (op V)).hom
        (((BigFppfOver.toScheme B S hS).map (yoneda.preimage (V.1.hom ≫ p₁))).appTop x)
  rw [← chartPullback_schemeTargetChartIndex B S hS p₂
      ((thickeningChartTransfer B S hS hi₁ hi₂).obj V) x,
    ← chartPullback_schemeTargetChartIndex B S hS p₁ V x]
  have hR := inverseImageRingChartIso_hom_app_chartPullback B S hS i₁ hi₁.isClosedImmersion
    hi₁.surjective (schemeSpaceHom B S hS p₁) (selfChart B S hS D)
    (schemeTargetChartIndex B S hS p₁ V) x
  have hL := inverseImageRingChartIso_hom_app_chartPullback B S hS i₂ hi₂.isClosedImmersion
    hi₂.surjective (schemeSpaceHom B S hS p₂) (selfChart B S hS D)
    (schemeTargetChartIndex B S hS p₂ ((thickeningChartTransfer B S hS hi₁ hi₂).obj V)) x
  have h2 := inverseImageRingChartIso_hom_app_thickeningChartRingHom B S hS hi₁ hi₂ φ V
    (chartPullback B S hS (schemeSpaceHom B S hS p₂) (selfChart B S hS D)
      (schemeTargetChartIndex B S hS p₂ ((thickeningChartTransfer B S hS hi₁ hi₂).obj V)) x)
  have h1 := inverseImageRingChartIso_hom_app_eq_inverseImageHomChartRingHom B S hS i₂
    hi₂.isClosedImmersion hi₂.surjective ((thickeningChartTransfer B S hS hi₁ hi₂).obj V)
    (chartPullback B S hS (schemeSpaceHom B S hS p₂) (selfChart B S hS D)
      (schemeTargetChartIndex B S hS p₂ ((thickeningChartTransfer B S hS hi₁ hi₂).obj V)) x)
  have hc := inverseImageHomChartRingHom_comp B S hS i₂ _ (𝟙 _) φ
    ((thickeningChartTransfer B S hS hi₁ hi₂).obj V)
    (chartBaseChangeArrow B S hS i₂ hi₂.isClosedImmersion.rep
      ((thickeningChartTransfer B S hS hi₁ hi₂).obj V))
    (chartPullback B S hS (schemeSpaceHom B S hS p₂) (selfChart B S hS D)
      (schemeTargetChartIndex B S hS p₂ ((thickeningChartTransfer B S hS hi₁ hi₂).obj V)) x)
  have hc' := inverseImageHomChartRingHom_comp B S hS (i₂ ≫ schemeSpaceHom B S hS p₂) _
    (inverseImageStructureSheafMap B S hS i₂ (schemeSpaceHom B S hS p₂)) φ (selfChart B S hS D)
    (schemeTargetCompIndex B S hS i₂ hi₂.isClosedImmersion.rep p₂
      ((thickeningChartTransfer B S hS hi₁ hi₂).obj V)) x
  have hres := inverseImageHomChartRingHom_restrict (i₂ ≫ schemeSpaceHom B S hS p₂)
    ((smallEtaleInverseImageRing B S hS i₁).obj (smallEtaleRingedTopos B S hS T₁).O)
    (inverseImageStructureSheafMap B S hS i₂ (schemeSpaceHom B S hS p₂) ≫ φ) (selfChart B S hS D)
    (schemeTargetCompIndex B S hS i₂ hi₂.isClosedImmersion.rep p₂
      ((thickeningChartTransfer B S hS hi₁ hi₂).obj V))
    ((thickeningChartTransferIso B S hS hi₁ hi₂).inv.app V) x
  have heq := inverseImageHomChartRingHom_eqToHom (B := B) (S := S) (hS := hS) hq.symm
    ((smallEtaleInverseImageRing B S hS i₁).obj (smallEtaleRingedTopos B S hS T₁).O)
    (inverseImageStructureSheafMap B S hS i₁ (schemeSpaceHom B S hS p₁)) (selfChart B S hS D)
    ((schemeTargetCompIndex B S hS i₂ hi₂.isClosedImmersion.rep p₂
        ((thickeningChartTransfer B S hS hi₁ hi₂).obj V)).hom ≫
      ((comparisonFunctor B S hS Z).map
        ((thickeningChartTransferIso B S hS hi₁ hi₂).inv.app V)).op).unop
    (schemeTargetCompIndex B S hS i₁ hi₁.isClosedImmersion.rep p₁ V).hom.unop
    (chartBaseChangeMap_schemeTargetCompIndex_eq B S hS hi₁ hi₂ p₁ p₂ hq V) x
  have hc2 := ((congrArg (fun ψ => inverseImageHomChartRingHom B S hS i₂
      ((smallEtaleInverseImageRing B S hS i₁).obj (smallEtaleRingedTopos B S hS T₁).O) ψ
      ((thickeningChartTransfer B S hS hi₁ hi₂).obj V)
      (chartBaseChangeArrow B S hS i₂ hi₂.isClosedImmersion.rep
        ((thickeningChartTransfer B S hS hi₁ hi₂).obj V))
      (chartPullback B S hS (schemeSpaceHom B S hS p₂) (selfChart B S hS D)
        (schemeTargetChartIndex B S hS p₂ ((thickeningChartTransfer B S hS hi₁ hi₂).obj V)) x))
    (Category.id_comp φ)).symm.trans hc).trans (congrArg _ (h1.symm.trans hL))
  refine (h2.trans ?_).trans hR.symm
  refine (congrArg (ConcreteCategory.hom
    (((smallEtaleInverseImageRing B S hS i₁).obj (smallEtaleRingedTopos B S hS T₁).O).obj.map
      ((thickeningChartTransferIso B S hS hi₁ hi₂).inv.app V).op)) (hc2.trans hc'.symm)).trans ?_
  refine hres.symm.trans ?_
  exact (congrArg (fun ψ => inverseImageHomChartRingHom B S hS (i₂ ≫ schemeSpaceHom B S hS p₂)
    ((smallEtaleInverseImageRing B S hS i₁).obj (smallEtaleRingedTopos B S hS T₁).O) ψ
    (selfChart B S hS D) _ x) hφ).trans heq

end AlgebraicGeometry.Space

end
