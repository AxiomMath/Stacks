module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjectionForgetCommRing
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjectionSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageSectionsGlobalFunctionsEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesAffineCaseBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleChartGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget

/-!
# Naturality of the sections of a direct image as global functions of the fibre

Let `X` be an algebraic space over `S` and `V` an étale scheme chart of `X`.  For an algebraic
space `A` over `X` through `p : A ⟶ X`,
`AlgebraicGeometry.Space.directImageSectionsToGlobalFunctions` identifies the sections of
`p_* 𝒪_A` over `V` with the global regular functions on `A ×_X V`.  This file shows that the
identification is natural in `A`: a morphism `a : A₁ ⟶ A₂` over `X` acts on the sections of the
direct images by `AlgebraicGeometry.Space.pushforwardAlgebraMap`, and on the global functions
of the fibres by pullback along the induced morphism `A₁ ×_X V ⟶ A₂ ×_X V`.

## Main definitions

* `AlgebraicGeometry.Space.chartBaseChangeSpaceMap`: the morphism `A₁ ×_X V ⟶ A₂ ×_X V`
  induced by a morphism `A₁ ⟶ A₂` over `X`; it is functorial
  (`AlgebraicGeometry.Space.chartBaseChangeSpaceMap_comp`), so an isomorphism over `X` induces
  `AlgebraicGeometry.Space.chartBaseChangeSpaceIso`.

## Main results

* `AlgebraicGeometry.Space.directImageChartProjectionRingHom_pushforwardAlgebraMap`: the
  direct-image map read at a chart lying above a chart of the target.
* `AlgebraicGeometry.Space.directImageSectionsToGlobalFunctions_pushforwardAlgebraMap`: the
  naturality square.
* `AlgebraicGeometry.Space.directImageSectionsToGlobalFunctions_algebraMap_eq`: the
  structure-algebra map, read on global functions, is pullback along `A ×_X V ⟶ V`.

## Implementation notes

The morphism `a` need not be representable, so the image of an étale scheme chart of
`A₁ ×_X V` in `A₂ ×_X V` is not a chart.  The two global functions are compared on one
surjective étale chart of `A₁ ×_X V` (`AlgebraicGeometry.Space.globalFunctions_ext_of_surjective`),
chosen to lie over a surjective étale chart `c₂` of `A₂ ×_X V`: it is an atlas of the fibre
product of `c₂` with `A₁ ×_X V ⟶ A₂ ×_X V`.  On such a chart the direct-image map reads as
pullback along the induced morphism of charts
(`AlgebraicGeometry.Space.directImageChartProjection_pushforwardAlgMap`), and so does pullback of
global functions (`AlgebraicGeometry.Space.globalFunctionsMap_apply_chart`).

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X A₁ A₂ : AlgebraicSpaces B S hS}

/-- The morphism `A₁ ×_X V ⟶ A₂ ×_X V` induced by a morphism `a : A₁ ⟶ A₂` over `X`. -/
def chartBaseChangeSpaceMap {p₁ : A₁ ⟶ X} {p₂ : A₂ ⟶ X} (a : A₁ ⟶ A₂) (ha : a ≫ p₂ = p₁)
    (V : SmallEtale B S hS X.1) :
    chartBaseChangeSpace B S hS p₁ V ⟶ chartBaseChangeSpace B S hS p₂ V :=
  (isPullback_chartBaseChangeInclusion B S hS p₂ V).lift
    (chartBaseChangeInclusion B S hS p₁ V ≫ a) (chartBaseChangeProjection B S hS p₁ V)
    (by rw [Category.assoc, ha]; exact (isPullback_chartBaseChangeInclusion B S hS p₁ V).w)

/-- The induced morphism of fibres commutes with the projections to `A₁` and `A₂`. -/
@[reassoc (attr := simp)]
theorem chartBaseChangeSpaceMap_inclusion {p₁ : A₁ ⟶ X} {p₂ : A₂ ⟶ X} (a : A₁ ⟶ A₂)
    (ha : a ≫ p₂ = p₁) (V : SmallEtale B S hS X.1) :
    chartBaseChangeSpaceMap B S hS a ha V ≫ chartBaseChangeInclusion B S hS p₂ V =
      chartBaseChangeInclusion B S hS p₁ V ≫ a :=
  IsPullback.lift_fst _ _ _ _

/-- The induced morphism of fibres commutes with the projections `A₁ ×_X V ⟶ V` and
`A₂ ×_X V ⟶ V`. -/
@[reassoc (attr := simp)]
theorem chartBaseChangeSpaceMap_projection {p₁ : A₁ ⟶ X} {p₂ : A₂ ⟶ X} (a : A₁ ⟶ A₂)
    (ha : a ≫ p₂ = p₁) (V : SmallEtale B S hS X.1) :
    chartBaseChangeSpaceMap B S hS a ha V ≫ chartBaseChangeProjection B S hS p₂ V =
      chartBaseChangeProjection B S hS p₁ V :=
  IsPullback.lift_snd _ _ _ _

/-- The induced morphism of fibres is functorial: a composite over `X` induces the composite. -/
theorem chartBaseChangeSpaceMap_comp {A₃ : AlgebraicSpaces B S hS} {p₁ : A₁ ⟶ X} {p₂ : A₂ ⟶ X}
    {p₃ : A₃ ⟶ X} (a : A₁ ⟶ A₂) (b : A₂ ⟶ A₃) (c : A₁ ⟶ A₃) (ha : a ≫ p₂ = p₁)
    (hb : b ≫ p₃ = p₂) (hc : c ≫ p₃ = p₁) (habc : a ≫ b = c) (V : SmallEtale B S hS X.1) :
    chartBaseChangeSpaceMap B S hS c hc V =
      chartBaseChangeSpaceMap B S hS a ha V ≫ chartBaseChangeSpaceMap B S hS b hb V :=
  (isPullback_chartBaseChangeInclusion B S hS p₃ V).hom_ext
    (by simp only [chartBaseChangeSpaceMap_inclusion, Category.assoc,
      chartBaseChangeSpaceMap_inclusion_assoc, habc])
    (by simp only [chartBaseChangeSpaceMap_projection, Category.assoc])

/-- The identity over `X` induces the identity of fibres. -/
theorem chartBaseChangeSpaceMap_id {p₁ : A₁ ⟶ X} (h : 𝟙 A₁ ≫ p₁ = p₁)
    (V : SmallEtale B S hS X.1) :
    chartBaseChangeSpaceMap B S hS (𝟙 A₁) h V = 𝟙 _ :=
  (isPullback_chartBaseChangeInclusion B S hS p₁ V).hom_ext
    (by simp only [chartBaseChangeSpaceMap_inclusion, Category.comp_id, Category.id_comp])
    (by simp only [chartBaseChangeSpaceMap_projection, Category.id_comp])

/-- The isomorphism of fibres `A₁ ×_X V ≅ A₂ ×_X V` induced by an isomorphism over `X`. -/
@[simps]
def chartBaseChangeSpaceIso {p₁ : A₁ ⟶ X} {p₂ : A₂ ⟶ X} (e : A₁ ≅ A₂) (he : e.hom ≫ p₂ = p₁)
    (V : SmallEtale B S hS X.1) :
    chartBaseChangeSpace B S hS p₁ V ≅ chartBaseChangeSpace B S hS p₂ V where
  hom := chartBaseChangeSpaceMap B S hS e.hom he V
  inv := chartBaseChangeSpaceMap B S hS e.inv (by rw [← he, e.inv_hom_id_assoc]) V
  hom_inv_id := by
    rw [← chartBaseChangeSpaceMap_comp B S hS _ _ (𝟙 A₁) _ _ (Category.id_comp p₁) e.hom_inv_id,
      chartBaseChangeSpaceMap_id]
  inv_hom_id := by
    rw [← chartBaseChangeSpaceMap_comp B S hS _ _ (𝟙 A₂) _ _ (Category.id_comp p₂) e.inv_hom_id,
      chartBaseChangeSpaceMap_id]

/-- **The chart projections of a direct-image map.**  For a morphism `a : A₁ ⟶ A₂` over `X`, a
chart `j'` of `A₂` above `A₂ ×_X V` and a chart `U` of `A₁` carrying an index `φ₁` above
`A₁ ×_X V` and an index `φ₂` above `A₁ ×_{A₂} j'` whose chartwise morphisms are compatible over
`V`, reading the direct-image map of a section `s` of `p₂_* 𝒪_{A₂}` at `φ₁` is pulling back the
reading of `s` at `j'` along the chartwise morphism of `φ₂`. -/
theorem directImageChartProjectionRingHom_pushforwardAlgebraMap {p₁ : A₁ ⟶ X} {p₂ : A₂ ⟶ X}
    (a : A₁ ⟶ A₂) (ha : a ≫ p₂ = p₁) (V : SmallEtale B S hS X.1)
    (j' : StructuredArrow (op (chartBaseChange B S hS p₂ V)) (comparisonFunctor B S hS A₂).op)
    (U : SmallEtale B S hS A₁.1)
    (φ₁ : op (chartBaseChange B S hS p₁ V) ⟶ (comparisonFunctor B S hS A₁).op.obj (op U))
    (φ₂ : op (chartBaseChange B S hS a j'.right.unop) ⟶
      (comparisonFunctor B S hS A₁).op.obj (op U))
    (hm : chartBaseChangeMap B S hS a j'.right.unop (StructuredArrow.mk φ₂) ≫
        chartBaseChangeMap B S hS p₂ V j' =
      chartBaseChangeMap B S hS p₁ V (StructuredArrow.mk φ₁))
    (s : (pushforwardAlgebra B S hS (Over.mk p₂)).right.obj.obj (op V)) :
    (directImageChartProjectionRingHom B S hS p₁ V (StructuredArrow.mk φ₁)).hom
        (((pushforwardAlgebraMap B S hS (Over.homMk a ha : Over.mk p₁ ⟶ Over.mk p₂)).right.hom.app
          (op V)).hom s) =
      chartPullback B S hS a j'.right.unop (StructuredArrow.mk φ₂)
        ((directImageChartProjectionRingHom B S hS p₂ V j').hom s) := by
  let J : StructuredArrow (op (chartBaseChange B S hS (a ≫ p₂) V))
      (comparisonFunctor B S hS A₁).op :=
    StructuredArrow.mk ((chartBaseChangeComp B S hS a p₂ V j').op ≫ φ₂)
  have hφ : ((pushforwardAlgebraMap B S hS
      (Over.homMk a ha : Over.mk p₁ ⟶ Over.mk p₂)).right.hom.app (op V)).hom s =
      (eqToHom (congrArg (fun q : A₁ ⟶ X => (pushforwardCommRingFunctor
        (smallEtaleRingedToposHom B S hS q).toToposHom).obj
          (smallEtaleRingedTopos B S hS A₁).O) ha)).hom.app (op V)
        ((pushforwardAlgMap B S hS a p₂).hom.app (op V) s) := by
    rw [pushforwardAlgebraMap_right, pushforwardRingMap_eq]
    rfl
  have hm' : chartBaseChangeMap B S hS (a ≫ p₂) V J =
      chartBaseChangeMap B S hS p₁ V (StructuredArrow.mk φ₁) :=
    (chartBaseChangeMap_comp_chart B S hS a p₂ V j' (StructuredArrow.mk φ₂)).trans hm
  have step2 := directImageChartProjection_eqToHom B S hS ha V U _ _ hm'
    (chartDiagramOfIndex B S hS (a ≫ p₂) V J).comm
    (chartDiagramOfIndex B S hS p₁ V (StructuredArrow.mk φ₁)).comm
    ((pushforwardAlgMap B S hS a p₂).hom.app (op V) s)
  have step3 := directImageChartProjection_pushforwardAlgMap B S hS a p₂ V j'
    (StructuredArrow.mk φ₂) s
  rw [hφ]
  refine (directImageChartProjectionRingHom_apply_forgetCommRing B S hS V _ _).trans ?_
  refine Eq.trans ?_ (congrArg (chartPullback B S hS a j'.right.unop (StructuredArrow.mk φ₂))
    (directImageChartProjectionRingHom_apply_forgetCommRing B S hS V j' s)).symm
  refine (eq_of_heq (directImageChartProjection_congr B S hS p₁ V
    (indexOfChartDiagram_chartDiagramOfIndex B S hS p₁ V (StructuredArrow.mk φ₁)) _ _)).symm.trans
      ?_
  refine step2.trans ?_
  refine (eq_of_heq (directImageChartProjection_congr B S hS (a ≫ p₂) V
    (indexOfChartDiagram_chartDiagramOfIndex B S hS (a ≫ p₂) V J) _ _)).trans ?_
  exact step3

/-- **The identification of the sections of a direct image with the global functions of the
fibre is natural.**  For a morphism `f : A₁ ⟶ A₂` over `X` and an étale chart `V` of `X`, the
direct-image map `p₂_* 𝒪_{A₂} ⟶ p₁_* 𝒪_{A₁}` on sections over `V` is pullback of global
functions along `A₁ ×_X V ⟶ A₂ ×_X V`. -/
theorem directImageSectionsToGlobalFunctions_pushforwardAlgebraMap {p₁ : A₁ ⟶ X} {p₂ : A₂ ⟶ X}
    (f : Over.mk p₁ ⟶ Over.mk p₂) (V : SmallEtale B S hS X.1)
    (s : (pushforwardAlgebra B S hS (Over.mk p₂)).right.obj.obj (op V)) :
    directImageSectionsToGlobalFunctions B S hS p₁ V
        (((pushforwardAlgebraMap B S hS f).right.hom.app (op V)).hom s) =
      globalFunctionsMap B S hS (chartBaseChangeSpaceMap B S hS f.left (Over.w f) V)
        (directImageSectionsToGlobalFunctions B S hS p₂ V s) := by
  let a : A₁ ⟶ A₂ := f.left
  have ha : a ≫ p₂ = p₁ := Over.w f
  let P₁ := chartBaseChangeSpace B S hS p₁ V
  let P₂ := chartBaseChangeSpace B S hS p₂ V
  let m : P₁ ⟶ P₂ := chartBaseChangeSpaceMap B S hS a ha V
  obtain ⟨T₂, a₂, hs₂, he₂⟩ := P₂.property.exists_atlas
  let c₂ : SmallEtale B S hS P₂.1 := ⟨CostructuredArrow.mk a₂, he₂⟩
  let j' := baseChangeSpaceChartIndex B S hS p₂ V c₂
  let i₂ : chartSpace B S hS P₂ c₂ ⟶ P₂ := chartToSpace B S hS P₂ c₂
  have hpb : IsPullback (pullback.fst m i₂) (pullback.snd m i₂) m i₂ :=
    IsPullback.of_hasPullback m i₂
  obtain ⟨T₁, a₁, hs₁, he₁⟩ := (pullback m i₂).property.exists_atlas
  let a₁' : yoneda.obj T₁ ⟶ P₁.1 := a₁ ≫ (pullback.fst m i₂).hom
  have he₁' : IsEtale B S hS a₁' :=
    isEtale_comp B S hS (isEtale_of_presheaf_etale B S hS he₁)
      (isEtale_of_isPullback B S hS _ _ _ _ hpb.flip (isEtale_chartToSpace B S hS P₂ c₂))
  let c₁ : SmallEtale B S hS P₁.1 :=
    ⟨CostructuredArrow.mk a₁', presheaf_etale_of_isEtale B S hS he₁'⟩
  have hsurj₁ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) c₁.1.hom := by
    refine (surjective_iff_surjective_pointsMap B S hS P₁.1 P₁.property T₁ a₁').2 ?_
    refine isSurjective_comp B S hS
      ((surjective_iff_surjective_pointsMap B S hS _ (pullback m i₂).property T₁ a₁).1 hs₁) ?_
    refine isSurjective_of_isPullback B S hS hpb.flip ?_
    exact (surjective_iff_surjective_pointsMap B S hS P₂.1 P₂.property T₂ a₂).1 hs₂
  refine globalFunctions_ext_of_surjective B S hS P₁ c₁ hsurj₁ ?_
  have h1 : (pullback.snd m i₂).hom ≫ i₂.hom = (pullback.fst m i₂).hom ≫ m.hom :=
    congrArg (fun k : pullback m i₂ ⟶ P₂ => k.hom) (pullback.condition (f := m) (g := i₂)).symm
  have hℓ : (a₁ ≫ (pullback.snd m i₂).hom) ≫ j'.right.unop.1.hom =
      (a₁' ≫ (chartBaseChangeInclusion B S hS p₁ V).hom) ≫ a.hom := by
    have h2 : m.hom ≫ (chartBaseChangeInclusion B S hS p₂ V).hom =
        (chartBaseChangeInclusion B S hS p₁ V).hom ≫ a.hom :=
      congrArg (fun k => k.hom) (chartBaseChangeSpaceMap_inclusion B S hS a ha V)
    change (a₁ ≫ (pullback.snd m i₂).hom) ≫ i₂.hom ≫
        (chartBaseChangeInclusion B S hS p₂ V).hom = _
    simp only [Category.assoc]
    rw [reassoc_of% h1, h2]
    rfl
  let ℓ : yoneda.obj T₁ ⟶ (chartBaseChangeSpace B S hS a j'.right.unop).1 :=
    (isPullback_chartBaseChangeProjection B S hS a j'.right.unop).lift _ _ hℓ
  have hℓ₂ : ℓ ≫ (chartBaseChangeProjection B S hS a j'.right.unop).hom =
      a₁ ≫ (pullback.snd m i₂).hom :=
    (isPullback_chartBaseChangeProjection B S hS a j'.right.unop).lift_fst _ _ hℓ
  have hℓ₁ : ℓ ≫ (chartBaseChangeInclusion B S hS a j'.right.unop).hom =
      a₁' ≫ (chartBaseChangeInclusion B S hS p₁ V).hom :=
    (isPullback_chartBaseChangeProjection B S hS a j'.right.unop).lift_snd _ _ hℓ
  let kHom : (comparisonFunctor B S hS A₁).obj (baseChangeSpaceChart B S hS p₁ V c₁) ⟶
      chartBaseChange B S hS a j'.right.unop :=
    ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk ℓ)
      (ObjectProperty.hom_ext _ hℓ₁))
  let k : StructuredArrow (op (chartBaseChange B S hS a j'.right.unop))
      (comparisonFunctor B S hS A₁).op :=
    StructuredArrow.mk (Y := op (baseChangeSpaceChart B S hS p₁ V c₁)) kHom.op
  let ψ := chartBaseChangeMap B S hS a j'.right.unop k
  have hψ : c₁.1.hom ≫ m.hom = yoneda.map ψ ≫ c₂.1.hom := by
    have hy : yoneda.map ψ = ℓ ≫ (chartBaseChangeProjection B S hS a j'.right.unop).hom :=
      yoneda_map_chartBaseChangeMap B S hS a j'.right.unop k
    have e : yoneda.map ψ = a₁ ≫ (pullback.snd m i₂).hom := hy.trans hℓ₂
    exact (Category.assoc _ _ _).trans ((congrArg (a₁ ≫ ·) h1.symm).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ c₂.1.hom) e.symm)))
  have hm : chartBaseChangeMap B S hS a j'.right.unop k ≫ chartBaseChangeMap B S hS p₂ V j' =
      chartBaseChangeMap B S hS p₁ V (baseChangeSpaceChartIndex B S hS p₁ V c₁) := by
    apply yoneda.map_injective
    have e : ∀ {A : AlgebraicSpaces B S hS} (p : A ⟶ X) (c : SmallEtale B S hS
        (chartBaseChangeSpace B S hS p V).1),
        yoneda.map (chartBaseChangeMap B S hS p V (baseChangeSpaceChartIndex B S hS p V c)) =
          c.1.hom ≫ (chartBaseChangeProjection B S hS p V).hom := fun p c =>
      (congrArg yoneda.map (chartBaseChangeMap_baseChangeSpaceChartIndex B S hS p V c)).trans
        (yoneda_map_smallEtaleChartMapToBase B S hS _ c)
    have e4 : m.hom ≫ (chartBaseChangeProjection B S hS p₂ V).hom =
        (chartBaseChangeProjection B S hS p₁ V).hom :=
      congrArg (fun k => k.hom) (chartBaseChangeSpaceMap_projection B S hS a ha V)
    refine (yoneda.map_comp _ _).trans (Eq.trans ?_ (e p₁ c₁).symm)
    refine (congrArg (yoneda.map ψ ≫ ·) (e p₂ c₂)).trans ?_
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hψ.symm).trans
      ((Category.assoc _ _ _).trans (congrArg (c₁.1.hom ≫ ·) e4)))
  rw [globalFunctionsMap_apply_chart B S hS m _ c₁ c₂ ψ hψ,
    directImageSectionsToGlobalFunctions_val]
  exact directImageChartProjectionRingHom_pushforwardAlgebraMap B S hS a ha V j'
    (baseChangeSpaceChart B S hS p₁ V c₁) (baseChangeSpaceChartHom B S hS p₁ V c₁).op kHom.op hm s

/-- **The structure-algebra map of a direct image, read as global functions of the fibre, is
pullback along the projection.**  For `p : A ⟶ X` and an étale chart `V` of `X`, the image of a
regular function `r` on `V` in the sections of `p_* 𝒪_A` over `V` is, as a global function on
`A ×_X V`, the pullback of `r` along `A ×_X V ⟶ V`. -/
theorem directImageSectionsToGlobalFunctions_algebraMap_eq {p : A₁ ⟶ X}
    (V : SmallEtale B S hS X.1) (r : (structureSheaf B S hS X.1 X.2).obj.obj (op V)) :
    directImageSectionsToGlobalFunctions B S hS p V
        ((pushforwardAlgebra B S hS (Over.mk p)).algebraMap (op V) r) =
      globalFunctionsMap B S hS (chartBaseChangeProjection B S hS p V)
        ((comparisonGlobalFunctionsRingEquiv B S hS X V).symm r) := by
  refine Subtype.ext (funext fun c => ?_)
  refine (directImageSectionsToGlobalFunctions_algebraMap B S hS p V c.unop r).trans ?_
  refine Eq.trans ?_ (globalFunctionsMap_val_chart B S hS (chartBaseChangeProjection B S hS p V)
    (idEtaleChart B S hS ((SmallEtale.toOver B S hS X.obj).obj V)) c.unop
    (smallEtaleChartMapToBase B S hS (chartBaseChangeProjection B S hS p V).hom c.unop)
    ((Category.comp_id _).trans
      (yoneda_map_smallEtaleChartMapToBase B S hS _ c.unop)) _).symm
  exact congrArg _ ((comparisonGlobalFunctionsRingEquiv B S hS X V).apply_symm_apply r).symm

end AlgebraicGeometry.Space

end
