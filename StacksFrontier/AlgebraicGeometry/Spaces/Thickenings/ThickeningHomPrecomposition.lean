module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningHomChartComponents

/-!
# Precomposing the morphism glued from partner charts

Let `i₀ : Z ⟶ T₀`, `i₁ : Z ⟶ T₁` and `i₂ : Z ⟶ T₂` be thickenings of algebraic spaces and
`t : T₀ ⟶ T₁` a closed immersion with `i₀ ≫ t = i₁`. If `g : T₁ ⟶ T₂` is glued from the partner
charts of a map `φ : i₂⁻¹𝒪_{T₂} ⟶ i₁⁻¹𝒪_{T₁}` and `g₀ : T₀ ⟶ T₂` from those of
`φ₀ = φ ≫ ψ_t`, where `ψ_t : i₁⁻¹𝒪_{T₁} ⟶ i₀⁻¹𝒪_{T₀}` is the inverse image along `i₀` of the
structure map of `t` (Stacks 03G8), then `t ≫ g = g₀`. This is the compatibility of the morphisms
`gₙ : Xₙ ⟶ X'` with the transition morphisms in the proof of [Stacks Project, Tag 0D3X].

## Main results

* `AlgebraicGeometry.Space.inverseImageHomChartRingHom_chartBaseChangeArrow`: the chart component
  of `φ` at the cartesian chart `Z ×_T V` is `φ` after `𝒪_T(V) ≅ (u⁻¹𝒪_T)(Z ×_T V)`.
* `AlgebraicGeometry.Space.inverseImageRingChartIso_hom_app_smallBaseChange_snd`: pullback of
  functions along `T₀ ×_{T₁} W ⟶ W`, read in `i₀⁻¹𝒪_{T₀}`, is `ψ_t` after restriction.
* `AlgebraicGeometry.Space.comp_eq_of_thickeningChartSiteHom_of_precomp`: `t ≫ g = g₀`.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 05ZN](https://stacks.math.columbia.edu/tag/05ZN)
* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The chart component of `φ` at the cartesian chart `Z ×_T V`** is `φ` after the
identification `𝒪_T(V) ≅ (u⁻¹𝒪_T)(Z ×_T V)`. -/
theorem inverseImageHomChartRingHom_chartBaseChangeArrow {Z T : AlgebraicSpaces B S hS}
    (u : Z ⟶ T) (hci : IsClosedImmersion B S hS u.hom)
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf u.hom)
    (A : Sheaf (SmallEtale.topology B S hS Z.1) CommRingCat.{u})
    (φ : (smallEtaleInverseImageRing B S hS u).obj (smallEtaleRingedTopos B S hS T).O ⟶ A)
    (V : SmallEtale B S hS T.1) (x : (smallEtaleRingedTopos B S hS T).O.obj.obj (op V)) :
    inverseImageHomChartRingHom B S hS u A φ V (chartBaseChangeArrow B S hS u hci.rep V) x =
      φ.hom.app (op ((smallBaseChange B S hS u hci.rep).obj V))
        ((inverseImageRingChartIso B S hS u hci hsurj (smallEtaleRingedTopos B S hS T).O).hom.app
          (op V) x) :=
  (congrArg (fun ψ => inverseImageHomChartRingHom B S hS u A ψ V
      (chartBaseChangeArrow B S hS u hci.rep V) x) (Category.id_comp φ)).symm.trans
    ((inverseImageHomChartRingHom_comp B S hS u _ (𝟙 _) φ V
      (chartBaseChangeArrow B S hS u hci.rep V) x).trans
    (congrArg _ (inverseImageRingChartIso_hom_app_eq_inverseImageHomChartRingHom B S hS u hci
      hsurj V x).symm))

/-- The comparison `Z ×_{T₀} (T₀ ×_{T₁} W) ⟶ Z ×_{T₁} W` of base changes of an étale chart `W`
of `T₁` along `u` and `t`, and along `u' = u ≫ t`. -/
def smallBaseChangeCompHom {Z T₀ T₁ : AlgebraicSpaces B S hS} {u : Z ⟶ T₀} {t : T₀ ⟶ T₁}
    {u' : Z ⟶ T₁} (hu : yoneda.relativelyRepresentable u.hom)
    (rt : yoneda.relativelyRepresentable t.hom) (hu' : yoneda.relativelyRepresentable u'.hom)
    (e : u ≫ t = u') (W : SmallEtale B S hS T₁.1) :
    (smallBaseChange B S hS u hu).obj ((smallBaseChange B S hS t rt).obj W) ⟶
      (smallBaseChange B S hS u' hu').obj W :=
  ObjectProperty.homMk (CostructuredArrow.homMk
    (hu'.lift (hu.fst (rt.fst W.1.hom)) (hu.snd (rt.fst W.1.hom) ≫ rt.snd W.1.hom) (by
      rw [← e]
      change hu.fst (rt.fst W.1.hom) ≫ u.hom ≫ t.hom = _
      rw [← Category.assoc, hu.w, Category.assoc, rt.w]
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ W.1.hom) (Functor.map_comp yoneda _ _).symm)))
    (hu'.lift_fst _ _ _))

/-- The second projection of `Z ×_{T₁} W` precomposed with `smallBaseChangeCompHom` is the
composite `Z ×_{T₀} (T₀ ×_{T₁} W) ⟶ T₀ ×_{T₁} W ⟶ W` of second projections. -/
theorem smallBaseChangeCompHom_snd {Z T₀ T₁ : AlgebraicSpaces B S hS} {u : Z ⟶ T₀}
    {t : T₀ ⟶ T₁} {u' : Z ⟶ T₁} (hu : yoneda.relativelyRepresentable u.hom)
    (rt : yoneda.relativelyRepresentable t.hom) (hu' : yoneda.relativelyRepresentable u'.hom)
    (e : u ≫ t = u') (W : SmallEtale B S hS T₁.1) :
    (SmallEtale.toOver B S hS Z.1).map (smallBaseChangeCompHom B S hS hu rt hu' e W) ≫
        hu'.snd W.1.hom = hu.snd (rt.fst W.1.hom) ≫ rt.snd W.1.hom := by
  unfold smallBaseChangeCompHom
  exact hu'.lift_snd _ _ _

/-- **Pullback of functions along `T₀ ×_{T₁} W ⟶ W`, read in `u⁻¹𝒪_{T₀}`**, is the map
`ψ_t : u'⁻¹𝒪_{T₁} ⟶ u⁻¹𝒪_{T₀}` (for `u' = u ≫ t`) after reading the function in `u'⁻¹𝒪_{T₁}`
and restricting along `Z ×_{T₀} (T₀ ×_{T₁} W) ⟶ Z ×_{T₁} W`. -/
theorem inverseImageRingChartIso_hom_app_smallBaseChange_snd {Z T₀ T₁ : AlgebraicSpaces B S hS}
    {u : Z ⟶ T₀} {u' : Z ⟶ T₁} (hu : IsThickeningHom B S hS u) (hu' : IsThickeningHom B S hS u')
    (t : T₀ ⟶ T₁) (rt : yoneda.relativelyRepresentable t.hom) (e : u ≫ t = u')
    (W : SmallEtale B S hS T₁.1) (z : (smallEtaleRingedTopos B S hS T₁).O.obj.obj (op W))
    (ψ : (smallEtaleInverseImageRing B S hS u').obj (smallEtaleRingedTopos B S hS T₁).O ⟶
      (smallEtaleInverseImageRing B S hS u).obj (smallEtaleRingedTopos B S hS T₀).O)
    (hψ : ψ = inverseImageStructureSheafMapOfEq B S hS u t e) :
    (inverseImageRingChartIso B S hS u hu.isClosedImmersion hu.surjective
        (smallEtaleRingedTopos B S hS T₀).O).hom.app (op ((smallBaseChange B S hS t rt).obj W))
        (((BigFppfOver.toScheme B S hS).map (rt.snd W.1.hom)).appTop z) =
      ψ.hom.app
        (op ((smallBaseChange B S hS u hu.isClosedImmersion.rep).obj
          ((smallBaseChange B S hS t rt).obj W)))
        (((smallEtaleInverseImageRing B S hS u').obj (smallEtaleRingedTopos B S hS T₁).O).obj.map
          (smallBaseChangeCompHom B S hS hu.isClosedImmersion.rep rt hu'.isClosedImmersion.rep e
            W).op
          ((inverseImageRingChartIso B S hS u' hu'.isClosedImmersion hu'.surjective
            (smallEtaleRingedTopos B S hS T₁).O).hom.app (op W) z)) := by
  subst hψ
  subst e
  have hOf : 𝟙 _ ≫ inverseImageStructureSheafMapOfEq B S hS u t rfl =
      inverseImageStructureSheafMap B S hS u t := by
    unfold inverseImageStructureSheafMapOfEq
    exact (Category.id_comp _).trans ((congrArg (· ≫ _) (eqToHom_refl _ _)).trans
      (Category.id_comp _))
  let d : ChartDiagram B S hS T₀.1 T₁.1 t.hom :=
    { U := (smallBaseChange B S hS t rt).obj W, V := W, g := rt.snd W.1.hom, comm := rt.w W.1.hom }
  let q := smallBaseChangeCompHom B S hS hu.isClosedImmersion.rep rt hu'.isClosedImmersion.rep
    rfl W
  let j₂ := StructuredArrow.mk (T := (comparisonFunctor B S hS Z).op)
    (Y := op ((smallBaseChange B S hS u hu.isClosedImmersion.rep).obj
      ((smallBaseChange B S hS t rt).obj W)))
    ((chartBaseChangeArrow B S hS (u ≫ t) hu'.isClosedImmersion.rep W).hom ≫
      ((comparisonFunctor B S hS Z).map q).op)
  have h1 := chartPullback_indexOfChartDiagram_appTop t d z
  have hB := inverseImageRingChartIso_hom_app_chartPullback B S hS u hu.isClosedImmersion
    hu.surjective t W (indexOfChartDiagram B S hS t d) z
  have hR1 := inverseImageRingChartIso_hom_app_eq_inverseImageHomChartRingHom B S hS (u ≫ t)
    hu'.isClosedImmersion hu'.surjective W z
  have hR2 := inverseImageHomChartRingHom_restrict (u ≫ t)
    ((smallEtaleInverseImageRing B S hS (u ≫ t)).obj (smallEtaleRingedTopos B S hS T₁).O) (𝟙 _) W
    (chartBaseChangeArrow B S hS (u ≫ t) hu'.isClosedImmersion.rep W) q z
  have hR3 := inverseImageHomChartRingHom_comp B S hS (u ≫ t)
    (A := (smallEtaleInverseImageRing B S hS (u ≫ t)).obj (smallEtaleRingedTopos B S hS T₁).O)
    (A' := (smallEtaleInverseImageRing B S hS u).obj (smallEtaleRingedTopos B S hS T₀).O)
    (𝟙 _) (inverseImageStructureSheafMapOfEq B S hS u t rfl) W j₂ z
  have ha : chartBaseChangeMap B S hS (u ≫ t) W j₂ =
      chartBaseChangeMap B S hS (u ≫ t) W
        (StructuredArrow.mk
          ((chartBaseChangeComp B S hS u t W (indexOfChartDiagram B S hS t d)).op ≫
            (chartBaseChangeArrow B S hS u hu.isClosedImmersion.rep
              ((smallBaseChange B S hS t rt).obj W)).hom)) := by
    have hL := (chartBaseChangeMap_comp B S hS (u ≫ t) W
      (j₁ := chartBaseChangeArrow B S hS (u ≫ t) hu'.isClosedImmersion.rep W)
      (j₂ := j₂) (StructuredArrow.homMk q.op rfl)).trans
      (congrArg (_ ≫ ·) (chartBaseChangeMap_chartBaseChangeArrow B S hS (u ≫ t)
        hu'.isClosedImmersion.rep W))
    have hRt := chartBaseChangeMap_comp_chart B S hS u t W (indexOfChartDiagram B S hS t d)
      (chartBaseChangeArrow B S hS u hu.isClosedImmersion.rep ((smallBaseChange B S hS t rt).obj W))
    have hR' : chartBaseChangeMap B S hS u ((smallBaseChange B S hS t rt).obj W)
          (chartBaseChangeArrow B S hS u hu.isClosedImmersion.rep
            ((smallBaseChange B S hS t rt).obj W)) ≫
        chartBaseChangeMap B S hS t W (indexOfChartDiagram B S hS t d) =
          hu.isClosedImmersion.rep.snd (rt.fst W.1.hom) ≫ rt.snd W.1.hom :=
      congrArg₂ (· ≫ ·) (chartBaseChangeMap_chartBaseChangeArrow B S hS u
        hu.isClosedImmersion.rep _) (chartBaseChangeMap_indexOfChartDiagram B S hS t _)
    exact hL.trans ((smallBaseChangeCompHom_snd B S hS _ rt _ rfl W).trans (hRt.trans hR').symm)
  have hR4 := inverseImageHomChartRingHom_eqToHom (B := B) (S := S) (hS := hS) (f := u ≫ t)
    (f' := u ≫ t) rfl
    ((smallEtaleInverseImageRing B S hS u).obj (smallEtaleRingedTopos B S hS T₀).O)
    (inverseImageStructureSheafMap B S hS u t) W _ _ ha z
  simp only [eqToHom_refl] at hR4
  refine (congrArg ((inverseImageRingChartIso B S hS u hu.isClosedImmersion hu.surjective
    (smallEtaleRingedTopos B S hS T₀).O).hom.app (op ((smallBaseChange B S hS t rt).obj W)))
    h1.symm).trans (hB.trans (hR4.symm.trans ?_))
  refine (congrArg (fun ψ => inverseImageHomChartRingHom B S hS (u ≫ t) _ ψ W _ z) hOf).symm.trans
    (hR3.trans (congrArg _ (hR2.trans (congrArg _ hR1.symm))))

/-- **Restricting a transported section along a morphism of charts, abstractly.** For
`ι₂ : O₂ ≅ b₂ᵒᵖ ⋙ P₂`, maps `φ : P₂ ⟶ P₁`, `ψ : P₁ ⟶ P₀` and `ε : V' ⟶ W'` with
`e₀ ≫ b₂(ε) = f ≫ e₁`, reading `ε^*x` through `ι₂`, `φ ≫ ψ` and `e₀` is reading `x` through `ι₂`,
`φ`, `e₁`, `f` and `ψ`. -/
theorem transport_app_map_apply {A₀ A₁ A₂ Zc : Type*} {_ : Category A₀} {_ : Category A₁}
    {_ : Category A₂} {_ : Category Zc} (Φ₀ : A₀ ⥤ A₂) (Φ₁ : A₁ ⥤ A₂) (b₂ : A₂ ⥤ Zc)
    (O₂ : A₂ᵒᵖ ⥤ CommRingCat.{u}) (P₂ P₁ P₀ : Zcᵒᵖ ⥤ CommRingCat.{u}) (ι₂ : O₂ ≅ b₂.op ⋙ P₂)
    (φ : P₂ ⟶ P₁) (ψ : P₁ ⟶ P₀) (χ : P₂ ⟶ P₀) (hχ : χ = φ ≫ ψ) {V : A₀} {W : A₁}
    (ε : Φ₀.obj V ⟶ Φ₁.obj W) {X₀ Y : Zc} (e₀ : X₀ ⟶ (Φ₀ ⋙ b₂).obj V) (f : X₀ ⟶ Y)
    (e₁ : Y ⟶ (Φ₁ ⋙ b₂).obj W) (h : e₀ ≫ b₂.map ε = f ≫ e₁) (x : O₂.obj (op (Φ₁.obj W))) :
    P₀.map e₀.op (χ.app (op (b₂.obj (Φ₀.obj V))) (ι₂.hom.app (op (Φ₀.obj V))
        (O₂.map ε.op x))) =
      ψ.app (op X₀) (P₁.map f.op (P₁.map e₁.op (φ.app (op (b₂.obj (Φ₁.obj W)))
        (ι₂.hom.app (op (Φ₁.obj W)) x)))) := by
  subst hχ
  have key : P₀.map (b₂.map ε).op ≫ P₀.map e₀.op = P₀.map e₁.op ≫ P₀.map f.op := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, h]
  have hm : O₂.map ε.op ≫ ι₂.hom.app (op (Φ₀.obj V)) ≫ (φ ≫ ψ).app (op (b₂.obj (Φ₀.obj V))) ≫
      P₀.map e₀.op = ι₂.hom.app (op (Φ₁.obj W)) ≫ φ.app (op (b₂.obj (Φ₁.obj W))) ≫
        P₁.map e₁.op ≫ P₁.map f.op ≫ ψ.app (op X₀) := by
    rw [NatTrans.comp_app, ι₂.hom.naturality_assoc]
    show ι₂.hom.app (op (Φ₁.obj W)) ≫ P₂.map (b₂.map ε).op ≫ φ.app _ ≫ ψ.app _ ≫
      P₀.map e₀.op = _
    rw [φ.naturality_assoc, ψ.naturality_assoc, key, ψ.naturality, ψ.naturality_assoc]
    rfl
  exact ConcreteCategory.congr_hom hm x

variable {Z T₀ T₁ T₂ : AlgebraicSpaces B S hS} {i₀ : Z ⟶ T₀} {i₁ : Z ⟶ T₁} {i₂ : Z ⟶ T₂}
  (hi₀ : IsThickeningHom B S hS i₀) (hi₁ : IsThickeningHom B S hS i₁)
  (hi₂ : IsThickeningHom B S hS i₂) {t : T₀ ⟶ T₁} (htc : IsClosedImmersion B S hS t.hom)
  (ht : i₀ ≫ t = i₁)

/-- **The partner chart of `T₀ ×_{T₁} W` maps to the partner chart of `W`**: the morphism of
étale charts of `T₂` whose base change along `i₂` is
`Z ×_{T₀} (T₀ ×_{T₁} W) ⟶ Z ×_{T₁} W` (Stacks 05ZS). -/
def thickeningChartPrecompHom (W : SmallEtale B S hS T₁.1) :
    (thickeningChartTransfer B S hS hi₀ hi₂).obj ((smallBaseChange B S hS t htc.rep).obj W) ⟶
      (thickeningChartTransfer B S hS hi₁ hi₂).obj W :=
  letI := isEquivalence_smallBaseChange_of_isThickeningHom B S hS i₂ hi₂
  (smallBaseChange B S hS i₂ hi₂.isClosedImmersion.rep).preimage
    ((thickeningChartTransferIso B S hS hi₀ hi₂).hom.app
        ((smallBaseChange B S hS t htc.rep).obj W) ≫
      smallBaseChangeCompHom B S hS hi₀.isClosedImmersion.rep htc.rep hi₁.isClosedImmersion.rep ht
        W ≫ (thickeningChartTransferIso B S hS hi₁ hi₂).inv.app W)

/-- The inverse of `thickeningChartTransferIso` at `T₀ ×_{T₁} W` followed by the base change along
`i₂` of `thickeningChartPrecompHom` is `smallBaseChangeCompHom` followed by the inverse of
`thickeningChartTransferIso` at `W`. -/
theorem thickeningChartTransferIso_inv_app_comp_smallBaseChange_map_thickeningChartPrecompHom
    (W : SmallEtale B S hS T₁.1) :
    (thickeningChartTransferIso B S hS hi₀ hi₂).inv.app ((smallBaseChange B S hS t htc.rep).obj W) ≫
        (smallBaseChange B S hS i₂ hi₂.isClosedImmersion.rep).map
          (thickeningChartPrecompHom B S hS hi₀ hi₁ hi₂ htc ht W) =
      smallBaseChangeCompHom B S hS hi₀.isClosedImmersion.rep htc.rep hi₁.isClosedImmersion.rep ht
        W ≫ (thickeningChartTransferIso B S hS hi₁ hi₂).inv.app W := by
  let := isEquivalence_smallBaseChange_of_isThickeningHom B S hS i₂ hi₂
  unfold thickeningChartPrecompHom
  rw [Functor.map_preimage, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

variable (φ : (smallEtaleInverseImageRing B S hS i₂).obj (smallEtaleRingedTopos B S hS T₂).O ⟶
    (smallEtaleInverseImageRing B S hS i₁).obj (smallEtaleRingedTopos B S hS T₁).O)
  (φ₀ : (smallEtaleInverseImageRing B S hS i₂).obj (smallEtaleRingedTopos B S hS T₂).O ⟶
    (smallEtaleInverseImageRing B S hS i₀).obj (smallEtaleRingedTopos B S hS T₀).O)
  {D : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj D)]
  (p₀ : T₀.1 ⟶ yoneda.obj D) (p₁ : T₁.1 ⟶ yoneda.obj D) (p₂ : T₂.1 ⟶ yoneda.obj D)
  (hbase₁ : ∀ V : SmallEtale B S hS T₁.1,
    ((BigFppfOver.toScheme B S hS).map (yoneda.preimage
        (((thickeningChartTransfer B S hS hi₁ hi₂).obj V).1.hom ≫ p₂))).appTop ≫
      (thickeningChartRingHom B S hS hi₁ hi₂ φ).app (op V) =
    ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (V.1.hom ≫ p₁))).appTop)
  (hbase₀ : ∀ V : SmallEtale B S hS T₀.1,
    ((BigFppfOver.toScheme B S hS).map (yoneda.preimage
        (((thickeningChartTransfer B S hS hi₀ hi₂).obj V).1.hom ≫ p₂))).appTop ≫
      (thickeningChartRingHom B S hS hi₀ hi₂
        φ₀).app (op V) =
    ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (V.1.hom ≫ p₀))).appTop)

include hbase₀ hbase₁ htc in
/-- **Precomposing the glued morphism with a closed immersion of thickenings.** If `g : T₁ ⟶ T₂`
is glued from the partner charts of `φ` and `g₀ : T₀ ⟶ T₂` from those of `φ ≫ ψ_t`, then
`t ≫ g = g₀`: on the charts `T₀ ×_{T₁} W` of affine étale charts `W` of `T₁` both are
`T₀ ×_{T₁} W ⟶ W ⟶ W' ⟶ T₂`, the two morphisms of affine schemes into `W'` having the same map
of global regular functions. -/
theorem comp_eq_of_thickeningChartSiteHom_of_precomp (g : T₁ ⟶ T₂)
    (hg : ∀ (V : SmallEtale B S hS T₁.1)
      [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS T₁.1).obj V))],
      V.1.hom ≫ g.hom = yoneda.map (thickeningChartSiteHom B S hS hi₁ hi₂ φ p₁ p₂ hbase₁ V) ≫
        ((thickeningChartTransfer B S hS hi₁ hi₂).obj V).1.hom)
    (g₀ : T₀ ⟶ T₂)
    (hg₀ : ∀ (V : SmallEtale B S hS T₀.1)
      [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS T₀.1).obj V))],
      V.1.hom ≫ g₀.hom = yoneda.map (thickeningChartSiteHom B S hS hi₀ hi₂
          φ₀ p₀ p₂ hbase₀ V) ≫
        ((thickeningChartTransfer B S hS hi₀ hi₂).obj V).1.hom)
    (ψ : (smallEtaleInverseImageRing B S hS i₁).obj (smallEtaleRingedTopos B S hS T₁).O ⟶
      (smallEtaleInverseImageRing B S hS i₀).obj (smallEtaleRingedTopos B S hS T₀).O)
    (hψ : ψ = inverseImageStructureSheafMapOfEq B S hS i₀ t ht) (hφ : φ₀ = φ ≫ ψ) :
    t ≫ g = g₀ := by
  refine ObjectProperty.hom_ext _ ?_
  refine hom_ext_of_affineChartBaseChange B S hS (Over.mk t) htc.rep T₂.2.isSheaf fun W hW => ?_
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS T₁.1).obj W)) :=
    hW
  have := isAffine_smallBaseChange_of_isClosedImmersion B S hS t htc W
  have := isAffine_thickeningChartTransfer B S hS hi₁ hi₂ W
  have key : htc.rep.snd W.1.hom ≫ thickeningChartSiteHom B S hS hi₁ hi₂ φ p₁ p₂ hbase₁ W =
      thickeningChartSiteHom B S hS hi₀ hi₂ φ₀
          p₀ p₂ hbase₀ ((smallBaseChange B S hS t htc.rep).obj W) ≫
        (SmallEtale.toOver B S hS T₂.1).map
          (thickeningChartPrecompHom B S hS hi₀ hi₁ hi₂ htc ht W) := by
    refine (BigFppfOver.toScheme B S hS).map_injective (ext_of_isAffine ?_)
    refine (congrArg Scheme.Hom.appTop ((BigFppfOver.toScheme B S hS).map_comp _ _)).trans
      ((Scheme.Hom.comp_appTop _ _).trans (Eq.trans ?_ ((congrArg Scheme.Hom.appTop
        ((BigFppfOver.toScheme B S hS).map_comp _ _)).trans (Scheme.Hom.comp_appTop _ _)).symm))
    have r₁ := (congrArg Scheme.Hom.appTop (toScheme_map_thickeningChartSiteHom B S hS hi₁ hi₂ φ
      p₁ p₂ hbase₁ W)).trans (thickeningChartHom_appTop B S hS hi₁ hi₂ φ W)
    have r₀ := (congrArg Scheme.Hom.appTop (toScheme_map_thickeningChartSiteHom B S hS hi₀ hi₂
      φ₀ p₀ p₂ hbase₀
      ((smallBaseChange B S hS t htc.rep).obj W))).trans (thickeningChartHom_appTop B S hS hi₀ hi₂
        φ₀ ((smallBaseChange B S hS t htc.rep).obj W))
    refine (congrArg (· ≫ ((BigFppfOver.toScheme B S hS).map (htc.rep.snd W.1.hom)).appTop)
      r₁).trans (Eq.trans ?_ (congrArg (((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS T₂.1).map
          (thickeningChartPrecompHom B S hS hi₀ hi₁ hi₂ htc ht W))).appTop ≫ ·) r₀).symm)
    refine (@cancel_mono _ _ _ _ _ ((inverseImageRingChartIso B S hS i₀ hi₀.isClosedImmersion
      hi₀.surjective (smallEtaleRingedTopos B S hS T₀).O).hom.app
        (op ((smallBaseChange B S hS t htc.rep).obj W))) (IsIso.mono_of_iso _) _ _).1 ?_
    ext x
    have sK := inverseImageRingChartIso_hom_app_smallBaseChange_snd B S hS hi₀ hi₁ t htc.rep ht W
      ((thickeningChartRingHom B S hS hi₁ hi₂ φ).app (op W) x) ψ hψ
    have sT := inverseImageRingChartIso_hom_app_thickeningChartRingHom B S hS hi₁ hi₂ φ W x
    have sL := inverseImageHomChartRingHom_chartBaseChangeArrow B S hS i₂ hi₂.isClosedImmersion
      hi₂.surjective _ φ ((thickeningChartTransfer B S hS hi₁ hi₂).obj W) x
    have side₁ := sK.trans (congrArg (fun y => ψ.hom.app _
      (((smallEtaleInverseImageRing B S hS i₁).obj (smallEtaleRingedTopos B S hS T₁).O).obj.map
        (smallBaseChangeCompHom B S hS hi₀.isClosedImmersion.rep htc.rep hi₁.isClosedImmersion.rep
          ht W).op y)) (sT.trans (congrArg _ sL)))
    have tT := inverseImageRingChartIso_hom_app_thickeningChartRingHom B S hS hi₀ hi₂
      φ₀ ((smallBaseChange B S hS t htc.rep).obj W)
      (((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS T₂.1).map
        (thickeningChartPrecompHom B S hS hi₀ hi₁ hi₂ htc ht W))).appTop x)
    have tL := inverseImageHomChartRingHom_chartBaseChangeArrow B S hS i₂ hi₂.isClosedImmersion
      hi₂.surjective _ φ₀
      ((thickeningChartTransfer B S hS hi₀ hi₂).obj ((smallBaseChange B S hS t htc.rep).obj W))
      (((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS T₂.1).map
        (thickeningChartPrecompHom B S hS hi₀ hi₁ hi₂ htc ht W))).appTop x)
    have hpre :=
      thickeningChartTransferIso_inv_app_comp_smallBaseChange_map_thickeningChartPrecompHom
        B S hS hi₀ hi₁ hi₂ htc ht W
    have tA := transport_app_map_apply (thickeningChartTransfer B S hS hi₀ hi₂)
      (thickeningChartTransfer B S hS hi₁ hi₂) (smallBaseChange B S hS i₂ hi₂.isClosedImmersion.rep)
      (smallEtaleRingedTopos B S hS T₂).O.obj
      ((smallEtaleInverseImageRing B S hS i₂).obj (smallEtaleRingedTopos B S hS T₂).O).obj
      ((smallEtaleInverseImageRing B S hS i₁).obj (smallEtaleRingedTopos B S hS T₁).O).obj
      ((smallEtaleInverseImageRing B S hS i₀).obj (smallEtaleRingedTopos B S hS T₀).O).obj
      (inverseImageRingChartIso B S hS i₂ hi₂.isClosedImmersion hi₂.surjective
        (smallEtaleRingedTopos B S hS T₂).O) φ.hom
      ψ.hom φ₀.hom (congrArg (fun k => k.hom) hφ)
      (thickeningChartPrecompHom B S hS hi₀ hi₁ hi₂ htc ht W)
      ((thickeningChartTransferIso B S hS hi₀ hi₂).inv.app
        ((smallBaseChange B S hS t htc.rep).obj W))
      (smallBaseChangeCompHom B S hS hi₀.isClosedImmersion.rep htc.rep hi₁.isClosedImmersion.rep
        ht W)
      ((thickeningChartTransferIso B S hS hi₁ hi₂).inv.app W) hpre x
    have hx : ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS T₂.1).map
        (thickeningChartPrecompHom B S hS hi₀ hi₁ hi₂ htc ht W))).appTop x =
        (smallEtaleRingedTopos B S hS T₂).O.obj.map
          (thickeningChartPrecompHom B S hS hi₀ hi₁ hi₂ htc ht W).op x := rfl
    rw [hx] at tT tL
    have side₂a := tT.trans (congrArg (((smallEtaleInverseImageRing B S hS i₀).obj
      (smallEtaleRingedTopos B S hS T₀).O).obj.map
        ((thickeningChartTransferIso B S hS hi₀ hi₂).inv.app
          ((smallBaseChange B S hS t htc.rep).obj W)).op) tL)
    exact side₁.trans (side₂a.trans tA).symm
  have hε := CostructuredArrow.w (thickeningChartPrecompHom B S hS hi₀ hi₁ hi₂ htc ht W).hom
  have key' : yoneda.map (htc.rep.snd W.1.hom) ≫
      yoneda.map (thickeningChartSiteHom B S hS hi₁ hi₂ φ p₁ p₂ hbase₁ W) =
        yoneda.map (thickeningChartSiteHom B S hS hi₀ hi₂ φ₀ p₀ p₂ hbase₀
          ((smallBaseChange B S hS t htc.rep).obj W)) ≫
        yoneda.map ((SmallEtale.toOver B S hS T₂.1).map
          (thickeningChartPrecompHom B S hS hi₀ hi₁ hi₂ htc ht W)) :=
    (yoneda.map_comp _ _).symm.trans ((congrArg yoneda.map key).trans (yoneda.map_comp _ _))
  show htc.rep.fst W.1.hom ≫ t.hom ≫ g.hom = htc.rep.fst W.1.hom ≫ g₀.hom
  refine ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ g.hom) (htc.rep.w W.1.hom)).trans
    (Category.assoc _ _ _))).trans ?_
  refine (congrArg (yoneda.map (htc.rep.snd W.1.hom) ≫ ·) (hg W)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) key').trans ?_)
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hε).trans ?_)
  exact (hg₀ ((smallBaseChange B S hS t htc.rep).obj W)).symm

end AlgebraicGeometry.Space

end
