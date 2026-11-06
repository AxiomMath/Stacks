module

public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Isomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.EtaleStageOfCutoffBoundedSystem
import all StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties

/-!
# Isomorphisms descend to a stage of a system bounded by the cutoff

Stacks 084S (and 0852) says: in the situation of Stacks 084W, if the base change `f : X ⟶ Y` of
a morphism `f₀ : X₀ ⟶ Y₀` locally of finite presentation over the stage `B₀` to the limit
`B = lim Bᵢ` is an isomorphism, then so is its base change `fᵢ : Xᵢ ⟶ Yᵢ` to some stage. The
library proves it as `AlgebraicGeometry.Space.MorphismDescentSystem.exists_isIso_mapAt` for a
morphism descent system, whose field `indexSize` asks the index set to be smaller than the
cofinality of the site's cutoff. This file proves it, together with its two inputs Stacks 07SN
and 084X, for an inverse system bounded by the cutoff
(`AlgebraicGeometry.Space.IsCutoffBoundedSystem`), with no condition on the cofinality. The third
input, Stacks 07SL, is
`AlgebraicGeometry.Space.exists_isEtale_pullbackMap_of_isCutoffBoundedSystem`.

## Main results

* `AlgebraicGeometry.Space.isPullback_pullbackMap_of_comp_eq`: the base change of `f₀` to a
  later stage is a base change of its base change to an earlier one.
* `AlgebraicGeometry.Space.exists_isSurjective_pullbackMap_of_isCutoffBoundedSystem`: Stacks 07SN.
* `AlgebraicGeometry.Space.exists_universallyInjective_pullbackMap_of_isCutoffBoundedSystem`:
  Stacks 084X.
* `AlgebraicGeometry.Space.exists_isIso_pullbackMap_of_isCutoffBoundedSystem`: Stacks 084S.

## Implementation notes

As for Stacks 07SL, the system is unbundled and the base changes of `f₀` are written as
`pullback.map`. The private characterisation of surjectivity on a chart square in
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties` is imported with
`import all`.

## References

* [Stacks Project, Tag 084S](https://stacks.math.columbia.edu/tag/084S)
* [Stacks Project, Tag 0852](https://stacks.math.columbia.edu/tag/0852)
* [Stacks Project, Tag 07SN](https://stacks.math.columbia.edu/tag/07SN)
* [Stacks Project, Tag 084X](https://stacks.math.columbia.edu/tag/084X)
* [Stacks Project, Tag 05W5](https://stacks.math.columbia.edu/tag/05W5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space

/-! ### Chart squares of a base change -/

section BaseChangeSquares

variable {A : Type*} [Category* A] [HasPullbacks A]

/-- **The base change of `f₀` to a later stage is a base change of its base change to an earlier
one.** Let `f : X ⟶ Y` be a morphism over `Bs`, and let `t₁ : B₁ ⟶ Bs`, `t₂ : B₂ ⟶ Bs` and
`s : B₂ ⟶ B₁` with `s ≫ t₁ = t₂`. Then the base change of `f` along `t₂` is the base change of
its base change along `t₁` by the induced morphism `B₂ ×_Bs Y ⟶ B₁ ×_Bs Y`. -/
theorem isPullback_pullbackMap_of_comp_eq {X Y Bs B₁ B₂ : A} (x : X ⟶ Bs) (y : Y ⟶ Bs)
    (f : X ⟶ Y) (hf : f ≫ y = x) (t₁ : B₁ ⟶ Bs) (t₂ : B₂ ⟶ Bs) (s : B₂ ⟶ B₁)
    (hs : s ≫ t₁ = t₂) :
    IsPullback (pullback.map t₂ x t₁ x s (𝟙 _) (𝟙 _) (by simp [hs]) (by simp))
      (pullback.map t₂ x t₂ y (𝟙 _) f (𝟙 _) (by simp) (by simp [hf]))
      (pullback.map t₁ x t₁ y (𝟙 _) f (𝟙 _) (by simp) (by simp [hf]))
      (pullback.map t₂ y t₁ y s (𝟙 _) (𝟙 _) (by simp [hs]) (by simp)) := by
  have key : ∀ {B' : A} (t : B' ⟶ Bs), IsPullback (pullback.snd t x)
      (pullback.map t x t y (𝟙 _) f (𝟙 _) (by simp) (by simp [hf])) f (pullback.snd t y) :=
    fun t => isPullback_of_proj_eq x y f hf t _ (by simp) (by simp)
  refine IsPullback.of_right ?_ ?_ (key t₁)
  · simpa using key t₂
  · apply pullback.hom_ext <;> simp

end BaseChangeSquares


variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

attribute [local instance] MorphismProperty.relative_isStableUnderBaseChange

/-- The limit of a directed system of algebraic spaces with affine transitions, bounded by the
cutoff, is an algebraic space. -/
private theorem isAlgebraicSpace_limit_of_isCutoffBoundedSystem {I : Type u} [Preorder I]
    [IsDirected I (· ≤ ·)] [Nonempty I] (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hD : IsCutoffBoundedSystem B S hS D)
    (hDalg : ∀ i : I, IsAlgebraicSpace B S hS (D.obj (op i)))
    (hDaff : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom B S hS (D.map a)) :
    IsAlgebraicSpace B S hS (limit D) := by
  obtain ⟨hSize, ⟨ν, hν, hHomSize⟩, hB⟩ := hD
  exact isAlgebraicSpace_limit_of_baseChangeSizeBounded B S hS D hSize hν hHomSize
    (fun i => hDalg i.unop) hDaff hB

/-! ### Stacks 07SN -/

/-- **Stacks 07SN, for an inverse system bounded by the cutoff.** Let `D` be a directed inverse
system of algebraic spaces over `S` with affine transition morphisms, bounded by the cutoff, let
`i₀` be a stage, and let `f₀ : X₀ ⟶ Y₀` be a morphism of algebraic spaces over `D i₀`, locally of
finite presentation, with `X₀` and `Y₀` quasi-compact and `Y₀` quasi-separated. If the base
change of `f₀` to `lim D` is surjective, then so is its base change to some stage `D i` with
`i₀ ≤ i`. -/
theorem exists_isSurjective_pullbackMap_of_isCutoffBoundedSystem {I : Type u} [Preorder I]
    [IsDirected I (· ≤ ·)] (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hD : IsCutoffBoundedSystem B S hS D)
    (hDalg : ∀ i : I, IsAlgebraicSpace B S hS (D.obj (op i)))
    (hDaff : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom B S hS (D.map a))
    (i₀ : I) {X₀ Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (x : X₀ ⟶ D.obj (op i₀))
    (y : Y₀ ⟶ D.obj (op i₀)) (f₀ : X₀ ⟶ Y₀) (hf₀ : f₀ ≫ y = x)
    (hX₀ : IsAlgebraicSpace B S hS X₀) (hY₀ : IsAlgebraicSpace B S hS Y₀)
    (hX₀qc : IsQuasiCompactSpace B S hS X₀) (hY₀qc : IsQuasiCompactSpace B S hS Y₀)
    (hY₀qs : IsAbsolutelyQuasiSeparated B S hS hZ Y₀)
    (fp : IsLocallyOfFinitePresentation B S hS f₀)
    (surj : IsSurjective B S hS (pullback.map (limit.π D (op i₀)) x (limit.π D (op i₀)) y
      (𝟙 _) f₀ (𝟙 _) (by simp) (by simp [hf₀]))) :
    ∃ (i : I) (hi : i₀ ≤ i), IsSurjective B S hS (pullback.map (D.map (homOfLE hi).op) x
      (D.map (homOfLE hi).op) y (𝟙 _) f₀ (𝟙 _) (by simp) (by simp [hf₀])) := by
  classical
  have _ : Nonempty I := ⟨i₀⟩
  have _ : IsCofiltered Iᵒᵖ := inferInstance
  have hlim := isAlgebraicSpace_limit_of_isCutoffBoundedSystem B S hS D hD hDalg hDaff
  obtain ⟨hSize, ⟨ν, hν, hHomSize⟩, hB⟩ := hD
  obtain ⟨U, b, hU, hbS, hbE⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS Y₀ hY₀).mp hY₀qc
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
  have hfibSpace : IsAlgebraicSpace B S hS (pullback f₀ b) :=
    isAlgebraicSpace_pullback B S hS f₀ b hX₀ (isAlgebraicSpace_yoneda B S hS U) hY₀
  have hfib : IsQuasiCompactSpace B S hS (pullback f₀ b) :=
    isQuasiCompactSpace_pullback B S hS hZ f₀ b hX₀ hY₀ hX₀qc
      (isQuasiCompactSpace_yoneda_obj B S hS inferInstance) hY₀qs
  obtain ⟨V, cover, hV, hcS, hcE⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS _ hfibSpace).mp hfib
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj V) := hV
  have hbE' := (isEtale_iff_presheaf_of_yoneda B S hS b).mp hbE
  have hcE' := (isEtale_iff_presheaf_of_yoneda B S hS cover).mp hcE
  have hcover : IsSurjective B S hS cover :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS _ hfibSpace _ cover).mp hcS
  have hchart : IsSurjective B S hS b :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS _ hY₀ _ b).mp hbS
  let r : V ⟶ U := yoneda.preimage (cover ≫ pullback.snd f₀ b)
  have hr : yoneda.map r = cover ≫ pullback.snd f₀ b := yoneda.map_preimage _
  let a : yoneda.obj V ⟶ X₀ := cover ≫ pullback.fst f₀ b
  have haE : (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf a := by
    have := isMultiplicative_presheaf_etale B S hS
    exact MorphismProperty.comp_mem _ _ _ hcE'
      (MorphismProperty.of_isPullback (IsPullback.of_hasPullback f₀ b).flip hbE')
  have hcomm : yoneda.map r ≫ b = a ≫ f₀ := by
    simp only [hr, a, Category.assoc, pullback.condition]
  have hrfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map r) :=
    fp _ _ a b r haE hbE' hcomm
  have htransfer : ∀ (B' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS B' →
      ∀ (t : B' ⟶ D.obj (op i₀)) (W : BigFppfOver B S hS) (p : yoneda.obj W ⟶ B')
        (q : W ⟶ U), IsPullback p (yoneda.map q) t (b ≫ y) →
      (IsSurjective B S hS (pullback.map t x t y (𝟙 _) f₀ (𝟙 _) (by simp) (by simp [hf₀])) ↔
        AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map (pullback.snd r q))) := by
    intro B' hB' t W p q hp
    have hX' : IsAlgebraicSpace B S hS (pullback t x) :=
      isAlgebraicSpace_pullback B S hS t x hB' hX₀ (hDalg i₀)
    have hY' : IsAlgebraicSpace B S hS (pullback t y) :=
      isAlgebraicSpace_pullback B S hS t y hB' hY₀ (hDalg i₀)
    rw [surjective_map_pullback_snd_iff, hr]
    exact (isSurjective_chart_iff hX₀ hY₀ hX' hY' (isAlgebraicSpace_yoneda B S hS _)
      (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS W) cover
      (isPullback_of_proj_eq x y f₀ hf₀ t _ (by simp) (by simp))
      (isPullback_chart_baseChange b y t p (yoneda.map q) hp) hcover hchart).symm
  let U₀ : BigAffineFppf B S hS := ⟨U, hU⟩
  let C := affineChartSystem B S hS (op i₀) D U₀ (b ≫ y) hDaff
  let L := C.limitBridgeOfBaseChangeSizeBounded hSize hν hHomSize hB
  let qs : ∀ j : Over (op i₀), C.siteDiagram.obj j ⟶ U := fun j => yoneda.preimage (C.baseMap j)
  have hqs : ∀ j, yoneda.map (qs j) = C.baseMap j := fun j => yoneda.map_preimage _
  let qL : L.cone.pt ⟶ U := yoneda.preimage L.toBase
  have hqL : yoneda.map qL = L.toBase := yoneda.map_preimage _
  have hqs_comp : ∀ {j k : Over (op i₀)} (g : j ⟶ k), C.siteDiagram.map g ≫ qs k = qs j := by
    intro j k g
    have hnat : yoneda.map (C.siteDiagram.map g) ≫ C.iso.hom.app k =
        C.iso.hom.app j ≫ (stageBaseChangeDiagram B S hS (op i₀) D U₀ (b ≫ y)).map g :=
      C.iso.hom.naturality g
    apply yoneda.map_injective
    rw [yoneda.map_comp, hqs, hqs]
    simp only [AffineChartSystem.baseMap]
    rw [← Category.assoc, hnat, Category.assoc, stageBaseChangeDiagram_map_comp_snd]
  have hcone_qs : ∀ j, L.cone.π.app j ≫ qs j = qL := fun j =>
    yoneda.map_injective <| by rw [yoneda.map_comp, hqs, hqL]; exact L.baseMap_comp j
  let j₀ : Over (op i₀) := Over.mk (𝟙 (op i₀))
  let T := BigFppfOver.toScheme B S hS
  let fbase := pullback.snd (T.map r) (T.map (qs j₀))
  let X₁ : Over (C.schemeDiagram.obj j₀) := Over.mk fbase
  let Y₁ : Over (C.schemeDiagram.obj j₀) := Over.mk (𝟙 (C.schemeDiagram.obj j₀))
  let φ₁ : X₁ ⟶ Y₁ := Over.homMk fbase (Category.comp_id _)
  have : ∀ {j k : Over (op i₀)} (g : j ⟶ k),
      _root_.AlgebraicGeometry.IsAffineHom (C.schemeDiagram.map g) :=
    fun g => C.isAffineHom_map g
  have := C.isAffine_obj j₀
  have hj₀aff : IsAffine (T.obj (C.siteDiagram.obj j₀)) := C.isAffine_obj j₀
  have hUaff : IsAffine (T.obj U) := hU
  have hfstAff : _root_.AlgebraicGeometry.IsAffineHom (pullback.fst (T.map r) (T.map (qs j₀))) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip
      (isAffineHom_of_isAffine (T.map (qs j₀)))
  have : IsAffine X₁.left := isAffine_of_isAffineHom (pullback.fst (T.map r) (T.map (qs j₀)))
  have hY₁aff : IsAffine Y₁.left := C.isAffine_obj j₀
  have : LocallyOfFinitePresentation φ₁.left :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback (T.map r) (T.map (qs j₀))) hrfp
  have : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let cL := T.mapCone L.cone
  have hqL' : cL.π.app j₀ ≫ T.map (qs j₀) = T.map qL := by
    show T.map (L.cone.π.app j₀) ≫ _ = _
    rw [← Functor.map_comp, hcone_qs j₀]
  have hpL : IsPullback L.toLimit (yoneda.map qL) (limit.π D (op i₀)) (b ≫ y) :=
    hqL ▸ L.isPullback
  have : AlgebraicGeometry.Surjective ((Over.pullback (cL.π.app j₀)).map φ₁).left := by
    refine (prop_overPullback_map_left_iff_pullback_snd _ fbase (cL.π.app j₀)).mpr ?_
    refine (prop_iteratedPullback_snd_iff T _ r (qs j₀) qL (cL.π.app j₀) hqL').mpr ?_
    exact (htransfer (limit D) hlim (limit.π D (op i₀)) L.cone.pt L.toLimit qL hpL).mp surj
  obtain ⟨j, g, hjj⟩ := exists_surjective_baseChange_of_surjective_limitBaseChange
    C.schemeDiagram cL L.schemeIsLimit j₀ X₁ Y₁ φ₁
  refine ⟨j.left.unop, leOfHom j.hom.unop, ?_⟩
  have hmap : D.map (homOfLE (leOfHom j.hom.unop)).op = D.map j.hom :=
    congrArg D.map (Subsingleton.elim _ _)
  have hp : IsPullback (C.stageMap j) (yoneda.map (qs j))
      (D.map (homOfLE (leOfHom j.hom.unop)).op) (b ≫ y) := by
    rw [hmap, hqs]; exact C.isPullback j
  have hqj : C.schemeDiagram.map g ≫ T.map (qs j₀) = T.map (qs j) := by
    show T.map (C.siteDiagram.map g) ≫ _ = _
    rw [← Functor.map_comp, hqs_comp g]
  refine (htransfer _ (hDalg _) _ _ (C.stageMap j) (qs j) hp).mpr ?_
  exact (prop_iteratedPullback_snd_iff T _ r (qs j₀) (qs j) (C.schemeDiagram.map g)
    hqj).mp ((prop_overPullback_map_left_iff_pullback_snd _ fbase
      (C.schemeDiagram.map g)).mp hjj)

/-! ### Stacks 084X -/

/-- **Stacks 084X, for an inverse system bounded by the cutoff.** In the situation of
`AlgebraicGeometry.Space.exists_isSurjective_pullbackMap_of_isCutoffBoundedSystem`, with `X₀`
quasi-separated as well and `f₀` only locally of finite type: if the base change of `f₀` to
`lim D` is universally injective, then so is its base change to some stage `D i` with `i₀ ≤ i`. -/
theorem exists_universallyInjective_pullbackMap_of_isCutoffBoundedSystem {I : Type u} [Preorder I]
    [IsDirected I (· ≤ ·)] (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hD : IsCutoffBoundedSystem B S hS D)
    (hDalg : ∀ i : I, IsAlgebraicSpace B S hS (D.obj (op i)))
    (hDaff : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom B S hS (D.map a))
    (i₀ : I) {X₀ Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (x : X₀ ⟶ D.obj (op i₀))
    (y : Y₀ ⟶ D.obj (op i₀)) (f₀ : X₀ ⟶ Y₀) (hf₀ : f₀ ≫ y = x)
    (hX₀ : IsAlgebraicSpace B S hS X₀) (hY₀ : IsAlgebraicSpace B S hS Y₀)
    (hX₀qc : IsQuasiCompactSpace B S hS X₀)
    (hX₀qs : IsAbsolutelyQuasiSeparated B S hS hZ X₀)
    (hY₀qs : IsAbsolutelyQuasiSeparated B S hS hZ Y₀)
    (ft : IsLocallyOfFiniteType B S hS f₀)
    (inj : UniversallyInjective B S hS (pullback.map (limit.π D (op i₀)) x (limit.π D (op i₀)) y
      (𝟙 _) f₀ (𝟙 _) (by simp) (by simp [hf₀]))) :
    ∃ (i : I) (hi : i₀ ≤ i), UniversallyInjective B S hS (pullback.map (D.map (homOfLE hi).op) x
      (D.map (homOfLE hi).op) y (𝟙 _) f₀ (𝟙 _) (by simp) (by simp [hf₀])) := by
  have _ : Nonempty I := ⟨i₀⟩
  have _ : IsCofiltered Iᵒᵖ := inferInstance
  have hdiag : ∀ {B' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (t : B' ⟶ D.obj (op i₀)),
      pullback.map t x t (pullback.fst f₀ f₀ ≫ x) (𝟙 _) (pullback.diagonal f₀) (𝟙 _)
          (by simp) (by simp) =
        (pullback.lift (pullback.fst t x) (pullback.snd t x ≫ pullback.diagonal f₀) (by
            simp only [pullback.diagonal_fst_assoc, Category.id_comp]
            exact pullback.condition (f := t) (g := x) :
              pullback.fst t x ≫ t =
                pullback.snd t x ≫ pullback.diagonal f₀ ≫ pullback.fst f₀ f₀ ≫ x) :
          pullback t x ⟶ pullback t (pullback.fst f₀ f₀ ≫ x)) := by
    intro B' t
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans (pullback.lift_fst _ _ _).symm
    · exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm
  have hP : IsAlgebraicSpace B S hS (pullback f₀ f₀) :=
    isAlgebraicSpace_pullback B S hS f₀ f₀ hX₀ hX₀ hY₀
  have hlim := isAlgebraicSpace_limit_of_isCutoffBoundedSystem B S hS D hD hDalg hDaff
  have hsurjLim : IsSurjective B S hS (pullback.map (limit.π D (op i₀)) x (limit.π D (op i₀))
      (pullback.fst f₀ f₀ ≫ x) (𝟙 _) (pullback.diagonal f₀) (𝟙 _) (by simp) (by simp)) := by
    rw [hdiag]
    exact (isSurjective_baseChange_diagonal_iff B S hS x y (limit.π D (op i₀)) f₀ hf₀ _
      (by simp) (by simp)).mpr (isSurjective_diagonal_of_universallyInjective B S hS
        (isAlgebraicSpace_pullback B S hS _ x hlim hX₀ (hDalg i₀)) _ inj)
  obtain ⟨i, hi, hs⟩ := exists_isSurjective_pullbackMap_of_isCutoffBoundedSystem B S hS hZ D hD
    hDalg hDaff i₀ x (pullback.fst f₀ f₀ ≫ x) (pullback.diagonal f₀) (by simp) hX₀ hP hX₀qc
    (isQuasiCompactSpace_pullback B S hS hZ f₀ f₀ hX₀ hY₀ hX₀qc hX₀qc hY₀qs)
    (isAbsolutelyQuasiSeparated_pullback B S hS hZ f₀ f₀ hX₀ hX₀ hY₀ hX₀qs hX₀qs)
    (isLocallyOfFinitePresentation_pullbackDiagonal B S hS f₀ hX₀ hY₀ ft) hsurjLim
  refine ⟨i, hi, universallyInjective_of_isSurjective_diagonal B S hS _ ?_⟩
  rw [hdiag] at hs
  exact (isSurjective_baseChange_diagonal_iff B S hS x y (D.map (homOfLE hi).op) f₀ hf₀ _
    (by simp) (by simp)).mp hs

/-! ### Stacks 084S -/

/-- **Stacks 084S, for an inverse system bounded by the cutoff.** Let `D` be a directed inverse
system of algebraic spaces over `S` with affine transition morphisms, bounded by the cutoff, let
`i₀` be a stage, and let `f₀ : X₀ ⟶ Y₀` be a morphism of quasi-compact and quasi-separated
algebraic spaces over `D i₀`, locally of finite presentation. If the base change of `f₀` to
`lim D` is an isomorphism, then so is its base change to some stage `D i` with `i₀ ≤ i`. -/
theorem exists_isIso_pullbackMap_of_isCutoffBoundedSystem {I : Type u} [Preorder I]
    [IsDirected I (· ≤ ·)] (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hD : IsCutoffBoundedSystem B S hS D)
    (hDalg : ∀ i : I, IsAlgebraicSpace B S hS (D.obj (op i)))
    (hDaff : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom B S hS (D.map a))
    (i₀ : I) {X₀ Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (x : X₀ ⟶ D.obj (op i₀))
    (y : Y₀ ⟶ D.obj (op i₀)) (f₀ : X₀ ⟶ Y₀) (hf₀ : f₀ ≫ y = x)
    (hX₀ : IsAlgebraicSpace B S hS X₀) (hY₀ : IsAlgebraicSpace B S hS Y₀)
    (hX₀qc : IsQuasiCompactSpace B S hS X₀) (hY₀qc : IsQuasiCompactSpace B S hS Y₀)
    (hX₀qs : IsAbsolutelyQuasiSeparated B S hS hZ X₀)
    (hY₀qs : IsAbsolutelyQuasiSeparated B S hS hZ Y₀)
    (fp : IsLocallyOfFinitePresentation B S hS f₀)
    (iso : IsIso (pullback.map (limit.π D (op i₀)) x (limit.π D (op i₀)) y
      (𝟙 _) f₀ (𝟙 _) (by simp) (by simp [hf₀]))) :
    ∃ (i : I) (hi : i₀ ≤ i), IsIso (pullback.map (D.map (homOfLE hi).op) x
      (D.map (homOfLE hi).op) y (𝟙 _) f₀ (𝟙 _) (by simp) (by simp [hf₀])) := by
  set fL := pullback.map (limit.π D (op i₀)) x (limit.π D (op i₀)) y
      (𝟙 _) f₀ (𝟙 _) (by simp) (by simp [hf₀]) with hfL
  have hEt : IsEtale B S hS fL := isEtale_of_iso B S hS (asIso fL)
  have hUI : UniversallyInjective B S hS fL := universallyInjective_of_isIso B S hS _
  have hSurj : IsSurjective B S hS fL := by
    intro z
    refine ⟨pointsMap B S hS _ (inv fL) z, ?_⟩
    rw [← pointsMap_comp_apply, IsIso.inv_hom_id, pointsMap_id, id_eq]
  obtain ⟨i₁, hi₁, h₁⟩ := exists_isEtale_pullbackMap_of_isCutoffBoundedSystem B S hS hZ D hD
    hDalg hDaff i₀ x y f₀ hf₀ hX₀ hY₀ hX₀qc hY₀qc hY₀qs fp hEt
  obtain ⟨i₂, hi₂, h₂⟩ := exists_universallyInjective_pullbackMap_of_isCutoffBoundedSystem B S hS
    hZ D hD hDalg hDaff i₀ x y f₀ hf₀ hX₀ hY₀ hX₀qc hX₀qs hY₀qs
    (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS fp) hUI
  obtain ⟨i₃, hi₃, h₃⟩ := exists_isSurjective_pullbackMap_of_isCutoffBoundedSystem B S hS hZ D hD
    hDalg hDaff i₀ x y f₀ hf₀ hX₀ hY₀ hX₀qc hY₀qc hY₀qs fp hSurj
  obtain ⟨k, hk₁, hk₂⟩ := directed_of (· ≤ ·) i₁ i₂
  obtain ⟨j, hjk, hj₃⟩ := directed_of (· ≤ ·) k i₃
  have hj : i₀ ≤ j := hi₁.trans (hk₁.trans hjk)
  have halgX : ∀ {i : I} (hi : i₀ ≤ i),
      IsAlgebraicSpace B S hS (pullback (D.map (homOfLE hi).op) x) :=
    fun hi => isAlgebraicSpace_pullback B S hS _ x (hDalg _) hX₀ (hDalg i₀)
  have halgY : ∀ {i : I} (hi : i₀ ≤ i),
      IsAlgebraicSpace B S hS (pullback (D.map (homOfLE hi).op) y) :=
    fun hi => isAlgebraicSpace_pullback B S hS _ y (hDalg _) hY₀ (hDalg i₀)
  have hcomp : ∀ {i : I} (hi : i₀ ≤ i) (hij : i ≤ j),
      D.map (homOfLE hij).op ≫ D.map (homOfLE hi).op = D.map (homOfLE hj).op := fun hi hij => by
    rw [← D.map_comp]; exact congrArg D.map (Subsingleton.elim _ _)
  have htr : ∀ {i : I} (hi : i₀ ≤ i) (hij : i ≤ j), IsPullback
      (pullback.map (D.map (homOfLE hj).op) x (D.map (homOfLE hi).op) x (D.map (homOfLE hij).op)
        (𝟙 _) (𝟙 _) (by simp [hcomp hi hij]) (by simp))
      (pullback.map (D.map (homOfLE hj).op) x (D.map (homOfLE hj).op) y (𝟙 _) f₀ (𝟙 _)
        (by simp) (by simp [hf₀]))
      (pullback.map (D.map (homOfLE hi).op) x (D.map (homOfLE hi).op) y (𝟙 _) f₀ (𝟙 _)
        (by simp) (by simp [hf₀]))
      (pullback.map (D.map (homOfLE hj).op) y (D.map (homOfLE hi).op) y (D.map (homOfLE hij).op)
        (𝟙 _) (𝟙 _) (by simp [hcomp hi hij]) (by simp)) := fun hi hij =>
    isPullback_pullbackMap_of_comp_eq x y f₀ hf₀ _ _ _ (hcomp hi hij)
  have hEtj : IsEtale B S hS (pullback.map (D.map (homOfLE hj).op) x (D.map (homOfLE hj).op) y
      (𝟙 _) f₀ (𝟙 _) (by simp) (by simp [hf₀])) := by
    have hpb := htr hi₁ (hk₁.trans hjk)
    rw [← hpb.flip.isoPullback_hom_fst]
    exact isEtale_comp B S hS (isEtale_of_iso B S hS hpb.flip.isoPullback)
      (isEtale_pullback_fst B S hS (halgY hj) (halgY hi₁) (halgX hi₁) _ _ h₁)
  have hUIj : UniversallyInjective B S hS (pullback.map (D.map (homOfLE hj).op) x
      (D.map (homOfLE hj).op) y (𝟙 _) f₀ (𝟙 _) (by simp) (by simp [hf₀])) :=
    universallyInjective_of_isPullback B S hS (halgX hi₂) (halgY hj) (halgY hi₂) _ _ h₂
      (htr hi₂ (hk₂.trans hjk)).flip
  have hSurjj : IsSurjective B S hS (pullback.map (D.map (homOfLE hj).op) x
      (D.map (homOfLE hj).op) y (𝟙 _) f₀ (𝟙 _) (by simp) (by simp [hf₀])) :=
    surjective_pointsMap_of_isPullback B S hS (htr hi₃ hj₃) h₃
  exact ⟨j, hj, isIso_of_isEtale_of_universallyInjective_of_isSurjective B S hS (halgX hj)
    (halgY hj) _ hEtj hUIj hSurjj⟩

end AlgebraicGeometry.Space

end
