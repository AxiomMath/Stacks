module

public import StacksFrontier.AlgebraicGeometry.Descent.FlatCoproductRefinement
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.RelativeHomGlue
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableModelHomExt

/-!
# Gluing local isomorphisms of stable models

Two stable models `c₁ : X ⟶ Y₁` and `c₂ : X ⟶ Y₂` of the same family of curves `X ⟶ S` which are
isomorphic, compatibly with the contractions, over the members of an étale covering of `S` are
isomorphic over `S`: this is the gluing step at the end of the proof of Stacks 0E8A, whose local
input is Stacks 0E89. The local isomorphisms agree on overlaps because morphisms between stable
models are unique (`AlgebraicGeometry.C1590Private.IsStableModel.hom_ext`, in the form
`AlgebraicGeometry.C1590Private.eq_of_comp_eq_of_isIso_structureSharp`), and they glue by the sheaf
property of the relative morphism functor (Stacks 05Y3,
`AlgebraicGeometry.C1590Private.exists_hom_of_local`).

## Main results

* `AlgebraicGeometry.C1590Private.IsStableModel.exists_totalMap_of_local`: compatible local
  morphisms of base changes glue to a morphism of total spaces compatible with the contractions.
* `AlgebraicGeometry.C1590Private.IsStableModel.exists_hom_of_locallyIso`: local isomorphisms
  glue to a morphism of families of curves `Y₁ ⟶ Y₂` compatible with the base maps and with the
  contractions.

## References

* [Stacks Project, Tag 0E8A](https://stacks.math.columbia.edu/tag/0E8A)
* [Stacks Project, Tag 0E89](https://stacks.math.columbia.edu/tag/0E89)
* [Stacks Project, Tag 05Y3](https://stacks.math.columbia.edu/tag/05Y3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.C1590Private

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- The local hypothesis of the gluing statements: around every point of the base of `X` there is
an étale `U ⟶ X.base` over which the base changes of the two targets admit a morphism over `U`,
compatible with the base changes of the two contractions. -/
def LocalModelHoms (X Y₁ Y₂ : CurveFamily B hZ) (b₁ : X.base ⟶ Y₁.base) (c₁ : X.total ⟶ Y₁.total)
    (b₂ : X.base ⟶ Y₂.base) (c₂ : X.total ⟶ Y₂.total) : Prop :=
  ∀ s : (BigFppfOver.toScheme B integerBase hZ).obj X.base,
    ∃ (U : BigFppfOver B integerBase hZ) (e : U ⟶ X.base),
      Etale ((BigFppfOver.toScheme B integerBase hZ).map e) ∧
      s ∈ Set.range ((BigFppfOver.toScheme B integerBase hZ).map e) ∧
      ∀ ⦃A₁ A₂ : AlgebraicSpaces B integerBase hZ⦄ (j₁ : A₁ ⟶ Y₁.total) (j₂ : A₂ ⟶ Y₂.total)
        (p₁ : A₁ ⟶ schemeSpace U) (p₂ : A₂ ⟶ schemeSpace U),
        IsPullback j₁ p₁ Y₁.toBase (schemeSpaceMap (e ≫ b₁)) →
        IsPullback j₂ p₂ Y₂.toBase (schemeSpaceMap (e ≫ b₂)) →
        ∃ θ : A₁ ⟶ A₂, θ ≫ p₂ = p₁ ∧
          ∀ ⦃A : AlgebraicSpaces B integerBase hZ⦄ (jX : A ⟶ X.total) (pX : A ⟶ schemeSpace U)
            (a₁ : A ⟶ A₁) (a₂ : A ⟶ A₂), IsPullback jX pX X.toBase (schemeSpaceMap e) →
            a₁ ≫ j₁ = jX ≫ c₁ → a₁ ≫ p₁ = pX → a₂ ≫ j₂ = jX ≫ c₂ → a₂ ≫ p₂ = pX →
            a₁ ≫ θ = a₂

/-- A jointly surjective family of étale morphisms to `X`, followed by an isomorphism `X ≅ Y`,
generates a covering sieve of `Y` in the big fppf site. -/
theorem ofArrows_comp_mem_topology {X Y : BigFppfOver B integerBase hZ} (b : X ⟶ Y) [IsIso b]
    {I : Type u} (U : I → BigFppfOver B integerBase hZ) (e : ∀ i, U i ⟶ X)
    (hopen : ∀ i, Etale ((BigFppfOver.toScheme B integerBase hZ).map (e i)))
    (hcov : ∀ x : (BigFppfOver.toScheme B integerBase hZ).obj X,
      ∃ i, x ∈ Set.range ((BigFppfOver.toScheme B integerBase hZ).map (e i))) :
    Sieve.ofArrows U (fun i => e i ≫ b) ∈ BigFppfOver.topology B integerBase hZ Y := by
  refine BigFppfOver.ofArrows_mem_topology_of_flat_lfp B integerBase hZ U _ (fun y => ?_)
    (fun i => ?_) (fun i => ?_)
  · obtain ⟨i, x, hx⟩ := hcov ((BigFppfOver.toScheme B integerBase hZ).map (inv b) y)
    refine ⟨i, x, ?_⟩
    have hb : (BigFppfOver.toScheme B integerBase hZ).map (inv b) ≫
        (BigFppfOver.toScheme B integerBase hZ).map b = 𝟙 _ := by
      rw [← CategoryTheory.Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id]
    rw [CategoryTheory.Functor.map_comp]
    change ((BigFppfOver.toScheme B integerBase hZ).map (e i) ≫
      (BigFppfOver.toScheme B integerBase hZ).map b) x = y
    rw [Scheme.Hom.comp_apply, hx, ← Scheme.Hom.comp_apply, hb]
    rfl
  · have := hopen i
    rw [CategoryTheory.Functor.map_comp]
    infer_instance
  · have := hopen i
    rw [CategoryTheory.Functor.map_comp]
    infer_instance

/-- The morphism `Y.total ⟶ Y.base` of a family of curves, as a morphism of presheaves into the
representable presheaf of the base. It is `Y.toBase.hom`, typed through Yoneda so that fibre
products along morphisms `yoneda.map v` are formed with matching types. -/
def yonedaToBase (Y : CurveFamily B hZ) : Y.total.obj ⟶ yoneda.obj Y.base := Y.toBase.hom

variable {g : ℕ} {X Y₁ Y₂ : CurveFamily B hZ} {b₁ : X.base ⟶ Y₁.base} {c₁ : X.total ⟶ Y₁.total}
  {b₂ : X.base ⟶ Y₂.base} {c₂ : X.total ⟶ Y₂.total}

/-- The base change `W ×_{Y.base} Y.total` of a family of curves along `v : W ⟶ Y.base`, formed
through Yoneda, as an algebraic space. -/
private noncomputable def yonedaPullback (Y : CurveFamily B hZ) {W : BigFppfOver B integerBase hZ}
    (v : W ⟶ Y.base) : AlgebraicSpaces B integerBase hZ :=
  ⟨pullback (yoneda.map v) (yonedaToBase Y), isAlgebraicSpace_pullback B integerBase hZ _ _
    (isAlgebraicSpace_yoneda B integerBase hZ _) Y.total.2
    (isAlgebraicSpace_yoneda B integerBase hZ _)⟩

/-- The presheaf pullback along `yoneda.map v` is a pullback of algebraic spaces. -/
private theorem isPullback_yonedaPullback (Y : CurveFamily B hZ) {W : BigFppfOver B integerBase hZ}
    (v : W ⟶ Y.base) :
    IsPullback
      (ObjectProperty.homMk (pullback.snd (yoneda.map v) (yonedaToBase Y)) :
        yonedaPullback Y v ⟶ Y.total)
      (ObjectProperty.homMk (pullback.fst (yoneda.map v) (yonedaToBase Y)) :
        yonedaPullback Y v ⟶ schemeSpace W)
      Y.toBase (schemeSpaceMap v) :=
  IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ pullback.condition.symm)
    (IsPullback.of_hasPullback (yoneda.map v) (yonedaToBase Y)).flip

/-- **Morphisms out of a base change of a stable model are determined by the contraction.** Two
morphisms `u, u' : W ×_{Y₁.base} Y₁ ⟶ Y₂` over a common morphism to `Y₂.base` which agree after
every morphism into `W ×_{Y₁.base} Y₁` factoring through the base change of `c₁` are equal: the
base change of `c₁` to `W` still has `𝒪 ≅ c_*𝒪` (condition (1) of Stacks 0E8A), and
`AlgebraicGeometry.C1590Private.eq_of_comp_eq_of_isIso_structureSharp` applies. -/
theorem IsStableModel.eq_of_forall_lift_comp (h₁ : IsStableModel B hZ g b₁ c₁)
    {W : BigFppfOver B integerBase hZ} (v : W ⟶ Y₁.base)
    {u u' : pullback (yoneda.map v) (yonedaToBase Y₁) ⟶ Y₂.total.obj}
    (hu : u ≫ yonedaToBase Y₂ = u' ≫ yonedaToBase Y₂)
    (hk : ∀ {R : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} (w : R ⟶ yoneda.obj W)
      (xR : R ⟶ X.total.obj) (hw : w ≫ yoneda.map v = (xR ≫ c₁.hom) ≫ yonedaToBase Y₁),
      pullback.lift w (xR ≫ c₁.hom) hw ≫ u = pullback.lift w (xR ≫ c₁.hom) hw ≫ u') :
    u = u' := by
  let D := yonedaPullback Y₁ v
  have hD := isPullback_yonedaPullback Y₁ v
  have hXW := AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ c₁
    (ObjectProperty.homMk (pullback.snd (yoneda.map v) (yonedaToBase Y₁)) : D ⟶ Y₁.total)
  have hA := hXW.paste_vert hD
  have hiso := (h₁.universallyAcyclic v _ _ _ _ hD hA hXW.w.symm).1
  refine congrArg (fun k => k.hom) (eq_of_comp_eq_of_isIso_structureSharp _ hiso Y₂.toBase
    Y₂.proper.1 (u := ObjectProperty.homMk u) (v := ObjectProperty.homMk u')
    (ObjectProperty.hom_ext _ hu) (ObjectProperty.hom_ext _ ?_))
  let sD : D ⟶ Y₁.total := ObjectProperty.homMk (pullback.snd (yoneda.map v) (yonedaToBase Y₁))
  have hw : (pullback.snd c₁.hom sD.hom ≫ pullback.fst (yoneda.map v) (yonedaToBase Y₁)) ≫
      yoneda.map v = (pullback.fst c₁.hom sD.hom ≫ c₁.hom) ≫ yonedaToBase Y₁ :=
    (congrArg (fun k => k.hom) hA.w).symm
  have hc : pullback.snd c₁.hom sD.hom ≫ pullback.snd (yoneda.map v) (yonedaToBase Y₁) =
      pullback.fst c₁.hom sD.hom ≫ c₁.hom := (congrArg (fun k => k.hom) hXW.w).symm
  have hl : pullback.snd c₁.hom sD.hom = pullback.lift _ _ hw :=
    pullback.hom_ext (pullback.lift_fst _ _ _).symm (hc.trans (pullback.lift_snd _ _ _).symm)
  change pullback.snd c₁.hom sD.hom ≫ u = pullback.snd c₁.hom sD.hom ≫ u'
  rw [hl]
  exact hk _ _ hw

/-- **Local morphisms of stable models agree on overlaps.** Two morphisms `μᵢ, μⱼ` from base
changes of `Y₁` to `Y₂`, over `Y₁.base` through an isomorphism `f'`, which are compatible with
the contractions, agree after restriction to any `W` mapping compatibly to their two bases. -/
theorem IsStableModel.local_compat (h₁ : IsStableModel B hZ g b₁ c₁) (f' : Y₂.base ⟶ Y₁.base)
    [IsIso f'] {Ui Uj W : BigFppfOver B integerBase hZ} (vi : Ui ⟶ Y₁.base) (vj : Uj ⟶ Y₁.base)
    (gi : W ⟶ Ui) (gj : W ⟶ Uj)
    (h : yoneda.map gi ≫ yoneda.map vi = yoneda.map gj ≫ yoneda.map vj)
    (μi : pullback (yoneda.map vi) (yonedaToBase Y₁) ⟶ Y₂.total.obj)
    (μj : pullback (yoneda.map vj) (yonedaToBase Y₁) ⟶ Y₂.total.obj)
    (hμi : μi ≫ yonedaToBase Y₂ ≫ yoneda.map f' = pullback.snd _ _ ≫ yonedaToBase Y₁)
    (hμj : μj ≫ yonedaToBase Y₂ ≫ yoneda.map f' = pullback.snd _ _ ≫ yonedaToBase Y₁)
    (keyi : ∀ {R : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} (w : R ⟶ yoneda.obj Ui)
      (xR : R ⟶ X.total.obj) (hw : w ≫ yoneda.map vi = (xR ≫ c₁.hom) ≫ yonedaToBase Y₁),
      pullback.lift w (xR ≫ c₁.hom) hw ≫ μi = xR ≫ c₂.hom)
    (keyj : ∀ {R : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} (w : R ⟶ yoneda.obj Uj)
      (xR : R ⟶ X.total.obj) (hw : w ≫ yoneda.map vj = (xR ≫ c₁.hom) ≫ yonedaToBase Y₁),
      pullback.lift w (xR ≫ c₁.hom) hw ≫ μj = xR ≫ c₂.hom)
    (hgi' : (pullback.fst (yoneda.map gi ≫ yoneda.map vi) (yonedaToBase Y₁) ≫ yoneda.map gi) ≫
        yoneda.map vi =
      pullback.snd (yoneda.map gi ≫ yoneda.map vi) (yonedaToBase Y₁) ≫ (yonedaToBase Y₁))
    (hgj' : (pullback.fst (yoneda.map gi ≫ yoneda.map vi) (yonedaToBase Y₁) ≫ yoneda.map gj) ≫
        yoneda.map vj =
      pullback.snd (yoneda.map gi ≫ yoneda.map vi) (yonedaToBase Y₁) ≫ (yonedaToBase Y₁)) :
    pullback.lift (pullback.fst (yoneda.map gi ≫ yoneda.map vi) (yonedaToBase Y₁) ≫ yoneda.map gi)
        (pullback.snd (yoneda.map gi ≫ yoneda.map vi) (yonedaToBase Y₁)) hgi' ≫ μi =
      pullback.lift (pullback.fst (yoneda.map gi ≫ yoneda.map vi) (yonedaToBase Y₁) ≫
          yoneda.map gj) (pullback.snd (yoneda.map gi ≫ yoneda.map vi) (yonedaToBase Y₁)) hgj' ≫
          μj := by
  have hfy : IsIso (yoneda.map f') := Functor.map_isIso _ _
  have ha : yoneda.map (gi ≫ vi) = yoneda.map gi ≫ yoneda.map vi := Functor.map_comp _ _ _
  have hci : (pullback.fst (yoneda.map (gi ≫ vi)) (yonedaToBase Y₁) ≫ yoneda.map gi) ≫
      yoneda.map vi = pullback.snd (yoneda.map (gi ≫ vi)) (yonedaToBase Y₁) ≫ yonedaToBase Y₁ := by
    rw [Category.assoc, ← ha, pullback.condition]
  have hcj : (pullback.fst (yoneda.map (gi ≫ vi)) (yonedaToBase Y₁) ≫ yoneda.map gj) ≫
      yoneda.map vj = pullback.snd (yoneda.map (gi ≫ vi)) (yonedaToBase Y₁) ≫ yonedaToBase Y₁ := by
    rw [Category.assoc, ← h, ← ha, pullback.condition]
  have hcomp : ∀ {U' : BigFppfOver B integerBase hZ} (gk : W ⟶ U') (vk : U' ⟶ Y₁.base)
      (hgk : (pullback.fst (yoneda.map (gi ≫ vi)) (yonedaToBase Y₁) ≫ yoneda.map gk) ≫
          yoneda.map vk = pullback.snd (yoneda.map (gi ≫ vi)) (yonedaToBase Y₁) ≫ (yonedaToBase Y₁))
      (μk : pullback (yoneda.map vk) (yonedaToBase Y₁) ⟶ Y₂.total.obj)
      (keyk : ∀ {R : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} (w : R ⟶ yoneda.obj U')
        (xR : R ⟶ X.total.obj) (hw : w ≫ yoneda.map vk = (xR ≫ c₁.hom) ≫ (yonedaToBase Y₁)),
        pullback.lift w (xR ≫ c₁.hom) hw ≫ μk = xR ≫ c₂.hom)
      {R : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} (w : R ⟶ yoneda.obj W)
      (xR : R ⟶ X.total.obj) (hw : w ≫ yoneda.map (gi ≫ vi) = (xR ≫ c₁.hom) ≫ (yonedaToBase Y₁))
      (hw' : (w ≫ yoneda.map gk) ≫ yoneda.map vk = (xR ≫ c₁.hom) ≫ (yonedaToBase Y₁)),
      pullback.lift w (xR ≫ c₁.hom) hw ≫ pullback.lift (pullback.fst (yoneda.map (gi ≫ vi))
          (yonedaToBase Y₁) ≫ yoneda.map gk) (pullback.snd (yoneda.map (gi ≫ vi))
          (yonedaToBase Y₁)) hgk ≫ μk =
        xR ≫ c₂.hom := by
    intro U' gk vk hgk μk keyk R w xR hw hw'
    have e : pullback.lift w (xR ≫ c₁.hom) hw ≫ pullback.lift (pullback.fst (yoneda.map (gi ≫ vi))
        (yonedaToBase Y₁) ≫ yoneda.map gk) (pullback.snd (yoneda.map (gi ≫ vi)) (yonedaToBase Y₁))
        hgk =
        pullback.lift (w ≫ yoneda.map gk) (xR ≫ c₁.hom) hw' := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst,
          pullback.lift_fst]
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ μk) e).trans (keyk _ _ hw'))
  have hwk : ∀ {U' : BigFppfOver B integerBase hZ} (gk : W ⟶ U') (vk : U' ⟶ Y₁.base),
      gk ≫ vk = gi ≫ vi → ∀ {R : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u}
      (w : R ⟶ yoneda.obj W) (xR : R ⟶ X.total.obj),
      w ≫ yoneda.map (gi ≫ vi) = (xR ≫ c₁.hom) ≫ (yonedaToBase Y₁) →
      (w ≫ yoneda.map gk) ≫ yoneda.map vk = (xR ≫ c₁.hom) ≫ (yonedaToBase Y₁) := by
    intro U' gk vk hk R w xR hw
    rw [Category.assoc, ← Functor.map_comp, hk, hw]
  have hij : gj ≫ vj = gi ≫ vi := by
    apply Yoneda.fullyFaithful.map_injective
    rw [Functor.map_comp, Functor.map_comp, h]
  have hmain : pullback.lift (pullback.fst (yoneda.map (gi ≫ vi)) (yonedaToBase Y₁) ≫
      yoneda.map gi) (pullback.snd (yoneda.map (gi ≫ vi)) (yonedaToBase Y₁)) hci ≫ μi =
      pullback.lift (pullback.fst (yoneda.map (gi ≫ vi)) (yonedaToBase Y₁) ≫ yoneda.map gj)
          (pullback.snd (yoneda.map (gi ≫ vi)) (yonedaToBase Y₁)) hcj ≫ μj := by
    refine h₁.eq_of_forall_lift_comp (gi ≫ vi) ?_ fun w xR hw => ?_
    · refine (cancel_mono (yoneda.map f')).1 ?_
      simp only [Category.assoc, hμi, hμj, pullback.lift_snd_assoc]
    · exact (hcomp gi vi hci μi keyi w xR hw (hwk gi vi rfl w xR hw)).trans
        (hcomp gj vj hcj μj keyj w xR hw (hwk gj vj hij w xR hw)).symm
  have hcongr : ∀ {U' : BigFppfOver B integerBase hZ} (gk : W ⟶ U') (vk : U' ⟶ Y₁.base)
      (hgk : (pullback.fst (yoneda.map (gi ≫ vi)) (yonedaToBase Y₁) ≫ yoneda.map gk) ≫
          yoneda.map vk = pullback.snd (yoneda.map (gi ≫ vi)) (yonedaToBase Y₁) ≫ (yonedaToBase Y₁))
      (hgk' : (pullback.fst (yoneda.map gi ≫ yoneda.map vi) (yonedaToBase Y₁) ≫ yoneda.map gk) ≫
          yoneda.map vk =
        pullback.snd (yoneda.map gi ≫ yoneda.map vi) (yonedaToBase Y₁) ≫ (yonedaToBase Y₁)),
      pullback.lift (pullback.fst (yoneda.map gi ≫ yoneda.map vi) (yonedaToBase Y₁) ≫
          yoneda.map gk) (pullback.snd (yoneda.map gi ≫ yoneda.map vi) (yonedaToBase Y₁)) hgk' =
        (pullback.congrHom ha.symm rfl).hom ≫ pullback.lift (pullback.fst (yoneda.map (gi ≫ vi))
            (yonedaToBase Y₁) ≫ yoneda.map gk) (pullback.snd (yoneda.map (gi ≫ vi))
            (yonedaToBase Y₁)) hgk := by
    intro U' gk vk hgk hgk'
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.congrHom_hom, pullback.lift_fst_assoc,
        Category.id_comp]
    · simp only [Category.assoc, pullback.lift_snd, pullback.congrHom_hom, Category.comp_id]
  exact (congrArg (· ≫ μi) (hcongr gi vi hci hgi')).trans ((Category.assoc _ _ _).trans
    ((congrArg ((pullback.congrHom ha.symm rfl).hom ≫ ·) hmain).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ μj) (hcongr gj vj hcj hgj')).symm)))

/-- **Local morphisms of stable models glue.** If two stable models `c₁ : X ⟶ Y₁` and
`c₂ : X ⟶ Y₂` admit, over the members of an étale covering of the base, morphisms of the base
changes of `Y₁` and `Y₂` compatible with the contractions, then there is a morphism of total spaces
`Y₁ ⟶ Y₂` over the isomorphism of bases `b₁⁻¹ ≫ b₂`, compatible with the contractions. -/
theorem IsStableModel.exists_totalMap_of_local (h₁ : IsStableModel B hZ g b₁ c₁)
    (h₂ : IsStableModel B hZ g b₂ c₂) (hloc : LocalModelHoms X Y₁ Y₂ b₁ c₁ b₂ c₂) :
    ∃ (f : Y₁.base ⟶ Y₂.base) (m : Y₁.total ⟶ Y₂.total),
      b₁ ≫ f = b₂ ∧ m ≫ Y₂.toBase = Y₁.toBase ≫ schemeSpaceMap f ∧ c₁ ≫ m = c₂ := by
  have := h₁.isIso_base
  have := h₂.isIso_base
  choose U e hopen hmem hθ using hloc
  -- the structure morphisms, typed through Yoneda so that all fibre products are formed alike
  let tX : X.total.obj ⟶ yoneda.obj X.base := yonedaToBase X
  let z : Y₁.total.obj ⟶ yoneda.obj Y₁.base := yonedaToBase Y₁
  let t₂ : Y₂.total.obj ⟶ yoneda.obj Y₂.base := yonedaToBase Y₂
  let x := t₂ ≫ yoneda.map (inv b₂ ≫ b₁)
  let v := fun s => e s ≫ b₁
  have hv : Sieve.ofArrows U v ∈ BigFppfOver.topology B integerBase hZ Y₁.base :=
    ofArrows_comp_mem_topology b₁ U e hopen (fun s => ⟨s, hmem s⟩)
  choose θ hθp hθc using fun s => hθ s _ _ _ _ (isPullback_yonedaPullback Y₁ (v s))
    (isPullback_yonedaPullback Y₂ (e s ≫ b₂))
  have hb₁y : IsIso (yoneda.map b₁) := Functor.map_isIso _ _
  have hc₁ : c₁.hom ≫ z = tX ≫ yoneda.map b₁ := congrArg (fun k => k.hom) h₁.comp_toBase
  have hc₂ : c₂.hom ≫ t₂ = tX ≫ yoneda.map b₂ := congrArg (fun k => k.hom) h₂.comp_toBase
  let μ : ∀ s, pullback (yoneda.map (v s)) z ⟶ Y₂.total.obj := fun s =>
    (θ s ≫ ObjectProperty.homMk (pullback.snd _ _)).hom
  -- the local morphisms are compatible with the contractions
  have key : ∀ s {R : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} (w : R ⟶ yoneda.obj (U s))
      (xR : R ⟶ X.total.obj) (hw : w ≫ yoneda.map (v s) = (xR ≫ c₁.hom) ≫ z),
      pullback.lift w (xR ≫ c₁.hom) hw ≫ μ s = xR ≫ c₂.hom := by
    intro s R w xR hw
    let XU := yonedaPullback X (e s)
    have hpbX := isPullback_yonedaPullback X (e s)
    have h₁w : pullback.fst (yoneda.map (e s)) tX ≫ yoneda.map (v s) =
        (pullback.snd (yoneda.map (e s)) tX ≫ c₁.hom) ≫ z := by
      rw [Category.assoc, hc₁, ← Category.assoc, ← pullback.condition, Category.assoc,
        ← Functor.map_comp]
    have h₂w : pullback.fst (yoneda.map (e s)) tX ≫ yoneda.map (e s ≫ b₂) =
        (pullback.snd (yoneda.map (e s)) tX ≫ c₂.hom) ≫ t₂ := by
      rw [Category.assoc, hc₂, ← Category.assoc, ← pullback.condition, Category.assoc,
        ← Functor.map_comp]
    let a₁ : XU ⟶ yonedaPullback Y₁ (v s) := ObjectProperty.homMk (pullback.lift _ _ h₁w)
    let a₂ : XU ⟶ yonedaPullback Y₂ (e s ≫ b₂) := ObjectProperty.homMk (pullback.lift _ _ h₂w)
    have hθa := hθc s _ _ a₁ a₂ hpbX
      (ObjectProperty.hom_ext _ (pullback.lift_snd _ _ _))
      (ObjectProperty.hom_ext _ (pullback.lift_fst _ _ _))
      (ObjectProperty.hom_ext _ (pullback.lift_snd _ _ _))
      (ObjectProperty.hom_ext _ (pullback.lift_fst _ _ _))
    have hr : w ≫ yoneda.map (e s) = xR ≫ tX := by
      rw [← cancel_mono (yoneda.map b₁), Category.assoc, ← Functor.map_comp]
      exact hw.trans (by rw [Category.assoc, Category.assoc, hc₁])
    have hlift : pullback.lift w (xR ≫ c₁.hom) hw =
        pullback.lift w xR hr ≫ pullback.lift _ _ h₁w := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, pullback.lift_fst]
      · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, ← Category.assoc,
          pullback.lift_snd]
    have hθa' := congrArg (fun k => (k ≫ ObjectProperty.homMk (pullback.snd _ _) :
      XU ⟶ Y₂.total).hom) hθa
    change pullback.lift _ _ h₁w ≫ μ s = pullback.lift _ _ h₂w ≫ pullback.snd _ _ at hθa'
    rw [hlift, Category.assoc, hθa', pullback.lift_snd, ← Category.assoc, pullback.lift_snd]
  have hμ₂ : ∀ s, μ s ≫ t₂ = pullback.fst _ _ ≫ yoneda.map (e s ≫ b₂) := fun s =>
    congrArg (fun k => k.hom) (show (θ s ≫ ObjectProperty.homMk (pullback.snd _ _)) ≫ Y₂.toBase =
        (ObjectProperty.homMk (pullback.fst _ _) : yonedaPullback Y₁ (v s) ⟶ schemeSpace (U s)) ≫
          schemeSpaceMap (e s ≫ b₂) by
      rw [Category.assoc, (isPullback_yonedaPullback Y₂ (e s ≫ b₂)).w, ← Category.assoc, hθp s])
  have hμ : ∀ s, μ s ≫ x = pullback.snd (yoneda.map (v s)) z ≫ z := by
    intro s
    rw [← Category.assoc, hμ₂, Category.assoc, ← Functor.map_comp, ← pullback.condition]
    congr 2
    simp [v]
  have hfy : IsIso (yoneda.map (inv b₂ ≫ b₁)) := Functor.map_isIso _ _
  have hglue := exists_hom_of_local Y₁.total.2 Y₂.total.2 z x U v hv μ hμ
  obtain ⟨m₀, hm₀, hm₀μ⟩ := hglue fun i j W gi gj h =>
    h₁.local_compat (inv b₂ ≫ b₁) (v i) (v j) gi gj h (μ i) (μ j) (hμ i) (hμ j) (key i) (key j)
      _ _
  refine ⟨inv b₁ ≫ b₂, ObjectProperty.homMk m₀, by simp, ?_, ?_⟩
  · apply ObjectProperty.hom_ext
    change m₀ ≫ t₂ = z ≫ yoneda.map (inv b₁ ≫ b₂)
    rw [← hm₀, Category.assoc, Category.assoc, ← Functor.map_comp]
    simp
  · apply ObjectProperty.hom_ext
    change c₁.hom ≫ m₀ = c₂.hom
    refine hom_ext_of_local Y₂.total.2.isSheaf (c₁.hom ≫ z) U v hv fun s => ?_
    have hw : pullback.fst (yoneda.map (v s)) (c₁.hom ≫ z) ≫ yoneda.map (v s) =
        (pullback.snd _ _ ≫ c₁.hom) ≫ z := by
      rw [pullback.condition, Category.assoc]
    have hl : pullback.snd (yoneda.map (v s)) (c₁.hom ≫ z) ≫ c₁.hom =
        pullback.lift _ _ hw ≫ pullback.snd (yoneda.map (v s)) z :=
      (pullback.lift_snd _ _ _).symm
    rw [← Category.assoc, hl, Category.assoc, hm₀μ s, key]

/-- `schemeSpaceMap` preserves identities. -/
private theorem schemeSpaceMap_id_eq (T : BigFppfOver B integerBase hZ) :
    schemeSpaceMap (𝟙 T) = 𝟙 _ :=
  (schemeSpaceFunctor B integerBase hZ).map_id T

/-- Morphisms of total spaces compatible with the contractions and with mutually inverse maps of
bases are mutually inverse, by uniqueness of morphisms out of a stable model. -/
private theorem IsStableModel.comp_eq_id_of_comp_eq_id (h₁ : IsStableModel B hZ g b₁ c₁)
    {f : Y₁.base ⟶ Y₂.base} {f' : Y₂.base ⟶ Y₁.base} {m : Y₁.total ⟶ Y₂.total}
    {m' : Y₂.total ⟶ Y₁.total} (hff' : f ≫ f' = 𝟙 _)
    (hm : m ≫ Y₂.toBase = Y₁.toBase ≫ schemeSpaceMap f)
    (hm' : m' ≫ Y₁.toBase = Y₂.toBase ≫ schemeSpaceMap f') (hcm : c₁ ≫ m = c₂)
    (hcm' : c₂ ≫ m' = c₁) : m ≫ m' = 𝟙 _ :=
  eq_of_comp_eq_of_isIso_structureSharp c₁ h₁.isIso_structureSharp Y₁.toBase Y₁.proper.1
    (by rw [Category.assoc, hm', reassoc_of% hm, ← schemeSpaceMap_comp, hff',
      schemeSpaceMap_id_eq, Category.comp_id, Category.id_comp])
    (by rw [reassoc_of% hcm, hcm', Category.comp_id])

/-- **Local isomorphisms of stable models glue** (the gluing step of the proof of Stacks 0E8A).
Let `c₁ : X ⟶ Y₁` and `c₂ : X ⟶ Y₂` be stable models of genus `g` of the same family. Suppose that
every point of the base of `X` is in the image of an étale `e : U ⟶ X.base` over which the base
changes of `Y₁` and `Y₂` are isomorphic over `U`, compatibly with the base changes of `c₁` and
`c₂`. Then there is a morphism of families `Y₁ ⟶ Y₂` compatible with the base maps and with the
contractions. -/
theorem IsStableModel.exists_hom_of_locallyIso (h₁ : IsStableModel B hZ g b₁ c₁)
    (h₂ : IsStableModel B hZ g b₂ c₂)
    (hloc : ∀ s : (BigFppfOver.toScheme B integerBase hZ).obj X.base,
      ∃ (U : BigFppfOver B integerBase hZ) (e : U ⟶ X.base),
        Etale ((BigFppfOver.toScheme B integerBase hZ).map e) ∧
        s ∈ Set.range ((BigFppfOver.toScheme B integerBase hZ).map e) ∧
        ∀ ⦃A₁ A₂ : AlgebraicSpaces B integerBase hZ⦄ (j₁ : A₁ ⟶ Y₁.total) (j₂ : A₂ ⟶ Y₂.total)
          (p₁ : A₁ ⟶ schemeSpace U) (p₂ : A₂ ⟶ schemeSpace U),
          IsPullback j₁ p₁ Y₁.toBase (schemeSpaceMap (e ≫ b₁)) →
          IsPullback j₂ p₂ Y₂.toBase (schemeSpaceMap (e ≫ b₂)) →
          ∃ θ : A₁ ≅ A₂, θ.hom ≫ p₂ = p₁ ∧
            ∀ ⦃A : AlgebraicSpaces B integerBase hZ⦄ (jX : A ⟶ X.total) (pX : A ⟶ schemeSpace U)
              (a₁ : A ⟶ A₁) (a₂ : A ⟶ A₂), IsPullback jX pX X.toBase (schemeSpaceMap e) →
              a₁ ≫ j₁ = jX ≫ c₁ → a₁ ≫ p₁ = pX → a₂ ≫ j₂ = jX ≫ c₂ → a₂ ≫ p₂ = pX →
              a₁ ≫ θ.hom = a₂) :
    ∃ e : Y₁ ⟶ Y₂, b₁ ≫ e.baseMap = b₂ ∧ c₁ ≫ e.totalMap = c₂ := by
  have := h₁.isIso_base
  have := h₂.isIso_base
  have H₁₂ : LocalModelHoms X Y₁ Y₂ b₁ c₁ b₂ c₂ := fun s => by
    obtain ⟨U, e, he, hs, hθ⟩ := hloc s
    refine ⟨U, e, he, hs, fun A₁ A₂ j₁ j₂ p₁ p₂ hp₁ hp₂ => ?_⟩
    obtain ⟨θ, hθp, hθc⟩ := hθ j₁ j₂ p₁ p₂ hp₁ hp₂
    exact ⟨θ.hom, hθp, hθc⟩
  have H₂₁ : LocalModelHoms X Y₂ Y₁ b₂ c₂ b₁ c₁ := fun s => by
    obtain ⟨U, e, he, hs, hθ⟩ := hloc s
    refine ⟨U, e, he, hs, fun A₂ A₁ j₂ j₁ p₂ p₁ hp₂ hp₁ => ?_⟩
    obtain ⟨θ, hθp, hθc⟩ := hθ j₁ j₂ p₁ p₂ hp₁ hp₂
    refine ⟨θ.inv, by rw [← hθp, Iso.inv_hom_id_assoc], fun A jX pX a₂ a₁ hX h₂j h₂p h₁j h₁p => ?_⟩
    rw [← hθc jX pX a₁ a₂ hX h₁j h₁p h₂j h₂p, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  obtain ⟨f, m, hf, hm, hcm⟩ := h₁.exists_totalMap_of_local h₂ H₁₂
  obtain ⟨f', m', hf', hm', hcm'⟩ := h₂.exists_totalMap_of_local h₁ H₂₁
  have hff' : f ≫ f' = 𝟙 _ := by
    rw [← cancel_epi b₁, reassoc_of% hf, hf', Category.comp_id]
  have hf'f : f' ≫ f = 𝟙 _ := by
    rw [← cancel_epi b₂, reassoc_of% hf', hf, Category.comp_id]
  have hmm' := h₁.comp_eq_id_of_comp_eq_id hff' hm hm' hcm hcm'
  have hm'm := h₂.comp_eq_id_of_comp_eq_id hf'f hm' hm hcm' hcm
  have : IsIso m := ⟨m', hmm', hm'm⟩
  have : IsIso (schemeSpaceMap f) := ⟨schemeSpaceMap f',
    by rw [← schemeSpaceMap_comp, hff', schemeSpaceMap_id_eq],
    by rw [← schemeSpaceMap_comp, hf'f, schemeSpaceMap_id_eq]⟩
  exact ⟨⟨f, m, IsPullback.of_horiz_isIso ⟨hm⟩⟩, hf, hcm⟩

/-- **Local isomorphisms of stable models glue**, in the form where the isomorphism over each
member of the covering may depend on the chosen presentation of the base change of `X`. This is
`AlgebraicGeometry.C1590Private.IsStableModel.exists_hom_of_locallyIso`: any two presentations of
the base change of `X` are isomorphic, and the compatibility condition is transported along that
isomorphism. -/
theorem IsStableModel.exists_hom_of_locallyIso' (h₁ : IsStableModel B hZ g b₁ c₁)
    (h₂ : IsStableModel B hZ g b₂ c₂)
    (hloc : ∀ s : (BigFppfOver.toScheme B integerBase hZ).obj X.base,
      ∃ (U : BigFppfOver B integerBase hZ) (e : U ⟶ X.base),
        Etale ((BigFppfOver.toScheme B integerBase hZ).map e) ∧
        s ∈ Set.range ((BigFppfOver.toScheme B integerBase hZ).map e) ∧
        ∀ ⦃A₁ A₂ A : AlgebraicSpaces B integerBase hZ⦄ (j₁ : A₁ ⟶ Y₁.total)
          (p₁ : A₁ ⟶ schemeSpace U) (j₂ : A₂ ⟶ Y₂.total) (p₂ : A₂ ⟶ schemeSpace U)
          (jX : A ⟶ X.total) (pX : A ⟶ schemeSpace U),
          IsPullback j₁ p₁ Y₁.toBase (schemeSpaceMap (e ≫ b₁)) →
          IsPullback j₂ p₂ Y₂.toBase (schemeSpaceMap (e ≫ b₂)) →
          IsPullback jX pX X.toBase (schemeSpaceMap e) →
          ∃ θ : A₁ ≅ A₂, θ.hom ≫ p₂ = p₁ ∧ ∀ (a₁ : A ⟶ A₁) (a₂ : A ⟶ A₂),
            a₁ ≫ j₁ = jX ≫ c₁ → a₁ ≫ p₁ = pX → a₂ ≫ j₂ = jX ≫ c₂ → a₂ ≫ p₂ = pX →
              a₁ ≫ θ.hom = a₂) :
    ∃ e : Y₁ ⟶ Y₂, b₁ ≫ e.baseMap = b₂ ∧ c₁ ≫ e.totalMap = c₂ := by
  refine h₁.exists_hom_of_locallyIso h₂ fun s => ?_
  obtain ⟨U, e, he, hs, hθ⟩ := hloc s
  refine ⟨U, e, he, hs, fun A₁ A₂ j₁ j₂ p₁ p₂ hp₁ hp₂ => ?_⟩
  have hX₀ := (AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ (schemeSpaceMap e)
    X.toBase).flip
  obtain ⟨θ, hθp, hθc⟩ := hθ j₁ p₁ j₂ p₂ _ _ hp₁ hp₂ hX₀
  refine ⟨θ, hθp, fun A jX pX a₁ a₂ hX ha₁j ha₁p ha₂j ha₂p => ?_⟩
  let κ := hX.isoIsPullback _ _ hX₀
  have hκj : κ.inv ≫ jX = _ := hX.isoIsPullback_inv_fst _ _ hX₀
  have hκp : κ.inv ≫ pX = _ := hX.isoIsPullback_inv_snd _ _ hX₀
  have key := hθc (κ.inv ≫ a₁) (κ.inv ≫ a₂)
    (by rw [Category.assoc, ha₁j, ← Category.assoc, hκj])
    (by rw [Category.assoc, ha₁p, hκp])
    (by rw [Category.assoc, ha₂j, ← Category.assoc, hκj])
    (by rw [Category.assoc, ha₂p, hκp])
  rw [Category.assoc] at key
  exact (cancel_epi κ.inv).1 key

end AlgebraicGeometry.C1590Private

end
