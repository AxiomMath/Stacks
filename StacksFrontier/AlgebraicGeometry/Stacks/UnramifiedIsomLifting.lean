module

public import
  StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSourceAndTarget.EtaleSmoothExamples
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartTargetDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionSurjectiveOnPointsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.AutomorphismGroupAtPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordRelativeInertia
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismRelativeConverse
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismSurjectiveDiagram
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRelocalize
public import StacksFrontier.AlgebraicGeometry.Stacks.SecondDiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveOnObjects

/-!
# Lifting isomorphisms along unramified 1-morphisms, pointwise

A morphism of algebraic spaces whose relative diagonal is an open immersion — for instance an
unramified one (**Stacks 05W1**) — separates sections at points: two sections which agree at
every field-valued point agree. Read through representability, this says that a 1-morphism of
categories fibred in groupoids which is representable by algebraic spaces and unramified in the
sense of **Stacks 04XB** lifts an isomorphism `g s₁ ≅ g s₂` over a scheme as soon as its
restriction to every field-valued point lifts.

Applied to the relative diagonal of a Deligne–Mumford 1-morphism, and to an unramified
1-morphism representable by algebraic spaces, this gives the two halves of the geometric
implication of **Stacks 0DU9**: a 1-morphism inducing isomorphisms between automorphism groups
at every point is faithful, and lifts every vertical automorphism of the image of an object.

## Main results

* `AlgebraicGeometry.Space.eq_of_isOpenImmersion_diagonal_of_forall_fieldValuedPoint`: two
  morphisms over `Z` into a presheaf with open-immersion relative diagonal agree as soon as they
  agree at every field-valued point.
* `AlgebraicGeometry.Stack.eq_of_isUnramified_of_forall_fieldObject`: two sections over `T` of
  an algebraic space unramified over `T` which agree at every field point of `T` are equal.
* `AlgebraicGeometry.Stack.exists_isHomLift_map_eq_of_isRelativelyUnramified`: the lifting of
  isomorphisms along a representable unramified 1-morphism.
* `AlgebraicGeometry.Stack.faithful_homFunctor_of_isDM`: a Deligne–Mumford 1-morphism of
  algebraic stacks inducing isomorphisms between automorphism groups at every point is faithful.
* `AlgebraicGeometry.Stack.isRelativelyUnramified_of_isUnramified`: an unramified 1-morphism
  (**Stacks 0CIT**) representable by algebraic spaces is unramified in the sense of
  **Stacks 04XB**.
* `AlgebraicGeometry.Stack.exists_map_eq_of_isUnramified_of_isRepresentable`: such a 1-morphism,
  if it induces isomorphisms between automorphism groups at every point, lifts every vertical
  automorphism of the image of an object.

## Implementation notes

The open-immersion argument is run on the pullback of the relative diagonal along the pair of
sections: it is an open immersion into the source, surjective on points because the two
sections agree at every field-valued point, hence an isomorphism
(`AlgebraicGeometry.Space.isIso_of_isOpenImmersion_of_surjective_pointsMap`).

To lift `φ : g s₁ ⟶ g s₂` along `g`, the scheme-valued point `g s₂` of the target is read as a
1-morphism out of the slice site of `T` (2-Yoneda,
`CategoryTheory.StacksRepresentableCFG.exists_pointOverMap_of_obj`); representability gives an
algebraic space `F` over `T` equivalent to the base change of `g` along it. The objects
`(s₁, φ)` and `(s₂, 𝟙)` of the base change become two sections of `F` over `T`, an isomorphism
between them over `𝟙` is exactly a lift of `φ`, and their restrictions to a field point are the
images of the restrictions of `s₁` and `s₂`, between which the hypothesis provides an
isomorphism.

The relative-property form of unramifiedness for a representable 1-morphism is obtained from the
étale-smooth diagram test of **Stacks 0CIT** by the third assertion of **Stacks 0CIF**, in the
form `AlgebraicGeometry.Stack.hasRelativeProperty_of_hasPropertyOnSomeEtaleSmoothDiagram`, on the
diagram that **Stacks 0CIF** builds for a representable 1-morphism, exactly as in the proof of
**Stacks 0CJ0** in `StacksFrontier/AlgebraicGeometry/Stacks/UnramifiedDiagonalCriterion.lean`.

## References

* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 05W1](https://stacks.math.columbia.edu/tag/05W1)
* [Stacks Project, Tag 0CIF](https://stacks.math.columbia.edu/tag/0CIF)
* [Stacks Project, Tag 0CIT](https://stacks.math.columbia.edu/tag/0CIT)
* [Stacks Project, Tag 0DU9](https://stacks.math.columbia.edu/tag/0DU9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance hasPullbacks_presheaf_UnramifiedIsomLifting :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_UnramifiedIsomLifting
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- Two morphisms into a presheaf over `Z` whose relative diagonal is an open immersion are equal
as soon as they agree at every field-valued point of their source. -/
theorem eq_of_isOpenImmersion_diagonal_of_forall_fieldValuedPoint
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (h : X ⟶ Z)
    (hΔ : IsOpenImmersion B S hS (pullback.diagonal h))
    (σ₁ σ₂ : Y ⟶ X) (hσ : σ₁ ≫ h = σ₂ ≫ h)
    (hpt : ∀ p : FieldValuedPoint B S hS Y,
      σ₁.app (Opposite.op p.siteObject) p.value = σ₂.app (Opposite.op p.siteObject) p.value) :
    σ₁ = σ₂ := by
  let τ : Y ⟶ pullback h h := pullback.lift σ₁ σ₂ hσ
  have hopen : IsOpenImmersion B S hS (pullback.fst τ (pullback.diagonal h)) :=
    (MorphismProperty.relative_isStableUnderBaseChange
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))).of_isPullback
      (IsPullback.of_hasPullback τ (pullback.diagonal h)).flip hΔ
  have hsurj : Function.Surjective
      (pointsMap B S hS _ (pullback.fst τ (pullback.diagonal h))) := by
    intro z
    induction z using Quot.ind with
    | mk p =>
      let y : yoneda.obj p.siteObject ⟶ Y := yonedaEquiv.symm p.value
      have hy : y ≫ τ = (y ≫ σ₁) ≫ pullback.diagonal h := by
        apply pullback.hom_ext
        · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.diagonal_fst,
            Category.comp_id]
        · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.diagonal_snd,
            Category.comp_id]
          apply yonedaEquiv.injective
          simp only [yonedaEquiv_comp, y, Equiv.apply_symm_apply]
          exact (hpt p).symm
      let q : yoneda.obj p.siteObject ⟶ pullback τ (pullback.diagonal h) :=
        pullback.lift y (y ≫ σ₁) hy
      refine ⟨Quot.mk _ { p with value := yonedaEquiv q }, ?_⟩
      show Quot.mk _ (FieldValuedPoint.map B S hS _ _ _) = Quot.mk _ p
      congr 1
      have hv : (pullback.fst τ (pullback.diagonal h)).app _ (yonedaEquiv q) = p.value := by
        rw [← yonedaEquiv_comp, pullback.lift_fst]
        exact Equiv.apply_symm_apply _ _
      cases p
      simp only [FieldValuedPoint.map]
      exact congrArg _ hv
  have hiso : IsIso (pullback.fst τ (pullback.diagonal h)) :=
    isIso_of_isOpenImmersion_of_surjective_pointsMap B S hS _ hopen hsurj
  -- a section `σ = τ ≫ π` through a retraction `π` of the diagonal is read off the pullback
  have key : ∀ (π : pullback h h ⟶ X) (σ : Y ⟶ X), pullback.diagonal h ≫ π = 𝟙 X → τ ≫ π = σ →
      σ = inv (pullback.fst τ (pullback.diagonal h)) ≫ pullback.snd τ (pullback.diagonal h) := by
    intro π σ hπ hσ'
    rw [IsIso.eq_inv_comp, ← hσ', ← Category.assoc, pullback.condition, Category.assoc, hπ,
      Category.comp_id]
  exact (key _ _ (pullback.diagonal_fst h) (pullback.lift_fst _ _ _)).trans
    (key _ _ (pullback.diagonal_snd h) (pullback.lift_snd _ _ _)).symm

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

open CategoryTheory CategoryTheory.Limits Opposite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Sections of an unramified algebraic space over a scheme are determined at field
points.** Let `F` be an algebraic space over a scheme `T` of the big fppf site of `S` whose
structure morphism, read over `S`, is unramified. Two sections of `F` over `T` which agree after
restriction to every field-valued point of `T` are equal. -/
theorem eq_of_isUnramified_of_forall_fieldObject (T : BigFppfOver B S hS)
    (F : (BigFppfOver B T.left.1 T.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B T.left.1 T.left.2 F)
    (hu : Space.IsUnramified B S hS
      (algebraicSpaceMap B S hS T
        ((spacesOverSmallerBaseFunctor B T.left.1 S T.left.2 hS T.hom).obj ⟨F, hF⟩)).hom)
    (e₁ e₂ : F.obj (op (Over.mk (𝟙 T.left))))
    (hpt : ∀ (a : Over T.left), IsFieldObject B S hS ((Over.map T.hom).obj a) →
      ∀ t : a ⟶ Over.mk (𝟙 T.left), F.map t.op e₁ = F.map t.op e₂) :
    e₁ = e₂ := by
  have hu' : Space.IsUnramified B T.left.1 T.left.2 (Space.toYonedaId B T.left.1 T.left.2 F) :=
    (Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff B T.left.1 S T.left.2 hS T.hom
      (@AlgebraicGeometry.Unramified.{u}) F).mp
      ((prop_algebraicSpaceMap_iff B S hS (Space.unramifiedMorphismProperty B S hS) T F hF).mp hu)
  have hΔ : Space.IsOpenImmersion B T.left.1 T.left.2
      (pullback.diagonal (Space.toYonedaId B T.left.1 T.left.2 F)) :=
    Space.isOpenImmersion_diagonal_of_isUnramified B T.left.1 T.left.2 hF
      (isAlgebraicSpace_yoneda B T.left.1 T.left.2 _) _ hu'
  let σ₁ : yoneda.obj (Over.mk (𝟙 T.left)) ⟶ F := yonedaEquiv.symm e₁
  let σ₂ : yoneda.obj (Over.mk (𝟙 T.left)) ⟶ F := yonedaEquiv.symm e₂
  have hσ : σ₁ ≫ Space.toYonedaId B T.left.1 T.left.2 F =
      σ₂ ≫ Space.toYonedaId B T.left.1 T.left.2 F := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_comp]
    exact Over.OverMorphism.ext rfl
  have heq : σ₁ = σ₂ := by
    refine Space.eq_of_isOpenImmersion_diagonal_of_forall_fieldValuedPoint B T.left.1 T.left.2
      _ hΔ σ₁ σ₂ hσ fun p => ?_
    show F.map p.value.op e₁ = F.map p.value.op e₂
    exact hpt _ ⟨p.carrier, p.field, ⟨Iso.refl _⟩⟩ p.value
  simpa [σ₁, σ₂] using congrArg yonedaEquiv heq

/-- **A representable, unramified 1-morphism lifts an isomorphism which lifts at every field
point.** Let `g : 𝒜 ⟶ ℬ` be a 1-morphism of categories fibred in groupoids over the big fppf site
of `S` which is representable by algebraic spaces and unramified in the sense of Stacks 04XB.
Let `s₁`, `s₂` be objects of `𝒜` over a scheme `T` and let `φ : g s₁ ⟶ g s₂` lie over `𝟙 T`. If
after pulling back to every field-valued point `t : V ⟶ T` the restriction of `φ` is the image of
a morphism over `𝟙 V`, then `φ` itself is the image of a morphism `s₁ ⟶ s₂` over `𝟙 T`. -/
theorem exists_isHomLift_map_eq_of_isRelativelyUnramified
    {𝒜 ℬ : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (g : 𝒜 ⟶ ℬ)
    (hrep : IsRepresentableByAlgebraicSpaces B S hS g.hom)
    (hur : IsRelativelyUnramified B S hS g)
    {T : BigFppfOver B S hS} {s₁ s₂ : 𝒜.val.obj} (h₁ : 𝒜.val.p.obj s₁ = T)
    (h₂ : 𝒜.val.p.obj s₂ = T)
    (φ : (CatFiberedInGroupoids.homFunctor g).obj s₁ ⟶
      (CatFiberedInGroupoids.homFunctor g).obj s₂)
    (hφ : ℬ.val.p.IsHomLift (𝟙 T) φ)
    (hpt : ∀ (V : BigFppfOver B S hS), IsFieldObject B S hS V → ∀ (t : V ⟶ T)
      (s₁' s₂' : 𝒜.val.obj) (m₁ : s₁' ⟶ s₁) (m₂ : s₂' ⟶ s₂),
      𝒜.val.p.IsHomLift t m₁ → 𝒜.val.p.IsHomLift t m₂ →
      ∃ γ : s₁' ⟶ s₂', 𝒜.val.p.IsHomLift (𝟙 V) γ ∧
        (CatFiberedInGroupoids.homFunctor g).map γ ≫
            (CatFiberedInGroupoids.homFunctor g).map m₂ =
          (CatFiberedInGroupoids.homFunctor g).map m₁ ≫ φ) :
    ∃ γ : s₁ ⟶ s₂, 𝒜.val.p.IsHomLift (𝟙 T) γ ∧
      (CatFiberedInGroupoids.homFunctor g).map γ = φ := by
  classical
  let G := CatFiberedInGroupoids.homFunctor g
  have hG : G ⋙ ℬ.val.p = 𝒜.val.p := CatFiberedInGroupoids.homFunctor_comp_p g
  have hq := ℬ.isFiberedInGroupoids
  have hp := 𝒜.isFiberedInGroupoids
  let _ : ℬ.val.p.IsFibered := hq.isFibered
  have _ : ℬ.val.p.IsStronglyCartesian (𝟙 T) φ := hq.isStronglyCartesian_homLift (𝟙 T) φ
  have _ : IsIso φ := Functor.IsStronglyCartesian.isIso_of_base_isIso ℬ.val.p (𝟙 T) φ
  have hs₁ : ℬ.val.p.obj (G.obj s₁) = T := (Functor.congr_obj hG s₁).trans h₁
  have hs₂ : ℬ.val.p.obj (G.obj s₂) = T := (Functor.congr_obj hG s₂).trans h₂
  -- the scheme-valued point of `ℬ` at `g s₂`, read as a 1-morphism out of the slice site of `T`
  obtain ⟨y, hy, ξ, hξ⟩ := StacksRepresentableCFG.exists_pointOverMap_of_obj ℬ.val.p hq T
    (G.obj s₂) hs₂
  obtain ⟨F, hF, ⟨E⟩⟩ := hrep T y hy
  have hu := hur T y hy F hF ⟨E⟩
  have hT' : (Over.map T.hom).obj (Over.mk (𝟙 T.left)) = T := Functor.overMap_obj_mkId T
  have hm₁ : ℬ.val.p.IsHomLift (𝟙 T) (ξ.hom ≫ inv φ) := by
    have := hξ
    infer_instance
  -- the two objects of the 2-fibre product over the terminal object of the slice site
  let c₁ : TwoFibreProductOver (Over.map T.hom) 𝒜.val.p ℬ.val.p y G :=
    { base := T, x := Over.mk (𝟙 T.left), y := s₁, hx := hT', hy := h₁,
      iso := asIso (ξ.hom ≫ inv φ), vertical := hm₁ }
  let c₂ : TwoFibreProductOver (Over.map T.hom) 𝒜.val.p ℬ.val.p y G :=
    { base := T, x := Over.mk (𝟙 T.left), y := s₂, hx := hT', hy := h₂,
      iso := ξ, vertical := hξ }
  have hE : ∀ c, (presheafOfCategories (F ⋙ typeToCat)).p.obj (E.hom.functor.obj c) =
      (TwoFibreProductOver.fst (Over.map T.hom) 𝒜.val.p ℬ.val.p y G).obj c :=
    fun c => Functor.congr_obj E.hom.w c
  let e₁ := PresheafOfCategories.elementOf F (hE c₁)
  let e₂ := PresheafOfCategories.elementOf F (hE c₂)
  have hmapE : ∀ {c c' : TwoFibreProductOver (Over.map T.hom) 𝒜.val.p ℬ.val.p y G}
      (u : c ⟶ c'), (presheafOfCategories (F ⋙ typeToCat)).p.IsHomLift u.a
        (E.hom.functor.map u) := by
    intro c c' u
    have : (TwoFibreProductOver.fst (Over.map T.hom) 𝒜.val.p ℬ.val.p y G).IsHomLift u.a u :=
      IsHomLift.map _ u
    exact Functor.isHomLift_map_of_comp_eq E.hom.w u.a u
  have he : e₁ = e₂ := by
    refine eq_of_isUnramified_of_forall_fieldObject B S hS T F hF hu e₁ e₂ ?_
    intro a hV t
    let V := (Over.map T.hom).obj a
    let t' : V ⟶ T := (Over.map T.hom).map t ≫ eqToHom hT'
    obtain ⟨s₁', m₁, hm₁'⟩ := hp.exists_lift t' s₁ h₁
    obtain ⟨s₂', m₂, hm₂'⟩ := hp.exists_lift t' s₂ h₂
    obtain ⟨γ', hγ', hγeq⟩ := hpt V hV t' s₁' s₂' m₁ m₂ hm₁' hm₂'
    have _ := hm₁'
    have _ := hm₂'
    have _ := hγ'
    have _ := hξ
    have _ : ℬ.val.p.IsHomLift (𝟙 T) c₁.iso.hom := c₁.vertical
    have _ : ℬ.val.p.IsHomLift (𝟙 T) c₂.iso.hom := c₂.vertical
    have hyt : ℬ.val.p.IsHomLift t' (y.map t) := by
      have : ℬ.val.p.IsHomLift ((Over.map T.hom).map t) (y.map t) :=
        Functor.isHomLift_map_of_comp_eq hy ((Over.map T.hom).map t) t
      infer_instance
    have hGm₁ : ℬ.val.p.IsHomLift t' (G.map m₁) := Functor.isHomLift_map_of_comp_eq hG t' m₁
    have hGm₂ : ℬ.val.p.IsHomLift t' (G.map m₂) := Functor.isHomLift_map_of_comp_eq hG t' m₂
    have _ : ℬ.val.p.IsStronglyCartesian t' (G.map m₁) := hq.isStronglyCartesian_homLift _ _
    have _ : ℬ.val.p.IsStronglyCartesian t' (G.map m₂) := hq.isStronglyCartesian_homLift _ _
    have _ : ℬ.val.p.IsStronglyCartesian t' (y.map t ≫ c₁.iso.hom) :=
      hq.isStronglyCartesian_homLift _ _
    have _ : ℬ.val.p.IsStronglyCartesian t' (y.map t ≫ c₂.iso.hom) :=
      hq.isStronglyCartesian_homLift _ _
    let i₁ := Functor.IsCartesian.domainUniqueUpToIso ℬ.val.p t' (G.map m₁)
      (y.map t ≫ c₁.iso.hom)
    let i₂ := Functor.IsCartesian.domainUniqueUpToIso ℬ.val.p t' (G.map m₂)
      (y.map t ≫ c₂.iso.hom)
    have hi₁ : i₁.hom ≫ G.map m₁ = y.map t ≫ c₁.iso.hom :=
      Functor.IsCartesian.fac ℬ.val.p t' (G.map m₁) (y.map t ≫ c₁.iso.hom)
    have hi₂ : i₂.hom ≫ G.map m₂ = y.map t ≫ c₂.iso.hom :=
      Functor.IsCartesian.fac ℬ.val.p t' (G.map m₂) (y.map t ≫ c₂.iso.hom)
    have hta : (Over.map T.hom).IsHomLift t' t := by
      have : (Over.map T.hom).IsHomLift ((Over.map T.hom).map t) t := IsHomLift.map _ t
      infer_instance
    let c₁' : TwoFibreProductOver (Over.map T.hom) 𝒜.val.p ℬ.val.p y G :=
      { base := V, x := a, y := s₁', hx := rfl, hy := IsHomLift.domain_eq _ t' m₁,
        iso := i₁, vertical := inferInstance }
    let c₂' : TwoFibreProductOver (Over.map T.hom) 𝒜.val.p ℬ.val.p y G :=
      { base := V, x := a, y := s₂', hx := rfl, hy := IsHomLift.domain_eq _ t' m₂,
        iso := i₂, vertical := inferInstance }
    let u₁ : c₁' ⟶ c₁ :=
      { hbase := t', a := t, b := m₁, ha := hta, hb := hm₁', w := hi₁.symm }
    let u₂ : c₂' ⟶ c₂ :=
      { hbase := t', a := t, b := m₂, ha := hta, hb := hm₂', w := hi₂.symm }
    have hw : y.map (𝟙 a) ≫ i₂.hom = i₁.hom ≫ G.map γ' := by
      rw [y.map_id, Category.id_comp]
      have _ : ℬ.val.p.IsHomLift (𝟙 V) (G.map γ') :=
        Functor.isHomLift_map_of_comp_eq hG (𝟙 V) γ'
      refine Functor.IsCartesian.ext ℬ.val.p t' (G.map m₂) _ _ ?_
      rw [hi₂, Category.assoc, hγeq, ← Category.assoc, hi₁]
      simp [c₁, c₂]
    let v : c₁' ⟶ c₂' :=
      { hbase := 𝟙 V, a := 𝟙 a, b := γ', ha := IsHomLift.id rfl, hb := hγ', w := hw }
    have k₁ := PresheafOfCategories.elementOf_eq_map (hE c₁') (hE c₁) t (E.hom.functor.map u₁)
      (hmapE u₁)
    have k₂ := PresheafOfCategories.elementOf_eq_map (hE c₂') (hE c₂) t (E.hom.functor.map u₂)
      (hmapE u₂)
    have k₃ := PresheafOfCategories.elementOf_eq_map (hE c₁') (hE c₂') (𝟙 a)
      (E.hom.functor.map v) (hmapE v)
    have k₃' := k₃.trans (show F.map (𝟙 a).op _ = _ by
      rw [show (𝟙 a).op = 𝟙 (op a) from rfl, F.map_id])
    exact k₁.symm.trans (k₃'.trans k₂)
  have hobj : E.hom.functor.obj c₁ = E.hom.functor.obj c₂ :=
    PresheafOfCategories.obj_eq_of_elementOf_eq (hE c₁) (hE c₂) he
  let ψ : c₁ ⟶ c₂ := E.unitIso.hom.app c₁ ≫ eqToHom (congrArg E.inv.functor.obj hobj) ≫
    E.unitIso.inv.app c₂
  have hψa : ψ.a = 𝟙 _ := Over.mkIdTerminal.hom_ext _ _
  have hψbase : ψ.hbase = 𝟙 T := by
    have _ := ψ.ha
    have _ : (Over.map T.hom).IsHomLift (𝟙 T) ψ.a := by
      rw [hψa]
      exact IsHomLift.id hT'
    exact (IsHomLift.fac (Over.map T.hom) ψ.hbase ψ.a).trans
      (IsHomLift.fac (Over.map T.hom) (𝟙 T) ψ.a).symm
  have hb := ψ.hb
  rw [hψbase] at hb
  refine ⟨ψ.b, hb, ?_⟩
  have hw := ψ.w
  rw [hψa, y.map_id, Category.id_comp] at hw
  change ξ.hom = (ξ.hom ≫ inv φ) ≫ G.map ψ.b at hw
  rw [Category.assoc, ← cancel_epi ξ.inv] at hw
  simpa using hw.symm

section AlgebraicStacks

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- **Condition (2) of Stacks 0DU9 at the objects over a field.** If a 1-morphism `f : 𝒳 ⟶ 𝒴`
of algebraic stacks induces an isomorphism between the automorphism groups at every point of
`|𝒳|`, then it induces a bijection of vertical automorphism groups at every object of `𝒳` lying
over the spectrum of a field. -/
theorem bijective_automorphismGroupMap_of_isFieldObject (f : 𝒳 ⟶ 𝒴)
    (hauto : ∀ q : points B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids,
      InducesIsomorphismAt B S hS f q)
    (b : 𝒳.val.val.obj) (hb : IsFieldObject B S hS (𝒳.val.val.p.obj b)) :
    Function.Bijective (automorphismGroupMap B S hS f b) := by
  obtain ⟨k, hk, ⟨e⟩⟩ := hb
  let p : FieldValuedPoint B S hS 𝒳.val.val :=
    { carrier := k, field := hk, base := 𝒳.val.val.p.obj b, isSpec := e, obj := b,
      «over» := rfl }
  exact (inducesIsomorphismAt_iff_forall_representatives B S hS f _).1 (hauto _) p rfl b (𝟙 b)

/-- An invertible endomorphism lying over an identity of the base is a vertical automorphism. -/
private theorem asIso_mem_verticalAut {𝒞 𝒜 : Type*} [Category 𝒞] [Category 𝒜] {p : 𝒜 ⥤ 𝒞}
    {V : 𝒞} {s : 𝒜} (a : s ⟶ s) [IsIso a] (h : p.IsHomLift (𝟙 V) a) :
    Aut.of (asIso a) ∈ p.verticalAut s := by
  refine (Functor.mem_verticalAut_iff p (Aut.of (asIso a))).mpr ?_
  change p.map a = _
  rw [IsHomLift.fac' p (𝟙 V) a]
  simp

/-- If `f` induces isomorphisms between automorphism groups, a vertical endomorphism of an object
over a field which `f` sends to an identity is an identity. -/
private theorem eq_id_of_isFieldObject_of_map_eq_id (f : 𝒳 ⟶ 𝒴)
    (hauto : ∀ q : points B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids,
      InducesIsomorphismAt B S hS f q)
    {V : BigFppfOver B S hS} (hV : IsFieldObject B S hS V) {s : 𝒳.val.val.obj} (a : s ⟶ s)
    (hav : 𝒳.val.val.p.IsHomLift (𝟙 V) a)
    (ha : (CatFiberedInGroupoids.homFunctor f.hom).map a = 𝟙 _) : a = 𝟙 s := by
  have hV' : 𝒳.val.val.p.obj s = V := IsHomLift.domain_eq _ (𝟙 V) a
  have _ : IsIso a := Functor.isIso_of_fiber_isGroupoid
    (𝒳.val.isFiberedInGroupoids.fiber_isGroupoid V) a inferInstance
  have hone : (⟨Aut.of (asIso a), asIso_mem_verticalAut a hav⟩ : 𝒳.val.val.p.verticalAut s) = 1 :=
    (bijective_automorphismGroupMap_of_isFieldObject B S hS f hauto s (hV' ▸ hV)).1 <| by
      rw [map_one]
      exact Subtype.ext (Aut.ext (Iso.ext ha))
  exact congrArg (fun z : 𝒳.val.val.p.verticalAut s => (z : Aut s).asIso.hom) hone

/-- If `f` induces isomorphisms between automorphism groups, the restriction to an object over a
field of an endomorphism which `f` sends to an identity is an identity. -/
private theorem eq_id_of_comp_eq_comp_of_isFieldObject (f : 𝒳 ⟶ 𝒴)
    (hauto : ∀ q : points B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids,
      InducesIsomorphismAt B S hS f q)
    {V : BigFppfOver B S hS} (hV : IsFieldObject B S hS V) {x s : 𝒳.val.val.obj}
    {t : V ⟶ 𝒳.val.val.p.obj x} (m : s ⟶ x) [𝒳.val.val.p.IsHomLift t m] (a : x ⟶ x)
    (ha : (CatFiberedInGroupoids.homFunctor f.hom).map a = 𝟙 _) (a' : s ⟶ s)
    [𝒳.val.val.p.IsHomLift (𝟙 V) a'] (ha' : a' ≫ m = m ≫ a) : a' = 𝟙 s := by
  let pY := 𝒴.val.val.p
  let F := CatFiberedInGroupoids.homFunctor f.hom
  have hF : F ⋙ pY = 𝒳.val.val.p := CatFiberedInGroupoids.homFunctor_comp_p f.hom
  have _ : pY.IsHomLift t (F.map m) := Functor.isHomLift_map_of_comp_eq hF t m
  have _ : pY.IsStronglyCartesian t (F.map m) :=
    𝒴.val.isFiberedInGroupoids.isStronglyCartesian_homLift t (F.map m)
  have _ : pY.IsHomLift (𝟙 V) (F.map a') := Functor.isHomLift_map_of_comp_eq hF (𝟙 V) a'
  have hFa : F.map a' = 𝟙 _ := by
    have _ : pY.IsHomLift (𝟙 V) (𝟙 (F.obj s)) :=
      IsHomLift.id ((Functor.congr_obj hF s).trans (IsHomLift.domain_eq _ t m))
    refine Functor.IsCartesian.ext pY t (F.map m) _ _ ?_
    rw [← F.map_comp, ha', F.map_comp, ha]
    simp [F]
  exact eq_id_of_isFieldObject_of_map_eq_id B S hS f hauto hV a' inferInstance hFa

/-- **The injectivity half of Stacks 0DU9, (2) `⟹` (1).** Let `f : 𝒳 ⟶ 𝒴` be a Deligne–Mumford
1-morphism of algebraic stacks inducing an isomorphism between the automorphism groups at every
point of `|𝒳|`. Then every endomorphism of an object of `𝒳` which `f` sends to an identity is
an identity.

Such an endomorphism `a` of `x` gives the automorphism `(𝟙, a)` of `Δ_f(x)` in
`𝒳 ×_𝒴 𝒳`; the relative diagonal is representable and unramified, and at every field-valued
point the restriction of `a` is trivial by the hypothesis, so `(𝟙, a)` lifts along `Δ_f`, which
forces `a = 𝟙`. -/
theorem eq_id_of_map_eq_id_of_isDM (f : 𝒳 ⟶ 𝒴) (hdm : IsDM B S hS f)
    (hauto : ∀ q : points B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids,
      InducesIsomorphismAt B S hS f q)
    (x : 𝒳.val.val.obj) (a : x ⟶ x)
    (ha : (CatFiberedInGroupoids.homFunctor f.hom).map a = 𝟙 _) : a = 𝟙 x := by
  classical
  let pX := 𝒳.val.val.p
  let pY := 𝒴.val.val.p
  let F := CatFiberedInGroupoids.homFunctor f.hom
  have hF : F ⋙ pY = pX := CatFiberedInGroupoids.homFunctor_comp_p f.hom
  have hp := 𝒳.val.isFiberedInGroupoids
  obtain ⟨hΔ, hunr⟩ := hdm
  let Δ := relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom
  have hav : pX.IsHomLift (𝟙 (pX.obj x)) a :=
    IsHomLift.of_fac' pX _ a rfl rfl (by simpa using RelativeInertia.map_eq_id_of_comp_eq hF a ha)
  let φ : (CatFiberedInGroupoids.homFunctor Δ).obj x ⟶
      (CatFiberedInGroupoids.homFunctor Δ).obj x :=
    { hbase := 𝟙 (pX.obj x)
      a := 𝟙 x
      b := a
      ha := IsHomLift.id rfl
      hb := hav
      w := by
        show F.map (𝟙 x) ≫ 𝟙 _ = 𝟙 _ ≫ F.map a
        rw [ha]
        simp [F] }
  have hφ : (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.p.IsHomLift
      (𝟙 (pX.obj x)) φ :=
    IsHomLift.map (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.p φ
  obtain ⟨γ, -, hγ⟩ := exists_isHomLift_map_eq_of_isRelativelyUnramified B S hS Δ hΔ hunr
    (rfl : pX.obj x = pX.obj x) rfl φ hφ (fun V hV t s₁' s₂' m₁ m₂ hm₁ hm₂ => by
      have _ := hm₁
      have _ := hm₂
      have _ : pX.IsStronglyCartesian t m₁ := hp.isStronglyCartesian_homLift t m₁
      have _ : pX.IsStronglyCartesian t m₂ := hp.isStronglyCartesian_homLift t m₂
      let δ := Functor.IsCartesian.map pX t m₂ m₁
      have hδ : δ ≫ m₂ = m₁ := Functor.IsCartesian.fac pX t m₂ m₁
      -- the restriction of `a` to `s₁'` is killed by `f`, hence trivial
      let a' := Functor.IsCartesian.map pX t m₁ (m₁ ≫ a)
      have ha' : a' ≫ m₁ = m₁ ≫ a := Functor.IsCartesian.fac pX t m₁ (m₁ ≫ a)
      have ha'id : a' = 𝟙 s₁' :=
        eq_id_of_comp_eq_comp_of_isFieldObject B S hS f hauto hV (t := t) m₁ a ha a' ha'
      have _ : pX.IsHomLift (𝟙 V) δ := inferInstance
      refine ⟨δ, inferInstance, TwoFibreProductOver.Hom.ext' ?_ ?_⟩
      · show δ ≫ m₂ = m₁ ≫ 𝟙 x
        rw [hδ, Category.comp_id]
      · show δ ≫ m₂ = m₁ ≫ a
        rw [hδ, ← ha', ha'id, Category.id_comp])
  have h₁ : γ = 𝟙 x := congrArg TwoFibreProductOver.Hom.a hγ
  have h₂ : γ = a := congrArg TwoFibreProductOver.Hom.b hγ
  exact h₂.symm.trans h₁

/-- **Faithfulness from condition (2) of Stacks 0DU9.** A Deligne–Mumford 1-morphism of
algebraic stacks inducing an isomorphism between the automorphism groups at every point of its
source has faithful underlying functor. -/
theorem faithful_homFunctor_of_isDM (f : 𝒳 ⟶ 𝒴) (hdm : IsDM B S hS f)
    (hauto : ∀ q : points B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids,
      InducesIsomorphismAt B S hS f q) :
    (CatFiberedInGroupoids.homFunctor f.hom).Faithful :=
  (Functor.IsFiberedInGroupoids.faithful_iff_autKernel_trivial 𝒳.val.isFiberedInGroupoids
    𝒴.val.isFiberedInGroupoids (CatFiberedInGroupoids.homFunctor_comp_p f.hom)).mpr
    (eq_id_of_map_eq_id_of_isDM B S hS f hdm hauto)

/-- **An unramified 1-morphism representable by algebraic spaces is unramified in the sense of
Stacks 04XB.** For `f` representable by algebraic spaces the universal étale-smooth diagram test
of Stacks 0CIT is passed on the diagram of Stacks 0CIF built from a presentation of the target,
and Stacks 0CIF identifies the existential test with the relative property of Stacks 03YK. -/
theorem isRelativelyUnramified_of_isUnramified (f : 𝒳 ⟶ 𝒴)
    (hrep : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) (hu : IsUnramified B S hS f) :
    IsRelativelyUnramified B S hS f.hom := by
  have : (Space.unramifiedMorphismProperty B S hS).IsStableUnderBaseChange :=
    Space.isUnramified_isStableUnderBaseChange B S hS
  have : (Space.unramifiedMorphismProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    (Space.isUnramified_isLocalAtTarget_fpqc.{u, u} B S hS).of_le
      (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  have hrel : HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.unramifiedMorphismProperty B S hS)
      f.hom hrep := by
    refine hasRelativeProperty_of_hasPropertyOnSomeEtaleSmoothDiagram.{u, u, w} B S hS _
      (Space.isUnramified_isEtaleSmoothLocalOnSourceAndTarget B S hS) f hrep ?_
    refine hasPropertyOnSomeEtaleSmoothDiagram_of_hasPropertyOnEveryEtaleSmoothDiagram
      B S hS _ f ?_ hu.2
    obtain ⟨U', V', hU', hV', a', b', h', η', hsu', hbsm', hcomp', -⟩ :=
      hasPropertyOnSomeEtaleSmoothDiagram_of_hasRelativeProperty.{u, u, w} B S hS
        (⊤ : MorphismProperty (AlgebraicSpaces B S hS)) f hrep
        (fun _ _ _ _ _ _ => trivial)
    exact ⟨U', V', hU', hV', a', b', h', η', hsu', hbsm', hcomp'⟩
  exact hrel

/-- **The surjectivity half of Stacks 0DU9, (2) `⟹` (1), for a representable 1-morphism.** Let
`f : 𝒳 ⟶ 𝒴` be an unramified 1-morphism of algebraic stacks which is representable by algebraic
spaces and induces an isomorphism between the automorphism groups at every point of `|𝒳|`. Then
every vertical automorphism of the image under `f` of an object of `𝒳` is the image of a
vertical automorphism of that object.

The automorphism `β` lifts along `f`, which is representable and unramified in the sense of
Stacks 04XB, because its restriction to every field-valued point lifts by the hypothesis. -/
theorem exists_map_eq_of_isUnramified_of_isRepresentable (f : 𝒳 ⟶ 𝒴)
    (hrep : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) (hu : IsUnramified B S hS f)
    (hauto : ∀ q : points B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids,
      InducesIsomorphismAt B S hS f q)
    (x : 𝒳.val.val.obj) (β : (CatFiberedInGroupoids.homFunctor f.hom).obj x ⟶
      (CatFiberedInGroupoids.homFunctor f.hom).obj x)
    (hβ : 𝒴.val.val.p.IsHomLift (𝟙 (𝒳.val.val.p.obj x)) β) :
    ∃ α : x ⟶ x, 𝒳.val.val.p.IsHomLift (𝟙 (𝒳.val.val.p.obj x)) α ∧
      (CatFiberedInGroupoids.homFunctor f.hom).map α = β := by
  classical
  let pX := 𝒳.val.val.p
  let pY := 𝒴.val.val.p
  let F := CatFiberedInGroupoids.homFunctor f.hom
  have hF : F ⋙ pY = pX := CatFiberedInGroupoids.homFunctor_comp_p f.hom
  have hp := 𝒳.val.isFiberedInGroupoids
  have hq := 𝒴.val.isFiberedInGroupoids
  refine exists_isHomLift_map_eq_of_isRelativelyUnramified B S hS f.hom hrep
    (isRelativelyUnramified_of_isUnramified B S hS f hrep hu) rfl rfl β hβ
    (fun V hV t s₁' s₂' m₁ m₂ hm₁ hm₂ => ?_)
  have _ := hm₁
  have _ := hm₂
  have _ : pX.IsStronglyCartesian t m₂ := hp.isStronglyCartesian_homLift t m₂
  let δ := Functor.IsCartesian.map pX t m₂ m₁
  have hδ : δ ≫ m₂ = m₁ := Functor.IsCartesian.fac pX t m₂ m₁
  have hFm₁ : pY.IsHomLift t (F.map m₁) := Functor.isHomLift_map_of_comp_eq hF t m₁
  have _ : pY.IsStronglyCartesian t (F.map m₁) := hq.isStronglyCartesian_homLift t (F.map m₁)
  have _ := hβ
  -- the restriction of `β` to `f(s₁')`
  let β' := Functor.IsCartesian.map pY t (F.map m₁) (F.map m₁ ≫ β)
  have hβ' : β' ≫ F.map m₁ = F.map m₁ ≫ β := Functor.IsCartesian.fac pY t (F.map m₁) _
  have hV' : pX.obj s₁' = V := IsHomLift.domain_eq pX t m₁
  have _ : IsIso β' := Functor.isIso_of_fiber_isGroupoid (hq.fiber_isGroupoid V) β' inferInstance
  obtain ⟨α', hα'⟩ := (bijective_automorphismGroupMap_of_isFieldObject B S hS f hauto s₁'
    (hV' ▸ hV)).2 ⟨Aut.of (asIso β'), asIso_mem_verticalAut (V := V) β' inferInstance⟩
  have hFα : F.map (α' : Aut s₁').asIso.hom = β' :=
    congrArg (fun z : pY.verticalAut (F.obj s₁') => (z : Aut (F.obj s₁')).asIso.hom) hα'
  have hα'v : pX.IsHomLift (𝟙 V) (α' : Aut s₁').asIso.hom := by
    refine IsHomLift.of_fac' pX _ _ hV' hV' ?_
    rw [Functor.verticalAut.cond α']
    simp [pX]
  have _ : pX.IsHomLift (𝟙 V) δ := inferInstance
  refine ⟨(α' : Aut s₁').asIso.hom ≫ δ, ?_, ?_⟩
  · simpa using IsHomLift.comp pX (𝟙 V) (𝟙 V) (α' : Aut s₁').asIso.hom δ
  · show F.map ((α' : Aut s₁').asIso.hom ≫ δ) ≫ F.map m₂ = F.map m₁ ≫ β
    rw [F.map_comp, Category.assoc, ← F.map_comp, hδ, hFα, hβ']

end AlgebraicStacks

end AlgebraicGeometry.Stack
