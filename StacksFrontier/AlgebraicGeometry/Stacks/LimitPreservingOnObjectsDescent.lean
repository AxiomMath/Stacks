module

public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingOnObjectsGluing
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingAtlasCover
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.LimitPreservingOnObjects

/-!
# Limit preservation on objects through a covering family of lifts

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of stacks in groupoids over the big fppf site of `S` satisfying
relative descent of morphisms and of equalities along cofiltered limits of affine schemes, and
let `a : 𝒲 ⟶ 𝒳` be a 1-morphism along which every object of `𝒳` lifts fppf locally. This file
shows that `f` is limit preserving on objects (Stacks 06CU) as soon as `a ≫ f` is. This is the
descent of objects in the proof of Stacks 0CMX: an object over the limit lifts to `𝒲` after a
single-member fppf covering descended to a finite stage, the lift descends because `a ≫ f` is
limit preserving on objects, and the descended lift is glued back along the covering at a finite
stage.

## Main results

* `AlgebraicGeometry.Stack.isLimitPreservingOnObjects_of_comp_of_singleCover_lift`: limit
  preservation on objects of `f` from that of `a ≫ f`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace AlgebraicGeometry.Stack

open GlueKernel BigAffineFppf

universe u

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion CategoryTheory.Bicategory.InducedBicategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Limit preservation on objects through a covering family of lifts.** Let `f : 𝒳 ⟶ 𝒴` be a
1-morphism of stacks in groupoids over the big fppf site of `S` satisfying relative descent of
morphisms and of equalities along cofiltered limits of affine schemes, and let `a : 𝒲 ⟶ 𝒳` be a
1-morphism such that every object of `𝒳` over a scheme `U` lifts to `𝒲` after a flat, surjective
morphism `T ⟶ U` locally of finite presentation. If `a ≫ f` is limit preserving on objects, then
so is `f`. -/
theorem isLimitPreservingOnObjects_of_comp_of_singleCover_lift
    {𝒲 𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (a : 𝒲 ⟶ 𝒳) (f : 𝒳 ⟶ 𝒴)
    (h𝒳 : 𝒳.val.p.IsStack (BigFppfOver.topology B S hS))
    (h𝒴 : 𝒴.val.p.IsStack (BigFppfOver.topology B S hS))
    (hHom : ∀ {J : Type u} [Category.{u} J] [IsCofiltered J] (D : J ⥤ BigAffineFppf B S hS)
      (c : Cone D), IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c) →
        RelativeDescentHom.{u, u, u, u, u} B S hS f D c)
    (hEq : ∀ {J : Type u} [Category.{u} J] [IsCofiltered J] (D : J ⥤ BigAffineFppf B S hS)
      (c : Cone D), IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c) →
        RelativeDescentEq.{u, u, u, u, u} B S hS f D c)
    (H : ∀ (U : BigFppfOver B S hS) (y : 𝒳.val.p.Fiber U),
      ∃ (T : B.Schemes) (m : T ⟶ U.left), Flat (B.inclusion.map m) ∧
        LocallyOfFinitePresentation (B.inclusion.map m) ∧ Surjective (B.inclusion.map m) ∧
        ∃ (z : 𝒲.val.obj) (φ : (CatFiberedInGroupoids.homFunctor a).obj z ⟶ y.1),
          𝒳.val.p.IsHomLift
            (Over.homMk m rfl : (Over.mk (m ≫ U.hom) : BigFppfOver B S hS) ⟶ U) φ)
    (hLP : BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS 𝒲 𝒴 (a ≫ f)) :
    BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS 𝒳 𝒴 f := by
  classical
  intro I _ _ D c hc i y x γ hγ
  let : 𝒲.val.p.IsFibered := 𝒲.2.isFibered
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  have hp : 𝒳.val.p.IsFiberedInGroupoids := 𝒳.2
  have hq : 𝒴.val.p.IsFiberedInGroupoids := 𝒴.2
  let ι := BigAffineFppf.inclusion B S hS
  let Fa := CatFiberedInGroupoids.homFunctor a
  let Ff := CatFiberedInGroupoids.homFunctor f
  have hFa : Fa ⋙ 𝒳.val.p = 𝒲.val.p := CatFiberedInGroupoids.homFunctor_comp_p a
  have hFf : Ff ⋙ 𝒴.val.p = 𝒳.val.p := CatFiberedInGroupoids.homFunctor_comp_p f
  -- a single-member covering of a stage over whose base change `x` lifts to `𝒲`
  obtain ⟨i₀, s₀, W₀, hW₀, w, hcov, z, φ, hφ⟩ := exists_singleCover_lift B S hS a H D c hc i x
  refine exists_descent_of_singleCover B S hS 𝒳.val.p 𝒴.val.p Ff hp hq hFf h𝒳 h𝒴
    (fun D c hc => hHom D c hc) (fun D c hc => hEq D c hc) D c hc i y x γ hγ.toIsHomLift
    i₀ s₀ hW₀ w hcov ?_
  -- the base change system and its lift to the big affine fppf category
  let V := BigAffineFppf.baseChangeSystem D i₀ w
  let Vc := BigAffineFppf.baseChangeCone D c i₀ w
  have hVlim : IsLimit ((BigFppfOver.toScheme B S hS).mapCone Vc) :=
    isLimit_baseChangeCone D c i₀ w hc
  have hVaff : ∀ j, IsAffineOver B S hS (V.obj j) :=
    fun j => isAffineOver_pullback _ _ hW₀ (D.obj j.left).2 (D.obj i₀).2
  have hVcaff : IsAffineOver B S hS Vc.pt :=
    isAffineOver_pullback _ _ hW₀ c.pt.2 (D.obj i₀).2
  let Vs := BigAffineFppf.baseChangeSnd D i₀ w
  let vT := pullback.snd w (ι.map (c.π.app i₀))
  have hVsc : ∀ j, Vc.π.app j ≫ Vs.app j = vT ≫ (overCone D c i₀).π.app j :=
    baseChangeCone_π_app_snd D c i₀ w
  -- the pullback of `y` to the first stage of the base change system
  let j₀ : Over i₀ := Over.mk (𝟙 i₀)
  obtain ⟨t₀, ht₀⟩ : ∃ t : V.obj j₀ ⟶ ι.obj (D.obj i),
      t = Vs.app j₀ ≫ ι.map (D.map (j₀.hom ≫ s₀)) := ⟨_, rfl⟩
  let y' : 𝒴.val.p.Fiber (V.obj j₀) := pullbackFiber 𝒴.val.p y t₀
  obtain ⟨π, hπ⟩ : ∃ π : y'.1 ⟶ y.1, π = IsPreFibered.pullbackMap y.2 t₀ := ⟨_, rfl⟩
  have iπ : 𝒴.val.p.IsHomLift t₀ π := by
    rw [hπ]
    exact (IsPreFibered.pullbackMap.IsCartesian y.2 t₀).toIsHomLift
  -- the lift `z` as an object over the limit of the base change system
  have iφ : 𝒳.val.p.IsHomLift vT φ := hφ
  have hz : 𝒲.val.p.obj z = Vc.pt :=
    (Functor.congr_obj hFa z).symm.trans (@IsHomLift.domain_eq _ _ _ _ 𝒳.val.p _ _ _ _ vT φ iφ)
  -- the comparison of `a ≫ f` of the lift with `y'`
  obtain ⟨ℓ₀, hℓ₀⟩ : ∃ ℓ : Vc.pt ⟶ V.obj j₀, ℓ = Vc.π.app j₀ := ⟨_, rfl⟩
  have hℓ₀t : vT ≫ ι.map (c.π.app i) = ℓ₀ ≫ t₀ := by
    rw [hℓ₀, ht₀, ← Category.assoc, hVsc j₀]
    simp only [overCone, Functor.mapCone_π_app, Cone.whisker_π, Functor.whiskerLeft_app,
      Over.forget_obj]
    exact congrArg (fun k => vT ≫ ι.map k) (c.w (j₀.hom ≫ s₀)).symm
  have iFφγ : 𝒴.val.p.IsHomLift (vT ≫ ι.map (c.π.app i)) (Ff.map φ ≫ γ) :=
    @IsHomLift.comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (CategoryTheory.PresheafOfCategories.isHomLift_map_of_comp hFf vT φ iφ) hγ.toIsHomLift
  obtain ⟨γt, iγt, hγt⟩ := exists_lift' hq iπ ℓ₀ hℓ₀t iFφγ
  have cγt : 𝒴.val.p.IsStronglyCartesian ((BigAffineFppf.inclusion B S hS).map
      ((liftCone hVaff Vc hVcaff).π.app j₀)) γt := by
    have : 𝒴.val.p.IsHomLift ℓ₀ γt := iγt
    have := hq.isStronglyCartesian_homLift ℓ₀ γt
    rwa [hℓ₀] at this
  -- limit preservation on objects of `a ≫ f` descends the lift
  obtain ⟨i', j, x', xU, δ, β, γ', cδ, iβ, -, cγ', hsq⟩ :=
    hLP (Over i₀) ((IsAffineOver B S hS).lift V hVaff) (liftCone hVaff Vc hVcaff)
      (isLimitLiftCone hVaff Vc hVcaff hVlim) j₀ y' ⟨z, hz⟩ γt cγt
  -- the descended lift, read in `𝒳`, is the descended restriction of `x`
  let X₀ : 𝒳.val.p.Fiber (V.obj i') := ⟨Fa.obj x'.1, (Functor.congr_obj hFa x'.1).trans x'.2⟩
  have iaβ : 𝒳.val.p.IsHomLift (𝟙 Vc.pt) (Fa.map β) :=
    CategoryTheory.PresheafOfCategories.isHomLift_map_of_comp hFa _ β iβ
  have iaδ : 𝒳.val.p.IsHomLift (Vc.π.app i') (Fa.map δ) :=
    CategoryTheory.PresheafOfCategories.isHomLift_map_of_comp hFa _ δ cδ.toIsHomLift
  have iγ' : 𝒴.val.p.IsHomLift (V.map j) γ' := cγ'.toIsHomLift
  have key : D.map j.left ≫ D.map (j₀.hom ≫ s₀) = D.map (i'.hom ≫ s₀) := by
    rw [← D.map_comp, ← Category.assoc, Over.w j]
  have hnat : V.map j ≫ t₀ = Vs.app i' ≫ ι.map (D.map (i'.hom ≫ s₀)) := by
    rw [ht₀, ← Category.assoc, Vs.naturality j]
    change Vs.app i' ≫ ι.map (D.map j.left) ≫ ι.map (D.map (j₀.hom ≫ s₀)) = _
    rw [← ι.map_comp, key]
  refine ⟨i', X₀, Fa.obj xU.1, Fa.map β ≫ φ, Fa.map δ, γ' ≫ π, ?_, iaδ, ?_, ?_⟩
  · exact isHomLift_of_eq' (Category.id_comp vT)
      (@IsHomLift.comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ iaβ iφ)
  · exact isHomLift_of_eq' hnat (@IsHomLift.comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ iγ' iπ)
  · have hsq' : Ff.map (Fa.map δ) ≫ γ' = Ff.map (Fa.map β) ≫ γt := hsq
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ π) hsq').trans
      ((Category.assoc _ _ _).trans ((congrArg (Ff.map (Fa.map β) ≫ ·) hγt).trans ?_)))
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ γ) (Ff.map_comp _ _).symm)

end Stack

end AlgebraicGeometry
