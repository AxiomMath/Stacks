module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackOneMorphismDescent

/-!
# Descent of 1-morphisms along one étale covering, from a 2-morphism on the kernel pair

Let `e : Y ⟶ T` be an étale surjective morphism of algebraic spaces with kernel pair
`(t, s) : R ⟶ Y`, and `F : Y ⟶ 𝒴` a 1-morphism into an algebraic stack. A 2-morphism
`Θ : F ∘ t ⟶ F ∘ s` satisfying the cocycle condition pointwise gives pointwise gluing data for
`F` along `e`, so `F` descends to a 1-morphism `G : T ⟶ 𝒴`.

## Main results

* `AlgebraicGeometry.Stack.kernelPairGluing`: the pointwise gluing data.
* `AlgebraicGeometry.Stack.exists_hom_of_kernelPair`: the descended 1-morphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe u v w

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒴 : AlgebraicStacks.{u, w} B S hS} {T Y R : AlgebraicSpaces B S hS} {e : Y ⟶ T}
  {t s : R ⟶ Y}

/-- A pair of points with the same image lifts uniquely to the kernel pair. -/
theorem existsUnique_kernelPair_point (hkp : IsPullback t s e e) (V : BigFppfOver B S hS)
    (a b : Y.obj.obj (Opposite.op V)) (h : e.hom.app _ a = e.hom.app _ b) :
    ∃! r : R.obj.obj (Opposite.op V), t.hom.app _ r = a ∧ s.hom.app _ r = b := by
  have hT := (AlgebraicSpaces.isPullback_hom B S hS hkp).map
    ((evaluation _ (Type u)).obj (Opposite.op V))
  obtain ⟨r, hr₁, hr₂⟩ := Types.exists_of_isPullback hT a b h
  exact ⟨r, ⟨hr₁, hr₂⟩, fun r' ⟨h₁, h₂⟩ =>
    Types.ext_of_isPullback hT (h₁.trans hr₁.symm) (h₂.trans hr₂.symm)⟩

variable (F : (algebraicSpaceStackFunctor.{u, w} B S hS).obj Y ⟶ 𝒴)
  (Θ : (algebraicSpaceStackFunctor.{u, w} B S hS).map t ≫ F ⟶
    (algebraicSpaceStackFunctor.{u, w} B S hS).map s ≫ F)

/-- The component of `Θ` at a point `r` of the kernel pair, read between the values of `F` at
two points equal to `t r` and `s r`. -/
def kernelPairComponent {V : BigFppfOver B S hS} (r : R.obj.obj (Opposite.op V))
    {a b : Y.obj.obj (Opposite.op V)} (ha : t.hom.app _ r = a) (hb : s.hom.app _ r = b) :
    F.hom.hom.obj (elt.{u, w} Y V a) ⟶ F.hom.hom.obj (elt.{u, w} Y V b) :=
  eqToHom (congrArg (fun z => F.hom.hom.obj (elt.{u, w} Y V z)) ha.symm) ≫
    Θ.hom.hom.app (elt.{u, w} R V r) ≫
      eqToHom (congrArg (fun z => F.hom.hom.obj (elt.{u, w} Y V z)) hb)

/-- With both transport equalities `rfl`, `kernelPairComponent` is the component of `Θ` at `r`. -/
theorem kernelPairComponent_rfl {V : BigFppfOver B S hS} (r : R.obj.obj (Opposite.op V)) :
    kernelPairComponent F Θ r rfl rfl = Θ.hom.hom.app (elt.{u, w} R V r) := by
  simp only [kernelPairComponent, eqToHom_refl, Category.id_comp]
  exact Category.comp_id _

/-- **The components of `Θ` are natural in the point of the kernel pair.** -/
theorem kernelPairComponent_naturality {V W : BigFppfOver B S hS} (r : R.obj.obj (Opposite.op V))
    (r' : R.obj.obj (Opposite.op W)) {a b : Y.obj.obj (Opposite.op V)}
    {a' b' : Y.obj.obj (Opposite.op W)} (ha : t.hom.app _ r = a) (hb : s.hom.app _ r = b)
    (ha' : t.hom.app _ r' = a') (hb' : s.hom.app _ r' = b')
    (κa : elt.{u, w} Y W a' ⟶ elt.{u, w} Y V a) (κb : elt.{u, w} Y W b' ⟶ elt.{u, w} Y V b)
    (g : W ⟶ V) (hκa : κa.base = g) (hκb : κb.base = g) (hr : r' = R.obj.map g.op r) :
    F.hom.hom.map κa ≫ kernelPairComponent F Θ r ha hb =
      kernelPairComponent F Θ r' ha' hb' ≫ F.hom.hom.map κb := by
  subst ha hb ha' hb' hr
  let κr : elt.{u, w} R W (R.obj.map g.op r) ⟶ elt.{u, w} R V r := eltHom g rfl
  obtain rfl : κa = ((algebraicSpaceStackFunctor.{u, w} B S hS).map t).hom.hom.map κr :=
    elt_hom_ext hκa
  obtain rfl : κb = ((algebraicSpaceStackFunctor.{u, w} B S hS).map s).hom.hom.map κr :=
    elt_hom_ext hκb
  rw [kernelPairComponent_rfl, kernelPairComponent_rfl]
  exact Θ.hom.hom.naturality κr

/-- Two ways of transporting along a pair of equalities agree. -/
theorem comp_eqToHom_comp_eqToHom_eq {C : Type*} [Category C] {A B C₁ C₂ D E : C}
    (x : A ⟶ B) (y : D ⟶ E) (p₁ : B = C₁) (q₁ : C₁ = D) (p₂ : B = C₂) (q₂ : C₂ = D) :
    (x ≫ eqToHom p₁) ≫ eqToHom q₁ ≫ y = (x ≫ eqToHom p₂) ≫ eqToHom q₂ ≫ y := by
  subst p₁ q₁ p₂
  simp

/-- **The cocycle condition, read on points with the same images.** -/
theorem kernelPairComponent_cocycle
    (hcoc : ∀ (V : BigFppfOver B S hS) (r₁ r₂ r₃ : R.obj.obj (Opposite.op V))
      (h₁₂ : s.hom.app _ r₁ = t.hom.app _ r₂) (h₁₃ : t.hom.app _ r₃ = t.hom.app _ r₁)
      (h₂₃ : s.hom.app _ r₃ = s.hom.app _ r₂),
      kernelPairComponent F Θ r₁ rfl h₁₂ ≫ kernelPairComponent F Θ r₂ rfl rfl =
        kernelPairComponent F Θ r₃ h₁₃ h₂₃)
    {V : BigFppfOver B S hS} (r₁ r₂ r₃ : R.obj.obj (Opposite.op V))
    {a b c : Y.obj.obj (Opposite.op V)} (ha : t.hom.app _ r₁ = a) (hb : s.hom.app _ r₁ = b)
    (hb' : t.hom.app _ r₂ = b) (hc : s.hom.app _ r₂ = c) (ha'' : t.hom.app _ r₃ = a)
    (hc'' : s.hom.app _ r₃ = c) :
    kernelPairComponent F Θ r₁ ha hb ≫ kernelPairComponent F Θ r₂ hb' hc =
      kernelPairComponent F Θ r₃ ha'' hc'' := by
  subst ha hb hc
  rw [← hcoc V r₁ r₂ r₃ hb'.symm ha'' hc'']
  simp only [kernelPairComponent, Category.assoc]
  exact congrArg _ (comp_eqToHom_comp_eqToHom_eq _ _ _ _ _ _)

variable (hkp : IsPullback t s e e)

/-- The point of the kernel pair over a pair of points with the same image. -/
def kernelPairPoint {V : BigFppfOver B S hS} (a b : Y.obj.obj (Opposite.op V))
    (h : e.hom.app _ a = e.hom.app _ b) : R.obj.obj (Opposite.op V) :=
  (existsUnique_kernelPair_point hkp V a b h).exists.choose

/-- The point `kernelPairPoint hkp a b h` maps to `a` under `t` and to `b` under `s`. -/
theorem kernelPairPoint_spec {V : BigFppfOver B S hS} (a b : Y.obj.obj (Opposite.op V))
    (h : e.hom.app _ a = e.hom.app _ b) :
    t.hom.app _ (kernelPairPoint hkp a b h) = a ∧ s.hom.app _ (kernelPairPoint hkp a b h) = b :=
  (existsUnique_kernelPair_point hkp V a b h).exists.choose_spec

/-- A point of the kernel pair mapping to `a` under `t` and to `b` under `s` is
`kernelPairPoint hkp a b h`. -/
theorem kernelPairPoint_eq {V : BigFppfOver B S hS} (a b : Y.obj.obj (Opposite.op V))
    (h : e.hom.app _ a = e.hom.app _ b) (r : R.obj.obj (Opposite.op V))
    (ha : t.hom.app _ r = a) (hb : s.hom.app _ r = b) : r = kernelPairPoint hkp a b h :=
  (existsUnique_kernelPair_point hkp V a b h).unique ⟨ha, hb⟩ (kernelPairPoint_spec hkp a b h)

/-- **Pointwise gluing data from a 2-morphism on the kernel pair.** -/
def kernelPairGluing
    (hcoc : ∀ (V : BigFppfOver B S hS) (r₁ r₂ r₃ : R.obj.obj (Opposite.op V))
      (h₁₂ : s.hom.app _ r₁ = t.hom.app _ r₂) (h₁₃ : t.hom.app _ r₃ = t.hom.app _ r₁)
      (h₂₃ : s.hom.app _ r₃ = s.hom.app _ r₂),
      kernelPairComponent F Θ r₁ rfl h₁₂ ≫ kernelPairComponent F Θ r₂ rfl rfl =
        kernelPairComponent F Θ r₃ h₁₃ h₂₃) :
    PointwiseGluing (fun _ : PUnit.{v + 1} => e) (fun _ => F) where
  φ _ _ V a b h := kernelPairComponent F Θ (kernelPairPoint hkp a b h)
    (kernelPairPoint_spec hkp a b h).1 (kernelPairPoint_spec hkp a b h).2
  isHomLift _ _ V a b h := by
    have h₁ : 𝒴.val.val.p.IsHomLift (𝟙 V) (eqToHom (congrArg
        (fun z => F.hom.hom.obj (elt.{u, w} Y V z)) (kernelPairPoint_spec hkp a b h).1.symm)) :=
      IsHomLift.eqToHom_domain_lift_id _ (BasedFunctor.w_obj F.hom.hom _)
    have h₂ : 𝒴.val.val.p.IsHomLift (𝟙 V)
        (Θ.hom.hom.app (elt.{u, w} R V (kernelPairPoint hkp a b h))) :=
      Θ.hom.hom.isHomLift' (elt.{u, w} R V (kernelPairPoint hkp a b h))
    have h₃ : 𝒴.val.val.p.IsHomLift (𝟙 V) (eqToHom (congrArg
        (fun z => F.hom.hom.obj (elt.{u, w} Y V z)) (kernelPairPoint_spec hkp a b h).2)) :=
      IsHomLift.eqToHom_domain_lift_id _ (BasedFunctor.w_obj F.hom.hom _)
    exact @IsHomLift.comp_of_lift_id _ _ _ _ _ V _ _ _ _ _ h₁
      (@IsHomLift.comp_of_lift_id _ _ _ _ _ V _ _ _ _ _ h₂ h₃)
  naturality := fun _ _ {V W} {a a' b b'} κa κb hκ h h' =>
    kernelPairComponent_naturality F Θ _ _ _ _ _ _ κa κb κa.base rfl hκ.symm
      (kernelPairPoint_eq hkp a' b' h' _
        ((NatTrans.naturality_apply t.hom κa.base.op (kernelPairPoint hkp a b h)).trans
          ((congrArg (Y.obj.map κa.base.op) (kernelPairPoint_spec hkp a b h).1).trans
            (point_eq_of_hom.{u, w} κa).symm))
        ((NatTrans.naturality_apply s.hom κa.base.op (kernelPairPoint hkp a b h)).trans
          ((congrArg (Y.obj.map κa.base.op) (kernelPairPoint_spec hkp a b h).2).trans
            ((congrArg (fun g => Y.obj.map g.op b) hκ).trans
              (point_eq_of_hom.{u, w} κb).symm)))).symm
  cocycle _ _ _ V a b c h₁ h₂ :=
    kernelPairComponent_cocycle F Θ hcoc _ _ _ (kernelPairPoint_spec hkp a b h₁).1
      (kernelPairPoint_spec hkp a b h₁).2 (kernelPairPoint_spec hkp b c h₂).1
      (kernelPairPoint_spec hkp b c h₂).2 (kernelPairPoint_spec hkp a c (h₁.trans h₂)).1
      (kernelPairPoint_spec hkp a c (h₁.trans h₂)).2

omit hkp in
/-- The component of `Θ` at a point `r'` equal to `r` is the component of `Θ` at `r`. -/
theorem kernelPairComponent_eq_of_eq {V : BigFppfOver B S hS} {r r' : R.obj.obj (Opposite.op V)}
    (hr : r' = r) (ha : t.hom.app _ r' = t.hom.app _ r) (hb : s.hom.app _ r' = s.hom.app _ r) :
    kernelPairComponent F Θ r' ha hb = kernelPairComponent F Θ r rfl rfl := by
  subst hr
  rfl

omit hkp in
/-- The two points of the kernel pair over a point of `R` have the same image. -/
theorem kernelPair_app_eq (hkp : IsPullback t s e e) {V : BigFppfOver B S hS}
    (r : R.obj.obj (Opposite.op V)) :
    e.hom.app _ (t.hom.app _ r) = e.hom.app _ (s.hom.app _ r) := by
  simpa using congrArg (fun φ => φ.app (Opposite.op V) r)
    (AlgebraicSpaces.isPullback_hom B S hS hkp).w

/-- **1-morphisms out of an algebraic space descend along an étale covering, from a 2-morphism
on the kernel pair.** -/
theorem exists_hom_of_kernelPair
    (he : Space.IsEtaleCovering B S hS (fun _ : PUnit.{v + 1} => Y.obj) (fun _ => e.hom))
    (hcoc : ∀ (V : BigFppfOver B S hS) (r₁ r₂ r₃ : R.obj.obj (Opposite.op V))
      (h₁₂ : s.hom.app _ r₁ = t.hom.app _ r₂) (h₁₃ : t.hom.app _ r₃ = t.hom.app _ r₁)
      (h₂₃ : s.hom.app _ r₃ = s.hom.app _ r₂),
      kernelPairComponent F Θ r₁ rfl h₁₂ ≫ kernelPairComponent F Θ r₂ rfl rfl =
        kernelPairComponent F Θ r₃ h₁₃ h₂₃) :
    ∃ (G : (algebraicSpaceStackFunctor.{u, w} B S hS).obj T ⟶ 𝒴)
      (ψ : (algebraicSpaceStackFunctor.{u, w} B S hS).map e ≫ G ⟶ F),
      ∀ (V : BigFppfOver B S hS) (r : R.obj.obj (Opposite.op V)),
        ψ.hom.hom.app (elt.{u, w} Y V (t.hom.app _ r)) ≫ Θ.hom.hom.app (elt.{u, w} R V r) =
          G.hom.hom.map (eltHom.{u, w} (T := T) (𝟙 V) (eq_map_id (kernelPair_app_eq hkp r))) ≫
            ψ.hom.hom.app (elt.{u, w} Y V (s.hom.app _ r)) := by
  obtain ⟨G, ψ, hψ⟩ := exists_hom_of_isEtaleCovering he (kernelPairGluing F Θ hkp hcoc)
  refine ⟨G, ψ PUnit.unit, fun V r => ?_⟩
  have h := hψ PUnit.unit PUnit.unit V _ _ (kernelPair_app_eq hkp r)
  have hr := kernelPairPoint_eq hkp _ _ (kernelPair_app_eq hkp r) r rfl rfl
  have hk := kernelPairComponent_eq_of_eq F Θ hr.symm
    (kernelPairPoint_spec hkp _ _ (kernelPair_app_eq hkp r)).1
    (kernelPairPoint_spec hkp _ _ (kernelPair_app_eq hkp r)).2
  rw [kernelPairComponent_rfl] at hk
  exact (congrArg (_ ≫ ·) hk).symm.trans h

end AlgebraicGeometry.Stack
