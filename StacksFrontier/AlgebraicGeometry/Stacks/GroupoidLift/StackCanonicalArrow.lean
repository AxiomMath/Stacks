module

public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.StackGroupoid

/-!
# Canonical arrows of the groupoid of a chart

Let `a : (Sch/U₀) ⟶ 𝒳` be a 1-morphism into a category fibred in groupoids and `ι : Spec P ⟶ U₀`
a chart over the affine object `T'`. Given two points `w₁ w₂ : P → C` and two morphisms
`c₁ : ξ w₁ ⟶ y`, `c₂ : ξ w₂ ⟶ y` of `𝒳` lying over one and the same morphism `m` of the base,
there is a unique arrow `ξ w₁ ⟶ ξ w₂` over the identity of `Spec C` through which `c₁` factors
via `c₂` (`AlgebraicGeometry.Stack.GroupoidLift.StackChart.canArr`). These canonical arrows are
stable under restriction, compose, and are the identities on the diagonal. They give the descent
arrow of the restriction of an object to a covering, together with its normalisation and its
cocycle condition.

## Main definitions

* `AlgebraicGeometry.Stack.GroupoidLift.StackChart.canArr`: the canonical arrow `ξ w₁ ⟶ ξ w₂`.

## Main results

* `AlgebraicGeometry.Stack.GroupoidLift.StackChart.map_canArr`: restriction.
* `AlgebraicGeometry.Stack.GroupoidLift.StackChart.comp_canArr`: composition.
* `AlgebraicGeometry.Stack.GroupoidLift.StackChart.canArr_eq_idt`: the diagonal.
-/

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry.Space.ChartDescent

namespace AlgebraicGeometry.Stack.GroupoidLift

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T' : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
  {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  {U₀ : BigFppfOver B S hS} {a : schemeFibredCategory B S hS U₀ ⟶ 𝒳}
  {P : SmallAlg (ringOf B S hS T') B.cutoff} {ι : specOver P ⟶ U₀}

namespace StackChart

variable {C : SmallAlg (ringOf B S hS T') B.cutoff} {y : 𝒳.val.obj} {W : BigFppfOver B S hS}

/-- **The canonical arrow** from `w₁` to `w₂` determined by two morphisms `c₁ : ξ w₁ ⟶ y` and
`c₂ : ξ w₂ ⟶ y` over the same `m : Spec C ⟶ W`: the unique `ψ` over the identity with
`ψ ≫ c₂ = c₁`. -/
noncomputable def canArr (m : specOver C ⟶ W) (w₁ w₂ : P.obj →ₐ[ringOf B S hS T'] C.obj)
    (c₁ : ξ a ι w₁ ⟶ y) (c₂ : ξ a ι w₂ ⟶ y) (h₁ : 𝒳.val.p.IsHomLift m c₁)
    (h₂ : 𝒳.val.p.IsHomLift m c₂) : Arr a ι C where
  src := w₁
  tgt := w₂
  hom :=
    haveI := h₁
    haveI := h₂
    haveI := 𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift m c₂
    Functor.IsCartesian.map 𝒳.val.p m c₂ c₁
  lift :=
    haveI := h₁
    haveI := h₂
    haveI := 𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift m c₂
    Functor.IsCartesian.map_isHomLift 𝒳.val.p m c₂ c₁

variable (m : specOver C ⟶ W) {w₁ w₂ w₃ : P.obj →ₐ[ringOf B S hS T'] C.obj}
  (c₁ : ξ a ι w₁ ⟶ y) (c₂ : ξ a ι w₂ ⟶ y) (c₃ : ξ a ι w₃ ⟶ y)
  (h₁ : 𝒳.val.p.IsHomLift m c₁) (h₂ : 𝒳.val.p.IsHomLift m c₂) (h₃ : 𝒳.val.p.IsHomLift m c₃)

/-- The source of the canonical arrow from `w₁` to `w₂` is `w₁`. -/
theorem canArr_src : (canArr m w₁ w₂ c₁ c₂ h₁ h₂).src = w₁ := rfl

/-- The target of the canonical arrow from `w₁` to `w₂` is `w₂`. -/
theorem canArr_tgt : (canArr m w₁ w₂ c₁ c₂ h₁ h₂).tgt = w₂ := rfl

/-- The canonical arrow followed by `c₂` is `c₁`. -/
theorem canArr_fac : (canArr m w₁ w₂ c₁ c₂ h₁ h₂).hom ≫ c₂ = c₁ := by
  have := h₁
  have := h₂
  have := 𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift m c₂
  exact Functor.IsCartesian.fac 𝒳.val.p m c₂ c₁

/-- Any morphism `ψ : ξ w₁ ⟶ ξ w₂` over the identity with `ψ ≫ c₂ = c₁` is the canonical arrow. -/
theorem canArr_hom_eq (ψ : ξ a ι w₁ ⟶ ξ a ι w₂) (hψ : 𝒳.val.p.IsHomLift (𝟙 (specOver C)) ψ)
    (hfac : ψ ≫ c₂ = c₁) : (canArr m w₁ w₂ c₁ c₂ h₁ h₂).hom = ψ := by
  have := h₁
  have := h₂
  have := hψ
  have := 𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift m c₂
  exact (Functor.IsCartesian.map_uniq 𝒳.val.p m c₂ c₁ ψ hfac).symm

/-- An arrow is the canonical arrow of any two morphisms it intertwines. -/
theorem eq_canArr (g : Arr a ι C) (hs : g.src = w₁) (ht : g.tgt = w₂)
    (hfac : eqToHom (congrArg (ξ a ι) hs.symm) ≫ g.hom ≫ eqToHom (congrArg (ξ a ι) ht) ≫ c₂ = c₁) :
    g = canArr m w₁ w₂ c₁ c₂ h₁ h₂ := by
  obtain ⟨s, t, φ, hl⟩ := g
  dsimp only at hs ht hfac
  subst hs ht
  simp only [eqToHom_refl, Category.id_comp] at hfac
  exact Arr.ext_heq rfl rfl (heq_of_eq (canArr_hom_eq m c₁ c₂ h₁ h₂ φ hl hfac).symm)

/-- **Restriction of a canonical arrow.** -/
theorem map_canArr {D : SmallAlg (ringOf B S hS T') B.cutoff} (h : C ⟶ D)
    (h₁' : 𝒳.val.p.IsHomLift (specOverMap h ≫ m) (trans a ι h w₁ ≫ c₁))
    (h₂' : 𝒳.val.p.IsHomLift (specOverMap h ≫ m) (trans a ι h w₂ ≫ c₂)) :
    Arr.map a ι h (canArr m w₁ w₂ c₁ c₂ h₁ h₂) =
      canArr (specOverMap h ≫ m) (h.hom.hom.comp w₁) (h.hom.hom.comp w₂)
        (trans a ι h w₁ ≫ c₁) (trans a ι h w₂ ≫ c₂) h₁' h₂' := by
  refine eq_canArr _ _ _ h₁' h₂' _ rfl rfl ?_
  have hf := Arr.map_hom_fac h (canArr m w₁ w₂ c₁ c₂ h₁ h₂)
  have hc := canArr_fac m c₁ c₂ h₁ h₂
  exact ((Category.id_comp _).trans (congrArg _ (Category.id_comp _))).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ c₂) hf).trans
      ((Category.assoc _ _ _).trans (congrArg _ hc))))

/-- **Composition of canonical arrows.** -/
theorem comp_canArr {w₂' : P.obj →ₐ[ringOf B S hS T'] C.obj} (c₂' : ξ a ι w₂' ⟶ y)
    (h₂' : 𝒳.val.p.IsHomLift m c₂') (e : w₂' = w₂)
    (hc : c₂' = eqToHom (congrArg (ξ a ι) e) ≫ c₂) :
    Arr.comp (canArr m w₂' w₃ c₂' c₃ h₂' h₃) (canArr m w₁ w₂ c₁ c₂ h₁ h₂) e =
      canArr m w₁ w₃ c₁ c₃ h₁ h₃ := by
  refine eq_canArr _ _ _ h₁ h₃ _ rfl rfl ?_
  have f₁ := canArr_fac m c₁ c₂ h₁ h₂
  have f₂ := canArr_fac m c₂' c₃ h₂' h₃
  exact ((Category.id_comp _).trans ((congrArg _ (Category.id_comp _)).trans
    ((Category.assoc _ _ _).trans (congrArg _ (Category.assoc _ _ _))))).trans
    ((congrArg (_ ≫ eqToHom _ ≫ ·) (f₂.trans hc)).trans
      ((congrArg _ ((eqToHom_trans_assoc _ _ _).trans (Category.id_comp _))).trans f₁))

/-- **Canonical arrows on the diagonal are identities.** -/
theorem canArr_eq_idt {w : P.obj →ₐ[ringOf B S hS T'] C.obj} (e₁ : w₁ = w) (e₂ : w₂ = w)
    (hc : c₁ = eqToHom (congrArg (ξ a ι) (e₁.trans e₂.symm)) ≫ c₂) :
    canArr m w₁ w₂ c₁ c₂ h₁ h₂ = Arr.idt w := by
  symm
  refine eq_canArr _ _ _ h₁ h₂ _ e₁.symm e₂.symm ?_
  exact (congrArg _ (Category.id_comp _)).trans ((eqToHom_trans_assoc _ _ _).trans hc.symm)

/-- **Congruence for canonical arrows.** -/
theorem canArr_congr {w₁' w₂' : P.obj →ₐ[ringOf B S hS T'] C.obj} (c₁' : ξ a ι w₁' ⟶ y)
    (c₂' : ξ a ι w₂' ⟶ y) (h₁' : 𝒳.val.p.IsHomLift m c₁') (h₂' : 𝒳.val.p.IsHomLift m c₂')
    (e₁ : w₁ = w₁') (e₂ : w₂ = w₂') (hc₁ : c₁ = eqToHom (congrArg (ξ a ι) e₁) ≫ c₁')
    (hc₂ : c₂ = eqToHom (congrArg (ξ a ι) e₂) ≫ c₂') :
    canArr m w₁ w₂ c₁ c₂ h₁ h₂ = canArr m w₁' w₂' c₁' c₂' h₁' h₂' := by
  subst e₁ e₂
  simp only [eqToHom_refl, Category.id_comp] at hc₁ hc₂
  subst hc₁ hc₂
  rfl

end StackChart

end AlgebraicGeometry.Stack.GroupoidLift

end
