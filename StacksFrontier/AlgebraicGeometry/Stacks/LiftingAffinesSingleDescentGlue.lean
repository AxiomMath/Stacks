module

public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesSingleDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackKernelPairDescent

/-!
# Gluing the descended smooth lift along one étale surjective morphism (Stacks 0CJU)

This file finishes the descent of smooth lifts along one étale surjective morphism `ε : X ⟶ U` of
`AlgebraicGeometry.Stack.EtaleSmoothLift.exists_quotientData`: the 1-morphism `x' : Y ⟶ 𝒳'` of `ξ`
descends to the quotient `U' = Y / R'` along the 2-morphism `Θ = σ₂^* ⁻¹ ∘ σ₁^*` on the kernel
pair `R'`, whose cocycle condition is the transitivity of `(σ₁, σ₂)`.

## Main results

* `AlgebraicGeometry.Stack.EtaleSmoothLift.cocycle_aux`: the cocycle identity in a plain category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

namespace CategoryTheory.Bicategory

/-- **The local filler of the descended smooth lift is compatible on the overlap**, in a strict
bicategory: whiskering `β = cξ ≫ incX ◁ γ` by the two projections `b₁, b₂` of the overlap gives
the same 2-morphism up to transport, by the coherences of `σ₁, σ₂` and the agreement `key` of the
two comparisons. -/
theorem descent_filler_compat_aux {𝔅 : Type*} [Bicategory 𝔅] [Bicategory.Strict 𝔅]
    {N X U R Y Q Z : 𝔅} {b₁ b₂ : N ⟶ X} {εb : X ⟶ U} {incX : X ⟶ Y} {incN : N ⟶ R}
    {s t : R ⟶ Y} {e : Y ⟶ Q} {iU : U ⟶ Q} {Fu : U ⟶ Z} {FN : N ⟶ Z} {Fx : X ⟶ Z}
    {yY : Y ⟶ Z} {yR : R ⟶ Z} {Gq : Q ⟶ Z}
    (cξ : Fx ⟶ incX ≫ yY) (cη : FN ⟶ incN ≫ yR) (σ₁c : yR ⟶ s ≫ yY) (σ₂c : yR ⟶ t ≫ yY)
    (γ : yY ⟶ e ≫ Gq) (hinc₁ : incN ≫ s = b₁ ≫ incX) (hinc₂ : incN ≫ t = b₂ ≫ incX)
    (hts : t ≫ (e ≫ Gq) = s ≫ (e ≫ Gq)) (hL₁ : FN = b₁ ≫ Fx)
    (hR₁ : b₁ ≫ (incX ≫ yY) = incN ≫ (s ≫ yY)) (hL₂ : FN = b₂ ≫ Fx)
    (hR₂ : b₂ ≫ (incX ≫ yY) = incN ≫ (t ≫ yY))
    (coh₁ : cη ≫ (incN ◁ σ₁c) = eqToHom hL₁ ≫ (b₁ ◁ cξ) ≫ eqToHom hR₁)
    (coh₂ : cη ≫ (incN ◁ σ₂c) = eqToHom hL₂ ≫ (b₂ ◁ cξ) ≫ eqToHom hR₂)
    (key : σ₂c ≫ (t ◁ γ) ≫ eqToHom hts = σ₁c ≫ (s ◁ γ))
    (hFx : εb ≫ Fu = Fx) (hβ₂ : incX ≫ (e ≫ Gq) = εb ≫ (iU ≫ Gq))
    (h₁ : b₁ ≫ (εb ≫ Fu) = b₂ ≫ (εb ≫ Fu))
    (h₂ : b₂ ≫ (εb ≫ (iU ≫ Gq)) = b₁ ≫ (εb ≫ (iU ≫ Gq))) :
    b₁ ◁ (eqToHom hFx ≫ cξ ≫ (incX ◁ γ) ≫ eqToHom hβ₂) =
      eqToHom h₁ ≫ (b₂ ◁ (eqToHom hFx ≫ cξ ≫ (incX ◁ γ) ≫ eqToHom hβ₂)) ≫ eqToHom h₂ := by
  subst hFx hL₁
  have e₁ : b₁ ◁ cξ = cη ≫ (incN ◁ σ₁c) ≫ eqToHom hR₁.symm := by
    rw [reassoc_of% coh₁]
    simp
  have e₂ : b₂ ◁ cξ = eqToHom hL₂.symm ≫ cη ≫ (incN ◁ σ₂c) ≫ eqToHom hR₂.symm := by
    rw [reassoc_of% coh₂]
    simp
  have w₁ := whiskerLeft_whiskerLeft_eqToHom hinc₁ γ
    (by rw [← Strict.assoc, ← hinc₁, Strict.assoc]) (by rw [← Strict.assoc, ← hinc₁, Strict.assoc])
  have w₂ := whiskerLeft_whiskerLeft_eqToHom hinc₂ γ
    (by rw [← Strict.assoc, ← hinc₂, Strict.assoc]) (by rw [← Strict.assoc, ← hinc₂, Strict.assoc])
  have w₁' := (comp_eqToHom_iff _ _ _).1 w₁.symm
  have w₂' := (comp_eqToHom_iff _ _ _).1 w₂.symm
  have key' := congrArg (incN ◁ ·) key
  simp only [whiskerLeft_comp, whiskerLeft_eqToHom] at key'
  simp only [whiskerLeft_comp, whiskerLeft_eqToHom, e₁, e₂, w₁', w₂', Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← reassoc_of% key']
  simp

end CategoryTheory.Bicategory

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} {ι : 𝒳 ⟶ 𝒳'} {hι : IsThickening ι}
  {W : AlgebraicSpaces B S hS}
  {x : (algebraicSpaceStackFunctor B S hS).obj W ⟶ 𝒳}
  {hx : AlgebraicStacks.IsSmooth B S hS x}

namespace EtaleSmoothLift

/-- **The cocycle identity of `Θ = u⁻¹ ≫ v`, in a plain category.** From the three relations
given by `a ≫ σ₂ = b ≫ σ₁`, `c ≫ σ₁ = a ≫ σ₁` and `c ≫ σ₂ = b ≫ σ₂` at one point. -/
theorem cocycle_aux {D : Type*} [Category D] {Ω E₁ E₂ E₃ Ft₁ Fs₁ Ft₂ Fs₂ Ft₃ Fs₃ : D}
    (ax : Ω ⟶ E₂) (bx : Ω ⟶ E₁) (cx : Ω ⟶ E₃) [IsIso bx] [IsIso cx]
    (u₁ : E₁ ⟶ Ft₁) (v₁ : E₁ ⟶ Fs₁) (u₂ : E₂ ⟶ Ft₂) (v₂ : E₂ ⟶ Fs₂) (u₃ : E₃ ⟶ Ft₃)
    (v₃ : E₃ ⟶ Fs₃) [IsIso u₁] [IsIso u₂] [IsIso u₃]
    (p₁₂ : Fs₁ = Ft₂) (p₁₃ : Ft₃ = Ft₁) (p₂₃ : Fs₃ = Fs₂)
    (hA : ax ≫ u₂ = bx ≫ v₁ ≫ eqToHom p₁₂) (hB : cx ≫ v₃ ≫ eqToHom p₂₃ = ax ≫ v₂)
    (hC : cx ≫ u₃ ≫ eqToHom p₁₃ = bx ≫ u₁) :
    (inv u₁ ≫ v₁) ≫ eqToHom p₁₂ ≫ (inv u₂ ≫ v₂) =
      eqToHom p₁₃.symm ≫ (inv u₃ ≫ v₃) ≫ eqToHom p₂₃ := by
  subst p₁₂ p₁₃ p₂₃
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at hA hB hC ⊢
  have hv₁ : v₁ = inv bx ≫ ax ≫ u₂ := by rw [hA]; simp
  have hu₁ : inv u₁ = inv u₃ ≫ inv cx ≫ bx := by
    rw [IsIso.inv_eq_of_hom_inv_id (f := u₁) (g := inv u₃ ≫ inv cx ≫ bx)]
    rw [← cancel_epi bx, ← Category.assoc, ← hC]
    simp
  rw [hu₁, hv₁]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← hB]
  simp

/-- `AlgebraicGeometry.Stack.EtaleSmoothLift.cocycle_aux` with explicit inverses and with the
transports in the shape of `AlgebraicGeometry.Stack.kernelPairComponent`. -/
theorem cocycle_aux' {D : Type*} [Category D] {Ω E₁ E₂ E₃ Ft₁ Fs₁ Ft₂ Fs₂ Ft₃ Fs₃ : D}
    (ax : Ω ⟶ E₂) (bx : Ω ⟶ E₁) (cx : Ω ⟶ E₃) (bx' : E₁ ⟶ Ω) (cx' : E₃ ⟶ Ω)
    (hb : bx ≫ bx' = 𝟙 _) (hb' : bx' ≫ bx = 𝟙 _) (hc : cx ≫ cx' = 𝟙 _) (hc' : cx' ≫ cx = 𝟙 _)
    (u₁ : E₁ ⟶ Ft₁) (v₁ : E₁ ⟶ Fs₁) (u₂ : E₂ ⟶ Ft₂) (v₂ : E₂ ⟶ Fs₂) (u₃ : E₃ ⟶ Ft₃)
    (v₃ : E₃ ⟶ Fs₃) (u₁' : Ft₁ ⟶ E₁) (u₂' : Ft₂ ⟶ E₂) (u₃' : Ft₃ ⟶ E₃)
    (hu₁ : u₁' ≫ u₁ = 𝟙 _) (hu₁' : u₁ ≫ u₁' = 𝟙 _) (hu₂ : u₂' ≫ u₂ = 𝟙 _)
    (hu₂' : u₂ ≫ u₂' = 𝟙 _) (hu₃ : u₃' ≫ u₃ = 𝟙 _) (hu₃' : u₃ ≫ u₃' = 𝟙 _)
    (p₁₂ : Fs₁ = Ft₂) (p₁₃ : Ft₃ = Ft₁) (p₂₃ : Fs₃ = Fs₂) (e₁ : Ft₁ = Ft₁) (e₂ : Ft₂ = Ft₂)
    (e₃ : Fs₂ = Fs₂)
    (hA : ax ≫ u₂ = bx ≫ v₁ ≫ eqToHom p₁₂) (hB : cx ≫ v₃ ≫ eqToHom p₂₃ = ax ≫ v₂)
    (hC : cx ≫ u₃ ≫ eqToHom p₁₃ = bx ≫ u₁) :
    (eqToHom e₁ ≫ (u₁' ≫ v₁) ≫ eqToHom p₁₂) ≫ (eqToHom e₂ ≫ (u₂' ≫ v₂) ≫ eqToHom e₃) =
      eqToHom p₁₃.symm ≫ (u₃' ≫ v₃) ≫ eqToHom p₂₃ := by
  have : IsIso bx := ⟨⟨bx', hb, hb'⟩⟩
  have : IsIso cx := ⟨⟨cx', hc, hc'⟩⟩
  have : IsIso u₁ := ⟨⟨u₁', hu₁', hu₁⟩⟩
  have : IsIso u₂ := ⟨⟨u₂', hu₂', hu₂⟩⟩
  have : IsIso u₃ := ⟨⟨u₃', hu₃', hu₃⟩⟩
  have i₁ : u₁' = inv u₁ := (IsIso.inv_eq_of_hom_inv_id hu₁').symm
  have i₂ : u₂' = inv u₂ := (IsIso.inv_eq_of_hom_inv_id hu₂').symm
  have i₃ : u₃' = inv u₃ := (IsIso.inv_eq_of_hom_inv_id hu₃').symm
  subst i₁ i₂ i₃
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id, Category.assoc] using
    cocycle_aux ax bx cx u₁ v₁ u₂ v₂ u₃ v₃ p₁₂ p₁₃ p₂₃ hA hB hC

/-- **Inverting a comparison compatible with `Θ = u⁻¹ ≫ v`, in a plain category.** -/
theorem inv_comparison_aux {D : Type*} [Category D] {E Ft Fs Gt Gs : D} (u : E ⟶ Ft)
    (v : E ⟶ Fs) (u' : Ft ⟶ E) (ψt : Gt ⟶ Ft) (ψs : Gs ⟶ Fs) (ψt' : Ft ⟶ Gt) (ψs' : Fs ⟶ Gs)
    (m : Gt ⟶ Gs) (hu' : u ≫ u' = 𝟙 _) (ht : ψt' ≫ ψt = 𝟙 _) (hs : ψs ≫ ψs' = 𝟙 _)
    (h : ψt ≫ (u' ≫ v) = m ≫ ψs) : u ≫ ψt' ≫ m = v ≫ ψs' := by
  have h₁ : u' ≫ v = ψt' ≫ m ≫ ψs := by rw [← h, ← Category.assoc, ht, Category.id_comp]
  have h₂ : v = u ≫ ψt' ≫ m ≫ ψs := by rw [← h₁, ← Category.assoc, hu', Category.id_comp]
  rw [h₂]
  simp only [Category.assoc, hs, Category.comp_id]

/-- **The comparison 2-morphisms of two equal morphisms agree at every point.** -/
theorem comm_app_eq_of_eq {ζ ξ : EtaleSmoothLift B S hS ι hι W x hx} {f₁ f₂ : ζ ⟶ ξ}
    (h : f₁ = f₂) {V : BigFppfOver B S hS} (y : ζ.ambient.obj.obj (Opposite.op V)) :
    (Hom.comm f₁).hom.hom.app (elt.{u, w} ζ.ambient V y) ≫
        eqToHom (congrArg (fun f : ζ ⟶ ξ => ξ.ambientMap.hom.hom.obj
          (elt.{u, w} ξ.ambient V ((Hom.ambient f).hom.app _ y))) h) =
      (Hom.comm f₂).hom.hom.app (elt.{u, w} ζ.ambient V y) := by
  subst h
  simp only
  exact Category.comp_id _

variable {ξ η : EtaleSmoothLift B S hS ι hι W x hx} (σ₁ σ₂ : η ⟶ ξ)
  {U : Space.SpacesEtale B S hS W} {ε₀ : ξ.base ⟶ U}

/-- Componentwise, `inv α` is a right inverse of the 2-isomorphism `α` of stack 1-morphisms. -/
private theorem app_hom_inv_id {A : AlgebraicStacks.{u, w} B S hS} {P R : A ⟶ 𝒳'}
    (α : P ⟶ R) [IsIso α] (o) : α.hom.hom.app o ≫ (inv α).hom.hom.app o = 𝟙 _ :=
  congrArg (fun γ => γ.hom.hom.app o) (IsIso.hom_inv_id α)

/-- Componentwise, `inv α` is a left inverse of the 2-isomorphism `α` of stack 1-morphisms. -/
private theorem app_inv_hom_id {A : AlgebraicStacks.{u, w} B S hS} {P R : A ⟶ 𝒳'}
    (α : P ⟶ R) [IsIso α] (o) : (inv α).hom.hom.app o ≫ α.hom.hom.app o = 𝟙 _ :=
  congrArg (fun γ => γ.hom.hom.app o) (IsIso.inv_hom_id α)

/-- **The cocycle condition of the descent 2-morphism on the kernel pair** is the transitivity of
`(σ₁, σ₂)`. -/
theorem descentComponent_cocycle (_hpb : IsPullback (Hom.base σ₁) (Hom.base σ₂) ε₀ ε₀)
    (htrans : ∀ (ω : EtaleSmoothLift B S hS ι hι W x hx) (a b : ω ⟶ η),
      IsPullback (Hom.base a) (Hom.base b) (Hom.base σ₂) (Hom.base σ₁) → a ≫ σ₂ = b ≫ σ₁ →
        ∃ c : ω ⟶ η, c ≫ σ₁ = a ≫ σ₁ ∧ c ≫ σ₂ = b ≫ σ₂)
    {Q : AlgebraicSpaces B S hS} {e : ξ.ambient ⟶ Q}
    (hkp : IsPullback (Hom.ambient σ₂) (Hom.ambient σ₁) e e)
    (V : BigFppfOver B S hS) (r₁ r₂ r₃ : η.ambient.obj.obj (Opposite.op V))
    (h₁₂ : (Hom.ambient σ₁).hom.app _ r₁ = (Hom.ambient σ₂).hom.app _ r₂)
    (h₁₃ : (Hom.ambient σ₂).hom.app _ r₃ = (Hom.ambient σ₂).hom.app _ r₁)
    (h₂₃ : (Hom.ambient σ₁).hom.app _ r₃ = (Hom.ambient σ₁).hom.app _ r₂) :
    kernelPairComponent ξ.ambientMap (inv (Hom.comm σ₂) ≫ Hom.comm σ₁) r₁ rfl h₁₂ ≫
        kernelPairComponent ξ.ambientMap (inv (Hom.comm σ₂) ≫ Hom.comm σ₁) r₂ rfl rfl =
      kernelPairComponent ξ.ambientMap (inv (Hom.comm σ₂) ≫ Hom.comm σ₁) r₃ h₁₃ h₂₃ := by
  -- the triple overlap
  obtain ⟨ω, a, hω, ha⟩ := exists_hom_base_eq η (pullback.fst (Hom.base σ₂) (Hom.base σ₁))
  have hh : (eqToHom hω ≫ pullback.snd (Hom.base σ₂) (Hom.base σ₁)) ≫ Hom.base σ₁ =
      Hom.base (a ≫ σ₂) := by
    show _ = Hom.base a ≫ Hom.base σ₂
    rw [ha, Category.assoc, Category.assoc, pullback.condition]
  let b : ω ⟶ η := fillIn σ₁ (a ≫ σ₂) _ hh
  have hab : a ≫ σ₂ = b ≫ σ₁ := (fillIn_comp σ₁ (a ≫ σ₂) _ hh).symm
  have hbase : IsPullback (Hom.base a) (Hom.base b) (Hom.base σ₂) (Hom.base σ₁) := by
    refine (IsPullback.of_hasPullback (Hom.base σ₂) (Hom.base σ₁)).of_iso (eqToIso hω.symm)
      (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
    · simp [ha]
    · show _ = _ ≫ (eqToHom hω ≫ pullback.snd _ _)
      simp
  obtain ⟨c, hc₁, hc₂⟩ := htrans ω a b hbase hab
  have hamb := (AlgebraicSpaces.isPullback_hom B S hS
    (isPullback_ambient σ₂ σ₁ a b hab hbase)).map ((evaluation _ (Type u)).obj (Opposite.op V))
  obtain ⟨y, hy₁, hy₂⟩ := Types.exists_of_isPullback hamb r₂ r₁ h₁₂.symm
  have hr₃ : r₃ = (Hom.ambient c).hom.app _ y := Types.ext_of_isPullback
    ((AlgebraicSpaces.isPullback_hom B S hS hkp).map ((evaluation _ (Type u)).obj (Opposite.op V)))
    (h₁₃.trans ((congrArg ((Hom.ambient σ₂).hom.app _) hy₂.symm).trans
      (congrArg (fun m => (Hom.ambient m).hom.app (Opposite.op V) y) hc₂).symm))
    (h₂₃.trans ((congrArg ((Hom.ambient σ₁).hom.app _) hy₁.symm).trans
      (congrArg (fun m => (Hom.ambient m).hom.app (Opposite.op V) y) hc₁).symm))
  subst hy₁ hy₂ hr₃
  let o := elt.{u, w} ω.ambient V y
  let ob := elt.{u, w} η.ambient V ((Hom.ambient b).hom.app _ y)
  let oa := elt.{u, w} η.ambient V ((Hom.ambient a).hom.app _ y)
  let oc := elt.{u, w} η.ambient V ((Hom.ambient c).hom.app _ y)
  exact cocycle_aux' ((Hom.comm a).hom.hom.app o) ((Hom.comm b).hom.hom.app o)
    ((Hom.comm c).hom.hom.app o) ((inv (Hom.comm b)).hom.hom.app o)
    ((inv (Hom.comm c)).hom.hom.app o)
    (app_hom_inv_id (Hom.comm b) o)
    (app_inv_hom_id (Hom.comm b) o)
    (app_hom_inv_id (Hom.comm c) o)
    (app_inv_hom_id (Hom.comm c) o)
    ((Hom.comm σ₂).hom.hom.app ob) ((Hom.comm σ₁).hom.hom.app ob)
    ((Hom.comm σ₂).hom.hom.app oa) ((Hom.comm σ₁).hom.hom.app oa)
    ((Hom.comm σ₂).hom.hom.app oc) ((Hom.comm σ₁).hom.hom.app oc)
    ((inv (Hom.comm σ₂)).hom.hom.app ob) ((inv (Hom.comm σ₂)).hom.hom.app oa)
    ((inv (Hom.comm σ₂)).hom.hom.app oc)
    (app_inv_hom_id (Hom.comm σ₂) ob)
    (app_hom_inv_id (Hom.comm σ₂) ob)
    (app_inv_hom_id (Hom.comm σ₂) oa)
    (app_hom_inv_id (Hom.comm σ₂) oa)
    (app_inv_hom_id (Hom.comm σ₂) oc)
    (app_hom_inv_id (Hom.comm σ₂) oc)
    _ _ _ _ _ _
    (((comp_eqToHom_iff _ _ _).1 (comm_app_eq_of_eq hab y)).trans (Category.assoc _ _ _))
    ((Category.assoc _ _ _).symm.trans (comm_app_eq_of_eq hc₁ y))
    ((Category.assoc _ _ _).symm.trans (comm_app_eq_of_eq hc₂ y))

/-- **The two comparisons of the descended 1-morphism agree on the overlap.** If `ψ` compares
the descent of `x'` with `x'` compatibly with `Θ`, then `σ₂^* ∘ t^*ψ⁻¹` and `σ₁^* ∘ s^*ψ⁻¹`
agree. -/
theorem comm_whiskerLeft_inv_eq {Q : AlgebraicSpaces B S hS} {e : ξ.ambient ⟶ Q}
    (hkp : IsPullback (Hom.ambient σ₂) (Hom.ambient σ₁) e e)
    (G : (algebraicSpaceStackFunctor.{u, w} B S hS).obj Q ⟶ 𝒳')
    (ψ : (algebraicSpaceStackFunctor.{u, w} B S hS).map e ≫ G ⟶ ξ.ambientMap) [IsIso ψ]
    (hψ : ∀ (V : BigFppfOver B S hS) (r : η.ambient.obj.obj (Opposite.op V)),
      ψ.hom.hom.app (elt.{u, w} ξ.ambient V ((Hom.ambient σ₂).hom.app _ r)) ≫
          (inv (Hom.comm σ₂) ≫ Hom.comm σ₁).hom.hom.app (elt.{u, w} η.ambient V r) =
        G.hom.hom.map (eltHom.{u, w} (T := Q) (𝟙 V) (eq_map_id (kernelPair_app_eq hkp r))) ≫
          ψ.hom.hom.app (elt.{u, w} ξ.ambient V ((Hom.ambient σ₁).hom.app _ r))) :
    Hom.comm σ₂ ≫ ((algebraicSpaceStackFunctor.{u, w} B S hS).map (Hom.ambient σ₂) ◁ inv ψ) ≫
        eqToHom (congrArg (fun f => (algebraicSpaceStackFunctor.{u, w} B S hS).map f ≫ G)
          hkp.w) =
      Hom.comm σ₁ ≫ ((algebraicSpaceStackFunctor.{u, w} B S hS).map (Hom.ambient σ₁) ◁ inv ψ) := by
  apply InducedBicategory.hom₂_ext
  apply InducedBicategory.hom₂_ext
  apply BasedNatTrans.ext
  ext ⟨V, ⟨r⟩⟩
  have h := hψ V r
  have hb : (eltHom.{u, w} (T := Q) (𝟙 V) (eq_map_id (kernelPair_app_eq hkp r))) =
      eqToHom (congrArg (elt.{u, w} Q V) (kernelPair_app_eq hkp r)) :=
    elt_hom_ext (by rw [eqToHom_base, eqToHom_refl]; rfl)
  rw [hb, eqToHom_map] at h
  let o := elt.{u, w} η.ambient V r
  have key := inv_comparison_aux ((Hom.comm σ₂).hom.hom.app o) ((Hom.comm σ₁).hom.hom.app o)
    ((inv (Hom.comm σ₂)).hom.hom.app o)
    (ψ.hom.hom.app (elt.{u, w} ξ.ambient V ((Hom.ambient σ₂).hom.app _ r)))
    (ψ.hom.hom.app (elt.{u, w} ξ.ambient V ((Hom.ambient σ₁).hom.app _ r)))
    ((inv ψ).hom.hom.app (elt.{u, w} ξ.ambient V ((Hom.ambient σ₂).hom.app _ r)))
    ((inv ψ).hom.hom.app (elt.{u, w} ξ.ambient V ((Hom.ambient σ₁).hom.app _ r)))
    _ (app_hom_inv_id (Hom.comm σ₂) o)
    (app_inv_hom_id ψ (elt.{u, w} ξ.ambient V ((Hom.ambient σ₂).hom.app _ r)))
    (app_hom_inv_id ψ (elt.{u, w} ξ.ambient V ((Hom.ambient σ₁).hom.app _ r))) h
  refine Eq.trans ?_ key
  exact congrArg (fun z => (Hom.comm σ₂).hom.hom.app o ≫
    (inv ψ).hom.hom.app (elt.{u, w} ξ.ambient V ((Hom.ambient σ₂).hom.app _ r)) ≫ z)
    (eqToHom_hom_hom_app _ _)

/-- **Descent of smooth lifts along one étale surjective morphism** (Stacks 0CJU). Let
`ε : X ⟶ U` be étale and surjective with `X` representable, `ξ` a smooth lift over `X` and
`σ₁, σ₂ : η ⟶ ξ` reflexive, symmetric and transitive morphisms over the two projections of
`X ×_U X`. Then there are a smooth lift `ζ` over `U` and a morphism `m : ξ ⟶ ζ` over `ε` with
`σ₁ ≫ m = σ₂ ≫ m`. -/
theorem exists_descent_single (hrep : ξ.base.obj.left.obj.IsRepresentable)
    (hsurj : Space.IsSurjective B S hS ε₀.hom.left.hom)
    (hpb : IsPullback (Hom.base σ₁) (Hom.base σ₂) ε₀ ε₀)
    (hrefl : ∃ r : ξ ⟶ η, r ≫ σ₁ = 𝟙 ξ ∧ r ≫ σ₂ = 𝟙 ξ)
    (hsymm : ∃ v : η ⟶ η, v ≫ σ₁ = σ₂ ∧ v ≫ σ₂ = σ₁)
    (htrans : ∀ (ω : EtaleSmoothLift B S hS ι hι W x hx) (a b : ω ⟶ η),
      IsPullback (Hom.base a) (Hom.base b) (Hom.base σ₂) (Hom.base σ₁) → a ≫ σ₂ = b ≫ σ₁ →
        ∃ c : ω ⟶ η, c ≫ σ₁ = a ≫ σ₁ ∧ c ≫ σ₂ = b ≫ σ₂) :
    ∃ (ζ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) (m : ξ ⟶ ζ.1),
      (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsHomLift ε₀ m ∧ σ₁ ≫ m = σ₂ ≫ m := by
  obtain ⟨Q, e, iU, hkp, het, hsur, hcomm, hcart⟩ :=
    exists_quotientData σ₁ σ₂ hrep hsurj hpb hrefl hsymm htrans
  have he₁ : Space.IsEtaleCovering B S hS (fun _ : PUnit.{u + 1} => ξ.ambient.obj)
      (fun _ => e.hom) :=
    ⟨Q.property, fun _ => ξ.ambient.property, fun _ => het,
      Set.eq_univ_of_forall fun y => Set.mem_iUnion.2 ⟨PUnit.unit, hsur y⟩⟩
  have heU : Space.IsEtaleCovering B S hS (fun _ : PUnit.{u + 1} => ξ.base.obj.left.obj)
      (fun _ => ε₀.hom.left.hom) :=
    ⟨U.obj.left.property, fun _ => ξ.base.obj.left.property,
      fun _ => Space.SpacesEtale.isEtale_toSpaces_map B S hS W ε₀,
      Set.eq_univ_of_forall fun y => Set.mem_iUnion.2 ⟨PUnit.unit, hsurj y⟩⟩
  obtain ⟨Gq, ψ, hψ⟩ := exists_hom_of_kernelPair.{u, u, w} ξ.ambientMap
    (inv (Hom.comm σ₂) ≫ Hom.comm σ₁) hkp he₁
    (descentComponent_cocycle σ₁ σ₂ hpb htrans hkp)
  have key := comm_whiskerLeft_inv_eq σ₁ σ₂ hkp Gq ψ hψ
  have hpbA : IsPullback (Hom.base σ₁).hom.left (Hom.base σ₂).hom.left ε₀.hom.left
      ε₀.hom.left := hpb.map (Space.SpacesEtale.toSpaces B S hS W)
  let β : (algebraicSpaceStackFunctor.{u, w} B S hS).map ε₀.hom.left ≫
        (((algebraicSpaceStackFunctor.{u, w} B S hS).map U.obj.hom ≫ x) ≫ ι) ⟶
      (algebraicSpaceStackFunctor.{u, w} B S hS).map ε₀.hom.left ≫
        ((algebraicSpaceStackFunctor.{u, w} B S hS).map iU ≫ Gq) :=
    eqToHom (gluing_left_leg ε₀).symm ≫ ξ.comm.hom ≫
      ((algebraicSpaceStackFunctor.{u, w} B S hS).map ξ.inclusion ◁ inv ψ) ≫
        eqToHom (gluing_right_leg Gq hcomm).symm
  obtain ⟨αQ, hαQ⟩ := exists_hom₂_of_isEtaleCovering_of_isPullback
    (fun _ : PUnit.{u + 1} => ε₀.hom.left) heU (fun _ => β)
    (fun _ _ => η.base.obj.left) (fun _ _ => (Hom.base σ₁).hom.left)
    (fun _ _ => (Hom.base σ₂).hom.left) (fun _ _ => hpbA)
    (fun _ _ => descent_filler_compat_aux ξ.comm.hom η.comm.hom (Hom.comm σ₁) (Hom.comm σ₂)
      (inv ψ) (gluing_square_leg (Hom.inclusion_comp σ₁)).symm
      (gluing_square_leg (Hom.inclusion_comp σ₂)).symm _ _ _ _ _ (Hom.coherence σ₁)
      (Hom.coherence σ₂) key _ _ _ _)
  have hcoh : ξ.comm.hom ≫
      ((algebraicSpaceStackFunctor.{u, w} B S hS).map ξ.inclusion ◁ inv ψ) =
        eqToHom (gluing_left_leg ε₀) ≫
          ((algebraicSpaceStackFunctor.{u, w} B S hS).map ε₀.hom.left ◁ αQ) ≫
            eqToHom (gluing_right_leg Gq hcomm) := by
    rw [hαQ PUnit.unit]
    simp only [β, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      eqToHom_trans, Category.comp_id]
  let G : GluingDatum.{u, w, u} (hι := hι) (hx := hx) U :=
    { ambient := Q
      inclusion := iU
      ambientMap := Gq
      isSmooth_ambientMap := isSmooth_of_isEtaleCovering Gq (fun _ : PUnit.{u + 1} => e) he₁
        (fun _ => AlgebraicStacks.isSmooth_of_twoIso B S hS (asIso ψ).symm ξ.isSmooth_ambientMap)
      comm := asIso αQ
      K := PUnit.{u + 1}
      ξ := fun _ => ξ
      base := fun _ => ε₀
      e := fun _ => e
      inclusion_comp := fun _ => hcomm
      isPullback := fun _ => hcart
      isEtaleCovering := he₁
      γ := fun _ => inv ψ
      coherence := fun _ => hcoh }
  refine ⟨⟨G.glue, rfl⟩, G.glueHom PUnit.unit, ?_, ?_⟩
  · show (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsHomLift
      ((proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).map (G.glueHom PUnit.unit))
      (G.glueHom PUnit.unit)
    infer_instance
  · exact hom_congr _ _ hpb.w hkp.w.symm
      (heq_of_comp_eqToHom _ _ _ ((Category.assoc _ _ _).trans key)).symm

end EtaleSmoothLift

end AlgebraicGeometry.Stack
