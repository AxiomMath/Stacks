module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Injective
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.Unramified.Finite

/-! # Base change of an injective module along an étale ring map

Let `A` be a Noetherian ring, let `A → C` be a flat ring map and let `I` be an injective
`A`-module.

* The `A`-module `C ⊗[A] I` is injective.  By Baer's criterion it suffices to extend maps out of
  ideals `𝔞 ⊆ A`; an ideal is finitely presented, so `Hom_C(C ⊗ 𝔞, C ⊗ I)` is the base change of
  `Hom_A(𝔞, I)` (`Module.FinitePresentation.isBaseChange_map`), and restriction from
  `Hom_A(A, I)` to `Hom_A(𝔞, I)` is surjective by injectivity of `I`, hence so is its base
  change.
* If moreover `A → C` is formally unramified and essentially of finite type — for instance
  étale — then `C ⊗[A] I` is an injective `C`-module.  The multiplication `C ⊗[A] C → C` is split
  by an element `t` with `(1 ⊗ c - c ⊗ 1) t = 0` and `t ↦ 1`
  (`Algebra.FormallyUnramified.iff_exists_tensorProduct`), and `t` makes every `C`-module `L` a
  natural `C`-linear retract of the extended module `C ⊗[A] L`.  Maps out of the extended module
  into `C ⊗[A] I` are `A`-linear maps out of `L`, which extend by the first part; composing with
  the retraction gives the extension over `C`.

These are the inputs of Stacks 09TL (2) that see no geometry: the restriction of an injective
quasi-coherent module on a Noetherian affine scheme to an affine scheme étale over it is again an
injective quasi-coherent module.

## Main results

* `Module.Injective.tensorProduct_of_flat`: `C ⊗[A] I` is an injective `A`-module.
* `Module.Injective.tensorProduct_of_formallyUnramified`: `C ⊗[A] I` is an injective
  `C`-module.
-/

@[expose] public section

open TensorProduct

universe u

namespace Module.Injective

variable {A : Type u} [CommRing A] (C : Type u) [CommRing C] [Algebra A C]

/-- Let `A` be a Noetherian ring and `A → C` a flat ring map.  If `I` is an injective
`A`-module, then so is `C ⊗[A] I`. -/
theorem tensorProduct_of_flat [IsNoetherianRing A] [Module.Flat A C]
    (I : Type u) [AddCommGroup I] [Module A I] [Module.Injective A I] :
    Module.Injective A (C ⊗[A] I) := by
  refine Module.Baer.injective fun 𝔞 g => ?_
  have hI : Module.Baer A I := Module.Baer.of_injective inferInstance
  have : Module.FinitePresentation A 𝔞 := Module.finitePresentation_of_finite A 𝔞
  have hbc := Module.FinitePresentation.isBaseChange_map A 𝔞 I C
  let ρ : (C ⊗[A] A →ₗ[C] C ⊗[A] I) →ₗ[C] (C ⊗[A] 𝔞 →ₗ[C] C ⊗[A] I) :=
    LinearMap.lcomp C (C ⊗[A] I) (𝔞.subtype.baseChange C)
  have hG : LinearMap.liftBaseChange C g ∈ LinearMap.range ρ := by
    refine hbc.inductionOn _ (fun G => G ∈ LinearMap.range ρ) (Submodule.zero_mem _) ?_
      (fun s n hn => Submodule.smul_mem _ s hn) (fun n₁ n₂ h₁ h₂ => Submodule.add_mem _ h₁ h₂)
    intro f
    obtain ⟨f', hf'⟩ := hI 𝔞 f
    refine ⟨f'.baseChange C, ?_⟩
    have hcomp : f' ∘ₗ 𝔞.subtype = f := LinearMap.ext fun x => hf' x x.2
    show (f'.baseChange C) ∘ₗ (𝔞.subtype.baseChange C) = f.baseChange C
    rw [← LinearMap.baseChange_comp, hcomp]
  obtain ⟨H, hH⟩ := hG
  refine ⟨(H.restrictScalars A) ∘ₗ TensorProduct.mk A C A 1, fun x hx => ?_⟩
  have := LinearMap.congr_fun hH ((1 : C) ⊗ₜ[A] (⟨x, hx⟩ : 𝔞))
  simpa [ρ] using this

section Unramified

variable (L : Type u) [AddCommGroup L] [Module C L] [Module A L] [IsScalarTower A C L]

/-- The action of `C ⊗[A] C` on the extended module `C ⊗[A] L`, through the `C`-module
structure of `L` on the right factor, read as an `A`-linear map `L → C ⊗[A] L`. -/
def tensorAct : C ⊗[A] C →ₗ[A] L →ₗ[A] C ⊗[A] L :=
  TensorProduct.lift (LinearMap.mk₂ A (fun x y =>
      (TensorProduct.mk A C L x) ∘ₗ ((LinearMap.lsmul C L y).restrictScalars A))
    (fun x x' y => by ext l; simp [TensorProduct.add_tmul])
    (fun a x y => by ext l; simp [TensorProduct.smul_tmul'])
    (fun x y y' => by ext l; simp [add_smul, TensorProduct.tmul_add])
    (fun a x y => by ext l; simp [smul_assoc, TensorProduct.tmul_smul]))

variable {C L}

/-- On a pure tensor, `tensorAct` sends `l` to `x ⊗ₜ (y • l)`. -/
theorem tensorAct_tmul (x y : C) (l : L) : tensorAct C L (x ⊗ₜ[A] y) l = x ⊗ₜ[A] (y • l) := by
  simp [tensorAct]

/-- Multiplying by `1 ⊗ₜ c` on the right acts on `L` by `c` before applying `tensorAct`. -/
theorem tensorAct_mul_one_tmul (w : C ⊗[A] C) (c : C) (l : L) :
    tensorAct C L (w * ((1 : C) ⊗ₜ[A] c)) l = tensorAct C L w (c • l) := by
  induction w using TensorProduct.induction_on <;>
    simp_all [tensorAct_tmul, mul_smul, add_mul]

/-- Multiplying by `c ⊗ₜ 1` on the right acts on `C ⊗[A] L` by `c` after applying `tensorAct`. -/
theorem tensorAct_mul_tmul_one (w : C ⊗[A] C) (c : C) (l : L) :
    tensorAct C L (w * (c ⊗ₜ[A] (1 : C))) l = c • tensorAct C L w l := by
  induction w using TensorProduct.induction_on <;>
    simp_all [tensorAct_tmul, TensorProduct.smul_tmul', mul_comm, add_mul]

/-- Composing `tensorAct C L w` with the counit `C ⊗[A] L → L` of the `C`-module structure is
the action of the image of `w` under the multiplication `C ⊗[A] C → C`. -/
theorem liftBaseChange_tensorAct (w : C ⊗[A] C) (l : L) :
    LinearMap.liftBaseChange C ((LinearMap.id : L →ₗ[C] L).restrictScalars A)
      (tensorAct C L w l) = Algebra.TensorProduct.lmul' A w • l := by
  induction w using TensorProduct.induction_on <;>
    simp_all [tensorAct_tmul, mul_smul, add_smul]

/-- `tensorAct` is natural in `L` with respect to `C`-linear maps `f : L → L'`. -/
theorem tensorAct_naturality {L' : Type u} [AddCommGroup L'] [Module C L'] [Module A L']
    [IsScalarTower A C L'] (f : L →ₗ[C] L') (w : C ⊗[A] C) (l : L) :
    tensorAct C L' w (f l) = (f.restrictScalars A).lTensor C (tensorAct C L w l) := by
  induction w using TensorProduct.induction_on <;> simp_all [tensorAct_tmul]

variable (C L) in
/-- The section `L → C ⊗[A] L` of the multiplication map attached to an element `t` of
`C ⊗[A] C` with `(1 ⊗ c - c ⊗ 1) t = 0` for every `c`: it is `C`-linear for the left
`C`-module structure of `C ⊗[A] L`. -/
def tensorSection (t : C ⊗[A] C) (ht : ∀ c : C, ((1 : C) ⊗ₜ[A] c - c ⊗ₜ[A] (1 : C)) * t = 0) :
    L →ₗ[C] C ⊗[A] L where
  toFun := tensorAct C L t
  map_add' := (tensorAct C L t).map_add
  map_smul' c l := by
    have h : t * ((1 : C) ⊗ₜ[A] c) = t * (c ⊗ₜ[A] (1 : C)) := by
      have := ht c
      rw [sub_mul, sub_eq_zero] at this
      rw [mul_comm, this, mul_comm]
    change tensorAct C L t (c • l) = c • tensorAct C L t l
    rw [← tensorAct_mul_one_tmul, h, tensorAct_mul_tmul_one]

variable [IsNoetherianRing A] [Module.Flat A C] [Algebra.FormallyUnramified A C]
  [Algebra.EssFiniteType A C]

variable (C) in
/-- Let `A` be a Noetherian ring and `A → C` a flat, formally unramified ring map essentially of
finite type (for instance an étale ring map).  If `I` is an injective `A`-module, then
`C ⊗[A] I` is an injective `C`-module. -/
theorem tensorProduct_of_formallyUnramified
    (I : Type u) [AddCommGroup I] [Module A I] [Module.Injective A I] :
    Module.Injective C (C ⊗[A] I) where
  out X Y _ _ _ _ f hf g := by
    obtain ⟨t, ht, ht1⟩ := (Algebra.FormallyUnramified.iff_exists_tensorProduct
      (R := A) (S := C)).1 inferInstance
    let : Module A X := Module.compHom X (algebraMap A C)
    let : Module A Y := Module.compHom Y (algebraMap A C)
    have : IsScalarTower A C X := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    have : IsScalarTower A C Y := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    have hA := tensorProduct_of_flat (A := A) C I
    obtain ⟨h₀, hh₀⟩ := Module.Injective.out (R := A) (Q := C ⊗[A] I) (f.restrictScalars A) hf
      (g.restrictScalars A)
    refine ⟨(LinearMap.liftBaseChange C h₀) ∘ₗ tensorSection C Y t ht, fun x => ?_⟩
    show LinearMap.liftBaseChange C h₀ (tensorAct C Y t (f x)) = g x
    rw [tensorAct_naturality f t x]
    have key : ∀ w : C ⊗[A] X, LinearMap.liftBaseChange C h₀
        ((f.restrictScalars A).lTensor C w) =
        g (LinearMap.liftBaseChange C ((LinearMap.id : X →ₗ[C] X).restrictScalars A) w) := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul c x' =>
        simp only [LinearMap.lTensor_tmul, LinearMap.liftBaseChange_tmul,
          LinearMap.restrictScalars_apply, LinearMap.id_apply, map_smul]
        exact congrArg (c • ·) (hh₀ x')
      | add w₁ w₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    rw [key, liftBaseChange_tensorAct, ht1, one_smul]

end Unramified

end Module.Injective
