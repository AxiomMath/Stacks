module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import StacksFrontier.Deformation.RingedSpaceThickening.FlatThickeningBoundary
public import StacksFrontier.Deformation.RingedSpaceThickening.BaseIdealTransition
public import StacksFrontier.Topology.Sheaves.Modules.Flat.PullbackTensorExact
import StacksCore.Tactic.StacksAttribute

/-!
# The two flat lifts of Stacks 08VT

In Situation **Stacks 08VS** the modules `π^* ℱ` and `h^* ℱ'₂` on `X'₁` are flat over `S'₁` and
restrict to `ℱ` on `X`. This file proves the flatness and builds the two flat lifts, together
with the remaining inputs of the boundary computation of **Stacks 08VT**.

## Main results

* `FlatShortExactThickeningDiagram.isFlatOver_pulledModule`: `h^* ℱ'₂` is flat over `S'₁`. On
  stalks the left square of the situation is a pushout of rings
  (`FlatShortExactThickeningDiagram.stalkSquareIsPushout₁₂`), by a Nakayama argument for the flat
  map `f'₁` and the square-zero ideal of `S'₁` (`isPushout_of_flat_of_sq_eq_bot`), so the stalk
  of `h^* ℱ'₂` is a base change of a flat module.
* `FlatShortExactThickeningDiagram.isFlatOver_trivialModule`: `π^* ℱ` is flat over `S'₁`, by the
  same argument for the square formed by `π` and the canonical splitting of the lower row.
* `FlatShortExactThickeningDiagram.isFlatOver_restriction`: `ℱ` is flat over `S`.
* `FlatShortExactThickeningDiagram.trivialLift`, `FlatShortExactThickeningDiagram.pulledLift`:
  the two flat lifts, with the identifications `i₁^* π^* ℱ ≅ ℱ` and `i₁^* h^* ℱ'₂ ≅ ℱ`.
* `FlatShortExactThickeningDiagram.underlyingExtensionClass_trivialLift`: the class `ξ` of
  `π^* ℱ` vanishes.
* `FlatShortExactThickeningDiagram.pushedExtension`: the unit `ℱ'₂ ⟶ h_* h^* ℱ'₂` is a map of
  extensions, which is how `h^* ℱ'₂` is the extension that **Stacks 08LC** produces from `ℱ'₂`.
* `FlatShortExactThickeningDiagram.baseTransition_shortExact`: the sequence
  `0 ⟶ f^* 𝒥₃ ⊗ ℱ ⟶ f^* 𝒥₂ ⊗ ℱ ⟶ f^* 𝒥₁ ⊗ ℱ ⟶ 0` is short exact (**Stacks 0GMU**).

## References

* [Stacks Project, Tag 08VT](https://stacks.math.columbia.edu/tag/08VT)
* [Stacks Project, Tag 08VS](https://stacks.math.columbia.edu/tag/08VS)
* [Stacks Project, Tag 08LI](https://stacks.math.columbia.edu/tag/08LI)
* [Stacks Project, Tag 0GMU](https://stacks.math.columbia.edu/tag/0GMU)
-/

@[expose] public section

open TensorProduct
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u w w'

namespace AlgebraicGeometry.RingedSpaceThickening

section SquareZeroNakayama

variable {A P Q : Type*} [CommRing A] [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]

/-- The multiplication map `J ⊗_A M ⟶ M` of an ideal on a module. -/
noncomputable abbrev idealSMulMap (J : Ideal A) (M : Type*) [AddCommGroup M] [Module A M] :
    J ⊗[A] M →ₗ[A] M :=
  TensorProduct.lift ((LinearMap.lsmul A M).comp J.subtype)

/-- The range of the multiplication map `J ⊗_A M ⟶ M` is the submodule `J • M` of `M`. -/
theorem range_idealSMulMap (J : Ideal A) (M : Type*) [AddCommGroup M] [Module A M] :
    LinearMap.range (idealSMulMap J M) = J • (⊤ : Submodule A M) := by
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul j m => exact Submodule.smul_mem_smul j.2 Submodule.mem_top
    | add s t hs ht =>
      rw [map_add]
      exact add_mem hs ht
  · exact Submodule.smul_le.mpr fun j hj m _ => ⟨⟨j, hj⟩ ⊗ₜ m, rfl⟩

/-- For a square-zero ideal `J`, tensoring with `J` does not see `J • M`: the map
`J ⊗_A M ⟶ J ⊗_A (M ⧸ J • M)` is bijective. -/
theorem lTensor_mkQ_bijective_of_sq_eq_bot (J : Ideal A) (hJ : J ^ 2 = ⊥)
    (M : Type*) [AddCommGroup M] [Module A M] :
    Function.Bijective ((J • (⊤ : Submodule A M)).mkQ.lTensor J) := by
  refine ⟨?_, LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective _)⟩
  rw [← LinearMap.ker_eq_bot, LinearMap.exact_iff.mp
    (lTensor_exact J (LinearMap.exact_subtype_mkQ (J • (⊤ : Submodule A M)))
      (Submodule.mkQ_surjective _)), eq_bot_iff]
  rintro _ ⟨t, rfl⟩
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul j m =>
    obtain ⟨m, hm⟩ := m
    simp only [LinearMap.lTensor_tmul, Submodule.subtype_apply, Submodule.mem_bot]
    induction hm using Submodule.smul_induction_on' with
    | smul a ha n _ =>
      rw [← TensorProduct.smul_tmul]
      have : a • j = 0 := by
        apply Subtype.ext
        have hmem : a * (j : A) ∈ J ^ 2 := by
          rw [pow_two]
          exact Ideal.mul_mem_mul ha j.2
        rwa [hJ] at hmem
      rw [this, TensorProduct.zero_tmul]
    | add x hx y hy hx' hy' =>
      rw [TensorProduct.tmul_add, hx', hy', add_zero]
  | add s t hs ht =>
    rw [map_add]
    exact add_mem hs ht

/-- A linear map carries `J • P` into `J • Q`. -/
theorem map_smul_top_le (J : Ideal A) (θ : P →ₗ[A] Q) :
    J • (⊤ : Submodule A P) ≤ (J • (⊤ : Submodule A Q)).comap θ :=
  Submodule.smul_le.mpr fun j hj p _ => by
    rw [Submodule.mem_comap, map_smul]
    exact Submodule.smul_mem_smul hj Submodule.mem_top

/-- **Nakayama's lemma for a square-zero ideal and a flat target.** A linear map `θ : P ⟶ Q`
into a flat module which is bijective modulo a square-zero ideal `J` is bijective. Surjectivity
holds because the cokernel `C` satisfies `C = J C = J² C = 0`; injectivity because a kernel
element lies in `J P`, is the image of some `t ∈ J ⊗ P`, and `J ⊗ θ` is bijective (it only sees
the reduction of `θ` modulo `J`) while `J ⊗ Q ⟶ Q` is injective by flatness. -/
theorem bijective_of_flat_of_sq_eq_bot [Module.Flat A Q] (J : Ideal A) (hJ : J ^ 2 = ⊥)
    (θ : P →ₗ[A] Q) (hsurj : ∀ q, ∃ p, q - θ p ∈ J • (⊤ : Submodule A Q))
    (hinj : ∀ p, θ p ∈ J • (⊤ : Submodule A Q) → p ∈ J • (⊤ : Submodule A P)) :
    Function.Bijective θ := by
  have hJJ : ∀ y ∈ J • (⊤ : Submodule A Q), ∀ j ∈ J, j • y = 0 := by
    intro y hy j hj
    have : j • y ∈ J • J • (⊤ : Submodule A Q) := Submodule.smul_mem_smul hj hy
    rwa [← Submodule.mul_smul, ← pow_two, hJ, Submodule.bot_smul] at this
  constructor
  · -- injectivity
    let θbar := (J • (⊤ : Submodule A P)).mapQ (J • (⊤ : Submodule A Q)) θ
      (map_smul_top_le J θ)
    have hθbar : Function.Bijective θbar := by
      constructor
      · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
        intro x hx
        obtain ⟨p, rfl⟩ := Submodule.mkQ_surjective _ x
        rw [LinearMap.mem_ker] at hx
        simp only [θbar, Submodule.mkQ_apply, Submodule.mapQ_apply,
          Submodule.Quotient.mk_eq_zero] at hx
        rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hinj p hx
      · intro y
        obtain ⟨q, rfl⟩ := Submodule.mkQ_surjective _ y
        obtain ⟨p, hp⟩ := hsurj q
        refine ⟨Submodule.Quotient.mk p, ?_⟩
        simp only [θbar, Submodule.mkQ_apply, Submodule.mapQ_apply]
        rwa [Submodule.Quotient.eq, ← neg_mem_iff, neg_sub]
    have hT : Function.Injective (θ.lTensor J) := by
      have hcomm : (J • (⊤ : Submodule A Q)).mkQ.lTensor J ∘ₗ θ.lTensor J =
          θbar.lTensor J ∘ₗ (J • (⊤ : Submodule A P)).mkQ.lTensor J := by
        rw [← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp]
        rfl
      have hl : Function.Injective (θbar.lTensor J) :=
        ((LinearEquiv.ofBijective θbar hθbar).lTensor J).injective
      have h := hl.comp (lTensor_mkQ_bijective_of_sq_eq_bot J hJ P).1
      intro a b hab
      apply h
      simpa only [Function.comp_apply, ← LinearMap.comp_apply, hcomm] using
        congrArg ((J • (⊤ : Submodule A Q)).mkQ.lTensor J) hab
    have hμ : Function.Injective (idealSMulMap J Q) := by
      have h1 := Module.Flat.rTensor_preserves_injective_linearMap (M := Q) J.subtype
        Subtype.val_injective
      have : idealSMulMap J Q = (TensorProduct.lid A Q).toLinearMap ∘ₗ J.subtype.rTensor Q := by
        ext j q
        simp
      rw [this]
      exact (TensorProduct.lid A Q).injective.comp h1
    have hnat : θ ∘ₗ idealSMulMap J P = idealSMulMap J Q ∘ₗ θ.lTensor J := by
      ext j p
      simp
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro p hp
    rw [LinearMap.mem_ker] at hp
    have hpJ : p ∈ J • (⊤ : Submodule A P) := hinj p (hp ▸ Submodule.zero_mem _)
    rw [← range_idealSMulMap] at hpJ
    obtain ⟨t, rfl⟩ := hpJ
    have h0 : idealSMulMap J Q (θ.lTensor J t) = 0 := by
      rw [← LinearMap.comp_apply, ← hnat, LinearMap.comp_apply, hp]
    have ht : t = 0 := hT (by rw [hμ (h0.trans (map_zero _).symm), map_zero])
    rw [Submodule.mem_bot, ht, map_zero]
  · -- surjectivity
    have hle : J • (⊤ : Submodule A Q) ≤ LinearMap.range θ := by
      refine Submodule.smul_le.mpr fun j hj q _ => ?_
      obtain ⟨p, hp⟩ := hsurj q
      refine ⟨j • p, ?_⟩
      have := hJJ _ hp j hj
      rw [smul_sub, sub_eq_zero] at this
      rw [map_smul, this]
    intro q
    obtain ⟨p, hp⟩ := hsurj q
    obtain ⟨p', hp'⟩ := hle hp
    exact ⟨p + p', by rw [map_add, hp', add_sub_cancel]⟩

end SquareZeroNakayama

section BaseChange

variable {A₂ A₁ B₂ B₁ E : Type*} [CommRing A₂] [CommRing A₁] [CommRing B₂] [CommRing B₁]
  [CommRing E] [Algebra A₂ A₁] [Algebra A₂ B₂] [Algebra A₁ B₁] [Algebra B₂ B₁] [Algebra A₂ B₁]
  [IsScalarTower A₂ A₁ B₁] [IsScalarTower A₂ B₂ B₁]

/-- **A morphism of flat square-zero thickenings over a base change is a base change.** Let
`A₂ ⟶ A₁` be a ring map, `J₁ ⊆ A₁` a square-zero ideal and `J₂ ⊆ A₂` an ideal mapping into
`J₁`, with `A₁ = A₂ + J₁`. Let `B₂` be an `A₂`-algebra and `B₁` a flat `A₁`-algebra with a
compatible map `B₂ ⟶ B₁`, and let `B₂ ⟶ E` and `B₁ ⟶ E` be compatible surjections with kernels
`J₂ B₂` and `J₁ B₁`. Then `B₁ = A₁ ⊗_{A₂} B₂`: the canonical map is bijective modulo `J₁`, where
both sides are `E`, hence bijective by `bijective_of_flat_of_sq_eq_bot`. -/
theorem isPushout_of_flat_of_sq_eq_bot [Module.Flat A₁ B₁] (J₁ : Ideal A₁) (hJ₁ : J₁ ^ 2 = ⊥)
    (J₂ : Ideal A₂) (hJ : J₂.map (algebraMap A₂ A₁) ≤ J₁)
    (hA : ∀ a : A₁, ∃ a' : A₂, a - algebraMap A₂ A₁ a' ∈ J₁)
    (ε₂ : B₂ →+* E) (ε₁ : B₁ →+* E) (hε : ε₁.comp (algebraMap B₂ B₁) = ε₂)
    (hε₂ : Function.Surjective ε₂)
    (hker₁ : RingHom.ker ε₁ = J₁.map (algebraMap A₁ B₁))
    (hker₂ : RingHom.ker ε₂ = J₂.map (algebraMap A₂ B₂)) :
    Algebra.IsPushout A₂ A₁ B₂ B₁ := by
  let θa : A₁ ⊗[A₂] B₂ →ₐ[A₁] B₁ := Algebra.TensorProduct.productLeftAlgHom
    (Algebra.ofId A₁ B₁) (IsScalarTower.toAlgHom A₂ B₂ B₁)
  let θ : A₁ ⊗[A₂] B₂ →ₗ[A₁] B₁ := θa.toLinearMap
  have hθ1 : ∀ b : B₂, θ (1 ⊗ₜ b) = algebraMap B₂ B₁ b := fun b => by simp [θ, θa]
  have hsmul₁ : J₁ • (⊤ : Submodule A₁ B₁) = (J₁.map (algebraMap A₁ B₁)).restrictScalars A₁ :=
    Ideal.smul_top_eq_map J₁
  have hbij : Function.Bijective θ := by
    refine bijective_of_flat_of_sq_eq_bot J₁ hJ₁ θ ?_ ?_
    · intro q
      obtain ⟨b, hb⟩ := hε₂ (ε₁ q)
      refine ⟨1 ⊗ₜ b, ?_⟩
      rw [hθ1, hsmul₁, Submodule.restrictScalars_mem, ← hker₁, RingHom.mem_ker, map_sub,
        ← RingHom.comp_apply, hε, hb, sub_self]
    · -- every element is congruent to some `1 ⊗ b` modulo `J₁`
      have hcong : ∀ p : A₁ ⊗[A₂] B₂, ∃ b : B₂,
          p - 1 ⊗ₜ b ∈ J₁.map (algebraMap A₁ (A₁ ⊗[A₂] B₂)) := by
        intro p
        induction p using TensorProduct.induction_on with
        | zero => exact ⟨0, by simp⟩
        | tmul a b =>
          obtain ⟨a', ha'⟩ := hA a
          refine ⟨a' • b, ?_⟩
          have h1 : a ⊗ₜ[A₂] b - 1 ⊗ₜ (a' • b) =
              algebraMap A₁ (A₁ ⊗[A₂] B₂) (a - algebraMap A₂ A₁ a') * (1 ⊗ₜ b) := by
            rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul,
              mul_one, Algebra.algebraMap_self, RingHom.id_apply, one_mul, sub_tmul,
              ← TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
          rw [h1]
          exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha')
        | add x y hx hy =>
          obtain ⟨b, hb⟩ := hx
          obtain ⟨b', hb'⟩ := hy
          refine ⟨b + b', ?_⟩
          rw [tmul_add, add_sub_add_comm]
          exact add_mem hb hb'
      intro p hp
      rw [Ideal.smul_top_eq_map J₁, Submodule.restrictScalars_mem]
      rw [hsmul₁, Submodule.restrictScalars_mem] at hp
      obtain ⟨b, hb⟩ := hcong p
      have hθb : θ (1 ⊗ₜ b) ∈ J₁.map (algebraMap A₁ B₁) := by
        have hdiff : θ (p - 1 ⊗ₜ b) ∈ J₁.map (algebraMap A₁ B₁) := by
          have he : (θa.toRingHom).comp (algebraMap A₁ (A₁ ⊗[A₂] B₂)) = algebraMap A₁ B₁ :=
            RingHom.ext fun a => θa.commutes a
          have := Ideal.mem_map_of_mem θa.toRingHom hb
          rwa [Ideal.map_map, he] at this
        simpa only [map_sub, sub_sub_cancel] using sub_mem hp hdiff
      rw [hθ1, ← hker₁, RingHom.mem_ker, ← RingHom.comp_apply, hε, ← RingHom.mem_ker,
        hker₂] at hθb
      have h1b : (1 : A₁) ⊗ₜ[A₂] b ∈ J₁.map (algebraMap A₁ (A₁ ⊗[A₂] B₂)) := by
        have := Ideal.mem_map_of_mem (Algebra.TensorProduct.includeRight :
          B₂ →ₐ[A₂] A₁ ⊗[A₂] B₂).toRingHom hθb
        rw [Ideal.map_map] at this
        have he : ((Algebra.TensorProduct.includeRight : B₂ →ₐ[A₂] A₁ ⊗[A₂] B₂).toRingHom).comp
            (algebraMap A₂ B₂) =
            (algebraMap A₁ (A₁ ⊗[A₂] B₂)).comp (algebraMap A₂ A₁) := by
          ext a
          simp [Algebra.algebraMap_eq_smul_one]
        rw [he, ← Ideal.map_map] at this
        exact Ideal.map_mono hJ this
      simpa only [sub_add_cancel] using add_mem hb h1b
  refine ⟨IsBaseChange.of_equiv (LinearEquiv.ofBijective θ hbij) fun b => ?_⟩
  rw [LinearEquiv.ofBijective_apply, hθ1]
  rfl

end BaseChange

section Stalks

/-- **Stalk maps along a commutative triangle**, with the points presented arbitrarily: for
`α ≫ β = γ` and points `α(p) = q`, `β(q) = r`, the composite of the two stalk maps is the stalk
map of `γ`, up to the identifications of stalks at equal points. -/
theorem stalkMap_eqToHom_comp {P Q R : RingedSpace.{u, u}} (α : P ⟶ Q) (β : Q ⟶ R) (γ : P ⟶ R)
    (h : α ≫ β = γ) (p : P) (q : Q) (r : R) (hq : α.hom.base p = q) (hr : β.hom.base q = r)
    (hr' : γ.hom.base p = r) :
    (eqToHom (congrArg R.presheaf.stalk hr.symm) ≫ β.hom.stalkMap q) ≫
        (eqToHom (congrArg Q.presheaf.stalk hq.symm) ≫ α.hom.stalkMap p) =
      eqToHom (congrArg R.presheaf.stalk hr'.symm) ≫ γ.hom.stalkMap p := by
  subst h hq hr
  simp only [eqToHom_refl, Category.id_comp]
  show _ = eqToHom _ ≫ (α.hom ≫ β.hom).stalkMap p
  rw [PresheafedSpace.stalkMap.comp]
  exact (Category.id_comp _).symm

/-- The stalk map of an identity, read through an identification of points, is the identity. -/
theorem eqToHom_comp_stalkMap_id (P : RingedSpace.{u, u}) (p : P)
    (h : (𝟙 P : P ⟶ P).hom.base p = p) :
    eqToHom (congrArg P.presheaf.stalk h.symm) ≫ (𝟙 P : P ⟶ P).hom.stalkMap p = 𝟙 _ := by
  have h1 : (𝟙 P : P ⟶ P).hom.stalkMap p = 𝟙 (P.presheaf.stalk p) :=
    PresheafedSpace.stalkMap.id P.toPresheafedSpace p
  rw [h1]
  exact Category.comp_id _

end Stalks

namespace FlatShortExactThickeningDiagram

variable (D : FlatShortExactThickeningDiagram.{u})

/-- Stalk maps along `α ≫ β = 𝟙 P`, with arbitrarily presented points, compose to the identity. -/
private theorem stalkMap_eqToHom_comp_eq_id {P Q : RingedSpace.{u, u}} (α : P ⟶ Q) (β : Q ⟶ P)
    (h : α ≫ β = 𝟙 P) (p : P) (q : Q) (hq : α.hom.base p = q) (hr : β.hom.base q = p) :
    (eqToHom (congrArg P.presheaf.stalk hr.symm) ≫ β.hom.stalkMap q) ≫
        (eqToHom (congrArg Q.presheaf.stalk hq.symm) ≫ α.hom.stalkMap p) = 𝟙 _ :=
  (stalkMap_eqToHom_comp α β (𝟙 P) h p q p hq hr rfl).trans (eqToHom_comp_stalkMap_id _ _ rfl)

/-- If `p₁ ∘ ψ = p₂` with `p₂` surjective, every element is congruent modulo `ker p₁` to some
element of the image of `ψ`. -/
private theorem exists_sub_mem_ker_of_comp_surjective {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] (p₁ : R →+* S) (ψ : T →+* R) (p₂ : T →+* S) (h : p₁.comp ψ = p₂)
    (hp : Function.Surjective p₂) (a : R) : ∃ a', a - ψ a' ∈ RingHom.ker p₁ := by
  obtain ⟨a', ha'⟩ := hp (p₁ a)
  refine ⟨a', ?_⟩
  rw [RingHom.mem_ker, map_sub, ← RingHom.comp_apply, h, ha', sub_self]

/-- **The left square of Situation 08VS is a pushout on stalks**: at every point `y` of `X'₁`,
`𝒪_{X'₁,y} = 𝒪_{S'₁,f'₁(y)} ⊗ 𝒪_{X'₂,h(y)}` over `𝒪_{S'₂}`. This is
`isPushout_of_flat_of_sq_eq_bot`: `f'₁` is flat, both squares `(f, f'₁)` and `(f, f'₂)` are
strict, and both thickenings of `S` are first order. -/
theorem stalkSquareIsPushout₁₂ :
    StalkSquareIsPushout D.upper.f₁₂ D.lower.f₁₂ D.f₁ D.f₂ D.comm₁₂ := by
  intro y
  have : IsIso D.upper.i₁.hom.base := D.upper.firstOrder₁.1.1
  obtain ⟨x, rfl⟩ : ∃ x, D.upper.i₁.hom.base x = y :=
    (TopCat.homeoOfIso (asIso D.upper.i₁.hom.base)).surjective y
  -- the point equations
  have hz : D.upper.i₂.hom.base x = D.upper.f₁₂.hom.base (D.upper.i₁.hom.base x) := by
    have h := congrArg (fun g : D.upper.X ⟶ D.upper.X₂ => g.hom.base x) D.upper.comm₁₂
    simpa using h.symm
  have hpt₁ : D.f₁.hom.base (D.upper.i₁.hom.base x) = D.lower.i₁.hom.base (D.f.hom.base x) :=
    stalkSquare_point D.restrict₁ x
  have hpt₂ : D.f₂.hom.base (D.upper.f₁₂.hom.base (D.upper.i₁.hom.base x)) =
      D.lower.i₂.hom.base (D.f.hom.base x) := by
    rw [← hz]
    exact stalkSquare_point D.restrict₂ x
  obtain ⟨hp₁, hJ₁, hε₁, hker₁⟩ := stalkMap_facts_of_isStrict D.morphism₁
    D.upper.firstOrder₁ D.lower.firstOrder₁ D.isStrict₁ x (D.upper.i₁.hom.base x) rfl hpt₁
  obtain ⟨hp₂, -, hε₂, hker₂⟩ := stalkMap_facts_of_isStrict D.morphism₂
    D.upper.firstOrder₂ D.lower.firstOrder₂ D.isStrict₂ x _ hz hpt₂
  simp only [eqToHom_refl, Category.id_comp] at hε₁ hker₁
  -- the rings and the algebra structures of the stalk square
  let AW := D.lower.X₂.presheaf.stalk (D.f₂.hom.base (D.upper.f₁₂.hom.base
    (D.upper.i₁.hom.base x)))
  let AT := D.lower.X₁.presheaf.stalk (D.f₁.hom.base (D.upper.i₁.hom.base x))
  let AZ := D.upper.X₂.presheaf.stalk (D.upper.f₁₂.hom.base (D.upper.i₁.hom.base x))
  let AY := D.upper.X₁.presheaf.stalk (D.upper.i₁.hom.base x)
  let ψ : AW ⟶ AT := eqToHom (congrArg D.lower.X₂.presheaf.stalk
    (stalkSquare_point D.comm₁₂ (D.upper.i₁.hom.base x))) ≫
      D.lower.f₁₂.hom.stalkMap (D.f₁.hom.base (D.upper.i₁.hom.base x))
  let _iWT : Algebra AW AT := ψ.hom.toAlgebra
  let _iWZ : Algebra AW AZ :=
    (D.f₂.hom.stalkMap (D.upper.f₁₂.hom.base (D.upper.i₁.hom.base x))).hom.toAlgebra
  let _iTY : Algebra AT AY := (D.f₁.hom.stalkMap (D.upper.i₁.hom.base x)).hom.toAlgebra
  let _iZY : Algebra AZ AY := (D.upper.f₁₂.hom.stalkMap (D.upper.i₁.hom.base x)).hom.toAlgebra
  let _iWY : Algebra AW AY :=
    ((D.upper.f₁₂.hom.stalkMap (D.upper.i₁.hom.base x)).hom.comp
      (D.f₂.hom.stalkMap (D.upper.f₁₂.hom.base (D.upper.i₁.hom.base x))).hom).toAlgebra
  have : IsScalarTower AW AZ AY := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower AW AT AY :=
    IsScalarTower.of_algebraMap_smul fun a b => congrArg (fun r => r * b)
      (congrArg (fun g : AW ⟶ AY => g.hom a)
        (stalkSquare_comm D.comm₁₂ (D.upper.i₁.hom.base x))).symm
  have : Module.Flat AT AY := D.flat₁ (D.upper.i₁.hom.base x)
  -- the two kernels on the base
  let p₁ : AT ⟶ D.lower.X.presheaf.stalk (D.f.hom.base x) :=
    eqToHom (congrArg D.lower.X₁.presheaf.stalk hpt₁) ≫
      D.lower.i₁.hom.stalkMap (D.f.hom.base x)
  let p₂ : AW ⟶ D.lower.X.presheaf.stalk (D.f.hom.base x) :=
    eqToHom (congrArg D.lower.X₂.presheaf.stalk hpt₂) ≫
      D.lower.i₂.hom.stalkMap (D.f.hom.base x)
  have hψ : ψ ≫ p₁ = p₂ :=
    stalkMap_eqToHom_comp D.lower.i₁ D.lower.f₁₂ D.lower.i₂ D.lower.comm₁₂ (D.f.hom.base x)
      _ _ hpt₁.symm (stalkSquare_point D.comm₁₂ (D.upper.i₁.hom.base x)).symm hpt₂.symm
  have hψ' : ∀ a, p₁.hom (ψ.hom a) = p₂.hom a := fun a =>
    congrArg (fun g : AW ⟶ _ => g.hom a) hψ
  -- the two kernels on the source
  let ε₂ : AZ ⟶ D.upper.X.presheaf.stalk x :=
    eqToHom (congrArg D.upper.X₂.presheaf.stalk hz.symm) ≫ D.upper.i₂.hom.stalkMap x
  have hε : D.upper.f₁₂.hom.stalkMap (D.upper.i₁.hom.base x) ≫ D.upper.i₁.hom.stalkMap x =
      ε₂ := by
    simpa only [eqToHom_refl, Category.id_comp] using stalkMap_eqToHom_comp D.upper.i₁
      D.upper.f₁₂ D.upper.i₂ D.upper.comm₁₂ x (D.upper.i₁.hom.base x) _ rfl rfl hz
  refine isPushout_of_flat_of_sq_eq_bot (RingHom.ker p₁.hom) hJ₁ (RingHom.ker p₂.hom) ?_ ?_
    ε₂.hom (D.upper.i₁.hom.stalkMap x).hom ?_ hε₂ hker₁ hker₂
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker]
    show p₁.hom (ψ.hom a) = 0
    rw [hψ']
    exact ha
  · exact exists_sub_mem_ker_of_comp_surjective _ _ _ (congrArg CommRingCat.Hom.hom hψ) hp₂
  · exact congrArg CommRingCat.Hom.hom hε

/-- **`h^* ℱ'₂` is flat over `S'₁`.** On stalks it is the base change of `ℱ'₂` along
`𝒪_{S'₂} ⟶ 𝒪_{S'₁}`, by `stalkSquareIsPushout₁₂`. -/
theorem isFlatOver_pulledModule :
    AlgebraicGeometry.IsFlatOver D.f₁ ((modulePullback D.upper.f₁₂).obj D.module₂) :=
  isFlatOver_modulePullback_of_stalkSquareIsPushout D.upper.f₁₂ D.lower.f₁₂ D.f₁ D.f₂ D.comm₁₂
    D.stalkSquareIsPushout₁₂ D.module₂ D.module₂_flat

/-- **`ℱ = ℱ'₂|_X` is flat over `S`.** -/
theorem isFlatOver_restriction : AlgebraicGeometry.IsFlatOver D.f D.restriction :=
  isFlatOver_modulePullback_of_isStrict D.morphism₂ D.upper.firstOrder₂ D.lower.firstOrder₂
    D.isStrict₂ D.module₂ D.module₂_flat

/-- The lower row is a complex of first order thickenings. -/
theorem isComplex_lower : IsComplex D.lower :=
  ⟨D.lower_exact.1, D.lower_exact.2.elim fun h _ => h⟩

/-- The canonical splitting `π_S : S'₁ ⟶ S` of the lower row (**Stacks 08LE**). -/
noncomputable def lowerTrivialization : SplitMono D.lower.i₁ where
  retraction :=
    (D.lower.existsUnique_trivialization_of_isComplex D.isComplex_lower).choose
  id := (D.lower.existsUnique_trivialization_of_isComplex D.isComplex_lower).choose_spec.1.1

/-- The canonical splitting of the lower row satisfies `π_S ≫ t₃ = g₁₂ ≫ g₂₃`. -/
theorem lowerTrivialization_retraction_comp :
    D.lowerTrivialization.retraction ≫ D.lower.i₃ = D.lower.f₁₂ ≫ D.lower.f₂₃ :=
  (D.lower.existsUnique_trivialization_of_isComplex D.isComplex_lower).choose_spec.1.2

/-- **The two canonical splittings are compatible with `f`**: `π ≫ f = f'₁ ≫ π_S`. Both sides
become `f₁₂ ≫ f₂₃ ≫ f'₃ = f'₁ ≫ g₁₂ ≫ g₂₃` after composing with the monomorphism `t₃`. -/
theorem trivialization_comp_f :
    D.trivialization.retraction ≫ D.f = D.f₁ ≫ D.lowerTrivialization.retraction := by
  have hmono : Mono D.lower.i₃ := mono_of_isThickening D.lower.i₃ D.lower.firstOrder₃.1
  apply (cancel_mono D.lower.i₃).1
  rw [Category.assoc, ← D.restrict₃, ← Category.assoc, D.trivialization_retraction_comp,
    Category.assoc, Category.assoc, D.lowerTrivialization_retraction_comp,
    D.comm₂₃, ← Category.assoc, D.comm₁₂, Category.assoc]

/-- **The square `(π, π_S)` is a pushout on stalks**: at every point `y` of `X'₁`,
`𝒪_{X'₁,y} = 𝒪_{S'₁,f'₁(y)} ⊗_{𝒪_{S,f(π(y))}} 𝒪_{X,π(y)}`. This is
`isPushout_of_flat_of_sq_eq_bot` for the flat map `f'₁`, the square-zero ideal of `S'₁` and the
zero ideal of `S`: the two splittings make `𝒪_{S'₁} = 𝒪_S + 𝔧₁` and `𝒪_{X'₁} ⟶ 𝒪_X` a retraction
of `π^♯`. -/
theorem stalkSquareIsPushout_trivialization :
    StalkSquareIsPushout D.trivialization.retraction D.lowerTrivialization.retraction D.f₁ D.f
      D.trivialization_comp_f := by
  intro y
  let x := D.trivialization.retraction.hom.base y
  have : IsIso D.upper.i₁.hom.base := D.upper.firstOrder₁.1.1
  have hz : D.upper.i₁.hom.base x = y := by
    obtain ⟨x₀, rfl⟩ : ∃ x₀, D.upper.i₁.hom.base x₀ = y :=
      (TopCat.homeoOfIso (asIso D.upper.i₁.hom.base)).surjective y
    have h : D.trivialization.retraction.hom.base (D.upper.i₁.hom.base x₀) = x₀ :=
      congrArg (fun g : D.upper.X ⟶ D.upper.X => g.hom.base x₀) D.trivialization.id
    exact congrArg D.upper.i₁.hom.base h
  have hpt₁ : D.f₁.hom.base y = D.lower.i₁.hom.base (D.f.hom.base x) := by
    rw [← hz]
    exact stalkSquare_point D.restrict₁ x
  obtain ⟨hp₁, hJ₁, hε₁, hker₁⟩ := stalkMap_facts_of_isStrict D.morphism₁
    D.upper.firstOrder₁ D.lower.firstOrder₁ D.isStrict₁ x y hz hpt₁
  -- the rings and the algebra structures of the stalk square
  let AW := D.lower.X.presheaf.stalk (D.f.hom.base x)
  let AT := D.lower.X₁.presheaf.stalk (D.f₁.hom.base y)
  let AZ := D.upper.X.presheaf.stalk x
  let AY := D.upper.X₁.presheaf.stalk y
  let ψ : AW ⟶ AT := eqToHom (congrArg D.lower.X.presheaf.stalk
    (stalkSquare_point D.trivialization_comp_f y)) ≫
      D.lowerTrivialization.retraction.hom.stalkMap (D.f₁.hom.base y)
  let _iWT : Algebra AW AT := ψ.hom.toAlgebra
  let _iWZ : Algebra AW AZ := (D.f.hom.stalkMap x).hom.toAlgebra
  let _iTY : Algebra AT AY := (D.f₁.hom.stalkMap y).hom.toAlgebra
  let _iZY : Algebra AZ AY := (D.trivialization.retraction.hom.stalkMap y).hom.toAlgebra
  let _iWY : Algebra AW AY :=
    ((D.trivialization.retraction.hom.stalkMap y).hom.comp (D.f.hom.stalkMap x).hom).toAlgebra
  have : IsScalarTower AW AZ AY := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower AW AT AY :=
    IsScalarTower.of_algebraMap_smul fun a b => congrArg (fun r => r * b)
      (congrArg (fun g : AW ⟶ AY => g.hom a)
        (stalkSquare_comm D.trivialization_comp_f y)).symm
  have : Module.Flat AT AY := D.flat₁ y
  -- the kernel on the base, and the splitting
  let p₁ : AT ⟶ AW :=
    eqToHom (congrArg D.lower.X₁.presheaf.stalk hpt₁) ≫
      D.lower.i₁.hom.stalkMap (D.f.hom.base x)
  have hψ : ψ ≫ p₁ = 𝟙 AW :=
    stalkMap_eqToHom_comp_eq_id D.lower.i₁ D.lowerTrivialization.retraction
      D.lowerTrivialization.id (D.f.hom.base x) (D.f₁.hom.base y) hpt₁.symm
      (stalkSquare_point D.trivialization_comp_f y).symm
  -- the retraction on the source
  let ε₁ : AY ⟶ AZ := eqToHom (congrArg D.upper.X₁.presheaf.stalk hz.symm) ≫
    D.upper.i₁.hom.stalkMap x
  have hε : D.trivialization.retraction.hom.stalkMap y ≫ ε₁ = 𝟙 AZ := by
    simpa only [eqToHom_refl, Category.id_comp] using
      stalkMap_eqToHom_comp_eq_id D.upper.i₁ D.trivialization.retraction D.trivialization.id x y hz
        rfl
  refine isPushout_of_flat_of_sq_eq_bot (RingHom.ker p₁.hom) hJ₁ ⊥ (by simp) ?_
    (RingHom.id AZ) ε₁.hom ?_ Function.surjective_id hker₁ ?_
  · exact exists_sub_mem_ker_of_comp_surjective _ _ _ (congrArg CommRingCat.Hom.hom hψ)
      Function.surjective_id
  · exact congrArg CommRingCat.Hom.hom hε
  · rw [Ideal.map_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).1 Function.injective_id

/-- **`π^* ℱ` is flat over `S'₁`.** On stalks it is the base change of `ℱ` along
`𝒪_S ⟶ 𝒪_{S'₁}`, by `stalkSquareIsPushout_trivialization`. -/
theorem isFlatOver_trivialModule :
    AlgebraicGeometry.IsFlatOver D.f₁ ((modulePullback D.trivialization.retraction).obj
      D.restriction) :=
  isFlatOver_modulePullback_of_stalkSquareIsPushout D.trivialization.retraction
    D.lowerTrivialization.retraction D.f₁ D.f D.trivialization_comp_f
    D.stalkSquareIsPushout_trivialization D.restriction D.isFlatOver_restriction

/-- **`π^* ℱ`**, the pullback of `ℱ` along the canonical splitting `π : X'₁ ⟶ X`, as an
`𝒪'₁`-module flat over `S'₁` restricting to `ℱ` on `X`: the restriction is
`i₁^* π^* ℱ ≅ (i₁ ≫ π)^* ℱ = 𝟙^* ℱ ≅ ℱ`. -/
noncomputable def trivialLift : FlatLift D.morphism₁ D.restriction where
  module' := (modulePullback D.trivialization.retraction).obj D.restriction
  flat := D.isFlatOver_trivialModule
  identification := (modulePullbackComp D.upper.i₁ D.trivialization.retraction).symm.app
      D.restriction ≪≫ (modulePullbackCongr D.trivialization.id).app D.restriction ≪≫
    (modulePullbackId D.upper.X).app D.restriction

/-- **`h^* ℱ'₂`**, the pullback of `ℱ'₂` along `h : X'₁ ⟶ X'₂`, as an `𝒪'₁`-module flat over
`S'₁` restricting to `ℱ` on `X`: the restriction is `i₁^* h^* ℱ'₂ ≅ (i₁ ≫ h)^* ℱ'₂ = i₂^* ℱ'₂`. -/
noncomputable def pulledLift : FlatLift D.morphism₁ D.restriction where
  module' := (modulePullback D.upper.f₁₂).obj D.module₂
  flat := D.isFlatOver_pulledModule
  identification := (modulePullbackComp D.upper.i₁ D.upper.f₁₂).symm.app D.module₂ ≪≫
    (modulePullbackCongr D.upper.comm₁₂).app D.module₂

/-- **The class `ξ` of `π^* ℱ` vanishes.** Read along the canonical splitting `π`, the kernel
extension of `π^* ℱ` is split by the unit `ℱ ⟶ π_* π^* ℱ`. -/
theorem underlyingExtensionClass_trivialLift
    [CategoryTheory.HasExt.{w} (SheafOfModules.{u} (structureSheafRing D.upper.X))] :
    underlyingExtensionClass D.upper.i₁ D.trivialization D.upper.firstOrder₁.1.1 D.restriction
      (idealTensor D.morphism₁ D.restriction)
      (D.trivialLift.kernelExtension D.upper.firstOrder₁ D.isStrict₁) = 0 :=
  (CategoryTheory.Abelian.extClass_eq_zero_iff_exists_section
    (splitExtension_shortExact D.upper.i₁ D.trivialization D.upper.firstOrder₁.1.1
      D.restriction (idealTensor D.morphism₁ D.restriction)
      (D.trivialLift.kernelExtension D.upper.firstOrder₁ D.isStrict₁))).2
    ⟨(modulePullbackPushforwardAdjunction D.trivialization.retraction).unit.app D.restriction,
      unit_comp_splitRestriction_reduction D.upper.i₁ D.trivialization D.restriction⟩

/-- **The map of extensions from `ℱ'₂` to `h^* ℱ'₂`.** The unit `ℱ'₂ ⟶ h_* h^* ℱ'₂` is the
identity on `ℱ` and the map `ℐ₂ ⊗ ℱ ⟶ ℐ₁ ⊗ ℱ` on kernel modules: this is how the source's
`h^* ℱ'₂` is the extension that **Stacks 08LC** produces from `ℱ'₂`. The map on kernels is
forced by the canonical maps of **Stacks 08L4** (**Stacks 08L5**): that of `ℱ'₂` is `1`, and
that of `h^* ℱ'₂` read over `X'₂` is `ℐ₂ ⊗ ℱ ⟶ ℐ₁ ⊗ ℱ`
(`firstOrderExtensionAction_restrictedExtension`). -/
noncomputable def pushedExtension :
    PushedExtension D.upper.i₁ D.upper.i₂ D.upper.f₁₂ D.upper.comm₁₂ D.restriction
      (idealTensor D.morphism₁ D.restriction) (idealTensor D.morphism₂ D.restriction)
      D.idealTensorTransition₂₁
      (D.liftOfModule₂.kernelExtension D.upper.firstOrder₂ D.isStrict₂)
      (D.pulledLift.kernelExtension D.upper.firstOrder₁ D.isStrict₁) := by
  have hg : (D.liftOfModule₂.kernelExtension D.upper.firstOrder₂ D.isStrict₂).g =
      (modulePullbackPushforwardAdjunction D.upper.i₂).unit.app D.module₂ := by
    change (modulePullbackPushforwardAdjunction D.upper.i₂).unit.app D.module₂ ≫
      (modulePushforward D.upper.i₂).map (Iso.refl _).hom = _
    simp
  have hq : (modulePullbackPushforwardAdjunction D.upper.f₁₂).unit.app D.module₂ ≫
      (modulePushforward D.upper.f₁₂).map
        (D.pulledLift.kernelExtension D.upper.firstOrder₁ D.isStrict₁).g =
      (D.liftOfModule₂.kernelExtension D.upper.firstOrder₂ D.isStrict₂).g ≫
        (thickeningPushforwardComp D.upper.i₁ D.upper.i₂ D.upper.f₁₂
          D.upper.comm₁₂).inv.app D.restriction := by
    rw [hg]
    exact unit_comp_pushforward_unit_thickening D.upper.i₁ D.upper.i₂ D.upper.f₁₂
      D.upper.comm₁₂ D.module₂
  refine { hom := (modulePullbackPushforwardAdjunction D.upper.f₁₂).unit.app D.module₂
           kernel_commutes := ?_
           quotient_commutes := hq }
  have hb : IsIso D.upper.f₁₂.hom.base := isIso_base_of_thickeningMap D.upper.i₁ D.upper.i₂
    D.upper.f₁₂ D.upper.comm₁₂ D.upper.firstOrder₁.1.1 D.upper.firstOrder₂.1.1
  let E₂ := D.liftOfModule₂.kernelExtension D.upper.firstOrder₂ D.isStrict₂
  let E₁ := D.pulledLift.kernelExtension D.upper.firstOrder₁ D.isStrict₁
  let E' := restrictedExtension D.upper.i₁ D.upper.i₂ D.upper.f₁₂ D.upper.comm₁₂ D.restriction
    (idealTensor D.morphism₁ D.restriction) E₁ hb
  let u : E₂.Z.left ⟶ E'.Z.left :=
    (modulePullbackPushforwardAdjunction D.upper.f₁₂).unit.app D.module₂
  have hug : u ≫ E'.g = E₂.g ≫ (modulePushforward D.upper.i₂).map (𝟙 D.restriction) := by
    calc u ≫ E'.g = (u ≫ (modulePushforward D.upper.f₁₂).map E₁.g) ≫
          (thickeningPushforwardComp D.upper.i₁ D.upper.i₂ D.upper.f₁₂
            D.upper.comm₁₂).hom.app D.restriction := (Category.assoc _ _ _).symm
      _ = (E₂.g ≫ (thickeningPushforwardComp D.upper.i₁ D.upper.i₂ D.upper.f₁₂
            D.upper.comm₁₂).inv.app D.restriction) ≫
          (thickeningPushforwardComp D.upper.i₁ D.upper.i₂ D.upper.f₁₂
            D.upper.comm₁₂).hom.app D.restriction := congrArg (· ≫ _) hq
      _ = E₂.g ≫ (modulePushforward D.upper.i₂).map (𝟙 D.restriction) := by
        rw [Category.assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  have h0 : (E₂.f ≫ u) ≫ E'.g = 0 := by
    rw [Category.assoc, hug, ← Category.assoc,
      CategoryTheory.Abelian.YonedaExtension.comp_eq_zero E₂, zero_comp]
  let hker := (CategoryTheory.Abelian.YonedaExtension.shortExact E').fIsKernel
  let l := hker.lift (KernelFork.ofι (E₂.f ≫ u) h0)
  have hl : l ≫ E'.f = E₂.f ≫ u := hker.fac _ WalkingParallelPair.zero
  have : (modulePushforward D.upper.i₂).Full :=
    (closedQuotientOfIsThickening D.upper.i₂ D.upper.firstOrder₂.1).full_modulePushforward
  let κ := (modulePushforward D.upper.i₂).preimage l
  have hκ : (modulePushforward D.upper.i₂).map κ = l := Functor.map_preimage _ _
  let S : ExtensionPair.{u} :=
    { X := D.upper.X, X' := D.upper.X₂, i := D.upper.i₂, firstOrder := D.upper.firstOrder₂,
      F := D.restriction, K := idealTensor D.morphism₂ D.restriction, G := D.restriction,
      L := idealTensor D.morphism₁ D.restriction, firstExtension := E₂, secondExtension := E',
      quotientMap := 𝟙 D.restriction, kernelMap := κ }
  let c : S.CompatibleMap :=
    { hom := u
      kernel_commutes := by
        change E₂.f ≫ u = (modulePushforward D.upper.i₂).map κ ≫ E'.f
        rw [hκ, hl]
      quotient_commutes := hug }
  have hnat := ExtensionPair.extensionAction_naturality S c
  have h1 : (firstOrderExtensionAction D.upper.i₂ D.restriction
      (idealTensor D.morphism₁ D.restriction) D.upper.firstOrder₂ E').val =
      D.idealTensorTransition₂₁ := by
    rw [firstOrderExtensionAction_restrictedExtension D.upper.i₁ D.upper.i₂ D.upper.f₁₂
      D.upper.comm₁₂ D.upper.firstOrder₁ D.upper.firstOrder₂ D.restriction
      (idealTensor D.morphism₁ D.restriction) E₁ hb,
      FlatLift.kernelExtension_action D.upper.firstOrder₁ D.isStrict₁ D.pulledLift]
    exact Category.comp_id _
  change (firstOrderExtensionAction D.upper.i₂ D.restriction
      (idealTensor D.morphism₂ D.restriction) D.upper.firstOrder₂ E₂).val ≫ κ =
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨D.upper.X.presheaf, D.upper.X.IsSheaf⟩)).map
        (((𝟙 (idealSheafPullback D.upper.i₂)), 𝟙 D.restriction) : (_, _) ⟶ (_, _))) ≫
      (firstOrderExtensionAction D.upper.i₂ D.restriction
        (idealTensor D.morphism₁ D.restriction) D.upper.firstOrder₂ E').val at hnat
  rw [FlatLift.kernelExtension_action D.upper.firstOrder₂ D.isStrict₂ D.liftOfModule₂, h1] at hnat
  have hκtr : κ = D.idealTensorTransition₂₁ :=
    (Category.id_comp κ).symm.trans (hnat.trans ((congrArg (· ≫ D.idealTensorTransition₂₁)
      (tensorSheafMap_id_id _ _ _)).trans (Category.id_comp _)))
  change E₂.f ≫ u = _
  rw [← hl, ← hκ, hκtr]
  rfl

/-! ### The sequence `0 ⟶ f^* 𝒥₃ ⊗ ℱ ⟶ f^* 𝒥₂ ⊗ ℱ ⟶ f^* 𝒥₁ ⊗ ℱ ⟶ 0` -/

/-- The map `f^* 𝒥₃ ⊗_{𝒪_X} ℱ ⟶ f^* 𝒥₂ ⊗_{𝒪_X} ℱ` induced by `𝒥₃ ⟶ 𝒥₂`. -/
noncomputable abbrev baseTransition₃₂ :
    baseIdealTensor D.morphism₃ D.restriction ⟶ baseIdealTensor D.morphism₂ D.restriction :=
  (Stacks.SheafOfModules.pullbackTensorFunctor D.f D.restriction).map D.lower.idealMap₃₂

/-- The map `f^* 𝒥₂ ⊗_{𝒪_X} ℱ ⟶ f^* 𝒥₁ ⊗_{𝒪_X} ℱ` induced by `𝒥₂ ⟶ 𝒥₁`. -/
noncomputable abbrev baseTransition₂₁ :
    baseIdealTensor D.morphism₂ D.restriction ⟶ baseIdealTensor D.morphism₁ D.restriction :=
  (Stacks.SheafOfModules.pullbackTensorFunctor D.f D.restriction).map D.lower.idealMap₂₁

/-- The composite `f^* 𝒥₃ ⊗_{𝒪_X} ℱ ⟶ f^* 𝒥₂ ⊗_{𝒪_X} ℱ ⟶ f^* 𝒥₁ ⊗_{𝒪_X} ℱ` is zero. -/
theorem baseTransition_comp : D.baseTransition₃₂ ≫ D.baseTransition₂₁ = 0 := by
  obtain ⟨hz, -⟩ := D.lower_exact.2
  have := Stacks.SheafOfModules.preservesZeroMorphisms_pullbackTensorFunctor D.f D.restriction
  exact (Functor.map_comp _ _ _).symm.trans ((congrArg _ hz).trans (Functor.map_zero _ _ _))

/-- **The sequence `0 ⟶ f^* 𝒥₃ ⊗ ℱ ⟶ f^* 𝒥₂ ⊗ ℱ ⟶ f^* 𝒥₁ ⊗ ℱ ⟶ 0` is short exact**: the lower row
is short exact and `𝒢 ↦ f^* 𝒢 ⊗_{𝒪_X} ℱ` is exact because `ℱ` is flat over `S`
(**Stacks 0GMU**). -/
theorem baseTransition_shortExact :
    (ShortComplex.mk D.baseTransition₃₂ D.baseTransition₂₁ D.baseTransition_comp).ShortExact := by
  obtain ⟨hz, hS⟩ := D.lower_exact.2
  have hex := Stacks.SheafOfModules.pullbackTensorFunctor_exact D.f D.restriction
    D.isFlatOver_restriction
  have : Limits.PreservesFiniteLimits
      (Stacks.SheafOfModules.pullbackTensorFunctor D.f D.restriction) := hex.1
  have : Limits.PreservesFiniteColimits
      (Stacks.SheafOfModules.pullbackTensorFunctor D.f D.restriction) := hex.2
  exact hS.map_of_exact _

/-- `𝒢 ↦ f^* 𝒢 ⊗_{𝒪_X} ℱ` on a morphism is the tensor product of its pullback with `𝟙 ℱ`. -/
theorem pullbackTensorFunctor_map_eq {G G' : SheafOfModules.{u} (structureSheafRing D.lower.X)}
    (φ : G ⟶ G') :
    (Stacks.SheafOfModules.pullbackTensorFunctor D.f D.restriction).map φ =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((D.upper.X)).presheaf, ((D.upper.X)).IsSheaf⟩)).map
          ((((modulePullback D.f).map φ), (𝟙 D.restriction)) : (_, _) ⟶ (_, _)) :=
  (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map
    ⟨((D.upper.X)).presheaf, ((D.upper.X)).IsSheaf⟩
    ((modulePullback D.f).map φ) (𝟙 D.restriction)).symm

/-- Tensoring with `𝟙 ℱ` preserves composition. -/
theorem tensor_map_comp_id {A B C : SheafOfModules.{u} (structureSheafRing D.upper.X)}
    (a : A ⟶ B) (b : B ⟶ C) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((D.upper.X)).presheaf, ((D.upper.X)).IsSheaf⟩)).map
          (((a ≫ b), (𝟙 D.restriction)) : (_, _) ⟶ (_, _)) =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((D.upper.X)).presheaf, ((D.upper.X)).IsSheaf⟩)).map
          ((a, (𝟙 D.restriction)) : (_, _) ⟶ (_, _)) ≫
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((D.upper.X)).presheaf, ((D.upper.X)).IsSheaf⟩)).map
          ((b, (𝟙 D.restriction)) : (_, _) ⟶ (_, _)) :=
  (congrArg (fun z => (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((D.upper.X)).presheaf, ((D.upper.X)).IsSheaf⟩)).map
          (((a ≫ b), z) : (A, D.restriction) ⟶ (C, D.restriction)))
    (Category.id_comp (𝟙 D.restriction)).symm).trans
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((D.upper.X)).presheaf, ((D.upper.X)).IsSheaf⟩)).map_comp
      ((a, 𝟙 D.restriction) : (A, D.restriction) ⟶ (B, D.restriction))
      ((b, 𝟙 D.restriction) : (B, D.restriction) ⟶ (C, D.restriction)))

/-- **The ideal maps of the two rows are compatible on the right square.** -/
theorem baseToSourceIdeal_transition₃₂ :
    (modulePullback D.f).map D.lower.idealMap₃₂ ≫ D.morphism₂.baseToSourceIdeal =
      D.morphism₃.baseToSourceIdeal ≫
        thickeningIdealMap D.upper.i₂ D.upper.i₃ D.upper.f₂₃ D.upper.comm₂₃ := by
  rw [← FirstOrderThickeningSequence.thickeningIdealMap_eq_idealMap₃₂ D.lower D.lower_exact.1]
  exact baseToSourceIdeal_comp_thickeningIdealMap D.upper.i₂ D.lower.i₂ D.f D.f₂ D.upper.i₃
    D.lower.i₃ D.f₃ D.upper.f₂₃ D.lower.f₂₃ D.upper.firstOrder₂ D.lower.firstOrder₂
    D.upper.firstOrder₃.1 D.lower.firstOrder₃.1 D.restrict₂ D.restrict₃ D.upper.comm₂₃
    D.lower.comm₂₃ D.comm₂₃

/-- **The ideal maps of the two rows are compatible on the left square.** -/
theorem baseToSourceIdeal_transition₂₁ :
    (modulePullback D.f).map D.lower.idealMap₂₁ ≫ D.morphism₁.baseToSourceIdeal =
      D.morphism₂.baseToSourceIdeal ≫
        thickeningIdealMap D.upper.i₁ D.upper.i₂ D.upper.f₁₂ D.upper.comm₁₂ := by
  rw [← FirstOrderThickeningSequence.thickeningIdealMap_eq_idealMap₂₁ D.lower D.lower_exact.1]
  exact baseToSourceIdeal_comp_thickeningIdealMap D.upper.i₁ D.lower.i₁ D.f D.f₁ D.upper.i₂
    D.lower.i₂ D.f₂ D.upper.f₁₂ D.lower.f₁₂ D.upper.firstOrder₁ D.lower.firstOrder₁
    D.upper.firstOrder₂.1 D.lower.firstOrder₂.1 D.restrict₁ D.restrict₂ D.upper.comm₁₂
    D.lower.comm₁₂ D.comm₁₂

end FlatShortExactThickeningDiagram

end AlgebraicGeometry.RingedSpaceThickening
