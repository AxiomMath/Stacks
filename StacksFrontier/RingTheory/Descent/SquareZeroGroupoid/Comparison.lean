module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
public import StacksFrontier.RingTheory.Descent.AmitsurComplex
public import StacksFrontier.RingTheory.Descent.EqualizerDescent
public import StacksFrontier.RingTheory.Descent.PushoutBaseChange
public import StacksFrontier.RingTheory.Etale.AffineStageCore
public import StacksFrontier.RingTheory.Flat.Nilpotent
public import StacksFrontier.RingTheory.Flat.TorCriterion

/-!
# Groupoids of rings and the comparisons over a square-zero ideal

A *groupoid of rings* here is a pair of ring maps `s, t : B → C`, with `t = algebraMap B C`
flat, together with a unit `e : C → B` (`e ∘ s = e ∘ t = id`) and a composition
`m : C → C ⊗[B] D` (`m ∘ s = s ⊗ 1`, `m ∘ t = 1 ⊗ σ ∘ t`), where `σ : C ≃+* D` is a copy of
`C` whose `B`-algebra structure is that of `s`. It is *effective* when it is the Čech groupoid of
a faithfully flat ring map: some `A → B` is faithfully flat, `s` and `t` agree on `A`, and
`B ⊗[A] B → C`, `x ⊗ y ↦ t x * s y`, is bijective.

This file sets up the deformation of an effective flat groupoid along a nilpotent invariant
ideal (the ring-level content of the proof of Stacks 05ZR). It defines effectiveness and the
reduction `s₀ : B ⧸ J → C ⧸ J C` of `s` along an ideal `J` whose two extensions to `C` agree, and,
for `J` of square zero, constructs the identifications `C₀ ⊗[B₀] J ≅ J C` and `B₀ ⊗[A₀] J ≅ J C`
given by flatness of `t`.

## Main definitions

* `Module.Descent.SquareZero.IsEffective`: effectiveness of a groupoid of rings.
* `Module.Descent.SquareZero.cmp`: the comparison `B ⊗[A] B → C`.

## Main results

* `Module.Descent.SquareZero.IsEffective.of_ringEquiv`: effectiveness is invariant under
  isomorphism.
* `Module.Descent.SquareZero.κ_bijective`: the comparison `C₀ ⊗[B₀] J ≅ J C`.
* `Module.Descent.SquareZero.α_bijective`: the comparison `B₀ ⊗[A₀] J ≅ J C` over the reduced
  equalizer.

## Implementation notes

The second `B`-algebra structure on `C` is carried by the separate ring `D` with the ring
isomorphism `σ : C ≃+* D`, because one type cannot carry two `Algebra B` instances.

## References

* [Stacks Project, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR)
* [Stacks Project, Tag 05ZQ](https://stacks.math.columbia.edu/tag/05ZQ)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 051C](https://stacks.math.columbia.edu/tag/051C)
-/

@[expose] public section

open TensorProduct

universe u

namespace Module.Descent.SquareZero

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]

variable (s : B →+* C) (J : Ideal B)

/-- The extension of `J` along `t = algebraMap B C`. -/
abbrev extJ (C : Type u) [CommRing C] [Algebra B C] (J : Ideal B) : Ideal C :=
  J.map (algebraMap B C)

/-- The reduction `s₀ : B/J → C/JC` of `s`, defined when the two extensions of `J` agree. -/
def s₀ (hinv : J.map s = extJ C J) : B ⧸ J →+* C ⧸ extJ C J :=
  Ideal.quotientMap (extJ C J) s (Ideal.map_le_iff_le_comap.mp hinv.le)

/-- `s₀` sends the class of `b` to the class of `s b`. -/
lemma s₀_mk (hinv : J.map s = extJ C J) (b : B) :
    s₀ s J hinv (Ideal.Quotient.mk J b) = Ideal.Quotient.mk (extJ C J) (s b) :=
  Ideal.quotientMap_mk

/-- The reduction `t₀ : B ⧸ J → C ⧸ J C` of `t` sends the class of `b` to the class of `t b`. -/
lemma t₀_mk (b : B) :
    algebraMap (B ⧸ J) (C ⧸ extJ C J) (Ideal.Quotient.mk J b) =
      Ideal.Quotient.mk (extJ C J) (algebraMap B C b) :=
  Ideal.Quotient.algebraMap_quotient_map_quotient b

/-- The comparison `B ⊗[A] P → C`, `a ⊗ b ↦ t a * σ b`, for ring maps `A → B`, `A → P` and
`σ : P → C` over which `σ` and `t = algebraMap B C` agree. -/
def cmpP {A P : Type*} [CommRing A] [CommRing P] [Algebra A B] [Algebra A P] (σ : P →+* C)
    (h : ∀ a : A, σ (algebraMap A P a) = algebraMap B C (algebraMap A B a)) :
    B ⊗[A] P →+ C :=
  TensorProduct.liftAddHom
    ((AddMonoidHom.mul.comp (algebraMap B C).toAddMonoidHom).compl₂ σ.toAddMonoidHom)
    (fun a x y => by
      simp only [AddMonoidHom.compl₂_apply, AddMonoidHom.coe_comp, Function.comp_apply,
        AddMonoidHom.mul_apply, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass,
        Algebra.smul_def, map_mul, h]
      ring)

/-- `cmpP σ h (x ⊗ y) = t x * σ y`. -/
lemma cmpP_tmul {A P : Type*} [CommRing A] [CommRing P] [Algebra A B] [Algebra A P]
    (σ : P →+* C) (h : ∀ a : A, σ (algebraMap A P a) = algebraMap B C (algebraMap A B a))
    (x : B) (y : P) : cmpP σ h (x ⊗ₜ y) = algebraMap B C x * σ y := rfl

/-- The comparison `B ⊗[A] B → C`, `a ⊗ b ↦ t a * s b`, for a ring `A` over which `s` and `t`
agree. -/
abbrev cmp (A : Type*) [CommRing A] [Algebra A B]
    (h : ∀ a : A, s (algebraMap A B a) = algebraMap B C (algebraMap A B a)) :
    B ⊗[A] B →+ C :=
  cmpP s h

/-- `cmp s A h (x ⊗ y) = t x * s y`. -/
lemma cmp_tmul (A : Type*) [CommRing A] [Algebra A B]
    (h : ∀ a : A, s (algebraMap A B a) = algebraMap B C (algebraMap A B a)) (x y : B) :
    cmp s A h (x ⊗ₜ y) = algebraMap B C x * s y := rfl

/-- The groupoid `s, t : B ⇉ C` is *effective* when it is the Čech groupoid of a faithfully flat
ring map `A → B`: `s` and `t` agree on `A` and the comparison `B ⊗[A] B → C` is bijective. -/
def IsEffective : Prop :=
  ∃ (A : Type u) (_ : CommRing A) (_ : Algebra A B)
    (h : ∀ a : A, s (algebraMap A B a) = algebraMap B C (algebraMap A B a)),
    Module.FaithfullyFlat A B ∧ Function.Bijective (cmp s A h)

/-- The equalizer `A` of `s` and `t`. -/
def eqLocus : Subring B := RingHom.eqLocus s (algebraMap B C)

/-! ### A comparison across a pushout square -/

section Pushout

variable {R A B' D' : Type*} [CommRing R] [CommRing A] [CommRing B'] [CommRing D']
  [Algebra R A] [Algebra R B'] [Algebra R D'] [Algebra A D'] [Algebra B' D'] [IsScalarTower R A D']

/-- **A comparison map out of `B' ⊗[R] M` across a pushout square of rings is injective whenever
the base change comparison over `A → D'` is.** The injective companion of
`Module.Descent.bijective_pushout_comparison`, with the same proof. -/
theorem injective_pushout_comparison (e : A ⊗[R] B' ≃ₗ[R] D')
    (he : ∀ (a : A) (b : B'), e (a ⊗ₜ b) = algebraMap A D' a * algebraMap B' D' b)
    {M : Type*} [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
    {N : Type*} [AddCommGroup N] [Module D' N] [Module R N] [IsScalarTower R D' N]
    (κ : D' ⊗[A] M →ₗ[D'] N) (hκ : Function.Injective κ)
    (ξ : B' ⊗[R] M →ₗ[R] N)
    (hξ : ∀ (b : B') (x : M), ξ (b ⊗ₜ x) = algebraMap B' D' b • κ (1 ⊗ₜ x)) :
    Function.Injective ξ := by
  have key : ∀ z : B' ⊗[R] M, ξ z = κ (pushoutBaseChangeEquiv e he z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul b x =>
        have hsm : (algebraMap B' D' b) • ((1 : D') ⊗ₜ[A] x) = (algebraMap B' D' b) ⊗ₜ[A] x := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [hξ b x, pushoutBaseChangeEquiv_tmul, ← hsm, κ.map_smul]
    | add z w hz hw => simp [hz, hw]
  have hfun : (ξ : B' ⊗[R] M → N) = (κ : D' ⊗[A] M → N) ∘ (pushoutBaseChangeEquiv e he) :=
    funext key
  rw [hfun]
  exact hκ.comp (pushoutBaseChangeEquiv e he).injective

end Pushout

/-! ### Transport of effectiveness along isomorphisms -/

/-- **Effectiveness is invariant under isomorphism of groupoids.** -/
theorem IsEffective.of_ringEquiv {B' C' : Type u} [CommRing B'] [CommRing C'] [Algebra B' C']
    {s' : B' →+* C'} (eB : B ≃+* B') (eC : C ≃+* C')
    (heC : ∀ b, eC (algebraMap B C b) = algebraMap B' C' (eB b)) (hs : ∀ b, eC (s b) = s' (eB b))
    (h : IsEffective s) : IsEffective s' := by
  obtain ⟨A, _, _, hA, hff, hbij⟩ := h
  let : Algebra A B' := (eB.toRingHom.comp (algebraMap A B)).toAlgebra
  have hA' : ∀ a : A, s' (algebraMap A B' a) = algebraMap B' C' (algebraMap A B' a) := by
    intro a
    change s' (eB (algebraMap A B a)) = algebraMap B' C' (eB (algebraMap A B a))
    rw [← hs, ← heC, hA]
  let eL : B ≃ₗ[A] B' :=
    { eB with
      map_smul' := fun a b => by
        change eB (a • b) = eB (algebraMap A B a) * eB b
        rw [Algebra.smul_def, map_mul] }
  have : Module.FaithfullyFlat A B' := Module.FaithfullyFlat.of_linearEquiv A B eL.symm
  refine ⟨A, inferInstance, inferInstance, hA', inferInstance, ?_⟩
  have key : ∀ z : B ⊗[A] B, cmp s' A hA' (TensorProduct.congr eL eL z) = eC (cmp s A hA z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
    | tmul x y =>
      rw [TensorProduct.congr_tmul, cmp_tmul, cmp_tmul, map_mul, heC, hs]
      rfl
  have hfun : (cmp s' A hA' : B' ⊗[A] B' → C') =
      eC ∘ (cmp s A hA) ∘ (TensorProduct.congr eL eL).symm := by
    funext z
    simp only [Function.comp_apply]
    rw [← key, LinearEquiv.apply_symm_apply]
  rw [hfun]
  exact eC.bijective.comp (hbij.comp (TensorProduct.congr eL eL).symm.bijective)

/-! ### Degree-zero descent -/

section DegreeZero

variable {A : Type*} [CommRing A] [Algebra A B]
  (h : ∀ a : A, s (algebraMap A B a) = algebraMap B C (algebraMap A B a))

/-- For an effective groupoid, the elements of `B` on which `s` and `t` agree are the image
of `A`. -/
lemma mem_range_of_eq [Module.FaithfullyFlat A B] (hbij : Function.Bijective (cmp s A h))
    {b : B} (hb : s b = algebraMap B C b) : b ∈ Set.range (algebraMap A B) := by
  have heff := Algebra.IsEffective.of_faithfullyFlat A B
  refine (heff b).mp ?_
  rw [Algebra.TensorProduct.includeLeftSubRight_apply, sub_eq_zero]
  apply hbij.1
  rw [cmp_tmul, cmp_tmul, map_one, map_one, one_mul, mul_one, hb]

end DegreeZero

/-! ### Flatness over a square-zero thickening -/

/-- **The local criterion of flatness for a square-zero ideal** (Stacks 051C): if `M ⧸ I M` is
flat over `R ⧸ I` and `I ⊗[R] M → M` is injective, then `M` is flat over `R`. -/
theorem flat_of_sq_eq_bot {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (hI : I ^ 2 = ⊥) (h1 : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))))
    (h2 : Function.Injective (I.subtype.rTensor M)) : Module.Flat R M :=
  flat_of_nilpotent I h1
    (tor1_vanishes_of_shortExact_rTensor_injective I.subtype I.mkQ Subtype.val_injective
      I.mkQ_surjective (by rw [LinearMap.exact_iff]; simp)
      (Tor_iso_Tor'.tor_flat_isZero R (ModuleCat.of R R) (ModuleCat.of R M) 0) h2)
    ⟨2, by norm_num, hI⟩

/-! ### Square-zero ideals as modules over the quotient -/

/-- If `I ^ 2 = ⊥`, the product of two elements of `I` vanishes. -/
private theorem mul_eq_zero_of_sq_eq_bot {R : Type*} [CommRing R] {I : Ideal R} (hI : I ^ 2 = ⊥)
    {x y : R} (hx : x ∈ I) (hy : y ∈ I) : x * y = 0 := by
  rw [← Ideal.mem_bot, ← hI, pow_two]
  exact Ideal.mul_mem_mul hx hy

section SquareZeroModule

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- An ideal `I` with `I ^ 2 = ⊥` is annihilated by `I` as an `R`-module. -/
lemma isTorsionBySet_of_sq (hI : I ^ 2 = ⊥) : Module.IsTorsionBySet R I I := by
  intro x a
  apply Subtype.ext
  simpa [mul_comm] using mul_eq_zero_of_sq_eq_bot hI a.2 x.2

/-- A square-zero ideal is a module over the quotient by itself. -/
noncomputable abbrev quotModule (hI : I ^ 2 = ⊥) : Module (R ⧸ I) I :=
  (isTorsionBySet_of_sq I hI).module

/-- The class of `r` in `R ⧸ I` acts on a square-zero ideal `I` as `r`. -/
lemma quotModule_mk_smul (hI : I ^ 2 = ⊥) (r : R) (x : I) :
    letI := quotModule I hI
    (Ideal.Quotient.mk I r • x : I) = r • x :=
  Module.IsTorsionBySet.mk_smul _ r x

end SquareZeroModule

/-! ### Reducing a base change modulo the ideal -/

section Reduce

variable (C) {M : Type*} [AddCommGroup M] [Module B M] [Module (B ⧸ J) M]
  [IsScalarTower B (B ⧸ J) M]

omit [Algebra B C] in
/-- The class of `b` in `B ⧸ J` acts on `M` as `b`. -/
lemma mk_smul_of_tower (b : B) (m : M) : (Ideal.Quotient.mk J b • m : M) = b • m := by
  rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul]

omit [Module B M] [Module (B ⧸ J) M] [IsScalarTower B (B ⧸ J) M] in
/-- The class of `b` in `B ⧸ J` acts on `C ⧸ J C` as `b`. -/
lemma quot_smul_C₀ (b : B) (y : C ⧸ extJ C J) : (Ideal.Quotient.mk J b) • y = b • y := by
  rw [Algebra.smul_def, Algebra.smul_def, t₀_mk]
  rfl

/-- The reduction `C ⊗[B] M → C₀ ⊗[B₀] M` of a base change modulo `J`. -/
noncomputable def reduceTensor : C ⊗[B] M →ₗ[B] (C ⧸ extJ C J) ⊗[B ⧸ J] M :=
  TensorProduct.lift
    { toFun := fun c => ((TensorProduct.mk (B ⧸ J) (C ⧸ extJ C J) M
          (Ideal.Quotient.mk (extJ C J) c)).restrictScalars B)
      map_add' := fun x y => by ext; simp
      map_smul' := fun b x => by
        ext j
        simp only [LinearMap.restrictScalars_apply, TensorProduct.mk_apply, RingHom.id_apply,
          LinearMap.smul_apply]
        rw [TensorProduct.smul_tmul']
        rfl }

/-- `reduceTensor` sends `c ⊗ m` to `c̄ ⊗ m`. -/
lemma reduceTensor_tmul (c : C) (m : M) :
    reduceTensor C J (c ⊗ₜ m) = Ideal.Quotient.mk (extJ C J) c ⊗ₜ m := rfl

/-- The reduction `C ⊗[B] M → C₀ ⊗[B₀] M` is surjective. -/
lemma reduceTensor_surjective : Function.Surjective (reduceTensor C J (M := M)) := by
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul c j =>
    obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
    exact ⟨c' ⊗ₜ j, rfl⟩
  | add x y hx hy =>
    obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hy
    exact ⟨x' + y', map_add _ _ _⟩

variable {N : Type*} [AddCommGroup N] [Module C N] [Module (C ⧸ extJ C J) N]
  [IsScalarTower C (C ⧸ extJ C J) N] [Module B N] [IsScalarTower B C N]
  [Module (B ⧸ J) N] [IsScalarTower (B ⧸ J) (C ⧸ extJ C J) N] [IsScalarTower B (B ⧸ J) N]

omit [Module B N] [IsScalarTower B C N] [Module (B ⧸ J) N] [IsScalarTower (B ⧸ J) (C ⧸ extJ C J) N]
  [IsScalarTower B (B ⧸ J) N] in
/-- The class of `c` in `C ⧸ J C` acts on `N` as `c`. -/
lemma mk_smul_of_towerC (c : C) (n : N) :
    (Ideal.Quotient.mk (extJ C J) c • n : N) = c • n := by
  rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul]

/-- The base change of `ℓ` to `C₀`, composed with `reduceTensor`, is the base change of `ℓ`
to `C`. -/
lemma liftBaseChange_reduceTensor (ℓ : M →ₗ[B ⧸ J] N) (z : C ⊗[B] M) :
    LinearMap.liftBaseChange (C ⧸ extJ C J) ℓ (reduceTensor C J z) =
      LinearMap.liftBaseChange C (ℓ.restrictScalars B) z := by
  induction z using TensorProduct.inductionOn with
  | tmul c m =>
    rw [reduceTensor_tmul, LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul,
      mk_smul_of_towerC]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- A comparison out of `C₀ ⊗[B₀] M` is injective as soon as the corresponding comparison out of
`C ⊗[B] M` is. -/
lemma injective_liftBaseChange_quot (ℓ : M →ₗ[B ⧸ J] N)
    (h : Function.Injective (LinearMap.liftBaseChange C (ℓ.restrictScalars B))) :
    Function.Injective (LinearMap.liftBaseChange (C ⧸ extJ C J) ℓ) := by
  intro x y hxy
  obtain ⟨x', rfl⟩ := reduceTensor_surjective C J x
  obtain ⟨y', rfl⟩ := reduceTensor_surjective C J y
  rw [liftBaseChange_reduceTensor, liftBaseChange_reduceTensor] at hxy
  rw [h hxy]

end Reduce

/-! ### The comparison `C₀ ⊗[B₀] J ≅ J C` -/

section Comparison

variable (C) [Module (B ⧸ J) J] [IsScalarTower B (B ⧸ J) J]
  [Module (C ⧸ extJ C J) (extJ C J)] [IsScalarTower C (C ⧸ extJ C J) (extJ C J)]

omit [Module (B ⧸ J) J] [IsScalarTower B (B ⧸ J) J] in
/-- The class of `c` in `C ⧸ J C` acts on `J C` as `c`. -/
lemma mk_smul_extJ (c : C) (x : extJ C J) :
    (Ideal.Quotient.mk (extJ C J) c • x : extJ C J) = c • x :=
  mk_smul_of_towerC C J c x

/-- The extension `j ↦ t j` of an element of `J` to an element of `J C`. -/
def tJ : J →ₗ[B] extJ C J where
  toFun j := ⟨algebraMap B C j, Ideal.mem_map_of_mem _ j.2⟩
  map_add' x y := by ext; simp
  map_smul' b j := by ext; simp [Algebra.smul_def]

omit [Module (B ⧸ J) J] [IsScalarTower B (B ⧸ J) J] [Module (C ⧸ extJ C J) (extJ C J)]
  [IsScalarTower C (C ⧸ extJ C J) (extJ C J)] in
/-- `tJ j = t j` as elements of `C`. -/
@[simp]
lemma tJ_apply (j : J) : (tJ C J j : C) = algebraMap B C j := rfl

omit [Module (B ⧸ J) J] [IsScalarTower B (B ⧸ J) J] in
/-- `B₀` acting on `J C` through `t₀`. -/
abbrev tModule : Module (B ⧸ J) (extJ C J) :=
  Module.compHom _ (algebraMap (B ⧸ J) (C ⧸ extJ C J))

/-- `j ↦ t j`, linear over `B₀` acting on `J C` through `t₀`. -/
def tJ₀ :
    letI := tModule C J
    J →ₗ[B ⧸ J] extJ C J :=
  letI := tModule C J
  { tJ C J with
    map_smul' := fun β j => by
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective β
      change tJ C J (Ideal.Quotient.mk J b • j) =
        algebraMap (B ⧸ J) (C ⧸ extJ C J) (Ideal.Quotient.mk J b) • tJ C J j
      rw [mk_smul_of_tower, LinearMap.map_smul, t₀_mk, mk_smul_extJ, algebraMap_smul] }

/-- The comparison `C₀ ⊗[B₀] J → J C`, `c ⊗ j ↦ c t(j)`. -/
noncomputable def κ : (C ⧸ extJ C J) ⊗[B ⧸ J] J →ₗ[C ⧸ extJ C J] extJ C J :=
  letI := tModule C J
  haveI : IsScalarTower (B ⧸ J) (C ⧸ extJ C J) (extJ C J) :=
    ⟨fun x y z => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  LinearMap.liftBaseChange (C ⧸ extJ C J) (tJ₀ C J)

/-- `κ (c̄ ⊗ j) = c * t j` as elements of `C`. -/
lemma κ_tmul (c : C) (j : J) :
    (κ C J (Ideal.Quotient.mk (extJ C J) c ⊗ₜ j) : C) = c * algebraMap B C j := by
  rw [show κ C J (Ideal.Quotient.mk (extJ C J) c ⊗ₜ j) =
    Ideal.Quotient.mk (extJ C J) c • tJ C J j from rfl, mk_smul_extJ]
  rfl

/-- If `t : B → C` is flat, the comparison `κ : C₀ ⊗[B₀] J → J C` is bijective. -/
lemma κ_bijective [Module.Flat B C] : Function.Bijective (κ C J) := by
  let := tModule C J
  have : IsScalarTower (B ⧸ J) (C ⧸ extJ C J) (extJ C J) :=
    ⟨fun x y z => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  have : IsScalarTower B (B ⧸ J) (extJ C J) := ⟨fun b β p => by
    change (algebraMap (B ⧸ J) (C ⧸ extJ C J) (b • β)) • p = b • (algebraMap _ _ β • p)
    rw [Algebra.smul_def, map_mul, mul_smul, Ideal.Quotient.algebraMap_eq, t₀_mk,
      mk_smul_extJ, algebraMap_smul]
    rfl⟩
  constructor
  · refine injective_liftBaseChange_quot C J (tJ₀ C J) ?_
    have h := (TensorProduct.rid B C).injective.comp
      (Module.Flat.lTensor_preserves_injective_linearMap (M := C) J.subtype
        Subtype.val_injective)
    intro x y hxy
    refine h ?_
    have key : ∀ z : C ⊗[B] J,
        ((LinearMap.liftBaseChange C ((tJ₀ C J).restrictScalars B) z : extJ C J) : C) =
          TensorProduct.rid B C (LinearMap.lTensor C J.subtype z) := by
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul c j =>
        rw [LinearMap.liftBaseChange_tmul, LinearMap.lTensor_tmul, TensorProduct.rid_tmul,
          Submodule.subtype_apply, Algebra.smul_def, mul_comm]
        rfl
      | add x y hx hy => simp only [map_add, Submodule.coe_add, hx, hy]
    simp only [Function.comp_apply, ← key, hxy]
  · let I' : Ideal C :=
      { carrier := {c | ∃ z, (κ C J z : C) = c}
        add_mem' := by
          rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
          exact ⟨x + y, by simp⟩
        zero_mem' := ⟨0, by simp⟩
        smul_mem' := by
          rintro c _ ⟨x, rfl⟩
          refine ⟨Ideal.Quotient.mk (extJ C J) c • x, ?_⟩
          rw [LinearMap.map_smul, mk_smul_extJ]
          rfl }
    have hle : extJ C J ≤ I' := by
      refine Ideal.map_le_iff_le_comap.mpr fun j hj => ?_
      refine ⟨(1 : C ⧸ extJ C J) ⊗ₜ ⟨j, hj⟩, ?_⟩
      rw [← map_one (Ideal.Quotient.mk (extJ C J)), κ_tmul, one_mul]
    intro p
    obtain ⟨z, hz⟩ := hle p.2
    exact ⟨z, Subtype.ext hz⟩

end Comparison

/-! ### The comparison `B₀ ⊗[A₀] J ≅ J C` over the reduced equalizer -/

section OverBase

variable (C)

/-- If `J ^ 2 = ⊥` then `(J C) ^ 2 = ⊥`. -/
lemma extJ_sq (hJ : J ^ 2 = ⊥) : extJ C J ^ 2 = ⊥ := by
  rw [extJ, ← Ideal.map_pow, hJ, Ideal.map_bot]

/-- If `J ^ 2 = ⊥`, the product of two elements of `J C` vanishes. -/
lemma mul_eq_zero_of_mem_extJ (hJ : J ^ 2 = ⊥) {x y : C} (hx : x ∈ extJ C J)
    (hy : y ∈ extJ C J) : x * y = 0 := by
  exact mul_eq_zero_of_sq_eq_bot (extJ_sq C J hJ) hx hy

variable {A₀ : Type u} [CommRing A₀] [Algebra A₀ (B ⧸ J)] [Algebra A₀ (C ⧸ extJ C J)]
  [IsScalarTower A₀ (B ⧸ J) (C ⧸ extJ C J)]
  [Module (B ⧸ J) J] [IsScalarTower B (B ⧸ J) J] [Module A₀ J] [IsScalarTower A₀ (B ⧸ J) J]
  [Module (C ⧸ extJ C J) (extJ C J)] [IsScalarTower C (C ⧸ extJ C J) (extJ C J)]
  [Module A₀ (extJ C J)] [IsScalarTower A₀ (C ⧸ extJ C J) (extJ C J)]

variable {C}

omit [Algebra A₀ (B ⧸ J)] [Algebra A₀ (C ⧸ extJ C J)]
  [IsScalarTower A₀ (B ⧸ J) (C ⧸ extJ C J)] [Module (B ⧸ J) J] [IsScalarTower B (B ⧸ J) J]
  [Module A₀ J] [IsScalarTower A₀ (B ⧸ J) J] [Module (C ⧸ extJ C J) (extJ C J)]
  [IsScalarTower C (C ⧸ extJ C J) (extJ C J)] [Module A₀ (extJ C J)]
  [IsScalarTower A₀ (C ⧸ extJ C J) (extJ C J)] in
/-- If `s J C = J C`, then `s j ∈ J C` for every `j ∈ J`. -/
lemma s_mem_extJ (hinv : J.map s = extJ C J) (j : J) : s j ∈ extJ C J :=
  hinv ▸ Ideal.mem_map_of_mem s j.2

omit [Algebra A₀ (B ⧸ J)] [Algebra A₀ (C ⧸ extJ C J)]
  [IsScalarTower A₀ (B ⧸ J) (C ⧸ extJ C J)] [Module (B ⧸ J) J] [IsScalarTower B (B ⧸ J) J]
  [Module A₀ J] [IsScalarTower A₀ (B ⧸ J) J] [Module (C ⧸ extJ C J) (extJ C J)]
  [IsScalarTower C (C ⧸ extJ C J) (extJ C J)] [Module A₀ (extJ C J)]
  [IsScalarTower A₀ (C ⧸ extJ C J) (extJ C J)] in
/-- If `s₀` and `t₀` agree on the class of `b`, then `s b - t b ∈ J C`. -/
lemma s_sub_t_mem (hinv : J.map s = extJ C J) {b : B}
    (hb : s₀ s J hinv (Ideal.Quotient.mk J b) =
      algebraMap (B ⧸ J) (C ⧸ extJ C J) (Ideal.Quotient.mk J b)) :
    s b - algebraMap B C b ∈ extJ C J := by
  rw [s₀_mk, t₀_mk] at hb
  exact Ideal.Quotient.eq.mp hb

/-- An element of `A₀` acts on `J` and on `J C` as any lift `b ∈ B` of its image in `B₀`. -/
lemma smul_eq_of_lift {a : A₀} {b : B} (hb : Ideal.Quotient.mk J b = algebraMap A₀ (B ⧸ J) a) :
    (∀ j : J, a • j = b • j) ∧ ∀ p : extJ C J, a • p = algebraMap B C b • p := by
  refine ⟨fun j => ?_, fun p => ?_⟩
  · rw [← algebraMap_smul (B ⧸ J) a j, ← hb, mk_smul_of_tower]
  · rw [← algebraMap_smul (C ⧸ extJ C J) a p, IsScalarTower.algebraMap_apply A₀ (B ⧸ J),
      ← hb, t₀_mk, mk_smul_extJ, algebraMap_smul]

variable (C) in
/-- `j ↦ t j`, linear over `A₀`. -/
def tJA : J →ₗ[A₀] extJ C J :=
  { tJ C J with
    map_smul' := fun a j => by
      obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (algebraMap A₀ (B ⧸ J) a)
      have h := smul_eq_of_lift J hb (C := C)
      change tJ C J (a • j) = a • tJ C J j
      rw [h.1, h.2, LinearMap.map_smul, algebraMap_smul] }

variable (hJ : J ^ 2 = ⊥) (hinv : J.map s = extJ C J)
  (hcomp : ∀ a : A₀, s₀ s J hinv (algebraMap A₀ (B ⧸ J) a) =
    algebraMap (B ⧸ J) (C ⧸ extJ C J) (algebraMap A₀ (B ⧸ J) a))

include hJ hcomp in
/-- The restriction `j ↦ s j` of an element of `J` to an element of `J C`. -/
def sJ : J →ₗ[A₀] extJ C J where
  toFun j := ⟨s j, s_mem_extJ s J hinv j⟩
  map_add' x y := by ext; simp
  map_smul' a j := by
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (algebraMap A₀ (B ⧸ J) a)
    have h := smul_eq_of_lift J hb (C := C)
    have hsub : s b - algebraMap B C b ∈ extJ C J := s_sub_t_mem s J hinv (hb ▸ hcomp a)
    have hz := mul_eq_zero_of_mem_extJ C J hJ hsub (s_mem_extJ s J hinv j)
    rw [sub_mul, sub_eq_zero] at hz
    ext
    rw [RingHom.id_apply, h.1, h.2]
    simp [hz, Algebra.smul_def]

/-- `sJ j = s j` as elements of `C`. -/
@[simp]
lemma sJ_apply (j : J) :
    (sJ (s := s) (J := J) (hJ := hJ) (hinv := hinv) (hcomp := hcomp) j : C) = s j := rfl

section General

variable {P : Type*} [CommRing P] [Algebra A₀ P] (σP : P →+* C ⧸ extJ C J)
  (hP : ∀ a : A₀, σP (algebraMap A₀ P a) =
    algebraMap (B ⧸ J) (C ⧸ extJ C J) (algebraMap A₀ (B ⧸ J) a))

omit [Module (B ⧸ J) J] [IsScalarTower B (B ⧸ J) J] [Module A₀ J] [IsScalarTower A₀ (B ⧸ J) J]
  [Module (C ⧸ extJ C J) (extJ C J)] [IsScalarTower C (C ⧸ extJ C J) (extJ C J)]
  [Module A₀ (extJ C J)] [IsScalarTower A₀ (C ⧸ extJ C J) (extJ C J)] in
/-- A bijective comparison `B₀ ⊗[A₀] P → C₀`, as an `A₀`-linear equivalence. -/
noncomputable def cmpPEquiv (hbij : Function.Bijective (cmpP σP hP)) :
    (B ⧸ J) ⊗[A₀] P ≃ₗ[A₀] C ⧸ extJ C J :=
  LinearEquiv.ofBijective
    { toFun := cmpP σP hP
      map_add' := map_add _
      map_smul' := fun a z => by
        induction z using TensorProduct.inductionOn with
        | tmul x y =>
          rw [TensorProduct.smul_tmul', RingHom.id_apply]
          change algebraMap _ _ (a • x) * σP y = a • (algebraMap _ _ x * σP y)
          rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, Algebra.smul_def,
            mul_assoc]
        | add x y hx hy => simp only [map_add, smul_add, hx, hy] } hbij

/-- `P` acting on `J C` through `σP`. -/
abbrev pModule : Module P (extJ C J) := Module.compHom _ σP

omit [Module (B ⧸ J) J] [IsScalarTower B (B ⧸ J) J] [Module A₀ J] [IsScalarTower A₀ (B ⧸ J) J]
  [IsScalarTower C (C ⧸ extJ C J) (extJ C J)] in
include hP in
/-- With `P` acting on `J C` through `σP`, the actions of `A₀` and `P` on `J C` form a scalar
tower. -/
lemma pTower :
    letI := pModule J σP
    IsScalarTower A₀ P (extJ C J) := by
  let := pModule J σP
  refine ⟨fun a b p => ?_⟩
  rw [Algebra.smul_def]
  change σP (algebraMap A₀ P a * b) • p = a • (σP b • p)
  rw [map_mul, mul_smul, hP, ← IsScalarTower.algebraMap_apply, algebraMap_smul]

include hP in
/-- The comparison `P ⊗[A₀] J → J C`, `b ⊗ j ↦ σP(b) t(j)`. -/
noncomputable def αP : P ⊗[A₀] J →ₗ[A₀] extJ C J :=
  letI := pModule J σP
  haveI := pTower J σP hP
  (LinearMap.liftBaseChange P (tJA C J)).restrictScalars A₀

/-- `αP (b ⊗ j) = σP(b) t(j)`. -/
lemma αP_tmul (b : P) (j : J) : αP J σP hP (b ⊗ₜ j) = σP b • tJ C J j := rfl

/-- If `t` is flat and `B₀ ⊗[A₀] P → C₀` is bijective, then `αP : P ⊗[A₀] J → J C` is
bijective. -/
lemma αP_bijective [Module.Flat B C] (hbij : Function.Bijective (cmpP σP hP)) :
    Function.Bijective (αP J σP hP) := by
  let : Algebra P (C ⧸ extJ C J) := σP.toAlgebra
  refine Module.Descent.bijective_pushout_comparison (cmpPEquiv J σP hP hbij)
    (fun _ _ => rfl) (κ C J) (κ_bijective C J) (αP J σP hP) (fun b x => ?_)
  change _ = _ • ((1 : C ⧸ extJ C J) • tJ C J x)
  rw [one_smul]
  rfl

end General

/-- The comparison `B₀ ⊗[A₀] J → J C`, `b ⊗ j ↦ s₀(b) t(j)`. -/
noncomputable abbrev α : (B ⧸ J) ⊗[A₀] J →ₗ[A₀] extJ C J :=
  αP J (s₀ s J hinv) hcomp

/-- `α (b ⊗ j) = s₀(b) t(j)`. -/
lemma α_tmul (b : B ⧸ J) (j : J) :
    α s J hinv hcomp (b ⊗ₜ j) = s₀ s J hinv b • tJ C J j := rfl

/-- If `t` is flat and the reduced comparison `B₀ ⊗[A₀] B₀ → C₀` is bijective, then
`α : B₀ ⊗[A₀] J → J C` is bijective. -/
lemma α_bijective [Module.Flat B C] (hbij : Function.Bijective (cmp (s₀ s J hinv) A₀ hcomp)) :
    Function.Bijective (α s J hinv hcomp) :=
  αP_bijective J _ hcomp hbij

/-- `α (β • x) = s₀(β) α(x)`. -/
lemma α_smul (β : B ⧸ J) (x : (B ⧸ J) ⊗[A₀] J) :
    α s J hinv hcomp (β • x) = s₀ s J hinv β • α s J hinv hcomp x := by
  let := pModule J (s₀ s J hinv)
  have := pTower J (s₀ s J hinv) hcomp
  exact (LinearMap.liftBaseChange (B ⧸ J) (tJA C J)).map_smul β x

/-- `sJ (β • n) = s₀(β) sJ(n)`. -/
lemma sJ_smul (β : B ⧸ J) (n : J) :
    sJ (s := s) (J := J) (hJ := hJ) (hinv := hinv) (hcomp := hcomp) (β • n) =
      s₀ s J hinv β • sJ (s := s) (J := J) (hJ := hJ) (hinv := hinv) (hcomp := hcomp) n := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective β
  ext
  rw [s₀_mk, mk_smul_extJ, Submodule.coe_smul_of_tower, sJ_apply, sJ_apply, mk_smul_of_tower,
    Submodule.coe_smul_of_tower, smul_eq_mul, map_mul, smul_eq_mul]

end OverBase

end Module.Descent.SquareZero

end
