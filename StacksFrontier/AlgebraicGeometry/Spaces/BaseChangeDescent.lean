module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartStalkTensorComparison

/-!
# Descending and transporting a semilinear map along a base change

A ring map `R → A` and an `R`-linear map `g : M → N` whose base change `A ⊗_R M → N` is
bijective let one descend a semilinear map out of `M` to a semilinear map out of `N`
(`AlgebraicGeometry.Space.baseChangeDesc`).

Separately, bijectivity of `AlgebraicGeometry.Space.baseChangeLift` transports along ring
equivalences of the source and target rings together with compatible semilinear equivalences of
the modules (`AlgebraicGeometry.Space.baseChangeLift_bijective_of_equiv`).

## Main definitions

* `AlgebraicGeometry.Space.baseChangeDesc` descends a semilinear map along a bijective base
  change.

## Main results

* `AlgebraicGeometry.Space.baseChangeDesc_apply` and
  `AlgebraicGeometry.Space.baseChangeDesc_unique`: the descent extends the given map along `g`,
  and it is the only semilinear map which does.
* `AlgebraicGeometry.Space.baseChangeLift_bijective_of_equiv`: bijectivity of a lifted
  semilinear map transports along ring and module equivalences.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped ChangeOfRings

universe u m

namespace AlgebraicGeometry.Space

section Desc
universe r k e c n q
variable {R : Type r} {A : Type k} {E : Type e} [CommRing R] [CommRing A] [CommRing E]
  [Algebra R A] {M : Type c} [AddCommGroup M] [Module R M]
  {N : Type n} [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower R A N]
  {P : Type q} [AddCommGroup P] [Module E P]

/-- **Descent of a semilinear map along a bijective base change.** If the base change
`A ⊗_R M → N` of an `R`-linear map `g` is bijective, a map out of `M` which is semilinear along
`l ∘ algebraMap R A` descends to a map out of `N` which is semilinear along `l`. -/
noncomputable def baseChangeDesc (g : M →ₗ[R] N)
    (hg : Function.Bijective (g.liftBaseChange A))
    (l : A →+* E) (h : M →ₛₗ[l.comp (algebraMap R A)] P) : N →ₛₗ[l] P := by
  letI : Module A P := Module.compHom P l
  letI : Module R P := Module.compHom P (l.comp (algebraMap R A))
  letI : IsScalarTower R A P := ⟨fun r a p => by
    change l (r • a) • p = l (algebraMap R A r) • (l a • p)
    rw [Algebra.smul_def, map_mul, mul_smul]⟩
  let h' : M →ₗ[R] P := { h with map_smul' := h.map_smul' }
  let L := (h'.liftBaseChange A).comp
    (LinearEquiv.ofBijective (g.liftBaseChange A) hg).symm.toLinearMap
  exact { toFun := L, map_add' := L.map_add, map_smul' := L.map_smul }

/-- The descent of a semilinear map agrees with it along `g`. -/
theorem baseChangeDesc_apply (g : M →ₗ[R] N)
    (hg : Function.Bijective (g.liftBaseChange A))
    (l : A →+* E) (h : M →ₛₗ[l.comp (algebraMap R A)] P) (t : M) :
    baseChangeDesc g hg l h (g t) = h t := by
  let : Module A P := Module.compHom P l
  let : Module R P := Module.compHom P (l.comp (algebraMap R A))
  let : IsScalarTower R A P := ⟨fun r a p => by
    change l (r • a) • p = l (algebraMap R A r) • (l a • p)
    rw [Algebra.smul_def, map_mul, mul_smul]⟩
  let h' : M →ₗ[R] P := { h with map_smul' := h.map_smul' }
  let e := LinearEquiv.ofBijective (g.liftBaseChange A) hg
  have he : e ((1 : A) ⊗ₜ[R] t) = g t := by
    change g.liftBaseChange A ((1 : A) ⊗ₜ[R] t) = g t
    rw [LinearMap.liftBaseChange_tmul, one_smul]
  change h'.liftBaseChange A (e.symm (g t)) = h t
  rw [← he, e.symm_apply_apply, LinearMap.liftBaseChange_tmul, one_smul]
  rfl

/-- Two semilinear maps out of `N` which agree along `g` are equal, when the base change of
`g` is bijective. -/
theorem baseChangeDesc_unique (g : M →ₗ[R] N)
    (hg : Function.Bijective (g.liftBaseChange A))
    (l : A →+* E) (h₁ h₂ : N →ₛₗ[l] P) (he : ∀ t, h₁ (g t) = h₂ (g t)) : h₁ = h₂ := by
  ext y
  obtain ⟨z, rfl⟩ := hg.2 y
  induction z using TensorProduct.inductionOn with
  | tmul a t =>
    rw [LinearMap.liftBaseChange_tmul, h₁.map_smulₛₗ, h₂.map_smulₛₗ, he]
  | add z z' hz hz' => simp only [map_add, hz, hz']

end Desc

section Transport
universe r k r' k' c c' n n'

/-- A ring equivalence and its inverse form a `RingHomInvPair`. -/
theorem ringEquivInvPair {R A : Type*} [CommRing R] [CommRing A] (e : R ≃+* A) :
    RingHomInvPair e.toRingHom e.symm.toRingHom :=
  ⟨e.symm_toRingHom_comp_toRingHom, e.symm.symm_toRingHom_comp_toRingHom⟩

/-- The inverse of a ring equivalence and the equivalence itself form a `RingHomInvPair`. -/
theorem ringEquivInvPairSymm {R A : Type*} [CommRing R] [CommRing A] (e : R ≃+* A) :
    RingHomInvPair e.symm.toRingHom e.toRingHom :=
  ⟨e.symm.symm_toRingHom_comp_toRingHom, e.symm_toRingHom_comp_toRingHom⟩

attribute [local instance] ringEquivInvPair ringEquivInvPairSymm

/-- **Bijectivity of a lifted semilinear map transports along equivalences.** Given ring
equivalences of the sources and targets commuting with the two ring maps, and semilinear
equivalences of the modules commuting with the two semilinear maps, the base changes of those
maps are bijective together. -/
theorem baseChangeLift_bijective_of_equiv
    {R : Type r} {A : Type k} {R' : Type r'} {A' : Type k'}
    [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    (f : R →+* A) (f' : R' →+* A') (eR : R ≃+* R') (eA : A ≃+* A')
    (hRing : ∀ a, f' (eR a) = eA (f a))
    (M : ModuleCat.{c} R) (M' : ModuleCat.{c'} R')
    {N : Type n} [AddCommGroup N] [Module A N]
    {N' : Type n'} [AddCommGroup N'] [Module A' N']
    (eM : M ≃ₛₗ[eR.toRingHom] M') (eN : N ≃ₛₗ[eA.toRingHom] N')
    (g : M →ₛₗ[f] N) (g' : M' →ₛₗ[f'] N')
    (hMap : ∀ t, g' (eM t) = eN (g t))
    (hBij : Function.Bijective (baseChangeLift f' M' g')) :
    Function.Bijective (baseChangeLift f M g) := by
  let eS : ((ModuleCat.restrictScalars f).obj (ModuleCat.of A A)) ≃ₛₗ[eR.toRingHom]
      ((ModuleCat.restrictScalars f').obj (ModuleCat.of A' A')) :=
    { __ := eA.toAddEquiv
      map_smul' := by
        intro a b
        change eA (f a * (@id A b)) = f' (eR a) * eA (@id A b)
        rw [map_mul, hRing] }
  let E := TensorProduct.congr eS eM
  have h : ∀ t, baseChangeLift f' M' g' (E t) = eN (baseChangeLift f M g t) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a y =>
      refine Eq.trans (congrArg (baseChangeLift f' M' g')
        (TensorProduct.congr_tmul eS eM a y)) ?_
      refine Eq.trans (baseChangeLift_tmul f' M' g' (eS a) (eM y)) ?_
      refine Eq.trans (congrArg (fun z : N' => eA a • z) (hMap y)) ?_
      exact ((congrArg eN (baseChangeLift_tmul f M g a y)).trans
        (eN.map_smulₛₗ a (g y))).symm
    | add y z hy hz =>
      refine Eq.trans (congrArg (baseChangeLift f' M' g') (map_add E y z)) ?_
      refine Eq.trans (map_add (baseChangeLift f' M' g') (E y) (E z)) ?_
      refine Eq.trans (congrArg (· + baseChangeLift f' M' g' (E z)) hy) ?_
      refine Eq.trans (congrArg (eN (baseChangeLift f M g y) + ·) hz) ?_
      exact ((congrArg eN (map_add (baseChangeLift f M g) y z)).trans
        (map_add eN _ _)).symm
  refine ⟨fun y z hyz => E.injective (hBij.1
    ((h y).trans ((congrArg eN hyz).trans (h z).symm))), fun z => ?_⟩
  obtain ⟨y, hy⟩ := hBij.2 (eN z)
  exact ⟨E.symm y, eN.injective ((h (E.symm y)).symm.trans
    ((congrArg (baseChangeLift f' M' g') (E.apply_symm_apply y)).trans hy))⟩

end Transport

end AlgebraicGeometry.Space

end
