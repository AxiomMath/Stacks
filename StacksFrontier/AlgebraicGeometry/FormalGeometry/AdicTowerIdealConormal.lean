module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicTowerGradedModule
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicTowerTransitionKernel

/-!
# The transition ideals of an adic tower as conormal pieces

In a cartesian tower `X₀ ⟶ X₁ ⟶ ⋯` over the adic thickenings, the ideal sheaf
`Ker(𝒪_{Xₙ₊₁} ⟶ 𝒪_{Xₙ}) = I^{n+1}𝒪_{Xₙ₊₁}` is the direct image along `X₀ ⟶ Xₙ₊₁` of the
degree-`(n+1)` piece of the conormal algebra of `X₀ ⟶ Xₙ₊₁`: over an affine open both are
`𝒥^{n+1}` with `𝒥 = I𝒪_{Xₙ₊₁}`, because `𝒥^{n+2} = 0`. This identifies the transition kernels of
the proof of [Stacks, Tag 089A] with the homogeneous pieces of the graded module
`Stacks.AdicTower.towerModule`, whose twists have uniformly vanishing cohomology.

## Main results

* `Stacks.AdicTower.conormalTransitionIdealIso`: `(X₀ ⟶ Xₙ₊₁)_* (C_{n+1})_{n+1} ≅ I^{n+1}𝒪_{Xₙ₊₁}`.

## References

* [Stacks Project, Tag 089A](https://stacks.math.columbia.edu/tag/089A)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.AdicTower

variable {A : Type u} [CommRing A] {I : Ideal A} {Xn : ℕ → Scheme.{u}}
  (q : ∀ n, Xn n ⟶ adicThickening A I n) (t : ∀ n, Xn n ⟶ Xn (n + 1))
  (hcart : ∀ n, IsPullback (t n) (q n) (q (n + 1)) (adicThickeningSucc A I n))
  [hci : ∀ k, IsClosedImmersion (incl t k)] [hct : ∀ k, IsClosedImmersion (t k)]

omit [∀ k, IsClosedImmersion (incl t k)] [∀ k, IsClosedImmersion (t k)] in
/-- The powers of `I𝒪_{Xₘ}` lie in the ideal powers `Iᵏ𝒪_{Xₘ}`. -/
lemma pow_ideal_towerIdealPow_one_le (m : ℕ) (U : (Xn m).affineOpens) :
    ∀ (k : ℕ) (h : k ≤ m + 1),
      (towerIdealPow q m 1 (by omega)).ideal U ^ k ≤ (towerIdealPow q m k h).ideal U
  | 0, h => by
    rw [pow_zero, Ideal.one_eq_top, ideal_towerIdealPow]
    intro x _
    have h1 : (1 : Γ(adicThickening A I m, ⊤)) ∈
        RingHom.ker (Spec.map (basePowHom A I m 0 h)).appTop.hom := by
      rw [mem_ker_appTop_iff]
      simp only [CommRingCat.hom_ofHom, Ideal.Quotient.factor_ker, pow_zero, Ideal.one_eq_top,
        Ideal.map_top]
      exact Submodule.mem_top
    simpa using Ideal.mul_mem_left _ x (Ideal.mem_map_of_mem (baseAppLEAt q m U).hom h1)
  | k + 1, h => by
    rw [pow_succ]
    refine (Ideal.mul_mono_left (pow_ideal_towerIdealPow_one_le m U k (by omega))).trans ?_
    exact ideal_mul_ideal_le_towerIdealPow q m k 1 (by omega) (by omega) h U

/-- On a chart of `Xₙ₊₁` the ideal of `X₀` is the first ideal power of the tower. -/
private lemma chartIdeal_eq_towerIdealPow_one (t : ∀ n, Xn n ⟶ Xn (n + 1))
    [∀ k, IsClosedImmersion (incl t k)]
    (hc : ∀ n, IsPullback (t n) (q n) (q (n + 1)) (adicThickeningSucc A I n))
    (n : ℕ) (V : (Xn (n + 1)).affineOpens) :
    Stacks.Conormal.chartIdeal (incl t (n + 1)) V =
      (towerIdealPow q (n + 1) 1 (by omega)).ideal V := by
  rw [towerIdealPow_one q t hc (n + 1), Scheme.Hom.ker_apply]

include hcart in
/-- On a chart of `Xₙ₊₁` the `(n+1)`-st power of the ideal of `X₀` is the kernel of
`Γ(Xₙ₊₁, V) ⟶ Γ(Xₙ, V)`. -/
lemma chartIdeal_pow_eq_ker (n : ℕ) (V : (Xn (n + 1)).affineOpens) :
    Stacks.Conormal.chartIdeal (incl t (n + 1)) V ^ (n + 1) = RingHom.ker ((t n).app V.1).hom := by
  have h1 : RingHom.ker ((t n).app V.1).hom =
      (towerIdealPow q (n + 1) (n + 1) (by omega)).ideal V := by
    rw [towerIdealPow_self q t hcart n, Scheme.Hom.ker_apply]
  rw [h1, chartIdeal_eq_towerIdealPow_one q t hcart n V]
  exact le_antisymm (pow_ideal_towerIdealPow_one_le q (n + 1) V (n + 1) (by omega))
    (ideal_towerIdealPow_le_pow q (n + 1) (n + 1) _ _ V)

include hcart in
omit hct in
/-- On a chart of `Xₙ₊₁` the `(n+2)`-nd power of the ideal of `X₀` vanishes. -/
lemma chartIdeal_pow_succ_eq_bot (n : ℕ) (V : (Xn (n + 1)).affineOpens) :
    Stacks.Conormal.chartIdeal (incl t (n + 1)) V ^ (n + 1 + 1) = ⊥ := by
  rw [chartIdeal_eq_towerIdealPow_one q t hcart n V]
  refine le_bot_iff.mp ((pow_ideal_towerIdealPow_one_le q (n + 1) V (n + 1 + 1) le_rfl).trans ?_)
  rw [towerIdealPow_eq_bot q (n + 1) V]

include hcart in
omit hct in
/-- On a chart `V` of `Xₙ₊₁`, the local presentation `𝒥^{n+1}(V) ⟶ (C_{n+1})_{n+1}(V)` of the
conormal algebra of `X₀ ⟶ Xₙ₊₁` in degree `n + 1` is bijective. -/
lemma bijective_localMap_top (n : ℕ) (V : (Xn (n + 1)).affineOpens) :
    Function.Bijective ((Stacks.Conormal.conormalAlgebra (incl t (n + 1))).localMap V
      (isClosedImmersion_resLE_incl t (n + 1) V.1) (n + 1)) := by
  refine ⟨fun a b hab => ?_, (Stacks.Conormal.conormalAlgebra (incl t (n + 1))).localMap_surjective
    V _ (n + 1)⟩
  rw [← sub_eq_zero, ← map_sub,
    (Stacks.Conormal.conormalAlgebra (incl t (n + 1))).localMap_eq_zero_iff,
    chartIdeal_pow_succ_eq_bot q t hcart n V, Ideal.mem_bot] at hab
  exact sub_eq_zero.mp (Subtype.ext hab)

/-- The local presentation `𝒥^{n+1}(V) ≃ (C_{n+1})_{n+1}(V)` in top degree, as an additive
equivalence. -/
def localMapTopEquiv (n : ℕ) (V : (Xn (n + 1)).affineOpens) :
    ↥(Stacks.Conormal.chartIdeal (incl t (n + 1)) V ^ (n + 1)) ≃+
      ((conormalAlg t (n + 1)).piece ((n + 1 : ℕ) : ℤ)).val.obj (op (chartOpen t (n + 1) V)) :=
  AddEquiv.ofBijective _ (bijective_localMap_top q t hcart n V)

/-! ### The comparison morphism -/

include hcart in
/-- On a chart `V` of `Xₙ₊₁`, a section of `I^{n+1}𝒪_{Xₙ₊₁}` over `V` is a function in the
`(n+1)`-st power of the ideal of `X₀`. -/
lemma kernelι_mem (n : ℕ) (V : (Xn (n + 1)).affineOpens)
    (x : (transitionIdeal t n).val.obj (op V.1)) :
    (show Γ(Xn (n + 1), V.1) from
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit (t n).toRingCatSheafHom)).val.app
        (op V.1) x) ∈ Stacks.Conormal.chartIdeal (incl t (n + 1)) V ^ (n + 1) := by
  rw [chartIdeal_pow_eq_ker q t hcart n V, RingHom.mem_ker]
  exact (Stacks.Thickenings.exact_app_idealSheafModule (t n) V.1).apply_apply_eq_zero x

/-- The comparison on the sections over an affine open of `Xₙ₊₁`, as a linear map: a function in
`I^{n+1}𝒪_{Xₙ₊₁}(V)` goes to its class in `𝒥^{n+1}/𝒥^{n+2}`. -/
def idealConormalLin (n : ℕ) (V : (Xn (n + 1)).affineOpens) :
    (transitionIdeal t n).val.obj (op V.1) →ₗ[(Xn (n + 1)).ringCatSheaf.obj.obj (op V.1)]
      ((Scheme.Modules.pushforward (incl t (n + 1))).obj
        ((conormalAlg t (n + 1)).piece ((n + 1 : ℕ) : ℤ))).val.obj (op V.1) where
  toFun x := (Stacks.Conormal.conormalAlgebra (incl t (n + 1))).localMap V
    (isClosedImmersion_resLE_incl t (n + 1) V.1) (n + 1) ⟨_, kernelι_mem q t hcart n V x⟩
  map_add' x y :=
    (congrArg ((Stacks.Conormal.conormalAlgebra (incl t (n + 1))).localMap V
      (isClosedImmersion_resLE_incl t (n + 1) V.1) (n + 1))
        (Subtype.ext (((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (t n).toRingCatSheafHom)).val.app (op V.1)).hom.map_add x y) :
        (⟨_, kernelι_mem q t hcart n V (x + y)⟩ :
          ↥(Stacks.Conormal.chartIdeal (incl t (n + 1)) V ^ (n + 1))) =
          ⟨_, kernelι_mem q t hcart n V x⟩ + ⟨_, kernelι_mem q t hcart n V y⟩)).trans
      (map_add _ _ _)
  map_smul' r x :=
    (Stacks.Conormal.conormalAlgebra (incl t (n + 1))).localMap_smul V _ (n + 1) r
      ⟨_, kernelι_mem q t hcart n V x⟩ ⟨_, kernelι_mem q t hcart n V (r • x)⟩
      (((kernel.ι (SheafOfModules.unitToPushforwardObjUnit (t n).toRingCatSheafHom)).val.app
        (op V.1)).hom.map_smul r x)

/-- The comparison on the sections over an affine open of `Xₙ₊₁`. -/
def idealConormalSec (n : ℕ) (V : (Xn (n + 1)).affineOpens) :
    (transitionIdeal t n).val.obj (op V.1) ⟶
      ((Scheme.Modules.pushforward (incl t (n + 1))).obj
        ((conormalAlg t (n + 1)).piece ((n + 1 : ℕ) : ℤ))).val.obj (op V.1) :=
  ModuleCat.ofHom (X := ↑((transitionIdeal t n).val.obj (op V.1)))
    (Y := ↑(((Scheme.Modules.pushforward (incl t (n + 1))).obj
        ((conormalAlg t (n + 1)).piece ((n + 1 : ℕ) : ℤ))).val.obj (op V.1)))
    (idealConormalLin q t hcart n V)

/-- The comparisons `idealConormalSec` on affine opens of `Xₙ₊₁` commute with restriction. -/
lemma idealConormalSec_compatible (n : ℕ) :
    Stacks.BasisRestriction.IsCompatibleOnBasis (transitionIdeal t n)
      ((Scheme.Modules.pushforward (incl t (n + 1))).obj
        ((conormalAlg t (n + 1)).piece ((n + 1 : ℕ) : ℤ)))
      (fun V : (Xn (n + 1)).affineOpens => V.1) (idealConormalSec q t hcart n) := by
  intro V W h x
  exact ((Stacks.Conormal.conormalAlgebra (incl t (n + 1))).localMap_naturality V W h
    ((incl t (n + 1)).preimage_mono h) (isClosedImmersion_resLE_incl t (n + 1) V.1)
    (isClosedImmersion_resLE_incl t (n + 1) W.1) (n + 1) ⟨_, kernelι_mem q t hcart n V x⟩
    ⟨_, kernelι_mem q t hcart n W ((transitionIdeal t n).val.map (homOfLE h).op x)⟩
    (PresheafOfModules.naturality_apply
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit (t n).toRingCatSheafHom)).val
      (homOfLE h).op x)).symm

/-- **The comparison morphism** `I^{n+1}𝒪_{Xₙ₊₁} ⟶ (X₀ ⟶ Xₙ₊₁)_* (C_{n+1})_{n+1}`. -/
def idealConormalHom (n : ℕ) :
    transitionIdeal t n ⟶ (Scheme.Modules.pushforward (incl t (n + 1))).obj
      ((conormalAlg t (n + 1)).piece ((n + 1 : ℕ) : ℤ)) :=
  Stacks.BasisRestriction.moduleSheafHomOfSectionHomOnBasis _ _
    (fun V : (Xn (n + 1)).affineOpens => V.1) (idealConormalSec q t hcart n)
    (by simpa using (Xn (n + 1)).isBasis_affineOpens) (idealConormalSec_compatible q t hcart n)

/-- The comparison morphism `idealConormalHom` is an isomorphism. -/
lemma isIso_idealConormalHom (n : ℕ) : IsIso (idealConormalHom q t hcart n) := by
  refine Stacks.AlgebraicGeometry.GenericStalkBaseChange.isIso_of_isIso_val_app_basis
    (B := fun V : (Xn (n + 1)).affineOpens => V.1)
    (by simpa using (Xn (n + 1)).isBasis_affineOpens) _ (fun V => ?_)
  have happ : (idealConormalHom q t hcart n).val.app (op V.1) = idealConormalSec q t hcart n V :=
    Stacks.BasisRestriction.moduleSheafHomOfSectionHomOnBasis_app _ _ _ _ _ _ V
  rw [happ, ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun x y hxy => ?_, fun y => ?_⟩
  · exact Stacks.Thickenings.injective_app_idealSheafModule (t n) V.1
      (congrArg Subtype.val ((bijective_localMap_top q t hcart n V).1 hxy))
  · obtain ⟨a, rfl⟩ := (bijective_localMap_top q t hcart n V).2 y
    have ha : (a : Γ(Xn (n + 1), V.1)) ∈ RingHom.ker ((t n).app V.1).hom := by
      rw [← chartIdeal_pow_eq_ker q t hcart n V]
      exact a.2
    obtain ⟨x, hx⟩ := (Stacks.Thickenings.exact_app_idealSheafModule (t n) V.1 a.1).1 ha
    refine ⟨x, ?_⟩
    change (Stacks.Conormal.conormalAlgebra (incl t (n + 1))).localMap V
      (isClosedImmersion_resLE_incl t (n + 1) V.1) (n + 1) ⟨_, kernelι_mem q t hcart n V x⟩ = _
    exact congrArg ((Stacks.Conormal.conormalAlgebra (incl t (n + 1))).localMap V
      (isClosedImmersion_resLE_incl t (n + 1) V.1) (n + 1)) (Subtype.ext hx)

/-- **The transition ideal is the direct image of a conormal piece.** -/
def conormalTransitionIdealIso (n : ℕ) :
    transitionIdeal t n ≅ (Scheme.Modules.pushforward (incl t (n + 1))).obj
      ((conormalAlg t (n + 1)).piece ((n + 1 : ℕ) : ℤ)) :=
  haveI := isIso_idealConormalHom q t hcart n
  asIso (idealConormalHom q t hcart n)

end Stacks.AdicTower

end
