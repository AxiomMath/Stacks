module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedConnectionBaseChange
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedConnectionCurvature
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDeRhamHorizontal
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDividedPowerForms
public import StacksFrontier.AlgebraicGeometry.Crystalline.TaylorRoundTrip

/-!
# The curvature of a completed connection: linearity, base change and transport

The curvature of a completed connection `∇ : M → M ⊗̂_D Ω¹` is the composite
`M --∇--> M ⊗̂_D Ω¹ --∇--> M ⊗̂_D Ω²` whose vanishing is
`Crystalline.CompletedDeRham.IsCurvatureZero`.

## Main results

* `Crystalline.CompletedDeRham.differential_one_nabla_smul`: the curvature is `D`-linear, as soon
  as the wedge product is anticommutative on one-forms and `d (d c) = 0`.
* `Crystalline.CompletedDeRham.isCurvatureZero_baseChange`: base change along `D → D'` preserves
  vanishing curvature.
* `Crystalline.CompletedDeRham.isCurvatureZero_iff_of_horizontalEquiv`: vanishing curvature
  transports along a horizontal `D`-linear equivalence.
* `Crystalline.completedDividedPowerWedgeOnRing_one_add_swap` and
  `Crystalline.completedDividedPowerDeRham_one_differentialOnRing`: the completed divided power
  forms of [Stacks, Tag 07HZ], read over the ring itself, have a wedge product anticommutative
  on one-forms and satisfy `d (d c) = 0`.

## References

* [Stacks Project, Tag 07I0](https://stacks.math.columbia.edu/tag/07I0)
* [Stacks Project, Lemma 60.17.5, Tag 07L5](https://stacks.math.columbia.edu/tag/07L5)
-/

@[expose] public section

open DividedPowers
open scoped TensorProduct

universe u v w

namespace Crystalline

namespace CompletedDeRham

/-! ### The curvature is `D`-linear -/

section Linear

variable (p : ℕ) (D : Type u) [CommRing D] (Om : ℕ → Type v) [∀ i, AddCommGroup (Om i)]
  [∀ i, Module D (Om i)] (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1)) {dmap : D → Om 1} (M : Type w) [AddCommGroup M]
  [Module D M] (nabla : CompletedConnection p D (Om 1) dmap M)
  (hleib : IsGradedLeibniz D Om wedge deRham dmap)

/-- **The degree-one differential on a multiple, uncompleted**: on `M ⊗_D Ω¹_D`,
`∇(c y) = c ∇ y + y ∧ d c`, the second term being `m ⊗ η ↦ m ⊗ (η ∧ d c)`. -/
public theorem rawDifferential_one_smul_add_wedgeFlip (c : D) (y : M ⊗[D] Om 1) :
    rawDifferential p D Om wedge deRham M nabla hleib 1 (c • y) =
      c • rawDifferential p D Om wedge deRham M nabla hleib 1 y +
        toCompletedTensor p D (Om (1 + 1)) M
          (LinearMap.lTensor M ((wedge 1).flip (dmap c)) y) := by
  induction y using TensorProduct.inductionOn with
  | tmul m ω =>
    rw [TensorProduct.smul_tmul', rawDifferential_tmul, rawDifferential_tmul, nabla.leibniz,
      map_add, LinearMap.map_smul, wedgeMap_of_tmul, LinearMap.lTensor_tmul,
      LinearMap.flip_apply, ← TensorProduct.smul_tmul', LinearMap.map_smul, smul_add]
    abel
  | add y y' hy hy' =>
    rw [smul_add, map_add, hy, hy']
    simp only [map_add, smul_add]
    abel

/-- **The degree-one differential on a multiple**: on `M ⊗̂_D Ω¹_D`,
`∇(c y) = c ∇ y + y ∧ d c`, the second term being the completion of
`m ⊗ η ↦ m ⊗ (η ∧ d c)`. -/
public theorem differential_one_smul_add_wedgeFlip (c : D) (y : CompletedTensor p D (Om 1) M) :
    differential p D Om wedge deRham M nabla hleib 1 (c • y) =
      c • differential p D Om wedge deRham M nabla hleib 1 y +
        AdicCompletion.map (pAdicIdeal (A := D) p)
          (LinearMap.lTensor M ((wedge 1).flip (dmap c))) y := by
  refine AdicCompletion.ext fun n ↦ ?_
  obtain ⟨y0, hy0⟩ := Submodule.Quotient.mk_surjective
    ((pAdicIdeal (A := D) p) ^ n • ⊤ : Submodule D (M ⊗[D] Om 1)) (y.val n)
  have hval : (c • y).val n = Submodule.Quotient.mk (c • y0) := by
    rw [AdicCompletion.val_smul_apply, ← hy0, Submodule.Quotient.mk_smul]
  rw [differential_val, hval, levelDifferential_mk, rawDifferential_one_smul_add_wedgeFlip,
    AdicCompletion.val_add_apply, AdicCompletion.val_add_apply, AdicCompletion.val_smul_apply,
    AdicCompletion.val_smul_apply, differential_val, AdicCompletion.map_val_apply, ← hy0,
    levelDifferential_mk, LinearMap.reduceModIdeal_apply]
  rfl

/-- **The curvature of a completed connection is `D`-linear**:
`∇(∇(c x)) = c · ∇(∇ x)`, for a wedge product that is anticommutative on one-forms and a
differential with `d (d c) = 0`. -/
public theorem differential_one_nabla_smul
    (hanti : ∀ η ζ : Om 1, wedge 1 η ζ + wedge 1 ζ η = 0)
    (hdd : ∀ c : D, deRham 1 (dmap c) = 0) (c : D) (x : M) :
    differential p D Om wedge deRham M nabla hleib 1 (nabla (c • x)) =
      c • differential p D Om wedge deRham M nabla hleib 1 (nabla x) := by
  have key : ∀ z : CompletedTensor p D (Om 1) M,
      AdicCompletion.map (pAdicIdeal (A := D) p)
          (LinearMap.lTensor M ((wedge 1).flip (dmap c))) z +
        wedgeMap p D Om wedge M 1 (dmap c) z = 0 := by
    intro z
    have hsum : (wedge 1).flip (dmap c) + wedge 1 (dmap c) = 0 :=
      LinearMap.ext fun η ↦ by
        rw [LinearMap.add_apply, LinearMap.flip_apply, LinearMap.zero_apply]
        exact hanti η (dmap c)
    change AdicCompletion.map (pAdicIdeal (A := D) p)
          (LinearMap.lTensor M ((wedge 1).flip (dmap c))) z +
        AdicCompletion.map (pAdicIdeal (A := D) p) (LinearMap.lTensor M (wedge 1 (dmap c))) z =
      0
    rw [← LinearMap.add_apply, ← _root_.map_add (AdicCompletion.map (pAdicIdeal (A := D) p)),
      ← LinearMap.lTensor_add, hsum, LinearMap.lTensor_zero, _root_.map_zero,
      LinearMap.zero_apply]
  rw [nabla.leibniz c x, map_add, differential_one_smul_add_wedgeFlip, differential_of_tmul,
    hdd c, TensorProduct.tmul_zero, map_zero, add_zero, add_assoc, key, add_zero]

end Linear

/-! ### Base change preserves vanishing curvature -/

section BaseChange

variable (p : ℕ) (D : Type u) [CommRing D] (D' : Type u) [CommRing D'] [Algebra D D']
  (M : Type u) [AddCommGroup M] [Module D M]
  (Om : ℕ → Type u) [∀ i, AddCommGroup (Om i)] [∀ i, Module D (Om i)]
  (Om' : ℕ → Type u) [∀ i, AddCommGroup (Om' i)] [∀ i, Module D' (Om' i)]
  (psi : ∀ i, Om i →ₛₗ[algebraMap D D'] Om' i)
  (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1))
  (wedge' : ∀ i, Om' i →ₗ[D'] Om' 1 →ₗ[D'] Om' (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1)) (deRham' : ∀ i, Om' i →+ Om' (i + 1))
  {d : D → Om 1} (d' : D' → Om' 1) (nabla : CompletedConnection p D (Om 1) d M)
  (hd'add : ∀ x y : D', d' (x + y) = d' x + d' y)
  (hd'leib : ∀ x y : D', d' (x * y) = x • d' y + y • d' x)
  (hpsi1 : ∀ x : D, psi 1 (d x) = d' (algebraMap D D' x))
  (hleib : IsGradedLeibniz D Om wedge deRham d)
  (hleib' : IsGradedLeibniz D' Om' wedge' deRham' d')
  (hpsi_wedge : ∀ (i : ℕ) (omega : Om i) (eta : Om 1),
    psi (i + 1) (wedge i omega eta) = wedge' i (psi i omega) (psi 1 eta))
  (hpsi_deRham : ∀ (i : ℕ) (omega : Om i),
    psi (i + 1) (deRham i omega) = deRham' i (psi i omega))

include hpsi_wedge hpsi_deRham in
/-- **Base change preserves vanishing curvature.**  If the curvature of `∇` on `M` vanishes,
so does the curvature of the base-changed connection
`Crystalline.CompletedConnection.baseChange` on `M ⊗̂_D D'`, provided the target forms have an
anticommutative wedge on one-forms and `d' (d' c) = 0`. -/
public theorem isCurvatureZero_baseChange
    (hanti' : ∀ η ζ : Om' 1, wedge' 1 η ζ + wedge' 1 ζ η = 0)
    (hdd' : ∀ c : D', deRham' 1 (d' c) = 0)
    (hK : IsCurvatureZero p D Om wedge deRham M nabla hleib) :
    IsCurvatureZero p D' Om' wedge' deRham' (CompletedConnection.baseChangeCarrier p D D' M)
      (CompletedConnection.baseChange p D D' M (Om 1) (Om' 1) d' (psi 1) nabla hd'add hd'leib
        hpsi1) hleib' := by
  set nabla' := CompletedConnection.baseChange p D D' M (Om 1) (Om' 1) d' (psi 1) nabla hd'add
    hd'leib hpsi1 with hnabla'
  have hlin := differential_one_nabla_smul p D' Om' wedge' deRham'
    (CompletedConnection.baseChangeCarrier p D D' M) nabla' hleib' hanti' hdd'
  have h := CompletedConnection.baseChangeCarrier_ext p D D' M (RingHom.id D')
    (inferInstance : IsHausdorff (pAdicIdeal (A := D') p)
      (CompletedTensor p D' (Om' (1 + 1)) (CompletedConnection.baseChangeCarrier p D D' M)))
    (ψ := (differential p D' Om' wedge' deRham' (CompletedConnection.baseChangeCarrier p D D' M)
      nabla' hleib' 1).comp (nablaHom p D' Om' _ nabla'))
    (ψ' := 0) (fun c' x ↦ hlin c' x) (fun c' x ↦ by simp) (fun m ↦ ?_)
  · exact fun x ↦ DFunLike.congr_fun h x
  · have hcomm := DFunLike.congr_fun (baseChangeTerm_comm p D D' M Om Om' psi wedge wedge' deRham
      deRham' d' nabla hd'add hd'leib hpsi1 hleib hleib' hpsi_wedge hpsi_deRham 1) (nabla m)
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, hK m, map_zero] at hcomm
    rwa [AddMonoidHom.comp_apply, nablaHom_apply, hnabla', CompletedConnection.baseChange_inclusion,
      AddMonoidHom.zero_apply]

end BaseChange

/-! ### Transport along a horizontal equivalence -/

section Horizontal

variable (p : ℕ) (D : Type u) [CommRing D] (Om : ℕ → Type v) [∀ i, AddCommGroup (Om i)]
  [∀ i, Module D (Om i)] (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1)) {dmap : D → Om 1} (M N : Type w) [AddCommGroup M]
  [Module D M] [AddCommGroup N] [Module D N] (e : M ≃ₗ[D] N)
  (nablaM : CompletedConnection p D (Om 1) dmap M)
  (nablaN : CompletedConnection p D (Om 1) dmap N)
  (hleib : IsGradedLeibniz D Om wedge deRham dmap)
  (hnabla : ∀ m : M, nablaN (e m) =
    AdicCompletion.map (pAdicIdeal (A := D) p)
      (TensorProduct.map e.toLinearMap (LinearMap.id (R := D) (M := Om 1))) (nablaM m))

include hnabla in
/-- **Vanishing curvature transports along a horizontal `D`-linear equivalence**, in both
directions. -/
public theorem isCurvatureZero_iff_of_horizontalEquiv :
    IsCurvatureZero p D Om wedge deRham M nablaM hleib ↔
      IsCurvatureZero p D Om wedge deRham N nablaN hleib := by
  have hcomm : ∀ m : M, differential p D Om wedge deRham N nablaN hleib 1 (nablaN (e m)) =
      horizontalTerm p D M N Om (e : M →ₗ[D] N) (1 + 1)
        (differential p D Om wedge deRham M nablaM hleib 1 (nablaM m)) := fun m ↦ by
    rw [hnabla m]
    exact horizontalTerm_comm p D M N Om (e : M →ₗ[D] N) wedge deRham nablaM nablaN hleib
      hnabla 1 (nablaM m)
  refine ⟨fun hM y ↦ ?_, fun hN m ↦ (horizontalTerm_bijective p D M N Om e (1 + 1)).1 ?_⟩
  · obtain ⟨m, rfl⟩ := e.surjective y
    rw [hcomm m, hM m, map_zero]
  · rw [← hcomm m, hN (e m), map_zero]

include hnabla in
/-- **Vanishing curvature transports along a horizontal `D`-linear equivalence**: if the
curvature of `∇_M` vanishes and `e : M ≃ N` is horizontal, the curvature of `∇_N` vanishes. -/
public theorem isCurvatureZero_of_horizontalEquiv
    (hM : IsCurvatureZero p D Om wedge deRham M nablaM hleib) :
    IsCurvatureZero p D Om wedge deRham N nablaN hleib :=
  (isCurvatureZero_iff_of_horizontalEquiv p D Om wedge deRham M N e nablaM nablaN hleib
    hnabla).1 hM

end Horizontal

end CompletedDeRham

/-! ### The completed divided power forms -/

section DividedPower

variable (p : ℕ) (A : Type u) [CommRing A] {B : Type v} [CommRing B] [Algebra A B]
  {J : Ideal B} (hJ : DividedPowers J)

/-- **The wedge product of divided power one-forms is anticommutative**:
`η ∧ ζ + ζ ∧ η = 0`. -/
public theorem dividedPowerWedge_one_add_swap
    (w e : dividedPowerDifferentialForms (A := A) hJ 1) :
    dividedPowerWedge hJ 1 w e + dividedPowerWedge hJ 1 e w = 0 := by
  refine Subtype.ext ?_
  rw [Submodule.coe_add, dividedPowerWedge_apply, dividedPowerWedge_apply, leftWedge_coe,
    leftWedge_coe, Submodule.coe_zero, Koszul.coe_oneEquiv w, Koszul.coe_oneEquiv e]
  exact ExteriorAlgebra.ι_add_mul_swap _ _

/-- **The universal divided power one-form is closed**: `d (d c) = 0`. -/
public theorem dividedPowerDeRham_one_dividedPowerOneForm (c : B) :
    dividedPowerDeRham hJ 1 (dividedPowerOneForm A hJ c) = 0 := by
  have h := dividedPowerDeRham_generator (A := A) hJ 0 fun _ : Fin 1 ↦ c
  have hc : dividedPowerOneForm A hJ c = dividedPowerDeRham hJ 0
      (c • exteriorPower.ιMulti B 0
        (fun j : Fin 0 ↦ dividedPowerDifferential (A := A) hJ ((fun _ : Fin 1 ↦ c) j.succ))) := by
    rw [h, dividedPowerOneForm_apply, LinearEquiv.symm_apply_eq, exteriorPower.oneEquiv_ιMulti]
  exact hc ▸ dividedPowerDeRham_dividedPowerDeRham hJ 0 _

/-- **The wedge product of the completed divided power one-forms, over the ring itself, is
anticommutative**: `η ∧ ζ + ζ ∧ η = 0`, for the forms of [Stacks, Tag 07HZ]. -/
public theorem completedDividedPowerWedgeOnRing_one_add_swap
    (η ζ : completedDividedPowerForms p A hJ 1) :
    completedDividedPowerWedgeOnRing p A hJ 1 η ζ +
      completedDividedPowerWedgeOnRing p A hJ 1 ζ η = 0 := by
  refine AdicCompletion.ext fun n ↦ ?_
  obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective
    (pAdicIdeal (A := B) p ^ n • ⊤ :
      Submodule B (dividedPowerDifferentialForms (A := A) hJ 1)) (η.val n)
  obtain ⟨e, he⟩ := Submodule.Quotient.mk_surjective
    (pAdicIdeal (A := B) p ^ n • ⊤ :
      Submodule B (dividedPowerDifferentialForms (A := A) hJ 1)) (ζ.val n)
  rw [AdicCompletion.val_add_apply, completedDividedPowerWedgeOnRing_apply,
    completedDividedPowerWedgeOnRing_apply,
    completedDividedPowerWedge_val p A hJ 1 n η ζ w e hw.symm he.symm,
    completedDividedPowerWedge_val p A hJ 1 n ζ η e w he.symm hw.symm,
    ← Submodule.Quotient.mk_add, dividedPowerWedge_one_add_swap, Submodule.Quotient.mk_zero]
  exact (AdicCompletion.val_zero_apply _ _ n).symm

/-- **The universal differential of the ring is closed in the completed divided power forms**:
`d (d c) = 0`, for the forms of [Stacks, Tag 07HZ]. -/
public theorem completedDividedPowerDeRham_one_differentialOnRing (c : B) :
    completedDividedPowerDeRham p A hJ 1 (completedDividedPowerDifferentialOnRing p A hJ c) =
      0 := by
  rw [completedDividedPowerDifferentialOnRing_eq, completedDividedPowerDeRham_of,
    dividedPowerDeRham_one_dividedPowerOneForm, _root_.map_zero]

end DividedPower

end Crystalline

end
