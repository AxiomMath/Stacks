module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedBaseChangeCancel
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.BaseChangeConnectionsHorizontal
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.CompletedPoincareCurvature

/-!
# The base-change connections on `M(b)` are integrable

`Crystalline.CosimplicialCompletedModule.baseChangeConnection` puts on each `M(b)` the base change
of a connection `∇` on `M(0)` along the coprojection `σ_b : ⦋0⦌ ⟶ ⦋b⦌`.  This module proves that
it is integrable — its curvature `∇ ∘ ∇ : M(b) → M(b) ⊗̂ Ω²_{D(b)}` vanishes — as soon as `∇` is,
so that `M(b) ⊗^∧_{D(b)} Ω^*_{D(b)}` is a complex, the field `isSquareZero` of
`Crystalline.CosimplicialCompletedPair`.

The argument is the classical one.  The curvature of a connection is linear over the base ring
(`Crystalline.CompletedDeRham.differential_connection_smul`, from the graded Leibniz rule and the
alternation of the wedge on one-forms), and the curvature of `∇_b` vanishes on the image of `M(0)`
because the transition `M(0) ⟶ M(b)` of `σ_b` is horizontal and commutes with the de Rham
differentials.  A linear map out of the completed base change `(D(b) ⊗_{D(0)} M(0))^∧` vanishing
on `M(0)` is zero.

## Main results

* `Crystalline.CompletedDeRham.differential_smul` — `d (c y) = c d y + y ∧ d c`.
* `Crystalline.CompletedDeRham.differential_connection_smul` — the curvature is linear.
* `Crystalline.CosimplicialCompletedModule.hasIntegrableConnection_baseChangeConnection` —
  **`∇_b` is integrable** when `∇` is.
* `Crystalline.CosimplicialCompletedModule.isSquareZero_baseChangeConnection` — hence
  `M(b) ⊗^∧_{D(b)} Ω^*_{D(b)}` is a complex.

## References

* [Stacks Project, Remark 60.5.4, Tag 07I0](https://stacks.math.columbia.edu/tag/07I0)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
-/

@[expose] public noncomputable section

universe u v w

open CategoryTheory Simplicial
open scoped TensorProduct

namespace Crystalline

open DividedPowers

namespace CompletedDeRham

section Smul

variable (p : ℕ) (D : Type u) [CommRing D] (Om : ℕ → Type v) [∀ i, AddCommGroup (Om i)]
  [∀ i, Module D (Om i)] (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1)) {dmap : D → Om 1} (M : Type w) [AddCommGroup M]
  [Module D M] (nabla : CompletedConnection p D (Om 1) dmap M)
  (hleib : IsGradedLeibniz D Om wedge deRham dmap)

/-- Exterior multiplication by a scalar multiple of a form is the scalar multiple. -/
theorem wedgeMap_smul_form (i : ℕ) (c : D) (ω : Om i) (z : CompletedTensor p D (Om 1) M) :
    wedgeMap p D Om wedge M i (c • ω) z = c • wedgeMap p D Om wedge M i ω z := by
  let F : CompletedTensor p D (Om 1) M →+ CompletedTensor p D (Om (i + 1)) M :=
    (wedgeMap p D Om wedge M i (c • ω)).toAddMonoidHom
  let G : CompletedTensor p D (Om 1) M →+ CompletedTensor p D (Om (i + 1)) M :=
    (AddMonoidHom.mk' (fun x => c • x) (fun x y => smul_add c x y)).comp
      (wedgeMap p D Om wedge M i ω).toAddMonoidHom
  suffices h : F = G from DFunLike.congr_fun h z
  refine completedTensor_addMonoidHom_ext p fun m η => ?_
  change wedgeMap p D Om wedge M i (c • ω) (toCompletedTensor p D (Om 1) M (m ⊗ₜ η)) =
    c • wedgeMap p D Om wedge M i ω (toCompletedTensor p D (Om 1) M (m ⊗ₜ η))
  rw [wedgeMap_of_tmul, wedgeMap_of_tmul, LinearMap.map_smul₂, TensorProduct.tmul_smul, map_smul]

include hleib in
/-- **The differential of a scalar multiple**: `d (c y) = c d y + y ∧ d c`, where `y ∧ d c` is
`1_M ⊗ (− ∧ d c)`. -/
theorem differential_smul (i : ℕ) (c : D) (y : CompletedTensor p D (Om i) M) :
    differential p D Om wedge deRham M nabla hleib i (c • y) =
      c • differential p D Om wedge deRham M nabla hleib i y +
        completedLTensor p D M ((wedge i).flip (dmap c)) y := by
  let F : CompletedTensor p D (Om i) M →+ CompletedTensor p D (Om (i + 1)) M :=
    (differential p D Om wedge deRham M nabla hleib i).comp
      (AddMonoidHom.mk' (fun x => c • x) (fun x y => smul_add c x y))
  let G : CompletedTensor p D (Om i) M →+ CompletedTensor p D (Om (i + 1)) M :=
    (AddMonoidHom.mk' (fun x => c • x) (fun x y => smul_add c x y)).comp
        (differential p D Om wedge deRham M nabla hleib i) +
      completedLTensor p D M ((wedge i).flip (dmap c))
  suffices h : F = G from DFunLike.congr_fun h y
  refine completedTensor_addMonoidHom_ext p fun m ω => ?_
  change differential p D Om wedge deRham M nabla hleib i
      (c • toCompletedTensor p D (Om i) M (m ⊗ₜ ω)) =
    c • differential p D Om wedge deRham M nabla hleib i
        (toCompletedTensor p D (Om i) M (m ⊗ₜ ω)) +
      completedLTensor p D M ((wedge i).flip (dmap c)) (toCompletedTensor p D (Om i) M (m ⊗ₜ ω))
  rw [← map_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul, differential_of_tmul,
    differential_of_tmul, hleib i c ω, wedgeMap_smul_form, TensorProduct.tmul_add, map_add,
    completedLTensor_toCompletedTensor_tmul, LinearMap.flip_apply]
  simp only [TensorProduct.tmul_smul, map_smul, smul_add]
  abel

/-- Two forms maps adding up to zero give completed maps adding up to zero. -/
theorem completedLTensor_add_eq_zero {X Y : Type*} [AddCommGroup X] [Module D X] [AddCommGroup Y]
    [Module D Y] (f g : X →ₗ[D] Y) (hfg : ∀ x, f x + g x = 0) (y : CompletedTensor p D X M) :
    completedLTensor p D M f y + completedLTensor p D M g y = 0 := by
  have h : completedLTensor p D M f + completedLTensor p D M g = 0 := by
    refine completedTensor_addMonoidHom_ext p fun m x => ?_
    change completedLTensor p D M f (toCompletedTensor p D X M (m ⊗ₜ x)) +
        completedLTensor p D M g (toCompletedTensor p D X M (m ⊗ₜ x)) = 0
    rw [completedLTensor_toCompletedTensor_tmul, completedLTensor_toCompletedTensor_tmul,
      ← map_add, ← TensorProduct.tmul_add, hfg, TensorProduct.tmul_zero, map_zero]
  exact DFunLike.congr_fun h y

include hleib in
/-- **The curvature of a connection is linear**: `∇(∇(c m)) = c ∇(∇ m)`, given that the wedge of
one-forms is anticommutative and that `d (d c) = 0`. -/
theorem differential_connection_smul (hanti : ∀ η ζ : Om 1, wedge 1 η ζ + wedge 1 ζ η = 0)
    (hdd : ∀ c : D, deRham 1 (dmap c) = 0) (c : D) (m : M) :
    differential p D Om wedge deRham M nabla hleib 1 (nabla (c • m)) =
      c • differential p D Om wedge deRham M nabla hleib 1 (nabla m) := by
  rw [CompletedConnection.leibniz, map_add, differential_smul, differential_of_tmul, hdd,
    TensorProduct.tmul_zero, map_zero, add_zero, add_assoc]
  have h := completedLTensor_add_eq_zero p D M ((wedge 1).flip (dmap c)) (wedge 1 (dmap c))
    (fun η => (add_comm _ _).trans (hanti (dmap c) η)) (nabla m)
  change c • differential p D Om wedge deRham M nabla hleib 1 (nabla m) +
      (completedLTensor p D M ((wedge 1).flip (dmap c)) (nabla m) +
        completedLTensor p D M (wedge 1 (dmap c)) (nabla m)) = _
  rw [h, add_zero]

end Smul

end CompletedDeRham

namespace CosimplicialCompletedModule

variable {A : Type u} [CommRing A] {E : CosimplicialDPAlgebra.{u, v} A} {p : ℕ}
  (V : CosimplicialCompletedModule.{u, v, v} E p)
  (nabla : CompletedConnection p (E.completedRing p 0) (E.forms p 1 0) (E.differential p 0)
    (V.carrier 0))
  (beta : ∀ b : ℕ, letI := E.coprojectionAlgebra p b
    CompletedConnection.baseChangeCarrier p (E.completedRing p 0) (E.completedRing p b)
      (V.carrier 0) ≃ₗ[E.completedRing p b] V.carrier b)
  (hbeta : ∀ (b : ℕ) (x : E.completedRing p b) (m : V.carrier 0),
    letI := E.coprojectionAlgebra p b
    beta b (AdicCompletion.of (pAdicIdeal (A := E.completedRing p b) p)
        (E.completedRing p b ⊗[E.completedRing p 0] V.carrier 0) (x ⊗ₜ[E.completedRing p 0] m)) =
      x • V.map (CosimplicialDPAlgebra.coprojection b) m)

/-- The transition map of the double complex is the semilinear comparison of the transition of
the modules and the transition of the forms. -/
theorem tensorMap_eq_comparisonValues {m n : SimplexCategory} (φ : m ⟶ n) (a : ℕ)
    (x : V.obj a m.len) :
    V.tensorMap φ a x = CompletedDeRham.comparisonValues p (E.completedRing p m.len)
      (E.completedRing p n.len) (E.completedRingMap p φ) (V.carrier m.len) (V.carrier n.len)
      (V.map φ) (fun i => E.forms p i m.len) (fun i => E.forms p i n.len)
      (fun i => E.formsMapCompleted p φ i) a x :=
  rfl

/-- **A horizontal transition map commutes with the de Rham differentials**: if
`∇' (M(φ) y) = M(φ)_* (∇ y)`, then the transition of the double complex is a chain map. -/
theorem differential_tensorMap_of_horizontal {m n : SimplexCategory}
    (nablam : CompletedConnection p (E.completedRing p m.len) (E.forms p 1 m.len)
      (E.differential p m.len) (V.carrier m.len))
    (nablan : CompletedConnection p (E.completedRing p n.len) (E.forms p 1 n.len)
      (E.differential p n.len) (V.carrier n.len)) (φ : m ⟶ n)
    (h : ∀ y, nablan (V.map φ y) = V.tensorMap φ 1 (nablam y)) (a : ℕ) (x : V.obj a m.len) :
    CompletedDeRham.differential p (E.completedRing p n.len) (fun i => E.forms p i n.len)
        (E.wedge p n.len) (E.deRham p n.len) (V.carrier n.len) nablan
        (E.isGradedLeibniz p n.len) a (V.tensorMap φ a x) =
      V.tensorMap φ (a + 1) (CompletedDeRham.differential p (E.completedRing p m.len)
        (fun i => E.forms p i m.len) (E.wedge p m.len) (E.deRham p m.len) (V.carrier m.len)
        nablam (E.isGradedLeibniz p m.len) a x) :=
  CompletedDeRham.differential_comparisonValues p (E.completedRing p m.len)
    (E.completedRing p n.len) (E.completedRingMap p φ) (V.carrier m.len) (V.carrier n.len)
    (V.map φ) (fun i => E.forms p i m.len) (fun i => E.forms p i n.len)
    (fun i => E.formsMapCompleted p φ i) (E.wedge p m.len) (E.wedge p n.len)
    (E.deRham p m.len) (E.deRham p n.len) nablam nablan (E.isGradedLeibniz p m.len)
    (E.isGradedLeibniz p n.len) (fun i ω η => E.formsMap_wedge p φ i ω η)
    (fun i ω => E.formsMap_deRham p φ i ω) h a x

/-- The wedge of one-forms of a cosimplicial degree is anticommutative. -/
theorem wedge_one_anticomm (b : ℕ) (η ζ : E.forms p 1 b) :
    E.wedge p b 1 η ζ + E.wedge p b 1 ζ η = 0 := by
  have h := CompletedDeRham.IsGradedExterior.wedge_comm (h := E.isGradedExterior p b) (i := 0)
    (ω := E.unitZeroForm p b) (η := η) (ζ := ζ)
  have hu : ∀ ξ : E.forms p 1 b, E.wedge p b 0 (E.unitZeroForm p b) ξ = ξ :=
    completedDividedPowerWedge_completedUnitZeroForm p A (E.dividedPowers b)
  rw [hu, hu] at h
  exact h

include hbeta in
/-- **The curvature of `∇_b` vanishes on the image of `M(0)`**: the coprojection is horizontal
and commutes with the de Rham differentials, and `∇` is integrable. -/
theorem curvature_map_coprojection
    (hint : CompletedDeRham.HasIntegrableConnection p (E.completedRing p 0)
      (fun a => E.forms p a 0) (E.wedge p 0) (E.deRham p 0) (V.carrier 0) nabla
      (E.isGradedLeibniz p 0)) (b : ℕ) (m : V.carrier 0) :
    CompletedDeRham.differential p (E.completedRing p b) (fun a => E.forms p a b) (E.wedge p b)
        (E.deRham p b) (V.carrier b) (V.baseChangeConnection nabla beta b)
        (E.isGradedLeibniz p b) 1
        (V.baseChangeConnection nabla beta b (V.map (CosimplicialDPAlgebra.coprojection b) m)) =
      0 := by
  have h1 := V.differential_tensorMap_of_horizontal nabla (V.baseChangeConnection nabla beta b)
    (CosimplicialDPAlgebra.coprojection b)
    (fun y => V.baseChangeConnection_map_coprojection nabla beta hbeta b y) 1 (nabla m)
  have h2 : CompletedDeRham.differential p (E.completedRing p (⦋0⦌ : SimplexCategory).len)
      (fun i => E.forms p i (⦋0⦌ : SimplexCategory).len) (E.wedge p (⦋0⦌ : SimplexCategory).len)
      (E.deRham p (⦋0⦌ : SimplexCategory).len) (V.carrier (⦋0⦌ : SimplexCategory).len) nabla
      (E.isGradedLeibniz p (⦋0⦌ : SimplexCategory).len) 1 (nabla m) = 0 := hint m
  rw [h2, map_zero, ← V.baseChangeConnection_map_coprojection nabla beta hbeta b m] at h1
  exact h1

include hbeta in
/-- **The base-change connection `∇_b` is integrable as soon as `∇` is.** -/
theorem hasIntegrableConnection_baseChangeConnection
    (hint : CompletedDeRham.HasIntegrableConnection p (E.completedRing p 0)
      (fun a => E.forms p a 0) (E.wedge p 0) (E.deRham p 0) (V.carrier 0) nabla
      (E.isGradedLeibniz p 0)) (b : ℕ) :
    CompletedDeRham.HasIntegrableConnection p (E.completedRing p b)
      (fun a => E.forms p a b) (E.wedge p b) (E.deRham p b) (V.carrier b)
      (V.baseChangeConnection nabla beta b) (E.isGradedLeibniz p b) := by
  let := E.coprojectionAlgebra p b
  intro x
  rw [← (beta b).apply_symm_apply x]
  generalize (beta b).symm x = y
  let Kc : CompletedConnection.baseChangeCarrier p (E.completedRing p 0) (E.completedRing p b)
      (V.carrier 0) →+ CompletedTensor p (E.completedRing p b) (E.forms p (1 + 1) b)
        (V.carrier b) :=
    AddMonoidHom.mk' (fun y => CompletedDeRham.differential p (E.completedRing p b)
        (fun a => E.forms p a b) (E.wedge p b) (E.deRham p b) (V.carrier b)
        (V.baseChangeConnection nabla beta b) (E.isGradedLeibniz p b) 1
        (V.baseChangeConnection nabla beta b (beta b y)))
      (fun y z => by simp only [map_add, CompletedConnection.map_add])
  refine eq_zero_of_baseChangeInclusion p (RingHom.id _) Kc (fun c z => ?_) (fun m => ?_) y
  · change CompletedDeRham.differential p (E.completedRing p b)
        (fun a => E.forms p a b) (E.wedge p b) (E.deRham p b) (V.carrier b)
        (V.baseChangeConnection nabla beta b) (E.isGradedLeibniz p b) 1
        (V.baseChangeConnection nabla beta b (beta b (c • z))) = c • Kc z
    rw [map_smul]
    exact CompletedDeRham.differential_connection_smul p _ _ _ _ _ _ _
      (wedge_one_anticomm b) (E.deRham_differential p b) c _
  · change CompletedDeRham.differential p (E.completedRing p b)
        (fun a => E.forms p a b) (E.wedge p b) (E.deRham p b) (V.carrier b)
        (V.baseChangeConnection nabla beta b) (E.isGradedLeibniz p b) 1
        (V.baseChangeConnection nabla beta b
          (beta b (CompletedConnection.baseChangeInclusion p _ _ _ m))) = 0
    rw [CompletedConnection.baseChangeInclusion_apply, hbeta, one_smul]
    exact V.curvature_map_coprojection nabla beta hbeta hint b m

include hbeta in
/-- **`M(b) ⊗^∧_{D(b)} Ω^*_{D(b)}` is a complex** for the base-change connection, as soon as `∇`
is integrable. -/
theorem isSquareZero_baseChangeConnection
    (hint : CompletedDeRham.HasIntegrableConnection p (E.completedRing p 0)
      (fun a => E.forms p a 0) (E.wedge p 0) (E.deRham p 0) (V.carrier 0) nabla
      (E.isGradedLeibniz p 0)) (b : ℕ) :
    CompletedDeRham.IsSquareZero p (E.completedRing p b) (fun a => E.forms p a b)
      (E.wedge p b) (E.deRham p b) (V.carrier b) (V.baseChangeConnection nabla beta b)
      (E.isGradedLeibniz p b) :=
  isSquareZero_completedDividedPowerForms_of_hasIntegrableConnection p A (E.dividedPowers b)
    (V.baseChangeConnection nabla beta b)
    (V.hasIntegrableConnection_baseChangeConnection nabla beta hbeta hint b)

end CosimplicialCompletedModule

end Crystalline

end
