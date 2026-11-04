module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.CompletedPoincareIntegrable
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.RelativePoincare

/-!
# The completed divided power Poincaré lemma for an integrable connection

Let `A` be a ring, let `(B, I, δ)` be a divided power ring which is an `A`-algebra, let
`P = B⟨x_w : w ∈ W⟩` be a divided power polynomial ring over `B` on an arbitrary family of
variables, and let `D`, resp. `D'`, be the `p`-adic completion of `B`, resp. `P`, with `Ω̂^i_D`,
resp. `Ω̂^i_{D'}`, the `p`-adic completion of `Ω^i_{B/A,δ}`, resp. `Ω^i_{P/A,δ}`.  This module
proves the second clause of [Stacks, Lemma 60.19.2, Tag 07LD]: for a `D`-module `M` with an
integrable connection `∇ : M → M ⊗̂_D Ω̂¹_D`, the map of de Rham complexes

`M ⊗̂_D Ω̂^*_D ⟶ M ⊗̂_D Ω̂^*_{D'}`

is a quasi-isomorphism, and in fact a homotopy equivalence.

## Integrability

The source's notion of integrability is that of [Stacks, Remark 60.5.4, Tag 07I0]: a connection
`∇` is integrable when the composite

`M --∇--> M ⊗̂_D Ω̂¹_D --∇--> M ⊗̂_D Ω̂²_D`

is zero, the second map being the extension `∇(m ⊗ ω) = ∇ m ∧ ω + m ⊗ d ω`.  That is
`Crystalline.CompletedDeRham.HasIntegrableConnection`.  It asks for nothing about coordinates or
a basis of `Ω̂¹_D`, which in the situation of the tag is an arbitrary module: the divided power
ideal `I` of `B` is arbitrary.

From it, the differentials of both de Rham complexes compose to zero in every degree:
`Crystalline.CompletedDeRham.isSquareZero_of_hasIntegrableConnection` proves this for any graded
family of forms carrying, besides the wedge with a one-form, a wedge with a two-form which is
associative and obeys the graded Leibniz rule.  The computation is the usual one,

`∇(∇(m ⊗ ω)) = ∇(∇ m ∧ ω) + ∇ m ∧ d ω = (∇ ∇ m) ∧ ω = 0`,

the only point being that `∇ m` lies in the completion, so the middle identity
`∇(y ∧ ω) = (∇ y) ∧ ω - y ∧ d ω` is first proved on the uncompleted tensor product and then
carried to the completion level by level.  The genuine completed divided power forms carry such a
wedge with a two-form, `Crystalline.completedDividedPowerWedgeTwo`, and the connection pushed into
the forms of `D'` is integrable as soon as the connection on `Ω̂¹_D` is.

## Main definitions

* `Crystalline.CompletedDeRham.HasIntegrableConnection` — integrability of a completed
  connection, in the sense of [Stacks, Tag 07I0].
* `Crystalline.completedDividedPowerWedgeTwo` — the wedge `Ω̂^i × Ω̂² → Ω̂^{i+2}` of completed
  divided power forms.
* `Crystalline.DividedPowerPolynomial.completedSourceDeRhamComplex`,
  `Crystalline.DividedPowerPolynomial.completedTargetDeRhamComplex` — the two de Rham complexes
  `M ⊗̂_D Ω̂^*_D` and `M ⊗̂_D Ω̂^*_{D'}`.
* `Crystalline.DividedPowerPolynomial.completedDeRhamComparison` — the canonical map between them,
  `1_M ⊗ ψ̂` in each degree.

## Main results

* `Crystalline.CompletedDeRham.isSquareZero_of_hasIntegrableConnection` — integrability makes the
  de Rham complex of a completed connection a complex.
* `Crystalline.DividedPowerPolynomial.exists_retraction_completedDeRhamComparison` — the comparison
  has a retraction `π` which is a map of complexes, with `π ∘ (1_M ⊗ ψ̂) = 1` and
  `(1_M ⊗ ψ̂) ∘ π` homotopic to the identity, degreewise.
* `Crystalline.DividedPowerPolynomial.quasiIso_completedDeRhamComparison` — **the second clause of
  [Stacks, Tag 07LD]**: the comparison is a quasi-isomorphism.

## References

* [Stacks Project, Lemma 60.19.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
* [Stacks Project, Remark 60.5.4, Tag 07I0](https://stacks.math.columbia.edu/tag/07I0)
-/

@[expose] public noncomputable section

open CategoryTheory
open DividedPowers
open scoped TensorProduct

universe u v w uA uB uM uW

namespace Crystalline

/-- Every level-`n` value of an adic completion is that of the image of an element of the module,
i.e. its class modulo `Iⁿ`. -/
private theorem exists_val_eq_mk {R : Type*} [CommRing R] {I : Ideal R} {X : Type*}
    [AddCommGroup X] [Module R X] (x : AdicCompletion I X) (n : ℕ) :
    ∃ z : X, x.val n = (AdicCompletion.of I X z).val n :=
  (Submodule.Quotient.mk_surjective _ (x.val n)).imp fun _ h ↦ h.symm

namespace CompletedDeRham

/-! ### Integrability and the square of the differential -/

section Curvature

variable (p : ℕ) (D : Type u) [CommRing D] (Om : ℕ → Type v) [∀ i, AddCommGroup (Om i)]
  [∀ i, Module D (Om i)] (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1)) {dmap : D → Om 1} (M : Type w) [AddCommGroup M]
  [Module D M] (nabla : CompletedConnection p D (Om 1) dmap M)
  (hleib : IsGradedLeibniz D Om wedge deRham dmap)

/-- **Integrability of a completed connection**, in the sense of
[Stacks, Remark 60.5.4, Tag 07I0]: the composite `M → M ⊗̂_D Ω¹ → M ⊗̂_D Ω²` of the connection
with its own extension `∇(m ⊗ ω) = ∇ m ∧ ω + m ⊗ d ω` to one-forms is zero. -/
def HasIntegrableConnection : Prop :=
  ∀ m : M, differential p D Om wedge deRham M nabla hleib 1 (nabla m) = 0

variable (wedgeTwo : ∀ i, Om i →ₗ[D] Om (1 + 1) →ₗ[D] Om (i + 1 + 1))

/-- The level-`n` value of the differential depends only on the level-`n` value of its argument;
the same holds for every `1_M ⊗ f`.  Together these let an identity of additive maps out of the
completed tensor product be checked on the image of the uncompleted one. -/
private theorem completedLTensor_val_congr {X Y : Type*} [AddCommGroup X] [Module D X]
    [AddCommGroup Y] [Module D Y] (f : X →ₗ[D] Y) (n : ℕ) (x y : CompletedTensor p D X M)
    (h : x.val n = y.val n) :
    (completedLTensor p D M f x).val n = (completedLTensor p D M f y).val n := by
  rw [completedLTensor_val, completedLTensor_val, h]

/-- `x ↦ ∇ x ∧ ω`, read as `1_M ⊗ (− ∧ ω)`, on the completed tensor product. -/
private theorem wedgeMap_eq_completedLTensor (i : ℕ) (ω : Om i)
    (x : CompletedTensor p D (Om 1) M) :
    wedgeMap p D Om wedge M i ω x = completedLTensor p D M (wedge i ω) x :=
  rfl

/-- Wedging with a one-form and then with a fixed `i`-form is wedging with their product. -/
private theorem completedLTensor_wedgeTwo_wedgeMap
    (hassoc : ∀ (i : ℕ) (ω : Om i) (η ξ : Om 1),
      wedge (i + 1) (wedge i ω η) ξ = wedgeTwo i ω (wedge 1 η ξ))
    (i : ℕ) (ω : Om i) (η : Om 1) (x : CompletedTensor p D (Om 1) M) :
    completedLTensor p D M (wedgeTwo i ω) (wedgeMap p D Om wedge M 1 η x) =
      wedgeMap p D Om wedge M (i + 1) (wedge i ω η) x := by
  have h : wedgeTwo i ω ∘ₗ wedge 1 η = wedge (i + 1) (wedge i ω η) :=
    LinearMap.ext fun ξ ↦ (hassoc i ω η ξ).symm
  rw [wedgeMap_eq_completedLTensor, wedgeMap_eq_completedLTensor, completedLTensor_comp, h]

include hleib in
/-- **The differential of `y ∧ ω`**: `∇(y ∧ ω) = (∇ y) ∧ ω - y ∧ d ω` for `y ∈ M ⊗̂_D Ω¹` and an
`i`-form `ω`, the wedge `(∇ y) ∧ ω` being the wedge of a two-form with `ω`.  This is checked on
the image of the uncompleted tensor product, where it is the associativity of the wedge and the
graded Leibniz rule, and carried to the completion level by level. -/
theorem differential_wedgeMap
    (hassoc : ∀ (i : ℕ) (ω : Om i) (η ξ : Om 1),
      wedge (i + 1) (wedge i ω η) ξ = wedgeTwo i ω (wedge 1 η ξ))
    (hleibTwo : ∀ (i : ℕ) (ω : Om i) (η : Om 1),
      deRham (i + 1) (wedge i ω η) =
        wedgeTwo i ω (deRham 1 η) - wedge (i + 1) (deRham i ω) η)
    (i : ℕ) (ω : Om i) (y : CompletedTensor p D (Om 1) M) :
    differential p D Om wedge deRham M nabla hleib (i + 1) (wedgeMap p D Om wedge M i ω y) =
      completedLTensor p D M (wedgeTwo i ω) (differential p D Om wedge deRham M nabla hleib 1 y) -
        wedgeMap p D Om wedge M (i + 1) (deRham i ω) y := by
  have hof : ∀ z : M ⊗[D] Om 1,
      differential p D Om wedge deRham M nabla hleib (i + 1)
          (wedgeMap p D Om wedge M i ω (toCompletedTensor p D (Om 1) M z)) =
        completedLTensor p D M (wedgeTwo i ω)
            (differential p D Om wedge deRham M nabla hleib 1 (toCompletedTensor p D (Om 1) M z)) -
          wedgeMap p D Om wedge M (i + 1) (deRham i ω) (toCompletedTensor p D (Om 1) M z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul m η =>
      rw [wedgeMap_of_tmul, differential_of_tmul, differential_of_tmul, wedgeMap_of_tmul,
        map_add, completedLTensor_toCompletedTensor_tmul,
        completedLTensor_wedgeTwo_wedgeMap p D Om wedge M wedgeTwo hassoc, hleibTwo,
        TensorProduct.tmul_sub, map_sub]
      abel
    | add a b ha hb =>
      simp only [map_add] at ha hb ⊢
      rw [ha, hb]
      abel
  refine AdicCompletion.ext fun n ↦ ?_
  obtain ⟨z, hyz⟩ := exists_val_eq_mk y n
  have hw : ∀ (j : ℕ) (θ : Om j), (wedgeMap p D Om wedge M j θ y).val n =
      (wedgeMap p D Om wedge M j θ (toCompletedTensor p D (Om 1) M z)).val n := fun j θ ↦
    completedLTensor_val_congr p D M (wedge j θ) n _ _ hyz
  rw [differential_val_congr p D Om wedge deRham M nabla hleib (i + 1) n _ _ (hw i ω),
    AdicCompletion.val_sub_apply,
    completedLTensor_val_congr p D M (wedgeTwo i ω) n _ _
      (differential_val_congr p D Om wedge deRham M nabla hleib 1 n _ _ hyz),
    hw (i + 1) (deRham i ω), hof z, AdicCompletion.val_sub_apply]

include hleib in
/-- **Integrability makes `M ⊗^∧_D Ω^*` a complex**: if the connection is integrable in the sense
of `Crystalline.CompletedDeRham.HasIntegrableConnection`, the differentials compose to zero in
every degree.

The forms are a carried graded family, so what they must satisfy is listed: the de Rham
differential squares to zero (`hdd`), and there is a wedge `wedgeTwo` with a two-form, which is
associative with the wedge by one-forms (`hassoc`) and obeys the graded Leibniz rule
`d (η ∧ ω) = d η ∧ ω - η ∧ d ω` (`hleibTwo`).  All three hold for the genuine completed divided
power forms; see `Crystalline.completedDividedPowerWedgeTwo`. -/
theorem isSquareZero_of_hasIntegrableConnection
    (hdd : ∀ (i : ℕ) (ω : Om i), deRham (i + 1) (deRham i ω) = 0)
    (hassoc : ∀ (i : ℕ) (ω : Om i) (η ξ : Om 1),
      wedge (i + 1) (wedge i ω η) ξ = wedgeTwo i ω (wedge 1 η ξ))
    (hleibTwo : ∀ (i : ℕ) (ω : Om i) (η : Om 1),
      deRham (i + 1) (wedge i ω η) =
        wedgeTwo i ω (deRham 1 η) - wedge (i + 1) (deRham i ω) η)
    (hint : HasIntegrableConnection p D Om wedge deRham M nabla hleib) :
    IsSquareZero p D Om wedge deRham M nabla hleib := by
  have hof : ∀ (i : ℕ) (z : M ⊗[D] Om i),
      differential p D Om wedge deRham M nabla hleib (i + 1)
        (differential p D Om wedge deRham M nabla hleib i (toCompletedTensor p D (Om i) M z)) =
          0 := by
    intro i z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul m ω =>
      rw [differential_of_tmul, map_add,
        differential_wedgeMap p D Om wedge deRham M nabla hleib wedgeTwo hassoc hleibTwo,
        differential_of_tmul, hdd, TensorProduct.tmul_zero, map_zero, add_zero, hint m,
        map_zero, zero_sub, neg_add_cancel]
    | add a b ha hb => rw [map_add, map_add, map_add, ha, hb, add_zero]
  intro i
  refine AddMonoidHom.ext fun x ↦ ?_
  refine AdicCompletion.ext fun n ↦ ?_
  obtain ⟨z, hxz⟩ := exists_val_eq_mk x n
  rw [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply, AdicCompletion.val_zero_apply,
    differential_val_congr p D Om wedge deRham M nabla hleib (i + 1) n _ _
      (differential_val_congr p D Om wedge deRham M nabla hleib i n x _ hxz),
    hof i z, AdicCompletion.val_zero_apply]

/-- **Integrability is the degree-zero part of the square-zero condition**: given a closed
zero-form `1` which is a unit for the wedge, the composite `M → M ⊗̂ Ω¹ → M ⊗̂ Ω²` is the square of
the differential on `m ⊗ 1`. So a connection whose de Rham differentials compose to zero is
integrable. -/
theorem hasIntegrableConnection_of_isSquareZero (one : Om 0) (hone : deRham 0 one = 0)
    (hwedge : ∀ η : Om 1, wedge 0 one η = η)
    (hsq : IsSquareZero p D Om wedge deRham M nabla hleib) :
    HasIntegrableConnection p D Om wedge deRham M nabla hleib := by
  intro m
  have h0 : differential p D Om wedge deRham M nabla hleib 0
      (toCompletedTensor p D (Om 0) M (m ⊗ₜ[D] one)) = nabla m := by
    have hid : wedge 0 one = LinearMap.id := LinearMap.ext hwedge
    rw [differential_of_tmul, hone, TensorProduct.tmul_zero, map_zero, add_zero,
      wedgeMap_eq_completedLTensor, hid, completedLTensor_id]
  rw [← h0]
  exact DFunLike.congr_fun (hsq 0) _

end Curvature

end CompletedDeRham

/-! ### The wedge with a two-form of divided power forms -/

section WedgeTwo

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
  {J : Ideal B} (hJ : DividedPowers J)

/-- **The wedge `Ω^i_{B/A,δ} × Ω²_{B/A,δ} → Ω^{i+2}_{B/A,δ}`**, `(ω, ζ) ↦ ζ ∧ ω`, in the variance
of `Crystalline.dividedPowerWedge`: the form of degree `i` first, the two-form multiplied on the
left. -/
def dividedPowerWedgeTwo (i : ℕ) :
    dividedPowerDifferentialForms (A := A) hJ i →ₗ[B]
      dividedPowerDifferentialForms (A := A) hJ (1 + 1) →ₗ[B]
        dividedPowerDifferentialForms (A := A) hJ (i + 1 + 1) :=
  (exteriorPower.wedgeMul (R := B) (M := dividedPowerDifferentials (A := A) hJ)
    (1 + 1) i).flip.compr₂
    (exteriorPower.degCongr (R := B) (M := dividedPowerDifferentials (A := A) hJ)
      (by omega : 1 + 1 + i = i + 1 + 1)).toLinearMap

/-- The wedge with a two-form, read in the exterior algebra. -/
theorem coe_dividedPowerWedgeTwo (i : ℕ) (omega : dividedPowerDifferentialForms (A := A) hJ i)
    (zeta : dividedPowerDifferentialForms (A := A) hJ (1 + 1)) :
    ((dividedPowerWedgeTwo hJ i omega zeta :
        dividedPowerDifferentialForms (A := A) hJ (i + 1 + 1)) :
        ExteriorAlgebra B (dividedPowerDifferentials (A := A) hJ)) =
      (zeta : ExteriorAlgebra B (dividedPowerDifferentials (A := A) hJ)) * omega :=
  rfl

/-- A one-form of `Ω¹_{B/A,δ}`, read in the exterior algebra. -/
private theorem coe_oneForm (eta : dividedPowerDifferentialForms (A := A) hJ 1) :
    (eta : ExteriorAlgebra B (dividedPowerDifferentials (A := A) hJ)) =
      ExteriorAlgebra.ι B
        (exteriorPower.oneEquiv B (dividedPowerDifferentials (A := A) hJ) eta) := by
  conv_lhs =>
    rw [← (exteriorPower.oneEquiv B (dividedPowerDifferentials (A := A) hJ)).symm_apply_apply eta]
  exact coe_oneEquiv_symm hJ _

/-- **Associativity of the wedge**: `ξ ∧ (η ∧ ω) = (ξ ∧ η) ∧ ω`. -/
theorem dividedPowerWedge_dividedPowerWedge (i : ℕ)
    (omega : dividedPowerDifferentialForms (A := A) hJ i)
    (eta xi : dividedPowerDifferentialForms (A := A) hJ 1) :
    dividedPowerWedge hJ (i + 1) (dividedPowerWedge hJ i omega eta) xi =
      dividedPowerWedgeTwo hJ i omega (dividedPowerWedge hJ 1 eta xi) := by
  refine Subtype.ext ?_
  show ExteriorAlgebra.ι B _ * (ExteriorAlgebra.ι B _ * _) =
    (ExteriorAlgebra.ι B _ *
      (eta : ExteriorAlgebra B (dividedPowerDifferentials (A := A) hJ))) * _
  rw [coe_oneForm hJ eta, mul_assoc]
  rfl

/-- The de Rham differential commutes with reindexing the degree. -/
private theorem dividedPowerDeRham_degCongr {m n : ℕ} (h : m = n)
    (x : dividedPowerDifferentialForms (A := A) hJ m) :
    dividedPowerDeRham hJ n (exteriorPower.degCongr h x) =
      exteriorPower.degCongr (congrArg (· + 1) h) (dividedPowerDeRham hJ m x) := by
  subst h
  rfl

/-- **The graded Leibniz rule against a one-form**: `d (η ∧ ω) = d η ∧ ω - η ∧ d ω`. -/
theorem dividedPowerDeRham_dividedPowerWedge (i : ℕ)
    (omega : dividedPowerDifferentialForms (A := A) hJ i)
    (eta : dividedPowerDifferentialForms (A := A) hJ 1) :
    dividedPowerDeRham hJ (i + 1) (dividedPowerWedge hJ i omega eta) =
      dividedPowerWedgeTwo hJ i omega (dividedPowerDeRham hJ 1 eta) -
        dividedPowerWedge hJ (i + 1) (dividedPowerDeRham hJ i omega) eta := by
  rw [dividedPowerWedge_eq_wedgeMul, dividedPowerDeRham_degCongr,
    dividedPowerDeRham_wedgeMul_degCongr]
  refine Subtype.ext ?_
  rw [exteriorPower.coe_degCongr, Submodule.coe_add, exteriorPower.coe_degCongr,
    exteriorPower.wedgeMul_apply_coe, SetLike.val_smul, exteriorPower.coe_degCongr,
    exteriorPower.wedgeMul_apply_coe, Submodule.coe_sub, coe_dividedPowerWedgeTwo]
  show _ = _ - ExteriorAlgebra.ι B _ * _
  rw [coe_oneForm hJ eta, pow_one, neg_one_smul, ← sub_eq_add_neg]
  rfl

end WedgeTwo

section CompletedWedgeTwo

variable (p : ℕ) (A : Type u) {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
  {J : Ideal B} (hJ : DividedPowers J)

/-- **The wedge `Ω̂^i × Ω̂² → Ω̂^{i+2}` of completed divided power forms**, the completion of
`Crystalline.dividedPowerWedgeTwo` level by level. -/
def completedDividedPowerWedgeTwo (i : ℕ) :
    completedDividedPowerForms p A hJ i →ₗ[completedDividedPowerRing p (B := B)]
      completedDividedPowerForms p A hJ (1 + 1) →ₗ[completedDividedPowerRing p (B := B)]
        completedDividedPowerForms p A hJ (i + 1 + 1) :=
  PAdicCompletion.mapBilinear p B (dividedPowerWedgeTwo hJ i)

/-- The value of the completed wedge with a two-form at the level `pⁿ`. -/
theorem completedDividedPowerWedgeTwo_val (i n : ℕ) (x : completedDividedPowerForms p A hJ i)
    (y : completedDividedPowerForms p A hJ (1 + 1))
    (omega : dividedPowerDifferentialForms (A := A) hJ i)
    (zeta : dividedPowerDifferentialForms (A := A) hJ (1 + 1))
    (hx : x.val n = Submodule.Quotient.mk omega) (hy : y.val n = Submodule.Quotient.mk zeta) :
    (completedDividedPowerWedgeTwo p A hJ i x y).val n =
      Submodule.Quotient.mk (dividedPowerWedgeTwo hJ i omega zeta) := by
  rw [completedDividedPowerWedgeTwo, PAdicCompletion.mapBilinear_val, hx, hy,
    PAdicCompletion.levelMapBilinear_mk_mk]

/-- **Associativity of the completed wedge**: `ξ ∧ (η ∧ ω) = (ξ ∧ η) ∧ ω`. -/
theorem completedDividedPowerWedge_completedDividedPowerWedge (i : ℕ)
    (x : completedDividedPowerForms p A hJ i) (y z : completedDividedPowerForms p A hJ 1) :
    completedDividedPowerWedge p A hJ (i + 1) (completedDividedPowerWedge p A hJ i x y) z =
      completedDividedPowerWedgeTwo p A hJ i x (completedDividedPowerWedge p A hJ 1 y z) := by
  refine AdicCompletion.ext fun n ↦ ?_
  obtain ⟨omega, homega⟩ := exists_val_eq_mk x n
  obtain ⟨eta, heta⟩ := exists_val_eq_mk y n
  obtain ⟨xi, hxi⟩ := exists_val_eq_mk z n
  rw [completedDividedPowerWedge_val p A hJ (i + 1) n _ z (dividedPowerWedge hJ i omega eta) xi
      (completedDividedPowerWedge_val p A hJ i n x y omega eta homega heta) hxi,
    completedDividedPowerWedgeTwo_val p A hJ i n x _ omega (dividedPowerWedge hJ 1 eta xi)
      homega (completedDividedPowerWedge_val p A hJ 1 n y z eta xi heta hxi),
    dividedPowerWedge_dividedPowerWedge]

/-- **The graded Leibniz rule for the completed forms against a one-form**:
`d (η ∧ ω) = d η ∧ ω - η ∧ d ω`. -/
theorem completedDividedPowerDeRham_completedDividedPowerWedge (i : ℕ)
    (x : completedDividedPowerForms p A hJ i) (y : completedDividedPowerForms p A hJ 1) :
    completedDividedPowerDeRham p A hJ (i + 1) (completedDividedPowerWedge p A hJ i x y) =
      completedDividedPowerWedgeTwo p A hJ i x (completedDividedPowerDeRham p A hJ 1 y) -
        completedDividedPowerWedge p A hJ (i + 1) (completedDividedPowerDeRham p A hJ i x) y := by
  refine AdicCompletion.ext fun n ↦ ?_
  obtain ⟨omega, homega⟩ := exists_val_eq_mk x n
  obtain ⟨eta, heta⟩ := exists_val_eq_mk y n
  rw [completedDividedPowerDeRham_val p A hJ (i + 1) n _ (dividedPowerWedge hJ i omega eta)
      (completedDividedPowerWedge_val p A hJ i n x y omega eta homega heta),
    AdicCompletion.val_sub_apply,
    completedDividedPowerWedgeTwo_val p A hJ i n x _ omega (dividedPowerDeRham hJ 1 eta)
      homega (completedDividedPowerDeRham_val p A hJ 1 n y eta heta),
    completedDividedPowerWedge_val p A hJ (i + 1) n _ y (dividedPowerDeRham hJ i omega) eta
      (completedDividedPowerDeRham_val p A hJ i n x omega homega) heta,
    dividedPowerDeRham_dividedPowerWedge]
  rfl

/-- **The de Rham complex of a completed connection on the completed divided power forms is a
complex as soon as the connection is integrable.** -/
theorem isSquareZero_completedDividedPowerForms_of_hasIntegrableConnection {M : Type w}
    [AddCommGroup M] [Module (completedDividedPowerRing p (B := B)) M]
    (nabla : CompletedConnection p (completedDividedPowerRing p (B := B))
      (completedDividedPowerForms p A hJ 1) (completedFormsDifferential p A hJ) M)
    (hint : CompletedDeRham.HasIntegrableConnection p (completedDividedPowerRing p (B := B))
      (completedDividedPowerForms p A hJ) (completedDividedPowerWedge p A hJ)
      (completedDividedPowerDeRham p A hJ) M nabla (isGradedLeibniz_completedDividedPower p A hJ)) :
    CompletedDeRham.IsSquareZero p (completedDividedPowerRing p (B := B))
      (completedDividedPowerForms p A hJ) (completedDividedPowerWedge p A hJ)
      (completedDividedPowerDeRham p A hJ) M nabla
      (isGradedLeibniz_completedDividedPower p A hJ) :=
  CompletedDeRham.isSquareZero_of_hasIntegrableConnection p _ _ _ _ M nabla _
    (completedDividedPowerWedgeTwo p A hJ)
    (isGradedExterior_completedDividedPower p A hJ).deRham_deRham
    (completedDividedPowerWedge_completedDividedPowerWedge p A hJ)
    (completedDividedPowerDeRham_completedDividedPowerWedge p A hJ) hint

end CompletedWedgeTwo

/-- **A bilinear map over `D'` is bilinear over `D`** when `D` acts on the three modules through
a ring map `g : D → D'`. -/
def restrictScalarsBilinear {D : Type*} {D' : Type*} [CommRing D] [CommRing D'] (g : D →+* D')
    {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z] [Module D' X]
    [Module D' Y] [Module D' Z] [Module D X] [Module D Y] [Module D Z]
    (b : X →ₗ[D'] Y →ₗ[D'] Z) (hX : ∀ (c : D) (x : X), c • x = g c • x)
    (hY : ∀ (c : D) (y : Y), c • y = g c • y) (hZ : ∀ (c : D) (z : Z), c • z = g c • z) :
    X →ₗ[D] Y →ₗ[D] Z :=
  LinearMap.mk₂ D (fun x y ↦ b x y)
    (fun x x' y ↦ by rw [map_add, LinearMap.add_apply])
    (fun c x y ↦ by rw [hX c x, hZ c (b x y), map_smul, LinearMap.smul_apply])
    (fun x y y' ↦ map_add (b x) y y')
    (fun c x y ↦ by rw [hY c y, hZ c (b x y), map_smul])

/-- The restricted bilinear map is the original one. -/
@[simp] theorem restrictScalarsBilinear_apply {D : Type*} {D' : Type*} [CommRing D] [CommRing D']
    (g : D →+* D') {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [Module D' X] [Module D' Y] [Module D' Z] [Module D X] [Module D Y] [Module D Z]
    (b : X →ₗ[D'] Y →ₗ[D'] Z) (hX : ∀ (c : D) (x : X), c • x = g c • x)
    (hY : ∀ (c : D) (y : Y), c • y = g c • y) (hZ : ∀ (c : D) (z : Z), c • z = g c • z)
    (x : X) (y : Y) :
    restrictScalarsBilinear g b hX hY hZ x y = b x y :=
  rfl

namespace DividedPowerPolynomial

/-! ### The forms of `D'` read over `D`, without a chosen order on the variables -/

section CompletedComparison

variable (A : Type uA) [CommRing A] (B : DividedPowerRing.{uB}) [Algebra A B] (W : Type uW)
  (p : ℕ)

/-- **The completed comparison `ψ̂ : Ω̂ⁿ_D → Ω̂ⁿ_{D'}`**, `D`-linearly: the `p`-adic completion of
the comparison `Ω^n_{B/A,δ} → Ω^n_{P/A,δ'}` of divided power forms along the coefficient
inclusion `B → P`.  It is `Crystalline.DividedPowerPolynomial.completedCoefficientFormsMapₗ`; the
linear order on the variables that the latter is stated with plays no part in its value, as
`Crystalline.DividedPowerPolynomial.completedFormsComparison_eq` records, so one is chosen here
and the statements below need none. -/
def completedFormsComparison (n : ℕ) :
    completedDividedPowerForms p A B.dividedPowers n →ₗ[
      completedDividedPowerRing p (B := (B : Type uB))] completedPolynomialForms A B W p n :=
  letI : LinearOrder W := IsWellOrder.linearOrder WellOrderingRel
  completedCoefficientFormsMapₗ A B W p n

/-- The completed comparison does not depend on the order on the variables. -/
theorem completedFormsComparison_eq [LinearOrder W] (n : ℕ) :
    completedFormsComparison A B W p n = completedCoefficientFormsMapₗ A B W p n :=
  rfl

/-- The completed comparison is the completion of the comparison of forms. -/
theorem completedFormsComparison_apply (n : ℕ)
    (x : completedDividedPowerForms p A B.dividedPowers n) :
    completedFormsComparison A B W p n x =
      PAdicCompletion.mapAddHom p (B : Type uB) (setIndexedDividedPowerPolynomialAlgebra B W)
        (coefficientFormsMap A B W n).toAddMonoidHom x :=
  rfl

/-- **The Leibniz rule `d (c · ω) = c · d ω + d c ∧ ω` on `Ω̂^*_{D'}` over `D`.** -/
theorem completedPolynomialForms_isGradedLeibniz :
    CompletedDeRham.IsGradedLeibniz (completedDividedPowerRing p (B := (B : Type uB)))
      (completedPolynomialForms A B W p) (completedPolynomialFormsWedge A B W p)
      (completedDividedPowerDeRham p A (setIndexedDividedPowerPolynomialDividedPowers B W))
      (completedPolynomialFormsDifferential A B W p) :=
  let : LinearOrder W := IsWellOrder.linearOrder WellOrderingRel
  isGradedLeibniz_completedPolynomialForms A B W p

/-- `ψ̂` carries the universal differential of `D` to that of `D'`. -/
theorem completedFormsComparison_completedFormsDifferential
    (c : completedDividedPowerRing p (B := (B : Type uB))) :
    completedFormsComparison A B W p 1 (completedFormsDifferential p A B.dividedPowers c) =
      completedPolynomialFormsDifferential A B W p c :=
  let : LinearOrder W := IsWellOrder.linearOrder WellOrderingRel
  completedCoefficientFormsMapₗ_completedFormsDifferential A B W p c

variable (M : Type uM) [AddCommGroup M]
  [Module (completedDividedPowerRing p (B := (B : Type uB))) M]

/-- **The connection of `M ⊗̂_D Ω̂^*_{D'}`**: a connection `∇ : M → M ⊗̂_D Ω̂¹_D` pushed into the
forms of `D'` along `ψ̂`, `m ↦ (1_M ⊗ ψ̂)(∇ m)`. -/
def completedPushedConnection
    (nabla : CompletedConnection p (completedDividedPowerRing p (B := (B : Type uB)))
      (completedDividedPowerForms p A B.dividedPowers 1)
      (completedFormsDifferential p A B.dividedPowers) M) :
    CompletedConnection p (completedDividedPowerRing p (B := (B : Type uB)))
      (completedPolynomialForms A B W p 1) (completedPolynomialFormsDifferential A B W p) M :=
  CompletedDeRham.pushforwardConnection p (completedDividedPowerRing p (B := (B : Type uB))) M
    (completedFormsComparison A B W p 1)
    (completedFormsComparison_completedFormsDifferential A B W p) nabla

/-- The pushed connection does not depend on the order on the variables. -/
theorem completedPushedConnection_eq [LinearOrder W]
    (nabla : CompletedConnection p (completedDividedPowerRing p (B := (B : Type uB)))
      (completedDividedPowerForms p A B.dividedPowers 1)
      (completedFormsDifferential p A B.dividedPowers) M) :
    completedPushedConnection A B W p M nabla = pushedConnection A B W p M nabla :=
  rfl

/-- **The de Rham differential of `M ⊗̂_D Ω̂^*_{D'}`**, `∇(m ⊗ ω) = ∇ m ∧ ω + m ⊗ d ω` for the
pushed connection. -/
def completedTargetDifferential
    (nabla : CompletedConnection p (completedDividedPowerRing p (B := (B : Type uB)))
      (completedDividedPowerForms p A B.dividedPowers 1)
      (completedFormsDifferential p A B.dividedPowers) M) (i : ℕ) :
    CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
        (completedPolynomialForms A B W p i) M →+
      CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
        (completedPolynomialForms A B W p (i + 1)) M :=
  CompletedDeRham.differential p (completedDividedPowerRing p (B := (B : Type uB)))
    (completedPolynomialForms A B W p) (completedPolynomialFormsWedge A B W p)
    (completedDividedPowerDeRham p A (setIndexedDividedPowerPolynomialDividedPowers B W)) M
    (completedPushedConnection A B W p M nabla) (completedPolynomialForms_isGradedLeibniz A B W p) i

/-- **The canonical comparison `1_M ⊗ ψ̂ : M ⊗̂_D Ω̂^i_D → M ⊗̂_D Ω̂^i_{D'}`.** -/
def completedModuleComparison (i : ℕ) :
    CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
        (completedDividedPowerForms p A B.dividedPowers i) M →+
      CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
        (completedPolynomialForms A B W p i) M :=
  CompletedDeRham.completedLTensor p (completedDividedPowerRing p (B := (B : Type uB))) M
    (completedFormsComparison A B W p i)

variable {M}

/-- **`1_M ⊗ ψ̂` commutes with the two de Rham differentials.** -/
theorem completedTargetDifferential_completedModuleComparison
    (nabla : CompletedConnection p (completedDividedPowerRing p (B := (B : Type uB)))
      (completedDividedPowerForms p A B.dividedPowers 1)
      (completedFormsDifferential p A B.dividedPowers) M) (i : ℕ)
    (z : CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
      (completedDividedPowerForms p A B.dividedPowers i) M) :
    completedTargetDifferential A B W p M nabla i (completedModuleComparison A B W p M i z) =
      completedModuleComparison A B W p M (i + 1)
        (coefficientDeRhamDifferential A B p M nabla i z) :=
  let : LinearOrder W := IsWellOrder.linearOrder WellOrderingRel
  polynomialDeRhamDifferential_moduleCoefficientFormsMap A B W p M nabla i z

/-- **The connection pushed into the forms of `D'` is integrable when `∇` is.** -/
theorem hasIntegrableConnection_completedPushedConnection
    (nabla : CompletedConnection p (completedDividedPowerRing p (B := (B : Type uB)))
      (completedDividedPowerForms p A B.dividedPowers 1)
      (completedFormsDifferential p A B.dividedPowers) M)
    (hint : CompletedDeRham.HasIntegrableConnection p
      (completedDividedPowerRing p (B := (B : Type uB)))
      (completedDividedPowerForms p A B.dividedPowers)
      (completedDividedPowerWedge p A B.dividedPowers)
      (completedDividedPowerDeRham p A B.dividedPowers) M nabla
      (isGradedLeibniz_completedDividedPower p A B.dividedPowers)) :
    CompletedDeRham.HasIntegrableConnection p (completedDividedPowerRing p (B := (B : Type uB)))
      (completedPolynomialForms A B W p) (completedPolynomialFormsWedge A B W p)
      (completedDividedPowerDeRham p A (setIndexedDividedPowerPolynomialDividedPowers B W)) M
      (completedPushedConnection A B W p M nabla)
      (completedPolynomialForms_isGradedLeibniz A B W p) := by
  intro m
  exact (completedTargetDifferential_completedModuleComparison A B W p nabla 1 (nabla m)).trans
    ((congrArg (completedModuleComparison A B W p M (1 + 1)) (hint m)).trans (map_zero _))

/-- **The wedge `Ω̂^i_{D'} × Ω̂²_{D'} → Ω̂^{i+2}_{D'}`, read `D`-bilinearly.** -/
def completedPolynomialFormsWedgeTwo (i : ℕ) :
    completedPolynomialForms A B W p i →ₗ[completedDividedPowerRing p (B := (B : Type uB))]
      completedPolynomialForms A B W p (1 + 1) →ₗ[completedDividedPowerRing p (B := (B : Type uB))]
        completedPolynomialForms A B W p (i + 1 + 1) :=
  restrictScalarsBilinear (completedCoefficientRingHom A B W p)
    (completedDividedPowerWedgeTwo p A (setIndexedDividedPowerPolynomialDividedPowers B W) i)
    (completedPolynomialForms_smul A B W p i) (completedPolynomialForms_smul A B W p (1 + 1))
    (completedPolynomialForms_smul A B W p (i + 1 + 1))

/-- **The de Rham complex `M ⊗̂_D Ω̂^*_D` is a complex for an integrable connection.** -/
theorem isSquareZero_coefficient_of_hasIntegrableConnection
    (nabla : CompletedConnection p (completedDividedPowerRing p (B := (B : Type uB)))
      (completedDividedPowerForms p A B.dividedPowers 1)
      (completedFormsDifferential p A B.dividedPowers) M)
    (hint : CompletedDeRham.HasIntegrableConnection p
      (completedDividedPowerRing p (B := (B : Type uB)))
      (completedDividedPowerForms p A B.dividedPowers)
      (completedDividedPowerWedge p A B.dividedPowers)
      (completedDividedPowerDeRham p A B.dividedPowers) M nabla
      (isGradedLeibniz_completedDividedPower p A B.dividedPowers)) :
    CompletedDeRham.IsSquareZero p (completedDividedPowerRing p (B := (B : Type uB)))
      (completedDividedPowerForms p A B.dividedPowers)
      (completedDividedPowerWedge p A B.dividedPowers)
      (completedDividedPowerDeRham p A B.dividedPowers) M nabla
      (isGradedLeibniz_completedDividedPower p A B.dividedPowers) :=
  isSquareZero_completedDividedPowerForms_of_hasIntegrableConnection p A B.dividedPowers nabla hint

/-- **The de Rham complex `M ⊗̂_D Ω̂^*_{D'}` is a complex for an integrable connection.** -/
theorem isSquareZero_polynomial_of_hasIntegrableConnection
    (nabla : CompletedConnection p (completedDividedPowerRing p (B := (B : Type uB)))
      (completedDividedPowerForms p A B.dividedPowers 1)
      (completedFormsDifferential p A B.dividedPowers) M)
    (hint : CompletedDeRham.HasIntegrableConnection p
      (completedDividedPowerRing p (B := (B : Type uB)))
      (completedDividedPowerForms p A B.dividedPowers)
      (completedDividedPowerWedge p A B.dividedPowers)
      (completedDividedPowerDeRham p A B.dividedPowers) M nabla
      (isGradedLeibniz_completedDividedPower p A B.dividedPowers)) :
    CompletedDeRham.IsSquareZero p (completedDividedPowerRing p (B := (B : Type uB)))
      (completedPolynomialForms A B W p) (completedPolynomialFormsWedge A B W p)
      (completedDividedPowerDeRham p A (setIndexedDividedPowerPolynomialDividedPowers B W)) M
      (completedPushedConnection A B W p M nabla)
      (completedPolynomialForms_isGradedLeibniz A B W p) :=
  CompletedDeRham.isSquareZero_of_hasIntegrableConnection p _ _ _ _ M _ _
    (completedPolynomialFormsWedgeTwo A B W p)
    (isGradedExterior_completedDividedPower p A
      (setIndexedDividedPowerPolynomialDividedPowers B W)).deRham_deRham
    (completedDividedPowerWedge_completedDividedPowerWedge p A
      (setIndexedDividedPowerPolynomialDividedPowers B W))
    (completedDividedPowerDeRham_completedDividedPowerWedge p A
      (setIndexedDividedPowerPolynomialDividedPowers B W))
    (hasIntegrableConnection_completedPushedConnection A B W p nabla hint)

/-- **The canonical comparison has a homotopy inverse**: for a `D`-module `M` with an integrable
connection `∇ : M → M ⊗̂_D Ω̂¹_D`, and any family of divided power variables, there are additive
maps `π_i : M ⊗̂_D Ω̂^i_{D'} → M ⊗̂_D Ω̂^i_D` and `H_i : M ⊗̂_D Ω̂^{i+1}_{D'} → M ⊗̂_D Ω̂^i_{D'}`
such that `π ∘ (1_M ⊗ ψ̂) = 1`, `π` commutes with the two de Rham differentials, and
`d H + H d + (1_M ⊗ ψ̂) π = 1` (in degree `0`, `H d + (1_M ⊗ ψ̂) π = 1`).

This is the degreewise form of the homotopy equivalence
`Crystalline.DividedPowerPolynomial.completedDeRhamHomotopyEquiv`, stated for a family of
variables in an arbitrary universe. -/
theorem exists_retraction_completedDeRhamComparison
    (nabla : CompletedConnection p (completedDividedPowerRing p (B := (B : Type uB)))
      (completedDividedPowerForms p A B.dividedPowers 1)
      (completedFormsDifferential p A B.dividedPowers) M)
    (hint : CompletedDeRham.HasIntegrableConnection p
      (completedDividedPowerRing p (B := (B : Type uB)))
      (completedDividedPowerForms p A B.dividedPowers)
      (completedDividedPowerWedge p A B.dividedPowers)
      (completedDividedPowerDeRham p A B.dividedPowers) M nabla
      (isGradedLeibniz_completedDividedPower p A B.dividedPowers)) :
    ∃ (pi' : ∀ i, CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
        (completedPolynomialForms A B W p i) M →+
      CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
        (completedDividedPowerForms p A B.dividedPowers i) M)
      (H : ∀ i, CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
          (completedPolynomialForms A B W p (i + 1)) M →+
        CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
          (completedPolynomialForms A B W p i) M),
      (∀ (i : ℕ) (z : CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
          (completedDividedPowerForms p A B.dividedPowers i) M),
          pi' i (completedModuleComparison A B W p M i z) = z) ∧
        (∀ (i : ℕ) (w : CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
            (completedPolynomialForms A B W p i) M),
            pi' (i + 1) (completedTargetDifferential A B W p M nabla i w) =
              coefficientDeRhamDifferential A B p M nabla i (pi' i w)) ∧
          (∀ w : CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
              (completedPolynomialForms A B W p 0) M,
              H 0 (completedTargetDifferential A B W p M nabla 0 w) +
                completedModuleComparison A B W p M 0 (pi' 0 w) = w) ∧
            ∀ (n : ℕ) (w : CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
                (completedPolynomialForms A B W p (n + 1)) M),
              completedTargetDifferential A B W p M nabla n (H n w) +
                  H (n + 1) (completedTargetDifferential A B W p M nabla (n + 1) w) +
                completedModuleComparison A B W p M (n + 1) (pi' (n + 1) w) = w :=
  let : LinearOrder W := IsWellOrder.linearOrder WellOrderingRel
  exists_homotopyEquiv_pushedConnection A B W p M nabla
    (isSquareZero_polynomial_of_hasIntegrableConnection A B W p nabla hint)

end CompletedComparison

/-! ### The two de Rham complexes and the comparison map -/

section Complexes

variable (A : Type uA) [CommRing A] (B : DividedPowerRing.{uB}) [Algebra A B] (W : Type uB)
  (p : ℕ) (M : Type uM) [AddCommGroup M]
  [Module (completedDividedPowerRing p (B := (B : Type uB))) M]
  (nabla : CompletedConnection p (completedDividedPowerRing p (B := (B : Type uB)))
    (completedDividedPowerForms p A B.dividedPowers 1)
    (completedFormsDifferential p A B.dividedPowers) M)
  (hint : CompletedDeRham.HasIntegrableConnection p
    (completedDividedPowerRing p (B := (B : Type uB)))
    (completedDividedPowerForms p A B.dividedPowers)
    (completedDividedPowerWedge p A B.dividedPowers)
    (completedDividedPowerDeRham p A B.dividedPowers) M nabla
    (isGradedLeibniz_completedDividedPower p A B.dividedPowers))

/-- **The de Rham complex `M ⊗̂_D Ω̂^*_D`** of a `D`-module with an integrable connection: in
degree `i` the completed tensor product `M ⊗̂_D Ω̂^i_D`, with differential
`∇(m ⊗ ω) = ∇ m ∧ ω + m ⊗ d ω`. -/
def completedSourceDeRhamComplex : CochainComplex AddCommGrpCat.{max uB uM} ℕ :=
  CompletedDeRham.complex p (completedDividedPowerRing p (B := (B : Type uB)))
    (completedDividedPowerForms p A B.dividedPowers)
    (completedDividedPowerWedge p A B.dividedPowers)
    (completedDividedPowerDeRham p A B.dividedPowers) M nabla
    (isGradedLeibniz_completedDividedPower p A B.dividedPowers)
    (isSquareZero_coefficient_of_hasIntegrableConnection A B p nabla hint)

/-- **The de Rham complex `M ⊗̂_D Ω̂^*_{D'}`**: in degree `i` the completed tensor product
`M ⊗̂_D Ω̂^i_{D'}`, with differential `∇(m ⊗ ω) = ∇ m ∧ ω + m ⊗ d ω` for the connection of `M`
read in the forms of `D'`. -/
def completedTargetDeRhamComplex : CochainComplex AddCommGrpCat.{max uB uM} ℕ :=
  CompletedDeRham.complex p (completedDividedPowerRing p (B := (B : Type uB)))
    (completedPolynomialForms A B W p) (completedPolynomialFormsWedge A B W p)
    (completedDividedPowerDeRham p A (setIndexedDividedPowerPolynomialDividedPowers B W)) M
    (completedPushedConnection A B W p M nabla) (completedPolynomialForms_isGradedLeibniz A B W p)
    (isSquareZero_polynomial_of_hasIntegrableConnection A B W p nabla hint)

/-- The differential of `M ⊗̂_D Ω̂^*_D` is the de Rham differential of the connection. -/
theorem completedSourceDeRhamComplex_d (i : ℕ) :
    (completedSourceDeRhamComplex A B p M nabla hint).d i (i + 1) =
      AddCommGrpCat.ofHom (coefficientDeRhamDifferential A B p M nabla i) :=
  CompletedDeRham.complex_d _ _ _ _ _ _ _ _ _ i

/-- The differential of `M ⊗̂_D Ω̂^*_{D'}` is the de Rham differential of the pushed
connection. -/
theorem completedTargetDeRhamComplex_d (i : ℕ) :
    (completedTargetDeRhamComplex A B W p M nabla hint).d i (i + 1) =
      AddCommGrpCat.ofHom (completedTargetDifferential A B W p M nabla i) :=
  CompletedDeRham.complex_d _ _ _ _ _ _ _ _ _ i

/-- **The map of de Rham complexes `M ⊗̂_D Ω̂^*_D ⟶ M ⊗̂_D Ω̂^*_{D'}`** of
[Stacks, Lemma 60.19.2, Tag 07LD]: `1_M ⊗ ψ̂` in every degree, `ψ̂` the completion of the
comparison of divided power forms along `B → P`. -/
def completedDeRhamComparison :
    completedSourceDeRhamComplex A B p M nabla hint ⟶
      completedTargetDeRhamComplex A B W p M nabla hint :=
  CochainComplex.ofHom (fun i ↦ AddCommGrpCat.ofHom (completedModuleComparison A B W p M i))
    (fun i ↦ by
      rw [completedSourceDeRhamComplex_d, completedTargetDeRhamComplex_d]
      exact AddCommGrpCat.ext fun z ↦
        completedTargetDifferential_completedModuleComparison A B W p nabla i z)

/-- The components of the comparison are `1_M ⊗ ψ̂`. -/
theorem completedDeRhamComparison_f (i : ℕ) :
    (completedDeRhamComparison A B W p M nabla hint).f i =
      AddCommGrpCat.ofHom (completedModuleComparison A B W p M i) :=
  rfl

/-- The retraction of
`Crystalline.DividedPowerPolynomial.exists_retraction_completedDeRhamComparison`, as a family of
additive maps. -/
def completedDeRhamRetraction (i : ℕ) :
    CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
        (completedPolynomialForms A B W p i) M →+
      CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
        (completedDividedPowerForms p A B.dividedPowers i) M :=
  (exists_retraction_completedDeRhamComparison A B W p nabla hint).choose i

/-- The homotopy of
`Crystalline.DividedPowerPolynomial.exists_retraction_completedDeRhamComparison`, as a family of
additive maps. -/
def completedDeRhamHomotopy (i : ℕ) :
    CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
        (completedPolynomialForms A B W p (i + 1)) M →+
      CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
        (completedPolynomialForms A B W p i) M :=
  (exists_retraction_completedDeRhamComparison A B W p nabla hint).choose_spec.choose i

/-- The four identities satisfied by the retraction and the homotopy. -/
theorem completedDeRhamRetraction_spec :
    (∀ (i : ℕ) (z : CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
        (completedDividedPowerForms p A B.dividedPowers i) M),
        completedDeRhamRetraction A B W p M nabla hint i
          (completedModuleComparison A B W p M i z) = z) ∧
      (∀ (i : ℕ) (w : CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
          (completedPolynomialForms A B W p i) M),
          completedDeRhamRetraction A B W p M nabla hint (i + 1)
              (completedTargetDifferential A B W p M nabla i w) =
            coefficientDeRhamDifferential A B p M nabla i
              (completedDeRhamRetraction A B W p M nabla hint i w)) ∧
        (∀ w : CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
            (completedPolynomialForms A B W p 0) M,
            completedDeRhamHomotopy A B W p M nabla hint 0
                (completedTargetDifferential A B W p M nabla 0 w) +
              completedModuleComparison A B W p M 0
                (completedDeRhamRetraction A B W p M nabla hint 0 w) = w) ∧
          ∀ (n : ℕ) (w : CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
              (completedPolynomialForms A B W p (n + 1)) M),
            completedTargetDifferential A B W p M nabla n
                  (completedDeRhamHomotopy A B W p M nabla hint n w) +
                completedDeRhamHomotopy A B W p M nabla hint (n + 1)
                  (completedTargetDifferential A B W p M nabla (n + 1) w) +
              completedModuleComparison A B W p M (n + 1)
                (completedDeRhamRetraction A B W p M nabla hint (n + 1) w) = w :=
  (exists_retraction_completedDeRhamComparison A B W p nabla hint).choose_spec.choose_spec

/-- The retraction is a map of complexes `M ⊗̂_D Ω̂^*_{D'} ⟶ M ⊗̂_D Ω̂^*_D`. -/
def completedDeRhamRetractionHom :
    completedTargetDeRhamComplex A B W p M nabla hint ⟶
      completedSourceDeRhamComplex A B p M nabla hint :=
  CochainComplex.ofHom
    (fun i ↦ AddCommGrpCat.ofHom (completedDeRhamRetraction A B W p M nabla hint i))
    (fun i ↦ by
      rw [completedSourceDeRhamComplex_d, completedTargetDeRhamComplex_d]
      exact AddCommGrpCat.ext fun w ↦
        ((completedDeRhamRetraction_spec A B W p M nabla hint).2.1 i w).symm)

/-- **The comparison `M ⊗̂_D Ω̂^*_D ⟶ M ⊗̂_D Ω̂^*_{D'}` is a homotopy equivalence**, with the
retraction and the homotopy of
`Crystalline.DividedPowerPolynomial.exists_retraction_completedDeRhamComparison`. -/
def completedDeRhamHomotopyEquiv :
    HomotopyEquiv (completedSourceDeRhamComplex A B p M nabla hint)
      (completedTargetDeRhamComplex A B W p M nabla hint) where
  hom := completedDeRhamComparison A B W p M nabla hint
  inv := completedDeRhamRetractionHom A B W p M nabla hint
  homotopyHomInvId := Homotopy.ofEq (HomologicalComplex.hom_ext _ _ fun i ↦
    AddCommGrpCat.ext fun z ↦ (completedDeRhamRetraction_spec A B W p M nabla hint).1 i z)
  homotopyInvHomId := (cochainHomotopyOfDegreewise
    (fun i ↦ AddCommGrpCat.ofHom (completedDeRhamHomotopy A B W p M nabla hint i))
    (by
      rw [completedTargetDeRhamComplex_d]
      exact AddCommGrpCat.ext fun w ↦
        ((completedDeRhamRetraction_spec A B W p M nabla hint).2.2.1 w).symm)
    (fun n ↦ by
      rw [completedTargetDeRhamComplex_d, completedTargetDeRhamComplex_d]
      refine AddCommGrpCat.ext fun w ↦ ?_
      change w = completedDeRhamHomotopy A B W p M nabla hint (n + 1)
          (completedTargetDifferential A B W p M nabla (n + 1) w) +
        completedTargetDifferential A B W p M nabla n
          (completedDeRhamHomotopy A B W p M nabla hint n w) +
        completedModuleComparison A B W p M (n + 1)
          (completedDeRhamRetraction A B W p M nabla hint (n + 1) w)
      rw [add_comm (completedDeRhamHomotopy A B W p M nabla hint (n + 1) _)]
      exact ((completedDeRhamRetraction_spec A B W p M nabla hint).2.2.2 n w).symm)).symm

/-- The homotopy equivalence is the canonical comparison. -/
theorem completedDeRhamHomotopyEquiv_hom :
    (completedDeRhamHomotopyEquiv A B W p M nabla hint).hom =
      completedDeRhamComparison A B W p M nabla hint :=
  rfl

/-- **[Stacks, Lemma 60.19.2, Tag 07LD], the clause over the `p`-adic completions.**

Let `A` be a ring, let `(B, I, δ)` be a divided power ring which is an `A`-algebra, and let
`P = B⟨x_w : w ∈ W⟩` be the divided power polynomial ring over `B` on an arbitrary family `W` of
variables, with divided power ideal `J = IP + B⟨x_w⟩₊`.  Let `D`, resp. `D'`, be the `p`-adic
completion of `B`, resp. `P`, and let `Ω̂^i_D`, resp. `Ω̂^i_{D'}`, be the `p`-adic completion of
`Ω^i_{B/A,δ}`, resp. `Ω^i_{P/A,δ}`.  Let `M` be a `D`-module with an integrable connection
`∇ : M → M ⊗̂_D Ω̂¹_D` (`hint`: the composite `M → M ⊗̂_D Ω̂¹_D → M ⊗̂_D Ω̂²_D` vanishes,
[Stacks, Remark 60.5.4, Tag 07I0]).  Then the map of de Rham complexes

`M ⊗̂_D Ω̂^*_D ⟶ M ⊗̂_D Ω̂^*_{D'}`

is a quasi-isomorphism.

The source asks `M` to be `p`-adically complete; the statement holds without it, so that
hypothesis is not made.  The map is a homotopy equivalence,
`Crystalline.DividedPowerPolynomial.completedDeRhamHomotopyEquiv`, and its degreewise form is
`Crystalline.DividedPowerPolynomial.exists_retraction_completedDeRhamComparison`.  The family of
variables lives in the universe of `B`, which is what lets the two complexes be compared in one
category of abelian groups.  Together with the clause for a `B`-module this is
`Crystalline.DividedPowerPolynomial.stacks07LD`. -/
theorem quasiIso_completedDeRhamComparison :
    QuasiIso (completedDeRhamComparison A B W p M nabla hint) := by
  rw [← completedDeRhamHomotopyEquiv_hom]
  infer_instance

end Complexes

end DividedPowerPolynomial

end Crystalline

end
