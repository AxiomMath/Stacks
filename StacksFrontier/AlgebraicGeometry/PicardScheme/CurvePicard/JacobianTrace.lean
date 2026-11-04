module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.JacobianPullback
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.CurveMapDegree
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.TateModule
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilTraceInput

/-!
# The trace of `φ^*` on the `ℓ`-adic Tate module of the Jacobian

Let `f : C ⟶ Spec k` be a smooth projective curve over a field and `φ : C ⟶ C` a morphism over
`k`. Pulling back along `φ` multiplies degrees by `deg φ`, so it preserves the degree-zero
Picard group `Pic⁰(C)`. The trace `Tr_J(φ^*)` of [Stacks, Tag 03U1] is the trace of `φ^*` on the
`ℓ`-adic Tate module `T_ℓ J` of the Jacobian `J = Pic⁰_{C/k}` ([Stacks, Tag 03RP] for the
structure of `J(k)[ℓ^n]`). Since `J(k) = Pic⁰(C)` compatibly with `φ^*`
(`Stacks.PicardFunctor.jacobianPointsAddEquiv_comp_jacobianPullback`), that trace is the trace
of `φ^*` on `T_ℓ Pic⁰(C)`, whatever site the Jacobian is built in.

## Main definitions

* `AlgebraicGeometry.CurveGraph.picardDegreeZeroPullback`: `φ^* : Pic⁰(C) →+ Pic⁰(C)`.
* `AlgebraicGeometry.CurveGraph.jacobianTateTrace`: the trace of `φ^*` on `T_ℓ Pic⁰(C)`.

## Main results

* `AlgebraicGeometry.CurveGraph.picardDegree_schemePicardPullbackHom`:
  `deg(φ^* L) = deg φ · deg L`, in the model `AlgebraicGeometry.schemePicard`.
* `Stacks.PicardFunctor.trace_tateModuleMap_jacobianPullback`: the trace of the endomorphism
  `T_ℓ(φ^*)` of the Tate module of the Jacobian is `jacobianTateTrace`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.CurveGraph

variable {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))

/-- **`deg(φ^* L) = deg φ · deg L`** in the model `AlgebraicGeometry.schemePicard` of `Pic(C)`. -/
theorem picardDegree_schemePicardPullbackHom [IsCurve k f] [IsProper f]
    (hdim : topologicalKrullDim C ≤ 1) (φ : C ⟶ C) (w : φ ≫ f = f) (x : schemePicard C) :
    picardDegree k f hdim (schemePicardPullbackHom φ x) =
      (curveMapDegree f φ w : ℤ) * picardDegree k f hdim x := by
  obtain ⟨y, rfl⟩ := (Stacks.GluePicard.picardModelAddEquiv C.toRingedSpace).surjective x
  rw [schemePicardPullbackHom_picardModelAddEquiv]
  exact picardDegree_schemePullbackClass f hdim φ w y

/-- **`φ^* : Pic⁰(C) →+ Pic⁰(C)`**, the restriction of the pullback of line bundles to the
degree-zero Picard group. -/
def picardDegreeZeroPullback [IsCurve k f] [IsProper f] (hdim : topologicalKrullDim C ≤ 1)
    (φ : C ⟶ C) (w : φ ≫ f = f) : picardDegreeZero k f hdim →+ picardDegreeZero k f hdim :=
  ((schemePicardPullbackHom φ).comp (picardDegreeZero k f hdim).subtype).codRestrict _
    fun x => by
      rw [AddMonoidHom.comp_apply, mem_picardDegreeZero_iff,
        picardDegree_schemePicardPullbackHom f hdim φ w, AddSubgroup.coe_subtype,
        (mem_picardDegreeZero_iff k f hdim x.1).1 x.2, mul_zero]

/-- The underlying class of `picardDegreeZeroPullback f hdim φ w x` is the pullback of `x`. -/
@[simp]
theorem coe_picardDegreeZeroPullback [IsCurve k f] [IsProper f]
    (hdim : topologicalKrullDim C ≤ 1) (φ : C ⟶ C) (w : φ ≫ f = f)
    (x : picardDegreeZero k f hdim) :
    (picardDegreeZeroPullback f hdim φ w x : schemePicard C) = schemePicardPullbackHom φ x :=
  rfl

/-- **The trace of `φ^*` on the `ℓ`-adic Tate module of `Pic⁰(C)`**, which is the trace
`Tr_J(φ^*)` of `φ^*` on the Tate module of the Jacobian
(`Stacks.PicardFunctor.trace_tateModuleMap_jacobianPullback`). -/
def jacobianTateTrace [IsCurve k f] [IsProper f] (hdim : topologicalKrullDim C ≤ 1)
    (φ : C ⟶ C) (w : φ ≫ f = f) (ℓ : ℕ) [Fact ℓ.Prime] : ℤ_[ℓ] :=
  LinearMap.trace ℤ_[ℓ] _
    (Stacks.AbelianGroup.tateModuleMap ℓ (picardDegreeZeroPullback f hdim φ w))

section AlgClosed

variable [IsAlgClosed k] [IsCurve k f] [Smooth f] [IsProper f]

/-- `Pic⁰(C)` is `ℓ`-divisible for `ℓ` invertible in `k` ([Stacks, Tag 03RP] through the
Jacobian). -/
theorem picardDegreeZero_divisible (hdim : topologicalKrullDim C ≤ 1) {ℓ : ℕ}
    (hℓ : IsUnit (ℓ : k)) (x : picardDegreeZero k f hdim) : ∃ y, ℓ • y = x :=
  exists_nsmul_eq_of_mem_picardDegreeZero f hdim hℓ x

/-- **`T_ℓ Pic⁰(C)` is free of finite rank over `ℤ_ℓ`** (of rank `2g`, through the Jacobian). -/
theorem module_free_finite_tateModule_picardDegreeZero (hdim : topologicalKrullDim C ≤ 1)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : k)) :
    Module.Free ℤ_[ℓ] (Stacks.AbelianGroup.tateModule (picardDegreeZero k f hdim) ℓ) ∧
      Module.Finite ℤ_[ℓ] (Stacks.AbelianGroup.tateModule (picardDegreeZero k f hdim) ℓ) := by
  obtain ⟨J, _, _, E, -⟩ := exists_jacobian_data f k hdim
  have htors : ∀ n, Nonempty (AddSubgroup.torsionBy (picardDegreeZero k f hdim)
      ((ℓ ^ n : ℕ) : ℤ) ≃+ (Fin (2 * Stacks.Groupoids.abelianVarietyDimension J) → ZMod (ℓ ^ n))) :=
    fun n => ⟨(Stacks.AbelianGroup.torsionAddEquiv E _).symm.trans
      (Stacks.Groupoids.nonempty_torsionBy_pow_addEquiv J ℓ hℓ n).some⟩
  exact ⟨Stacks.AbelianGroup.module_free_tateModule (picardDegreeZero_divisible f hdim hℓ) htors,
    Stacks.AbelianGroup.module_finite_tateModule (picardDegreeZero_divisible f hdim hℓ) htors⟩

/-- The `ℓ^n`-torsion of `Pic⁰(C)`, in the model `schemePicard`, is the `ℓ^n`-torsion of
`Pic(C)` in the model `Stacks.Picard.ofScheme` used by `picardTorsionTrace`. -/
def picardDegreeZeroTorsionEquiv (hdim : topologicalKrullDim C ≤ 1) (ℓ n : ℕ) [NeZero ℓ] :
    AddSubgroup.torsionBy (picardDegreeZero k f hdim) ((ℓ ^ n : ℕ) : ℤ) ≃+
      Submodule.torsionBy ℤ (Stacks.Picard.ofScheme C) ((ℓ : ℤ) ^ n) where
  toFun x := ⟨(Stacks.GluePicard.picardModelAddEquiv C.toRingedSpace).symm x.1.1, by
    have hx : ((ℓ ^ n : ℕ) : ℤ) • x.1 = 0 := x.2
    rw [Submodule.mem_torsionBy_iff, ← map_zsmul, ← Nat.cast_pow,
      ← AddSubgroup.coe_zsmul, hx, ZeroMemClass.coe_zero, map_zero]⟩
  invFun y := ⟨⟨Stacks.GluePicard.picardModelAddEquiv C.toRingedSpace y.1, by
      refine mem_picardDegreeZero_of_nsmul_eq_zero k f hdim (pow_ne_zero n (NeZero.ne ℓ)) _ ?_
      have hy := (Submodule.mem_torsionBy_iff _ _).1 y.2
      rw [← natCast_zsmul, Nat.cast_pow, ← map_zsmul, hy, map_zero]⟩, by
    apply Subtype.ext
    have hy := (Submodule.mem_torsionBy_iff _ _).1 y.2
    change ((ℓ ^ n : ℕ) : ℤ) • Stacks.GluePicard.picardModelAddEquiv C.toRingedSpace y.1 = 0
    rw [Nat.cast_pow, ← map_zsmul, hy, map_zero]⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_add' x y := by ext; simp

/-- **`Tr_J(φ^*)` modulo `ℓ^n` is the trace of `φ^*` on `Pic(C)[ℓ^n]`**: the trace
`Stacks.EtaleCohomology.picardTorsionTrace` of the statement `WeilTraceInput`. -/
theorem toZModPow_jacobianTateTrace (hdim : topologicalKrullDim C ≤ 1) (φ : C ⟶ C)
    (w : φ ≫ f = f) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : k)) (n : ℕ) :
    haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
    PadicInt.toZModPow n (jacobianTateTrace f hdim φ w ℓ) =
      Stacks.EtaleCohomology.picardTorsionTrace C (Stacks.Picard.schemePullbackClassHom φ) ℓ n := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  obtain ⟨_, _⟩ := module_free_finite_tateModule_picardDegreeZero f hdim ℓ hℓ
  let g : Submodule.torsionBy ℤ (Stacks.Picard.ofScheme C) ((ℓ : ℤ) ^ n) →+
      Submodule.torsionBy ℤ (Stacks.Picard.ofScheme C) ((ℓ : ℤ) ^ n) :=
    Stacks.Picard.torsionByRestrict (A := Stacks.Picard.ofScheme C)
      (Stacks.Picard.schemePullbackClassHom (X := C) (Y := C) φ) ((ℓ : ℤ) ^ n)
  refine Stacks.AbelianGroup.toZModPow_trace_tateModuleMap (picardDegreeZero_divisible f hdim hℓ)
    (picardDegreeZeroPullback f hdim φ w) (picardDegreeZeroTorsionEquiv f hdim ℓ n) g
    fun x => ?_
  apply Subtype.ext
  show Stacks.Picard.schemePullbackClass φ
      ((Stacks.GluePicard.picardModelAddEquiv C.toRingedSpace).symm x.1.1) =
    (Stacks.GluePicard.picardModelAddEquiv C.toRingedSpace).symm
      (schemePicardPullbackHom φ x.1.1)
  simp [schemePicardPullbackHom]

end AlgClosed

end AlgebraicGeometry.CurveGraph

namespace Stacks.PicardFunctor

section Jacobian

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk) (Ψ : X ⟶ X)
  (hΨ : Ψ ≫ B.inclusion.map f = B.inclusion.map f)
  [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [IsProjectiveVariety k (B.inclusion.map f)]
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 (Spec (.of k)))
  [(picardFunctor B hX hk f).IsRepresentable] [IsSepClosed k]

/-- `T_ℓ` of two additive maps with composite the identity composes to the identity. -/
private theorem tateModuleMap_comp_eq_id {M N : Type*} [AddCommGroup M] [AddCommGroup N] (ℓ : ℕ)
    [Fact ℓ.Prime] (g : N →+ M) (f : M →+ N) (h : g.comp f = AddMonoidHom.id M) :
    Stacks.AbelianGroup.tateModuleMap ℓ g ∘ₗ Stacks.AbelianGroup.tateModuleMap ℓ f =
      LinearMap.id := by
  rw [← Stacks.AbelianGroup.tateModuleMap_comp, h, Stacks.AbelianGroup.tateModuleMap_id]

/-- On `J(k) = Pic⁰(X)`, `φ^*` on the Jacobian is the pullback of line bundles. -/
theorem jacobianPointsAddEquiv_jacobianPullback (hdim : topologicalKrullDim X ≤ 1)
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ (jacobianGrp B hX hk f σ hσ).X) :
    jacobianPointsAddEquiv B hX hk f σ hσ hdim
        (Additive.ofMul (x ≫ jacobianPullback B hX hk f Ψ hΨ σ hσ)) =
      AlgebraicGeometry.CurveGraph.picardDegreeZeroPullback (B.inclusion.map f) hdim Ψ hΨ
        (jacobianPointsAddEquiv B hX hk f σ hσ hdim (Additive.ofMul x)) := by
  apply Subtype.ext
  rw [AlgebraicGeometry.CurveGraph.coe_picardDegreeZeroPullback]
  apply (Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace).symm.injective
  rw [jacobianPointsAddEquiv_comp_jacobianPullback B hX hk f Ψ hΨ σ hσ hdim x]
  have h := schemePicardPullbackHom_picardModelAddEquiv Ψ
    ((Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace).symm
      (jacobianPointsAddEquiv B hX hk f σ hσ hdim (Additive.ofMul x)).1)
  rw [AddEquiv.apply_symm_apply] at h
  rw [h, AddEquiv.symm_apply_apply]

/-- **The trace of `φ^*` on the Tate module of the Jacobian is `jacobianTateTrace`.** -/
theorem trace_tateModuleMap_jacobianPullback (hdim : topologicalKrullDim X ≤ 1) (ℓ : ℕ)
    [Fact ℓ.Prime] :
    haveI := isAbelianVariety_jacobian B hX hk f σ hσ
    LinearMap.trace ℤ_[ℓ] _
        (Stacks.Groupoids.tateModuleMap ℓ (jacobianPullback B hX hk f Ψ hΨ σ hσ)) =
      AlgebraicGeometry.CurveGraph.jacobianTateTrace (B.inclusion.map f) hdim Ψ hΨ ℓ := by
  have := isAbelianVariety_jacobian B hX hk f σ hσ
  set E := jacobianPointsAddEquiv B hX hk f σ hσ hdim
  set p := AlgebraicGeometry.CurveGraph.picardDegreeZeroPullback (B.inclusion.map f) hdim Ψ hΨ
  let eT : Stacks.AbelianGroup.tateModule
      (Additive (𝟙_ (Over (Spec (.of k))) ⟶ (jacobianGrp B hX hk f σ hσ).X)) ℓ ≃ₗ[ℤ_[ℓ]]
      Stacks.AbelianGroup.tateModule (picardDegreeZero k (B.inclusion.map f) hdim) ℓ :=
    LinearEquiv.ofLinearMap (Stacks.AbelianGroup.tateModuleMap ℓ E.toAddMonoidHom)
    (Stacks.AbelianGroup.tateModuleMap ℓ E.symm.toAddMonoidHom)
    (tateModuleMap_comp_eq_id ℓ _ _ (by ext; simp))
    (tateModuleMap_comp_eq_id ℓ _ _ (by ext; simp))
  have key : Stacks.Groupoids.tateModuleMap ℓ (jacobianPullback B hX hk f Ψ hΨ σ hσ) =
      eT.symm.conj (Stacks.AbelianGroup.tateModuleMap ℓ p) := by
    refine LinearMap.ext fun x => Stacks.AbelianGroup.tateModule_ext fun n => ?_
    rw [LinearEquiv.conj_apply, Stacks.Groupoids.tateModuleMap_seq]
    show _ = E.symm (p (E ((x : ℕ → _) n)))
    rw [AddEquiv.eq_symm_apply, jacobianPointsAddEquiv_jacobianPullback B hX hk f Ψ hΨ σ hσ hdim]
    rfl
  rw [key, LinearMap.trace_conj']
  rfl

end Jacobian

end Stacks.PicardFunctor

end
