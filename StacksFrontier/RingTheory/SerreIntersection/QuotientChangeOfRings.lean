module

public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToTheDiagonal.SerreMultiplicity
public import StacksFrontier.RingTheory.SerreIntersection.DiagonalTor
public import StacksFrontier.RingTheory.Tor.Balancing

/-!
# `Tor` over a ring and over its quotient by a nonzerodivisor

Let `S → T` be surjective with kernel `(f)`, `f` a nonzerodivisor of `S`. For a `T`-module `M`
and a finite `S`-module `N` on which `f` is a nonzerodivisor, over a Noetherian `S`,

`Tor_i^S(N, M) ≅ Tor_i^T(T ⊗_S N, M)`

as `S`-modules.

## Main results

* `Stacks.SerreIntersection.nonempty_tor'_quotient_equiv`: the isomorphism in positive degrees.
* `Stacks.SerreIntersection.length_tor_quotient`: equality of the lengths in every degree.
* `Stacks.SerreIntersection.torEulerCharacteristic_quotient`: `χ^S(M, N) = χ^T(M, T ⊗_S N)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct Pointwise

universe u

namespace Stacks.SerreIntersection

section Reduction

variable {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
  (hT : Function.Surjective (algebraMap S T)) {f : S}
  (hf : RingHom.ker (algebraMap S T) = Ideal.span {f})

/-- `T ≅ S ⧸ (f)`, `S`-linearly. -/
def quotientLinearEquiv : T ≃ₗ[S] S ⧸ Ideal.span {f} :=
  (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId S T) hT).symm.toLinearEquiv.trans
    (Ideal.quotientEquivAlgOfEq S
      (show RingHom.ker (Algebra.ofId S T) = Ideal.span {f} from hf)).toLinearEquiv

/-- `quotientLinearEquiv` sends `1` to `1`. -/
theorem quotientLinearEquiv_one : quotientLinearEquiv hT hf (1 : T) = 1 := by
  show (Ideal.quotientEquivAlgOfEq S
    (show RingHom.ker (Algebra.ofId S T) = Ideal.span {f} from hf))
      ((Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId S T) hT).symm 1) = 1
  rw [map_one, map_one]

/-- `T ⊗_S X` is `X / f X`, `S`-linearly. -/
def baseChangeEquivQuotSMulTop (X : Type u) [AddCommGroup X] [Module S X] :
    T ⊗[S] X ≃ₗ[S] QuotSMulTop f X :=
  (LinearEquiv.rTensor X (quotientLinearEquiv hT hf)).trans
    (QuotSMulTop.equivQuotTensor f X).symm

/-- `baseChangeEquivQuotSMulTop` sends `1 ⊗ x` to the class of `x`. -/
theorem baseChangeEquivQuotSMulTop_one_tmul (X : Type u) [AddCommGroup X] [Module S X] (x : X) :
    baseChangeEquivQuotSMulTop hT hf X ((1 : T) ⊗ₜ x) = Submodule.Quotient.mk x := by
  rw [baseChangeEquivQuotSMulTop, LinearEquiv.trans_apply, LinearEquiv.rTensor_tmul,
    quotientLinearEquiv_one, LinearEquiv.symm_apply_eq]
  rfl

include hT hf in
/-- Reduction modulo `f` is injective on a submodule `K ⊆ X` when `f` is a nonzerodivisor on
`X ⧸ K`. -/
theorem baseChange_subtype_injective {X : Type u} [AddCommGroup X] [Module S X]
    (K : Submodule S X) (hK : IsSMulRegular (X ⧸ K) f) :
    Function.Injective (LinearMap.baseChange T K.subtype) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨z, rfl⟩ := (baseChangeEquivQuotSMulTop hT hf K).symm.surjective z
  obtain ⟨k, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  have h1 : ((baseChangeEquivQuotSMulTop hT hf K).symm (Submodule.Quotient.mk k)) =
      (1 : T) ⊗ₜ k := by
    rw [LinearEquiv.symm_apply_eq, baseChangeEquivQuotSMulTop_one_tmul]
  rw [h1, LinearMap.baseChange_tmul] at hz
  have h2 := congrArg (baseChangeEquivQuotSMulTop hT hf X) hz
  rw [baseChangeEquivQuotSMulTop_one_tmul, map_zero, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_smul_pointwise_iff_exists] at h2
  obtain ⟨v, -, hv⟩ := h2
  have hvK : v ∈ K := (Submodule.Quotient.mk_eq_zero _).mp <| hK (by
    show f • Submodule.Quotient.mk v = f • 0
    rw [smul_zero, ← Submodule.Quotient.mk_smul, hv, Submodule.Quotient.mk_eq_zero]
    exact k.2)
  rw [LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_smul_pointwise_iff_exists]
  exact ⟨⟨v, hvK⟩, Submodule.mem_top, Subtype.ext hv⟩

end Reduction

section TorShift

variable {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]

/-- A `T`-module with a compatible `S`-module structure is its own twist along `S → T`. -/
def twistEquivOfIsScalarTower (P : Type u) [AddCommGroup P] [Module T P] [Module S P]
    [IsScalarTower S T P] : Twist (algebraMap S T) P ≃ₗ[S] P where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' s x := algebraMap_smul T s (show P from x)
  left_inv _ := rfl
  right_inv _ := rfl

variable (M : Type u) [AddCommGroup M] [Module T M] [Module S M] [IsScalarTower S T M]

/-- `(T ⊗_S X) ⊗_T M ≅ X ⊗_S M`, `S`-linearly. -/
def baseChangeTensorEquiv (X : Type u) [AddCommGroup X] [Module S X] :
    Twist (algebraMap S T) ((T ⊗[S] X) ⊗[T] M) ≃ₗ[S] X ⊗[S] M :=
  (Twist.congr (TensorProduct.comm T (T ⊗[S] X) M)).trans
    ((Twist.congr (TensorProduct.AlgebraTensorModule.cancelBaseChange S T T M X)).trans
      ((twistEquivOfIsScalarTower (M ⊗[S] X)).trans (TensorProduct.comm S M X)))

/-- `baseChangeTensorEquiv` sends `(t ⊗ x) ⊗ m` to `x ⊗ t • m`. -/
theorem baseChangeTensorEquiv_tmul (X : Type u) [AddCommGroup X] [Module S X] (t : T) (x : X)
    (m : M) : baseChangeTensorEquiv (T := T) M X (Twist.mk _ ((t ⊗ₜ[S] x) ⊗ₜ[T] m)) =
      x ⊗ₜ[S] (t • m) := rfl

/-- `baseChangeTensorEquiv` is natural in `X`: it intertwines `(T ⊗_S g) ⊗_T M` with
`g ⊗_S M` for an `S`-linear map `g : X → X'`. -/
theorem baseChangeTensorEquiv_naturality {X X' : Type u} [AddCommGroup X] [Module S X]
    [AddCommGroup X'] [Module S X'] (g : X →ₗ[S] X')
    (z : Twist (algebraMap S T) ((T ⊗[S] X) ⊗[T] M)) :
    baseChangeTensorEquiv (T := T) M X' (twistMap (algebraMap S T)
        (LinearMap.rTensor M (LinearMap.baseChange T g)) z) =
      LinearMap.rTensor M g (baseChangeTensorEquiv (T := T) M X z) := by
  obtain ⟨z, rfl⟩ : ∃ z' : (T ⊗[S] X) ⊗[T] M, Twist.mk _ z' = z := ⟨z, rfl⟩
  induction z using TensorProduct.induction_on with
  | zero => simp only [Twist.mk_zero, map_zero]
  | add x y hx hy => rw [← Twist.mk_add, map_add, map_add, map_add, hx, hy, map_add]
  | tmul y m =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.zero_tmul, Twist.mk_zero, map_zero]
    | add a b ha hb =>
      rw [TensorProduct.add_tmul, ← Twist.mk_add, map_add, map_add, map_add, ha, hb, map_add]
    | tmul t x =>
      show baseChangeTensorEquiv (T := T) M X' (Twist.mk _ ((t ⊗ₜ[S] g x) ⊗ₜ[T] m)) = _
      rw [baseChangeTensorEquiv_tmul, baseChangeTensorEquiv_tmul, LinearMap.rTensor_tmul]

/-- The kernel of `K ⊗_S M → X ⊗_S M` for a submodule `K ⊆ X` is that of
`(T ⊗_S K) ⊗_T M → (T ⊗_S X) ⊗_T M`, `S`-linearly. -/
def kerRTensorBaseChangeEquiv {X : Type u} [AddCommGroup X] [Module S X] (K : Submodule S X) :
    LinearMap.ker (LinearMap.rTensor M K.subtype) ≃ₗ[S] Twist (algebraMap S T)
      (LinearMap.ker (LinearMap.rTensor M (LinearMap.baseChange T K.subtype))) :=
  (kerEquivOfComm _ _ (baseChangeTensorEquiv (T := T) M K) (baseChangeTensorEquiv (T := T) M X)
    (fun z ↦ baseChangeTensorEquiv_naturality M K.subtype z)).symm.trans
    (twistKerEquiv (algebraMap S T) _).symm

variable [IsNoetherianRing S] (hT : Function.Surjective (algebraMap S T)) {f : S}
  (hf : RingHom.ker (algebraMap S T) = Ideal.span {f}) (hfS : IsSMulRegular S f)

omit [IsNoetherianRing S] in
include hfS in
/-- A nonzerodivisor of `S` is a nonzerodivisor on the free module `S^j`. -/
theorem isSMulRegular_pi (j : ℕ) : IsSMulRegular (Fin j → S) f := fun _ _ h ↦
  funext fun i ↦ hfS (congrFun h i)

omit [IsNoetherianRing S] in
/-- For a surjection `p : S^j → N`, base change to `T` gives an exact sequence
`T ⊗_S ker p → T ⊗_S S^j → T ⊗_S N`. -/
theorem exact_baseChange_cover {N : Type u} [AddCommGroup N] [Module S N] {j : ℕ}
    (p : (Fin j → S) →ₗ[S] N) (hp : Function.Surjective p) :
    Function.Exact (LinearMap.baseChange T (LinearMap.ker p).subtype)
      (LinearMap.baseChange T p) := by
  rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
  exact lTensor_exact T (LinearMap.exact_subtype_ker_map p) hp

/-- The reduction modulo `f` of a finite free cover, a short exact sequence when `f` is a
nonzerodivisor on the covered module. -/
def coverSCReduce {N : Type u} [AddCommGroup N] [Module S N] {j : ℕ}
    (p : (Fin j → S) →ₗ[S] N) (hp : Function.Surjective p) : ShortComplex (ModuleCat.{u} T) :=
  ShortComplex.mk (ModuleCat.ofHom (LinearMap.baseChange T (LinearMap.ker p).subtype))
    (ModuleCat.ofHom (LinearMap.baseChange T p)) (ModuleCat.hom_ext
      (LinearMap.ext fun x ↦ (exact_baseChange_cover p hp).apply_apply_eq_zero x))

omit [IsNoetherianRing S] in
include hT hf in
/-- The reduction modulo `f` of a finite free cover of `N` is short exact when `f` is a
nonzerodivisor on `N`. -/
theorem coverSCReduce_shortExact {N : Type u} [AddCommGroup N] [Module S N] {j : ℕ}
    (p : (Fin j → S) →ₗ[S] N) (hp : Function.Surjective p) (hN : IsSMulRegular N f) :
    (coverSCReduce (T := T) p hp).ShortExact := by
  refine ModuleCat.shortComplex_shortExact _ (exact_baseChange_cover p hp)
    (baseChange_subtype_injective hT hf _ fun a b hab ↦ ?_) ?_
  · change f • a = f • b at hab
    let e := p.quotKerEquivOfSurjective hp
    exact e.injective (hN (show f • e a = f • e b by rw [← map_smul, ← map_smul, hab]))
  · show Function.Surjective (LinearMap.baseChange T p)
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective _ hp

/-- The `T`-module `T ⊗_S S^j` is projective. -/
instance projective_baseChange_pi (j : ℕ) :
    Projective (ModuleCat.of T (T ⊗[S] (Fin j → S))) :=
  (ModuleCat.of T (T ⊗[S] (Fin j → S))).projective_of_categoryTheory_projective

include hT hf hfS in
/-- **`Tor` against a module over the quotient.** For a `T`-module `M` and a finite `S`-module
`N` on which `f` is a nonzerodivisor, `Tor_{i}^S(N, M) ≅ Tor_{i}^T(T ⊗_S N, M)` in positive
degrees, `S`-linearly. -/
theorem nonempty_tor'_quotient_equiv (n : ℕ) :
    ∀ (N : Type u) [AddCommGroup N] [Module S N] [Module.Finite S N], IsSMulRegular N f →
      Nonempty (((Tor' (ModuleCat.{u} S) (n + 1)).obj (ModuleCat.of S N)).obj (ModuleCat.of S M)
        ≃ₗ[S] Twist (algebraMap S T) (((Tor' (ModuleCat.{u} T) (n + 1)).obj
          (ModuleCat.of T (T ⊗[S] N))).obj (ModuleCat.of T M))) := by
  induction n with
  | zero =>
    intro N _ _ _ hN
    obtain ⟨j, p, hp⟩ := Module.Finite.exists_fin' S N
    have hS := coverSC_shortExact p hp
    have hST := coverSCReduce_shortExact hT hf p hp hN
    have : Projective (coverSC p).X₂ :=
      (ModuleCat.of S (Fin j → S)).projective_of_categoryTheory_projective
    have hR : IsZero (((Tor' (ModuleCat.{u} S) 1).obj (coverSC p).X₂).obj (ModuleCat.of S M)) :=
      isZero_Tor'_succ_of_projective _ _ _ 0
    have : Projective (coverSCReduce (T := T) p hp).X₂ := projective_baseChange_pi j
    have hR' : IsZero (((Tor' (ModuleCat.{u} T) 1).obj (coverSCReduce (T := T) p hp).X₂).obj
        (ModuleCat.of T M)) := isZero_Tor'_succ_of_projective _ _ _ 0
    let eS := (tor'OneIsoKernel hS (ModuleCat.of S M) hR ≪≫ ModuleCat.kernelIsoKer _).toLinearEquiv
    let eT := (tor'OneIsoKernel hST (ModuleCat.of T M) hR' ≪≫
      ModuleCat.kernelIsoKer _).toLinearEquiv
    exact ⟨eS.trans ((kerRTensorBaseChangeEquiv M (LinearMap.ker p)).trans
      (Twist.congr eT.symm))⟩
  | succ n ih =>
    intro N _ _ _ hN
    obtain ⟨j, p, hp⟩ := Module.Finite.exists_fin' S N
    have hS := coverSC_shortExact p hp
    have hST := coverSCReduce_shortExact hT hf p hp hN
    have : Projective (coverSC p).X₂ :=
      (ModuleCat.of S (Fin j → S)).projective_of_categoryTheory_projective
    have : Projective (coverSCReduce (T := T) p hp).X₂ := projective_baseChange_pi j
    let eS := (tor'δFirstIso hS (ModuleCat.of S M) (n + 1)
      (isZero_Tor'_succ_of_projective _ _ _ (n + 1))
      (isZero_Tor'_succ_of_projective _ _ _ n)).toLinearEquiv
    let eT := (tor'δFirstIso hST (ModuleCat.of T M) (n + 1)
      (isZero_Tor'_succ_of_projective _ _ _ (n + 1))
      (isZero_Tor'_succ_of_projective _ _ _ n)).toLinearEquiv
    obtain ⟨e⟩ := ih (LinearMap.ker p) fun a b hab ↦
      Subtype.ext (isSMulRegular_pi hfS j (congrArg Subtype.val hab))
    exact ⟨eS.trans (e.trans (Twist.congr eT.symm))⟩

end TorShift

section Lengths

variable {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
  (M : Type u) [AddCommGroup M] [Module T M] [Module S M] [IsScalarTower S T M]
  [IsNoetherianRing S] (hT : Function.Surjective (algebraMap S T)) {f : S}
  (hf : RingHom.ker (algebraMap S T) = Ideal.span {f}) (hfS : IsSMulRegular S f)

include hT hf hfS in
/-- **Lengths of `Tor` over the quotient by a nonzerodivisor.** For a `T`-module `M` and a finite
`S`-module `N` on which `f` is a nonzerodivisor, `length_S Tor_i^S(M, N) =
length_T Tor_i^T(M, T ⊗_S N)` for every `i`. -/
theorem length_tor_quotient (N : Type u) [AddCommGroup N] [Module S N] [Module.Finite S N]
    (hN : IsSMulRegular N f) (i : ℕ) :
    Module.length S (((Tor (ModuleCat.{u} S) i).obj (ModuleCat.of S M)).obj (ModuleCat.of S N)) =
      Module.length T (((Tor (ModuleCat.{u} T) i).obj (ModuleCat.of T M)).obj
        (ModuleCat.of T (T ⊗[S] N))) := by
  have hTw : ∀ (X : Type u) [AddCommGroup X] [Module T X],
      Module.length S (Twist (algebraMap S T) X) = Module.length T X := fun X _ _ ↦
    Twist.length_eq _ X (fun b ↦ by
      obtain ⟨r, rfl⟩ := hT b
      exact ⟨r, fun _ ↦ rfl⟩)
  let eS := ((torFlip_iso_Tor' S i).app (ModuleCat.of S N)).app (ModuleCat.of S M)
  let eT := ((torFlip_iso_Tor' T i).app (ModuleCat.of T (T ⊗[S] N))).app (ModuleCat.of T M)
  refine eS.toLinearEquiv.length_eq.trans (Eq.trans ?_ eT.toLinearEquiv.length_eq.symm)
  rw [← hTw]
  cases i with
  | zero =>
    let zS := (((tensoringRight (ModuleCat.{u} S)).obj
      (ModuleCat.of S M)).leftDerivedZeroIsoSelf.app (ModuleCat.of S N))
    let zT := (((tensoringRight (ModuleCat.{u} T)).obj
      (ModuleCat.of T M)).leftDerivedZeroIsoSelf.app (ModuleCat.of T (T ⊗[S] N)))
    exact (zS.toLinearEquiv.trans ((baseChangeTensorEquiv (T := T) M N).symm.trans
      (Twist.congr zT.toLinearEquiv.symm))).length_eq
  | succ n => exact (nonempty_tor'_quotient_equiv M hT hf hfS n N hN).some.length_eq

include hT hf hfS in
/-- **The Euler characteristic over the quotient by a nonzerodivisor**:
`χ^S(M, N) = χ^T(M, T ⊗_S N)` for a `T`-module `M` and a finite `S`-module `N` on which `f` is a
nonzerodivisor. -/
theorem torEulerCharacteristic_quotient (N : Type u) [AddCommGroup N] [Module S N]
    [Module.Finite S N] (hN : IsSMulRegular N f) :
    Stacks.Intersection.torEulerCharacteristic S M N =
      Stacks.Intersection.torEulerCharacteristic T M (T ⊗[S] N) := by
  simp only [Stacks.Intersection.torEulerCharacteristic, length_tor_quotient M hT hf hfS N hN]

end Lengths

section Congr

variable {A : Type u} [CommRing A]

/-- The Euler characteristic depends on the first module only up to isomorphism. -/
theorem torEulerCharacteristic_congr_left {M M' : Type u} [AddCommGroup M] [Module A M]
    [AddCommGroup M'] [Module A M'] (e : M ≃ₗ[A] M') (N : Type u) [AddCommGroup N]
    [Module A N] :
    Stacks.Intersection.torEulerCharacteristic A M N =
      Stacks.Intersection.torEulerCharacteristic A M' N := by
  unfold Stacks.Intersection.torEulerCharacteristic
  congr 1
  funext i
  rw [(((Tor (ModuleCat.{u} A) i).mapIso e.toModuleIso).app
    (ModuleCat.of A N)).toLinearEquiv.length_eq]

/-- **The Euler characteristic is symmetric**: `χ(M, N) = χ(N, M)`. -/
theorem torEulerCharacteristic_comm (M N : Type u) [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] :
    Stacks.Intersection.torEulerCharacteristic A M N =
      Stacks.Intersection.torEulerCharacteristic A N M := by
  unfold Stacks.Intersection.torEulerCharacteristic
  congr 1
  funext i
  obtain ⟨e⟩ := tor_symm_canonically_iso A i
  rw [((e.app (ModuleCat.of A M)).app (ModuleCat.of A N)).toLinearEquiv.length_eq]
  rfl

end Congr

end Stacks.SerreIntersection
