module

public import Mathlib.RingTheory.TotallySplit
public import StacksFrontier.RingTheory.FinitePresentation.Relative
public import StacksFrontier.Algebra.Module.FinitePresentation.Transport
public import StacksCore.RingTheory.FiniteStability
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Base change of relatively finitely presented modules

Let `R → A` be a finite type ring map and let `M` be an `A`-module that is finitely presented
relative to `R`, in the sense of `Module.FinitePresentationRel`.

## Main definitions

* `baseChangeCollapseEquiv`: for a surjective `algebraMap P A`, the `A`-linear isomorphism
  `A ⊗[P] M ≃ M`, `a ⊗ m ↦ a • m`.
* `baseChangeQuotientLinearEquiv`: for presentations `α : P ↠ A` and `β : P'' ↠ A'` with
  `P = R[x_1, …, x_n]` and `P'' = A[y_1, …, y_m]`, the identification of `A' ⊗[A] M` with
  `(P' ⧸ ker δ) ⊗[P'] (P' ⊗[P] M)`, where `P' = P[y_1, …, y_m]` and `δ : P' ↠ A'` is the
  combined surjection.

## Main results

* `finiteType_tensorProduct_rightAlgebra`: if `R → A` is of finite type, then so is
  `R' → A ⊗[R] R'` for any ring map `R → R'`.
* `finitePresentation_relative_baseChange`: for any ring map `R → R'`, the module
  `(A ⊗[R] R') ⊗[A] M` is finitely presented relative to `R'`.
* `finitelyPresentedRelative_baseChange`: for a ring map `A → A'` of finite presentation, the
  `A'`-module `A' ⊗[A] M` is finitely presented relative to `R`.

## Implementation notes

The ring `A ⊗[R] R'` carries `Algebra R' (A ⊗[R] R')` via `Algebra.TensorProduct.rightAlgebra`
and `Algebra A (A ⊗[R] R')` via `Algebra.TensorProduct.leftAlgebra`; both are introduced
explicitly in the statement of `finitePresentation_relative_baseChange`.
-/
open scoped TensorProduct

/-- If `R → A` is of finite type, then so is `R' → A ⊗[R] R'` for any `R → R'`. -/
theorem finiteType_tensorProduct_rightAlgebra (R A R' : Type*) [CommRing R] [CommRing A]
    [CommRing R'] [Algebra R A] [Algebra R R'] [Algebra.FiniteType R A] :
    letI : Algebra R' (A ⊗[R] R') := Algebra.TensorProduct.rightAlgebra
    Algebra.FiniteType R' (A ⊗[R] R') :=
  let : Algebra R' (A ⊗[R] R') := Algebra.TensorProduct.rightAlgebra
  .of_surjective (Algebra.TensorProduct.commRight R R' A).toAlgHom
    (Algebra.TensorProduct.commRight R R' A).surjective

section tensorBaseChangeEquiv

variable {R P R' M : Type*} [CommRing R] [CommRing P] [Algebra R P] [CommRing R']
  [Algebra R R'] [AddCommGroup M] [Module R M] [Module P M] [IsScalarTower R P M]

/-- The inverse of `Module.tensorBaseChangeEquiv` on pure tensors. -/
@[simp]
theorem Module.tensorBaseChangeEquiv_symm_tmul (x : M) (r : R') :
    (Module.tensorBaseChangeEquiv (R := R) (S := P)).symm (x ⊗ₜ[R] r) = (1 ⊗ₜ[R] r) ⊗ₜ[P] x := by
  simp [Module.tensorBaseChangeEquiv]

/-- For `α : P →ₐ[R] A` compatible with the actions on `M`, the identifications
`(P ⊗[R] R') ⊗[P] M ≃ M ⊗[R] R' ≃ (A ⊗[R] R') ⊗[A] M` are semilinear along `α ⊗ id`. -/
theorem Module.tensorBaseChangeEquiv_smul_map {A : Type*} [CommRing A] [Algebra R A] [Module A M]
    [IsScalarTower R A M] (α : P →ₐ[R] A) (hα : ∀ (p : P) (y : M), p • y = α p • y)
    (s : P ⊗[R] R') (x : (P ⊗[R] R') ⊗[P] M) :
    Module.tensorBaseChangeEquiv (s • x) =
      Module.tensorBaseChangeEquiv (Algebra.TensorProduct.map α (AlgHom.id R R') s •
        (Module.tensorBaseChangeEquiv (R := R) (S := A)).symm
          (Module.tensorBaseChangeEquiv x)) := by
  induction s using TensorProduct.inductionOn with
  | add s₁ s₂ h₁ h₂ => simp only [add_smul, map_add, h₁, h₂]
  | tmul p r =>
    induction x using TensorProduct.inductionOn with
    | add x₁ x₂ h₁ h₂ => simp only [smul_add, map_add, h₁, h₂]
    | tmul b x =>
      induction b using TensorProduct.inductionOn with
      | add b₁ b₂ h₁ h₂ => simp only [TensorProduct.add_tmul, smul_add, map_add, h₁, h₂]
      | tmul q r₂ => simp [TensorProduct.smul_tmul', mul_smul, hα]

end tensorBaseChangeEquiv

/-- Let `R → A` be a finite type ring map and `M` an `A`-module finitely presented relative
to `R`. For any ring map `R → R'`, set
`A' := A ⊗[R] R'` (an `R'`-algebra via the right factor and, canonically, an `A`-algebra via
the left factor) and `M' := A' ⊗[A] M` (an `A'`-module via the left tensor factor `A'`). Then
`R' → A'` is of finite type, and `M'` is finitely presented relative to `R'`. -/
@[stacks 065B, ega "IV 1.3.1", ega "IV 1.4.1" "more general"]
theorem finitePresentation_relative_baseChange (R A R' M : Type*)
    [CommRing R] [CommRing A] [CommRing R'] [Algebra R A] [Algebra R R']
    [AddCommGroup M] [Module A M] [Algebra.FiniteType R A]
    (hM : Module.FinitePresentationRel R A M) :
    letI : Algebra R' (TensorProduct R A R') := Algebra.TensorProduct.rightAlgebra
    letI : Algebra A (TensorProduct R A R') := Algebra.TensorProduct.leftAlgebra
    Algebra.FiniteType R' (TensorProduct R A R') ∧
    Module.FinitePresentationRel R' (TensorProduct R A R')
      (TensorProduct A (TensorProduct R A R') M) := by
  let : Algebra R' (A ⊗[R] R') := Algebra.TensorProduct.rightAlgebra
  refine ⟨finiteType_tensorProduct_rightAlgebra R A R', ?_⟩
  obtain ⟨n, α, hα, hfp⟩ := hM
  let P := MvPolynomial (Fin n) R
  let P' := MvPolynomial (Fin n) R'
  let : Module P M := Module.compHom M α.toRingHom
  have : Module.FinitePresentation P M := hfp
  let g : P' ≃ₐ[R'] R' ⊗[R] P := (MvPolynomial.algebraTensorAlgEquiv R R').symm
  let m : R' ⊗[R] P →ₐ[R'] R' ⊗[R] A := Algebra.TensorProduct.map (AlgHom.id R' R') α
  let c := Algebra.TensorProduct.commRight R R' A
  let β : P' →ₐ[R'] (A ⊗[R] R') := (c.toAlgHom.comp m).comp g.toAlgHom
  refine ⟨n, β, (c.surjective.comp
    (Algebra.TensorProduct.map_surjective _ _ Function.surjective_id hα)).comp g.surjective, ?_⟩
  let B := P ⊗[R] R'
  let : Module P' (A ⊗[R] R' ⊗[A] M) := Module.compHom (A ⊗[R] R' ⊗[A] M) β.toRingHom
  let e0 : B ≃+* P' :=
    ((Algebra.TensorProduct.comm R P R').toRingEquiv).trans (g.symm.toRingEquiv)
  let Φ : (P ⊗[R] R') →ₐ[R] (A ⊗[R] R') := Algebra.TensorProduct.map α (AlgHom.id R R')
  have hβe0 : ∀ s : B, β (e0 s) = Φ s := by
    intro s
    induction s using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
    | tmul p r' =>
      change c (m (g (g.symm (Algebra.TensorProduct.comm R P R' (p ⊗ₜ[R] r'))))) = _
      rw [Algebra.TensorProduct.comm_tmul, g.apply_symm_apply]
      exact congrArg c (Algebra.TensorProduct.map_tmul _ _ _ _)
  let : Module R M := Module.compHom M (algebraMap R A)
  have : IsScalarTower R A M := .of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower R P M := .of_algebraMap_smul fun r x => by
    change α (algebraMap R P r) • x = algebraMap R A r • x
    rw [AlgHom.commutes]
  let φN := Module.tensorBaseChangeEquiv (R := R) (S := P) (M := M) (R' := R')
  let φM' := Module.tensorBaseChangeEquiv (R := R) (S := A) (M := M) (R' := R')
  refine finitePresentation_of_ringEquiv B P' e0 (B ⊗[P] M) (A ⊗[R] R' ⊗[A] M)
    (φN.toAddEquiv.trans φM'.toAddEquiv.symm) (fun s x => ?_) inferInstance
  change φM'.symm (φN (s • x)) = β (e0 s) • φM'.symm (φN x)
  rw [hβe0, Module.tensorBaseChangeEquiv_smul_map α (fun _ _ => rfl), LinearEquiv.symm_apply_apply]

/-- An element of the ideal generated in a `P`-algebra `P'` by `RingHom.ker α` annihilates the
base change `P' ⊗[P] M`, where `M` is an `A`-module whose `P`-action is the one induced by
`α : P →+* A`. -/
theorem TensorProduct.smul_eq_zero_of_mem_map_ker {P P' A : Type*} [CommRing P] [CommRing P']
    [CommRing A] [Algebra P P'] (M : Type*) [AddCommGroup M] [Module A M] [Module P M]
    (α : P →+* A) (hcompat : ∀ (k : P) (y : M), k • y = α k • y) {z : P'}
    (hz : z ∈ Ideal.map (algebraMap P P') (RingHom.ker α)) (x : P' ⊗[P] M) :
    z • x = 0 := by
  have key : ∀ k : P, α k = 0 → ∀ x : P' ⊗[P] M, (algebraMap P P' k) • x = 0 := by
    intro k hk x
    induction x using TensorProduct.inductionOn with
    | add a b ha hb => rw [smul_add, ha, hb, add_zero]
    | tmul p' mm =>
        rw [algebraMap_smul, TensorProduct.smul_tmul']
        have hkm : k • mm = (0 : M) := by rw [hcompat, hk, zero_smul]
        rw [TensorProduct.smul_tmul, hkm, TensorProduct.tmul_zero]
  rw [Ideal.map, Ideal.span] at hz
  induction hz using Submodule.span_induction with
  | mem z hz => obtain ⟨k, hk, rfl⟩ := hz; exact key k hk x
  | zero => rw [zero_smul]
  | add a b _ _ ha hb => rw [add_smul, ha, hb, add_zero]
  | smul c a _ ha => rw [smul_assoc, ha, smul_zero]

section baseChangeCollapse

variable (P A M : Type*) [CommSemiring P] [CommSemiring A] [Algebra P A]
  [AddCommMonoid M] [Module A M] [Module P M] [IsScalarTower P A M]

/-- For a `P`-algebra `A` with `algebraMap P A` surjective and an `A`-module `M`,
the canonical map `A ⊗[P] M → M`, `a ⊗ m ↦ a • m`, is an `A`-linear isomorphism. -/
noncomputable def baseChangeCollapseEquiv (hsurj : Function.Surjective (algebraMap P A)) :
    A ⊗[P] M ≃ₗ[A] M :=
  LinearEquiv.ofLinearMap
    (TensorProduct.AlgebraTensorModule.lift
      { toFun := fun a => a • (LinearMap.id : M →ₗ[P] M)
        map_add' := fun a b => by ext m; simp [add_smul]
        map_smul' := fun a b => by ext m; simp [mul_smul] })
    { toFun := fun m => (1 : A) ⊗ₜ[P] m
      map_add' := fun x y => by simp [TensorProduct.tmul_add]
      map_smul' := fun a m => by
        simp only [RingHom.id_apply]
        obtain ⟨p, rfl⟩ := hsurj a
        have h1 : (algebraMap P A p) • m = p • m := (algebraMap_smul A p m)
        rw [h1, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
        congr 1
        rw [Algebra.smul_def, mul_one]; simp }
    (by ext m; simp)
    (by ext a; simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq,
        TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
        LinearMap.coe_restrictScalars, TensorProduct.AlgebraTensorModule.lift_tmul,
        LinearMap.coe_mk, AddHom.coe_mk, one_smul])

/-- `baseChangeCollapseEquiv` sends `a ⊗ x` to `a • x`. -/
@[simp]
theorem baseChangeCollapseEquiv_tmul (hsurj : Function.Surjective (algebraMap P A)) (a : A)
    (x : M) : baseChangeCollapseEquiv P A M hsurj (a ⊗ₜ[P] x) = a • x := rfl

/-- The inverse of `baseChangeCollapseEquiv` sends `x` to `1 ⊗ x`. -/
@[simp]
theorem baseChangeCollapseEquiv_symm_apply (hsurj : Function.Surjective (algebraMap P A))
    (x : M) : (baseChangeCollapseEquiv P A M hsurj).symm x = 1 ⊗ₜ[P] x := rfl

end baseChangeCollapse

/-- With `P := MvPolynomial (Fin n) R`, `P' := MvPolynomial (Fin m) P`, `N := P' ⊗[P] M`, and
`δ : P' →ₐ[R] A'` the surjection combining `MvPolynomial.mapAlgHom α` with `β`, the submodule
`(RingHom.ker δ) • ⊤` of `N` is finitely generated when `RingHom.ker β` is. -/
theorem baseChange_smul_top_fg
    (R A A' : Type*) [CommRing R] [CommRing A] [CommRing A']
    [Algebra R A] [Algebra A A'] [Algebra R A'] [IsScalarTower R A A']
    (M : Type*) [AddCommGroup M] [Module A M]
    {n : ℕ} (α : MvPolynomial (Fin n) R →ₐ[R] A) (hα : Function.Surjective α)
    [@Module.FinitePresentation (MvPolynomial (Fin n) R) M _ _
      (Module.compHom M (α : MvPolynomial (Fin n) R →+* A))]
    {m : ℕ} (β : MvPolynomial (Fin m) A →ₐ[A] A')
    (hJ : (RingHom.ker β.toRingHom).FG) :
    letI : Module (MvPolynomial (Fin n) R) M :=
      Module.compHom M (α : MvPolynomial (Fin n) R →+* A)
    (((RingHom.ker
        (((β.restrictScalars R).comp (MvPolynomial.mapAlgHom α) :
            MvPolynomial (Fin m) (MvPolynomial (Fin n) R) →ₐ[R] A').toRingHom)) •
      (⊤ : Submodule (MvPolynomial (Fin m) (MvPolynomial (Fin n) R))
        (TensorProduct (MvPolynomial (Fin n) R)
          (MvPolynomial (Fin m) (MvPolynomial (Fin n) R)) M))).FG) := by
  let : Module (MvPolynomial (Fin n) R) M :=
    Module.compHom M (α : MvPolynomial (Fin n) R →+* A)
  classical
  let f : MvPolynomial (Fin m) (MvPolynomial (Fin n) R) →+* MvPolynomial (Fin m) A :=
    MvPolynomial.map α.toRingHom
  have hf : Function.Surjective f := MvPolynomial.map_surjective α.toRingHom hα
  obtain ⟨G, hG⟩ := hJ
  let G' := G.image (Function.surjInv hf)
  have hmapJ : Ideal.map f (Ideal.span (G' : Set _)) = RingHom.ker β.toRingHom := by
    rw [Ideal.map_span, ← hG, Finset.coe_image, Set.image_image]
    simp [Function.surjInv_eq hf]
  have hdecomp : RingHom.ker ((β.restrictScalars R).comp (MvPolynomial.mapAlgHom α)).toRingHom
      = Ideal.span (G' : Set _) ⊔ RingHom.ker f := by
    rw [show RingHom.ker ((β.restrictScalars R).comp (MvPolynomial.mapAlgHom α)).toRingHom
      = Ideal.comap f (RingHom.ker β.toRingHom) from rfl, ← hmapJ,
      Ideal.comap_map_of_surjective f hf]
    congr 1
  have hannih : RingHom.ker f •
      (⊤ : Submodule (MvPolynomial (Fin m) (MvPolynomial (Fin n) R))
        (TensorProduct (MvPolynomial (Fin n) R)
          (MvPolynomial (Fin m) (MvPolynomial (Fin n) R)) M)) = ⊥ := by
    rw [eq_bot_iff, Submodule.smul_le]
    intro r hr x _
    rw [MvPolynomial.ker_map, ← MvPolynomial.algebraMap_eq] at hr
    exact (Submodule.mem_bot _).mpr
      (TensorProduct.smul_eq_zero_of_mem_map_ker M α.toRingHom (fun _ _ => rfl) hr x)
  rw [hdecomp, Submodule.sup_smul, hannih, sup_bot_eq]
  exact Submodule.FG.smul ⟨G', rfl⟩ Module.Finite.fg_top

/-- With `P := MvPolynomial (Fin n) R`, `P' := MvPolynomial (Fin m) P`, `N := P' ⊗[P] M`, and
`δ : P' →ₐ[R] A'` the surjection combining `MvPolynomial.mapAlgHom α` with `β`, the
`P'`-linear equivalence between `A' ⊗[A] M`, with its `δ`-twisted `P'`-module structure, and
`(P' ⧸ ker δ) ⊗[P'] N`. -/
noncomputable def baseChangeQuotientLinearEquiv
    (R A A' : Type*) [CommRing R] [CommRing A] [CommRing A']
    [Algebra R A] [Algebra A A'] [Algebra R A'] [IsScalarTower R A A']
    (M : Type*) [AddCommGroup M] [Module A M]
    {n : ℕ} (α : MvPolynomial (Fin n) R →ₐ[R] A) (hα : Function.Surjective α)
    {m : ℕ} (β : MvPolynomial (Fin m) A →ₐ[A] A') (hβ : Function.Surjective β) :
    letI : Module (MvPolynomial (Fin n) R) M :=
      Module.compHom M (α : MvPolynomial (Fin n) R →+* A)
    letI : Module (MvPolynomial (Fin m) (MvPolynomial (Fin n) R)) (TensorProduct A A' M) :=
      Module.compHom (TensorProduct A A' M)
        (((β.restrictScalars R).comp (MvPolynomial.mapAlgHom α) :
            MvPolynomial (Fin m) (MvPolynomial (Fin n) R) →ₐ[R] A').toRingHom)
    ((TensorProduct A A' M) ≃ₗ[MvPolynomial (Fin m) (MvPolynomial (Fin n) R)]
      (TensorProduct (MvPolynomial (Fin m) (MvPolynomial (Fin n) R))
        ((MvPolynomial (Fin m) (MvPolynomial (Fin n) R)) ⧸
          (RingHom.ker
            (((β.restrictScalars R).comp (MvPolynomial.mapAlgHom α) :
                MvPolynomial (Fin m) (MvPolynomial (Fin n) R) →ₐ[R] A').toRingHom)))
        (TensorProduct (MvPolynomial (Fin n) R)
          (MvPolynomial (Fin m) (MvPolynomial (Fin n) R)) M))) := by
  letI : Module (MvPolynomial (Fin n) R) M :=
    Module.compHom M (α : MvPolynomial (Fin n) R →+* A)
  let δ : MvPolynomial (Fin m) (MvPolynomial (Fin n) R) →ₐ[R] A' :=
    (β.restrictScalars R).comp (MvPolynomial.mapAlgHom α)
  letI : Module (MvPolynomial (Fin m) (MvPolynomial (Fin n) R)) (TensorProduct A A' M) :=
    Module.compHom (TensorProduct A A' M) δ.toRingHom
  letI : Algebra (MvPolynomial (Fin n) R) A := α.toRingHom.toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin n) R) A M := ⟨fun p a x => mul_smul (α p) a x⟩
  letI : Algebra (MvPolynomial (Fin n) R) A' := ((algebraMap A A').comp α.toRingHom).toAlgebra
  letI : Algebra (MvPolynomial (Fin m) (MvPolynomial (Fin n) R)) A' := δ.toRingHom.toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin n) R) A A' := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (MvPolynomial (Fin n) R)
      (MvPolynomial (Fin m) (MvPolynomial (Fin n) R)) A' := .of_algebraMap_eq fun p => by
    change algebraMap A A' (α p) = β (MvPolynomial.map α.toRingHom (MvPolynomial.C p))
    rw [MvPolynomial.map_C]
    exact (β.commutes (α p)).symm
  let chainA' := (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A' A')
      (baseChangeCollapseEquiv (MvPolynomial (Fin n) R) A M hα)).symm ≪≫ₗ
    TensorProduct.AlgebraTensorModule.cancelBaseChange (MvPolynomial (Fin n) R) A A' A' M ≪≫ₗ
    (TensorProduct.AlgebraTensorModule.cancelBaseChange (MvPolynomial (Fin n) R)
      (MvPolynomial (Fin m) (MvPolynomial (Fin n) R)) A' A' M).symm
  haveI : IsScalarTower (MvPolynomial (Fin m) (MvPolynomial (Fin n) R)) A' A' :=
    IsScalarTower.right
  let qkae : ((MvPolynomial (Fin m) (MvPolynomial (Fin n) R)) ⧸ RingHom.ker δ.toRingHom)
      ≃ₐ[MvPolynomial (Fin m) (MvPolynomial (Fin n) R)] A' :=
    Ideal.quotientKerAlgEquivOfSurjective
      (f := Algebra.ofId (MvPolynomial (Fin m) (MvPolynomial (Fin n) R)) A')
      (hβ.comp (MvPolynomial.map_surjective α.toRingHom hα))
  let chainP' : (A' ⊗[A] M) ≃ₗ[MvPolynomial (Fin m) (MvPolynomial (Fin n) R)]
      A' ⊗[MvPolynomial (Fin m) (MvPolynomial (Fin n) R)]
        (MvPolynomial (Fin m) (MvPolynomial (Fin n) R) ⊗[MvPolynomial (Fin n) R] M) :=
    { chainA'.toAddEquiv with
      map_smul' := fun p x => map_smul chainA' (δ p) x }
  exact chainP' ≪≫ₗ LinearEquiv.rTensor _ qkae.symm.toLinearEquiv

/-- The quotient of a finitely presented module by a finitely generated submodule is finitely
presented. -/
theorem Module.finitePresentation_quotient {S Y : Type*} [Ring S] [AddCommGroup Y] [Module S Y]
    [Module.FinitePresentation S Y] {p : Submodule S Y} (hp : p.FG) :
    Module.FinitePresentation S (Y ⧸ p) :=
  Module.finitePresentation_of_surjective p.mkQ p.mkQ_surjective (by rwa [Submodule.ker_mkQ])

/-- Let `P = MvPolynomial (Fin n) R`, let `α : P →ₐ[R] A` be a surjection making `M` a finitely
presented `P`-module, and let `β : MvPolynomial (Fin m) A →ₐ[A] A'` be a surjection with
finitely generated kernel. Set `P' := MvPolynomial (Fin m) P`. Then `A' ⊗[A] M`, viewed as a
`P'`-module via the surjection
`δ := β.restrictScalars R ∘ MvPolynomial.mapAlgHom α : P' →ₐ[R] A'`, is finitely presented
over `P'`. -/
@[ega "IV 1.4.1" "more general"]
theorem baseChange_finitePresentation_over_polynomial
    (R A A' : Type*) [CommRing R] [CommRing A] [CommRing A']
    [Algebra R A] [Algebra A A'] [Algebra R A'] [IsScalarTower R A A']
    (M : Type*) [AddCommGroup M] [Module A M]
    {n : ℕ} (α : MvPolynomial (Fin n) R →ₐ[R] A) (hα : Function.Surjective α)
    [@Module.FinitePresentation (MvPolynomial (Fin n) R) M _ _
      (Module.compHom M (α : MvPolynomial (Fin n) R →+* A))]
    {m : ℕ} (β : MvPolynomial (Fin m) A →ₐ[A] A') (hβ : Function.Surjective β)
    (hJ : (RingHom.ker β.toRingHom).FG) :
    @Module.FinitePresentation (MvPolynomial (Fin m) (MvPolynomial (Fin n) R))
      (TensorProduct A A' M) _ _
      (Module.compHom (TensorProduct A A' M)
        (((β.restrictScalars R).comp (MvPolynomial.mapAlgHom α) :
            MvPolynomial (Fin m) (MvPolynomial (Fin n) R) →ₐ[R] A') :
          MvPolynomial (Fin m) (MvPolynomial (Fin n) R) →+* A')) := by
  let : Module (MvPolynomial (Fin n) R) M :=
    Module.compHom M (α : MvPolynomial (Fin n) R →+* A)
  let δ : MvPolynomial (Fin m) (MvPolynomial (Fin n) R) →ₐ[R] A' :=
    (β.restrictScalars R).comp (MvPolynomial.mapAlgHom α)
  let : Module (MvPolynomial (Fin m) (MvPolynomial (Fin n) R)) (TensorProduct A A' M) :=
    Module.compHom (TensorProduct A A' M) δ.toRingHom
  exact (LinearEquiv.finitePresentation_iff
    (baseChangeQuotientLinearEquiv R A A' M α hα β hβ ≪≫ₗ
      TensorProduct.quotTensorEquivQuotSMul (R := MvPolynomial (Fin m) (MvPolynomial (Fin n) R))
        (TensorProduct (MvPolynomial (Fin n) R)
          (MvPolynomial (Fin m) (MvPolynomial (Fin n) R)) M) (RingHom.ker δ.toRingHom))).mpr
    (Module.finitePresentation_quotient (baseChange_smul_top_fg R A A' M α hα β hJ))

/-- Let `R → A` be a ring map, `M` an `A`-module finitely presented relative to `R`, and
`A → A'` a ring map of finite presentation. Then the `A'`-module `A' ⊗[A] M` (here
`TensorProduct A A' M`, with its natural `A'`-module structure) is finitely presented relative
to `R`.

The finite type hypothesis on `R → A` of the Stacks statement is not needed. -/
@[stacks 0670, ega "IV 1.4.1" "more general"]
theorem finitelyPresentedRelative_baseChange
    (R A A' : Type*) [CommRing R] [CommRing A] [CommRing A']
    [Algebra R A] [Algebra A A'] [Algebra R A'] [IsScalarTower R A A']
    (M : Type*) [AddCommGroup M] [Module A M]
    (hM : Module.FinitePresentationRel R A M)
    [Algebra.FinitePresentation A A'] :
    Module.FinitePresentationRel R A' (TensorProduct A A' M) := by
  obtain ⟨n, α, hα, hMfp⟩ := hM
  let : Module (MvPolynomial (Fin n) R) M :=
    Module.compHom M (α : MvPolynomial (Fin n) R →+* A)
  have : @Module.FinitePresentation (MvPolynomial (Fin n) R) M _ _ _ := hMfp
  obtain ⟨m, β, hβ, hJ⟩ := (Algebra.FinitePresentation.out (R := A) (A := A'))
  let δ : MvPolynomial (Fin m) (MvPolynomial (Fin n) R) →ₐ[R] A' :=
    (β.restrictScalars R).comp (MvPolynomial.mapAlgHom α)
  let e : MvPolynomial (Fin (m + n)) R ≃ₐ[R]
      MvPolynomial (Fin m) (MvPolynomial (Fin n) R) :=
    (MvPolynomial.renameEquiv R (finSumFinEquiv (m := m) (n := n)).symm).trans
      (MvPolynomial.sumAlgEquiv R (Fin m) (Fin n))
  let : Module (MvPolynomial (Fin m) (MvPolynomial (Fin n) R)) (TensorProduct A A' M) :=
    Module.compHom (TensorProduct A A' M) (δ : _ →+* A')
  have := baseChange_finitePresentation_over_polynomial R A A' M α hα β hβ hJ
  refine ⟨m + n, δ.comp (e : _ →ₐ[R] _), ?_, ?_⟩
  · exact (hβ.comp (MvPolynomial.map_surjective α.toRingHom hα)).comp e.surjective
  · exact fp_transport (e : MvPolynomial (Fin (m + n)) R ≃+*
      MvPolynomial (Fin m) (MvPolynomial (Fin n) R))
