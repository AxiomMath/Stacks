module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDifferenceDerivation
public import Mathlib.RingTheory.Kaehler.Basic

/-!
# The difference of two maps through the diagonal, affine case

Let `S` be a scheme, let `i : X ⟶ X'` be a first-order thickening, let `Y` be a scheme over `S`,
and let `a', b' : X' ⟶ Y` be two morphisms over `S` with `i ≫ a' = i ≫ b' = a`. The commutative
square
```
X  --i-->   X'
|           |
a           (b', a')
↓           ↓
Y  --Δ-->  Y ×_S Y
```
induces a map `θ : a^*Ω_{Y/S} ⟶ 𝒞_{X/X'}` of conormal modules, and the difference derivation `D`
of the pair `(a', b')` satisfies `D = d_{Y/S} ∘ θ`. This file proves this on global sections when
`X'` and `Y` are affine.

With `R = Γ(S, ⊤)`, `A = Γ(Y, ⊤)` and `B = Γ(X', ⊤)`, the comorphism of `(b', a')` is the
`R`-algebra map `A ⊗[R] A ⟶ B` sending `x ⊗ₜ y` to `b'.appTop x * a'.appTop y`, the conormal
module of the diagonal is `Ω[A⁄R] = (KaehlerDifferential.ideal R A).Cotangent`, and the conormal
module of `i` is the ideal `RingHom.ker i.appTop.hom`. The target thickening is the identity of
`Y`, and the `R`-algebra structure on `A` is `Stacks.Thickenings.appTopAlgebra (𝟙 Y ≫ q)`.

## Main definitions

* `Stacks.Thickenings.appTopAlgHom`: `a'.appTop` as a `Γ(S, ⊤)`-algebra map, for `a'` over `S`.
* `Stacks.Thickenings.diagonalPairAppTop`: the comorphism of `(b', a') : X' ⟶ Y ×_S Y`, as a
  `Γ(S, ⊤)`-algebra map out of `Γ(Y, ⊤) ⊗[Γ(S, ⊤)] Γ(Y, ⊤)`.
* `Stacks.Thickenings.diagonalConormalIdealMap`: its restriction to the ideal of the diagonal,
  valued in the conormal module of `i`.
* `Stacks.Thickenings.diagonalConormalMap`: the induced map `θ` on the conormal module
  `Ω[Γ(Y, ⊤)⁄Γ(S, ⊤)]` of the diagonal.

## Main results

* `Stacks.Thickenings.isFirstOrderThickening_id`: the identity is a first-order thickening.
* `Stacks.Thickenings.conormalMap_eq_of_target_id`: two morphisms of thickenings into an identity
  thickening induce the same map of conormal modules.
* `Stacks.Thickenings.diagonalPairAppTop_tmul`,
  `Stacks.Thickenings.diagonalPairAppTop_includeLeft` and
  `Stacks.Thickenings.diagonalPairAppTop_includeRight`: the comorphism of the pair on pure tensors
  and on the two factors.
* `Stacks.Thickenings.mem_ker_diagonalPairAppTop`: the comorphism of the pair carries the ideal of
  the diagonal into the defining ideal of `i`.
* `Stacks.Thickenings.diagonalConormalMap_fromIdeal` and
  `Stacks.Thickenings.eq_diagonalConormalMap`: `θ` is the unique `Γ(Y, ⊤)`-linear map on
  `Ω[Γ(Y, ⊤)⁄Γ(S, ⊤)]` induced by that comorphism.
* `Stacks.Thickenings.diagonalConormalMap_D`: the difference derivation of the pair `(a', b')` is
  `d_{Y/S}` followed by `θ`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TensorProduct

universe u

namespace Stacks.Thickenings

variable {S X X' Y : Scheme.{u}}

/-! ### The identity as a target thickening -/

/-- The identity of a scheme is a first-order thickening. -/
theorem isFirstOrderThickening_id (Y : Scheme.{u}) : IsFirstOrderThickening (𝟙 Y) :=
  ⟨inferInstance, by rw [Scheme.Hom.ker_eq_bot_of_isIso]; exact zero_pow two_ne_zero⟩

variable {i : X ⟶ X'} {a : X ⟶ Y} {a' b' : X' ⟶ Y} {p : X' ⟶ S} {q : Y ⟶ S}

/-- Two morphisms of thickenings from a first-order thickening `i` into the identity thickening
of `Y`, with the same restriction `a` to `X`, induce the same map of conormal modules. -/
theorem conormalMap_eq_of_target_id [IsAffine X'] [IsAffine Y] (hi : IsFirstOrderThickening i)
    (comm_a : i ≫ a' = a ≫ 𝟙 Y) (comm_b : i ≫ b' = a ≫ 𝟙 Y) :
    conormalMap hi (isFirstOrderThickening_id Y) comm_a
      = conormalMap hi (isFirstOrderThickening_id Y) comm_b := by
  let := Smooth.thickeningKerModule (isFirstOrderThickening_id Y)
  let := conormalModuleAlong hi a
  refine LinearMap.ext fun z ↦ Subtype.ext ?_
  rw [conormalMap_apply, conormalMap_apply,
    show (z : Γ(Y, (⊤ : Y.Opens))) = 0 from RingHom.mem_ker.mp z.2, map_zero, map_zero]

/-! ### The comorphism of the pair `(b', a')` -/

/-- For a morphism `a' : X' ⟶ Y` over `S`, the map `a'.appTop` as a `Γ(S, ⊤)`-algebra map, for
the algebra structures induced by `𝟙 Y ≫ q` and `p`. -/
noncomputable def appTopAlgHom (q : Y ⟶ S) {a' : X' ⟶ Y} {p : X' ⟶ S} (ha' : a' ≫ q = p) :
    letI := appTopAlgebra (𝟙 Y ≫ q)
    letI := appTopAlgebra p
    Γ(Y, (⊤ : Y.Opens)) →ₐ[Γ(S, (⊤ : S.Opens))] Γ(X', (⊤ : X'.Opens)) :=
  let := appTopAlgebra (𝟙 Y ≫ q)
  let := appTopAlgebra p
  AlgHom.mk a'.appTop.hom fun r ↦ by
    change a'.appTop.hom (q.appTop.hom r) = p.appTop.hom r
    rw [appTop_comp_apply, ha']

/-- The comorphism of `(b', a') : X' ⟶ Y ×_S Y` on global sections: the `Γ(S, ⊤)`-algebra map
`Γ(Y, ⊤) ⊗[Γ(S, ⊤)] Γ(Y, ⊤) ⟶ Γ(X', ⊤)` sending `x ⊗ₜ y` to `b'.appTop x * a'.appTop y`. -/
noncomputable def diagonalPairAppTop (q : Y ⟶ S) {a' b' : X' ⟶ Y} {p : X' ⟶ S}
    (ha' : a' ≫ q = p) (hb' : b' ≫ q = p) :
    letI := appTopAlgebra (𝟙 Y ≫ q)
    letI := appTopAlgebra p
    (Γ(Y, (⊤ : Y.Opens)) ⊗[Γ(S, (⊤ : S.Opens))] Γ(Y, (⊤ : Y.Opens)))
      →ₐ[Γ(S, (⊤ : S.Opens))] Γ(X', (⊤ : X'.Opens)) :=
  letI := appTopAlgebra (𝟙 Y ≫ q)
  letI := appTopAlgebra p
  Algebra.TensorProduct.lift (appTopAlgHom q hb') (appTopAlgHom q ha')
    fun _ _ ↦ Commute.all _ _

/-- The value of `Stacks.Thickenings.diagonalPairAppTop` on a pure tensor. -/
theorem diagonalPairAppTop_tmul (q : Y ⟶ S) (ha' : a' ≫ q = p) (hb' : b' ≫ q = p)
    (x y : Γ(Y, (⊤ : Y.Opens))) :
    letI := appTopAlgebra (𝟙 Y ≫ q)
    letI := appTopAlgebra p
    diagonalPairAppTop q ha' hb' (x ⊗ₜ y) = b'.appTop.hom x * a'.appTop.hom y := by
  let := appTopAlgebra (𝟙 Y ≫ q)
  let := appTopAlgebra p
  exact Algebra.TensorProduct.lift_tmul _ _ _ _ _

/-- The comorphism of the pair `(b', a')` sends `x ⊗ₜ 1` to `b'.appTop x`. -/
theorem diagonalPairAppTop_includeLeft (q : Y ⟶ S) (ha' : a' ≫ q = p) (hb' : b' ≫ q = p)
    (x : Γ(Y, (⊤ : Y.Opens))) :
    letI := appTopAlgebra (𝟙 Y ≫ q)
    letI := appTopAlgebra p
    diagonalPairAppTop q ha' hb' (x ⊗ₜ 1) = b'.appTop.hom x := by
  let := appTopAlgebra (𝟙 Y ≫ q)
  let := appTopAlgebra p
  rw [diagonalPairAppTop_tmul, map_one, mul_one]

/-- The comorphism of the pair `(b', a')` sends `1 ⊗ₜ x` to `a'.appTop x`. -/
theorem diagonalPairAppTop_includeRight (q : Y ⟶ S) (ha' : a' ≫ q = p) (hb' : b' ≫ q = p)
    (x : Γ(Y, (⊤ : Y.Opens))) :
    letI := appTopAlgebra (𝟙 Y ≫ q)
    letI := appTopAlgebra p
    diagonalPairAppTop q ha' hb' (1 ⊗ₜ x) = a'.appTop.hom x := by
  let := appTopAlgebra (𝟙 Y ≫ q)
  let := appTopAlgebra p
  rw [diagonalPairAppTop_tmul, map_one, one_mul]

/-! ### The comorphism of the pair carries the diagonal ideal into the conormal ideal -/

/-- If `i ≫ a' = a` and `i ≫ b' = a`, the comorphism of `(b', a')` followed by `i.appTop` is the
multiplication map `Γ(Y, ⊤) ⊗[Γ(S, ⊤)] Γ(Y, ⊤) ⟶ Γ(Y, ⊤)` followed by `a.appTop`. -/
theorem appTop_comm_diagonalPairAppTop (q : Y ⟶ S) (ha' : a' ≫ q = p) (hb' : b' ≫ q = p)
    (comm_a : i ≫ a' = a ≫ 𝟙 Y) (comm_b : i ≫ b' = a ≫ 𝟙 Y) :
    letI := appTopAlgebra (𝟙 Y ≫ q)
    letI := appTopAlgebra p
    ∀ z : Γ(Y, (⊤ : Y.Opens)) ⊗[Γ(S, (⊤ : S.Opens))] Γ(Y, (⊤ : Y.Opens)),
      i.appTop.hom (diagonalPairAppTop q ha' hb' z)
        = a.appTop.hom (Algebra.TensorProduct.lmul' (S := Γ(Y, (⊤ : Y.Opens)))
            Γ(S, (⊤ : S.Opens)) z) := by
  let := appTopAlgebra (𝟙 Y ≫ q)
  let := appTopAlgebra p
  intro z
  induction z with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul x y =>
      rw [diagonalPairAppTop_tmul, map_mul, appTop_comm_of_comm comm_a, appTop_comm_of_comm comm_b,
        Algebra.TensorProduct.lmul'_apply_tmul, map_mul]
      rfl
  | add z w hz hw => rw [map_add, map_add, map_add, map_add, hz, hw]

/-- The comorphism of the pair carries the ideal of the diagonal into the defining ideal of
`i`. -/
theorem mem_ker_diagonalPairAppTop (q : Y ⟶ S) (ha' : a' ≫ q = p) (hb' : b' ≫ q = p)
    (comm_a : i ≫ a' = a ≫ 𝟙 Y) (comm_b : i ≫ b' = a ≫ 𝟙 Y) :
    letI := appTopAlgebra (𝟙 Y ≫ q)
    letI := appTopAlgebra p
    ∀ u : KaehlerDifferential.ideal Γ(S, (⊤ : S.Opens)) Γ(Y, (⊤ : Y.Opens)),
      diagonalPairAppTop q ha' hb'
          (u : Γ(Y, (⊤ : Y.Opens)) ⊗[Γ(S, (⊤ : S.Opens))] Γ(Y, (⊤ : Y.Opens)))
        ∈ RingHom.ker i.appTop.hom := by
  let := appTopAlgebra (𝟙 Y ≫ q)
  let := appTopAlgebra p
  intro u
  rw [RingHom.mem_ker, appTop_comm_diagonalPairAppTop q ha' hb' comm_a comm_b,
    RingHom.mem_ker.mp u.2, map_zero]

/-! ### The conormal map of the diagonal square -/

/-- The comorphism of `(b', a')`, restricted to the ideal of the diagonal and corestricted to the
conormal module of `i`, as a `Γ(Y, ⊤)`-linear map for the scalar action induced by `a`. -/
noncomputable def diagonalConormalIdealMap [IsAffine X'] (hi : IsFirstOrderThickening i)
    (q : Y ⟶ S) (ha' : a' ≫ q = p) (hb' : b' ≫ q = p) (comm_a : i ≫ a' = a ≫ 𝟙 Y)
    (comm_b : i ≫ b' = a ≫ 𝟙 Y) :
    letI := appTopAlgebra (𝟙 Y ≫ q)
    letI := conormalModuleAlong hi a
    KaehlerDifferential.ideal Γ(S, (⊤ : S.Opens)) Γ(Y, (⊤ : Y.Opens))
      →ₗ[Γ(Y, (⊤ : Y.Opens))] RingHom.ker i.appTop.hom :=
  let := appTopAlgebra (𝟙 Y ≫ q)
  let := appTopAlgebra p
  let := conormalModuleAlong hi a
  { toFun := fun u ↦ ⟨diagonalPairAppTop q ha' hb' (u : _),
      mem_ker_diagonalPairAppTop q ha' hb' comm_a comm_b u⟩
    map_add' := fun u v ↦ Subtype.ext (by
      change diagonalPairAppTop q ha' hb' ((u + v : _) : _) = _
      rw [AddMemClass.coe_add, map_add]
      rfl)
    map_smul' := fun c u ↦ Subtype.ext (by
      change diagonalPairAppTop q ha' hb' ((c • u : _) : _) = _
      rw [Submodule.coe_smul_of_tower, Algebra.smul_def, map_mul,
        Algebra.TensorProduct.algebraMap_apply, diagonalPairAppTop_includeLeft,
        RingHom.id_apply, conormalModuleAlong_smul hi a c (x := b'.appTop.hom c)
          (appTop_comm_of_comm comm_b c), Submodule.coe_smul, smul_eq_mul]
      rfl) }

/-- The map `θ : Ω[Γ(Y, ⊤)⁄Γ(S, ⊤)] ⟶ RingHom.ker i.appTop.hom` from the conormal module of the
diagonal to the conormal module of `i`, induced by
`Stacks.Thickenings.diagonalConormalIdealMap`. -/
noncomputable def diagonalConormalMap [IsAffine X'] (hi : IsFirstOrderThickening i) (q : Y ⟶ S)
    (ha' : a' ≫ q = p) (hb' : b' ≫ q = p) (comm_a : i ≫ a' = a ≫ 𝟙 Y)
    (comm_b : i ≫ b' = a ≫ 𝟙 Y) :
    letI := appTopAlgebra (𝟙 Y ≫ q)
    letI := conormalModuleAlong hi a
    Ω[Γ(Y, (⊤ : Y.Opens))⁄Γ(S, (⊤ : S.Opens))] →ₗ[Γ(Y, (⊤ : Y.Opens))]
      RingHom.ker i.appTop.hom :=
  let := appTopAlgebra (𝟙 Y ≫ q)
  let := appTopAlgebra p
  let := conormalModuleAlong hi a
  LinearMap.comp
    ((((KaehlerDifferential.ideal Γ(S, (⊤ : S.Opens)) Γ(Y, (⊤ : Y.Opens))) •
          (⊤ : Submodule (Γ(Y, (⊤ : Y.Opens)) ⊗[Γ(S, (⊤ : S.Opens))] Γ(Y, (⊤ : Y.Opens)))
            (KaehlerDifferential.ideal Γ(S, (⊤ : S.Opens)) Γ(Y, (⊤ : Y.Opens))))).restrictScalars
          Γ(Y, (⊤ : Y.Opens))).liftQ
      (diagonalConormalIdealMap hi q ha' hb' comm_a comm_b)
      (by
        intro z hz
        rw [LinearMap.mem_ker]
        refine Submodule.smul_induction_on ((Submodule.restrictScalars_mem _ _ _).mp hz) ?_ ?_
        · intro r hr v _
          refine Subtype.ext ?_
          have hmul : ((r • v : KaehlerDifferential.ideal Γ(S, (⊤ : S.Opens))
                Γ(Y, (⊤ : Y.Opens))) :
              Γ(Y, (⊤ : Y.Opens)) ⊗[Γ(S, (⊤ : S.Opens))] Γ(Y, (⊤ : Y.Opens)))
              = r * (v : _) := by
            rw [Submodule.coe_smul, smul_eq_mul]
          change diagonalPairAppTop q ha' hb' ((r • v : _) : _) = _
          rw [hmul, map_mul, ZeroMemClass.coe_zero]
          exact mul_eq_zero_of_mem_ker_appTop hi
            ⟨diagonalPairAppTop q ha' hb' r,
              mem_ker_diagonalPairAppTop q ha' hb' comm_a comm_b ⟨r, hr⟩⟩
            ⟨diagonalPairAppTop q ha' hb' (v : _),
              mem_ker_diagonalPairAppTop q ha' hb' comm_a comm_b v⟩
        · intro z w ez ew; rw [map_add, ez, ew, zero_add]))
    (Submodule.Quotient.restrictScalarsEquiv Γ(Y, (⊤ : Y.Opens)) _).symm.toLinearMap

/-- On the class of a section `u` of the ideal of the diagonal,
`Stacks.Thickenings.diagonalConormalMap` takes the value `(b', a')^♯ u`. -/
theorem diagonalConormalMap_fromIdeal [IsAffine X'] (hi : IsFirstOrderThickening i) (q : Y ⟶ S)
    (ha' : a' ≫ q = p) (hb' : b' ≫ q = p) (comm_a : i ≫ a' = a ≫ 𝟙 Y)
    (comm_b : i ≫ b' = a ≫ 𝟙 Y) :
    letI := appTopAlgebra (𝟙 Y ≫ q)
    letI := appTopAlgebra p
    letI := conormalModuleAlong hi a
    ∀ u : KaehlerDifferential.ideal Γ(S, (⊤ : S.Opens)) Γ(Y, (⊤ : Y.Opens)),
      ((diagonalConormalMap hi q ha' hb' comm_a comm_b
            (KaehlerDifferential.fromIdeal Γ(S, (⊤ : S.Opens)) Γ(Y, (⊤ : Y.Opens)) u) :
          RingHom.ker i.appTop.hom) : Γ(X', (⊤ : X'.Opens)))
        = diagonalPairAppTop q ha' hb' (u : _) :=
  fun _ ↦ rfl

/-- A `Γ(Y, ⊤)`-linear map `θ : Ω[Γ(Y, ⊤)⁄Γ(S, ⊤)] ⟶ RingHom.ker i.appTop.hom` sending the class
of each `u` in the ideal of the diagonal to `(b', a')^♯ u` is
`Stacks.Thickenings.diagonalConormalMap`. -/
theorem eq_diagonalConormalMap [IsAffine X'] (hi : IsFirstOrderThickening i) (q : Y ⟶ S)
    (ha' : a' ≫ q = p) (hb' : b' ≫ q = p) (comm_a : i ≫ a' = a ≫ 𝟙 Y)
    (comm_b : i ≫ b' = a ≫ 𝟙 Y) :
    letI := appTopAlgebra (𝟙 Y ≫ q)
    letI := appTopAlgebra p
    letI := conormalModuleAlong hi a
    ∀ θ : Ω[Γ(Y, (⊤ : Y.Opens))⁄Γ(S, (⊤ : S.Opens))] →ₗ[Γ(Y, (⊤ : Y.Opens))]
        RingHom.ker i.appTop.hom,
      (∀ u : KaehlerDifferential.ideal Γ(S, (⊤ : S.Opens)) Γ(Y, (⊤ : Y.Opens)),
          ((θ (KaehlerDifferential.fromIdeal Γ(S, (⊤ : S.Opens)) Γ(Y, (⊤ : Y.Opens)) u) :
              RingHom.ker i.appTop.hom) : Γ(X', (⊤ : X'.Opens)))
            = diagonalPairAppTop q ha' hb' (u : _)) →
        θ = diagonalConormalMap hi q ha' hb' comm_a comm_b := by
  let := appTopAlgebra (𝟙 Y ≫ q)
  let := appTopAlgebra p
  let := conormalModuleAlong hi a
  intro θ hθ
  refine LinearMap.ext fun ω ↦ ?_
  obtain ⟨u, rfl⟩ :=
    KaehlerDifferential.fromIdeal_surjective Γ(S, (⊤ : S.Opens)) Γ(Y, (⊤ : Y.Opens)) ω
  exact Subtype.ext ((hθ u).trans
    (diagonalConormalMap_fromIdeal hi q ha' hb' comm_a comm_b u).symm)

/-! ### The difference derivation through the diagonal -/

/-- Let `i : X ⟶ X'` be a first-order thickening with `X'` affine, let `Y` be an affine scheme
over `S`, and let `a', b' : X' ⟶ Y` be two morphisms over `S` with `i ≫ a' = i ≫ b' = a`. Then the
difference derivation `D` of the pair `(a', b')` is `d_{Y/S}` followed by the map
`θ = Stacks.Thickenings.diagonalConormalMap`: `D x = θ (d x)` for every `x : Γ(Y, ⊤)`. -/
theorem diagonalConormalMap_D [IsAffine X'] [IsAffine Y] (hi : IsFirstOrderThickening i)
    (q : Y ⟶ S) (ha' : a' ≫ q = p) (hb' : b' ≫ q = p) (comm_a : i ≫ a' = a ≫ 𝟙 Y)
    (comm_b : i ≫ b' = a ≫ 𝟙 Y) :
    letI := appTopAlgebra (𝟙 Y ≫ q)
    letI := conormalModuleAlong hi a
    letI := conormalModuleAlong hi (i ≫ p)
    ∀ x : Γ(Y, (⊤ : Y.Opens)),
      mapDifferenceDerivation hi (isFirstOrderThickening_id Y) comm_a comm_b ha' hb'
          (conormalMap_eq_of_target_id hi comm_a comm_b) x
        = diagonalConormalMap hi q ha' hb' comm_a comm_b
            (KaehlerDifferential.D Γ(S, (⊤ : S.Opens)) Γ(Y, (⊤ : Y.Opens)) x) := by
  let := appTopAlgebra (𝟙 Y ≫ q)
  let := appTopAlgebra p
  let := conormalModuleAlong hi a
  let := conormalModuleAlong hi (i ≫ p)
  intro x
  refine Subtype.ext ?_
  have hD := mapDifferenceDerivation_appTop hi (isFirstOrderThickening_id Y) comm_a comm_b ha' hb'
    (conormalMap_eq_of_target_id hi comm_a comm_b) x
  have hθ := diagonalConormalMap_fromIdeal hi q ha' hb' comm_a comm_b
    ⟨1 ⊗ₜ x - x ⊗ₜ 1, KaehlerDifferential.one_smul_sub_smul_one_mem_ideal _ x⟩
  rw [show ((⟨1 ⊗ₜ x - x ⊗ₜ 1, KaehlerDifferential.one_smul_sub_smul_one_mem_ideal _ x⟩ :
        KaehlerDifferential.ideal Γ(S, (⊤ : S.Opens)) Γ(Y, (⊤ : Y.Opens))) :
      Γ(Y, (⊤ : Y.Opens)) ⊗[Γ(S, (⊤ : S.Opens))] Γ(Y, (⊤ : Y.Opens)))
      = 1 ⊗ₜ x - x ⊗ₜ 1 from rfl, map_sub, diagonalPairAppTop_includeLeft,
    diagonalPairAppTop_includeRight] at hθ
  exact hD.trans hθ.symm

end Stacks.Thickenings

end
