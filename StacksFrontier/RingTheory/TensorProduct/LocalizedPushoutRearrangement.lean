module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Rearranging a module over a pushout of rings, and along a localization of the base

Let `R → A` and `R → R'` be commutative rings, write `A' = A ⊗_R R'` for their pushout, and let
`M` be an `A'`-module. Let `B` be an `A`-algebra and `C` an `R'`-algebra. Tensoring `M` up to
`B ⊗_R C` is the same as base changing it along `R' → C` and then along `A → B`:

`(B ⊗_R C) ⊗_{A ⊗_R R'} M  ≅  B ⊗_A (M ⊗_{R'} C)`.

When `B` and `C` are moreover algebras over a localization `R_S` of `R`, the left-hand side may
be written with the tensor product taken over `R_S`: an `R_S`-algebra tensored with an
`R_S`-algebra over `R` is the same as over `R_S`, which is `IsLocalization.algebraTensorEquiv`.
That gives the second form

`(B ⊗_{R_S} C) ⊗_{A ⊗_R R'} M  ≅  B ⊗_A (M ⊗_{R'} C)`,

the shape in which the affine reduction of Stacks 0DJ8 needs it: there `R = 𝒪_S(V)`,
`A = 𝒪_X(U)`, `R' = 𝒪_{S'}(V')`, `R_S = 𝒪_{S,s}`, `B = 𝒪_{X,x}` and `C = 𝒪_{S',s'}`, and the
left-hand side is the source of the pointwise map of Stacks 0DJ7 at a point of `X'`.

## Main definitions

* `Stacks.TensorProductPushout.rearrange`: the first displayed isomorphism.
* `Stacks.TensorProductPushout.localizedRearrange`: the second.
* `Stacks.TensorProductPushout.mapAlgebra` and `mapAlgebraMid`: the `A ⊗_R R'`-algebra
  structures on `B ⊗_R C` and on `B ⊗_{R_S} C` that a commuting square of rings provides, and
  `mapLocalizedRearrange`: the second isomorphism at the latter.
* `Stacks.TensorProductPushout.baseCongr`: base change along an isomorphism of the base change
  ring, given as a ring homomorphism with a two-sided inverse.

## Main results

* `Stacks.TensorProductPushout.rearrange_tmul`, `rearrange_symm_tmul`,
  `localizedRearrange_tmul`, `localizedRearrange_symm_tmul`, `baseCongr_tmul`,
  `baseCongr_symm_tmul`: all four isomorphisms on pure tensors, which is what identifies them.

## Implementation notes

`Mathlib` has the localization input: `IsLocalization.algebraLid` is `R_S ⊗_R T ≅ T` for an
`R`-algebra `T` which is already an `R_S`-algebra — the statement that tensoring up from `R` to
`R_S` changes nothing once the multiplicative set acts invertibly — and
`IsLocalization.algebraTensorEquiv` is the two-sided form `B ⊗_{R_S} C ≅ B ⊗_R C` used below.
Neither the pushout rearrangement nor the base congruence is in `Mathlib`.

The factors are ordered so that every module structure in sight is a `Mathlib` instance. An
`A`-action on `M ⊗_{R'} C` exists because `TensorProduct.leftModule` lets scalars act through
the *left* factor, so `M` is written first; `C ⊗_{R'} M` would need an `A`-action through the
right factor, and the one the project has,
`Stacks.TensorProductPushout.rightModule`, asks for a scalar tower from the base of the tensor
product to the acting ring — here that would be `R' → A`, and `A` and `R'` are two independent
algebras over `R`. A consumer wanting the other order has `TensorProduct.comm` and whichever
`A`-action its module carries. For a related reason `rearrange` is an `AddEquiv`: its two sides
are modules over `B ⊗_R C` resp. `B`, and neither ring acts canonically on both.

`Algebra.TensorProduct.rightAlgebra`, the `R'`-algebra structure on `A ⊗_R R'`, is a local
instance here as it is in `Mathlib`: made global it would make the action of a ring on its own
tensor square ambiguous.

The `A'`-algebra structure on `B ⊗_R C` is data, not an instance — the induced map on a tensor
product of algebras over different base rings is not canonical — so it is taken as an instance
argument together with the equation `halg` computing it on pure tensors. For `B ⊗_R C` built by
`Algebra.TensorProduct.map`, which is how `localizedRearrange` builds the one it uses, that
equation is `rfl`.

## References

* [Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

@[expose] public noncomputable section

open TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace Stacks.TensorProductPushout

/-! ### The two actions of the base on an `A ⊗_R R'`-module -/

section Actions

variable {R A R' M : Type*} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']
  [AddCommGroup M] [Module (A ⊗[R] R') M] [Module A M] [Module R' M]
  [IsScalarTower A (A ⊗[R] R') M] [IsScalarTower R' (A ⊗[R] R') M]

/-- A pure tensor of `A ⊗_R R'` is the product of its two factors' images. -/
private theorem tmul_eq_algebraMap_mul (a : A) (r' : R') :
    (a ⊗ₜ[R] r' : A ⊗[R] R') =
      algebraMap A (A ⊗[R] R') a * algebraMap R' (A ⊗[R] R') r' := by
  simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.right_algebraMap_apply,
    Algebra.TensorProduct.tmul_mul_tmul]

/-- A pure tensor of `A ⊗_R R'` acts on an `A ⊗_R R'`-module by its two factors in turn. -/
theorem tmul_smul_eq (a : A) (r' : R') (m : M) :
    (a ⊗ₜ[R] r' : A ⊗[R] R') • m = a • (r' • m) := by
  rw [tmul_eq_algebraMap_mul, mul_smul, IsScalarTower.algebraMap_smul,
    IsScalarTower.algebraMap_smul]

/-- The `A`-action and the `R'`-action on an `A ⊗_R R'`-module commute. -/
theorem smulCommClass_of_tensorTower (R : Type*) [CommRing R] [Algebra R A] [Algebra R R']
    [Module (A ⊗[R] R') M] [IsScalarTower A (A ⊗[R] R') M] [IsScalarTower R' (A ⊗[R] R') M] :
    SMulCommClass R' A M where
  smul_comm r' a m := by
    rw [← tmul_smul_eq (R := R) a r' m, ← IsScalarTower.algebraMap_smul (A ⊗[R] R') r',
      ← IsScalarTower.algebraMap_smul (A ⊗[R] R') a, smul_smul, tmul_eq_algebraMap_mul, mul_comm]

/-- The two routes `R → A → M` and `R → R' → M` by which the base acts on an
`A ⊗_R R'`-module agree. -/
theorem algebraMap_smul_eq (r : R) (m : M) :
    (algebraMap R A r) • m = (algebraMap R R' r) • m := by
  rw [← IsScalarTower.algebraMap_smul (A ⊗[R] R') (algebraMap R A r) m,
    ← IsScalarTower.algebraMap_smul (A ⊗[R] R') (algebraMap R R' r) m,
    ← IsScalarTower.algebraMap_apply R A (A ⊗[R] R'), ← IsScalarTower.algebraMap_apply R R' _]

end Actions

/-! ### The rearrangement -/

section Rearrange

variable {R A R' B C M : Type*}
  [CommRing R] [CommRing A] [CommRing R'] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R R'] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
  [Algebra R' C] [Algebra R C] [IsScalarTower R R' C]
  [AddCommGroup M] [Module (A ⊗[R] R') M] [Module A M] [Module R' M]
  [IsScalarTower A (A ⊗[R] R') M] [IsScalarTower R' (A ⊗[R] R') M]
  [SMulCommClass R' A M]
  [Algebra (A ⊗[R] R') (B ⊗[R] C)]

variable (halg : ∀ (a : A) (r' : R'),
  algebraMap (A ⊗[R] R') (B ⊗[R] C) (a ⊗ₜ[R] r') = algebraMap A B a ⊗ₜ[R] algebraMap R' C r')

omit [SMulCommClass R' A M] [IsScalarTower R A B] [IsScalarTower R R' C]
  [Module (A ⊗[R] R') M] [Module A M] [Module R' M] [IsScalarTower A (A ⊗[R] R') M]
  [IsScalarTower R' (A ⊗[R] R') M] in
include halg in
/-- A pure tensor of `A ⊗_R R'` acts on `B ⊗_R C` by its two factors in turn. -/
theorem smul_tmul_tmul (a : A) (r' : R') (b : B) (c : C) :
    (a ⊗ₜ[R] r' : A ⊗[R] R') • (b ⊗ₜ[R] c) = (a • b) ⊗ₜ[R] (r' • c) := by
  rw [Algebra.smul_def, halg, Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def,
    Algebra.smul_def]

/-- `(b, c, m) ↦ b ⊗ (m ⊗ c)`, additive in each variable. -/
def rearrangeFwdCurry : B →+ C →+ M →+ B ⊗[A] (M ⊗[R'] C) :=
  AddMonoidHom.mk'
    (fun b => AddMonoidHom.mk'
      (fun c => AddMonoidHom.mk' (fun m => b ⊗ₜ[A] (m ⊗ₜ[R'] c))
        (fun m₁ m₂ => by rw [TensorProduct.add_tmul, TensorProduct.tmul_add]))
      (fun c₁ c₂ => AddMonoidHom.ext fun m => by
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, TensorProduct.tmul_add]))
    (fun b₁ b₂ => AddMonoidHom.ext fun c => AddMonoidHom.ext fun m => by
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, TensorProduct.add_tmul])

@[simp] theorem rearrangeFwdCurry_apply (b : B) (c : C) (m : M) :
    rearrangeFwdCurry b c m = b ⊗ₜ[A] (m ⊗ₜ[R'] c) := rfl

/-- `b ⊗ c ↦ (m ↦ b ⊗ (m ⊗ c))`: the curried forward map, descended to `B ⊗_R C`. -/
def rearrangeFwdHom : (B ⊗[R] C) →+ M →+ B ⊗[A] (M ⊗[R'] C) :=
  TensorProduct.liftAddHom rearrangeFwdCurry
    fun r b c => AddMonoidHom.ext fun m => by
      simp only [rearrangeFwdCurry_apply]
      rw [← IsScalarTower.algebraMap_smul A r b, TensorProduct.smul_tmul,
        TensorProduct.smul_tmul' (algebraMap R A r) m c,
        algebraMap_smul_eq (A := A) (R' := R'),
        TensorProduct.smul_tmul, IsScalarTower.algebraMap_smul R' r c]

omit [Algebra (A ⊗[R] R') (B ⊗[R] C)] in
@[simp] theorem rearrangeFwdHom_tmul (b : B) (c : C) (m : M) :
    rearrangeFwdHom (A := A) (R' := R') (b ⊗ₜ[R] c) m = b ⊗ₜ[A] (m ⊗ₜ[R'] c) := by
  simp [rearrangeFwdHom]

include halg in
/-- The forward map is balanced over `A ⊗_R R'`. -/
theorem rearrangeFwdHom_smul (x : A ⊗[R] R') (t : B ⊗[R] C) (m : M) :
    rearrangeFwdHom (A := A) (R' := R') (x • t) m =
      rearrangeFwdHom (A := A) (R' := R') t (x • m) := by
  induction x with
  | add x y hx hy => simp [add_smul, hx, hy]
  | tmul a r' =>
      induction t with
      | add t₁ t₂ h₁ h₂ => simp [smul_add, h₁, h₂]
      | tmul b c =>
          rw [smul_tmul_tmul halg, rearrangeFwdHom_tmul, rearrangeFwdHom_tmul, tmul_smul_eq,
            TensorProduct.smul_tmul a b _, TensorProduct.smul_tmul' a m (r' • c),
            ← TensorProduct.smul_tmul r' (a • m) c, smul_comm r' a m]

include halg in
/-- `(b ⊗ c) ⊗ m ↦ b ⊗ (m ⊗ c)`. -/
def rearrangeFwd : (B ⊗[R] C) ⊗[A ⊗[R] R'] M →+ B ⊗[A] (M ⊗[R'] C) :=
  TensorProduct.liftAddHom (rearrangeFwdHom (A := A) (R' := R')) (rearrangeFwdHom_smul halg)

include halg in
@[simp] theorem rearrangeFwd_tmul (b : B) (c : C) (m : M) :
    rearrangeFwd halg ((b ⊗ₜ[R] c) ⊗ₜ[A ⊗[R] R'] m) = b ⊗ₜ[A] (m ⊗ₜ[R'] c) := by
  simp [rearrangeFwd]

/-- `(m, c, b) ↦ (b ⊗ c) ⊗ m`, additive in each variable. -/
def rearrangeBwdCurry : M →+ C →+ B →+ ((B ⊗[R] C) ⊗[A ⊗[R] R'] M) :=
  AddMonoidHom.mk'
    (fun m => AddMonoidHom.mk'
      (fun c => AddMonoidHom.mk' (fun b => (b ⊗ₜ[R] c) ⊗ₜ[A ⊗[R] R'] m)
        (fun b₁ b₂ => by rw [TensorProduct.add_tmul, TensorProduct.add_tmul]))
      (fun c₁ c₂ => AddMonoidHom.ext fun b => by
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, TensorProduct.tmul_add,
          TensorProduct.add_tmul]))
    (fun m₁ m₂ => AddMonoidHom.ext fun c => AddMonoidHom.ext fun b => by
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, TensorProduct.tmul_add])

@[simp] theorem rearrangeBwdCurry_apply (m : M) (c : C) (b : B) :
    rearrangeBwdCurry (R := R) (A := A) m c b = (b ⊗ₜ[R] c) ⊗ₜ[A ⊗[R] R'] m := rfl

include halg in
/-- `m ⊗ c ↦ (b ↦ (b ⊗ c) ⊗ m)`: the curried backward map, descended to `M ⊗_{R'} C`. -/
def rearrangeBwdHom : (M ⊗[R'] C) →+ (B →+ ((B ⊗[R] C) ⊗[A ⊗[R] R'] M)) :=
  TensorProduct.liftAddHom rearrangeBwdCurry
    fun r' m c => AddMonoidHom.ext fun b => by
      simp only [rearrangeBwdCurry_apply]
      rw [show b ⊗ₜ[R] (r' • c) = ((1 : A) ⊗ₜ[R] r' : A ⊗[R] R') • (b ⊗ₜ[R] c) by
          rw [smul_tmul_tmul halg, one_smul],
        TensorProduct.smul_tmul, tmul_smul_eq, one_smul]

include halg in
@[simp] theorem rearrangeBwdHom_tmul (m : M) (c : C) (b : B) :
    rearrangeBwdHom halg (m ⊗ₜ[R'] c) b = (b ⊗ₜ[R] c) ⊗ₜ[A ⊗[R] R'] m := by
  simp [rearrangeBwdHom]

include halg in
/-- The backward map is balanced over `A`. -/
theorem rearrangeBwdHom_smul (a : A) (b : B) (x : M ⊗[R'] C) :
    rearrangeBwdHom halg x (a • b) = rearrangeBwdHom halg (a • x) b := by
  induction x with
  | add x y hx hy => simp [smul_add, hx, hy]
  | tmul m c =>
      rw [TensorProduct.smul_tmul' a m c, rearrangeBwdHom_tmul, rearrangeBwdHom_tmul,
        show (a • b) ⊗ₜ[R] c = (a ⊗ₜ[R] (1 : R') : A ⊗[R] R') • (b ⊗ₜ[R] c) by
          rw [smul_tmul_tmul halg, one_smul],
        TensorProduct.smul_tmul, tmul_smul_eq, one_smul]

include halg in
/-- `b ⊗ (m ⊗ c) ↦ (b ⊗ c) ⊗ m`. -/
def rearrangeBwd : B ⊗[A] (M ⊗[R'] C) →+ (B ⊗[R] C) ⊗[A ⊗[R] R'] M :=
  TensorProduct.liftAddHom (rearrangeBwdHom halg).flip
    fun a b x => by
      simpa only [AddMonoidHom.flip_apply] using rearrangeBwdHom_smul halg a b x

include halg in
@[simp] theorem rearrangeBwd_tmul (b : B) (m : M) (c : C) :
    rearrangeBwd halg (b ⊗ₜ[A] (m ⊗ₜ[R'] c)) = (b ⊗ₜ[R] c) ⊗ₜ[A ⊗[R] R'] m := by
  simp [rearrangeBwd]

include halg in
/-- **Tensoring an `A ⊗_R R'`-module up to `B ⊗_R C` is two base changes.** For `B` an
`A`-algebra and `C` an `R'`-algebra, `(B ⊗_R C) ⊗_{A ⊗_R R'} M ≅ B ⊗_A (M ⊗_{R'} C)`: both sides
are generated by `(b ⊗ c) ⊗ m`, resp. `b ⊗ (m ⊗ c)`. -/
def rearrange : ((B ⊗[R] C) ⊗[A ⊗[R] R'] M) ≃+ B ⊗[A] (M ⊗[R'] C) where
  toFun := rearrangeFwd halg
  invFun := rearrangeBwd halg
  map_add' := (rearrangeFwd halg).map_add
  left_inv z := by
    induction z with
    | add z w hz hw => simp [hz, hw]
    | tmul t m =>
        induction t with
        | add t₁ t₂ h₁ h₂ => simp [TensorProduct.add_tmul, h₁, h₂]
        | tmul b c => simp
  right_inv x := by
    induction x with
    | add x y hx hy => simp [hx, hy]
    | tmul b x =>
        induction x with
        | add x y hx hy => simp [TensorProduct.tmul_add, hx, hy]
        | tmul m c => simp

include halg in
@[simp] theorem rearrange_tmul (b : B) (c : C) (m : M) :
    rearrange halg ((b ⊗ₜ[R] c) ⊗ₜ[A ⊗[R] R'] m) = b ⊗ₜ[A] (m ⊗ₜ[R'] c) :=
  rearrangeFwd_tmul halg b c m

include halg in
@[simp] theorem rearrange_symm_tmul (b : B) (m : M) (c : C) :
    (rearrange halg).symm (b ⊗ₜ[A] (m ⊗ₜ[R'] c)) = (b ⊗ₜ[R] c) ⊗ₜ[A ⊗[R] R'] m :=
  rearrangeBwd_tmul halg b m c

end Rearrange

/-! ### The rearrangement with the first tensor product taken over a localization -/

section Localized

variable {R A R' Rp B C M : Type*}
  [CommRing R] [CommRing A] [CommRing R'] [CommRing Rp] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R R'] [Algebra R Rp]
  [Algebra A B] [Algebra R B] [IsScalarTower R A B] [Algebra Rp B] [IsScalarTower R Rp B]
  [Algebra R' C] [Algebra R C] [IsScalarTower R R' C] [Algebra Rp C] [IsScalarTower R Rp C]
  [AddCommGroup M] [Module (A ⊗[R] R') M] [Module A M] [Module R' M]
  [IsScalarTower A (A ⊗[R] R') M] [IsScalarTower R' (A ⊗[R] R') M]
  [SMulCommClass R' A M]

/-- The `A ⊗_R R'`-algebra structure on `B ⊗_R C` induced by `A → B` and `R' → C`. -/
@[instance_reducible] def mapAlgebra : Algebra (A ⊗[R] R') (B ⊗[R] C) :=
  RingHom.toAlgebra (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A B)
    (IsScalarTower.toAlgHom R R' C)).toRingHom

/-- The structure map of `mapAlgebra` on a pure tensor `a ⊗ r'` of `A ⊗_R R'`. -/
theorem mapAlgebra_algebraMap_tmul (a : A) (r' : R') :
    letI := mapAlgebra (R := R) (A := A) (R' := R') (B := B) (C := C)
    algebraMap (A ⊗[R] R') (B ⊗[R] C) (a ⊗ₜ[R] r') =
      algebraMap A B a ⊗ₜ[R] algebraMap R' C r' := rfl

/-- The `A ⊗_R R'`-algebra structure on `B ⊗_{Rp} C` induced by `R → Rp`, `A → B` and `R' → C`:
the heterobasic `Algebra.TensorProduct.mapRingHom`, whose two compatibilities are the two scalar
towers over `R`. -/
@[instance_reducible] def mapAlgebraMid : Algebra (A ⊗[R] R') (B ⊗[Rp] C) :=
  RingHom.toAlgebra (Algebra.TensorProduct.mapRingHom (algebraMap R Rp) (algebraMap A B)
    (algebraMap R' C)
    ((IsScalarTower.algebraMap_eq R A B).symm.trans (IsScalarTower.algebraMap_eq R Rp B))
    ((IsScalarTower.algebraMap_eq R R' C).symm.trans (IsScalarTower.algebraMap_eq R Rp C)))

/-- The structure map of `mapAlgebraMid` on a pure tensor `a ⊗ r'` of `A ⊗_R R'`. -/
theorem mapAlgebraMid_algebraMap_tmul (a : A) (r' : R') :
    letI := mapAlgebraMid (R := R) (A := A) (R' := R') (Rp := Rp) (B := B) (C := C)
    algebraMap (A ⊗[R] R') (B ⊗[Rp] C) (a ⊗ₜ[R] r') =
      algebraMap A B a ⊗ₜ[Rp] algebraMap R' C r' :=
  Algebra.TensorProduct.mapRingHom_tmul _ _ _ _ _ a r'

variable (S : Submonoid R) [IsLocalization S Rp]
  [Algebra (A ⊗[R] R') (B ⊗[Rp] C)]
  (halg : ∀ (a : A) (r' : R'),
    algebraMap (A ⊗[R] R') (B ⊗[Rp] C) (a ⊗ₜ[R] r') =
      algebraMap A B a ⊗ₜ[Rp] algebraMap R' C r')

include S halg in
/-- `B ⊗_{R_S} C ≅ B ⊗_R C` as `A ⊗_R R'`-algebras, hence as `A ⊗_R R'`-modules: the
isomorphism is `IsLocalization.algebraTensorEquiv`, which is the identity on pure tensors, and
the two `A ⊗_R R'`-algebra structures are computed by the same formula. -/
def localizedBaseEquiv [Algebra (A ⊗[R] R') (B ⊗[R] C)]
    (halg' : ∀ (a : A) (r' : R'),
      algebraMap (A ⊗[R] R') (B ⊗[R] C) (a ⊗ₜ[R] r') =
        algebraMap A B a ⊗ₜ[R] algebraMap R' C r') :
    (B ⊗[Rp] C) ≃ₗ[A ⊗[R] R'] (B ⊗[R] C) :=
  AddEquiv.toLinearEquiv (IsLocalization.algebraTensorEquiv S Rp B C).toAddEquiv
    fun x z => by
      have hcoe : ∀ w : B ⊗[Rp] C,
          (IsLocalization.algebraTensorEquiv S Rp B C).toAddEquiv w =
            IsLocalization.algebraTensorEquiv S Rp B C w := fun _ => rfl
      have hmap : ∀ y : A ⊗[R] R',
          IsLocalization.algebraTensorEquiv S Rp B C (algebraMap (A ⊗[R] R') (B ⊗[Rp] C) y) =
            algebraMap (A ⊗[R] R') (B ⊗[R] C) y := by
        intro y
        induction y with
        | add y₁ y₂ h₁ h₂ => simp [h₁, h₂]
        | tmul a r' => rw [halg, halg']; rfl
      rw [hcoe, hcoe, Algebra.smul_def, Algebra.smul_def, map_mul, hmap]

include S halg in
@[simp] theorem localizedBaseEquiv_tmul [Algebra (A ⊗[R] R') (B ⊗[R] C)]
    (halg' : ∀ (a : A) (r' : R'),
      algebraMap (A ⊗[R] R') (B ⊗[R] C) (a ⊗ₜ[R] r') =
        algebraMap A B a ⊗ₜ[R] algebraMap R' C r')
    (b : B) (c : C) :
    localizedBaseEquiv S halg halg' (b ⊗ₜ[Rp] c) = b ⊗ₜ[R] c := rfl

include S halg in
/-- **The rearrangement, with the first tensor product taken over a localization of the base.**
For `R_S` a localization of `R` and `B`, `C` algebras over `R_S` compatibly with their
`A`-, resp. `R'`-algebra structures, `(B ⊗_{R_S} C) ⊗_{A ⊗_R R'} M ≅ B ⊗_A (M ⊗_{R'} C)`. -/
def localizedRearrange : ((B ⊗[Rp] C) ⊗[A ⊗[R] R'] M) ≃+ B ⊗[A] (M ⊗[R'] C) :=
  letI := mapAlgebra (R := R) (A := A) (R' := R') (B := B) (C := C)
  (TensorProduct.congr (localizedBaseEquiv S halg mapAlgebra_algebraMap_tmul)
      (LinearEquiv.refl (A ⊗[R] R') M)).toAddEquiv.trans
    (rearrange mapAlgebra_algebraMap_tmul)

include S halg in
@[simp] theorem localizedRearrange_tmul (b : B) (c : C) (m : M) :
    localizedRearrange S halg ((b ⊗ₜ[Rp] c) ⊗ₜ[A ⊗[R] R'] m) = b ⊗ₜ[A] (m ⊗ₜ[R'] c) := by
  let := mapAlgebra (R := R) (A := A) (R' := R') (B := B) (C := C)
  simp [localizedRearrange]

include S halg in
@[simp] theorem localizedRearrange_symm_tmul (b : B) (m : M) (c : C) :
    (localizedRearrange S halg (M := M)).symm (b ⊗ₜ[A] (m ⊗ₜ[R'] c)) =
      (b ⊗ₜ[Rp] c) ⊗ₜ[A ⊗[R] R'] m :=
  (AddEquiv.symm_apply_eq _).mpr (localizedRearrange_tmul S halg b c m).symm

omit [Algebra (A ⊗[R] R') (B ⊗[Rp] C)] in
include S in
/-- **The rearrangement at the algebra structure a square of rings provides.**
`localizedRearrange` for the `A ⊗_R R'`-algebra structure of `mapAlgebraMid`, which asks for
nothing beyond the two scalar towers over `R`. -/
def mapLocalizedRearrange :
    letI := mapAlgebraMid (R := R) (A := A) (R' := R') (Rp := Rp) (B := B) (C := C)
    ((B ⊗[Rp] C) ⊗[A ⊗[R] R'] M) ≃+ B ⊗[A] (M ⊗[R'] C) :=
  letI := mapAlgebraMid (R := R) (A := A) (R' := R') (Rp := Rp) (B := B) (C := C)
  localizedRearrange S mapAlgebraMid_algebraMap_tmul

omit [Algebra (A ⊗[R] R') (B ⊗[Rp] C)] in
include S in
/-- `mapLocalizedRearrange` sends `(b ⊗ c) ⊗ m` to `b ⊗ (m ⊗ c)`. -/
theorem mapLocalizedRearrange_tmul (b : B) (c : C) (m : M) :
    letI := mapAlgebraMid (R := R) (A := A) (R' := R') (Rp := Rp) (B := B) (C := C)
    mapLocalizedRearrange S (M := M) ((b ⊗ₜ[Rp] c) ⊗ₜ[A ⊗[R] R'] m) =
      b ⊗ₜ[A] (m ⊗ₜ[R'] c) := by
  let := mapAlgebraMid (R := R) (A := A) (R' := R') (Rp := Rp) (B := B) (C := C)
  exact localizedRearrange_tmul S mapAlgebraMid_algebraMap_tmul b c m

end Localized

/-! ### Base change along an isomorphism of the base change ring -/

section BaseCongr

variable {A B₁ B₂ M : Type*} [CommRing A] [CommRing B₁] [CommRing B₂]
  [Algebra A B₁] [Algebra A B₂] [AddCommGroup M] [Module A M]
  (f : B₁ →+* B₂) (g : B₂ →+* B₁) (hgf : ∀ x, g (f x) = x) (hfg : ∀ z, f (g z) = z)
  (hf : ∀ a : A, f (algebraMap A B₁ a) = algebraMap A B₂ a)

include hgf hfg hf in
/-- **Base change along an isomorphism of the base change ring.** A ring homomorphism
`f : B₁ → B₂` of `A`-algebras with a two-sided inverse gives `B₁ ⊗_A M ≅ B₂ ⊗_A M` for every
`A`-module `M`. -/
def baseCongr : B₁ ⊗[A] M ≃ₗ[A] B₂ ⊗[A] M :=
  TensorProduct.congr
    (AlgEquiv.ofRingEquiv (f :=
      { toFun := f, invFun := g, left_inv := hgf, right_inv := hfg,
        map_mul' := f.map_mul, map_add' := f.map_add }) hf).toLinearEquiv
    (LinearEquiv.refl A M)

include hgf hfg hf in
@[simp] theorem baseCongr_tmul (b : B₁) (m : M) :
    baseCongr f g hgf hfg hf (b ⊗ₜ[A] m) = f b ⊗ₜ[A] m := by
  simp [baseCongr]

include hgf hfg hf in
@[simp] theorem baseCongr_symm_tmul (z : B₂) (m : M) :
    (baseCongr f g hgf hfg hf (M := M)).symm (z ⊗ₜ[A] m) = g z ⊗ₜ[A] m :=
  (LinearEquiv.symm_apply_eq _).mpr (by rw [baseCongr_tmul, hfg])

end BaseCongr

end Stacks.TensorProductPushout

end
