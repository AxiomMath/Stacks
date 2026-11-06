module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Tactic.SuppressCompilation
public import StacksCore.Algebra.Algebra.Tower
public import StacksCore.Algebra.Module.LinearMap.Defs
import StacksCore.Tactic.StacksAttribute

/-! ## Tower law of tensor products -/

add_to_stacks 00D2 TensorProduct.AlgebraTensorModule.assoc
add_to_stacks 05G4 LinearMap.baseChange

@[expose] public section

open scoped TensorProduct

/-! ### Tensor-hom adjunction across a ring map (Stacks 08YQ)

For `R → S`, `S`-modules `M`, `N` and an `R`-module `P`, the tag asserts
`Hom_R(M ⊗_S N, P) = Hom_S(M, Hom_R(N, P))`.

Mathlib's heterobasic `TensorProduct.AlgebraTensorModule.lift.equiv` is the *mirror image* of
this — it tensors over the smaller ring and takes `Hom` over the bigger one — and it cannot be
reoriented, since `M ⊗[S] N` is a proper quotient of `M ⊗[R] N`. Mathlib has no form of 08YQ
itself either; the nearest results (`homTensorHomEquiv` and friends in
`Mathlib/LinearAlgebra/Contraction.lean`) are single-ring and need `Module.Free` + `Module.Finite`.

Nor does the tag's right-hand side typecheck out of the box: `Hom_R(N, P)` carries no `S`-action
by instance search, because the relevant action is on the *source*, `(s • f) n = f (s • n)`.
Mathlib does have that action in full generality, but indexed by the `DomMulAct` synonym
`Sᵈᵐᵃ` rather than by `S` — `LinearMap.instModuleDomMulActOfSMulCommClass`. The indexing is
deliberate: as a `Module S` it would collide with the *target* action `LinearMap.module`, and
`Mathlib/GroupTheory/GroupAction/DomAct/Basic.lean` says so explicitly. The two actions are
genuinely different — over `ℝ ⊂ ℂ` they differ on complex conjugation — and agree exactly on the
`S`-linear maps. `homSourceModule` below transports the `Sᵈᵐᵃ` instance back along
`RingEquiv.toOpposite`, legitimate because `S` is commutative, following the same recipe as
Mathlib's own `CharacterModule.instModule`.

It stays a *local* instance for the reason above. One consequence is worth recording rather than
rediscovering: with it in scope, `M →ₗ[S] (N →ₗ[R] P)` — the codomain of `tensorHomAdjEquiv` —
resolves `Module S` to `homSourceModule` but `SMul S` to `LinearMap.instSMul`, a genuine
non-defeq diamond. It is harmless here precisely because that type consists of `S`-linear maps,
where the two actions coincide; the same happens with the `Sᵈᵐᵃ` instance, so it is not
something this file introduces.

The backwards direction goes through `TensorProduct.liftAddHom`, whose balancing hypothesis is
exactly `g (s • m) n = g m (s • n)` — which is `g`'s `S`-linearity read through the source
action. `TensorProduct.lift` is unusable here because it wants an `S`-module target and `P` is
only an `R`-module.
-/

section TensorHom

variable {R S M N P : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
  [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
  [AddCommGroup P] [Module R P]

/-- `S` acts on `Hom_R(N, P)` through the source: `(s • f) n = f (s • n)`.

This is Mathlib's `LinearMap.instModuleDomMulActOfSMulCommClass : Module Sᵈᵐᵃ (N →ₗ[R] P)`
transported along `RingEquiv.toOpposite S : S ≃+* Sᵈᵐᵃ`; see the module docstring for why
Mathlib indexes it by `Sᵈᵐᵃ`. Note the `_` is load-bearing — spelling it `RingEquiv.toOpposite S`
makes elaboration settle on `Sᵐᵒᵖ` and instance search then fails. -/
@[instance_reducible]
def homSourceModule : Module S (N →ₗ[R] P) :=
  fast_instance% Module.compHom (N →ₗ[R] P) (RingEquiv.toOpposite _ |>.toRingHom : S →+* Sᵈᵐᵃ)

attribute [local instance] homSourceModule

@[simp]
theorem homSourceModule_smul_apply (s : S) (f : N →ₗ[R] P) (n : N) : (s • f) n = f (s • n) := rfl

suppress_compilation

/-- Currying: an `R`-linear map out of `M ⊗_S N` is `S`-linear in the first slot. -/
@[simps]
def tensorHomCurry (f : M ⊗[S] N →ₗ[R] P) : M →ₗ[S] (N →ₗ[R] P) where
  toFun m := f ∘ₗ (TensorProduct.mk S M N m).restrictScalars R
  map_add' m m' := by ext n; simp
  map_smul' s m := by ext n; simp

/-- `tensorHomCurry` bundled as an `S`-linear map.

Worth doing before building the equivalence rather than after: both fields are `rfl` here, so
`tensorHomAdjEquiv` can inherit them with `__ := tensorHomCurryL` instead of discharging
`map_add'` and `map_smul'` itself — the latter otherwise needs the tensor balancing
`TensorProduct.smul_tmul`. -/
@[simps]
def tensorHomCurryL : (M ⊗[S] N →ₗ[R] P) →ₗ[S] (M →ₗ[S] (N →ₗ[R] P)) where
  toFun := tensorHomCurry
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Uncurrying, via `TensorProduct.liftAddHom`: the balancing hypothesis is `g`'s `S`-linearity. -/
def tensorHomUncurry (g : M →ₗ[S] (N →ₗ[R] P)) : M ⊗[S] N →ₗ[R] P where
  toFun := TensorProduct.liftAddHom {
    toFun m := (g m).toAddMonoidHom
    map_zero' := by simp
    map_add' := by simp [LinearMap.add_toAddMonoidHom]} (by simp)
  map_add' := map_add _
  map_smul' r x := by
    induction x with
    | tmul m n => simp [TensorProduct.smul_tmul', IsScalarTower.map_smul]
    | add x y hu hv => simp [hu, hv]

/-- **Stacks 08YQ**: `Hom_R(M ⊗_S N, P) = Hom_S(M, Hom_R(N, P))` for `S`-modules `M`, `N` and an
`R`-module `P`.

Stated `S`-linearly rather than as a bare bijection: both sides carry the source `S`-action —
the left through `M ⊗_S N`, the right through `Hom_R(N, P)` — so `S` is the finer structure and
`R`-linearity is its restriction. This matches how Mathlib states the sibling tag 05DQ, where
`LinearMap.liftBaseChangeEquiv` is linear over the *bigger* ring. -/
@[stacks 08YQ]
noncomputable def tensorHomAdjEquiv : (M ⊗[S] N →ₗ[R] P) ≃ₗ[S] (M →ₗ[S] (N →ₗ[R] P)) where
  __ := tensorHomCurryL
  invFun := tensorHomUncurry
  left_inv _ := LinearMap.ext fun x ↦ TensorProduct.inductionOn x (fun _ _ ↦ rfl) <| by
    simp +contextual
  right_inv _ := rfl

end TensorHom
