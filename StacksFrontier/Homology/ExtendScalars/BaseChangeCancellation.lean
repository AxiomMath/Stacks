module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksFrontier.Homology.TorAmplitude.Defs

/-!
# Cancelling a base change against an extension of scalars

Let `R → B` and `R → R'` be ring maps.  For a `B`-module `M` there is a cancellation
`(B ⊗_R R') ⊗_B M = M ⊗_R R'`: extending the scalars of `M` along the left coprojection
`B → B ⊗_R R'` is tensoring `M`, read as an `R`-module, with `R'`.  No ring isomorphism occurs in
it, and it is natural in `M`, so it carries a statement about the cohomology of `K^• ⊗_R R'` to
one about the cohomology of the termwise extension of scalars of `K^•` along the left
coprojection.

## Main definitions

* `StacksDraft.BaseChangeCancellation.cancelAddEquiv` -- the cancellation itself, as an additive
  equivalence.

## Main results

* `StacksDraft.BaseChangeCancellation.isZero_homology_iff_function_exact` -- the cohomology of a
  cochain complex of modules vanishes in degree `n` exactly when its three terms around degree
  `n` are exact in the middle.
* `StacksDraft.BaseChangeCancellation.cancelAddEquiv_symm_naturality` -- the cancellation is
  natural.
* `StacksDraft.BaseChangeCancellation.isZero_homology_extendScalars_includeLeft_iff` -- the
  cohomology of the termwise extension of scalars of `K^•` along `B → B ⊗_R R'` vanishes in a
  degree exactly when that of `K^• ⊗_R R'` does.

## Implementation notes

Two module structures on `B ⊗_R R'` as a `B`-module are in play and they are *not*
interchangeable: `ModuleCat.extendScalars` builds its tensor product with the structure coming
from `Module.compHom` of the ring map, `b` acting as multiplication by `b ⊗ₜ 1`, while
`TensorProduct.AlgebraTensorModule.cancelBaseChange` is stated for `TensorProduct.leftModule`, `b`
acting on the left factor.  The two actions agree -- that is
`StacksDraft.BaseChangeCancellation.includeLeftRingHom_mul`, which is `Algebra.smul_def` read
through `Algebra.TensorProduct.algebraMap_def` -- but the instances differ, so the cancellation
does not apply directly.  The mediating equivalence
`StacksDraft.BaseChangeCancellation.relabelIncludeLeft` is the identity map seen as `B`-linear for
the two structures, and the cancellation is `TensorProduct.congr` of it with the identity followed
by Mathlib's.

Naturality is stated and proved on the *inverse* of the cancellation.  The source there is the
honest tensor product `M ⊗_R R'`, so its generators may be introduced and the two sides compared
on them; on the other side the source is a value of `ModuleCat.extendScalars`, whose elements are
only a tensor product after unfolding, and introducing a generator there leaves a goal that the
elaborator will not rewrite in.

The conclusion is stated as an additive equivalence rather than a linear one: the two sides are
modules over different rings -- `B ⊗_R R'` on the left and `R` on the right -- and nothing but the
additive structure is shared.  That is all the consumer needs, exactness of a sequence of modules
being a statement about the underlying additive groups.
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u v

namespace StacksDraft.BaseChangeCancellation

noncomputable section

/-! ### Vanishing cohomology as exactness of three terms -/

/-- The cohomology of a cochain complex of modules vanishes in degree `n` exactly when
`C^{n-1} → C^n → C^{n+1}` is exact in the middle. -/
theorem isZero_homology_iff_function_exact {S : Type u} [Ring S]
    (C : CochainComplex (ModuleCat.{v} S) ℤ) (n : ℤ) :
    Limits.IsZero (C.homology n) ↔
      Function.Exact (C.d (n - 1) n).hom (C.d n (n + 1)).hom := by
  have hprev : (ComplexShape.up ℤ).prev n = n - 1 := by simp [CochainComplex.prev]
  have hnext : (ComplexShape.up ℤ).next n = n + 1 := by simp [CochainComplex.next]
  rw [← HomologicalComplex.exactAt_iff_isZero_homology, HomologicalComplex.exactAt_iff,
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  change Function.Exact (C.d ((ComplexShape.up ℤ).prev n) n).hom
    (C.d n ((ComplexShape.up ℤ).next n)).hom ↔ _
  rw [hprev, hnext]

/-! ### The cancellation -/

variable {R B R' : Type u} [CommRing R] [CommRing B] [CommRing R'] [Algebra R B] [Algebra R R']

/-- Multiplication by `b ⊗ₜ 1` on `B ⊗_R R'` is the action of `b` on the left factor: the two
`B`-module structures used by `ModuleCat.extendScalars` and by
`TensorProduct.AlgebraTensorModule.cancelBaseChange` agree. -/
theorem includeLeftRingHom_mul (b : B) (y : B ⊗[R] R') :
    (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := B) (B := R') b) * y = b • y := by
  rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_def]
  simp

/-- **The mediating equivalence.**  `B ⊗_R R'` as a `B`-module by restriction of scalars along the
left coprojection is `B ⊗_R R'` as a `B`-module by the action on the left factor, by the identity
map. -/
def relabelIncludeLeft :
    ((ModuleCat.restrictScalars (Algebra.TensorProduct.includeLeftRingHom :
        B →+* B ⊗[R] R')).obj (ModuleCat.of (B ⊗[R] R') (B ⊗[R] R'))) ≃ₗ[B] (B ⊗[R] R') :=
  AddEquiv.toLinearEquiv (AddEquiv.refl _) fun b x => includeLeftRingHom_mul b x

/-- **The base-change cancellation** `(B ⊗_R R') ⊗_B M = M ⊗_R R'`.  The left-hand side is the
extension of scalars of `M` along the left coprojection `B → B ⊗_R R'`; the right-hand side is
`M`, read as an `R`-module, tensored with `R'`. -/
def cancelAddEquiv (M : ModuleCat.{u} B) :
    TensorProduct B
        ((ModuleCat.restrictScalars (Algebra.TensorProduct.includeLeftRingHom :
          B →+* B ⊗[R] R')).obj (ModuleCat.of (B ⊗[R] R') (B ⊗[R] R'))) M ≃+
      TensorProduct R ((ModuleCat.restrictScalars (algebraMap R B)).obj M)
        (ModuleCat.of R R') :=
  letI : IsScalarTower R B ((ModuleCat.restrictScalars (algebraMap R B)).obj M) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  ((TensorProduct.congr relabelIncludeLeft
        (LinearEquiv.refl B ((ModuleCat.restrictScalars (algebraMap R B)).obj M))).trans
      ((TensorProduct.comm B (B ⊗[R] R')
          ((ModuleCat.restrictScalars (algebraMap R B)).obj M)).trans
        (TensorProduct.AlgebraTensorModule.cancelBaseChange R B B
          ((ModuleCat.restrictScalars (algebraMap R B)).obj M) R'))).toAddEquiv

/-- Tensoring a map with `R'` on the right, as a map of the underlying additive groups, with
source and target written as tensor products rather than as values of the functor.  That is what
lets the generators be used. -/
def tensorMapAddMonoidHom {M N : ModuleCat.{u} B} (φ : M ⟶ N) :
    TensorProduct R ((ModuleCat.restrictScalars (algebraMap R B)).obj M) (ModuleCat.of R R') →+
      TensorProduct R ((ModuleCat.restrictScalars (algebraMap R B)).obj N)
        (ModuleCat.of R R') :=
  ((StacksDraft.TorAmplitude.tensorModuleRight (ModuleCat.of R R')).map
    ((ModuleCat.restrictScalars (algebraMap R B)).map φ)).hom.toAddMonoidHom

/-- **The cancellation is natural in `M`.**  Read on the inverse it is an identity on
generators: `m ⊗ₜ r'` goes to `(1 ⊗ₜ r') ⊗ₜ m` on both sides, and `φ` is applied in the second
factor either way. -/
theorem cancelAddEquiv_symm_naturality {M N : ModuleCat.{u} B} (φ : M ⟶ N) :
    (((ModuleCat.extendScalars (Algebra.TensorProduct.includeLeftRingHom :
          B →+* B ⊗[R] R')).map φ).hom.toAddMonoidHom).comp
        (cancelAddEquiv (R := R) (R' := R') M).symm.toAddMonoidHom =
      (cancelAddEquiv (R := R) (R' := R') N).symm.toAddMonoidHom.comp
        (tensorMapAddMonoidHom (R := R) (R' := R') φ) := by
  refine AddMonoidHom.ext fun w => ?_
  induction w using TensorProduct.inductionOn with
  | tmul m r' => rfl
  | add w w' h h' =>
      exact (map_add _ _ _).trans ((congrArg₂ (· + ·) h h').trans (map_add _ _ _).symm)

/-- **The vanishing of the cohomology of `K^• ⊗_R R'` read after extension of scalars along the
left coprojection.**  The degree-`j` cohomology of the termwise extension of scalars of `K^•`
along `B → B ⊗_R R'` vanishes exactly when that of `K^• ⊗_R R'` does.

Both are exactness of three terms in the middle,
`StacksDraft.BaseChangeCancellation.isZero_homology_iff_function_exact`, and the three terms are
identified by `StacksDraft.BaseChangeCancellation.cancelAddEquiv`, which is natural. -/
theorem isZero_homology_extendScalars_includeLeft_iff
    (E : CochainComplex (ModuleCat.{u} B) ℤ) (j : ℤ) :
    Limits.IsZero ((((ModuleCat.extendScalars (Algebra.TensorProduct.includeLeftRingHom :
          B →+* B ⊗[R] R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj E).homology j) ↔
      Limits.IsZero ((((StacksDraft.TorAmplitude.tensorModuleRight
            (ModuleCat.of R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((ModuleCat.restrictScalars (algebraMap R B)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj E)).homology j) := by
  rw [isZero_homology_iff_function_exact, isZero_homology_iff_function_exact]
  simp only [Functor.mapHomologicalComplex_obj_d]
  exact Function.Exact.iff_of_ladder_addEquiv
    (cancelAddEquiv (R := R) (R' := R') (E.X (j - 1))).symm
    (cancelAddEquiv (R := R) (R' := R') (E.X j)).symm
    (cancelAddEquiv (R := R) (R' := R') (E.X (j + 1))).symm
    (cancelAddEquiv_symm_naturality (E.d (j - 1) j))
    (cancelAddEquiv_symm_naturality (E.d j (j + 1)))

end

end StacksDraft.BaseChangeCancellation

end
