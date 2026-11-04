module

public import Mathlib.RingTheory.Kaehler.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartGlue.DerivationAlong

/-!
# Derivations along an algebra map are semilinear maps out of the differentials

Let `R` and `C` be algebras over a commutative ring `A'`, let `g : R → C` be an algebra map and
let `N` be a `C`-module. The derivations of `R` along `g` with values in `N`,
`Stacks.ChartGlue.DerAlong g N`, are the `g`-semilinear maps `Ω[R⁄A'] → N`: this is the universal
property of the module of differentials, `KaehlerDifferential.linearMapEquivDerivation`, for the
`R`-module structure on `N` induced by `g`, read without making that structure an instance.

## Main definitions

* `Stacks.ChartGlue.DerAlong.toSemilinear`: the semilinear map out of `Ω[R⁄A']` attached to a
  derivation along `g`.
* `Stacks.ChartGlue.DerAlong.ofSemilinear`: the derivation along `g` attached to a semilinear map.
* `Stacks.ChartGlue.DerAlong.semilinearEquiv`: the two constructions form an equivalence.

## Main results

* `Stacks.ChartGlue.DerAlong.semilinear_ext`: a semilinear map out of `Ω[R⁄A']` is determined by
  its values on the universal derivation.
-/

@[expose] public noncomputable section

universe u v w

namespace Stacks.ChartGlue

namespace DerAlong

variable {A' : Type w} [CommRing A'] {R : Type u} [CommRing R] [Algebra A' R]
  {C : Type u} [CommRing C] [Algebra A' C] {N : Type v} [AddCommGroup N] [Module C N]
  {g : R →ₐ[A'] C}

/-- The derivation along `g` attached to a `g`-semilinear map out of the differentials. -/
def ofSemilinear (l : Ω[R⁄A'] →ₛₗ[(g : R →+* C)] N) : DerAlong g N :=
  ⟨fun r ↦ l (KaehlerDifferential.D A' R r),
    fun r s ↦ by rw [_root_.map_add, _root_.map_add],
    fun a ↦ by rw [Derivation.map_algebraMap, _root_.map_zero],
    fun r s ↦ by
      rw [Derivation.leibniz, _root_.map_add, l.map_smulₛₗ, l.map_smulₛₗ]
      rfl⟩

/-- `ofSemilinear l r = l (d r)`. -/
@[simp] lemma ofSemilinear_apply (l : Ω[R⁄A'] →ₛₗ[(g : R →+* C)] N) (r : R) :
    ofSemilinear l r = l (KaehlerDifferential.D A' R r) := rfl

/-- The `R`-module structure on a `C`-module induced by `g`. -/
abbrev inducedModule (g : R →ₐ[A'] C) : Module R N := Module.compHom N (g : R →+* C)

/-- The `A'`-module structure on a `C`-module induced by `C`. -/
abbrev inducedBaseModule : Module A' N := Module.compHom N (algebraMap A' C)

/-- The induced module structures form a scalar tower `A' → R → N`. -/
lemma inducedModule_isScalarTower (g : R →ₐ[A'] C) :
    letI := inducedModule (N := N) g
    letI := inducedBaseModule (A' := A') (C := C) (N := N)
    IsScalarTower A' R N :=
  let := inducedModule (N := N) g
  let := inducedBaseModule (A' := A') (C := C) (N := N)
  ⟨fun a r n ↦ by
    show g (a • r) • n = algebraMap A' C a • (g r • n)
    rw [_root_.map_smul, Algebra.smul_def, mul_smul]⟩

/-- The Mathlib derivation attached to a derivation along `g`, for the induced module
structures. -/
def toDerivation (δ : DerAlong g N) :
    letI := inducedModule (N := N) g
    letI := inducedBaseModule (A' := A') (C := C) (N := N)
    Derivation A' R N :=
  letI := inducedModule (N := N) g
  letI := inducedBaseModule (A' := A') (C := C) (N := N)
  { toFun := δ
    map_add' := δ.map_add
    map_smul' := fun a r ↦ by
      rw [δ.map_smul]
      rfl
    map_one_eq_zero' := δ.map_one
    leibniz' := fun r s ↦ by
      change δ (r * s) = g r • δ s + g s • δ r
      rw [δ.leibniz] }

/-- The `g`-semilinear map out of the differentials attached to a derivation along `g`. -/
def toSemilinear (δ : DerAlong g N) : Ω[R⁄A'] →ₛₗ[(g : R →+* C)] N :=
  letI := inducedModule (N := N) g
  letI := inducedBaseModule (A' := A') (C := C) (N := N)
  haveI := inducedModule_isScalarTower (N := N) g
  { toFun := δ.toDerivation.liftKaehlerDifferential
    map_add' := _root_.map_add _
    map_smul' := fun r ω ↦ (δ.toDerivation.liftKaehlerDifferential).map_smul r ω }

/-- `toSemilinear δ (d r) = δ r`. -/
@[simp] lemma toSemilinear_D (δ : DerAlong g N) (r : R) :
    δ.toSemilinear (KaehlerDifferential.D A' R r) = δ r :=
  let := inducedModule (N := N) g
  let := inducedBaseModule (A' := A') (C := C) (N := N)
  have := inducedModule_isScalarTower (N := N) g
  δ.toDerivation.liftKaehlerDifferential_comp_D r

/-- `ofSemilinear` is a left inverse of `toSemilinear`. -/
lemma ofSemilinear_toSemilinear (δ : DerAlong g N) : ofSemilinear δ.toSemilinear = δ :=
  DerAlong.ext (funext fun r ↦ δ.toSemilinear_D r)

/-- A semilinear map out of the differentials is determined by its values on the image of the
universal derivation. -/
lemma semilinear_ext {l l' : Ω[R⁄A'] →ₛₗ[(g : R →+* C)] N}
    (h : ∀ r, l (KaehlerDifferential.D A' R r) = l' (KaehlerDifferential.D A' R r)) : l = l' := by
  ext ω
  have hω : ω ∈ Submodule.span R (Set.range (KaehlerDifferential.D A' R)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hω using Submodule.span_induction with
  | mem x hx => obtain ⟨r, rfl⟩ := hx; exact h r
  | zero => simp
  | add x y _ _ hx hy => rw [_root_.map_add, _root_.map_add, hx, hy]
  | smul a x _ hx => rw [l.map_smulₛₗ, l'.map_smulₛₗ, hx]

/-- `ofSemilinear` is a right inverse of `toSemilinear`. -/
lemma toSemilinear_ofSemilinear (l : Ω[R⁄A'] →ₛₗ[(g : R →+* C)] N) :
    (ofSemilinear l).toSemilinear = l :=
  semilinear_ext fun r ↦ toSemilinear_D _ r

/-- **Derivations along `g` are the `g`-semilinear maps out of the differentials.** -/
def semilinearEquiv : DerAlong g N ≃ (Ω[R⁄A'] →ₛₗ[(g : R →+* C)] N) where
  toFun := toSemilinear
  invFun := ofSemilinear
  left_inv := ofSemilinear_toSemilinear
  right_inv := toSemilinear_ofSemilinear

/-- `toSemilinear` commutes with postcomposition by a `C`-linear map. -/
lemma toSemilinear_postcomp {N' : Type v} [AddCommGroup N'] [Module C N'] (h : N →ₗ[C] N')
    (δ : DerAlong g N) : (δ.postcomp h).toSemilinear = h.comp δ.toSemilinear :=
  semilinear_ext fun r ↦ by simp

/-- `toSemilinear` is additive. -/
lemma toSemilinear_add (δ ε : DerAlong g N) :
    (δ + ε).toSemilinear = δ.toSemilinear + ε.toSemilinear :=
  semilinear_ext fun r ↦ by simp

/-- `toSemilinear` is `C`-linear. -/
lemma toSemilinear_smul (c : C) (δ : DerAlong g N) :
    (c • δ).toSemilinear = c • δ.toSemilinear :=
  semilinear_ext fun r ↦ by simp

end DerAlong

end Stacks.ChartGlue

end
