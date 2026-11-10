module

public import Mathlib.LinearAlgebra.Basis.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ChernComponent.Trivialization
public import StacksFrontier.AlgebraicGeometry.Modules.TensorStalkGenerators

/-!
# The stalk of an invertible module is free of rank one

Let `X` be a scheme and `L` an invertible `𝒪_X`-module. Near every point `x` there is a section
of `L` whose germ `m` is a *stalk basis* in the sense of `Stacks.Divisors.IsStalkBasis`
(bijectivity of `r ↦ r • m`). Such a germ generates `L_x`, the stalk `L_x` is free of rank one
on it, and `L_x ≃ₗ 𝒪_{X, x}` by the coordinate in that basis.

For any `𝒪_X`-module `F`, tensoring with `L` does not change the stalk:
`(F ⊗_{𝒪_X} L)_x ≃ₗ F_x`, by the comparison of Tag 01CB followed by `L_x ≃ₗ 𝒪_{X, x}` and
`F_x ⊗ 𝒪_{X, x} ≃ₗ F_x`. This isomorphism carries the product of `n ∈ F_x` with the stalk
basis back to `n`.

## Main definitions

* `Stacks.Divisors.IsStalkBasis.linearEquiv`: multiplication by a stalk basis, as an
  isomorphism `𝒪_{X, x} ≃ₗ L_x`.
* `Stacks.Divisors.IsStalkBasis.coord`: its inverse, the coordinate of `L_x` in the basis.
* `Stacks.Divisors.IsStalkBasis.basis`: the stalk basis read as a `Basis (Fin 1)`.
* `Stacks.InvertibleStalk.tensorStalkRightEquiv` and
  `Stacks.InvertibleStalk.tensorStalkLeftEquiv`: the isomorphisms `(F ⊗ L)_x ≃ₗ F_x` and
  `(L ⊗ F)_x ≃ₗ F_x` attached to a stalk basis of `L` at `x`.

## Main results

* `Stacks.Divisors.IsStalkBasis.span_eq_top`: a stalk basis generates the stalk.
* `Stacks.Divisors.IsStalkBasis.free`: the stalk is a free module.
* `Stacks.InvertibleStalk.exists_germ_isStalkBasis`: an invertible module has, near any point, a
  section whose germ is a stalk basis there.
* `Stacks.InvertibleStalk.nonempty_linearEquiv_stalk` and `Stacks.InvertibleStalk.free_stalk`:
  the stalk of an invertible module is free of rank one.
* `Stacks.InvertibleStalk.tensorStalkRightEquiv_tensorStalkTmul`: the isomorphism
  `(F ⊗ L)_x ≃ₗ F_x` carries the product of an element of `F_x` with the trivializing germ to
  that element.
* `Stacks.InvertibleStalk.nonempty_tensorStalkRightEquiv`: the existence form of
  `(F ⊗ L)_x ≃ₗ F_x` for an invertible `L`.
* `Stacks.InvertibleStalk.isInvertible_presheaf_iff`: the two spellings of the invertibility
  hypothesis are the same proposition.

## References

* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped TensorProduct

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} {L : X.Modules} {x : X} {m : L.presheaf.stalk x}

/-- **A stalk basis generates the stalk.** -/
theorem IsStalkBasis.span_eq_top (hm : IsStalkBasis L x m) :
    Submodule.span ↑(X.presheaf.stalk x) {m} = ⊤ :=
  Submodule.eq_top_iff'.2 fun z =>
    Submodule.mem_span_singleton.2 (hm.surjective z)

/-- **Multiplication by a stalk basis**, as an isomorphism `𝒪_{X, x} ≃ₗ L_x`. -/
def IsStalkBasis.linearEquiv (hm : IsStalkBasis L x m) :
    X.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] L.presheaf.stalk x :=
  LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton ↑(X.presheaf.stalk x) ↑(L.presheaf.stalk x) m) hm

/-- `IsStalkBasis.linearEquiv` sends `r` to `r • m`. -/
@[simp] theorem IsStalkBasis.linearEquiv_apply (hm : IsStalkBasis L x m)
    (r : X.presheaf.stalk x) : hm.linearEquiv r = r • m := rfl

/-- `IsStalkBasis.linearEquiv` sends `1` to the stalk basis. -/
@[simp] theorem IsStalkBasis.linearEquiv_one (hm : IsStalkBasis L x m) :
    hm.linearEquiv 1 = m := (hm.linearEquiv_apply 1).trans (one_smul _ m)

/-- **The coordinate of the stalk in a stalk basis**, `L_x ≃ₗ 𝒪_{X, x}`: the inverse of
multiplication by the basis. -/
def IsStalkBasis.coord (hm : IsStalkBasis L x m) :
    L.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] X.presheaf.stalk x :=
  hm.linearEquiv.symm

/-- The coordinate of `r • m` is `r`. -/
@[simp] theorem IsStalkBasis.coord_smul (hm : IsStalkBasis L x m) (r : X.presheaf.stalk x) :
    hm.coord (r • m) = r :=
  hm.linearEquiv.symm_apply_apply r

/-- The coordinate of the stalk basis itself is `1`. -/
@[simp] theorem IsStalkBasis.coord_self (hm : IsStalkBasis L x m) : hm.coord m = 1 :=
  (congrArg (fun y : L.presheaf.stalk x => hm.coord y)
    (one_smul ↑(X.presheaf.stalk x) m).symm).trans (hm.coord_smul 1)

/-- The inverse of the coordinate sends `r` to `r • m`. -/
@[simp] theorem IsStalkBasis.coord_symm_apply (hm : IsStalkBasis L x m)
    (r : X.presheaf.stalk x) : hm.coord.symm r = r • m := rfl

/-- Every element of the stalk is its coordinate times the stalk basis. -/
@[simp] theorem IsStalkBasis.smul_coord (hm : IsStalkBasis L x m) (n : L.presheaf.stalk x) :
    hm.coord n • m = n :=
  hm.linearEquiv.apply_symm_apply n

/-- **The stalk is free of rank one on a stalk basis**, read as a one-element `Basis`. -/
def IsStalkBasis.basis (hm : IsStalkBasis L x m) :
    Module.Basis (Fin 1) ↑(X.presheaf.stalk x) ↑(L.presheaf.stalk x) :=
  (Module.Basis.singleton (Fin 1) ↑(X.presheaf.stalk x)).map hm.linearEquiv

/-- The one element of `IsStalkBasis.basis` is the stalk basis. -/
@[simp] theorem IsStalkBasis.basis_apply (hm : IsStalkBasis L x m) (i : Fin 1) :
    hm.basis i = m :=
  ((Module.Basis.singleton (Fin 1) ↑(X.presheaf.stalk x)).map_apply hm.linearEquiv i).trans
    ((congrArg (fun y : X.presheaf.stalk x => hm.linearEquiv y)
      (Module.Basis.singleton_apply (Fin 1) ↑(X.presheaf.stalk x) i)).trans hm.linearEquiv_one)

/-- The stalk of a module with a stalk basis at a point is a free module over the local ring
there. -/
theorem IsStalkBasis.free (hm : IsStalkBasis L x m) :
    Module.Free ↑(X.presheaf.stalk x) ↑(L.presheaf.stalk x) :=
  Module.Free.of_basis hm.basis

end Stacks.Divisors

namespace Stacks.InvertibleStalk

open Stacks.Divisors

variable {X : Scheme.{u}}

/-! ### The stalk of an invertible module -/

-- The forward direction duplicates `Stacks.Divisors.isInvertible_presheaf`; the two should be
-- merged when the two spellings are deduplicated.
/-- **The two spellings of the invertibility hypothesis agree.** The structure sheaf of a scheme
read as a sheaf of commutative rings is written both `X.presheaf` with sheaf condition
`X.ringCatSheaf.2` and `X.sheaf.obj` with sheaf condition `X.ringCatSheaf.property`, and the two
invertibility predicates are the same proposition. -/
theorem isInvertible_presheaf_iff (L : X.Modules) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L ↔
      AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
  Iff.rfl

/-- **An invertible module has a trivializing basis near every point.** Some open neighbourhood
of `x` carries a section of `L` whose germ at `x` is a basis of the free rank-one
`𝒪_{X, x}`-module `L_x`. -/
theorem exists_germ_isStalkBasis (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (x : X) :
    ∃ (V : X.Opens) (hx : x ∈ V) (e : Γ(L, V)),
      IsStalkBasis L x (L.presheaf.germ V x hx e) := by
  obtain ⟨V, hx, e, he⟩ := isTrivializedNear_of_isInvertible L x
  exact ⟨V, hx, e, he x hx⟩

/-- **The stalk of an invertible module is isomorphic to the local ring.** -/
theorem nonempty_linearEquiv_stalk (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (x : X) :
    Nonempty (L.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] X.presheaf.stalk x) := by
  obtain ⟨_, _, _, he⟩ := exists_germ_isStalkBasis L x
  exact ⟨he.coord⟩

/-- **The stalk of an invertible module is free**, of rank one. -/
theorem free_stalk (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (x : X) :
    Module.Free ↑(X.presheaf.stalk x) ↑(L.presheaf.stalk x) := by
  obtain ⟨_, _, _, he⟩ := exists_germ_isStalkBasis L x
  exact he.free

/-! ### Tensoring with an invertible module does nothing to a stalk -/

variable (F : X.Modules) {L : X.Modules} {x : X} {m : L.presheaf.stalk x}

/-- **The stalk of `F ⊗_{𝒪_X} L` is the stalk of `F`**, when `L` has a stalk basis at the point:
the comparison of Tag 01CB identifies `(F ⊗ L)_x` with `F_x ⊗ L_x`, the basis identifies `L_x`
with `𝒪_{X, x}`, and a tensor product with the base ring collapses. -/
def tensorStalkRightEquiv (hm : IsStalkBasis L x m) :
    (Scheme.Modules.tensorObj F L).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      F.presheaf.stalk x :=
  (tensorStalkEquiv F L x).trans
    ((TensorProduct.congr (LinearEquiv.refl ↑(X.presheaf.stalk x) ↑(F.presheaf.stalk x))
      hm.coord).trans (TensorProduct.rid ↑(X.presheaf.stalk x) ↑(F.presheaf.stalk x)))

/-- The isomorphism `(F ⊗ L)_x ≃ₗ F_x` reads off the coordinate of the second factor. -/
theorem tensorStalkRightEquiv_tensorStalkTmul' (hm : IsStalkBasis L x m)
    (n : F.presheaf.stalk x) (p : L.presheaf.stalk x) :
    tensorStalkRightEquiv F hm (tensorStalkTmul F L x n p) = hm.coord p • n := by
  change (TensorProduct.rid ↑(X.presheaf.stalk x) ↑(F.presheaf.stalk x))
      (TensorProduct.congr (LinearEquiv.refl ↑(X.presheaf.stalk x) ↑(F.presheaf.stalk x))
        hm.coord (tensorStalkEquiv F L x (tensorStalkTmul F L x n p))) = _
  rw [tensorStalkEquiv_tensorStalkTmul, TensorProduct.congr_tmul, TensorProduct.rid_tmul]
  rfl

/-- **The isomorphism `(F ⊗ L)_x ≃ₗ F_x` undoes the trivializing germ**: the product of
`n ∈ F_x` with the stalk basis goes back to `n`. -/
theorem tensorStalkRightEquiv_tensorStalkTmul (hm : IsStalkBasis L x m)
    (n : F.presheaf.stalk x) :
    tensorStalkRightEquiv F hm (tensorStalkTmul F L x n m) = n := by
  rw [tensorStalkRightEquiv_tensorStalkTmul' F hm n m, hm.coord_self, one_smul]

/-- The inverse of `(F ⊗ L)_x ≃ₗ F_x` multiplies by the stalk basis. -/
theorem tensorStalkRightEquiv_symm_apply (hm : IsStalkBasis L x m) (n : F.presheaf.stalk x) :
    (tensorStalkRightEquiv F hm).symm n = tensorStalkTmul F L x n m :=
  ((tensorStalkRightEquiv F hm).eq_symm_apply.2
    (tensorStalkRightEquiv_tensorStalkTmul F hm n)).symm

/-- **The stalk of `L ⊗_{𝒪_X} F` is the stalk of `F`**, when `L` has a stalk basis at the
point. -/
def tensorStalkLeftEquiv (hm : IsStalkBasis L x m) :
    (Scheme.Modules.tensorObj L F).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      F.presheaf.stalk x :=
  (tensorStalkEquiv L F x).trans
    ((TensorProduct.congr hm.coord
      (LinearEquiv.refl ↑(X.presheaf.stalk x) ↑(F.presheaf.stalk x))).trans
      (TensorProduct.lid ↑(X.presheaf.stalk x) ↑(F.presheaf.stalk x)))

/-- **The isomorphism `(L ⊗ F)_x ≃ₗ F_x` undoes the trivializing germ.** -/
theorem tensorStalkLeftEquiv_tensorStalkTmul (hm : IsStalkBasis L x m)
    (n : F.presheaf.stalk x) :
    tensorStalkLeftEquiv F hm (tensorStalkTmul L F x m n) = n := by
  change (TensorProduct.lid ↑(X.presheaf.stalk x) ↑(F.presheaf.stalk x))
      (TensorProduct.congr hm.coord
        (LinearEquiv.refl ↑(X.presheaf.stalk x) ↑(F.presheaf.stalk x))
        (tensorStalkEquiv L F x (tensorStalkTmul L F x m n))) = _
  rw [tensorStalkEquiv_tensorStalkTmul, TensorProduct.congr_tmul, TensorProduct.lid_tmul,
    hm.coord_self, one_smul]
  rfl

/-- The inverse of `(L ⊗ F)_x ≃ₗ F_x` multiplies by the stalk basis. -/
theorem tensorStalkLeftEquiv_symm_apply (hm : IsStalkBasis L x m) (n : F.presheaf.stalk x) :
    (tensorStalkLeftEquiv F hm).symm n = tensorStalkTmul L F x m n :=
  ((tensorStalkLeftEquiv F hm).eq_symm_apply.2
    (tensorStalkLeftEquiv_tensorStalkTmul F hm n)).symm

/-- **`(F ⊗ L)_x ≃ₗ F_x` for an invertible `L`.** -/
theorem nonempty_tensorStalkRightEquiv (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (x : X) :
    Nonempty ((Scheme.Modules.tensorObj F L).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      F.presheaf.stalk x) := by
  obtain ⟨_, _, _, he⟩ := exists_germ_isStalkBasis L x
  exact ⟨tensorStalkRightEquiv F he⟩

/-- **`(L ⊗ F)_x ≃ₗ F_x` for an invertible `L`.** -/
theorem nonempty_tensorStalkLeftEquiv (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (x : X) :
    Nonempty ((Scheme.Modules.tensorObj L F).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      F.presheaf.stalk x) := by
  obtain ⟨_, _, _, he⟩ := exists_germ_isStalkBasis L x
  exact ⟨tensorStalkLeftEquiv F he⟩

end Stacks.InvertibleStalk

end
