module

public import StacksFrontier.AlgebraicGeometry.CohomologyZeroLinear.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.CohenMacaulay
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.RingedSpaceTrace
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.SyntomicFibres
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.CotangentSheafComparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.SmoothMorphisms.Basic

/-!
# Vanishing of `Ext` into the dualizing module from vanishing of cohomology

Let `X` be a proper Cohen--Macaulay scheme over a field `k`, equidimensional of dimension `d`,
with dualizing module `ω_X`. Serre duality ([Stacks, Tag 0FVZ], part (4)) identifies
`Ext^{d-i}_X(ℱ, ω_X)` with the `k`-dual of `H^i(X, ℱ)` for `ℱ` quasi-coherent. Since a
`k`-vector space vanishes exactly when its dual does, `Ext^{d-i}_X(ℱ, ω_X) = 0` if and only if
`H^i(X, ℱ) = 0`.

In degree `i = 0` the cohomology `H^0(X, ℱ)` is the group `Hom(𝒪_X, ℱ)`. For `X` smooth and
proper over `k` and `ℱ = Ω_{X/k}` this says: if `X` has no nonzero global `1`-forms, then
`Ext^d_X(Ω_{X/k}, ω_X) = 0`, and the same for any module isomorphic to `ω_X` in place of `ω_X`.

## Main results

* `Stacks.Duality.subsingleton_ext_dualizingModule_iff`:
  `Ext^n(ℱ, ω_X) = 0 ↔ H^i(X, ℱ) = 0` for `n + i = d`.
* `Stacks.Duality.subsingleton_cohomologyOverField_zero_iff`: `H^0(X, ℱ) = 0 ↔ Hom(𝒪_X, ℱ) = 0`.
* `Stacks.Duality.subsingleton_ext_relativeDifferentials_dualizingModule`:
  `Ext^d(Ω_{X/k}, ω_X) = 0` when `H^0(X, Ω_{X/k}) = 0`, for `X` smooth and proper over `k`.
* `Stacks.Duality.subsingleton_ext_relativeDifferentials_of_iso`: the same with `ω_X` replaced
  by an isomorphic module.

## References

* [Stacks Project, Tag 0FVZ](https://stacks.math.columbia.edu/tag/0FVZ)
-/

attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe v u

namespace Stacks.Duality

section Iso

variable {C : Type*} [Category.{v} C] [Abelian C] [HasExt.{u} C]

/-- `Ext^n(A, B)` and `Ext^n(A, B')` are in bijection along an isomorphism `B ≅ B'`, by
composition with the degree-zero classes of the isomorphism and of its inverse. -/
def extEquivOfIsoRight {A B B' : C} (e : B ≅ B') (n : ℕ) :
    Ext.{u} A B n ≃ Ext.{u} A B' n where
  toFun x := x.comp (Ext.mk₀ e.hom) (add_zero n)
  invFun x := x.comp (Ext.mk₀ e.inv) (add_zero n)
  left_inv x := by
    dsimp only
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, e.hom_inv_id, Ext.comp_mk₀_id]
  right_inv x := by
    dsimp only
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, e.inv_hom_id, Ext.comp_mk₀_id]

end Iso

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **`H^0(X, ℱ) = 0` if and only if `Hom(𝒪_X, ℱ) = 0`.** Degree-zero cohomology is the module of
global sections (`AlgebraicGeometry.cohomologyOverFieldZeroLinearIso`), and global sections are
the morphisms out of the structure sheaf (`AlgebraicGeometry.Scheme.Modules.unitHomEquivTop`). -/
theorem subsingleton_cohomologyOverField_zero_iff (F : X.Modules) :
    Subsingleton (cohomologyOverField k f F 0) ↔
      Subsingleton (SheafOfModules.unit X.ringCatSheaf ⟶ F) :=
  ((cohomologyOverFieldZeroLinearIso k f F).toLinearEquiv.toEquiv.trans
    (Scheme.Modules.unitHomEquivTop F)).subsingleton_congr

variable [IsProper f]

/-- **`Ext^n(ℱ, ω_X) = 0` if and only if `H^i(X, ℱ) = 0`, for `n + i = d`.** Let `X` be proper,
Cohen--Macaulay and equidimensional of dimension `d` over a field `k`, and `ℱ` quasi-coherent.
Serre duality (`Stacks.Duality.dualizingModuleExtEquivOfIsProper`) identifies `Ext^n(ℱ, ω_X)`
with the `k`-dual of `H^i(X, ℱ)`, and a `k`-vector space is zero exactly when its dual is. -/
theorem subsingleton_ext_dualizingModule_iff (hCM : AlgebraicGeometry.IsCohenMacaulay X)
    (hequi : TopologicalSpace.Equidimensional X) (d : ℕ) (hd : topologicalKrullDim X = d)
    (F : X.Modules) [F.IsQuasicoherent] (n i : ℕ) (hni : n + i = d) :
    Subsingleton (Ext.{u} F (dualizingModule f) n) ↔
      Subsingleton (cohomologyOverField k f F i) := by
  have h : ((d : ℤ) - i) = (n : ℤ) := by omega
  have e := (dualizingModuleExtEquivOfIsProper f hCM hequi d hd F i).toEquiv
  rw [h] at e
  exact (Ext.homEquiv.trans e).subsingleton_congr.trans (Module.subsingleton_dual_iff k)

/-- **`Ext^d(ℱ, ω_X) = 0` if and only if `Hom(𝒪_X, ℱ) = 0`**, for `X` proper, Cohen--Macaulay
and equidimensional of dimension `d` over a field and `ℱ` quasi-coherent: the case `i = 0` of
`Stacks.Duality.subsingleton_ext_dualizingModule_iff`. -/
theorem subsingleton_ext_dualizingModule_top_iff (hCM : AlgebraicGeometry.IsCohenMacaulay X)
    (hequi : TopologicalSpace.Equidimensional X) (d : ℕ) (hd : topologicalKrullDim X = d)
    (F : X.Modules) [F.IsQuasicoherent] :
    Subsingleton (Ext.{u} F (dualizingModule f) d) ↔
      Subsingleton (SheafOfModules.unit X.ringCatSheaf ⟶ F) :=
  (subsingleton_ext_dualizingModule_iff f hCM hequi d hd F d 0 (add_zero d)).trans
    (subsingleton_cohomologyOverField_zero_iff f F)

variable [AlgebraicGeometry.Smooth f]

/-- **`Ext^d(Ω_{X/k}, ω_X) = 0` when `X` has no nonzero global `1`-forms.** Let `X` be smooth and
proper over a field `k`, equidimensional of dimension `d`. If `H^0(X, Ω_{X/k}) = 0`, then
`Ext^d_X(Ω_{X/k}, ω_X) = 0`: it is dual to `H^0(X, Ω_{X/k})` by Serre duality. -/
theorem subsingleton_ext_relativeDifferentials_dualizingModule
    (hequi : TopologicalSpace.Equidimensional X) (d : ℕ) (hd : topologicalKrullDim X = d)
    (h0 : Subsingleton (SheafOfModules.unit X.ringCatSheaf ⟶ Scheme.Hom.relativeDifferentials f)) :
    Subsingleton (Ext.{u} (Scheme.Hom.relativeDifferentials f) (dualizingModule f) d) := by
  have := Scheme.Hom.isQuasicoherent_relativeDifferentials f
  exact (subsingleton_ext_dualizingModule_top_iff f
    (isCohenMacaulay_of_syntomic_over_field f (syntomic_of_smooth f)) hequi d hd _).2 h0

/-- **`Ext^d(Ω_{X/k}, M) = 0` for `M ≅ ω_X` when `X` has no nonzero global `1`-forms.** This is
`Stacks.Duality.subsingleton_ext_relativeDifferentials_dualizingModule` carried along the
isomorphism `M ≅ ω_X`; for instance `M = 𝒪_X` when `ω_X` is trivial. -/
theorem subsingleton_ext_relativeDifferentials_of_iso
    (hequi : TopologicalSpace.Equidimensional X) (d : ℕ) (hd : topologicalKrullDim X = d)
    (h0 : Subsingleton (SheafOfModules.unit X.ringCatSheaf ⟶ Scheme.Hom.relativeDifferentials f))
    {M : X.Modules} (e : M ≅ dualizingModule f) :
    Subsingleton (Ext.{u} (Scheme.Hom.relativeDifferentials f) M d) := by
  have := subsingleton_ext_relativeDifferentials_dualizingModule f hequi d hd h0
  exact (extEquivOfIsoRight e d).subsingleton

end Stacks.Duality

end
