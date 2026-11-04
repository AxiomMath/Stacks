module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.RingTheory.Ideal.Colon
public import StacksFrontier.AlgebraicGeometry.CardinalGeneratedColimit.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.IdealPowerMultiple

/-!
# The subsheaf `I ^ n • F` of a quasi-coherent module

Let `X` be a scheme, `I` a quasi-coherent sheaf of ideals on `X` given by its affine-local ideal
data, `n : ℕ` and `F` a quasi-coherent sheaf of modules on `X`. This file constructs the
quasi-coherent subsheaf `I ^ n • F` of `F` whose sections over an *affine* open `U` are exactly
`I(U) ^ n • Γ(F, U)`, which is the subsheaf the proofs of [Stacks, Tag 01YD] and
[Stacks, Tag 01YF] filter by.

The construction is the passage from a compatible affine-local family of submodules to a
subsheaf, `Stacks.AlgebraicGeometry.GabberColimit.sheafSubmodule`, so the computation of its
sections over an affine open and its quasi-coherence are both inherited. All that has to be
proved here is that the family `U ↦ I(U) ^ n • Γ(F, U)` is compatible, which is
`AlgebraicGeometry.Scheme.IdealSheafData.map_ideal` together with the surjectivity half of
[Stacks, Tag 01I9].

## Main definitions

* `Stacks.AlgebraicGeometry.IdealPowerSmul.idealPowFamily`: the affine-local family
  `U ↦ I(U) ^ n • Γ(F, U)`.
* `Stacks.AlgebraicGeometry.IdealPowerSmul.idealPowSmul`: the subsheaf `I ^ n • F` of `F`.

## Main results

* `Stacks.AlgebraicGeometry.IdealPowerSmul.isCompatible_idealPowFamily`: the family is compatible.
* `Stacks.AlgebraicGeometry.IdealPowerSmul.obj_idealPowSmul`: the sections of `I ^ n • F` over an
  affine open `U` are `I(U) ^ n • Γ(F, U)`.
* `Stacks.AlgebraicGeometry.IdealPowerSmul.isQuasicoherent_idealPowSmul`: `I ^ n • F` is
  quasi-coherent.
* `Stacks.AlgebraicGeometry.IdealPowerSmul.idealPowSmul_mono_left`: `I ^ n • F` is monotone in the
  ideal `I`.
* `Stacks.AlgebraicGeometry.IdealPowerSmul.idealPowFamily_eq_top`: on an affine open where `I` is
  the unit ideal the family is everything.
* `Stacks.AlgebraicGeometry.IdealPowerSmul.localSections_idealPowFamily_eq_top`: if `I` is the unit
  ideal on every affine open contained in `V`, then `I ^ n • F` and `F` have the same sections
  over `V`.

## Implementation notes

This is not `Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple` of
`StacksFrontier/AlgebraicGeometry/Modules/IdealPowerMultiple.lean`, which is defined as the
infimum of all subsheaves dominating the affine-local data. That definition needs no
quasi-coherence, but it also does not determine the sections over an affine open, which is the
only handle the support computations of [Stacks, Tag 01YD] have. The two agree for
quasi-coherent `F`, but the comparison is not needed anywhere below and is not proved.

The compatibility condition is an equality of submodules of `Γ(F, W)` for nested affine opens
`W ≤ U`. The inclusion of the restriction of `I(U) ^ n • Γ(F, U)` is
`AlgebraicGeometry.Scheme.Modules.map_smul` plus `Ideal.mem_map_of_mem`; the reverse inclusion
uses that `Γ(F, W)` is generated over `Γ(X, W)` by the restrictions of `Γ(F, U)`, which is
`Stacks.AlgebraicGeometry.GabberColimit.span_range_restrict_eq_top`, and is organised through
the colon ideal so that the induction over `Ideal.map` is `Ideal.map_le_iff_le_comap`.

## References

* [Stacks Project, Tag 01YD](https://stacks.math.columbia.edu/tag/01YD)
* [Stacks Project, Tag 01YF](https://stacks.math.columbia.edu/tag/01YF)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.GabberColimit

universe u

namespace Stacks.AlgebraicGeometry.IdealPowerSmul

variable {X : Scheme.{u}}

/-! ### The affine-local family -/

/-- The affine-local family `U ↦ I(U) ^ n • Γ(F, U)` of submodules of the sections of `F`. -/
def idealPowFamily (I : X.IdealSheafData) (n : ℕ) (F : X.Modules) :
    ∀ U : X.affineOpens, Submodule Γ(X, U.1) Γ(F, U.1) :=
  fun U ↦ I.ideal U ^ n • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1))

/-- Unfolds the family at an affine open `U`. -/
private theorem idealPowFamily_apply (I : X.IdealSheafData) (n : ℕ) (F : X.Modules)
    (U : X.affineOpens) :
    idealPowFamily I n F U = I.ideal U ^ n • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1)) := rfl

/-- **The family `U ↦ I(U) ^ n • Γ(F, U)` is compatible.** For nested affine opens `W ≤ U` the
submodule attached to `W` is generated over `Γ(X, W)` by the restrictions of the sections of the
submodule attached to `U`. -/
theorem isCompatible_idealPowFamily (I : X.IdealSheafData) (n : ℕ) (F : X.Modules)
    [F.IsQuasicoherent] : IsCompatible F (idealPowFamily I n F) := by
  intro U W h
  have hmap : Ideal.map (X.presheaf.map (homOfLE h).op).hom (I.ideal U ^ n) = I.ideal W ^ n := by
    rw [Ideal.map_pow]
    exact congrArg (· ^ n) (I.map_ideal h)
  set T : Submodule Γ(X, W.1) Γ(F, W.1) := Submodule.span Γ(X, W.1)
    (F.presheaf.map (homOfLE h).op '' (idealPowFamily I n F U : Set Γ(F, U.1))) with hT
  refine le_antisymm ?_ ?_
  · -- `I(W) ^ n • Γ(F, W) ≤ T`, via the colon ideal of `T`.
    have key : Ideal.map (X.presheaf.map (homOfLE h).op).hom (I.ideal U ^ n) ≤
        T.colon (Set.univ : Set Γ(F, W.1)) := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, Submodule.mem_colon]
      intro y _
      have hspan : (⊤ : Submodule Γ(X, W.1) Γ(F, W.1)) ≤
          T.comap (LinearMap.lsmul Γ(X, W.1) Γ(F, W.1)
            ((X.presheaf.map (homOfLE h).op).hom a)) := by
        rw [← span_range_restrict_eq_top F U.2 W.2 h, Submodule.span_le]
        rintro - ⟨m, rfl⟩
        refine Submodule.mem_comap.mpr ?_
        rw [LinearMap.lsmul_apply,
          show ((X.presheaf.map (homOfLE h).op).hom a) • F.presheaf.map (homOfLE h).op m =
            F.presheaf.map (homOfLE h).op (a • m) from (F.map_smul (homOfLE h) a m).symm]
        exact Submodule.subset_span ⟨a • m, Submodule.smul_mem_smul ha Submodule.mem_top, rfl⟩
      exact hspan Submodule.mem_top
    rw [idealPowFamily_apply, ← hmap]
    refine Submodule.smul_le.mpr fun a ha y _ ↦ ?_
    exact Submodule.mem_colon.mp (key ha) y (Set.mem_univ y)
  · -- `T ≤ I(W) ^ n • Γ(F, W)`, since restriction maps `I(U) ^ n` into `I(W) ^ n`.
    rw [hT, Submodule.span_le]
    rintro - ⟨m, hm, rfl⟩
    refine Submodule.smul_induction_on hm ?_ ?_
    · intro a ha x _
      rw [F.map_smul (homOfLE h) a x]
      refine Submodule.smul_mem_smul ?_ Submodule.mem_top
      rw [← hmap]
      exact Ideal.mem_map_of_mem _ ha
    · intro x y hx hy
      rw [show F.presheaf.map (homOfLE h).op (x + y) =
        F.presheaf.map (homOfLE h).op x + F.presheaf.map (homOfLE h).op y from
          map_add (F.presheaf.map (homOfLE h).op).hom x y]
      exact Submodule.add_mem _ hx hy

/-! ### The subsheaf -/

/-- **The subsheaf `I ^ n • F` of a quasi-coherent module `F`.** Its sections over an affine
open `U` are `I(U) ^ n • Γ(F, U)`; see `obj_idealPowSmul`. -/
def idealPowSmul (I : X.IdealSheafData) (n : ℕ) (F : X.Modules) [F.IsQuasicoherent] :
    F.Submodule :=
  sheafSubmodule F (idealPowFamily I n F) (isCompatible_idealPowFamily I n F)

/-- The sections of `I ^ n • F` over an affine open `U` are `I(U) ^ n • Γ(F, U)`. -/
theorem obj_idealPowSmul (I : X.IdealSheafData) (n : ℕ) (F : X.Modules) [F.IsQuasicoherent]
    (U : X.affineOpens) :
    (idealPowSmul I n F).toSubmodule.obj (op U.1) =
      I.ideal U ^ n • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1)) :=
  obj_sheafSubmodule F (idealPowFamily I n F) (isCompatible_idealPowFamily I n F) U

/-- `I ^ n • F` is quasi-coherent. -/
theorem isQuasicoherent_idealPowSmul (I : X.IdealSheafData) (n : ℕ) (F : X.Modules)
    [F.IsQuasicoherent] : (idealPowSmul I n F).toSheafOfModules.IsQuasicoherent :=
  isQuasicoherent_sheafSubmodule F (idealPowFamily I n F) (isCompatible_idealPowFamily I n F)

/-- **`I ^ n • F` is monotone in the ideal.** A section lies in `I ^ n • F` exactly when each of
its restrictions to an affine open `W` lies in `I(W) ^ n • Γ(F, W)`, and that submodule grows
with `I`, the order on `X.IdealSheafData` being affine-local inclusion of ideals. -/
theorem idealPowSmul_mono_left {I J : X.IdealSheafData} (h : I ≤ J) (n : ℕ) (F : X.Modules)
    [F.IsQuasicoherent] : idealPowSmul I n F ≤ idealPowSmul J n F := by
  refine SheafOfModules.Submodule.le_iff.mpr (PresheafOfModules.Submodule.le_iff.mpr ?_)
  intro V s hs W hW
  exact Submodule.smul_mono_left
    (pow_le_pow_left' (Scheme.IdealSheafData.le_def.mp h W) n) (hs W hW)

/-! ### Where the ideal is the unit ideal -/

/-- On an affine open where `I` is the unit ideal, the family is all of the sections. -/
theorem idealPowFamily_eq_top (I : X.IdealSheafData) (n : ℕ) (F : X.Modules)
    {U : X.affineOpens} (hU : I.ideal U = ⊤) : idealPowFamily I n F U = ⊤ := by
  rw [idealPowFamily_apply, hU, Ideal.top_pow, Submodule.top_smul]

/-- **Where `I` is the unit ideal, `I ^ n • F` has all the sections of `F`.** If `I` is the unit
ideal on every affine open contained in `V`, then every section of `F` over `V` lies locally in
the family, i.e. is a section of `I ^ n • F`. -/
theorem localSections_idealPowFamily_eq_top (I : X.IdealSheafData) (n : ℕ) (F : X.Modules)
    {V : X.Opens} (hV : ∀ W : X.affineOpens, W.1 ≤ V → I.ideal W = ⊤) :
    localSections F (idealPowFamily I n F) V = ⊤ :=
  top_unique fun s _ W hW ↦ by
    rw [idealPowFamily_eq_top I n F (hV W hW)]
    exact Submodule.mem_top

end Stacks.AlgebraicGeometry.IdealPowerSmul

end
