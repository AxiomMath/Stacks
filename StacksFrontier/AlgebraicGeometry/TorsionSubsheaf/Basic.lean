module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Modules.Stalk

/-!
# The torsion subsheaf of a module on an integral scheme

Let `X` be an integral scheme and let `F` be an `𝒪_X`-module. A local section of `F` is
*torsion* if its germ at every point of its domain is annihilated by a nonzero element of the
local ring there. This file constructs the submodule sheaf `torsionSubsheaf F` of `F` whose
sections over an open `U` are exactly the torsion sections of `F` over `U`, and identifies it
with the supremum `torsionSubmodule F` of all submodule sheaves of `F` all of whose sections
are torsion.

The construction is elementary: because the local rings of an integral scheme are domains (an
instance of Mathlib's `AlgebraicGeometry.Scheme.FunctionField` file), the
torsion sections over a fixed open form a submodule of the sections of `F`, and the torsion
condition is stable under restriction (germs are unchanged) and local (a germ at a point of `U`
only sees a neighbourhood of that point, and a covering sieve of `U` provides one). Hence the
family of submodules of torsion sections is a `SheafOfModules.Submodule`, and it is both a
member of the above family of submodule sheaves and an upper bound for it, so it is the
supremum.

The identification with the supremum is what makes the supremum computable on sections: in
Mathlib the complete lattice structure on `SheafOfModules.Submodule` is obtained from its
infima, so `sSup` carries no sections description a priori, whereas `sInf` and `iInf` do.

## Main definitions

* `IsTorsionElement`: an element of a module annihilated by a nonzero scalar.
* `IsTorsionSection F s`: all germs of the local section `s` of `F` are torsion elements.
* `torsionSections F U`: the submodule of `Γ(F, U)` of torsion sections.
* `torsionSubsheaf F`: the submodule sheaf of `F` of torsion sections.
* `torsionSubmodule F`: the supremum of all submodule sheaves of `F` whose sections are all
  torsion.

## Main results

* `mem_torsionSubsheaf_iff`, `torsionSubmodule_eq_torsionSubsheaf` and
  `mem_torsionSubmodule_iff`: the sections of `torsionSubsheaf F`, resp. of `torsionSubmodule F`,
  over an open are precisely the torsion sections there.

## Implementation notes

The module structure on the stalk of an `𝒪_X`-module over the local ring is
`AlgebraicGeometry.Scheme.Modules.moduleStalkPresheaf`, imported from
`StacksFrontier.AlgebraicGeometry.Modules.Stalk`; it only repackages Mathlib's module structure on
the stalk of a presheaf of modules so that instance search finds it for `X.Modules`, where the
structure presheaf appears as `X.ringCatSheaf.obj` rather than as `X.presheaf ⋙ forget₂ _ _`.

This file covers the first assertion of [Stacks, Tag 0AXT] only at the level of the
construction of the subsheaf and of the description of its sections; the quasi-coherence of
the torsion subsheaf, and the torsion freeness of the quotient, are not formalized here, and
therefore no stacks attribute for that tag is attached to any declaration below.

## References

* [Stacks Project, Tag 0AXT](https://stacks.math.columbia.edu/tag/0AXT)
* [Stacks Project, Tag 0AVR](https://stacks.math.columbia.edu/tag/0AVR)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.TorsionSubsheaf

variable {X : Scheme.{u}}

/-- An element `m` of a module over a commutative ring is a *torsion element* if it is
annihilated by a nonzero scalar. -/
def IsTorsionElement {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (m : M) : Prop :=
  ∃ r : R, r ≠ 0 ∧ r • m = 0

/-- Taking germs is semilinear: the germ of `r • s` is the germ of `r` acting on the germ
of `s`. -/
lemma germ_smul (F : X.Modules) {U : X.Opens} (x : X) (hx : x ∈ U) (r : Γ(X, U)) (s : Γ(F, U)) :
    F.presheaf.germ U x hx (r • s) = X.presheaf.germ U x hx r • F.presheaf.germ U x hx s :=
  PresheafOfModules.germ_smul (R := X.presheaf) F.val x U hx r s

/-- A local section of a quasi-coherent module on an integral scheme is *torsion* if its germ
at every point of its domain is a torsion element over the local ring there. This is
condition (2) of [Stacks, Tag 0AXR] and the notion of [Stacks, Tag 0AVR]. -/
@[ega "I 7.4.1" "partial"]
def IsTorsionSection [IsIntegral X] (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens}
    (s : Γ(F, U)) : Prop :=
  ∀ (x : X) (hx : x ∈ U), IsTorsionElement (R := X.presheaf.stalk x)
    (M := F.presheaf.stalk x) (F.presheaf.germ U x hx s)

/-- The torsion sections of `F` over an open `U` form a `Γ(X, U)`-submodule of `Γ(F, U)`: the
product of two nonzero annihilators is a nonzero annihilator of the sum because the local rings
of an integral scheme are domains. -/
noncomputable def torsionSections [IsIntegral X] (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) : Submodule Γ(X, U) Γ(F, U) where
  carrier := {s | IsTorsionSection F s}
  add_mem' := by
    rintro s t hs ht x hx
    obtain ⟨r, hr, hrs⟩ := hs x hx
    obtain ⟨r', hr', hr't⟩ := ht x hx
    refine ⟨r * r', mul_ne_zero hr hr', ?_⟩
    have h1 : (r * r') • F.presheaf.germ U x hx s = 0 := by
      rw [mul_comm, mul_smul, hrs, smul_zero]
    have h2 : (r * r') • F.presheaf.germ U x hx t = 0 := by rw [mul_smul, hr't, smul_zero]
    rw [map_add, smul_add, h1, h2, add_zero]
  zero_mem' := fun x _ => ⟨1, one_ne_zero, by simp⟩
  smul_mem' := by
    rintro c s hs x hx
    obtain ⟨r, hr, hrs⟩ := hs x hx
    exact ⟨r, hr, by rw [germ_smul F x hx c s, smul_comm, hrs, smul_zero]⟩

/-- A section of `F` over `U` lies in `torsionSections F U` exactly when it is a torsion
section. -/
@[simp]
lemma mem_torsionSections_iff [IsIntegral X] (F : X.Modules) [F.IsQuasicoherent]
    {U : X.Opens} (s : Γ(F, U)) :
    s ∈ torsionSections F U ↔ IsTorsionSection F s :=
  Iff.rfl

/-- The torsion sections of `F`, as a submodule of the underlying presheaf of modules of `F`:
restricting a section does not change its germs, so torsion sections restrict to torsion
sections. -/
noncomputable def torsionPresheafSubmodule [IsIntegral X] (F : X.Modules)
    [F.IsQuasicoherent] : F.val.Submodule where
  obj U := torsionSections F U.unop
  map {_ Z} f := by
    rintro s hs x hx
    change IsTorsionElement (F.presheaf.germ Z.unop x hx (F.presheaf.map f s))
    rw [TopCat.Presheaf.germ_res_apply' F.presheaf f x hx s]
    exact hs x (f.unop.le hx)

/-- **The torsion sections of `F` form a submodule sheaf of `F`.** Being torsion is a local
condition: a germ at a point `x` of `U` is computed on any neighbourhood of `x` inside `U`, and
a sieve covering `U` contains one. -/
noncomputable def torsionSubsheaf [IsIntegral X] (F : X.Modules) [F.IsQuasicoherent] :
    F.Submodule where
  toSubmodule := torsionPresheafSubmodule F
  isSheaf {Y} s hs := by
    intro x hx
    obtain ⟨V, f, hf, hxV⟩ := hs x hx
    have key : F.presheaf.germ V x hxV
        ((F.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat).map f.op s) =
        F.presheaf.germ Y.unop x hx s :=
      TopCat.Presheaf.germ_res_apply F.presheaf f x hxV s
    rw [← key]
    exact hf x hxV

/-- The sections of the torsion subsheaf `torsionSubsheaf F` over an open `U` are precisely the
torsion sections of `F` over `U`. -/
@[simp]
lemma mem_torsionSubsheaf_iff [IsIntegral X] (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (s : Γ(F, U)) :
    s ∈ (torsionSubsheaf F).toSubmodule.obj (op U) ↔ IsTorsionSection F s :=
  Iff.rfl

/-- The largest submodule sheaf of `F` all of whose sections are torsion, defined as the
supremum of all of them. -/
noncomputable def torsionSubmodule [IsIntegral X] (F : X.Modules) [F.IsQuasicoherent] :
    F.Submodule :=
  letI : CompleteLattice F.Submodule :=
    SheafOfModules.Submodule.instCompleteLattice
  sSup {N | ∀ (U : X.Opens) (s : Γ(F, U)),
    s ∈ N.toSubmodule.obj (op U) → IsTorsionSection F s}

/-- The supremum of the submodule sheaves of `F` with torsion sections is the submodule sheaf
of torsion sections: the latter is both a member of that family and an upper bound for it. -/
theorem torsionSubmodule_eq_torsionSubsheaf [IsIntegral X] (F : X.Modules)
    [F.IsQuasicoherent] : torsionSubmodule F = torsionSubsheaf F := by
  let _ : CompleteLattice F.Submodule :=
    SheafOfModules.Submodule.instCompleteLattice
  refine le_antisymm (sSup_le ?_) (le_sSup ?_)
  · exact fun N hN =>
      SheafOfModules.Submodule.le_iff.mpr fun Y _ hs => hN Y.unop _ hs
  · exact fun _ _ hs => hs

/-- **The sections of the torsion submodule sheaf are precisely the torsion sections.** This is
the sections description of [Stacks, Tag 0AXT]'s torsion subsheaf `F_tors ⊆ F`. -/
theorem mem_torsionSubmodule_iff [IsIntegral X] (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (s : Γ(F, U)) :
    s ∈ (torsionSubmodule F).toSubmodule.obj (op U) ↔ IsTorsionSection F s := by
  rw [torsionSubmodule_eq_torsionSubsheaf]
  exact mem_torsionSubsheaf_iff F U s

end Stacks.AlgebraicGeometry.TorsionSubsheaf
