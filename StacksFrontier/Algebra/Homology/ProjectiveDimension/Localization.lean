module

public import Mathlib.RingTheory.LocalProperties.ProjectiveDimension
public import StacksFrontier.Algebra.Homology.ProjectiveDimension.Defs
public import StacksFrontier.RingTheory.GlobalDimension.Defs
public import StacksCore.Tactic.StacksAttribute
public import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension

/-!
# Localization and bounds on projective and global dimension

Let `R` be a ring and `S ⊆ R` a multiplicative subset. Localization at `S` does not raise a
bound on the projective dimension of an `R`-module, nor on the global dimension of `R`.

## Main results

* `Module.projectiveDimension_localizedModule_le` (Stacks 00O8 (1)): if `M` has projective
  dimension `≤ n` over `R`, then `S⁻¹M` has projective dimension `≤ n` over `S⁻¹R`.
* `ringGlobalDimension_localization_le` (Stacks 00O8 (2)): if `R` has global dimension `≤ n`,
  then so does `S⁻¹R`.

## Implementation notes

Projective dimension is `Module.projectiveDimension` (Stacks 00O4) and global dimension is
`ringGlobalDimension` (Stacks 00O6). Part (1) is Mathlib's
`ModuleCat.projectiveDimension_le_projectiveDimension_of_isLocalizedModule`, which localizes into
`Shrink (LocalizedModule S M)`; the linear equivalence with `LocalizedModule S M` itself carries
the bound across (`ModuleCat.projectiveDimension_eq_of_linearEquiv`). Part (2) follows from (1) as
in the source, every `S⁻¹R`-module being its own localization (`isLocalizedModule_id`).

## References

* [Stacks Project, Tag 00O8](https://stacks.math.columbia.edu/tag/00O8)
-/

@[expose] public section

universe v u

open CategoryTheory

/-- **Stacks 00O8 (1).** Let `R` be a ring, `M` an `R`-module and `S ⊆ R` a multiplicative
subset. If `M` has projective dimension `≤ n`, then `S⁻¹M` has projective dimension `≤ n` over
`S⁻¹R`. Projective dimension is the library's `Module.projectiveDimension` (Stacks 00O4); the
module `M` lives in any universe in which `R` is small, the hypothesis under which that invariant
is the source's minimal length of a projective resolution (00O5, 0CXC). The localization `S⁻¹M`
is `LocalizedModule S M` itself, in its own universe. -/
@[stacks 00O8 "(1)"]
theorem Module.projectiveDimension_localizedModule_le {R : Type u} [CommRing R] [Small.{v} R]
    (S : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ)
    (hM : Module.projectiveDimension R M ≤ n) :
    Module.projectiveDimension (Localization S) (LocalizedModule S M) ≤ n := by
  have : Small.{v} (Localization S) := small_of_surjective Localization.mkHom_surjective
  have : Small.{max u v} (Localization S) := small_of_surjective Localization.mkHom_surjective
  have : Small.{v} (LocalizedModule S M) :=
    small_of_surjective (IsLocalizedModule.mk'_surjective S (LocalizedModule.mkLinearMap S M))
  calc Module.projectiveDimension (Localization S) (LocalizedModule S M)
      = CategoryTheory.projectiveDimension ((ModuleCat.of R M).localizedModule S) :=
        ModuleCat.projectiveDimension_eq_of_linearEquiv.{max u v, v}
          (M := ModuleCat.of (Localization S) (LocalizedModule S M))
          (N := (ModuleCat.of R M).localizedModule S)
          (Shrink.linearEquiv.{v} (Localization S) (LocalizedModule S M)).symm
    _ ≤ CategoryTheory.projectiveDimension (ModuleCat.of R M) :=
        ModuleCat.projectiveDimension_le_projectiveDimension_of_isLocalizedModule S _
    _ ≤ n := hM

/-- **Stacks 00O8 (2).** Let `R` be a ring and `S ⊆ R` a multiplicative subset. If `R` has
finite global dimension `≤ n`, then so does `S⁻¹R`. Global dimension is the library's
`ringGlobalDimension` (Stacks 00O6), the supremum of the projective dimensions of all modules,
which is `≤ n` exactly when every module has a projective resolution of length `≤ n`. The proof
is the source's: every `S⁻¹R`-module `M'` is its own localization `S⁻¹M'`, so (1) applies. -/
@[stacks 00O8 "(2)"]
theorem ringGlobalDimension_localization_le {R : Type u} [CommRing R] (S : Submonoid R) (n : ℕ)
    (hR : ringGlobalDimension R ≤ n) : ringGlobalDimension (Localization S) ≤ n := by
  refine iSup_le fun X => ?_
  let M' := (X : Type u)
  let : Module R M' := Module.compHom M' (algebraMap R (Localization S))
  have : IsScalarTower R (Localization S) M' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsLocalizedModule S (LinearMap.id : M' →ₗ[R] M') :=
    isLocalizedModule_id S M' (Localization S)
  have h := Module.projectiveDimension_localizedModule_le S M' n
    (le_trans (le_iSup (fun N : ModuleCat.{u} R => projectiveDimension N) (ModuleCat.of R M')) hR)
  rwa [Module.projectiveDimension, ModuleCat.projectiveDimension_eq_of_linearEquiv.{u, u}
    (M := ModuleCat.of (Localization S) (LocalizedModule S M')) (N := X)
    (LinearEquiv.extendScalarsOfIsLocalization S (Localization S)
      (IsLocalizedModule.iso S (LinearMap.id : M' →ₗ[R] M')))] at h

end
