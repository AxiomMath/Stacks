module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.IdealPowerMultiple
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicInverseSystem.Sections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.QuotientRestriction
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CanonicalSectionsMap
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiSeparated.LocalizedRestriction

/-!
# The unit section of an ideal power off the support

Let `I` be a quasi-coherent ideal sheaf on a scheme `X`. Off the support of `I` the ideal is the
unit ideal, so every power `I ^ n` is too, and the constant section `1` is a section of the
subsheaf `I ^ n 𝒪_X` over any open disjoint from the support. This file records that section.

## Main definitions

* `Stacks.Algebraization.complementUnitLift` is the unit section of `I ^ n 𝒪_X` over an open
  contained in the open complement of the support of the ideal sheaf.

## Main results

* `Stacks.Algebraization.one_mem_idealPowerMultiple_of_le_idealComplement` — the unit lies in
  `I ^ n 𝒪_X` over any open disjoint from the support of `I`.

## Implementation notes

`Stacks.LocalCohomology.idealComplement I` is definitionally `I.support.compl`, and
`idealComplement_eq_support_compl` records the identification by `rfl`.

The sections of `I ^ n 𝒪_X` over an affine open are computed by
`idealPowerMultiple_toSubmodule_obj_affine`, and off the support they are everything by
`idealPowerMultiple_obj_eq_top_of_le_compl_support`; the passage from affine opens to an
arbitrary open is by the sheaf condition on the subsheaf.

Several statements here mention both `Γ(X, V)` and `Γ(SheafOfModules.unit X.ringCatSheaf, V)`,
which are definitionally equal and not syntactically equal. Elaboration crosses between them but
`rw` and `simp` cannot, so the steps that span the two are supplied as terms, and
`ideal_smul_top` is stated over an abstract ring so that unification absorbs the crossing at the
use site.

## References

* [Stacks Project, Tag 01PQ](https://stacks.math.columbia.edu/tag/01PQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

noncomputable section

/-- The complete lattice of subsheaves of a sheaf of modules on a scheme. -/
local instance {X : Scheme.{u}} {M : X.Modules} : CompleteLattice M.Submodule :=
  SheafOfModules.Submodule.instCompleteLattice

/-! ### Commutative algebra -/

/-- For an ideal `J` of a commutative ring `R`, `J • ⊤ = J` in the submodules of `R`. -/
private lemma ideal_smul_top {R : Type*} [CommRing R] (J : Ideal R) :
    J • (⊤ : Submodule R R) = J := by
  simp only [smul_eq_mul, Ideal.mul_top]

/-! ### The complement of the support -/

/-- `Stacks.LocalCohomology.idealComplement I` is the open complement of the support of `I`. -/
lemma idealComplement_eq_support_compl {X : Scheme.{u}} (I : X.IdealSheafData) :
    Stacks.LocalCohomology.idealComplement I = I.support.compl :=
  rfl

/-- The sections of `I ^ n 𝒪_X` over an affine open are the `n`-th power of the ideal there. -/
lemma idealPowerMultiple_unit_toSubmodule_obj_affine {X : Scheme.{u}} (I : X.IdealSheafData)
    (n : ℕ) (U : X.affineOpens) :
    (((idealPowerMultiple I n (SheafOfModules.unit X.ringCatSheaf)).toSubmodule.obj (op U.1) :
        Submodule Γ(X, U.1) Γ(X, U.1)))
      = I.ideal U ^ n :=
  (idealPowerMultiple_toSubmodule_obj_affine I n
    (SheafOfModules.unit X.ringCatSheaf) U).trans (ideal_smul_top _)

/-- On an open disjoint from the support of `I`, the ideal-power subsheaf contains the unit
section. -/
lemma one_mem_idealPowerMultiple_of_le_idealComplement
    {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ) (V : X.Opens)
    (hV : V ≤ Stacks.LocalCohomology.idealComplement I) :
    (1 : Γ(X, V)) ∈
      (idealPowerMultiple I n (SheafOfModules.unit X.ringCatSheaf)).toSubmodule.obj (op V) := by
  let P := idealPowerMultiple I n (SheafOfModules.unit X.ringCatSheaf)
  let R : Presieve V := fun W _ =>
    ∃ A : X.affineOpens, W = (A : X.Opens) ∧ (A : X.Opens) ≤ V
  have hcov : Sieve.generate R ∈ Opens.grothendieckTopology X V := by
    intro x hx
    obtain ⟨_, ⟨A, hA, rfl⟩, hxA, hAV⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx V.2
    exact ⟨A, homOfLE hAV, ⟨A, 𝟙 _, homOfLE hAV, ⟨(⟨A, hA⟩ : X.affineOpens), rfl, hAV⟩, by simp⟩,
      hxA⟩
  have hR : R ≤ P.toSubmodule.toSubfunctor.sieveOfSection (1 : Γ(X, V)) := by
    rintro W f ⟨A, rfl, hAV⟩
    exact (idealPowerMultiple_obj_eq_top_of_le_compl_support I n
      (SheafOfModules.unit X.ringCatSheaf) A (hAV.trans hV)).ge Submodule.mem_top
  exact P.isSheaf (1 : Γ(X, V))
    ((Opens.grothendieckTopology X).superset_covering ((Sieve.generate_le_iff R _).2 hR) hcov)

/-- The unit section of `I ^ n 𝒪_X` over an open disjoint from the support of `I`. -/
def complementUnitLift {X : Scheme.{u}}
    (I : X.IdealSheafData) (n : ℕ) (V : X.Opens)
    (hV : V ≤ Stacks.LocalCohomology.idealComplement I) :
    Γ((idealPowerMultiple I n (SheafOfModules.unit X.ringCatSheaf)).toSheafOfModules, V) :=
  ⟨(show Γ(SheafOfModules.unit X.ringCatSheaf, V) from (1 : Γ(X, V))),
    one_mem_idealPowerMultiple_of_le_idealComplement I n V hV⟩

/-- The unit section of `I ^ n 𝒪_X` is the unit section of `𝒪_X`. -/
lemma complementUnitLift_spec {X : Scheme.{u}}
    (I : X.IdealSheafData) (n : ℕ) (V : X.Opens)
    (hV : V ≤ Stacks.LocalCohomology.idealComplement I) :
    (((idealPowerMultiple I n (SheafOfModules.unit X.ringCatSheaf)).ι.val.app (op V)).hom
      (complementUnitLift I n V hV)) = (1 : Γ(X, V)) := by
  show (show Γ(SheafOfModules.unit X.ringCatSheaf, V) from
      (1 : Γ(X, V))) = _
  rfl

end

end Stacks.Algebraization

end
