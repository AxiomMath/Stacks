module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.FittingSupport
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.RetrocompactOpen
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.SupportedSerreQuotient

/-!
# The support of a sheaf of modules and the quasi-compactness of its complement

The support of a sheaf of modules on a scheme is the set of points at which its stalk is
nonzero.  This file gives that set the spelling `AlgebraicGeometry.IsSupportedOn` and
`AlgebraicGeometry.quasicoherentSupportedOn` use, records that it is closed for a module of
finite type, names its open complement, and proves that on a quasi-compact scheme the complement
of the support of a finitely presented quasi-coherent module is again quasi-compact.

That last statement is **step 4** of [Stacks, Tag 0GPJ].  The support is the vanishing locus of
the zeroth Fitting ideal ([Stacks, Tag 0CYX]), that ideal sheaf is of finite type
([Stacks, Tag 0C3E]), and the complement of the vanishing locus of a finite type quasi-coherent
sheaf of ideals on a quasi-compact scheme is quasi-compact ([Stacks, Tag 01PH], (4) implies (2)).

## Main definitions

* `AlgebraicGeometry.supportSet` — the set of points at which the stalk of a sheaf of modules is
  nonzero, in the spelling `AlgebraicGeometry.IsSupportedOn` uses.
* `AlgebraicGeometry.supportComplement` — its open complement, for a module of finite type.

## Main results

* `AlgebraicGeometry.isClosed_supportSet` — the support of a module of finite type is closed.
* `AlgebraicGeometry.isCompact_compl_supportSet` — **step 4 of [Stacks, Tag 0GPJ]**.

## References

* [Stacks Project, Proposition 56.6.6 (Tag 0GPJ)](https://stacks.math.columbia.edu/tag/0GPJ)
* [Stacks Project, Lemma 28.25.1 (Tag 01PH)](https://stacks.math.columbia.edu/tag/01PH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### The support of a sheaf of modules and its complement -/

section Support

variable {X : Scheme.{u}}

/-- **The support of a sheaf of modules**, as the set of points at which the stalk of the
underlying sheaf of abelian groups is nonzero.  This is the subset
`AlgebraicGeometry.IsSupportedOn` compares with: `IsSupportedOn E F` is support containment of
`E` in `supportSet F`, and `AlgebraicGeometry.quasicoherentSupportedOn X (supportSet F)` is the
Serre subcategory of quasi-coherent modules supported there. -/
def supportSet (M : X.Modules) : Set X :=
  {x : X | ∃ a : ((Scheme.Modules.toPresheaf X).obj M).stalk x, a ≠ 0}

/-- Support containment in the support of `F` is membership in the Serre subcategory of modules
supported on `AlgebraicGeometry.supportSet F`.  Both sides are the same term. -/
theorem quasicoherentSupportedOn_supportSet (F : X.Modules)
    (E : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    quasicoherentSupportedOn X (supportSet F) E ↔ IsSupportedOn E.obj F :=
  Iff.rfl

/-- `AlgebraicGeometry.supportSet` is `SheafOfModules.supp` of the underlying sheaf of abelian
groups.  Both sides are the same term; the two spellings exist because `SheafOfModules.supp` is
stated for a sheaf of modules on a topological space while `AlgebraicGeometry.IsSupportedOn` is
stated with `AlgebraicGeometry.Scheme.Modules.toPresheaf`. -/
theorem supportSet_eq_supp (M : X.Modules) : supportSet M = SheafOfModules.supp M := rfl

/-- **The support of a module of finite type is closed.**  This is `SheafOfModules.isClosed_supp`,
[Stacks, Tag 01BA], read through `AlgebraicGeometry.supportSet`. -/
theorem isClosed_supportSet (M : X.Modules) [M.IsFiniteType] : IsClosed (supportSet M) :=
  supportSet_eq_supp M ▸ SheafOfModules.isClosed_supp M

/-- **The open complement of the support of a module of finite type.** -/
def supportComplement (M : X.Modules) [M.IsFiniteType] : X.Opens :=
  ⟨(supportSet M)ᶜ, (isClosed_supportSet M).isOpen_compl⟩

/-- The underlying set of `AlgebraicGeometry.supportComplement` is the complement of the
support. -/
@[simp] theorem coe_supportComplement (M : X.Modules) [M.IsFiniteType] :
    (supportComplement M : Set X) = (supportSet M)ᶜ := rfl

/-- **Step 4 of [Stacks, Tag 0GPJ]: the complement of the support of a finitely presented
quasi-coherent module on a quasi-compact scheme is quasi-compact.**  The support is the vanishing
locus of the zeroth Fitting ideal ([Stacks, Tag 0CYX]), that ideal sheaf is of finite type
([Stacks, Tag 0C3E]), and the complement of the vanishing locus of a finite type quasi-coherent
sheaf of ideals on a quasi-compact scheme is quasi-compact ([Stacks, Tag 01PH], (4) ⟹ (2)). -/
theorem isCompact_compl_supportSet [CompactSpace X] (M : X.Modules) [M.IsQuasicoherent]
    [M.IsFinitePresentation] : IsCompact (supportSet M)ᶜ := by
  have hft : M.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation M
  have hcast : fittingIdealOfNat M 0 = fittingIdeal M 0 := by
    simp only [fittingIdealOfNat, Nat.cast_zero]
  have hI : Scheme.IdealSheafData.IsFiniteType (fittingIdeal M 0) :=
    hcast ▸ fittingIdeal_isFiniteType M 0
  refine isCompact_of_isFiniteType_idealSheafData (supportComplement M) (fittingIdeal M 0) hI ?_
  change ((fittingIdeal M 0).support : Set X) = ((supportSet M)ᶜ)ᶜ
  rw [compl_compl]
  exact (fittingIdeal_zero_support_eq_supp M).trans (supportSet_eq_supp M).symm

end Support

end AlgebraicGeometry

end
