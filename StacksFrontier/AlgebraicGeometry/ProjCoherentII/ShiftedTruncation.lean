module

public import StacksFrontier.AlgebraicGeometry.ProjCoherentII.GradedActionTruncation
public import StacksFrontier.AlgebraicGeometry.ProjCoherentII.Truncation

/-!
# The module `N'` of Tag 0B5R as an `S`-submodule

Let `S = ⨁_{d ≥ 0} 𝒮 d` be a nonnegatively graded ring, `M = ⨁_{n ∈ ℤ} 𝒨 n` a graded
`S`-module and `X = Proj 𝒮`. `Stacks.AlgebraicGeometry.ProjCoherentII.shiftedSectionsTruncation`
is the module

`N' = ⨁_{n ≥ k} Γ(X, M(n)~)`

of [Stacks, Tag 0B5R], cut out of `⨁_{n ∈ ℤ} Γ(X, M(n)~)` by the vanishing of the components in
degrees `< k`. It is defined there as an `AddSubgroup`, which is all that parts (3) and (4) of the
tag need: both are *maps into* `N'`, and additivity is enough to state them.

Part (1) is a statement about `N'` as an `S`-module, so `N'` has to be an `S`-submodule, and this
file is that upgrade. The scalar action is the graded one of Equation 01MR
(`Stacks.AlgebraicGeometry.ProjShiftedSections.GlobalSectionsModuleMap`), and the fact that makes
the upgrade go through is the same degree bookkeeping as on the twisted side: a homogeneous scalar
of degree `i ≥ 0` carries the degree-`n` summand into the degree-`i + n` summand, and
`i + n ≥ n ≥ k`.

That bookkeeping is not reproved here. It is
`Stacks.AlgebraicGeometry.ProjTwistedSections.gradedActionTruncation`, which was generalised off
the twisted global sections for this purpose: it asks only for a family of groups indexed by `ℤ`,
a module structure on their direct sum, and a degree-raising formula for the homogeneous scalars.
The only work left here is to put the action of Equation 01MR into that form.

## Main results

* `Stacks.AlgebraicGeometry.ProjShiftedSections.GlobalSectionsModuleMap.smul_of`: the
  degree-raising formula for the action of Equation 01MR, in the `DirectSum.of` form that
  `gradedActionTruncation` consumes. The bundled datum states its scalar formula *pointwise*, in
  the module fibres; this is that formula read on the direct sum.
* `Stacks.AlgebraicGeometry.ProjShiftedSections.GlobalSectionsModuleMap.truncation`: **`N'` as an
  `S`-submodule.**
* `Stacks.AlgebraicGeometry.ProjShiftedSections.GlobalSectionsModuleMap.toAddSubgroup_truncation`:
  its underlying additive subgroup is the `N'` of Tag 0B5R, so parts (3) and (4) are statements
  about this submodule.

## Implementation notes

`smul_of` is proved from the two fields `gradedSMul` and `smul_homogeneous` of the bundled datum
and from nothing else. `gradedSMul` says that `a • (degree n)` is homogeneous of degree `i + n`,
which is what makes `a • of n s` of the form `of (i + n) y` at all — the datum's pointwise
formula alone cannot say that, because it describes only the degree-`i + n` component.
`smul_homogeneous` then identifies `y` with the homogeneous action, in the fibres, and sections of
an associated sheaf are determined by their values there.

The degree `(i : ℕ) +ᵥ n` produced by `SetLike.GradedSMul.smul_mem` is `(i : ℤ) + n` by
definition of the `VAdd ℕ ℤ` instance that the graded action of an `ℕ`-graded ring on a
`ℤ`-graded module is stated through, so no transport appears.

## References

* [Stacks Project, Tag 0B5R](https://stacks.math.columbia.edu/tag/0B5R)
* [Stacks Project, Tag 01MR](https://stacks.math.columbia.edu/tag/01MR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace DirectSum
open AlgebraicGeometry.ProjectiveSpectrum.Proj (associatedModuleSheaf
  associatedModuleSheafSectionsEquiv)
open Stacks.GradedModule (shiftedGrading)
open scoped Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjShiftedSections

universe u w t

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj

variable {S : Type u} {M : Type u} {σ : Type w} {τ : Type t}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]

omit [DirectSum.Decomposition 𝒨] in
/-- **The degree-raising formula for the action of Equation 01MR, on the direct sum.** A
homogeneous scalar of degree `i` carries the degree-`n` summand of `⨁_{n ∈ ℤ} Γ(X, M(n)~)` to the
degree-`i + n` summand, by the homogeneous action
`Stacks.AlgebraicGeometry.ProjShiftedSections.homogeneousScalarGlobalSections`.

The bundled datum states its scalar formula pointwise in the module fibres; this is the same
formula read on the direct sum, which is the form the truncation needs. -/
public theorem GlobalSectionsModuleMap.smul_of (D : GlobalSectionsModuleMap 𝒮 𝒨) (i : ℕ) (n : ℤ)
    (a : 𝒮 i) (s : shiftedSectionsComponent 𝒮 𝒨 n) :
    letI := D.moduleInst
    (a : S) • (DirectSum.of (fun k : ℤ => shiftedSectionsComponent 𝒮 𝒨 k) n s :
        shiftedModuleGlobalSections 𝒮 𝒨) =
      DirectSum.of (fun k : ℤ => shiftedSectionsComponent 𝒮 𝒨 k) ((i : ℤ) + n)
        (homogeneousScalarGlobalSections 𝒮 𝒨 i n a s) := by
  let := D.moduleInst
  let := D.gradedSMul
  have hmem : (DirectSum.of (fun k : ℤ => shiftedSectionsComponent 𝒮 𝒨 k) n s :
      shiftedModuleGlobalSections 𝒮 𝒨) ∈ shiftedModuleGlobalSectionsGrading 𝒮 𝒨 n :=
    (DirectSum.mem_rangeGrading ℤ (fun k : ℤ => shiftedSectionsComponent 𝒮 𝒨 k) n _).mpr ⟨s, rfl⟩
  have hsm : ((a : S) • (DirectSum.of (fun k : ℤ => shiftedSectionsComponent 𝒮 𝒨 k) n s :
      shiftedModuleGlobalSections 𝒮 𝒨)) ∈
      shiftedModuleGlobalSectionsGrading 𝒮 𝒨 ((i : ℤ) + n) :=
    SetLike.GradedSMul.smul_mem (A := 𝒮) (B := shiftedModuleGlobalSectionsGrading 𝒮 𝒨) a.2 hmem
  obtain ⟨y, hy⟩ :=
    (DirectSum.mem_rangeGrading ℤ (fun k : ℤ => shiftedSectionsComponent 𝒮 𝒨 k)
      ((i : ℤ) + n) _).mp hsm
  rw [hy]
  refine congrArg (DirectSum.of (fun k : ℤ => shiftedSectionsComponent 𝒮 𝒨 k) ((i : ℤ) + n)) ?_
  refine (associatedModuleSheafSectionsEquiv 𝒮 (shiftedGrading 𝒨 ((i : ℤ) + n)) ⊤).injective ?_
  refine Subtype.ext (funext fun x => ?_)
  have hcomp : DirectSum.component ℤ ℤ (fun k : ℤ => shiftedSectionsComponent 𝒮 𝒨 k)
      ((i : ℤ) + n) ((a : S) • (DirectSum.of
        (fun k : ℤ => shiftedSectionsComponent 𝒮 𝒨 k) n s :
          shiftedModuleGlobalSections 𝒮 𝒨)) = y := by
    rw [hy, ← DirectSum.apply_eq_component, DirectSum.of_eq_same]
  have h := D.smul_homogeneous i n a s x
  rw [hcomp] at h
  exact h.trans (homogeneousScalarGlobalSections_apply 𝒮 𝒨 i n a s x).symm

/-- **The module `N' = ⨁_{n ≥ k} Γ(X, M(n)~)` of Tag 0B5R, as an `S`-submodule.** The scalar
action is the graded one of Equation 01MR; a homogeneous scalar of degree `i ≥ 0` cannot lower a
degree, so the vanishing of the components in degrees `< k` is preserved. -/
public def GlobalSectionsModuleMap.truncation (D : GlobalSectionsModuleMap 𝒮 𝒨) (k : ℤ) :
    @Submodule S (shiftedModuleGlobalSections 𝒮 𝒨) _ _ D.moduleInst :=
  letI := D.moduleInst
  ProjTwistedSections.gradedActionTruncation 𝒮 (homogeneousScalarGlobalSections 𝒮 𝒨)
    (D.smul_of 𝒮 𝒨) k

omit [DirectSum.Decomposition 𝒨] in
/-- Membership in the degree-`≥ k` truncation is the vanishing of all components in degrees
`< k`. -/
public theorem GlobalSectionsModuleMap.mem_truncation (D : GlobalSectionsModuleMap 𝒮 𝒨) (k : ℤ)
    (x : shiftedModuleGlobalSections 𝒮 𝒨) :
    x ∈ D.truncation 𝒮 𝒨 k ↔
      ∀ n : ℤ, n < k →
        DirectSum.component ℤ ℤ (fun j : ℤ => shiftedSectionsComponent 𝒮 𝒨 j) n x = 0 :=
  Iff.rfl

omit [DirectSum.Decomposition 𝒨] in
/-- **The `N'` of Tag 0B5R is the additive subgroup underlying this submodule.** Parts (3) and
(4) of the tag are stated against
`Stacks.AlgebraicGeometry.ProjCoherentII.shiftedSectionsTruncation`, and they are therefore
statements about this `S`-submodule; part (1) is the assertion that it is a finite `S`-module. -/
public theorem GlobalSectionsModuleMap.toAddSubgroup_truncation
    (D : GlobalSectionsModuleMap 𝒮 𝒨) (k : ℤ) :
    (D.truncation 𝒮 𝒨 k).toAddSubgroup = ProjCoherentII.shiftedSectionsTruncation 𝒮 𝒨 k :=
  rfl

end Stacks.AlgebraicGeometry.ProjShiftedSections

end
