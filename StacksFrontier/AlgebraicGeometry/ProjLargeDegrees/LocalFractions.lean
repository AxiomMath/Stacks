module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjModuleDegreeZeroFlat
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjShiftedSectionModule

/-!
# Global sections of `M(n)~` as fractions on a standard open

Let `S = ⨁_{d ≥ 0} 𝒮 d` be a graded ring, `M = ⨁_{i ∈ ℤ} 𝒨 i` a graded `S`-module and
`X = Proj 𝒮`. A global section of `M(n)~` restricts, on the standard open `D₊(f)` of a
homogeneous element `f` of positive degree `c`, to a *single* fraction `m / f ^ k` with `m`
homogeneous of degree `kc + n`: the sections of the associated sheaf over `D₊(f)` are the
degree-zero part of the localization away from `f`, and every element of that degree-zero part is
a homogeneous fraction.

This is the input of the "clearing denominators" argument: it is what turns the merely *local*
fraction representation built into the definition of the associated sheaf into one valid on a
whole standard open, so that a finite cover by standard opens gives finitely many numerators.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjLargeDegrees.sectionValue`: the value of a global section of
  `M(n)~` at a point of `Proj 𝒮`, an element of the localized module fiber there.

## Main results

* `Stacks.AlgebraicGeometry.ProjLargeDegrees.sectionValue_degreeNToGlobalSections`,
  `Stacks.AlgebraicGeometry.ProjLargeDegrees.sectionValue_homogeneousScalarGlobalSections`: the
  two formulas of [Stacks, Tag 0AG2] in terms of `sectionValue`.
* `Stacks.AlgebraicGeometry.ProjLargeDegrees.sectionValue_zero`: the zero section has value `0`
  everywhere.
* `Stacks.AlgebraicGeometry.ProjLargeDegrees.shiftedSectionsComponent_ext`: two global sections
  of `M(n)~` with the same value at every point are equal.
* `Stacks.AlgebraicGeometry.ProjLargeDegrees.exists_forall_sectionValue_eq_mk`: a global section
  of `M(n)~` is the fraction `m / f ^ k` at every point of `D₊(f)`.

## Implementation notes

`sectionValue` abbreviates
`((associatedModuleSheafSectionsEquiv 𝒮 (shiftedGrading 𝒨 n) ⊤).toFun s).1 ⟨y, trivial⟩`, the
spelling in which `Stacks.AlgebraicGeometry.ProjShiftedSections.degreeNToGlobalSections_apply`
and `Stacks.AlgebraicGeometry.ProjShiftedSections.homogeneousScalarGlobalSections_apply` state
their formulas. It is introduced only because the denominator-clearing computation of
`ClearDenominators.lean` is a chain of equalities between such values, and nothing in the tree
names them; `associatedModuleSheafSectionsEquiv` is the identity equivalence, so the two
formulas above are the definition read twice and need no proof.

## References

* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
* [Stacks Project, Tag 0AG2](https://stacks.math.columbia.edu/tag/0AG2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace DirectSum
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShiftedSections
  (shiftedSectionsComponent degreeNToGlobalSections degreeNToGlobalSections_apply
    homogeneousScalarGlobalSections homogeneousScalarGlobalSections_apply)
open Stacks.GradedModule (shiftedGrading)
open scoped Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjLargeDegrees

universe u v w t

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {S : Type u} {M : Type v} {σ : Type w} {τ : Type t}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]

/-- **The value of a global section of `M(n)~` at a point of `Proj 𝒮`**, an element of the
localized module fiber `M_{p}` there. Sections of the associated sheaf are exactly the families
of fiber elements that are locally homogeneous fractions, so this is a projection of the
section. -/
def sectionValue (n : ℤ) (s : shiftedSectionsComponent 𝒮 𝒨 n)
    (y : ProjectiveSpectrum.top 𝒮) : ModuleFiber (M := M) 𝒮 y :=
  ((associatedModuleSheafSectionsEquiv 𝒮 (shiftedGrading 𝒨 n) ⊤).toFun s).1 ⟨y, trivial⟩

omit [Decomposition 𝒨] in
/-- **The global section attached to a homogeneous element has value `m / 1` everywhere.** -/
theorem sectionValue_degreeNToGlobalSections (n : ℤ) (m : 𝒨 n)
    (y : ProjectiveSpectrum.top 𝒮) :
    sectionValue 𝒮 𝒨 n (degreeNToGlobalSections 𝒮 𝒨 n m) y =
      LocalizedModule.mk m.1 (1 : y.asHomogeneousIdeal.toIdeal.primeCompl) :=
  degreeNToGlobalSections_apply 𝒮 𝒨 n m y

omit [Decomposition 𝒨] in
/-- **A homogeneous scalar acts on a global section by multiplication in every fiber.** -/
theorem sectionValue_homogeneousScalarGlobalSections (i : ℕ) (n : ℤ) (a : 𝒮 i)
    (s : shiftedSectionsComponent 𝒮 𝒨 n) (y : ProjectiveSpectrum.top 𝒮) :
    sectionValue 𝒮 𝒨 ((i : ℤ) + n) (homogeneousScalarGlobalSections 𝒮 𝒨 i n a s) y =
      (a : S) • sectionValue 𝒮 𝒨 n s y :=
  homogeneousScalarGlobalSections_apply 𝒮 𝒨 i n a s ⟨y, trivial⟩

omit [Decomposition 𝒨] in
/-- **The zero global section has value `0` everywhere.** -/
theorem sectionValue_zero (n : ℤ) (y : ProjectiveSpectrum.top 𝒮) :
    sectionValue 𝒮 𝒨 n (0 : shiftedSectionsComponent 𝒮 𝒨 n) y = 0 := rfl

omit [Decomposition 𝒨] in
/-- **Two global sections of `M(n)~` with the same value at every point are equal.** Sections of
the associated sheaf are functions into the localized module fibers. -/
theorem shiftedSectionsComponent_ext {n : ℤ} {s t : shiftedSectionsComponent 𝒮 𝒨 n}
    (h : ∀ y : ProjectiveSpectrum.top 𝒮, sectionValue 𝒮 𝒨 n s y = sectionValue 𝒮 𝒨 n t y) :
    s = t := by
  refine (associatedModuleSheafSectionsEquiv 𝒮 (shiftedGrading 𝒨 n) ⊤).injective
    (Subtype.ext (funext fun y => ?_))
  exact h y.1

/-- **A global section of `M(n)~` is a single fraction on a standard open.** For `f` homogeneous
of positive degree `c` there are `k` and a homogeneous `m` of degree `kc + n` with
`s = m / f ^ k` at every point of `D₊(f)`: the sections over `D₊(f)` are the degree-zero part of
the localization away from `f`, by
`AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv`, and every
element of it is a homogeneous fraction, by
`AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeZeroFraction_surjective`. -/
theorem exists_forall_sectionValue_eq_mk {n : ℤ} (s : shiftedSectionsComponent 𝒮 𝒨 n)
    {f : S} {c : ℕ} (hf : f ∈ 𝒮 c) (hc : 0 < c) :
    ∃ (k : ℕ) (m : M), m ∈ 𝒨 ((k * c : ℕ) + n) ∧
      ∀ (y : ProjectiveSpectrum.top 𝒮) (hy : f ∈ y.asHomogeneousIdeal.toIdeal.primeCompl),
        sectionValue 𝒮 𝒨 n s y =
          LocalizedModule.mk m
            ⟨f ^ k, y.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem hy k⟩ := by
  obtain ⟨k, m, hm, hfrac⟩ := degreeZeroFraction_surjective 𝒮 (shiftedGrading 𝒨 n) hf
    (associatedModuleSheafStandardOpenEquiv 𝒮 (shiftedGrading 𝒨 n) hf hc
      ((associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 n)).val.map
        (homOfLE (le_top : ProjectiveSpectrum.basicOpen 𝒮 f ≤ ⊤)).op s))
  have hmdeg : m ∈ 𝒨 ((k * c : ℕ) + n) := by
    have hms : m ∈ shiftedGrading 𝒨 n (k • (c : ℤ)) := hm
    simpa only [shiftedGrading, nsmul_eq_mul, Nat.cast_mul] using hms
  refine ⟨k, m, hmdeg, fun y hy => ?_⟩
  have hyf : y ∈ ProjectiveSpectrum.basicOpen 𝒮 f := hy
  have hres : (associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 n)).val.map
      (homOfLE (le_top : ProjectiveSpectrum.basicOpen 𝒮 f ≤ ⊤)).op s =
        degreeZeroToSection 𝒮 (shiftedGrading 𝒨 n) f
          (degreeZeroFraction 𝒮 (shiftedGrading 𝒨 n) hf k m hm) := by
    rw [hfrac]
    exact ((associatedModuleSheafStandardOpenEquiv 𝒮 (shiftedGrading 𝒨 n) hf hc).symm_apply_apply
      _).symm
  have hval := congrArg (fun z => (associatedModuleSheafSectionsEquiv 𝒮 (shiftedGrading 𝒨 n)
    (ProjectiveSpectrum.basicOpen 𝒮 f) z).1 ⟨y, hyf⟩) hres
  refine Eq.trans ?_ (hval.trans ?_)
  · exact (associatedModuleSheaf_restrict_apply 𝒮 (shiftedGrading 𝒨 n)
      (homOfLE (le_top : ProjectiveSpectrum.basicOpen 𝒮 f ≤ ⊤)) s ⟨y, hyf⟩).symm
  · exact degreeZeroToSection_fraction 𝒮 (shiftedGrading 𝒨 n) hf k m hm ⟨y, hyf⟩

end Stacks.AlgebraicGeometry.ProjLargeDegrees

end
