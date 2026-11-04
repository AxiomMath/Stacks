module

public import StacksFrontier.AlgebraicGeometry.ProjCoherentII.Basic

/-!
# The degree-at-least-`k` truncation of the twisted global sections, as an `S`-submodule

Let `S = ⨁_{d ≥ 0} 𝒮 d` be a nonnegatively graded ring, `X = Proj 𝒮` and `ℱ` a sheaf of
`𝒪_X`-modules, and let `⨁_{n ∈ ℤ} Γ(X, ℱ(n))` carry the graded `S`-module structure of Tag 03GK.
For an integer `k` the sections whose components in degrees `< k` vanish form an `S`-submodule,
since a homogeneous scalar of degree `i ≥ 0` sends the degree-`n` summand to the degree-`i + n`
summand.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTwistedSections.twistedGlobalSectionsTruncation`: the module
  `⨁_{n ≥ k} Γ(X, ℱ(n))`, as a submodule of `⨁_{n ∈ ℤ} Γ(X, ℱ(n))` over `S`.
* `Stacks.AlgebraicGeometry.ProjTwistedSections.TwistedGlobalSectionsModule.truncation`: the same
  submodule for the canonical graded `S`-module structure.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistedSections.mem_twistedGlobalSectionsTruncation`: membership
  is the vanishing of all components in degrees `< k`.
* `Stacks.AlgebraicGeometry.ProjTwistedSections.twistedGlobalSectionsTruncation_eq_span`: the
  submodule is the `S`-span of the homogeneous sections of degree `≥ k`.
* `Stacks.AlgebraicGeometry.ProjTwistedSections.toAddSubgroup_twistedGlobalSectionsTruncation`:
  its underlying additive subgroup is the module `N` of Tag 0B5R.

## Implementation notes

The module structure and the formula for the homogeneous action are taken as an instance argument
and an explicit hypothesis rather than read off a bundled datum, so that each statement mentions
only the action it is about; `TwistedGlobalSectionsModule.truncation` instantiates them at the
canonical datum.

That a general scalar preserves the truncation is reduced to the homogeneous case by decomposing
the scalar, and the homogeneous case to the degree bookkeeping `n < k ≤ m ≤ i + m` by decomposing
the section; `Stacks.AlgebraicGeometry.ProjCoherentII.twistedSectionsTruncation` is cut out by the
same conditions, so the comparison with it is reflexivity.

## References

* [Stacks Project, Tag 03GK](https://stacks.math.columbia.edu/tag/03GK)
* [Stacks Project, Tag 0B5R](https://stacks.math.columbia.edu/tag/0B5R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace DirectSum
open AlgebraicGeometry.ProjectiveSpectrum.Proj
  (twistSheafOfModules twistedGlobalSections associatedModuleSheaf)
open scoped Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjTwistedSections

universe u w t

attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

variable (F : SheafOfModules.{u}
  ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
    (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮)))

/-! ### The truncation of an abstract graded action -/

/-- A nonzero component of a section whose components in degrees `< k` vanish has degree `≥ k`. -/
private theorem le_of_apply_ne_zero {k : ℤ} {x : twistedGlobalSections 𝒮 F}
    (hx : ∀ m : ℤ, m < k →
      DirectSum.component ℤ ℤ (fun j : ℤ => twistedSectionsComponent 𝒮 F j) m x = 0)
    {m : ℤ} (hm : x m ≠ 0) : k ≤ m := by
  by_contra hlt
  refine hm ?_
  have h0 := hx m (not_le.mp hlt)
  rwa [← DirectSum.apply_eq_component] at h0

/-- Scaling a twisted global section whose components in degrees `< k` vanish keeps them zero:
the scalar decomposes into homogeneous pieces, and a piece of degree `i` sends the degree-`m`
summand to the degree-`i + m` summand, where `n < k ≤ m ≤ i + m`. -/
theorem component_smul_eq_zero [Module S (twistedGlobalSections 𝒮 F)]
    (hsmul : ∀ (i : ℕ) (n : ℤ) (a : 𝒮 i) (s : twistedSectionsComponent 𝒮 F n),
      (a : S) • (DirectSum.of (fun m : ℤ => twistedSectionsComponent 𝒮 F m) n s :
          twistedGlobalSections 𝒮 F) =
        DirectSum.of (fun m : ℤ => twistedSectionsComponent 𝒮 F m) ((i : ℤ) + n)
          (homogeneousScalarTwistedSections 𝒮 F i n a s))
    (k : ℤ) (c : S) {x : twistedGlobalSections 𝒮 F}
    (hx : ∀ m : ℤ, m < k →
      DirectSum.component ℤ ℤ (fun j : ℤ => twistedSectionsComponent 𝒮 F j) m x = 0)
    (n : ℤ) (hn : n < k) :
    DirectSum.component ℤ ℤ (fun j : ℤ => twistedSectionsComponent 𝒮 F j) n (c • x) = 0 := by
  classical
  have hhom : ∀ (i : ℕ) (a : 𝒮 i),
      DirectSum.component ℤ ℤ (fun j : ℤ => twistedSectionsComponent 𝒮 F j) n
        ((a : S) • x) = 0 := by
    intro i a
    rw [← DirectSum.sum_support_of x, Finset.smul_sum, map_sum]
    refine Finset.sum_eq_zero fun m hm => ?_
    have hmk := le_of_apply_ne_zero 𝒮 F hx (DFinsupp.mem_support_iff.mp hm)
    refine (congrArg
      (fun y => DirectSum.component ℤ ℤ (fun j : ℤ => twistedSectionsComponent 𝒮 F j) n y)
      (hsmul i m a (x m))).trans ?_
    rw [← DirectSum.apply_eq_component,
      DirectSum.of_eq_of_ne _ _ _ (by omega : n ≠ (i : ℤ) + m)]
  rw [← DirectSum.sum_support_decompose 𝒮 c, Finset.sum_smul, map_sum]
  exact Finset.sum_eq_zero fun i _ => hhom i (DirectSum.decompose 𝒮 c i)

/-- **The module `⨁_{n ≥ k} Γ(X, ℱ(n))` of Tag 0B5R, as an `S`-submodule** of the twisted global
sections `⨁_{n ∈ ℤ} Γ(X, ℱ(n))` of `ℱ` on `X = Proj 𝒮`: the sections whose components in degrees
`< k` vanish. The hypothesis `hsmul` is the formula for the graded action of a homogeneous
scalar. -/
def twistedGlobalSectionsTruncation [Module S (twistedGlobalSections 𝒮 F)]
    (hsmul : ∀ (i : ℕ) (n : ℤ) (a : 𝒮 i) (s : twistedSectionsComponent 𝒮 F n),
      (a : S) • (DirectSum.of (fun m : ℤ => twistedSectionsComponent 𝒮 F m) n s :
          twistedGlobalSections 𝒮 F) =
        DirectSum.of (fun m : ℤ => twistedSectionsComponent 𝒮 F m) ((i : ℤ) + n)
          (homogeneousScalarTwistedSections 𝒮 F i n a s))
    (k : ℤ) : Submodule S (twistedGlobalSections 𝒮 F) where
  carrier := {x | ∀ n : ℤ, n < k →
    DirectSum.component ℤ ℤ (fun j : ℤ => twistedSectionsComponent 𝒮 F j) n x = 0}
  add_mem' {x y} hx hy n hn := by rw [map_add, hx n hn, hy n hn, add_zero]
  zero_mem' n _ := map_zero _
  smul_mem' c x hx n hn := component_smul_eq_zero 𝒮 F hsmul k c hx n hn

variable [Module S (twistedGlobalSections 𝒮 F)]
  (hsmul : ∀ (i : ℕ) (n : ℤ) (a : 𝒮 i) (s : twistedSectionsComponent 𝒮 F n),
    (a : S) • (DirectSum.of (fun m : ℤ => twistedSectionsComponent 𝒮 F m) n s :
        twistedGlobalSections 𝒮 F) =
      DirectSum.of (fun m : ℤ => twistedSectionsComponent 𝒮 F m) ((i : ℤ) + n)
        (homogeneousScalarTwistedSections 𝒮 F i n a s))

/-- A twisted global section lies in the degree-`≥ k` truncation exactly when all its components
in degrees `< k` vanish. -/
theorem mem_twistedGlobalSectionsTruncation (k : ℤ) (x : twistedGlobalSections 𝒮 F) :
    x ∈ twistedGlobalSectionsTruncation 𝒮 F hsmul k ↔
      ∀ n : ℤ, n < k →
        DirectSum.component ℤ ℤ (fun j : ℤ => twistedSectionsComponent 𝒮 F j) n x = 0 :=
  Iff.rfl

/-- A section of a single twist `ℱ(m)` with `k ≤ m` lies in the degree-`≥ k` truncation. -/
theorem of_mem_twistedGlobalSectionsTruncation (k m : ℤ) (hkm : k ≤ m)
    (s : twistedSectionsComponent 𝒮 F m) :
    (DirectSum.of (fun j : ℤ => twistedSectionsComponent 𝒮 F j) m s :
        twistedGlobalSections 𝒮 F) ∈ twistedGlobalSectionsTruncation 𝒮 F hsmul k := by
  intro n hn
  rw [← DirectSum.apply_eq_component, DirectSum.of_eq_of_ne _ _ _ (by omega : n ≠ m)]

/-- The degree-`m` piece of the grading of the twisted global sections lies in the degree-`≥ k`
truncation whenever `k ≤ m`. -/
theorem coe_twistedGlobalSectionsGrading_subset_truncation (k m : ℤ) (hkm : k ≤ m) :
    (twistedGlobalSectionsGrading 𝒮 F m : Set (twistedGlobalSections 𝒮 F)) ⊆
      twistedGlobalSectionsTruncation 𝒮 F hsmul k := by
  intro x hx
  obtain ⟨s, rfl⟩ :=
    (DirectSum.mem_rangeGrading ℤ (fun j : ℤ => twistedSectionsComponent 𝒮 F j) m x).mp hx
  exact of_mem_twistedGlobalSectionsTruncation 𝒮 F hsmul k m hkm s

/-- **The degree-`≥ k` truncation is the `S`-span of the homogeneous twisted global sections of
degree `≥ k`.** -/
theorem twistedGlobalSectionsTruncation_eq_span (k : ℤ) :
    twistedGlobalSectionsTruncation 𝒮 F hsmul k =
      Submodule.span S (⋃ m ∈ Set.Ici k,
        (twistedGlobalSectionsGrading 𝒮 F m : Set (twistedGlobalSections 𝒮 F))) := by
  classical
  refine le_antisymm (fun x hx => ?_) (Submodule.span_le.mpr fun z hz => ?_)
  · rw [← DirectSum.sum_support_of x]
    refine Submodule.sum_mem _ fun m hm => ?_
    have hmk := le_of_apply_ne_zero 𝒮 F hx (DFinsupp.mem_support_iff.mp hm)
    refine Submodule.subset_span (Set.mem_biUnion (Set.mem_Ici.mpr hmk) ?_)
    exact (DirectSum.mem_rangeGrading ℤ (fun j : ℤ => twistedSectionsComponent 𝒮 F j) m _).mpr
      ⟨x m, rfl⟩
  · obtain ⟨m, hm, hzm⟩ := Set.mem_iUnion₂.mp hz
    exact coe_twistedGlobalSectionsGrading_subset_truncation 𝒮 F hsmul k m
      (Set.mem_Ici.mp hm) hzm

/-! ### The truncation of the canonical graded module structure -/

/-- The degree-`≥ k` truncation of the twisted global sections for the canonical graded
`S`-module structure of Tag 03GK. -/
def TwistedGlobalSectionsModule.truncation (D : TwistedGlobalSectionsModule 𝒮 F) (k : ℤ) :
    @Submodule S (twistedGlobalSections 𝒮 F) _ _ D.moduleInst :=
  letI := D.moduleInst
  twistedGlobalSectionsTruncation 𝒮 F D.smul_homogeneous k

/-! ### Comparison with the additive subgroup of Tag 0B5R -/

section AssociatedSheaf

variable {M : Type u} {τ : Type t} [AddCommGroup M] [Module S M]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]

omit [DirectSum.Decomposition 𝒨] in
/-- The module `N = ⨁_{n ≥ k} H⁰(X, M̃(n))` of Tag 0B5R is the additive subgroup underlying the
degree-`≥ k` truncation, so the truncation upgrades it to an `S`-submodule. -/
theorem toAddSubgroup_twistedGlobalSectionsTruncation
    [Module S (twistedGlobalSections 𝒮 (associatedModuleSheaf 𝒮 𝒨))]
    (hsmul : ∀ (i : ℕ) (n : ℤ) (a : 𝒮 i)
        (s : twistedSectionsComponent 𝒮 (associatedModuleSheaf 𝒮 𝒨) n),
      (a : S) • (DirectSum.of
            (fun m : ℤ => twistedSectionsComponent 𝒮 (associatedModuleSheaf 𝒮 𝒨) m) n s :
          twistedGlobalSections 𝒮 (associatedModuleSheaf 𝒮 𝒨)) =
        DirectSum.of (fun m : ℤ => twistedSectionsComponent 𝒮 (associatedModuleSheaf 𝒮 𝒨) m)
          ((i : ℤ) + n)
          (homogeneousScalarTwistedSections 𝒮 (associatedModuleSheaf 𝒮 𝒨) i n a s))
    (k : ℤ) :
    (twistedGlobalSectionsTruncation 𝒮 (associatedModuleSheaf 𝒮 𝒨) hsmul k).toAddSubgroup =
      ProjCoherentII.twistedSectionsTruncation 𝒮 𝒨 k :=
  rfl

end AssociatedSheaf

end Stacks.AlgebraicGeometry.ProjTwistedSections

end
