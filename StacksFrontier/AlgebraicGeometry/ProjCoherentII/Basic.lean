module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjDegreeOpen
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjShiftedSectionModule
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjStandardOpenCover
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistSectionModuleGraded
public import StacksFrontier.AlgebraicGeometry.ModuleTwistIso.Basic
public import StacksFrontier.AlgebraicGeometry.ProjNoetherian.Basic

/-!
# Coherent sheaves on `Proj`, II: the two canonical maps into `N'` and the comparison `N → N'`

Let `A` be a graded ring, `M` a `ℤ`-graded `A`-module, `X = Proj(A)` and `M̃` the associated
quasi-coherent `𝒪_X`-module. Tag 0B5R studies, for an integer `k`, the two graded `A`-modules

`N  = ⨁_{n ≥ k} H⁰(X, M̃(n))`   and   `N' = ⨁_{n ≥ k} H⁰(X, M(n)~)`,

the first built from the *twists of the associated sheaf* and the second from the *associated
sheaves of the shifted modules*. Both ambient direct sums over all of `ℤ` are already in the
repository — `twistedGlobalSections` for `N` and `shiftedModuleGlobalSections` for `N'` — so
`N` and `N'` are realized here as the subgroups of elements supported in degrees `≥ k`.

Three of Tag 0B5R's six assertions are proved:

* **(3)** there is a canonical map `N → N'`. It is the global sections of the canonical
  comparison `M̃ ⊗ 𝒪(n) → M(n)~` of Tag 01MQ, taken in each degree `n` and assembled over the
  direct sum; `twistedToShiftedSections_component` records that this is what it is.
* **(4)** if `k` is small enough there is a canonical map `M → N'`. The map is the one of Tag
  01MR; "`k` small enough" is used in the form in which the source uses it — generators of `M` in
  degrees `≥ k` force `M_n = 0` for `n < k`, and that vanishing is the hypothesis `hlow`.
* **(6)** `N_n → N'_n` is an isomorphism for `d ∣ n`. The source takes `d` to be the lcm of the
  degrees of a set of homogeneous generators of `A` over `A_0`; the only property of `d` its
  proof uses is that the standard opens of the homogeneous elements of degree `d` cover `X`,
  which is `degreeOpen 𝒜 d = ⊤`, and that is the hypothesis of
  `bijective_twistedToShiftedComponent`. For `A` Noetherian such a positive `d` exists, by the
  common-degree finite standard-open cover of the quasi-compact `X`; that is
  `exists_pos_degreeOpen_eq_top`, and combining the two gives
  `exists_pos_forall_bijective_twistedToShiftedComponent`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjCoherentII.twistedToShiftedComponent`: the degree-`n` comparison
  `H⁰(X, M̃(n)) → H⁰(X, M(n)~)`, the global sections of Tag 01MQ's map.
* `Stacks.AlgebraicGeometry.ProjCoherentII.twistedToShiftedSections`: its assembly
  `⨁_{n ∈ ℤ} H⁰(X, M̃(n)) → ⨁_{n ∈ ℤ} H⁰(X, M(n)~)`.
* `Stacks.AlgebraicGeometry.ProjCoherentII.twistedSectionsTruncation`,
  `Stacks.AlgebraicGeometry.ProjCoherentII.shiftedSectionsTruncation`: the modules `N` and `N'`,
  as the subgroups of elements whose components in degrees `< k` vanish.
* `Stacks.AlgebraicGeometry.ProjCoherentII.truncatedTwistedToShifted`: **Tag 0B5R (3)**, the
  canonical map `N → N'`.
* `Stacks.AlgebraicGeometry.ProjCoherentII.moduleToTruncatedShiftedSections`: **Tag 0B5R (4)**,
  the canonical map `M → N'`.

## Main results

* `Stacks.AlgebraicGeometry.ProjCoherentII.twistedToShiftedSections_component`: the assembled
  map is degreewise the global sections of Tag 01MQ's comparison.
* `Stacks.AlgebraicGeometry.ProjCoherentII.globalSectionsModuleMap_hom_component`: the degree-`n`
  component of Tag 01MR's map `M → ⨁_n H⁰(X, M(n)~)` is the canonical map on the degree-`n`
  homogeneous part of `M`, applied to the degree-`n` piece of the decomposition of the argument.
  This is what makes `M → N'` land in `N'`.
* `Stacks.AlgebraicGeometry.ProjCoherentII.globalSectionsModuleMap_hom_mem_truncation`: the
  image of `M` lies in `N'`, which is the content of (4).
* `Stacks.AlgebraicGeometry.ProjCoherentII.bijective_twistedToShiftedComponent` and
  `Stacks.AlgebraicGeometry.ProjCoherentII.exists_pos_forall_bijective_twistedToShiftedComponent`:
  **Tag 0B5R (6)**, in the two forms described above.

## Implementation notes

The degreewise map is `((moduleTwistMap 𝒮 𝒨 n).val.app (op ⊤)).hom`. Its domain is the sections
over `⊤` of the sheafified tensor product
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf (Proj 𝒮).toRingedSpace M̃ 𝒪(n)`, while
`twistedSectionsComponent` is phrased with
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistSheafOfModules`, built from
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf`. The two tensor-sheaf constructions are
different declarations with definitionally equal bodies, and the local `implicit_reducible`
attributes of this file are what lets the elaborator cross between them; `exact` accepts the
identification where `rw` would have nothing to rewrite. The same identification is what lets
`ModuleTwistIso.bijective_moduleTwistAb_app_of_le_ratioLocus` — stated for
`ConcreteCategory.hom ((moduleTwistAb 𝒮 𝒨 n).app (op ⊤))` — be used directly as a statement
about `twistedToShiftedComponent`.

`N` and `N'` are cut out by the vanishing of the components in degrees `< k`, read through
`DirectSum.component ℤ ℤ`, rather than as the span of the summands with `n ≥ k`: for a direct sum
the two descriptions agree, and the first is the one under which the degreewise formulas
`twistedToShiftedSections_component` and `globalSectionsModuleMap_hom_component` immediately give
membership. `DirectSum.component` is also the spelling in which Tag 01MR's datum states its
scalar formula.

`globalSectionsModuleMap_hom_component` is proved by decomposing the argument, not by
extensionality on the direct sum: the map out of `M` is only characterized on homogeneous
elements, so the sum over `(DirectSum.decompose 𝒨 m).support` is unavoidable, and the two cases
of the proof are whether `n` is in that support.

## What is not done here

Parts **(1)**, **(2)** and **(5)** of Tag 0B5R are not proved, and nothing in this file carries
a `stacks` attribute for them.

* (2), finiteness of `N` over `A`, is part (4) of Tag 0B5Q. Of Tag 0B5Q only the assertion that
  `Proj(A)` is a Noetherian scheme is proved in this library
  (`Stacks.AlgebraicGeometry.Proj.isNoetherian_proj`), which is what this file uses for
  quasi-compactness; its finiteness assertion is absent, so (2) has no input to be deduced from.
* (1), finiteness of `N'`, is deduced in the source from (2) by the Veronese trick, and so is
  blocked behind (2).
* (5), that `M_n → N'_n` is an isomorphism for `n ≫ 0`, needs the vanishing-in-large-degrees
  statement for a finite module with vanishing associated sheaf, which rests on (1) and (2).

Nothing is claimed about the `A`-module structure of the comparison `N → N'` beyond additivity:
the map is assembled from the degreewise maps as a homomorphism of additive groups, and its
compatibility with the homogeneous scalar actions of `twistedSectionsGModule` and
`shiftedSectionsGModule` is not proved.

## References

* [Stacks Project, Tag 0B5R](https://stacks.math.columbia.edu/tag/0B5R)
* [Stacks Project, Tag 01MQ](https://stacks.math.columbia.edu/tag/01MQ)
* [Stacks Project, Tag 01MR](https://stacks.math.columbia.edu/tag/01MR)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 0B5Q](https://stacks.math.columbia.edu/tag/0B5Q)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace DirectSum
open AlgebraicGeometry.ProjectiveSpectrum.Proj
  (associatedModuleSheaf twistSheafOfModules twistingSheaf twistedGlobalSections)
open Stacks.AlgebraicGeometry.ProjShiftedSections
  (shiftedSectionsComponent shiftedModuleGlobalSections globalSectionsModuleMap
    degreeNToGlobalSections)
open Stacks.AlgebraicGeometry.ProjTwistedSections (twistedSectionsComponent)
open Stacks.GradedModule (shiftedGrading)
open scoped Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjCoherentII

universe u w t

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

variable {S : Type u} {M : Type u} {σ : Type w} {τ : Type t}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]

/-! ### The degreewise comparison and its assembly -/

/-- The degree-`n` comparison `H⁰(X, M̃(n)) → H⁰(X, M(n)~)` on `X = Proj(A)`: the global sections
of the canonical map `M̃ ⊗ 𝒪(n) → M(n)~` of Tag 01MQ. -/
def twistedToShiftedComponent (n : ℤ) :
    twistedSectionsComponent 𝒮 (associatedModuleSheaf 𝒮 𝒨) n →+
      shiftedSectionsComponent 𝒮 𝒨 n :=
  ((ProjShifted.moduleTwistMap 𝒮 𝒨 n).val.app (op ⊤)).hom.toAddMonoidHom

/-- The comparison `⨁_{n ∈ ℤ} H⁰(X, M̃(n)) → ⨁_{n ∈ ℤ} H⁰(X, M(n)~)` assembled from the
degreewise maps. -/
def twistedToShiftedSections :
    twistedGlobalSections 𝒮 (associatedModuleSheaf 𝒮 𝒨) →+
      shiftedModuleGlobalSections 𝒮 𝒨 :=
  DirectSum.toAddMonoid fun n =>
    (DirectSum.of (fun k : ℤ => shiftedSectionsComponent 𝒮 𝒨 k) n).comp
      (twistedToShiftedComponent 𝒮 𝒨 n)

/-- The `n`-th component of an element supported in a different degree `i ≠ n` vanishes. -/
private theorem component_of_of_ne {R ι : Type*} [Semiring R] [DecidableEq ι] {β : ι → Type*}
    [∀ i, AddCommMonoid (β i)] [∀ i, Module R (β i)] {i n : ι} (h : i ≠ n) (y : β i) :
    DirectSum.component R ι β n (DirectSum.of β i y) = 0 := by
  rw [← DirectSum.apply_eq_component, DirectSum.of_eq_of_ne _ _ _ h.symm]

/-- The assembled comparison is degreewise the global sections of Tag 01MQ's map: its degree-`n`
component is the degree-`n` comparison applied to the degree-`n` component of the argument. -/
theorem twistedToShiftedSections_component
    (x : twistedGlobalSections 𝒮 (associatedModuleSheaf 𝒮 𝒨)) (n : ℤ) :
    DirectSum.component ℤ ℤ (fun k : ℤ => shiftedSectionsComponent 𝒮 𝒨 k) n
        (twistedToShiftedSections 𝒮 𝒨 x) =
      twistedToShiftedComponent 𝒮 𝒨 n
        (DirectSum.component ℤ ℤ
          (fun k : ℤ => twistedSectionsComponent 𝒮 (associatedModuleSheaf 𝒮 𝒨) k) n x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of j y =>
      rw [twistedToShiftedSections, DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply]
      rcases eq_or_ne j n with rfl | hjn
      · rw [← DirectSum.apply_eq_component, ← DirectSum.apply_eq_component,
          DirectSum.of_eq_same, DirectSum.of_eq_same]
      · rw [component_of_of_ne hjn, component_of_of_ne hjn, map_zero]
  | add y z hy hz =>
      rw [map_add, map_add, hy, hz]
      exact (map_add _ _ _).symm

/-! ### The modules `N` and `N'` -/

/-- **The module `N' = ⨁_{n ≥ k} H⁰(X, M(n)~)`** of Tag 0B5R: the subgroup of
`⨁_{n ∈ ℤ} H⁰(X, M(n)~)` of elements all of whose components in degrees `< k` vanish. -/
def shiftedSectionsTruncation (k : ℤ) : AddSubgroup (shiftedModuleGlobalSections 𝒮 𝒨) where
  carrier := {x | ∀ n : ℤ, n < k →
    DirectSum.component ℤ ℤ (fun j : ℤ => shiftedSectionsComponent 𝒮 𝒨 j) n x = 0}
  add_mem' {x y} hx hy n hn := by
    rw [map_add, hx n hn, hy n hn, add_zero]
  zero_mem' n _ := map_zero _
  neg_mem' {x} hx n hn := by
    rw [map_neg, hx n hn, neg_zero]

/-- **The module `N = ⨁_{n ≥ k} H⁰(X, M̃(n))`** of Tag 0B5R: the subgroup of
`⨁_{n ∈ ℤ} H⁰(X, M̃(n))` of elements all of whose components in degrees `< k` vanish. -/
def twistedSectionsTruncation (k : ℤ) :
    AddSubgroup (twistedGlobalSections 𝒮 (associatedModuleSheaf 𝒮 𝒨)) where
  carrier := {x | ∀ n : ℤ, n < k →
    DirectSum.component ℤ ℤ
      (fun j : ℤ => twistedSectionsComponent 𝒮 (associatedModuleSheaf 𝒮 𝒨) j) n x = 0}
  add_mem' {x y} hx hy n hn := by
    rw [map_add, hx n hn, hy n hn, add_zero]
  zero_mem' n _ := map_zero _
  neg_mem' {x} hx n hn := by
    rw [map_neg, hx n hn, neg_zero]

/-! ### Part (3): the canonical map `N → N'` -/

/-- **Tag 0B5R (3): the canonical map `N → N'`.** The comparison assembled from the global
sections of Tag 01MQ's maps carries the degrees `≥ k` part of `⨁_n H⁰(X, M̃(n))` into the
degrees `≥ k` part of `⨁_n H⁰(X, M(n)~)`, because it is degreewise. -/
@[stacks 0B5R "part (3), the canonical map N → N'"]
def truncatedTwistedToShifted (k : ℤ) :
    twistedSectionsTruncation 𝒮 𝒨 k →+ shiftedSectionsTruncation 𝒮 𝒨 k :=
  ((twistedToShiftedSections 𝒮 𝒨).comp
      (twistedSectionsTruncation 𝒮 𝒨 k).subtype).codRestrict _ fun x n hn => by
    rw [AddMonoidHom.comp_apply, twistedToShiftedSections_component]
    exact (congrArg (twistedToShiftedComponent 𝒮 𝒨 n) (x.2 n hn)).trans (map_zero _)

/-! ### Part (4): the canonical map `M → N'` -/

/-- The degree-`n` component of Tag 01MR's map `M → ⨁_n H⁰(X, M(n)~)` is the canonical map
`M_n → H⁰(X, M(n)~)` applied to the degree-`n` piece of the decomposition of the argument. -/
theorem globalSectionsModuleMap_hom_component (m : M) (n : ℤ) :
    DirectSum.component ℤ ℤ (fun j : ℤ => shiftedSectionsComponent 𝒮 𝒨 j) n
        ((globalSectionsModuleMap 𝒮 𝒨).hom m) =
      degreeNToGlobalSections 𝒮 𝒨 n (DirectSum.decompose 𝒨 m n) := by
  classical
  have key : ∀ (i : ℤ) (x : 𝒨 i),
      (globalSectionsModuleMap 𝒮 𝒨).hom (x : M) =
        DirectSum.of (fun j : ℤ => shiftedSectionsComponent 𝒮 𝒨 j) i
          (degreeNToGlobalSections 𝒮 𝒨 i x) :=
    fun i x => (globalSectionsModuleMap 𝒮 𝒨).map_homogeneous i x
  have h1 : DirectSum.component ℤ ℤ (fun j : ℤ => shiftedSectionsComponent 𝒮 𝒨 j) n
        ((globalSectionsModuleMap 𝒮 𝒨).hom m)
      = ∑ i ∈ (DirectSum.decompose 𝒨 m).support,
          DirectSum.component ℤ ℤ (fun j : ℤ => shiftedSectionsComponent 𝒮 𝒨 j) n
            ((globalSectionsModuleMap 𝒮 𝒨).hom ((DirectSum.decompose 𝒨 m i : 𝒨 i) : M)) := by
    rw [← map_sum, ← map_sum, DirectSum.sum_support_decompose 𝒨 m]
  rw [h1]
  by_cases hn : n ∈ (DirectSum.decompose 𝒨 m).support
  · rw [Finset.sum_eq_single_of_mem n hn (fun b _ hbn => by
      rw [key b _, component_of_of_ne hbn]),
      key n _, ← DirectSum.apply_eq_component, DirectSum.of_eq_same]
  · have hz : DirectSum.decompose 𝒨 m n = 0 := DFinsupp.notMem_support_iff.mp hn
    rw [hz, map_zero]
    refine Finset.sum_eq_zero fun b hb => ?_
    have hbn : n ≠ b := fun h => hn (h ▸ hb)
    rw [key b _, component_of_of_ne hbn.symm]

/-- Tag 01MR's canonical map `M → ⨁_{n ∈ ℤ} H⁰(X, M(n)~)` lands in `N'` as soon as `M` vanishes
in the degrees below `k`. This is the content of Tag 0B5R (4): the source's hypothesis is that
the generators of `M` sit in degrees `≥ k`, and what it uses is exactly this vanishing. -/
theorem globalSectionsModuleMap_hom_mem_truncation (k : ℤ)
    (hlow : ∀ n : ℤ, n < k → ∀ x ∈ 𝒨 n, x = (0 : M)) (m : M) :
    (globalSectionsModuleMap 𝒮 𝒨).hom m ∈ shiftedSectionsTruncation 𝒮 𝒨 k := by
  intro n hn
  rw [globalSectionsModuleMap_hom_component]
  have hz : (DirectSum.decompose 𝒨 m n) = 0 := by
    refine Subtype.ext ?_
    rw [ZeroMemClass.coe_zero]
    exact hlow n hn _ (DirectSum.decompose 𝒨 m n).2
  rw [hz, map_zero]

/-- **Tag 0B5R (4): for `k` small enough there is a canonical map `M → N'`.** The map is Tag
01MR's `M → ⨁_{n ∈ ℤ} H⁰(X, M(n)~)`, and "`k` small enough" is the hypothesis
`hlow : ∀ n < k, ∀ x ∈ 𝒨 n, x = 0` that `M` vanishes below degree `k`, which is what generators
of `M` in degrees `≥ k` give. -/
@[stacks 0B5R "part (4), the canonical map M → N'"]
def moduleToTruncatedShiftedSections (k : ℤ)
    (hlow : ∀ n : ℤ, n < k → ∀ x ∈ 𝒨 n, x = (0 : M)) :
    M →+ shiftedSectionsTruncation 𝒮 𝒨 k :=
  (globalSectionsModuleMap 𝒮 𝒨).hom.toAddMonoidHom.codRestrict _
    (globalSectionsModuleMap_hom_mem_truncation 𝒮 𝒨 k hlow)

/-! ### Part (6): `N_n → N'_n` is an isomorphism for `d ∣ n` -/

/-- **Tag 0B5R (6), in the form that exhibits the hypothesis on `d`.** If the standard opens of
the homogeneous elements of degree `d` cover `Proj(A)` then, for every `n` divisible by `d`, the
degree-`n` comparison `N_n = H⁰(X, M̃(n)) → H⁰(X, M(n)~) = N'_n` is bijective.

The source's `d` is the lcm of the degrees of homogeneous generators of `A` over `A_0`, and the
hypothesis `hd` is the only property of it the source's proof uses: each such generator `f` has
`f ^ (d / deg f)` of degree `d` with the same standard open, and the standard opens of the
generators cover. The proof here is Tag 01MU's comparison assertion: `hd` puts all of `Proj(A)`
inside the ratio locus `⋃ D₊(fg)` with `deg f = deg g + d` — take `g = 1` in degree `0` — on
which the comparison `M̃ ⊗ 𝒪(dm) → M(dm)~` is bijective on sections over every open. -/
theorem bijective_twistedToShiftedComponent
    {d : ℕ} (hd : AlgebraicGeometry.Proj.degreeOpen 𝒮 d = ⊤) {n : ℤ} (hdn : (d : ℤ) ∣ n) :
    Function.Bijective (twistedToShiftedComponent 𝒮 𝒨 n) := by
  obtain ⟨m, rfl⟩ := hdn
  have hW : (⊤ : Opens (ProjectiveSpectrum.top 𝒮)) ≤ ProjShared.ratioLocus 𝒮 d := by
    intro x _
    have hx : x ∈ AlgebraicGeometry.Proj.degreeOpen 𝒮 d := by rw [hd]; trivial
    obtain ⟨f, hfx⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    refine (ProjShared.mem_ratioLocus_iff 𝒮 d x).mpr
      ⟨0, (f : S), 1, by rw [zero_add]; exact f.2, SetLike.one_mem_graded 𝒮, ?_, ?_⟩
    · exact (AlgebraicGeometry.Proj.mem_basicOpen 𝒮 (f : S) x).mp hfx
    · exact fun hmem => x.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hmem)
  exact ModuleTwistIso.bijective_moduleTwistAb_app_of_le_ratioLocus 𝒮 𝒨 hW
    (mul_comm (m : ℤ) (d : ℤ))

/-- For a Noetherian graded ring `A` there is a positive `d` whose degree-`d` standard opens
cover `Proj(A)`: `Proj(A)` is a Noetherian scheme, hence quasi-compact, and a quasi-compact open
has a finite cover by standard opens of homogeneous elements of one common positive degree. -/
theorem exists_pos_degreeOpen_eq_top [IsNoetherianRing S] :
    ∃ d : ℕ, 0 < d ∧ AlgebraicGeometry.Proj.degreeOpen 𝒮 d = ⊤ := by
  have hcompact : IsCompact ((⊤ : (AlgebraicGeometry.Proj 𝒮).Opens) :
      Set (AlgebraicGeometry.Proj 𝒮)) := by
    rw [TopologicalSpace.Opens.coe_top]
    exact isCompact_univ
  obtain ⟨d, hd, s, hs, hcover⟩ :=
    AlgebraicGeometry.Proj.exists_common_degree_finite_basicOpen_cover 𝒮 ⊤ hcompact
  refine ⟨d, hd, top_le_iff.mp fun x _ => ?_⟩
  have hx : x ∈ ⨆ f ∈ s, AlgebraicGeometry.Proj.basicOpen 𝒮 f ⊓
      (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens) := by
    rw [← hcover]; trivial
  obtain ⟨f, hf⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  obtain ⟨hfs, hxf⟩ := TopologicalSpace.Opens.mem_iSup.mp hf
  exact AlgebraicGeometry.Proj.basicOpen_le_degreeOpen 𝒮 (hs f hfs)
    (TopologicalSpace.Opens.mem_inf.mp hxf).1

/-- **Tag 0B5R (6).** For a Noetherian graded ring `A` and a graded `A`-module `M` there is a
positive `d` such that `N_n = H⁰(X, M̃(n)) → H⁰(X, M(n)~) = N'_n` is bijective for every `n`
divisible by `d`. The `d` is the common degree of a finite standard-open cover of `Proj(A)`,
which is the property the source's `d = lcm(deg f_i)` is used for. -/
@[stacks 0B5R "part (6), N_n ≅ N'_n for d | n"]
theorem exists_pos_forall_bijective_twistedToShiftedComponent [IsNoetherianRing S] :
    ∃ d : ℕ, 0 < d ∧ ∀ n : ℤ, (d : ℤ) ∣ n →
      Function.Bijective (twistedToShiftedComponent 𝒮 𝒨 n) := by
  obtain ⟨d, hdpos, hd⟩ := exists_pos_degreeOpen_eq_top 𝒮
  exact ⟨d, hdpos, fun n hdn => bijective_twistedToShiftedComponent 𝒮 𝒨 hd hdn⟩

end Stacks.AlgebraicGeometry.ProjCoherentII

end
