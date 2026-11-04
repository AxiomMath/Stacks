module

public import StacksFrontier.AlgebraicGeometry.AffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.NonvanishingTrivialization.Basic

/-!
# The nonvanishing locus of a sum of two global sections

Let `X` be a scheme, `M` an invertible `𝒪_X`-module and `u, v ∈ Γ(X, M)` two global sections.
This file describes the nonvanishing locus `X_{u + v}` in terms of `X_u` and `X_v`, and proves
the fact that makes it useful: **if `X_u` and `X_v` are affine then so is `X_{u + v}`.**

That last statement is the engine of the inductive proofs of
[Stacks, Tag 0F20](https://stacks.math.columbia.edu/tag/0F20) and
[Stacks, Tag 09NV](https://stacks.math.columbia.edu/tag/09NV), where finitely many points are
collected into a single affine nonvanishing locus one point at a time: the Stacks proofs of
those lemmas first shrink the ambient open to an affine one (so that affineness of the new
locus follows from [Stacks, Tag 01PV]) and that shrinking is what forces them through Tag 01ZY
and the embedding of Tag 01Q3. The statement below needs none of that: affineness of a sum's
nonvanishing locus is unconditional, with no hypothesis on the ambient open and no appeal to
`Proj`.

## Main results

* `Stacks.SheafOfModules.nonvanishingLocus_sectionsOfTop_add_le`: `X_{u + v} ⊆ X_u ∪ X_v`.
* `Stacks.SheafOfModules.mem_nonvanishingLocus_sectionsOfTop_add`: a point of `X_u` which is
  not in `X_v` lies in `X_{u + v}`.
* `AlgebraicGeometry.Scheme.Modules.basicOpen_eq_inf_nonvanishingOpen_of_smul_eq`: if a function
  `h` on an open `T` inside `X_w` satisfies `h • w|_T = u|_T`, then the basic open of `h` is
  `X_u ⊓ T`.
* `AlgebraicGeometry.Scheme.Modules.isAffineOpen_nonvanishingOpen_add`: **if `X_u` and `X_v` are
  affine then `X_{u + v}` is affine.**

## Implementation notes

The proof of the main result is Serre's affineness criterion, in Mathlib's form
`AlgebraicGeometry.isAffineOpen_of_isAffineOpen_basicOpen`: an open `T` of a scheme is affine as
soon as a spanning set of `Γ(X, T)` has affine basic opens. Take `T = X_{u + v}`. On `T` the
section `u + v` trivializes `M` — this is
`Stacks.SheafOfModules.bijective_smul_eval_of_le_nonvanishingOpen`, the trivialization clause of
[Stacks, Tag 01CY] — so there are unique functions `h₁, h₂ ∈ Γ(X, T)` with
`h₁ • (u + v)|_T = u|_T` and `h₂ • (u + v)|_T = v|_T`, and injectivity of the same map turns
`u|_T + v|_T = (u + v)|_T` into `h₁ + h₂ = 1`. That is the spanning condition. The basic open of
`h₁` is `X_u ⊓ T`, because on `T` the germ of `u` is the germ of `h₁` times a generator of the
stalk, which is the local-algebra fact
`Stacks.SheafOfModules.smul_notMem_maximalIdeal_smul_top_iff`; and `X_u ⊓ T` is affine by
[Stacks, Tag 01PV] (`AlgebraicGeometry.Scheme.Modules.isAffineOpen_inf_nonvanishingOpen`).

No `@[stacks]` attribute is attached: these statements are ingredients of Tags 09NV, 0F20 and
01ZY rather than any one of those tags, none of which is in the library.

Global sections are written as elements of `Γ(X, M) = M.val.obj (op ⊤)` and converted to
Mathlib's `PresheafOfModules.sections` by `Stacks.SheafOfModules.sectionsOfTop`, which is the
spelling in which they can be added; `PresheafOfModules.sections` carries no additive structure
of its own, and `Stacks.SheafOfModules.nonvanishingLocus_sectionsOfTop_eval` says that nothing
is lost, the nonvanishing locus depending only on the value over `⊤`.

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
* [Stacks Project, Tag 01QF](https://stacks.math.columbia.edu/tag/01QF)
* [Stacks Project, Tag 09NV](https://stacks.math.columbia.edu/tag/09NV)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.SheafOfModules.TensorStalkRingedSpace (ringStalk ringGerm grpStalk grpGerm)

universe u

namespace Stacks.SheafOfModules

section RingedSpace

variable {X : RingedSpace.{u, u}} (M : SheafOfModules.{u} (structureSheafRing X))

/-- The germ over an open `T` of the restriction of a global section is its germ over `⊤`. -/
theorem germ_eval_sectionsOfTop (m : M.val.obj (op (⊤ : Opens X.carrier)))
    (T : Opens X.carrier) {x : X.carrier} (hx : x ∈ T) :
    grpGerm X M.val x T hx ((sectionsOfTop M m).eval (op T))
      = grpGerm X M.val x ⊤ (Opens.mem_top x) m :=
  TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) M.val.presheaf
    (homOfLE (le_top (a := T))) x hx m

/-- Restricting to an open is additive on global sections. -/
theorem eval_sectionsOfTop_add (T : Opens X.carrier)
    (m m' : M.val.obj (op (⊤ : Opens X.carrier))) :
    (sectionsOfTop M (m + m')).eval (op T)
      = (sectionsOfTop M m).eval (op T) + (sectionsOfTop M m').eval (op T) :=
  map_add (ConcreteCategory.hom (M.val.presheaf.map (homOfLE (le_top (a := T))).op)) m m'

variable [∀ x : X.carrier, IsLocalRing (ringStalk X x)]

/-- **A sum of two global sections vanishes wherever both summands do**: `X_{u + v}` is
contained in `X_u ∪ X_v`. -/
theorem nonvanishingLocus_sectionsOfTop_add_le
    (u v : M.val.obj (op (⊤ : Opens X.carrier))) :
    nonvanishingLocus M (sectionsOfTop M (u + v)) ⊆
      nonvanishingLocus M (sectionsOfTop M u) ∪ nonvanishingLocus M (sectionsOfTop M v) := by
  intro x hx
  by_contra hcon
  rw [Set.mem_union, not_or] at hcon
  obtain ⟨hu, hv⟩ := hcon
  rw [mem_nonvanishingLocus_sectionsOfTop_iff] at hx
  simp only [mem_nonvanishingLocus_sectionsOfTop_iff, not_not] at hu hv
  exact hx (by rw [map_add]; exact Submodule.add_mem _ hu hv)

/-- **A point at which one summand is nonvanishing and the other vanishes lies in the
nonvanishing locus of the sum.** -/
theorem mem_nonvanishingLocus_sectionsOfTop_add
    (u v : M.val.obj (op (⊤ : Opens X.carrier))) {x : X.carrier}
    (hu : x ∈ nonvanishingLocus M (sectionsOfTop M u))
    (hv : x ∉ nonvanishingLocus M (sectionsOfTop M v)) :
    x ∈ nonvanishingLocus M (sectionsOfTop M (u + v)) := by
  rw [mem_nonvanishingLocus_sectionsOfTop_iff] at hu ⊢
  rw [mem_nonvanishingLocus_sectionsOfTop_iff, not_not] at hv
  rw [map_add]
  exact notMem_maximalIdeal_smul_top_add _ _ hu hv

end RingedSpace

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

open Stacks.SheafOfModules

variable {X : Scheme.{u}} (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  [Stacks.SheafOfModules.IsInvertible X.presheaf
    (structureSheafRing X.toRingedSpace).property M]

/-- A function `h` on an open `T ⊆ X_w` with `h • w|_T = u|_T` is a unit at a point of `T`
exactly when `u` is nonvanishing there: on `T` the germ of `w` generates the stalk of `M`, so
the germ of `u` escapes `𝔪ₓ Mₓ` exactly when the germ of `h` is a unit. -/
theorem mem_basicOpen_iff_of_smul_eq
    (T : _root_.TopologicalSpace.Opens X.carrier)
    (u w : M.val.obj (op (⊤ : _root_.TopologicalSpace.Opens X.carrier)))
    (hT : T ≤ nonvanishingOpen (X := X.toRingedSpace) M (sectionsOfTop M w))
    (h : X.presheaf.obj (op T))
    (hh : h • (sectionsOfTop M w).eval (op T) = (sectionsOfTop M u).eval (op T))
    {x : X.carrier} (hx : x ∈ T) :
    x ∈ X.basicOpen h ↔
      x ∈ nonvanishingOpen (X := X.toRingedSpace) M (sectionsOfTop M u) := by
  have hwx : grpGerm X.toRingedSpace M.val x ⊤ (Opens.mem_top x) w ∉
      IsLocalRing.maximalIdeal (ringStalk X.toRingedSpace x) •
        (⊤ : Submodule (ringStalk X.toRingedSpace x) (grpStalk X.toRingedSpace M.val x)) :=
    (mem_nonvanishingLocus_sectionsOfTop_iff M w x).mp (hT hx)
  rw [show (x ∈ nonvanishingOpen (X := X.toRingedSpace) M (sectionsOfTop M u)) ↔
      (x ∈ nonvanishingLocus M (sectionsOfTop M u)) from Iff.rfl,
    mem_nonvanishingLocus_sectionsOfTop_iff,
    ← germ_eval_sectionsOfTop M u T hx, ← hh,
      Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule_germ_smul,
    germ_eval_sectionsOfTop M w T hx, smul_notMem_maximalIdeal_smul_top_iff,
    and_iff_left hwx]
  exact (isUnit_ringGerm_iff_mem_basicOpen (X := X.toRingedSpace) h x hx).symm

/-- The basic open of a function `h` on `T ⊆ X_w` with `h • w|_T = u|_T` is `X_u ⊓ T`. -/
theorem basicOpen_eq_inf_nonvanishingOpen_of_smul_eq
    (T : _root_.TopologicalSpace.Opens X.carrier)
    (u w : M.val.obj (op (⊤ : _root_.TopologicalSpace.Opens X.carrier)))
    (hT : T ≤ nonvanishingOpen (X := X.toRingedSpace) M (sectionsOfTop M w))
    (h : X.presheaf.obj (op T))
    (hh : h • (sectionsOfTop M w).eval (op T) = (sectionsOfTop M u).eval (op T)) :
    X.basicOpen h = nonvanishingOpen (X := X.toRingedSpace) M (sectionsOfTop M u) ⊓ T := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · have hxT : x ∈ T := X.basicOpen_le h hx
    exact ⟨(mem_basicOpen_iff_of_smul_eq M T u w hT h hh hxT).mp hx, hxT⟩
  · exact (mem_basicOpen_iff_of_smul_eq M T u w hT h hh hx.2).mpr hx.1

/-- **The nonvanishing locus of a sum of two global sections of an invertible module is affine
as soon as the nonvanishing loci of the two summands are.**

Serre's criterion applied to `T = X_{u + v}`: the section `u + v` trivializes `M` over `T`, so
`u|_T` and `v|_T` are `h₁ • (u + v)|_T` and `h₂ • (u + v)|_T` for unique functions `h₁, h₂` on
`T`, which then satisfy `h₁ + h₂ = 1` and have basic opens `X_u ⊓ T` and `X_v ⊓ T`, both affine
by [Stacks, Tag 01PV]. -/
theorem isAffineOpen_nonvanishingOpen_add
    (u v : M.val.obj (op (⊤ : _root_.TopologicalSpace.Opens X.carrier)))
    (hu : IsAffineOpen (nonvanishingOpen (X := X.toRingedSpace) M (sectionsOfTop M u)))
    (hv : IsAffineOpen (nonvanishingOpen (X := X.toRingedSpace) M (sectionsOfTop M v))) :
    IsAffineOpen (nonvanishingOpen (X := X.toRingedSpace) M (sectionsOfTop M (u + v))) := by
  classical
  set T := nonvanishingOpen (X := X.toRingedSpace) M (sectionsOfTop M (u + v))
  have hbij := bijective_smul_eval_of_le_nonvanishingOpen M (sectionsOfTop M (u + v)) T le_rfl
  have key : ∀ w, IsAffineOpen (nonvanishingOpen (X := X.toRingedSpace) M (sectionsOfTop M w)) →
      ∃ h : X.presheaf.obj (op T), h • (sectionsOfTop M (u + v)).eval (op T) =
        (sectionsOfTop M w).eval (op T) ∧ IsAffineOpen (X.basicOpen h) := fun w hw => by
    obtain ⟨h, hh⟩ := hbij.surjective ((sectionsOfTop M w).eval (op T))
    replace hh : h • (sectionsOfTop M (u + v)).eval (op T) = (sectionsOfTop M w).eval (op T) := hh
    refine ⟨h, hh, ?_⟩
    rw [basicOpen_eq_inf_nonvanishingOpen_of_smul_eq M _ w (u + v) le_rfl _ hh]
    exact isAffineOpen_inf_nonvanishingOpen M (sectionsOfTop M (u + v)) _ hw
  obtain ⟨h₁, hh₁, ha₁⟩ := key u hu
  obtain ⟨h₂, hh₂, ha₂⟩ := key v hv
  have hsum : h₁ + h₂ = 1 := by
    refine hbij.injective ?_
    change (h₁ + h₂) • _ = (1 : X.presheaf.obj _) • _
    rw [add_smul, hh₁, hh₂, one_smul]
    exact (eval_sectionsOfTop_add M _ u v).symm
  refine AlgebraicGeometry.isAffineOpen_of_isAffineOpen_basicOpen _ {h₁, h₂} ?_ ?_
  · rw [Ideal.eq_top_iff_one, ← hsum]
    exact Ideal.add_mem _ (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))
  · intro i hi
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    rcases hi with rfl | rfl
    exacts [ha₁, ha₂]

end AlgebraicGeometry.Scheme.Modules

end
