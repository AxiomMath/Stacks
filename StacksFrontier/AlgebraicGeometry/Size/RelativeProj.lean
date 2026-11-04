module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.RelativeProjSectionRings
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Charts.Descent
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.Proj
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.BaseChangeGluing

/-!
# Projective spectra stay inside a size cutoff (Stacks 000R)

The relative projective spectrum `Proj_S(𝒜)` of Stacks 01NQ is glued from the absolute
projective spectra `Proj Γ(U, 𝒜)` of the graded rings of sections over the affine opens of
the base. This file bounds the size invariant `AlgebraicGeometry.Scheme.size` of both, and
so places them inside the full subcategory `Sch_κ` cut off at a cardinal `κ` — the
condition `AlgebraicGeometry.BigFppfSite.Contains`, which is by definition that size bound.

## The bound

For an absolute `Proj`, the estimate is

> `size (Proj 𝒜) ≤ max {ℵ₀, #A}`

(`AlgebraicGeometry.Scheme.size_Proj_le`), where `A` is the *whole* graded ring, through the
open-cover bound of Stacks 000Q. No finiteness hypothesis is needed, unlike for the bound of
Stacks 000R (5) by a finite type morphism to the base.

For the relative `Proj` of a situation `s` of Stacks 01NN, the same open-cover bound over
the charts `Stacks.RelativeProj.Situation.relativeProjChart` gives

> `size (relativeProj s) ≤ c` whenever `ℵ₀ ≤ c`, `#affineOpens(base) ≤ c`
> and `#Γ(W, 𝒜) ≤ c` for every affine open `W` of the base

(`Stacks.RelativeProj.Situation.size_relativeProj_le`). The bound must be *uniform* in `W`:
a cutoff cardinal is a strong prelimit of uncountable cofinality but need not be regular, so
a supremum of fewer than `κ` cardinals each below `κ` can reach `κ`.

## Main results

* `AlgebraicGeometry.Scheme.size_le_of_isOpenImmersion_cover`: Stacks 000Q for a jointly
  surjective family of open immersions with a uniform bound.
* `AlgebraicGeometry.Scheme.size_Proj_lt_of_mk_le`: the absolute projective spectrum, in the
  cutoff form of `AlgebraicGeometry.Scheme.size_Proj_le`.
* `Stacks.RelativeProj.Situation.size_relativeProj_le`: the relative projective spectrum.
* `AlgebraicGeometry.BigFppfSite.contains_relativeProj`: the relative projective spectrum of
  a situation whose base is an object of a big fppf site, and whose graded rings of sections
  are uniformly bounded below the cutoff, is an object of that site; this is the size
  condition on the blowing ups of Stacks 085Q and 0BHE.
-/

@[expose] public section

open Cardinal CategoryTheory HomogeneousLocalization TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {κ : Cardinal.{u}}

/-! ### Stacks 000Q for a jointly surjective family of open immersions -/

/-- **Stacks 000Q, uniform form.** If a scheme `Y` is covered by the images of a family of
open immersions `g i : X i ⟶ Y` indexed by a type `ι`, and a single cardinal `c` bounds both
`#ι` and the size of every `X i`, then `size Y ≤ c`. -/
theorem Scheme.size_le_of_isOpenImmersion_cover {Y : Scheme.{u}} {ι : Type u} [Nonempty ι]
    {X : ι → Scheme.{u}} (g : ∀ i, X i ⟶ Y) (hg : ∀ i, IsOpenImmersion (g i))
    (hcov : ∀ y : Y, ∃ i, y ∈ Set.range (g i)) {c : Cardinal.{u}} (hι : #ι ≤ c)
    (hX : ∀ i, (X i).size ≤ c) : Y.size ≤ c := by
  have := hg
  have hsup : ⨆ i, (g i).opensRange = ⊤ := by
    refine Opens.ext (Set.eq_univ_of_forall fun y => ?_)
    obtain ⟨i, hi⟩ := hcov y
    rw [Opens.coe_iSup]
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  refine (Scheme.size_le_of_iSup_eq_top (fun i => (g i).opensRange) hsup).trans
    (max_le hι (ciSup_le' fun i => ?_))
  rw [← Scheme.size_congr (g i).isoOpensRange]
  exact hX i

/-! ### The absolute projective spectrum -/

/-- **Stacks 000R (6) and (9) for an absolute `Proj`, in the cutoff form.** If `A` has
cardinality at most `Bound(size T) = size(T) ^ ℵ₀` for an object `T` of `Sch_κ`, then
`Proj 𝒜` is an object of `Sch_κ`. -/
theorem Scheme.size_Proj_lt_of_mk_le (hκ : ℵ₀ < κ) (hsl : Cardinal.IsStrongPrelimit κ)
    {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ)
    [GradedRing 𝒜] {T : Scheme.{u}} (hT : T.size < κ) (h : #A ≤ T.size ^ ℵ₀) :
    (Proj 𝒜).size < κ :=
  (Scheme.size_Proj_le 𝒜).trans_lt
    (max_lt hκ (h.trans_lt (Cardinal.power_aleph0_lt_of_isStrongPrelimit hκ hsl hT)))

end AlgebraicGeometry

namespace Stacks.RelativeProj.Situation

open _root_.Stacks.AlgebraicGeometry

/-- **Stacks 000R (6) for a relative `Proj`.** Let `s` be a relative projective spectrum
situation (Stacks 01NN) and let `c` be an infinite cardinal bounding both the number of
affine opens of the base and the cardinality of the graded ring of sections over each of
them. Then `size (Proj_S(𝒜)) ≤ c`. -/
theorem size_relativeProj_le (s : Situation.{u}) {c : Cardinal.{u}} (hc : ℵ₀ ≤ c)
    (hbase : #s.base.affineOpens ≤ c)
    (hsec : ∀ W : s.base.affineOpens, #(s.sectionRing W.1) ≤ c) :
    (relativeProj s).size ≤ c := by
  have : Nonempty s.base.affineOpens := ⟨⟨⊥, AlgebraicGeometry.isAffineOpen_bot s.base⟩⟩
  refine AlgebraicGeometry.Scheme.size_le_of_isOpenImmersion_cover (relativeProjChart s)
    (fun W => inferInstance) (fun x => ?_) hbase
    fun W => (AlgebraicGeometry.Scheme.size_Proj_le _).trans (max_le hc (hsec W))
  obtain ⟨W, hW⟩ := Opens.mem_iSup.mp
    ((AlgebraicGeometry.iSup_affineOpens_eq_top s.base).ge (Set.mem_univ (relativeProjToBase s x)))
  exact ⟨W, (mem_opensRange_relativeProjChart s W x).mpr hW⟩

end Stacks.RelativeProj.Situation

namespace AlgebraicGeometry.BigFppfSite

open Stacks.RelativeProj

/-- **The relative projective spectrum of a situation over a scheme of a big fppf site is a
scheme of that site**, provided the graded rings of sections over the affine opens of the
base are uniformly bounded by a cardinal below the cutoff. This is the size condition on the
blowing up of Stacks 085Q, and on the blowing up of an algebraic space at a closed point,
Stacks 0BHE. -/
theorem contains_relativeProj (B : BigFppfSite.{u}) (s : Situation.{u}) {c : Cardinal.{u}}
    (hc : c < B.cutoff) (hbase : s.base.size ≤ c)
    (hsec : ∀ W : s.base.affineOpens, #(s.sectionRing W.1) ≤ c) :
    B.Contains (Situation.relativeProj s) :=
  (Situation.size_relativeProj_le s ((Scheme.aleph0_le_size s.base).trans hbase)
    ((Scheme.mk_affineOpens_le_size s.base).trans hbase) hsec).trans_lt hc

end AlgebraicGeometry.BigFppfSite

end
