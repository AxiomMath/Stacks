module

public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.BadPointsMeasure
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.PushforwardCokernelVanishing

/-!
# The stalks of `f_*𝒪_{X'}/𝒪_X` have finite length

The measure of the induction of [Stacks, Tag 0C1L] is the length of the coherent
`𝒪_X`-module `f_*𝒪_{X'}/𝒪_X`, and the first thing it needs is that this length is *finite* at
every point: `Stacks.Chow.sheafMultiplicity` is read through `ENat.toNat`, so an infinite stalk
length is recorded as multiplicity `0`, indistinguishable from a vanishing stalk, and no strict
drop can be read off it.

This file proves that finiteness. It is the assembly of three facts each of which was proved
separately and none of which gives it alone: the cokernel of `𝒪_X ⟶ f_*𝒪_{X'}` has vanishing
stalk wherever `f` is an isomorphism
(`Stacks.GlueSquishFactor.isZero_stalk_cokernel_structureUnitHom`), so its support lies in the
finite bad set; every point of that set is closed
(`Stacks.GlueSquishFactor.isClosed_singleton_of_mem_compl_isoLocus`), so no other point of the
support specializes to it; and a coherent module whose support has such an isolated closed point
has finite length there
(`Stacks.GlueSquishFactor.isFiniteLength_stalk_of_isClosed_of_forall_specializes_eq`).

## Main results

* `Stacks.GlueSquishFactor.isFiniteLength_stalk_of_supp_subset_compl` — a coherent module on a
  scheme locally of finite type over a field, supported inside the complement of an open with
  finite complement, has stalks of finite length at *every* point. The hypothesis is exactly the
  shape of data `Stacks.GlueSquishFactor.IsAlmostIsoCore` supplies.
* `Stacks.GlueSquishFactor.supp_subset_compl_cokernel_structureUnitHom` — the support of
  `f_*𝒪_{X'}/𝒪_X` lies in the complement of any open over which `f` is an isomorphism.
* `Stacks.GlueSquishFactor.finite_supp_cokernel_structureUnitHom` — hence that support is
  finite.
* `Stacks.GlueSquishFactor.isFiniteLength_stalk_cokernel_structureUnitHom` — **the stalks of
  `f_*𝒪_{X'}/𝒪_X` have finite length**, at every point, for an almost isomorphism of algebraic
  `k`-schemes.

## Implementation notes

**The two cases.** Off the support the stalk is a subsingleton, hence of length `0`; this is the
same split as in `Stacks.Chow.isFiniteLength_stalk_of_relativeDimension_eq`, and it is why the
conclusion can be stated for every point rather than for the points of the support.

**Isolation of the bad points.** The hypothesis `huniq` of
`Stacks.GlueSquishFactor.isFiniteLength_stalk_of_isClosed_of_forall_specializes_eq` asks that no
other point of the support specializes to the given one. Here it is free: a point of the support
is a bad point, every bad point is closed, and a closed point which specializes to `x` *is* `x`,
because `x` then lies in the closure of a singleton.

**Coherence is a hypothesis.** `(cokernel (structureUnitHom f)).IsCoherent` is carried as an
argument rather than derived. The module is a quotient of `f_*𝒪_{X'}`, which for a finite `f`
over a locally Noetherian base is coherent; what is not in the tree at this pin is the step from
finite type to coherence over a locally Noetherian scheme, so deriving it here would mean proving
that first. It is a standard property of the module and says nothing about the factorization.

**What this does not give.** Not the measure. A `ℕ`-valued measure also needs the sum over the
support to be compared along a splitting `X' ⟶ Spec_X(𝒜) ⟶ X`. One half of that comparison is
proved on top of this file: additivity of length in the short exact sequence
`0 → 𝒜/𝒪_X → f_*𝒪_{X'}/𝒪_X → f_*𝒪_{X'}/𝒜 → 0` is
`Stacks.GlueSquishFactor.sheafMultiplicity_cokernel_structureUnitHom_add` in
`StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.BadPointsAdditivity`, which consumes
`isFiniteLength_stalk_cokernel_structureUnitHom` below and, through
`Stacks.GlueSquishFactor.isFiniteLength_stalk_cokernel_of_comp_left` and its `_right` companion,
makes it cover both halves of *every* intermediate factorization at once — neither half needs a
finiteness argument of its own. What is still missing is the fibre sum over the points of
`Spec_X(𝒜)` lying over a point of `X`, and a *proper* `𝒜`; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.SubalgebraProducer` and of
`StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.StalkProperSubalgebra`. Nothing here
constructs a measure, so no part of [Stacks, Tag 0C1L] is asserted and no attribute is attached.

## References

* [Stacks Project, Tag 0C1L](https://stacks.math.columbia.edu/tag/0C1L)
* [Stacks Project, Tag 02QW](https://stacks.math.columbia.edu/tag/02QW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.GlueSquishFactor

/-! ### A coherent module supported in the finite bad set -/

/-- **A coherent module supported in a finite bad set has stalks of finite length.** Let `X` be
a scheme locally of finite type over a field, let `U` be an open of `X` whose complement is
finite — the shape of data `Stacks.GlueSquishFactor.IsAlmostIsoCore` supplies — and let `F` be a
coherent `𝒪_X`-module supported inside that complement. Then the stalk of `F` at every point of
`X` has finite length over the local ring there.

On the support the point is a bad point, hence closed, and no other point of the support
specializes to it, because such a point is closed too; so
`Stacks.GlueSquishFactor.isFiniteLength_stalk_of_isClosed_of_forall_specializes_eq` applies. Off
the support the stalk is a subsingleton and the length is `0`. -/
theorem isFiniteLength_stalk_of_supp_subset_compl {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] (F : X.Modules) [F.IsCoherent]
    {U : X.Opens} (hUfin : Set.Finite ((U : Set X)ᶜ))
    (hsupp : SheafOfModules.supp F ⊆ ((U : Set X)ᶜ)) (x : X) :
    IsFiniteLength (X.presheaf.stalk x) (F.presheaf.stalk x) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  by_cases hxF : x ∈ SheafOfModules.supp F
  · refine isFiniteLength_stalk_of_isClosed_of_forall_specializes_eq F hxF
      (isClosed_singleton_of_mem_compl_isoLocus p hUfin (hsupp hxF)) fun η hη hηsupp => ?_
    have hηclosed := isClosed_singleton_of_mem_compl_isoLocus p hUfin (hsupp hηsupp)
    have hx : x ∈ ({η} : Set X) := by
      rw [← hηclosed.closure_eq]
      exact specializes_iff_mem_closure.mp hη
    exact hx.symm
  · have : Subsingleton (F.presheaf.stalk x) :=
      not_nontrivial_iff_subsingleton.mp fun hn =>
        hxF ((SheafOfModules.mem_supp_iff_nontrivial_stalk F x).mpr hn)
    exact Module.length_ne_top_iff.mp (by simp [Module.length_eq_zero])

/-! ### The support of `f_*𝒪_{X'}/𝒪_X` -/

/-- **The support of `f_*𝒪_{X'}/𝒪_X` lies in the bad set.** Over an open on which `f` is an
isomorphism the unit `𝒪_X ⟶ f_*𝒪_{X'}` is surjective on stalks, so its cokernel has vanishing
stalk there. -/
theorem supp_subset_compl_cokernel_structureUnitHom {X' X : Scheme.{u}} (f : X' ⟶ X)
    (U : X.Opens) [IsIso (f ∣_ U)] :
    SheafOfModules.supp (cokernel (structureUnitHom f)) ⊆ ((U : Set X)ᶜ) :=
  fun _ hz hzU =>
    (AlgebraicGeometry.Scheme.Modules.notMem_supp_iff_isZero_stalk
      (cokernel (structureUnitHom f)) _).mpr
        (isZero_stalk_cokernel_structureUnitHom f U hzU) hz

/-- **The support of `f_*𝒪_{X'}/𝒪_X` is finite** when `f` is an isomorphism away from a finite
set: it is contained in that set. This is the half of the measure which says the sum defining it
has finitely many terms. -/
theorem finite_supp_cokernel_structureUnitHom {X' X : Scheme.{u}} (f : X' ⟶ X)
    (U : X.Opens) [IsIso (f ∣_ U)] (hUfin : Set.Finite ((U : Set X)ᶜ)) :
    Set.Finite (SheafOfModules.supp (cokernel (structureUnitHom f))) :=
  hUfin.subset (supp_subset_compl_cokernel_structureUnitHom f U)

/-! ### Finiteness of the length of `f_*𝒪_{X'}/𝒪_X` at every point -/

/-- **The stalks of `f_*𝒪_{X'}/𝒪_X` have finite length.** Let `f : X' ⟶ X` be a morphism of
`k`-schemes with `X` locally of finite type over the field `k`, which restricts to an
isomorphism over an open `U` with finite complement, and suppose the cokernel of
`𝒪_X ⟶ f_*𝒪_{X'}` is coherent. Then that cokernel has a stalk of finite length at *every* point
of `X`.

This is the finiteness that the measure of [Stacks, Tag 0C1L] needs before it can be read as a
natural number: see the implementation notes of this file for what remains. -/
theorem isFiniteLength_stalk_cokernel_structureUnitHom {k : Type u} [Field k]
    {X' X : Scheme.{u}} (f : X' ⟶ X) (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (hcoh : (cokernel (structureUnitHom f)).IsCoherent) (U : X.Opens) [IsIso (f ∣_ U)]
    (hUfin : Set.Finite ((U : Set X)ᶜ)) (x : X) :
    IsFiniteLength (X.presheaf.stalk x)
      ((cokernel (structureUnitHom f)).presheaf.stalk x) := by
  have := hcoh
  exact isFiniteLength_stalk_of_supp_subset_compl p (cokernel (structureUnitHom f)) hUfin
    (supp_subset_compl_cokernel_structureUnitHom f U) x

end Stacks.GlueSquishFactor

end
