module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.Topology.JacobsonSpace
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Support
public import StacksFrontier.RingTheory.Artinian.FiniteType
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Three ingredients for the measure of [Stacks, Tag 0C1L]

The measure the splitting hypothesis of
`Stacks.GlueSquishFactor.isElementaryChain_of_isAlmostIso` needs is the length of the coherent
module `f_*𝒪_{X'}/𝒪_X`; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.SubalgebraProducer`. This file proves,
as standalone lemmas with no reference to the glueing/squishing geometry, the facts that those
notes identify as missing.

## Main results

* `Stacks.GlueSquishFactor.isField_of_finite_primeSpectrum` — a finite-type domain over a field
  with only finitely many primes is a field.
* `Stacks.GlueSquishFactor.isClosed_singleton_of_mem_of_isClosed_of_finite` — a point of a
  *finite* closed subset of a Jacobson space is itself closed.
* `Stacks.GlueSquishFactor.isClosed_singleton_of_mem_compl_isoLocus` — **the bad points are
  closed**: if `p : Y ⟶ Spec (.of k)` is locally of finite type and `U` is an open of `Y` with
  finite complement (the shape of data `IsAlmostIsoCore` supplies), every point outside `U` is
  closed.
* `Stacks.GlueSquishFactor.isFiniteLength_stalk_of_isClosed_of_forall_specializes_eq` — the
  stalk of a coherent module at a point `x` of its support has finite length as soon as `x` is a
  closed point and no other point of the support specializes to `x`. This is what finiteness of
  the stalk of `f_*𝒪_{X'}/𝒪_X` at a bad point needs, given that the bad points are closed.

## Implementation notes

`isClosed_singleton_of_mem_compl_isoLocus` does not need `isField_of_finite_primeSpectrum`: a
scheme locally of finite type over a field is a `JacobsonSpace`
(`AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace`, already in Mathlib), and in a Jacobson
space a finite closed set is discrete
(`JacobsonSpace.of_isClosedEmbedding` + the `[Finite X] [JacobsonSpace X] : DiscreteTopology X`
instance), which already makes every point of it closed in the subspace, hence in the ambient
space by `IsClosed.isClosedMap_subtype_val`. `isField_of_finite_primeSpectrum` is kept below as
it is the ring-theoretic statement the source argues from, but the geometric conclusion needed
here is reached more directly through the Jacobson-space route. Neither `IsIso (f.left ∣_ U)`
nor finiteness/quasi-compactness of the morphism is used for closedness of the bad points: only
that `U` is open with finite complement, and that the ambient scheme is locally of finite type
over a field.

## References

* [Stacks Project, Tag 0C1L](https://stacks.math.columbia.edu/tag/0C1L)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.GlueSquishFactor

/-! ### The bad points are closed: the ring-theoretic ingredient -/

/-- **A finite-type domain over a field with finitely many primes is a field.**

The `Spec` of such a domain is irreducible (it is a domain) with finitely many points, hence a
single point once it is known to be Artinian/zero-dimensional; that it is zero-dimensional as
soon as its prime spectrum is finite is
`Stacks.Artinian.ZeroDimFiniteType.solution` ([Stacks, Tag 0ALW]), read off its TFAE packaging
`Algebra.FiniteType.krullDimLE_zero_tfae`. A zero-dimensional domain is a field:
`Ring.KrullDimLE.isField_of_isDomain`. -/
theorem isField_of_finite_primeSpectrum (k A : Type*) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] [Finite (PrimeSpectrum A)] : IsField A := by
  have : Ring.KrullDimLE 0 A :=
    ((Algebra.FiniteType.krullDimLE_zero_tfae k A).out 2 1).mp ‹Finite (PrimeSpectrum A)›
  exact Ring.KrullDimLE.isField_of_isDomain

/-! ### The bad points are closed -/

/-- **A point of a finite closed subset of a Jacobson space is closed.**

The subspace `C` is itself a Jacobson space (`JacobsonSpace.of_isClosedEmbedding`), and a finite
Jacobson space is discrete, so `{y}` is closed in `C`; since `C` is closed in `S`, closed in a
closed subspace is closed in the ambient space. -/
theorem isClosed_singleton_of_mem_of_isClosed_of_finite {S : Type*} [TopologicalSpace S]
    [JacobsonSpace S] {C : Set S} {y : S} (hy : y ∈ C) (hC : IsClosed C) (hCfin : C.Finite) :
    IsClosed ({y} : Set S) := by
  have : JacobsonSpace C := JacobsonSpace.of_isClosedEmbedding hC.isClosedEmbedding_subtypeVal
  have : Finite C := Set.finite_coe_iff.mpr hCfin
  have hsing : IsClosed ({(⟨y, hy⟩ : C)} : Set C) := isClosed_singleton
  simpa using hC.isClosedMap_subtype_val _ hsing

/-- **The bad points of [Stacks, Tag 0C1L] are closed.**

`IsAlmostIsoCore` supplies an open `U` of `Y.left` with finite complement on which `f.left` is
an isomorphism; this is the "finite set of points" the source modifies along. Every point of
that complement is closed: `Y` is a Jacobson space because it is locally of finite type over a
field (`AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace`), and
`isClosed_singleton_of_mem_of_isClosed_of_finite` applies to the closed, finite set `Uᶜ`.

Stated with only the hypotheses this argument uses: neither `IsIso (f.left ∣_ U)` nor any
finiteness/quasi-compactness of a morphism between `X'` and `X` enters, only that `U` is open
with finite complement in a scheme locally of finite type over a field. -/
theorem isClosed_singleton_of_mem_compl_isoLocus {k : Type u} [Field k] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (.of k)) [LocallyOfFiniteType p] {U : Y.Opens}
    (hUfin : Set.Finite ((U : Set Y)ᶜ)) {y : Y} (hy : y ∈ (U : Set Y)ᶜ) :
    IsClosed ({y} : Set Y) :=
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace p
  isClosed_singleton_of_mem_of_isClosed_of_finite hy U.isOpen.isClosed_compl hUfin

/-! ### Finiteness of the stalk at an isolated closed point of the support -/

/-- **An isolated closed point of the support is the generic point of an irreducible component of
it.** If `x` is a closed point of the support of `F`, the support is closed, and no other point
of the support specializes to `x`, then the singleton `{x}` *is* an irreducible component of the
support, and `x` is of course its generic point.

Any closed irreducible subset of the support containing `x` has, by sobriety of `X`, a generic
point `g`, and `g` specializes to `x`, so `huniq` forces `g = x`; since `x` is itself closed,
that subset is `{x}`.

Neither coherence of `F` nor local Noetherianity of `X` is used: closedness of the support is a
hypothesis rather than an instance consequence, which is what lets the same statement serve a
module whose support is finite and discrete for a reason other than coherence. -/
theorem isGenericPoint_component_supp_of_isClosed_of_forall_specializes_eq {X : Scheme.{u}}
    (F : X.Modules) (hFclosed : IsClosed (SheafOfModules.supp F : Set X)) {x : X}
    (hxsupp : x ∈ SheafOfModules.supp F) (hxclosed : IsClosed ({x} : Set X))
    (huniq : ∀ η : X, η ⤳ x → η ∈ SheafOfModules.supp F → η = x) :
    ∃ C : irreducibleComponents (SheafOfModules.supp F : Set X),
      IsGenericPoint x (Subtype.val '' C.1 : Set X) := by
  classical
  obtain ⟨Z, hZmem, hZsub⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible
      ({(⟨x, hxsupp⟩ : (SheafOfModules.supp F : Set X))} : Set (SheafOfModules.supp F : Set X))
      isIrreducible_singleton
  have hxZ : (⟨x, hxsupp⟩ : (SheafOfModules.supp F : Set X)) ∈ Z := hZsub rfl
  have hZirr : IsIrreducible Z := hZmem.1
  have hZclosed : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZmem
  have hCclosed : IsClosed (Subtype.val '' Z : Set X) :=
    hFclosed.isClosedMap_subtype_val Z hZclosed
  have hCirr : IsIrreducible (Subtype.val '' Z : Set X) :=
    hZirr.image Subtype.val continuous_subtype_val.continuousOn
  obtain ⟨g, hg⟩ := QuasiSober.sober hCirr hCclosed
  have hxC : x ∈ (Subtype.val '' Z : Set X) := ⟨⟨x, hxsupp⟩, hxZ, rfl⟩
  have hgC : g ∈ (Subtype.val '' Z : Set X) := by
    rw [← hg.def]; exact subset_closure rfl
  have hgsupp : g ∈ SheafOfModules.supp F := by
    obtain ⟨z, -, rfl⟩ := hgC
    exact z.2
  have hgx : g ⤳ x := by
    rw [specializes_iff_mem_closure, hg.def]; exact hxC
  have hCeq : (Subtype.val '' Z : Set X) = {x} := by
    rw [← hg.def, huniq g hgx hgsupp, hxclosed.closure_eq]
  refine ⟨⟨Z, hZmem⟩, ?_⟩
  rw [isGenericPoint_def, hCeq]
  exact hxclosed.closure_eq

/-- **The stalk of a coherent module is of finite length at a closed point of its support that no
other point of the support specializes to.**

The hypothesis `huniq` makes the singleton `{x}` an irreducible component of the support,
`Stacks.GlueSquishFactor.isGenericPoint_component_supp_of_isClosed_of_forall_specializes_eq`, and
the finite-length conclusion is then
`Stacks.Chow.isFiniteLength_stalk_of_isGenericPoint_component_supp`, [Stacks, Tag 02QW] part (2),
applied at the generic point `x` of that component. -/
@[ega "IV 4.7.7" "special case"]
theorem isFiniteLength_stalk_of_isClosed_of_forall_specializes_eq {X : Scheme.{u}}
    [IsLocallyNoetherian X] (F : X.Modules) [F.IsCoherent] {x : X}
    (hxsupp : x ∈ SheafOfModules.supp F) (hxclosed : IsClosed ({x} : Set X))
    (huniq : ∀ η : X, η ⤳ x → η ∈ SheafOfModules.supp F → η = x) :
    IsFiniteLength (X.presheaf.stalk x) (F.presheaf.stalk x) := by
  have := Stacks.Chow.isFiniteType_of_isCoherent F
  obtain ⟨C, hC⟩ := isGenericPoint_component_supp_of_isClosed_of_forall_specializes_eq F
    (SheafOfModules.isClosed_supp F) hxsupp hxclosed huniq
  exact Stacks.Chow.isFiniteLength_stalk_of_isGenericPoint_component_supp F C x hC

end Stacks.GlueSquishFactor

end
