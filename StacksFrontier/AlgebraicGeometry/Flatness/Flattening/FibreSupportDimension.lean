module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent
public import StacksFrontier.AlgebraicGeometry.DevissageNoetherian.Support
public import StacksFrontier.AlgebraicGeometry.FiniteTypeSubmodule.KernelGlue
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.ElementaryDevissage
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.OneStep.FreeMap
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Bounded
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Functoriality
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.PullbackSkyscraper
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The induction variable of the Raynaud–Gruson flattening theorem

The proof of [Stacks, Tag 0815] is an induction on

  `max_{s ∈ S} dim Supp(ℱ_s)`,

the largest dimension of the support of a fibre of the module `ℱ` being flattened. This module
introduces that quantity, in the form in which an induction can consume it — a natural number
`n` with `dim Supp(ℱ_s) < n` for every `s` — and proves the two facts about it that the
induction turns on: the base case, and the two ways the Stacks proof makes the number drop.

**The variable exists.** `AlgebraicGeometry.exists_topologicalKrullDim_supp_fiber_lt` produces
the bound. It is the support bound of [Stacks, Tag 0A3V]
(`AlgebraicGeometry.exists_topologicalKrullDim_fiber_le`, which bounds the whole fibre) cut down
to the support, which is a subspace of the fibre.

**The base case.** `n = 0` says every fibre support is empty, hence so is the support of `ℱ`
itself, and a module with empty support is flat over anything:
`AlgebraicGeometry.isFlatOver_of_topologicalKrullDim_supp_fiber_lt_zero`. So the induction never
has to appeal to a blowup at the bottom.

**The drop.** The Stacks proof lowers the variable in two places, and each is a corollary of the
one elementary fact that a proper closed subset of an irreducible finite-dimensional space has
strictly smaller dimension (`AlgebraicGeometry.topologicalKrullDim_supp_lt_of_notMem`):

* at an elementary dévissage (`AlgebraicGeometry.ElementaryDevissage`, [Stacks, Tag 057S]), whose
  relative dimension `D.n` is the *local* dimension of the fibre support at the chosen point and
  so is below the global bound — `AlgebraicGeometry.ElementaryDevissage.dimension_lt`;
* at the cokernel of a map which is an isomorphism on an open meeting every fibre, where the
  fibre support misses the generic point of each fibre —
  `AlgebraicGeometry.topologicalKrullDim_supp_fiber_lt_of_disjoint_surjective_open` and its
  cokernel form `AlgebraicGeometry.topologicalKrullDim_supp_cokernel_fiber_lt`.

## Main results

* `AlgebraicGeometry.exists_topologicalKrullDim_supp_fiber_lt`: **the induction variable of
  [Stacks, Tag 0815]** exists.
* `AlgebraicGeometry.isFlatOverAt_of_notMem_supp`: a module is flat over the base at a point
  outside its support.
* `AlgebraicGeometry.isFlatOver_of_topologicalKrullDim_supp_fiber_lt_zero`: **the base case** of
  the induction.
* `AlgebraicGeometry.ElementaryDevissage.dimension_lt`: **the dimension drop at a dévissage.**
* `AlgebraicGeometry.topologicalKrullDim_supp_fiber_lt_of_disjoint_surjective_open`: **the
  dimension drop off a fibrewise-surjective open**, and
  `AlgebraicGeometry.topologicalKrullDim_supp_cokernel_fiber_lt`: **the dimension drop at a
  cokernel**, which is the form the Stacks proof applies it in.

## Implementation notes

The fibre module is `(Scheme.Modules.pullback (f.fiberι s)).obj ℱ`, the pullback of `ℱ` to the
scheme-theoretic fibre, and its support is computed by [Stacks, Tag 056J]
(`Stacks.Modules.supp_pullback`) as the preimage of the support of `ℱ`. That is what makes the
base case work: emptiness of every fibre support is emptiness of the support, because the fibres
cover the source.

The dimension drop needs the fibres irreducible, which is why
`AlgebraicGeometry.topologicalKrullDim_supp_fiber_lt_of_disjoint_surjective_open` carries
`∀ s, IrreducibleSpace (f.fiber s)`; in the application `f` is a smooth morphism with
geometrically integral fibres, where that instance is available.

`AlgebraicGeometry.dim_support_cokernel_fiber_lt` ([Stacks, Tag 05HF]) is the same dimension drop
for the cokernel of a map into the direct image of a one-step dévissage, where the drop is read
against the dimension of the fibre support rather than against a global bound; the two share the
elementary fact but neither specializes to the other.

## References

* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
* [Stacks Project, Tag 0A3V](https://stacks.math.columbia.edu/tag/0A3V)
* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
* [Stacks Project, Tag 057S](https://stacks.math.columbia.edu/tag/057S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### The induction variable -/

/-- **The induction variable of [Stacks, Tag 0815] exists.** For a finite-type morphism to a
quasi-compact base there is a single natural number strictly above the dimension of the support
of every fibre of a module on the source.

This is [Stacks, Tag 0A3V] (`AlgebraicGeometry.exists_topologicalKrullDim_fiber_le`), which
bounds the dimensions of the fibres themselves, read on the subspace `Supp ℱ_s ⊆ f⁻¹(s)`. The
bound is taken strict so that the induction can be run on `n` with the hypothesis
`dim Supp ℱ_s < n`, whose `n = 0` case is the vacuous one. -/
@[sga "4 XVII 5.1.4" "more general"]
theorem exists_topologicalKrullDim_supp_fiber_lt {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] [CompactSpace S] (F : X.Modules) :
    ∃ n : ℕ, ∀ s : S, topologicalKrullDim
      (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj F)) < n := by
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_fiber_le f
  refine ⟨n + 1, fun s ↦ lt_of_le_of_lt
    ((topologicalKrullDim_subspace_le (f.fiber s) _).trans (hn s)) ?_⟩
  exact_mod_cast Nat.lt_succ_self n

/-! ### The base case -/

/-- **A module is flat over the base at a point outside its support.** The stalk there is zero,
and the zero module is flat. -/
theorem isFlatOverAt_of_notMem_supp {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (x : X)
    (hx : x ∉ SheafOfModules.supp F) :
    IsFlatOverAt f.toLRSHom.toShHom F x := by
  have : Subsingleton (F.presheaf.stalk x) :=
    not_nontrivial_iff_subsingleton.mp fun _ ↦
      let ⟨a, ha⟩ := exists_ne (0 : F.presheaf.stalk x)
      hx ⟨a, ha⟩
  let _ : Module (S.presheaf.stalk (f x)) (F.presheaf.stalk x) :=
    Module.compHom _ (f.stalkMap x).hom
  change Module.Flat (S.presheaf.stalk (f x)) (F.presheaf.stalk x)
  infer_instance

/-- **The base case of the induction of [Stacks, Tag 0815].** If the support of every fibre of
`ℱ` has dimension `< 0` — that is, if every fibre support is empty — then `ℱ` is already flat
over the base, so no blowup is needed.

A point of the support of `ℱ` would give a point of the support of the fibre module through
[Stacks, Tag 056J], and a nonempty space has Krull dimension at least `0`. -/
theorem isFlatOver_of_topologicalKrullDim_supp_fiber_lt_zero {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) [F.IsFiniteType]
    (hdim : ∀ s : S, topologicalKrullDim
      (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj F)) < 0) :
    IsFlatOver f.toLRSHom.toShHom F := by
  intro x
  refine isFlatOverAt_of_notMem_supp f F x fun hx ↦ ?_
  have hx' : f.asFiber x ∈
      SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F) := by
    rw [Stacks.Modules.supp_pullback]
    simpa using hx
  have : Nonempty (IrreducibleCloseds
      (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F))) :=
    ⟨⟨closure {(⟨f.asFiber x, hx'⟩ : _)}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  exact absurd (hdim (f x)) (not_lt_of_ge (Order.krullDim_nonneg))

/-! ### The dimension drop -/

/-- **The dimension drop at an elementary dévissage.** The relative dimension `D.n` of the smooth
morphism of an elementary dévissage ([Stacks, Tag 057S]) is the *local* dimension of the fibre
support at the chosen point, so it is below any bound for the *global* dimension of that
support. This is what makes the dévissage step of [Stacks, Tag 0815] a descent of the
induction variable. -/
theorem ElementaryDevissage.dimension_lt {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (x : X)
    (hx : f.asFiber x ∈
      SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F))
    (D : ElementaryDevissage f F x hx) {n : ℕ}
    (hdim : topologicalKrullDim
      (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F)) < n) :
    D.n < n := by
  have hle := topologicalKrullDimAt_le_topologicalKrullDim
    (X := SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F))
    ⟨f.asFiber x, hx⟩
  rw [D.dimension] at hle
  exact_mod_cast lt_of_le_of_lt hle hdim

/-- The generic point of every fibre of `f` lies in an open subset of the source which surjects
onto the base. Indeed the open subset meets the fibre, and a nonempty open subset of an
irreducible space contains its generic point. -/
theorem genericPoint_mem_open_of_surjective_on_base {X S : Scheme.{u}} (f : X ⟶ S)
    [∀ s : S, IrreducibleSpace (f.fiber s)] (V : X.Opens)
    (hV : Function.Surjective (V.ι ≫ f).base) (s : S) :
    f.fiberι s (genericPoint (f.fiber s)) ∈ V := by
  obtain ⟨v, hv⟩ := hV s
  change f (V.ι v) = s at hv
  subst s
  have hv' : f.asFiber (V.ι v) ∈ (f.fiberι (f (V.ι v))) ⁻¹' (V : Set X) := by
    change f.fiberι (f (V.ι v)) (f.asFiber (V.ι v)) ∈ V
    rw [f.fiberι_asFiber]
    exact v.2
  have hopen : IsOpen ((f.fiberι (f (V.ι v))) ⁻¹' (V : Set X)) :=
    V.2.preimage (f.fiberι (f (V.ι v))).continuous
  exact (IsGenericPoint.mem_open_set_iff
    (genericPoint_spec (f.fiber (f (V.ι v)))) hopen).2
    ⟨f.asFiber (V.ι v), by simpa using hv'⟩

/-- **The dimension drop off a fibrewise-surjective open.** If the support of `ℱ` is disjoint
from an open subset `V` of the source which surjects onto the base, then the dimension of each
fibre support is *strictly* below any bound for the dimensions of the fibres themselves: the
generic point of the fibre lies in `V`, hence outside the fibre support, which is therefore a
proper closed subset of the irreducible fibre.

This is how the Stacks proof of [Stacks, Tag 0815] lowers the induction variable after replacing
`ℱ` by the cokernel of a map that is an isomorphism over `V`. -/
theorem topologicalKrullDim_supp_fiber_lt_of_disjoint_surjective_open {X S : Scheme.{u}}
    (f : X ⟶ S) [∀ s : S, IrreducibleSpace (f.fiber s)] (F : X.Modules) [F.IsFiniteType]
    (V : X.Opens) (hV : Function.Surjective (V.ι ≫ f).base)
    (hFV : Disjoint (SheafOfModules.supp F) (V : Set X)) {n : ℕ}
    (hdim : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ n) :
    ∀ s : S, topologicalKrullDim
      (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj F)) < n := by
  intro s
  have _ : ((Scheme.Modules.pullback (f.fiberι s)).obj F).IsFiniteType :=
    SheafOfModules.pullback_isFiniteType (f.fiberι s).toLRSHom.toShHom F
  have hmiss : genericPoint (f.fiber s) ∉
      SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj F) := by
    rw [Stacks.Modules.supp_pullback]
    exact fun hmem ↦ Set.disjoint_left.mp hFV hmem
      (genericPoint_mem_open_of_surjective_on_base f V hV s)
  have hfin : topologicalKrullDim (f.fiber s) ≠ ⊤ :=
    ne_top_of_le_ne_top (fun he ↦ ENat.natCast_ne_top n (WithBot.coe_eq_coe.mp he)) (hdim s)
  exact lt_of_lt_of_le (topologicalKrullDim_supp_lt_of_notMem hfin _ hmiss) (hdim s)

/-- A module whose pullback to an open subset is zero has support disjoint from that open
subset, by [Stacks, Tag 056J]. -/
theorem disjoint_supp_of_isZero_pullback_open {X : Scheme.{u}} (F : X.Modules) [F.IsFiniteType]
    (V : X.Opens) (hV : IsZero ((Scheme.Modules.pullback V.ι).obj F)) :
    Disjoint (SheafOfModules.supp F) (V : Set X) := by
  rw [Set.disjoint_left]
  intro x hx hxV
  have h := SheafOfModules.supp_eq_empty_of_isZero hV
  rw [Stacks.Modules.supp_pullback] at h
  have hx' : (⟨x, hxV⟩ : V) ∈ V.ι ⁻¹' SheafOfModules.supp F := hx
  rw [h] at hx'
  exact hx'

/-- **The dimension drop at a cokernel.** If `α : 𝒢 ⟶ ℱ` becomes an isomorphism on an open
subset `V` of the source which surjects onto the base, then the fibre supports of `coker α` have
dimension strictly below any bound for the dimensions of the fibres.

This is the form in which [Stacks, Tag 0815] lowers its induction variable: having arranged, over
a neighbourhood of the generic point of each fibre, a map from a finite free module which is an
isomorphism there, the proof passes to the cokernel, whose fibre supports have dropped. -/
theorem topologicalKrullDim_supp_cokernel_fiber_lt {X S : Scheme.{u}} (f : X ⟶ S)
    [∀ s : S, IrreducibleSpace (f.fiber s)] {G F : X.Modules} [F.IsFiniteType] (α : G ⟶ F)
    (V : X.Opens) (hV : Function.Surjective (V.ι ≫ f).base)
    (hα : IsIso ((Scheme.Modules.pullback V.ι).map α)) {n : ℕ}
    (hdim : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ n) :
    ∀ s : S, topologicalKrullDim
      (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj (cokernel α))) < n := by
  have hepi : Epi (cokernel.π α) := inferInstance
  have _ : (cokernel α).IsFiniteType :=
    @Stacks.SheafOfModules.isFiniteType_of_epi'.{u} _ _ _ _ _ _ _ _ _ (cokernel.π α)
      inferInstance hepi
  have _ := hα
  have hzero : IsZero ((Scheme.Modules.pullback V.ι).obj (cokernel α)) :=
    (Stacks.AlgebraicGeometry.FiniteTypeSubmodule.isZero_cokernel_of_epi
      ((Scheme.Modules.pullback V.ι).map α)).of_iso
      (PreservesCokernel.iso (Scheme.Modules.pullback V.ι) α)
  exact topologicalKrullDim_supp_fiber_lt_of_disjoint_surjective_open f (cokernel α) V hV
    (disjoint_supp_of_isZero_pullback_open _ V hzero) hdim

end AlgebraicGeometry

end
