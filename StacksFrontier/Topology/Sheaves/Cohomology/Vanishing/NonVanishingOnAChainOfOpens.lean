module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Topology.Order.UpperLowerSetTopology
public import Mathlib.Topology.QuasiSeparated
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.Topology.Spectral.Prespectral
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyAtTheTerminalObject
public import StacksFrontier.Topology.Sheaves.Cohomology.AbelianFilteredColimits.NativeLongExactSequence
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.FlasqueAbelianSheavesAreAcyclic
public import StacksFrontier.Topology.Sheaves.Cohomology.SpectralLimitVertex.BaseChangeToTheLimit
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.IrreducibleSpaces
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ExtensionByZero
public import StacksFrontier.Topology.Sheaves.Sheaf.ConstantIntegerSubsheaves
import StacksCore.Tactic.StacksAttribute

/-!
# Nonvanishing cohomology on a space whose opens form a chain

Let `X` be the set of natural numbers with the topology whose opens are `∅`, `X` and
`U_n = {i | i ≤ n}`. An abelian sheaf `ℱ` on `X` is the same thing as an inverse system of
abelian groups `A_n = ℱ(U_n)`, and `Γ(X, ℱ) = lim A_n`. The inverse limit functor is not right
exact on inverse systems — the reduction `ℤ ⟶ lim ℤ/2ⁿℤ` misses `1 + 4 + 4² + ⋯` — so there is
an abelian sheaf on `X` with nonzero `H¹`. Since `X` has a basis of quasi-compact opens whose
pairwise intersections are quasi-compact, this is [Stacks, Tag 0BX0]: conditions (2), (3) and
(4) of [Stacks, Tag 02UX] do not imply its conclusion, the missing hypothesis being
quasi-compactness of `X`, which fails here. All three conditions are proved below. Condition (4),
the vanishing `H^p(X, j_!ℤ_U) = 0` for `p ≥ 1` over a quasi-compact open `U`, is proved inside the
inverse-system description of sheaves on `X`: for `U = U_n` the extension by zero is the kernel of
the reduction of the constant sheaf `ℤ` onto the system which is `0` up to `n` and `ℤ` above, and
both outer terms of that short exact sequence are flasque.

## Main definitions

* `Stacks.CohomologyVanishing.ChainOfOpens.Chain`: the space, `ℕ` with the lower-set topology.
* `Stacks.CohomologyVanishing.ChainOfOpens.basicOpen`: the open `U_n = {i | i ≤ n}`.
* `Stacks.CohomologyVanishing.ChainOfOpens.towerSheaf`: the abelian sheaf attached to an inverse
  system of abelian groups, with `towerSections` its groups of sections.
* `Stacks.CohomologyVanishing.ChainOfOpens.sheafTower`: the inverse system `n ↦ ℱ(U_n)` attached
  to an abelian sheaf.
* `Stacks.CohomologyVanishing.ChainOfOpens.nonVanishingSheaf`: the sheaf with nonzero `H¹`.
* `Stacks.CohomologyVanishing.ChainOfOpens.cotruncTower`: the inverse system which is the zero
  group in degrees `≤ n` and `ℤ` above, realised as `k ↦ ℤ/cotruncMod n k`, with
  `cotruncProjection` the reduction of the constant system `ℤ` onto it.
* `Stacks.CohomologyVanishing.ChainOfOpens.cotruncSequence`: the short exact sequence
  `0 ⟶ 𝒦ₙ ⟶ ℤ ⟶ Cₙ ⟶ 0` through which condition (4) of [Stacks, Tag 02UX] is proved.
* `Stacks.CohomologyVanishing.ChainOfOpens.kerTower`: the inverse system of the kernels of the
  reductions, realised as the subgroups `cotruncKer n k` of `ℤ` with the inclusions for transition
  maps; its sheaf is `𝒦ₙ` (`kerSheafIso`).
* `Stacks.CohomologyVanishing.ChainOfOpens.basicOpenSpace`: the basic open `U_n` as a space, on
  which the constant sheaf `ℤ_{U_n}` of condition (4) lives.

## Main results

* `Stacks.CohomologyVanishing.ChainOfOpens.eq_bot_or_eq_top_or_eq_basicOpen`: the opens are
  exactly `∅`, `X` and the `U_n`.
* `Stacks.CohomologyVanishing.ChainOfOpens.bijective_towerComparison_app` and
  `globalSectionsAddEquiv`: an abelian sheaf is its inverse system of sections over the `U_n`,
  and `Γ(X, ℱ) = lim ℱ(U_n)`.
* `Stacks.CohomologyVanishing.ChainOfOpens.hasBasisOfCompactOpens_chain`,
  `interCompactOpenIsCompact_chain`, `not_isCompact_univ`: conditions (2) and (3) of
  [Stacks, Tag 02UX] hold, condition (1) fails.
* `Stacks.CohomologyVanishing.ChainOfOpens.not_surjective_dyadicProjection_app_top`: the failure
  of right exactness of `lim` on inverse systems, in the form `ℤ ⟶ lim ℤ/2ⁿℤ` not surjective.
* `Stacks.CohomologyVanishing.ChainOfOpens.exists_not_subsingleton_sheafH_one`:
  **[Stacks, Tag 0BX0]**, an abelian sheaf on `X` with nonzero `H¹`.
* `Stacks.CohomologyVanishing.ChainOfOpens.eq_top_of_mem_grothendieckTopology`,
  `surjective_app_basicOpen_of_epi`, `bijective_toSheafify_app_basicOpen`: a basic open is a
  *local* object of the site of opens — its only covering sieve is the maximal one — so an
  epimorphism of abelian sheaves is honestly surjective on sections over it and sheafification
  does not change the sections of a presheaf over it.
* `Stacks.CohomologyVanishing.ChainOfOpens.subsingleton_sheafH_constantSheaf_chain`: the higher
  cohomology of a constant abelian sheaf on `Chain` vanishes, `Chain` being irreducible
  ([Stacks, Tag 02UW]).
* `Stacks.CohomologyVanishing.ChainOfOpens.isFlasque_towerSheaf_of_const`: the sheaf of an
  inverse system which is a levelwise quotient of a constant system is flasque on `Chain`; hence
  `isFlasque_towerSheaf_constIntTower` and `isFlasque_towerSheaf_cotruncTower`.
* `Stacks.CohomologyVanishing.ChainOfOpens.surjective_towerPresheafMap_cotruncProjection_app_top`:
  the reduction `ℤ ⟶ Cₙ` *is* surjective on global sections — the point at which `Cₙ` differs
  from the inverse system `(ℤ/2ⁿℤ)ₙ` of the counterexample, for which the same map is not
  surjective (`not_surjective_dyadicProjection_app_top`).
* `Stacks.CohomologyVanishing.ChainOfOpens.subsingleton_sheafH_cotruncSequence_X₁`: **condition
  (4) of [Stacks, Tag 02UX] over `Chain`, in the inverse-system spelling** — `Hᵖ(X, 𝒦ₙ) = 0` for
  every `p > 0`.
* `Stacks.CohomologyVanishing.ChainOfOpens.integerExtensionByZeroIsoKernel`: the extension by
  zero `j_!ℤ_{U n}` is the kernel `𝒦ₙ`, through
  `Stacks.CohomologyVanishing.ChainOfOpens.integerConstantSheafIsoRestrict` (the restriction of
  `𝒦ₙ` to `U n` is the constant sheaf `ℤ` there) and
  `Stacks.CohomologyVanishing.ChainOfOpens.isZero_stalk_cotruncSequence_X₁` (its stalks vanish off
  `U n`).
* `Stacks.CohomologyVanishing.ChainOfOpens.subsingleton_sheafH_integerExtensionByZero`:
  **condition (4) of [Stacks, Tag 02UX] over `Chain` in the `j_!ℤ_U` spelling of this
  repository's own Tag 02UX** — `Hᵖ(X, j_!ℤ_U) = 0` for every `p > 0` and every quasi-compact
  open `U`; the degenerate case `U = ∅` is
  `subsingleton_sheafH_integerExtensionByZero_bot`.

## Implementation notes

The space is `Topology.WithLowerSet (ULift.{u} ℕ)`: the lower sets of `ℕ` are exactly `∅`, the
initial segments `{i | i ≤ n}` and `ℕ`, so this is the source's space (under the shift
`i ↦ i + 1`, which matches the source's indexing of `U_n` by `n ≥ 1`). The `ULift` keeps the
coefficients in `AddCommGrpCat.{u}`, the universe at which the surrounding vanishing theorems are
stated.

Sections of the sheaf of an inverse system `A` over an open `W` are the compatible families
`(s_n)` indexed by the `n` with `U_n ⊆ W`; this is a limit over a sieve written out by hand, and
it makes the sheaf condition the observation that a basic open contained in a union of opens is
contained in one of them, because the opens are lower sets.

The nonvanishing is obtained from the long exact sequence of
`0 ⟶ 𝒦 ⟶ ℤ ⟶ (ℤ/2ⁿℤ)ₙ ⟶ 0`, with `𝒦` the kernel of the reduction: were `H¹(X, 𝒦)` zero, then
`Γ(X, ℤ) ⟶ Γ(X, (ℤ/2ⁿℤ)ₙ)` would be surjective. The reduction of sheaves is an epimorphism
because it is locally surjective, which is where the shape of the topology enters: every point
has a smallest open neighbourhood, over which the reduction `ℤ ⟶ ℤ/2ⁿℤ` is surjective.

The source also asserts condition (4) of [Stacks, Tag 02UX], the vanishing
`H^p(X, j_!ℤ_U) = 0` for `p ≥ 1` over a quasi-compact open `U`, and leaves it to the reader. In
the spelling of this repository's own Tag 02UX
(`Stacks.CohomologyVanishing.IsZeroIntegerExtensions`, and the hypothesis `hvanish` of
`Stacks.CohomologyVanishing.subsingleton_sheafH_of_subsingleton_sheafH_integerExtensionByZero`)
it reads

```
∀ (U : Opens Chain.{u}), IsCompact (U : Set Chain.{u}) → ∀ p : ℕ, 0 < p →
  Subsingleton (Sheaf.H.{u, u, u, u}
    (Stacks.Sheaves.ConstantIntegerSubsheaves.integerExtensionByZero chainSpace.{u} U) p)
```

and `subsingleton_sheafH_integerExtensionByZero` proves exactly that. The quasi-compact opens of
`Chain` are exactly `∅` and the `U n` (`finite_of_isCompact`, `finite_basicOpen`,
`eq_bot_or_eq_top_or_eq_basicOpen` and `not_isCompact_univ`); over `∅` the sheaf is zero, and over
`U n` the extension by zero is identified with the kernel `𝒦ₙ` of
`towerSheafMap (cotruncProjection n)` by `integerExtensionByZeroIsoKernel`.

That identification is *not* obtained by computing the sections of `j_!ℤ_{U n}` over the basic
opens. It uses instead the description of the essential image of `j_!` ([Stacks, Tag 00A9],
`ExtensionByZero.jExt_counit_isIso_of_vanishing`): a sheaf whose stalks vanish off `U n` is the
extension by zero of its own restriction to `U n`. The stalks of `𝒦ₙ` vanish off `U n` because the
smallest open neighbourhood of a point above `n` is a basic open, over which `𝒦ₙ` has no nonzero
section; and the restriction of `𝒦ₙ` to `U n` is the constant sheaf `ℤ` of the space `U n` because
`U n` is irreducible, so that constant sheaf is the explicit model of [Stacks, Tag 02UW]
(`Stacks.CohomologyVanishing.constantSheafIsoIrreducibleModel`), which is compared with the
sections of `𝒦ₙ` over the image opens directly. The sections of `𝒦ₙ` themselves are reached
through `kerTower n`: the universal property of the kernel gives a comparison
`towerSheaf (kerTower n) ⟶ 𝒦ₙ`, a monomorphism because its composite with `𝒦ₙ ⟶ ℤ` is one and an
epimorphism because it is locally surjective, the opens of `Chain` having a smallest
neighbourhood at each point.

The route taken to condition (4) is **not** the one through the closed complement `Z` of `U n`
and the sequence `0 ⟶ j_!ℤ_{U n} ⟶ ℤ_X ⟶ i_*ℤ_Z ⟶ 0` of
`Stacks.Sheaf.canonicalComplementSequence_shortExact`. Everything is done instead inside the
inverse-system description of sheaves on `Chain`, where `ℤ_X` and the quotient are both sheaves
of towers: `cotruncSequence n` is `0 ⟶ 𝒦ₙ ⟶ ℤ ⟶ Cₙ ⟶ 0` with `Cₙ` the sheaf of `cotruncTower n`,
both outer terms are flasque by `isFlasque_towerSheaf_of_const`, and the degree-one end of the
long exact sequence — the surjectivity of `Γ(X, ℤ) ⟶ Γ(X, Cₙ)` — is
`surjective_towerPresheafMap_cotruncProjection_app_top`. That surjectivity is where `Cₙ` differs
from the inverse system `(ℤ/2ⁿℤ)ₙ` of the counterexample above: a compatible family for `Cₙ` over
the whole space is constant in the degrees above `n`, where the transition maps are the identity
of `ℤ`, so a single integer produces it.

Two notes on the surrounding library, found while doing this.
`Stacks.Cohomology.FlasqueAbelian.subsingleton_sheafH_of_isFlasque` cannot be used here, and has
no consumer anywhere in the repository: it pins the two `HasDerivedCategory` universes to `u`,
whereas `HasDerivedCategory.standard` supplies them at `max u (u+1)`. The usable form is
`isZero_rightDerived_abSections_of_isFlasque`, whose derived-category universes are free; it is
what `isZero_H'functor_of_isFlasque` below calls, transported to native cohomology along
`nonempty_H'functor_iso_rightDerived`. Its `HasRightDerivedFunctor` hypothesis has to be supplied
by name — through `HasPointwiseRightDerivedFunctor` — because as one composite instance goal its
search exhausts the `synthInstance` budget.

## References

* [Stacks Project, Tag 0BX0](https://stacks.math.columbia.edu/tag/0BX0)
* [Stacks Project, Tag 02UW](https://stacks.math.columbia.edu/tag/02UW)
* [Stacks Project, Tag 02UX](https://stacks.math.columbia.edu/tag/02UX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.CohomologyVanishing.ChainOfOpens

/-- The set of natural numbers with the topology whose open sets are the lower sets, that is
`∅`, the sets `{i | i ≤ n}` for `n : ℕ`, and the whole space. -/
abbrev Chain : Type u := Topology.WithLowerSet (ULift.{u} ℕ)

/-- The open subset `{i | i ≤ n}` of `Chain`. -/
def basicOpen (n : ℕ) : Opens Chain.{u} :=
  ⟨Set.Iic (ULift.up n), Topology.IsLowerSet.isOpen_iff_isLowerSet.2 (isLowerSet_Iic _)⟩

/-- A point `x` of `Chain` lies in `basicOpen n` if and only if `x ≤ n`. -/
@[simp]
lemma mem_basicOpen {n : ℕ} {x : Chain.{u}} : x ∈ basicOpen.{u} n ↔ x.down ≤ n := Iff.rfl

/-- Every point `x` of `Chain` lies in the basic open `basicOpen x`. -/
lemma self_mem_basicOpen (x : Chain.{u}) : x ∈ basicOpen.{u} x.down :=
  mem_basicOpen.2 (le_refl x.down)

/-- The basic open `basicOpen m` is contained in `basicOpen n` if and only if `m ≤ n`. -/
lemma basicOpen_le_basicOpen_iff {m n : ℕ} :
    basicOpen.{u} m ≤ basicOpen.{u} n ↔ m ≤ n :=
  ⟨fun h => h (mem_basicOpen.2 (le_refl m)), fun h _ hx => le_trans hx h⟩

/-- The map `n ↦ basicOpen n` is monotone. -/
lemma monotone_basicOpen : Monotone (basicOpen.{u}) :=
  fun _ _ h => basicOpen_le_basicOpen_iff.2 h

/-- Every point of an open subset of `Chain` has a basic open neighbourhood inside it: the opens
of `Chain` are lower sets. -/
lemma basicOpen_le_of_mem {W : Opens Chain.{u}} {x : Chain.{u}} (hx : x ∈ W) :
    basicOpen.{u} x.down ≤ W :=
  fun _ hy => (Topology.IsLowerSet.isOpen_iff_isLowerSet.1 W.isOpen) hy hx

/-- The basic opens cover `Chain`. -/
lemma iSup_basicOpen : (⨆ n : ULift.{u} ℕ, basicOpen.{u} n.down) = ⊤ :=
  le_antisymm le_top fun x _ => Opens.mem_iSup.2 ⟨x, self_mem_basicOpen x⟩

/-- **The opens of `Chain` are exactly `∅`, the whole space, and the sets `{i | i ≤ n}`.** -/
@[stacks 0BX0 "the lattice of opens of the space: ∅, X and the U_n"]
lemma eq_bot_or_eq_top_or_eq_basicOpen (W : Opens Chain.{u}) :
    W = ⊥ ∨ W = ⊤ ∨ ∃ n, W = basicOpen.{u} n := by
  classical
  by_cases htop : ∀ x : Chain.{u}, x ∈ W
  · exact Or.inr (Or.inl (Opens.ext (Set.eq_univ_of_forall htop)))
  simp only [not_forall] at htop
  obtain ⟨y, hy⟩ := htop
  have hex : ∃ k : ℕ, (ULift.up.{u} k : Chain.{u}) ∉ W := ⟨y.down, hy⟩
  have hmem_iff : ∀ x : Chain.{u}, x ∈ W ↔ x.down < Nat.find hex := by
    intro x
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · by_contra hcon
      exact Nat.find_spec hex
        ((Topology.IsLowerSet.isOpen_iff_isLowerSet.1 W.isOpen) (Nat.not_lt.1 hcon) hx)
    · by_contra h
      exact absurd hx (Nat.not_lt.2 (Nat.find_min' hex h))
  rcases Nat.eq_zero_or_pos (Nat.find hex) with hk0 | hk0
  · refine Or.inl (Opens.ext (Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_))
    exact absurd ((hmem_iff x).1 hx) (by omega)
  · refine Or.inr (Or.inr ⟨Nat.find hex - 1, Opens.ext (Set.ext fun x => ?_)⟩)
    change x ∈ W ↔ x.down ≤ Nat.find hex - 1
    exact (hmem_iff x).trans (by omega)

/-! ### A basis of quasi-compact opens, and the failure of quasi-compactness -/

/-- A basic open of `Chain` is a finite set. -/
lemma finite_basicOpen (n : ℕ) : (basicOpen.{u} n : Set Chain.{u}).Finite := by
  refine Set.Finite.subset ((Set.finite_Iic n).image ULift.up) fun x hx => ?_
  exact ⟨x.down, hx, rfl⟩

/-- A quasi-compact open of `Chain` is finite: it is covered by the basic opens of its points,
and a finite subcover is contained in a single basic open. -/
lemma finite_of_isCompact {V : Set Chain.{u}} (hV : IsCompact V) : V.Finite := by
  obtain ⟨t, ht⟩ := hV.elim_finite_subcover
    (fun x : Chain.{u} => (basicOpen.{u} x.down : Set Chain.{u}))
    (fun x => (basicOpen.{u} x.down).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, self_mem_basicOpen x⟩)
  refine Set.Finite.subset (finite_basicOpen.{u} (t.sup fun x => x.down)) fun x hx => ?_
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht hx)
  exact le_trans hxy (Finset.le_sup (f := fun x : Chain.{u} => x.down) hy)

/-- `Chain` is not quasi-compact: the chain of basic opens is an open cover with no finite
subcover. -/
lemma not_isCompact_univ : ¬ IsCompact (Set.univ : Set Chain.{u}) := by
  intro h
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => (ULift.up n : Chain.{u})) (fun a b hab => by simpa using hab)
    (fun _ => Set.mem_univ _) (finite_of_isCompact h)

/-! ### Abelian sheaves on `Chain` are inverse systems of abelian groups -/

/-- The space `Chain` as an object of `TopCat`. -/
abbrev chainSpace : TopCat.{u} := TopCat.of Chain.{u}

/-- If a basic open is contained in a union of opens, it is contained in one of them. -/
lemma exists_basicOpen_le_of_le_iSup {ι : Type*} (V : ι → Opens Chain.{u}) {n : ℕ}
    (h : basicOpen.{u} n ≤ ⨆ i, V i) : ∃ i, basicOpen.{u} n ≤ V i := by
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (h (self_mem_basicOpen (ULift.up n)))
  exact ⟨i, basicOpen_le_of_mem hi⟩

section Tower

variable (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u})

/-- The transition map `Aₙ ⟶ Aₘ` of an inverse system of abelian groups, for `m ≤ n`. -/
abbrev trans {m n : ℕ} (h : m ≤ n) : A.obj (op n) ⟶ A.obj (op m) := A.map (homOfLE h).op

/-- The indices of the basic opens contained in `W`. -/
abbrev Index (W : Opens Chain.{u}) : Type := {n : ℕ // basicOpen.{u} n ≤ W}

/-- The compatible families of elements of `A` indexed by the basic opens contained in `W`.
This is the group of sections over `W` of the sheaf attached to the inverse system `A`. -/
def towerSections (W : Opens Chain.{u}) : AddSubgroup (∀ n : Index.{u} W, A.obj (op n.1)) where
  carrier := {s | ∀ (m n : Index.{u} W) (h : m.1 ≤ n.1), trans A h (s n) = s m}
  add_mem' {s t} hs ht m n h := by
    change trans A h (s n + t n) = s m + t m
    rw [map_add, hs m n h, ht m n h]
  zero_mem' m n h := by
    change trans A h 0 = 0
    rw [map_zero]
  neg_mem' {s} hs m n h := by
    change trans A h (-s n) = -s m
    rw [map_neg, hs m n h]

/-- The presheaf of compatible families attached to an inverse system of abelian groups. -/
def towerPresheaf : (Opens Chain.{u})ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj W := AddCommGrpCat.of (towerSections A W.unop)
  map {_ _} f := AddCommGrpCat.ofHom
    { toFun := fun s => ⟨fun n => s.1 ⟨n.1, le_trans n.2 (leOfHom f.unop)⟩,
        fun m n h => s.2 ⟨m.1, _⟩ ⟨n.1, _⟩ h⟩
      map_zero' := rfl
      map_add' _ _ := rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The restriction maps of `towerPresheaf A` act on a compatible family by restricting its index
set. -/
@[simp]
lemma towerPresheaf_map_apply_coe {W W' : (Opens Chain.{u})ᵒᵖ} (f : W ⟶ W')
    (s : towerSections A W.unop) (n : Index.{u} W'.unop) :
    (((towerPresheaf A).map f) s).1 n = s.1 ⟨n.1, le_trans n.2 (leOfHom f.unop)⟩ := rfl

/-- Sections of `towerPresheaf A` over an open `W` are determined by their coordinates. -/
lemma towerSections_ext {W : Opens Chain.{u}} {s t : towerSections A W}
    (h : ∀ n : Index.{u} W, s.1 n = t.1 n) : s = t :=
  Subtype.ext (funext h)

/-- **The presheaf of compatible families is a sheaf.** A basic open contained in a union of
opens is contained in one of them, so the index sets of the members of a cover glue to the index
set of the covered open. -/
lemma isSheaf_towerPresheaf :
    TopCat.Presheaf.IsSheaf (X := chainSpace.{u}) (towerPresheaf A) := by
  classical
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι V sf hsf
  -- The coordinates of the given sections agree wherever two of them are both defined.
  have hwd : ∀ (k : ℕ) (i j : ι) (hi : basicOpen.{u} k ≤ V i) (hj : basicOpen.{u} k ≤ V j),
      (sf i).1 ⟨k, hi⟩ = (sf j).1 ⟨k, hj⟩ := by
    intro k i j hi hj
    have h2 : (((towerPresheaf A).map (Opens.infLELeft (V i) (V j)).op) (sf i)).1
          ⟨k, le_inf hi hj⟩ =
        (((towerPresheaf A).map (Opens.infLERight (V i) (V j)).op) (sf j)).1
          ⟨k, le_inf hi hj⟩ := by
      rw [hsf i j]
    exact h2
  have hchoice : ∀ n : Index.{u} (⨆ i, V i), ∃ i, basicOpen.{u} n.1 ≤ V i :=
    fun n => exists_basicOpen_le_of_le_iSup V n.2
  choose idx hidx using hchoice
  refine ⟨⟨fun n => (sf (idx n)).1 ⟨n.1, hidx n⟩, fun m n h => ?_⟩, fun i => ?_, fun t ht => ?_⟩
  · have hle : basicOpen.{u} m.1 ≤ V (idx n) := le_trans (monotone_basicOpen h) (hidx n)
    rw [(sf (idx n)).2 ⟨m.1, hle⟩ ⟨n.1, hidx n⟩ h]
    exact hwd m.1 (idx n) (idx m) hle (hidx m)
  · refine towerSections_ext A fun k => ?_
    have hle : basicOpen.{u} k.1 ≤ ⨆ i, V i := le_trans k.2 (le_iSup V i)
    exact hwd k.1 (idx ⟨k.1, hle⟩) i (hidx ⟨k.1, hle⟩) k.2
  · refine towerSections_ext A fun n => ?_
    have h3 : (((towerPresheaf A).map (Opens.leSupr V (idx n)).op) t).1 ⟨n.1, hidx n⟩ =
        (sf (idx n)).1 ⟨n.1, hidx n⟩ := by rw [ht (idx n)]
    exact h3

/-- The sheaf attached to an inverse system of abelian groups. -/
def towerSheaf : Sheaf (Opens.grothendieckTopology Chain.{u}) AddCommGrpCat.{u} :=
  ⟨towerPresheaf A, isSheaf_towerPresheaf A⟩

/-- The transition maps of an inverse system compose: `Aₙ ⟶ Aₘ ⟶ Aₗ` is `Aₙ ⟶ Aₗ`. -/
lemma trans_comp_trans {l m n : ℕ} (h₁ : l ≤ m) (h₂ : m ≤ n) :
    trans A h₂ ≫ trans A h₁ = trans A (h₁.trans h₂) := by
  rw [← A.map_comp]
  rfl

/-- The transition map `Aₙ ⟶ Aₙ` is the identity. -/
lemma trans_refl (n : ℕ) : trans A (le_refl n) = 𝟙 (A.obj (op n)) := A.map_id _

/-- The section of `towerSheaf A` over the basic open `U k` determined by an element of `Aₖ`:
its coordinate at `n ≤ k` is the image of the element under the transition map. -/
def mkBasicOpenSection (k : ℕ) (a : A.obj (op k)) : towerSections A (basicOpen.{u} k) :=
  ⟨fun n => trans A (basicOpen_le_basicOpen_iff.1 n.2) a, fun m n h => by
    have := ConcreteCategory.congr_hom
      (trans_comp_trans A h (basicOpen_le_basicOpen_iff.1 n.2)) a
    simpa using this⟩

/-- The coordinate at `n ≤ k` of `mkBasicOpenSection A k a` is the image of `a` under the
transition map `Aₖ ⟶ Aₙ`. -/
@[simp]
lemma mkBasicOpenSection_coe (k : ℕ) (a : A.obj (op k)) (n : Index.{u} (basicOpen.{u} k)) :
    (mkBasicOpenSection A k a).1 n = trans A (basicOpen_le_basicOpen_iff.1 n.2) a := rfl

/-- Evaluating a section over `U k` at the index `k` recovers the element it came from. -/
lemma mkBasicOpenSection_eval (k : ℕ) (a : A.obj (op k)) :
    (mkBasicOpenSection A k a).1 ⟨k, le_rfl⟩ = a := by
  have : trans A (le_refl k) a = a := by rw [trans_refl]; rfl
  exact this

/-- A section over `U k` is the one determined by its coordinate at `k`. -/
lemma eq_mkBasicOpenSection (k : ℕ) (s : towerSections A (basicOpen.{u} k)) :
    s = mkBasicOpenSection A k (s.1 ⟨k, le_rfl⟩) :=
  towerSections_ext A fun n => (s.2 n ⟨k, le_rfl⟩ (basicOpen_le_basicOpen_iff.1 n.2)).symm

end Tower

/-! ### Morphisms of inverse systems -/

section Morphism

variable {A B : ℕᵒᵖ ⥤ AddCommGrpCat.{u}} (f : A ⟶ B)

/-- A morphism of inverse systems commutes with the transition maps. -/
lemma trans_naturality {m n : ℕ} (h : m ≤ n) (a : A.obj (op n)) :
    f.app (op m) (trans A h a) = trans B h (f.app (op n) a) :=
  ConcreteCategory.congr_hom (f.naturality (homOfLE h).op) a

/-- The morphism of presheaves of compatible families attached to a morphism of inverse
systems. -/
def towerPresheafMap : towerPresheaf A ⟶ towerPresheaf B where
  app W := AddCommGrpCat.ofHom
    { toFun := fun s => ⟨fun n => f.app (op n.1) (s.1 n), fun m n h => by
        rw [← trans_naturality f h (s.1 n), s.2 m n h]⟩
      map_zero' := by
        refine towerSections_ext B fun n => ?_
        change f.app (op n.1) 0 = 0
        rw [map_zero]
      map_add' s t := by
        refine towerSections_ext B fun n => ?_
        change f.app (op n.1) (s.1 n + t.1 n) = f.app (op n.1) (s.1 n) + f.app (op n.1) (t.1 n)
        rw [map_add] }
  naturality _ _ _ := rfl

/-- The morphism `towerPresheafMap f` applies `f` to each coordinate of a compatible family. -/
@[simp]
lemma towerPresheafMap_app_coe (W : (Opens Chain.{u})ᵒᵖ) (s : towerSections A W.unop)
    (n : Index.{u} W.unop) :
    (((towerPresheafMap f).app W) s).1 n = f.app (op n.1) (s.1 n) := rfl

/-- The morphism of sheaves attached to a morphism of inverse systems. -/
def towerSheafMap : towerSheaf A ⟶ towerSheaf B := ⟨towerPresheafMap f⟩

/-- **A morphism of inverse systems surjective in every degree induces an epimorphism of
sheaves.** It is locally surjective: a section over `W` restricts, on the basic open of any point
of `W`, to the image of the section determined by a lift of its coordinate there. -/
lemma isLocallySurjective_towerPresheafMap
    (hf : ∀ n : ℕ, Function.Surjective (f.app (op n))) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology Chain.{u}) (towerPresheafMap f) where
  imageSieve_mem {W} x := by
    rw [Opens.mem_grothendieckTopology]
    intro p hp
    obtain ⟨b, hb⟩ := hf p.down (x.1 ⟨p.down, basicOpen_le_of_mem hp⟩)
    refine ⟨basicOpen.{u} p.down, homOfLE (basicOpen_le_of_mem hp),
      ⟨mkBasicOpenSection A p.down b, towerSections_ext B fun n => ?_⟩, self_mem_basicOpen p⟩
    have hn : basicOpen.{u} n.1 ≤ basicOpen.{u} p.down := n.2
    have hnp : n.1 ≤ p.down := basicOpen_le_basicOpen_iff.1 hn
    have hL : (((towerPresheafMap f).app (op (basicOpen.{u} p.down)))
          (mkBasicOpenSection A p.down b)).1 n = f.app (op n.1) (trans A hnp b) := rfl
    have hR : (((towerPresheaf B).map (homOfLE (basicOpen_le_of_mem hp)).op) x).1 n =
        x.1 ⟨n.1, le_trans hn (basicOpen_le_of_mem hp)⟩ := rfl
    rw [hL, hR, trans_naturality f, hb]
    exact x.2 ⟨n.1, le_trans hn (basicOpen_le_of_mem hp)⟩
      ⟨p.down, basicOpen_le_of_mem hp⟩ hnp

/-- A morphism of inverse systems surjective in every degree induces an epimorphism of sheaves
`towerSheafMap f`. -/
lemma epi_towerSheafMap (hf : ∀ n : ℕ, Function.Surjective (f.app (op n))) :
    Epi (towerSheafMap f) := by
  have : Sheaf.IsLocallySurjective (towerSheafMap f) :=
    isLocallySurjective_towerPresheafMap f hf
  exact Sheaf.epi_of_isLocallySurjective _

end Morphism

/-! ### Every abelian sheaf on `Chain` is the sheaf of an inverse system -/

section Comparison

variable (F : Sheaf (Opens.grothendieckTopology Chain.{u}) AddCommGrpCat.{u})

/-- Restriction along two nested inclusions of opens is restriction along the composite. -/
lemma map_comp_map {W W' W'' : Opens Chain.{u}} (h₁ : W ≤ W') (h₂ : W' ≤ W'') :
    F.obj.map (homOfLE h₂).op ≫ F.obj.map (homOfLE h₁).op =
      F.obj.map (homOfLE (h₁.trans h₂)).op := by
  rw [← F.obj.map_comp]
  rfl

/-- The inverse system `n ↦ ℱ(Uₙ)` attached to an abelian sheaf `ℱ` on `Chain`. -/
def sheafTower : ℕᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj n := F.obj.obj (op (basicOpen.{u} n.unop))
  map {_ _} φ := F.obj.map (homOfLE (monotone_basicOpen (leOfHom φ.unop))).op
  map_id _ := by rw [← F.obj.map_id]; rfl
  map_comp _ _ := by rw [← F.obj.map_comp]; rfl

/-- The comparison map `ℱ(W) ⟶ lim_{Uₙ ⊆ W} ℱ(Uₙ)`: restriction to the basic opens inside `W`. -/
def towerComparison : F.obj ⟶ towerPresheaf (sheafTower F) where
  app W := AddCommGrpCat.ofHom
    { toFun := fun s => ⟨fun n => F.obj.map (homOfLE n.2).op s, fun m n h =>
        ConcreteCategory.congr_hom (map_comp_map F (monotone_basicOpen h) n.2) s⟩
      map_zero' := towerSections_ext _ fun _ => map_zero _
      map_add' s t := towerSections_ext _ fun _ => map_add _ s t }
  naturality _ _ f := by
    refine AddCommGrpCat.ext fun s => towerSections_ext _ fun n => ?_
    exact ConcreteCategory.congr_hom (map_comp_map F n.2 (leOfHom f.unop)) s

/-- The basic opens of the points of an open `W` of `Chain` cover `W`. -/
lemma iSup_basicOpen_eq (W : Opens Chain.{u}) :
    (⨆ x : {x : Chain.{u} // x ∈ W}, basicOpen.{u} x.1.down) = W :=
  le_antisymm (iSup_le fun x => basicOpen_le_of_mem x.2)
    fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, self_mem_basicOpen y⟩

/-- **An abelian sheaf on `Chain` is the same thing as an inverse system of abelian groups.**
The comparison map is bijective on sections over every open: the index sets of the basic opens
cover, so a section is determined by, and can be glued from, its restrictions to the basic
opens. In particular `Γ(X, ℱ) = lim ℱ(Uₙ)`. -/
@[stacks 0BX0 "an abelian sheaf on the space is the inverse system of its sections over the \
U_n; the clause `Γ(X, ℱ) = lim A_n` is globalSectionsAddEquiv"]
lemma bijective_towerComparison_app (W : (Opens Chain.{u})ᵒᵖ) :
    Function.Bijective ((towerComparison F).app W) := by
  have hiUV : ∀ x : {x : Chain.{u} // x ∈ W.unop}, basicOpen.{u} x.1.down ≤ W.unop :=
    fun x => basicOpen_le_of_mem x.2
  have hcover : W.unop ≤ ⨆ x : {x : Chain.{u} // x ∈ W.unop}, basicOpen.{u} x.1.down :=
    (iSup_basicOpen_eq W.unop).ge
  refine ⟨fun s t hst => ?_, fun y => ?_⟩
  · exact TopCat.Sheaf.eq_of_locally_eq' (X := chainSpace.{u}) (F := F)
      (fun x : {x : Chain.{u} // x ∈ W.unop} => basicOpen.{u} x.1.down) W.unop
      (fun x => homOfLE (hiUV x)) hcover s t fun x =>
        congrArg (fun z : towerSections (sheafTower F) W.unop => z.1 ⟨x.1.down, hiUV x⟩) hst
  · have hcompat : TopCat.Presheaf.IsCompatible (X := chainSpace.{u}) F.obj
        (fun x : {x : Chain.{u} // x ∈ W.unop} => basicOpen.{u} x.1.down)
        (fun x => y.1 ⟨x.1.down, hiUV x⟩) := by
      intro x z
      have hle : (basicOpen.{u} x.1.down ⊓ basicOpen.{u} z.1.down : Opens Chain.{u}) ≤
          basicOpen.{u} (min x.1.down z.1.down) :=
        fun _ hw => mem_basicOpen.2 (le_min hw.1 hw.2)
      have hkW : basicOpen.{u} (min x.1.down z.1.down) ≤ W.unop :=
        le_trans (monotone_basicOpen (min_le_left _ _)) (hiUV x)
      -- Restricting `y` at `a` to `U (min a b)` agrees with its coordinate at `min a b`.
      have key : ∀ a : {x : Chain.{u} // x ∈ W.unop}, ∀ h : min x.1.down z.1.down ≤ a.1.down,
          F.obj.map (homOfLE (hle.trans (monotone_basicOpen h))).op (y.1 ⟨a.1.down, hiUV a⟩) =
            F.obj.map (homOfLE hle).op (y.1 ⟨min x.1.down z.1.down, hkW⟩) := fun a h => by
        rw [← y.2 ⟨min x.1.down z.1.down, hkW⟩ ⟨a.1.down, hiUV a⟩ h]
        exact (ConcreteCategory.congr_hom (map_comp_map F hle (monotone_basicOpen h))
          (y.1 ⟨a.1.down, hiUV a⟩)).symm
      exact (key x (min_le_left _ _)).trans (key z (min_le_right _ _)).symm
    obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' (X := chainSpace.{u}) (F := F)
      (fun x : {x : Chain.{u} // x ∈ W.unop} => basicOpen.{u} x.1.down) W.unop
      (fun x => homOfLE (hiUV x)) hcover (fun x => y.1 ⟨x.1.down, hiUV x⟩) hcompat
    exact ⟨s, towerSections_ext _ fun n =>
      hs ⟨ULift.up n.1, n.2 (self_mem_basicOpen (ULift.up n.1))⟩⟩

/-- **`Γ(X, ℱ) = lim ℱ(Uₙ)`.** Global sections of an abelian sheaf on `Chain` are the inverse
limit of its inverse system of sections over the basic opens. -/
@[stacks 0BX0 "the clause `Γ(X, ℱ) = lim A_n` with `A_n = ℱ(U_n)`"]
noncomputable def globalSectionsAddEquiv :
    F.obj.obj (op (⊤ : Opens Chain.{u})) ≃+ towerSections (sheafTower F) ⊤ :=
  AddEquiv.ofBijective (((towerComparison F).app (op ⊤)).hom)
    (bijective_towerComparison_app F (op ⊤))

end Comparison

/-! ### The inverse system `ℤ/2ⁿℤ` and the failure of right exactness of `lim` -/

/-- The `ULift` of an additive group homomorphism, as a morphism of `AddCommGrpCat.{u}`. -/
def uliftOfHom {G H : Type} [AddCommGroup G] [AddCommGroup H] (φ : G →+ H) :
    AddCommGrpCat.of (ULift.{u} G) ⟶ AddCommGrpCat.of (ULift.{u} H) :=
  AddCommGrpCat.ofHom (AddMonoidHom.mk' (fun x => ULift.up (φ x.down))
    fun a b => congrArg ULift.up (map_add φ a.down b.down))

/-- The morphism `uliftOfHom φ` sends `x` to `ULift.up (φ x.down)`. -/
@[simp]
lemma uliftOfHom_apply {G H : Type} [AddCommGroup G] [AddCommGroup H] (φ : G →+ H)
    (x : ULift.{u} G) : uliftOfHom.{u} φ x = ULift.up (φ x.down) := rfl

/-- The constant inverse system `ℤ`; the corresponding sheaf is the constant sheaf `ℤ`. -/
def constIntTower : ℕᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (Functor.const ℕᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ))

/-- Any two reductions `ℤ/2ⁿℤ ⟶ ℤ/2ˡℤ` factoring through `ℤ/2ᵐℤ` agree. -/
private lemma zmod_cast_comp {l m n : ℕ} (h₁ : l ≤ m) (h₂ : m ≤ n) (c : ZMod (2 ^ n)) :
    (ZMod.castHom (pow_dvd_pow 2 (h₁.trans h₂)) (ZMod (2 ^ l))) c =
      (ZMod.castHom (pow_dvd_pow 2 h₁) (ZMod (2 ^ l)))
        ((ZMod.castHom (pow_dvd_pow 2 h₂) (ZMod (2 ^ m))) c) :=
  (RingHom.congr_fun (ZMod.castHom_comp (pow_dvd_pow 2 h₁) (pow_dvd_pow 2 h₂)) c).symm

private lemma zmod_cast_self {n : ℕ} (c : ZMod (2 ^ n)) :
    (ZMod.castHom (pow_dvd_pow 2 (le_refl n)) (ZMod (2 ^ n))) c = c := by
  rw [ZMod.castHom_apply, ZMod.cast_id]

/-- The inverse system `n ↦ ℤ/2ⁿℤ` with the reduction maps; its limit is the group of `2`-adic
integers. -/
def dyadicTower : ℕᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj n := AddCommGrpCat.of (ULift.{u} (ZMod (2 ^ n.unop)))
  map {_ Y} φ := uliftOfHom.{u}
    (ZMod.castHom (pow_dvd_pow 2 (leOfHom φ.unop)) (ZMod (2 ^ Y.unop))).toAddMonoidHom
  map_id _ := by
    refine AddCommGrpCat.ext fun c => ?_
    exact congrArg ULift.up (zmod_cast_self c.down)
  map_comp φ ψ := by
    refine AddCommGrpCat.ext fun c => ?_
    exact congrArg ULift.up (zmod_cast_comp (leOfHom ψ.unop) (leOfHom φ.unop) c.down)

/-- The reduction of the constant system `ℤ` modulo `2ⁿ`. -/
def dyadicProjection : constIntTower.{u} ⟶ dyadicTower.{u} where
  app n := uliftOfHom.{u} (Int.castAddHom (ZMod (2 ^ n.unop)))
  naturality {_ Y} φ := by
    refine AddCommGrpCat.ext fun a => ?_
    exact congrArg ULift.up
      (map_intCast (ZMod.castHom (pow_dvd_pow 2 (leOfHom φ.unop)) (ZMod (2 ^ Y.unop)))
        a.down).symm

/-- The reduction `ℤ ⟶ ℤ/Nℤ` (lifted to the universe of `AddCommGrpCat.{u}`) is surjective. -/
private lemma surjective_uliftOfHom_intCast (N : ℕ) :
    Function.Surjective (uliftOfHom.{u} (Int.castAddHom (ZMod N))) := by
  intro c
  obtain ⟨a, ha⟩ := ZMod.intCast_surjective (n := N) c.down
  exact ⟨ULift.up a, congrArg ULift.up ha⟩

/-- The reduction `ℤ ⟶ ℤ/2ⁿℤ` is surjective in every degree `n`. -/
lemma surjective_dyadicProjection_app (n : ℕ) :
    Function.Surjective (dyadicProjection.{u}.app (op n)) :=
  surjective_uliftOfHom_intCast _

/-- Sections of the constant inverse system `ℤ` are constant families. -/
lemma constIntTower_sections_eq {W : Opens Chain.{u}} (s : towerSections constIntTower.{u} W)
    (m n : Index.{u} W) (h : m.1 ≤ n.1) : s.1 n = s.1 m := s.2 m n h

/-! ### A `2`-adic integer which is not an integer -/

/-- The finite sums `aₙ = 1 + 4 + ⋯ + 4ⁿ⁻¹`. -/
def dyadicPartialSum : ℕ → ℤ
  | 0 => 0
  | (n + 1) => dyadicPartialSum n + 4 ^ n

/-- The closed form `3 (1 + 4 + ⋯ + 4ⁿ⁻¹) = 4ⁿ - 1`. -/
lemma three_mul_dyadicPartialSum (n : ℕ) : 3 * dyadicPartialSum n = 4 ^ n - 1 := by
  induction n with
  | zero => simp [dyadicPartialSum]
  | succ n ih =>
    change 3 * (dyadicPartialSum n + 4 ^ n) = 4 ^ (n + 1) - 1
    rw [mul_add, ih]
    ring

/-- For `m ≤ n`, the difference `aₙ - aₘ` of partial sums is divisible by `2ᵐ`. -/
lemma dvd_sub_dyadicPartialSum {m n : ℕ} (h : m ≤ n) :
    (2 : ℤ) ^ m ∣ dyadicPartialSum n - dyadicPartialSum m := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    have h4 : (2 : ℤ) ^ m ∣ 4 ^ n :=
      (pow_dvd_pow 2 (by omega)).trans (pow_dvd_pow_of_dvd (by norm_num) n)
    change (2 : ℤ) ^ m ∣ dyadicPartialSum n + 4 ^ n - dyadicPartialSum m
    have hrw : dyadicPartialSum n + 4 ^ n - dyadicPartialSum m =
        dyadicPartialSum n - dyadicPartialSum m + 4 ^ n := by ring
    rw [hrw]
    exact dvd_add ih h4

/-- The `2`-adic integer `1 + 4 + 4² + ⋯ = -1/3`, as a global section of the sheaf of the
inverse system `ℤ/2ⁿℤ`. -/
def dyadicWitness : towerSections dyadicTower.{u} ⊤ :=
  ⟨fun n => ULift.up ((dyadicPartialSum n.1 : ZMod (2 ^ n.1))), fun m n h => by
    refine congrArg ULift.up ?_
    have hcast := map_intCast
      (ZMod.castHom (pow_dvd_pow 2 h) (ZMod (2 ^ m.1))) (dyadicPartialSum n.1)
    refine hcast.trans ?_
    have hz : ((dyadicPartialSum n.1 - dyadicPartialSum m.1 : ℤ) : ZMod (2 ^ m.1)) = 0 := by
      refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 ?_
      have := dvd_sub_dyadicPartialSum (m := m.1) (n := n.1) h
      push_cast
      exact this
    rw [Int.cast_sub, sub_eq_zero] at hz
    exact hz⟩

/-- No integer reduces to `1 + 4 + 4² + ⋯` modulo every power of `2`: such an integer `m` would
satisfy `2ⁿ ∣ 3m + 1` for every `n`, hence `3m = -1`. -/
private lemma not_congr_dyadicPartialSum (m : ℤ)
    (key : ∀ n : ℕ, ((m : ZMod (2 ^ n)) = (dyadicPartialSum n : ZMod (2 ^ n)))) : False := by
  have hall : ∀ n : ℕ, (2 : ℤ) ^ n ∣ 3 * m + 1 := by
    intro n
    have hz : ((m - dyadicPartialSum n : ℤ) : ZMod (2 ^ n)) = 0 := by
      rw [Int.cast_sub, sub_eq_zero]
      exact key n
    have hdvd : (2 : ℤ) ^ n ∣ m - dyadicPartialSum n := by
      have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hz
      push_cast at hd
      exact hd
    have h3 : (2 : ℤ) ^ n ∣ 3 * m - (4 ^ n - 1) := by
      rw [← three_mul_dyadicPartialSum n, ← mul_sub]
      exact Dvd.dvd.mul_left hdvd 3
    have h4 : (2 : ℤ) ^ n ∣ 4 ^ n := pow_dvd_pow_of_dvd (by norm_num) n
    have hsum := dvd_add h3 h4
    have hrw : 3 * m - (4 ^ n - 1) + 4 ^ n = 3 * m + 1 := by ring
    rwa [hrw] at hsum
  have hne : 3 * m + 1 ≠ 0 := by omega
  have hdvd := hall (3 * m + 1).natAbs
  have hle : (2 : ℤ) ^ (3 * m + 1).natAbs ≤ |3 * m + 1| :=
    Int.le_of_dvd (abs_pos.2 hne) ((dvd_abs _ _).2 hdvd)
  have hgt : ((3 * m + 1).natAbs : ℤ) < (2 : ℤ) ^ (3 * m + 1).natAbs := by
    have hlt := Nat.lt_two_pow_self (n := (3 * m + 1).natAbs)
    exact_mod_cast hlt
  rw [Int.abs_eq_natAbs] at hle
  omega

/-- **The inverse limit functor is not right exact**: the reduction `ℤ ⟶ lim ℤ/2ⁿℤ` is not
surjective, because `1 + 4 + 4² + ⋯` is not an integer. -/
lemma not_surjective_dyadicProjection_app_top :
    ¬ Function.Surjective ((towerPresheafMap dyadicProjection.{u}).app (op ⊤)) := by
  intro hsurj
  obtain ⟨s, hs⟩ := hsurj dyadicWitness.{u}
  refine not_congr_dyadicPartialSum ((s.1 ⟨0, le_top⟩).down) fun n => ?_
  have hconst : s.1 ⟨n, le_top⟩ = s.1 ⟨0, le_top⟩ :=
    constIntTower_sections_eq s ⟨0, le_top⟩ ⟨n, le_top⟩ (Nat.zero_le n)
  rw [← hconst]
  exact congrArg (fun y : towerSections dyadicTower.{u} ⊤ => (y.1 ⟨n, le_top⟩).down) hs

/-! ### Conditions (2) and (3) of [Stacks, Tag 02UX] -/

/-- **Condition (2) of [Stacks, Tag 02UX]**: `Chain` has a basis of quasi-compact opens, namely
the finite opens `{i | i ≤ n}`. -/
@[stacks 0BX0 "condition (2) of Tag 02UX: a basis of quasi-compact opens"]
lemma hasBasisOfCompactOpens_chain : PrespectralSpace Chain.{u} := by
  refine PrespectralSpace.of_isTopologicalBasis
    (B := {s | ∃ n, s = (basicOpen.{u} n : Set Chain.{u})}) ?_ ?_
  · refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · rintro s ⟨n, rfl⟩
      exact (basicOpen.{u} n).isOpen
    · intro x W hx hW
      exact ⟨(basicOpen.{u} x.down : Set Chain.{u}), ⟨x.down, rfl⟩, self_mem_basicOpen x,
        basicOpen_le_of_mem (W := ⟨W, hW⟩) hx⟩
  · rintro s ⟨n, rfl⟩
    exact (finite_basicOpen.{u} n).isCompact

/-- **Condition (3) of [Stacks, Tag 02UX]**: the intersection of two quasi-compact opens of
`Chain` is quasi-compact, both being finite. -/
@[stacks 0BX0 "condition (3) of Tag 02UX: quasi-compact opens have quasi-compact intersections"]
lemma interCompactOpenIsCompact_chain : QuasiSeparatedSpace Chain.{u} :=
  ⟨fun _ _ _ hU _ _ => ((finite_of_isCompact hU).subset Set.inter_subset_left).isCompact⟩

/-! ### An abelian sheaf on `Chain` with nonvanishing first cohomology -/

section Counterexample

open Stacks.Cohomology.AbelianColimit

/-- Abelian presheaves on the site of opens of `Chain` admit sheafification. -/
noncomputable local instance hasSheafifyChain :
    HasSheafify (Opens.grothendieckTopology Chain.{u}) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite _ _

/-- The short exact sequence `0 ⟶ 𝒦 ⟶ ℤ ⟶ (ℤ/2ⁿℤ)ₙ ⟶ 0` of abelian sheaves on `Chain`, with
`𝒦` the kernel of the reduction of the constant sheaf `ℤ`. -/
noncomputable abbrev witnessSequence :
    ShortComplex (Sheaf (Opens.grothendieckTopology Chain.{u}) AddCommGrpCat.{u}) :=
  ShortComplex.kernelSequence (towerSheafMap dyadicProjection.{u})

/-- The abelian sheaf on `Chain` whose first cohomology does not vanish: the kernel of the
reduction of the constant sheaf `ℤ` onto the sheaf of the inverse system `ℤ/2ⁿℤ`. As an inverse
system it is `n ↦ 2ⁿℤ`, with inverse limit `0`. -/
noncomputable def nonVanishingSheaf :
    Sheaf (Opens.grothendieckTopology Chain.{u}) AddCommGrpCat.{u} :=
  witnessSequence.{u}.X₁

/-- The sequence `0 ⟶ 𝒦 ⟶ ℤ ⟶ (ℤ/2ⁿℤ)ₙ ⟶ 0` of `witnessSequence` is short exact. -/
lemma witnessSequence_shortExact : witnessSequence.{u}.ShortExact where
  exact := ShortComplex.kernelSequence_exact _
  mono_f := inferInstance
  epi_g := epi_towerSheafMap _ surjective_dyadicProjection_app

/-- Being an epimorphism on a given arrow is invariant under natural isomorphism of functors. -/
private lemma epi_map_of_natIso {C D : Type*} [Category* C] [Category* D] {F G : C ⥤ D}
    (e : F ≅ G) {X Y : C} (f : X ⟶ Y) (hf : Epi (F.map f)) : Epi (G.map f) := by
  have h1 : F.map f ≫ e.hom.app Y = e.hom.app X ≫ G.map f := e.hom.naturality f
  have h2 : Epi (e.hom.app X ≫ G.map f) := by
    rw [← h1]
    have := hf
    infer_instance
  have := h2
  exact epi_of_epi (e.hom.app X) (G.map f)

/-- **The first cohomology of `𝒦` does not vanish.** If it did, the long exact sequence would
make `Γ(X, ℤ) ⟶ Γ(X, (ℤ/2ⁿℤ)ₙ) = lim ℤ/2ⁿℤ` surjective, which it is not. -/
theorem not_isZero_H'functor_one_nonVanishingSheaf :
    ¬ IsZero ((H'functor (X := Chain.{u}) ⊤ 1).obj nonVanishingSheaf.{u}) := by
  intro hz
  have hS := witnessSequence_shortExact.{u}
  have hepi : Epi ((H'functor (X := Chain.{u}) ⊤ 0).map witnessSequence.{u}.g) :=
    (shortComplex_H'_exact₃ hS ⊤ (zero_add 1)).epi_f (hz.eq_of_tgt _ 0)
  have h3 := epi_map_of_natIso
    (nonempty_H'functor_zero_iso_abSections (X := Chain.{u}) ⊤).some
    witnessSequence.{u}.g hepi
  rw [AddCommGrpCat.epi_iff_surjective] at h3
  exact not_surjective_dyadicProjection_app_top h3

/-- The cohomology of a sheaf on `Chain` vanishes in degree `p` iff the cohomology presheaf is zero
at `⊤`. -/
private lemma subsingleton_sheafH_iff_isZero_H'functor
    (F : Sheaf (Opens.grothendieckTopology Chain.{u}) AddCommGrpCat.{u}) (p : ℕ) :
    Subsingleton (Sheaf.H.{u, u, u, u} F p) ↔ IsZero ((H'functor (X := Chain.{u}) ⊤ p).obj F) :=
  (Stacks.Cohomology.TerminalCohomology.subsingleton_H_iff_subsingleton_H'_top
    (X := Chain.{u}) F p).trans AddCommGrpCat.isZero_iff_subsingleton.symm

/-- **[Stacks, Tag 0BX0].** Let `X` be the natural numbers with the topology whose opens are
`∅`, `X` and `U_n = {i | i ≤ n}`. An abelian sheaf on `X` is an inverse system of abelian groups
`A_n = ℱ(U_n)` with `Γ(X, ℱ) = lim A_n`, and since `lim` is not exact on inverse systems there is
an abelian sheaf on `X` with nonzero `H¹` — even though `X` satisfies conditions (2) and (3) of
[Stacks, Tag 02UX] with `d = 0`. -/
@[stacks 0BX0 "the existence of an abelian sheaf with nonzero H¹; the lattice of opens, the \
identification of abelian sheaves with inverse systems and conditions (2) and (3) of Tag 02UX \
are given by eq_bot_or_eq_top_or_eq_basicOpen, bijective_towerComparison_app, \
globalSectionsAddEquiv, hasBasisOfCompactOpens_chain and interCompactOpenIsCompact_chain; \
condition (4), the vanishing H^p(X, j_!ℤ_U) = 0 for p ≥ 1, which the source leaves to the \
reader, is subsingleton_sheafH_integerExtensionByZero, proved through the \
identification j_!ℤ_{U n} = 𝒦ₙ of integerExtensionByZeroIsoKernel"]
theorem exists_not_subsingleton_sheafH_one :
    ∃ F : Sheaf (Opens.grothendieckTopology Chain.{u}) AddCommGrpCat.{u},
      ¬ Subsingleton (Sheaf.H.{u, u, u, u} F 1) := by
  exact ⟨nonVanishingSheaf.{u}, fun hsub => not_isZero_H'functor_one_nonVanishingSheaf.{u}
    ((subsingleton_sheafH_iff_isZero_H'functor _ 1).1 hsub)⟩

end Counterexample

/-! ### Basic opens are local objects of the site, and `Chain` is irreducible

The two facts about `Chain` that the proof of condition (4) of [Stacks, Tag 02UX] over it rests
on: a cover of a basic open contains that basic open itself, and a nonempty open of `Chain`, or of
one of its basic opens, contains the least point. -/

section LocalObjects

/-- Abelian presheaves on the site of opens of `Chain` admit sheafification. -/
noncomputable local instance hasSheafifyChain' :
    HasSheafify (Opens.grothendieckTopology Chain.{u}) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite _ _

/-- **A basic open of `Chain` is a local object of its site of opens**: every covering sieve of
`U n` is the maximal sieve. A cover of `U n` has a member containing the point `n`, and every
open containing `n` contains `U n`, so that member is `U n` itself. -/
lemma eq_top_of_mem_grothendieckTopology {n : ℕ} {S : Sieve (basicOpen.{u} n)}
    (hS : S ∈ Opens.grothendieckTopology Chain.{u} (basicOpen.{u} n)) : S = ⊤ := by
  rw [← Sieve.id_mem_iff_eq_top]
  obtain ⟨V, f, hf, hV⟩ := hS (ULift.up n) (self_mem_basicOpen _)
  have hle : basicOpen.{u} n ≤ V := basicOpen_le_of_mem hV
  obtain rfl : V = basicOpen.{u} n := le_antisymm (leOfHom f) hle
  exact Subsingleton.elim f (𝟙 _) ▸ hf

/-- A locally surjective morphism of presheaves on `Chain` is honestly surjective on sections
over a basic open, the only covering sieve of a basic open being the maximal one. -/
lemma surjective_app_basicOpen {P Q : (Opens Chain.{u})ᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ Q)
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology Chain.{u}) φ] (n : ℕ) :
    Function.Surjective (φ.app (op (basicOpen.{u} n))) := by
  intro s
  have h := eq_top_of_mem_grothendieckTopology
    (Presheaf.imageSieve_mem (Opens.grothendieckTopology Chain.{u}) φ
      (U := op (basicOpen.{u} n)) s)
  have h1 : (Presheaf.imageSieve φ s).arrows (𝟙 (basicOpen.{u} n)) := by
    rw [h]; trivial
  obtain ⟨t, ht⟩ := h1
  refine ⟨t, ?_⟩
  simpa using ht

/-- A locally injective morphism of presheaves on `Chain` is honestly injective on sections over
a basic open. -/
lemma injective_app_basicOpen {P Q : (Opens Chain.{u})ᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ Q)
    [Presheaf.IsLocallyInjective (Opens.grothendieckTopology Chain.{u}) φ] (n : ℕ) :
    Function.Injective (φ.app (op (basicOpen.{u} n))) := by
  intro x y hxy
  have h := eq_top_of_mem_grothendieckTopology
    (Presheaf.equalizerSieve_mem (Opens.grothendieckTopology Chain.{u}) φ x y hxy)
  exact (Presheaf.equalizerSieve_eq_top_iff x y).1 h

/-- **Sheafification does not change the sections of a presheaf on `Chain` over a basic open.**
This is what computes the sections of a sheaf given by sheafifying an explicit presheaf — for
instance the extension by zero `j_!ℤ_{U n}` of condition (4) of [Stacks, Tag 02UX]. -/
lemma bijective_toSheafify_app_basicOpen (P : (Opens Chain.{u})ᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) :
    Function.Bijective
      ((toSheafify (Opens.grothendieckTopology Chain.{u}) P).app (op (basicOpen.{u} n))) :=
  ⟨injective_app_basicOpen _ n, surjective_app_basicOpen _ n⟩

/-- **Sections over a basic open of `Chain` are exact on abelian sheaves**: an epimorphism of
abelian sheaves is surjective on sections over `U n`, and not merely locally surjective. -/
lemma surjective_app_basicOpen_of_epi
    {F G : Sheaf (Opens.grothendieckTopology Chain.{u}) AddCommGrpCat.{u}} (f : F ⟶ G) [Epi f]
    (n : ℕ) : Function.Surjective (f.hom.app (op (basicOpen.{u} n))) := by
  have h : Sheaf.IsLocallySurjective f :=
    (Sheaf.isLocallySurjective_iff_epi' _ f).2 inferInstance
  exact surjective_app_basicOpen f.hom n

/-- **`Chain` is irreducible**: every nonempty open is a nonempty lower set, hence contains the
least point, so any two nonempty opens meet. -/
instance preirreducibleSpace_chain : PreirreducibleSpace Chain.{u} where
  isPreirreducible_univ := by
    intro u v hu hv hsu hsv
    obtain ⟨y, -, hy⟩ := hsu
    obtain ⟨z, -, hz⟩ := hsv
    have hle : ∀ w : Chain.{u}, (ULift.up 0 : Chain.{u}) ≤ w := fun w => Nat.zero_le w.down
    exact ⟨ULift.up 0, Set.mem_univ _,
      (Topology.IsLowerSet.isOpen_iff_isLowerSet.1 hu) (hle y) hy,
      (Topology.IsLowerSet.isOpen_iff_isLowerSet.1 hv) (hle z) hz⟩

/-- The space `Chain` is irreducible. -/
instance irreducibleSpace_chain : IrreducibleSpace Chain.{u} where
  toNonempty := ⟨ULift.up 0⟩

/-- **The higher cohomology of a constant abelian sheaf on `Chain` vanishes**, by
[Stacks, Tag 02UW], `Chain` being irreducible. This is the acyclicity of the middle term of the
short exact sequence `0 ⟶ j_!ℤ_{U n} ⟶ ℤ_X ⟶ i_*ℤ_Z ⟶ 0` through which condition (4) of
[Stacks, Tag 02UX] is proved over `Chain`. -/
theorem subsingleton_sheafH_constantSheaf_chain (A : AddCommGrpCat.{u}) (p : ℕ) (hp : 0 < p) :
    Subsingleton
      (Sheaf.H.{u, u, u, u}
        ((constantSheaf (Opens.grothendieckTopology Chain.{u}) AddCommGrpCat.{u}).obj A) p) :=
  Stacks.CohomologyVanishing.subsingleton_sheafH_constantSheaf_of_irreducibleSpace A p hp

end LocalObjects

/-! ### Flasqueness of the sheaf of an inverse system covered by a constant one -/

section FlasqueTower

/-- A basic open of `Chain` is nonempty — it contains the least point — so it is not contained in
the empty open. -/
lemma not_basicOpen_le_bot (n : ℕ) : ¬ basicOpen.{u} n ≤ (⊥ : Opens Chain.{u}) := fun h =>
  Opens.mem_bot.1 (h (mem_basicOpen.2 (Nat.zero_le n)) : (ULift.up 0 : Chain.{u}) ∈ ⊥)

/-- The transition maps of a constant inverse system are identities. -/
lemma trans_const {G : AddCommGrpCat.{u}} {m n : ℕ} (h : m ≤ n) (g : G) :
    trans ((Functor.const ℕᵒᵖ).obj G) h g = g := by
  simp

/-- The constant family of value `g`, as a section of the sheaf of a constant inverse system. -/
def constTowerSection {G : AddCommGrpCat.{u}} (g : G) (W : Opens Chain.{u}) :
    towerSections ((Functor.const ℕᵒᵖ).obj G) W :=
  ⟨fun _ => g, fun _ _ h => trans_const h g⟩

/-- **The sheaf of an inverse system which is a levelwise quotient of a constant system is
flasque.** The opens of `Chain` are `∅`, the whole space and the basic opens: sections over `∅`
are unique, a section over the whole space restricts to itself, and a section over `U k` is the
one determined by its coordinate at `k`, which lifts to the constant system and so extends over
every larger open as a constant family. -/
lemma isFlasque_towerSheaf_of_const {G : AddCommGrpCat.{u}} {A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}}
    (π : (Functor.const ℕᵒᵖ).obj G ⟶ A)
    (hπ : ∀ k : ℕ, Function.Surjective (π.app (op k))) :
    TopCat.Sheaf.IsFlasque (X := chainSpace.{u}) (towerSheaf A) where
  epi {U V} i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    have hVU : V.unop ≤ U.unop := leOfHom i.unop
    intro t
    rcases eq_bot_or_eq_top_or_eq_basicOpen V.unop with hV | hV | ⟨k, hV⟩
    · refine ⟨0, towerSections_ext A fun n => ?_⟩
      exact absurd (le_of_le_of_eq n.2 hV) (not_basicOpen_le_bot n.1)
    · have hle : ∀ m : ℕ, basicOpen.{u} m ≤ V.unop := fun m => le_of_le_of_eq le_top hV.symm
      exact ⟨⟨fun n => t.1 ⟨n.1, hle n.1⟩,
        fun m n h => t.2 ⟨m.1, hle m.1⟩ ⟨n.1, hle n.1⟩ h⟩, towerSections_ext A fun _ => rfl⟩
    · obtain ⟨g, hg⟩ := hπ k (t.1 ⟨k, le_of_eq hV.symm⟩)
      refine ⟨((towerPresheafMap π).app U) (constTowerSection g U.unop),
        towerSections_ext A fun n => ?_⟩
      have hn : n.1 ≤ k := basicOpen_le_basicOpen_iff.1 (le_of_le_of_eq n.2 hV)
      change π.app (op n.1) g = t.1 n
      rw [← t.2 n ⟨k, le_of_eq hV.symm⟩ hn, ← hg, ← trans_naturality π hn g, trans_const]

/-- **The constant sheaf of an abelian group is flasque on `Chain`**, in its inverse-system
spelling: the identity of a constant system is levelwise surjective. -/
lemma isFlasque_towerSheaf_const (G : AddCommGrpCat.{u}) :
    TopCat.Sheaf.IsFlasque (X := chainSpace.{u}) (towerSheaf ((Functor.const ℕᵒᵖ).obj G)) :=
  isFlasque_towerSheaf_of_const (𝟙 _) fun _ => Function.surjective_id

end FlasqueTower

/-! ### The inverse system supported above a basic open

`cotruncTower n` is the inverse system which is `0` in degrees `≤ n` and `ℤ` above, realised
uniformly as `k ↦ ℤ/cotruncMod n k` so that its transition maps are reduction maps of `ZMod` and
its functoriality is the uniqueness of ring maps out of `ZMod`.  Its sheaf is the quotient of the
constant sheaf `ℤ` by the extension by zero `j_!ℤ_{U n}`, which is how condition (4) of
[Stacks, Tag 02UX] is reached over `Chain`. -/

section CotruncTower

/-- The modulus of `cotruncTower n` in degree `k`: `1` in the degrees where the system is the
zero group, and `0` in the degrees where it is `ℤ`. -/
def cotruncMod (n k : ℕ) : ℕ := if k ≤ n then 1 else 0

/-- For `k ≤ n`, the modulus `cotruncMod n k` is `1`. -/
lemma cotruncMod_eq_one {n k : ℕ} (h : k ≤ n) : cotruncMod n k = 1 := ite_eq_left h

/-- For `n < k`, the modulus `cotruncMod n k` is `0`. -/
lemma cotruncMod_eq_zero {n k : ℕ} (h : n < k) : cotruncMod n k = 0 := ite_eq_right (Nat.not_le.2 h)

/-- The moduli of `cotruncTower n` divide each other downwards, which is what makes the reduction
maps of `ZMod` into the transition maps of an inverse system. -/
lemma cotruncMod_dvd {n m k : ℕ} (h : m ≤ k) : cotruncMod n m ∣ cotruncMod n k := by
  rcases le_or_gt k n with hk | hk
  · rw [cotruncMod_eq_one (h.trans hk), cotruncMod_eq_one hk]
  · rw [cotruncMod_eq_zero hk]
    exact dvd_zero _

/-- Reduction from a modulus to itself is the identity. -/
private lemma cotrunc_cast_self {n k : ℕ} (c : ZMod (cotruncMod n k)) :
    (ZMod.castHom (cotruncMod_dvd (n := n) (le_refl k)) (ZMod (cotruncMod n k))) c = c := by
  rw [ZMod.castHom_apply, ZMod.cast_id]

/-- Any two reductions factoring the same reduction of `cotruncMod` agree: there is only one ring
map out of a `ZMod`. -/
private lemma cotrunc_cast_comp {n l m k : ℕ} (h₁ : l ≤ m) (h₂ : m ≤ k)
    (c : ZMod (cotruncMod n k)) :
    (ZMod.castHom (cotruncMod_dvd (n := n) (h₁.trans h₂)) (ZMod (cotruncMod n l))) c =
      (ZMod.castHom (cotruncMod_dvd (n := n) h₁) (ZMod (cotruncMod n l)))
        ((ZMod.castHom (cotruncMod_dvd (n := n) h₂) (ZMod (cotruncMod n m))) c) :=
  (RingHom.congr_fun
    (ZMod.castHom_comp (cotruncMod_dvd (n := n) h₁) (cotruncMod_dvd (n := n) h₂)) c).symm

/-- The inverse system which is the zero group in degrees `≤ n` and `ℤ` in degrees `> n`. -/
def cotruncTower (n : ℕ) : ℕᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj k := AddCommGrpCat.of (ULift.{u} (ZMod (cotruncMod n k.unop)))
  map {_ Y} φ := uliftOfHom.{u}
    (ZMod.castHom (cotruncMod_dvd (n := n) (leOfHom φ.unop))
      (ZMod (cotruncMod n Y.unop))).toAddMonoidHom
  map_id _ := by
    refine AddCommGrpCat.ext fun c => ?_
    exact congrArg ULift.up (cotrunc_cast_self c.down)
  map_comp φ ψ := by
    refine AddCommGrpCat.ext fun c => ?_
    exact congrArg ULift.up (cotrunc_cast_comp (leOfHom ψ.unop) (leOfHom φ.unop) c.down)

/-- In the degrees `≤ n` the system `cotruncTower n` is the zero group. -/
lemma subsingleton_cotruncTower_obj {n k : ℕ} (h : k ≤ n) :
    Subsingleton ((cotruncTower.{u} n).obj (op k)) := by
  change Subsingleton (ULift.{u} (ZMod (cotruncMod n k)))
  rw [cotruncMod_eq_one h]
  infer_instance

/-- **Above `n` the system `cotruncTower n` is not the zero group**, it is `ℤ`.  This is what
makes `cotruncSequence n` below a non-degenerate sequence: were the system zero in every degree,
its sheaf would be zero, the kernel `𝒦ₙ` would be the whole constant sheaf `ℤ`, and the vanishing
proved for `𝒦ₙ` would be a statement about the wrong sheaf. -/
lemma not_subsingleton_cotruncTower_obj {n k : ℕ} (h : n < k) :
    ¬ Subsingleton ((cotruncTower.{u} n).obj (op k)) := by
  change ¬ Subsingleton (ULift.{u} (ZMod (cotruncMod n k)))
  rw [cotruncMod_eq_zero h]
  intro hsub
  have h01 : (ULift.up (0 : ZMod 0) : ULift.{u} (ZMod 0)) = ULift.up (1 : ZMod 0) :=
    hsub.elim _ _
  have h01' : (0 : ZMod 0) = 1 := congrArg ULift.down h01
  exact zero_ne_one h01'

/-- **Above `n` the transition maps of `cotruncTower n` are injective**: both moduli are `0`, so
the reduction map has a reduction map for a retraction. -/
lemma injective_trans_cotruncTower {n m k : ℕ} (hm : n < m) (h : m ≤ k) :
    Function.Injective (trans (cotruncTower.{u} n) h) := by
  have hdvd : cotruncMod n k ∣ cotruncMod n m := by
    rw [cotruncMod_eq_zero hm]
    exact dvd_zero _
  have hretract : ∀ c : ZMod (cotruncMod n k),
      (ZMod.castHom hdvd (ZMod (cotruncMod n k)))
        ((ZMod.castHom (cotruncMod_dvd (n := n) h) (ZMod (cotruncMod n m))) c) = c :=
    fun c => RingHom.congr_fun
      (RingHom.ext_zmod ((ZMod.castHom hdvd (ZMod (cotruncMod n k))).comp
        (ZMod.castHom (cotruncMod_dvd (n := n) h) (ZMod (cotruncMod n m)))) (RingHom.id _)) c
  intro x y hxy
  have hdown : (ZMod.castHom (cotruncMod_dvd (n := n) h) (ZMod (cotruncMod n m))) x.down =
      (ZMod.castHom (cotruncMod_dvd (n := n) h) (ZMod (cotruncMod n m))) y.down :=
    congrArg ULift.down hxy
  refine ULift.ext ?_
  rw [← hretract x.down, ← hretract y.down, hdown]

/-- The reduction of the constant system `ℤ` onto `cotruncTower n`. -/
def cotruncProjection (n : ℕ) : constIntTower.{u} ⟶ cotruncTower.{u} n where
  app k := uliftOfHom.{u} (Int.castAddHom (ZMod (cotruncMod n k.unop)))
  naturality {_ Y} φ := by
    refine AddCommGrpCat.ext fun a => ?_
    exact congrArg ULift.up
      (map_intCast (ZMod.castHom (cotruncMod_dvd (n := n) (leOfHom φ.unop))
        (ZMod (cotruncMod n Y.unop))) a.down).symm

/-- The reduction of `ℤ` onto `cotruncTower n` is surjective in every degree `k`. -/
lemma surjective_cotruncProjection_app (n k : ℕ) :
    Function.Surjective ((cotruncProjection.{u} n).app (op k)) :=
  surjective_uliftOfHom_intCast _

/-- **The sheaf of `cotruncTower n` is flasque.** -/
lemma isFlasque_towerSheaf_cotruncTower (n : ℕ) :
    TopCat.Sheaf.IsFlasque (X := chainSpace.{u}) (towerSheaf (cotruncTower.{u} n)) :=
  isFlasque_towerSheaf_of_const (cotruncProjection.{u} n) (surjective_cotruncProjection_app.{u} n)

/-- **The constant sheaf `ℤ` is flasque on `Chain`**, in its inverse-system spelling. -/
lemma isFlasque_towerSheaf_constIntTower :
    TopCat.Sheaf.IsFlasque (X := chainSpace.{u}) (towerSheaf constIntTower.{u}) :=
  isFlasque_towerSheaf_const _

/-- The transition maps of the constant system `ℤ` are the identity. -/
lemma trans_constIntTower {m n : ℕ} (h : m ≤ n) (z : constIntTower.{u}.obj (op n)) :
    trans constIntTower.{u} h z = z :=
  trans_const h z

/-- The reduction onto `cotruncTower n` commutes with the transition maps; the constant system's
own transitions being identities, this says the reduction of an integer in degree `k` transits to
its reduction in degree `m`.  Stated as one lemma and applied by `exact`: after a rewrite the
constant system's two spellings of the integer are no longer type-correct at `implicit`
transparency. -/
lemma trans_cotruncProjection {n m k : ℕ} (h : m ≤ k) (z : constIntTower.{u}.obj (op k)) :
    trans (cotruncTower.{u} n) h ((cotruncProjection.{u} n).app (op k) z) =
      (cotruncProjection.{u} n).app (op m) z :=
  (trans_naturality (cotruncProjection.{u} n) h z).symm.trans
    (congrArg (fun y => ((cotruncProjection.{u} n).app (op m)) y) (trans_constIntTower h z))

/-- **The reduction `ℤ ⟶ Cₙ` is surjective on global sections.** A compatible family for
`cotruncTower n` over the whole space is killed in the degrees `≤ n` and constant in the degrees
above `n`, where the transition maps are the identity of `ℤ`; so it is the reduction of the
constant family of any integer lifting its coordinate at `n + 1`. -/
lemma surjective_towerPresheafMap_cotruncProjection_app_top (n : ℕ) :
    Function.Surjective ((towerPresheafMap (cotruncProjection.{u} n)).app
      (op (⊤ : Opens Chain.{u}))) := by
  intro t
  obtain ⟨z, hz⟩ := surjective_cotruncProjection_app.{u} n (n + 1) (t.1 ⟨n + 1, le_top⟩)
  refine ⟨constTowerSection z ⊤, towerSections_ext _ fun m => ?_⟩
  change (cotruncProjection.{u} n).app (op m.1) z = t.1 m
  rcases le_or_gt m.1 n with hm | hm
  · exact (subsingleton_cotruncTower_obj.{u} hm).elim _ _
  · refine injective_trans_cotruncTower.{u} (Nat.lt_succ_self n) hm ?_
    exact ((trans_cotruncProjection.{u} hm z).trans hz).trans
      (t.2 ⟨n + 1, le_top⟩ m hm).symm

end CotruncTower

/-! ### Condition (4) of [Stacks, Tag 02UX] over `Chain`, in the inverse-system spelling -/

section Condition4

open Stacks.Cohomology.AbelianColimit

attribute [local instance 10000] HasDerivedCategory.standard

/-- Abelian presheaves on the site of opens of `Chain` admit sheafification. -/
noncomputable local instance hasSheafifyChain'' :
    HasSheafify (Opens.grothendieckTopology Chain.{u}) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite _ _

/-- The short exact sequence `0 ⟶ 𝒦ₙ ⟶ ℤ ⟶ Cₙ ⟶ 0` of abelian sheaves on `Chain`, with `Cₙ` the
sheaf of `cotruncTower n` and `𝒦ₙ` the kernel of the reduction of the constant sheaf `ℤ` onto it.

`𝒦ₙ` is the extension by zero `j_!ℤ_{U n}` (`integerExtensionByZeroIsoKernel`): its sections over
`U k` are `ℤ` for `k ≤ n` and `0` above. -/
noncomputable abbrev cotruncSequence (n : ℕ) :
    ShortComplex (Sheaf (Opens.grothendieckTopology Chain.{u}) AddCommGrpCat.{u}) :=
  ShortComplex.kernelSequence (towerSheafMap (cotruncProjection.{u} n))

/-- The sequence `0 ⟶ 𝒦ₙ ⟶ ℤ ⟶ Cₙ ⟶ 0` of `cotruncSequence n` is short exact. -/
lemma cotruncSequence_shortExact (n : ℕ) : (cotruncSequence.{u} n).ShortExact where
  exact := ShortComplex.kernelSequence_exact _
  mono_f := inferInstance
  epi_g := epi_towerSheafMap _ (surjective_cotruncProjection_app.{u} n)

/-- Flasque sheaves on `Chain` have no higher native cohomology over the whole space.

This goes through `isZero_rightDerived_abSections_of_isFlasque`, whose derived-category universes
are free, rather than through `subsingleton_sheafH_of_isFlasque`, which pins them to `u`: the
`HasDerivedCategory.standard` instance is at `max u (u+1)`, so the pinned form has no instance
here. -/
private lemma isZero_H'functor_of_isFlasque
    (F : Sheaf (Opens.grothendieckTopology Chain.{u}) AddCommGrpCat.{u})
    (hF : TopCat.Sheaf.IsFlasque (X := chainSpace.{u}) F) (p : ℕ) (hp : 0 < p) :
    IsZero ((H'functor (X := Chain.{u}) ⊤ p).obj F) := by
  -- The derived-functor instance is supplied by name: as a composite its search exhausts the
  -- `synthInstance` budget, while each subgoal of the named route gets a fresh one.
  have hpt : ((abSections (X := Chain.{u}) ⊤).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh).HasPointwiseRightDerivedFunctor
        (HomotopyCategory.Plus.quasiIso
          (Sheaf (Opens.grothendieckTopology Chain.{u}) AddCommGrpCat.{u})) :=
    (HomotopyCategory.Plus.localizerMorphism_derives _).hasPointwiseRightDerivedFunctor
  have hplus : ((abSections (X := Chain.{u}) ⊤).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh).HasRightDerivedFunctor
        (HomotopyCategory.Plus.quasiIso
          (Sheaf (Opens.grothendieckTopology Chain.{u}) AddCommGrpCat.{u})) :=
    Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _
  exact (Stacks.Cohomology.FlasqueAbelian.isZero_rightDerived_abSections_of_isFlasque
      (X := Chain.{u}) ⊤ F hF p hp).of_iso
    ((nonempty_H'functor_iso_rightDerived (X := Chain.{u}) ⊤ p).some.app F)

/-- **Condition (4) of [Stacks, Tag 02UX] over `Chain`, in the inverse-system spelling.** The
kernel of the reduction of the constant sheaf `ℤ` onto the sheaf of `cotruncTower n` has
vanishing cohomology in every positive degree.

Both outer terms of `cotruncSequence n` are flasque, hence acyclic, and the reduction is
surjective on global sections; so in the long exact sequence the connecting map out of degree
`p - 1` vanishes — because its source is zero when `p ≥ 2`, and because the preceding map is
surjective when `p = 1` — which makes `Hᵖ(X, 𝒦ₙ) ⟶ Hᵖ(X, ℤ) = 0` a monomorphism. -/
theorem subsingleton_sheafH_cotruncSequence_X₁ (n p : ℕ) (hp : 0 < p) :
    Subsingleton (Sheaf.H.{u, u, u, u} (cotruncSequence.{u} n).X₁ p) := by
  have hS := cotruncSequence_shortExact.{u} n
  have h2 : ∀ q : ℕ, 0 < q →
      IsZero ((H'functor (X := Chain.{u}) ⊤ q).obj (cotruncSequence.{u} n).X₂) :=
    fun q hq => isZero_H'functor_of_isFlasque _ isFlasque_towerSheaf_constIntTower.{u} q hq
  have h3 : ∀ q : ℕ, 0 < q →
      IsZero ((H'functor (X := Chain.{u}) ⊤ q).obj (cotruncSequence.{u} n).X₃) :=
    fun q hq => isZero_H'functor_of_isFlasque _ (isFlasque_towerSheaf_cotruncTower.{u} n) q hq
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  have hδ : H'δ hS ⊤ (rfl : q + 1 = q + 1) = 0 := by
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst hq
      have hepi0 : Epi ((abSections (X := Chain.{u}) ⊤).map (cotruncSequence.{u} n).g) :=
        (AddCommGrpCat.epi_iff_surjective _).2
          (surjective_towerPresheafMap_cotruncProjection_app_top.{u} n)
      have hepi : Epi ((H'functor (X := Chain.{u}) ⊤ 0).map (cotruncSequence.{u} n).g) :=
        epi_map_of_natIso
          (nonempty_H'functor_zero_iso_abSections (X := Chain.{u}) ⊤).some.symm
          (cotruncSequence.{u} n).g hepi0
      have hinst := hepi
      exact zero_of_epi_comp _
        (ShortComplex.mk ((H'functor (X := Chain.{u}) ⊤ 0).map (cotruncSequence.{u} n).g)
          (H'δ hS ⊤ (rfl : 0 + 1 = 0 + 1))
          (postcomp_mk₀_g_comp_postcomp_extClass hS ⊤ rfl)).zero
    · exact (h3 q hq).eq_zero_of_src _
  have hmono : Mono ((H'functor (X := Chain.{u}) ⊤ (q + 1)).map (cotruncSequence.{u} n).f) :=
    (shortComplex_H'_exact₁ hS ⊤ rfl).mono_g hδ
  have hzero :
      IsZero ((H'functor (X := Chain.{u}) ⊤ (q + 1)).obj (cotruncSequence.{u} n).X₁) := by
    rw [IsZero.iff_id_eq_zero]
    refine (cancel_mono ((H'functor (X := Chain.{u}) ⊤ (q + 1)).map
      (cotruncSequence.{u} n).f)).1 ?_
    rw [Category.id_comp, zero_comp]
    exact (h2 (q + 1) (Nat.succ_pos q)).eq_of_tgt _ _
  exact (subsingleton_sheafH_iff_isZero_H'functor _ (q + 1)).2 hzero

/-! ### The extension by zero `j_!ℤ_{U n}` is the kernel `𝒦ₙ`

In degree `k` the kernel of the reduction of the constant system `ℤ` onto `cotruncTower n` is the
subgroup `cotruncKer n k` of `ℤ` — the whole of `ℤ` for `k ≤ n` and `0` above — and its transition
maps are the inclusions of those subgroups, so no case distinction on the degree enters either the
inverse system `kerTower n` or its sheaf, exactly as for `cotruncTower n` itself. The sheaf of that
system is `𝒦ₙ` (`kerSheafIso`); its stalks vanish outside `U n` and its restriction to `U n` is the
constant sheaf `ℤ` of the space `U n`, so it is the extension by zero `j_!ℤ_{U n}` by the
description of the essential image of `j_!` ([Stacks, Tag 00A9]). -/

/-- The kernel of the reduction `ℤ ⟶ ℤ/cotruncMod n k`: all of `ℤ` in the degrees `k ≤ n`, where
the modulus is `1`, and `0` in the degrees above `n`, where it is `0`. -/
def cotruncKer (n k : ℕ) : AddSubgroup ℤ := (Int.castAddHom (ZMod (cotruncMod n k))).ker

/-- An integer lies in `cotruncKer n k` if and only if it vanishes in `ZMod (cotruncMod n k)`. -/
lemma mem_cotruncKer {n k : ℕ} {z : ℤ} :
    z ∈ cotruncKer n k ↔ ((z : ZMod (cotruncMod n k)) = 0) := Iff.rfl

/-- The kernels grow as the degree does, the moduli dividing each other downwards; this is what
makes the inclusions into the transition maps of an inverse system. -/
lemma cotruncKer_le {n m k : ℕ} (h : m ≤ k) : cotruncKer n k ≤ cotruncKer n m := by
  intro z hz
  rw [mem_cotruncKer, ZMod.intCast_zmod_eq_zero_iff_dvd] at hz ⊢
  exact dvd_trans (Int.natCast_dvd_natCast.2 (cotruncMod_dvd (n := n) h)) hz

/-- In the degrees `≤ n` the kernel is all of `ℤ`. -/
lemma mem_cotruncKer_of_le {n k : ℕ} (h : k ≤ n) (z : ℤ) : z ∈ cotruncKer n k := by
  rw [mem_cotruncKer, ZMod.intCast_zmod_eq_zero_iff_dvd, cotruncMod_eq_one h]
  exact one_dvd _

/-- Above `n` the kernel is zero, the reduction being the identity of `ℤ` there. -/
lemma eq_zero_of_mem_cotruncKer {n k : ℕ} (h : n < k) {z : ℤ} (hz : z ∈ cotruncKer n k) :
    z = 0 := by
  rw [mem_cotruncKer, ZMod.intCast_zmod_eq_zero_iff_dvd, cotruncMod_eq_zero h] at hz
  simpa using hz

/-- The inverse system of the kernels of the reductions onto `cotruncTower n`, with the inclusions
of subgroups of `ℤ` for transition maps. -/
def kerTower (n : ℕ) : ℕᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj k := AddCommGrpCat.of (ULift.{u} (cotruncKer n k.unop))
  map {_ _} φ := uliftOfHom.{u} (AddSubgroup.inclusion (cotruncKer_le (n := n) (leOfHom φ.unop)))
  map_id _ := by refine AddCommGrpCat.ext fun c => ?_; rfl
  map_comp _ _ := by refine AddCommGrpCat.ext fun c => ?_; rfl

/-- The inclusion of `kerTower n` into the constant system `ℤ`. -/
def kerIncl (n : ℕ) : kerTower.{u} n ⟶ constIntTower.{u} where
  app k := uliftOfHom.{u} (cotruncKer n k.unop).subtype
  naturality _ _ _ := by refine AddCommGrpCat.ext fun c => ?_; rfl

/-- The sheaf of the inverse system of kernels; it is `𝒦ₙ` by `kerSheafIso`. -/
noncomputable abbrev kerSheaf (n : ℕ) :
    Sheaf (Opens.grothendieckTopology Chain.{u}) AddCommGrpCat.{u} :=
  towerSheaf (kerTower.{u} n)

/-- The composite `kerTower n ⟶ ℤ ⟶ Cₙ` of sheaves is zero: every coordinate of a section of
`towerSheaf (kerTower n)` lies, by construction, in the kernel of the reduction. -/
lemma towerSheafMap_kerIncl_comp (n : ℕ) :
    towerSheafMap (kerIncl.{u} n) ≫ towerSheafMap (cotruncProjection.{u} n) = 0 := by
  refine CategoryTheory.Sheaf.hom_ext
    (NatTrans.ext (funext fun W => AddCommGrpCat.ext fun s => ?_))
  refine towerSections_ext _ fun p => ?_
  change (cotruncProjection.{u} n).app (op p.1) ((kerIncl.{u} n).app (op p.1) (s.1 p)) = 0
  exact congrArg ULift.up (mem_cotruncKer.1 (s.1 p).down.2)

/-- On sections over every open, the morphism of sheaves induced by `kerIncl n` is injective. -/
lemma injective_towerSheafMap_kerIncl_app (n : ℕ) (W : (Opens Chain.{u})ᵒᵖ) :
    Function.Injective ((towerSheafMap (kerIncl.{u} n)).hom.app W) := by
  intro s t hst
  refine towerSections_ext _ fun p => ?_
  have h := congrArg (fun z : towerSections constIntTower.{u} W.unop => (z.1 p).down) hst
  exact ULift.ext (Subtype.ext h)

/-- The inclusion `𝒦ₙ ⟶ ℤ` is injective on sections over every open: it is a monomorphism of
sheaves, and `sheafToPresheaf` preserves limits, hence monomorphisms. -/
lemma injective_cotruncSequence_f_app (n : ℕ) (W : (Opens Chain.{u})ᵒᵖ) :
    Function.Injective (((cotruncSequence.{u} n).f).hom.app W) := by
  have hmono : Mono ((cotruncSequence.{u} n).f) := (cotruncSequence_shortExact.{u} n).mono_f
  have h1 : Mono ((sheafToPresheaf (Opens.grothendieckTopology Chain.{u}) AddCommGrpCat.{u}).map
      ((cotruncSequence.{u} n).f)) := inferInstance
  have h2 : Mono (((cotruncSequence.{u} n).f).hom.app W) := by
    have := h1
    infer_instance
  rw [← AddCommGrpCat.mono_iff_injective]
  exact h2

/-- The comparison `towerSheaf (kerTower n) ⟶ 𝒦ₙ` together with its factorisation through the
inclusion into the constant sheaf `ℤ`, from the universal property of the kernel. -/
noncomputable def kerComparisonData (n : ℕ) :
    { l : kerSheaf.{u} n ⟶ (cotruncSequence.{u} n).X₁ //
      l ≫ (cotruncSequence.{u} n).f = towerSheafMap (kerIncl.{u} n) } :=
  KernelFork.IsLimit.lift' ((cotruncSequence_shortExact.{u} n).exact.fIsKernel)
    (towerSheafMap (kerIncl.{u} n)) (towerSheafMap_kerIncl_comp.{u} n)

/-- The comparison map of sheaves `towerSheaf (kerTower n) ⟶ 𝒦ₙ`. -/
noncomputable def kerComparison (n : ℕ) : kerSheaf.{u} n ⟶ (cotruncSequence.{u} n).X₁ :=
  (kerComparisonData.{u} n).1

/-- The composite of `kerComparison n` with the kernel inclusion `𝒦ₙ ⟶ ℤ` is the morphism of
sheaves induced by `kerIncl n`. -/
lemma kerComparison_comp_f (n : ℕ) :
    kerComparison.{u} n ≫ (cotruncSequence.{u} n).f = towerSheafMap (kerIncl.{u} n) :=
  (kerComparisonData.{u} n).2

/-- On sections, `kerComparison n` followed by the inclusion `𝒦ₙ ⟶ ℤ` is the map induced by
`kerIncl n`. -/
private lemma cotruncSequence_f_app_kerComparison_app (n : ℕ) (W : (Opens Chain.{u})ᵒᵖ)
    (r : (kerSheaf.{u} n).obj.obj W) :
    ((cotruncSequence.{u} n).f).hom.app W ((kerComparison.{u} n).hom.app W r) =
      (towerSheafMap (kerIncl.{u} n)).hom.app W r :=
  congrArg (fun φ : kerSheaf.{u} n ⟶ towerSheaf constIntTower.{u} => (φ.hom.app W) r)
    (kerComparison_comp_f.{u} n)

/-- On sections over every open, `kerComparison n` is injective. -/
lemma injective_kerComparison_app (n : ℕ) (W : (Opens Chain.{u})ᵒᵖ) :
    Function.Injective ((kerComparison.{u} n).hom.app W) := by
  intro s t hst
  refine injective_towerSheafMap_kerIncl_app.{u} n W ?_
  rw [← cotruncSequence_f_app_kerComparison_app, ← cotruncSequence_f_app_kerComparison_app, hst]

/-- The comparison map `kerComparison n` is a monomorphism of sheaves. -/
instance mono_kerComparison (n : ℕ) : Mono (kerComparison.{u} n) :=
  CategoryTheory.Sheaf.mono_of_injective _ (injective_kerComparison_app.{u} n)

/-- Every coordinate of the image in the constant sheaf `ℤ` of a section of `𝒦ₙ` is killed by the
reduction onto `cotruncTower n`: that is the defining property of the kernel, read on sections. -/
lemma cotruncProjection_app_cotruncSequence_f (n : ℕ) (W : (Opens Chain.{u})ᵒᵖ)
    (s : (cotruncSequence.{u} n).X₁.obj.obj W) (p : Index.{u} W.unop) :
    (cotruncProjection.{u} n).app (op p.1)
      ((((cotruncSequence.{u} n).f).hom.app W s).1 p) = 0 :=
  congrArg (fun y : towerSections (cotruncTower.{u} n) W.unop => y.1 p)
    (congrArg (fun φ : (cotruncSequence.{u} n).X₁ ⟶ towerSheaf (cotruncTower.{u} n) =>
      (φ.hom.app W) s) (cotruncSequence.{u} n).zero)

/-- The coordinate at `p` of the image in `ℤ` of a section of `𝒦ₙ` lies in `cotruncKer n p`. -/
lemma mem_cotruncKer_cotruncSequence_f (n : ℕ) (W : (Opens Chain.{u})ᵒᵖ)
    (s : (cotruncSequence.{u} n).X₁.obj.obj W) (p : Index.{u} W.unop) :
    (((((cotruncSequence.{u} n).f).hom.app W s).1 p).down : ℤ) ∈ cotruncKer n p.1 :=
  mem_cotruncKer.2 (congrArg ULift.down
    (cotruncProjection_app_cotruncSequence_f.{u} n W s p))

/-- **The comparison into `𝒦ₙ` is locally surjective.** A section of `𝒦ₙ` over `W` has, on the
basic open of any point of `W`, an image in the constant sheaf `ℤ` which is a constant family whose
value lies in the kernel at that degree; the section of `towerSheaf (kerTower n)` that value
determines is a preimage, the inclusion `𝒦ₙ ⟶ ℤ` being injective. -/
lemma isLocallySurjective_kerComparison (n : ℕ) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology Chain.{u})
      (kerComparison.{u} n).hom where
  imageSieve_mem {W} s := by
    rw [Opens.mem_grothendieckTopology]
    intro x hx
    have hmem := mem_cotruncKer_cotruncSequence_f.{u} n (op (basicOpen.{u} x.down))
      ((cotruncSequence.{u} n).X₁.obj.map (homOfLE (basicOpen_le_of_mem hx)).op s)
      ⟨x.down, le_rfl⟩
    refine ⟨basicOpen.{u} x.down, homOfLE (basicOpen_le_of_mem hx),
      ⟨mkBasicOpenSection (kerTower.{u} n) x.down (ULift.up ⟨_, hmem⟩), ?_⟩,
      self_mem_basicOpen x⟩
    refine injective_cotruncSequence_f_app.{u} n (op (basicOpen.{u} x.down)) ?_
    refine (cotruncSequence_f_app_kerComparison_app.{u} n _ _).trans ?_
    refine towerSections_ext _ fun p => ?_
    have hp : p.1 ≤ x.down := basicOpen_le_basicOpen_iff.1 p.2
    exact (constIntTower_sections_eq
      ((((cotruncSequence.{u} n).f).hom.app (op (basicOpen.{u} x.down)))
        ((cotruncSequence.{u} n).X₁.obj.map (homOfLE (basicOpen_le_of_mem hx)).op s))
      p ⟨x.down, le_rfl⟩ hp)

/-- The comparison map `kerComparison n` is an epimorphism of sheaves. -/
instance epi_kerComparison (n : ℕ) : Epi (kerComparison.{u} n) := by
  have : CategoryTheory.Sheaf.IsLocallySurjective (kerComparison.{u} n) :=
    isLocallySurjective_kerComparison.{u} n
  exact CategoryTheory.Sheaf.epi_of_isLocallySurjective _

/-- **The sheaf of the inverse system of kernels is the kernel `𝒦ₙ`**: the comparison map is a
monomorphism and an epimorphism of abelian sheaves. -/
noncomputable def kerSheafIso (n : ℕ) : kerSheaf.{u} n ≅ (cotruncSequence.{u} n).X₁ := by
  have h1 : Mono (kerComparison.{u} n) := mono_kerComparison.{u} n
  have h2 : Epi (kerComparison.{u} n) := epi_kerComparison.{u} n
  have h3 : IsIso (kerComparison.{u} n) := isIso_of_mono_of_epi _
  exact asIso (kerComparison.{u} n)

/-- The basic open `U n` as a topological space in its own right: the space on which the constant
sheaf `ℤ_{U n}` of condition (4) of [Stacks, Tag 02UX] lives. -/
abbrev basicOpenSpace (n : ℕ) : TopCat.{u} := TopCat.of ↥(basicOpen.{u} n)

/-- **`U n` is an irreducible space**: its opens are the lower sets of `U n`, so each nonempty one
contains the least point. -/
instance preirreducibleSpace_basicOpenSpace (n : ℕ) :
    PreirreducibleSpace (basicOpenSpace.{u} n) where
  isPreirreducible_univ := by
    intro a b ha hb hsa hsb
    obtain ⟨y, -, hy⟩ := hsa
    obtain ⟨z, -, hz⟩ := hsb
    obtain ⟨A', hA', rfl⟩ := isOpen_induced_iff.1 ha
    obtain ⟨B', hB', rfl⟩ := isOpen_induced_iff.1 hb
    refine ⟨⟨ULift.up 0, mem_basicOpen.2 (Nat.zero_le n)⟩, Set.mem_univ _, ?_, ?_⟩
    · exact (Topology.IsLowerSet.isOpen_iff_isLowerSet.1 hA')
        (Nat.zero_le (y.1 : Chain.{u}).down) hy
    · exact (Topology.IsLowerSet.isOpen_iff_isLowerSet.1 hB')
        (Nat.zero_le (z.1 : Chain.{u}).down) hz

/-- The image in `Chain` of an open of the space `U n`; the sections over it are the sections of
the restriction to `U n` of a sheaf on `Chain`. -/
noncomputable abbrev imageOpen (n : ℕ) (W : Opens ↥(basicOpen.{u} n)) : Opens Chain.{u} :=
  (TopCat.Presheaf.ExtensionByInitial.imF (X := chainSpace.{u}) (basicOpen.{u} n)).obj W

/-- A point of `W` sits in the image of `W`, so its basic open is an index of that image. -/
lemma basicOpen_le_imageOpen (n : ℕ) {W : Opens ↥(basicOpen.{u} n)} {y : ↥(basicOpen.{u} n)}
    (hy : y ∈ W) : basicOpen.{u} (y.1 : Chain.{u}).down ≤ imageOpen.{u} n W :=
  basicOpen_le_of_mem (⟨y, hy, rfl⟩ : (y.1 : Chain.{u}) ∈ imageOpen.{u} n W)

/-- Conversely an index of the image of `W` exhibits a point of `W`. -/
lemma exists_mem_of_index (n : ℕ) {W : Opens ↥(basicOpen.{u} n)} {p : ℕ}
    (hp : basicOpen.{u} p ≤ imageOpen.{u} n W) : ∃ y : basicOpenSpace.{u} n, y ∈ W := by
  obtain ⟨y, hy, -⟩ := hp (self_mem_basicOpen (ULift.up p))
  exact ⟨y, hy⟩

/-- An index of the image of an open of `U n` is at most `n`, that image being inside `U n`. -/
lemma le_of_index_imageOpen (n : ℕ) {W : Opens ↥(basicOpen.{u} n)} {p : ℕ}
    (hp : basicOpen.{u} p ≤ imageOpen.{u} n W) : p ≤ n :=
  basicOpen_le_basicOpen_iff.1
    (le_trans hp (TopCat.Presheaf.ExtensionByInitial.imF_le
      (X := chainSpace.{u}) (basicOpen.{u} n) W))

/-- All coordinates of a section of `towerSheaf (kerTower n)` have the same underlying integer,
the transition maps being inclusions of subgroups of `ℤ`. -/
lemma kerTower_sections_down_eq (n : ℕ) {V : Opens Chain.{u}}
    (σ : towerSections (kerTower.{u} n) V) (p q : Index.{u} V) :
    ((σ.1 p).down : ℤ) = ((σ.1 q).down : ℤ) := by
  have hr : basicOpen.{u} (min p.1 q.1) ≤ V :=
    le_trans (monotone_basicOpen (min_le_left _ _)) p.2
  have hp := σ.2 ⟨min p.1 q.1, hr⟩ p (min_le_left _ _)
  have hq := σ.2 ⟨min p.1 q.1, hr⟩ q (min_le_right _ _)
  exact (congrArg (fun w => ((w.down : ℤ))) hp).trans
    (congrArg (fun w => ((w.down : ℤ))) hq).symm

/-- **The constant sheaf `ℤ` on the space `U n` maps to the restriction of `𝒦ₙ` to `U n`.** On an
open `W` of `U n` the constant sheaf is the explicit model of [Stacks, Tag 02UW] — one integer, and
nothing at all over the empty open — and that integer goes to the compatible family having it in
every degree, which is a family of `kerTower n` because every degree of the image of `W` is at
most `n`, where the kernel is the whole of `ℤ`. -/
noncomputable def modelToKerSheaf (n : ℕ) :
    Stacks.CohomologyVanishing.irreducibleConstantModelSheaf (basicOpenSpace.{u} n)
        (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶
      (Opens.sheafRestrict (X := chainSpace.{u}) (basicOpen.{u} n)).obj (kerSheaf.{u} n) :=
  ⟨{ app := fun _ => AddCommGrpCat.ofHom
      { toFun := fun s => ⟨fun p => ULift.up ⟨(s ⟨exists_mem_of_index n p.2⟩).down,
            mem_cotruncKer_of_le (le_of_index_imageOpen n p.2) _⟩,
          fun _ _ _ => ULift.ext (Subtype.ext
            (congrArg (fun w => (s w).down) (Subsingleton.elim _ _)))⟩
        map_zero' := towerSections_ext _ fun _ => rfl
        map_add' := fun _ _ => towerSections_ext _ fun _ => rfl }
     naturality := fun _ _ _ => AddCommGrpCat.ext fun s =>
       towerSections_ext _ fun _ => ULift.ext (Subtype.ext
         (congrArg (fun w => (s w).down) (Subsingleton.elim _ _))) }⟩

/-- That map is bijective on sections over every open `W` of `U n`: over a nonempty `W` both sides
are `ℤ`, read off at any index of the image of `W`, and over the empty open the image has no index
at all and both sides are zero. -/
lemma bijective_modelToKerSheaf_app (n : ℕ) (W : (Opens ↥(basicOpen.{u} n))ᵒᵖ) :
    Function.Bijective ((modelToKerSheaf.{u} n).hom.app W) := by
  refine ⟨fun s t hst => ?_, fun σ => ?_⟩
  · funext w
    obtain ⟨y, hy⟩ := w.down
    have hp : basicOpen.{u} (y.1 : Chain.{u}).down ≤ imageOpen.{u} n W.unop :=
      basicOpen_le_imageOpen n hy
    have h := congrArg (fun σ : towerSections (kerTower.{u} n) (imageOpen.{u} n W.unop) =>
      ((σ.1 ⟨(y.1 : Chain.{u}).down, hp⟩).down : ℤ)) hst
    exact ULift.ext <|
      (congrArg (fun z => (s z).down) (Subsingleton.elim w ⟨exists_mem_of_index n hp⟩)).trans
      (h.trans (congrArg (fun z => (t z).down)
        (Subsingleton.elim ⟨exists_mem_of_index n hp⟩ w)))
  · by_cases hW : ∃ y : basicOpenSpace.{u} n, y ∈ W.unop
    · obtain ⟨y, hy⟩ := hW
      refine ⟨fun _ => ULift.up ((σ.1 ⟨(y.1 : Chain.{u}).down,
        basicOpen_le_imageOpen n hy⟩).down : ℤ), towerSections_ext _ fun p => ?_⟩
      exact ULift.ext (Subtype.ext (kerTower_sections_down_eq n σ
        ⟨(y.1 : Chain.{u}).down, basicOpen_le_imageOpen n hy⟩ p))
    · exact ⟨0, towerSections_ext _ fun p => absurd (exists_mem_of_index n p.2) hW⟩

/-- **The restriction of `𝒦ₙ` to `U n` is the constant sheaf `ℤ` of the space `U n`.** -/
noncomputable def integerConstantSheafIsoRestrict (n : ℕ) :
    Stacks.Sheaves.ConstantIntegerSubsheaves.integerConstantSheaf (basicOpenSpace.{u} n) ≅
      (Opens.sheafRestrict (X := chainSpace.{u}) (basicOpen.{u} n)).obj
        ((cotruncSequence.{u} n).X₁) := by
  have happ : ∀ W, IsIso ((modelToKerSheaf.{u} n).hom.app W) := fun W =>
    (ConcreteCategory.isIso_iff_bijective _).2 (bijective_modelToKerSheaf_app.{u} n W)
  have hhom : IsIso ((modelToKerSheaf.{u} n).hom) := NatIso.isIso_of_isIso_app _
  letI hmap : IsIso ((sheafToPresheaf (Opens.grothendieckTopology (basicOpenSpace.{u} n))
      AddCommGrpCat.{u}).map (modelToKerSheaf.{u} n)) := hhom
  letI hiso : IsIso (modelToKerSheaf.{u} n) :=
    isIso_of_fully_faithful (sheafToPresheaf _ _) _
  exact Stacks.CohomologyVanishing.constantSheafIsoIrreducibleModel _ _ ≪≫
    @asIso _ _ _ _ (modelToKerSheaf.{u} n) hiso ≪≫
    (Opens.sheafRestrict (X := chainSpace.{u}) (basicOpen.{u} n)).mapIso (kerSheafIso.{u} n)

/-- **Above `n` the sheaf `𝒦ₙ` has no nonzero section over `U m`**: the image in the constant sheaf
`ℤ` of such a section is a constant family whose value is killed by the reduction modulo `0`. -/
lemma subsingleton_cotruncSequence_X₁_app (n m : ℕ) (h : n < m) :
    Subsingleton ((cotruncSequence.{u} n).X₁.obj.obj (op (basicOpen.{u} m))) := by
  have key : ∀ σ : (cotruncSequence.{u} n).X₁.obj.obj (op (basicOpen.{u} m)),
      ∀ p : Index.{u} (basicOpen.{u} m),
      ((((cotruncSequence.{u} n).f).hom.app (op (basicOpen.{u} m))) σ).1 p = 0 := by
    intro σ p
    refine (constIntTower_sections_eq
      ((((cotruncSequence.{u} n).f).hom.app (op (basicOpen.{u} m))) σ)
      p ⟨m, le_rfl⟩ (basicOpen_le_basicOpen_iff.1 p.2)).symm.trans (ULift.ext ?_)
    exact eq_zero_of_mem_cotruncKer h
      (mem_cotruncKer_cotruncSequence_f.{u} n (op (basicOpen.{u} m)) σ ⟨m, le_rfl⟩)
  refine ⟨fun s t => injective_cotruncSequence_f_app.{u} n _ (towerSections_ext _ fun p => ?_)⟩
  rw [key s p, key t p]

/-- **The stalks of `𝒦ₙ` vanish outside `U n`**: the smallest open neighbourhood of a point above
`n` is a basic open, over which `𝒦ₙ` has no nonzero section. -/
lemma isZero_stalk_cotruncSequence_X₁ (n : ℕ) (x : Chain.{u}) (hx : x ∉ basicOpen.{u} n) :
    IsZero (TopCat.Presheaf.stalk (X := chainSpace.{u}) ((cotruncSequence.{u} n).X₁).obj x) := by
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  have hn : n < x.down := Nat.not_le.1 fun hle => hx (mem_basicOpen.2 hle)
  have hsub := subsingleton_cotruncSequence_X₁_app.{u} n x.down hn
  refine ⟨fun a b => ?_⟩
  obtain ⟨V, hxV, s, hs⟩ :=
    TopCat.Presheaf.exists_germ_eq (X := chainSpace.{u}) ((cotruncSequence.{u} n).X₁).obj a
  obtain ⟨V', hxV', t, ht⟩ :=
    TopCat.Presheaf.exists_germ_eq (X := chainSpace.{u}) ((cotruncSequence.{u} n).X₁).obj b
  refine hs.symm.trans (Eq.trans ?_ ht)
  refine (TopCat.Presheaf.germ_res_apply (X := chainSpace.{u}) ((cotruncSequence.{u} n).X₁).obj
    (homOfLE (basicOpen_le_of_mem hxV)) x (self_mem_basicOpen x) s).symm.trans ?_
  refine Eq.trans ?_ (TopCat.Presheaf.germ_res_apply (X := chainSpace.{u})
    ((cotruncSequence.{u} n).X₁).obj
    (homOfLE (basicOpen_le_of_mem hxV')) x (self_mem_basicOpen x) t)
  exact congrArg (fun y => TopCat.Presheaf.germ (X := chainSpace.{u})
    ((cotruncSequence.{u} n).X₁).obj
    (basicOpen.{u} x.down) x (self_mem_basicOpen x) y) (Subsingleton.elim _ _)

/-- **`𝒦ₙ` is the extension by zero of its own restriction to `U n`.** Its stalks vanish off `U n`,
so the counit of `j_! ⊣ j^{-1}` at it is an isomorphism ([Stacks, Tag 00A9]). -/
noncomputable def jExtRestrictIsoKernel (n : ℕ) :
    (ExtensionByZero.jExt (X := chainSpace.{u}) (basicOpen.{u} n)).obj
        ((ExtensionByZero.restrict (X := chainSpace.{u}) (basicOpen.{u} n)).obj
          ((cotruncSequence.{u} n).X₁)) ≅ (cotruncSequence.{u} n).X₁ := by
  letI h := ExtensionByZero.jExt_counit_isIso_of_vanishing (X := chainSpace.{u})
    (basicOpen.{u} n) ((cotruncSequence.{u} n).X₁)
    (fun x hx => isZero_stalk_cotruncSequence_X₁.{u} n x hx)
  exact @asIso _ _ _ _ _ h

/-- **The extension by zero `j_!ℤ_{U n}` is the kernel `𝒦ₙ`** of the reduction of the constant
sheaf `ℤ` onto the sheaf of `cotruncTower n`. This is the identification through which condition
(4) of [Stacks, Tag 02UX] over `Chain` is proved in the `j_!ℤ_U` spelling. -/
noncomputable def integerExtensionByZeroIsoKernel (n : ℕ) :
    Stacks.Sheaves.ConstantIntegerSubsheaves.integerExtensionByZero chainSpace.{u}
        (basicOpen.{u} n) ≅ (cotruncSequence.{u} n).X₁ :=
  (ExtensionByZero.jExt (X := chainSpace.{u}) (basicOpen.{u} n)).mapIso
      (integerConstantSheafIsoRestrict.{u} n) ≪≫ jExtRestrictIsoKernel.{u} n

/-- The sheaf `towerSheaf (kerTower n)` has `ℤ` for its sections over `U n`, so it is not the zero
sheaf. -/
lemma not_subsingleton_kerSheaf_app (n : ℕ) :
    ¬ Subsingleton ((kerSheaf.{u} n).obj.obj (op (basicOpen.{u} n))) := by
  intro hsub
  have h0 : (0 : ℤ) ∈ cotruncKer n n := mem_cotruncKer_of_le le_rfl 0
  have h1 : (1 : ℤ) ∈ cotruncKer n n := mem_cotruncKer_of_le le_rfl 1
  have hEq := hsub.elim
    (mkBasicOpenSection (kerTower.{u} n) n (ULift.up ⟨0, h0⟩))
    (mkBasicOpenSection (kerTower.{u} n) n (ULift.up ⟨1, h1⟩))
  have hcoord := congrArg
    (fun σ : towerSections (kerTower.{u} n) (basicOpen.{u} n) => ((σ.1 ⟨n, le_rfl⟩).down : ℤ)) hEq
  have h01 : (0 : ℤ) = 1 := hcoord
  exact absurd h01 (by norm_num)

/-- **The extension by zero `j_!ℤ_{U n}` is not the zero sheaf**: its sections over `U n` are `ℤ`.
So the vanishing of its higher cohomology proved below is a statement about a nonzero sheaf, as
`not_subsingleton_cotruncTower_obj` is for the quotient. -/
lemma not_subsingleton_integerExtensionByZero_app (n : ℕ) :
    ¬ Subsingleton ((Stacks.Sheaves.ConstantIntegerSubsheaves.integerExtensionByZero
      chainSpace.{u} (basicOpen.{u} n)).obj.obj (op (basicOpen.{u} n))) := by
  intro hsub
  refine not_subsingleton_kerSheaf_app.{u} n ⟨fun a b => ?_⟩
  have e := kerSheafIso.{u} n ≪≫ (integerExtensionByZeroIsoKernel.{u} n).symm
  have key : ∀ y : (kerSheaf.{u} n).obj.obj (op (basicOpen.{u} n)),
      (e.inv.hom.app (op (basicOpen.{u} n))) ((e.hom.hom.app (op (basicOpen.{u} n))) y) = y :=
    fun y => congrArg (fun φ : kerSheaf.{u} n ⟶ kerSheaf.{u} n => (φ.hom.app _) y) e.hom_inv_id
  rw [← key a, ← key b, hsub.elim ((e.hom.hom.app _) a) ((e.hom.hom.app _) b)]

/-- **Condition (4) of [Stacks, Tag 02UX] over `Chain`, for a basic open.** The vanishing
`Hᵖ(X, j_!ℤ_{U n}) = 0` for every `p > 0`: the extension by zero is the kernel `𝒦ₙ` of the
reduction of the constant sheaf `ℤ` onto the sheaf of `cotruncTower n`
(`integerExtensionByZeroIsoKernel`), whose higher cohomology vanishes by
`subsingleton_sheafH_cotruncSequence_X₁`.  The quasi-compact opens of `Chain` are `∅` and the
`U n`, so together with the vanishing for `U = ∅` — where the sheaf is zero — this is the whole of
condition (4) over `Chain`. -/
theorem subsingleton_sheafH_integerExtensionByZero_basicOpen (n : ℕ)
    (p : ℕ) (hp : 0 < p) :
    Subsingleton (Sheaf.H.{u, u, u, u}
      (Stacks.Sheaves.ConstantIntegerSubsheaves.integerExtensionByZero chainSpace.{u}
        (basicOpen.{u} n)) p) := by
  have hzero := (subsingleton_sheafH_iff_isZero_H'functor _ p).1
    (subsingleton_sheafH_cotruncSequence_X₁.{u} n p hp)
  exact (subsingleton_sheafH_iff_isZero_H'functor _ p).2
    (hzero.of_iso ((H'functor (X := Chain.{u}) ⊤ p).mapIso
      (integerExtensionByZeroIsoKernel.{u} n)))

/-- No point of `Chain` lies in the empty open. -/
lemma notMem_bot (x : Chain.{u}) : x ∉ (⊥ : Opens Chain.{u}) := fun hc => Opens.mem_bot.1 hc

/-- The extension by zero from the empty open is the zero sheaf: every one of its stalks
vanishes, every point lying outside `∅`. -/
lemma isZero_integerExtensionByZero_bot :
    IsZero (Stacks.Sheaves.ConstantIntegerSubsheaves.integerExtensionByZero chainSpace.{u}
      (⊥ : Opens Chain.{u})) := by
  rw [TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero]
  intro x
  change IsZero ((Stacks.Sheaves.ConstantIntegerSubsheaves.integerExtensionByZero chainSpace.{u}
    (⊥ : Opens Chain.{u})).presheaf.stalk x)
  exact TopCat.Presheaf.isZero_stalk_extendByInitialSheafify (X := chainSpace.{u})
    (⊥ : Opens Chain.{u})
    (Stacks.Sheaves.ConstantIntegerSubsheaves.integerConstantSheaf
      (TopCat.of ((⊥ : Opens Chain.{u}) : Type u))).obj (notMem_bot.{u} x)

/-- **Condition (4) of [Stacks, Tag 02UX] holds for the empty open**, the sheaf being zero. -/
theorem subsingleton_sheafH_integerExtensionByZero_bot (p : ℕ) :
    Subsingleton (Sheaf.H.{u, u, u, u}
      (Stacks.Sheaves.ConstantIntegerSubsheaves.integerExtensionByZero chainSpace.{u}
        (⊥ : Opens Chain.{u})) p) :=
  (subsingleton_sheafH_iff_isZero_H'functor _ p).2
    (Functor.map_isZero (H'functor (X := Chain.{u}) ⊤ p) isZero_integerExtensionByZero_bot.{u})

/-- **Condition (4) of [Stacks, Tag 02UX] over `Chain`**: the vanishing `Hᵖ(X, j_!ℤ_U) = 0` for
every `p > 0` and every quasi-compact open `U` of `Chain`.  The quasi-compact opens are `∅` and
the `U n`, the whole space not being quasi-compact; over `∅` the sheaf is zero, and over `U n` the
extension by zero is the kernel `𝒦ₙ` of the reduction of the constant sheaf `ℤ` onto the sheaf of
`cotruncTower n`, whose higher cohomology vanishes.

This is the condition the source leaves to the reader.  Together with
`hasBasisOfCompactOpens_chain` and `interCompactOpenIsCompact_chain` it makes `Chain` satisfy
conditions (2), (3) and (4) of [Stacks, Tag 02UX] with `d = 0`, while
`exists_not_subsingleton_sheafH_one` denies the conclusion. -/
@[stacks 0BX0 "condition (4) of Tag 02UX for this space, which the source leaves to the reader: \
H^p(X, j_!ℤ_U) = 0 for every p > 0 and every quasi-compact open U"]
theorem subsingleton_sheafH_integerExtensionByZero
    (U : Opens Chain.{u}) (hU : IsCompact (U : Set Chain.{u})) (p : ℕ) (hp : 0 < p) :
    Subsingleton (Sheaf.H.{u, u, u, u}
      (Stacks.Sheaves.ConstantIntegerSubsheaves.integerExtensionByZero chainSpace.{u} U) p) := by
  rcases eq_bot_or_eq_top_or_eq_basicOpen U with hUb | hUt | ⟨n, hUn⟩
  · subst hUb
    exact subsingleton_sheafH_integerExtensionByZero_bot.{u} p
  · subst hUt
    rw [Opens.coe_top] at hU
    exact absurd hU not_isCompact_univ.{u}
  · subst hUn
    exact subsingleton_sheafH_integerExtensionByZero_basicOpen.{u} n p hp

end Condition4

end Stacks.CohomologyVanishing.ChainOfOpens

end
