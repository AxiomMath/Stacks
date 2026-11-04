module

public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.DeterminantInvertible
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankBaseOpen
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RankDecomposition

/-!
# Finite local freeness of a given rank over an open, produced and read off

A module `M` on a scheme `X` and an open `V ⊆ X` give the hypothesis

`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (M.over V) r`,

"`M` is finite locally free of rank `r` over `V`", in the slice-site spelling of
[Stacks, Tag 01C6] — the *generic rank* hypothesis of [Stacks, Tag 0B3N] and of
[Stacks, Tag 0B3T] when `V` is nonempty and `X` is integral. This file produces that hypothesis
from local free presentations and reads local free presentations off it.

## The crossing

The hypothesis lives on the slice site `Opens(X)/V`, while every local free presentation the
library produces lives on `Opens(X)` — as an isomorphism `free I ≅ M.over W` for an open `W` of
`X`, or as `M.restrict W.ι ≅ free I`. Crossing from one to the other needs the trivialisation to
be moved *up* from the slice over `W` to the iterated slice over an object of `Opens(X)/V`, and
`AlgebraicGeometry.Scheme.Modules.freeIsoOverLeft` only moves it *down*. The equivalence
`Stacks.SheafOfModules.sliceEquiv` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SliceRestrictionColimits.lean` is what makes the
upward direction available; `freeIsoOverSlice` below is the resulting converse of
`freeIsoOverLeft`, and everything else in this file is bookkeeping on top of it.

## Main definitions

The elided prefix is `AlgebraicGeometry.Scheme.Modules`.

* `freeIsoOverSlice`: **the converse of
  `AlgebraicGeometry.Scheme.Modules.freeIsoOverLeft`** — a trivialisation of `M` on the slice
  over `W.left` is one of `M.over V` on the iterated slice over `W`.

## Main results

* `isFiniteLocallyFreeOfRank_over_of_forall_freeIso`: **the producer.** A module which is free
  on a type with `r` elements near every point of `V` is finite locally free of rank `r` over
  `V`. Each of the three forms a local free presentation comes in feeds this: `free I ≅ M.over W`
  directly, `M.restrict W.ι ≅ free I` through
  `AlgebraicGeometry.Scheme.Modules.overIsoOfRestrictIso`.
* `exists_freeIso_of_isFiniteLocallyFreeOfRank_over`: **the reader.** Conversely, a module
  finite locally free of rank `r` over `V` is free on an `r`-element type near every point of
  `V`.
* `isFiniteLocallyFreeOfRank_over_of_le`: **the rank hypothesis shrinks to a smaller open.**
* `isFiniteLocallyFreeOfRank_over`: **a globally finite locally free module of rank `r` has
  rank `r` over every open**, which is the base case of every propagation.
* `isFiniteLocallyFreeOfRank_over_pullback`: **the rank hypothesis crosses a morphism**, from
  `V` downstairs to `q ⁻¹ᵁ V` upstairs, with no hypothesis on `q`. This is the half of the
  generic-rank hypothesis of [Stacks, Tag 0B3T] that concerns `b^*Ω` rather than `Ω` upstairs.

## Implementation notes

The producer indexes its covering family by the points of `V` rather than by a cover: the
trivialising opens are `W x ⊓ V` for `x ∈ V`, which lie over `V` on the nose, so the covering
sieve is the pointwise condition that defines `TopologicalSpace.Opens.grothendieckTopology`
and no refinement of a cover is needed. The index type is `X` itself (with the membership
carried in the sieve witness), which keeps it in `Type u`.

`isFiniteLocallyFreeOfRank_over_of_le` is proved directly from the local generators data rather
than by composing the reader with the producer, which would be the same proof with an extra
`Classical.choice`.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 0B3N](https://stacks.math.columbia.edu/tag/0B3N)
* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-! ### Trivialisations move up to an iterated slice -/

/-- **A trivialisation on the slice site below an iterated slice lifts to it.** An isomorphism
of `M.over W.left` with the free module on a finite index type `I`, on the slice site over the
open `W.left`, gives an isomorphism of `(M.over V).over W` with the free module on `I`, on the
iterated slice site `(Opens X / V) / W`.

This is the converse of `AlgebraicGeometry.Scheme.Modules.freeIsoOverLeft`, and unlike it needs
no comparison of pushforwards: `Stacks.SheafOfModules.sliceEquiv` is an *equivalence* between
sheaves of modules on the two sites, `Stacks.SheafOfModules.sliceEquivObjIso` says it carries
`M.over W.left` to `(M.over V).over W`, and `SheafOfModules.mapFreeIso` carries the free module
along it because an equivalence preserves coproducts. -/
def freeIsoOverSlice (M : X.Modules) (V : X.Opens) (W : Over V) (I : Type u) [Finite I]
    (e : _root_.SheafOfModules.free.{u} I ≅ M.over W.left) :
    _root_.SheafOfModules.free.{u} I ≅ (M.over V).over W :=
  letI Φ := (Stacks.SheafOfModules.sliceEquiv X.ringCatSheaf V W).functor
  letI : PreservesColimitsOfShape (Discrete I) Φ := preservesColimitsOfShape_of_discrete _
  _root_.SheafOfModules.mapFreeIso Φ I
      (Stacks.SheafOfModules.sliceEquivUnitIso X.ringCatSheaf V W).symm ≪≫
    Φ.mapIso e ≪≫ Stacks.SheafOfModules.sliceEquivObjIso M V W

/-! ### The producer -/

/-- **A module free on an `r`-element type near every point of an open is finite locally free of
rank `r` over that open.**

The trivialising family is `fun x => W x ⊓ V`, indexed by the points of `X`; it covers `V`
because `W x` contains `x`, and the covering sieve asked for by
`TopologicalSpace.Opens.grothendieckTopology` is exactly that pointwise condition.
`Stacks.SheafOfModules.freeIsoOverMap` cuts each trivialisation down to `W x ⊓ V` and
`AlgebraicGeometry.Scheme.Modules.freeIsoOverSlice` lifts it to the iterated slice, which is
where `Stacks.SheafOfModules.isFiniteLocallyFreeOfRank_of_free_iso` reads it. -/
theorem isFiniteLocallyFreeOfRank_over_of_forall_freeIso (M : X.Modules) (V : X.Opens) (r : ℕ)
    (h : ∀ x : X, x ∈ V → ∃ (W : X.Opens) (_ : x ∈ W) (I : Type u) (_ : Nonempty (I ≃ Fin r)),
      Nonempty (_root_.SheafOfModules.free.{u} I ≅ M.over W)) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (M.over V) r := by
  classical
  have h' : ∀ y : {x : X // x ∈ V}, ∃ (W : X.Opens) (_ : (y : X) ∈ W) (I : Type u)
      (_ : Nonempty (I ≃ Fin r)), Nonempty (_root_.SheafOfModules.free.{u} I ≅ M.over W) :=
    fun y => h y.1 y.2
  choose W hW I hI e using h'
  have hfin : ∀ y, Finite (I y) := fun y => Finite.of_equiv _ (hI y).some.symm
  refine Stacks.SheafOfModules.isFiniteLocallyFreeOfRank_of_free_iso r
    (fun y : {x : X // x ∈ V} => Over.mk (homOfLE (inf_le_right : W y ⊓ V ≤ V))) ?_ fun y =>
      (_root_.SheafOfModules.freeFunctor.mapIso
        ((hI y).some.trans Equiv.ulift.symm).toIso).symm ≪≫
      freeIsoOverSlice M V (Over.mk (homOfLE (inf_le_right : W y ⊓ V ≤ V))) _
        (Stacks.SheafOfModules.freeIsoOverMap M (homOfLE inf_le_left) _ (e y).some)
  refine Stacks.SheafOfModules.coversTop_over_of_ofArrows_mem (Opens.grothendieckTopology ↑X) V
    (fun y : {x : X // x ∈ V} => W y ⊓ V) (fun _ => homOfLE inf_le_right) ?_
  intro x hx
  exact ⟨_, homOfLE inf_le_right, Sieve.ofArrows_mk _ _ ⟨x, hx⟩, ⟨hW ⟨x, hx⟩, hx⟩⟩

/-- A module free on an `r`-element type near every point of an open, with the trivialisations
given in the `AlgebraicGeometry.Scheme.Modules.restrictFunctor` spelling, is finite locally free
of rank `r` over that open. -/
theorem isFiniteLocallyFreeOfRank_over_of_forall_restrictIso (M : X.Modules) (V : X.Opens)
    (r : ℕ)
    (h : ∀ x : X, x ∈ V → ∃ (W : X.Opens) (_ : x ∈ W) (I : Type u) (_ : Nonempty (I ≃ Fin r)),
      Nonempty ((restrictFunctor W.ι).obj M ≅ _root_.SheafOfModules.free.{u} I)) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (M.over V) r := by
  refine isFiniteLocallyFreeOfRank_over_of_forall_freeIso M V r fun x hx => ?_
  obtain ⟨W, hW, I, hI, ⟨e⟩⟩ := h x hx
  exact ⟨W, hW, I, hI, ⟨overIsoOfRestrictIso M W I e⟩⟩

/-! ### The reader -/

/-- **A module finite locally free of rank `r` over an open is free on an `r`-element type near
every point of that open.** The trivialising covering family of `M.over V` lives on the slice
site over `V`; one of its members has an underlying open containing the given point
(`AlgebraicGeometry.Scheme.Modules.exists_mem_left_of_coversTop`), and
`AlgebraicGeometry.Scheme.Modules.freeIsoOverLeft` descends the trivialisation there from the
iterated slice to the slice over that open. -/
theorem exists_freeIso_of_isFiniteLocallyFreeOfRank_over (M : X.Modules) (V : X.Opens) (r : ℕ)
    [h : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (M.over V) r] {x : X} (hx : x ∈ V) :
    ∃ (W : X.Opens) (_ : x ∈ W) (I : Type u) (_ : Nonempty (I ≃ Fin r)),
      Nonempty (_root_.SheafOfModules.free.{u} I ≅ M.over W) := by
  obtain ⟨q, hq, hrank⟩ := h.exists_isFiniteLocallyFreeOfRankData
  obtain ⟨i, hxi⟩ := exists_mem_left_of_coversTop V q.X q.coversTop hx
  have : Finite (q.generators i).I := Finite.of_equiv _ (hrank i).some.symm
  have : IsIso (q.generators i).π := hq.isIso i
  exact ⟨(q.X i).left, hxi, (q.generators i).I, hrank i,
    ⟨freeIsoOverLeft M V (q.X i) _ (asIso (q.generators i).π)⟩⟩

/-- A module finite locally free of rank `r` over an open is free on an `r`-element type near
every point of that open, in the `AlgebraicGeometry.Scheme.Modules.restrictFunctor` spelling. -/
theorem exists_restrictIso_of_isFiniteLocallyFreeOfRank_over (M : X.Modules) (V : X.Opens)
    (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (M.over V) r] {x : X}
    (hx : x ∈ V) :
    ∃ (W : X.Opens) (_ : x ∈ W) (I : Type u) (_ : Nonempty (I ≃ Fin r)),
      Nonempty ((restrictFunctor W.ι).obj M ≅ _root_.SheafOfModules.free.{u} I) := by
  obtain ⟨W, hW, I, hI, ⟨e⟩⟩ := exists_freeIso_of_isFiniteLocallyFreeOfRank_over M V r hx
  exact ⟨W, hW, I, hI, ⟨restrictIsoFreeOfOverIso M W I e⟩⟩

/-! ### Consequences -/

/-- **The rank hypothesis over an open shrinks to a smaller open.** -/
theorem isFiniteLocallyFreeOfRank_over_of_le (M : X.Modules) {U V : X.Opens} (hVU : V ≤ U)
    (r : ℕ) [h : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (M.over U) r] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (M.over V) r :=
  isFiniteLocallyFreeOfRank_over_of_forall_freeIso M V r fun _ hx =>
    exists_freeIso_of_isFiniteLocallyFreeOfRank_over M U r (hVU hx)

/-- **A globally finite locally free module of rank `r` is finite locally free of rank `r` over
every open.** This is the base case of a propagation of the generic-rank hypothesis along a
chain of morphisms. -/
theorem isFiniteLocallyFreeOfRank_over (M : X.Modules) (V : X.Opens) (r : ℕ)
    [h : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (M.over V) r := by
  refine isFiniteLocallyFreeOfRank_over_of_forall_freeIso M V r fun x _ => ?_
  obtain ⟨q, hq, hrank⟩ := h.exists_isFiniteLocallyFreeOfRankData
  have hsup : iSup q.X = ⊤ := (Opens.coversTop_iff X q.X).1 q.coversTop
  have hx' : x ∈ iSup q.X := by rw [hsup]; trivial
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.1 hx'
  have : IsIso (q.generators i).π := hq.isIso i
  exact ⟨q.X i, hxi, (q.generators i).I, hrank i, ⟨asIso (q.generators i).π⟩⟩

/-- **The rank hypothesis over an open crosses an arbitrary morphism of schemes.** If `M` is
finite locally free of rank `r` over `V ⊆ X` then `q^*M` is finite locally free of rank `r` over
`q ⁻¹ᵁ V ⊆ T`, for every `q : T ⟶ X`.

No hypothesis on `q` is needed: a local free presentation of `M` on an open `W` pulls back to
one of `q^*M` on `q ⁻¹ᵁ W`, which is
`AlgebraicGeometry.Scheme.Modules.restrictPullbackIsoFree`. -/
theorem isFiniteLocallyFreeOfRank_over_pullback {T : Scheme.{u}} (M : X.Modules) (q : T ⟶ X)
    (V : X.Opens) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (M.over V) r] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (((pullback q).obj M).over (q ⁻¹ᵁ V)) r := by
  refine isFiniteLocallyFreeOfRank_over_of_forall_restrictIso _ _ r fun t ht => ?_
  obtain ⟨W, hW, I, hI, ⟨e⟩⟩ :=
    exists_restrictIso_of_isFiniteLocallyFreeOfRank_over M V r (x := q.base t) ht
  exact ⟨q ⁻¹ᵁ W, hW, I, hI, ⟨restrictPullbackIsoFree M q W I e⟩⟩

end AlgebraicGeometry.Scheme.Modules

end
