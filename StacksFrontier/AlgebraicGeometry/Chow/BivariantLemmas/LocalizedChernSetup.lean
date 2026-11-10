module

public import StacksFrontier.AlgebraicGeometry.Chow.Vocabulary
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Defs
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Unconditional
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksCore.Tactic.StacksAttribute

/-!
# The situation for localized Chern classes

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S`, let `i : Z ⟶ X` be a closed immersion, let `E` be an object of
`D(𝒪_X)` and let `p ≥ 0`. The localized Chern class `c_p(Z ⟶ X, E)` and the localized Chern
character component `P_p(Z ⟶ X, E)` are constructed under three hypotheses: `E` is perfect, `E`
restricted to `X \ Z` is zero (respectively a finite locally free module of rank `< p` in degree
`0`), and one of four technical finiteness alternatives holds on `X` or on a representative of
`E`. This file is that standing situation.

## Main definitions

* `Stacks.Chow.IsFiniteLocallyFreeOfRankLT` — a finite locally free module whose rank is
  everywhere below a given bound.
* `Stacks.Chow.IsLocallyBoundedFiniteLocallyFree` — a complex of finite locally free modules
  whose terms vanish outside a finite range of degrees near each point.
* `Stacks.Chow.LocalizedChernSituation` — the standing situation.

## Main results

* `Stacks.Chow.exists_bounds_of_isLocallyBoundedFiniteLocallyFree` — on a quasi-compact ringed
  space the local degree bounds of a locally bounded complex can be replaced by a single global
  pair of bounds.

## Implementation notes

The two alternatives of the restriction hypothesis — zero, or a finite locally free module of
rank `< p` in degree `0` — are kept as the two disjuncts of a single field, since the source
states them in parallel and the two constructions they feed differ only in which disjunct they
consume.

Local boundedness in alternative (c) is boundedness *near each point*, with the bounds allowed
to depend on the point; it is strictly weaker than boundedness of the complex, which is why the
condition is spelled out rather than taken from an existing bounded-complex predicate. It does
become boundedness of the complex when the space is quasi-compact, which is the content of
`Stacks.Chow.exists_bounds_of_isLocallyBoundedFiniteLocallyFree` below.

In alternative (d) the auxiliary scheme is required to be locally of finite type over the same
base and the morphism to it to be a morphism over that base, as in the source.

Both of the auxiliary predicates are stated for a ringed space rather than a scheme: nothing in
either uses more than the structure sheaf, and the situation below applies them to
`AlgebraicGeometry.Scheme.toRingedSpace`.

## References

* [Stacks Project, Tag 0GUJ](https://stacks.math.columbia.edu/tag/0GUJ)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open AlgebraicGeometry.RingedSpace.PseudoCoherence

universe u

namespace Stacks.Chow

attribute [local instance] HasDerivedCategory.standard

/-- A finite locally free module on a ringed space whose rank is everywhere strictly below `p`.
The rank is allowed to vary from point to point, so this is a local, not a global, condition:
on a neighbourhood of each point the module is finite locally free of some rank `< p`. -/
def IsFiniteLocallyFreeOfRankLT {X : RingedSpace.{u, u}} (M : OXMod.{u, u, u} X) (p : ℕ) :
    Prop :=
  SheafOfModules.IsFiniteLocallyFree (R := structureSheafOfRings X) M ∧
    ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧ ∃ r < p,
      SheafOfModules.IsFiniteLocallyFreeOfRank
        (R := structureSheafOfRings (X.restrict U.isOpenEmbedding))
        ((restrictModules X U).obj M) r

/-- A complex of finite locally free modules on a ringed space that is *locally bounded*: each
term is finite locally free, and on a neighbourhood of each point all but finitely many terms
restrict to zero. The bounds may depend on the point, so the complex itself need not be
bounded. -/
def IsLocallyBoundedFiniteLocallyFree {X : RingedSpace.{u, u}}
    (P : CochainComplex (OXMod.{u, u, u} X) ℤ) : Prop :=
  (∀ n : ℤ, SheafOfModules.IsFiniteLocallyFree (R := structureSheafOfRings X) (P.X n)) ∧
    ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧ ∃ lo hi : ℤ, ∀ n : ℤ,
      (n < lo ∨ hi < n) → IsZero ((restrictModules X U).obj (P.X n))

/-- A sheaf of `𝒪_X`-modules whose restrictions to the members of an open covering of `X` all
vanish is itself zero. -/
private theorem isZero_of_restrictModules_cover (X : RingedSpace.{u, u})
    (M : OXMod.{u, u, u} X) {ι : Type*} (U : ι → Opens X.carrier)
    (hU : ∀ x : X.carrier, ∃ i, x ∈ U i)
    (hM : ∀ i, IsZero ((restrictModules X (U i)).obj M)) : IsZero M := by
  apply (IsZero.iff_id_eq_zero M).2
  ext V s
  change s = 0
  apply (show TopCat.Presheaf.IsSheaf M.val.presheaf from M.isSheaf).section_ext
    (U := V) (s := s) (t := 0)
  intro x hx
  obtain ⟨i, hi⟩ := hU x
  refine ⟨V.unop ⊓ U i, inf_le_left, ⟨hx, hi⟩, ?_⟩
  have hW : (U i).isOpenEmbedding.functor.obj ((Opens.map (U i).inclusion').obj V.unop) =
      V.unop ⊓ U i := by
    ext y
    simp [Topology.IsOpenEmbedding.functor]
  have hZ : IsZero (M.val.obj (Opposite.op (V.unop ⊓ U i))) := by
    have hh : IsZero (M.val.obj (Opposite.op ((U i).isOpenEmbedding.functor.obj
        ((Opens.map (U i).inclusion').obj V.unop)))) :=
      (IsZero.iff_id_eq_zero _).2 <|
        congrArg (fun f : (restrictModules X (U i)).obj M ⟶ (restrictModules X (U i)).obj M =>
            f.val.app (Opposite.op ((Opens.map (U i).inclusion').obj V.unop)))
          ((IsZero.iff_id_eq_zero _).1 (hM i))
    exact Eq.mp (congrArg (fun W : Opens X.carrier => IsZero (M.val.obj (Opposite.op W))) hW) hh
  have : Subsingleton (M.val.presheaf.obj (Opposite.op (V.unop ⊓ U i))) :=
    ModuleCat.isZero_iff_subsingleton.mp hZ
  exact Subsingleton.elim _ _

/-- **On a quasi-compact ringed space a locally bounded complex of finite locally free modules
is bounded.** If every point of `X` has a neighbourhood on which the terms of `P` restrict to
zero outside a finite range of degrees, then there is a single such range valid on all of `X`:
`P.X n` itself vanishes for `n` outside it. -/
theorem exists_bounds_of_isLocallyBoundedFiniteLocallyFree {X : RingedSpace.{u, u}}
    [CompactSpace X.carrier] {P : CochainComplex (OXMod.{u, u, u} X) ℤ}
    (hP : IsLocallyBoundedFiniteLocallyFree P) :
    ∃ lo hi : ℤ, ∀ n : ℤ, (n < lo ∨ hi < n) → IsZero (P.X n) := by
  classical
  choose U hxU lo hi hvan using hP.2
  obtain ⟨t, ht⟩ := (isCompact_univ (X := X.carrier)).elim_finite_subcover
    (fun x : X.carrier => (U x : Set X.carrier)) (fun x => (U x).isOpen)
    fun x _ => Set.mem_iUnion.2 ⟨x, hxU x⟩
  obtain ⟨L, hL⟩ := (t.image fun x => -lo x).exists_le
  obtain ⟨H, hH⟩ := (t.image hi).exists_le
  refine ⟨-L, H, fun n hn => ?_⟩
  refine isZero_of_restrictModules_cover X _ (fun x : {x // x ∈ t} => U x.1) (fun x => ?_)
    fun x => ?_
  · obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact ⟨⟨y, hy⟩, hxy⟩
  · have hlo : -L ≤ lo x.1 := neg_le.2 (hL _ (Finset.mem_image_of_mem _ x.2))
    exact hvan x.1 n (hn.imp (·.trans_le hlo) ((hH _ (Finset.mem_image_of_mem _ x.2)).trans_lt))

/-- The standing situation for the localized Chern classes and localized Chern character
components of chapter 42 of the Stacks Project: a scheme locally of finite type over the base, a
closed subscheme, a perfect object of the derived category of the ambient scheme which away from
the closed subscheme is zero or a finite locally free module of rank below the chosen degree, and
one of four finiteness alternatives. -/
@[stacks 0GUJ]
structure LocalizedChernSituation where
  /-- The base situation of chapter 42, with its dimension function. -/
  base : ChowSituation.{u}
  /-- The ambient scheme. -/
  X : Scheme.{u}
  /-- Its structure morphism over the base. -/
  a : X ⟶ base.S
  /-- The ambient scheme is locally of finite type over the base. -/
  [locallyOfFiniteType : LocallyOfFiniteType a]
  /-- The closed subscheme along which the classes are localized. -/
  Z : Scheme.{u}
  /-- Its inclusion into the ambient scheme. -/
  i : Z ⟶ X
  /-- The inclusion is a closed immersion. -/
  [isClosedImmersion : IsClosedImmersion i]
  /-- The object of the derived category the classes are attached to. -/
  E : DerivedCategory (OXMod.{u, u, u} X.toRingedSpace)
  /-- The degree of the Chern class. -/
  p : ℕ
  /-- `E` is a perfect object. -/
  perfect : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E
  /-- On the complement of the closed subscheme `E` is zero, or else a finite locally free
  module of rank `< p` placed in cohomological degree `0`. -/
  restriction :
    letI U : Opens X :=
      ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
    letI F := Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (X.toRingedSpace.ofRestrict U.isOpenEmbedding)
    IsZero (F.obj E) ∨
      ∃ M : OXMod.{u, u, u} (X.toRingedSpace.restrict U.isOpenEmbedding),
        IsFiniteLocallyFreeOfRankLT M p ∧
          Nonempty (F.obj E ≅ (DerivedCategory.singleFunctor _ 0).obj M)
  /-- One of four finiteness alternatives: the ambient scheme is quasi-compact, or its irreducible
  components are, or `E` is represented by a locally bounded complex of finite locally free
  modules, or `E` is the pullback of a perfect object on a scheme over the base with quasi-compact
  irreducible components. -/
  finiteness :
    CompactSpace X ∨
      (∀ C ∈ irreducibleComponents X, IsCompact C) ∨
      (∃ P : CochainComplex (OXMod.{u, u, u} X.toRingedSpace) ℤ,
        IsLocallyBoundedFiniteLocallyFree P ∧ Nonempty (DerivedCategory.Q.obj P ≅ E)) ∨
      (∃ (X' : Scheme.{u}) (a' : X' ⟶ base.S) (f : X ⟶ X')
          (E' : DerivedCategory (OXMod.{u, u, u} X'.toRingedSpace)),
        LocallyOfFiniteType a' ∧ f ≫ a' = a ∧
          Cohomology.PerfectComplexes.IsPerfect (X := X'.toRingedSpace) E' ∧
          Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            f.toLRSHom.toShHom).obj E' ≅ E) ∧
          ∀ C ∈ irreducibleComponents X', IsCompact C)

attribute [instance] LocalizedChernSituation.locallyOfFiniteType
  LocalizedChernSituation.isClosedImmersion

end Stacks.Chow

end
