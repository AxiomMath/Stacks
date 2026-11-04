module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeAtGenericPoints
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeRankLocusApproximation
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.LimitPreserving
public import StacksFrontier.CategoryTheory.Sites.SubsingletonPresheaf
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeAtGenericPointsRepresentability

/-!
# Descent and approximation criteria for the generic-rank functor

The functor of Situation 05MP recording whether a finite type quasi-coherent module is free of
a fixed rank near the generic point of every fibre is subterminal, so neither of the two
properties asserted of it by Stacks 05MS carries any categorical content beyond a statement
about the generic-point condition itself. This file makes both reductions precise: the fpqc
sheaf property is *equivalent* to fpqc-locality of the condition, and limit preservation is
*equivalent* to the assertion that the condition over a cofiltered limit of affine schemes
already holds over some stage.

## Main results

* In the namespace `AlgebraicGeometry.FreeAtGenericPointsSituation`, the statement
  `freeAtGenericPointsFunctor_isSheaf_fpqc_iff` identifies the first clause of Stacks 05MS with
  fpqc-locality of the generic-point condition, and
  `freeAtGenericPointsFunctor_isSheaf_fpqc_of_fpqcCover` deduces that clause *from* the
  locality statement, in the covering-family form in which such a statement is usually proved.
* `AlgebraicGeometry.FreeAtGenericPointsSituation.freeAtGenericPointsFunctor_limitPreserving_iff`
  identifies the second clause of Stacks 05MS with the approximation statement for the
  generic-point condition, `freeAtGenericPointsFunctor_limitPreserving_small_iff` is that
  equivalence at a `u`-small index category, and
  `AlgebraicGeometry.FreeAtGenericPointsSituation.freeAtGenericPointsFunctor_limitPreserving`
  deduces that clause *from* the approximation statement.
* `AlgebraicGeometry.FreeAtGenericPointsSituation.freeAtGenericPointsFunctor_limitPreserving_small`
  **is** the second clause of Stacks 05MS: the approximation statement is proved outright, so
  this takes the equivalence at the `u`-small seating with nothing assumed.

## Implementation notes

The values of `AlgebraicGeometry.FreeAtGenericPointsSituation.freeAtGenericPointsFunctor` are
`ULift (PLift _)` of a proposition, hence subsingletons, which is what feeds
`CategoryTheory.Presheaf.isSheaf_iff_nonempty_of_subsingleton` and
`CategoryTheory.nonempty_isColimit_mapCocone_op_iff_of_subsingleton`.

The fpqc topology on schemes over the base is Mathlib's `AlgebraicGeometry.Scheme.fpqcTopology`
localized at the base with `CategoryTheory.GrothendieckTopology.over`, as for the four
flattening functors of Stacks 05MJ. Passing from covering sieves to covering families uses
`CategoryTheory.over_toGrothendieck_eq_toGrothendieck_comap_forget` together with
`CategoryTheory.Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange`: the fpqc
precoverage is stable under base change and the forgetful functor to schemes preserves fibre
products, so the sheaf condition for the generated topology is the sheaf condition for the
covering presieves themselves.

Limit preservation is `AlgebraicGeometry.LimitPreserving` for the forgetful functor from the
slice over the base, and its conclusion is literally the hypothesis of
`CategoryTheory.nonempty_isColimit_mapCocone_op_iff_of_subsingleton`, so the reduction needs
nothing beyond that lemma.

*Where the clauses themselves are proved.* The second clause of Stacks 05MS is proved here, as
`freeAtGenericPointsFunctor_limitPreserving_small`, which carries the tag. The first clause is
proved in
`StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeAtGenericPointsLocality`, as
`freeAtGenericPointsFunctor_isSheaf_fpqc`, which carries the tag too. The geometric input of the
first clause is carried as an explicit hypothesis on
`freeAtGenericPointsFunctor_isSheaf_fpqc_of_fpqcCover`, in the shape the source's proof
establishes it: that the generic-point condition descends along an fpqc covering of the base.
Because that reduction is an equivalence the hypothesis is not merely sufficient for the
clause, it is exactly its content, so that statement may not carry the tag — it assumes what
the tag asserts.

The two halves which discharge that hypothesis are the descent
`stalkFreeOfRank_of_fpqcCover` in
`StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeAtGenericPointsStalkDescent`, which gives a
free stalk of rank `p` at the generic point of every fibre over the base of an fpqc covering, and
`AlgebraicGeometry.freeAtPointOfRank_of_forall_stalkFreeOfRank`, which spreads those free stalks
out to neighbourhoods.

The engine of that spreading out is
`AlgebraicGeometry.nonempty_basis_sections_of_forall_stalkFreeOfRank`
(`StacksFrontier/AlgebraicGeometry/Flatness/Flattening/FreeAtGenericPointsAffineBridge.lean:242`):
for an affine open `U` of the source lying over an affine open `V` of the base and meeting every
fibre over `V`, with the induced map of functions flat of finite presentation and with
geometrically integral fibres, `p` sections generating `Γ(F, U)` and a free stalk of rank `p` at
the generic point of every fibre together force those sections to be a basis. Its three
ingredients are
`Module.nonempty_basis_of_forall_basis_localizedModule_genericFibre`
(`StacksFrontier/AlgebraicGeometry/Flatness/FinitelyPresented/FreeMapGenericFibreFreeness.lean:171`), which is Stacks 05IA — in the
form `Module.bijective_of_forall_flat_localizedModule_genericFibre`,
`StacksFrontier/AlgebraicGeometry/Flatness/FinitelyPresented/FreeMapGenericFibreInjectivity.lean:155` — run at every prime of the base
with its two hypotheses discharged from a free localization; and the two halves of the
scheme-to-ring bridge, `AlgebraicGeometry.nonempty_basis_localizedModule_of_stalkFreeOfRank` and
`AlgebraicGeometry.primeIdealOf_eq_map_appLE_of_isGenericPoint`, the latter being the source's
identification of the generic point of the fibre over `r` with the prime `rS`.

Note that the module being of finite type rather than of finite presentation — so that Stacks
080Q, whose module hypothesis is finite presentation, cannot spread a free stalk out — never
enters: the ring-theoretic input assumes only `Module.Finite S N` throughout.

The pair of affine opens the engine asks for is produced by the *shrinking*, which the source
does in the one sentence "after shrinking `T` we may assume that `U → T` is surjective"; that, and
the reading of the resulting basis as the generic-point condition, are in
`StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeAtGenericPointsLocality`.

For the second clause the right-hand side of
`freeAtGenericPointsFunctor_limitPreserving_small_iff` is
`AlgebraicGeometry.FreeAtGenericPointsSituation.exists_condition_of_isLimit`, proved outright
in `StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeRankLocusApproximation` by the
source's own argument: it covers the generic points of the fibres over the affine limit by an
affine open of the base change carrying the module as finite locally free of rank `p`,
descends that open to a stage by Stacks 01Z4 (1), makes the module flat over that stage by
Stacks 05LY, recovers freeness of some rank near each fibre's generic point there by
Stacks 080Q, pins that rank to `p`, and applies Stacks 01Z4 (3) to the open image of the
rank-`p` locus. The `u`-small seating is what makes this possible: it is the one at which the
library forms of Stacks 01Z4 (3) and Stacks 05LY are stated, and it is the seating the
source's statement about directed systems asks for.
`freeAtGenericPointsFunctor_limitPreserving` is kept beside the proved form for the general
universe seating, where the geometric input is still a hypothesis and the tag therefore still
cannot be placed. Finite presentation of the module, which the source assumes for this clause,
is an instance hypothesis on both.

## References

* [Stacks Project, Tag 05MP](https://stacks.math.columbia.edu/tag/05MP)
* [Stacks Project, Tag 05MS](https://stacks.math.columbia.edu/tag/05MS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w' w u

namespace AlgebraicGeometry.FreeAtGenericPointsSituation

variable (D : FreeAtGenericPointsSituation.{u}) (p : ℕ)

/-- The fpqc sheaf property of the generic-rank functor is exactly fpqc-locality of the
generic-point freeness condition: the condition holds over a scheme over the base as soon as it
holds over every member of one fpqc covering sieve of it. -/
theorem freeAtGenericPointsFunctor_isSheaf_fpqc_iff :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over D.S) (D.freeAtGenericPointsFunctor p) ↔
      ∀ (T : Over D.S) (S : Sieve T), S ∈ (Scheme.fpqcTopology.over D.S) T →
        (∀ ⦃T' : Over D.S⦄ (g : T' ⟶ T), S.arrows g → D.Condition p T') → D.Condition p T := by
  have := D.subsingleton_freeAtGenericPointsFunctor_obj p
  rw [Presheaf.isSheaf_iff_nonempty_of_subsingleton]
  exact ⟨fun h T S hS hloc ↦ (h T S hS fun _ g hg ↦ ⟨⟨⟨hloc g hg⟩⟩⟩).some.down.down,
    fun h T S hS hne ↦ ⟨⟨⟨h T S hS fun _ g hg ↦ (hne g hg).some.down.down⟩⟩⟩⟩

/-- Fpqc-locality of the generic-point freeness condition in covering-family form — the
condition holds over a scheme over the base as soon as it holds over every member of one fpqc
covering family of it — implies the fpqc sheaf property of the generic-rank functor, which is
the first clause of Stacks 05MS. The hypothesis is that clause, so this is a reformulation of
it and not a proof of it. -/
theorem freeAtGenericPointsFunctor_isSheaf_fpqc_of_fpqcCover
    (h : ∀ (T : Over D.S)
      (𝒰 : Precoverage.ZeroHypercover.{u + 1} Scheme.fpqcPrecoverage T.left),
      (∀ i, D.Condition p (Over.mk (𝒰.f i ≫ T.hom))) → D.Condition p T) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over D.S) (D.freeAtGenericPointsFunctor p) := by
  have := D.subsingleton_freeAtGenericPointsFunctor_obj p
  rw [isSheaf_iff_isSheaf_of_type]
  show Presieve.IsSheaf ((Scheme.fpqcPrecoverage.toGrothendieck).over D.S)
    (D.freeAtGenericPointsFunctor p)
  rw [CategoryTheory.over_toGrothendieck_eq_toGrothendieck_comap_forget
    Scheme.fpqcPrecoverage D.S,
    Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  intro T R hR
  obtain ⟨ι, Y, g, rfl⟩ := R.exists_eq_ofArrows
  let 𝒰 : Scheme.fpqcPrecoverage.ZeroHypercover T.left :=
    ⟨⟨ι, fun i ↦ (Y i).left, fun i ↦ (g i).left⟩, by
      simpa [Precoverage.mem_comap_iff] using hR⟩
  rw [Presieve.isSheafFor_arrows_iff]
  intro x _
  have hlocal (i : ι) : D.Condition p (Over.mk (𝒰.f i ≫ T.hom)) := by
    show D.Condition p (Over.mk ((g i).left ≫ T.hom))
    convert (x i).down.down using 1
    exact CostructuredArrow.obj_ext _ _ rfl (CostructuredArrow.w (g i)).symm
  exact ⟨⟨⟨h T 𝒰 hlocal⟩⟩, fun _ ↦ Subsingleton.elim _ _, fun _ _ ↦ Subsingleton.elim _ _⟩

/-- Limit preservation of the generic-rank functor is exactly the assertion that the
generic-point freeness condition over a cofiltered limit of affine schemes over the base
already holds over some stage of the system. -/
theorem freeAtGenericPointsFunctor_limitPreserving_iff :
    LimitPreserving.{u, u, w, w', u + 1, u} (Over.forget D.S)
        (D.freeAtGenericPointsFunctor p) ↔
      ∀ (I : Type (max w w')) [Category.{w'} I] [IsCofiltered I] (E : I ⥤ Over D.S)
        (c : Cone E), IsLimit ((Over.forget D.S).mapCone c) →
        (∀ i, IsAffine ((Over.forget D.S).obj (E.obj i))) →
        IsAffine ((Over.forget D.S).obj c.pt) →
        D.Condition p c.pt → ∃ i, D.Condition p (E.obj i) := by
  have := D.subsingleton_freeAtGenericPointsFunctor_obj p
  constructor
  · intro h I _ _ E c hc hE hpt hcond
    obtain ⟨i, hi⟩ := (nonempty_isColimit_mapCocone_op_iff_of_subsingleton
      (D.freeAtGenericPointsFunctor p) E c).mp (h I E c hc hE hpt) ⟨⟨⟨hcond⟩⟩⟩
    exact ⟨i, hi.some.down.down⟩
  · intro h I _ _ E c hc hE hpt
    refine (nonempty_isColimit_mapCocone_op_iff_of_subsingleton
      (D.freeAtGenericPointsFunctor p) E c).mpr fun hne ↦ ?_
    obtain ⟨i, hi⟩ := h I E c hc hE hpt hne.some.down.down
    exact ⟨i, ⟨⟨⟨hi⟩⟩⟩⟩

/-- The equivalence of `freeAtGenericPointsFunctor_limitPreserving_iff` at `w = w' = u`: limit
preservation of the generic-rank functor over a `u`-small cofiltered index category is exactly
the assertion that the generic-point freeness condition over a cofiltered limit of affine
schemes over the base already holds over some stage of the system.

This is the seating the second clause of Stacks 05MS asks for, the source's statement being
about directed systems of schemes, and the only one whose right-hand side can consume the
approximation results the source's proof uses: Stacks 01Z4 (3),
`AlgebraicGeometry.exists_iSup_map_preimage_eq_top`, needs an index category in `Type u`, and
Stacks 05LY, `AlgebraicGeometry.eventually_isFlatOver_modulePullback`, one that is essentially
`u`-small. -/
theorem freeAtGenericPointsFunctor_limitPreserving_small_iff :
    LimitPreserving.{u, u, u, u, u + 1, u} (Over.forget D.S)
        (D.freeAtGenericPointsFunctor p) ↔
      ∀ (I : Type u) [Category.{u} I] [IsCofiltered I] (E : I ⥤ Over D.S)
        (c : Cone E), IsLimit ((Over.forget D.S).mapCone c) →
        (∀ i, IsAffine ((Over.forget D.S).obj (E.obj i))) →
        IsAffine ((Over.forget D.S).obj c.pt) →
        D.Condition p c.pt → ∃ i, D.Condition p (E.obj i) :=
  D.freeAtGenericPointsFunctor_limitPreserving_iff p

/-- The approximation statement for the generic-point freeness condition — when the condition
holds over the limit of a cofiltered system of affine schemes over the base, it already holds
over one stage of the system — implies that the generic-rank functor of a module of finite
presentation is limit preserving, which is the second clause of Stacks 05MS. The hypothesis is
that clause, so this is a reformulation of it and not a proof of it. -/
theorem freeAtGenericPointsFunctor_limitPreserving [D.F.IsFinitePresentation]
    (h : ∀ (I : Type (max w w')) [Category.{w'} I] [IsCofiltered I] (E : I ⥤ Over D.S)
      (c : Cone E), IsLimit ((Over.forget D.S).mapCone c) →
      (∀ i, IsAffine ((Over.forget D.S).obj (E.obj i))) →
      IsAffine ((Over.forget D.S).obj c.pt) →
      D.Condition p c.pt → ∃ i, D.Condition p (E.obj i)) :
    LimitPreserving.{u, u, w, w', u + 1, u} (Over.forget D.S)
      (D.freeAtGenericPointsFunctor p) :=
  (D.freeAtGenericPointsFunctor_limitPreserving_iff p).mpr h

/-- **Stacks Project, Tag 05MS, part (2).** The generic-rank functor of a module of finite
presentation is limit preserving: over a cofiltered limit of affine schemes over the base the
functor has a section as soon as one stage of the system has one.

The approximation statement which `freeAtGenericPointsFunctor_limitPreserving_small_iff`
identifies with this clause is
`AlgebraicGeometry.FreeAtGenericPointsSituation.exists_condition_of_isLimit`, so nothing is
assumed here. -/
@[stacks 05MS "part (2), the generic-rank functor is limit preserving"]
theorem freeAtGenericPointsFunctor_limitPreserving_small [D.F.IsFinitePresentation] :
    LimitPreserving.{u, u, u, u, u + 1, u} (Over.forget D.S)
      (D.freeAtGenericPointsFunctor p) :=
  (D.freeAtGenericPointsFunctor_limitPreserving_small_iff p).mpr
    fun _ _ _ E c hc hE hpt hcond => D.exists_condition_of_isLimit p E c hc hE hpt hcond

end AlgebraicGeometry.FreeAtGenericPointsSituation

end
