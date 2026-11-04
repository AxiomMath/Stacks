module

public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ObjectsSituation
public import StacksFrontier.CategoryTheory.Sites.WeaklyContractible

/-!
# A covering collection of objects gives enough objects of its property

Two forms of "the distinguished objects cover the site" occur in this repository.

* The *situation* form, `Stacks.Sites.QuasiCompactObjectsSituation.HasEnoughObjects`, condition
  (1) of Stacks 0937: every object carries a `CategoryTheory.PreZeroHypercover` indexed in
  `Type (max u v)` whose generated sieve covers and whose members are distinguished.
* The *object-property* form, `CategoryTheory.GrothendieckTopology.HasEnoughObjects`, Stacks
  090L (3): every object carries a covering family indexed in `Type v` whose members satisfy a
  given `CategoryTheory.ObjectProperty`.

The object-property form is what the consumers of Stacks 0BKZ take as a hypothesis, e.g.
`Stacks.Cohomology.HypercohomologyEdge.isIso_hypercohomologyEdge_app_of_acyclic_cover`. This
file passes from the first form to the second.

The two differ in the universe of the index: `Type (max u v)` against `Type v`. Over a site whose
underlying category is `v`-small the index can be cut down, because the covering family may be
replaced by the family of *all* arrows it contains, and those form a subtype of
`Σ V : C, V ⟶ U`, which is `v`-small. That replacement changes neither the generated sieve nor
the collection of sources, so no hypothesis beyond `Small.{v} C` is needed; this is the content
of `CategoryTheory.GrothendieckTopology.hasEnoughObjects_of_exists_preZeroHypercover`, which is
the converse of `Stacks.Cohomology.AcyclicCover.exists_preZeroHypercover_of_hasEnoughObjects`.

The hypothesis of that lemma is the body of the situation form, and it is stated for an index in
an arbitrary universe, so a holder of condition (1) for *either* of the two
`QuasiCompactObjectsSituation` structures of this repository — the one of
`StacksFrontier/CategoryTheory/Sites/QuasiCompact/ObjectsSituation.lean` and the one of
`StacksFrontier/Topology/Sheaves/Spectral/CompactBasisColimit.lean` — can feed it directly.
`Stacks.Sites.QuasiCompactObjectsSituation.topology_hasEnoughObjects` records the passage for
the first of them.

The small étale site is not an instance of this: its objects form a `Type (u + 1)` while its
homs are in `Type u`, so `Small.{u}` fails for it and the index of an étale cover has to be cut
down with information about that site instead. That is done in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/SmallEtaleEnoughObjects.lean`, where one
particular étale cover -- an object's affine opens lying over affine opens of the base -- is
observed to be indexed by a `ULift` of a `Type u` already, so that reindexing it suffices.

## Main results

* `CategoryTheory.GrothendieckTopology.HasEnoughObjects.mono`: the predicate is monotone in its
  object property.
* `CategoryTheory.GrothendieckTopology.hasEnoughObjects_of_exists_preZeroHypercover`: on a
  `v`-small site, a covering `PreZeroHypercover` over every object, indexed in any universe,
  with all members satisfying `P`, gives `J.HasEnoughObjects P`.
* `Stacks.Sites.QuasiCompactObjectsSituation.topology_hasEnoughObjects`: condition (1) of
  Stacks 0937 gives `HasEnoughObjects` for the property of belonging to the distinguished
  collection.

## References

* [Stacks Project, Tag 0937](https://stacks.math.columbia.edu/tag/0937)
* [Stacks Project, Tag 090L](https://stacks.math.columbia.edu/tag/090L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C]

/-- **Enough objects is monotone in the object property.** A covering family by objects with `P`
is a covering family by objects with any weaker property.

`CategoryTheory.Presheaf.isIso_presheafToSheaf_map_of_hasEnoughObjects_bijective` and
`PresheafOfModules.isIso_sheafification_map_of_isIso_evaluation` both appeal to this in their
docstrings, to know that taking the object property to be exactly the locus of a condition is no
weaker than taking an arbitrary property contained in it. -/
theorem HasEnoughObjects.mono {J : GrothendieckTopology C} {P Q : ObjectProperty C}
    (h : J.HasEnoughObjects P) (hPQ : ∀ U : C, P U → Q U) :
    J.HasEnoughObjects Q := fun U => by
  obtain ⟨I, Ui, f, hf, hP⟩ := h U
  exact ⟨I, Ui, f, hf, fun i => hPQ _ (hP i)⟩

/-- On a site whose underlying category is `v`-small, a covering family of every object by
objects with the property `P`, presented as a `PreZeroHypercover` with an index in any universe,
gives enough `P` objects in the sense of Stacks 090L (3), whose families are indexed in
`Type v`.

The index is cut down by replacing the family by the family of all the arrows it contains:
those form a subtype of `Σ V : C, V ⟶ U`, which is `v`-small, and they generate the same sieve
with the same collection of sources. This is the converse of
`Stacks.Cohomology.AcyclicCover.exists_preZeroHypercover_of_hasEnoughObjects`.

Smallness of `C` is not a convenience: the hypothesis gives a covering family whose index may
be larger than `Type v`, and over a site with more arrows than `Type v` has elements there is
in general no `Type v`-indexed family generating a covering sieve. -/
theorem hasEnoughObjects_of_exists_preZeroHypercover [Small.{v} C]
    (J : GrothendieckTopology C) (P : ObjectProperty C)
    (h : ∀ U : C, ∃ 𝒰 : PreZeroHypercover.{w} U,
      𝒰.sieve₀ ∈ J U ∧ ∀ i, P (𝒰.X i)) :
    J.HasEnoughObjects P := by
  intro U
  obtain ⟨𝒰, hmem, hP⟩ := h U
  -- The arrows of the covering family, as a subtype of `Σ V : C, V ⟶ U`, which is `v`-small.
  let A : Type (max u v) := { x : (Σ V : C, V ⟶ U) // Presieve.ofArrows 𝒰.X 𝒰.f x.2 }
  let E : PreZeroHypercover.{max u v} U := ⟨A, fun x => x.1.1, fun x => x.1.2⟩
  have hE : E.presieve₀ = Presieve.ofArrows 𝒰.X 𝒰.f :=
    le_antisymm (fun W k hk => by obtain ⟨x⟩ := hk; exact x.2)
      fun W k hk => Presieve.ofArrows.mk (⟨⟨W, k⟩, hk⟩ : A)
  -- Reindexing it along `Shrink A ≃ A` puts the index in `Type v`.
  let F : PreZeroHypercover.{v} U := E.reindex (equivShrink A).symm
  refine ⟨F.I₀, F.X, F.f, ?_, fun i => ?_⟩
  · rw [show Sieve.ofArrows F.X F.f = 𝒰.sieve₀ from
      congrArg Sieve.generate ((E.presieve₀_reindex (equivShrink A).symm).trans hE)]
    exact hmem
  · obtain ⟨j, hj, -⟩ := Presieve.ofArrows_surj 𝒰.f _ ((equivShrink A).symm i).2
    show P ((((equivShrink A).symm i : A)).1.1)
    exact hj ▸ hP j

end CategoryTheory.GrothendieckTopology

namespace Stacks.Sites.QuasiCompactObjectsSituation

variable {C : Type u} [Category.{v} C] [Small.{v} C]

/-- **Condition (1) of Stacks 0937 gives enough objects in the sense of Stacks 090L (3).** If
the distinguished objects of a `QuasiCompactObjectsSituation` cover every object of the site,
then the site has enough objects with the property of being distinguished — the form of the
condition that the consumers of Stacks 0BKZ take as a hypothesis. -/
theorem topology_hasEnoughObjects {S : QuasiCompactObjectsSituation C}
    (hS : S.HasEnoughObjects) :
    S.topology.HasEnoughObjects (fun U => U ∈ S.objects) :=
  S.topology.hasEnoughObjects_of_exists_preZeroHypercover _ hS

end Stacks.Sites.QuasiCompactObjectsSituation

end
