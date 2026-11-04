module

public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits
public import Mathlib.CategoryTheory.Filtered.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Profinite topological groups as limits of finite discrete groups

A topological group is profinite as a topological space exactly when it is a (cofiltered) limit of
finite discrete topological groups. The cofiltered diagram realising a profinite group is the
diagram of its quotients by open normal subgroups.

## Main definitions

* `IsProfiniteTop`: the underlying topological space is compact, Hausdorff and totally
  disconnected.
* `IsLimitOfFiniteDiscreteGroups`: the group is isomorphic, as a topological group, to the limit of
  a diagram of finite discrete topological groups.
* `IsCofilteredLimitOfFiniteDiscreteGroups`: as above, with the indexing category cofiltered.

## Main results

* `tfae_profinite_group`: the three conditions above are equivalent.
-/

@[expose] public section

open CategoryTheory

universe u

namespace Stacks.Chapter05.Tag_0BR1

/-- "`G` is profinite as a topological space" is the conjunction of the three characterising
properties: compactness, Hausdorffness, and total disconnectedness. -/
@[sga "1 V 5.1", sga "4 IV 2.7.2"]
def IsProfiniteTop (G : Type u) [TopologicalSpace G] : Prop :=
  CompactSpace G ∧ T2Space G ∧ TotallyDisconnectedSpace G

/-- "`G` is a limit of a diagram of finite discrete topological groups": there exists a small
index category `J`, a functor `F : J ⥤ ProfiniteGrp` whose values are finite and discrete, and a
continuous group isomorphism between `G` and the limit of `F` in `ProfiniteGrp`. -/
def IsLimitOfFiniteDiscreteGroups (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : Prop :=
  ∃ (J : Type u) (_ : SmallCategory J) (F : J ⥤ ProfiniteGrp.{u}),
    (∀ j, Finite (F.obj j) ∧ DiscreteTopology (F.obj j)) ∧
      Nonempty (G ≃ₜ* (ProfiniteGrp.limit F : ProfiniteGrp.{u}))

/-- "`G` is a cofiltered limit of finite discrete topological groups": as in
`IsLimitOfFiniteDiscreteGroups`, but additionally requiring `J` to be cofiltered. -/
@[sga "1 V 5.1"]
def IsCofilteredLimitOfFiniteDiscreteGroups (G : Type u) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] : Prop :=
  ∃ (J : Type u) (_ : SmallCategory J) (_ : IsCofiltered J) (F : J ⥤ ProfiniteGrp.{u}),
    (∀ j, Finite (F.obj j) ∧ DiscreteTopology (F.obj j)) ∧
      Nonempty (G ≃ₜ* (ProfiniteGrp.limit F : ProfiniteGrp.{u}))

/-- The whole group is open and normal, so `OpenNormalSubgroup` is nonempty. -/
instance instNonemptyOpenNormalSubgroup
    (G : Type u) [Group G] [TopologicalSpace G] : Nonempty (OpenNormalSubgroup G) :=
  ⟨{ (⊤ : OpenSubgroup G) with isNormal' := Subgroup.normal_top }⟩

/-- Each finite quotient of `P` by an open normal subgroup is, when included in
`ProfiniteGrp`, a finite discrete topological group. -/
private lemma diagram_finite_discrete (P : ProfiniteGrp.{u}) (U : OpenNormalSubgroup P) :
    Finite ((ProfiniteGrp.diagram P).obj U) ∧
      DiscreteTopology ((ProfiniteGrp.diagram P).obj U) := by
  refine ⟨?_, ?_⟩
  · -- The underlying type of `(diagram P).obj U` is `P ⧸ U.toOpenSubgroup.toSubgroup`,
    -- which is finite because an open subgroup of a compact group has finite index.
    unfold ProfiniteGrp.diagram ProfiniteGrp.toFiniteQuotientFunctor
    dsimp [forget₂, HasForget₂.forget₂, ProfiniteGrp.ofFiniteGrp]
    infer_instance
  · -- `ofFiniteGrp` equips the underlying carrier of a `FiniteGrp` with the bottom
    -- topology, which is the discrete topology.
    unfold ProfiniteGrp.diagram ProfiniteGrp.toFiniteQuotientFunctor
    dsimp [ProfiniteGrp.ofFiniteGrp]
    exact ⟨rfl⟩

/-- **Stacks 0BR1**.
For a topological group `G`, the following are equivalent: `G` is profinite as a topological space;
`G` is a limit of a diagram of finite discrete topological groups; `G` is a cofiltered limit of
finite discrete topological groups. -/
@[stacks 0BR1, sga "1 V 5.1", sga "4 IV 2.7.2" "more general"]
theorem tfae_profinite_group (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] :
    List.TFAE
      [ IsProfiniteTop G,
        IsLimitOfFiniteDiscreteGroups G,
        IsCofilteredLimitOfFiniteDiscreteGroups G ] := by
  tfae_have h13 : 1 → 3 := by
    rintro ⟨_, _, _⟩
    let P : ProfiniteGrp.{u} := ProfiniteGrp.of G
    exact ⟨OpenNormalSubgroup P, inferInstance, inferInstance, ProfiniteGrp.diagram P,
      diagram_finite_discrete P,
      ⟨ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor P⟩⟩
  tfae_have h32 : 3 → 2 := by
    rintro ⟨J, _, _, F, hF, e⟩
    exact ⟨J, ‹_›, F, hF, e⟩
  tfae_have h21 : 2 → 1 := by
    rintro ⟨J, _, F, _, ⟨e⟩⟩
    exact ⟨Homeomorph.compactSpace e.toHomeomorph.symm, Homeomorph.t2Space e.toHomeomorph.symm,
      Homeomorph.totallyDisconnectedSpace e.toHomeomorph.symm⟩
  tfae_finish

end Stacks.Chapter05.Tag_0BR1
