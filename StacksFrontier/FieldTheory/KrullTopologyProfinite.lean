module

public import Mathlib.FieldTheory.Galois.Profinite
public import StacksCore.FieldTheory.KrullTopology

/-!
# The Krull topology: coarsest topology and profiniteness

Let `L/K` be a Galois extension. We show the two parts of Stacks 0BMJ together with the
characterisation of the Krull topology that the statement uses as its definition:

* the Krull topology on `Gal(L/K)` is the coarsest topology for which the action
  `Gal(L/K) × L → L` is continuous when `L` carries the discrete topology;
* (1) a map `f : X → Gal(L/K)` from a topological space is continuous as soon as the induced
  action `X × L → L` is continuous;
* (2) `Gal(L/K)` is a profinite topological group: a topological group which is compact,
  Hausdorff and totally disconnected.

## References

* [Stacks Project, Tag 0BMJ](https://stacks.math.columbia.edu/tag/0BMJ)
-/

@[expose] public section

namespace krullTopology

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- With `L` discrete, the action `X × L → L`, `(i, x) ↦ f i x`, is continuous if and only if
each set `{i | f i x = y}` is open. -/
theorem continuous_action_iff {X : Type*} [TopologicalSpace X] (f : X → Gal(L/K)) :
    @Continuous (X × L) L (@instTopologicalSpaceProd X L _ ⊥) ⊥ (fun p ↦ f p.1 p.2) ↔
      ∀ x y : L, IsOpen {i | f i x = y} := by
  let : TopologicalSpace L := ⊥
  have : DiscreteTopology L := ⟨rfl⟩
  exact continuous_prod_of_discrete_right.trans <|
    forall_congr' fun x ↦ continuous_discrete_rng.trans <| forall_congr' fun y ↦ Iff.rfl

variable (K L)

/-- **Stacks 0BMJ** (2). For a Galois extension `L/K`, the Krull topology makes `Gal(L/K)` a
profinite topological group: a topological group which is compact, Hausdorff and totally
disconnected. -/
@[stacks 0BMJ "(2): Gal(L/K) is a profinite topological group"]
theorem isTopologicalGroup_and_compactSpace_and_t2Space_and_totallyDisconnectedSpace
    [IsGalois K L] :
    IsTopologicalGroup Gal(L/K) ∧ CompactSpace Gal(L/K) ∧ T2Space Gal(L/K) ∧
      TotallyDisconnectedSpace Gal(L/K) :=
  ⟨inferInstance, inferInstance, krullTopology_t2, inferInstance⟩

/-- **Stacks 0BMJ**. Let `L/K` be a Galois extension and give `L` the discrete topology.
The Krull topology is the coarsest topology on `Gal(L/K)` for which the action
`Gal(L/K) × L → L` is continuous, and with it
(1) a map `f : X → Gal(L/K)` from a topological space `X` is continuous whenever the induced
action `X × L → L` is continuous, and
(2) `Gal(L/K)` is a profinite topological group. -/
@[stacks 0BMJ "coarsest topology making the action continuous; (1) universal property;
(2) profinite topological group"]
theorem isGreatest_and_continuous_and_profinite [IsGalois K L] :
    IsGreatest {t : TopologicalSpace Gal(L/K) |
        @Continuous (Gal(L/K) × L) L (@instTopologicalSpaceProd _ L t ⊥) ⊥ fun p ↦ p.1 p.2}
      (krullTopology K L) ∧
    (∀ (X : Type*) [TopologicalSpace X] (f : X → Gal(L/K)),
      @Continuous (X × L) L (@instTopologicalSpaceProd X L _ ⊥) ⊥ (fun p ↦ f p.1 p.2) →
        Continuous f) ∧
    (IsTopologicalGroup Gal(L/K) ∧ CompactSpace Gal(L/K) ∧ T2Space Gal(L/K) ∧
      TotallyDisconnectedSpace Gal(L/K)) := by
  refine ⟨⟨?_, fun t ht ↦ ?_⟩, fun X _ f hf ↦ ?_,
    isTopologicalGroup_and_compactSpace_and_t2Space_and_totallyDisconnectedSpace K L⟩
  · exact (continuous_action_iff (X := Gal(L/K)) id).mpr fun x y ↦
      isOpen_krullTopology_apply_eq' K x y
  · exact continuous_id_iff_le.mp <| @continuous_krullTopology K L Gal(L/K) _ _ _ t id <|
      (@continuous_action_iff K L _ _ _ Gal(L/K) t id).mp ht
  · exact continuous_krullTopology <| (continuous_action_iff f).mp hf

end krullTopology
