module

public import Mathlib.Topology.Category.Profinite.AsLimit
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.Separation.Connected
public import Mathlib.Topology.Separation.CompletelyRegular

/-!
# Profinite topological spaces

A topological space is *profinite* if it is homeomorphic to a limit of a diagram of finite discrete
spaces. That is recorded here as `IsProfiniteStacks` and connected both to Mathlib's bundled
category `Profinite` and to the familiar characterisation as compact, Hausdorff and totally
disconnected. The forward comparison lifts the given diagram of finite discrete spaces to a diagram
in `Profinite`; the backward one uses the `DiscreteQuotient` diagram of a bundled profinite space.

## Main results

* `IsProfiniteStacks` (Stacks 08ZX): the Stacks Project's definition of a profinite space.
* `isProfiniteStacks_iff_exists_profinite`: it agrees with being homeomorphic to an object of
  Mathlib's `Profinite`.
* `isProfiniteStacks_iff_compact_t2_totallyDisconnected`: it agrees with being compact, Hausdorff
  and totally disconnected.
-/

@[expose] public section

open CategoryTheory Limits

universe u v

/-- **Stacks 08ZX** (definition of profinite). A topological space `X` is profinite if it is
homeomorphic to (the underlying space of) the limit of some diagram of finite discrete topological
spaces. -/
@[stacks 08ZX]
def IsProfiniteStacks (X : Type u) [TopologicalSpace X] : Prop :=
  ∃ (J : Type u) (_ : SmallCategory J) (F : J ⥤ TopCat.{u}) (c : Cone F),
    (∀ j, Finite (F.obj j) ∧ DiscreteTopology (F.obj j)) ∧
    Nonempty (IsLimit c) ∧
    Nonempty (c.pt ≃ₜ X)

/-- A bundled `Profinite.{u}` homeomorphic to `X` exists iff `X` is compact, Hausdorff and totally
disconnected. -/
lemma exists_profinite_iff_triple (X : Type u) [TopologicalSpace X] :
    (∃ Y : Profinite.{u}, Nonempty (Y ≃ₜ X)) ↔
      CompactSpace X ∧ T2Space X ∧ TotallyDisconnectedSpace X := by
  refine ⟨fun ⟨_, ⟨e⟩⟩ => ⟨e.compactSpace, e.t2Space, e.totallyDisconnectedSpace⟩,
    fun ⟨_, _, _⟩ => ?_⟩
  exact ⟨Profinite.of X, ⟨Homeomorph.refl X⟩⟩

/-- Lift a diagram of finite discrete topological spaces to a diagram in `Profinite.{u}`. -/
noncomputable def liftToProfinite (J : Type v) [SmallCategory J] (F : J ⥤ TopCat.{u})
    (hfd : ∀ j, Finite (F.obj j) ∧ DiscreteTopology (F.obj j)) :
    J ⥤ Profinite.{u} :=
  letI (j : J) : Finite ((F.obj j) : Type u) := (hfd j).1
  letI (j : J) : DiscreteTopology ((F.obj j) : Type u) := (hfd j).2
  { obj := fun j => Profinite.of (F.obj j)
    map := fun {_ _} f => CompHausLike.ofHom _ (F.map f).hom
    map_id := fun _ => by ext; simp
    map_comp := fun _ _ => by ext; simp }

/-- The lifted diagram composed with the forgetful functor to `TopCat` recovers the original
diagram. -/
noncomputable def liftToProfiniteNatIso (J : Type v) [SmallCategory J]
    (F : J ⥤ TopCat.{u})
    (hfd : ∀ j, Finite (F.obj j) ∧ DiscreteTopology (F.obj j)) :
    liftToProfinite J F hfd ⋙ Profinite.toTopCat ≅ F :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by ext; rfl)

/-- A Stacks-profinite space is homeomorphic to a bundled profinite space in the same universe. -/
lemma isProfiniteStacks_to_exists_profinite (X : Type u) [TopologicalSpace X]
    (h : IsProfiniteStacks X) :
    ∃ Y : Profinite.{u}, Nonempty (Y ≃ₜ X) := by
  obtain ⟨J, _, F, c, hfd, ⟨isLimC⟩, ⟨homX⟩⟩ := h
  let F' : J ⥤ Profinite.{u} := liftToProfinite J F hfd
  have isLimC' : IsLimit ((Cone.postcompose (liftToProfiniteNatIso J F hfd).hom).obj
      (Profinite.toTopCat.mapCone (limit.cone F'))) :=
    (IsLimit.postcomposeHomEquiv _ _).symm
      (isLimitOfPreserves Profinite.toTopCat (limit.isLimit F'))
  have e : ((limit F' : Profinite.{u}) : Type u) ≃ₜ X :=
    (TopCat.homeoOfIso (IsLimit.conePointUniqueUpToIso isLimC' isLimC)).trans homX
  exact ⟨limit F', ⟨e⟩⟩

/-- A bundled profinite space homeomorphic to `X` exhibits `X` as a limit of finite discrete
spaces, via the `DiscreteQuotient` diagram. -/
lemma exists_profinite_to_isProfiniteStacks (X : Type u) [TopologicalSpace X]
    (h : ∃ Y : Profinite.{u}, Nonempty (Y ≃ₜ X)) :
    IsProfiniteStacks X := by
  obtain ⟨Y, ⟨e⟩⟩ := h
  obtain ⟨_, _, _⟩ := (exists_profinite_iff_triple X).1 ⟨Y, ⟨e⟩⟩
  let XProf : Profinite.{u} := Profinite.of X
  refine ⟨DiscreteQuotient X, inferInstance,
    XProf.diagram ⋙ Profinite.toTopCat,
    Profinite.toTopCat.mapCone XProf.asLimitCone,
    fun j => ⟨?_, ?_⟩,
    ⟨isLimitOfPreserves Profinite.toTopCat XProf.asLimit⟩,
    ⟨Homeomorph.refl X⟩⟩
  all_goals
    rw [Functor.comp_obj, Profinite.toTopCat, CompHausLike.compHausLikeToTop, inducedFunctor_obj,
      Profinite.diagram, Functor.comp_obj]
    infer_instance

/-- The Stacks definition of profinite is equivalent to being homeomorphic to an object of
Mathlib's bundled category `Profinite`. -/
theorem isProfiniteStacks_iff_exists_profinite (X : Type u) [TopologicalSpace X] :
    IsProfiniteStacks X ↔ ∃ Y : Profinite.{u}, Nonempty (Y ≃ₜ X) :=
  ⟨isProfiniteStacks_to_exists_profinite X, exists_profinite_to_isProfiniteStacks X⟩

/-- The Stacks definition of profinite is equivalent to `X` being a compact, Hausdorff, totally
disconnected topological space. -/
theorem isProfiniteStacks_iff_compact_t2_totallyDisconnected
    (X : Type u) [TopologicalSpace X] :
    IsProfiniteStacks X ↔
      CompactSpace X ∧ T2Space X ∧ TotallyDisconnectedSpace X :=
  (isProfiniteStacks_iff_exists_profinite X).trans (exists_profinite_iff_triple X)
