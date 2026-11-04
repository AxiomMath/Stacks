module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleSmallModel
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleLocalization
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact

/-!
# The terminal object of the spaces-étale model of a quasi-compact space is quasi-compact

Let `X` be an algebraic space over `S` and `X_{spaces,étale}` its spaces-étale site, read through
its small model `AlgebraicGeometry.Space.spacesEtaleModelRingedTopos`. If an object of the model
has quasi-compact point space, it is a quasi-compact object of the site in the sense of
[Stacks, Tag 090H]: a covering sieve is jointly surjective on points, each of its arrows has open
image on points (an étale morphism of algebraic spaces is open on points, [Stacks, Tag 03IR]), so
finitely many of its arrows already have images covering the point space. In particular, when
`X` is quasi-compact the terminal object of the model is quasi-compact ([Stacks, Tag 03E4]).

This is the finiteness the proof of [Stacks, Tag 0CTM] uses to give a perfect object on `X` a
Tor amplitude in a fixed interval.

## Main results

* `AlgebraicGeometry.Space.exists_finite_ofArrows_mem_smallModelTopology`: finitely many arrows
  of a covering sieve of an object with quasi-compact point space cover it.
* `AlgebraicGeometry.Space.isQuasiCompactObject_smallModelTopology`: such an object is
  quasi-compact.
* `AlgebraicGeometry.Space.isQuasiCompactObject_spacesEtaleModelTerminal`: the terminal object
  of the model of a quasi-compact space is quasi-compact.

## References

* [Stacks Project, Tag 090H](https://stacks.math.columbia.edu/tag/090H)
* [Stacks Project, Tag 03IR](https://stacks.math.columbia.edu/tag/03IR)
* [Stacks Project, Tag 03E4](https://stacks.math.columbia.edu/tag/03E4)
* [Stacks Project, Tag 0CTM](https://stacks.math.columbia.edu/tag/0CTM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **Finitely many arrows of a covering sieve of the spaces-étale model cover.** Let `W` be an
object of the small model of `X_{spaces,étale}` whose underlying algebraic space has quasi-compact
point space. Every covering sieve of `W` contains finitely many arrows which generate a covering
sieve. -/
theorem exists_finite_ofArrows_mem_smallModelTopology
    (W : SmallModel.{u} (SpacesEtale B S hS X))
    (hW : CompactSpace (points B S hS ((SpacesEtale.toSpaces B S hS X).obj
      ((equivSmallModel.{u} (SpacesEtale B S hS X)).inverse.obj W)).1))
    (R : Sieve W) (hR : R ∈ smallModelTopology B S hS X W) :
    ∃ (ι : Type u) (_ : Finite ι) (V : ι → SmallModel.{u} (SpacesEtale B S hS X))
      (f : ∀ i, V i ⟶ W), (∀ i, R (f i)) ∧ Sieve.ofArrows V f ∈ smallModelTopology B S hS X W := by
  classical
  let e := equivSmallModel.{u} (SpacesEtale B S hS X)
  let F := SpacesEtale.toSpaces B S hS X
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense,
    SpacesEtale.mem_topology_iff_sievePointwiseCover] at hR
  -- For each point, an arrow of `R` whose image contains it.
  have hx : ∀ x : points B S hS (F.obj (e.inverse.obj W)).1, ∃ (Z : SmallModel.{u} _)
      (g : Z ⟶ W), R g ∧ x ∈ Set.range (pointsMap B S hS (F.obj (e.inverse.obj Z)).1
        (F.map (e.inverse.map g)).hom) := by
    intro x
    obtain ⟨V, f, ⟨Z, g, h, hg, rfl⟩, y, rfl⟩ := hR x
    refine ⟨Z, g, hg, pointsMap B S hS _ (F.map h).hom y, ?_⟩
    rw [F.map_comp]
    exact (pointsMap_comp_apply B S hS (F.map h).hom (F.map (e.inverse.map g)).hom y).symm
  choose Z g hg hmem using hx
  have hopen : ∀ x, IsOpen (Set.range (pointsMap B S hS (F.obj (e.inverse.obj (Z x))).1
      (F.map (e.inverse.map (g x))).hom)) := fun x =>
    isOpen_range_pointsMap_of_isEtale B S hS _ (F.obj (e.inverse.obj (Z x))).2
      (F.obj (e.inverse.obj W)).2 (SpacesEtale.isEtale_toSpaces_map B S hS X _)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _ hopen
    (fun x _ => Set.mem_iUnion.2 ⟨x, hmem x⟩)
  let k : ULift.{u} (Fin t.card) → points B S hS (F.obj (e.inverse.obj W)).1 :=
    fun j => (t.equivFin.symm j.down).1
  refine ⟨ULift.{u} (Fin t.card), inferInstance, fun j => Z (k j), fun j => g (k j),
    fun j => hg (k j), ?_⟩
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense,
    SpacesEtale.mem_topology_iff_sievePointwiseCover]
  intro x
  obtain ⟨i, hi, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  have hk : k ⟨t.equivFin ⟨i, hi⟩⟩ = i := by simp [k]
  obtain ⟨y, hy⟩ := hk ▸ hy
  exact ⟨_, e.inverse.map (g (k ⟨t.equivFin ⟨i, hi⟩⟩)), Sieve.image_mem_functorPushforward _ _
    (Sieve.ofArrows_mk _ _ (ULift.up (t.equivFin ⟨i, hi⟩))), y, hy⟩

/-- **An object of the spaces-étale model with quasi-compact point space is quasi-compact**
([Stacks, Tag 090H]). -/
theorem isQuasiCompactObject_smallModelTopology
    (W : SmallModel.{u} (SpacesEtale B S hS X))
    (hW : CompactSpace (points B S hS ((SpacesEtale.toSpaces B S hS X).obj
      ((equivSmallModel.{u} (SpacesEtale B S hS X)).inverse.obj W)).1)) :
    (smallModelTopology B S hS X).IsQuasiCompactObject W := by
  intro 𝒰 h𝒰
  obtain ⟨ι, hι, V, f, hf, hcov⟩ :=
    exists_finite_ofArrows_mem_smallModelTopology B S hS X W hW _ h𝒰
  choose s α hα using fun i => (Sieve.mem_ofArrows_iff _ _ _).1 (hf i)
  exact ⟨⟨ι, V, f⟩, ⟨s, α, fun i => (hα i).symm⟩, hcov, Set.toFinite _⟩

/-- **The terminal object of the spaces-étale model of a quasi-compact algebraic space is
quasi-compact** ([Stacks, Tag 090H], [Stacks, Tag 03E4]). -/
theorem isQuasiCompactObject_spacesEtaleModelTerminal (hX : IsQuasiCompactSpace B S hS X.1) :
    (smallModelTopology B S hS X).IsQuasiCompactObject (spacesEtaleModelTerminal B S hS X) := by
  let e := equivSmallModel.{u} (SpacesEtale B S hS X)
  let F := SpacesEtale.toSpaces B S hS X
  have : CompactSpace (points B S hS (F.obj (SpacesEtale.idObj B S hS X)).1) :=
    compactSpace_points_of_isQuasiCompactSpace B S hS X.2 hX
  refine isQuasiCompactObject_smallModelTopology B S hS X _ ?_
  let i := e.unitIso.app (SpacesEtale.idObj B S hS X)
  have hsurj : Function.Surjective (pointsMap B S hS (F.obj (SpacesEtale.idObj B S hS X)).1
      (F.map i.hom).hom) := fun y => ⟨pointsMap B S hS _ (F.map i.inv).hom y, by
    rw [← pointsMap_comp_apply, ← ObjectProperty.FullSubcategory.comp_hom, ← F.map_comp,
      i.inv_hom_id, F.map_id]
    exact congrFun (pointsMap_id B S hS _) y⟩
  exact hsurj.compactSpace (continuous_pointsMap B S hS _)

end AlgebraicGeometry.Space

end
