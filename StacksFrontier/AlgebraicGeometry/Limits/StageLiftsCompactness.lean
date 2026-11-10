module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.DiscreteSubset

/-!
# Lifts of a point through a limit of morphisms with finitely many lifts

Let `D : I ⥤ Scheme` be a diagram over a fixed scheme `Y`, through `t : D ⟶ const Y`, let `c` be a
limit cone with vertex `X` and let `f : X ⟶ Y` be the induced morphism. Fix a morphism
`y : T ⟶ Y`. A lift of `y` through `f` determines a lift of `y` through every `t j`, by
composing with the projections, and is determined by these. When every `t j` admits only finitely
many lifts of `y`, the lifts through `f` form a compact space for the topology in which the
*cylinders* — the sets of lifts agreeing with a given one at a given stage — are open: they are a
closed subset of a product of finite discrete sets. This file proves the consequence that every
choice of a stage for each lift gives a cover of the lifts by cylinders admitting a finite
subcover.

## Main results

* `AlgebraicGeometry.exists_finset_forall_exists_comp_eq_of_isLimit` — a choice of a stage
  `j x` for every lift `x` through `f` admits a finite set `S` of lifts such that every lift agrees
  with some member `x` of `S` at the stage `j x`.

## Implementation notes

The topology is not made an instance: it is built inside the proof, as the topology induced from
the product of the finite discrete sets of lifts through the stages. Tychonoff's theorem makes
that product compact, and the image of the lifts through `f` is the closed subset of compatible
families, every compatible family coming from a lift through `f` by the limit property.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  {Y : Scheme.{u}} (t : D ⟶ (Functor.const I).obj Y) (f : c.pt ⟶ Y)
  (hf : ∀ j, c.π.app j ≫ t.app j = f) {T : Scheme.{u}} (y : T ⟶ Y)

include hc hf in
/-- **Finitely many cylinders cover the lifts through a limit.** If every stage `t j` admits
only finitely many lifts of `y`, then for every choice of a stage `j x` for each lift `x` of `y`
through `f` there is a finite set `S` of lifts such that every lift `x'` agrees with some
`x ∈ S` after composing with the projection to the stage `j x`. -/
theorem exists_finset_forall_exists_comp_eq_of_isLimit [Nonempty I]
    [∀ k, Finite {a : T ⟶ D.obj k // a ≫ t.app k = y}]
    (j : {a : T ⟶ c.pt // a ≫ f = y} → I) :
    ∃ S : Finset {a : T ⟶ c.pt // a ≫ f = y},
      ∀ x' : {a : T ⟶ c.pt // a ≫ f = y}, ∃ x ∈ S,
        x'.1 ≫ c.π.app (j x) = x.1 ≫ c.π.app (j x) := by
  classical
  let L := {a : T ⟶ c.pt // a ≫ f = y}
  let Lk (k : I) := {a : T ⟶ D.obj k // a ≫ t.app k = y}
  let (k : I) : TopologicalSpace (Lk k) := ⊥
  have (k : I) : DiscreteTopology (Lk k) := ⟨rfl⟩
  have (k : I) : CompactSpace (Lk k) := Finite.compactSpace
  let ev : L → ∀ k, Lk k := fun x k =>
    ⟨x.1 ≫ c.π.app k, by rw [Category.assoc, hf, x.2]⟩
  let : TopologicalSpace L := TopologicalSpace.induced ev Pi.topologicalSpace
  have hind : Topology.IsInducing ev := ⟨rfl⟩
  have hinj : Function.Injective ev := fun x x' h =>
    Subtype.ext (hc.hom_ext fun k => congrArg Subtype.val (congrFun h k))
  have hemb : Topology.IsEmbedding ev := ⟨hind, hinj⟩
  have hrange : Set.range ev =
      ⋂ (k : I) (k' : I) (a : k ⟶ k'), {φ : ∀ k, Lk k | (φ k).1 ≫ D.map a = (φ k').1} := by
    ext φ
    simp only [Set.mem_range, Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, rfl⟩ k k' a
      change (x.1 ≫ c.π.app k) ≫ D.map a = x.1 ≫ c.π.app k'
      rw [Category.assoc, c.w]
    · intro hφ
      obtain ⟨k₀⟩ := ‹Nonempty I›
      let s : Cone D :=
        { pt := T
          π := { app := fun k => (φ k).1
                 naturality := fun k k' a => by
                   simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
                   exact (hφ k k' a).symm } }
      refine ⟨⟨hc.lift s, ?_⟩, ?_⟩
      · rw [← hf k₀, ← Category.assoc, hc.fac s k₀]
        exact (φ k₀).2
      · funext k
        exact Subtype.ext (hc.fac s k)
  have hclosed : IsClosed (Set.range ev) := by
    rw [hrange]
    refine isClosed_iInter fun k => isClosed_iInter fun k' => isClosed_iInter fun a => ?_
    let g : (∀ k, Lk k) → Lk k × Lk k' := fun φ => (φ k, φ k')
    have hg : Continuous g := (continuous_apply k).prodMk (continuous_apply k')
    exact (isClosed_discrete
      {p : Lk k × Lk k' | p.1.1 ≫ D.map a = p.2.1}).preimage hg
  have hcompact : IsCompact (Set.univ : Set L) := by
    rw [hemb.isCompact_iff, Set.image_univ]
    exact hclosed.isCompact
  let U (x : L) : Set L := {x' | x'.1 ≫ c.π.app (j x) = x.1 ≫ c.π.app (j x)}
  have hU (x : L) : IsOpen (U x) := by
    have : U x = ev ⁻¹' ((fun φ : ∀ k, Lk k => φ (j x)) ⁻¹' {ev x (j x)}) := by
      ext x'
      simp only [U, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, ev]
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    rw [this]
    exact ((isOpen_discrete _).preimage (continuous_apply (j x))).preimage hind.continuous
  obtain ⟨S, hS⟩ := hcompact.elim_finite_subcover U hU fun x _ => Set.mem_iUnion.mpr ⟨x, rfl⟩
  refine ⟨S, fun x' => ?_⟩
  obtain ⟨x, hxS, hx'⟩ := Set.mem_iUnion₂.mp (hS (Set.mem_univ x'))
  exact ⟨x, hxS, hx'⟩

end AlgebraicGeometry
