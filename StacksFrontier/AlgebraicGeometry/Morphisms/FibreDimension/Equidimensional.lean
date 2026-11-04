module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Comparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components
public import StacksFrontier.Topology.Dimension.Equidimensional
public import StacksCore.Tactic.StacksAttribute

/-!
# Equidimensional fibres and relative dimension

A scheme locally of finite type over a field is equidimensional of dimension `d` exactly when its
local dimension is `d` at every point: the local dimension at a point is the largest dimension of
an irreducible component through that point (Tag 0A21), so constancy of the local dimension and
equality of the dimensions of all the components determine each other.

This gives the two stability properties of the relative dimension of Tag 02NJ used when a
morphism is cut down to an open subscheme of its source or factored through an open subscheme of
its target: the fibres only get replaced by open subspaces, respectively by homeomorphic copies.

## Main results

* `AlgebraicGeometry.topologicalKrullDimAt_eq_of_equidimensional` and
  `AlgebraicGeometry.equidimensional_of_topologicalKrullDimAt_eq` are the two directions of the
  comparison for a scheme locally of finite type over a field.
* `AlgebraicGeometry.topologicalKrullDimAt_fiber_eq_of_relativeDimension`: on an open subscheme
  of constant relative dimension `d` the fibre has local dimension `d`.
* `AlgebraicGeometry.RelativeDimension.comp_isOpenImmersion` and
  `AlgebraicGeometry.RelativeDimension.of_comp_isOpenImmersion`: relative dimension is inherited
  by the restriction of the source to an open subscheme and by a factorization through an open
  subscheme of the target.
* `AlgebraicGeometry.topologicalKrullDim_eq_of_relativeDimension`: over a one-point base the
  relative dimension of a morphism out of a nonempty scheme is the dimension of its source.

## References

* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
* [Stacks Project, Tag 02NJ](https://stacks.math.columbia.edu/tag/02NJ)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A scheme locally of finite type over a field whose local dimension is constant is
equidimensional: at the generic point of a component the local dimension is the dimension of that
component, since no other component contains it. -/
public theorem equidimensional_of_topologicalKrullDimAt_eq (k : Type u) [Field k]
    (Z : Scheme.{u}) (q : Z ⟶ Spec (.of k)) [LocallyOfFiniteType q] {d : ℕ}
    (hd : ∀ z : Z, topologicalKrullDimAt Z z = (d : WithBot ℕ∞)) : Equidimensional Z := by
  have hcomp : ∀ W ∈ irreducibleComponents Z, topologicalKrullDim W = (d : WithBot ℕ∞) := by
    intro W hW
    have hηW : IsGenericPoint hW.1.genericPoint W :=
      hW.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents W hW)
    have honly : ∀ V ∈ irreducibleComponents Z, hW.1.genericPoint ∈ V → V = W := by
      intro V hV hηV
      have hWV : W ⊆ V := hηW ▸ closure_minimal (Set.singleton_subset_iff.mpr hηV)
        (isClosed_of_mem_irreducibleComponents V hV)
      exact (hWV.antisymm (hW.2 hV.1 hWV)).symm
    have hlocal : topologicalKrullDimAt Z hW.1.genericPoint = topologicalKrullDim W := by
      rw [topologicalKrullDimAt_eq_iSup_irreducibleComponents k Z q hW.1.genericPoint]
      refine le_antisymm (iSup_le fun V ↦ iSup_le fun hV ↦ by rw [honly V hV.1 hV.2]) ?_
      exact le_iSup_of_le W (le_iSup_of_le ⟨hW, hηW.mem⟩ le_rfl)
    exact hlocal.symm.trans (hd _)
  exact fun C hC D hD ↦ (hcomp C hC).trans (hcomp D hD).symm

/-- The local dimension of a fibre, read at the point of the fibre determined by a point of the
source lying over its base point. -/
private theorem topologicalKrullDimAt_fiber_eq_cast {X S : Scheme.{u}} (f : X ⟶ S) {s : S}
    (w : f.fiber s) :
    topologicalKrullDimAt (f.fiber s) w =
      topologicalKrullDimAt (f.fiber (f (f.fiberι s w))) (f.asFiber (f.fiberι s w)) :=
  (Scheme.Hom.topologicalKrullDimAt_fiber_fiberι f s w).symm

/-- If `f` has relative dimension `d`, the fibre through any point `x` of the source has local
dimension `d` at `x`. -/
private theorem topologicalKrullDimAt_fiber_eq_of_relativeDimension_aux {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] {d : ℕ} (hf : RelativeDimension f d) (x : X) :
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = (d : WithBot ℕ∞) := by
  have : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) := by
    change LocallyOfFiniteType (Limits.pullback.snd f (S.fromSpecResidueField (f x)))
    infer_instance
  obtain ⟨heq, hdim⟩ := hf (f x) ⟨f.asFiber x⟩
  exact topologicalKrullDimAt_eq_of_equidimensional (S.residueField (f x)) (f.fiber (f x))
    (f.fiberToSpecResidueField (f x)) heq hdim (f.asFiber x)

/-- Relative dimension in the sense of Tag 02NJ is inherited by the restriction of the source to
an open subscheme: the fibres of the restriction are open subspaces of the original fibres, so
their local dimensions are unchanged, and a scheme over a field with constant local dimension `d`
is equidimensional of dimension `d`. -/
public theorem RelativeDimension.comp_isOpenImmersion {U X S : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (f : X ⟶ S) [LocallyOfFiniteType f] {d : ℕ}
    (hf : RelativeDimension f d) : RelativeDimension (j ≫ f) d := by
  have : LocallyOfFiniteType (j ≫ f) := inferInstance
  intro s hs
  have hlocal : ∀ w : (j ≫ f).fiber s,
      topologicalKrullDimAt ((j ≫ f).fiber s) w = (d : WithBot ℕ∞) := by
    intro w
    set x : U := (j ≫ f).fiberι s w with hx
    rw [topologicalKrullDimAt_fiber_eq_cast (j ≫ f) w, ← hx,
      fiberDimensionAt_comp_openImmersion j f x]
    exact topologicalKrullDimAt_fiber_eq_of_relativeDimension_aux f hf (j x)
  have hFT : LocallyOfFiniteType ((j ≫ f).fiberToSpecResidueField s) := by
    change LocallyOfFiniteType (Limits.pullback.snd (j ≫ f) (S.fromSpecResidueField s))
    infer_instance
  refine ⟨equidimensional_of_topologicalKrullDimAt_eq (S.residueField s) ((j ≫ f).fiber s)
    ((j ≫ f).fiberToSpecResidueField s) hlocal, ?_⟩
  rw [topologicalKrullDim_eq_iSup_localKrullDim]
  have hloc : ∀ w : (j ≫ f).fiber s,
      localKrullDim ((j ≫ f).fiber s) w = (d : WithBot ℕ∞) := fun w ↦ by
    rw [← topologicalKrullDimAt_eq_localKrullDim]; exact hlocal w
  simp_rw [hloc]
  have : Nonempty ((j ≫ f).fiber s) := hs
  exact iSup_const

/-- Relative dimension in the sense of Tag 02NJ passes to a factorization through an open
subscheme of the target: the fibres of the factor are homeomorphic to the fibres of the
composite. -/
public theorem RelativeDimension.of_comp_isOpenImmersion {X V Y : Scheme.{u}} (g : X ⟶ V)
    [LocallyOfFiniteType g] (i : V ⟶ Y) [IsOpenImmersion i] (f : X ⟶ Y) (hcomp : g ≫ i = f)
    [LocallyOfFiniteType f] {d : ℕ} (hf : RelativeDimension f d) : RelativeDimension g d := by
  intro v hne
  have hx : ∀ x : X, f x = i (g x) := fun x ↦ by
    simpa [Scheme.Hom.comp_apply] using (congrArg (fun k : X ⟶ Y ↦ k x) hcomp).symm
  have hset : (g ⁻¹' {v} : Set X) = f ⁻¹' {i v} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [hx x]
    exact ⟨fun h ↦ congrArg i h, fun h ↦ i.isOpenEmbedding.injective h⟩
  let e : g.fiber v ≃ₜ f.fiber (i v) :=
    (g.fiberHomeo v).trans ((Homeomorph.setCongr hset).trans (f.fiberHomeo (i v)).symm)
  obtain ⟨w⟩ := hne
  obtain ⟨heq, hdim⟩ := hf (i v) ⟨e w⟩
  exact ⟨heq.of_homeomorph e, (IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph).trans hdim⟩

/-- On an open subscheme over which a morphism has relative dimension `d`, the fibre has local
dimension exactly `d` at every point. -/
public theorem topologicalKrullDimAt_fiber_eq_of_relativeDimension {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (U : X.Opens) (d : ℕ)
    (hU : RelativeDimension (U.ι ≫ f) d) (x : X) (hx : x ∈ U) :
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = (d : WithBot ℕ∞) := by
  exact (fiberDimensionAt_comp_openImmersion U.ι f ⟨x, hx⟩).symm.trans
    (topologicalKrullDimAt_fiber_eq_of_relativeDimension_aux (U.ι ≫ f) hU ⟨x, hx⟩)

/-- Over a base with a single point the only nonempty fibre of a morphism is homeomorphic to its
source. So a nonempty scheme of relative dimension `d` (Tag 02NJ) over a one-point base, such as
`Spec(k)` for a field `k`, has dimension `d`. -/
public theorem topologicalKrullDim_eq_of_relativeDimension {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [Subsingleton S] [Nonempty X] {d : ℕ}
    (hf : RelativeDimension f d) : topologicalKrullDim X = (d : WithBot ℕ∞) := by
  obtain ⟨x⟩ := ‹Nonempty X›
  have hpre : f ⁻¹' {f x} = (Set.univ : Set X) := by
    ext y
    exact ⟨fun _ ↦ trivial, fun _ ↦ Subsingleton.elim _ _⟩
  let e : f.fiber (f x) ≃ₜ X :=
    (f.fiberHomeo (f x)).trans ((Homeomorph.setCongr hpre).trans (Homeomorph.Set.univ X))
  exact (IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph).symm.trans
    (hf (f x) ⟨f.asFiber x⟩).2

end AlgebraicGeometry

end
