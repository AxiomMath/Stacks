module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Properties
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Openness
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen

/-!
# The generic fibre has the smallest local dimension

Let `f : X ⟶ S` be a dominant morphism locally of finite type between irreducible schemes, and
let `η` be the generic point of `S`. Every fibre of `f` has local dimension at least `dim X_η` at
every point, and a fibre `X_s` whose dimension is at most that of the generic fibre has local
dimension exactly `dim X_η` at every one of its points.

For any morphism locally of finite type, the local dimension of the fibre through a point only
grows when the point is specialized. The two fibres compared are in general distinct, so this is
not the monotonicity of the local dimension of a single space along a specialization.

## Main results

* `AlgebraicGeometry.apply_genericPoint_eq_genericPoint`: a dominant morphism of irreducible
  schemes sends the generic point to the generic point.
* `AlgebraicGeometry.irreducibleSpace_fiber_apply_genericPoint`: the fibre through the generic
  point of the source is irreducible.
* `AlgebraicGeometry.topologicalKrullDim_fiber_genericPoint_le`: the generic fibre's dimension
  bounds the local dimension of every fibre from below.
* `AlgebraicGeometry.topologicalKrullDimAt_fiber_eq_of_le`: a fibre of dimension at most that of
  the generic fibre has local dimension exactly `dim X_η` everywhere.
* `AlgebraicGeometry.fiberDimensionAt_le_of_specializes`: without any irreducibility or dominance
  hypothesis, the local dimension of the fibre through a point only grows when the point is
  specialized.

## Implementation notes

The generic point of an irreducible scheme is Mathlib's `genericPoint`, available because a
scheme is sober. A point of the fibre over `f x` corresponding to `x : X` is
`Scheme.Hom.asFiber x`, and the identification of `f.fiber s` with the set-theoretic preimage is
`Scheme.Hom.fiberHomeo`. The residue field at a point is `Scheme.residueField` and the structure
morphism of a fibre is `Scheme.Hom.fiberToSpecResidueField`.

## References

* [Stacks Project, Tag 02FZ](https://stacks.math.columbia.edu/tag/02FZ)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
* [Stacks Project, Tag 053R](https://stacks.math.columbia.edu/tag/053R)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A dominant morphism from an irreducible scheme to an irreducible scheme carries the generic
point to the generic point. -/
public theorem apply_genericPoint_eq_genericPoint {X S : Scheme.{u}} (f : X ⟶ S)
    [IrreducibleSpace X] [IrreducibleSpace S] [IsDominant f] :
    f (genericPoint X) = genericPoint S := by
  refine IsGenericPoint.eq (S := Set.univ) ?_ (genericPoint_spec S)
  show closure {f (genericPoint X)} = (Set.univ : Set S)
  refine Set.eq_univ_of_univ_subset ?_
  rw [← f.denseRange.closure_range]
  refine closure_minimal ?_ isClosed_closure
  rintro _ ⟨x, rfl⟩
  exact specializes_iff_mem_closure.mp ((genericPoint_specializes x).map f.continuous)

/-- The fibre of a morphism through the generic point of an irreducible source is irreducible. -/
public theorem irreducibleSpace_fiber_apply_genericPoint {X S : Scheme.{u}} (f : X ⟶ S)
    [IrreducibleSpace X] :
    IrreducibleSpace (f.fiber (f (genericPoint X))) := by
  refine (f.fiberHomeo (f (genericPoint X))).irreducibleSpace_iff.mpr
    (isIrreducible_iff_irreducibleSpace.mp ⟨⟨genericPoint X, rfl⟩, ?_⟩)
  rintro U V hU hV ⟨u, -, huU⟩ ⟨v, -, hvV⟩
  exact ⟨genericPoint X, rfl, (genericPoint_specializes u).mem_open hU huU,
    (genericPoint_specializes v).mem_open hV hvV⟩

/-- A quantity bounded by every natural number bounding the local dimension at a point is bounded
by that local dimension. -/
private theorem le_topologicalKrullDimAt_of_forall_nat {Y : Type*} [TopologicalSpace Y]
    (y : Y) {a : WithBot ℕ∞} (H : ∀ n : ℕ, topologicalKrullDimAt Y y ≤ n → a ≤ n) :
    a ≤ topologicalKrullDimAt Y y := by
  rcases eq_or_ne (topologicalKrullDimAt Y y) ⊤ with hne | hne
  · simp [hne]
  obtain ⟨⟨U, hyU, hU, hdU⟩, -⟩ := topologicalKrullDimAt_isLeast Y y
  have : Nonempty (IrreducibleCloseds ↥U) :=
    ⟨⟨closure {(⟨y, hyU⟩ : ↥U)}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  have h0 : (0 : WithBot ℕ∞) ≤ topologicalKrullDimAt Y y := hdU ▸ Order.krullDim_nonneg
  have hbot : topologicalKrullDimAt Y y ≠ ⊥ := fun hb => by rw [hb] at h0; simp at h0
  obtain ⟨a', ha⟩ := WithBot.ne_bot_iff_exists.mp hbot
  have ha' : a' ≠ ⊤ := by rintro rfl; exact hne (by simpa using ha.symm)
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp ha'
  rw [← ha]
  exact H n ha.ge

/-- If some fibre of a dominant morphism of irreducible schemes has local dimension at most `n`
at some point, then the generic fibre has dimension at most `n`. -/
@[ega "IV 13.1.6"]
private theorem topologicalKrullDim_fiber_genericPoint_le_of_le {X S : Scheme.{u}} (f : X ⟶ S)
    [IrreducibleSpace X] [IrreducibleSpace S] [IsDominant f] [LocallyOfFiniteType f]
    {x : X} {n : ℕ}
    (hx : topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) ≤ (n : WithBot ℕ∞)) :
    topologicalKrullDim (f.fiber (genericPoint S)) ≤ (n : WithBot ℕ∞) := by
  have hmem : genericPoint X ∈
      {z : X | topologicalKrullDimAt (f.fiber (f z)) (f.asFiber z) ≤ (n : WithBot ℕ∞)} :=
    (genericPoint_specializes x).mem_open (isOpen_setOf_fiberDimensionAt_le f n) hx
  have : IrreducibleSpace (f.fiber (f (genericPoint X))) :=
    irreducibleSpace_fiber_apply_genericPoint f
  have : LocallyOfFiniteType (f.fiberToSpecResidueField (f (genericPoint X))) :=
    (inferInstance : LocallyOfFiniteType
      (Limits.pullback.snd f (S.fromSpecResidueField (f (genericPoint X)))))
  rw [← apply_genericPoint_eq_genericPoint f,
    topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible
      (S.residueField (f (genericPoint X))) _
      (f.fiberToSpecResidueField (f (genericPoint X))) (f.asFiber (genericPoint X))]
  exact hmem

/-- **The generic fibre has the smallest local dimension.** For a dominant morphism locally of
finite type between irreducible schemes, the dimension of the generic fibre is at most the local
dimension of the fibre through any point of the source. -/
@[ega "IV 13.1.6", ega "IV 13.2.1"]
public theorem topologicalKrullDim_fiber_genericPoint_le {X S : Scheme.{u}} (f : X ⟶ S)
    [IrreducibleSpace X] [IrreducibleSpace S] [IsDominant f] [LocallyOfFiniteType f] (x : X) :
    topologicalKrullDim (f.fiber (genericPoint S)) ≤
      topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) := by
  exact le_topologicalKrullDimAt_of_forall_nat _ fun n hn ↦
    topologicalKrullDim_fiber_genericPoint_le_of_le f hn

/-- The local dimension of the fibre through a point only grows when the point is specialized: if
`η ⤳ x` then the fibre through `η` has local dimension at `η` at most the local dimension at `x`
of the fibre through `x`. -/
public theorem fiberDimensionAt_le_of_specializes {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] {η x : X} (hηx : η ⤳ x) :
    topologicalKrullDimAt (f.fiber (f η)) (f.asFiber η) ≤
      topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) := by
  exact le_topologicalKrullDimAt_of_forall_nat _ fun n hn ↦
    hηx.mem_open (isOpen_setOf_fiberDimensionAt_le f n) hn

/-- For a dominant morphism locally of finite type between irreducible schemes, a fibre whose
dimension does not exceed that of the generic fibre has local dimension exactly the dimension of
the generic fibre at every one of its points. -/
public theorem topologicalKrullDimAt_fiber_eq_of_le {X S : Scheme.{u}} (f : X ⟶ S)
    [IrreducibleSpace X] [IrreducibleSpace S] [IsDominant f] [LocallyOfFiniteType f] (s : S)
    (hdim : topologicalKrullDim (f.fiber s) ≤ topologicalKrullDim (f.fiber (genericPoint S)))
    (y : f.fiber s) :
    topologicalKrullDimAt (f.fiber s) y = topologicalKrullDim (f.fiber (genericPoint S)) := by
  refine le_antisymm ((topologicalKrullDimAt_le_topologicalKrullDim y).trans hdim) ?_
  have hsy : f (f.fiberι s y) = s := by
    simpa [Scheme.Hom.comp_apply] using congrArg (fun q : f.fiber s ⟶ S ↦ q y) (f.fiber_fac s)
  let e : f.fiber s ≃ₜ f.fiber (f (f.fiberι s y)) :=
    (f.fiberHomeo s).trans <| (Homeomorph.setCongr (by rw [hsy])).trans <|
      (f.fiberHomeo (f (f.fiberι s y))).symm
  have hey : e y = f.asFiber (f.fiberι s y) := (f.fiberι _).isEmbedding.injective rfl
  rw [topologicalKrullDimAt_eq_of_homeomorph e y, hey]
  exact topologicalKrullDim_fiber_genericPoint_le f (f.fiberι s y)

end AlgebraicGeometry

end
