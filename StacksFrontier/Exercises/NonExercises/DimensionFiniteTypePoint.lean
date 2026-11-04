module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Properties
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.SpecField
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Properties.NoetherianClosedPoints
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Specialization
public import StacksFrontier.Topology.Dimension.Krull

/-!
# Dimension achieved at a closed finite type point

The dimension of a finite-dimensional scheme is attained as its local dimension at a closed
point, and such a point is a finite type point of the scheme.

The proof starts from a chain of irreducible closed subsets of maximal length. Its bottom
member is minimal among irreducible closed subsets, so the scheme being sober it is the
closure of a single point `x`, and minimality makes that closure the singleton `{x}`, which is
therefore closed. Every open neighbourhood of `x` meets all members of the chain, so the chain
restricts to a chain of the same length in it; hence the local dimension at `x` is at least the
length of the chain, while it is at most the dimension of the scheme. Finally the inclusion of
a closed point is a closed immersion, hence locally of finite type, which by the
characterization of finite-type morphisms from the spectrum of a field makes `x` a finite type
point.

## Main results

* `AlgebraicGeometry.exists_isClosed_isFiniteTypePoint_dim_eq`: a finite-dimensional scheme has
  a closed finite type point at which its local dimension equals its dimension.

## Implementation notes

Finite dimension is expressed by an equality `topologicalKrullDim X = d` with `d` a natural
number; in particular this excludes the empty scheme, whose dimension is `⊥`.

## References

* [Stacks Project, Tag 0DRR](https://stacks.math.columbia.edu/tag/0DRR)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- A chain of irreducible closed subsets whose bottom member meets an open subset `U`
restricts to a chain of the same length in `U`, so `U` has dimension at least that length. -/
private lemma length_le_topologicalKrullDim_of_head_mem
    {X : Type u} [TopologicalSpace X]
    (p : LTSeries (TopologicalSpace.IrreducibleCloseds X))
    {x : X} (hx : x ∈ (p.head : Set X))
    (U : Set X) (hU : IsOpen U) (hxU : x ∈ U) :
    (p.length : WithBot ℕ∞) ≤ topologicalKrullDim (↥U) := by
  let e := TopologicalSpace.IrreducibleCloseds.orderIsoOfIsOpenEmbedding
    (Subtype.val : ↥U → X) hU.isOpenEmbedding_subtypeVal
  have hmem (i : Fin (p.length + 1)) :
      ((Subtype.val : ↥U → X) ⁻¹' (p.toFun i : Set X)).Nonempty :=
    ⟨⟨x, hxU⟩, (LTSeries.monotone p (Fin.zero_le i)) hx⟩
  let q : LTSeries (TopologicalSpace.IrreducibleCloseds ↥U) :=
    { length := p.length
      toFun := fun i => e.symm ⟨p.toFun i, hmem i⟩
      step := fun i => e.symm.strictMono (p.step i) }
  exact Order.LTSeries.length_le_krullDim q

/-- A closed point of a scheme is a finite type point. -/
private lemma isFiniteTypePoint_of_isClosed
    {X : Scheme.{u}} {x : X} (hx : IsClosed ({x} : Set X)) :
    IsFiniteTypePoint x := by
  have hloc : LocallyOfFiniteType (X.fromSpecResidueField x) := by
    have : IsClosedImmersion (X.fromSpecResidueField x) :=
      isClosed_singleton_iff_isClosedImmersion.mp hx
    infer_instance
  exact ((finiteType_specField_tfae (X.fromSpecResidueField x)).out 2 1).mp hloc

/-- A finite-dimensional scheme has a closed finite type point at which its local dimension
equals its dimension. -/
@[stacks 0DRR]
theorem exists_isClosed_isFiniteTypePoint_dim_eq
    (X : Scheme.{u}) (d : ℕ) (hX : topologicalKrullDim X = d) :
    ∃ x : X, IsClosed ({x} : Set X) ∧
      IsFiniteTypePoint x ∧
      topologicalKrullDimAt X x = topologicalKrullDim X := by
  obtain ⟨p, hp⟩ : ∃ p : LTSeries (TopologicalSpace.IrreducibleCloseds X), p.length = d :=
    Order.le_krullDim_iff.mp hX.ge
  have hmin : ∀ {Z : TopologicalSpace.IrreducibleCloseds X}, Z ≤ p.head → p.head ≤ Z := by
    intro Z hZ
    by_contra hnot
    have hqle : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim X := by
      simpa [topologicalKrullDim, hp] using
        Order.LTSeries.length_le_krullDim
          (p.cons Z (lt_of_le_of_ne hZ (fun h => hnot (h ▸ le_rfl))))
    rw [hX] at hqle
    exact Nat.not_succ_le_self d (by exact_mod_cast hqle)
  obtain ⟨x, hgen⟩ := QuasiSober.sober p.head.isIrreducible' p.head.isClosed'
  have hx := hgen.mem
  have hclosedset : (p.head : Set X) = {x} := by
    refine Set.Subset.antisymm (fun y hy => ?_) (Set.singleton_subset_iff.mpr hx)
    let Z : TopologicalSpace.IrreducibleCloseds X :=
      ⟨closure ({y} : Set X), isIrreducible_singleton.closure, isClosed_closure⟩
    have hZle : Z ≤ p.head := by
      change closure ({y} : Set X) ⊆ (p.head : Set X)
      exact closure_minimal (Set.singleton_subset_iff.mpr hy) p.head.isClosed'
    exact (hgen.eq (show IsGenericPoint y (p.head : Set X) from
      congrArg (fun V : TopologicalSpace.IrreducibleCloseds X => (V : Set X))
        (le_antisymm hZle (hmin hZle)))).symm
  have hxclosed : IsClosed ({x} : Set X) := hclosedset ▸ p.head.isClosed'
  have hlocal : (d : WithBot ℕ∞) ≤ topologicalKrullDimAt X x := by
    unfold topologicalKrullDimAt
    exact le_iInf fun U => by
      simpa [hp] using length_le_topologicalKrullDim_of_head_mem p hx U.1 U.2.2 U.2.1
  refine ⟨x, hxclosed, isFiniteTypePoint_of_isClosed hxclosed, ?_⟩
  apply le_antisymm (topologicalKrullDimAt_le_topologicalKrullDim x)
  rwa [hX]

/-- **The local dimension of a locally Noetherian scheme is attained at a locally closed point
of any prescribed neighbourhood.** For `x ∈ W` with `W` open there is a point `x₀ ∈ W` whose
singleton is locally closed in `X` and at which the local dimension of `X` is the local dimension
at `x`.

The local dimension is a *minimum* over open neighbourhoods, so some open `V ⊆ W` containing `x`
has `dim V = dim_x X`. If that value is finite,
`AlgebraicGeometry.exists_isClosed_isFiniteTypePoint_dim_eq` produces a point of `V` closed in
`V` at which `V` attains its dimension; a point closed in an open subset is locally closed, and
the local dimension is unchanged by passing to an open subscheme. If the value is infinite no
neighbourhood of `x` is finite dimensional and that lemma does not apply; instead `x` specializes
inside `V` to a point closed in `V`, and the local dimension cannot decrease along a
specialization, so the value `∞` is attained there as well. -/
theorem exists_isLocallyClosed_topologicalKrullDimAt_eq (X : Scheme.{u})
    [IsLocallyNoetherian X] (x : X) {W : Set X} (hW : IsOpen W) (hxW : x ∈ W) :
    ∃ x₀ ∈ W, IsLocallyClosed ({x₀} : Set X) ∧
      topologicalKrullDimAt X x₀ = topologicalKrullDimAt X x := by
  classical
  obtain ⟨⟨V, hxV, hVopen, hVdim⟩, hleast⟩ := topologicalKrullDimAt_isLeast X x
  set U : X.Opens := ⟨V ∩ W, hVopen.inter hW⟩
  have hxU : x ∈ U := ⟨hxV, hxW⟩
  have hUdim : topologicalKrullDimAt X x = topologicalKrullDim U.toScheme :=
    le_antisymm (hleast ⟨(U : Set X), hxU, U.2, rfl⟩)
      ((topologicalKrullDim_le_of_subset Set.inter_subset_left).trans hVdim.ge)
  have : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
  have hopen : topologicalKrullDimAt X x = topologicalKrullDimAt U.toScheme ⟨x, hxU⟩ :=
    U.ι.isOpenEmbedding.topologicalKrullDimAt_eq ⟨x, hxU⟩
  have key : ∃ p : U.toScheme, IsClosed ({p} : Set U.toScheme) ∧
      topologicalKrullDimAt U.toScheme p = topologicalKrullDimAt X x := by
    rcases eq_or_ne (topologicalKrullDim U.toScheme) ⊤ with htop | hfin
    · obtain ⟨p, hp, hspec⟩ := exists_specializes_closedPoint U.toScheme ⟨x, hxU⟩
      refine ⟨p, hp, le_antisymm ?_ ?_⟩
      · simp [hUdim, htop]
      · rw [hopen]
        exact topologicalKrullDimAt_le_of_specialization hspec
    · have hbot : topologicalKrullDim U.toScheme ≠ ⊥ := by
        rw [← hUdim]
        exact topologicalKrullDimAt_ne_bot x
      obtain ⟨d, hd⟩ : ∃ d : ℕ, topologicalKrullDim U.toScheme = (d : WithBot ℕ∞) := by
        obtain ⟨b, hb⟩ := WithBot.ne_bot_iff_exists.mp hbot
        have hbne : b ≠ ⊤ := fun hbtop => hfin (by rw [← hb, hbtop]; rfl)
        obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp hbne
        refine ⟨d, ?_⟩
        rw [← hb, ← hd]
        rfl
      obtain ⟨p, hpclosed, -, hpdim⟩ :=
        exists_isClosed_isFiniteTypePoint_dim_eq U.toScheme d hd
      exact ⟨p, hpclosed, hpdim.trans hUdim.symm⟩
  obtain ⟨p, hpclosed, hpdim⟩ := key
  refine ⟨U.ι p, ?_, ?_, (U.ι.isOpenEmbedding.topologicalKrullDimAt_eq p).trans hpdim⟩
  · have hmem : (U.ι p : X) ∈ (U : Set X) := U.range_ι ▸ Set.mem_range_self p
    exact hmem.2
  · have himg := hpclosed.isLocallyClosed.image U.ι.isOpenEmbedding.isEmbedding.isInducing
      (by rw [Scheme.Opens.range_ι]; exact U.2.isLocallyClosed)
    rwa [Set.image_singleton] at himg

end AlgebraicGeometry

end
