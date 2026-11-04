module

public import StacksFrontier.AlgebraicGeometry.F6Rank128.FiberDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.CodimensionZeroCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Sober
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionFunction
public import StacksFrontier.AlgebraicGeometry.Spaces.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionEtaleInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionLocalRings
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ConstructibleSets
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.DimensionSemicontinuity
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RationalMaps
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence

/-!
# Dominant morphisms of finite type between integral algebraic spaces

A dominant morphism locally of finite type between integral algebraic spaces over a scheme,
with locally Noetherian target, is the datum from which the dimension of the source is
bounded by the dimension of the target plus the transcendence degree of the generic point of
the source over that of the target, with equality when the morphism is proper (Stacks 0EDC).
The two generic points are part of the datum: the point space of an integral algebraic space
is irreducible, so a generic point exists, but it is a choice, and every statement about the
two of them fixes one.

## Main definitions

* `AlgebraicGeometry.Space.IntegralDominantMorphismSituation` bundles the two spaces, the
  morphism, the four hypotheses on them and the two chosen generic points.

## Main results

* `AlgebraicGeometry.Space.dimension_le_dimension_add_transcendenceDegree`: the dimension
  inequality of **Stacks 0EDC**.
* `AlgebraicGeometry.Space.dimension_eq_dimension_add_transcendenceDegree`: the equality of
  **Stacks 0EDC** for a proper morphism.

## Implementation notes

The spaces are presheaves on the big fppf site over the base, and local Noetherianity of the
target is the étale-local property of Stacks 03E6 applied to locally Noetherian schemes, as
elsewhere in the library. Integrality is `AlgebraicGeometry.Space.IsIntegralSpace` of
Stacks 0AD4, which already contains decency, so the point spaces are the sober irreducible
spaces the generic points are chosen in.

A generic point is recorded as a point whose closure in the canonical topology
`AlgebraicGeometry.Space.pointTopology` is the whole point space, which is
`IsGenericPoint _ Set.univ`; the topology is supplied inside the type of each of those two
fields, since it is not an instance outside the files that make it one.

The inequality is the supremum over the points of the source of the inequality of
Stacks 0BAX: at a point `x'` the dimension of the local ring of the source is at most the
dimension of the local ring of the target at the image of `x'` plus the largest
residue-field transcendence degree at a codimension-zero point specializing to `x'`. Both
dimensions are the suprema of the dimensions of the local rings by Stacks 0BAN, so the only
work is to identify that largest degree with the degree at the chosen generic point. What that
needs is the content of Stacks 0ABV, that the generic point of `|X|` is the unique point at
which the local ring of `X` has dimension zero, and in the form
`AlgebraicGeometry.Space.eq_of_specializes_of_localRingDimension_eq_zero`: a codimension-zero
point of a decent algebraic space has no generization but itself, and the chosen generic
point generizes every point. Soberness of `|X|` — Stacks 03K6 — is what the source invokes to
produce the generic point of the irreducible component through a given point, and it is not
needed here, because the generic point of the whole of `|X|` is part of the datum.

The numerical form of the transcendence degree of Stacks 04NM used by Stacks 0BAX is
`AlgebraicGeometry.Space.residueFieldTranscendenceDegreeAt`, which takes the unique value the
chartwise predicate holds at; the statement below is phrased with the predicate itself, so it
holds for whichever value of `ℕ∞` specifies the transcendence degree at the generic point.

The reverse inequality under properness is proved by exhibiting chains of specializations
rather than by the reduction to schemes of the source, which passes through a finite
surjective cover of a quasi-compact quasi-separated algebraic space by a scheme. Both
dimensions are read on one commuting pair of surjective étale scheme charts — Stacks 02X1
produces the pair and Stacks 0A4H says a surjective étale morphism does not change the
dimension — so each becomes the Krull dimension of the point space of a scheme, and a lower
bound on it is a chain of specializations. Three facts assemble such a chain in the source. A
chain in the chart of the target pushes forward to a chain of the same length in the point
space of the target because two points of an étale chart with the same image, one a
specialization of the other, are equal (Stacks 03K5); the chain may be taken to begin at the
generic point, which generizes every point. Properness makes the map on points closed, so that
chain lifts to the source from any point above the generic point of the target (Stacks 0066).
Below such a point sit the transcendence degree many further nontrivial specializations: the
fibre of the morphism of charts through the chart point above the generic point of the source
has dimension at least the transcendence degree there, by the dimension formula for a fibre of
Stacks 02FX, and the resulting chain lies inside that fibre, hence over the generic point of
the target. The concatenation is a chain in the point space of the source, and it lifts to the
chart by Stacks 03IL.

## References

* [Stacks Project, Tag 0AD4](https://stacks.math.columbia.edu/tag/0AD4)
* [Stacks Project, Tag 0ABV](https://stacks.math.columbia.edu/tag/0ABV)
* [Stacks Project, Tag 02FX](https://stacks.math.columbia.edu/tag/02FX)
* [Stacks Project, Tag 03IL](https://stacks.math.columbia.edu/tag/03IL)
* [Stacks Project, Tag 03K5](https://stacks.math.columbia.edu/tag/03K5)
* [Stacks Project, Tag 0A4H](https://stacks.math.columbia.edu/tag/0A4H)
* [Stacks Project, Tag 0BAX](https://stacks.math.columbia.edu/tag/0BAX)
* [Stacks Project, Tag 0BAN](https://stacks.math.columbia.edu/tag/0BAN)
* [Stacks Project, Tag 0EDC](https://stacks.math.columbia.edu/tag/0EDC)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- A dominant morphism locally of finite type between integral algebraic spaces over `S`
whose target is locally Noetherian, together with a generic point of each of the two point
spaces. -/
structure IntegralDominantMorphismSituation
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) where
  /-- The source of the morphism. -/
  source : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- The target of the morphism. -/
  target : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- The morphism itself. -/
  hom : source ⟶ target
  /-- The source is an algebraic space over `S`. -/
  isAlgebraicSpace_source : IsAlgebraicSpace B S hS source
  /-- The target is an algebraic space over `S`. -/
  isAlgebraicSpace_target : IsAlgebraicSpace B S hS target
  /-- The target is locally Noetherian. -/
  locallyNoetherian_target : HasEtaleLocalProperty B S hS target
    (fun T : Scheme.{u} => IsLocallyNoetherian T)
  /-- The source is integral. -/
  isIntegralSpace_source : IsIntegralSpace B S hS source
  /-- The target is integral. -/
  isIntegralSpace_target : IsIntegralSpace B S hS target
  /-- The morphism is dominant. -/
  isDominant : IsDominant B S hS hom
  /-- The morphism is locally of finite type. -/
  isLocallyOfFiniteType : IsLocallyOfFiniteType B S hS hom
  /-- The chosen point of the source. -/
  sourcePoint : points B S hS source
  /-- The chosen point of the target. -/
  targetPoint : points B S hS target
  /-- The chosen point of the source is a generic point of its point space. -/
  isGenericPoint_sourcePoint :
    letI : TopologicalSpace (points B S hS source) := pointTopology B S hS source
    IsGenericPoint sourcePoint Set.univ
  /-- The chosen point of the target is a generic point of its point space. -/
  isGenericPoint_targetPoint :
    letI : TopologicalSpace (points B S hS target) := pointTopology B S hS target
    IsGenericPoint targetPoint Set.univ

/-! ### The dimension inequality -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0EDC, the dimension inequality.** Let `f : X ⟶ Y` be a dominant morphism locally
of finite type of integral algebraic spaces over `S` with `Y` locally Noetherian, and let `x`
and `y` be generic points of `|X|` and `|Y|`. If the transcendence degree of `f` at `x` is
`r`, then `dim X ≤ dim Y + r`. -/
@[stacks 0EDC "the dimension inequality"]
theorem dimension_le_dimension_add_transcendenceDegree
    (s : IntegralDominantMorphismSituation B S hS) (r : ℕ∞)
    (hr : HasTranscendenceDegreeAt B S hS s.hom s.sourcePoint r) :
    dimension B S hS s.source s.isAlgebraicSpace_source ≤
      dimension B S hS s.target s.isAlgebraicSpace_target + (r : WithBot ℕ∞) := by
  have hdeg : residueFieldTranscendenceDegreeAt B S hS s.hom s.sourcePoint = r :=
    (residueFieldTranscendenceDegreeAt_eq_iff B S hS s.hom s.isAlgebraicSpace_source
      s.isAlgebraicSpace_target s.sourcePoint r).2 hr
  -- Every codimension-zero point of `|X|` is the chosen generic point, so the correction term
  -- of Stacks 0BAX is the transcendence degree at that point.
  have hgeneric (z : points B S hS s.source) :
      genericResidueFieldTranscendenceDegreeAt B S hS s.hom z ≤ r := by
    refine iSup_le fun ξ ↦ ?_
    rw [← eq_of_specializes_of_localRingDimension_eq_zero B S hS s.isAlgebraicSpace_source
      s.isIntegralSpace_source.isDecentSpace ξ.2.2 s.sourcePoint
      (s.isGenericPoint_sourcePoint.specializes (Set.mem_univ ξ.1))]
    exact hdeg.le
  rw [dimension_eq_iSup_localRingDimension B S hS s.source s.isAlgebraicSpace_source]
  refine iSup_le fun z ↦ ?_
  have hYdim : (localRingDimension B S hS (pointsMap B S hS s.source s.hom z) : WithBot ℕ∞) ≤
      dimension B S hS s.target s.isAlgebraicSpace_target := by
    rw [dimension_eq_iSup_localRingDimension B S hS s.target s.isAlgebraicSpace_target]
    exact le_iSup_of_le (pointsMap B S hS s.source s.hom z) le_rfl
  calc (localRingDimension B S hS z : WithBot ℕ∞)
      ≤ (localRingDimension B S hS z : WithBot ℕ∞) +
          (residueFieldTranscendenceDegreeAt B S hS s.hom z : WithBot ℕ∞) :=
        le_add_of_nonneg_right (by simp)
    _ ≤ (localRingDimension B S hS (pointsMap B S hS s.source s.hom z) : WithBot ℕ∞) +
          (genericResidueFieldTranscendenceDegreeAt B S hS s.hom z : WithBot ℕ∞) :=
        localRingDimension_add_residueFieldTranscendenceDegree_le B S hS s.hom
          s.isAlgebraicSpace_source s.isAlgebraicSpace_target s.locallyNoetherian_target
          s.isLocallyOfFiniteType z
    _ ≤ dimension B S hS s.target s.isAlgebraicSpace_target + (r : WithBot ℕ∞) :=
        add_le_add hYdim (WithBot.coe_le_coe.mpr (hgeneric z))

/-! ### Chains of specializations and the Krull dimension -/

section Chains

open TopologicalSpace

/-- A chain `z 0, …, z n` of nontrivial specializations in a Kolmogorov space — each `z (i + 1)`
a generization of `z i`, distinct from it — witnesses that the Krull dimension of the space is
at least `n`: the closures of the `z i` form a strictly increasing chain of irreducible closed
subsets. -/
private theorem natCast_le_topologicalKrullDim_of_chain {α : Type*} [TopologicalSpace α]
    [T0Space α] (n : ℕ) (z : ℕ → α) (hstep : ∀ i < n, z (i + 1) ⤳ z i)
    (hne : ∀ i < n, z (i + 1) ≠ z i) :
    (n : WithBot ℕ∞) ≤ topologicalKrullDim α := by
  have hlt : ∀ i < n,
      (⟨closure {z i}, isIrreducible_singleton.closure, isClosed_closure⟩ :
          IrreducibleCloseds α) <
        ⟨closure {z (i + 1)}, isIrreducible_singleton.closure, isClosed_closure⟩ := by
    intro i hi
    have hs : z (i + 1) ⤳ z i := hstep i hi
    refine lt_of_le_of_ne
      (SetLike.coe_subset_coe.mp (specializes_iff_closure_subset.mp hs)) fun heq => ?_
    have heq' : closure ({z i} : Set α) = closure {z (i + 1)} :=
      congrArg (fun t : IrreducibleCloseds α => (t : Set α)) heq
    exact hne i hi (hs.antisymm (specializes_iff_closure_subset.mpr heq'.symm.subset)).eq
  rw [topologicalKrullDim]
  exact Order.le_krullDim_iff.mpr ⟨LTSeries.mk n
    (fun i => ⟨closure {z (i : ℕ)}, isIrreducible_singleton.closure, isClosed_closure⟩)
    (Fin.strictMono_iff_lt_succ.mpr fun i => by simpa using hlt i.1 i.2), by simp⟩

/-- Conversely, a sober space whose Krull dimension is at least `n` carries a chain of `n`
nontrivial specializations: take the generic points of a chain of irreducible closed
subsets. -/
private theorem exists_specializes_chain_of_natCast_le_topologicalKrullDim (α : Type*)
    [TopologicalSpace α] [QuasiSober α] (n : ℕ)
    (hn : (n : WithBot ℕ∞) ≤ topologicalKrullDim α) :
    ∃ z : ℕ → α, (∀ i < n, z (i + 1) ⤳ z i) ∧ (∀ i < n, z (i + 1) ≠ z i) := by
  rw [topologicalKrullDim] at hn
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.mp hn
  classical
  set D : ℕ → IrreducibleCloseds α := fun i => l.toFun ⟨min i l.length, by omega⟩
  have hDlt : ∀ i < n, D i < D (i + 1) := by
    intro i hi
    refine l.strictMono ?_
    simp only [Fin.mk_lt_mk]
    omega
  have hclos : ∀ i, closure ({(D i).isIrreducible.genericPoint} : Set α) = (D i : Set α) :=
    fun i => (D i).isIrreducible.closure_genericPoint (D i).isClosed
  refine ⟨fun i => (D i).isIrreducible.genericPoint, ?_, ?_⟩
  · intro i hi
    refine specializes_iff_closure_subset.mpr ?_
    rw [hclos i, hclos (i + 1)]
    exact SetLike.coe_subset_coe.mpr (hDlt i hi).le
  · intro i hi heq
    refine (hDlt i hi).ne (IrreducibleCloseds.ext ?_)
    rw [← hclos i, ← hclos (i + 1), show (D (i + 1)).isIrreducible.genericPoint
      = (D i).isIrreducible.genericPoint from heq]

/-- Appending a last element to a chain preserves a relation between consecutive members. -/
private theorem forall_lt_update_succ {α : Type*} (P : α → α → Prop) {m : ℕ} {z : ℕ → α} (a : α)
    (hz : ∀ i < m, P (z (i + 1)) (z i)) (ha : P a (z m)) :
    ∀ i < m + 1, P (Function.update z (m + 1) a (i + 1)) (Function.update z (m + 1) a i) := by
  intro i hi
  by_cases hc : i + 1 ≤ m
  · rw [Function.update_of_ne (show i + 1 ≠ m + 1 by omega),
      Function.update_of_ne (show i ≠ m + 1 by omega)]
    exact hz i (by omega)
  · obtain rfl : i = m := by omega
    rwa [Function.update_self, Function.update_of_ne (show i ≠ i + 1 by omega)]

/-- Appending a last element to a chain preserves a property of the members at their positions. -/
private theorem forall_le_update_succ {α : Type*} (Q : ℕ → α → Prop) {m : ℕ} {z : ℕ → α} (a : α)
    (hz : ∀ i ≤ m, Q i (z i)) (ha : Q (m + 1) a) :
    ∀ i ≤ m + 1, Q i (Function.update z (m + 1) a i) := by
  intro i hi
  by_cases hc : i ≤ m
  · rw [Function.update_of_ne (show i ≠ m + 1 by omega)]
    exact hz i hc
  · obtain rfl : i = m + 1 := by omega
    rwa [Function.update_self]

/-- A chain of specializations lifts along a closed continuous map from a prescribed point above
its most generic member: this is Stacks 0066 (1), applied `n` times. -/
private theorem exists_lift_specializes_chain_of_isClosedMap {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {g : α → β} (hg : IsClosedMap g) (n : ℕ) (c : ℕ → β)
    (hstep : ∀ i < n, c (i + 1) ⤳ c i) (a : α) (ha : g a = c n) :
    ∃ z : ℕ → α, z n = a ∧ (∀ i ≤ n, g (z i) = c i) ∧ (∀ i < n, z (i + 1) ⤳ z i) := by
  induction n generalizing a with
  | zero =>
    refine ⟨fun _ => a, rfl, ?_, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
    intro i hi
    obtain rfl : i = 0 := Nat.le_zero.mp hi
    exact ha
  | succ m ih =>
    have hmem : c m ∈ closure ({g a} : Set β) := by
      rw [ha]
      exact (hstep m (by omega)).mem_closure
    obtain ⟨a', ha'mem, ha'⟩ := hg.specializingMap.closure_singleton_subset a hmem
    obtain ⟨z, hzm, hzmap, hzstep⟩ := ih (fun i hi => hstep i (by omega)) a' ha'
    exact ⟨Function.update z (m + 1) a, Function.update_self _ _ _,
      forall_le_update_succ (fun i x => g x = c i) a hzmap ha,
      forall_lt_update_succ (· ⤳ ·) a hzstep (hzm ▸ specializes_iff_mem_closure.mpr ha'mem)⟩

end Chains

/-! ### Extended natural number arithmetic -/

section Arithmetic

/-- An extended natural number bounded below by every natural number is `⊤`. -/
private theorem enat_eq_top_of_forall {D : ℕ∞} (h : ∀ n : ℕ, (n : ℕ∞) ≤ D) : D = ⊤ := by
  rcases eq_or_ne D ⊤ with hD | hD
  · exact hD
  · obtain ⟨j, rfl⟩ := ENat.ne_top_iff_exists.mp hD
    exact absurd (h (j + 1)) (by exact_mod_cast Nat.not_succ_le_self j)

/-- A sum of two extended natural numbers is bounded by `D` as soon as every sum of natural
numbers below the two summands is. -/
private theorem enat_add_le_of_forall_nat {A r D : ℕ∞}
    (key : ∀ d e : ℕ, (d : ℕ∞) ≤ A → (e : ℕ∞) ≤ r → ((d + e : ℕ) : ℕ∞) ≤ D) :
    A + r ≤ D := by
  rcases eq_or_ne A ⊤ with rfl | hA
  · have hD : D = ⊤ := enat_eq_top_of_forall fun n => by
      simpa using key n 0 le_top (by simp)
    simp [hD]
  obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp hA
  rcases eq_or_ne r ⊤ with rfl | hr
  · have hD : D = ⊤ := enat_eq_top_of_forall fun n => by
      refine le_trans ?_ (key m n le_rfl le_top)
      exact_mod_cast Nat.le_add_left n m
    simp [hD]
  obtain ⟨k, rfl⟩ := ENat.ne_top_iff_exists.mp hr
  exact_mod_cast key m k le_rfl le_rfl

/-- For `DY = A` and `DX = Dx` in `WithBot ℕ∞`, the sum `DY + r` is bounded by `DX` as soon as
every sum of natural numbers below `A` and `r` is bounded by `Dx`. -/
private theorem withBot_add_le_of_forall_nat {DY DX : WithBot ℕ∞} {r A Dx : ℕ∞}
    (hA : DY = (A : WithBot ℕ∞)) (hDx : DX = (Dx : WithBot ℕ∞))
    (key : ∀ d e : ℕ, (d : ℕ∞) ≤ A → (e : ℕ∞) ≤ r → ((d + e : ℕ) : ℕ∞) ≤ Dx) :
    DY + (r : WithBot ℕ∞) ≤ DX := by
  subst hA hDx
  rw [← WithBot.coe_add, WithBot.coe_le_coe]
  exact enat_add_le_of_forall_nat key

end Arithmetic

/-! ### Lifting a chain of specializations to an étale chart -/

/-- A chain of specializations of a decent algebraic space lifts to any étale scheme chart,
from a prescribed point above its most special member: this is Stacks 03IL, applied `n`
times. -/
private theorem exists_chart_specializes_chain {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hdec : IsDecentSpace B S hS X) (U : BigFppfOver B S hS)
    (φ : yoneda.obj U ⟶ X)
    (hφ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ)
    (n : ℕ) (z : ℕ → points B S hS X) (u : points B S hS (yoneda.obj U))
    (hu : pointsMap B S hS (yoneda.obj U) φ u = z 0) (hstep : ∀ i < n, z (i + 1) ⤳ z i) :
    ∃ w : ℕ → points B S hS (yoneda.obj U),
      (∀ i ≤ n, pointsMap B S hS (yoneda.obj U) φ (w i) = z i) ∧
      (∀ i < n, w (i + 1) ⤳ w i) := by
  induction n with
  | zero =>
    refine ⟨fun _ => u, ?_, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
    intro i hi
    obtain rfl : i = 0 := Nat.le_zero.mp hi
    exact hu
  | succ m ih =>
    obtain ⟨w, hwmap, hwstep⟩ := ih fun i hi => hstep i (by omega)
    obtain ⟨w', hw'spec, hw'map⟩ := exists_specialization_lift_of_isDecentSpace B S hS _ hX
      hdec _ _ (hstep m (by omega)) U φ hφ (w m) (hwmap m le_rfl)
    exact ⟨Function.update w (m + 1) w',
      forall_le_update_succ (fun i x => pointsMap B S hS (yoneda.obj U) φ x = z i) w' hwmap
        hw'map,
      forall_lt_update_succ (· ⤳ ·) w' hwstep hw'spec⟩

/-- An étale surjective scheme chart of an algebraic space is surjective on points, and the
dimension of the space is the Krull dimension of the chart. -/
private theorem surjective_pointsMap_and_dimension_eq {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X)
    (hSurj : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf a)
    (hEt : (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf a) :
    Function.Surjective (pointsMap B S hS (yoneda.obj U) a) ∧
      dimension B S hS X hX = topologicalKrullDim ((BigFppfOver.toScheme B S hS).obj U) := by
  have hpts := (presheafSurjective_iff_isSurjective_yoneda B S hS X hX U a).mp hSurj
  refine ⟨hpts, ?_⟩
  rw [← dimension_eq_of_isEtale_of_isSurjective B S hS (isAlgebraicSpace_yoneda B S hS U) hX a
    ((isEtale_iff_presheaf_of_yoneda B S hS a).mpr hEt) hpts]
  exact dimension_yoneda_eq_topologicalKrullDim B S hS U

/-! ### The dimension of a represented algebraic space -/

/-! ### The equality for a proper morphism -/

open TopologicalSpace in
/-- **Stacks 0EDC, equality for a proper morphism.** Let `f : X ⟶ Y` be a dominant morphism
locally of finite type of integral algebraic spaces over `S` with `Y` locally Noetherian, and
let `x` and `y` be generic points of `|X|` and `|Y|`. If `f` is proper and the transcendence
degree of `f` at `x` is `r`, then `dim X = dim Y + r`.

The inequality `≤` is `AlgebraicGeometry.Space.dimension_le_dimension_add_transcendenceDegree`.
For the reverse inequality both dimensions are read on one commuting pair of surjective étale
scheme charts `U → X` and `V → Y` (Stacks 0A4H and Stacks 02X1), so that each becomes a
topological Krull dimension and a bound on it is a chain of specializations. A chain of length
`d` in `V` gives one of length at least `d` in `|Y|` ending at `y`, since two points of an
étale chart with the same image, one a specialization of the other, are equal (Stacks 03K5);
properness makes `|f|` closed, so that chain lifts to `|X|` from any point above `y` (Stacks
0066). Below such a point
there are `r` further nontrivial specializations: the fibre of `U → V` through the chart point
above `x` has dimension at least the transcendence degree there by the dimension formula of
Stacks 02FX, and the resulting chain lies over `y`. The concatenation is a chain of length
`d + r` in `|X|`, and it lifts to the chart `U` by Stacks 03IL. -/
@[stacks 0EDC "equality for a proper morphism"]
theorem dimension_eq_dimension_add_transcendenceDegree
    (s : IntegralDominantMorphismSituation B S hS) (hproper : IsProper B S hS s.hom) (r : ℕ∞)
    (hr : HasTranscendenceDegreeAt B S hS s.hom s.sourcePoint r) :
    dimension B S hS s.source s.isAlgebraicSpace_source =
      dimension B S hS s.target s.isAlgebraicSpace_target + (r : WithBot ℕ∞) := by
  refine le_antisymm (dimension_le_dimension_add_transcendenceDegree B S hS s r hr) ?_
  have hdecX : IsDecentSpace B S hS s.source := s.isIntegralSpace_source.isDecentSpace
  have hdecY : IsDecentSpace B S hS s.target := s.isIntegralSpace_target.isDecentSpace
  have : T0Space (points B S hS s.target) :=
    t0Space_points_of_isDecentSpace B S hS s.isAlgebraicSpace_target hdecY
  -- the generic point of the source lies over the generic point of the target
  have hfy : pointsMap B S hS s.source s.hom s.sourcePoint = s.targetPoint := by
    have hsub : Set.range (pointsMap B S hS s.source s.hom) ⊆
        closure {pointsMap B S hS s.source s.hom s.sourcePoint} := by
      rintro _ ⟨ξ, rfl⟩
      exact ((s.isGenericPoint_sourcePoint.specializes (Set.mem_univ ξ)).map
        (continuous_pointsMap B S hS s.hom)).mem_closure
    have hgen : IsGenericPoint (pointsMap B S hS s.source s.hom s.sourcePoint) Set.univ := by
      refine Set.eq_univ_of_univ_subset ?_
      rw [← s.isDominant.closure_eq]
      exact closure_minimal hsub isClosed_closure
    exact hgen.eq s.isGenericPoint_targetPoint
  -- properness makes the map on points closed
  have hclosedf : IsClosedMap (pointsMap B S hS s.source s.hom) :=
    isClosed_of_universallyClosed B S hS s.isAlgebraicSpace_target s.hom hproper.2.2
  -- a commuting pair of surjective étale scheme charts
  obtain ⟨V, b, hbSurj, hbEt⟩ := s.isAlgebraicSpace_target.exists_atlas
  obtain ⟨U, a, h, hcomm, haSurj, haEt⟩ := exists_surjective_etale_presentation_lift B S hS
    s.isAlgebraicSpace_source s.isAlgebraicSpace_target s.hom V b hbSurj hbEt
  obtain ⟨haSurjPts, hdimX⟩ := surjective_pointsMap_and_dimension_eq B S hS
    s.isAlgebraicSpace_source U a haSurj haEt
  obtain ⟨-, hdimY⟩ := surjective_pointsMap_and_dimension_eq B S hS
    s.isAlgebraicSpace_target V b hbSurj hbEt
  -- the chart, pointed at the generic point of the source
  obtain ⟨q₀, hq₀⟩ := haSurjPts s.sourcePoint
  obtain ⟨p₀, rfl⟩ := Quot.exists_rep q₀
  let c : EtaleChartAtPoint B S hS s.hom s.sourcePoint :=
    { U := U
      V := V
      a := a
      b := b
      h := h
      a_etale := haEt
      b_etale := hbEt
      comm := hcomm.symm
      representative := p₀
      point := IsLocalRing.closedPoint p₀.carrier
      maps_to := hq₀ }
  have hLft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map h) :=
    s.isLocallyOfFiniteType U V a b h haEt hbEt hcomm.symm
  have hrdeg : residueFieldTranscendenceDegree ((BigFppfOver.toScheme B S hS).map h)
      (c.sourcePoint B S hS) = r :=
    (MorphismOfGerms.hasResidueFieldTranscendenceDegree_ofSchemeHom_iff _ _ r).1 (hr c)
  -- the fibre of the chart morphism through that point has dimension at least `r`
  have hfibre : (r : WithBot ℕ∞) ≤ topologicalKrullDim
      (((BigFppfOver.toScheme B S hS).map h).fiber
        (((BigFppfOver.toScheme B S hS).map h) (c.sourcePoint B S hS))) := by
    refine le_trans ?_ (topologicalKrullDimAt_le_topologicalKrullDim
      (((BigFppfOver.toScheme B S hS).map h).asFiber (c.sourcePoint B S hS)))
    rw [topologicalKrullDimAt_fiber_eq_krullDimOfRing_stalk_add_trdeg, ← hrdeg]
    exact le_add_of_nonneg_left ringKrullDim_nonneg_of_nontrivial
  -- the chart point selected at `x`, read as a point of the represented presheaf
  have hsrc : c.sourcePoint B S hS =
      pointsToScheme B S hS U (p₀.class B S hS (yoneda.obj U)) := rfl
  have hsymm : ∀ t : (BigFppfOver.toScheme B S hS).obj U,
      pointsToScheme B S hS U ((schemePointsHomeomorph B S hS U).symm t) = t := fun t => by
    rw [← schemePointsHomeomorph_apply]
    exact (schemePointsHomeomorph B S hS U).apply_symm_apply t
  -- a point of the chart lying over the chart image of `x` lies over the generic point of `|Y|`
  have hfactor : ∀ w : points B S hS (yoneda.obj U),
      pointsMap B S hS s.source s.hom (pointsMap B S hS (yoneda.obj U) a w) =
        pointsMap B S hS (yoneda.obj V) b
          (pointsMap B S hS (yoneda.obj U) (yoneda.map h) w) := by
    intro w
    rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, hcomm]
  have hconst : ∀ w : points B S hS (yoneda.obj U),
      (BigFppfOver.toScheme B S hS).map h (pointsToScheme B S hS U w) =
        (BigFppfOver.toScheme B S hS).map h (c.sourcePoint B S hS) →
      pointsMap B S hS s.source s.hom (pointsMap B S hS (yoneda.obj U) a w) =
        s.targetPoint := by
    intro w hw
    have hident : pointsMap B S hS (yoneda.obj U) (yoneda.map h) w =
        pointsMap B S hS (yoneda.obj U) (yoneda.map h) (p₀.class B S hS (yoneda.obj U)) := by
      refine (schemePointsHomeomorph B S hS V).injective ?_
      rw [schemePointsHomeomorph_apply, schemePointsHomeomorph_apply,
        pointsToScheme_pointsMap, pointsToScheme_pointsMap, ← hsrc]
      exact hw
    rw [hfactor w, hident, ← hfactor, hq₀, hfy]
  -- the `r` nontrivial specializations above the generic point of the target
  have hEchain : ∀ e : ℕ, (e : ℕ∞) ≤ r →
      ∃ E : ℕ → points B S hS s.source,
        (∀ i, pointsMap B S hS s.source s.hom (E i) = s.targetPoint) ∧
        (∀ i < e, E (i + 1) ⤳ E i) ∧ (∀ i < e, E (i + 1) ≠ E i) := by
    intro e he
    have _ : QuasiSober (((BigFppfOver.toScheme B S hS).map h).fiber
        (((BigFppfOver.toScheme B S hS).map h) (c.sourcePoint B S hS))) :=
      inferInstanceAs (QuasiSober ((((BigFppfOver.toScheme B S hS).map h).fiber
        (((BigFppfOver.toScheme B S hS).map h) (c.sourcePoint B S hS)) : Scheme.{u})))
    obtain ⟨ζ, hζstep, hζne⟩ := exists_specializes_chain_of_natCast_le_topologicalKrullDim
      _ e (le_trans (by exact_mod_cast he) hfibre)
    set ι := ((BigFppfOver.toScheme B S hS).map h).fiberι
      (((BigFppfOver.toScheme B S hS).map h) (c.sourcePoint B S hS)) with hι
    have hover : ∀ i, (BigFppfOver.toScheme B S hS).map h (ι (ζ i)) =
        (BigFppfOver.toScheme B S hS).map h (c.sourcePoint B S hS) := by
      intro i
      have hr' := ((BigFppfOver.toScheme B S hS).map h).range_fiberι
        (((BigFppfOver.toScheme B S hS).map h) (c.sourcePoint B S hS))
      have hmem : ι (ζ i) ∈ (BigFppfOver.toScheme B S hS).map h ⁻¹'
          {(BigFppfOver.toScheme B S hS).map h (c.sourcePoint B S hS)} :=
        hr' ▸ Set.mem_range_self (ζ i)
      simpa using hmem
    have hstepw : ∀ i < e, (schemePointsHomeomorph B S hS U).symm (ι (ζ (i + 1))) ⤳
        (schemePointsHomeomorph B S hS U).symm (ι (ζ i)) := fun i hi =>
      ((hζstep i hi).map ι.isEmbedding.continuous).map
        (schemePointsHomeomorph B S hS U).symm.continuous
    refine ⟨fun i => pointsMap B S hS (yoneda.obj U) a
      ((schemePointsHomeomorph B S hS U).symm (ι (ζ i))), fun i => hconst _ ?_, ?_, ?_⟩
    · rw [hsymm, hover i]
    · exact fun i hi => (hstepw i hi).map (continuous_pointsMap B S hS a)
    · intro i hi hEq
      have heq := eq_of_specializes_of_pointsMap_eq_of_hasFiniteChartFibers B S hS
        s.isAlgebraicSpace_source
        (hasFiniteChartFibersAtEveryPoint_of_isDecentSpace B S hS hdecX) U a haEt
        ((schemePointsHomeomorph B S hS U).symm (ι (ζ i)))
        ((schemePointsHomeomorph B S hS U).symm (ι (ζ (i + 1)))) hEq.symm (hstepw i hi)
      exact hζne i hi
        (ι.isEmbedding.injective ((schemePointsHomeomorph B S hS U).symm.injective heq)).symm
  -- a chain in `|Y|` of length at least `d` whose most generic member is the generic point
  have hYchain : ∀ d : ℕ, (d : WithBot ℕ∞) ≤
      topologicalKrullDim ((BigFppfOver.toScheme B S hS).obj V) →
      ∃ (m : ℕ) (C : ℕ → points B S hS s.target), d ≤ m ∧ C m = s.targetPoint ∧
        (∀ i < m, C (i + 1) ⤳ C i) ∧ (∀ i < m, C (i + 1) ≠ C i) := by
    intro d hd
    obtain ⟨v, hvstep, hvne⟩ :=
      exists_specializes_chain_of_natCast_le_topologicalKrullDim _ d hd
    have hstepw : ∀ i < d, (schemePointsHomeomorph B S hS V).symm (v (i + 1)) ⤳
        (schemePointsHomeomorph B S hS V).symm (v i) := fun i hi =>
      (hvstep i hi).map (schemePointsHomeomorph B S hS V).symm.continuous
    set C₀ : ℕ → points B S hS s.target := fun i =>
      pointsMap B S hS (yoneda.obj V) b ((schemePointsHomeomorph B S hS V).symm (v i)) with hC₀
    have hC₀step : ∀ i < d, C₀ (i + 1) ⤳ C₀ i := fun i hi =>
      (hstepw i hi).map (continuous_pointsMap B S hS b)
    have hC₀ne : ∀ i < d, C₀ (i + 1) ≠ C₀ i := by
      intro i hi hEq
      have heq := eq_of_specializes_of_pointsMap_eq_of_hasFiniteChartFibers B S hS
        s.isAlgebraicSpace_target
        (hasFiniteChartFibersAtEveryPoint_of_isDecentSpace B S hS hdecY) V b hbEt
        ((schemePointsHomeomorph B S hS V).symm (v i))
        ((schemePointsHomeomorph B S hS V).symm (v (i + 1))) hEq.symm (hstepw i hi)
      exact hvne i hi ((schemePointsHomeomorph B S hS V).symm.injective heq).symm
    by_cases hdtop : C₀ d = s.targetPoint
    · exact ⟨d, C₀, le_rfl, hdtop, hC₀step, hC₀ne⟩
    exact ⟨d + 1, Function.update C₀ (d + 1) s.targetPoint, by omega,
      Function.update_self _ _ _,
      forall_lt_update_succ (· ⤳ ·) _ hC₀step
        (s.isGenericPoint_targetPoint.specializes (Set.mem_univ _)),
      forall_lt_update_succ (· ≠ ·) _ hC₀ne fun hEq => hdtop hEq.symm⟩
  -- the numerical inequality, read on the two charts
  have key : ∀ d e : ℕ, (d : WithBot ℕ∞) ≤
      topologicalKrullDim ((BigFppfOver.toScheme B S hS).obj V) → (e : ℕ∞) ≤ r →
      ((d + e : ℕ) : WithBot ℕ∞) ≤
        topologicalKrullDim ((BigFppfOver.toScheme B S hS).obj U) := by
    intro d e hd he
    obtain ⟨m, C, hdm, hCm, hCstep, hCne⟩ := hYchain d hd
    obtain ⟨E, hEmap, hEstep, hEne⟩ := hEchain e he
    obtain ⟨L, hLm, hLmap, hLstep⟩ := exists_lift_specializes_chain_of_isClosedMap
      hclosedf m C hCstep (E 0) (by rw [hEmap 0, hCm])
    have hLne : ∀ j < m, L (j + 1) ≠ L j := by
      intro j hj hEq
      exact hCne j hj (by rw [← hLmap (j + 1) (by omega), ← hLmap j (by omega), hEq])
    set Z : ℕ → points B S hS s.source := fun i => if i ≤ m then L i else E (i - m) with hZ
    have hZle : ∀ i, i ≤ m → Z i = L i := by
      intro i hi; simp only [hZ, hi, ite_true]
    have hZgt : ∀ i, ¬ i ≤ m → Z i = E (i - m) := by
      intro i hi; simp only [hZ, hi, ite_false]
    have hZcat : ∀ P : points B S hS s.source → points B S hS s.source → Prop,
        (∀ j < m, P (L (j + 1)) (L j)) → (∀ i < e, P (E (i + 1)) (E i)) →
        ∀ i < m + e, P (Z (i + 1)) (Z i) := by
      intro P hL hE i hi
      by_cases hc : i + 1 ≤ m
      · rw [hZle _ hc, hZle i (by omega)]
        exact hL i (by omega)
      rw [hZgt _ hc]
      by_cases hc' : i ≤ m
      · obtain rfl : i = m := by omega
        rw [hZle i le_rfl, hLm, show i + 1 - i = 1 from by omega]
        simpa using hE 0 (by omega)
      · rw [hZgt i hc', show i + 1 - m = (i - m) + 1 from by omega]
        exact hE (i - m) (by omega)
    have hZstep := hZcat (· ⤳ ·) hLstep hEstep
    have hZne := hZcat (· ≠ ·) hLne hEne
    -- lift the whole chain to the chart `U`
    obtain ⟨w₀, hw₀⟩ := haSurjPts (Z 0)
    obtain ⟨W, hWmap, hWstep⟩ := exists_chart_specializes_chain B S hS
      s.isAlgebraicSpace_source hdecX U a haEt (m + e) Z w₀ hw₀ hZstep
    refine le_trans ?_ (natCast_le_topologicalKrullDim_of_chain (m + e)
      (fun i => pointsToScheme B S hS U (W i)) ?_ ?_)
    · exact_mod_cast Nat.add_le_add_right hdm e
    · exact fun i hi => (hWstep i hi).map (schemePointsHomeomorph B S hS U).continuous
    · intro i hi hEq
      have hWeq : W (i + 1) = W i := (schemePointsHomeomorph B S hS U).injective hEq
      exact hZne i hi (by rw [← hWmap (i + 1) (by omega), ← hWmap i (by omega), hWeq])
  -- both charts are nonempty, so neither dimension is `-∞`
  have hUne : topologicalKrullDim ((BigFppfOver.toScheme B S hS).obj U) ≠ ⊥ := fun hb =>
    ((topologicalKrullDim_eq_bot_iff_isEmpty _).mp hb).false (c.sourcePoint B S hS)
  have hVne : topologicalKrullDim ((BigFppfOver.toScheme B S hS).obj V) ≠ ⊥ := fun hb =>
    ((topologicalKrullDim_eq_bot_iff_isEmpty _).mp hb).false
      ((BigFppfOver.toScheme B S hS).map h (c.sourcePoint B S hS))
  obtain ⟨Dx, hDx⟩ := WithBot.ne_bot_iff_exists.mp hUne
  obtain ⟨A, hA⟩ := WithBot.ne_bot_iff_exists.mp hVne
  rw [hdimX, hdimY]
  refine withBot_add_le_of_forall_nat hA.symm hDx.symm fun d e hd he => ?_
  have hkey := key d e (by rw [← hA]; exact_mod_cast hd) he
  rw [← hDx] at hkey
  exact_mod_cast hkey

end AlgebraicGeometry.Space

end
