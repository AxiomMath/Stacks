module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Topology.JacobsonSpace
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.JacobsonPuncturedSpectrum.Basic
public import StacksFrontier.Topology.Dimension.CatenaryAdditive
public import StacksFrontier.Topology.Dimension.CodimensionOpen
public import StacksFrontier.Topology.Dimension.Krull
public import StacksFrontier.Topology.Dimension.LocalKrullDim

/-!
# Constancy of dimension

On an irreducible, Jacobson, catenary, locally Noetherian scheme of finite dimension, every
nonempty open subset has the same dimension as the scheme; equivalently, the local dimension is
constant.

## Main results

* `AlgebraicGeometry.topologicalKrullDim_isOpen_eq_of_catenary`: a nonempty open subset has the
  dimension of the ambient scheme, with no finiteness of that dimension assumed.
* `AlgebraicGeometry.topologicalKrullDim_eq_of_isOpen_of_catenary`: a nonempty open subset has the
  dimension of the ambient scheme.
* `AlgebraicGeometry.isConstant_topologicalKrullDimAt`: the local dimension is constant.

## Implementation notes

Finite dimension is recorded by a natural number `d` together with `topologicalKrullDim X = d`.
Open subsets carry their subspace topology, and local dimension is `topologicalKrullDimAt`.

Finiteness of the dimension is not needed for the equality of dimensions, and
`AlgebraicGeometry.topologicalKrullDim_isOpen_eq_of_catenary` does without it; the two statements
carrying the hypothesis keep it in the form the source gives them.

## References

* [Stacks Project, Tag 0DRT](https://stacks.math.columbia.edu/tag/0DRT)
-/

@[expose] public section

open TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- On an irreducible locally Noetherian scheme, a point outside a nonempty open subset admits an
immediate specialization to it: a point of the open subset specializing to the given point with no
intermediate specialization. -/
@[ega "IV 10.7.3" "partial"]
private lemma exists_immediate_specialization_in_open
    (X : Scheme.{u}) [IrreducibleSpace X] [QuasiSober X] [T0Space X]
    [IsLocallyNoetherian X] (x : X) (U : Set X) (hU : IsOpen U)
    (hne : U.Nonempty) (hxU : x ∉ U) :
    ∃ y : X, y ∈ U ∧
      y ⤳ x ∧ y ≠ x ∧ ∀ z : X, y ⤳ z → z ⤳ x → z = y ∨ z = x := by
  let R := X.presheaf.stalk x
  let f := X.fromSpecStalk x
  let m : PrimeSpectrum R := IsLocalRing.closedPoint R
  let S : Set (PrimeSpectrum R) := ({m} : Set (PrimeSpectrum R))ᶜ
  have : IsNoetherianRing R := inferInstance
  have : JacobsonSpace ↥S :=
    PrimeSpectrum.jacobsonSpace_compl_closedPoint R
  have hm : f m = x := Scheme.fromSpecStalk_closedPoint
  let η : X := genericPoint (↥X)
  obtain ⟨x₀, hx₀U⟩ := hne
  have hηU : η ∈ U := (genericPoint_specializes x₀).mem_open hU hx₀U
  have hηx : η ⤳ x := genericPoint_specializes x
  obtain ⟨t, ht⟩ : η ∈ Set.range f := by rwa [Scheme.range_fromSpecStalk]
  have htm : t ≠ m := fun e => hxU (ht.symm.trans ((congrArg f e).trans hm) ▸ hηU)
  let V : Set S := Subtype.val ⁻¹' (f ⁻¹' U)
  have hVopen : IsOpen V := (hU.preimage f.continuous).preimage continuous_subtype_val
  have hVne : V.Nonempty := ⟨⟨t, htm⟩, show f t ∈ U from ht ▸ hηU⟩
  obtain ⟨z, hzV, hzclosed⟩ :=
    nonempty_inter_closedPoints (X := ↥S) hVne hVopen.isLocallyClosed
  let z₀ : PrimeSpectrum R := z.1
  have hzS : z₀ ∈ S := z.2
  have hzclosed' : IsClosed ({z} : Set S) := hzclosed
  have hzU : f z₀ ∈ U := hzV
  have hno_intermediate : ∀ w : PrimeSpectrum R, z₀ ⤳ w → w ≠ m → w = z₀ := by
    intro w hzw hwm
    have hwS : w ∈ S := hwm
    let w' : S := ⟨w, hwS⟩
    have hzw' : (⟨z₀, hzS⟩ : S) ⤳ w' := (subtype_specializes_iff _ _).2 hzw
    have hwcl : w' ∈ closure ({(⟨z₀, hzS⟩ : S)} : Set S) := hzw'.mem_closure
    rw [closure_eq_iff_isClosed.mpr hzclosed'] at hwcl
    have heq : w' = (⟨z₀, hzS⟩ : S) := by simpa using hwcl
    exact congrArg Subtype.val heq
  have hrel : f z₀ ⤳ x := by
    have hz_m : z₀ ⤳ m := IsLocalRing.specializes_closedPoint z₀
    simpa only [hm] using hz_m.map f.continuous
  have hne' : f z₀ ≠ x := fun e => hxU (e ▸ hzU)
  refine ⟨f z₀, hzU, hrel, hne', ?_⟩
  intro w hyw hwx
  obtain ⟨w₀, hw₀⟩ : w ∈ Set.range f := by rwa [Scheme.range_fromSpecStalk]
  have hzw₀ : z₀ ⤳ w₀ := by
    apply (f.isEmbedding.isInducing.specializes_iff).mp
    simpa [hw₀] using hyw
  by_cases hwm : w₀ = m
  · exact .inr (hw₀.symm.trans ((congrArg f hwm).trans hm))
  · exact .inl (hw₀.symm.trans (congrArg f (hno_intermediate w₀ hzw₀ hwm)))

/-- An immediate specialization `y ⤳ x` to a closed point `x` makes the closure of `y` cover the
singleton `{x}` in the poset of irreducible closed subsets. -/
private lemma closure_singleton_covBy_of_immediate {X : Type*} [TopologicalSpace X]
    [QuasiSober X] [T0Space X] {x y : X} (hxclosed : IsClosed ({x} : Set X))
    (h : y ⤳ x ∧ y ≠ x ∧ ∀ z : X, y ⤳ z → z ⤳ x → z = y ∨ z = x) :
    (⟨{x}, isIrreducible_singleton, hxclosed⟩ : IrreducibleCloseds X) ⋖
      (⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩ :
        IrreducibleCloseds X) := by
  let a : IrreducibleCloseds X := ⟨{x}, isIrreducible_singleton, hxclosed⟩
  let b : IrreducibleCloseds X := ⟨closure {y}, isIrreducible_singleton.closure,
    isClosed_closure⟩
  have hle : a ≤ b := Set.singleton_subset_iff.mpr h.1.mem_closure
  have hlt : a < b := by
    refine lt_of_le_of_ne hle ?_
    intro hab
    have hyb : y ∈ (b : Set X) := subset_closure (Set.mem_singleton y)
    have hy_a : y ∈ (a : Set X) := hab ▸ hyb
    exact h.2.1 (Set.mem_singleton_iff.mp hy_a)
  apply (covBy_iff_lt_and_eq_or_eq).2
  refine ⟨hlt, ?_⟩
  intro c hac hcb
  by_cases hca : c = a
  · exact Or.inl hca
  by_cases hcb' : c = b
  · exact Or.inr hcb'
  let η := c.isIrreducible.genericPoint
  have hηc : closure ({η} : Set X) = (c : Set X) :=
    c.isIrreducible.closure_genericPoint c.isClosed
  have hgen : IsGenericPoint η (c : Set X) :=
    c.isIrreducible.isGenericPoint_genericPoint c.isClosed
  have hyη : y ⤳ η := specializes_iff_mem_closure.mpr (hcb hgen.mem)
  have hηx : η ⤳ x := specializes_iff_mem_closure.mpr
    (hηc ▸ hac (show x ∈ (a : Set X) by simp [a]))
  rcases h.2.2 η hyη hηx with hηy | hηx'
  · exfalso
    apply hcb'
    apply IrreducibleCloseds.ext
    calc
      (c : Set X) = closure {η} := hηc.symm
      _ = closure {y} := by rw [hηy]
      _ = (b : Set X) := rfl
  · exfalso
    apply hca
    apply IrreducibleCloseds.ext
    calc
      (c : Set X) = closure {η} := hηc.symm
      _ = closure {x} := by rw [hηx']
      _ = {x} := hxclosed.closure_eq

/-- **A nonempty open subset of an irreducible, Jacobson, catenary, locally Noetherian scheme has
the dimension of the scheme.** No finiteness of that dimension is assumed. -/
@[ega "IV 10.6.3" "special case", ega "IV 5.2.5" "special case", sga "3 VIB 1.5" "more general"]
theorem topologicalKrullDim_isOpen_eq_of_catenary
    (X : Scheme.{u}) [IrreducibleSpace X] [JacobsonSpace X]
    (hcat : IrreducibleClosedsCodim.IsCatenarySpace X) [IsLocallyNoetherian X]
    (U : Set X) (hU : IsOpen U) (hne : U.Nonempty) :
    topologicalKrullDim U = topologicalKrullDim X := by
  refine le_antisymm (topologicalKrullDim_subspace_le X U) ?_
  rw [topologicalKrullDim, Order.krullDim]
  refine iSup_le fun p => ?_
  let top : IrreducibleCloseds X :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  obtain ⟨x, hxHead, hxClosedPts⟩ :=
    nonempty_inter_closedPoints (p.head.isIrreducible.nonempty)
      p.head.isClosed.isLocallyClosed
  have hxclosed : IsClosed ({x} : Set X) := mem_closedPoints_iff.mp hxClosedPts
  let a : IrreducibleCloseds X := ⟨{x}, isIrreducible_singleton, hxclosed⟩
  obtain ⟨q, hqhead, hqlast, hqlen⟩ : ∃ q : LTSeries (IrreducibleCloseds X),
      q.head = a ∧ q.last = top ∧ p.length ≤ q.length := by
    obtain ⟨p₁, hp₁head, hp₁last, hp₁len⟩ : ∃ p₁ : LTSeries (IrreducibleCloseds X),
        p₁.head = a ∧ p₁.last = p.last ∧ p.length ≤ p₁.length := by
      rcases eq_or_lt_of_le (show a ≤ p.head from Set.singleton_subset_iff.mpr hxHead) with h | h
      · exact ⟨p, h.symm, rfl, le_rfl⟩
      · exact ⟨p.cons a h, by simp, by simp, by simp⟩
    rcases eq_or_lt_of_le (show p₁.last ≤ top from Set.subset_univ _) with h | h
    · exact ⟨p₁, hp₁head, h, hp₁len⟩
    · refine ⟨p₁.snoc top h, by simpa using hp₁head, by simp, ?_⟩
      simp only [RelSeries.snoc_length]
      omega
  have hqcod : (q.length : ℕ∞) ≤ IrreducibleClosedsCodim.topCodim a top :=
    IrreducibleClosedsCodim.length_le_topCodim a top q hqhead hqlast
  by_cases hxU : x ∈ U
  · have h1 : (p.length : WithBot ℕ∞) ≤ (q.length : WithBot ℕ∞) := by exact_mod_cast hqlen
    exact h1.trans (length_le_topologicalKrullDim_of_mem q U hU x hxU (by rw [hqhead]; rfl))
  · obtain ⟨y, hyU, hyx⟩ := exists_immediate_specialization_in_open X x U hU hne hxU
    let b : IrreducibleCloseds X :=
      ⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩
    have hab : a ⋖ b := closure_singleton_covBy_of_immediate hxclosed hyx
    have hbt : b ≤ top := Set.subset_univ _
    have hadd := topCodim_additive_of_catenary hcat a b top (le_of_lt hab.1) hbt
    rw [topCodim_eq_one_of_covby a b hab] at hadd
    obtain ⟨r, hrmax, hrcod⟩ := exists_maximalChain_length_eq_topCodim b top hbt
      (topCodim_ne_top_of_catenary hcat b top hbt)
    obtain ⟨hrhead, -, -⟩ := hrmax
    obtain ⟨u, huW, huClosedPts⟩ :=
      nonempty_inter_closedPoints (X := X)
        (show ((b : Set X) ∩ U).Nonempty from
          ⟨y, subset_closure (Set.mem_singleton y), hyU⟩)
        (b.isClosed.isLocallyClosed.inter hU.isLocallyClosed)
    have huclosed : IsClosed ({u} : Set X) := mem_closedPoints_iff.mp huClosedPts
    have hux : u ≠ x := fun h => hxU (h ▸ huW.2)
    let c : IrreducibleCloseds X := ⟨{u}, isIrreducible_singleton, huclosed⟩
    have hcb : c < b := by
      refine lt_of_le_of_ne (Set.singleton_subset_iff.mpr huW.1) ?_
      intro heq
      have hxC : x ∈ (c : Set X) := heq.symm ▸ hyx.1.mem_closure
      exact hux (Set.mem_singleton_iff.mp hxC).symm
    let s := r.cons c (hrhead ▸ hcb)
    have hslen : (s.length : ℕ∞) = IrreducibleClosedsCodim.topCodim a top := by
      rw [hadd, ← hrcod]
      simp only [s, RelSeries.cons_length, Nat.cast_add, Nat.cast_one]
      exact add_comm _ _
    have hqs : q.length ≤ s.length := by exact_mod_cast hqcod.trans_eq hslen.symm
    have h1 : (p.length : WithBot ℕ∞) ≤ (s.length : WithBot ℕ∞) := by
      exact_mod_cast hqlen.trans hqs
    exact h1.trans (length_le_topologicalKrullDim_of_mem s U hU u huW.2 (by simp [s, c]))

/-- A nonempty open subset of an irreducible, Jacobson, catenary, locally Noetherian scheme of
finite dimension has the same dimension as the scheme. -/
@[stacks 0DRT "dimension of nonempty opens", sga "3 VIB 1.5" "more general"]
theorem topologicalKrullDim_eq_of_isOpen_of_catenary
    (X : Scheme.{u}) [IrreducibleSpace X] [JacobsonSpace X]
    (hcat : IrreducibleClosedsCodim.IsCatenarySpace X) [IsLocallyNoetherian X]
    (d : ℕ) (hX : topologicalKrullDim X = d)
    (U : Set X) (hU : IsOpen U) (hne : U.Nonempty) :
    topologicalKrullDim X = topologicalKrullDim U := by
  have hdU : topologicalKrullDim U = (d : WithBot ℕ∞) :=
    (topologicalKrullDim_isOpen_eq_of_catenary X hcat U hU hne).trans hX
  rw [hX, hdU]


/-- On an irreducible, Jacobson, catenary, locally Noetherian scheme of finite dimension, the
local Krull dimension is constant. -/
@[stacks 0DRT "constancy of local dimension"]
theorem isConstant_topologicalKrullDimAt
    (X : Scheme.{u}) [IrreducibleSpace X] [JacobsonSpace X]
    (hcat : IrreducibleClosedsCodim.IsCatenarySpace X) [IsLocallyNoetherian X]
    (d : ℕ) (hX : topologicalKrullDim X = d) :
    ∀ x y : X, topologicalKrullDimAt X x = topologicalKrullDimAt X y := by
  intro x y
  have hlocal (z : X) : topologicalKrullDimAt X z = (d : WithBot ℕ∞) := by
    unfold topologicalKrullDimAt
    have hUniv : topologicalKrullDim (↥(Set.univ : Set X)) = (d : WithBot ℕ∞) :=
      (topologicalKrullDim_eq_of_isOpen_of_catenary X hcat d hX Set.univ isOpen_univ
        ⟨z, Set.mem_univ z⟩).symm.trans hX
    apply le_antisymm
    · exact (iInf_le _ ⟨Set.univ, Set.mem_univ z, isOpen_univ⟩).trans_eq hUniv
    · exact le_iInf fun V => (hX.symm.trans (topologicalKrullDim_eq_of_isOpen_of_catenary X hcat d
        hX V.1 V.2.2 ⟨z, V.2.1⟩)).le
  rw [hlocal x, hlocal y]


/-- **An immediate specialization inside a nonempty open avoiding a point.** In an irreducible
quasi-sober `T₀` locally Noetherian scheme, a point `x` outside a nonempty open `U` has an
immediate generization `y ∈ U`: `y ⤳ x`, `y ≠ x`, and nothing lies strictly between them. -/
alias exists_immediate_specialization_mem_open := exists_immediate_specialization_in_open

/-- **An immediate specialization to a closed point is a covering of irreducible closed
sets**: if `y` is an immediate generization of the closed point `x`, then `{x} ⋖ closure {y}` in
the order of irreducible closed subsets. -/
alias covBy_closure_singleton_of_immediate := closure_singleton_covBy_of_immediate

end AlgebraicGeometry
