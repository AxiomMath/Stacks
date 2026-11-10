module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
import StacksCore.FieldTheory.IntermediateField.Adjoin.Defs
public import StacksCore.FieldTheory.MvRatFunc.Basic
import StacksCore.RingTheory.AlgebraicIndependent.Basic
import StacksCore.Tactic.StacksAttribute

/-! # Purely transcendental extensions -/

@[expose] public section

open IntermediateField

/-- **Stacks 030E** (part 3).
A field extension `K/k` is *purely transcendental* if there exists a set `s ⊆ K`
that is algebraically independent over `k` and generates `K` as a field over `k`.
Equivalently, `K` is isomorphic to the field of fractions of a polynomial ring
over `k` on the variables indexed by `s`. -/
@[stacks_fixed 030E "3", mk_iff]
class PurelyTranscendental (k K : Type*) [Field k] [Field K] [Algebra k K] : Prop where
  exists_basis (k K) : ∃ s : Set K, AlgebraicIndepOn k id s ∧ adjoin k s = ⊤

namespace PurelyTranscendental

/-- If a family `x : ι → K` is algebraically independent over `k` and its range generates
`K` as a field over `k`, then `K/k` is purely transcendental. -/
theorem of_algebraicIndependent {k K ι : Type*} [Field k] [Field K] [Algebra k K] {x : ι → K}
    (hx : AlgebraicIndependent k x) (hkx : adjoin k (Set.range x) = ⊤) :
    PurelyTranscendental k K :=
  ⟨Set.range x, .coe_range hx, hkx⟩

/-- **Stacks 030E** (part 3, a part of the correctness).
Any purely transcendental extension `K/k` is `k`-isomorphic to a multivariate
field of rational functions `MvRatFunc s k` for some indexing set `s ⊆ K`. -/
@[stacks 030E "3, a part of the correctness"]
theorem exists_algEquiv_mvRatFunc (k K : Type*) [Field k] [Field K] [Algebra k K]
    [PurelyTranscendental k K] : ∃ s : Set K, Nonempty (MvRatFunc s k ≃ₐ[k] K) := by
  obtain ⟨s, hsi, hsa⟩ := PurelyTranscendental.exists_basis k K
  refine ⟨s, ⟨hsi.aevalEquivField.trans ?_⟩⟩
  rw [show Set.range _ = s by simp, hsa]
  exact Subalgebra.topEquiv

/-- **Stacks 030E** (part 3, a part of the correctness).
The multivariate field of rational functions `MvRatFunc σ k` is purely transcendental
over `k`, with the variables `X i` (`i : σ`) forming a transcendence basis. -/
@[stacks 030E "3, a part of the correctness"]
instance mvRatFunc (k σ : Type*) [Field k] : PurelyTranscendental k (MvRatFunc σ k) := by
  refine of_algebraicIndependent
    (x := fun i ↦ Algebra.algHom k (MvPolynomial σ k) _ (.X i))
    ((MvPolynomial.algebraicIndependent_X σ k).map' <| IsFractionRing.injective _ _) ?_
  refine eq_top_iff.mpr fun x _ ↦ x.induction_on fun ⟨x, y⟩ ↦ ?_
  rw [FractionRing.mk_eq_div, mem_adjoin_iff_div]
  simp_rw [show (Algebra.algHom k (MvPolynomial σ k) (MvRatFunc σ k)) =
      IsScalarTower.toAlgHom k _ _ from rfl,
    IsScalarTower.toAlgHom_apply, Set.range_comp', Algebra.adjoin_algebraMap,
    MvPolynomial.adjoin_range_X]
  refine ⟨_, ?_, _, ?_, rfl⟩ <;> exact Subalgebra.mem_map.mpr ⟨_, trivial, rfl⟩

end PurelyTranscendental

/-- **Stacks 030E** (part 3, a part of the correctness).
Pure transcendence transports across `k`-algebra isomorphisms: if `F ≃ₐ[k] E` and
`F/k` is purely transcendental, then so is `E/k`. -/
@[stacks 030E "3, a part of the correctness"]
theorem AlgEquiv.purelyTranscendental {k F E : Type*}
    [Field k] [Field F] [Field E] [Algebra k F] [Algebra k E]
    (e : F ≃ₐ[k] E) [PurelyTranscendental k F] : PurelyTranscendental k E := by
  obtain ⟨s, hsi, hsa⟩ := PurelyTranscendental.exists_basis k F
  refine ⟨e '' s, .image hsi (f := e.toAlgHom) e.injective, ?_⟩
  rw [← AlgHom.coe_ofClass, ← adjoin_map, hsa, map_top_of_surjective e.surjective]

/-- **Stacks 030E** (part 3, a part of the correctness).
The reverse-direction transport: if `F ≃ₐ[k] E` and `E/k` is purely transcendental,
then so is `F/k`. -/
@[stacks 030E "3, a part of the correctness"]
theorem AlgEquiv.purelyTranscendental' {k F E : Type*}
    [Field k] [Field F] [Field E] [Algebra k F] [Algebra k E]
    (e : F ≃ₐ[k] E) [PurelyTranscendental k E] : PurelyTranscendental k F :=
  e.symm.purelyTranscendental

/-- The single-variable field of rational functions `RatFunc k` is purely transcendental
over `k`. -/
instance PurelyTranscendental.ratFunc (k : Type*) [Field k] : PurelyTranscendental k (RatFunc k) :=
  MvRatFunc.ofRatFunc k |>.purelyTranscendental'

/-- **Stacks 09I8** (immediate generalization).
If `x ∈ K` is transcendental over `k`, then the simple extension `k⟮x⟯` is purely
transcendental over `k`. The Stacks tag records the special case `Q(π)/Q`. -/
@[stacks 09I8 "immediate generalization"]
theorem Transcendental.purelyTranscendental_adjoin
    {k K : Type*} [Field k] [Field K] [Algebra k K] {x : K} (hx : Transcendental k x) :
    PurelyTranscendental k k⟮x⟯ :=
  RatFunc.algEquivOfTranscendental _ hx |>.purelyTranscendental

/-- The intermediate field generated over `k` by an algebraically independent family
`x : ι → K` is purely transcendental over `k`. -/
theorem AlgebraicIndependent.purelyTranscendental_adjoin_range
    {k K ι : Type*} [Field k] [Field K] [Algebra k K]
    {x : ι → K} (hx : AlgebraicIndependent k x) :
    PurelyTranscendental k (adjoin k (Set.range x)) :=
  hx.aevalEquivField.purelyTranscendental

/-- The intermediate field generated over `k` by an algebraically independent set
`s ⊆ K` is purely transcendental over `k`. -/
theorem AlgebraicIndepOn.purelyTranscendental_adjoin
    {k K : Type*} [Field k] [Field K] [Algebra k K]
    {s : Set K} (hx : AlgebraicIndepOn k id s) :
    PurelyTranscendental k (adjoin k s) := by
  convert hx.purelyTranscendental_adjoin_range <;> simp

/-- **Stacks 09IA**.
Every field extension `E/F` admits an intermediate field `F'` such that `F'/F` is
purely transcendental and `E/F'` is algebraic. (The Stacks tag also notes that this
decomposition is not unique, e.g. for `F(t)/F` one can take either `F(t)` itself or
`F(t²)` as the purely transcendental part.) -/
@[stacks 09IA]
theorem exists_intermediateField_purelyTranscendental_and_algebraic
    (F E : Type*) [Field F] [Field E] [Algebra F E] :
    ∃ F' : IntermediateField F E, PurelyTranscendental F F' ∧ Algebra.IsAlgebraic F' E := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F E
  rw [isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic,
    algebraicIndependent_subtypeVal_iff, show Set.range _ = s by simp] at hs
  obtain ⟨hs, _⟩ := hs
  exact ⟨adjoin F s, hs.purelyTranscendental_adjoin, open algebraAdjoinAdjoin in
    Algebra.IsAlgebraic.extendScalars (R := Algebra.adjoin F s) (IsFractionRing.injective _ _)⟩
