module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalFirstChernCapTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalPrincipalDivisorUnits
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaProof.ChowClass
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisorCycleOfGoodDifference
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalenceSumsCanonical

/-!
# Rational equivalence by canonical principal divisors

In Situation 0EDT let `X/B` be good. Stacks 0EQ6 calls a `k`-cycle on `X` rationally equivalent
to zero when it is a locally finite sum `∑ (i_j)_* div(f_j)` of principal divisors on integral
closed subspaces `W_j ⊆ X` of δ-dimension `k + 1`, the principal divisor `div(f_j)` of
`f_j ∈ R(W_j)^*` being the one of Stacks 0EQ1, computed through the canonical embeddings
`R(W_j) → Q(𝒪^h_{W_j,ξ})` of Stacks 0ENK
(`AlgebraicGeometry.Space.canonicalPrincipalDivisorCycleAt`).

This file records such sums with the witnessing family and rational functions kept explicit,
and with the point sets of the `W_j` inside a given set `T ⊆ |X|`
(`AlgebraicGeometry.Space.IsCanonicallyRationallyEquivalentToZeroWithin`), as the locally
finite sums `AlgebraicGeometry.Space.IsCycleFamilySumWithin` whose summands are canonical
principal divisors. Such sums are carried along a closed immersion `j : T → X`, and a sum on `X`
whose subspaces lie in the image of `j` comes from one on `T`.

## Main definitions

* `AlgebraicGeometry.Space.canonicalPrincipalDivisors`: the principal divisors `div(f)` on an
  integral closed subspace of δ-dimension `k + 1`, at the canonical embeddings of Stacks 0ENK.
* `AlgebraicGeometry.Space.IsCanonicallyRationallyEquivalentToZeroWithin`: `α` is a locally finite
  sum of pushforwards of such principal divisors on integral closed subspaces inside `T`.

## Main results

* `IsCanonicallyRationallyEquivalentToZeroWithin.isRationallyEquivalentToZeroCanonical`: such a
  sum is rationally equivalent to zero in the sense of Stacks 0EQ6,
  `AlgebraicGeometry.Space.IsRationallyEquivalentToZeroCanonical`.
* `isRationallyEquivalentToZeroCanonical_finsum_of_canonicallyWithin`: Stacks 0EQ8 for such sums.
* `IsCanonicallyRationallyEquivalentToZeroWithin.isRationallyEquivalentToZeroWithin`: such a sum
  is a sum of principal divisors in the existentially quantified reading.
* `cycleGroupClosedPushforward_cycleFamilySum`: the pushforward along a closed immersion of a
  locally finite sum.
* `IsCanonicallyRationallyEquivalentToZeroWithin.closedPushforward`: pushforward along a closed
  immersion.
* `IsCanonicallyRationallyEquivalentToZeroWithin.of_closedPushforward`: a sum on `X` whose
  subspaces lie in the image of a closed immersion `j : T → X` and which is `j_* β` comes from
  such a sum on `T`.

## References

* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQ1](https://stacks.math.columbia.edu/tag/0EQ1)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EQ8](https://stacks.math.columbia.edu/tag/0EQ8)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u v w

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (k : ℤ)

/-! ### Canonical principal divisors -/

/-- The *canonical principal divisors* on an integral closed subspace `W ⊆ X` of δ-dimension
`k + 1`: the cycles `div(f)` of Stacks 0EQ1 for `f ∈ R(W)^*`, at the canonical embeddings of
Stacks 0ENK. -/
def canonicalPrincipalDivisors (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    Set (CycleGroup D (W.subspace.ι ≫ sX) k) :=
  {c | ∃ (hk : deltaDimensionClosed D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
      Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt))
    (f : (rationalFunctions D.site D.base D.base_mem
      (isGood_integralClosedSubspace D sX hX W).1)ˣ),
    c = canonicalPrincipalDivisorCycleAt D (W.subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D sX hX W) W.isIntegralSpace f hk}

variable {D sX hX k}

/-- The δ-dimension of an integral closed subspace is `k + 1` once its `univ` has that
δ-dimension as a closed subset. -/
private theorem deltaDimension_eq_of_deltaDimensionClosed_eq
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hk : deltaDimensionClosed D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
      Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt)) :
    deltaDimension D sX W = k + 1 := by
  rw [deltaDimensionClosed_univ_integralClosedSubspace D sX hX W] at hk
  exact WithBotTop.coe_injective hk

/-- A canonical principal divisor is a principal divisor of Stacks 0EQ6, on a subspace of the
right δ-dimension. -/
theorem mem_principalDivisors_of_mem_canonicalPrincipalDivisors
    {W : IntegralClosedSubspace D.site D.base D.base_mem X} {c : CycleGroup D (W.subspace.ι ≫ sX) k}
    (h : c ∈ canonicalPrincipalDivisors D sX hX k W) :
    c ∈ {c | IsPrincipalDivisorCycle D (W.subspace.ι ≫ sX) k c ∧
      deltaDimension D sX W = k + 1} := by
  obtain ⟨hk, f, rfl⟩ := h
  refine ⟨isPrincipalDivisorCycle_canonicalPrincipalDivisorCycleAt D _
    (isGood_integralClosedSubspace D sX hX W) W.isIntegralSpace f hk,
    deltaDimension_eq_of_deltaDimensionClosed_eq (hX := hX) hk⟩

/-- An integer multiple of a canonical principal divisor is one: `n · div(f) = div(f^n)`. -/
theorem zsmul_mem_canonicalPrincipalDivisors
    {W : IntegralClosedSubspace D.site D.base D.base_mem X} {c : CycleGroup D (W.subspace.ι ≫ sX) k}
    (h : c ∈ canonicalPrincipalDivisors D sX hX k W) (n : ℤ) :
    n • c ∈ canonicalPrincipalDivisors D sX hX k W := by
  obtain ⟨hk, f, rfl⟩ := h
  exact ⟨hk, f ^ n, (canonicalPrincipalDivisorCycleAt_zpow D _ _ W.isIntegralSpace f n hk).symm⟩

/-- The negative of a canonical principal divisor is one: `-div(f) = div(f⁻¹)`. -/
theorem neg_mem_canonicalPrincipalDivisors
    {W : IntegralClosedSubspace D.site D.base D.base_mem X} {c : CycleGroup D (W.subspace.ι ≫ sX) k}
    (h : c ∈ canonicalPrincipalDivisors D sX hX k W) :
    -c ∈ canonicalPrincipalDivisors D sX hX k W := by
  simpa using zsmul_mem_canonicalPrincipalDivisors h (-1)

/-! ### Sums of canonical principal divisors -/

variable (D sX hX k) in
/-- A `k`-cycle `α` on `X` is *canonically rationally equivalent to zero within* `T ⊆ |X|` when
it is a sum `∑ (i_j)_* div(f_j)` as in Stacks 0EQ6 over a locally finite family of integral closed
subspaces `W_j` with point sets in `T`, the `div(f_j)` being canonical principal divisors
(`AlgebraicGeometry.Space.canonicalPrincipalDivisors`). -/
abbrev IsCanonicallyRationallyEquivalentToZeroWithin (α : CycleGroup D sX k)
    (T : Set (points D.site D.base D.base_mem X)) : Prop :=
  IsCycleFamilySumWithin.{u, v} D sX hX k (canonicalPrincipalDivisors D sX hX k) α T

/-- A sum of canonical principal divisors within `T` is rationally equivalent to zero within `T`
in the sense of Stacks 0EQ6. -/
theorem IsCanonicallyRationallyEquivalentToZeroWithin.isRationallyEquivalentToZeroWithin
    {α : CycleGroup D sX k} {T : Set (points D.site D.base D.base_mem X)}
    (h : IsCanonicallyRationallyEquivalentToZeroWithin.{u, v} D sX hX k α T) :
    IsRationallyEquivalentToZeroWithin.{v} D sX hX k α T :=
  (IsCycleFamilySumWithin.of_subset h fun _ _ hc =>
    mem_principalDivisors_of_mem_canonicalPrincipalDivisors hc).isRationallyEquivalentToZeroWithin

/-- A canonical principal divisor is a principal divisor at the canonical embeddings of
Stacks 0ENK in the sense of `AlgebraicGeometry.Space.IsPrincipalDivisorCycleOfGood`, on a
subspace of δ-dimension `k + 1`. -/
theorem isPrincipalDivisorCycleOfGood_of_mem_canonicalPrincipalDivisors
    {W : IntegralClosedSubspace D.site D.base D.base_mem X} {c : CycleGroup D (W.subspace.ι ≫ sX) k}
    (h : c ∈ canonicalPrincipalDivisors D sX hX k W) :
    IsPrincipalDivisorCycleOfGood D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
        W.isIntegralSpace k c ∧ deltaDimension D sX W = k + 1 := by
  obtain ⟨hk, f, rfl⟩ := h
  refine ⟨isPrincipalDivisorCycleOfGood_canonicalPrincipalDivisorCycleAt D _
    (isGood_integralClosedSubspace D sX hX W) W.isIntegralSpace f hk,
    deltaDimension_eq_of_deltaDimensionClosed_eq (hX := hX) hk⟩

/-- A sum of canonical principal divisors within `T` is rationally equivalent to zero within `T`
at the canonical embeddings of Stacks 0ENK, in the sense of
`AlgebraicGeometry.Space.IsRationallyEquivalentToZeroWithinCanonical`. -/
theorem IsCanonicallyRationallyEquivalentToZeroWithin.isRationallyEquivalentToZeroWithinCanonical
    {α : CycleGroup D sX k} {T : Set (points D.site D.base D.base_mem X)}
    (h : IsCanonicallyRationallyEquivalentToZeroWithin.{u, v} D sX hX k α T) :
    IsRationallyEquivalentToZeroWithinCanonical.{v} D sX hX k α T := by
  obtain ⟨J, W, hWfin, c, hsub, hc, hsum⟩ := h
  exact ⟨J, W, hWfin, c, hsub,
    fun j => (isPrincipalDivisorCycleOfGood_of_mem_canonicalPrincipalDivisors (hc j)).2,
    fun j => (isPrincipalDivisorCycleOfGood_of_mem_canonicalPrincipalDivisors (hc j)).1, hsum⟩

/-- A sum of canonical principal divisors is rationally equivalent to zero in the sense of
Stacks 0EQ6, `AlgebraicGeometry.Space.IsRationallyEquivalentToZeroCanonical`. -/
theorem IsCanonicallyRationallyEquivalentToZeroWithin.isRationallyEquivalentToZeroCanonical
    {α : CycleGroup D sX k} {T : Set (points D.site D.base D.base_mem X)}
    (h : IsCanonicallyRationallyEquivalentToZeroWithin.{u, v} D sX hX k α T) :
    IsRationallyEquivalentToZeroCanonical.{v} D sX hX k α :=
  h.isRationallyEquivalentToZeroWithinCanonical.isRationallyEquivalentToZeroCanonical

variable (D sX hX k) in
/-- **Stacks 0EQ8 for sums of canonical principal divisors.** A `k`-cycle which is
coefficientwise the locally finite sum of cycles `β i`, each a sum of canonical principal
divisors within the member `T i` of a locally finite family of subsets of `|X|`, is rationally
equivalent to zero in the sense of Stacks 0EQ6. -/
theorem isRationallyEquivalentToZeroCanonical_finsum_of_canonicallyWithin {I : Type w}
    (T : I → Set (points D.site D.base D.base_mem X)) (hT : LocallyFinite T)
    (β : I → CycleGroup D sX k)
    (hβ : ∀ i, IsCanonicallyRationallyEquivalentToZeroWithin.{u, v} D sX hX k (β i) (T i))
    {α : CycleGroup D sX k} (hα : ∀ Z, α.1 Z = ∑ᶠ i : I, (β i).1 Z) :
    IsRationallyEquivalentToZeroCanonical.{max w v} D sX hX k α :=
  IsCanonicallyRationallyEquivalentToZeroWithin.isRationallyEquivalentToZeroCanonical
    (isCycleFamilySumWithin_finsum D sX hX k T hT β hβ hα)

/-! ### Closed immersions -/

section ClosedImmersion

variable {T : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sT : T ⟶ D.space)
    (hT : D.IsGood sT) {j : T ⟶ X} (hj : IsClosedImmersion D.site D.base D.base_mem j)
    (hjs : j ≫ sX = sT)

/-- The `univ` of the image `j(V) ⊆ X` of an integral closed subspace `V ⊆ T` has δ-dimension
`k + 1` as a closed subset iff the `univ` of `V` does. -/
private theorem deltaDimensionClosed_pushforward_eq_iff (hjs : j ≫ sX = sT)
    (V : IntegralClosedSubspace D.site D.base D.base_mem T) :
    deltaDimensionClosed D
        ((IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hT.1
          (D.isDecentSpace_of_isGood sX hX) hj V).subspace.ι ≫ sX)
        (isGood_integralClosedSubspace D sX hX _) Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt) ↔
      deltaDimensionClosed D (V.subspace.ι ≫ sT) (isGood_integralClosedSubspace D sT hT V)
        Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt) := by
  rw [deltaDimensionClosed_univ_integralClosedSubspace D sX hX,
    IntegralClosedSubspace.deltaDimension_pushforward D sX hX.2.2 hX.1 hT.1
      (D.isDecentSpace_of_isGood sX hX) hj V, hjs,
    deltaDimensionClosed_univ_integralClosedSubspace D sT hT V]

/-- The pushforward along a closed immersion `j : T → X` of the pushforward of a canonical
principal divisor from an integral closed subspace `V ⊆ T` is the pushforward of a canonical
principal divisor from the image `j(V) ⊆ X`. -/
theorem exists_cycleGroupClosedPushforward_integralClosedSubspacePushforward_eq
    (V : IntegralClosedSubspace D.site D.base D.base_mem T)
    {c : CycleGroup D (V.subspace.ι ≫ sT) k} (hc : c ∈ canonicalPrincipalDivisors D sT hT k V) :
    ∃ c' ∈ canonicalPrincipalDivisors D sX hX k
        (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hT.1
          (D.isDecentSpace_of_isGood sX hX) hj V),
      cycleGroupClosedPushforward D hX.1 hT.1 (D.isDecentSpace_of_isGood sX hX) hj sX hX.2.2 sT
          hjs k (integralClosedSubspacePushforward D sT hT V k c) =
        integralClosedSubspacePushforward D sX hX
          (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hT.1
            (D.isDecentSpace_of_isGood sX hX) hj V) k c' := by
  have hdec := D.isDecentSpace_of_isGood sX hX
  set V' := IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hT.1
    (D.isDecentSpace_of_isGood sX hX) hj V with hV'def
  obtain ⟨hk, f, rfl⟩ := hc
  have hV := isGood_integralClosedSubspace D sT hT V
  have hV' := isGood_integralClosedSubspace D sX hX V'
  let φ := IntegralClosedSubspace.isoPushforward hX.1 hT.1 hdec hj V
  have hk' := (deltaDimensionClosed_pushforward_eq_iff (hX := hX) sT hT hj hjs V).2 hk
  refine ⟨_, ⟨hk', Units.map (rationalFunctionsMapIso hV'.1 φ : _ →* _) f, rfl⟩, ?_⟩
  refine Subtype.ext ?_
  exact cycleClosedPushforward_principalDivisorCycleCoefficients_image D sX hX hdec hT.1
    (D.isDecentSpace_of_isGood sT hT) hj V (V.subspace.ι ≫ sT) hV (V'.subspace.ι ≫ sX) hV'
    (f : rationalFunctions D.site D.base D.base_mem hV.1) f.isUnit

/-- Conversely, the pushforward of a canonical principal divisor from an integral closed subspace
of `X` which is the image `j(V)` of one of `T` is the pushforward along `j` of the pushforward of a
canonical principal divisor from `V`. -/
theorem exists_integralClosedSubspacePushforward_eq_cycleGroupClosedPushforward
    (V : IntegralClosedSubspace D.site D.base D.base_mem T)
    {c : CycleGroup D ((IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hT.1
      (D.isDecentSpace_of_isGood sX hX) hj V).subspace.ι ≫ sX) k}
    (hc : c ∈ canonicalPrincipalDivisors D sX hX k
      (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hT.1
        (D.isDecentSpace_of_isGood sX hX) hj V)) :
    ∃ c' ∈ canonicalPrincipalDivisors D sT hT k V,
      cycleGroupClosedPushforward D hX.1 hT.1 (D.isDecentSpace_of_isGood sX hX) hj sX hX.2.2 sT
          hjs k (integralClosedSubspacePushforward D sT hT V k c') =
        integralClosedSubspacePushforward D sX hX
          (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hT.1
            (D.isDecentSpace_of_isGood sX hX) hj V) k c := by
  have hdec := D.isDecentSpace_of_isGood sX hX
  set V' := IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hT.1
    (D.isDecentSpace_of_isGood sX hX) hj V with hV'def
  obtain ⟨hk, f, rfl⟩ := hc
  have hV := isGood_integralClosedSubspace D sT hT V
  have hV' := isGood_integralClosedSubspace D sX hX V'
  let φ := IntegralClosedSubspace.isoPushforward hX.1 hT.1 hdec hj V
  have hk' := (deltaDimensionClosed_pushforward_eq_iff (hX := hX) sT hT hj hjs V).1 hk
  refine ⟨_, ⟨hk', Units.map (rationalFunctionsMapIso hV.1 φ.symm : _ →* _) f, rfl⟩, ?_⟩
  have hdecV := D.isDecentSpace_of_isGood _ hV
  have hdecV' := D.isDecentSpace_of_isGood _ hV'
  have hiso := cycleClosedPushforward_principalDivisorCycleCoefficients_of_iso D
    (V'.subspace.ι ≫ sX) hV' (V.subspace.ι ≫ sT) hV hdecV' hdecV φ.symm V'.isIntegralSpace
    V.isIntegralSpace (f : rationalFunctions D.site D.base D.base_mem hV'.1) f.isUnit
  have hc₁ := isClosedImmersion_comp D.site D.base D.base_mem _ _ V.isClosedSubspace.2 hj
  have hφ : φ.inv ≫ V.subspace.ι ≫ j = V'.subspace.ι := by
    rw [← IntegralClosedSubspace.isoPushforward_hom_comp_ι hX.1 hT.1 hdec hj V,
      Iso.inv_hom_id_assoc]
  refine Subtype.ext ?_
  change cycleClosedPushforward D hX.1 hT.1 hdec hj
      (cycleClosedPushforward D hT.1 hV.1 (D.isDecentSpace_of_isGood sT hT) V.isClosedSubspace.2
        (canonicalPrincipalDivisorCycleAt D _ hV V.isIntegralSpace
          (Units.map (rationalFunctionsMapIso hV.1 φ.symm : _ →* _) f) hk').1) =
    cycleClosedPushforward D hX.1 hV'.1 hdec V'.isClosedSubspace.2
      (canonicalPrincipalDivisorCycleAt D _ hV' V'.isIntegralSpace f hk).1
  rw [cycleClosedPushforward_cycleClosedPushforward D hX.1 hT.1 hV.1 hdec
      (D.isDecentSpace_of_isGood sT hT) rfl V.isClosedSubspace.2 hj hc₁]
  have h2 := cycleClosedPushforward_cycleClosedPushforward D hX.1 hV.1 hV'.1 hdec hdecV hφ
    (isClosedImmersion_of_isIso D.site D.base D.base_mem φ.inv) hc₁ V'.isClosedSubspace.2
    (canonicalPrincipalDivisorCycleAt D _ hV' V'.isIntegralSpace f hk).1
  refine Eq.trans ?_ h2
  exact congrArg _ hiso.symm

/-- **The pushforward of a locally finite sum along a closed immersion.** If the pushforward
along `j : T → X` of each summand `(V_i → T)_* c_i` of a locally finite sum on `T` is the
pushforward of a cycle `c'_i` on the image `j(V_i) ⊆ X`, then `j_* ∑ (V_i → T)_* c_i` is
`∑ (j(V_i) → X)_* c'_i`. -/
theorem cycleGroupClosedPushforward_cycleFamilySum {I : Type w}
    (V : I → IntegralClosedSubspace D.site D.base D.base_mem T)
    (hV : LocallyFinite fun i => subspacePointSet D.site D.base D.base_mem T (V i).subspace)
    (hV' : LocallyFinite fun i => subspacePointSet D.site D.base D.base_mem X
      (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hT.1
        (D.isDecentSpace_of_isGood sX hX) hj (V i)).subspace)
    (c : ∀ i, CycleGroup D ((V i).subspace.ι ≫ sT) k)
    (c' : ∀ i, CycleGroup D ((IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1
      hT.1 (D.isDecentSpace_of_isGood sX hX) hj (V i)).subspace.ι ≫ sX) k)
    (hc : ∀ i, cycleGroupClosedPushforward D hX.1 hT.1 (D.isDecentSpace_of_isGood sX hX) hj sX
        hX.2.2 sT hjs k (integralClosedSubspacePushforward D sT hT (V i) k (c i)) =
      integralClosedSubspacePushforward D sX hX (IntegralClosedSubspace.pushforward D.site D.base
        D.base_mem hX.1 hT.1 (D.isDecentSpace_of_isGood sX hX) hj (V i)) k (c' i)) :
    cycleGroupClosedPushforward D hX.1 hT.1 (D.isDecentSpace_of_isGood sX hX) hj sX hX.2.2 sT
        hjs k (cycleFamilySum D sT hT V hV k c) =
      cycleFamilySum D sX hX (fun i => IntegralClosedSubspace.pushforward D.site D.base
        D.base_mem hX.1 hT.1 (D.isDecentSpace_of_isGood sX hX) hj (V i)) hV' k c' := by
  have hdec := D.isDecentSpace_of_isGood sX hX
  refine Subtype.ext (funext fun Z => ?_)
  change cycleClosedPushforward D hX.1 hT.1 hdec hj (cycleFamilySum D sT hT V hV k c).1 Z =
    (cycleFamilySum D sX hX _ hV' k c').1 Z
  rw [cycleFamilySum_apply]
  simp_rw [← hc]
  by_cases hZ : ∃ Z₀, IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hT.1 hdec
      hj Z₀ = Z
  · obtain ⟨Z₀, rfl⟩ := hZ
    rw [cycleClosedPushforward_apply_pushforward, cycleFamilySum_apply]
    refine finsum_congr fun i => ?_
    exact (cycleClosedPushforward_apply_pushforward D hX.1 hT.1 hdec hj _ Z₀).symm
  · rw [cycleClosedPushforward_apply_of_forall_ne D hX.1 hT.1 hdec hj _ Z
      fun Z₀ hZ₀ => hZ ⟨Z₀, hZ₀⟩]
    exact (finsum_eq_zero_of_forall_eq_zero fun i => cycleClosedPushforward_apply_of_forall_ne D
      hX.1 hT.1 hdec hj _ Z fun Z₀ hZ₀ => hZ ⟨Z₀, hZ₀⟩).symm

/-- **Pushforward along a closed immersion.** If `β` is canonically rationally equivalent to zero
within `S ⊆ |T|`, then `j_* β` is canonically rationally equivalent to zero within `j(S)`. -/
theorem IsCanonicallyRationallyEquivalentToZeroWithin.closedPushforward
    {β : CycleGroup D sT k} {S : Set (points D.site D.base D.base_mem T)}
    (h : IsCanonicallyRationallyEquivalentToZeroWithin.{u, v} D sT hT k β S) :
    IsCanonicallyRationallyEquivalentToZeroWithin.{u, v} D sX hX k
      (cycleGroupClosedPushforward D hX.1 hT.1 (D.isDecentSpace_of_isGood sX hX) hj sX hX.2.2 sT
        hjs k β) (pointsMap D.site D.base D.base_mem T j '' S) := by
  have hdec := D.isDecentSpace_of_isGood sX hX
  obtain ⟨J, W, hWfin, c, hsub, hcan, rfl⟩ := h
  choose c' hc' heq using fun i =>
    exists_cycleGroupClosedPushforward_integralClosedSubspacePushforward_eq sT hT hj hjs (W i)
      (hcan i)
  have hfin : LocallyFinite fun i => subspacePointSet D.site D.base D.base_mem X
      (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hT.1 hdec hj
        (W i)).subspace :=
    locallyFinite_of_isClosedEmbedding_extend
      (isClosedEmbedding_pointsMap_of_isClosedImmersion D.site D.base D.base_mem hX.1 hj)
      (e := id) (fun i hi => absurd rfl (hi i))
      (fun i => (IntegralClosedSubspace.subspacePointSet_pushforward D.site D.base D.base_mem
        hX.1 hT.1 hdec hj (W i)).le) hWfin
  refine ⟨J, fun i => IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hT.1 hdec
    hj (W i), hfin, c', fun i => ?_, hc',
    cycleGroupClosedPushforward_cycleFamilySum sT hT hj hjs W hWfin hfin c c' heq⟩
  rw [IntegralClosedSubspace.subspacePointSet_pushforward]
  exact Set.image_mono (hsub i)

/-- **Descent along a closed immersion.** Let `j : T → X` be a closed immersion over the base,
`β` a `k`-cycle on `T` and `S ⊆ |X|` a set inside the image of `|j|`. If `j_* β` is canonically
rationally equivalent to zero within `S`, then `β` is canonically rationally equivalent to zero
within `|j|⁻¹(S)`. -/
theorem IsCanonicallyRationallyEquivalentToZeroWithin.of_closedPushforward
    {β : CycleGroup D sT k} {S : Set (points D.site D.base D.base_mem X)}
    (hS : S ⊆ Set.range (pointsMap D.site D.base D.base_mem T j))
    (h : IsCanonicallyRationallyEquivalentToZeroWithin.{u, v} D sX hX k
      (cycleGroupClosedPushforward D hX.1 hT.1 (D.isDecentSpace_of_isGood sX hX) hj sX hX.2.2 sT
        hjs k β) S) :
    IsCanonicallyRationallyEquivalentToZeroWithin.{u, v} D sT hT k β
      (pointsMap D.site D.base D.base_mem T j ⁻¹' S) := by
  have hdec := D.isDecentSpace_of_isGood sX hX
  have hTdec := D.isDecentSpace_of_isGood sT hT
  obtain ⟨J, W, hWfin, c, hsub, hcan, hsum⟩ := h
  choose V hV using fun i => IntegralClosedSubspace.exists_pushforward_eq D.site D.base D.base_mem
    hX.1 hT.1 hdec hTdec hj (W i) ((hsub i).trans hS)
  obtain rfl : W = fun i => IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hT.1
      hdec hj (V i) := funext fun i => (hV i).symm
  choose c' hc' heq using fun i =>
    exists_integralClosedSubspacePushforward_eq_cycleGroupClosedPushforward sT hT hj hjs (V i)
      (hcan i)
  have hpts : ∀ i, subspacePointSet D.site D.base D.base_mem T (V i).subspace ⊆
      pointsMap D.site D.base D.base_mem T j ⁻¹'
        subspacePointSet D.site D.base D.base_mem X
          (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hT.1 hdec hj
            (V i)).subspace := by
    intro i x hx
    rw [Set.mem_preimage, IntegralClosedSubspace.subspacePointSet_pushforward]
    exact Set.mem_image_of_mem _ hx
  have hfin : LocallyFinite fun i => subspacePointSet D.site D.base D.base_mem T (V i).subspace :=
    (hWfin.preimage_continuous (continuous_pointsMap D.site D.base D.base_mem j)).subset hpts
  refine ⟨J, V, hfin, c', fun i => (hpts i).trans (Set.preimage_mono (hsub i)), hc', ?_⟩
  refine injective_cycleGroupClosedPushforward D hX.1 hT.1 hdec hj sX hX.2.2 sT hjs k ?_
  rw [hsum]
  exact (cycleGroupClosedPushforward_cycleFamilySum sT hT hj hjs V hfin hWfin c' c heq).symm

end ClosedImmersion

end AlgebraicGeometry.Space

end
