module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChowOperations
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardRationalEquivalence

/-!
# Proper pushforward on the Chow group of a good algebraic space

In Situation 0EDT let `X/B` and `Y/B` be good and let `p : X ⟶ Y` be proper over the base. Proper
pushforward of cycles `p_* : Z_k(X) → Z_k(Y)` (Stacks 0EP1) carries cycles rationally equivalent
to zero to cycles rationally equivalent to zero (Stacks 0EQC), and so induces a homomorphism

`p_* : CH_k(X) → CH_k(Y)`

on the Chow groups `CH_k = Z_k/∼_rat` of Stacks 0EQ6, characterised by `p_*[α] = [p_*α]`.

The Chow group here is `AlgebraicGeometry.Space.chowGroup`, whose summands `div(f_j)` are read at
the canonical embeddings `R(W_j) → Q(𝒪^h_{W_j,ξ})` of Stacks 0ENK, with the goodness and
integrality of `W_j` quantified as propositions. The same rational equivalence is
`AlgebraicGeometry.Space.IsRationallyEquivalentToZeroCanonical`, where goodness and integrality
are those computed from the ambient space: two proofs of a proposition are equal, so the two
summand conditions agree, and the two subgroups of `Z_k(X)` coincide. Stacks 0EQC is then the
theorem `AlgebraicGeometry.Space.isRationallyEquivalentToZeroCanonical_properCyclePushforward`,
read through that identification.

## Main definitions

* `AlgebraicGeometry.Space.chowGroupProperPushforward`: `p_* : CH_k(X) → CH_k(Y)`.

## Main results

* `AlgebraicGeometry.Space.IsPrincipalDivisorCycle.isPrincipalDivisorCycleOfGood`: a principal
  divisor in the sense of `AlgebraicGeometry.Space.IsPrincipalDivisorCycle` is one at the
  goodness and integrality of the space.
* `AlgebraicGeometry.Space.isRationallyEquivalentToZeroCanonical_iff`: the two readings of
  "rationally equivalent to zero" agree.
* `AlgebraicGeometry.Space.rationalEquivalencesCanonical_eq_rationalEquivalences` and
  `AlgebraicGeometry.Space.bijective_chowGroupCanonicalToChowGroup`: so do the subgroups and the
  Chow groups.
* `AlgebraicGeometry.Space.isRationallyEquivalentToZero_properCyclePushforward` and
  `AlgebraicGeometry.Space.rationallyEquivalent_properCyclePushforward`: Stacks 0EQC.
* `AlgebraicGeometry.Space.chowGroupProperPushforward_chowClass`: `p_*[α] = [p_*α]`.
* `AlgebraicGeometry.Space.chowGroupCanonicalToChowGroup_comp_chowGroupCanonicalProperPushforward`:
  the pushforward commutes with the identification of the two Chow groups.
* `AlgebraicGeometry.Space.PrivateChern.properPushforwardChow_of`: on `CH_*(X)` the proper
  pushforward is `chowGroupProperPushforward` in each degree.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQC](https://stacks.math.columbia.edu/tag/0EQC)
-/

/- Stacks 0EQC is proved for the canonical reading of rational equivalence in
`ProperPushforwardRationalEquivalence.lean`, by
`rationallyEquivalentCanonical_properCyclePushforward`; the underlying statement for cycles
rationally equivalent to zero, `isRationallyEquivalentToZeroCanonical_properCyclePushforward`, is
used here as it stands. Nothing new about the pushforward is proved in this file: it only
identifies the two readings of rational equivalence and descends to `chowGroup`. -/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The two readings of rational equivalence agree -/

section Comparison

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- A principal divisor in the sense of `AlgebraicGeometry.Space.IsPrincipalDivisorCycle`, whose
goodness and integrality are quantified, is a principal divisor at any given proofs of
goodness and integrality: both read `div(f)` at the canonical embeddings of Stacks 0ENK, and two
proofs of a proposition are equal. -/
theorem IsPrincipalDivisorCycle.isPrincipalDivisorCycleOfGood {sY : Y ⟶ D.space}
    (hY : D.IsGood sY) (hint : IsIntegralSpace D.site D.base D.base_mem Y) {k : ℤ}
    {c : CycleGroup D sY k} (h : IsPrincipalDivisorCycle D sY k c) :
    IsPrincipalDivisorCycleOfGood D sY hY hint k c := by
  obtain ⟨_, _, f, heq⟩ := h
  exact ⟨f, f.isUnit, heq⟩

/-- On a good integral space the two readings of "principal divisor" agree. -/
theorem isPrincipalDivisorCycleOfGood_iff (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (hint : IsIntegralSpace D.site D.base D.base_mem Y) (k : ℤ) (c : CycleGroup D sY k) :
    IsPrincipalDivisorCycleOfGood D sY hY hint k c ↔ IsPrincipalDivisorCycle D sY k c :=
  ⟨fun h => h.isPrincipalDivisorCycle,
    IsPrincipalDivisorCycle.isPrincipalDivisorCycleOfGood D hY hint⟩

/-- The two readings of "rationally equivalent to zero" agree: the summand conditions do, by
`AlgebraicGeometry.Space.isPrincipalDivisorCycleOfGood_iff`, and nothing else differs. -/
theorem isRationallyEquivalentToZeroCanonical_iff (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ)
    (α : CycleGroup D sX k) :
    IsRationallyEquivalentToZeroCanonical.{v} D sX hX k α ↔
      IsRationallyEquivalentToZero.{v} D sX hX k α := by
  refine ⟨fun h => h.isRationallyEquivalentToZero, ?_⟩
  rintro ⟨J, W, hWfin, c, hWdim, hWprin, hWsum⟩
  exact ⟨J, W, hWfin, c, hWdim, fun j => (hWprin j).isPrincipalDivisorCycleOfGood D
    (isGood_integralClosedSubspace D sX hX (W j)) (W j).isIntegralSpace, hWsum⟩

/-- The subgroups of cycles rationally equivalent to zero in the two readings coincide. -/
theorem rationalEquivalencesCanonical_eq_rationalEquivalences (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (k : ℤ) :
    rationalEquivalencesCanonical.{v} D sX hX k = rationalEquivalences.{v} D sX hX k :=
  AddSubgroup.ext fun α => isRationallyEquivalentToZeroCanonical_iff.{v} D sX hX k α

/-- Two cycles are rationally equivalent in one reading exactly when they are in the other. -/
theorem rationallyEquivalentCanonical_iff (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ)
    (α β : CycleGroup D sX k) :
    RationallyEquivalentCanonical.{v} D sX hX k α β ↔ RationallyEquivalent.{v} D sX hX k α β :=
  isRationallyEquivalentToZeroCanonical_iff.{v} D sX hX k (α - β)

/-- The comparison map `AlgebraicGeometry.Space.chowGroupCanonicalToChowGroup` is bijective, the
two subgroups of `Z_k(X)` being equal. -/
theorem bijective_chowGroupCanonicalToChowGroup (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ) :
    Function.Bijective (chowGroupCanonicalToChowGroup.{v} D sX hX k) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_,
    surjective_chowGroupCanonicalToChowGroup.{v} D sX hX k⟩
  obtain ⟨α, rfl⟩ := QuotientAddGroup.mk'_surjective (rationalEquivalencesCanonical.{v} D sX hX k) x
  change chowGroupCanonicalToChowGroup.{v} D sX hX k (chowClassCanonical.{v} D sX hX k α) = 0
    at hx
  rw [chowGroupCanonicalToChowGroup_chowClassCanonical, chowClass_eq_zero_iff,
    ← isRationallyEquivalentToZeroCanonical_iff] at hx
  exact (chowClassCanonical_eq_zero_iff.{v} D sX hX k α).2 hx

/-- The identification of the Chow group at the canonical embeddings with
`AlgebraicGeometry.Space.chowGroup`, as an isomorphism of groups. -/
def chowGroupCanonicalEquivChowGroup (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ) :
    chowGroupCanonical.{v} D sX hX k ≃+ chowGroup.{v} D sX hX k :=
  AddEquiv.ofBijective (chowGroupCanonicalToChowGroup.{v} D sX hX k)
    (bijective_chowGroupCanonicalToChowGroup.{v} D sX hX k)

/-- The isomorphism `AlgebraicGeometry.Space.chowGroupCanonicalEquivChowGroup` sends the class of
a cycle `α` at the canonical embeddings to the class of `α` in
`AlgebraicGeometry.Space.chowGroup`. -/
@[simp]
theorem chowGroupCanonicalEquivChowGroup_chowClassCanonical (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (k : ℤ) (α : CycleGroup D sX k) :
    chowGroupCanonicalEquivChowGroup.{v} D sX hX k (chowClassCanonical.{v} D sX hX k α) =
      chowClass.{v} D sX hX k α :=
  rfl

end Comparison

/-! ### Stacks 0EQC and the pushforward on Chow groups -/

section Pushforward

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    {p : X ⟶ Y} (hpB : p ≫ sY = sX) (hp : IsProper D.site D.base D.base_mem p)

/-- **Stacks 0EQC, for cycles rationally equivalent to zero.** If `α ∈ Z_k(X)` is rationally
equivalent to zero then so is `p_*α ∈ Z_k(Y)`, for `p : X ⟶ Y` proper over the base. -/
theorem isRationallyEquivalentToZero_properCyclePushforward (k : ℤ) (α : CycleGroup D sX k)
    (hα : IsRationallyEquivalentToZero.{v} D sX hX k α) :
    IsRationallyEquivalentToZero.{v} D sY hY k
      (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k α) :=
  (isRationallyEquivalentToZeroCanonical_iff.{v} D sY hY k _).1
    (isRationallyEquivalentToZeroCanonical_properCyclePushforward.{v} D sX hX sY hY hpB hp k α
      ((isRationallyEquivalentToZeroCanonical_iff.{v} D sX hX k α).2 hα))

/-- **Stacks 0EQC.** If `α, β ∈ Z_k(X)` are rationally equivalent, then `p_*α` and `p_*β` are
rationally equivalent, for `p : X ⟶ Y` proper over the base. -/
theorem rationallyEquivalent_properCyclePushforward (k : ℤ) {α β : CycleGroup D sX k}
    (h : RationallyEquivalent.{v} D sX hX k α β) :
    RationallyEquivalent.{v} D sY hY k
      (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k α)
      (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k β) := by
  have h' := isRationallyEquivalentToZero_properCyclePushforward.{v} D sX hX sY hY hpB hp k
    (α - β) h
  rwa [map_sub] at h'

/-- Proper pushforward of cycles maps the subgroup of cycles rationally equivalent to zero into
the subgroup of cycles rationally equivalent to zero. -/
theorem rationalEquivalences_le_comap_properCyclePushforward (k : ℤ) :
    rationalEquivalences.{v} D sX hX k ≤
      (rationalEquivalences.{v} D sY hY k).comap
        (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k) :=
  fun α hα => isRationallyEquivalentToZero_properCyclePushforward.{v} D sX hX sY hY hpB hp k α hα

/-- **Proper pushforward on Chow groups.** The homomorphism `p_* : CH_k(X) → CH_k(Y)` induced by
the proper pushforward of cycles of Stacks 0EP1 along a proper morphism `p : X ⟶ Y` over the
base; it is well defined by Stacks 0EQC. -/
def chowGroupProperPushforward (k : ℤ) :
    chowGroup.{v} D sX hX k →+ chowGroup.{v} D sY hY k :=
  QuotientAddGroup.map _ _ (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k)
    (rationalEquivalences_le_comap_properCyclePushforward.{v} D sX hX sY hY hpB hp k)

/-- `p_*[α] = [p_*α]`: the pushforward on Chow groups is computed on cycles. -/
@[simp]
theorem chowGroupProperPushforward_chowClass (k : ℤ) (α : CycleGroup D sX k) :
    chowGroupProperPushforward.{v} D sX hX sY hY hpB hp k (chowClass.{v} D sX hX k α) =
      chowClass.{v} D sY hY k (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k α) :=
  rfl

/-- The pushforward on Chow groups composed with the class map is the class map composed with
the pushforward of cycles. -/
theorem chowGroupProperPushforward_comp_chowClass (k : ℤ) :
    (chowGroupProperPushforward.{v} D sX hX sY hY hpB hp k).comp (chowClass.{v} D sX hX k) =
      (chowClass.{v} D sY hY k).comp (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k) :=
  rfl

/-- The pushforward on Chow groups is the pushforward on the Chow groups at the canonical
embeddings, read through the identification
`AlgebraicGeometry.Space.chowGroupCanonicalToChowGroup`. -/
theorem chowGroupCanonicalToChowGroup_comp_chowGroupCanonicalProperPushforward (k : ℤ) :
    (chowGroupCanonicalToChowGroup.{v} D sY hY k).comp
        (chowGroupCanonicalProperPushforward.{v} D sX hX sY hY hpB hp k) =
      (chowGroupProperPushforward.{v} D sX hX sY hY hpB hp k).comp
        (chowGroupCanonicalToChowGroup.{v} D sX hX k) :=
  QuotientAddGroup.addMonoidHom_ext _ (AddMonoidHom.ext fun _ => rfl)

end Pushforward

/-! ### The pushforward on Chow homology -/

namespace PrivateChern

variable (D : BaseSpaceDimensionSituation.{u}) {X Y : D.Ambient}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    {p : X ⟶ Y} (hpB : p ≫ sY = sX) (hp : IsProper D.site D.base D.base_mem p)

/-- **Stacks 0EQC**, in the form `AlgebraicGeometry.Space.PrivateChern.chowDescend` takes as its
hypothesis: proper pushforward of cycles respects rational equivalence. -/
theorem respectsRationalEquivalence_properCyclePushforward (k : ℤ) :
    RespectsRationalEquivalence.{u, v} D sX hX sY hY
      (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k) :=
  rationalEquivalences_le_comap_properCyclePushforward.{v} D sX hX sY hY hpB hp k

/-- The homomorphism of Chow groups that `AlgebraicGeometry.Space.PrivateChern.chowDescend`
induces from proper pushforward of cycles is
`AlgebraicGeometry.Space.chowGroupProperPushforward`. -/
theorem chowDescend_properCyclePushforward (k : ℤ) :
    chowDescend.{u, v} D sX hX sY hY (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k) =
      chowGroupProperPushforward.{v} D sX hX sY hY hpB hp k := by
  rw [chowDescend, dite_eq_left
    (respectsRationalEquivalence_properCyclePushforward.{v, u} D sX hX sY
    hY hpB hp k)]
  rfl

/-- On a homogeneous element of `CH_*(X)` of degree `k` the proper pushforward on Chow homology
is `AlgebraicGeometry.Space.chowGroupProperPushforward`. -/
theorem properPushforwardChow_of (k : ℤ) (α : chowGroup.{v} D sX hX k) :
    properPushforwardChow.{u, v} D sX hX sY hY p hpB hp (DirectSum.of _ k α) =
      DirectSum.of (fun k => chowGroup.{v} D sY hY k) k
        (chowGroupProperPushforward.{v} D sX hX sY hY hpB hp k α) := by
  have hcongr : ∀ {a b : ℤ} (h : a = b) (x : chowGroup.{v} D sY hY a),
      DirectSum.of (fun k => chowGroup.{v} D sY hY k) b
          (chowGroupDegreeCongr.{u, v} D sY hY h x) =
        DirectSum.of (fun k => chowGroup.{v} D sY hY k) a x := by
    intro a b h x
    subst h
    rfl
  rw [properPushforwardChow, gradedChowMap_of, AddMonoidHom.comp_apply,
    chowDescend_properCyclePushforward.{v, u} D sX hX sY hY hpB hp k]
  exact hcongr (add_zero k).symm _

end PrivateChern

end AlgebraicGeometry.Space

end
