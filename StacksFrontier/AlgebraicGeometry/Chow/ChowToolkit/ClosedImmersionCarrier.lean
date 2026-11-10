module

public import StacksFrontier.AlgebraicGeometry.Chow.CycleAdditivity
public import StacksFrontier.AlgebraicGeometry.Chow.DivisorTransport
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.LocallyFiniteImage

/-!
# Where a pushed-forward rational equivalence lives, and locally finite sums of them

Stacks 02RZ says that rational equivalences on a locally finite family of closed subschemes
`T i ⊆ X` may be summed: if a cycle `α` on `X` is coefficientwise the locally finite sum of the
pushforwards of cycles `a i` on the `T i`, and each `a i` is rationally equivalent to zero, then so
is `α`. This file proves it.

The combinatorial half is already available as
`Stacks.Chow.rationallyEquivalentToZero_finsum`, but it asks for more than rational equivalence to
zero of each summand: it asks for `Stacks.Chow.IsRationallyEquivalentToZeroWithin`, the refinement
of Stacks 02RW that remembers a set containing the whole witnessing family. That extra information
is exactly what makes the combined family locally finite, and it is indispensable — nothing stops
infinitely many of the witnessing subschemes of the individual equivalences from passing through
one point of `X`.

So what is missing, and supplied here, is that the pushforward of a rational equivalence **along a
closed immersion** is witnessed inside the image of that closed immersion. That is visible in the
reduction of Stacks 02S2 to its one-subscheme case,
`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_killsPrincipalDivisor`: the
family it produces is the family of scheme-theoretic images `(W j).map p`, whose supports are
contained in the closure of the image of `p` by `Scheme.IdealSheafData.support_map`. Only the
conclusion of that theorem forgets it, so the reduction is carried out again here with the carrier
retained. For a closed immersion the closure is the image itself, and for the inclusion of a closed
subscheme the image is its support — which is the set the summation lemma wants.

## Main results

* `Stacks.Chow.properPushforward_isRationallyEquivalentToZeroWithin_of_killsPrincipalDivisor` —
  the reduction of Stacks 02S2, with the carrier of the resulting rational equivalence retained.
* `Stacks.Chow.properPushforward_isRationallyEquivalentToZeroWithin_of_isClosedImmersion` — along a
  closed immersion, a pushed-forward rational equivalence to zero is witnessed inside the image.
  This needs no hypothesis: Stacks 02S2 for a closed immersion is proved outright.
* `Stacks.Chow.rationallyEquivalentToZero_finsum_of_closedSupports`,
  `Stacks.Chow.rationallyEquivalent_finsum_of_closedSupports` — **Stacks 02RZ**, in the form of
  equivalence to zero and in the two-sided form of the source.

## Implementation notes

Stacks 02RZ is proved first in the form of equivalence to zero, the form its consumers use and the
form the summation lemma `Stacks.Chow.rationallyEquivalentToZero_finsum` has. The two-sided form of
the source follows because the pushforward of a cycle on `T i` is supported in `(T i).support`, so
the two locally finite sums have finite support at each point and may be subtracted termwise.

The `@[stacks 02RZ]` attribute sits on the two-sided form, the statement of the tag; the local
finiteness of the combined family, the other half of its content, is internal to
`Stacks.Chow.rationallyEquivalentToZeroWithin_finsum`.

## References

* [Stacks Project, Tag 02RZ](https://stacks.math.columbia.edu/tag/02RZ)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]

/-! ### The carrier of a pushed-forward rational equivalence -/

/-- **The reduction of Stacks 02S2 to its one-subscheme case, with the carrier retained.** Granted
`Stacks.Chow.ProperPushforwardKillsPrincipalDivisor`, the proper pushforward along `p` of a cycle
rationally equivalent to zero is rationally equivalent to zero *within the closure of the image of
`p`*: the witnessing family is the family of scheme-theoretic images of the original witnesses, and
the support of a scheme-theoretic image lies in that closure.

This is `Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_killsPrincipalDivisor`
with the carrier of `Stacks.Chow.IsRationallyEquivalentToZeroWithin` kept rather than discarded;
the carrier is what makes a locally finite family of such equivalences summable.

Stated for a rational equivalence that already carries a carrier `T` upstairs, which is what
Stacks 0B73 needs: there a rational equivalence produced inside one divisor has to be pushed into
the ambient scheme and stay inside the image of that divisor, rather than spreading over the whole
image of `p`. The plain statement is the case `T = Set.univ`, recorded below as
`Stacks.Chow.properPushforward_isRationallyEquivalentToZeroWithin_of_killsPrincipalDivisor`. -/
theorem properPushforward_isRationallyEquivalentToZeroWithin_of_killsPrincipalDivisor_of_within
    (p : X ⟶ Y) [IsProper p] (hp : p ≫ sY = sX) (k : ℤ)
    (hrule : ProperPushforwardKillsPrincipalDivisor C sX sY p k) {α : CycleGroup C sX k}
    {T : Set X} (hα : IsRationallyEquivalentToZeroWithin C sX k α T) :
    IsRationallyEquivalentToZeroWithin C sY k (properPushforward C sX sY p hp k α)
      (closure (p.base '' T)) := by
  classical
  obtain ⟨J, W, hW, hDim, hLocal, hsub, g, hg⟩ := hα
  -- the index set of the new family: those `j` whose pushforward is again a principal divisor
  set P : J → Prop := fun j ↦ ∃ hT : IsIntegral ((W j).map p).subscheme,
    schemeDeltaDimension C (((W j).map p).subschemeι ≫ sY) = ((k + 1 : ℤ) : EInt) ∧
      ∃ h : (rationalFunctions ((W j).map p).subscheme)ˣ,
        properPushforwardPrincipalDivisor C sX sY p (W j) (hW j) (g j) =
          principalDivisorPushforward C sY ((W j).map p) hT h with hP
  have hzero : ∀ j, ¬ P j → properPushforwardPrincipalDivisor C sX sY p (W j) (hW j) (g j) = 0 :=
    fun j hj ↦ (hrule (W j) (hW j) (hDim j) (g j)).resolve_right hj
  choose hT hTDim h heq using fun j : {j // P j} ↦ j.2
  have hsupport (j : {j // P j}) :
      ((((W j.1).map p)).support : Set Y) = closure (p.base '' ((W j.1).support : Set X)) := by
    rw [Scheme.IdealSheafData.support_map]
    rfl
  refine ⟨{j // P j}, fun j ↦ (W j.1).map p, hT, hTDim, ?_, ?_, h, fun y ↦ ?_⟩
  · -- local finiteness of the new family: Stacks 02R2 for the proper, hence spectral, `p`
    have himg : LocallyFinite fun j : J ↦ closure (p.base '' ((W j).support : Set X)) :=
      locallyFinite_closure_image_of_isSpectralMap p.base p.isSpectralMap _ hLocal
    rw [show (fun j : {j // P j} ↦ ((((W j.1).map p)).support : Set Y)) =
        (fun j : J ↦ closure (p.base '' ((W j).support : Set X))) ∘ Subtype.val from
      funext hsupport]
    exact himg.comp_injective Subtype.val_injective
  · -- the carrier: a scheme-theoretic image lies in the closure of the image of the carrier
    intro j
    rw [hsupport j]
    exact closure_mono (Set.image_mono (hsub j.1))
  · -- the coefficient identity, as in the reduction of Stacks 02S2
    have hpush : (properPushforward C sX sY p hp k α).1 y =
        ∑ᶠ j : J, properPushforwardPrincipalDivisor C sX sY p (W j) (hW j) (g j) y := by
      refine algebraicCycle_map_finsum_apply p _ _ (fun j ↦ ((W j).support : Set X)) hLocal
        (fun j ↦ principalDivisorPushforward C sX (W j) (hW j) (g j))
        (fun j ↦ support_principalDivisorPushforward_subset C sX (W j) (hW j) (g j)) α.1
        (fun x ↦ hg x) y
    rw [hpush]
    unfold principalDivisorFamilyCoefficient
    simp only [← heq]
    rw [finsum_subtype_eq_finsum_cond
      (f := fun j : J ↦ properPushforwardPrincipalDivisor C sX sY p (W j) (hW j) (g j) y) P]
    refine finsum_congr fun j ↦ ?_
    by_cases hj : P j
    · have _ : Unique (P j) := ⟨⟨hj⟩, fun _ ↦ rfl⟩
      rw [finsum_unique]
    · have _ : IsEmpty (P j) := ⟨hj⟩
      rw [finsum_of_isEmpty, hzero j hj]
      rfl

/-- **The reduction of Stacks 02S2 to its one-subscheme case, with the carrier retained.** The
case `T = Set.univ` of the carried statement above: the pushforward of a cycle rationally
equivalent to zero is rationally equivalent to zero within the closure of the image of `p`. -/
theorem properPushforward_isRationallyEquivalentToZeroWithin_of_killsPrincipalDivisor
    (p : X ⟶ Y) [IsProper p] (hp : p ≫ sY = sX) (k : ℤ)
    (hrule : ProperPushforwardKillsPrincipalDivisor C sX sY p k) {α : CycleGroup C sX k}
    (hα : IsRationallyEquivalentToZero C sX k α) :
    IsRationallyEquivalentToZeroWithin C sY k (properPushforward C sX sY p hp k α)
      (closure (Set.range p.base)) := by
  have h := properPushforward_isRationallyEquivalentToZeroWithin_of_killsPrincipalDivisor_of_within
    C sX sY p hp k hrule ((isRationallyEquivalentToZeroWithin_univ_iff C sX k α).2 hα)
  rwa [Set.image_univ] at h

/-- **Along a closed immersion, a pushed-forward rational equivalence to zero is witnessed inside
the image.** This carries no hypothesis: Stacks 02S2 for a closed immersion is the already-proved
`Stacks.Chow.properPushforwardKillsPrincipalDivisor_of_isClosedImmersion`, and the image of a
closed immersion is closed, so the closure in
`Stacks.Chow.properPushforward_isRationallyEquivalentToZeroWithin_of_killsPrincipalDivisor` may be
dropped. -/
theorem properPushforward_isRationallyEquivalentToZeroWithin_of_isClosedImmersion
    (p : X ⟶ Y) [IsClosedImmersion p] (hp : p ≫ sY = sX) (k : ℤ) {α : CycleGroup C sX k}
    (hα : IsRationallyEquivalentToZero C sX k α) :
    IsRationallyEquivalentToZeroWithin C sY k (properPushforward C sX sY p hp k α)
      (Set.range p.base) := by
  have hwithin := properPushforward_isRationallyEquivalentToZeroWithin_of_killsPrincipalDivisor
    C sX sY p hp k (properPushforwardKillsPrincipalDivisor_of_isClosedImmersion p C sX sY hp k) hα
  rwa [p.isClosedEmbedding.isClosed_range.closure_eq] at hwithin

/-- **Along a closed immersion, a rational equivalence carried by a closed set is pushed forward
to one carried by its image.** The image of a closed set under a closed immersion is closed, so
the closure in the carried reduction of Stacks 02S2 above may be dropped; Stacks 02S2 for a closed
immersion is proved outright, so no hypothesis is carried.

This is the direction Stacks 0B73 uses against
`Stacks.Chow.isRationallyEquivalentToZeroWithin_of_properPushforward`: a rational equivalence
produced inside a divisor is pushed into the ambient scheme and must stay inside that divisor. -/
theorem properPushforward_isRationallyEquivalentToZeroWithin_of_isClosedImmersion_of_within
    (p : X ⟶ Y) [IsClosedImmersion p] (hp : p ≫ sY = sX) (k : ℤ) {α : CycleGroup C sX k}
    {T : Set X} (hT : IsClosed T) (hα : IsRationallyEquivalentToZeroWithin C sX k α T) :
    IsRationallyEquivalentToZeroWithin C sY k (properPushforward C sX sY p hp k α)
      (p.base '' T) := by
  have h := properPushforward_isRationallyEquivalentToZeroWithin_of_killsPrincipalDivisor_of_within
    C sX sY p hp k (properPushforwardKillsPrincipalDivisor_of_isClosedImmersion p C sX sY hp k) hα
  rwa [(p.isClosedEmbedding.isClosedMap T hT).closure_eq] at h

/-! ### Stacks 02RZ -/

/-- **Stacks 02RZ.** Rational equivalences on a locally finite family of closed subschemes of `X`
may be summed: a cycle whose coefficients are the locally finite sum of the coefficients of the
pushforwards of cycles `a i` on the closed subschemes `T i`, each rationally equivalent to zero, is
itself rationally equivalent to zero.

The pushforward along the closed immersion `(T i).subschemeι` of a rational equivalence to zero is
witnessed inside the image of that immersion, which is `(T i).support`
(`Scheme.IdealSheafData.range_subschemeι`); the family of those supports is locally finite by
hypothesis, so the combined family of witnesses is locally finite and
`Stacks.Chow.rationallyEquivalentToZero_finsum` applies.

Carries no hypothesis of Stacks 02S2: see
`Stacks.Chow.properPushforward_isRationallyEquivalentToZeroWithin_of_isClosedImmersion`. -/
theorem rationallyEquivalentToZero_finsum_of_closedSupports (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (k : ℤ) {I : Type u} (T : I → X.IdealSheafData)
    (hT : LocallyFinite fun i ↦ ((T i).support : Set X))
    (a : ∀ i, CycleGroup C ((T i).subschemeι ≫ p) k)
    (ha : ∀ i, IsRationallyEquivalentToZero C ((T i).subschemeι ≫ p) k (a i))
    {α : CycleGroup C p k}
    (hα : ∀ x : X, α.1 x = ∑ᶠ i : I,
      (properPushforward C ((T i).subschemeι ≫ p) p (T i).subschemeι rfl k (a i)).1 x) :
    IsRationallyEquivalentToZero C p k α := by
  refine rationallyEquivalentToZero_finsum C p k
    (fun i ↦ properPushforward C ((T i).subschemeι ≫ p) p (T i).subschemeι rfl k (a i))
    (fun i ↦ ((T i).support : Set X)) hT (fun i ↦ ?_) hα
  have hwithin := properPushforward_isRationallyEquivalentToZeroWithin_of_isClosedImmersion
    C ((T i).subschemeι ≫ p) p (T i).subschemeι rfl k (ha i)
  rwa [Scheme.IdealSheafData.range_subschemeι] at hwithin

/-- The pushforward of a cycle on a closed subscheme `T ⊆ X` is supported on `T`. Away from
`T.support` the fibre of `T.subschemeι` is empty, so the locally finite sum computing the
coefficient of the pushforward there is empty; the image of `T.subschemeι` is `T.support` by
`Scheme.IdealSheafData.range_subschemeι`. -/
private theorem support_properPushforward_subschemeι_subset (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (k : ℤ) (T : X.IdealSheafData)
    (c : CycleGroup C (T.subschemeι ≫ p) k) :
    Function.support (properPushforward C (T.subschemeι ≫ p) p T.subschemeι rfl k c).1 ⊆
      (T.support : Set X) := by
  rw [← T.range_subschemeι]
  intro x hx
  by_contra hnx
  refine hx ?_
  have hempty : T.subschemeι.base ⁻¹' {x} = (∅ : Set T.subscheme) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    exact fun hz ↦ hnx ⟨z, hz⟩
  rw [properPushforward_apply, hempty, finsum_mem_empty]

/-- **Stacks 02RZ, two-sided form.** Rational equivalences on a locally finite family of closed
subschemes of `X` may be summed: if cycles `a i` and `b i` on the closed subschemes `T i` are
rationally equivalent for each `i`, and the cycles `α`, `β` on `X` are coefficientwise the locally
finite sums of the pushforwards of the `a i` and of the `b i`, then `α` and `β` are rationally
equivalent on `X`.

Both locally finite sums have finite support at each point, because the pushforward of a cycle on
`T i` is supported on `(T i).support` and the family of those supports is locally finite. So they
may be subtracted termwise, which exhibits `α - β` as the locally finite sum of the pushforwards of
the `a i - b i`, each rationally equivalent to zero, and
`Stacks.Chow.rationallyEquivalentToZero_finsum_of_closedSupports` applies. -/
@[stacks 02RZ]
theorem rationallyEquivalent_finsum_of_closedSupports (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (k : ℤ) {I : Type u} (T : I → X.IdealSheafData)
    (hT : LocallyFinite fun i ↦ ((T i).support : Set X))
    (a b : ∀ i, CycleGroup C ((T i).subschemeι ≫ p) k)
    (hab : ∀ i, RationallyEquivalent C ((T i).subschemeι ≫ p) k (a i) (b i))
    {α β : CycleGroup C p k}
    (hα : ∀ x : X, α.1 x = ∑ᶠ i : I,
      (properPushforward C ((T i).subschemeι ≫ p) p (T i).subschemeι rfl k (a i)).1 x)
    (hβ : ∀ x : X, β.1 x = ∑ᶠ i : I,
      (properPushforward C ((T i).subschemeι ≫ p) p (T i).subschemeι rfl k (b i)).1 x) :
    RationallyEquivalent C p k α β := by
  change IsRationallyEquivalentToZero C p k (α - β)
  refine rationallyEquivalentToZero_finsum_of_closedSupports C p k T hT (fun i ↦ a i - b i)
    (fun i ↦ hab i) fun x ↦ ?_
  have hfin (c : ∀ i, CycleGroup C ((T i).subschemeι ≫ p) k) : (Function.support fun i : I ↦
      (properPushforward C ((T i).subschemeι ≫ p) p (T i).subschemeι rfl k (c i)).1 x).Finite :=
    finite_support_of_locallyFinite _ hT
      (fun i ↦ (properPushforward C ((T i).subschemeι ≫ p) p (T i).subschemeι rfl k (c i)).1)
      (fun i ↦ support_properPushforward_subschemeι_subset C p k (T i) (c i)) x
  have hsub : (α - β).1 x = α.1 x - β.1 x := rfl
  rw [hsub, hα x, hβ x, ← finsum_sub_distrib (hfin a) (hfin b)]
  refine finsum_congr fun i ↦ ?_
  rw [properPushforward_sub]
  rfl

end Stacks.Chow

end
