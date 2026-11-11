module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.ProperPushforwardDescent
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinityPresentation

/-!
# The Gysin class at infinity commutes with every bivariant class over the base

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `b : W ⟶ 𝐏¹_X` be proper and an isomorphism over the affine chart
`𝐀¹_X`, and let `C ∈ A⁰(W_∞ ⟶ X)` be the class of Stacks 0F9J. **Stacks 0FAS** says that for
every morphism `fY : Y ⟶ X` locally of finite type and every `c ∈ A^p(Y ⟶ X)` one has

  `C ∘ c = c ∘ C`   in   `A^p(W_∞ ×_X Y ⟶ X)`,

which by Remark 0FA2 is exactly the assertion that `C` and `c` *commute*.

This file reduces Stacks 0FAS, for an abstract class at infinity given with a presentation of
its cap operation, to the two naturality steps of the source's proof. It does not carry the tag:
the unconditional Stacks 0FAS, for the canonical class `Stacks.Chow.gysinAtInfinityClass`, is
`Stacks.Chow.GysinAtInfinity.gysinAtInfinityClass_comp_comm` (the displayed equation) and
`Stacks.Chow.gysinAtInfinityClass_bivariantCommute` (the form of Remark 0FA2), with the version
for a nonhomogeneous `c ∈ A^*(Y ⟶ X)`
`Stacks.Chow.nonhomogeneousBivariantTransport_compositeOfInvertible_gysinAtInfinityClass`.

## Main results

* `Stacks.Chow.gysinAtInfinity_bivariantCommute` — the reduction of Stacks 0FAS: `C` and `c`
  commute, in the sense of `Stacks.Chow.BivariantCommute` (the repository's Stacks 0FA2), given a
  presentation of `C` and the two naturality steps.
* `Stacks.Chow.gysinAtInfinity_commuteCompositeCap_eq` — the same reduction in the displayed form
  of the tag: the cap operations of the two composites `res(C) ∘ c` and `res(c) ∘ C` agree under the
  canonical identification `W_∞ ×_X Y ≅ Y ×_X W_∞`.
* `Stacks.Chow.gysinAtInfinity_bivariantCommute_zero` — the two naturality hypotheses are
  satisfiable: for the zero class of `A^p(Y ⟶ X)` they hold for every class at infinity and
  every presentation of it, so they are not jointly contradictory and the carrier above is not
  vacuous for that reason.

## Implementation notes

### How the objects of the tag are spelled

`A^p(Y ⟶ X)` is `Stacks.Chow.BivariantClass C G (fY ≫ f) f fY rfl p` (Stacks 0B76), stated
against a `Stacks.Chow.GysinSystem`. `W_∞` is
`Stacks.Chow.modificationFibreAtInfinity f b = W ×_{𝐏¹_X} X`, the inverse image of the divisor at
infinity, and `W_∞ ⟶ X` is `Stacks.Chow.modificationProjectionAtInfinity f b`; `C` is the
`bivariantClass` field of `Stacks.Chow.GysinAtInfinityData` (Stacks 0F9J). The composite
`C ∘ c = c ∘ C` is read through `Stacks.Chow.BivariantCommute`, the repository's rendering of
Remark 0FA2, whose equivalence with the equality of the two composites is
`Stacks.Chow.bivariantCommute_iff_commuteCompositeCap_eq`; the second main result above is the
tag's own equation obtained from that equivalence.

### Why the construction of Stacks 0F9J is a hypothesis

The source proves Stacks 0FAS *from the construction* of `C`: choose `β ∈ CH_{k+1}(W)`
restricting over `𝐀¹_X` to the flat pullback of `α`, then `c ∩ β` is a lift of `c ∩ α` and
`i_{Y,∞}^*(c ∩ β) = c ∩ i_\infty^*β` because `c` is a bivariant class. The class `C` alone does
not suffice: `Stacks.Chow.GysinAtInfinityData` records the class and its pushforward identity,
and that identity does not determine the class, since `i_{∞,*}` is not injective — see
`Stacks.Chow.GysinAtInfinityData.bivariantClass_eq_of_injective`. So the hypothesis here is a
`Stacks.Chow.GysinAtInfinityCapPresentation`: the factorisation `C ∩ - = i_∞^* ∘ lift` of the
construction, with the two factors as data.

### The two hypotheses, and why neither is the conclusion

Beyond the presentation there are exactly two hypotheses, one for each factor, and they are the
two steps of the source's proof:

* `hlift`: the lift is natural under `c`, i.e. `c ∩ β` is a lift of `c ∩ α`. In the source this
  holds because `β` restricts over `𝐀¹_X` to the flat pullback of `α` and `c` commutes with flat
  pullback (Stacks 0B76 (2)). That restriction property is *not* recorded by
  `Stacks.Chow.gysinCapOfLift`, which takes the lift as bare data, so it cannot be derived here;
  it is Stacks 42.14.2 and 42.19.3 (Stacks 02RC, 02RX) that make the lift exist and be unique up
  to the fibre at infinity.
* `hgysinStep`: the Gysin map of the divisor at infinity is natural under `c`. This is
  condition (3) of Stacks 0B76 for `c`, i.e. the field
  `Stacks.Chow.BivariantClass.gysin_naturality`, instantiated at the divisor at infinity. It is
  a hypothesis rather than an application of that field only because the instantiation needs the
  identification of the base change of a zero scheme with the zero scheme of the pulled-back
  section — **Stacks 0B6Y** — which this repository does not have; see the docstring of
  `Stacks.Chow.GysinSystem.onChow`.

Neither hypothesis is the conclusion in disguise. `hlift` is a statement about `lift`, a map into
`CH_{k+1}(W ×_X T)`, and `hgysinStep` a statement about the Gysin step, a map out of it; the
conclusion is about their composite `C ∩ -`, a map into `CH_k(W_∞ ×_X T)`. The Gysin step is not
injective — that is precisely why Stacks 0F9J needs Remark 42.29.6 to be well defined — so
`hgysinStep` cannot be recovered from the conclusion, and `hlift` concerns a group the conclusion
never mentions. Dropping either leaves the conclusion unprovable: `hlift` alone says nothing
about how `c` interacts with `i_∞^*`, and `hgysinStep` alone says nothing about how it interacts
with the choice of lift.

### The two comparison isomorphisms

The cap operation lands in the *chosen* categorical fibre product, so `C ∩ (c ∩ α)` lives on
`W_∞ ×_X (Y ×_X T)` and `c ∩ (C ∩ α)` on `Y ×_X (W_∞ ×_X T)`; likewise one degree up on the
`W`-level fibre products. `Stacks.Chow.commuteComparisonHom` is the isomorphism between them, and
`Stacks.Chow.commuteCapTransport` below is `c ∩ -` read through it, which is the form in which
the two hypotheses are stated. Both comparisons are isomorphisms, so pushing forward along them
needs only the isomorphism case of Stacks 02S2, namely
`Stacks.Chow.chowPushforwardOfIso`, and carries no hypothesis.

## References

* [Stacks Project, Tag 0FAS](https://stacks.math.columbia.edu/tag/0FAS)
* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0FA2](https://stacks.math.columbia.edu/tag/0FA2)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Transport of a cap operation across the comparison of two iterated fibre products -/

section Transport

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (fY : Y ⟶ X) [LocallyOfFiniteType fY] (f₁ : Z ⟶ X)
  [LocallyOfFiniteType f₁] (p : ℤ) (c : BivariantClass C G (fY ≫ sX) sX fY rfl p)

/-- The cap operation of `c ∈ A^p(Y ⟶ X)` at the test scheme `Z ×_X T ⟶ X`, read on the fibre
products taken in the other order: it lands on `Y ×_X (Z ×_X T)` and is pushed forward along the
comparison isomorphism `Stacks.Chow.commuteComparisonHom` to `Z ×_X (Y ×_X T)`.

This is the shape in which the two naturality hypotheses of Stacks 0FAS are stated: with `Z = W`
for the lift and `Z = W_∞` for the Gysin step, both sides of each hypothesis then live on a
base change of the same scheme. -/
def commuteCapTransport {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ) :
    chowGroup C (pullback.fst f₁ t ≫ (f₁ ≫ sX)) k →+
      chowGroup C (pullback.fst f₁ (pullback.fst fY t ≫ fY) ≫ (f₁ ≫ sX)) (k - p) :=
  (chowPushforwardOfIso C (pullback.fst fY (pullback.fst f₁ t ≫ f₁) ≫ (fY ≫ sX))
      (pullback.fst f₁ (pullback.fst fY t ≫ fY) ≫ (f₁ ≫ sX)) (commuteComparisonHom fY f₁ t)
      (commuteComparisonHom_comp_structureMorphism C sX fY f₁ t) (k - p)).comp
    ((c.cap (pullback.fst f₁ t ≫ f₁) k).comp
      (chowGroupCongr C (Category.assoc (pullback.fst f₁ t) f₁ sX).symm k).toAddMonoidHom)

/-- The transported cap operation, read on an element. -/
theorem commuteCapTransport_apply {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ)
    (x : chowGroup C (pullback.fst f₁ t ≫ (f₁ ≫ sX)) k) :
    commuteCapTransport C G sX fY f₁ p c t k x =
      chowPushforwardOfIso C (pullback.fst fY (pullback.fst f₁ t ≫ f₁) ≫ (fY ≫ sX))
        (pullback.fst f₁ (pullback.fst fY t ≫ fY) ≫ (f₁ ≫ sX)) (commuteComparisonHom fY f₁ t)
        (commuteComparisonHom_comp_structureMorphism C sX fY f₁ t) (k - p)
        (c.cap (pullback.fst f₁ t ≫ f₁) k
          (chowGroupCongr C (Category.assoc (pullback.fst f₁ t) f₁ sX).symm k x)) :=
  rfl

/-- Pushing the transported cap operation back along the comparison isomorphism recovers the cap
operation of `c`: the two comparison morphisms of the two orders are mutually inverse. -/
theorem chowPushforwardOfIso_commuteCapTransport {T : Scheme.{u}} (t : T ⟶ X)
    [LocallyOfFiniteType t] (k : ℤ)
    (x : chowGroup C (pullback.fst f₁ t ≫ (f₁ ≫ sX)) k) :
    chowPushforwardOfIso C (pullback.fst f₁ (pullback.fst fY t ≫ fY) ≫ (f₁ ≫ sX))
        (pullback.fst fY (pullback.fst f₁ t ≫ f₁) ≫ (fY ≫ sX)) (commuteComparisonHom f₁ fY t)
        (commuteComparisonHom_comp_structureMorphism C sX f₁ fY t) (k - p)
        (commuteCapTransport C G sX fY f₁ p c t k x) =
      c.cap (pullback.fst f₁ t ≫ f₁) k
        (chowGroupCongr C (Category.assoc (pullback.fst f₁ t) f₁ sX).symm k x) := by
  rw [commuteCapTransport_apply, chowPushforwardOfIso_comp_apply,
    chowPushforwardOfIso_congr_apply C (pullback.fst fY (pullback.fst f₁ t ≫ f₁) ≫ (fY ≫ sX))
      (pullback.fst fY (pullback.fst f₁ t ≫ f₁) ≫ (fY ≫ sX))
      (commuteComparisonHom fY f₁ t ≫ commuteComparisonHom f₁ fY t)
      (𝟙 (pullback fY (pullback.fst f₁ t ≫ f₁)))
      (commuteComparisonHom_comp_commuteComparisonHom fY f₁ t) _ (Category.id_comp _) (k - p),
    chowPushforwardOfIso_id]

end Transport

/-! ### Stacks 0FAS -/

section Commuting

variable {C : ChowSituation.{u}} {G : GysinSystem C} {X W Y : Scheme.{u}} {f : X ⟶ C.S}
  [LocallyOfFiniteType f] {b : W ⟶ projectiveLineProduct f} [IsProper b]
  {hA : IsIso (pullback.snd b (projectiveLineAffineChart f))}
  [LocallyOfFiniteType (modificationProjection f b)]
  [LocallyOfFiniteType (modificationProjectionAtInfinity f b)]
  {D : GysinAtInfinityData C G f b hA} (P : GysinAtInfinityCapPresentation C G f b hA D)
  (fY : Y ⟶ X) [LocallyOfFiniteType fY] (p : ℤ)
  (c : BivariantClass C G (fY ≫ f) f fY rfl p)

/-- A reduction of Stacks 0FAS to the construction of Stacks 0F9J and its two naturality
properties under `c`. The unconditional Stacks 0FAS, for the canonical class
`Stacks.Chow.gysinAtInfinityClass`, is `Stacks.Chow.gysinAtInfinityClass_bivariantCommute`.

In the setting of Stacks 0F9J, let `fY : Y ⟶ X` be locally of finite type and let
`c ∈ A^p(Y ⟶ X)`. Then the canonical class `C ∈ A⁰(W_∞ ⟶ X)` and `c` commute, in the sense of
Remark 0FA2: `C ∩ (c ∩ α) = c ∩ (C ∩ α)` for every `α ∈ CH_k(T)` and every test scheme
`t : T ⟶ X` locally of finite type, the two sides being compared by the canonical isomorphism
`W_∞ ×_X (Y ×_X T) ≅ Y ×_X (W_∞ ×_X T)`.

The hypotheses are the source's own proof steps, and none of them is the conclusion:

* `P`, a `Stacks.Chow.GysinAtInfinityCapPresentation`, is the construction of Stacks 0F9J:
  `C ∩ - = i_∞^* ∘ lift`. It is needed because the pushforward identity recorded by
  `Stacks.Chow.GysinAtInfinityData` does not determine `C`.
* `hlift` is "`c ∩ β` is a lift of `c ∩ α`", a statement about the lift alone.
* `hgysinStep` is condition (3) of Stacks 0B76 for `c` at the divisor at infinity, a statement
  about the Gysin step alone; it is `Stacks.Chow.BivariantClass.gysin_naturality` modulo the
  zero-scheme base-change identification of Stacks 0B6Y, which this repository lacks.

See the implementation notes of `StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinityCommuting`. -/
theorem gysinAtInfinity_bivariantCommute
    (hlift : ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ)
        (α : chowGroup C (t ≫ f) k),
      P.lift (pullback.fst fY t ≫ fY) (k - p)
          (chowGroupCongr C (Category.assoc (pullback.fst fY t) fY f).symm (k - p)
            (c.cap t k α)) =
        chowGroupDegreeEquiv C (modificationBaseChangeOver f b (pullback.fst fY t ≫ fY))
          (by ring : k + 1 - p = k - p + 1)
          (commuteCapTransport C G f fY (modificationProjection f b) p c t (k + 1)
            (P.lift t k α)))
    (hgysinStep : ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ)
        (β : chowGroup C (modificationBaseChangeOver f b t) (k + 1)),
      P.gysinStep (pullback.fst fY t ≫ fY) (k - p)
          (chowGroupDegreeEquiv C (modificationBaseChangeOver f b (pullback.fst fY t ≫ fY))
            (by ring : k + 1 - p = k - p + 1)
            (commuteCapTransport C G f fY (modificationProjection f b) p c t (k + 1) β)) =
        commuteCapTransport C G f fY (modificationProjectionAtInfinity f b) p c t k
          (P.gysinStep t k β)) :
    BivariantCommute C G f (modificationProjectionAtInfinity f b) fY 0 p D.bivariantClass c := by
  intro T t _ k α
  rw [bivariantIteratedCap_apply, bivariantIteratedCap_apply,
    P.cap_eq (pullback.fst fY t ≫ fY) (k - p), P.cap_eq t k α,
    ← chowGroupDegreeEquiv_chowPushforwardOfIso, hlift t k α, hgysinStep t k (P.lift t k α),
    chowPushforwardOfIso_commuteCapTransport, chowGroupCongr_chowGroupDegreeEquiv]
  exact c.cap_transport_eq (pullback.fst (modificationProjectionAtInfinity f b) t ≫
    modificationProjectionAtInfinity f b) (sub_zero k).symm (sub_zero (k - p)).symm (by ring) _

/-- The hypotheses of `Stacks.Chow.gysinAtInfinity_bivariantCommute` are satisfiable, so the
theorem is not vacuous: for the zero class of `A^p(Y ⟶ X)` both naturality hypotheses hold for
every class at infinity and every presentation of it, and the conclusion follows. -/
theorem gysinAtInfinity_bivariantCommute_zero
    (Q : GysinAtInfinityCapPresentation C G f b hA D) :
    BivariantCommute C G f (modificationProjectionAtInfinity f b) fY 0 p D.bivariantClass 0 := by
  refine gysinAtInfinity_bivariantCommute Q fY p 0 ?_ ?_ <;> intro T t _ k x <;>
    simp [commuteCapTransport_apply, BivariantClass.zero_cap]

/-- The reduction of Stacks 0FAS in the displayed form of the tag: `C ∘ c = c ∘ C` in
`A^p(W_∞ ×_X Y ⟶ X)`, read on cap operations, for a presented class at infinity satisfying the two
naturality steps. The unconditional statement, for the canonical class, is
`Stacks.Chow.GysinAtInfinity.gysinAtInfinityClass_comp_comm`.

This is `Stacks.Chow.gysinAtInfinity_bivariantCommute` pushed through the equivalence of Remark
0FA2, `Stacks.Chow.bivariantCommute_iff_commuteCompositeCap_eq`: the cap operations of the two
composites `res(C) ∘ c` and `res(c) ∘ C` agree under the canonical identification
`W_∞ ×_X Y ≅ Y ×_X W_∞` of their sources and the equality `0 + p = p + 0` of their degrees. The
hypothesis `hgys` is the isomorphism case of Stacks 02TA for the Gysin system, which
`Stacks.Chow.bivariantRestriction` (Stacks 0F9Z) needs in order to be a bivariant class; the
Stacks 02S2 hypothesis of `Stacks.Chow.bivariantCompositeCap` is discharged by
`Stacks.Chow.properPushforwardDescends`. -/
theorem gysinAtInfinity_commuteCompositeCap_eq (hgys : G.IsNaturalUnderBaseChangeIso)
    (hlift : ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ)
        (α : chowGroup C (t ≫ f) k),
      P.lift (pullback.fst fY t ≫ fY) (k - p)
          (chowGroupCongr C (Category.assoc (pullback.fst fY t) fY f).symm (k - p)
            (c.cap t k α)) =
        chowGroupDegreeEquiv C (modificationBaseChangeOver f b (pullback.fst fY t ≫ fY))
          (by ring : k + 1 - p = k - p + 1)
          (commuteCapTransport C G f fY (modificationProjection f b) p c t (k + 1)
            (P.lift t k α)))
    (hgysinStep : ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ)
        (β : chowGroup C (modificationBaseChangeOver f b t) (k + 1)),
      P.gysinStep (pullback.fst fY t ≫ fY) (k - p)
          (chowGroupDegreeEquiv C (modificationBaseChangeOver f b (pullback.fst fY t ≫ fY))
            (by ring : k + 1 - p = k - p + 1)
            (commuteCapTransport C G f fY (modificationProjection f b) p c t (k + 1) β)) =
        commuteCapTransport C G f fY (modificationProjectionAtInfinity f b) p c t k
          (P.gysinStep t k β))
    {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ)
    (α : chowGroup C (t ≫ f) k) :
    chowPushforwardOfIso C
        (pullback.fst (pullback.snd (modificationProjectionAtInfinity f b) fY ≫ fY) t ≫
          (pullback.fst (modificationProjectionAtInfinity f b) fY ≫
            (modificationProjectionAtInfinity f b ≫ f)))
        (pullback.fst (pullback.snd fY (modificationProjectionAtInfinity f b) ≫
            modificationProjectionAtInfinity f b) t ≫
          (pullback.fst fY (modificationProjectionAtInfinity f b) ≫ (fY ≫ f)))
        (compositeComparisonHom (modificationProjectionAtInfinity f b) fY t)
        (compositeComparisonHom_comp_structureMorphism C f
          (modificationProjectionAtInfinity f b) fY t) (k - p - 0)
        (commuteCompositeCap C G f (modificationProjectionAtInfinity f b) fY 0 p
          D.bivariantClass c hgys (properPushforwardDescends C) t k α) =
      chowGroupDegreeEquiv C
        (pullback.fst (pullback.snd fY (modificationProjectionAtInfinity f b) ≫
            modificationProjectionAtInfinity f b) t ≫
          (pullback.fst fY (modificationProjectionAtInfinity f b) ≫ (fY ≫ f)))
        (by ring : k - 0 - p = k - p - 0)
        (commuteCompositeCap C G f fY (modificationProjectionAtInfinity f b) p 0 c
          D.bivariantClass hgys (properPushforwardDescends C) t k α) :=
  (bivariantCommute_iff_commuteCompositeCap_eq C G f (modificationProjectionAtInfinity f b) fY 0 p
      D.bivariantClass c hgys (properPushforwardDescends C)).mp
    (gysinAtInfinity_bivariantCommute P fY p c hlift hgysinStep) t k α

end Commuting

end Stacks.Chow

end
