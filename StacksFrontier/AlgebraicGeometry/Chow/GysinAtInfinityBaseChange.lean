module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinityPresentation

/-!
# The Gysin class at infinity is compatible with base change

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `b : W ⟶ 𝐏¹_X` be proper and an isomorphism over the affine chart
`𝐀¹_X`, and let `C ∈ A⁰(W_∞ ⟶ X)` be the class of Stacks 0F9J. **Stacks 0GUH** says that for a
morphism `q : X' ⟶ X` locally of finite type, with `b' : W' ⟶ 𝐏¹_{X'}` and
`i'_∞ : W'_∞ ⟶ W'` the base changes of `b` and `i_∞`, the class `C' ∈ A⁰(W'_∞ ⟶ X')` constructed
as in Stacks 0F9J using `b'` is the restriction of `C` in the sense of Remark 0F9Z.

## Main definitions

* `Stacks.Chow.modificationBaseChangeComparison` and
  `Stacks.Chow.modificationInfinityBaseChangeComparison` — the canonical identifications
  `W ×_X T ≅ W' ×_{X'} T` and `W_∞ ×_X T ≅ W'_∞ ×_{X'} T` on a test scheme `T ⟶ X'`, obtained
  from the two base-change witnesses by pasting fibre squares.

## Main results

* `Stacks.Chow.gysinAtInfinity_eq_bivariantTransport_bivariantRestriction` — **Stacks 0GUH**: the
  class `C'` equals the restriction of `C` along `q`, transported along the identification
  `W_∞ ×_X X' ≅ W'_∞`. This is an equality of two elements of `A⁰(W'_∞ ⟶ X')`.
* `Stacks.Chow.gysinAtInfinity_baseChange_cap` — the same statement read on cap operations:
  `C' ∩ α = C ∩ α` under the identification of the two base-changed fibres at infinity, which is
  the form the tag's proof produces.
* `Stacks.Chow.gysinAtInfinity_baseChange_cap_iff` — the conclusion is *equivalent* to the
  composite of the two hypotheses `hlift` and `hgysinStep`, which is the precise sense in which
  those two are stronger than the conclusion and neither is the conclusion restated.

## Implementation notes

### How the objects of the tag are spelled

`A⁰(W_∞ ⟶ X)` is `Stacks.Chow.BivariantClass` of degree `0` (Stacks 0B76), stated against a
`Stacks.Chow.GysinSystem`; `C` is the `bivariantClass` field of
`Stacks.Chow.GysinAtInfinityData` (Stacks 0F9J) and `C'` that of a second such datum for `b'`
over `X'`. The restriction of Remark 0F9Z is `Stacks.Chow.bivariantRestriction`, which produces a
class for the *chosen* fibre product `W_∞ ×_X X' ⟶ X'`; `Stacks.Chow.bivariantTransport` then
carries it along the identification of that fibre product with `W'_∞`, so that the two sides of
the conclusion are elements of one and the same group. Both are the library's own constructions:
nothing here defines a second restriction or a second cap operation.

### The base-change witnesses

That `b'` and `i'_∞` are the base changes of `b` and `i_∞` is a hypothesis of the tag, and it is
carried here as explicit data rather than as an existence statement:

* `η : W ×_X X' ≅ W'` over `X'`, with `hη` saying it lies over `X'`;
* `θ : W_∞ ×_X X' ≅ W'_∞` over `X'`, with `hθ` saying the same.

From these the test-scheme level identifications `W ×_X T ≅ W' ×_{X'} T` and
`W_∞ ×_X T ≅ W'_∞ ×_{X'} T` are *constructed*, by pasting
`Stacks.Chow.transportPullbackIso` onto `CategoryTheory.Limits.pullbackLeftPullbackSndIso`; no
further identification is assumed. This is why the properness of `b'` and the isomorphism
property of `b'` over `𝐀¹_{X'}` appear as instance and argument rather than as theorems: they are
part of "let `b'` be the base change", and deriving them is the geometry of Stacks 02S5, not the
content of Stacks 0GUH.

### Why the construction of Stacks 0F9J is a hypothesis

The source's proof of Stacks 0GUH is "immediate from the construction and the fact that a similar
statement holds for flat pullback and `i_∞^*`". The construction is needed: as the implementation
notes of `StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity` record,
`Stacks.Chow.GysinAtInfinityData` carries the class and the identity
`i_{∞,*}(C ∩ α) = i_{0,*}α`, and that identity does not determine the class, because `i_{∞,*}` is
not injective. So both `C` and `C'` come with a `Stacks.Chow.GysinAtInfinityCapPresentation`,
which is the factorisation `C ∩ - = i_∞^* ∘ lift` of Stacks 0F9J with the two factors as data,
and the two hypotheses `hlift` and `hgysinStep` are exactly the source's "similar statement holds
for flat pullback and `i_∞^*`", one for each factor.

Neither hypothesis is the conclusion in disguise: `hlift` is a statement about the lift, a map
into `CH_{k+1}(W ×_X T)`, which the conclusion never mentions, and `hgysinStep` is a statement
about the Gysin step, a map out of that group. Their composite is the conclusion, which is the
source's proof; separately neither gives it, since a lift is determined only up to a class
supported on the fibre at infinity (Stacks 02RX) and the Gysin step is not injective.

## References

* [Stacks Project, Tag 0GUH](https://stacks.math.columbia.edu/tag/0GUH)
* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Pushforward along a composite of isomorphisms -/

/-- Pushforward on Chow groups along a composite of two isomorphisms over the base, presented as
a single isomorphism. -/
theorem chowPushforwardOfIso_comp_eq (C : ChowSituation.{u}) {A B D : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    (sD : D ⟶ C.S) [LocallyOfFiniteType sD] (u : A ⟶ B) [IsIso u] (v : B ⟶ D) [IsIso v]
    (w : A ⟶ D) [IsIso w] (hw : u ≫ v = w) (hu : u ≫ sB = sA) (hv : v ≫ sD = sB)
    (hwb : w ≫ sD = sA) (k : ℤ) (x : chowGroup C sA k) :
    chowPushforwardOfIso C sB sD v hv k (chowPushforwardOfIso C sA sB u hu k x) =
      chowPushforwardOfIso C sA sD w hwb k x := by
  subst hw
  exact chowPushforwardOfIso_comp_apply C sA sB sD u v hu hv k x

/-- The pasting of a base-change witness `θ : A ×_X X' ≅ A'` with `pullbackLeftPullbackSndIso`
lies over the base. -/
private theorem pullbackLeftPullbackSndIso_inv_comp_transport_comp_base (C : ChowSituation.{u})
    {X X' A A' : Scheme.{u}} (f : X ⟶ C.S) (q : X' ⟶ X) (p : A ⟶ X) (p' : A' ⟶ X')
    (θ : pullback p q ≅ A') (hθ : θ.hom ≫ p' = pullback.snd p q) {T : Scheme.{u}} (g : T ⟶ X') :
    (pullbackLeftPullbackSndIso p q g).inv ≫
        (transportPullbackIso (pullback.snd p q) p' θ hθ g).hom ≫
          (pullback.fst p' g ≫ p' ≫ q ≫ f) =
      pullback.fst p (g ≫ q) ≫ p ≫ f := by
  rw [transportPullbackIso_hom_comp_base C (pullback.fst p q ≫ (p ≫ f)) (p' ≫ (q ≫ f)) (q ≫ f)
      (pullback.snd p q) (pullbackSnd_comp_structureMorphism_eq C (p ≫ f) f p rfl q) p' rfl θ hθ g]
  simp

/-! ### The comparison of a base change of the modification with the base-changed modification -/

section Comparison

variable (C : ChowSituation.{u}) {X W X' W' : Scheme.{u}} (f : X ⟶ C.S)
  (b : W ⟶ projectiveLineProduct f) (q : X' ⟶ X) (b' : W' ⟶ projectiveLineProduct (q ≫ f))

/-- The identification `W ×_X T ≅ W' ×_{X'} T` of the two base changes of the modification by a
test scheme `g : T ⟶ X'`, obtained from a witness `η : W ×_X X' ≅ W'` that `W'` is the base
change of `W`: paste `W ×_X T ≅ (W ×_X X') ×_{X'} T` with the transport of `η`. -/
def modificationBaseChangeComparison
    (η : pullback (modificationProjection f b) q ≅ W')
    (hη : η.hom ≫ modificationProjection (q ≫ f) b' =
      pullback.snd (modificationProjection f b) q)
    {T : Scheme.{u}} (g : T ⟶ X') :
    modificationBaseChange f b (g ≫ q) ⟶ modificationBaseChange (q ≫ f) b' g :=
  (pullbackLeftPullbackSndIso (modificationProjection f b) q g).inv ≫
    (transportPullbackIso (pullback.snd (modificationProjection f b) q)
      (modificationProjection (q ≫ f) b') η hη g).hom

/-- The identification of the two base changes of the modification is an isomorphism, being a
composite of two isomorphisms. -/
instance isIso_modificationBaseChangeComparison
    (η : pullback (modificationProjection f b) q ≅ W')
    (hη : η.hom ≫ modificationProjection (q ≫ f) b' =
      pullback.snd (modificationProjection f b) q)
    {T : Scheme.{u}} (g : T ⟶ X') :
    IsIso (modificationBaseChangeComparison C f b q b' η hη g) := by
  rw [modificationBaseChangeComparison]
  infer_instance

/-- The identification of the two base changes of the modification lies over the base. -/
theorem modificationBaseChangeComparison_comp_base
    (η : pullback (modificationProjection f b) q ≅ W')
    (hη : η.hom ≫ modificationProjection (q ≫ f) b' =
      pullback.snd (modificationProjection f b) q)
    {T : Scheme.{u}} (g : T ⟶ X') :
    modificationBaseChangeComparison C f b q b' η hη g ≫
        modificationBaseChangeOver (q ≫ f) b' g =
      modificationBaseChangeOver f b (g ≫ q) := by
  rw [modificationBaseChangeComparison, Category.assoc]
  exact pullbackLeftPullbackSndIso_inv_comp_transport_comp_base C f q _ _ η hη g

/-- The identification `W_∞ ×_X T ≅ W'_∞ ×_{X'} T` of the two base changes of the fibre at
infinity by a test scheme `g : T ⟶ X'`, obtained from a witness `θ : W_∞ ×_X X' ≅ W'_∞` that
`W'_∞` is the base change of `W_∞`. -/
def modificationInfinityBaseChangeComparison
    (θ : pullback (modificationProjectionAtInfinity f b) q ≅
      modificationFibreAtInfinity (q ≫ f) b')
    (hθ : θ.hom ≫ modificationProjectionAtInfinity (q ≫ f) b' =
      pullback.snd (modificationProjectionAtInfinity f b) q)
    {T : Scheme.{u}} (g : T ⟶ X') :
    pullback (modificationProjectionAtInfinity f b) (g ≫ q) ⟶
      pullback (modificationProjectionAtInfinity (q ≫ f) b') g :=
  (pullbackLeftPullbackSndIso (modificationProjectionAtInfinity f b) q g).inv ≫
    (transportPullbackIso (pullback.snd (modificationProjectionAtInfinity f b) q)
      (modificationProjectionAtInfinity (q ≫ f) b') θ hθ g).hom

/-- The identification of the two base changes of the fibre at infinity is an isomorphism, being a
composite of two isomorphisms. -/
instance isIso_modificationInfinityBaseChangeComparison
    (θ : pullback (modificationProjectionAtInfinity f b) q ≅
      modificationFibreAtInfinity (q ≫ f) b')
    (hθ : θ.hom ≫ modificationProjectionAtInfinity (q ≫ f) b' =
      pullback.snd (modificationProjectionAtInfinity f b) q)
    {T : Scheme.{u}} (g : T ⟶ X') :
    IsIso (modificationInfinityBaseChangeComparison C f b q b' θ hθ g) := by
  rw [modificationInfinityBaseChangeComparison]
  infer_instance

/-- The identification of the two base changes of the fibre at infinity lies over the base. -/
theorem modificationInfinityBaseChangeComparison_comp_base
    (θ : pullback (modificationProjectionAtInfinity f b) q ≅
      modificationFibreAtInfinity (q ≫ f) b')
    (hθ : θ.hom ≫ modificationProjectionAtInfinity (q ≫ f) b' =
      pullback.snd (modificationProjectionAtInfinity f b) q)
    {T : Scheme.{u}} (g : T ⟶ X') :
    modificationInfinityBaseChangeComparison C f b q b' θ hθ g ≫
        modificationInfinityBaseChangeOver (q ≫ f) b' g =
      modificationInfinityBaseChangeOver f b (g ≫ q) := by
  rw [modificationInfinityBaseChangeComparison, Category.assoc]
  exact pullbackLeftPullbackSndIso_inv_comp_transport_comp_base C f q _ _ θ hθ g

/-- The comparison of the two base changes of the fibre at infinity is the composite of the
pasting isomorphism with the transport of `θ`: the form in which the pushforward along it splits
into the restriction step of Remark 0F9Z and the transport step. -/
theorem modificationInfinityBaseChangeComparison_eq
    (θ : pullback (modificationProjectionAtInfinity f b) q ≅
      modificationFibreAtInfinity (q ≫ f) b')
    (hθ : θ.hom ≫ modificationProjectionAtInfinity (q ≫ f) b' =
      pullback.snd (modificationProjectionAtInfinity f b) q)
    {T : Scheme.{u}} (g : T ⟶ X') :
    (pullbackLeftPullbackSndIso (modificationProjectionAtInfinity f b) q g).inv ≫
        (transportPullbackIso (pullback.snd (modificationProjectionAtInfinity f b) q)
          (modificationProjectionAtInfinity (q ≫ f) b') θ hθ g).hom =
      modificationInfinityBaseChangeComparison C f b q b' θ hθ g :=
  rfl

end Comparison

/-! ### Stacks 0GUH -/

section BaseChange

variable {C : ChowSituation.{u}} {G : GysinSystem C} {X W X' W' : Scheme.{u}} {f : X ⟶ C.S}
  [LocallyOfFiniteType f] {b : W ⟶ projectiveLineProduct f} [IsProper b]
  {hA : IsIso (pullback.snd b (projectiveLineAffineChart f))}
  [LocallyOfFiniteType (modificationProjection f b)]
  [LocallyOfFiniteType (modificationProjectionAtInfinity f b)]
  {D : GysinAtInfinityData C G f b hA} (P : GysinAtInfinityCapPresentation C G f b hA D)
  (q : X' ⟶ X) [LocallyOfFiniteType q]
  {b' : W' ⟶ projectiveLineProduct (q ≫ f)} [IsProper b']
  {hA' : IsIso (pullback.snd b' (projectiveLineAffineChart (q ≫ f)))}
  [LocallyOfFiniteType (modificationProjection (q ≫ f) b')]
  [LocallyOfFiniteType (modificationProjectionAtInfinity (q ≫ f) b')]
  {D' : GysinAtInfinityData C G (q ≫ f) b' hA'}
  (P' : GysinAtInfinityCapPresentation C G (q ≫ f) b' hA' D')
  (η : pullback (modificationProjection f b) q ≅ W')
  (hη : η.hom ≫ modificationProjection (q ≫ f) b' =
    pullback.snd (modificationProjection f b) q)
  (θ : pullback (modificationProjectionAtInfinity f b) q ≅
    modificationFibreAtInfinity (q ≫ f) b')
  (hθ : θ.hom ≫ modificationProjectionAtInfinity (q ≫ f) b' =
    pullback.snd (modificationProjectionAtInfinity f b) q)

/-- **Stacks 0GUH, on cap operations**, conditional on the construction of Stacks 0F9J for both
modifications and its compatibility with base change.

For every test scheme `g : T ⟶ X'` locally of finite type, `C' ∩ α = C ∩ α` after the canonical
identification `W_∞ ×_X T ≅ W'_∞ ×_{X'} T` of the two base changes of the fibre at infinity. This
is the form the source's proof produces; the equality of bivariant classes asserted by the tag is
`Stacks.Chow.gysinAtInfinity_eq_bivariantTransport_bivariantRestriction`. -/
@[stacks 0GUH "on cap operations: given the construction of Stacks 0F9J as a presentation of \
each cap operation by a lift and a Gysin step, and the compatibility of each of those two \
factors with the base change (the source's `a similar statement holds for flat pullback and \
i_infty^*`), the class constructed from the base-changed modification caps as the original one \
does"]
theorem gysinAtInfinity_baseChange_cap
    (hlift : ∀ {T : Scheme.{u}} (g : T ⟶ X') [LocallyOfFiniteType g] (k : ℤ)
        (α : chowGroup C (g ≫ (q ≫ f)) k),
      P'.lift g k α =
        chowPushforwardOfIso C (modificationBaseChangeOver f b (g ≫ q))
          (modificationBaseChangeOver (q ≫ f) b' g)
          (modificationBaseChangeComparison C f b q b' η hη g)
          (modificationBaseChangeComparison_comp_base C f b q b' η hη g) (k + 1)
          (P.lift (g ≫ q) k (chowGroupCongr C (Category.assoc g q f).symm k α)))
    (hgysinStep : ∀ {T : Scheme.{u}} (g : T ⟶ X') [LocallyOfFiniteType g] (k : ℤ)
        (β : chowGroup C (modificationBaseChangeOver f b (g ≫ q)) (k + 1)),
      P'.gysinStep g k
          (chowPushforwardOfIso C (modificationBaseChangeOver f b (g ≫ q))
            (modificationBaseChangeOver (q ≫ f) b' g)
            (modificationBaseChangeComparison C f b q b' η hη g)
            (modificationBaseChangeComparison_comp_base C f b q b' η hη g) (k + 1) β) =
        chowPushforwardOfIso C (modificationInfinityBaseChangeOver f b (g ≫ q))
          (modificationInfinityBaseChangeOver (q ≫ f) b' g)
          (modificationInfinityBaseChangeComparison C f b q b' θ hθ g)
          (modificationInfinityBaseChangeComparison_comp_base C f b q b' θ hθ g) k
          (P.gysinStep (g ≫ q) k β))
    {T : Scheme.{u}} (g : T ⟶ X') [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ (q ≫ f)) k) :
    D'.bivariantClass.cap g k α =
      chowPushforwardOfIso C (modificationInfinityBaseChangeOver f b (g ≫ q))
        (modificationInfinityBaseChangeOver (q ≫ f) b' g)
        (modificationInfinityBaseChangeComparison C f b q b' θ hθ g)
        (modificationInfinityBaseChangeComparison_comp_base C f b q b' θ hθ g) (k - 0)
        (D.bivariantClass.cap (g ≫ q) k
          (chowGroupCongr C (Category.assoc g q f).symm k α)) := by
  rw [P'.cap_eq g k α, hlift g k α, hgysinStep g k (P.lift (g ≫ q) k _),
    P.cap_eq (g ≫ q) k (chowGroupCongr C (Category.assoc g q f).symm k α),
    chowGroupDegreeEquiv_chowPushforwardOfIso]

/-- The exact relation between the conclusion of Stacks 0GUH and its two hypotheses: once both
cap operations are presented, the conclusion is *equivalent* to the composite of the two
naturality statements `hlift` and `hgysinStep`.

So the pair `hlift`, `hgysinStep` is strictly stronger than the conclusion — it asserts the
compatibility of each factor separately, where the conclusion asserts it only for the composite —
and neither of them is the conclusion restated: read from left to right this lemma is the only
thing the conclusion gives back, and it mentions the lift and the Gysin step only through their
composite. A lift is determined by the construction of Stacks 0F9J only up to a class supported
on the fibre at infinity (Stacks 02RX), and the Gysin step kills exactly such classes (Remark
42.29.6), so the composite statement is genuinely weaker than the pair. -/
theorem gysinAtInfinity_baseChange_cap_iff {T : Scheme.{u}} (g : T ⟶ X')
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ (q ≫ f)) k) :
    D'.bivariantClass.cap g k α =
        chowPushforwardOfIso C (modificationInfinityBaseChangeOver f b (g ≫ q))
          (modificationInfinityBaseChangeOver (q ≫ f) b' g)
          (modificationInfinityBaseChangeComparison C f b q b' θ hθ g)
          (modificationInfinityBaseChangeComparison_comp_base C f b q b' θ hθ g) (k - 0)
          (D.bivariantClass.cap (g ≫ q) k
            (chowGroupCongr C (Category.assoc g q f).symm k α)) ↔
      P'.gysinStep g k (P'.lift g k α) =
        chowPushforwardOfIso C (modificationInfinityBaseChangeOver f b (g ≫ q))
          (modificationInfinityBaseChangeOver (q ≫ f) b' g)
          (modificationInfinityBaseChangeComparison C f b q b' θ hθ g)
          (modificationInfinityBaseChangeComparison_comp_base C f b q b' θ hθ g) k
          (P.gysinStep (g ≫ q) k
            (P.lift (g ≫ q) k (chowGroupCongr C (Category.assoc g q f).symm k α))) := by
  rw [P'.cap_eq g k α,
    P.cap_eq (g ≫ q) k (chowGroupCongr C (Category.assoc g q f).symm k α),
    ← chowGroupDegreeEquiv_chowPushforwardOfIso, EmbeddingLike.apply_eq_iff_eq]

/-- **Stacks 0GUH.** In the setting of Stacks 0F9J let `q : X' ⟶ X` be locally of finite type and
let `b' : W' ⟶ 𝐏¹_{X'}` and `i'_∞ : W'_∞ ⟶ W'` be the base changes of `b` and `i_∞`. Then the
class `C' ∈ A⁰(W'_∞ ⟶ X')` constructed as in Stacks 0F9J using `b'` is the restriction (Remark
0F9Z) of `C`: it equals `Stacks.Chow.bivariantRestriction` of `C` along `q`, carried along the
identification `W_∞ ×_X X' ≅ W'_∞` by `Stacks.Chow.bivariantTransport`.

The transport is needed only because `Stacks.Chow.bivariantRestriction` produces a class for the
chosen fibre product `W_∞ ×_X X' ⟶ X'`, whereas `C'` is a class for `W'_∞ ⟶ X'`; the tag
identifies the two silently. Both constructions are the library's own.

The hypotheses are the base-change witnesses `η`, `θ`, the construction of Stacks 0F9J for both
modifications, and the compatibility of each of its two factors with the base change; see the
implementation notes of `StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinityBaseChange`. -/
@[stacks 0GUH "given the construction of Stacks 0F9J as a presentation of each cap operation by \
a lift and a Gysin step, and the compatibility of each of those two factors with the base \
change (the source's `a similar statement holds for flat pullback and i_infty^*`), together \
with the isomorphism case of Stacks 02TA for the Gysin system that Stacks 0F9Z needs"]
theorem gysinAtInfinity_eq_bivariantTransport_bivariantRestriction
    (hgys : G.IsNaturalUnderBaseChangeIso)
    (hlift : ∀ {T : Scheme.{u}} (g : T ⟶ X') [LocallyOfFiniteType g] (k : ℤ)
        (α : chowGroup C (g ≫ (q ≫ f)) k),
      P'.lift g k α =
        chowPushforwardOfIso C (modificationBaseChangeOver f b (g ≫ q))
          (modificationBaseChangeOver (q ≫ f) b' g)
          (modificationBaseChangeComparison C f b q b' η hη g)
          (modificationBaseChangeComparison_comp_base C f b q b' η hη g) (k + 1)
          (P.lift (g ≫ q) k (chowGroupCongr C (Category.assoc g q f).symm k α)))
    (hgysinStep : ∀ {T : Scheme.{u}} (g : T ⟶ X') [LocallyOfFiniteType g] (k : ℤ)
        (β : chowGroup C (modificationBaseChangeOver f b (g ≫ q)) (k + 1)),
      P'.gysinStep g k
          (chowPushforwardOfIso C (modificationBaseChangeOver f b (g ≫ q))
            (modificationBaseChangeOver (q ≫ f) b' g)
            (modificationBaseChangeComparison C f b q b' η hη g)
            (modificationBaseChangeComparison_comp_base C f b q b' η hη g) (k + 1) β) =
        chowPushforwardOfIso C (modificationInfinityBaseChangeOver f b (g ≫ q))
          (modificationInfinityBaseChangeOver (q ≫ f) b' g)
          (modificationInfinityBaseChangeComparison C f b q b' θ hθ g)
          (modificationInfinityBaseChangeComparison_comp_base C f b q b' θ hθ g) k
          (P.gysinStep (g ≫ q) k β)) :
    D'.bivariantClass =
      bivariantTransport C G
        (pullback.fst (modificationProjectionAtInfinity f b) q ≫
          (modificationProjectionAtInfinity f b ≫ f))
        (modificationProjectionAtInfinity (q ≫ f) b' ≫ (q ≫ f)) (q ≫ f)
        (pullback.snd (modificationProjectionAtInfinity f b) q)
        (pullbackSnd_comp_structureMorphism_eq C (modificationProjectionAtInfinity f b ≫ f) f
          (modificationProjectionAtInfinity f b) rfl q)
        (modificationProjectionAtInfinity (q ≫ f) b') rfl θ hθ 0 hgys
        (bivariantRestriction C G (modificationProjectionAtInfinity f b ≫ f) f
          (modificationProjectionAtInfinity f b) rfl q 0 hgys D.bivariantClass) := by
  refine eq_of_isBivariantTransport C G
    (pullback.fst (modificationProjectionAtInfinity f b) q ≫
      (modificationProjectionAtInfinity f b ≫ f))
    (modificationProjectionAtInfinity (q ≫ f) b' ≫ (q ≫ f)) (q ≫ f)
    (pullback.snd (modificationProjectionAtInfinity f b) q)
    (pullbackSnd_comp_structureMorphism_eq C (modificationProjectionAtInfinity f b ≫ f) f
      (modificationProjectionAtInfinity f b) rfl q)
    (modificationProjectionAtInfinity (q ≫ f) b') rfl θ hθ 0 ?_
    (isBivariantTransport_bivariantTransport C G _ _ _ _ _ _ _ θ hθ 0 hgys _)
  intro T g _ k α
  rw [bivariantTransportCap_apply, bivariantRestriction_cap, bivariantRestrictionCap_apply,
    chowPushforwardOfIso_comp_eq C (modificationInfinityBaseChangeOver f b (g ≫ q))
      (pullback.fst (pullback.snd (modificationProjectionAtInfinity f b) q) g ≫
        (pullback.fst (modificationProjectionAtInfinity f b) q ≫
          (modificationProjectionAtInfinity f b ≫ f)))
      (modificationInfinityBaseChangeOver (q ≫ f) b' g) _ _
      (modificationInfinityBaseChangeComparison C f b q b' θ hθ g)
      (modificationInfinityBaseChangeComparison_eq C f b q b' θ hθ g) _ _
      (modificationInfinityBaseChangeComparison_comp_base C f b q b' θ hθ g) (k - 0)]
  exact gysinAtInfinity_baseChange_cap P q P' η hη θ hθ hlift hgysinStep g k α

end BaseChange

end Stacks.Chow

end
