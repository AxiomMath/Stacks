module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Bilinearity
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDataBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChernBivariantCommute
public import StacksCore.Tactic.StacksAttribute

/-!
# Commuting a bivariant class past a Chow cohomology class, and the power sums of a complex

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, Stacks 02QL, let `X` be a
scheme locally of finite type over `S`, let `g : X' ⟶ X` be locally of finite type and let
`c ∈ A^q(X' ⟶ X)` be a bivariant class. Clause (2) of **Stacks 0FAC** says that for a perfect
object `E` of `D(𝒪_X)` whose Chern classes are defined,

  `c ∘ c_p(E) = c_p(Lg^*E) ∘ c`   in   `A^{q+p}(X' ⟶ X)`.

This file provides the shape that identity takes between two Chow cohomology classes, and proves
the **last step** of the source's proof: once the object is given by a bounded complex `ℰ^•` of
finite locally free modules, the identity for the class of the complex follows from the identity
for the classes of its terms, because the class of the complex is an alternating sum of those.

## Main definitions

* `Stacks.Chow.bivariantCompositeIdRightHom` — the composite `x ↦ c ∘ x` of `c` with a class
  `x ∈ A^p(X)`, read as a class for `g` itself rather than for `g ≫ 𝟙 X`, as a homomorphism of
  groups.
* `Stacks.Chow.bivariantCompositeIdLeftHom` — the composite `x' ↦ x' ∘ c` of a class
  `x' ∈ A^p(X')` with `c`, read as a class for `g` itself rather than for `𝟙 X' ≫ g` and in the
  degree `q + p`, as a homomorphism of groups.
* `Stacks.Chow.CommutesWithChowCohomologyClass` — the identity `c ∘ x = x' ∘ c` of the two,
  which is the shape of clause (2) of Stacks 0FAC for a pair of Chow cohomology classes.

## Main results

* `Stacks.Chow.commutesWithChowCohomologyClass_powerSumClassComplex` — the identity for the class
  `P_p(ℰ^•)` of Stacks 0ESZ of a complex of finite locally free modules and the class
  `P_p(g^*ℰ^•)` of its degreewise pullback, granted the identity for the terms.
* `Stacks.Chow.bivariantCompositeIdRightHom_cap`,
  `Stacks.Chow.bivariantCompositeIdLeftHom_cap` — the cap operations of the two composites on a
  test scheme, which is what the relation has to be read through to be carried past the **product**
  of `A^*(X)` rather than only past its sums; `Stacks.Chow.bivariantClassCongr_cap_heq` is the
  transport lemma both rest on.

## Implementation notes

### Why no Stacks 0FAC attribute is placed here

Clause (2) of Stacks 0FAC is about a perfect object `E` of `D(𝒪_X)` whose Chern classes are
defined in the sense of Stacks 0F9E (1) — that is, one carrying an envelope presentation
`Stacks.Chow.EnvelopePresentation`. The theorem below is the identity for a complex on `X`
itself, which is the case where that envelope is the identity of `X` (Stacks 0GUE (2)), and it
carries the identity for the terms of the complex, which is clause (2) of Stacks 02UA. So of the
five ingredients of the tag's proof —

1. the reduction of Stacks 02UC to integral `X`,
2. the reduction of Stacks 0GUF to a bounded complex of constant rank,
3. clause (2) of Stacks 02UA for the modules appearing,
4. the assembly of the class of a complex out of the classes of its terms,
5. in this repository, the descent of the identity along the envelope of a presentation, which
   stands in for 1 and 2,

— only 4 is proved here, 3 is carried, and 5 is **missing**. The sibling clause (1),
`Stacks.Chow.powerSum_mem_center_of_envelopePresentation` of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.Centrality`, carries 3 and proves 4 *and*
5, which is why it is registered against the tag and this is not. What blocks 5 is this:
`Stacks.Chow.bivariantTransport_bivariantComposite_bivariantRestriction` expresses the
restriction of a composite along the envelope through the restriction of the *middle* scheme,
whereas `Stacks.Chow.chowCohomologyRestriction` — the map in which an envelope presentation pins
a class down — is that restriction followed by a transport along
`Stacks.Chow.identityBaseChangeIso`, and `Stacks.Chow.bivariantTransportAddHom` is injective but
has no inverse in this repository.

### What the three transports are for

A class `x ∈ A^p(X)` is a bivariant class for `𝟙 X`, so `c ∘ x` is a class for `g ≫ 𝟙 X` of
degree `q + p` and `x' ∘ c` is a class for `𝟙 X' ≫ g` of degree `p + q`. The two morphisms and
the two degrees are equal and are not the same terms, so both composites are read back at `g` by
`Stacks.Chow.bivariantClassCongr` and the second one is read in the degree `q + p` by
`Stacks.Chow.bivariantClassCongrDeg`. All three transports are additive, which is what lets the
two composites be packaged as homomorphisms of groups; the alternating sum then passes through
them by `map_sum` and `map_zsmul`.

The structure morphism of `X'` is taken to be `g ≫ sX` rather than an abstract morphism to the
base, exactly as in `Stacks.Chow.PowerSumClassRule.IsBaseChangeCompatible` of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassDataBaseChange`, so that the two power sum data are
indexed the way the restriction map of Stacks 0B7F indexes them.

### Which hypotheses are carried

`Stacks.Chow.bivariantComposite` is defined carrying the two cases of Stacks 02TA for the Gysin
system, `Stacks.Chow.GysinSystem.IsNaturalUnderBaseChangeIso` and
`Stacks.Chow.GysinSystem.IsNaturalUnderPullbackCompPushforward`; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Class`. The classes `P_p` of a module
are the parameter `Stacks.Chow.PowerSumClassRule`, standing in for the evaluated power sums of
Stacks 0F9B, so the identity for them is a hypothesis and not a theorem; it is clause (2) of
Stacks 02UA in the power sum reading. The library's clause (2) of Stacks 02UA,
`Stacks.Chow.isChernCapFamily_bivariantClass`, is about the Chern class cap products of a module
and not about the evaluated power sums, so it does not discharge it.

## References

* [Stacks Project, Tag 0FAC](https://stacks.math.columbia.edu/tag/0FAC)
* [Stacks Project, Tag 02UA](https://stacks.math.columbia.edu/tag/02UA)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
* [Stacks Project, Tag 0GUE](https://stacks.math.columbia.edu/tag/0GUE)
* [Stacks Project, Tag 0GUF](https://stacks.math.columbia.edu/tag/0GUF)
* [Stacks Project, Tag 0F9E](https://stacks.math.columbia.edu/tag/0F9E)
* [Stacks Project, Tag 0F9B](https://stacks.math.columbia.edu/tag/0F9B)
* [Stacks Project, Tag 0ESZ](https://stacks.math.columbia.edu/tag/0ESZ)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0B7E](https://stacks.math.columbia.edu/tag/0B7E)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The transport of a degree, as a homomorphism of groups -/

section CongrDeg

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
  [LocallyOfFiniteType f] (hf : f ≫ sY = sX)

/-- Reading a bivariant class in an equal degree carries the zero class to the zero class. -/
theorem bivariantClassCongrDeg_zero {p q : ℤ} (hpq : p = q) :
    bivariantClassCongrDeg C G sX sY f hf hpq 0 = 0 := by
  subst hpq
  rfl

/-- Reading a bivariant class in an equal degree is additive. -/
theorem bivariantClassCongrDeg_add {p q : ℤ} (hpq : p = q)
    (c d : BivariantClass C G sX sY f hf p) :
    bivariantClassCongrDeg C G sX sY f hf hpq (c + d) =
      bivariantClassCongrDeg C G sX sY f hf hpq c + bivariantClassCongrDeg C G sX sY f hf hpq d :=
  by subst hpq; rfl

/-- `Stacks.Chow.bivariantClassCongrDeg` as a homomorphism of groups. -/
def bivariantClassCongrDegAddHom {p q : ℤ} (hpq : p = q) :
    BivariantClass C G sX sY f hf p →+ BivariantClass C G sX sY f hf q where
  toFun := bivariantClassCongrDeg C G sX sY f hf hpq
  map_zero' := bivariantClassCongrDeg_zero C G sX sY f hf hpq
  map_add' := bivariantClassCongrDeg_add C G sX sY f hf hpq

end CongrDeg

/-! ### The two composites with a class for the identity -/

section Composites

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X X' : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (g : X' ⟶ X) [LocallyOfFiniteType g]
  (hgys : G.IsNaturalUnderBaseChangeIso)
  (hgysc : G.IsNaturalUnderPullbackCompPushforward) (p q : ℤ)
  (c : BivariantClass C G (g ≫ sX) sX g rfl q)

/-- The composite `c ∘ x ∈ A^{q+p}(X' ⟶ X)` of `c ∈ A^q(X' ⟶ X)` with a class `x ∈ A^p(X)` of
Stacks 0B7E, as a homomorphism of groups in `x`.

A class of `A^p(X)` is a bivariant class for `𝟙 X`, so the composite of Stacks 0B75 is a class
for `g ≫ 𝟙 X`; it is read back at `g` by `Stacks.Chow.bivariantClassCongr`. -/
def bivariantCompositeIdRightHom :
    chowCohomologyComponent C G sX p →+ BivariantClass C G (g ≫ sX) sX g rfl (q + p) :=
  (bivariantClassCongr C G (g ≫ sX) sX (Category.comp_id g)
      (comp_comp_structureMorphism_eq (rfl : g ≫ sX = g ≫ sX) (Category.id_comp sX)) rfl
      (q + p)).toAddMonoidHom.comp
    (bivariantCompositeAddHomRight C G (g ≫ sX) sX sX g (𝟙 X) rfl (Category.id_comp sX) q p
      hgys hgysc c)

/-- The composite `x' ∘ c ∈ A^{q+p}(X' ⟶ X)` of a class `x' ∈ A^p(X')` of Stacks 0B7E with
`c ∈ A^q(X' ⟶ X)`, as a homomorphism of groups in `x'`.

A class of `A^p(X')` is a bivariant class for `𝟙 X'`, so the composite of Stacks 0B75 is a class
for `𝟙 X' ≫ g` of degree `p + q`; it is read back at `g` by `Stacks.Chow.bivariantClassCongr` and
in the degree `q + p` by `Stacks.Chow.bivariantClassCongrDeg`. -/
def bivariantCompositeIdLeftHom :
    chowCohomologyComponent C G (g ≫ sX) p →+ BivariantClass C G (g ≫ sX) sX g rfl (q + p) :=
  (bivariantClassCongrDegAddHom C G (g ≫ sX) sX g rfl (add_comm p q)).comp
    ((bivariantClassCongr C G (g ≫ sX) sX (Category.id_comp g)
        (comp_comp_structureMorphism_eq (Category.id_comp (g ≫ sX)) (rfl : g ≫ sX = g ≫ sX)) rfl
        (p + q)).toAddMonoidHom.comp
      (bivariantCompositeAddHomLeft C G (g ≫ sX) (g ≫ sX) sX (𝟙 X') g
        (Category.id_comp (g ≫ sX)) rfl p q hgys hgysc c))

/-- **The shape of clause (2) of Stacks 0FAC for a pair of Chow cohomology classes.** That a
bivariant class `c ∈ A^q(X' ⟶ X)` carries `x ∈ A^p(X)` to `x' ∈ A^p(X')`:

  `c ∘ x = x' ∘ c`   in   `A^{q+p}(X' ⟶ X)`.

At `x = c_p(E)` and `x' = c_p(Lg^*E)` this is the identity the tag asserts. It is not registered
against the tag: see the implementation notes of this file for which of the tag's ingredients are
proved, carried and missing. -/
def CommutesWithChowCohomologyClass (x : chowCohomologyComponent C G sX p)
    (x' : chowCohomologyComponent C G (g ≫ sX) p) : Prop :=
  bivariantCompositeIdRightHom C G sX g hgys hgysc p q c x =
    bivariantCompositeIdLeftHom C G sX g hgys hgysc p q c x'

/-- The relation unfolded to the equality of the two composites. -/
theorem commutesWithChowCohomologyClass_iff (x : chowCohomologyComponent C G sX p)
    (x' : chowCohomologyComponent C G (g ≫ sX) p) :
    CommutesWithChowCohomologyClass C G sX g hgys hgysc p q c x x' ↔
      bivariantCompositeIdRightHom C G sX g hgys hgysc p q c x =
        bivariantCompositeIdLeftHom C G sX g hgys hgysc p q c x' :=
  Iff.rfl

/-- The relation holds for the two zero classes: both composites are zero. -/
theorem commutesWithChowCohomologyClass_zero :
    CommutesWithChowCohomologyClass C G sX g hgys hgysc p q c 0 0 := by
  rw [commutesWithChowCohomologyClass_iff, map_zero, map_zero]

/-- The relation is closed under sums: a bivariant class that carries `x₁` to `x₁'` and `x₂` to
`x₂'` carries `x₁ + x₂` to `x₁' + x₂'`. -/
theorem commutesWithChowCohomologyClass_add {x₁ x₂ : chowCohomologyComponent C G sX p}
    {x₁' x₂' : chowCohomologyComponent C G (g ≫ sX) p}
    (h₁ : CommutesWithChowCohomologyClass C G sX g hgys hgysc p q c x₁ x₁')
    (h₂ : CommutesWithChowCohomologyClass C G sX g hgys hgysc p q c x₂ x₂') :
    CommutesWithChowCohomologyClass C G sX g hgys hgysc p q c (x₁ + x₂) (x₁' + x₂') := by
  rw [commutesWithChowCohomologyClass_iff] at h₁ h₂
  rw [commutesWithChowCohomologyClass_iff, map_add, map_add, h₁, h₂]

/-- The relation is closed under integer multiples. -/
theorem commutesWithChowCohomologyClass_zsmul {x : chowCohomologyComponent C G sX p}
    {x' : chowCohomologyComponent C G (g ≫ sX) p}
    (h : CommutesWithChowCohomologyClass C G sX g hgys hgysc p q c x x') (n : ℤ) :
    CommutesWithChowCohomologyClass C G sX g hgys hgysc p q c (n • x) (n • x') := by
  rw [commutesWithChowCohomologyClass_iff] at h
  rw [commutesWithChowCohomologyClass_iff, map_zsmul, map_zsmul, h]

/-! #### The cap operations of the two composites

What the relation asserts on a test scheme. Closure under sums and under integer multiples above
needs only that the two composites are homomorphisms of groups; closure under the **product** of
`A^*(X)`, which is what would carry the relation from the Chern classes to a polynomial in them,
has to be read on the test schemes, and the three lemmas below are that reading. The bridge from
them to closure under the product is still missing. -/

/-- Reading a bivariant class at an equal morphism does not change its cap operation. The two
sides are classes for two equal morphisms, so their cap operations land in the Chow groups of two
equal — and not identical — base changes, whence the heterogeneous equality. -/
theorem bivariantClassCongr_cap_heq {Z W : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
    (sW : W ⟶ C.S) [LocallyOfFiniteType sW] {f f' : Z ⟶ W} [LocallyOfFiniteType f]
    [LocallyOfFiniteType f'] (hff : f = f') (hf : f ≫ sW = sZ) (hf' : f' ≫ sW = sZ) (n : ℤ)
    (a : BivariantClass C G sZ sW f hf n) {T : Scheme.{u}} (t : T ⟶ W) [LocallyOfFiniteType t]
    (k : ℤ) (α : chowGroup C (t ≫ sW) k) :
    (bivariantClassCongr C G sZ sW hff hf hf' n a).cap t k α ≍ a.cap t k α := by
  subst hff
  rfl

/-- Reading a composite at an equal morphism does not change its cap operation, up to the
transport of Chow groups along the equality of degrees. -/
private theorem bivariantClassCongr_bivariantComposite_cap_heq {U V W : Scheme.{u}}
    (sU : U ⟶ C.S) [LocallyOfFiniteType sU] (sV : V ⟶ C.S) [LocallyOfFiniteType sV]
    (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (u : U ⟶ V) [LocallyOfFiniteType u] (v : V ⟶ W)
    [LocallyOfFiniteType v] {w : U ⟶ W} [LocallyOfFiniteType w] (hu : u ≫ sV = sU)
    (hv : v ≫ sW = sV) (huv : u ≫ v = w) (hw : w ≫ sW = sU) (a : BivariantClass C G sU sV u hu p)
    (b : BivariantClass C G sV sW v hv q) {T : Scheme.{u}} (t : T ⟶ W) [LocallyOfFiniteType t]
    (k : ℤ) (α : chowGroup C (t ≫ sW) k) :
    (bivariantClassCongr C G sU sW huv (comp_comp_structureMorphism_eq hu hv) hw (p + q)
        (bivariantComposite C G sU sV sW u v hu hv p q a b hgys hgysc)).cap t k α ≍
      bivariantCompositeCap C G sU sV sW u v hu hv (properPushforwardDescends C) p q a b t k α := by
  refine HEq.trans (bivariantClassCongr_cap_heq C G sU sW huv _ hw (p + q) _ t k α) ?_
  rw [bivariantComposite_cap]
  exact chowGroupDegreeEquiv_heq C _ _ _

/-- **The cap operation of `x ↦ c ∘ x`.** On a test scheme `t : T ⟶ X` the composite caps as cap
with `x`, then cap with `c`, pushed forward along the associativity isomorphism of pullbacks —
that is, it is the cap operation of the composite of Stacks 0B75, the transport back to `g` of
`Stacks.Chow.bivariantCompositeIdRightHom` leaving it unchanged. -/
theorem bivariantCompositeIdRightHom_cap (x : chowCohomologyComponent C G sX p)
    {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ)
    (α : chowGroup C (t ≫ sX) k) :
    (bivariantCompositeIdRightHom C G sX g hgys hgysc p q c x).cap t k α ≍
      bivariantCompositeCap C G (g ≫ sX) sX sX g (𝟙 X) rfl (Category.id_comp sX)
        (properPushforwardDescends C) q p c x t k α := by
  exact bivariantClassCongr_bivariantComposite_cap_heq C G hgys hgysc q p (g ≫ sX) sX sX g (𝟙 X)
    rfl (Category.id_comp sX) (Category.comp_id g) rfl c x t k α

/-- **The cap operation of `x' ↦ x' ∘ c`.** On a test scheme `t : T ⟶ X` the composite caps as
cap with `c`, then cap with `x'` on the base change, pushed forward along the associativity
isomorphism of pullbacks; the transport back to `g` and the reading in the degree `q + p` leave
it unchanged. -/
theorem bivariantCompositeIdLeftHom_cap (x' : chowCohomologyComponent C G (g ≫ sX) p)
    {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ)
    (α : chowGroup C (t ≫ sX) k) :
    (bivariantCompositeIdLeftHom C G sX g hgys hgysc p q c x').cap t k α ≍
      bivariantCompositeCap C G (g ≫ sX) (g ≫ sX) sX (𝟙 X') g (Category.id_comp (g ≫ sX)) rfl
        (properPushforwardDescends C) p q x' c t k α := by
  refine (heq_of_eq (bivariantClassCongrDeg_cap C G (g ≫ sX) sX g rfl (add_comm p q) _ t k α)).trans
    ((chowGroupDegreeEquiv_heq C _ _ _).trans
    (bivariantClassCongr_bivariantComposite_cap_heq C G hgys hgysc p q (g ≫ sX) (g ≫ sX) sX (𝟙 X')
      g (Category.id_comp (g ≫ sX)) rfl (Category.id_comp g) rfl x' c t k α))

end Composites

/-! ### The power sums of a complex -/

section PowerSum

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X X' : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (g : X' ⟶ X) [LocallyOfFiniteType g]
  (hgys : G.IsNaturalUnderBaseChangeIso)
  (hgysc : G.IsNaturalUnderPullbackCompPushforward) (q : ℤ)
  (c : BivariantClass C G (g ≫ sX) sX g rfl q)

/-- **The power sum reading of clause (2) of Stacks 02UA for the modules of `X`.** That the
bivariant class `c` carries the power sum `P_p(ℰ)` of a finite locally free module `ℰ` on `X` to
the power sum `P_p(g^*ℰ)` of its pullback:

  `c ∘ P_p(ℰ) = P_p(g^*ℰ) ∘ c`.

This is clause (2) of Stacks 02UA read for the evaluated power sums of Stacks 0F9B rather than
for the Chern classes; the power sums are a bare parameter here, so it is a hypothesis. It is
asked only of the finite locally free modules, matching
`Stacks.Chow.PowerSumClassRule.IsBaseChangeCompatible`. -/
def PowerSumClassRule.CommutesWithBivariantClass (W : PowerSumClassRule C G sX)
    (W' : PowerSumClassRule C G (g ≫ sX)) : Prop :=
  ∀ M : X.Modules,
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M →
      ∀ p : ℕ, CommutesWithChowCohomologyClass C G sX g hgys hgysc (p : ℤ) q c (W.cls M p)
        (W'.cls ((Scheme.Modules.pullback g).obj M) p)

/-- **Clause (2) of Stacks 0FAC for the power sums of a complex, granted it for the terms.** The
bivariant class `c ∈ A^q(X' ⟶ X)` carries the class `P_p(ℰ^•)` of Stacks 0ESZ of a complex of
finite locally free modules bounded in the degrees `a, …, a + k` to the class `P_p(g^*ℰ^•)` of its
degreewise pullback:

  `c ∘ P_p(ℰ^•) = P_p(g^*ℰ^•) ∘ c`   in   `A^{q+p}(X' ⟶ X)`.

This is the step with which the source's proof of clause (2) ends, where it observes that
`c_p(ℰ^•)` is a polynomial in the Chern classes of the `ℰ^n`: for the power sums that polynomial
is the alternating **sum** `∑_n (-1)^n P_p(ℰ^n)` of `Stacks.Chow.powerSumClassComplex_eq_sum`, and
composition with `c` is additive on each side by the bilinearity of Stacks 0B75. The terms of the
complex are assumed finite locally free, which is the hypothesis the source states on `ℰ^•`.

The two reductions the source uses before reaching this step, Stacks 02UC and Stacks 0GUF, are
not available here, and neither is their repository stand-in, the descent of the identity along
the envelope of an envelope presentation; so this is **not** registered against Stacks 0FAC. See
the implementation notes of this file. -/
theorem commutesWithChowCohomologyClass_powerSumClassComplex {W : PowerSumClassRule C G sX}
    {W' : PowerSumClassRule C G (g ≫ sX)}
    (hW : PowerSumClassRule.CommutesWithBivariantClass C G sX g hgys hgysc q c W W')
    (P : CochainComplex X.Modules ℤ) (a : ℤ) (k : ℕ)
    (hflf : ∀ i ∈ Finset.range (k + 1),
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
        (P.X (a + (i : ℤ)))) (p : ℕ) :
    CommutesWithChowCohomologyClass C G sX g hgys hgysc (p : ℤ) q c
      (powerSumClassComplex C G sX W P a k p)
      (powerSumClassComplex C G (g ≫ sX) W'
        (((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) a k p) := by
  rw [commutesWithChowCohomologyClass_iff, powerSumClassComplex_eq_sum,
    powerSumClassComplex_eq_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have e := (commutesWithChowCohomologyClass_iff C G sX g hgys hgysc (p : ℤ) q c _ _).mp
    (hW (P.X (a + (i : ℤ))) (hflf i hi) p)
  rw [map_zsmul, map_zsmul, e]
  rfl

end PowerSum

end Stacks.Chow

end
