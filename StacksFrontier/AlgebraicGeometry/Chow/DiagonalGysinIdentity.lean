module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FirstChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Restriction
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.DiagonalGysin

/-!
# The diagonal Gysin identity `Δ^! ∘ pr_i^! = 1`

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `f : X ⟶ Y` be a
smooth morphism of schemes locally of finite type over `S`, let `Δ : X ⟶ X ×_Y X` be the
diagonal and let `pr_i : X ×_Y X ⟶ X` be the two projections. Stacks 0FBS asserts

  `Δ^! ∘ pr_i^! = 1`   in `A^0(X)`.

Three things make that statement, and this file supplies all of them that this repository can
support.

* The **right-hand side**, the unit `1 ∈ A^0(X) = A^0(X ⟶ X)`. It is built here: the bivariant
  class of degree `0` for `𝟙 X` whose operation on each test scheme `g : T ⟶ X` is the identity
  of `A_k(T)`, carried to the chosen pullback `X ×_X T` along the canonical isomorphism
  `X ×_X T ≅ T`.
* The **geometric inputs** of the source proof: `Δ ≫ pr_i = 𝟙 X` (which is
  `CategoryTheory.Limits.pullback.diagonal_fst` and
  `CategoryTheory.Limits.pullback.diagonal_snd` in Mathlib, and is used as such below) and the
  availability of the Gysin maps of Stacks 0FF3 for `Δ` and for the two projections — the
  diagonal is an immersion by Stacks 0FBR, and the projections are smooth by base change.
* The **identity itself**, reduced to what the repository can state: a class in `A^0(X ⟶ X)`
  equals `1` exactly when the operation it induces on every test scheme is the identity, and
  the cap operation of a class witnessing the composition of a class for `Δ` with a class for
  `pr_i`, transported along `Δ ≫ pr_i = 𝟙 X`, *is* the composite operation
  `a ∩ (b ∩ -)`. Together: the composite of the two Gysin classes is `1` precisely when it acts
  as the identity on Chow groups, and by `Stacks.Chow.eq_of_isBivariantClassComposition` there is
  at most one class that composes them.

## Main definitions

* `Stacks.Chow.identityCapRule` — the identity cap rule of degree `0`, the operation
  `A_k(T) ⟶ A_{k-0}(T)` that is the identity up to the transport of degrees.
* `Stacks.Chow.bivariantIdentityClass` — **the class `1 ∈ A^0(X)`**, i.e. the unit of
  `A^0(X ⟶ X)`.
* `Stacks.Chow.BivariantClass.copy` — a bivariant class read for an equal morphism in an equal
  degree.

## Main results

* `Stacks.Chow.identityCapRule_properNaturality`,
  `Stacks.Chow.identityCapRule_transportFlatNaturality` — the proper and the flat axiom of
  Stacks 0B76 for the identity cap rule, the second from the isomorphism case of Stacks 02RG.
* `Stacks.Chow.bivariantIdentityClass_cap_pushforward`,
  `Stacks.Chow.bivariantIdentityClass_cap_pushforward_heq` — the cap operation of `1` is the
  identity: pushing it forward along `X ×_X T ≅ T` returns the class it was applied to.
* `Stacks.Chow.eq_bivariantIdentityClass_iff` — a class of degree `0` for `𝟙 X` is `1` exactly
  when the operation it induces on every test scheme is the identity.
* `Stacks.Chow.gysinMapExists_fst_of_smooth`, `Stacks.Chow.gysinMapExists_snd_of_smooth` — the
  Gysin maps of the two projections are available, the projections being smooth by base change.
* `Stacks.Chow.copy_cap_heq_bivariantCompositeCap` — for a class witnessing the composition of a
  class for `Δ` with one for `pr_i` in total degree `0`, the transport along `Δ ≫ pr_i = 𝟙 X`
  caps by the composite operation. This is the left-hand side of Stacks 0FBS, read in
  `A^0(X ⟶ X)`.

## Implementation notes

### What is missing, and what it blocks

The classes `Δ^!` and `pr_i^!` themselves cannot be written down in this repository. The Gysin
map of Stacks 0FF3 is `f^! = i^! ∘ g^*`, and all three of its inputs are absent: the
higher-codimension class `c(Z ⟶ X, 𝒩)` of Stacks 0FBK, the flat-pullback bivariant class of
Stacks 0B78, and a *construction* — as opposed to the characterization
`Stacks.Chow.IsBivariantClassComposition` — of the composition of bivariant classes of
Stacks 0B75, which is itself blocked on Stacks 0B6Y. See the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection` and of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Basic`.

So the two factors are carried as arbitrary bivariant classes `a` for `Δ` and `b` for `pr_i`,
and the composite as an arbitrary class witnessing
`Stacks.Chow.IsBivariantClassComposition`. Nothing is lost by that at the level of the
conclusion: the composition formula pins the composite down
(`Stacks.Chow.eq_of_isBivariantClassComposition`), so the content of Stacks 0FBS that remains
once the composite exists is the identification of it with `1`, and that identification is the
equivalence proved here.

### The one hypothesis the identity class carries

`Stacks.Chow.bivariantIdentityClass` is built from `Stacks.Chow.IdentityCapRule.toBivariantClass`
and discharges two of the three naturality axioms of Stacks 0B76 outright. The proper axiom is
`Stacks.Chow.IdentityCapRule.transport_proper_naturality` applied to the identity rule, whose own
projection formula is the transport lemma `Stacks.Chow.properChowPushforward_cast`. The flat axiom
is the isomorphism case of Stacks 02RG,
`Stacks.Chow.flatPullbackChow_chowPushforwardOfIso`, applied to the square formed by the two
base-change isomorphisms `X ×_X T ≅ T` and `X ×_X T' ≅ T'`; that case *is* in this repository,
so unlike the situation recorded in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Basic` the flat axiom is no obstruction
here.

The Gysin axiom is a hypothesis, `hgysin`, stated as
`Stacks.Chow.IdentityCapRule.TransportGysinNaturality`, which is literally the `gysin_naturality`
field of `Stacks.Chow.BivariantClass` for the transported identity rule, hence the weakest
hypothesis that yields the class. It cannot be discharged: the axiom compares the Gysin map of a
`Stacks.Chow.GysinSystem` on `T` with its Gysin map on `X ×_X T`, and the first Chern class rules
a Gysin system supplies at two isomorphic schemes are unrelated data — the same obstruction that
`Stacks.Chow.GysinSystem.IsNaturalUnderBaseChangeIso` resolves for Stacks 0F9Z in
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Restriction`. That hypothesis does not apply here
unchanged, because one of the two modules compared would be the pullback of `L` along `𝟙 T`
rather than `L` itself. Being a `Prop`, `hgysin` is proof-irrelevant: two values of
`Stacks.Chow.bivariantIdentityClass` differing only in it are definitionally equal.

### Degrees

A cap operation of degree `p` produces `A_{k-p}`, so at `p = 0` it produces `A_{k-0}`. That is
the same integer as `k` and not the same term, whence the transports
`Stacks.Chow.chowGroupDegreeEquiv` in the identity rule and the four `cast` lemmas below.

## References

* [Stacks Project, Tag 0FBS](https://stacks.math.columbia.edu/tag/0FBS)
* [Stacks Project, Tag 0FBR](https://stacks.math.columbia.edu/tag/0FBR)
* [Stacks Project, Tag 0FF3](https://stacks.math.columbia.edu/tag/0FF3)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Transports along an equality of degrees -/

/-- The transport of a Chow class along an equality of degrees is the corresponding cast. -/
theorem chowGroupDegreeEquiv_apply (C : ChowSituation.{u}) {T : Scheme.{u}} (q : T ⟶ C.S)
    [LocallyOfFiniteType q] {k l : ℤ} (h : k = l) (α : chowGroup C q k) :
    chowGroupDegreeEquiv C q h α = Eq.mp (congrArg (chowGroup C q) h) α := by
  cases h
  rfl

/-- A Chow class is heterogeneously equal to its transport along an equality of degrees. -/
theorem chowGroup_cast_heq {C : ChowSituation.{u}} {A : Scheme.{u}} (q : A ⟶ C.S)
    [LocallyOfFiniteType q] {i j : ℤ} (hij : i = j) (x : chowGroup C q i) :
    HEq (Eq.mp (congrArg (chowGroup C q) hij) x) x := by
  cases hij
  rfl

/-- Pushforward along an isomorphism over the base commutes with the transport along an equality
of degrees. This is `Stacks.Chow.properChowPushforward_cast` for an isomorphism, where no
instance of Stacks 02S2 has to be supplied. -/
theorem chowPushforwardOfIso_cast (C : ChowSituation.{u}) {A B : Scheme.{u}} (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (w : A ⟶ B) [IsIso w]
    (hw : w ≫ sB = sA) {i j : ℤ} (hij : i = j) (α : chowGroup C sA i) :
    Eq.mp (congrArg (chowGroup C sB) hij) (chowPushforwardOfIso C sA sB w hw i α) =
      chowPushforwardOfIso C sA sB w hw j (Eq.mp (congrArg (chowGroup C sA) hij) α) := by
  cases hij
  rfl

/-- Flat pullback of fixed relative dimension commutes with the transport along an equality of
degrees. -/
theorem flatPullbackChow_cast (C : ChowSituation.{u}) {A B : Scheme.{u}} (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (v : A ⟶ B)
    [LocallyOfFiniteType v] [Flat v] (hv : v ≫ sB = sA) (r : ℕ)
    (hvr : AlgebraicGeometry.RelativeDimension v r) {i j : ℤ} (hij : i = j)
    (hfaci : FlatPullbackFactorsThroughRationalEquivalence C sA sB v hv r hvr i)
    (hfacj : FlatPullbackFactorsThroughRationalEquivalence C sA sB v hv r hvr j)
    (α : chowGroup C sB i) :
    Eq.mp (congrArg (chowGroup C sA) (congrArg (· + (r : ℤ)) hij))
        (flatPullbackChow C sA sB v hv r hvr i hfaci α) =
      flatPullbackChow C sA sB v hv r hvr j hfacj
        (Eq.mp (congrArg (chowGroup C sB) hij) α) := by
  cases hij
  rfl

/-- Stacks 02S1 for a flat morphism of fixed relative dimension is unchanged by replacing the
degree with an equal one. -/
theorem flatPullbackFactorsThroughRationalEquivalence_cast (C : ChowSituation.{u})
    {A B : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S)
    [LocallyOfFiniteType sB] (v : A ⟶ B) [LocallyOfFiniteType v] [Flat v] (hv : v ≫ sB = sA)
    (r : ℕ) (hvr : AlgebraicGeometry.RelativeDimension v r) {i j : ℤ} (hij : i = j)
    (hfacj : FlatPullbackFactorsThroughRationalEquivalence C sA sB v hv r hvr j) :
    FlatPullbackFactorsThroughRationalEquivalence C sA sB v hv r hvr i := by
  cases hij
  exact hfacj

/-! ### The identity cap rule -/

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- The *identity cap rule* of degree `0` on `X`: on every test scheme `g : T ⟶ X` and in every
degree it is the identity of `A_k(T)`, read as a map `A_k(T) ⟶ A_{k-0}(T)`. -/
def identityCapRule : IdentityCapRule C sX 0 := fun {_T} g _ k ↦
  (chowGroupDegreeEquiv C (g ≫ sX) (sub_zero k).symm).toAddMonoidHom

/-- The identity cap rule does nothing but transport the degree. -/
theorem identityCapRule_apply {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ sX) k) :
    identityCapRule C sX g k α = Eq.mp (congrArg (chowGroup C (g ≫ sX)) (sub_zero k).symm) α :=
  chowGroupDegreeEquiv_apply C (g ≫ sX) (sub_zero k).symm α

/-- The transport of the identity cap rule to the chosen pullbacks is pushforward along the
base-change isomorphism `T ≅ X ×_X T`, up to the transport of the degree. -/
theorem identityCapRule_transport_apply {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g]
    (k : ℤ) (α : chowGroup C (g ≫ sX) k) :
    IdentityCapRule.transport C sX 0 (identityCapRule C sX) g k α =
      Eq.mp (congrArg (chowGroup C (pullback.fst (𝟙 X) g ≫ sX)) (sub_zero k).symm)
        (chowPushforwardOfIso C (g ≫ sX) (pullback.fst (𝟙 X) g ≫ sX)
          (identityBaseChangeIso g).inv (identityBaseChangeIso_hom_comp C sX g) k α) := by
  rw [IdentityCapRule.transport, AddMonoidHom.coe_comp, Function.comp_apply,
    identityCapRule_apply]
  exact (chowPushforwardOfIso_cast C (g ≫ sX) (pullback.fst (𝟙 X) g ≫ sX)
    (identityBaseChangeIso g).inv (identityBaseChangeIso_hom_comp C sX g) (sub_zero k).symm
    α).symm

/-- **Stacks 0B76 (1) for the identity cap rule.** The identity commutes with proper pushforward
on the test schemes: the two sides differ only by the transport of the degree. -/
theorem identityCapRule_properNaturality :
    IdentityCapRule.ProperNaturality C sX 0 (identityCapRule C sX) := by
  intro T T' g _ h _ k hfac hfacp α
  rw [identityCapRule_apply, identityCapRule_apply]
  exact properChowPushforward_cast C ((h ≫ g) ≫ sX) (g ≫ sX) h (by simp [Category.assoc])
    (sub_zero k).symm hfac hfacp α

/-- **Stacks 0B76 (2) for the identity cap rule.** The transport of the identity cap rule to the
chosen pullbacks commutes with flat pullback of fixed relative dimension.

The transport is pushforward along the base-change isomorphisms `T ≅ X ×_X T` and
`T' ≅ X ×_X T'`, and the cartesian square of the axiom makes those two isomorphisms into the
horizontal legs of a square whose vertical legs are the flat morphism and its base change. So
this is the isomorphism case of Stacks 02RG,
`Stacks.Chow.flatPullbackChow_chowPushforwardOfIso`. -/
theorem identityCapRule_transportFlatNaturality :
    IdentityCapRule.TransportFlatNaturality C sX 0 (identityCapRule C sX) := by
  intro T T' g _ h _ _ r hr h' sq hfst k hr' hfac hfac' α
  have hft' : LocallyOfFiniteType h' :=
    MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
  have hfl' : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
  have hinv : (identityBaseChangeIso g).inv ≫ pullback.fst (𝟙 X) g ≫ sX = g ≫ sX :=
    identityBaseChangeIso_hom_comp C sX g
  have hu : (identityBaseChangeIso (h ≫ g)).inv ≫ pullback.fst (𝟙 X) (h ≫ g) ≫ sX =
      (h ≫ g) ≫ sX := identityBaseChangeIso_hom_comp C sX (h ≫ g)
  have hm : h' ≫ pullback.fst (𝟙 X) g ≫ sX = pullback.fst (𝟙 X) (h ≫ g) ≫ sX := by
    rw [← Category.assoc, hfst]
  have hh : h ≫ g ≫ sX = (h ≫ g) ≫ sX := by simp
  have hsq : (identityBaseChangeIso (h ≫ g)).hom ≫ h = h' ≫ (identityBaseChangeIso g).hom := sq.w
  have hconj : (identityBaseChangeIso (h ≫ g)).inv ≫ h' ≫ (identityBaseChangeIso g).hom = h := by
    rw [← hsq, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hmove : h ≫ (identityBaseChangeIso g).inv =
      (identityBaseChangeIso (h ≫ g)).inv ≫ h' := by
    conv_lhs => rw [← hconj]
    rw [Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hfacv : FlatPullbackFactorsThroughRationalEquivalence C
      (pullback.fst (𝟙 X) (h ≫ g) ≫ sX) (pullback.fst (𝟙 X) g ≫ sX) h' hm r hr' k :=
    flatPullbackFactorsThroughRationalEquivalence_cast C _ _ h' hm r hr' (sub_zero k).symm hfac'
  have key := flatPullbackChow_chowPushforwardOfIso C (g ≫ sX) ((h ≫ g) ≫ sX)
    (pullback.fst (𝟙 X) g ≫ sX) (pullback.fst (𝟙 X) (h ≫ g) ≫ sX)
    (identityBaseChangeIso g).inv hinv (identityBaseChangeIso (h ≫ g)).inv hu h hh h' hm hmove
    r hr hr' k hfac hfacv α
  rw [identityCapRule_transport_apply, identityCapRule_transport_apply,
    ← flatPullbackChow_cast C (pullback.fst (𝟙 X) (h ≫ g) ≫ sX) (pullback.fst (𝟙 X) g ≫ sX) h'
      hm r hr' (sub_zero k).symm hfacv hfac', key]
  exact (chowGroup_cast_heq _ (sub_zero (k + (r : ℤ))).symm _).trans
    (chowGroup_cast_heq _ (congrArg (· + (r : ℤ)) (sub_zero k).symm) _).symm

/-! ### The identity class `1 ∈ A^0(X)` -/

/-- **Stacks 0FBS, the right-hand side.** The *identity bivariant class* `1 ∈ A^0(X)`: the
bivariant class of degree `0` for `𝟙 X` whose operation on every test scheme `g : T ⟶ X` is the
identity of `A_k(T)`, carried to the chosen pullback `X ×_X T` along the canonical isomorphism.

The Gysin axiom of Stacks 0B76 is the hypothesis `hgysin`; it is literally the
`gysin_naturality` field of `Stacks.Chow.BivariantClass` for this cap operation, hence the
weakest hypothesis that produces the class, and it is a `Prop`, so the class does not depend on
which proof is supplied. See the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.DiagonalGysinIdentity`. -/
@[stacks 0FBS "the right-hand side: the unit 1 ∈ A^0(X) of Stacks 0B76, built with the \
proper and flat axioms discharged and the Gysin axiom of Stacks 0B76 for its cap operation \
carried as a hypothesis; the Gysin classes Δ^! and pr_i^! of the left-hand side cannot be \
written down here, their three inputs — Stacks 0FBK, 0B78 and a construction of the \
composition of Stacks 0B75 — all being absent from this repository"]
def bivariantIdentityClass (G : GysinSystem C)
    (hgysin : IdentityCapRule.TransportGysinNaturality C sX 0 (identityCapRule C sX) G) :
    BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) 0 :=
  IdentityCapRule.toBivariantClass C sX 0 (identityCapRule C sX) G
    (identityCapRule_properNaturality C sX) (identityCapRule_transportFlatNaturality C sX) hgysin

/-- The cap operation of `1` is the transport of the identity cap rule. -/
@[simp]
theorem bivariantIdentityClass_cap (G : GysinSystem C)
    (hgysin : IdentityCapRule.TransportGysinNaturality C sX 0 (identityCapRule C sX) G)
    {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ) :
    (bivariantIdentityClass C sX G hgysin).cap g k =
      IdentityCapRule.transport C sX 0 (identityCapRule C sX) g k :=
  rfl

/-- **The cap operation of `1` is the identity.** Pushing `1 ∩ α` forward along the projection
`X ×_X T ⟶ T` returns `α`, up to the transport of the degree. -/
theorem bivariantIdentityClass_cap_pushforward (G : GysinSystem C)
    (hgysin : IdentityCapRule.TransportGysinNaturality C sX 0 (identityCapRule C sX) G)
    {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ sX) k) :
    chowPushforwardOfIso C (pullback.fst (𝟙 X) g ≫ sX) (g ≫ sX) (identityBaseChangeIso g).hom
        (identityBaseChangeIso_hom_comp_base C sX g) (k - 0)
        ((bivariantIdentityClass C sX G hgysin).cap g k α) =
      identityCapRule C sX g k α :=
  IdentityCapRule.pushforward_transport C sX 0 (identityCapRule C sX) g k α

/-- **The cap operation of `1` is the identity**, with the transport of the degree removed. -/
theorem bivariantIdentityClass_cap_pushforward_heq (G : GysinSystem C)
    (hgysin : IdentityCapRule.TransportGysinNaturality C sX 0 (identityCapRule C sX) G)
    {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ sX) k) :
    HEq (chowPushforwardOfIso C (pullback.fst (𝟙 X) g ≫ sX) (g ≫ sX)
        (identityBaseChangeIso g).hom (identityBaseChangeIso_hom_comp_base C sX g) (k - 0)
        ((bivariantIdentityClass C sX G hgysin).cap g k α)) α := by
  rw [bivariantIdentityClass_cap_pushforward, identityCapRule_apply]
  exact chowGroup_cast_heq _ (sub_zero k).symm α

/-- **Stacks 0FBS, the identification with `1`.** A bivariant class of degree `0` for `𝟙 X` is
the identity class exactly when the operation it induces on every test scheme is the identity.

This is what the conclusion of Stacks 0FBS asserts of `Δ^! ∘ pr_i^!`, and the direction that
matters for the tag is the one from right to left: a composite acting as the identity on Chow
groups *is* the class `1`. Uniqueness comes from
`Stacks.Chow.BivariantClass.eq_of_pushforward_cap_eq`, pushforward along the base-change
isomorphism being a bijection of Chow groups. -/
@[stacks 0FBS "the conclusion, reduced to an identification: a degree-0 class for 𝟙 X equals \
the unit 1 ∈ A^0(X) exactly when it acts as the identity on every test scheme; the composite \
Δ^! ∘ pr_i^! itself is not constructed, the Gysin classes needing Stacks 0FBK, 0B78 and a \
construction of the composition of Stacks 0B75"]
theorem eq_bivariantIdentityClass_iff (G : GysinSystem C)
    (hgysin : IdentityCapRule.TransportGysinNaturality C sX 0 (identityCapRule C sX) G)
    (c : BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) 0) :
    c = bivariantIdentityClass C sX G hgysin ↔
      ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
        (α : chowGroup C (g ≫ sX) k),
        chowPushforwardOfIso C (pullback.fst (𝟙 X) g ≫ sX) (g ≫ sX)
            (identityBaseChangeIso g).hom (identityBaseChangeIso_hom_comp_base C sX g) (k - 0)
            (c.cap g k α) =
          identityCapRule C sX g k α := by
  constructor
  · rintro rfl T g _ k α
    exact bivariantIdentityClass_cap_pushforward C sX G hgysin g k α
  · intro h
    refine BivariantClass.eq_of_pushforward_cap_eq C sX 0 G c (bivariantIdentityClass C sX G
      hgysin) fun {T} g _ k α ↦ ?_
    exact (h (T := T) g k α).trans
      (bivariantIdentityClass_cap_pushforward C sX G hgysin g k α).symm

/-! ### A bivariant class read for an equal morphism -/

/-- A bivariant class of degree `p` for `f` is one of degree `p'` for `f'` whenever `f = f'` and
`p = p'`. The transport is needed because the composite `Δ ≫ pr_i` and the identity of `X` are
equal morphisms and not the same term, and likewise for the degrees `p + q` and `0`. -/
def BivariantClass.copy (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    {f f' : X ⟶ Y} [LocallyOfFiniteType f] [LocallyOfFiniteType f'] (hff' : f = f')
    (hf : f ≫ sY = sX) (hf' : f' ≫ sY = sX) {p p' : ℤ} (hpp' : p = p')
    (c : BivariantClass C G sX sY f hf p) : BivariantClass C G sX sY f' hf' p' := by
  subst hff'
  subst hpp'
  exact c

/-- The transported class caps the way the original one does. -/
theorem BivariantClass.copy_cap (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    {f f' : X ⟶ Y} [LocallyOfFiniteType f] [LocallyOfFiniteType f'] (hff' : f = f')
    (hf : f ≫ sY = sX) (hf' : f' ≫ sY = sX) {p p' : ℤ} (hpp' : p = p')
    (c : BivariantClass C G sX sY f hf p) {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g]
    (k : ℤ) (α : chowGroup C (g ≫ sY) k) :
    HEq ((BivariantClass.copy C G sX sY hff' hf hf' hpp' c).cap g k α) (c.cap g k α) := by
  subst hff'
  subst hpp'
  rfl

/-! ### The diagonal and the projections -/

/-- **Stacks 0FBS, the geometric input for the first projection.** The Gysin map of Stacks 0FF3
is available for `pr_1 : X ×_Y X ⟶ X`, which is smooth because `f` is and smoothness is stable
under base change. Together with `CategoryTheory.Limits.pullback.diagonal_fst`, which says
`Δ ≫ pr_1 = 𝟙 X`, and `Stacks.Chow.gysinMapExists_diagonal_of_smooth`, this is the geometric
content the source proof of Stacks 0FBS uses. -/
@[stacks 0FBS "a geometric input: the Gysin map of the first projection X ×_Y X ⟶ X is \
available, the projection being smooth by base change; the class pr_1^! itself is not \
constructed, needing Stacks 0FBK, 0B78 and a construction of the composition of Stacks 0B75"]
theorem gysinMapExists_fst_of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] :
    GysinMapExists (pullback.fst f f) :=
  GysinMapExists.of_smooth _

/-- **Stacks 0FBS, the geometric input for the second projection.** The Gysin map of Stacks 0FF3
is available for `pr_2 : X ×_Y X ⟶ X`, which is smooth by base change; and
`CategoryTheory.Limits.pullback.diagonal_snd` says `Δ ≫ pr_2 = 𝟙 X`. -/
@[stacks 0FBS "a geometric input: the Gysin map of the second projection X ×_Y X ⟶ X is \
available, the projection being smooth by base change; the class pr_2^! itself is not \
constructed, needing Stacks 0FBK, 0B78 and a construction of the composition of Stacks 0B75"]
theorem gysinMapExists_snd_of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] :
    GysinMapExists (pullback.snd f f) :=
  GysinMapExists.of_smooth _

/-! ### The left-hand side of Stacks 0FBS, read in `A^0(X)` -/

section Composite

variable (G : GysinSystem C) {Y : Scheme.{u}} (f : X ⟶ Y) (sP : pullback f f ⟶ C.S)
  [LocallyOfFiniteType sP] [LocallyOfFiniteType (pullback.diagonal f)]
  (pr : pullback f f ⟶ X) [LocallyOfFiniteType pr]
  (hdiag : pullback.diagonal f ≫ pr = 𝟙 X) (hΔ : pullback.diagonal f ≫ sP = sX)
  (hpr : pr ≫ sX = sP) (hpp : ProperPushforwardDescends C) {p q : ℤ} (hpq : p + q = 0)

/-- **Stacks 0FBS, the left-hand side.** Let `pr : X ×_Y X ⟶ X` be a projection, so that
`Δ ≫ pr = 𝟙 X`, let `a ∈ A^p(X ⟶ X ×_Y X)` be a bivariant class for the diagonal — the slot
`Δ^!` occupies — and let `b ∈ A^q(X ×_Y X ⟶ X)` be one for the projection, the slot `pr^!`
occupies, with `p + q = 0`. If `c` witnesses that it is the composition of `a` and `b`, then the
class in `A^0(X ⟶ X)` that `c` becomes under `Δ ≫ pr = 𝟙 X` caps by the composite operation
`a ∩ (b ∩ -)`.

With `Stacks.Chow.eq_bivariantIdentityClass_iff` this says that `Δ^! ∘ pr^! = 1` holds exactly
when the composite operation acts as the identity on the Chow groups of every test scheme; and
by `Stacks.Chow.eq_of_isBivariantClassComposition` there is at most one class `c` witnessing the
composition, so no generality is lost by carrying it as a hypothesis. -/
@[stacks 0FBS "the left-hand side, read in A^0(X): the transport along Δ ≫ pr_i = 𝟙 X of a \
bivariant class witnessing the composition of one for Δ with one for pr_i in total degree 0 \
caps by the composite operation; the Gysin classes Δ^! and pr_i^! are carried as arbitrary \
bivariant classes, since Stacks 0FBK, 0B78 and a construction of the composition of \
Stacks 0B75 are all absent from this repository"]
theorem copy_cap_heq_bivariantCompositeCap
    (a : BivariantClass C G sX sP (pullback.diagonal f) hΔ p)
    (b : BivariantClass C G sP sX pr hpr q)
    (c : BivariantClass C G sX sX (pullback.diagonal f ≫ pr)
      (comp_comp_structureMorphism_eq hΔ hpr) (p + q))
    (hc : IsBivariantClassComposition C G sX sP sX (pullback.diagonal f) pr hΔ hpr hpp p q a b c)
    {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ)
    (α : chowGroup C (t ≫ sX) k) :
    HEq ((BivariantClass.copy C G sX sX hdiag (comp_comp_structureMorphism_eq hΔ hpr)
          (Category.id_comp sX) hpq c).cap t k α)
      (bivariantCompositeCap C G sX sP sX (pullback.diagonal f) pr hΔ hpr hpp p q a b t k α) :=
  (BivariantClass.copy_cap C G sX sX hdiag (comp_comp_structureMorphism_eq hΔ hpr)
    (Category.id_comp sX) hpq c t k α).trans (hc t k α)

end Composite

end Stacks.Chow

end
