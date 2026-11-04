module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.IntersectionCommutativity.ChernCapDescent
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic

/-!
# The first Chern class as a bivariant class

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and let `L` be an invertible `O_X`-module. Stacks 0FDW defines the *first
Chern class*

  `c₁(L) ∈ A^1(X)`

to be the bivariant class of Stacks 0B77, the one given by capping with `L`: for every
`g : T ⟶ X` locally of finite type and every `k` the operation
`A_k(T) ⟶ A_{k-1}(T)`, `α ↦ c₁(g^*L) ∩ α`, of Stacks 02TI. Here `A^1(X)` is `A^1(X ⟶ X)`, the
bivariant classes of degree `1` for the identity of `X`, which in this repository is
`Stacks.Chow.BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) 1`.

A bivariant class for `f : X ⟶ Y` caps into the Chow group of the chosen categorical pullback
`X ×_Y T`, so for `f = 𝟙 X` the operation above has first to be carried across the isomorphism
`X ×_X T ≅ T`. That transport is `Stacks.Chow.IdentityCapRule.transport`, and it is a bijection
onto the operations into the pullback, so the characterization of Stacks 0B77 **determines**
`c₁(L)`: this file shows the cap operation is forced, proves uniqueness, and assembles the
class.

## Main definitions

* `Stacks.Chow.IdentityCapRule.TransportFlatNaturality`,
  `Stacks.Chow.IdentityCapRule.TransportGysinNaturality` — axioms (2) and (3) of Stacks 0B76 for
  the transport of an identity cap rule, i.e. the two remaining fields of
  `Stacks.Chow.BivariantClass` at `f = 𝟙 X`.
* `Stacks.Chow.IdentityCapRule.toBivariantClass` — an identity cap rule satisfying the three
  transported axioms, as an element of `A^p(X ⟶ X)`.
* `Stacks.Chow.FirstChernCapRule` — **Stacks 02SO and 02TI as a single datum**: for every scheme
  locally of finite type over the base and every invertible module on it, the cap product
  `c₁(-) ∩ - : A_{k+1} ⟶ A_k` in every degree.
* `Stacks.Chow.firstChernIdentityCapRule` — the rule `α ↦ c₁(g^*L) ∩ α` on the test schemes.
* `Stacks.Chow.firstChernClassBivariantCap` — the cap operation of `c₁(L)`, into the Chow group
  of the chosen pullback.
* `Stacks.Chow.IsFirstChernClassBivariant` — **the characterization of Stacks 0B77**: that a
  bivariant class of degree `1` for `𝟙 X` caps by `c₁(g^*L) ∩ -` on every test scheme.
* `Stacks.Chow.firstChernClass` — **Stacks 0FDW**, `c₁(L) ∈ A^1(X)`, given the three naturality
  axioms of Stacks 0B76 for its cap operation.

## Main results

* `Stacks.Chow.isFirstChernClassBivariant_iff` — the characterization of Stacks 0B77 holds exactly
  when the cap operation **is** `Stacks.Chow.firstChernClassBivariantCap`, so Stacks 0B77 has at
  most one solution and its cap operation is forced.
* `Stacks.Chow.eq_of_isFirstChernClassBivariant` — uniqueness in Stacks 0B77, hence that
  `c₁(L)` is well defined.
* `Stacks.Chow.firstChernClassBivariantCap_proper_naturality` — axiom (1) of Stacks 0B76 for the
  forced cap operation, from the projection formula of Stacks 02SU.
* `Stacks.Chow.isFirstChernClassBivariant_firstChernClass` — the class assembled below does
  satisfy the characterization of Stacks 0B77.
* `Stacks.Chow.firstChernClass_cap` — its cap operation.

## Implementation notes

`Stacks.Chow.FirstChernCapRule` is data, so it is a parameter of every declaration below rather
than a quantified hypothesis: for data, `∀ G, P G` is strictly stronger than `P G₀`. It is
global, defined for every scheme locally of finite type over the base, because the cap operation
of a bivariant class acts on every test scheme and the operation attached to `g : T ⟶ X` is that
of `g^*L`, which lives on `T`.

The source states the operation of Stacks 02TI as `A_{k+1}(X) ⟶ A_k(X)`, and
`Stacks.Chow.ChernCapOperator.capOnChow` keeps that indexing, while a bivariant class of degree
`1` operates `A_k(T) ⟶ A_{k-1}(T)`. These are the same operation at `k ↦ k - 1`, but `k` and
`(k - 1) + 1` are not the same term, so `Stacks.Chow.firstChernIdentityCapRule` carries the
transport `Stacks.Chow.chowGroupDegreeCast`.

`Stacks.Chow.firstChernClass` takes the three naturality axioms of Stacks 0B76 for the forced cap
operation as hypotheses, each literally the corresponding field of `Stacks.Chow.BivariantClass`.

## References

* [Stacks Project, Tag 0FDW](https://stacks.math.columbia.edu/tag/0FDW)
* [Stacks Project, Tag 0B77](https://stacks.math.columbia.edu/tag/0B77)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
* [Stacks Project, Tag 02SU](https://stacks.math.columbia.edu/tag/02SU)
* [Stacks Project, Tag 02SS](https://stacks.math.columbia.edu/tag/02SS)
* [Stacks Project, Tag 0B72](https://stacks.math.columbia.edu/tag/0B72)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (p : ℤ)

/-! ### The two remaining axioms of Stacks 0B76 for a transported rule -/

/-- **Stacks 0B76 (2) for the transport of an identity cap rule.** The flat-pullback axiom of a
bivariant class of degree `p` for `𝟙 X`, for the cap operation
`Stacks.Chow.IdentityCapRule.transport`: this is the `flat_naturality` field of
`Stacks.Chow.BivariantClass` at `f = 𝟙 X` and `cap = op.transport`.

It is an `HEq` because the flat pullback of a `k`-cycle has degree `k + r`, so the two sides sit
in degrees `(k + r) - p` and `(k - p) + r`, which are the same integer and not the same term. -/
def IdentityCapRule.TransportFlatNaturality (op : IdentityCapRule C sX p) : Prop :=
  ∀ {T T' : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (h : T' ⟶ T)
      [LocallyOfFiniteType h] [Flat h] (r : ℕ) (hr : AlgebraicGeometry.RelativeDimension h r)
      (h' : pullback (𝟙 X) (h ≫ g) ⟶ pullback (𝟙 X) g)
      (sq : IsPullback (pullback.snd (𝟙 X) (h ≫ g)) h' h (pullback.snd (𝟙 X) g))
      (hfst : h' ≫ pullback.fst (𝟙 X) g = pullback.fst (𝟙 X) (h ≫ g)) (k : ℤ),
      letI : LocallyOfFiniteType h' :=
        MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
      letI : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
      ∀ (hr' : AlgebraicGeometry.RelativeDimension h' r)
        (hfac : FlatPullbackFactorsThroughRationalEquivalence C ((h ≫ g) ≫ sX) (g ≫ sX) h
          (by simp [Category.assoc]) r hr k)
        (hfac' : FlatPullbackFactorsThroughRationalEquivalence C
          (pullback.fst (𝟙 X) (h ≫ g) ≫ sX) (pullback.fst (𝟙 X) g ≫ sX) h'
          (by rw [← Category.assoc, hfst]) r hr' (k - p))
        (α : chowGroup C (g ≫ sX) k),
        HEq
          (op.transport C sX p (h ≫ g) (k + (r : ℤ))
            (flatPullbackChow C ((h ≫ g) ≫ sX) (g ≫ sX) h (by simp [Category.assoc]) r hr k
              hfac α))
          (flatPullbackChow C (pullback.fst (𝟙 X) (h ≫ g) ≫ sX) (pullback.fst (𝟙 X) g ≫ sX) h'
            (by rw [← Category.assoc, hfst]) r hr' (k - p) hfac' (op.transport C sX p g k α))

/-- **Stacks 0B76 (3) for the transport of an identity cap rule.** The Gysin axiom of a bivariant
class of degree `p` for `𝟙 X`, for the cap operation
`Stacks.Chow.IdentityCapRule.transport`: this is the `gysin_naturality` field of
`Stacks.Chow.BivariantClass` at `f = 𝟙 X` and `cap = op.transport`.

The identification of the base change of the zero scheme `D ⊆ T` with the zero scheme `E` of the
pulled-back section is the isomorphism `e`, and the induced map on Chow groups is proper
pushforward along `e.hom`. -/
def IdentityCapRule.TransportGysinNaturality (op : IdentityCapRule C sX p) (G : GysinSystem C) :
    Prop :=
  ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (N : T.Modules)
      [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property N]
      [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback (𝟙 X) g).sheaf.obj
        (pullback (𝟙 X) g).ringCatSheaf.property
        ((Scheme.Modules.pullback (pullback.snd (𝟙 X) g)).obj N)]
      (s : Γ(N, ⊤)) (k : ℤ),
      let D := Stacks.Divisors.zeroScheme T N s
      let N' := (Scheme.Modules.pullback (pullback.snd (𝟙 X) g)).obj N
      let s' := AlgebraicGeometry.pullbackGlobalSections (pullback.snd (𝟙 X) g) N s
      let E := Stacks.Divisors.zeroScheme (pullback (𝟙 X) g) N' s'
      ∀ (e : pullback (𝟙 X) (D.subschemeι ≫ g) ≅ E.subscheme)
        (_he : e.hom ≫ E.subschemeι = bivariantBaseChangeMap (𝟙 X) g D.subschemeι)
        (hbase : e.hom ≫ (E.subschemeι ≫ pullback.fst (𝟙 X) g ≫ sX) =
          pullback.fst (𝟙 X) (D.subschemeι ≫ g) ≫ sX)
        (hfac : ProperPushforwardFactorsThroughRationalEquivalence C
          (pullback.fst (𝟙 X) (D.subschemeι ≫ g) ≫ sX)
          (E.subschemeι ≫ pullback.fst (𝟙 X) g ≫ sX) e.hom hbase (k - p))
        (α : chowGroup C (g ≫ sX) (k + 1)),
        properChowPushforward C (pullback.fst (𝟙 X) (D.subschemeι ≫ g) ≫ sX)
            (E.subschemeι ≫ pullback.fst (𝟙 X) g ≫ sX) e.hom hbase (k - p) hfac
            (op.transport C sX p (D.subschemeι ≫ g) k (G.onChow (g ≫ sX) N s k α)) =
          G.onChow (pullback.fst (𝟙 X) g ≫ sX) N' s' (k - p)
            (Eq.mp (congrArg (chowGroup C (pullback.fst (𝟙 X) g ≫ sX))
              (by omega : (k + 1) - p = (k - p) + 1)) (op.transport C sX p g (k + 1) α))

/-- An identity cap rule whose transport satisfies the three naturality axioms of Stacks 0B76 is a
bivariant class of degree `p` for `𝟙 X`, that is, an element of `A^p(X ⟶ X)`. -/
def IdentityCapRule.toBivariantClass (op : IdentityCapRule C sX p) (G : GysinSystem C)
    (hproper : op.ProperNaturality C sX p) (hflat : op.TransportFlatNaturality C sX p)
    (hgysin : op.TransportGysinNaturality C sX p G) :
    BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) p where
  cap g _ k := op.transport C sX p g k
  cap_properPushforward := by
    intro T T' g hg h hh h' sq hfst k α
    exact op.transport_proper_naturality C sX p hproper g h h' sq hfst k _ _ α
  cap_flatPullbackChow := by
    intro T₀ T₀' g₀ _ w₀ _ _ r₀ hr₀ w₀' sq₀ hfst₀ k₀ α₀
    exact hflat g₀ w₀ r₀ hr₀ w₀' sq₀ hfst₀ k₀ _ _ _ α₀
  cap_gysin := by
    intro T₀ g₀ _ L₀ _ s₀ k₀ _ _ _ _ ε₀ hε₀ hbase₀ α₀
    exact hgysin g₀ L₀ s₀ k₀ ε₀ hε₀ hbase₀ _ α₀

/-! ### The cap product of the first Chern class -/

/-- **Stacks 02SO and 02TI as a single datum.** For every scheme locally of finite type over the
base and every invertible module on it, the first Chern class cap product
`c₁(-) ∩ - : A_{k+1} ⟶ A_k` in every degree. -/
abbrev FirstChernCapRule (C : ChowSituation.{u}) : Type (u + 1) :=
  ∀ {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q] (M : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property M],
    ChernCapOperator C q

variable (fcap : FirstChernCapRule C) (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- **Stacks 0B77, the operation on the test schemes.** The identity cap rule of degree `1` given
by capping with the first Chern class of the pulled-back module: `α ↦ c₁(g^*L) ∩ α` on
`A_k(T)`, for `g : T ⟶ X`. -/
def firstChernIdentityCapRule : IdentityCapRule C sX 1 := fun {_T} g _ k ↦
  chowGroupDegreeCast C (g ≫ sX) (by omega)
    ((fcap (g ≫ sX) ((Scheme.Modules.pullback g).obj L)).capOnChow C (g ≫ sX) (k - 1))

/-- **Stacks 0B77, the cap operation.** The cap operation of the bivariant first Chern class:
capping with `c₁(g^*L)` on the test scheme, pushed forward to the chosen pullback `X ×_X T`. -/
def firstChernClassBivariantCap {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ) :
    chowGroup C (g ≫ sX) k →+ chowGroup C (pullback.fst (𝟙 X) g ≫ sX) (k - 1) :=
  IdentityCapRule.transport C sX 1 (firstChernIdentityCapRule C sX fcap L) g k

/-! ### The characterization of Stacks 0B77, and uniqueness -/

/-- **Stacks 0B77.** The characterization of the bivariant first Chern class: a bivariant class
`c` of degree `1` for `𝟙 X` is *the* first Chern class of `L` when, for every test scheme
`g : T ⟶ X` and every `k`, pushing `c ∩ α` forward along the projection `X ×_X T ⟶ T` gives
`c₁(g^*L) ∩ α`. -/
def IsFirstChernClassBivariant (G : GysinSystem C)
    (c : BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) 1) : Prop :=
  ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ sX) k),
    chowPushforwardOfIso C (pullback.fst (𝟙 X) g ≫ sX) (g ≫ sX) (identityBaseChangeIso g).hom
        (identityBaseChangeIso_hom_comp_base C sX g) (k - 1) (c.cap g k α) =
      firstChernIdentityCapRule C sX fcap L g k α

/-- **Stacks 0B77, the cap operation is forced.** A bivariant class satisfies the characterization
of the first Chern class exactly when its cap operation is
`Stacks.Chow.firstChernClassBivariantCap`. -/
theorem isFirstChernClassBivariant_iff (G : GysinSystem C)
    (c : BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) 1) :
    IsFirstChernClassBivariant C sX fcap L G c ↔
      ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ),
        c.cap g k = firstChernClassBivariantCap C sX fcap L g k :=
  forall_congr' fun _ ↦ forall_congr' fun g ↦ forall_congr' fun _ ↦ forall_congr' fun k ↦
    IdentityCapRule.eq_transport_iff C sX 1 (firstChernIdentityCapRule C sX fcap L) g k (c.cap g k)

/-- **Uniqueness in Stacks 0B77.** Two bivariant classes satisfying the characterization of the
first Chern class of `L` are equal. -/
theorem eq_of_isFirstChernClassBivariant (G : GysinSystem C)
    {c d : BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) 1}
    (hc : IsFirstChernClassBivariant C sX fcap L G c)
    (hd : IsFirstChernClassBivariant C sX fcap L G d) : c = d :=
  BivariantClass.eq_of_pushforward_cap_eq C sX 1 G c d
    fun {T} g _ k α ↦ (hc (T := T) g k α).trans (hd (T := T) g k α).symm

/-! ### The axioms of Stacks 0B76 for the forced cap operation -/

/-- **Stacks 0B76 (1) for the bivariant first Chern class.** Granted the projection formula of
Stacks 02SU for the cap product on the test schemes, the forced cap operation of Stacks 0B77
satisfies the proper-pushforward axiom of a bivariant class. -/
theorem firstChernClassBivariantCap_proper_naturality
    (hproper : IdentityCapRule.ProperNaturality C sX 1 (firstChernIdentityCapRule C sX fcap L))
    {T T' : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (h : T' ⟶ T) [IsProper h]
    (h' : pullback (𝟙 X) (h ≫ g) ⟶ pullback (𝟙 X) g)
    (sq : IsPullback (pullback.snd (𝟙 X) (h ≫ g)) h' h (pullback.snd (𝟙 X) g))
    (hfst : h' ≫ pullback.fst (𝟙 X) g = pullback.fst (𝟙 X) (h ≫ g)) (k : ℤ) :
    letI : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
    ∀ (hfac : ProperPushforwardFactorsThroughRationalEquivalence C ((h ≫ g) ≫ sX) (g ≫ sX) h
        (by simp [Category.assoc]) k)
      (hfac' : ProperPushforwardFactorsThroughRationalEquivalence C
        (pullback.fst (𝟙 X) (h ≫ g) ≫ sX) (pullback.fst (𝟙 X) g ≫ sX) h'
        (by rw [← Category.assoc, hfst]) (k - 1))
      (α : chowGroup C ((h ≫ g) ≫ sX) k),
      firstChernClassBivariantCap C sX fcap L g k
          (properChowPushforward C ((h ≫ g) ≫ sX) (g ≫ sX) h (by simp [Category.assoc]) k
            hfac α) =
        properChowPushforward C (pullback.fst (𝟙 X) (h ≫ g) ≫ sX) (pullback.fst (𝟙 X) g ≫ sX) h'
          (by rw [← Category.assoc, hfst]) (k - 1) hfac'
          (firstChernClassBivariantCap C sX fcap L (h ≫ g) k α) :=
  IdentityCapRule.transport_proper_naturality C sX 1 (firstChernIdentityCapRule C sX fcap L)
    hproper g h h' sq hfst k

/-! ### The first Chern class -/

/-- **Stacks 0FDW.** The *first Chern class* `c₁(L) ∈ A^1(X)` of an invertible module `L` on a
scheme `X` locally of finite type over the base: the bivariant class of degree `1` for `𝟙 X`
given by capping with `L`, which is Stacks 0B77, granted the three naturality axioms of Stacks
0B76: `hproper` the projection formula of Stacks 02SU read on the test schemes, `hflat` and
`hgysin` the flat and Gysin axioms. -/
def firstChernClass (G : GysinSystem C)
    (hproper : IdentityCapRule.ProperNaturality C sX 1 (firstChernIdentityCapRule C sX fcap L))
    (hflat : IdentityCapRule.TransportFlatNaturality C sX 1
      (firstChernIdentityCapRule C sX fcap L))
    (hgysin : IdentityCapRule.TransportGysinNaturality C sX 1
      (firstChernIdentityCapRule C sX fcap L) G) :
    BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) 1 :=
  IdentityCapRule.toBivariantClass C sX 1 (firstChernIdentityCapRule C sX fcap L) G hproper hflat
    hgysin

/-- The cap operation of `c₁(L)` is `Stacks.Chow.firstChernClassBivariantCap`. -/
@[simp]
theorem firstChernClass_cap (G : GysinSystem C)
    (hproper : IdentityCapRule.ProperNaturality C sX 1 (firstChernIdentityCapRule C sX fcap L))
    (hflat : IdentityCapRule.TransportFlatNaturality C sX 1
      (firstChernIdentityCapRule C sX fcap L))
    (hgysin : IdentityCapRule.TransportGysinNaturality C sX 1
      (firstChernIdentityCapRule C sX fcap L) G)
    {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ) :
    (firstChernClass C sX fcap L G hproper hflat hgysin).cap g k =
      firstChernClassBivariantCap C sX fcap L g k :=
  rfl

/-- **Stacks 0B77.** The class `Stacks.Chow.firstChernClass` does satisfy the characterization of
the first Chern class: it caps by `c₁(g^*L) ∩ -` on every test scheme. -/
theorem isFirstChernClassBivariant_firstChernClass (G : GysinSystem C)
    (hproper : IdentityCapRule.ProperNaturality C sX 1 (firstChernIdentityCapRule C sX fcap L))
    (hflat : IdentityCapRule.TransportFlatNaturality C sX 1
      (firstChernIdentityCapRule C sX fcap L))
    (hgysin : IdentityCapRule.TransportGysinNaturality C sX 1
      (firstChernIdentityCapRule C sX fcap L) G) :
    IsFirstChernClassBivariant C sX fcap L G
      (firstChernClass C sX fcap L G hproper hflat hgysin) :=
  fun {_T} g _ k α ↦
    IdentityCapRule.pushforward_transport C sX 1 (firstChernIdentityCapRule C sX fcap L) g k α

end Stacks.Chow

end
