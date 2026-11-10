module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.Composition
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.BaseChange

/-!
# Flat pullback as a bivariant class

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `f : X ⟶ Y` be a
flat morphism of relative dimension `r` between schemes locally of finite type over `S`.
**Stacks 0B78** asserts that the rule which assigns to a test scheme `g : T ⟶ Y` the flat
pullback `(f')^* : A_k(T) ⟶ A_{k+r}(X ×_Y T)` along the base change `f' : X ×_Y T ⟶ T` is a
bivariant class of degree `-r` for `f`.

## Main definitions

* `Stacks.Chow.ProperPushforwardFlatPullbackBaseChange` — Stacks 02RG on Chow groups, as a
  hypothesis.
* `Stacks.Chow.GysinSystem.FlatPullbackNaturality` — Stacks 0B71 on Chow groups, with the
  identification of Stacks 0B6Y, as a hypothesis.
* `Stacks.Chow.flatPullbackBivariantCap` — the cap operation: flat pullback along the base change
  of `f`, read in the degree a class of degree `-r` produces. This is **not** declared here; it is
  imported from `StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullback`, which this module
  builds on. See the implementation notes.
* `Stacks.Chow.flatPullbackBivariantClass` — **Stacks 0B78**, that cap operation together with
  the three naturality laws, as an element of `A^{-r}(X ⟶ Y)`.

## Main results

* `Stacks.Chow.flatPullbackChow_comp_heq` — **Stacks 02RD on Chow groups**: pulling back along
  `w` and then along `v` is pulling back along `v ≫ w`.
* `Stacks.Chow.relativeDimension_pullbackSnd` — **Stacks 02NK** for the base change of `f` along
  a test scheme.
* `Stacks.Chow.flatPullbackBivariantCap_proper_naturality` and
  `Stacks.Chow.flatPullbackBivariantCap_gysin_naturality` — the projection formula and the Gysin
  law of Stacks 0B76 for the cap operation, from the hypotheses `hRG` and `h71`. The third law,
  the flat-pullback law `Stacks.Chow.flatPullbackBivariantCap_flat_naturality`, is the one that is
  proved outright rather than assumed, and it too is imported rather than declared here.
* `Stacks.Chow.flatPullbackBivariantClass_cap` — the class of Stacks 0B78 caps by flat pullback.

## Implementation notes

### The cap operation is imported, not redeclared

`Stacks.Chow.flatPullbackBivariantCap`, `Stacks.Chow.flatPullbackBivariantCap_heq` and
`Stacks.Chow.flatPullbackBivariantCap_flat_naturality` come from
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullback`. The descent hypothesis of Stacks
02S1
is bundled here as `Stacks.Chow.FlatPullbackDescends C` and quantified inline there; these are the
same proposition — `Stacks.Chow.FlatPullbackDescends` is definitionally the inline hypothesis — so
the imported declarations serve both, and no second construction of the cap operation is made.

What is left here is what the imported module does not provide: the projection formula, the Gysin
law, the bivariant class of Stacks 0B78 itself, and the proof that that class satisfies the
imported characterization.

### Which inputs are proved here and which are hypotheses

The source deduces Stacks 0B78 from four lemmas: Stacks 02S1, 02RD, 02RG and 0B71. Two further
inputs are needed to write the cap operation down at all, namely that the base change of `f`
along a test scheme is again flat, which is formal, and that it has relative dimension `r`, which
is Stacks 02NK.

Of these, Stacks 02RD and Stacks 02NK are theorems of this repository and are used as such.
Stacks 02RD, `Stacks.Chow.flatPullback_comp`, is descended to Chow groups here as
`Stacks.Chow.flatPullbackChow_comp_heq`, and it is what discharges the flat-pullback law of
Stacks 0B76 outright rather than assuming it; that discharge is
`Stacks.Chow.flatPullbackBivariantCap_flat_naturality`, which is imported. Stacks 02NK,
`AlgebraicGeometry.RelativeDimension.of_isPullback`, gives the relative dimension of every base
change, in `Stacks.Chow.relativeDimension_pullbackSnd`.

The other three are not in this repository and are carried as explicitly named hypotheses of
`Stacks.Chow.flatPullbackBivariantClass`, each standing in for one tag of the source:

* `hS1 : Stacks.Chow.FlatPullbackDescends C` is **Stacks 02S1**, bundled over all flat morphisms
  over the base. Without it flat pullback does not descend from cycles to Chow groups, so the cap
  operation does not exist. In this repository Stacks 02S1 is proved only along open immersions.
* `hRG : Stacks.Chow.ProperPushforwardFlatPullbackBaseChange C` is **Stacks 02RG** on Chow
  groups, in the four-corner form of the source: a cartesian square with proper horizontal legs
  and flat vertical legs of a common relative dimension. In this repository Stacks 02RG is proved
  only when the two horizontal legs are isomorphisms,
  `Stacks.Chow.flatPullbackChow_chowPushforwardOfIso`, which is the instance of this hypothesis
  in which `u₀` and `u₁` are invertible.
* `h71 : G.FlatPullbackNaturality r` is **Stacks 0B71** on Chow groups, together with the
  identification of **Stacks 0B6Y** of the zero scheme upstairs with the base change of the zero
  scheme downstairs, which is what the isomorphism `ε` in that hypothesis records. Neither tag is
  in this repository.

Each of the three is a `Pi` into `Prop`, hence itself a `Prop`, so assuming it asserts exactly
the corresponding statement and nothing more; substituting the genuine lemmas discharges it and
leaves Stacks 0B78 unconditional. None of the three mentions `Stacks.Chow.BivariantClass`, and
none asserts any part of the conclusion of Stacks 0B78: that conclusion is that *this particular
rule is a bivariant class*, whereas `hS1`, `hRG` and `h71` are statements about flat pullback,
proper pushforward and Gysin maps in the generality in which the source states them, with no
reference to `f`.

### The Gysin system

As everywhere in this development the class is stated against a `Stacks.Chow.GysinSystem`, which
supplies the first Chern class rule of Stacks 02SO and the vanishing of Stacks 02TO; see the
implementation notes of `StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Basic` for why that datum
is a parameter rather than a quantified hypothesis.

### Degrees

A bivariant class of degree `p` sends degree `k` to degree `k - p`, while flat pullback of
relative dimension `r` sends it to `k + r`. With `p = -r` these are the same integer and not the
same term, so the cap operation composes flat pullback with the transport
`Stacks.Chow.chowGroupDegreeEquiv`. The three naturality laws are therefore proved by moving
every transport out of the way with the congruence lemmas
`Stacks.Chow.flatPullbackChow_heq_congr`, `Stacks.Chow.properChowPushforward_heq_congr` and
`Stacks.Chow.gysinSystemOnChow_heq_congr`, each of which says that the operation in question
depends on its degree and its argument only up to heterogeneous equality.

## References

* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 02RD](https://stacks.math.columbia.edu/tag/02RD)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 0B71](https://stacks.math.columbia.edu/tag/0B71)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 02NK](https://stacks.math.columbia.edu/tag/02NK)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The three operations up to heterogeneous equality -/

/-- Flat pullback on Chow groups depends on its morphism, its relative dimension, its degree and
its argument only up to equality and heterogeneous equality. -/
theorem flatPullbackChow_heq_congr (C : ChowSituation.{u}) {A B : Scheme.{u}} (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (v v' : A ⟶ B)
    [LocallyOfFiniteType v] [Flat v] [LocallyOfFiniteType v'] [Flat v'] (hv : v ≫ sB = sA)
    (hv' : v' ≫ sB = sA) (hvv' : v = v') {n n' : ℕ} (hnn' : n = n')
    (hvn : AlgebraicGeometry.RelativeDimension v n)
    (hv'n' : AlgebraicGeometry.RelativeDimension v' n') {k k' : ℤ} (hkk' : k = k')
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C sA sB v hv n hvn k)
    (hfac' : FlatPullbackFactorsThroughRationalEquivalence C sA sB v' hv' n' hv'n' k')
    (α : chowGroup C sB k) (α' : chowGroup C sB k') (hαα' : α ≍ α') :
    flatPullbackChow C sA sB v hv n hvn k hfac α ≍
      flatPullbackChow C sA sB v' hv' n' hv'n' k' hfac' α' := by
  subst hvv'
  subst hnn'
  subst hkk'
  obtain rfl := eq_of_heq hαα'
  rfl

/-- Proper pushforward on Chow groups depends on its degree and its argument only up to equality
and heterogeneous equality. -/
theorem properChowPushforward_heq_congr (C : ChowSituation.{u}) {A B : Scheme.{u}} (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (u : A ⟶ B) [IsProper u]
    (hu : u ≫ sB = sA) {k k' : ℤ} (hkk' : k = k')
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sA sB u hu k)
    (hfac' : ProperPushforwardFactorsThroughRationalEquivalence C sA sB u hu k')
    (α : chowGroup C sA k) (α' : chowGroup C sA k') (hαα' : α ≍ α') :
    properChowPushforward C sA sB u hu k hfac α ≍
      properChowPushforward C sA sB u hu k' hfac' α' := by
  subst hkk'
  obtain rfl := eq_of_heq hαα'
  rfl

/-- The Gysin map of a Gysin system depends on its degree and its argument only up to equality and
heterogeneous equality. -/
theorem gysinSystemOnChow_heq_congr {C : ChowSituation.{u}} (G : GysinSystem C) {T : Scheme.{u}}
    (q : T ⟶ C.S) [LocallyOfFiniteType q] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) {k k' : ℤ} (hkk' : k = k') (α : chowGroup C q (k + 1))
    (α' : chowGroup C q (k' + 1)) (hαα' : α ≍ α') :
    G.onChow q L s k α ≍ G.onChow q L s k' α' := by
  subst hkk'
  obtain rfl := eq_of_heq hαα'
  rfl

/-- Transport of a Chow class along an equality of degrees, in the `Eq.mp` form in which the
Gysin law of `Stacks.Chow.BivariantClass` states it, does not change the class. -/
theorem eq_mp_chowGroup_heq (C : ChowSituation.{u}) {A : Scheme.{u}} (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] {k l : ℤ} (hkl : k = l) (α : chowGroup C sA k) :
    Eq.mp (congrArg (chowGroup C sA) hkl) α ≍ α := by
  subst hkl
  rfl

/-- The class of a cycle depends on its degree and the cycle only up to equality and
heterogeneous equality. -/
theorem chowGroupMk_heq_congr (C : ChowSituation.{u}) {A : Scheme.{u}} (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] {j j' : ℤ} (hjj' : j = j') (c : CycleGroup C sA j)
    (c' : CycleGroup C sA j') (hcc' : c ≍ c') :
    (QuotientAddGroup.mk' (rationalEquivalences C sA j) c : chowGroup C sA j) ≍
      QuotientAddGroup.mk' (rationalEquivalences C sA j') c' := by
  subst hjj'
  obtain rfl := eq_of_heq hcc'
  rfl

/-! ### Stacks 02RD on Chow groups -/

/-- **Stacks 02RD on Chow groups.** Flat pullback on Chow groups is compatible with composition:
pulling back along `w` of relative dimension `m` and then along `v` of relative dimension `n` is
pulling back along `v ≫ w` of relative dimension `n + m`. The two degrees are the same integer
written two ways, whence the heterogeneous equality.

This is the cycle-level identity `Stacks.Chow.flatPullback_comp` descended through rational
equivalence, so it is stated against the bundled form of Stacks 02S1 that lets all three
pullbacks descend. -/
theorem flatPullbackChow_comp_heq (C : ChowSituation.{u}) (hS1 : FlatPullbackDescends C)
    {A B D : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S)
    [LocallyOfFiniteType sB] (sD : D ⟶ C.S) [LocallyOfFiniteType sD] (v : A ⟶ B)
    [LocallyOfFiniteType v] [Flat v] (w : B ⟶ D) [LocallyOfFiniteType w] [Flat w]
    (hv : v ≫ sB = sA) (hw : w ≫ sD = sB) (n m : ℕ)
    (hvn : AlgebraicGeometry.RelativeDimension v n)
    (hwm : AlgebraicGeometry.RelativeDimension w m) (k : ℤ) (α : chowGroup C sD k) :
    flatPullbackChow C sA sB v hv n hvn (k + (m : ℤ)) (hS1 sA sB v hv n hvn (k + (m : ℤ)))
        (flatPullbackChow C sB sD w hw m hwm k (hS1 sB sD w hw m hwm k) α) ≍
      flatPullbackChow C sA sD (v ≫ w) (by rw [Category.assoc, hw, hv]) (n + m)
        (AlgebraicGeometry.RelativeDimension.comp_of_flat v w hvn hwm) k
        (hS1 sA sD (v ≫ w) (by rw [Category.assoc, hw, hv]) (n + m)
          (AlgebraicGeometry.RelativeDimension.comp_of_flat v w hvn hwm) k) α := by
  induction α using QuotientAddGroup.induction_on with
  | H c =>
    have hcast : k + (m : ℤ) + (n : ℤ) = k + ((n + m : ℕ) : ℤ) := by push_cast; ring
    have hc := flatPullback_comp C sA sB sD v w hv hw n m hvn hwm k hcast c
    exact chowGroupMk_heq_congr C sA hcast _ _ ((eqRec_heq hcast _).symm.trans (heq_of_eq hc))

/-! ### The base change of a flat morphism along a test scheme -/

/-- The base change `X ×_Y T ⟶ T` of `f : X ⟶ Y` along a test scheme `g : T ⟶ Y` is a morphism
over the base: it carries the structure morphism of `T` to the one of `X ×_Y T`. -/
theorem pullbackSnd_comp_structureMorphism {S X Y T : Scheme.{u}} {sX : X ⟶ S} {sY : Y ⟶ S}
    {f : X ⟶ Y} (hf : f ≫ sY = sX) (g : T ⟶ Y) :
    pullback.snd f g ≫ (g ≫ sY) = pullback.fst f g ≫ sX := by
  rw [← Category.assoc, ← pullback.condition, Category.assoc, hf]

/-- **Stacks 02NK.** The base change `X ×_Y T ⟶ T` of a flat morphism of relative dimension `r`
along a test scheme is again of relative dimension `r`. -/
theorem relativeDimension_pullbackSnd {X Y T : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    {r : ℕ} (hfr : AlgebraicGeometry.RelativeDimension f r) (g : T ⟶ Y) :
    AlgebraicGeometry.RelativeDimension (pullback.snd f g) r :=
  AlgebraicGeometry.RelativeDimension.of_isPullback (IsPullback.of_hasPullback f g) hfr

/-! ### Stacks 02RG and Stacks 0B71 as hypotheses -/

/-- **Stacks 02RG on Chow groups.** In a cartesian square with horizontal legs `u₀ : A₀ ⟶ B₀` and
`u₁ : A₁ ⟶ B₁` proper and vertical legs `d : A₁ ⟶ A₀` and `v : B₁ ⟶ B₀` flat of relative
dimension `r`, all over the base, flat pullback commutes with proper pushforward.

Carried as a hypothesis, because Stacks 02RG is proved in this repository only when the two
horizontal legs are isomorphisms. That case,
`Stacks.Chow.flatPullbackChow_chowPushforwardOfIso`, is the instance of this statement in which
`u₀` and `u₁` are invertible. -/
def ProperPushforwardFlatPullbackBaseChange (C : ChowSituation.{u}) : Prop :=
  ∀ {A₀ A₁ B₀ B₁ : Scheme.{u}} (sA₀ : A₀ ⟶ C.S) [LocallyOfFiniteType sA₀] (sA₁ : A₁ ⟶ C.S)
    [LocallyOfFiniteType sA₁] (sB₀ : B₀ ⟶ C.S) [LocallyOfFiniteType sB₀] (sB₁ : B₁ ⟶ C.S)
    [LocallyOfFiniteType sB₁] (u₀ : A₀ ⟶ B₀) [IsProper u₀] (hu₀ : u₀ ≫ sB₀ = sA₀)
    (u₁ : A₁ ⟶ B₁) [IsProper u₁] (hu₁ : u₁ ≫ sB₁ = sA₁) (d : A₁ ⟶ A₀) [LocallyOfFiniteType d]
    [Flat d] (hd : d ≫ sA₀ = sA₁) (v : B₁ ⟶ B₀) [LocallyOfFiniteType v] [Flat v]
    (hv : v ≫ sB₀ = sB₁) (_hsq : IsPullback d u₁ u₀ v) (r : ℕ)
    (hdr : AlgebraicGeometry.RelativeDimension d r)
    (hvr : AlgebraicGeometry.RelativeDimension v r) (k : ℤ)
    (hfacd : FlatPullbackFactorsThroughRationalEquivalence C sA₁ sA₀ d hd r hdr k)
    (hfacv : FlatPullbackFactorsThroughRationalEquivalence C sB₁ sB₀ v hv r hvr k)
    (hppu₀ : ProperPushforwardFactorsThroughRationalEquivalence C sA₀ sB₀ u₀ hu₀ k)
    (hppu₁ : ProperPushforwardFactorsThroughRationalEquivalence C sA₁ sB₁ u₁ hu₁ (k + (r : ℤ)))
    (α : chowGroup C sA₀ k),
    flatPullbackChow C sB₁ sB₀ v hv r hvr k hfacv
        (properChowPushforward C sA₀ sB₀ u₀ hu₀ k hppu₀ α) =
      properChowPushforward C sA₁ sB₁ u₁ hu₁ (k + (r : ℤ)) hppu₁
        (flatPullbackChow C sA₁ sA₀ d hd r hdr k hfacd α)

/-- **Stacks 0B71 on Chow groups, with the identification of Stacks 0B6Y.** Let `v : A ⟶ T` be
flat of relative dimension `r` over the base, let `L` be an invertible module on `T` with a
global section `s`, and let `D ⊆ T` and `E ⊆ A` be the zero schemes of `s` and of its pullback.
Let `v'' : A'' ⟶ D` be flat of relative dimension `r` and let `ε : A'' ≅ E` identify its source
with the zero scheme upstairs, over the base. Then the Gysin map of `s` commutes with flat
pullback.

The isomorphism `ε` is the identification of Stacks 0B6Y of the zero scheme upstairs with the
base change of the zero scheme downstairs; the identity itself is Stacks 0B71. Neither is in this
repository, so both are carried here. -/
def GysinSystem.FlatPullbackNaturality {C : ChowSituation.{u}} (G : GysinSystem C) (r : ℕ) :
    Prop :=
  ∀ {T A A'' : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q] (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] (sA'' : A'' ⟶ C.S) [LocallyOfFiniteType sA''] (v : A ⟶ T)
    [LocallyOfFiniteType v] [Flat v] (hv : v ≫ q = sA)
    (hvr : AlgebraicGeometry.RelativeDimension v r) (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible A.sheaf.obj A.ringCatSheaf.property
      ((Scheme.Modules.pullback v).obj L)]
    (s : Γ(L, ⊤)) (k : ℤ) (v'' : A'' ⟶ (Stacks.Divisors.zeroScheme T L s).subscheme)
    [LocallyOfFiniteType v''] [Flat v'']
    (hv'' : v'' ≫ ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ q) = sA'')
    (hv''r : AlgebraicGeometry.RelativeDimension v'' r)
    (ε : A'' ≅ (Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback v).obj L)
      (AlgebraicGeometry.pullbackGlobalSections v L s)).subscheme)
    (hε : ε.hom ≫ ((Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback v).obj L)
      (AlgebraicGeometry.pullbackGlobalSections v L s)).subschemeι ≫ sA) = sA'')
    (hfacv'' : FlatPullbackFactorsThroughRationalEquivalence C sA''
      ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ q) v'' hv'' r hv''r k)
    (hfacv : FlatPullbackFactorsThroughRationalEquivalence C sA q v hv r hvr (k + 1))
    (hpp : ProperPushforwardFactorsThroughRationalEquivalence C sA''
      ((Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback v).obj L)
        (AlgebraicGeometry.pullbackGlobalSections v L s)).subschemeι ≫ sA) ε.hom hε
      (k + (r : ℤ)))
    (α : chowGroup C q (k + 1)),
    properChowPushforward C sA''
        ((Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback v).obj L)
          (AlgebraicGeometry.pullbackGlobalSections v L s)).subschemeι ≫ sA) ε.hom hε
        (k + (r : ℤ)) hpp
        (flatPullbackChow C sA'' ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ q) v'' hv'' r
          hv''r k hfacv'' (G.onChow q L s k α)) =
      G.onChow sA ((Scheme.Modules.pullback v).obj L)
        (AlgebraicGeometry.pullbackGlobalSections v L s) (k + (r : ℤ))
        (chowGroupDegreeEquiv C sA (by ring : k + 1 + (r : ℤ) = k + (r : ℤ) + 1)
          (flatPullbackChow C sA q v hv r hvr (k + 1) hfacv α))

/-! ### The cap operation of Stacks 0B78 -/

section Class

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
  [LocallyOfFiniteType f] [Flat f] (hf : f ≫ sY = sX) (r : ℕ)
  (hfr : AlgebraicGeometry.RelativeDimension f r) (hS1 : FlatPullbackDescends C)

/-! ### The three naturality laws -/

/-- Proper pushforward of the flat pullback along the base change of `f` is proper pushforward of
the cap operation, up to the transport of degrees. -/
private theorem properChowPushforward_flatPullbackBivariantCap_heq {T' B : Scheme.{u}}
    (g' : T' ⟶ Y) [LocallyOfFiniteType g'] {sB : B ⟶ C.S} [LocallyOfFiniteType sB]
    (u : pullback f g' ⟶ B) [IsProper u] (hu : u ≫ sB = pullback.fst f g' ≫ sX) (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C _ sB u hu (k - -(r : ℤ)))
    (α : chowGroup C (g' ≫ sY) k) :
    properChowPushforward C _ sB u hu (k + (r : ℤ)) (by rwa [sub_neg_eq_add] at hfac)
        (flatPullbackChow C (pullback.fst f g' ≫ sX) (g' ≫ sY) (pullback.snd f g')
          (pullbackSnd_comp_structureMorphism hf g') r (relativeDimension_pullbackSnd f hfr g') k
          (hS1 _ _ _ (pullbackSnd_comp_structureMorphism hf g') r
            (relativeDimension_pullbackSnd f hfr g') k) α) ≍
      properChowPushforward C _ sB u hu (k - -(r : ℤ)) hfac
        (flatPullbackBivariantCap C sX sY f hf r hfr hS1 g' k α) :=
  properChowPushforward_heq_congr C _ sB u hu (by ring) _ hfac _ _
    (flatPullbackBivariantCap_heq C sX sY f hf r hfr hS1 g' k α).symm

/-- **Stacks 02RG.** The projection formula of Stacks 0B76 (1) for the cap operation of
Stacks 0B78: flat pullback along the base change of `f` commutes with proper pushforward along a
proper morphism of test schemes. The input is Stacks 02RG, carried as `hRG`. -/
theorem flatPullbackBivariantCap_proper_naturality
    (hRG : ProperPushforwardFlatPullbackBaseChange C) {T T' : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] (h : T' ⟶ T) [IsProper h]
    (h' : pullback f (h ≫ g) ⟶ pullback f g) [IsProper h']
    (sq : IsPullback (pullback.snd f (h ≫ g)) h' h (pullback.snd f g))
    (hfst : h' ≫ pullback.fst f g = pullback.fst f (h ≫ g)) (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C ((h ≫ g) ≫ sY) (g ≫ sY) h
      (by simp [Category.assoc]) k)
    (hfac' : ProperPushforwardFactorsThroughRationalEquivalence C
      (pullback.fst f (h ≫ g) ≫ sX) (pullback.fst f g ≫ sX) h'
      (by rw [← Category.assoc, hfst]) (k - -(r : ℤ)))
    (α : chowGroup C ((h ≫ g) ≫ sY) k) :
    flatPullbackBivariantCap C sX sY f hf r hfr hS1 g k
        (properChowPushforward C ((h ≫ g) ≫ sY) (g ≫ sY) h (by simp [Category.assoc]) k hfac
          α) =
      properChowPushforward C (pullback.fst f (h ≫ g) ≫ sX) (pullback.fst f g ≫ sX) h'
        (by rw [← Category.assoc, hfst]) (k - -(r : ℤ)) hfac'
        (flatPullbackBivariantCap C sX sY f hf r hfr hS1 (h ≫ g) k α) := by
  have hpp2 : ProperPushforwardFactorsThroughRationalEquivalence C
      (pullback.fst f (h ≫ g) ≫ sX) (pullback.fst f g ≫ sX) h'
      (by rw [← Category.assoc, hfst]) (k + (r : ℤ)) := by
    rwa [sub_neg_eq_add] at hfac'
  have hcap := flatPullbackBivariantCap_heq C sX sY f hf r hfr hS1 g k
    (properChowPushforward C ((h ≫ g) ≫ sY) (g ≫ sY) h (by simp [Category.assoc]) k hfac α)
  have hrg := hRG ((h ≫ g) ≫ sY) (pullback.fst f (h ≫ g) ≫ sX) (g ≫ sY)
    (pullback.fst f g ≫ sX) h (by simp [Category.assoc]) h' (by rw [← Category.assoc, hfst])
    (pullback.snd f (h ≫ g)) (pullbackSnd_comp_structureMorphism hf (h ≫ g))
    (pullback.snd f g) (pullbackSnd_comp_structureMorphism hf g) sq r
    (relativeDimension_pullbackSnd f hfr (h ≫ g)) (relativeDimension_pullbackSnd f hfr g) k
    (hS1 (pullback.fst f (h ≫ g) ≫ sX) ((h ≫ g) ≫ sY) (pullback.snd f (h ≫ g))
      (pullbackSnd_comp_structureMorphism hf (h ≫ g)) r
      (relativeDimension_pullbackSnd f hfr (h ≫ g)) k)
    (hS1 (pullback.fst f g ≫ sX) (g ≫ sY) (pullback.snd f g)
      (pullbackSnd_comp_structureMorphism hf g) r (relativeDimension_pullbackSnd f hfr g) k)
    hfac hpp2 α
  have hmove := properChowPushforward_flatPullbackBivariantCap_heq C sX sY f hf r hfr hS1 (h ≫ g)
    h' (by rw [← Category.assoc, hfst]) k hfac' α
  exact eq_of_heq (hcap.trans ((heq_of_eq hrg).trans hmove))

/-- **Stacks 0B71.** The Gysin law of Stacks 0B76 (3) for the cap operation of Stacks 0B78:
flat pullback along the base change of `f` commutes with the Gysin map of the zero scheme of a
section of an invertible module on a test scheme. The input is Stacks 0B71, carried as `h71`. -/
theorem flatPullbackBivariantCap_gysin_naturality (h71 : G.FlatPullbackNaturality r)
    {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback f g).sheaf.obj
      (pullback f g).ringCatSheaf.property
      ((Scheme.Modules.pullback (pullback.snd f g)).obj L)]
    (s : Γ(L, ⊤)) (k : ℤ)
    (e : pullback f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≅
      (Stacks.Divisors.zeroScheme (pullback f g)
        ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s)).subscheme)
    (hbase : e.hom ≫ ((Stacks.Divisors.zeroScheme (pullback f g)
        ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s)).subschemeι ≫
        pullback.fst f g ≫ sX) =
      pullback.fst f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sX)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C
      (pullback.fst f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sX)
      ((Stacks.Divisors.zeroScheme (pullback f g)
        ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s)).subschemeι ≫
        pullback.fst f g ≫ sX) e.hom hbase (k - -(r : ℤ)))
    (α : chowGroup C (g ≫ sY) (k + 1)) :
    properChowPushforward C
        (pullback.fst f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sX)
        ((Stacks.Divisors.zeroScheme (pullback f g)
          ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s)).subschemeι ≫
          pullback.fst f g ≫ sX) e.hom hbase (k - -(r : ℤ)) hfac
        (flatPullbackBivariantCap C sX sY f hf r hfr hS1
          ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) k
          (G.onChow (g ≫ sY) L s k α)) =
      G.onChow (pullback.fst f g ≫ sX)
        ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s) (k - -(r : ℤ))
        (Eq.mp (congrArg (chowGroup C (pullback.fst f g ≫ sX))
          (by omega : k + 1 - -(r : ℤ) = k - -(r : ℤ) + 1))
          (flatPullbackBivariantCap C sX sY f hf r hfr hS1 g (k + 1) α)) := by
  have hdeg : k + (r : ℤ) = k - -(r : ℤ) := by ring
  have hpp2 : ProperPushforwardFactorsThroughRationalEquivalence C
      (pullback.fst f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sX)
      ((Stacks.Divisors.zeroScheme (pullback f g)
        ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s)).subschemeι ≫
        pullback.fst f g ≫ sX) e.hom hbase (k + (r : ℤ)) := by
    rwa [sub_neg_eq_add] at hfac
  have hvb : pullback.snd f g ≫ (g ≫ sY) = pullback.fst f g ≫ sX :=
    pullbackSnd_comp_structureMorphism hf g
  have hvbr : AlgebraicGeometry.RelativeDimension (pullback.snd f g) r :=
    relativeDimension_pullbackSnd f hfr g
  have hdb : pullback.snd f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫
      (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sY) =
      pullback.fst f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sX :=
    pullbackSnd_comp_structureMorphism hf ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g)
  have hdbr : AlgebraicGeometry.RelativeDimension
      (pullback.snd f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g)) r :=
    relativeDimension_pullbackSnd f hfr ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g)
  have hfacv := hS1 (pullback.fst f g ≫ sX) (g ≫ sY) (pullback.snd f g) hvb r hvbr (k + 1)
  have hfacv'' := hS1 (pullback.fst f
    ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sX)
    (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sY)
    (pullback.snd f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g)) hdb r hdbr k
  have hmove := (properChowPushforward_flatPullbackBivariantCap_heq C sX sY f hf r hfr hS1
    ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) e.hom hbase k hfac
    (G.onChow (g ≫ sY) L s k α)).symm
  have h71inst := h71 (g ≫ sY) (pullback.fst f g ≫ sX)
    (pullback.fst f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sX)
    (pullback.snd f g) hvb hvbr L s k
    (pullback.snd f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g)) hdb hdbr
    e hbase hfacv'' hfacv hpp2 α
  have harg := (chowGroupDegreeEquiv_heq C (pullback.fst f g ≫ sX)
    (by ring : k + 1 + (r : ℤ) = k + (r : ℤ) + 1)
    (flatPullbackChow C (pullback.fst f g ≫ sX) (g ≫ sY) (pullback.snd f g) hvb r hvbr (k + 1)
      hfacv α)).trans
    (((flatPullbackBivariantCap_heq C sX sY f hf r hfr hS1 g (k + 1) α).symm).trans
      ((eq_mp_chowGroup_heq C (pullback.fst f g ≫ sX)
        (by omega : k + 1 - -(r : ℤ) = k - -(r : ℤ) + 1)
        (flatPullbackBivariantCap C sX sY f hf r hfr hS1 g (k + 1) α)).symm))
  have hgys := gysinSystemOnChow_heq_congr G (pullback.fst f g ≫ sX)
    ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
    (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s) hdeg _ _ harg
  exact eq_of_heq (hmove.trans ((heq_of_eq h71inst).trans hgys))

/-! ### The bivariant class of Stacks 0B78 -/

/-- **Stacks 0B78.** For `f : X ⟶ Y` flat of relative dimension `r` between schemes locally of
finite type over the base, the rule which assigns to a test scheme `g : T ⟶ Y` the flat pullback
`A_k(T) ⟶ A_{k+r}(X ×_Y T)` along the base change of `f` is a bivariant class of degree `-r`
for `f`.

The three inputs of the source that this repository does not have are the named hypotheses `hS1`
(Stacks 02S1), `hRG` (Stacks 02RG) and `h71` (Stacks 0B71, with the identification of Stacks
0B6Y). The fourth, Stacks 02RD, is proved here, as is Stacks 02NK; see the implementation notes
of `StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackClass`. -/
@[stacks 0B78 "with Stacks 02S1 as hS1, Stacks 02RG as hRG and Stacks 0B71 as h71"]
def flatPullbackBivariantClass (hRG : ProperPushforwardFlatPullbackBaseChange C)
    (h71 : G.FlatPullbackNaturality r) :
    BivariantClass C G sX sY f hf (-(r : ℤ)) where
  cap := fun {_T} g _ k ↦ flatPullbackBivariantCap C sX sY f hf r hfr hS1 g k
  cap_properPushforward := by
    intro T T' g _ h _ h' sq hfst k α
    have : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
    exact flatPullbackBivariantCap_proper_naturality C sX sY f hf r hfr hS1 hRG g h h' sq hfst k
      _ _ α
  cap_flatPullbackChow := by
    intro T T' g _ h _ _ m hm h' sq hfst k α
    have : LocallyOfFiniteType h' :=
      MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
    have : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
    exact flatPullbackBivariantCap_flat_naturality C sX sY f hf r hfr hS1 g h m hm h' sq hfst k
      _ _ _ α
  cap_gysin := by
    intro T g _ L _ s k
    dsimp only
    intro e _he hbase α
    exact flatPullbackBivariantCap_gysin_naturality C G sX sY f hf r hfr hS1 h71 g L s k e hbase
      _ α

/-- **Stacks 0B78.** The class of Stacks 0B78 caps by flat pullback along the base change of `f`,
up to the transport of degrees. -/
theorem flatPullbackBivariantClass_cap (hRG : ProperPushforwardFlatPullbackBaseChange C)
    (h71 : G.FlatPullbackNaturality r) {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g]
    (k : ℤ) (α : chowGroup C (g ≫ sY) k) :
    (flatPullbackBivariantClass C G sX sY f hf r hfr hS1 hRG h71).cap g k α ≍
      flatPullbackChow C (pullback.fst f g ≫ sX) (g ≫ sY) (pullback.snd f g)
        (pullbackSnd_comp_structureMorphism hf g) r (relativeDimension_pullbackSnd f hfr g) k
        (hS1 (pullback.fst f g ≫ sX) (g ≫ sY) (pullback.snd f g)
          (pullbackSnd_comp_structureMorphism hf g) r (relativeDimension_pullbackSnd f hfr g) k)
        α :=
  flatPullbackBivariantCap_heq C sX sY f hf r hfr hS1 g k α

end Class

end Stacks.Chow

end
