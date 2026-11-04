module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Triviality

/-!
# The weak form of Fulton's Theorem 17.1

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `f : X ⟶ Y` be a
morphism of schemes locally of finite type over `S`. A *weak cap rule of degree `p`* assigns to
every morphism `g : Y' ⟶ Y` locally of finite type and every `k` a map

  `c ∩ - : A_k(Y') ⟶ A_{k-p}(X')`,   `X' = Y' ×_Y X`,

satisfying conditions (1) and (2) of Stacks 0B76 and condition (3) only for those divisors whose
normal bundle is trivial. Stacks 0F9A says that such a rule is automatically a bivariant class,
that is, that condition (3) then holds for every divisor; this file defines the rule.

## Main definitions

* `Stacks.Chow.WeakCapRule` — the rule of Stacks 0F9A: the cap operation of Stacks 0B76 with
  conditions (1), (2) and condition (3) restricted to divisors with trivial normal bundle.
* `Stacks.Chow.BivariantClass.toWeakCapRule` — a bivariant class is a weak cap rule.

The converse, Stacks 0F9A itself, is `Stacks.Chow.WeakCapRule.toBivariantClass` of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.WeakBivariantCriterionProof`, which needs the
whole of Stacks 0F99 (including its base-change clause) and so lives downstream of it.

## Implementation notes

### The three fields shared with `BivariantClass`

`Stacks.Chow.WeakCapRule.cap`, `proper_naturality` and `flat_naturality` are the verbatim fields
of `Stacks.Chow.BivariantClass`, including the quantified Stacks 02S1 and 02S2 descent
hypotheses and the `HEq` of the flat axiom; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Basic` for why they are shaped that way. Sharing
them literally is what makes `Stacks.Chow.BivariantClass.toWeakCapRule` the identity on those
three components and what makes the converse — Stacks 0F9A — a statement about the fourth
field alone.

### The restriction on condition (3)

The source writes the restriction as `ℒ'|_{D'} ≅ 𝒪_{D'}`, a condition on the divisor upstairs,
on `Y'`. It is spelled here as
`AlgebraicGeometry.SheafOfModules.IsTrivial` of `(D.subschemeι)^*L` for `D = Z(s)` the zero
scheme, which is the spelling `Stacks.Chow.gysinCycleMap` (Stacks 0B6Z) uses for the same
condition. Nothing is assumed about the divisor downstairs, on `X'`: triviality is inherited by
the pulled-back divisor, which is
`Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections`, so a hypothesis there
would be redundant as well as a weakening.

## References

* [Stacks Project, Tag 0F9A](https://stacks.math.columbia.edu/tag/0F9A)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0B6Z](https://stacks.math.columbia.edu/tag/0B6Z)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- **Stacks 0F9A, the hypothesis.** A *weak cap rule* of degree `p` for `f : X ⟶ Y`: a rule
assigning to every morphism `g : T ⟶ Y` locally of finite type and every `k` a map
`A_k(T) ⟶ A_{k-p}(T ×_Y X)`, natural for proper pushforward and for flat pullback of fixed
relative dimension — conditions (1) and (2) of Stacks 0B76 — and natural for the Gysin map of
the zero scheme of a section of an invertible module *whose restriction to that zero scheme is
trivial*, which is condition (3) of Stacks 0B76 restricted as in Stacks 0F9A.

Stated against a `Stacks.Chow.GysinSystem`, exactly as `Stacks.Chow.BivariantClass` is. -/
structure WeakCapRule (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX) (p : ℤ) where
  /-- The map `c ∩ - : A_k(T) ⟶ A_{k-p}(T ×_Y X)` for each test scheme. The source asks for a
  map, not a homomorphism; additivity follows from conditions (1) and (2)
  (`Stacks.Chow.WeakCapRule.cap_add`). -/
  cap : ∀ {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ),
    chowGroup C (g ≫ sY) k → chowGroup C (pullback.fst f g ≫ sX) (k - p)
  /-- Cap product commutes with proper pushforward: Stacks 0B76 (1). -/
  proper_naturality : ∀ {T T' : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (h : T' ⟶ T)
      [IsProper h] (h' : pullback f (h ≫ g) ⟶ pullback f g)
      (sq : IsPullback (pullback.snd f (h ≫ g)) h' h (pullback.snd f g))
      (hfst : h' ≫ pullback.fst f g = pullback.fst f (h ≫ g)) (k : ℤ),
      letI : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
      ∀ (hfac : ProperPushforwardFactorsThroughRationalEquivalence C ((h ≫ g) ≫ sY) (g ≫ sY) h
          (by simp [Category.assoc]) k)
        (hfac' : ProperPushforwardFactorsThroughRationalEquivalence C
          (pullback.fst f (h ≫ g) ≫ sX) (pullback.fst f g ≫ sX) h'
          (by rw [← Category.assoc, hfst]) (k - p))
        (α : chowGroup C ((h ≫ g) ≫ sY) k),
        cap g k (properChowPushforward C ((h ≫ g) ≫ sY) (g ≫ sY) h
            (by simp [Category.assoc]) k hfac α) =
          properChowPushforward C (pullback.fst f (h ≫ g) ≫ sX) (pullback.fst f g ≫ sX) h'
            (by rw [← Category.assoc, hfst]) (k - p) hfac' (cap (h ≫ g) k α)
  /-- Cap product commutes with flat pullback of fixed relative dimension: Stacks 0B76 (2). -/
  flat_naturality : ∀ {T T' : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (h : T' ⟶ T)
      [LocallyOfFiniteType h] [Flat h] (r : ℕ) (hr : AlgebraicGeometry.RelativeDimension h r)
      (h' : pullback f (h ≫ g) ⟶ pullback f g)
      (sq : IsPullback (pullback.snd f (h ≫ g)) h' h (pullback.snd f g))
      (hfst : h' ≫ pullback.fst f g = pullback.fst f (h ≫ g)) (k : ℤ),
      letI : LocallyOfFiniteType h' :=
        MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
      letI : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
      ∀ (hr' : AlgebraicGeometry.RelativeDimension h' r)
        (hfac : FlatPullbackFactorsThroughRationalEquivalence C ((h ≫ g) ≫ sY) (g ≫ sY) h
          (by simp [Category.assoc]) r hr k)
        (hfac' : FlatPullbackFactorsThroughRationalEquivalence C
          (pullback.fst f (h ≫ g) ≫ sX) (pullback.fst f g ≫ sX) h'
          (by rw [← Category.assoc, hfst]) r hr' (k - p))
        (α : chowGroup C (g ≫ sY) k),
        HEq
          (cap (h ≫ g) (k + (r : ℤ))
            (flatPullbackChow C ((h ≫ g) ≫ sY) (g ≫ sY) h (by simp [Category.assoc]) r hr k
              hfac α))
          (flatPullbackChow C (pullback.fst f (h ≫ g) ≫ sX) (pullback.fst f g ≫ sX) h'
            (by rw [← Category.assoc, hfst]) r hr' (k - p) hfac' (cap g k α))
  /-- Cap product commutes with the Gysin map of every pulled-back divisor whose normal bundle is
  trivial: Stacks 0B76 (3), restricted as in Stacks 0F9A. -/
  gysin_naturality_of_isTrivial : ∀ {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g]
      (L : T.Modules)
      [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
      [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback f g).sheaf.obj
        (pullback f g).ringCatSheaf.property
        ((Scheme.Modules.pullback (pullback.snd f g)).obj L)]
      (s : Γ(L, ⊤)) (k : ℤ),
      let D := Stacks.Divisors.zeroScheme T L s
      let L' := (Scheme.Modules.pullback (pullback.snd f g)).obj L
      let s' := AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s
      let E := Stacks.Divisors.zeroScheme (pullback f g) L' s'
      ∀ (_htriv : AlgebraicGeometry.SheafOfModules.IsTrivial D.subscheme.sheaf.obj
          D.subscheme.ringCatSheaf.property
          ((Scheme.Modules.pullback D.subschemeι).obj L))
        (e : pullback f (D.subschemeι ≫ g) ≅ E.subscheme)
        (_he : e.hom ≫ E.subschemeι = bivariantBaseChangeMap f g D.subschemeι)
        (hbase : e.hom ≫ (E.subschemeι ≫ pullback.fst f g ≫ sX) =
          pullback.fst f (D.subschemeι ≫ g) ≫ sX)
        (hfac : ProperPushforwardFactorsThroughRationalEquivalence C
          (pullback.fst f (D.subschemeι ≫ g) ≫ sX) (E.subschemeι ≫ pullback.fst f g ≫ sX)
          e.hom hbase (k - p))
        (α : chowGroup C (g ≫ sY) (k + 1)),
        properChowPushforward C (pullback.fst f (D.subschemeι ≫ g) ≫ sX)
            (E.subschemeι ≫ pullback.fst f g ≫ sX) e.hom hbase (k - p) hfac
            (cap (D.subschemeι ≫ g) k (G.onChow (g ≫ sY) L s k α)) =
          G.onChow (pullback.fst f g ≫ sX) L' s' (k - p)
            (Eq.mp (congrArg (chowGroup C (pullback.fst f g ≫ sX))
              (by omega : (k + 1) - p = (k - p) + 1)) (cap g (k + 1) α))

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
  [LocallyOfFiniteType f] (hf : f ≫ sY = sX) (p : ℤ)

/-- A bivariant class is a weak cap rule: its three first components are literally those of a
weak cap rule, and its Gysin axiom is the restricted one with the triviality hypothesis
discarded. -/
def BivariantClass.toWeakCapRule (c : BivariantClass C G sX sY f hf p) :
    WeakCapRule C G sX sY f hf p where
  cap g _ k := c.cap g k
  proper_naturality := c.proper_naturality
  flat_naturality := c.flat_naturality
  gysin_naturality_of_isTrivial := by
    intro T g _ L _ _ s k
    exact fun _htriv => c.gysin_naturality g L s k

/-- The cap map of the weak cap rule underlying a bivariant class `c` is the cap map of `c`. -/
@[simp]
theorem BivariantClass.toWeakCapRule_cap (c : BivariantClass C G sX sY f hf p) {T : Scheme.{u}}
    (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ) :
    (c.toWeakCapRule C G sX sY f hf p).cap g k = ⇑(c.cap g k) :=
  rfl

end Stacks.Chow

end
