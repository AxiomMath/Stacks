module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Basic

/-!
# Generalized bivariant classes for a diagram `X ⟶ Z ⟵ Y`

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let

  `X --x--> Z <--y-- Y`

be a diagram of schemes locally of finite type over `S`. For `p : ℤ`, a *generalized bivariant
class of degree `p` for this diagram* assigns to every morphism `z' : Z' ⟶ Z` locally of finite
type and every `k` an additive map

  `c ∩ - : A_k(Y') ⟶ A_{k - p}(X')`,   `X' = X ×_Z Z'`,  `Y' = Z' ×_Z Y`,

compatibly with the three operations chapter 42 puts on Chow groups: proper pushforward along a
proper `Z'' ⟶ Z'`, flat pullback along a flat `Z'' ⟶ Z'` of fixed relative dimension, and the
Gysin map of the zero scheme of a section of an invertible module on `Z'`. The group of all of
them is denoted `A^p(X ⟶ Z ⟵ Y)`, and that group is
`Stacks.Chow.GeneralizedBivariantClass`, an abelian group under the pointwise operations.

Taking `Z = Y` and `y = 𝟙 Y` recovers the bivariant classes of Stacks 0B76, which are
`Stacks.Chow.BivariantClass`; the point of the generalized notion is that the source and the
target of the cap operation are *both* base changes of the test scheme, so the two factors of the
diagram may differ.

## Main definitions

* `Stacks.Chow.generalizedBivariantBaseChangeMap` — the map `Z'' ×_Z Y ⟶ Z' ×_Z Y` induced by a
  morphism `Z'' ⟶ Z'`, that is, base change in the first factor of the fibre product.
* `Stacks.Chow.GeneralizedBivariantClass` — the group `A^p(X ⟶ Z ⟵ Y)` of generalized bivariant
  classes of degree `p` for the diagram `X ⟶ Z ⟵ Y`.

## Main results

* `Stacks.Chow.GeneralizedBivariantClass.ext` — a generalized bivariant class is determined by
  its cap operations.
* `Stacks.Chow.GeneralizedBivariantClass.zero_cap`, `add_cap`, `neg_cap`, `sub_cap`, `nsmul_cap`,
  `zsmul_cap` — the abelian group structure is the pointwise one.

## Implementation notes

### Modelling

The two base changes of a test morphism `z' : Z' ⟶ Z` are the chosen categorical pullbacks
`pullback x z'` for `X' = X ×_Z Z'`, whose map to `X` is `pullback.fst x z'`, and `pullback z' y`
for `Y' = Z' ×_Z Y`, whose map to `Y` is `pullback.snd z' y`; the structure morphisms over the
base are the composites of these with `sX` and `sY`. A cap operation therefore goes
`chowGroup C (pullback.snd z' y ≫ sY) k ⟶ chowGroup C (pullback.fst x z' ≫ sX) (k - p)`.

Each compatibility axiom is stated for arbitrary comparison morphisms between the relevant
pullbacks, given together with `CategoryTheory.IsPullback` squares exhibiting them as base
changes of `Z'' ⟶ Z'` — which is what makes properness, flatness and local finite type descend to
them — and with the commutation conditions with the projections to `X` respectively `Y`. They
apply in particular to the canonical base-change maps
`Stacks.Chow.bivariantBaseChangeMap` and `Stacks.Chow.generalizedBivariantBaseChangeMap`. Unlike
in `Stacks.Chow.BivariantClass`, *both* sides need such a comparison morphism: there the source of
the cap operation is the test scheme itself, so the morphism to compare along is `Z'' ⟶ Z'` on the
nose.

The flat axiom is an `HEq` because the flat pullback of a `k`-cycle has degree `k + r` while the
cap operation of degree `p` produces degree `(k + r) - p` on one side and `(k - p) + r` on the
other; these are the same integer and not the same term. In it, the relative dimension of
`Z'' ⟶ Z'` itself is carried as a hypothesis, since "flat of fixed relative dimension" is part of
the data the axiom is given, but it does not occur in the conclusion: the flat pullbacks compared
there are along the two base-changed morphisms, whose relative dimensions are separately
quantified over (Stacks 02NK not being in this repository).

In the Gysin axiom the divisor is cut out on the test scheme `Z'`, so *two* identifications are
needed rather than the single one of `Stacks.Chow.BivariantClass`: the base change of the zero
scheme `D ⊆ Z'` to `X'` must be identified with the zero scheme of the pulled-back section there,
and likewise on `Y'`. Both are recorded as isomorphism hypotheses over the ambient pullback, each
with the condition that it commutes with the base-change map, and the induced maps on Chow groups
are proper pushforward along them. They point in opposite directions because that is the direction
each one is used in: on `X'` the cap operation produces the class that must be transported to the
zero scheme, while on `Y'` it is the Gysin map that produces the class to be fed to the cap
operation.

### The parameters threaded, and why

As for `Stacks.Chow.BivariantClass`, each of the three operations is available in this repository
only in a parameterized form, and the axioms carry those parameters in exactly the same shape:
the `Prop`-valued hypotheses that let proper pushforward and flat pullback descend from cycles to
Chow groups (`Stacks.Chow.ProperPushforwardFactorsThroughRationalEquivalence`, Stacks 02S2, and
`Stacks.Chow.FlatPullbackFactorsThroughRationalEquivalence`, Stacks 02S1) are `∀`-quantified
inside the fields, as are the relative dimensions of the base-changed morphisms, while the Gysin
operation is **data** and is therefore a parameter: a `Stacks.Chow.GysinSystem C`. The reasons —
quantifying a `Prop` is harmless by proof irrelevance, quantifying data would strictly strengthen
the axioms and so cut the group down — are set out at length in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Basic` and are not repeated here. Invertibility of
the pulled-back module (Stacks 0B8L) is likewise carried as an extra instance hypothesis of the
Gysin axiom rather than imported.

### The `GysinSystem` parameter and the tag

`Stacks.Chow.BivariantClass` carries the same parameter. The group of Stacks 0B76 is the one
formed at the genuine first Chern class rule, and a family parameterized by an arbitrary rule is
not literally it; that genuine system is `Stacks.Chow.canonicalGysinSystem`, built in
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Canonical`, where `@[stacks 0B76]` is placed on the
group read against it. The attribute of this remark is placed on
`Stacks.Chow.GeneralizedBivariantClass` in its parameterized form: substituting
`Stacks.Chow.canonicalGysinSystem` for `G` — the genuine Stacks 02SO rule with the genuine Stacks
02TO vanishing — turns the structure into `A^p(X ⟶ Z ⟵ Y)` verbatim, and its naturality
conditions are otherwise those of the remark, clause for clause.

### The remark's example

Stacks 0FDU closes by observing that a proper morphism `f : X₂ ⟶ X₁`, which is not a bivariant
class in the sense of Stacks 0B76, does give `f_* ∈ A^0(X₁ ⟶ X₁ ⟵ X₂)`. That element is
`Stacks.Chow.properPushforwardGeneralizedBivariantClass` of
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GeneralizedProperPushforward`, formed at the Gysin
system of the first Chern class rule `Stacks.Chow.gysinSystemOfInvertible` with nothing assumed:
its three compatibilities are Stacks 02R5, Stacks 02RG on Chow groups and Stacks 02TA for that
Gysin system, all theorems of this repository downstream of this module.

## References

* [Stacks Project, Tag 0FDU](https://stacks.math.columbia.edu/tag/0FDU)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
* [Stacks Project, Tag 0FVK](https://stacks.math.columbia.edu/tag/0FVK)
* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Base change in the first factor of a fibre product -/

/-- The map `Z'' ×_Z Y ⟶ Z' ×_Z Y` between two base changes of `y : Y ⟶ Z` induced by a morphism
`h : Z'' ⟶ Z'`. This is the counterpart, for the first factor of the fibre product, of
`Stacks.Chow.bivariantBaseChangeMap`. -/
abbrev generalizedBivariantBaseChangeMap {Y Z T T' : Scheme.{u}} (g : T ⟶ Z) (y : Y ⟶ Z)
    (h : T' ⟶ T) : pullback (h ≫ g) y ⟶ pullback g y :=
  pullback.map (h ≫ g) y g y h (𝟙 Y) (𝟙 Z) (by simp) (by simp)

/-! ### Generalized bivariant classes -/

/-- A generalized bivariant class of degree `p` for a diagram `X --x--> Z <--y-- Y` of schemes
locally of finite type over the base: a rule assigning to every morphism `z' : Z' ⟶ Z` locally of
finite type and every `k` an additive map `A_k(Z' ×_Z Y) ⟶ A_{k-p}(X ×_Z Z')`, natural for proper
pushforward, for flat pullback of fixed relative dimension, and for the Gysin map of the zero
scheme of a section of an invertible module on the test scheme, the Gysin maps being those of the
`Stacks.Chow.GysinSystem` `G`. The group of all of them is denoted `A^p(X ⟶ Z ⟵ Y)`. -/
@[stacks 0FDU]
structure GeneralizedBivariantClass (C : ChowSituation.{u}) (G : GysinSystem C)
    {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (x : X ⟶ Z)
    [LocallyOfFiniteType x] (y : Y ⟶ Z) [LocallyOfFiniteType y] (hx : x ≫ sZ = sX)
    (hy : y ≫ sZ = sY) (p : ℤ) where
  /-- The cap operation from the Chow group of `Z' ×_Z Y` to that of `X ×_Z Z'`, for each test
  scheme. -/
  cap : ∀ {Z' : Scheme.{u}} (z' : Z' ⟶ Z) [LocallyOfFiniteType z'] (k : ℤ),
    chowGroup C (pullback.snd z' y ≫ sY) k →+ chowGroup C (pullback.fst x z' ≫ sX) (k - p)
  /-- Cap product commutes with proper pushforward. -/
  proper_naturality : ∀ {Z' Z'' : Scheme.{u}} (z' : Z' ⟶ Z) [LocallyOfFiniteType z']
      (h : Z'' ⟶ Z') [IsProper h] (hX' : pullback x (h ≫ z') ⟶ pullback x z')
      (sqX : IsPullback (pullback.snd x (h ≫ z')) hX' h (pullback.snd x z'))
      (hfstX : hX' ≫ pullback.fst x z' = pullback.fst x (h ≫ z'))
      (hY' : pullback (h ≫ z') y ⟶ pullback z' y)
      (sqY : IsPullback (pullback.fst (h ≫ z') y) hY' h (pullback.fst z' y))
      (hsndY : hY' ≫ pullback.snd z' y = pullback.snd (h ≫ z') y) (k : ℤ),
      letI : IsProper hX' := MorphismProperty.of_isPullback sqX (P := @IsProper) inferInstance
      letI : IsProper hY' := MorphismProperty.of_isPullback sqY (P := @IsProper) inferInstance
      ∀ (hfacY : ProperPushforwardFactorsThroughRationalEquivalence C
          (pullback.snd (h ≫ z') y ≫ sY) (pullback.snd z' y ≫ sY) hY'
          (by rw [← Category.assoc, hsndY]) k)
        (hfacX : ProperPushforwardFactorsThroughRationalEquivalence C
          (pullback.fst x (h ≫ z') ≫ sX) (pullback.fst x z' ≫ sX) hX'
          (by rw [← Category.assoc, hfstX]) (k - p))
        (α : chowGroup C (pullback.snd (h ≫ z') y ≫ sY) k),
        cap z' k (properChowPushforward C (pullback.snd (h ≫ z') y ≫ sY)
            (pullback.snd z' y ≫ sY) hY' (by rw [← Category.assoc, hsndY]) k hfacY α) =
          properChowPushforward C (pullback.fst x (h ≫ z') ≫ sX) (pullback.fst x z' ≫ sX) hX'
            (by rw [← Category.assoc, hfstX]) (k - p) hfacX (cap (h ≫ z') k α)
  /-- Cap product commutes with flat pullback of fixed relative dimension. -/
  flat_naturality : ∀ {Z' Z'' : Scheme.{u}} (z' : Z' ⟶ Z) [LocallyOfFiniteType z']
      (h : Z'' ⟶ Z') [LocallyOfFiniteType h] [Flat h] (r : ℕ)
      (_hr : AlgebraicGeometry.RelativeDimension h r)
      (hX' : pullback x (h ≫ z') ⟶ pullback x z')
      (sqX : IsPullback (pullback.snd x (h ≫ z')) hX' h (pullback.snd x z'))
      (hfstX : hX' ≫ pullback.fst x z' = pullback.fst x (h ≫ z'))
      (hY' : pullback (h ≫ z') y ⟶ pullback z' y)
      (sqY : IsPullback (pullback.fst (h ≫ z') y) hY' h (pullback.fst z' y))
      (hsndY : hY' ≫ pullback.snd z' y = pullback.snd (h ≫ z') y) (k : ℤ),
      letI : LocallyOfFiniteType hX' :=
        MorphismProperty.of_isPullback sqX (P := @LocallyOfFiniteType) inferInstance
      letI : Flat hX' := MorphismProperty.of_isPullback sqX (P := @Flat) inferInstance
      letI : LocallyOfFiniteType hY' :=
        MorphismProperty.of_isPullback sqY (P := @LocallyOfFiniteType) inferInstance
      letI : Flat hY' := MorphismProperty.of_isPullback sqY (P := @Flat) inferInstance
      ∀ (hrX' : AlgebraicGeometry.RelativeDimension hX' r)
        (hrY' : AlgebraicGeometry.RelativeDimension hY' r)
        (hfacY : FlatPullbackFactorsThroughRationalEquivalence C
          (pullback.snd (h ≫ z') y ≫ sY) (pullback.snd z' y ≫ sY) hY'
          (by rw [← Category.assoc, hsndY]) r hrY' k)
        (hfacX : FlatPullbackFactorsThroughRationalEquivalence C
          (pullback.fst x (h ≫ z') ≫ sX) (pullback.fst x z' ≫ sX) hX'
          (by rw [← Category.assoc, hfstX]) r hrX' (k - p))
        (α : chowGroup C (pullback.snd z' y ≫ sY) k),
        HEq
          (cap (h ≫ z') (k + (r : ℤ))
            (flatPullbackChow C (pullback.snd (h ≫ z') y ≫ sY) (pullback.snd z' y ≫ sY) hY'
              (by rw [← Category.assoc, hsndY]) r hrY' k hfacY α))
          (flatPullbackChow C (pullback.fst x (h ≫ z') ≫ sX) (pullback.fst x z' ≫ sX) hX'
            (by rw [← Category.assoc, hfstX]) r hrX' (k - p) hfacX (cap z' k α))
  /-- Cap product commutes with the Gysin map of every divisor on a test scheme. -/
  gysin_naturality : ∀ {Z' : Scheme.{u}} (z' : Z' ⟶ Z) [LocallyOfFiniteType z'] (L : Z'.Modules)
      [AlgebraicGeometry.SheafOfModules.IsInvertible Z'.sheaf.obj Z'.ringCatSheaf.property L]
      [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback x z').sheaf.obj
        (pullback x z').ringCatSheaf.property
        ((Scheme.Modules.pullback (pullback.snd x z')).obj L)]
      [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback z' y).sheaf.obj
        (pullback z' y).ringCatSheaf.property
        ((Scheme.Modules.pullback (pullback.fst z' y)).obj L)]
      (s : Γ(L, ⊤)) (k : ℤ),
      let D := Stacks.Divisors.zeroScheme Z' L s
      let LX := (Scheme.Modules.pullback (pullback.snd x z')).obj L
      let tX := AlgebraicGeometry.pullbackGlobalSections (pullback.snd x z') L s
      let EX := Stacks.Divisors.zeroScheme (pullback x z') LX tX
      let LY := (Scheme.Modules.pullback (pullback.fst z' y)).obj L
      let tY := AlgebraicGeometry.pullbackGlobalSections (pullback.fst z' y) L s
      let EY := Stacks.Divisors.zeroScheme (pullback z' y) LY tY
      ∀ (eX : pullback x (D.subschemeι ≫ z') ≅ EX.subscheme)
        (_heX : eX.hom ≫ EX.subschemeι = bivariantBaseChangeMap x z' D.subschemeι)
        (hbaseX : eX.hom ≫ (EX.subschemeι ≫ pullback.fst x z' ≫ sX) =
          pullback.fst x (D.subschemeι ≫ z') ≫ sX)
        (hfacX : ProperPushforwardFactorsThroughRationalEquivalence C
          (pullback.fst x (D.subschemeι ≫ z') ≫ sX) (EX.subschemeι ≫ pullback.fst x z' ≫ sX)
          eX.hom hbaseX (k - p))
        (eY : EY.subscheme ≅ pullback (D.subschemeι ≫ z') y)
        (_heY : eY.hom ≫ generalizedBivariantBaseChangeMap z' y D.subschemeι = EY.subschemeι)
        (hbaseY : eY.hom ≫ (pullback.snd (D.subschemeι ≫ z') y ≫ sY) =
          EY.subschemeι ≫ pullback.snd z' y ≫ sY)
        (hfacY : ProperPushforwardFactorsThroughRationalEquivalence C
          (EY.subschemeι ≫ pullback.snd z' y ≫ sY)
          (pullback.snd (D.subschemeι ≫ z') y ≫ sY) eY.hom hbaseY k)
        (α : chowGroup C (pullback.snd z' y ≫ sY) (k + 1)),
        properChowPushforward C (pullback.fst x (D.subschemeι ≫ z') ≫ sX)
            (EX.subschemeι ≫ pullback.fst x z' ≫ sX) eX.hom hbaseX (k - p) hfacX
            (cap (D.subschemeι ≫ z') k
              (properChowPushforward C (EY.subschemeι ≫ pullback.snd z' y ≫ sY)
                (pullback.snd (D.subschemeι ≫ z') y ≫ sY) eY.hom hbaseY k hfacY
                (G.onChow (pullback.snd z' y ≫ sY) LY tY k α))) =
          G.onChow (pullback.fst x z' ≫ sX) LX tX (k - p)
            (Eq.mp (congrArg (chowGroup C (pullback.fst x z' ≫ sX))
              (by omega : (k + 1) - p = (k - p) + 1)) (cap z' (k + 1) α))

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S)
  [LocallyOfFiniteType sZ] (x : X ⟶ Z) [LocallyOfFiniteType x] (y : Y ⟶ Z)
  [LocallyOfFiniteType y] (hx : x ≫ sZ = sX) (hy : y ≫ sZ = sY) (p : ℤ)

/-- Two generalized bivariant classes agree as soon as all their cap operations agree. -/
@[ext]
theorem GeneralizedBivariantClass.ext
    {c d : GeneralizedBivariantClass C G sX sY sZ x y hx hy p}
    (h : ∀ {Z' : Scheme.{u}} (z' : Z' ⟶ Z) [LocallyOfFiniteType z'] (k : ℤ)
      (α : chowGroup C (pullback.snd z' y ≫ sY) k), c.cap z' k α = d.cap z' k α) : c = d := by
  cases c with
  | mk ccap cproper cflat cgysin =>
    cases d with
    | mk dcap dproper dflat dgysin =>
      have hcap : @ccap = @dcap := by
        funext Z' z' hz' k
        exact AddMonoidHom.ext fun α => h z' k α
      cases hcap
      congr

/-- The zero generalized bivariant class, capping to zero on every test scheme. -/
instance : Zero (GeneralizedBivariantClass C G sX sY sZ x y hx hy p) where
  zero :=
    { cap := fun _ _ _ => 0
      proper_naturality := by
        intros
        simp
      flat_naturality := by
        intro Z' Z'' z' hz' h hh fh r hr hX' sqX hfstX hY' sqY hsndY k hrX' hrY' hfacY hfacX α
        dsimp
        rw [show (k + (r : ℤ)) - p = (k - p) + (r : ℤ) by omega]
        simp
      gysin_naturality := by
        intro Z' z' hz' L hL hLX hLY s k
        dsimp only
        let F : ℤ → Type u := chowGroup C (pullback.fst x z' ≫ sX)
        have cast_zero (i j : ℤ) (h : i = j) : Eq.mp (congrArg F h) (0 : F i) = 0 := by
          cases h
          rfl
        intro eX heX hbaseX hfacX eY heY hbaseY hfacY α
        have hidx : (k + 1) - p = (k - p) + 1 := by omega
        conv_lhs => arg 2; change (0 : _)
        rw [map_zero]
        conv_rhs => arg 2; arg 2; change (0 : _)
        rw [cast_zero _ _ hidx, map_zero] }

/-- The pointwise sum of two generalized bivariant classes. -/
instance : Add (GeneralizedBivariantClass C G sX sY sZ x y hx hy p) where
  add c d :=
    { cap := fun z' _ k => c.cap z' k + d.cap z' k
      proper_naturality := by
        intro Z' Z'' z' hz' h hh hX' sqX hfstX hY' sqY hsndY k hfacY hfacX α
        simp only [AddMonoidHom.add_apply, map_add]
        exact congrArg₂ (· + ·)
          (c.proper_naturality z' h hX' sqX hfstX hY' sqY hsndY k hfacY hfacX α)
          (d.proper_naturality z' h hX' sqX hfstX hY' sqY hsndY k hfacY hfacX α)
      flat_naturality := by
        intro Z' Z'' z' hz' h hh fh r hr hX' sqX hfstX hY' sqY hsndY k hrX' hrY' hfacY hfacX α
        let F : ℤ → Type u := chowGroup C (pullback.fst x (h ≫ z') ≫ sX)
        have hidx : (k + (r : ℤ)) - p = (k - p) + (r : ℤ) := by omega
        have cast_add (i j : ℤ) (hij : i = j) (a b : F j) :
            cast (congrArg F hij).symm (a + b) =
              cast (congrArg F hij).symm a + cast (congrArg F hij).symm b := by
          cases hij
          rfl
        simp only [AddMonoidHom.add_apply, map_add]
        apply (eq_cast_iff_heq (e := (congrArg F hidx).symm)).1
        rw [cast_add _ _ hidx]
        exact congrArg₂ (· + ·)
          ((eq_cast_iff_heq (e := (congrArg F hidx).symm)).2
            (c.flat_naturality z' h r hr hX' sqX hfstX hY' sqY hsndY k hrX' hrY' hfacY hfacX α))
          ((eq_cast_iff_heq (e := (congrArg F hidx).symm)).2
            (d.flat_naturality z' h r hr hX' sqX hfstX hY' sqY hsndY k hrX' hrY' hfacY hfacX α))
      gysin_naturality := by
        intro Z' z' hz' L hL hLX hLY s k D LX tX EX LY tY EY eX heX hbaseX hfacX eY heY hbaseY
          hfacY α
        let F : ℤ → Type u := chowGroup C (pullback.fst x z' ≫ sX)
        have hidx : (k + 1) - p = (k - p) + 1 := by omega
        have cast_add (i j : ℤ) (hij : i = j) (a b : F i) :
            Eq.mp (congrArg F hij) (a + b) =
              Eq.mp (congrArg F hij) a + Eq.mp (congrArg F hij) b := by
          cases hij
          rfl
        simp only [AddMonoidHom.add_apply]
        rw [cast_add _ _ hidx]
        simp only [map_add]
        exact congrArg₂ (· + ·)
          (c.gysin_naturality z' L s k eX heX hbaseX hfacX eY heY hbaseY hfacY α)
          (d.gysin_naturality z' L s k eX heX hbaseX hfacX eY heY hbaseY hfacY α) }

/-- The pointwise negation of a generalized bivariant class. -/
instance : Neg (GeneralizedBivariantClass C G sX sY sZ x y hx hy p) where
  neg c :=
    { cap := fun z' _ k => -c.cap z' k
      proper_naturality := by
        intro Z' Z'' z' hz' h hh hX' sqX hfstX hY' sqY hsndY k hfacY hfacX α
        simpa only [AddMonoidHom.neg_apply, map_neg] using congrArg Neg.neg
          (c.proper_naturality z' h hX' sqX hfstX hY' sqY hsndY k hfacY hfacX α)
      flat_naturality := by
        intro Z' Z'' z' hz' h hh fh r hr hX' sqX hfstX hY' sqY hsndY k hrX' hrY' hfacY hfacX α
        let F : ℤ → Type u := chowGroup C (pullback.fst x (h ≫ z') ≫ sX)
        have hidx : (k + (r : ℤ)) - p = (k - p) + (r : ℤ) := by omega
        have cast_neg (i j : ℤ) (hij : i = j) (a : F j) :
            cast (congrArg F hij).symm (-a) = -cast (congrArg F hij).symm a := by
          cases hij
          rfl
        simp only [AddMonoidHom.neg_apply, map_neg]
        apply (eq_cast_iff_heq (e := (congrArg F hidx).symm)).1
        rw [cast_neg _ _ hidx]
        exact congrArg Neg.neg ((eq_cast_iff_heq (e := (congrArg F hidx).symm)).2
          (c.flat_naturality z' h r hr hX' sqX hfstX hY' sqY hsndY k hrX' hrY' hfacY hfacX α))
      gysin_naturality := by
        intro Z' z' hz' L hL hLX hLY s k D LX tX EX LY tY EY eX heX hbaseX hfacX eY heY hbaseY
          hfacY α
        let F : ℤ → Type u := chowGroup C (pullback.fst x z' ≫ sX)
        have hidx : (k + 1) - p = (k - p) + 1 := by omega
        have cast_neg (i j : ℤ) (hij : i = j) (a : F i) :
            Eq.mp (congrArg F hij) (-a) = -(Eq.mp (congrArg F hij) a) := by
          cases hij
          rfl
        simp only [AddMonoidHom.neg_apply]
        rw [cast_neg _ _ hidx]
        simp only [map_neg]
        exact congrArg Neg.neg
          (c.gysin_naturality z' L s k eX heX hbaseX hfacX eY heY hbaseY hfacY α) }

/-- The zero generalized bivariant class caps to zero. -/
@[simp]
theorem GeneralizedBivariantClass.zero_cap {Z' : Scheme.{u}} (z' : Z' ⟶ Z)
    [LocallyOfFiniteType z'] (k : ℤ) (α : chowGroup C (pullback.snd z' y ≫ sY) k) :
    (0 : GeneralizedBivariantClass C G sX sY sZ x y hx hy p).cap z' k α = 0 :=
  rfl

/-- A sum of generalized bivariant classes caps to the sum of their cap products. -/
@[simp]
theorem GeneralizedBivariantClass.add_cap
    (c d : GeneralizedBivariantClass C G sX sY sZ x y hx hy p) {Z' : Scheme.{u}} (z' : Z' ⟶ Z)
    [LocallyOfFiniteType z'] (k : ℤ) (α : chowGroup C (pullback.snd z' y ≫ sY) k) :
    (c + d).cap z' k α = c.cap z' k α + d.cap z' k α :=
  rfl

/-- A negated generalized bivariant class caps to the negated cap product. -/
@[simp]
theorem GeneralizedBivariantClass.neg_cap
    (c : GeneralizedBivariantClass C G sX sY sZ x y hx hy p) {Z' : Scheme.{u}} (z' : Z' ⟶ Z)
    [LocallyOfFiniteType z'] (k : ℤ) (α : chowGroup C (pullback.snd z' y ≫ sY) k) :
    (-c).cap z' k α = -c.cap z' k α :=
  rfl

/-- Generalized bivariant classes of degree `p` for the diagram `X ⟶ Z ⟵ Y` form a commutative
additive monoid. -/
instance : AddCommMonoid (GeneralizedBivariantClass C G sX sY sZ x y hx hy p) where
  add_assoc a b c := by
    apply GeneralizedBivariantClass.ext
    intro Z' z' hz' k α
    simp only [GeneralizedBivariantClass.add_cap]
    exact _root_.add_assoc _ _ _
  zero_add a := by
    apply GeneralizedBivariantClass.ext
    intro Z' z' hz' k α
    simp only [GeneralizedBivariantClass.add_cap, GeneralizedBivariantClass.zero_cap]
    exact _root_.zero_add _
  add_zero a := by
    apply GeneralizedBivariantClass.ext
    intro Z' z' hz' k α
    simp only [GeneralizedBivariantClass.add_cap, GeneralizedBivariantClass.zero_cap]
    exact _root_.add_zero _
  add_comm a b := by
    apply GeneralizedBivariantClass.ext
    intro Z' z' hz' k α
    simp only [GeneralizedBivariantClass.add_cap]
    exact _root_.add_comm _ _
  nsmul := nsmulRec

/-- The difference of two generalized bivariant classes. -/
instance : Sub (GeneralizedBivariantClass C G sX sY sZ x y hx hy p) where
  sub a b := a + -b

/-- The group `A^p(X ⟶ Z ⟵ Y)` of generalized bivariant classes of degree `p` for the diagram
`X ⟶ Z ⟵ Y`. -/
instance : AddCommGroup (GeneralizedBivariantClass C G sX sY sZ x y hx hy p) where
  toAddCommMonoid := inferInstance
  toNeg := inferInstance
  toSub := inferInstance
  neg_add_cancel a := by
    apply GeneralizedBivariantClass.ext
    intro Z' z' hz' k α
    simp only [GeneralizedBivariantClass.add_cap, GeneralizedBivariantClass.neg_cap,
      GeneralizedBivariantClass.zero_cap]
    exact _root_.neg_add_cancel _
  sub_eq_add_neg _ _ := rfl
  zsmul := zsmulRec

/-- A difference of generalized bivariant classes caps to the difference of their cap products. -/
@[simp]
theorem GeneralizedBivariantClass.sub_cap
    (c d : GeneralizedBivariantClass C G sX sY sZ x y hx hy p) {Z' : Scheme.{u}} (z' : Z' ⟶ Z)
    [LocallyOfFiniteType z'] (k : ℤ) (α : chowGroup C (pullback.snd z' y ≫ sY) k) :
    (c - d).cap z' k α = c.cap z' k α - d.cap z' k α := by
  simp [sub_eq_add_neg]

/-- A natural multiple of a generalized bivariant class caps to that multiple of its cap
product. -/
@[simp]
theorem GeneralizedBivariantClass.nsmul_cap (n : ℕ)
    (c : GeneralizedBivariantClass C G sX sY sZ x y hx hy p) {Z' : Scheme.{u}} (z' : Z' ⟶ Z)
    [LocallyOfFiniteType z'] (k : ℤ) (α : chowGroup C (pullback.snd z' y ≫ sY) k) :
    (n • c).cap z' k α = n • c.cap z' k α := by
  induction n with
  | zero => simp
  | succ n ih => simp [succ_nsmul, ih]

/-- An integer multiple of a generalized bivariant class caps to that multiple of its cap
product. -/
@[simp]
theorem GeneralizedBivariantClass.zsmul_cap (n : ℤ)
    (c : GeneralizedBivariantClass C G sX sY sZ x y hx hy p) {Z' : Scheme.{u}} (z' : Z' ⟶ Z)
    [LocallyOfFiniteType z'] (k : ℤ) (α : chowGroup C (pullback.snd z' y ≫ sY) k) :
    (n • c).cap z' k α = n • c.cap z' k α := by
  cases n with
  | ofNat n => exact GeneralizedBivariantClass.nsmul_cap C G sX sY sZ x y hx hy p n c z' k α
  | negSucc n => simp [GeneralizedBivariantClass.nsmul_cap]

end Stacks.Chow

end
