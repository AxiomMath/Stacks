module

public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.UnitDivisorDevissage

/-!
# The reduction of a Cartier Gysin map to a principal divisor

Let `S` be the base situation of chapter 42, let `X` be a scheme locally of finite type over it,
and let `(ℒ, s, i : D ⟶ X)` be a triple as in [Stacks, Tag 02T8]: an invertible `𝒪_X`-module, a
global section of it, and its zero scheme. [Stacks, Tag 0F99] asserts the existence of a
commutative square

  `D' --i'--> X'`
  `|p         |g`
  `D --i-->   X`

such that `p` and `g` are of finite type and flat of relative dimension one, `p^*` is injective
on `A_k(D)` for every `k`, `D' ⊆ X'` is the zero scheme of a **global** section of `𝒪_{X'}`, and
`p^*i^* = (i')^*g^*`; and it closes by asserting that all of this remains true after arbitrary
base change by a morphism locally of finite type.

This file carries the **statement** of that tag: `PrincipalSquare` is the square together with
the clauses that are about schemes alone, `PrincipalReduction` adds the two clauses that are
about Chow groups, and `PrincipalReduction.IsStableUnderBaseChange` is the closing base-change
assertion, as a property of a square. The tag itself is proved in
`StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.PrincipalReductionExistence`.

## Main definitions

* `Stacks.Chow.TensorZeroScheme.PrincipalSquare`: **the square of [Stacks, Tag 0F99] with its
  clauses (1) and (3)** — the four corners and two vertical maps, the finite-type, flatness and
  relative-dimension assertions for `g` and for `p`, and the global section of `𝒪_{X'}` whose
  zero scheme is `D'`.
* `Stacks.Chow.TensorZeroScheme.PrincipalSquare.flatPullbackAmbient`: `g^*`.
* `Stacks.Chow.TensorZeroScheme.PrincipalSquare.gysinBranch`: `(i')^*`.
* `Stacks.Chow.TensorZeroScheme.PrincipalSquare.flatPullbackBranch`: `p^*`.
* `Stacks.Chow.TensorZeroScheme.PrincipalReduction`: **the square and all four clauses of
  [Stacks, Tag 0F99].**
* `Stacks.Chow.TensorZeroScheme.PrincipalReduction.IsStableUnderBaseChange`: the closing
  base-change assertion of the tag, as a property of a reduction.

## Implementation notes

### The four maps are those the square's own data supplies

Clauses (2) and (4) name four maps on Chow groups, and they are named here for the abstract
square, not for the one the proof of the tag constructs. No generalization of
`StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.ChowMaps` is needed for that, because the
two constructions those maps are instances of take no hypotheses beyond what a square carries:
`Stacks.Chow.flatPullbackChowOfRelativeDimension` — [Stacks, Tag 0FVK] with [Stacks, Tag 02S1]
discharged — takes a morphism, its flatness and finite type, its relative dimension and the
commutation of the two structure morphisms, which are exactly the fields of `PrincipalSquare`;
and `Stacks.Chow.gysinChowOfInvertible` — [Stacks, Tag 02TO] with no hypothesis — takes an
invertible module and a global section of it, which for `(i')^*` are `𝒪_{X'}` and the section of
clause (3) and for `i^*` are the given `ℒ` and `s`. The declarations of `ChowMaps` are the
instances of these at the constructed square; this file does not use them.

### `D'` is not separate data

Clause (3) presents `D' ⊆ X'` as the zero scheme of a global section `s'` of `𝒪_{X'}`, and the
source observes that this is what makes `(i')^*` defined at all — the Gysin map of [Stacks, Tag
02T8] needs the triple `(𝒪_{X'}, s', i' : D' ⟶ X')`. So `s'` is data of the square and `D'` is
`Stacks.Divisors.zeroScheme X' 𝒪_{X'} s'`, with `i'` its canonical closed immersion; clause (3)
is then carried by the shape of the structure rather than by a field. The same reading is forced
on `D` and `i` by the hypothesis: the triple of [Stacks, Tag 02T8] is `(ℒ, s)` together with the
zero scheme of `s`, which is how `Stacks.Chow.gysinChowOfInvertible` is stated.

### The structure morphisms over the base situation

`D'` sits over `S` along `i' ≫ (g ≫ sX)`, and the flat pullback along `p` is taken with that as
its target structure morphism rather than with `p ≫ (i ≫ sX)`; the two agree by
`Stacks.Chow.TensorZeroScheme.PrincipalSquare.p_comp_structureMorphism`, which is the `hbase`
argument of `Stacks.Chow.flatPullbackChowOfRelativeDimension`. This is the normalization of
`StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.ChowMaps`, and it is what lets clause (4) be
stated with no transport of degrees: `i^*` is taken as a map out of `A_{k+1}` rather than into
`A_{k-1}`, so clause (4) is an identity of maps `A_{k+1}(X) ⟶ A_{k+1}(D')`.

Finite type is expressed as locally of finite type together with quasi-compactness, and relative
dimension one by `AlgebraicGeometry.RelativeDimension`, this repository's reading of
[Stacks, Tag 02NJ]. Every statement of a relative dimension carries a `letI` supplying the
locally-of-finite-type instance, because `AlgebraicGeometry.RelativeDimension` takes it as an
argument.

## References

* [Stacks Project, Tag 0F99](https://stacks.math.columbia.edu/tag/0F99)
* [Stacks Project, Tag 02NJ](https://stacks.math.columbia.edu/tag/02NJ)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
* [Stacks Project, Tag 0FVK](https://stacks.math.columbia.edu/tag/0FVK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow.TensorZeroScheme

/-- The structure morphism of the divisor `D = Z(s)` over the base situation of chapter 42. It is
determined by the triple `(ℒ, s, i : D ⟶ X)` and the structure morphism of `X`, so it does not
depend on a square over it. -/
abbrev zeroSchemeStructureMorphism (C : Stacks.Chow.ChowSituation.{u}) {X : Scheme.{u}}
    (sX : X ⟶ C.S) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) : (Stacks.Divisors.zeroScheme X L s).subscheme ⟶ C.S :=
  (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ sX

/-- **The square of [Stacks, Tag 0F99], with its clauses (1) and (3).** For a scheme `X` locally
of finite type over the base situation of chapter 42 and a triple `(ℒ, s, i : D ⟶ X)` as in
[Stacks, Tag 02T8], this records a scheme `X'` over `X`, a global section `s'` of `𝒪_{X'}` whose
zero scheme is the closed subscheme `D' ⊆ X'`, a map `p : D' ⟶ D` making the square commute, and
the assertion that `g` and `p` are of finite type and flat of relative dimension one. -/
structure PrincipalSquare (C : Stacks.Chow.ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) where
  /-- The upper-right corner `X'` of the square. -/
  X' : Scheme.{u}
  /-- The right-hand vertical map `g : X' ⟶ X`. -/
  g : X' ⟶ X
  /-- **Tag 0F99(1)**: `g` is locally of finite type. -/
  g_locallyOfFiniteType : LocallyOfFiniteType g
  /-- **Tag 0F99(1)**: `g` is quasi-compact; with the previous field, `g` is of finite type. -/
  g_quasiCompact : QuasiCompact g
  /-- **Tag 0F99(1)**: `g` is flat. -/
  g_flat : AlgebraicGeometry.Flat g
  /-- **Tag 0F99(1)**: `g` has relative dimension one. -/
  g_relativeDimension : letI : LocallyOfFiniteType g := g_locallyOfFiniteType
    AlgebraicGeometry.RelativeDimension g 1
  /-- **Tag 0F99(3)**: the global section `s'` of `𝒪_{X'}` whose zero scheme is `D'`. -/
  s' : Γ(Scheme.unitModule X', ⊤)
  /-- The left-hand vertical map `p : D' ⟶ D`. -/
  p : (Stacks.Divisors.zeroScheme X' (Scheme.unitModule X') s').subscheme ⟶
    (Stacks.Divisors.zeroScheme X L s).subscheme
  /-- The square commutes: `i' ≫ g = p ≫ i`. -/
  comm : (Stacks.Divisors.zeroScheme X' (Scheme.unitModule X') s').subschemeι ≫ g =
    p ≫ (Stacks.Divisors.zeroScheme X L s).subschemeι
  /-- **Tag 0F99(1)**: `p` is locally of finite type. -/
  p_locallyOfFiniteType : LocallyOfFiniteType p
  /-- **Tag 0F99(1)**: `p` is quasi-compact; with the previous field, `p` is of finite type. -/
  p_quasiCompact : QuasiCompact p
  /-- **Tag 0F99(1)**: `p` is flat. -/
  p_flat : AlgebraicGeometry.Flat p
  /-- **Tag 0F99(1)**: `p` has relative dimension one. -/
  p_relativeDimension : letI : LocallyOfFiniteType p := p_locallyOfFiniteType
    AlgebraicGeometry.RelativeDimension p 1

namespace PrincipalSquare

variable {C : Stacks.Chow.ChowSituation.{u}} {X : Scheme.{u}} {sX : X ⟶ C.S}
  [LocallyOfFiniteType sX] {L : X.Modules}
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  {s : Γ(L, ⊤)} (R : PrincipalSquare C sX L s)

/-- The right-hand map `g` of the square is locally of finite type. -/
instance : LocallyOfFiniteType R.g := R.g_locallyOfFiniteType

/-- The right-hand map `g` of the square is quasi-compact. -/
instance : QuasiCompact R.g := R.g_quasiCompact

/-- The right-hand map `g` of the square is flat. -/
instance : AlgebraicGeometry.Flat R.g := R.g_flat

/-- The left-hand map `p` of the square is locally of finite type. -/
instance : LocallyOfFiniteType R.p := R.p_locallyOfFiniteType

/-- The left-hand map `p` of the square is quasi-compact. -/
instance : QuasiCompact R.p := R.p_quasiCompact

/-- The left-hand map `p` of the square is flat. -/
instance : AlgebraicGeometry.Flat R.p := R.p_flat

/-- The closed subscheme `D' ⊆ X'`: the zero scheme of the global section `s'` of `𝒪_{X'}` of
clause (3). -/
abbrev branch : R.X'.IdealSheafData :=
  Stacks.Divisors.zeroScheme R.X' (Scheme.unitModule R.X') R.s'

/-- The structure morphism of `D'` over the base situation of chapter 42, taken along
`i' ≫ g`. -/
abbrev branchStructureMorphism : R.branch.subscheme ⟶ C.S :=
  R.branch.subschemeι ≫ R.g ≫ sX

/-- **The two structure morphisms of `D'` agree.** Flat pullback along `p : D' ⟶ D` produces a
class for `D'` over the base situation along `p ≫ (i ≫ sX)`, and the Gysin map of `i'` produces
one along `i' ≫ (g ≫ sX)`; the two composites are equal, by the commutativity of the square. -/
theorem p_comp_structureMorphism :
    R.p ≫ zeroSchemeStructureMorphism C sX L s = R.branchStructureMorphism :=
  (Category.assoc R.p _ sX).symm.trans
    ((congrArg (fun t => t ≫ sX) R.comm.symm).trans (Category.assoc _ R.g sX))

/-- **`g^* : A_k(X) ⟶ A_{k+1}(X')`, the flat pullback along the right-hand map of the square.**

`g` is flat, locally of finite type and of relative dimension one by clause (1), so this is
`Stacks.Chow.flatPullbackChowOfRelativeDimension`, [Stacks, Tag 0FVK] with [Stacks, Tag 02S1]
discharged. -/
def flatPullbackAmbient (k : ℤ) :
    Stacks.Chow.chowGroup C sX k →+
      Stacks.Chow.chowGroup C (R.g ≫ sX) (k + ((1 : ℕ) : ℤ)) :=
  Stacks.Chow.flatPullbackChowOfRelativeDimension C (R.g ≫ sX) sX R.g rfl 1
    R.g_relativeDimension k

/-- **`(i')^* : A_{k+1}(X') ⟶ A_k(D')`, the Gysin map of the upper divisor of the square.**

`D'` is the zero scheme of the global section `s'` of `𝒪_{X'}` by clause (3), so this is
`Stacks.Chow.gysinChowOfInvertible`, [Stacks, Tag 02TO] with no hypothesis, at the triple
`(𝒪_{X'}, s', i' : D' ⟶ X')` of [Stacks, Tag 02T8]. -/
def gysinBranch (k : ℤ) :
    Stacks.Chow.chowGroup C (R.g ≫ sX) (k + 1) →+
      Stacks.Chow.chowGroup C R.branchStructureMorphism k :=
  Stacks.Chow.gysinChowOfInvertible C (R.g ≫ sX) k (Scheme.unitModule R.X') R.s'

/-- **`p^* : A_k(D) ⟶ A_{k+1}(D')`, the flat pullback along the left-hand map of the square.**

`p` is flat, locally of finite type and of relative dimension one by clause (1). Its target is
`D'` over the base situation along `i' ≫ (g ≫ sX)`, the target of `(i')^*` as well. -/
def flatPullbackBranch (k : ℤ) :
    Stacks.Chow.chowGroup C (zeroSchemeStructureMorphism C sX L s) k →+
      Stacks.Chow.chowGroup C R.branchStructureMorphism (k + ((1 : ℕ) : ℤ)) :=
  Stacks.Chow.flatPullbackChowOfRelativeDimension C R.branchStructureMorphism
    (zeroSchemeStructureMorphism C sX L s) R.p R.p_comp_structureMorphism 1
    R.p_relativeDimension k

end PrincipalSquare

/-- **[Stacks, Tag 0F99]: the square and all four of its clauses.** For a scheme `X` locally of
finite type over the base situation of chapter 42 and a triple `(ℒ, s, i : D ⟶ X)` as in
[Stacks, Tag 02T8], this is a `Stacks.Chow.TensorZeroScheme.PrincipalSquare` — the commutative
square, clause (1) for both of its vertical maps, and clause (3) — together with clauses (2) and
(4). -/
structure PrincipalReduction (C : Stacks.Chow.ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) extends PrincipalSquare C sX L s where
  /-- **Tag 0F99(2)**: `p^* : A_k(D) ⟶ A_{k+1}(D')` is injective for every `k`. -/
  flatPullbackBranch_injective :
    ∀ k : ℤ, Function.Injective (toPrincipalSquare.flatPullbackBranch k)
  /-- **Tag 0F99(4)**: `p^*i^* = (i')^*g^*` as maps `A_{k+1}(X) ⟶ A_{k+1}(D')`. -/
  gysinBranch_flatPullbackAmbient :
    ∀ (k : ℤ) (α : Stacks.Chow.chowGroup C sX (k + 1)),
      toPrincipalSquare.gysinBranch (k + 1)
          (toPrincipalSquare.flatPullbackAmbient (k + 1) α) =
        toPrincipalSquare.flatPullbackBranch k
          (Stacks.Chow.gysinChowOfInvertible C sX k L s α)

/-- **[Stacks, Tag 0F99], the closing base-change assertion**, as a property of a reduction:
*"Moreover, these properties remain true after arbitrary base change by morphisms `Y → X` which
are locally of finite type."*

For every morphism `f : Y ⟶ X` locally of finite type there is a reduction of the base-changed
triple `(f^*ℒ, f^*s)` whose upper-right corner is the fibre product `X' ×_X Y` and whose upper
divisor is the inverse image of `D'`. -/
def PrincipalReduction.IsStableUnderBaseChange {C : Stacks.Chow.ChowSituation.{u}}
    {X : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {L : X.Modules}
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    {s : Γ(L, ⊤)} (R : PrincipalReduction C sX L s) : Prop :=
  ∀ {Y : Scheme.{u}} (f : Y ⟶ X) [LocallyOfFiniteType f],
    letI : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property
      ((Scheme.Modules.pullback f).obj L) := Stacks.Divisors.pullback_isInvertible f L
    ∃ (R' : PrincipalReduction C (f ≫ sX) ((Scheme.Modules.pullback f).obj L)
          (AlgebraicGeometry.pullbackGlobalSections f L s))
      (h : R'.X' ⟶ R.X'),
      IsPullback h R'.g R.g f ∧ R'.branch = R.branch.comap h

end Stacks.Chow.TensorZeroScheme

end
