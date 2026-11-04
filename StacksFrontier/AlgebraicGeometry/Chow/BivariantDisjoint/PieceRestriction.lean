module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Restriction
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceComparison
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceUniqueness
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.SquareFlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.SquarePushforward
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.OpenImmersionPieces
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.GeneralRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.DimensionDropApplications

/-!
# Restriction of a bivariant class to a piece of a disjoint union decomposition

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `f : X ⟶ Y` be a
morphism of schemes locally of finite type over `S`, let `X = ∐_{i ∈ I} X_i` and
`Y = ∐_{j ∈ J} Y_j` be decompositions into open and closed subschemes and let `a : I → J` satisfy
`f(X_i) ⊆ Y_{a(i)}`. **Stacks 0FDZ** reads

  `A^p(X ⟶ Y) = ∏_{i ∈ I} A^p(X_i ⟶ Y_{a(i)})`.

This file builds the map from left to right. Given `c ∈ A^p(X ⟶ Y)` and a test scheme
`g : T ⟶ Y_{a(i)}`, the source caps `c` against the pushforward of a class on `T` to `Y` and
restricts the result to `X_i`; since the pushforward is along the piece inclusion, which is an
open immersion, this is the same as capping `c` at the test scheme `g ≫ (Y_{a(i)} ⟶ Y)` and
restricting the resulting class along the open immersion
`X_i ×_{Y_{a(i)}} T ⟶ X ×_Y T`. The latter formulation needs no pushforward, and is the one used
here.

## Main definitions

* `Stacks.Chow.FlatPullbackDescends` — Stacks 02S1 for every flat morphism over the base, bundled;
  discharged outright by `Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general`, so
  the constructions below no longer carry it as a hypothesis.
* `Stacks.Chow.GysinSystem.IsNaturalUnderOpenImmersion` — the open-immersion case of Stacks 02TA
  for a Gysin system, carried as a hypothesis here and discharged for the Gysin system of the
  genuine first Chern class rule by
  `Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderOpenImmersion`; see the implementation
  notes.
* `Stacks.Chow.comapSubschemeMap`, `Stacks.Chow.zeroSchemeRestrictMap` — the morphism of
  subschemes induced by a morphism of ambient schemes, and in particular the open immersion of
  the zero scheme of a pulled-back section into the zero scheme of the section pulled back
  further.
* `Stacks.Chow.zeroSchemeBaseChangeIso` — **Stacks 0B6Y**, the identification of the base change
  of the zero scheme of a section on a test scheme with the zero scheme of the pulled-back
  section. This is the identification the Gysin axiom of a bivariant class quantifies over.
* `Stacks.Chow.pieceComparisonCongr` — the comparison `X_i ×_{Y_{a(i)}} T ⟶ X ×_Y T` at a test
  morphism whose composite with the piece inclusion is presented by an equality.
* `Stacks.Chow.bivariantPieceRestrictionCap` — **Stacks 0FDZ**, the cap operation `c_i ∩ -` of
  the restriction of `c` to the piece `i`.
* `Stacks.Chow.bivariantPieceRestriction` — the restricted class
  `c_i ∈ A^p(X_i ⟶ Y_{a(i)})` of **Stacks 0FDZ**, at an arbitrary Gysin system.
* `Stacks.Chow.bivariantPieceRestrictionHom` — the homomorphism
  `A^p(X ⟶ Y) ⟶ ∏_i A^p(X_i ⟶ Y_{a(i)})` of **Stacks 0FDZ**, at an arbitrary Gysin system.

## Main results

* `Stacks.Chow.pieceMap_comp_structureMorphism` — the restriction of `f` to a piece is a morphism
  over the base, which is what makes the restricted class statable.
* `Stacks.Chow.bivariantPieceRestrictionCap_eq` — the restricted cap operation read through any
  identification of the two fibre products commuting with both projections, there being only one.
* `Stacks.Chow.bivariantPieceRestrictionCap_proper_naturality`,
  `Stacks.Chow.bivariantPieceRestrictionCap_flat_naturality`,
  `Stacks.Chow.bivariantPieceRestrictionCap_gysin_naturality` — the three axioms of Stacks 0B76
  for the restricted cap operation, which is what makes
  `Stacks.Chow.bivariantPieceRestriction` a bivariant class.
* `Stacks.Chow.bivariantPieceRestriction_cap`,
  `Stacks.Chow.bivariantPieceRestrictionHom_apply` — the restricted class caps by the restricted
  cap operation, and the components of the map into the product are the restrictions.
* `Stacks.Chow.bivariantPieceRestriction_add`, `_neg`, `_zero` — restriction to a piece is a
  homomorphism of groups.

## Implementation notes

### The cap operation

The cap operation of a bivariant class lands in the *chosen* categorical pullback, so the cap of
the restricted class at `g : T ⟶ Y_{a(i)}` must land in `X_i ×_{Y_{a(i)}} T` while the cap of `c`
at `g ≫ (Y_{a(i)} ⟶ Y)` lands in `X ×_Y T`. The comparison between them is
`Stacks.Chow.pieceComparison`, an open immersion, and the restricted cap operation is the
original one restricted along it by `Stacks.Chow.chowGroupRestrict`. Only
`Stacks.Chow.eq_opensPullbackComparison` is used to recognize the comparison, so the construction
makes no choice: every morphism of the two fibre products commuting with both projections is the
comparison.

A second piece of bookkeeping recurs throughout: the cap of the restricted class at `g` is
indexed by the structure morphism `g ≫ ((Y_{a(i)} ⟶ Y) ≫ sY)` while `c` is indexed by
`(g ≫ (Y_{a(i)} ⟶ Y)) ≫ sY`. These are the same morphism and not the same term, and
`Stacks.Chow.chowGroupCongr` transports between the two Chow groups.

### The three axioms and the two carried hypotheses

The restricted cap operation is not by itself a bivariant class; the content of the construction
is the three naturality axioms of `Stacks.Chow.BivariantClass` for it. Each of them is proved by
invoking the corresponding axiom of `c` at the test scheme `g ≫ (Y_{a(i)} ⟶ Y)` and then
comparing the operation on the Chow group of the piece with the operation upstairs, along the
open immersion of the piece. Three such comparisons are needed, one per operation, and they are
of three different kinds.

* The **proper** axiom needs the open-immersion case of Stacks 02RG for proper pushforward, which
  is proved outright as `Stacks.Chow.chowGroupRestrict_properChowPushforward`, and Stacks 02S2 at
  the base change of the proper morphism, which is proved outright as
  `Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence`. So that axiom carries
  nothing.
* The **flat** axiom needs the open-immersion case of Stacks 02RG for flat pullback, which is
  proved outright as `Stacks.Chow.chowGroupRestrict_flatPullbackChow`, and Stacks 02S1 at the
  base change of the flat morphism. That last instance is the one piece that would otherwise be
  unavailable: the instance of Stacks 02S1 needed along the base change to `X_i ×_{Y_{a(i)}} T` is
  unrelated, by the naive square-transport lemmas, to the one the axiom of `c` supplies along the
  base change to `X ×_Y T` — the square joining them has open immersions, not isomorphisms, for
  its horizontal legs, so
  `Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_of_isIso_square` does not apply.
  Stacks 02S1 is proved in general in this repository, as
  `Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general`, so the needed instance is
  simply supplied outright and the construction below carries no hypothesis for it.
* The **Gysin** axiom needs restriction along an open immersion to commute with the Gysin map of
  a pulled-back divisor. Unlike the other two this cannot be proved from
  `Stacks.Chow.GysinSystem` alone: the first Chern class rules a Gysin system provides at the
  piece and at the ambient scheme are unrelated data, so no axiom of `c` constrains the two
  Gysin maps. What is needed is exactly `Stacks.Chow.GysinSystem.IsNaturalUnderOpenImmersion`,
  the open-immersion case of Stacks 02TA for the system, stated in the style of
  `Stacks.Chow.GysinSystem.IsNaturalUnderBaseChangeIso`. Substituting the genuine first Chern
  class rule discharges it, which is
  `Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderOpenImmersion` of
  `StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceGysinSystemOfInvertible`; the
  Stacks 0FDZ attribute therefore sits on the declarations of that file, which assume no case of
  Stacks 02TA. Carrying such a hypothesis is the same situation as Stacks 0F9Z,
  whose construction `Stacks.Chow.bivariantRestriction` carries the isomorphism case of the same
  tag.

The identification of the base change of the zero scheme of a section with the zero scheme of the
pulled-back section is Stacks 0B6Y, available here as `Stacks.Divisors.zeroScheme_pullback`; the
open immersion it induces between the zero schemes of two successive pullbacks is
`Stacks.Chow.zeroSchemeRestrictMap`, and the identification the Gysin axiom of `c` quantifies
over is `Stacks.Chow.zeroSchemeBaseChangeIso`.

### The other half of the tag

Only the map from `A^p(X ⟶ Y)` to the product is built here. That it is injective is
`Stacks.Chow.BivariantClass.eq_of_clopenRestrict_cap_eq`
(`StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceUniqueness`), stated there in terms
of restriction to the pieces of `X ×_Y T` rather than of the map below; surjectivity, which
assembles a class from a family, is not in this file.

## References

* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The two compatibilities Stacks 02S1 and Stacks 02TA -/

/-- **Stacks 02S1.** Flat pullback along every flat morphism of fixed relative dimension over the
base carries cycles rationally equivalent to zero to cycles rationally equivalent to zero. This
is the analogue for flat pullback of `Stacks.Chow.ProperPushforwardDescends`.

It holds outright, by `Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general`, so the
constructions of this file do not carry it as a hypothesis; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceRestriction`. -/
def FlatPullbackDescends (C : ChowSituation.{u}) : Prop :=
  ∀ {A B : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S)
    [LocallyOfFiniteType sB] (v : A ⟶ B) [LocallyOfFiniteType v] [Flat v] (hv : v ≫ sB = sA)
    (r : ℕ) (hr : AlgebraicGeometry.RelativeDimension v r) (k : ℤ),
    FlatPullbackFactorsThroughRationalEquivalence C sA sB v hv r hr k

/-- **The open-immersion case of Stacks 02TA for a Gysin system**: for an open immersion
`u : A ⟶ B` of schemes over a test scheme `T` carrying an invertible module with a global section,
restriction along `u` of the Gysin map on `B` is the Gysin map on `A` of the restricted class,
the restriction downstairs being taken along the induced open immersion of the two zero schemes.

Like `Stacks.Chow.GysinSystem.IsNaturalUnderBaseChangeIso` this cannot be derived from
`Stacks.Chow.GysinSystem`: the first Chern class rules the system provides on `A` and on `B` are
unrelated data, so nothing ties the two Gysin maps together. It is therefore carried as a
hypothesis, and substituting the genuine first Chern class rule discharges it:
`Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderOpenImmersion`.

The open immersion `j` of the two zero schemes is constrained by the square of Remark 0B6Y,
`j ≫ i = i' ≫ u`, and not only by its commutativity over the base: the structure morphism of `B`
is not a monomorphism, so commutativity over the base does not recover the square, and no case of
Stacks 02TA constrains an open immersion of the two zero schemes unrelated to `u`. With the square
`j` is the unique such morphism, which is what makes the discharge possible. The morphism the
consumers supply, `Stacks.Chow.zeroSchemeRestrictMap`, satisfies it by
`Stacks.Chow.zeroSchemeRestrictMap_comp_subschemeι`. -/
def GysinSystem.IsNaturalUnderOpenImmersion {C : ChowSituation.{u}} (G : GysinSystem C) : Prop :=
  ∀ {A B T : Scheme.{u}} (t : T ⟶ C.S) [LocallyOfFiniteType t] (qA : A ⟶ T)
    [LocallyOfFiniteType qA] (qB : B ⟶ T) [LocallyOfFiniteType qB] (u : A ⟶ B)
    [IsOpenImmersion u] (hu : u ≫ qB = qA) (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (k : ℤ)
    [AlgebraicGeometry.SheafOfModules.IsInvertible A.sheaf.obj A.ringCatSheaf.property
      ((Scheme.Modules.pullback qA).obj L)]
    [AlgebraicGeometry.SheafOfModules.IsInvertible B.sheaf.obj B.ringCatSheaf.property
      ((Scheme.Modules.pullback qB).obj L)]
    (j : (Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback qA).obj L)
            (AlgebraicGeometry.pullbackGlobalSections qA L s)).subscheme ⟶
          (Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
            (AlgebraicGeometry.pullbackGlobalSections qB L s)).subscheme)
    [IsOpenImmersion j]
    (hjsq : j ≫ (Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qB L s)).subschemeι =
        (Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback qA).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qA L s)).subschemeι ≫ u)
    (hj : j ≫ ((Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qB L s)).subschemeι ≫ (qB ≫ t)) =
        (Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback qA).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qA L s)).subschemeι ≫ (qA ≫ t))
    (α : chowGroup C (qB ≫ t) (k + 1)),
    chowGroupRestrict C
        ((Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qB L s)).subschemeι ≫ (qB ≫ t))
        ((Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback qA).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qA L s)).subschemeι ≫ (qA ≫ t)) j hj k
        (G.onChow (qB ≫ t) ((Scheme.Modules.pullback qB).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qB L s) k α) =
      G.onChow (qA ≫ t) ((Scheme.Modules.pullback qA).obj L)
        (AlgebraicGeometry.pullbackGlobalSections qA L s) k
        (chowGroupRestrict C (qB ≫ t) (qA ≫ t) u (by rw [← Category.assoc, hu]) (k + 1) α)

/-- **The open-immersion case of Stacks 02TA for a Gysin system**, read against structure
morphisms presented by equalities rather than as literal composites. -/
theorem GysinSystem.onChow_openImmersion {C : ChowSituation.{u}} {G : GysinSystem C}
    (hgys : G.IsNaturalUnderOpenImmersion) {A B T : Scheme.{u}} (t : T ⟶ C.S)
    [LocallyOfFiniteType t] (qA : A ⟶ T) [LocallyOfFiniteType qA] (qB : B ⟶ T)
    [LocallyOfFiniteType qB] (pA : A ⟶ C.S) [LocallyOfFiniteType pA] (pB : B ⟶ C.S)
    [LocallyOfFiniteType pB] (hpA : qA ≫ t = pA) (hpB : qB ≫ t = pB) (u : A ⟶ B)
    [IsOpenImmersion u] (hu : u ≫ qB = qA) (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (k : ℤ)
    [AlgebraicGeometry.SheafOfModules.IsInvertible A.sheaf.obj A.ringCatSheaf.property
      ((Scheme.Modules.pullback qA).obj L)]
    [AlgebraicGeometry.SheafOfModules.IsInvertible B.sheaf.obj B.ringCatSheaf.property
      ((Scheme.Modules.pullback qB).obj L)]
    (j : (Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback qA).obj L)
            (AlgebraicGeometry.pullbackGlobalSections qA L s)).subscheme ⟶
          (Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
            (AlgebraicGeometry.pullbackGlobalSections qB L s)).subscheme)
    [IsOpenImmersion j]
    (hjsq : j ≫ (Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qB L s)).subschemeι =
        (Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback qA).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qA L s)).subschemeι ≫ u)
    (hj : j ≫ ((Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qB L s)).subschemeι ≫ pB) =
        (Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback qA).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qA L s)).subschemeι ≫ pA)
    (hupg : u ≫ pB = pA) (α : chowGroup C pB (k + 1)) :
    chowGroupRestrict C
        ((Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qB L s)).subschemeι ≫ pB)
        ((Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback qA).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qA L s)).subschemeι ≫ pA) j hj k
        (G.onChow pB ((Scheme.Modules.pullback qB).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qB L s) k α) =
      G.onChow pA ((Scheme.Modules.pullback qA).obj L)
        (AlgebraicGeometry.pullbackGlobalSections qA L s) k
        (chowGroupRestrict C pB pA u hupg (k + 1) α) := by
  subst hpA
  subst hpB
  exact hgys t qA qB u hu L s k j hjsq hj α

/-! ### Transport, base change and zero-scheme bookkeeping -/

/-- Restriction of Chow classes along an open immersion commutes with the transport of a class
along an equality of degrees. -/
theorem chowGroupRestrict_cast (C : ChowSituation.{u}) {X U : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sU : U ⟶ C.S) [LocallyOfFiniteType sU] (j : U ⟶ X)
    [IsOpenImmersion j] (hj : j ≫ sX = sU) {m n : ℤ} (hmn : m = n) (α : chowGroup C sX m) :
    chowGroupRestrict C sX sU j hj n (Eq.mp (congrArg (chowGroup C sX) hmn) α) =
      Eq.mp (congrArg (chowGroup C sU) hmn) (chowGroupRestrict C sX sU j hj m α) := by
  cases hmn
  rfl

/-- For a morphism `u : A ⟶ B` and quasi-coherent ideal sheaf data `J` on `B`, the induced
morphism from the subscheme cut out by the pullback of `J` to the subscheme cut out by `J`. It is
an open immersion when `u` is, being the base change of `u` along the closed immersion of `J`. -/
def comapSubschemeMap {A B : Scheme.{u}} (J : B.IdealSheafData) (u : A ⟶ B) :
    (J.comap u).subscheme ⟶ J.subscheme :=
  (J.comapIso u).hom ≫ pullback.snd u J.subschemeι

/-- The morphism `comapSubschemeMap J u` is an open immersion when `u` is. -/
instance isOpenImmersion_comapSubschemeMap {A B : Scheme.{u}} (J : B.IdealSheafData) (u : A ⟶ B)
    [IsOpenImmersion u] : IsOpenImmersion (comapSubschemeMap J u) :=
  inferInstanceAs (IsOpenImmersion ((J.comapIso u).hom ≫ pullback.snd u J.subschemeι))

/-- The induced morphism of subschemes lies over `u`. -/
theorem comapSubschemeMap_comp_subschemeι {A B : Scheme.{u}} (J : B.IdealSheafData) (u : A ⟶ B) :
    comapSubschemeMap J u ≫ J.subschemeι = (J.comap u).subschemeι ≫ u := by
  rw [comapSubschemeMap, Category.assoc, ← pullback.condition,
    Scheme.IdealSheafData.comapIso_hom_fst_assoc]

/-- **Stacks 0B6Y along an open immersion.** For an open immersion `u : A ⟶ B` over a scheme `T`
carrying an invertible module `L` with a global section `s`, the open immersion of the zero scheme
of the section pulled back to `A` into the zero scheme of the section pulled back to `B`. -/
def zeroSchemeRestrictMap {A B T : Scheme.{u}} (qA : A ⟶ T) (qB : B ⟶ T) (u : A ⟶ B)
    (hu : u ≫ qB = qA) (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) :
    (Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback qA).obj L)
        (AlgebraicGeometry.pullbackGlobalSections qA L s)).subscheme ⟶
      (Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
        (AlgebraicGeometry.pullbackGlobalSections qB L s)).subscheme :=
  eqToHom (congrArg Scheme.IdealSheafData.subscheme
      (zeroScheme_pullback_comap qA qB u hu L s)) ≫
    comapSubschemeMap (Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
      (AlgebraicGeometry.pullbackGlobalSections qB L s)) u

/-- The morphism `zeroSchemeRestrictMap qA qB u hu L s` is an open immersion when `u` is. -/
instance isOpenImmersion_zeroSchemeRestrictMap {A B T : Scheme.{u}} (qA : A ⟶ T) (qB : B ⟶ T)
    (u : A ⟶ B) [IsOpenImmersion u] (hu : u ≫ qB = qA) (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) : IsOpenImmersion (zeroSchemeRestrictMap qA qB u hu L s) :=
  inferInstanceAs (IsOpenImmersion (eqToHom _ ≫ comapSubschemeMap _ u))

/-- The open immersion of the two zero schemes lies over `u`. -/
theorem zeroSchemeRestrictMap_comp_subschemeι {A B T : Scheme.{u}} (qA : A ⟶ T) (qB : B ⟶ T)
    (u : A ⟶ B) (hu : u ≫ qB = qA) (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) :
    zeroSchemeRestrictMap qA qB u hu L s ≫
        (Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qB L s)).subschemeι =
      (Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback qA).obj L)
        (AlgebraicGeometry.pullbackGlobalSections qA L s)).subschemeι ≫ u := by
  rw [zeroSchemeRestrictMap, Category.assoc, comapSubschemeMap_comp_subschemeι,
    ← Category.assoc, subschemeι_eqToHom (zeroScheme_pullback_comap qA qB u hu L s)]

/-- **Stacks 0B6Y for a base change.** The identification of the base change of the zero scheme of
a section on a test scheme `g : T ⟶ Y` with the zero scheme of the section pulled back to
`X ×_Y T`; this is the identification the Gysin axiom of a bivariant class quantifies over. -/
def zeroSchemeBaseChangeIso {X Y T : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y) (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤))
    [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback f g).sheaf.obj
      (pullback f g).ringCatSheaf.property
      ((Scheme.Modules.pullback (pullback.snd f g)).obj L)] :
    pullback f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≅
      (Stacks.Divisors.zeroScheme (pullback f g)
        ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s)).subscheme :=
  (pullbackLeftPullbackSndIso f g (Stacks.Divisors.zeroScheme T L s).subschemeι).symm.trans
    (((Stacks.Divisors.zeroScheme T L s).comapIso (pullback.snd f g)).symm.trans
      (eqToIso (congrArg Scheme.IdealSheafData.subscheme
        (Stacks.Divisors.zeroScheme_pullback (pullback.snd f g) L s).symm)))

/-- The identification of the base change of a zero scheme lies over the canonical map of the two
base changes of `f`. -/
theorem zeroSchemeBaseChangeIso_hom_subschemeι {X Y T : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y)
    (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤))
    [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback f g).sheaf.obj
      (pullback f g).ringCatSheaf.property
      ((Scheme.Modules.pullback (pullback.snd f g)).obj L)] :
    (zeroSchemeBaseChangeIso f g L s).hom ≫
        (Stacks.Divisors.zeroScheme (pullback f g)
          ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s)).subschemeι =
      bivariantBaseChangeMap f g (Stacks.Divisors.zeroScheme T L s).subschemeι := by
  rw [zeroSchemeBaseChangeIso, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Iso.symm_hom,
    eqToIso.hom, Category.assoc, Category.assoc,
    subschemeι_eqToHom (Stacks.Divisors.zeroScheme_pullback (pullback.snd f g) L s).symm,
    Scheme.IdealSheafData.comapIso_inv_subschemeι]
  apply pullback.hom_ext <;> simp

/-! ### The comparison at a test morphism presented as a composite -/

section PieceComparisonCongr

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {I J : Type u} (UX : I → X.Opens) (UY : J → Y.Opens)
  (a : I → J) (ha : ∀ i, UX i ≤ f ⁻¹ᵁ UY (a i)) (i : I) {T : Scheme.{u}}
  (g : T ⟶ (UY (a i) : Scheme.{u})) (m : T ⟶ Y) (hm : g ≫ (UY (a i)).ι = m)

/-- The comparison `X_i ×_{Y_{a(i)}} T ⟶ X ×_Y T` at a test morphism `g : T ⟶ Y_{a(i)}`, read
against a morphism `m : T ⟶ Y` presented by an equality with `g ≫ (Y_{a(i)} ⟶ Y)` rather than as
that literal composite. For `m` that composite itself it is `Stacks.Chow.pieceComparison`. -/
def pieceComparisonCongr : pullback (pieceMap f UX UY a ha i) g ⟶ pullback f m :=
  pullback.lift (pullback.fst (pieceMap f UX UY a ha i) g ≫ (UX i).ι)
    (pullback.snd (pieceMap f UX UY a ha i) g) (by
      rw [Category.assoc, ← hm, ← pieceMap_comp_ι f UX UY a ha i, ← Category.assoc,
        pullback.condition, Category.assoc])

/-- The comparison at a test morphism presented as a composite is compatible with the projections
to `X`. -/
@[simp, reassoc]
theorem pieceComparisonCongr_fst :
    pieceComparisonCongr f UX UY a ha i g m hm ≫ pullback.fst f m =
      pullback.fst (pieceMap f UX UY a ha i) g ≫ (UX i).ι :=
  pullback.lift_fst _ _ _

/-- The comparison at a test morphism presented as a composite is compatible with the projections
to the test scheme. -/
@[simp, reassoc]
theorem pieceComparisonCongr_snd :
    pieceComparisonCongr f UX UY a ha i g m hm ≫ pullback.snd f m =
      pullback.snd (pieceMap f UX UY a ha i) g :=
  pullback.lift_snd _ _ _

/-- The comparison at a test morphism presented as a composite exhibits `X_i ×_{Y_{a(i)}} T` as
the base change of the piece `X_i ⊆ X` along the projection `X ×_Y T ⟶ X`. -/
theorem isPullback_pieceComparisonCongr :
    IsPullback (pieceComparisonCongr f UX UY a ha i g m hm)
      (pullback.fst (pieceMap f UX UY a ha i) g) (pullback.fst f m) (UX i).ι := by
  subst hm
  exact (isPullback_opensPullbackComparison f (UX i) (UY (a i)) (pieceMap f UX UY a ha i)
    (pieceMap_comp_ι f UX UY a ha i) g).flip

/-- The comparison at a test morphism presented as a composite is an open immersion. -/
instance isOpenImmersion_pieceComparisonCongr :
    IsOpenImmersion (pieceComparisonCongr f UX UY a ha i g m hm) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_pieceComparisonCongr f UX UY a ha i g m hm).flip inferInstance

/-- The comparison at a test morphism presented as a composite carries the structure morphism of
`X ×_Y T` to the structure morphism of `X_i ×_{Y_{a(i)}} T`. -/
theorem pieceComparisonCongr_comp_structureMorphism {S : Scheme.{u}} (sX : X ⟶ S) :
    pieceComparisonCongr f UX UY a ha i g m hm ≫ (pullback.fst f m ≫ sX) =
      pullback.fst (pieceMap f UX UY a ha i) g ≫ ((UX i).ι ≫ sX) := by
  rw [← Category.assoc, pieceComparisonCongr_fst, Category.assoc]

end PieceComparisonCongr

section PieceComparisonBaseChange

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {I J : Type u} (UX : I → X.Opens) (UY : J → Y.Opens)
  (a : I → J) (ha : ∀ i, UX i ≤ f ⁻¹ᵁ UY (a i)) (i : I) {T T' : Scheme.{u}}
  (g : T ⟶ (UY (a i) : Scheme.{u})) (d : T' ⟶ T)

/-- The comparisons at `g` and at `d ≫ g` form a commuting square with the canonical maps between
the two base changes of `f` and of `f_i` induced by `d`. -/
theorem pieceComparisonCongr_comp_bivariantBaseChangeMap :
    pieceComparisonCongr f UX UY a ha i (d ≫ g) (d ≫ g ≫ (UY (a i)).ι)
          (Category.assoc d g (UY (a i)).ι) ≫
        bivariantBaseChangeMap f (g ≫ (UY (a i)).ι) d =
      bivariantBaseChangeMap (pieceMap f UX UY a ha i) g d ≫
        pieceComparison f UX UY a ha i g := by
  refine pullback.hom_ext ?_ ?_ <;> simp [pieceComparisonCongr_snd_assoc]

end PieceComparisonBaseChange

/-! ### The cap operation of the restriction to a piece -/

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX) (p : ℤ)
  {I J : Type u} (UX : I → X.Opens) (UY : J → Y.Opens) (a : I → J)
  (ha : ∀ i, UX i ≤ f ⁻¹ᵁ UY (a i)) (i : I)

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [LocallyOfFiniteType f] in
include hf in
/-- The restriction of `f` to a piece is a morphism over the base: the structure morphism of the
piece `X_i` of the source factors through the structure morphism of the piece `Y_{a(i)}` of the
target. -/
theorem pieceMap_comp_structureMorphism :
    pieceMap f UX UY a ha i ≫ ((UY (a i)).ι ≫ sY) = (UX i).ι ≫ sX := by
  rw [← Category.assoc, pieceMap_comp_ι, Category.assoc, hf]

/-- **Stacks 0FDZ.** The cap operation `c_i ∩ -` of the restriction of a bivariant class `c` of
degree `p` for `f : X ⟶ Y` to the piece `f_i : X_i ⟶ Y_{a(i)}`: on a test scheme
`g : T ⟶ Y_{a(i)}` it is the cap operation of `c` at `g ≫ (Y_{a(i)} ⟶ Y)`, restricted along the
open immersion `X_i ×_{Y_{a(i)}} T ⟶ X ×_Y T`. -/
@[stacks 0FDZ "the cap operation of the restriction of a bivariant class to a piece"]
def bivariantPieceRestrictionCap (c : BivariantClass C G sX sY f hf p) {T : Scheme.{u}}
    (g : T ⟶ (UY (a i) : Scheme.{u})) [LocallyOfFiniteType g] (k : ℤ) :
    chowGroup C (g ≫ ((UY (a i)).ι ≫ sY)) k →+
      chowGroup C (pullback.fst (pieceMap f UX UY a ha i) g ≫ ((UX i).ι ≫ sX)) (k - p) :=
  (chowGroupRestrict C (pullback.fst f (g ≫ (UY (a i)).ι) ≫ sX)
      (pullback.fst (pieceMap f UX UY a ha i) g ≫ ((UX i).ι ≫ sX))
      (pieceComparison f UX UY a ha i g)
      (pieceComparison_comp_structureMorphism f UX UY a ha i g sX) (k - p)).comp
    ((c.cap (g ≫ (UY (a i)).ι) k).comp
      (chowGroupCongr C (Category.assoc g (UY (a i)).ι sY).symm k).toAddMonoidHom)

/-- The cap operation of the restriction to a piece, read on an element. -/
theorem bivariantPieceRestrictionCap_apply (c : BivariantClass C G sX sY f hf p)
    {T : Scheme.{u}} (g : T ⟶ (UY (a i) : Scheme.{u})) [LocallyOfFiniteType g] (k : ℤ)
    (β : chowGroup C (g ≫ ((UY (a i)).ι ≫ sY)) k) :
    bivariantPieceRestrictionCap C G sX sY f hf p UX UY a ha i c g k β =
      chowGroupRestrict C (pullback.fst f (g ≫ (UY (a i)).ι) ≫ sX)
        (pullback.fst (pieceMap f UX UY a ha i) g ≫ ((UX i).ι ≫ sX))
        (pieceComparison f UX UY a ha i g)
        (pieceComparison_comp_structureMorphism f UX UY a ha i g sX) (k - p)
        (c.cap (g ≫ (UY (a i)).ι) k
          (chowGroupCongr C (Category.assoc g (UY (a i)).ι sY).symm k β)) :=
  rfl

/-- The cap operation of the restriction to a piece, read through any identification of the base
change of `f_i` along `g` with the base change of `f` along a morphism equal to
`g ≫ (Y_{a(i)} ⟶ Y)`. Only the two projection identities are used, so by
`Stacks.Chow.eq_opensPullbackComparison` the identification is forced. -/
theorem bivariantPieceRestrictionCap_eq (c : BivariantClass C G sX sY f hf p) {T : Scheme.{u}}
    (g : T ⟶ (UY (a i) : Scheme.{u})) [LocallyOfFiniteType g] (m : T ⟶ Y)
    [LocallyOfFiniteType m] (hm : g ≫ (UY (a i)).ι = m)
    (hmY : g ≫ ((UY (a i)).ι ≫ sY) = m ≫ sY)
    (w : pullback (pieceMap f UX UY a ha i) g ⟶ pullback f m) [IsOpenImmersion w]
    (hwfst : w ≫ pullback.fst f m = pullback.fst (pieceMap f UX UY a ha i) g ≫ (UX i).ι)
    (hwsnd : w ≫ pullback.snd f m = pullback.snd (pieceMap f UX UY a ha i) g) (k : ℤ)
    (hbase : w ≫ (pullback.fst f m ≫ sX) =
      pullback.fst (pieceMap f UX UY a ha i) g ≫ ((UX i).ι ≫ sX))
    (β : chowGroup C (g ≫ ((UY (a i)).ι ≫ sY)) k) :
    bivariantPieceRestrictionCap C G sX sY f hf p UX UY a ha i c g k β =
      chowGroupRestrict C (pullback.fst f m ≫ sX)
        (pullback.fst (pieceMap f UX UY a ha i) g ≫ ((UX i).ι ≫ sX)) w hbase (k - p)
        (c.cap m k (chowGroupCongr C hmY k β)) := by
  subst hm
  rw [chowGroupRestrict_congr C (pullback.fst f (g ≫ (UY (a i)).ι) ≫ sX)
    (pullback.fst (pieceMap f UX UY a ha i) g ≫ ((UX i).ι ≫ sX)) w hbase (k - p)
    (pieceComparison f UX UY a ha i g)
    (eq_opensPullbackComparison f (UX i) (UY (a i)) (pieceMap f UX UY a ha i)
      (pieceMap_comp_ι f UX UY a ha i) g w hwfst hwsnd)
    (pieceComparison_comp_structureMorphism f UX UY a ha i g sX)]
  rfl

/-! ### The proper-pushforward axiom of the restriction to a piece -/

/-- The cap operation of the restriction to a piece, read through the comparison at a test
morphism presented as a composite. -/
private theorem bivariantPieceRestrictionCap_eq_pieceComparisonCongr
    (c : BivariantClass C G sX sY f hf p) {T : Scheme.{u}} (g : T ⟶ (UY (a i) : Scheme.{u}))
    [LocallyOfFiniteType g] (m : T ⟶ Y) [LocallyOfFiniteType m] (hm : g ≫ (UY (a i)).ι = m)
    (hmY : g ≫ ((UY (a i)).ι ≫ sY) = m ≫ sY) (k : ℤ)
    (β : chowGroup C (g ≫ ((UY (a i)).ι ≫ sY)) k) :
    bivariantPieceRestrictionCap C G sX sY f hf p UX UY a ha i c g k β =
      chowGroupRestrict C (pullback.fst f m ≫ sX)
        (pullback.fst (pieceMap f UX UY a ha i) g ≫ ((UX i).ι ≫ sX))
        (pieceComparisonCongr f UX UY a ha i g m hm)
        (pieceComparisonCongr_comp_structureMorphism f UX UY a ha i g m hm sX) (k - p)
        (c.cap m k (chowGroupCongr C hmY k β)) :=
  bivariantPieceRestrictionCap_eq C G sX sY f hf p UX UY a ha i c g m hm hmY _ (by simp)
    (by simp) k _ β

/-- The two comparisons over a proper or flat map `q` of test schemes form a cartesian square
with the base change of `q` and its restriction to the piece. -/
private theorem isPullback_pieceComparisonCongr_comp_bivariantBaseChangeMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) {I J : Type u} (UX : I → X.Opens) (UY : J → Y.Opens)
    (a : I → J) (ha : ∀ i, UX i ≤ f ⁻¹ᵁ UY (a i)) (i : I) {T T' : Scheme.{u}}
    (g : T ⟶ (UY (a i) : Scheme.{u})) (q : T' ⟶ T)
    (q' : pullback (pieceMap f UX UY a ha i) (q ≫ g) ⟶ pullback (pieceMap f UX UY a ha i) g)
    (sq : IsPullback (pullback.snd (pieceMap f UX UY a ha i) (q ≫ g)) q' q
      (pullback.snd (pieceMap f UX UY a ha i) g))
    (hfst : q' ≫ pullback.fst (pieceMap f UX UY a ha i) g =
      pullback.fst (pieceMap f UX UY a ha i) (q ≫ g)) :
    IsPullback
      (pieceComparisonCongr f UX UY a ha i (q ≫ g) (q ≫ g ≫ (UY (a i)).ι) (Category.assoc q g _))
      q' (bivariantBaseChangeMap f (g ≫ (UY (a i)).ι) q) (pieceComparison f UX UY a ha i g) := by
  have hQfst : bivariantBaseChangeMap f (g ≫ (UY (a i)).ι) q ≫
      pullback.fst f (g ≫ (UY (a i)).ι) = pullback.fst f (q ≫ g ≫ (UY (a i)).ι) := by simp
  have hWsq : pieceComparisonCongr f UX UY a ha i (q ≫ g) (q ≫ g ≫ (UY (a i)).ι)
        (Category.assoc q g _) ≫ bivariantBaseChangeMap f (g ≫ (UY (a i)).ι) q =
      q' ≫ pieceComparison f UX UY a ha i g := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, pullbackMap_fst, Category.comp_id, pieceComparisonCongr_fst,
        opensPullbackComparison_fst]
      rw [reassoc_of% hfst]
    · simp only [Category.assoc, pullbackMap_snd, pieceComparisonCongr_snd_assoc,
        opensPullbackComparison_snd]
      exact sq.w
  refine IsPullback.of_bot ?_ hWsq
    (isPullback_opensPullbackComparison f (UX i) (UY (a i)) (pieceMap f UX UY a ha i)
      (pieceMap_comp_ι f UX UY a ha i) g).flip
  rw [hfst, hQfst]
  exact isPullback_pieceComparisonCongr f UX UY a ha i (q ≫ g) (q ≫ g ≫ (UY (a i)).ι)
    (Category.assoc q g _)

/-- **Stacks 0FDZ.** The cap operation of the restriction of `c` to the piece `i` commutes with
proper pushforward: the proper-pushforward axiom of Stacks 0B76 for the restricted class.

It is proved from that axiom for `c` at the test scheme `g ≫ (Y_{a(i)} ⟶ Y)` together with the
open-immersion case of Stacks 02RG, `Stacks.Chow.chowGroupRestrict_properChowPushforward`,
applied to the cartesian square formed by the two comparisons and the two base changes of the
proper morphism. -/
theorem bivariantPieceRestrictionCap_proper_naturality (c : BivariantClass C G sX sY f hf p)
    {T T' : Scheme.{u}} (g : T ⟶ (UY (a i) : Scheme.{u})) [LocallyOfFiniteType g] (q : T' ⟶ T)
    [IsProper q]
    (q' : pullback (pieceMap f UX UY a ha i) (q ≫ g) ⟶ pullback (pieceMap f UX UY a ha i) g)
    (sq : IsPullback (pullback.snd (pieceMap f UX UY a ha i) (q ≫ g)) q' q
      (pullback.snd (pieceMap f UX UY a ha i) g))
    (hfst : q' ≫ pullback.fst (pieceMap f UX UY a ha i) g =
      pullback.fst (pieceMap f UX UY a ha i) (q ≫ g)) (k : ℤ) :
    letI : IsProper q' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
    ∀ (hfac : ProperPushforwardFactorsThroughRationalEquivalence C
        ((q ≫ g) ≫ ((UY (a i)).ι ≫ sY)) (g ≫ ((UY (a i)).ι ≫ sY)) q
        (by simp [Category.assoc]) k)
      (hfac' : ProperPushforwardFactorsThroughRationalEquivalence C
        (pullback.fst (pieceMap f UX UY a ha i) (q ≫ g) ≫ ((UX i).ι ≫ sX))
        (pullback.fst (pieceMap f UX UY a ha i) g ≫ ((UX i).ι ≫ sX)) q'
        (by rw [← Category.assoc, hfst]) (k - p))
      (α : chowGroup C ((q ≫ g) ≫ ((UY (a i)).ι ≫ sY)) k),
      bivariantPieceRestrictionCap C G sX sY f hf p UX UY a ha i c g k
          (properChowPushforward C ((q ≫ g) ≫ ((UY (a i)).ι ≫ sY))
            (g ≫ ((UY (a i)).ι ≫ sY)) q (by simp [Category.assoc]) k hfac α) =
        properChowPushforward C
          (pullback.fst (pieceMap f UX UY a ha i) (q ≫ g) ≫ ((UX i).ι ≫ sX))
          (pullback.fst (pieceMap f UX UY a ha i) g ≫ ((UX i).ι ≫ sX)) q'
          (by rw [← Category.assoc, hfst]) (k - p) hfac'
          (bivariantPieceRestrictionCap C G sX sY f hf p UX UY a ha i c (q ≫ g) k α) := by
  intro hfac hfac' α
  have hassoc : (q ≫ g) ≫ (UY (a i)).ι = q ≫ g ≫ (UY (a i)).ι := Category.assoc q g _
  have hgY : g ≫ ((UY (a i)).ι ≫ sY) = (g ≫ (UY (a i)).ι) ≫ sY :=
    (Category.assoc g (UY (a i)).ι sY).symm
  have hmY : (q ≫ g) ≫ ((UY (a i)).ι ≫ sY) = (q ≫ g ≫ (UY (a i)).ι) ≫ sY := by
    simp only [Category.assoc]
  have hqB : q ≫ (g ≫ ((UY (a i)).ι ≫ sY)) = (q ≫ g) ≫ ((UY (a i)).ι ≫ sY) := by
    simp only [Category.assoc]
  have hqB' : q ≫ ((g ≫ (UY (a i)).ι) ≫ sY) = (q ≫ g ≫ (UY (a i)).ι) ≫ sY := by
    simp only [Category.assoc]
  have : IsProper q' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
  have : IsProper (bivariantBaseChangeMap f (g ≫ (UY (a i)).ι) q) :=
    MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap f (g ≫ (UY (a i)).ι) q)
      (P := @IsProper) inferInstance
  have hQfst : bivariantBaseChangeMap f (g ≫ (UY (a i)).ι) q ≫
      pullback.fst f (g ≫ (UY (a i)).ι) = pullback.fst f (q ≫ g ≫ (UY (a i)).ι) := by simp
  have hQbase : bivariantBaseChangeMap f (g ≫ (UY (a i)).ι) q ≫
      (pullback.fst f (g ≫ (UY (a i)).ι) ≫ sX) =
        pullback.fst f (q ≫ g ≫ (UY (a i)).ι) ≫ sX := by rw [reassoc_of% hQfst]
  have hq'base : q' ≫ (pullback.fst (pieceMap f UX UY a ha i) g ≫ ((UX i).ι ≫ sX)) =
      pullback.fst (pieceMap f UX UY a ha i) (q ≫ g) ≫ ((UX i).ι ≫ sX) := by
    rw [reassoc_of% hfst]
  have hcart := isPullback_pieceComparisonCongr_comp_bivariantBaseChangeMap f UX UY a ha i g q q'
    sq hfst
  have hfacr : ProperPushforwardFactorsThroughRationalEquivalence C
      ((q ≫ g ≫ (UY (a i)).ι) ≫ sY) ((g ≫ (UY (a i)).ι) ≫ sY) q hqB' k :=
    properPushforwardFactorsThroughRationalEquivalence_congr_base C hmY hgY q hqB hqB' k hfac
  have hfacQ := properPushforwardFactorsThroughRationalEquivalence C
    (pullback.fst f (q ≫ g ≫ (UY (a i)).ι) ≫ sX) (pullback.fst f (g ≫ (UY (a i)).ι) ≫ sX)
    (bivariantBaseChangeMap f (g ≫ (UY (a i)).ι) q) hQbase (k - p)
  rw [bivariantPieceRestrictionCap_apply C G sX sY f hf p UX UY a ha i c g k,
    bivariantPieceRestrictionCap_eq_pieceComparisonCongr C G sX sY f hf p UX UY a ha i c (q ≫ g)
      (q ≫ g ≫ (UY (a i)).ι) hassoc hmY k,
    properChowPushforward_chowGroupCongr C hmY hgY q hqB hqB' k hfac hfacr α,
    c.proper_naturality (g ≫ (UY (a i)).ι) q (bivariantBaseChangeMap f (g ≫ (UY (a i)).ι) q)
      (isPullback_bivariantBaseChangeMap f (g ≫ (UY (a i)).ι) q) hQfst k hfacr hfacQ
      (chowGroupCongr C hmY k α),
    chowGroupRestrict_properChowPushforward C
      (pullback.fst f (q ≫ g ≫ (UY (a i)).ι) ≫ sX) (pullback.fst f (g ≫ (UY (a i)).ι) ≫ sX)
      (pullback.fst (pieceMap f UX UY a ha i) (q ≫ g) ≫ ((UX i).ι ≫ sX))
      (pullback.fst (pieceMap f UX UY a ha i) g ≫ ((UX i).ι ≫ sX))
      (bivariantBaseChangeMap f (g ≫ (UY (a i)).ι) q) hQbase
      (pieceComparisonCongr f UX UY a ha i (q ≫ g) (q ≫ g ≫ (UY (a i)).ι) hassoc)
      (pieceComparisonCongr_comp_structureMorphism f UX UY a ha i (q ≫ g)
        (q ≫ g ≫ (UY (a i)).ι) hassoc sX)
      (pieceComparison f UX UY a ha i g)
      (pieceComparison_comp_structureMorphism f UX UY a ha i g sX) q' hq'base hcart (k - p)
      hfacQ hfac']

/-! ### The flat-pullback axiom of the restriction to a piece -/

/-- **Stacks 0FDZ.** The cap operation of the restriction of `c` to the piece `i` commutes with
flat pullback of fixed relative dimension: the flat naturality axiom of
`Stacks.Chow.BivariantClass` for `Stacks.Chow.bivariantPieceRestrictionCap`.

It is proved from that axiom for `c` at the test scheme `g ≫ (Y_{a(i)} ⟶ Y)` together with the
open-immersion case of Stacks 02RG for flat pullback,
`Stacks.Chow.chowGroupRestrict_flatPullbackChow`, applied to the cartesian square formed by the
two comparisons and the two base changes of the flat morphism. Invoking the axiom of `c` at the
base change to `X ×_Y T` needs Stacks 02S1 there, supplied unconditionally by
`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general`.

The degrees are `(k + r) - p` on the left and `(k - p) + r` on the right, the same integer written
two ways, which is why the conclusion is an `HEq`. -/
theorem bivariantPieceRestrictionCap_flat_naturality
    (c : BivariantClass C G sX sY f hf p) {T T' : Scheme.{u}}
    (g : T ⟶ (UY (a i) : Scheme.{u})) [LocallyOfFiniteType g] (q : T' ⟶ T)
    [LocallyOfFiniteType q] [Flat q] (r : ℕ) (hr : AlgebraicGeometry.RelativeDimension q r)
    (q' : pullback (pieceMap f UX UY a ha i) (q ≫ g) ⟶ pullback (pieceMap f UX UY a ha i) g)
    (sq : IsPullback (pullback.snd (pieceMap f UX UY a ha i) (q ≫ g)) q' q
      (pullback.snd (pieceMap f UX UY a ha i) g))
    (hfst : q' ≫ pullback.fst (pieceMap f UX UY a ha i) g =
      pullback.fst (pieceMap f UX UY a ha i) (q ≫ g)) (k : ℤ) :
    letI : LocallyOfFiniteType q' :=
      MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
    letI : Flat q' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
    ∀ (hr' : AlgebraicGeometry.RelativeDimension q' r)
      (hfac : FlatPullbackFactorsThroughRationalEquivalence C
        ((q ≫ g) ≫ ((UY (a i)).ι ≫ sY)) (g ≫ ((UY (a i)).ι ≫ sY)) q
        (by simp [Category.assoc]) r hr k)
      (hfac' : FlatPullbackFactorsThroughRationalEquivalence C
        (pullback.fst (pieceMap f UX UY a ha i) (q ≫ g) ≫ ((UX i).ι ≫ sX))
        (pullback.fst (pieceMap f UX UY a ha i) g ≫ ((UX i).ι ≫ sX)) q'
        (by rw [← Category.assoc, hfst]) r hr' (k - p))
      (α : chowGroup C (g ≫ ((UY (a i)).ι ≫ sY)) k),
      HEq
        (bivariantPieceRestrictionCap C G sX sY f hf p UX UY a ha i c (q ≫ g) (k + (r : ℤ))
          (flatPullbackChow C ((q ≫ g) ≫ ((UY (a i)).ι ≫ sY)) (g ≫ ((UY (a i)).ι ≫ sY)) q
            (by simp [Category.assoc]) r hr k hfac α))
        (flatPullbackChow C
          (pullback.fst (pieceMap f UX UY a ha i) (q ≫ g) ≫ ((UX i).ι ≫ sX))
          (pullback.fst (pieceMap f UX UY a ha i) g ≫ ((UX i).ι ≫ sX)) q'
          (by rw [← Category.assoc, hfst]) r hr' (k - p) hfac'
          (bivariantPieceRestrictionCap C G sX sY f hf p UX UY a ha i c g k α)) := by
  intro hr' hfac hfac' α
  have hassoc : (q ≫ g) ≫ (UY (a i)).ι = q ≫ g ≫ (UY (a i)).ι := Category.assoc q g _
  have hgY : g ≫ ((UY (a i)).ι ≫ sY) = (g ≫ (UY (a i)).ι) ≫ sY :=
    (Category.assoc g (UY (a i)).ι sY).symm
  have hmY : (q ≫ g) ≫ ((UY (a i)).ι ≫ sY) = (q ≫ g ≫ (UY (a i)).ι) ≫ sY := by
    simp only [Category.assoc]
  have hqB : q ≫ (g ≫ ((UY (a i)).ι ≫ sY)) = (q ≫ g) ≫ ((UY (a i)).ι ≫ sY) := by
    simp only [Category.assoc]
  have hqB' : q ≫ ((g ≫ (UY (a i)).ι) ≫ sY) = (q ≫ g ≫ (UY (a i)).ι) ≫ sY := by
    simp only [Category.assoc]
  have hft' : LocallyOfFiniteType q' :=
    MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
  have hfl' : Flat q' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
  have sqQ := isPullback_bivariantBaseChangeMap f (g ≫ (UY (a i)).ι) q
  have hftQ : LocallyOfFiniteType (bivariantBaseChangeMap f (g ≫ (UY (a i)).ι) q) :=
    MorphismProperty.of_isPullback sqQ (P := @LocallyOfFiniteType) inferInstance
  have hflQ : Flat (bivariantBaseChangeMap f (g ≫ (UY (a i)).ι) q) :=
    MorphismProperty.of_isPullback sqQ (P := @Flat) inferInstance
  have hrQ : AlgebraicGeometry.RelativeDimension
      (bivariantBaseChangeMap f (g ≫ (UY (a i)).ι) q) r :=
    AlgebraicGeometry.RelativeDimension.of_isPullback sqQ hr
  have hQfst : bivariantBaseChangeMap f (g ≫ (UY (a i)).ι) q ≫
      pullback.fst f (g ≫ (UY (a i)).ι) = pullback.fst f (q ≫ g ≫ (UY (a i)).ι) := by simp
  have hQbase : bivariantBaseChangeMap f (g ≫ (UY (a i)).ι) q ≫
      (pullback.fst f (g ≫ (UY (a i)).ι) ≫ sX) =
        pullback.fst f (q ≫ g ≫ (UY (a i)).ι) ≫ sX := by rw [reassoc_of% hQfst]
  have hq'base : q' ≫ (pullback.fst (pieceMap f UX UY a ha i) g ≫ ((UX i).ι ≫ sX)) =
      pullback.fst (pieceMap f UX UY a ha i) (q ≫ g) ≫ ((UX i).ι ≫ sX) := by
    rw [reassoc_of% hfst]
  have hcart := isPullback_pieceComparisonCongr_comp_bivariantBaseChangeMap f UX UY a ha i g q q'
    sq hfst
  have hfacG : FlatPullbackFactorsThroughRationalEquivalence C
      ((q ≫ g ≫ (UY (a i)).ι) ≫ sY) ((g ≫ (UY (a i)).ι) ≫ sY) q hqB' r hr k :=
    flatPullbackFactorsThroughRationalEquivalence_congr_base C hmY hgY q hqB hqB' r hr k hfac
  have hfacQ := flatPullbackFactorsThroughRationalEquivalence_general C
    (pullback.fst f (q ≫ g ≫ (UY (a i)).ι) ≫ sX)
    (pullback.fst f (g ≫ (UY (a i)).ι) ≫ sX)
    (bivariantBaseChangeMap f (g ≫ (UY (a i)).ι) q) hQbase r hrQ (k - p)
  have hidx : (k + (r : ℤ)) - p = (k - p) + (r : ℤ) := by omega
  have hc := c.flat_naturality (g ≫ (UY (a i)).ι) q r hr
    (bivariantBaseChangeMap f (g ≫ (UY (a i)).ι) q) sqQ hQfst k hrQ hfacG hfacQ
    (chowGroupCongr C hgY k α)
  rw [bivariantPieceRestrictionCap_eq_pieceComparisonCongr C G sX sY f hf p UX UY a ha i c (q ≫ g)
      (q ≫ g ≫ (UY (a i)).ι) hassoc hmY (k + (r : ℤ)),
    bivariantPieceRestrictionCap_apply C G sX sY f hf p UX UY a ha i c g k,
    flatPullbackChow_chowGroupCongr C hmY hgY q hqB hqB' r hr k hfac hfacG α,
    ← chowGroupRestrict_flatPullbackChow C
      (pullback.fst f (q ≫ g ≫ (UY (a i)).ι) ≫ sX)
      (pullback.fst f (g ≫ (UY (a i)).ι) ≫ sX)
      (pullback.fst (pieceMap f UX UY a ha i) (q ≫ g) ≫ ((UX i).ι ≫ sX))
      (pullback.fst (pieceMap f UX UY a ha i) g ≫ ((UX i).ι ≫ sX))
      (bivariantBaseChangeMap f (g ≫ (UY (a i)).ι) q) hQbase r hrQ
      (pieceComparisonCongr f UX UY a ha i (q ≫ g) (q ≫ g ≫ (UY (a i)).ι) hassoc)
      (pieceComparisonCongr_comp_structureMorphism f UX UY a ha i (q ≫ g)
        (q ≫ g ≫ (UY (a i)).ι) hassoc sX)
      (pieceComparison f UX UY a ha i g)
      (pieceComparison_comp_structureMorphism f UX UY a ha i g sX) q' hq'base hcart hr' (k - p)
      hfacQ hfac']
  exact heq_map_index hidx hc
    (fun n x => chowGroupRestrict C (pullback.fst f (q ≫ g ≫ (UY (a i)).ι) ≫ sX)
      (pullback.fst (pieceMap f UX UY a ha i) (q ≫ g) ≫ ((UX i).ι ≫ sX))
      (pieceComparisonCongr f UX UY a ha i (q ≫ g) (q ≫ g ≫ (UY (a i)).ι) hassoc)
      (pieceComparisonCongr_comp_structureMorphism f UX UY a ha i (q ≫ g)
        (q ≫ g ≫ (UY (a i)).ι) hassoc sX) n x)

/-! ### The Gysin axiom of the restriction to a piece -/

/-- **Stacks 0FDZ.** The cap operation of the restriction of `c` to the piece `i` commutes with
the Gysin map of the zero scheme of a section of an invertible module on a test scheme: the third
naturality condition of Stacks 0B76 for the restricted class.

Unlike the proper and the flat axiom, this one is not a consequence of the axioms of `c`: the
restricted cap operation lands on a piece of the base change of `f` while `c` caps into the whole
base change, and the first Chern class rules a `Stacks.Chow.GysinSystem` provides at the two
schemes are unrelated data. The hypothesis is the open-immersion case of Stacks 02TA for the
system. -/
theorem bivariantPieceRestrictionCap_gysin_naturality (hgys : G.IsNaturalUnderOpenImmersion)
    (c : BivariantClass C G sX sY f hf p) {T : Scheme.{u}} (g : T ⟶ (UY (a i) : Scheme.{u}))
    [LocallyOfFiniteType g] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible
      (pullback (pieceMap f UX UY a ha i) g).sheaf.obj
      (pullback (pieceMap f UX UY a ha i) g).ringCatSheaf.property
      ((Scheme.Modules.pullback (pullback.snd (pieceMap f UX UY a ha i) g)).obj L)]
    (s : Γ(L, ⊤)) (k : ℤ) :
    let D := Stacks.Divisors.zeroScheme T L s
    let L' := (Scheme.Modules.pullback (pullback.snd (pieceMap f UX UY a ha i) g)).obj L
    let s' := AlgebraicGeometry.pullbackGlobalSections
      (pullback.snd (pieceMap f UX UY a ha i) g) L s
    let E := Stacks.Divisors.zeroScheme (pullback (pieceMap f UX UY a ha i) g) L' s'
    ∀ (e : pullback (pieceMap f UX UY a ha i) (D.subschemeι ≫ g) ≅ E.subscheme)
      (_he : e.hom ≫ E.subschemeι =
        bivariantBaseChangeMap (pieceMap f UX UY a ha i) g D.subschemeι)
      (hbase : e.hom ≫ (E.subschemeι ≫ pullback.fst (pieceMap f UX UY a ha i) g ≫
          ((UX i).ι ≫ sX)) =
        pullback.fst (pieceMap f UX UY a ha i) (D.subschemeι ≫ g) ≫ ((UX i).ι ≫ sX))
      (hfac : ProperPushforwardFactorsThroughRationalEquivalence C
        (pullback.fst (pieceMap f UX UY a ha i) (D.subschemeι ≫ g) ≫ ((UX i).ι ≫ sX))
        (E.subschemeι ≫ pullback.fst (pieceMap f UX UY a ha i) g ≫ ((UX i).ι ≫ sX))
        e.hom hbase (k - p))
      (α : chowGroup C (g ≫ ((UY (a i)).ι ≫ sY)) (k + 1)),
      properChowPushforward C
          (pullback.fst (pieceMap f UX UY a ha i) (D.subschemeι ≫ g) ≫ ((UX i).ι ≫ sX))
          (E.subschemeι ≫ pullback.fst (pieceMap f UX UY a ha i) g ≫ ((UX i).ι ≫ sX))
          e.hom hbase (k - p) hfac
          (bivariantPieceRestrictionCap C G sX sY f hf p UX UY a ha i c (D.subschemeι ≫ g) k
            (G.onChow (g ≫ ((UY (a i)).ι ≫ sY)) L s k α)) =
        G.onChow (pullback.fst (pieceMap f UX UY a ha i) g ≫ ((UX i).ι ≫ sX)) L' s' (k - p)
          (Eq.mp (congrArg (chowGroup C
            (pullback.fst (pieceMap f UX UY a ha i) g ≫ ((UX i).ι ≫ sX)))
            (by omega : (k + 1) - p = (k - p) + 1))
            (bivariantPieceRestrictionCap C G sX sY f hf p UX UY a ha i c g (k + 1) α)) := by
  dsimp only
  intro e he hbase hfac α
  have hidx : (k + 1) - p = (k - p) + 1 := by omega
  have hDassoc : ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ (UY (a i)).ι =
      (Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g ≫ (UY (a i)).ι :=
    Category.assoc _ g _
  have hgY : g ≫ ((UY (a i)).ι ≫ sY) = (g ≫ (UY (a i)).ι) ≫ sY :=
    (Category.assoc g (UY (a i)).ι sY).symm
  have hmY : ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ ((UY (a i)).ι ≫ sY) =
      ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g ≫ (UY (a i)).ι) ≫ sY := by
    simp only [Category.assoc]
  -- the structure morphisms of the two base changes over the test scheme
  have hpA := pullbackSnd_comp_structureMorphism_eq C ((UX i).ι ≫ sX) ((UY (a i)).ι ≫ sY)
    (pieceMap f UX UY a ha i) (pieceMap_comp_structureMorphism C sX sY f hf UX UY a ha i) g
  have hpB := pullbackSnd_comp_structureMorphism_eq C sX sY f hf (g ≫ (UY (a i)).ι)
  have hW0snd : pieceComparison f UX UY a ha i g ≫ pullback.snd f (g ≫ (UY (a i)).ι) =
      pullback.snd (pieceMap f UX UY a ha i) g :=
    opensPullbackComparison_snd f (UX i) (UY (a i)) (pieceMap f UX UY a ha i)
      (pieceMap_comp_ι f UX UY a ha i) g
  -- the open immersion of the two zero schemes and the identification upstairs
  have hjι := zeroSchemeRestrictMap_comp_subschemeι (pullback.snd (pieceMap f UX UY a ha i) g)
    (pullback.snd f (g ≫ (UY (a i)).ι)) (pieceComparison f UX UY a ha i g) hW0snd L s
  have hj : zeroSchemeRestrictMap (pullback.snd (pieceMap f UX UY a ha i) g)
        (pullback.snd f (g ≫ (UY (a i)).ι)) (pieceComparison f UX UY a ha i g) hW0snd L s ≫
      ((Stacks.Divisors.zeroScheme (pullback f (g ≫ (UY (a i)).ι))
          ((Scheme.Modules.pullback (pullback.snd f (g ≫ (UY (a i)).ι))).obj L)
          (AlgebraicGeometry.pullbackGlobalSections
            (pullback.snd f (g ≫ (UY (a i)).ι)) L s)).subschemeι ≫
        pullback.fst f (g ≫ (UY (a i)).ι) ≫ sX) =
      (Stacks.Divisors.zeroScheme (pullback (pieceMap f UX UY a ha i) g)
        ((Scheme.Modules.pullback (pullback.snd (pieceMap f UX UY a ha i) g)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections
          (pullback.snd (pieceMap f UX UY a ha i) g) L s)).subschemeι ≫
        pullback.fst (pieceMap f UX UY a ha i) g ≫ ((UX i).ι ≫ sX) := by
    rw [← Category.assoc, hjι, Category.assoc,
      pieceComparison_comp_structureMorphism f UX UY a ha i g sX]
  have hêι := zeroSchemeBaseChangeIso_hom_subschemeι f (g ≫ (UY (a i)).ι) L s
  have hbcmfst : bivariantBaseChangeMap f (g ≫ (UY (a i)).ι)
        (Stacks.Divisors.zeroScheme T L s).subschemeι ≫
      pullback.fst f (g ≫ (UY (a i)).ι) =
        pullback.fst f
          ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g ≫ (UY (a i)).ι) := by simp
  have hêbase : (zeroSchemeBaseChangeIso f (g ≫ (UY (a i)).ι) L s).hom ≫
      ((Stacks.Divisors.zeroScheme (pullback f (g ≫ (UY (a i)).ι))
          ((Scheme.Modules.pullback (pullback.snd f (g ≫ (UY (a i)).ι))).obj L)
          (AlgebraicGeometry.pullbackGlobalSections
            (pullback.snd f (g ≫ (UY (a i)).ι)) L s)).subschemeι ≫
        pullback.fst f (g ≫ (UY (a i)).ι) ≫ sX) =
      pullback.fst f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g ≫ (UY (a i)).ι) ≫ sX := by
    rw [reassoc_of% hêι, reassoc_of% hbcmfst]
  have hfacê := properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _
    (zeroSchemeBaseChangeIso f (g ≫ (UY (a i)).ι) L s).hom hêbase (k - p)
  -- the comparison at the test scheme cut out by the divisor, and the cartesian square
  have hWDbase := pieceComparisonCongr_comp_structureMorphism f UX UY a ha i
    ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g)
    ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g ≫ (UY (a i)).ι) hDassoc sX
  have hbcm := pieceComparisonCongr_comp_bivariantBaseChangeMap f UX UY a ha i g
    (Stacks.Divisors.zeroScheme T L s).subschemeι
  have hsqD : pieceComparisonCongr f UX UY a ha i
        ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g)
        ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g ≫ (UY (a i)).ι) hDassoc ≫
      (zeroSchemeBaseChangeIso f (g ≫ (UY (a i)).ι) L s).hom =
      e.hom ≫ zeroSchemeRestrictMap (pullback.snd (pieceMap f UX UY a ha i) g)
        (pullback.snd f (g ≫ (UY (a i)).ι)) (pieceComparison f UX UY a ha i g) hW0snd L s := by
    rw [← cancel_mono (Stacks.Divisors.zeroScheme (pullback f (g ≫ (UY (a i)).ι))
      ((Scheme.Modules.pullback (pullback.snd f (g ≫ (UY (a i)).ι))).obj L)
      (AlgebraicGeometry.pullbackGlobalSections
        (pullback.snd f (g ≫ (UY (a i)).ι)) L s)).subschemeι, Category.assoc, Category.assoc,
      hêι, hjι, hbcm, reassoc_of% he]
  have hcartD := IsPullback.of_vert_isIso (CommSq.mk hsqD)
  -- the two descriptions of the restricted cap products
  have hcapD : bivariantPieceRestrictionCap C G sX sY f hf p UX UY a ha i c
        ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) k
        (G.onChow (g ≫ ((UY (a i)).ι ≫ sY)) L s k α) =
      chowGroupRestrict C
        (pullback.fst f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g ≫ (UY (a i)).ι) ≫ sX)
        (pullback.fst (pieceMap f UX UY a ha i)
          ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ ((UX i).ι ≫ sX))
        (pieceComparisonCongr f UX UY a ha i
          ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g)
          ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g ≫ (UY (a i)).ι) hDassoc)
        hWDbase (k - p)
        (c.cap ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g ≫ (UY (a i)).ι) k
          (G.onChow ((g ≫ (UY (a i)).ι) ≫ sY) L s k (chowGroupCongr C hgY (k + 1) α))) :=
    (bivariantPieceRestrictionCap_eq_pieceComparisonCongr C G sX sY f hf p UX UY a ha i c
      ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g)
      ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g ≫ (UY (a i)).ι) hDassoc hmY k
      (G.onChow (g ≫ ((UY (a i)).ι ≫ sY)) L s k α)).trans
      (DFunLike.congr_arg (chowGroupRestrict C _ _ _ hWDbase (k - p))
        (DFunLike.congr_arg (c.cap ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫
          g ≫ (UY (a i)).ι) k)
          (GysinSystem.onChow_chowGroupCongr G hgY L s k hmY α)))
  have hcapg : bivariantPieceRestrictionCap C G sX sY f hf p UX UY a ha i c g (k + 1) α =
      chowGroupRestrict C (pullback.fst f (g ≫ (UY (a i)).ι) ≫ sX)
        (pullback.fst (pieceMap f UX UY a ha i) g ≫ ((UX i).ι ≫ sX))
        (pieceComparison f UX UY a ha i g)
        (pieceComparison_comp_structureMorphism f UX UY a ha i g sX) ((k + 1) - p)
        (c.cap (g ≫ (UY (a i)).ι) (k + 1) (chowGroupCongr C hgY (k + 1) α)) :=
    bivariantPieceRestrictionCap_apply C G sX sY f hf p UX UY a ha i c g (k + 1) α
  -- the Gysin axiom of `c` upstairs, and the naturality of `G` along the piece comparison
  have hc := c.gysin_naturality (g ≫ (UY (a i)).ι) L s k
    (zeroSchemeBaseChangeIso f (g ≫ (UY (a i)).ι) L s) hêι hêbase hfacê
    (chowGroupCongr C hgY (k + 1) α)
  have hG := GysinSystem.onChow_openImmersion hgys (g ≫ ((UY (a i)).ι ≫ sY))
    (pullback.snd (pieceMap f UX UY a ha i) g) (pullback.snd f (g ≫ (UY (a i)).ι))
    (pullback.fst (pieceMap f UX UY a ha i) g ≫ ((UX i).ι ≫ sX))
    (pullback.fst f (g ≫ (UY (a i)).ι) ≫ sX) hpA hpB (pieceComparison f UX UY a ha i g)
    hW0snd L s (k - p) _ hjι hj
    (pieceComparison_comp_structureMorphism f UX UY a ha i g sX)
    (Eq.mp (congrArg (chowGroup C (pullback.fst f (g ≫ (UY (a i)).ι) ≫ sX)) hidx)
      (c.cap (g ≫ (UY (a i)).ι) (k + 1) (chowGroupCongr C hgY (k + 1) α)))
  have hPR := chowGroupRestrict_properChowPushforward C
    (pullback.fst f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g ≫ (UY (a i)).ι) ≫ sX)
    ((Stacks.Divisors.zeroScheme (pullback f (g ≫ (UY (a i)).ι))
        ((Scheme.Modules.pullback (pullback.snd f (g ≫ (UY (a i)).ι))).obj L)
        (AlgebraicGeometry.pullbackGlobalSections
          (pullback.snd f (g ≫ (UY (a i)).ι)) L s)).subschemeι ≫
      pullback.fst f (g ≫ (UY (a i)).ι) ≫ sX)
    (pullback.fst (pieceMap f UX UY a ha i)
      ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ ((UX i).ι ≫ sX))
    ((Stacks.Divisors.zeroScheme (pullback (pieceMap f UX UY a ha i) g)
        ((Scheme.Modules.pullback (pullback.snd (pieceMap f UX UY a ha i) g)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections
          (pullback.snd (pieceMap f UX UY a ha i) g) L s)).subschemeι ≫
      pullback.fst (pieceMap f UX UY a ha i) g ≫ ((UX i).ι ≫ sX))
    (zeroSchemeBaseChangeIso f (g ≫ (UY (a i)).ι) L s).hom hêbase
    (pieceComparisonCongr f UX UY a ha i
      ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g)
      ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g ≫ (UY (a i)).ι) hDassoc) hWDbase
    (zeroSchemeRestrictMap (pullback.snd (pieceMap f UX UY a ha i) g)
      (pullback.snd f (g ≫ (UY (a i)).ι)) (pieceComparison f UX UY a ha i g) hW0snd L s) hj
    e.hom hbase hcartD (k - p) hfacê hfac
    (c.cap ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g ≫ (UY (a i)).ι) k
      (G.onChow ((g ≫ (UY (a i)).ι) ≫ sY) L s k (chowGroupCongr C hgY (k + 1) α)))
  refine ((DFunLike.congr_arg
    (properChowPushforward C _ _ e.hom hbase (k - p) hfac) hcapD).trans hPR.symm).trans ?_
  refine ((DFunLike.congr_arg (chowGroupRestrict C _ _ _ hj (k - p)) hc).trans hG).trans ?_
  exact DFunLike.congr_arg
    (G.onChow (pullback.fst (pieceMap f UX UY a ha i) g ≫ ((UX i).ι ≫ sX))
      ((Scheme.Modules.pullback (pullback.snd (pieceMap f UX UY a ha i) g)).obj L)
      (AlgebraicGeometry.pullbackGlobalSections
        (pullback.snd (pieceMap f UX UY a ha i) g) L s) (k - p))
    ((chowGroupRestrict_cast C (pullback.fst f (g ≫ (UY (a i)).ι) ≫ sX)
        (pullback.fst (pieceMap f UX UY a ha i) g ≫ ((UX i).ι ≫ sX))
        (pieceComparison f UX UY a ha i g)
        (pieceComparison_comp_structureMorphism f UX UY a ha i g sX) hidx
        (c.cap (g ≫ (UY (a i)).ι) (k + 1) (chowGroupCongr C hgY (k + 1) α))).trans
      (congrArg (Eq.mp (congrArg (chowGroup C
        (pullback.fst (pieceMap f UX UY a ha i) g ≫ ((UX i).ι ≫ sX))) hidx)) hcapg.symm))

/-! ### The restricted class and the map into the product -/

/-- **Stacks 0FDZ.** The restriction `c_i` of a bivariant class `c` of degree `p` for
`f : X ⟶ Y` to the piece `f_i : X_i ⟶ Y_{a(i)}` of a disjoint union decomposition: the bivariant
class of degree `p` for `f_i` whose cap operation is
`Stacks.Chow.bivariantPieceRestrictionCap`.

The construction carries the open-immersion case of Stacks 02TA for the Gysin system, so **no
`@[stacks 0FDZ]` attribute is placed here**: the tag sits on
`Stacks.Chow.bivariantPieceRestrictionOfInvertible`
(`StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceGysinSystemOfInvertible`), which is
this construction at the Gysin system of the genuine first Chern class rule, where that
compatibility is a theorem. See the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceRestriction`. -/
def bivariantPieceRestriction
    (hgys : G.IsNaturalUnderOpenImmersion) (c : BivariantClass C G sX sY f hf p) :
    BivariantClass C G ((UX i).ι ≫ sX) ((UY (a i)).ι ≫ sY) (pieceMap f UX UY a ha i)
      (pieceMap_comp_structureMorphism C sX sY f hf UX UY a ha i) p where
  cap g _ k := bivariantPieceRestrictionCap C G sX sY f hf p UX UY a ha i c g k
  cap_properPushforward := by
    intro T₀ T₀' g₀ _ w₀ _ w₀' sq₀ hfst₀ k₀ α₀
    exact (bivariantPieceRestrictionCap_proper_naturality C G sX sY f hf p UX UY a ha i c)
      g₀ w₀ w₀' sq₀ hfst₀ k₀ _ _ α₀
  cap_flatPullbackChow := by
    intro T₀ T₀' g₀ _ w₀ _ _ r₀ hr₀ w₀' sq₀ hfst₀ k₀ α₀
    exact (bivariantPieceRestrictionCap_flat_naturality C G sX sY f hf p UX UY a ha i c)
      g₀ w₀ r₀ hr₀ w₀' sq₀ hfst₀ k₀ _ _ _ α₀
  cap_gysin := by
    intro T₀ g₀ _ L₀ _ s₀ k₀ _ _ _ _ ε₀ hε₀ hbase₀ α₀
    exact (bivariantPieceRestrictionCap_gysin_naturality C G sX sY f hf p UX UY a ha i hgys c)
      g₀ L₀ s₀ k₀ ε₀ hε₀ hbase₀ _ α₀

/-- **Stacks 0FDZ.** The restriction to a piece caps by the restricted cap operation. -/
@[simp]
theorem bivariantPieceRestriction_cap
    (hgys : G.IsNaturalUnderOpenImmersion) (c : BivariantClass C G sX sY f hf p)
    {T : Scheme.{u}} (g : T ⟶ (UY (a i) : Scheme.{u})) [LocallyOfFiniteType g] (k : ℤ)
    (β : chowGroup C (g ≫ ((UY (a i)).ι ≫ sY)) k) :
    (bivariantPieceRestriction C G sX sY f hf p UX UY a ha i hgys c).cap g k β =
      bivariantPieceRestrictionCap C G sX sY f hf p UX UY a ha i c g k β :=
  rfl

/-- **Stacks 0FDZ.** Restriction to a piece is additive. -/
theorem bivariantPieceRestriction_add
    (hgys : G.IsNaturalUnderOpenImmersion) (c d : BivariantClass C G sX sY f hf p) :
    bivariantPieceRestriction C G sX sY f hf p UX UY a ha i hgys (c + d) =
      bivariantPieceRestriction C G sX sY f hf p UX UY a ha i hgys c +
        bivariantPieceRestriction C G sX sY f hf p UX UY a ha i hgys d := by
  refine BivariantClass.ext C G ((UX i).ι ≫ sX) ((UY (a i)).ι ≫ sY) (pieceMap f UX UY a ha i)
    (pieceMap_comp_structureMorphism C sX sY f hf UX UY a ha i) p ?_
  intro T g _ k β
  simp only [bivariantPieceRestriction_cap, BivariantClass.add_cap,
    bivariantPieceRestrictionCap_apply, map_add]

/-- **Stacks 0FDZ.** Restriction to a piece commutes with negation. -/
theorem bivariantPieceRestriction_neg
    (hgys : G.IsNaturalUnderOpenImmersion) (c : BivariantClass C G sX sY f hf p) :
    bivariantPieceRestriction C G sX sY f hf p UX UY a ha i hgys (-c) =
      -bivariantPieceRestriction C G sX sY f hf p UX UY a ha i hgys c := by
  refine BivariantClass.ext C G ((UX i).ι ≫ sX) ((UY (a i)).ι ≫ sY) (pieceMap f UX UY a ha i)
    (pieceMap_comp_structureMorphism C sX sY f hf UX UY a ha i) p ?_
  intro T g _ k β
  simp only [bivariantPieceRestriction_cap, BivariantClass.neg_cap,
    bivariantPieceRestrictionCap_apply, map_neg]

/-- **Stacks 0FDZ.** Restriction to a piece carries the zero class to the zero class. -/
theorem bivariantPieceRestriction_zero
    (hgys : G.IsNaturalUnderOpenImmersion) :
    bivariantPieceRestriction C G sX sY f hf p UX UY a ha i hgys 0 = 0 := by
  refine BivariantClass.ext C G ((UX i).ι ≫ sX) ((UY (a i)).ι ≫ sY) (pieceMap f UX UY a ha i)
    (pieceMap_comp_structureMorphism C sX sY f hf UX UY a ha i) p ?_
  intro T g _ k β
  simp only [bivariantPieceRestriction_cap, BivariantClass.zero_cap,
    bivariantPieceRestrictionCap_apply, map_zero]

/-- **Stacks 0FDZ.** The map `A^p(X ⟶ Y) ⟶ ∏_{i ∈ I} A^p(X_i ⟶ Y_{a(i)})` of the tag, as a
homomorphism of groups: its `i`-th component is restriction to the piece `i`.

Like `Stacks.Chow.bivariantPieceRestriction` this carries the open-immersion case of Stacks 02TA
for the Gysin system, so the attribute sits on
`Stacks.Chow.bivariantPieceRestrictionHomOfInvertible` instead. -/
def bivariantPieceRestrictionHom
    (hgys : G.IsNaturalUnderOpenImmersion) :
    BivariantClass C G sX sY f hf p →+
      ∀ i, BivariantClass C G ((UX i).ι ≫ sX) ((UY (a i)).ι ≫ sY) (pieceMap f UX UY a ha i)
        (pieceMap_comp_structureMorphism C sX sY f hf UX UY a ha i) p where
  toFun c i := bivariantPieceRestriction C G sX sY f hf p UX UY a ha i hgys c
  map_zero' := funext fun i ↦ bivariantPieceRestriction_zero C G sX sY f hf p UX UY a ha i hgys
  map_add' c d :=
    funext fun i ↦ bivariantPieceRestriction_add C G sX sY f hf p UX UY a ha i hgys c d

/-- **Stacks 0FDZ.** The components of the map into the product are the restrictions to the
pieces. -/
@[simp]
theorem bivariantPieceRestrictionHom_apply
    (hgys : G.IsNaturalUnderOpenImmersion) (c : BivariantClass C G sX sY f hf p) :
    bivariantPieceRestrictionHom C G sX sY f hf p UX UY a ha hgys c i =
      bivariantPieceRestriction C G sX sY f hf p UX UY a ha i hgys c :=
  rfl

end Stacks.Chow

end
