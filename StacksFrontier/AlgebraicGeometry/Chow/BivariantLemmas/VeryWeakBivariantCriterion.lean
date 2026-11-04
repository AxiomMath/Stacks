module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.SectionGysinRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.FamilyBaseChangeProduct
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.FamilyFibreDifferenceExistence
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.IntegralFamilyCycle
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Triviality

/-!
# The very weak form of Fulton's Theorem 17.1

Let `(S, δ)` be the base situation of chapter 42 and let `f : X ⟶ Y` be a morphism of schemes
locally of finite type over `S`. A *very weak cap rule of degree `p`* assigns to every morphism
`g : Y' ⟶ Y` locally of finite type and every `k` an additive map

  `c ∩ - : Z_k(Y') ⟶ A_{k-p}(X')`,   `X' = Y' ×_Y X`,

**on cycles** rather than on Chow classes. Stacks 0B7A says that such a rule automatically
factors through rational equivalence as soon as it satisfies condition (3) of Stacks 0B76 for
every divisor whose normal bundle is trivial, and that is what is proved here.

The proof is the one in the source. A cycle `α` rationally equivalent to zero is the total fibre
difference of a locally finite family of integral closed subschemes of `P = Y' ×_S ℙ¹_S`
(Stacks 02S4 part (4)); so `α = i_0^*β - i_∞^*β` for the cycle `β` on `P` presented by that
family and the two constant sections `i_0, i_∞ : Y' ⟶ P`, which are effective Cartier divisors
with trivial normal bundle (Stacks 0F93). Condition (3) therefore applies at both sections and
gives `c ∩ i_0^*β = j_0^*(c ∩ β)` and `c ∩ i_∞^*β = j_∞^*(c ∩ β)`, where `j_0, j_∞` are the two
constant sections of `X' ×_S ℙ¹_S ⟶ X'` read inside `X' ×_Y P`. The two right-hand sides agree
in `A_{k-p}(X')` because the two section Gysin maps of a family of projective lines agree on
Chow groups (Stacks 02S4 again), so `c ∩ α = 0`.

## Main definitions

* `Stacks.Chow.VeryWeakCapRule` — the rule of Stacks 0B7A: a cap operation on cycles.
* `Stacks.Chow.VeryWeakCapRule.IsCycleGysinNatural` — condition (3) of Stacks 0B76 for such a
  rule, with both Gysin maps the ones on cycles of Stacks 0B6Z.
* `Stacks.Chow.VeryWeakCapRule.IsGysinNaturalOnCycles` — condition (3) with the Gysin map on
  Chow groups of a Gysin system on the base change, phrased as in Definition 02T8 for a triple
  `(L, s, i)` with `i` an arbitrary closed immersion cutting out the zero scheme of `s`.
* `Stacks.Chow.GysinSystem.OnChowEqGysinCycleMap` — the compatibility of a Gysin system with the
  Gysin map on cycles of Stacks 0B6Z, which turns the second form of condition (3) into the
  first.
* `Stacks.Chow.VeryWeakCapRule.capChowOfCycleGysin` — the descended operation
  `A_k(Y') ⟶ A_{k-p}(X')`.

## Main results

* `Stacks.Chow.VeryWeakCapRule.cap_eq_zero_of_isCycleGysinNatural` — **Stacks 0B7A**: a very
  weak cap rule satisfying condition (3) kills every cycle rationally equivalent to zero.
* `Stacks.Chow.VeryWeakCapRule.cap_eq_zero_of_mem_rationalEquivalences` — the same conclusion
  for a rule whose condition (3) is stated against a Gysin system.
* `Stacks.Chow.sub_gysinCycleMapAlong_sections_eq_of_familyFibreDifference` — the cycle identity
  `i_0^*β - i_∞^*β = α` of the proof.
* `Stacks.Chow.eq_of_chowPushforwardOfIso_mk_gysinCycleMap_sections` — the equality of the two
  section Gysin maps on cycles of a family of projective lines, read back on the base through
  the two presenting isomorphisms.

## Implementation notes

### Condition (3) is stated as in Definition 02T8, not as `BivariantClass.gysin_naturality`

`Stacks.Chow.BivariantClass.gysin_naturality` states condition (3) for the **canonical**
presentation of the zero scheme: the divisor is `D = Z(s)` and the Gysin map is taken along
`D.subschemeι`. That form cannot prove Stacks 0B7A. The proof applies condition (3) on
`P = Y' ×_S ℙ¹_S` at the zero-section divisor, and needs the rule at `Y'` *itself*; but the
canonical form produces the rule at `D.subscheme` for `D` the zero-section divisor, and
`D.subscheme` is merely isomorphic to `Y'`, so the two composites have different domains and no
equation mentioning `c ∩ -` at `Y'` results.

Definition 02T8 — which Stacks 0B76 (3) refers to — presents the divisor by a triple
`(L, s, i : D ⟶ Y')` with `i` an *arbitrary* closed immersion cutting out `Z(s)`, and that is
the form used here. At `i = (Z(s)).subschemeι` it is exactly `gysin_naturality`, since
`Stacks.Chow.gysinCycleMapAlong_subschemeι` says the Gysin map along the canonical presentation
is `Stacks.Chow.gysinCycleMap`. The extra generality is what makes the hypothesis applicable at a
section of a family, where the natural presentation of the divisor is the section itself.

### The rule is additive

The source says only "a map", but the map is a homomorphism of abelian groups: the proof
computes `c ∩ (i_0^*β - i_∞^*β)` as `c ∩ i_0^*β - c ∩ i_∞^*β`, and without that the conclusion
is false as stated. So `Stacks.Chow.VeryWeakCapRule.cap` lands in `→+`, as the cap operation of
Stacks 0B76 does.

### Why condition (3) is read on cycles, and in that quantifier order

Stacks 0B7A restricts condition (3) to divisors with `ℒ'|_{D'} ≅ 𝒪_{D'}`, and Stacks 0B6Z says
that for such a divisor the Gysin pullback is defined on cycles. So both Gysin maps of
condition (3) are the ones of Stacks 0B6Z in `Stacks.Chow.VeryWeakCapRule.IsCycleGysinNatural`:
the left-hand side is a cycle on `Y'`, and the right-hand side is read on a cycle `δ`
representing `c ∩ α`. That identifies the two Chern-class-free rules with each other and needs
no Gysin system; `Stacks.Chow.GysinSystem.OnChowEqGysinCycleMap` is what converts the Gysin
system form of condition (3) into it, and the two forms say the same thing once the Gysin map on
Chow groups of Stacks 02T8 is known to be induced by the one on cycles.

The representative `δ` is chosen once per cycle `α`, before the divisor is quantified, and that
order matters. Quantifying `δ` over all representatives of `c ∩ α` would make the condition
assert, for two representatives differing by a rational equivalence, that their Gysin images on
cycles agree in the Chow group — which is a part of Stacks 02TO rather than of condition (3), and
would leave the condition with no instances. In the order used here the zero rule satisfies it,
which is `Stacks.Chow.isCycleGysinNatural_zero`.

### Two source defects

The display of Stacks 0B7A writes `Y' = X' ×_X Y`, which is backwards: Stacks 0B76 writes
`X' = Y' ×_Y X`, and that is the direction used here and the only one that makes the rule a rule
on morphisms `Y' ⟶ Y`. And `Let α ∈ Z_k(X')` in the proof must read `Z_k(Y')`, since `c ∩ -` is
defined on cycles on `Y'`; likewise the `j_0, j_∞ : Y' ⟶ Y' × 𝐏¹` of the proof are the sections
of `X' × 𝐏¹`.

## References

* [Stacks Project, Tag 0B7A](https://stacks.math.columbia.edu/tag/0B7A)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 0B6Z](https://stacks.math.columbia.edu/tag/0B6Z)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 02S4](https://stacks.math.columbia.edu/tag/02S4)
* [Stacks Project, Tag 0F93](https://stacks.math.columbia.edu/tag/0F93)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### A closed immersion presenting a given closed subscheme -/

/-- The isomorphism `D ≅ Z` attached to a closed immersion `m : D ⟶ V` cutting out a given closed
subscheme `Z ⊆ V`. For `Z = m.ker` it is `AlgebraicGeometry.Scheme.Hom.toImage`. -/
def isoSubschemeOfKer {D V : Scheme.{u}} (m : D ⟶ V) [IsClosedImmersion m]
    (Z : V.IdealSheafData) (hker : m.ker = Z) : D ≅ Z.subscheme := by
  subst hker
  exact asIso m.toImage

/-- The isomorphism attached to a closed immersion presenting a closed subscheme is an
isomorphism over the ambient scheme. -/
@[reassoc (attr := simp)]
theorem isoSubschemeOfKer_hom_subschemeι {D V : Scheme.{u}} (m : D ⟶ V) [IsClosedImmersion m]
    (Z : V.IdealSheafData) (hker : m.ker = Z) :
    (isoSubschemeOfKer m Z hker).hom ≫ Z.subschemeι = m := by
  subst hker
  exact m.toImage_imageι

/-! ### The pullback of a divisor to the base change -/

section BivariantPullback

variable {X Y T : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y) (L : T.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]

/-- The invertible module `𝒩'` of condition (3) of Stacks 0B76: the pullback of `ℒ'` to the base
change `X' = Y' ×_Y X`. -/
abbrev bivariantPullbackModule : (pullback f g).Modules :=
  (Scheme.Modules.pullback (pullback.snd f g)).obj L

/-- The section `t'` of condition (3) of Stacks 0B76: the pullback of `s'` to the base change
`X' = Y' ×_Y X`. -/
abbrev bivariantPullbackSection (s : Γ(L, ⊤)) : Γ(bivariantPullbackModule f g L, ⊤) :=
  pullbackGlobalSections (pullback.snd f g) L s

/-- The divisor `E'` of condition (3) of Stacks 0B76: the zero scheme on the base change
`X' = Y' ×_Y X` of the pulled-back section, which by Stacks 0B6Y is the inverse image of the
divisor `D' = Z(s')` on `Y'`. -/
abbrev bivariantPullbackZeroScheme (s : Γ(L, ⊤)) : (pullback f g).IdealSheafData :=
  Stacks.Divisors.zeroScheme (pullback f g) (bivariantPullbackModule f g L)
    (bivariantPullbackSection f g L s)

end BivariantPullback

/-! ### The compatibility of a Gysin system with the Gysin map on cycles -/

/-- **The compatibility of a Gysin system with the Gysin map on cycles of Stacks 0B6Z.** For every
scheme locally of finite type over the base, every invertible module `L` on it, every section `s`
whose zero scheme carries a trivial restriction of `L`, and every cycle `δ`, the Gysin map on
Chow groups of the system sends the class of `δ` to the class of the Gysin map on cycles.

What converts condition (3) stated against a Gysin system into
`Stacks.Chow.VeryWeakCapRule.IsCycleGysinNatural`; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VeryWeakBivariantCriterion`. -/
def GysinSystem.OnChowEqGysinCycleMap {C : ChowSituation.{u}} (G : GysinSystem C) : Prop :=
  ∀ {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤))
    (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme T L s).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme T L s).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme T L s).subschemeι).obj L))
    (k : ℤ) (δ : CycleGroup C q (k + 1)),
    G.onChow q L s k (QuotientAddGroup.mk' (rationalEquivalences C q (k + 1)) δ) =
      QuotientAddGroup.mk' (rationalEquivalences C
        ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ q) k) (gysinCycleMap C q k L s htriv δ)

/-! ### The rule of Stacks 0B7A -/

/-- **Stacks 0B7A.** A *very weak cap rule of degree `p` for `f : X ⟶ Y`*: a rule assigning to
every morphism `g : Y' ⟶ Y` locally of finite type and every `k` an additive map
`Z_k(Y') ⟶ A_{k-p}(X')`, where `X' = Y' ×_Y X`.

Unlike a bivariant class (Stacks 0B76) the source is the group of *cycles* and no compatibility
is required; the compatibilities available are hypotheses on the use site, of which Stacks 0B7A
needs only `Stacks.Chow.VeryWeakCapRule.IsGysinNaturalOnCycles`. -/
structure VeryWeakCapRule (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
    [LocallyOfFiniteType f] (hf : f ≫ sY = sX) (p : ℤ) : Type (u + 1) where
  /-- The cap operation on the cycles of each test scheme. -/
  cap : ∀ {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ),
    CycleGroup C (g ≫ sY) k →+ chowGroup C (pullback.fst f g ≫ sX) (k - p)

/-- **Condition (3) of Stacks 0B76 for a rule on cycles, phrased as in Definition 02T8.** For a
triple `(L, s, i : D ⟶ Y')` as in Definition 02T8 whose invertible module restricts trivially to
the zero scheme of `s`, with pullback `(𝒩', t', j' : E' ⟶ X')` to `X'`, the cap operation
commutes with the two Gysin maps:

  `c ∩ i^*α = (j')^*(c ∩ α)`   for every cycle `α` on `Y'`,

where `i^*` is the Gysin map on cycles of Stacks 0B6Z read along `i`, `(j')^*` is the Gysin map
on Chow groups of the Gysin system `G`, and the identification `D ×_Y X ≅ E'` of Stacks 0B6Y is
recorded by the isomorphism `e`.

The morphism `gZ : D ⟶ Y` is `i ≫ g` presented as a morphism in its own right, which is what
lets the conclusion mention the rule at a *given* test scheme — at a section `i` of a family
`g : P ⟶ Y` over `Y'`, `gZ` is the structure morphism of `Y'` itself. -/
def VeryWeakCapRule.IsGysinNaturalOnCycles {C : ChowSituation.{u}} {X Y : Scheme.{u}}
    {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {f : X ⟶ Y}
    [LocallyOfFiniteType f] {hf : f ≫ sY = sX} {p : ℤ}
    (c : VeryWeakCapRule C sX sY f hf p) (G : GysinSystem C) : Prop :=
  ∀ {T D : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤))
    (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme T L s).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme T L s).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme T L s).subschemeι).obj L))
    (i : D ⟶ T) [IsClosedImmersion i] (hker : i.ker = Stacks.Divisors.zeroScheme T L s)
    (gZ : D ⟶ Y) [LocallyOfFiniteType gZ] (hgZ : i ≫ g = gZ) (k : ℤ)
    (e : pullback f gZ ≅ (bivariantPullbackZeroScheme f g L s).subscheme)
    (_he₁ : e.hom ≫ (bivariantPullbackZeroScheme f g L s).subschemeι =
      pullback.map f gZ f g (𝟙 X) i (𝟙 Y) (by simp)
        (by rw [Category.comp_id]; exact hgZ.symm))
    (he₂ : e.hom ≫ ((bivariantPullbackZeroScheme f g L s).subschemeι ≫
      pullback.fst f g ≫ sX) = pullback.fst f gZ ≫ sX)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C (pullback.fst f gZ ≫ sX)
      ((bivariantPullbackZeroScheme f g L s).subschemeι ≫ pullback.fst f g ≫ sX) e.hom he₂
      (k - p))
    (α : CycleGroup C (g ≫ sY) (k + 1)),
    properChowPushforward C (pullback.fst f gZ ≫ sX)
        ((bivariantPullbackZeroScheme f g L s).subschemeι ≫ pullback.fst f g ≫ sX) e.hom he₂
        (k - p) hfac
        (c.cap gZ k (gysinCycleMapAlong C (g ≫ sY) (gZ ≫ sY) k L s i htriv
          (by rw [← Category.assoc, hgZ]) hker α)) =
      G.onChow (pullback.fst f g ≫ sX) (bivariantPullbackModule f g L)
        (bivariantPullbackSection f g L s) (k - p)
        (Eq.mp (congrArg (chowGroup C (pullback.fst f g ≫ sX))
          (by omega : (k + 1) - p = (k - p) + 1)) (c.cap g (k + 1) α))

/-- **Condition (3) of Stacks 0B76 for a rule on cycles, with both Gysin maps read on cycles.**
For a triple `(L, s, i : D ⟶ Y')` as in Definition 02T8 whose invertible module restricts
trivially to the zero scheme of `s`, with pullback `(𝒩', t', j' : E' ⟶ X')` to `X'`, the cap
operation commutes with the two Gysin maps on cycles of Stacks 0B6Z:

  `c ∩ i^*α = (j')^*δ`   for every cycle `α` on `Y'`,

where `δ` is a cycle representing `c ∩ α`, one and the same for every triple, and the
identification `D ×_Y X ≅ E'` of Stacks 0B6Y is recorded by the isomorphism `e`.

Since `𝒩'|_{E'}` is trivial, `(j')^*` is defined on cycles, which is what lets the condition be
stated without the Gysin map on Chow groups of a Gysin system. -/
def VeryWeakCapRule.IsCycleGysinNatural {C : ChowSituation.{u}} {X Y : Scheme.{u}}
    {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {f : X ⟶ Y}
    [LocallyOfFiniteType f] {hf : f ≫ sY = sX} {p : ℤ}
    (c : VeryWeakCapRule C sX sY f hf p) : Prop :=
  ∀ {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ)
    (α : CycleGroup C (g ≫ sY) (k + 1)),
    ∃ δ : CycleGroup C (pullback.fst f g ≫ sX) ((k - p) + 1),
      Eq.mp (congrArg (chowGroup C (pullback.fst f g ≫ sX))
            (by omega : (k + 1) - p = (k - p) + 1)) (c.cap g (k + 1) α) =
          QuotientAddGroup.mk'
            (rationalEquivalences C (pullback.fst f g ≫ sX) ((k - p) + 1)) δ ∧
      ∀ {D : Scheme.{u}} (L : T.Modules)
        [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
        (s : Γ(L, ⊤))
        (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
          (Stacks.Divisors.zeroScheme T L s).subscheme.sheaf.obj
          (Stacks.Divisors.zeroScheme T L s).subscheme.ringCatSheaf.property
          ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme T L s).subschemeι).obj L))
        (i : D ⟶ T) [IsClosedImmersion i] (hker : i.ker = Stacks.Divisors.zeroScheme T L s)
        (gZ : D ⟶ Y) [LocallyOfFiniteType gZ] (hgZ : i ≫ g = gZ)
        (e : pullback f gZ ≅ (bivariantPullbackZeroScheme f g L s).subscheme)
        (_he₁ : e.hom ≫ (bivariantPullbackZeroScheme f g L s).subschemeι =
          pullback.map f gZ f g (𝟙 X) i (𝟙 Y) (by simp)
            (by rw [Category.comp_id]; exact hgZ.symm))
        (he₂ : e.hom ≫ ((bivariantPullbackZeroScheme f g L s).subschemeι ≫
          pullback.fst f g ≫ sX) = pullback.fst f gZ ≫ sX)
        (hfac : ProperPushforwardFactorsThroughRationalEquivalence C (pullback.fst f gZ ≫ sX)
          ((bivariantPullbackZeroScheme f g L s).subschemeι ≫ pullback.fst f g ≫ sX) e.hom he₂
          (k - p)),
        properChowPushforward C (pullback.fst f gZ ≫ sX)
            ((bivariantPullbackZeroScheme f g L s).subschemeι ≫ pullback.fst f g ≫ sX) e.hom he₂
            (k - p) hfac
            (c.cap gZ k (gysinCycleMapAlong C (g ≫ sY) (gZ ≫ sY) k L s i htriv
              (by rw [← Category.assoc, hgZ]) hker α)) =
          QuotientAddGroup.mk' (rationalEquivalences C
            ((bivariantPullbackZeroScheme f g L s).subschemeι ≫ pullback.fst f g ≫ sX) (k - p))
            (gysinCycleMap C (pullback.fst f g ≫ sX) (k - p) (bivariantPullbackModule f g L)
              (bivariantPullbackSection f g L s)
              (Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections
                (pullback.snd f g) L s htriv) δ)

/-- A rule satisfying condition (3) in the form of
`Stacks.Chow.VeryWeakCapRule.IsGysinNaturalOnCycles` satisfies it in the form of
`Stacks.Chow.VeryWeakCapRule.IsCycleGysinNatural` as soon as the Gysin map on Chow groups of the
system is the class of the Gysin map on cycles. -/
theorem VeryWeakCapRule.isCycleGysinNatural_of_isGysinNaturalOnCycles {C : ChowSituation.{u}}
    (G : GysinSystem C) {X Y : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
    {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {f : X ⟶ Y} [LocallyOfFiniteType f]
    {hf : f ≫ sY = sX} {p : ℤ} (c : VeryWeakCapRule C sX sY f hf p)
    (hc : c.IsGysinNaturalOnCycles G) (hG : G.OnChowEqGysinCycleMap) :
    c.IsCycleGysinNatural := by
  intro T g _ k α
  obtain ⟨δ, hδ⟩ := QuotientAddGroup.mk'_surjective
    (rationalEquivalences C (pullback.fst f g ≫ sX) ((k - p) + 1))
    (Eq.mp (congrArg (chowGroup C (pullback.fst f g ≫ sX))
      (by omega : (k + 1) - p = (k - p) + 1)) (c.cap g (k + 1) α))
  refine ⟨δ, hδ.symm, ?_⟩
  intro D L _ s htriv i _ hker gZ _ hgZ e he₁ he₂ hfac
  refine (hc g L s htriv i hker gZ hgZ k e he₁ he₂ hfac α).trans ?_
  refine (congrArg (fun x ↦ G.onChow (pullback.fst f g ≫ sX) (bivariantPullbackModule f g L)
    (bivariantPullbackSection f g L s) (k - p) x) hδ.symm).trans ?_
  exact hG (pullback.fst f g ≫ sX) (bivariantPullbackModule f g L)
    (bivariantPullbackSection f g L s)
    (Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections
      (pullback.snd f g) L s htriv) (k - p) δ

/-- The zero rule, capping every cycle to zero. -/
instance (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f]
    (hf : f ≫ sY = sX) (p : ℤ) : Zero (VeryWeakCapRule C sX sY f hf p) where
  zero := { cap := fun _ _ _ ↦ 0 }

/-- Transporting the zero class of a Chow group along an equality of degrees gives zero. -/
private theorem eq_mp_chowGroup_zero (C : ChowSituation.{u}) {Z : Scheme.{u}} (q : Z ⟶ C.S)
    [LocallyOfFiniteType q] {m n : ℤ} (h : m = n) :
    Eq.mp (congrArg (chowGroup C q) h) (0 : chowGroup C q m) = 0 := by
  cases h
  rfl

/-- **Condition (3) has instances.** The zero rule satisfies it, so the hypothesis of
Stacks 0B7A is satisfiable and the criterion is not vacuous. -/
theorem isGysinNaturalOnCycles_zero (C : ChowSituation.{u}) (G : GysinSystem C)
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX) (p : ℤ) :
    (0 : VeryWeakCapRule C sX sY f hf p).IsGysinNaturalOnCycles G := by
  intro T D g _ L _ s htriv i _ hker gZ _ hgZ k e he₁ he₂ hfac α
  have h1 : (0 : VeryWeakCapRule C sX sY f hf p).cap gZ k = 0 := rfl
  have h2 : (0 : VeryWeakCapRule C sX sY f hf p).cap g (k + 1) = 0 := rfl
  rw [h1, h2, AddMonoidHom.zero_apply, AddMonoidHom.zero_apply, eq_mp_chowGroup_zero, map_zero,
    map_zero]
  omega

/-- **Condition (3) read on cycles has instances.** The zero rule satisfies it, so the hypothesis
of Stacks 0B7A is satisfiable and the criterion is not vacuous. -/
theorem isCycleGysinNatural_zero (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
    [LocallyOfFiniteType f] (hf : f ≫ sY = sX) (p : ℤ) :
    (0 : VeryWeakCapRule C sX sY f hf p).IsCycleGysinNatural := by
  intro T g _ k α
  have h1 : (0 : VeryWeakCapRule C sX sY f hf p).cap g (k + 1) = 0 := rfl
  refine ⟨0, ?_, ?_⟩
  · rw [h1, AddMonoidHom.zero_apply, eq_mp_chowGroup_zero, map_zero]
    omega
  · intro D L _ s htriv i _ hker gZ _ hgZ e he₁ he₂ hfac
    have h2 : (0 : VeryWeakCapRule C sX sY f hf p).cap gZ k = 0 := rfl
    rw [h2, AddMonoidHom.zero_apply, map_zero, map_zero, map_zero]

/-! ### The cycle identity of the proof -/

section FibreDifference

attribute [local instance] isEffectiveCartierDivisor_ker_zeroSection
  isEffectiveCartierDivisor_ker_infinitySection

/-- **The cycle identity `i_0^*β - i_∞^*β = α` of the proof of Stacks 0B7A.** Let `α` be a
`k`-cycle on `Z` which is the total fibre difference of a locally finite family `(W_j)_j` of
integral closed subschemes of `Z ×_S 𝐏¹_S`, each of delta-dimension `k + 1` and contained in
neither distinguished section, and let `β` be the `(k+1)`-cycle presented by that family. Then
`α` is the difference of the two section Gysin maps of Stacks 0B6Z applied to `β`.

Each Gysin map is the coefficientwise extension of its rule on integral components, so both
sides are locally finite sums over the family; away from the two sections the rule is the
fundamental cycle of the fibre, which is exactly the summand of
`Stacks.Chow.familyFibreDifferenceCoefficient`. -/
theorem sub_gysinCycleMapAlong_sections_eq_of_familyFibreDifference (C : ChowSituation.{u})
    {Z : Scheme.{u}} (q : Z ⟶ C.S) [LocallyOfFiniteType q] (k : ℤ) {J : Type u}
    (W : J → (projectiveLineProduct q).IdealSheafData)
    (hInt : ∀ j, IsIntegral (W j).subscheme)
    (hDim : ∀ j, schemeDeltaDimension C ((W j).subschemeι ≫ familyStructureMorphism q) =
      ((k + 1 : ℤ) : EInt))
    (hn0 : ∀ j, ¬ Set.range (W j).subschemeι ⊆ Set.range (zeroSection q))
    (hni : ∀ j, ¬ Set.range (W j).subschemeι ⊆ Set.range (infinitySection q))
    (hLoc : LocallyFinite fun j ↦ ((W j).support : Set (projectiveLineProduct q)))
    (β : CycleGroup C (familyStructureMorphism q) (k + 1))
    (hβ : ∀ x : projectiveLineProduct q, β.1 x = ∑ᶠ j : J, (1 : ℤ) *
      (cycleAssociatedToClosedSubscheme C (familyStructureMorphism q) (W j).subschemeι
        (k + 1)).1 x)
    (α : CycleGroup C q k)
    (hα : ∀ x : Z, α.1 x = familyFibreDifferenceCoefficient C q k W x) :
    gysinCycleMapAlong C (familyStructureMorphism q) q k
        (Stacks.Divisors.divisorSheaf (zeroSection q).ker)
        (Stacks.Divisors.divisorSheafGlobalSection (zeroSection q).ker) (zeroSection q)
        (isTrivial_zeroScheme_ker_zeroSection q) (zeroSection_comp_familyStructureMorphism q)
        (ker_zeroSection_eq_zeroScheme q) β -
      gysinCycleMapAlong C (familyStructureMorphism q) q k
        (Stacks.Divisors.divisorSheaf (infinitySection q).ker)
        (Stacks.Divisors.divisorSheafGlobalSection (infinitySection q).ker) (infinitySection q)
        (isTrivial_zeroScheme_ker_infinitySection q)
        (infinitySection_comp_familyStructureMorphism q)
        (ker_infinitySection_eq_zeroScheme q) β = α := by
  have key : ∀ (σ : Z ⟶ projectiveLineProduct q) [IsClosedImmersion σ]
      (L : (projectiveLineProduct q).Modules)
      [AlgebraicGeometry.SheafOfModules.IsInvertible (projectiveLineProduct q).sheaf.obj
        (projectiveLineProduct q).ringCatSheaf.property L]
      (s : Γ(L, ⊤)), σ.ker = Stacks.Divisors.zeroScheme (projectiveLineProduct q) L s →
      (∀ j, ¬ Set.range (W j).subschemeι ⊆ Set.range σ) →
      (∀ j, gysinCycleMapComponentAlong C (familyStructureMorphism q) q k L s σ
        (W j) (hInt j) (hDim j) =
          cycleAssociatedToClosedSubscheme C q ((W j).comap σ).subschemeι k) ∧
      ∀ y : Z, (Function.support fun j : J ↦ (1 : ℤ) *
        (gysinCycleMapComponentAlong C (familyStructureMorphism q) q k L s σ
          (W j) (hInt j) (hDim j)).1 y).Finite := by
    intro σ _ L _ s hker hn
    refine ⟨fun j ↦ gysinCycleMapComponentAlong_of_not_le C (familyStructureMorphism q) q k _ _ σ
      (W j) (hInt j) (hDim j) fun hle ↦ hn j ?_, fun y ↦ ?_⟩
    · have _ := hInt j
      rw [Scheme.IdealSheafData.range_subschemeι]
      exact (support_subset_range_iff_ker_le σ (W j)).2 (hker.trans_le hle)
    · refine finite_support_of_locallyFinite
        (fun j ↦ σ.base ⁻¹' ((W j).support : Set (projectiveLineProduct q)))
        (hLoc.preimage_continuous σ.continuous)
        (fun j y' ↦ (1 : ℤ) * (gysinCycleMapComponentAlong C (familyStructureMorphism q) q k L s σ
          (W j) (hInt j) (hDim j)).1 y') (fun j y' hy' ↦ ?_) y
      exact support_gysinCycleMapComponentAlong_subset C (familyStructureMorphism q) q k _ _
        σ (W j) (hInt j) (hDim j) (right_ne_zero_of_mul hy')
  obtain ⟨hcomp0, hfin0⟩ := key (zeroSection q) _ _ (ker_zeroSection_eq_zeroScheme q) hn0
  obtain ⟨hcompi, hfini⟩ := key (infinitySection q) _ _ (ker_infinitySection_eq_zeroScheme q) hni
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
  show (gysinCycleMapAlong C (familyStructureMorphism q) q k _ _ (zeroSection q)
        (isTrivial_zeroScheme_ker_zeroSection q)
        (zeroSection_comp_familyStructureMorphism q) (ker_zeroSection_eq_zeroScheme q) β).1 x -
      (gysinCycleMapAlong C (familyStructureMorphism q) q k _ _ (infinitySection q)
        (isTrivial_zeroScheme_ker_infinitySection q)
        (infinitySection_comp_familyStructureMorphism q)
        (ker_infinitySection_eq_zeroScheme q) β).1 x = α.1 x
  rw [gysinCycleMapAlong_apply_of_presentation C (familyStructureMorphism q) q k _ _
      (zeroSection q) (isTrivial_zeroScheme_ker_zeroSection q)
      (zeroSection_comp_familyStructureMorphism q) (ker_zeroSection_eq_zeroScheme q)
      W hInt hDim hLoc (fun _ ↦ (1 : ℤ)) β hβ x,
    gysinCycleMapAlong_apply_of_presentation C (familyStructureMorphism q) q k _ _
      (infinitySection q) (isTrivial_zeroScheme_ker_infinitySection q)
      (infinitySection_comp_familyStructureMorphism q) (ker_infinitySection_eq_zeroScheme q)
      W hInt hDim hLoc (fun _ ↦ (1 : ℤ)) β hβ x,
    hα x, familyFibreDifferenceCoefficient, ← finsum_sub_distrib (hfin0 x) (hfini x)]
  refine finsum_congr fun j ↦ ?_
  rw [one_mul, one_mul, hcomp0 j, hcompi j]
  rfl

end FibreDifference

/-! ### The two section Gysin maps of a Gysin system, read back on the base -/

/-- The Gysin map on Chow groups of a presentation of the zero scheme, read on the class of a
cycle and transported to the zero scheme itself: it is the class of
`Stacks.Chow.gysinCycleMap`. -/
theorem chowPushforwardOfIso_mk_gysinCycleMapAlong (C : ChowSituation.{u}) {V Z : Scheme.{u}}
    (sV : V ⟶ C.S) [LocallyOfFiniteType sV] (k : ℤ) (L : V.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible V.sheaf.obj V.ringCatSheaf.property L]
    (s : Γ(L, ⊤))
    (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme V L s).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme V L s).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme V L s).subschemeι).obj L))
    (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (i : Z ⟶ V) [IsClosedImmersion i]
    (hq : i ≫ sV = sZ) (hker : i.ker = Stacks.Divisors.zeroScheme V L s)
    (e : Z ≅ (Stacks.Divisors.zeroScheme V L s).subscheme)
    (he : e.hom ≫ (Stacks.Divisors.zeroScheme V L s).subschemeι = i)
    (hb : e.hom ≫ ((Stacks.Divisors.zeroScheme V L s).subschemeι ≫ sV) = sZ)
    (δ : CycleGroup C sV (k + 1)) :
    chowPushforwardOfIso C sZ ((Stacks.Divisors.zeroScheme V L s).subschemeι ≫ sV) e.hom hb k
        (QuotientAddGroup.mk' (rationalEquivalences C sZ k)
          (gysinCycleMapAlong C sV sZ k L s i htriv hq hker δ)) =
      QuotientAddGroup.mk' (rationalEquivalences C
        ((Stacks.Divisors.zeroScheme V L s).subschemeι ≫ sV) k)
        (gysinCycleMap C sV k L s htriv δ) :=
  (chowPushforwardOfIso_mk C sZ ((Stacks.Divisors.zeroScheme V L s).subschemeι ≫ sV) e.hom hb k
    _).trans (congrArg _ (properPushforward_gysinCycleMapAlong C sV k L s htriv sZ i hq hker e
      he δ))

/-- **The two section Gysin maps on cycles agree on the base.** Let `V` be a family of projective
lines over `B`, presented by `Φ : B ×_S 𝐏¹_S ≅ V` over `S`, and let `(L₀, s₀)` and `(L_∞, s_∞)`
present the two sections as zero schemes of sections of invertible modules with trivial
restriction. If two classes on `B` push forward, along the two induced isomorphisms, to the
classes of the two Gysin images on cycles of one and the same cycle `δ` on `V`, then those two
classes are equal.

The pushforward along either isomorphism is injective, and
`Stacks.Chow.chowPushforwardOfIso_mk_gysinCycleMapAlong` identifies each class with the class of
the Gysin map read along the corresponding section; those two agree by
`Stacks.Chow.mk_gysinCycleMapAlong_zeroSection_eq_infinitySection`. -/
theorem eq_of_chowPushforwardOfIso_mk_gysinCycleMap_sections (C : ChowSituation.{u})
    {B V : Scheme.{u}} (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    (sV : V ⟶ C.S) [LocallyOfFiniteType sV] (k : ℤ)
    (Φ : projectiveLineProduct sB ≅ V) (hΦ : Φ.hom ≫ sV = familyStructureMorphism sB)
    (L₀ : V.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible V.sheaf.obj V.ringCatSheaf.property L₀]
    (s₀ : Γ(L₀, ⊤))
    (htriv₀ : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme V L₀ s₀).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme V L₀ s₀).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme V L₀ s₀).subschemeι).obj L₀))
    (hker₀ : (zeroSection sB ≫ Φ.hom).ker = Stacks.Divisors.zeroScheme V L₀ s₀)
    (e₀ : B ≅ (Stacks.Divisors.zeroScheme V L₀ s₀).subscheme)
    (he₀ : e₀.hom ≫ (Stacks.Divisors.zeroScheme V L₀ s₀).subschemeι = zeroSection sB ≫ Φ.hom)
    (hb₀ : e₀.hom ≫ ((Stacks.Divisors.zeroScheme V L₀ s₀).subschemeι ≫ sV) = sB)
    (LI : V.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible V.sheaf.obj V.ringCatSheaf.property LI]
    (sI : Γ(LI, ⊤))
    (htrivI : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme V LI sI).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme V LI sI).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme V LI sI).subschemeι).obj LI))
    (hkerI : (infinitySection sB ≫ Φ.hom).ker = Stacks.Divisors.zeroScheme V LI sI)
    (eI : B ≅ (Stacks.Divisors.zeroScheme V LI sI).subscheme)
    (heI : eI.hom ≫ (Stacks.Divisors.zeroScheme V LI sI).subschemeι =
      infinitySection sB ≫ Φ.hom)
    (hbI : eI.hom ≫ ((Stacks.Divisors.zeroScheme V LI sI).subschemeι ≫ sV) = sB)
    (δ : CycleGroup C sV (k + 1)) (x₀ xI : chowGroup C sB k)
    (hx₀ : chowPushforwardOfIso C sB ((Stacks.Divisors.zeroScheme V L₀ s₀).subschemeι ≫ sV)
      e₀.hom hb₀ k x₀ =
      QuotientAddGroup.mk' (rationalEquivalences C
        ((Stacks.Divisors.zeroScheme V L₀ s₀).subschemeι ≫ sV) k)
        (gysinCycleMap C sV k L₀ s₀ htriv₀ δ))
    (hxI : chowPushforwardOfIso C sB ((Stacks.Divisors.zeroScheme V LI sI).subschemeι ≫ sV)
      eI.hom hbI k xI =
      QuotientAddGroup.mk' (rationalEquivalences C
        ((Stacks.Divisors.zeroScheme V LI sI).subschemeι ≫ sV) k)
        (gysinCycleMap C sV k LI sI htrivI δ)) :
    x₀ = xI := by
  have hq₀ : (zeroSection sB ≫ Φ.hom) ≫ sV = sB := by
    rw [Category.assoc, hΦ, zeroSection_comp_familyStructureMorphism]
  have hqI : (infinitySection sB ≫ Φ.hom) ≫ sV = sB := by
    rw [Category.assoc, hΦ, infinitySection_comp_familyStructureMorphism]
  have h0 := chowPushforwardOfIso_mk_gysinCycleMapAlong C sV k L₀ s₀ htriv₀ sB
    (zeroSection sB ≫ Φ.hom) hq₀ hker₀ e₀ he₀ hb₀ δ
  have hI := chowPushforwardOfIso_mk_gysinCycleMapAlong C sV k LI sI htrivI sB
    (infinitySection sB ≫ Φ.hom) hqI hkerI eI heI hbI δ
  have hx₀' : x₀ = QuotientAddGroup.mk' (rationalEquivalences C sB k)
      (gysinCycleMapAlong C sV sB k L₀ s₀ (zeroSection sB ≫ Φ.hom) htriv₀ hq₀ hker₀ δ) :=
    (chowGroupEquivOfIso C sB ((Stacks.Divisors.zeroScheme V L₀ s₀).subschemeι ≫ sV) e₀.hom
      hb₀ k).injective (hx₀.trans h0.symm)
  have hxI' : xI = QuotientAddGroup.mk' (rationalEquivalences C sB k)
      (gysinCycleMapAlong C sV sB k LI sI (infinitySection sB ≫ Φ.hom) htrivI hqI hkerI δ) :=
    (chowGroupEquivOfIso C sB ((Stacks.Divisors.zeroScheme V LI sI).subschemeι ≫ sV) eI.hom
      hbI k).injective (hxI.trans hI.symm)
  rw [hx₀', hxI']
  exact mk_gysinCycleMapAlong_zeroSection_eq_infinitySection C sB sV k Φ hΦ L₀ s₀ htriv₀
    hker₀ LI sI htrivI hkerI δ

/-- **The two section Gysin maps of a Gysin system agree on the base.** Let `V` be a family of
projective lines over `B`, presented by `Φ : B ×_S 𝐏¹_S ≅ V` over `S`, and let `(L₀, s₀)` and
`(L_∞, s_∞)` present the two sections as zero schemes of sections of invertible modules with
trivial restriction. If two classes on `B` push forward, along the two induced isomorphisms, to
the two Gysin images of one and the same class `γ` on `V`, then those two classes are equal.

`Stacks.Chow.GysinSystem.OnChowEqGysinCycleMap` rewrites each Gysin image of a cycle class as the
class of the Gysin map on cycles, which is
`Stacks.Chow.eq_of_chowPushforwardOfIso_mk_gysinCycleMap_sections`. -/
theorem eq_of_chowPushforwardOfIso_onChow_sections (C : ChowSituation.{u}) (G : GysinSystem C)
    (hG : G.OnChowEqGysinCycleMap) {B V : Scheme.{u}} (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    (sV : V ⟶ C.S) [LocallyOfFiniteType sV] (k : ℤ)
    (Φ : projectiveLineProduct sB ≅ V) (hΦ : Φ.hom ≫ sV = familyStructureMorphism sB)
    (L₀ : V.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible V.sheaf.obj V.ringCatSheaf.property L₀]
    (s₀ : Γ(L₀, ⊤))
    (htriv₀ : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme V L₀ s₀).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme V L₀ s₀).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme V L₀ s₀).subschemeι).obj L₀))
    (hker₀ : (zeroSection sB ≫ Φ.hom).ker = Stacks.Divisors.zeroScheme V L₀ s₀)
    (e₀ : B ≅ (Stacks.Divisors.zeroScheme V L₀ s₀).subscheme)
    (he₀ : e₀.hom ≫ (Stacks.Divisors.zeroScheme V L₀ s₀).subschemeι = zeroSection sB ≫ Φ.hom)
    (hb₀ : e₀.hom ≫ ((Stacks.Divisors.zeroScheme V L₀ s₀).subschemeι ≫ sV) = sB)
    (LI : V.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible V.sheaf.obj V.ringCatSheaf.property LI]
    (sI : Γ(LI, ⊤))
    (htrivI : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme V LI sI).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme V LI sI).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme V LI sI).subschemeι).obj LI))
    (hkerI : (infinitySection sB ≫ Φ.hom).ker = Stacks.Divisors.zeroScheme V LI sI)
    (eI : B ≅ (Stacks.Divisors.zeroScheme V LI sI).subscheme)
    (heI : eI.hom ≫ (Stacks.Divisors.zeroScheme V LI sI).subschemeι =
      infinitySection sB ≫ Φ.hom)
    (hbI : eI.hom ≫ ((Stacks.Divisors.zeroScheme V LI sI).subschemeι ≫ sV) = sB)
    (γ : chowGroup C sV (k + 1)) (x₀ xI : chowGroup C sB k)
    (hx₀ : chowPushforwardOfIso C sB ((Stacks.Divisors.zeroScheme V L₀ s₀).subschemeι ≫ sV)
      e₀.hom hb₀ k x₀ = G.onChow sV L₀ s₀ k γ)
    (hxI : chowPushforwardOfIso C sB ((Stacks.Divisors.zeroScheme V LI sI).subschemeι ≫ sV)
      eI.hom hbI k xI = G.onChow sV LI sI k γ) :
    x₀ = xI := by
  revert x₀ xI
  induction γ using QuotientAddGroup.induction_on with
  | H δ =>
    intro x₀ xI hx₀ hxI
    exact eq_of_chowPushforwardOfIso_mk_gysinCycleMap_sections C sB sV k Φ hΦ L₀ s₀ htriv₀
      hker₀ e₀ he₀ hb₀ LI sI htrivI hkerI eI heI hbI δ x₀ xI
      (hx₀.trans (hG sV L₀ s₀ htriv₀ k δ)) (hxI.trans (hG sV LI sI htrivI k δ))

/-! ### Condition (3) at the two sections of the family -/

section Criterion

attribute [local instance] isEffectiveCartierDivisor_ker_zeroSection
  isEffectiveCartierDivisor_ker_infinitySection

/-- **Condition (3) applied at both sections of the family of projective lines.** For a cycle `β`
on `Y' ×_S 𝐏¹_S`, the two values of `c ∩ -` on the two section Gysin images of `β` agree in
`A_{k-p}(X')`.

Condition (3) is applied twice, at the zero-section and at the infinity-section divisor; both
times the triple is presented by the section itself, so the conclusion is an equation about
`c ∩ -` at `Y'`. The identification `Y' ×_Y X ≅ E'` the condition asks for is the base change of
the section, which `Stacks.Chow.ker_sectionComparison_zero` and Stacks 0B6Y identify with the
zero scheme of the pulled-back section; and the two right-hand sides agree by
`Stacks.Chow.eq_of_chowPushforwardOfIso_mk_gysinCycleMap_sections`, the family of projective
lines over `X'` being `X' ×_Y (Y' ×_S 𝐏¹_S)` through `Stacks.Chow.familyProductIso`. -/
theorem cap_gysinCycleMapAlong_zeroSection_eq_infinitySection_of_isCycleGysinNatural
    (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] (p : ℤ)
    (c : VeryWeakCapRule C (f ≫ sY) sY f rfl p) (hc : c.IsCycleGysinNatural)
    {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ)
    (β : CycleGroup C (familyStructureMorphism (g ≫ sY)) (k + 1)) :
    c.cap g k (gysinCycleMapAlong C (familyStructureMorphism (g ≫ sY)) (g ≫ sY) k
        (Stacks.Divisors.divisorSheaf (zeroSection (g ≫ sY)).ker)
        (Stacks.Divisors.divisorSheafGlobalSection (zeroSection (g ≫ sY)).ker)
        (zeroSection (g ≫ sY)) (isTrivial_zeroScheme_ker_zeroSection (g ≫ sY))
        (zeroSection_comp_familyStructureMorphism (g ≫ sY))
        (ker_zeroSection_eq_zeroScheme (g ≫ sY)) β) =
      c.cap g k (gysinCycleMapAlong C (familyStructureMorphism (g ≫ sY)) (g ≫ sY) k
        (Stacks.Divisors.divisorSheaf (infinitySection (g ≫ sY)).ker)
        (Stacks.Divisors.divisorSheafGlobalSection (infinitySection (g ≫ sY)).ker)
        (infinitySection (g ≫ sY)) (isTrivial_zeroScheme_ker_infinitySection (g ≫ sY))
        (infinitySection_comp_familyStructureMorphism (g ≫ sY))
        (ker_infinitySection_eq_zeroScheme (g ≫ sY)) β) := by
  have hΦ : (familyProductIso f g sY).hom ≫
        (pullback.fst f (pullback.fst (g ≫ sY) (relativeProjectiveLine C.S ↘ C.S) ≫ g) ≫
          f ≫ sY) =
      familyStructureMorphism (pullback.fst f g ≫ f ≫ sY) := by
    rw [familyProductIso_hom_fst_assoc]
  obtain ⟨δ, -, hcond⟩ := hc (pullback.fst (g ≫ sY) (relativeProjectiveLine C.S ↘ C.S) ≫ g) k β
  -- condition (3) at a section `σ = constantSection e` presented by `(L, s)`
  have key : ∀ (σ : T ⟶ projectiveLineProduct (g ≫ sY)) [IsClosedImmersion σ]
      (σ' : pullback f g ⟶ projectiveLineProduct (pullback.fst f g ≫ f ≫ sY))
      [IsClosedImmersion σ'] (e : (⊤_ Scheme.{u}) ⟶ projectiveLine (ULift.{u} ℤ)),
      σ = constantSection (g ≫ sY) e → σ' = constantSection (pullback.fst f g ≫ f ≫ sY) e →
      ∀ (L : (projectiveLineProduct (g ≫ sY)).Modules)
      [AlgebraicGeometry.SheafOfModules.IsInvertible (projectiveLineProduct (g ≫ sY)).sheaf.obj
        (projectiveLineProduct (g ≫ sY)).ringCatSheaf.property L]
      (s : Γ(L, ⊤))
      (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
        (Stacks.Divisors.zeroScheme (projectiveLineProduct (g ≫ sY)) L s).subscheme.sheaf.obj
        (Stacks.Divisors.zeroScheme (projectiveLineProduct (g ≫ sY)) L
          s).subscheme.ringCatSheaf.property
        ((Scheme.Modules.pullback
          (Stacks.Divisors.zeroScheme (projectiveLineProduct (g ≫ sY)) L s).subschemeι).obj L))
      (hker : σ.ker = Stacks.Divisors.zeroScheme (projectiveLineProduct (g ≫ sY)) L s)
      (hq : σ ≫ familyStructureMorphism (g ≫ sY) = g ≫ sY),
      ∃ (E : pullback f g ≅ (bivariantPullbackZeroScheme f
          (pullback.fst (g ≫ sY) (relativeProjectiveLine C.S ↘ C.S) ≫ g) L s).subscheme)
        (hb : E.hom ≫ ((bivariantPullbackZeroScheme f (pullback.fst (g ≫ sY)
          (relativeProjectiveLine C.S ↘ C.S) ≫ g) L s).subschemeι ≫
          pullback.fst f (pullback.fst (g ≫ sY) (relativeProjectiveLine C.S ↘ C.S) ≫ g) ≫
            f ≫ sY) = pullback.fst f g ≫ f ≫ sY),
        E.hom ≫ (bivariantPullbackZeroScheme f (pullback.fst (g ≫ sY)
          (relativeProjectiveLine C.S ↘ C.S) ≫ g) L s).subschemeι =
          σ' ≫ (familyProductIso f g sY).hom ∧
        (σ' ≫ (familyProductIso f g sY).hom).ker =
          bivariantPullbackZeroScheme f (pullback.fst (g ≫ sY)
            (relativeProjectiveLine C.S ↘ C.S) ≫ g) L s ∧
        chowPushforwardOfIso C (pullback.fst f g ≫ f ≫ sY) ((bivariantPullbackZeroScheme f
          (pullback.fst (g ≫ sY) (relativeProjectiveLine C.S ↘ C.S) ≫ g) L s).subschemeι ≫
          pullback.fst f (pullback.fst (g ≫ sY) (relativeProjectiveLine C.S ↘ C.S) ≫ g) ≫
            f ≫ sY) E.hom hb (k - p)
          (c.cap g k (gysinCycleMapAlong C (familyStructureMorphism (g ≫ sY)) (g ≫ sY) k L s σ
            htriv hq hker β)) =
          QuotientAddGroup.mk' (rationalEquivalences C ((bivariantPullbackZeroScheme f
            (pullback.fst (g ≫ sY) (relativeProjectiveLine C.S ↘ C.S) ≫ g) L s).subschemeι ≫
            pullback.fst f (pullback.fst (g ≫ sY) (relativeProjectiveLine C.S ↘ C.S) ≫ g) ≫
              f ≫ sY) (k - p))
            (gysinCycleMap C (pullback.fst f (pullback.fst (g ≫ sY)
              (relativeProjectiveLine C.S ↘ C.S) ≫ g) ≫ f ≫ sY) (k - p)
              (bivariantPullbackModule f (pullback.fst (g ≫ sY)
                (relativeProjectiveLine C.S ↘ C.S) ≫ g) L)
              (bivariantPullbackSection f (pullback.fst (g ≫ sY)
                (relativeProjectiveLine C.S ↘ C.S) ≫ g) L s)
              (Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections
                (pullback.snd f (pullback.fst (g ≫ sY) (relativeProjectiveLine C.S ↘ C.S) ≫ g))
                L s htriv) δ) := by
    intro σ _ σ' _ e hσ hσ' L _ s htriv hker hq
    subst hσ hσ'
    have hgZ : constantSection (g ≫ sY) e ≫
        (pullback.fst (g ≫ sY) (relativeProjectiveLine C.S ↘ C.S) ≫ g) = g := by
      rw [← Category.assoc, constantSection_comp_fst, Category.id_comp]
    have hkerSC := ker_eq_comap_ker_of_isPullback (isPullback_sectionComparison f g sY e)
    rw [← constantSection_comp_familyProductIso, hker] at hkerSC
    replace hkerSC := hkerSC.trans (Stacks.Divisors.zeroScheme_pullback _ _ _).symm
    refine ⟨isoSubschemeOfKer _ _ hkerSC, ?_, isoSubschemeOfKer_hom_subschemeι _ _ hkerSC,
      hkerSC, ?_⟩
    · rw [← Category.assoc, isoSubschemeOfKer_hom_subschemeι, constantSection_comp_familyProductIso,
        sectionComparison_comp_fst_assoc]
    · refine hcond L s htriv _ hker g hgZ _ ?_ _
        (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ (k - p))
      rw [isoSubschemeOfKer_hom_subschemeι, constantSection_comp_familyProductIso]
      refine pullback.hom_ext ?_ ?_
      · rw [sectionComparison_comp_fst, pullback.lift_fst, Category.comp_id]
      · rw [sectionComparison_comp_snd, pullback.lift_snd]
  obtain ⟨e₀, hb₀, he₀, hkerSC₀, hx₀⟩ := key (zeroSection (g ≫ sY))
    (zeroSection (pullback.fst f g ≫ f ≫ sY)) integralZeroSection rfl rfl _ _
    (isTrivial_zeroScheme_ker_zeroSection (g ≫ sY)) (ker_zeroSection_eq_zeroScheme (g ≫ sY))
    (zeroSection_comp_familyStructureMorphism (g ≫ sY))
  obtain ⟨eI, hbI, heI, hkerSCI, hxI⟩ := key (infinitySection (g ≫ sY))
    (infinitySection (pullback.fst f g ≫ f ≫ sY)) integralInfinitySection rfl rfl _ _
    (isTrivial_zeroScheme_ker_infinitySection (g ≫ sY))
    (ker_infinitySection_eq_zeroScheme (g ≫ sY))
    (infinitySection_comp_familyStructureMorphism (g ≫ sY))
  exact eq_of_chowPushforwardOfIso_mk_gysinCycleMap_sections C (pullback.fst f g ≫ f ≫ sY)
    (pullback.fst f (pullback.fst (g ≫ sY) (relativeProjectiveLine C.S ↘ C.S) ≫ g) ≫ f ≫ sY)
    (k - p) (familyProductIso f g sY) hΦ _ _
    (Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections _ _ _
      (isTrivial_zeroScheme_ker_zeroSection (g ≫ sY)))
    hkerSC₀ e₀ he₀ hb₀ _ _
    (Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections _ _ _
      (isTrivial_zeroScheme_ker_infinitySection (g ≫ sY)))
    hkerSCI eI heI hbI δ _ _ hx₀ hxI

/-- **Condition (3) of a Gysin system applied at both sections of the family of projective
lines.** For a cycle `β` on `Y' ×_S 𝐏¹_S`, the two values of `c ∩ -` on the two section Gysin
images of `β` agree in `A_{k-p}(X')`. -/
theorem cap_gysinCycleMapAlong_zeroSection_eq_infinitySection (C : ChowSituation.{u})
    (G : GysinSystem C) (hG : G.OnChowEqGysinCycleMap) {X Y : Scheme.{u}} (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] (p : ℤ)
    (c : VeryWeakCapRule C (f ≫ sY) sY f rfl p) (hc : c.IsGysinNaturalOnCycles G)
    {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ)
    (β : CycleGroup C (familyStructureMorphism (g ≫ sY)) (k + 1)) :
    c.cap g k (gysinCycleMapAlong C (familyStructureMorphism (g ≫ sY)) (g ≫ sY) k
        (Stacks.Divisors.divisorSheaf (zeroSection (g ≫ sY)).ker)
        (Stacks.Divisors.divisorSheafGlobalSection (zeroSection (g ≫ sY)).ker)
        (zeroSection (g ≫ sY)) (isTrivial_zeroScheme_ker_zeroSection (g ≫ sY))
        (zeroSection_comp_familyStructureMorphism (g ≫ sY))
        (ker_zeroSection_eq_zeroScheme (g ≫ sY)) β) =
      c.cap g k (gysinCycleMapAlong C (familyStructureMorphism (g ≫ sY)) (g ≫ sY) k
        (Stacks.Divisors.divisorSheaf (infinitySection (g ≫ sY)).ker)
        (Stacks.Divisors.divisorSheafGlobalSection (infinitySection (g ≫ sY)).ker)
        (infinitySection (g ≫ sY)) (isTrivial_zeroScheme_ker_infinitySection (g ≫ sY))
        (infinitySection_comp_familyStructureMorphism (g ≫ sY))
        (ker_infinitySection_eq_zeroScheme (g ≫ sY)) β) :=
  cap_gysinCycleMapAlong_zeroSection_eq_infinitySection_of_isCycleGysinNatural C sY f p c
    (VeryWeakCapRule.isCycleGysinNatural_of_isGysinNaturalOnCycles G c hc hG) g k β

/-! ### Stacks 0B7A -/

/-- **Stacks 0B7A, the very weak form of Fulton's Theorem 17.1.** Let `(S, δ)` be as in
Situation 02QL, let `f : X ⟶ Y` be a morphism of schemes locally of finite type over `S` and let
`p ∈ ℤ`. A rule assigning to every locally of finite type `g : Y' ⟶ Y` and every `k` a map

  `c ∩ - : Z_k(Y') ⟶ A_{k-p}(X')`,   `X' = Y' ×_Y X`,

which satisfies condition (3) of Definition 0B76 whenever the invertible module restricts
trivially to the divisor, factors through rational equivalence: it kills every cycle rationally
equivalent to zero.

A cycle `α` rationally equivalent to zero is the total fibre difference of a locally finite
family of integral closed subschemes of `Y' ×_S 𝐏¹_S` (Stacks 02S4 part (4)); so `α` is the
difference of the two section Gysin images of the cycle `β` that family presents
(`Stacks.Chow.sub_gysinCycleMapAlong_sections_eq_of_familyFibreDifference`), and the two
sections are effective Cartier divisors with trivial normal bundle, so condition (3) applies at
both and gives the same value
(`Stacks.Chow.cap_gysinCycleMapAlong_zeroSection_eq_infinitySection_of_isCycleGysinNatural`). -/
@[stacks 0B7A]
theorem VeryWeakCapRule.cap_eq_zero_of_isCycleGysinNatural (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f]
    (hf : f ≫ sY = sX) (p : ℤ) (c : VeryWeakCapRule C sX sY f hf p)
    (hc : c.IsCycleGysinNatural) {T : Scheme.{u}}
    (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ) (α : CycleGroup C (g ≫ sY) k)
    (hα : α ∈ rationalEquivalences C (g ≫ sY) k) :
    c.cap g k α = 0 := by
  subst hf
  obtain ⟨J, W, hInt, hDimGen, hn0, hni, hLoc, hcoeff⟩ :=
    exists_familyFibreDifferences C (g ≫ sY) k α hα
  have hDim : ∀ j, schemeDeltaDimension C
      ((W j).subschemeι ≫ familyStructureMorphism (g ≫ sY)) = ((k + 1 : ℤ) : EInt) := by
    intro j
    have _ := hInt j
    exact schemeDeltaDimension_of_relativeDimension_genericPoints C _ (k + 1) (hDimGen j)
  obtain ⟨β, hβ⟩ := exists_integralFamilyCycle C (familyStructureMorphism (g ≫ sY)) (k + 1) W
    hLoc fun _ ↦ (1 : ℤ)
  rw [← sub_gysinCycleMapAlong_sections_eq_of_familyFibreDifference C (g ≫ sY) k W hInt hDim
      hn0 hni hLoc β hβ α hcoeff, map_sub, sub_eq_zero]
  exact cap_gysinCycleMapAlong_zeroSection_eq_infinitySection_of_isCycleGysinNatural C sY f p c
    hc g k β

/-- **Stacks 0B7A.** The operation `c ∩ -` of a very weak cap rule satisfying condition (3) read
on cycles, descended to Chow groups: `A_k(Y') ⟶ A_{k-p}(X')`. -/
@[stacks 0B7A "the operation descended to Chow groups"]
def VeryWeakCapRule.capChowOfCycleGysin (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX) (p : ℤ)
    (c : VeryWeakCapRule C sX sY f hf p) (hc : c.IsCycleGysinNatural) {T : Scheme.{u}}
    (g : T ⟶ Y) [LocallyOfFiniteType g]
    (k : ℤ) : chowGroup C (g ≫ sY) k →+ chowGroup C (pullback.fst f g ≫ sX) (k - p) :=
  QuotientAddGroup.lift (rationalEquivalences C (g ≫ sY) k) (c.cap g k) fun α hα ↦
    VeryWeakCapRule.cap_eq_zero_of_isCycleGysinNatural C sX sY f hf p c hc g k α hα

/-- **Stacks 0B7A.** The descended operation agrees with `c ∩ -` on cycle representatives. -/
@[simp]
theorem VeryWeakCapRule.capChowOfCycleGysin_mk (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX) (p : ℤ)
    (c : VeryWeakCapRule C sX sY f hf p) (hc : c.IsCycleGysinNatural) {T : Scheme.{u}}
    (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ) (α : CycleGroup C (g ≫ sY) k) :
    VeryWeakCapRule.capChowOfCycleGysin C sX sY f hf p c hc g k
        (QuotientAddGroup.mk' (rationalEquivalences C (g ≫ sY) k) α) = c.cap g k α :=
  rfl

/-- A very weak cap rule satisfying condition (3) in the form of
`Stacks.Chow.VeryWeakCapRule.IsGysinNaturalOnCycles` kills every cycle rationally equivalent to
zero, given the comparison `Stacks.Chow.GysinSystem.OnChowEqGysinCycleMap` between the Gysin map
on Chow groups and the one on cycles. The tag sits on
`Stacks.Chow.VeryWeakCapRule.cap_eq_zero_of_isCycleGysinNatural`, which needs no comparison. -/
theorem VeryWeakCapRule.cap_eq_zero_of_mem_rationalEquivalences (C : ChowSituation.{u})
    (G : GysinSystem C) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f]
    (hf : f ≫ sY = sX) (p : ℤ) (c : VeryWeakCapRule C sX sY f hf p)
    (hc : c.IsGysinNaturalOnCycles G) (hG : G.OnChowEqGysinCycleMap) {T : Scheme.{u}}
    (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ) (α : CycleGroup C (g ≫ sY) k)
    (hα : α ∈ rationalEquivalences C (g ≫ sY) k) :
    c.cap g k α = 0 :=
  VeryWeakCapRule.cap_eq_zero_of_isCycleGysinNatural C sX sY f hf p c
    (VeryWeakCapRule.isCycleGysinNatural_of_isGysinNaturalOnCycles G c hc hG) g k α hα

/-- The operation `c ∩ -` of a very weak cap rule whose condition (3) is stated against a Gysin
system, descended to Chow groups: `A_k(Y') ⟶ A_{k-p}(X')`. The descent carrying the tag is
`Stacks.Chow.VeryWeakCapRule.capChowOfCycleGysin`, which needs no comparison. -/
def VeryWeakCapRule.capChow (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX) (p : ℤ)
    (c : VeryWeakCapRule C sX sY f hf p) (hc : c.IsGysinNaturalOnCycles G)
    (hG : G.OnChowEqGysinCycleMap) {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g]
    (k : ℤ) : chowGroup C (g ≫ sY) k →+ chowGroup C (pullback.fst f g ≫ sX) (k - p) :=
  QuotientAddGroup.lift (rationalEquivalences C (g ≫ sY) k) (c.cap g k) fun α hα ↦
    VeryWeakCapRule.cap_eq_zero_of_mem_rationalEquivalences C G sX sY f hf p c hc hG g k α hα

/-- **Stacks 0B7A.** The descended operation agrees with `c ∩ -` on cycle representatives. -/
@[simp]
theorem VeryWeakCapRule.capChow_mk (C : ChowSituation.{u}) (G : GysinSystem C)
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX) (p : ℤ)
    (c : VeryWeakCapRule C sX sY f hf p) (hc : c.IsGysinNaturalOnCycles G)
    (hG : G.OnChowEqGysinCycleMap) {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g]
    (k : ℤ) (α : CycleGroup C (g ≫ sY) k) :
    VeryWeakCapRule.capChow C G sX sY f hf p c hc hG g k
        (QuotientAddGroup.mk' (rationalEquivalences C (g ≫ sY) k) α) = c.cap g k α :=
  rfl

end Criterion

end Stacks.Chow

end
