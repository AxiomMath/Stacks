module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.ZeroSectionCartier
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.GysinComponentDischarge
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceFiniteType
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.ZeroSectionZeroScheme

/-!
# The Gysin map of the zero section of a line bundle

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `ℒ` be an invertible `𝒪_X`-module and let

  `p : L = \underline{\Spec}(\Sym^*(ℒ)) ⟶ X`

be the associated line bundle, with zero section `o : X ⟶ L`. Clause (3) of [Stacks, Tag 0F96]
asserts that there is a Gysin map

  `o^* : \CH_{k + 1}(L) ⟶ \CH_k(X)`,

"as `o(X)` is an effective Cartier divisor". This file constructs it.

## The two steps

The Gysin map of [Stacks, Tag 02TO] attached to the zero scheme `Z(s)` of a global section `s`
of an invertible module on `L` is `Stacks.Chow.gysinChowOfInvertible`, a homomorphism

  `\CH_{k + 1}(L) ⟶ \CH_k(Z(s))`,

available with no hypothesis. Clause (1) of the same tag presents `o(X)` as such a zero scheme:
`Stacks.LineBundle.Situation.zeroScheme_tautologicalSectionBase_eq_ker_zeroSection` identifies
it with the zero scheme of the tautological section of `p^*(ℒ^{⊗ -1})`, and that section is
regular, so the subscheme is an effective Cartier divisor — the clause's own justification. So
the first step lands in `\CH_k(o(X))` rather than in `\CH_k(X)`.

The second step is the identification of `o(X)` with `X`. The structure morphism of `o(X)` over
`X` is an isomorphism, `o` being a closed immersion splitting `p`
(`Stacks.LineBundle.Situation.isIso_ker_zeroSection_subschemeι_comp_totalSpaceToBase`), and
proper pushforward along an isomorphism over the base is an isomorphism of Chow groups with no
instance of [Stacks, Tag 02S2] needed: `Stacks.Chow.chowPushforwardOfIso`, with inverse
`Stacks.Chow.chowGroupEquivOfIso`, and functorial by `Stacks.Chow.chowPushforwardOfIso_id` and
`Stacks.Chow.chowPushforwardOfIso_comp_apply`. Composing the two steps gives `o^*`.

## Main definitions

* `Stacks.Chow.gysinChowOfInvertibleTransported` — the Gysin map of [Stacks, Tag 02TO] read on a
  scheme isomorphic to the zero scheme over the base: given an isomorphism `e : Z(s) ≅ Y` with
  `e` compatible with the structure morphisms, a homomorphism `\CH_{k + 1}(X) ⟶ \CH_k(Y)`. The
  isomorphism and its compatibility are arguments rather than a fixed pair, which keeps the
  transport off any concrete equality of schemes.
* `Stacks.Chow.zeroSectionGysinChow` — **clause (3) of [Stacks, Tag 0F96]**: the Gysin map
  `o^* : \CH_{k + 1}(L) ⟶ \CH_k(X)` of the zero section of a line bundle.

## Main results

* `Stacks.LineBundle.Situation.isIso_zeroScheme_tautologicalSectionBase_subschemeι_comp` — the
  structure morphism of the zero scheme of the tautological section over `X` is an isomorphism;
  this is the clause-(1) presentation of `o(X)` fed into
  `Stacks.LineBundle.Situation.isIso_ker_zeroSection_subschemeι_comp_totalSpaceToBase`.
* `Stacks.LineBundle.Situation.zeroSectionDivisorIso` — that isomorphism `o(X) ≅ X`, packaged.
* `Stacks.Chow.zeroSectionGysinChow_mk` — on the class of a cycle, `o^*` is the class of the
  pushforward along `o(X) ≅ X` of the Gysin cycle of [Stacks, Tag 02T8].

## The effective Cartier divisor the clause names

`Stacks.Chow.gysinChowOfInvertible` is unconditional in this repository — [Stacks, Tag 02TO] is
proved for the zero scheme of an arbitrary global section of an invertible module, as
`Stacks.Chow.gysinOfInvertibleFactorsThroughRationalEquivalence` — so the construction below
takes no effective-Cartier hypothesis. That is not a weakening of the clause: the divisor really
is an effective Cartier divisor, by
`Stacks.LineBundle.Situation.isEffectiveCartierDivisor_ker_zeroSection`, and in the relative
sense of [Stacks, Tag 062T] as well, by
`Stacks.LineBundle.Situation.isRelativeEffectiveCartierDivisor_zeroScheme_tautologicalSectionBase`;
the clause's justification is simply available for free here rather than assumed.

The hypotheses of [Stacks, Tag 0B74] on the line bundle — that `p` be flat of relative dimension
one — are likewise not needed and not taken: the Gysin map of a divisor does not refer to them.
Only the hypothesis that `X` be locally of finite type over `S` is taken, and that is what makes
the two Chow groups exist.

## References

* [Stacks Project, Tag 0F96](https://stacks.math.columbia.edu/tag/0F96)
* [Stacks Project, Tag 0B74](https://stacks.math.columbia.edu/tag/0B74)
* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 062T](https://stacks.math.columbia.edu/tag/062T)
* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

/-! ### The zero scheme of the tautological section is isomorphic to the base -/

namespace Stacks.LineBundle

variable (D : Situation.{u})

/-- **The structure morphism of the zero scheme of the tautological section over the base of the
line bundle is an isomorphism.** By clause (1) of [Stacks, Tag 0F96] that zero scheme is the
image `o(X)` of the zero section, whose structure morphism over `X` is an isomorphism because
`o` is a closed immersion splitting `p`. -/
theorem Situation.isIso_zeroScheme_tautologicalSectionBase_subschemeι_comp :
    IsIso ((Stacks.Divisors.zeroScheme D.totalSpace D.basePullbackInverse
      D.tautologicalSectionBase).subschemeι ≫ D.totalSpaceToBase) := by
  rw [D.zeroScheme_tautologicalSectionBase_eq_ker_zeroSection]
  exact D.isIso_ker_zeroSection_subschemeι_comp_totalSpaceToBase

/-- **The image of the zero section is isomorphic to the base**, presented as a zero scheme the
way clause (1) of [Stacks, Tag 0F96] presents it. The forward map is the structure morphism
`o(X) ⟶ X` itself, which is what makes the compatibility with the structure morphisms over the
base situation of chapter 42 a reassociation and nothing more. -/
def Situation.zeroSectionDivisorIso :
    (Stacks.Divisors.zeroScheme D.totalSpace D.basePullbackInverse
      D.tautologicalSectionBase).subscheme ≅ D.X :=
  haveI := D.isIso_zeroScheme_tautologicalSectionBase_subschemeι_comp
  asIso ((Stacks.Divisors.zeroScheme D.totalSpace D.basePullbackInverse
    D.tautologicalSectionBase).subschemeι ≫ D.totalSpaceToBase)

/-- The forward map of `Stacks.LineBundle.Situation.zeroSectionDivisorIso` is the structure
morphism of the zero scheme of the tautological section over the base. -/
@[simp]
theorem Situation.zeroSectionDivisorIso_hom :
    D.zeroSectionDivisorIso.hom =
      (Stacks.Divisors.zeroScheme D.totalSpace D.basePullbackInverse
        D.tautologicalSectionBase).subschemeι ≫ D.totalSpaceToBase :=
  rfl

end Stacks.LineBundle

/-! ### The Gysin map of a divisor, read on a scheme isomorphic to it -/

namespace Stacks.Chow

/-- **The Gysin map of [Stacks, Tag 02TO], transported along an isomorphism of the divisor.**
Let `X` be locally of finite type over the base situation of chapter 42, let `s` be a global
section of an invertible module `L` on `X`, and let `e : Z(s) ≅ Y` be an isomorphism of the zero
scheme of `s` with a scheme `Y` over the base. Then the Gysin map
`i^* : \CH_{k + 1}(X) ⟶ \CH_k(Z(s))` composed with the pushforward along `e` is a homomorphism

  `\CH_{k + 1}(X) ⟶ \CH_k(Y)`.

Both factors are unconditional: [Stacks, Tag 02TO] is proved for an arbitrary global section of
an invertible module, and pushforward along an isomorphism over the base needs no instance of
[Stacks, Tag 02S2].

The isomorphism `e` and its compatibility `he` are arguments. They are not replaced by a concrete
pair derived from an equality of schemes on purpose: a transport written against a concrete
equality puts an `eqToHom` at that equality into the term, which the kernel then tries to reduce
through `Eq.rec`. -/
def gysinChowOfInvertibleTransported (C : ChowSituation.{u}) {X Y : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (k : ℤ) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (e : (Stacks.Divisors.zeroScheme X L s).subscheme ≅ Y)
    (he : e.hom ≫ sY = (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) :
    chowGroup C p (k + 1) →+ chowGroup C sY k :=
  (chowPushforwardOfIso C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) sY e.hom he
    k).comp (gysinChowOfInvertible C p k L s)

/-- The transported Gysin map `Stacks.Chow.gysinChowOfInvertibleTransported` sends a cycle class
`α` to the pushforward along `e` of its image under `Stacks.Chow.gysinChowOfInvertible`. -/
theorem gysinChowOfInvertibleTransported_apply (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (k : ℤ)
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (e : (Stacks.Divisors.zeroScheme X L s).subscheme ≅ Y)
    (he : e.hom ≫ sY = (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
    (α : chowGroup C p (k + 1)) :
    gysinChowOfInvertibleTransported C p sY k L s e he α =
      chowPushforwardOfIso C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) sY e.hom he k
        (gysinChowOfInvertible C p k L s α) :=
  rfl

/-! ### Clause (3) of Stacks 0F96 -/

variable (C : ChowSituation.{u}) (D : Stacks.LineBundle.Situation.{u}) (sX : D.X ⟶ C.S)
  [LocallyOfFiniteType sX]

omit [LocallyOfFiniteType sX] in
/-- The isomorphism `o(X) ≅ X` of
`Stacks.LineBundle.Situation.zeroSectionDivisorIso` is compatible with the structure morphisms
over the base situation of chapter 42. Its forward map being the structure morphism of `o(X)`
over `X`, this is a reassociation. -/
theorem zeroSectionDivisorIso_hom_comp :
    D.zeroSectionDivisorIso.hom ≫ sX =
      (Stacks.Divisors.zeroScheme D.totalSpace D.basePullbackInverse
        D.tautologicalSectionBase).subschemeι ≫ D.totalSpaceToBase ≫ sX :=
  Category.assoc _ _ _

/-- **Stacks 0F96, clause (3).** The image `o(X)` of the zero section of a line bundle
`p : L ⟶ X` is an effective Cartier divisor on `L`, so it has a Gysin map; composed with the
identification of `o(X)` with `X` it is

  `o^* : \CH_{k + 1}(L) ⟶ \CH_k(X)`.

The divisor is presented as clause (1) presents it, the zero scheme of the tautological global
section of `p^*(ℒ^{⊗ -1})`, and the Gysin map of a zero scheme is the unconditional
[Stacks, Tag 02TO] on Chow groups. That the divisor is an effective Cartier divisor — the
clause's justification — is
`Stacks.LineBundle.Situation.isRelativeEffectiveCartierDivisor_zeroScheme_tautologicalSectionBase`;
it is a theorem here and so is not taken as a hypothesis. -/
@[stacks 0F96 "part (3)"]
def zeroSectionGysinChow (k : ℤ) :
    chowGroup C (D.totalSpaceToBase ≫ sX) (k + 1) →+ chowGroup C sX k :=
  gysinChowOfInvertibleTransported C (D.totalSpaceToBase ≫ sX) sX k D.basePullbackInverse
    D.tautologicalSectionBase D.zeroSectionDivisorIso (zeroSectionDivisorIso_hom_comp C D sX)

/-- On the class of a cycle, the Gysin map of the zero section is the class of the pushforward
along `o(X) ≅ X` of the Gysin cycle of [Stacks, Tag 02T8]. -/
theorem zeroSectionGysinChow_mk (k : ℤ)
    (α : CycleGroup C (D.totalSpaceToBase ≫ sX) (k + 1)) :
    zeroSectionGysinChow C D sX k
        (QuotientAddGroup.mk' (rationalEquivalences C (D.totalSpaceToBase ≫ sX) (k + 1)) α) =
      chowPushforwardOfIso C
        ((Stacks.Divisors.zeroScheme D.totalSpace D.basePullbackInverse
          D.tautologicalSectionBase).subschemeι ≫ D.totalSpaceToBase ≫ sX) sX
        D.zeroSectionDivisorIso.hom (zeroSectionDivisorIso_hom_comp C D sX) k
        (gysinHomomorphismOfInvertible C (D.totalSpaceToBase ≫ sX) k D.basePullbackInverse
          D.tautologicalSectionBase α) :=
  rfl

end Stacks.Chow

end
