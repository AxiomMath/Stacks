module

public import StacksFrontier.AlgebraicGeometry.Spaces.PicardWeilDivisorClass

/-!
# The Weil divisor class of an invertible module, from one meromorphic section

Let `X` be a locally Noetherian integral algebraic space over `S` and let `ℒ` be an invertible
`𝒪_X`-module. A nonzero meromorphic section `s` of `ℒ` has a Weil divisor
`div_ℒ(s) = ∑_Z ord_{Z,ℒ}(s) [Z] ∈ Div(X)`, which is part (1) of Stacks 0EPU and is
`AlgebraicGeometry.Space.divisorOfSection`. Part (2) of Stacks 0EPU is the *Weil divisor class
of `ℒ`*: the image of `div_ℒ(s)` in the Weil divisor class group `Cl(X)`, for `s` any nonzero
meromorphic section of `ℒ`. It is well defined because two nonzero meromorphic sections of `ℒ`
have Weil divisors differing by the principal divisor of their ratio, which is Stacks 0EPT, and
a principal divisor is zero in `Cl(X)`.

## Main definitions

* `AlgebraicGeometry.Space.divisorClassOfSection` is **Stacks 0EPU, part (2)**: the class of
  `div_ℒ(s)` in `Cl(X)`.
* `AlgebraicGeometry.Space.divisorClassOfSectionOfGenerating` is the same with the local
  finiteness that makes `div_ℒ(s)` a Weil divisor supplied by Stacks 0EPS from a nonempty open
  subspace over which `s` generates `ℒ`.

## Main results

* `AlgebraicGeometry.Space.divisorClassOfSection_eq` is the well-definedness of Stacks 0EPU,
  part (2): the class in `Cl(X)` does not depend on the chosen nonzero meromorphic section.
  This is the use the source makes of Stacks 0EPT.
* `AlgebraicGeometry.Space.PicardDivisorData.divisorClass_eq_divisorClassOfSection`: the Weil
  divisor class that the construction of Stacks 0EPW assigns to an invertible `𝒪_X`-module is
  the one defined here, taken at that construction's chosen section. The bundled
  `AlgebraicGeometry.Space.PicardDivisorData.divisorClass` is therefore not a second notion of
  Weil divisor class but this one specialized, and the two cannot drift apart.

## Implementation notes

The target `Cl(X)` is `AlgebraicGeometry.Space.GenericFractionEmbedding.weilDivisorClassGroup`
of Stacks 0ENR, stated relative to an `AlgebraicGeometry.Space.GenericFractionEmbedding`, and
the parameter `E` below is that datum, exactly as in the library's Stacks 0ENQ, 0ENR, 0EPR, 0EPS,
0EPT, 0EPU part (1), 0EPV, 0EPW and 0EPX. On the integral, locally Noetherian `X` of the source
it is inhabited by Stacks 0ENK: the canonical embedding `R(X) → Q(𝒪^h_{X,ξ})` is
`AlgebraicGeometry.Space.genericFractionEmbedding`
(`StacksFrontier/AlgebraicGeometry/Spaces/Decent/PrimeDivisorFunctionFieldEmbedding.lean`).

For the same reason — the morphism `c_ξ : Spec(𝒪^h_{X,ξ}) → X` along which the source pulls
back a meromorphic section is not available — the ratio `s / s_ξ` against a generator of `ℒ` at
the generic point of a prime divisor is the parameter `ratio` of
`AlgebraicGeometry.Space.orderOfVanishingSection` of Stacks 0EPR, and is a parameter here. That
it takes values in the *units* of `Q(𝒪^h_{X,ξ})` is regularity — nonzeroness — of the
meromorphic section, which is where the source uses it. A single ratio family is used for both
sections in `AlgebraicGeometry.Space.divisorClassOfSection_eq`, which is the single choice of
`s_ξ` the proof of Stacks 0EPT makes at each generic point.

Well-definedness is stated in the form Stacks 0EPT supplies: the hypothesis is that the two
sections have ratios differing by the image of an invertible rational function `f`, which is
the assertion `f = s/s' ∈ R(X)^*` of that lemma, and the conclusion is the equality of classes,
which is the content the source draws from `div_ℒ(s) = div_ℒ(s') + div(f)`. The principal
divisor `div(f)` of Stacks 0ENP needs the local finiteness of `ord_Z(f)` to exist as a Weil
divisor, which this development carries as a separate hypothesis; the equality of classes is
proved without it, directly from the subgroup of principal Weil divisors of Stacks 0ENR, whose
membership condition is the coefficientwise one.

The source states both parts for an invertible `ℒ`. Invertibility is never used: it enters the
source only to produce a nonzero meromorphic section of `ℒ` in the first place (Stacks 0EPQ),
and here that section is the hypothesis `s`. So, exactly as for part (1) and for
Stacks 0EPR, the definitions are stated for an arbitrary `𝒪_X`-module.

The three standing hypotheses on the henselian local rings at the generic points of the prime
divisors — nontrivial, Noetherian, of Krull dimension at most one — are the content of Stacks
0ENK and are fields of `AlgebraicGeometry.Space.GenericFractionEmbedding`; they are carried
here as instance arguments as well, as they are in the library's Stacks 0EPR, 0EPS, 0EPT, 0EPU
part (1), 0EPV and 0EPW, so that these declarations compose with those.

## References

* [Stacks Project, Tag 0EPQ](https://stacks.math.columbia.edu/tag/0EPQ)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EPS](https://stacks.math.columbia.edu/tag/0EPS)
* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
* [Stacks Project, Tag 0EPU](https://stacks.math.columbia.edu/tag/0EPU)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0ENR](https://stacks.math.columbia.edu/tag/0ENR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u z

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
variable (hdec : IsDecentSpace B S hS X)
variable (E : GenericFractionEmbedding B S hS hX hdec)
variable [∀ W : PrimeDivisor B S hS X,
  Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hdec)]
variable [∀ W : PrimeDivisor B S hS X,
  IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hdec)]
variable [∀ W : PrimeDivisor B S hS X,
  Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hdec)]

/-! ### The Weil divisor class of a meromorphic section -/

/-- **Stacks 0EPU, part (2).** The *Weil divisor class associated to `ℒ`*: the image in `Cl(X)`
of the Weil divisor `div_ℒ(s) = ∑_Z ord_{Z,ℒ}(s) [Z]` of a nonzero meromorphic section `s` of
`ℒ`.

It depends only on `ℒ` and not on `s`, which is
`AlgebraicGeometry.Space.divisorClassOfSection_eq` and is the use the source makes of Stacks
0EPT. -/
@[stacks 0EPU "part (2): the Weil divisor class of ℒ, the image of div_ℒ(s) in Cl(X); the class
  group is Stacks 0ENR, relative to the embedding R(X) → Q(𝒪^h_{X,ξ}) of Stacks 0ENK, which is
  the parameter `E` inhabited by genericFractionEmbedding, and the ratio s/s_ξ is the parameter
  `ratio` as in Stacks 0EPR and in part (1)"]
def divisorClassOfSection (L : Modules.{u, max u z} B S hS X hX)
    (s : MeromorphicSection.{u, z} B S hS X hX L)
    (ratio : LocalRatioFamily.{u, z} B S hS hX hdec L)
    (hfin : LocallyFinite fun W : PrimeDivisor B S hS X ↦
      if divisorCoefficients.{u, z} B S hS hX hdec L s ratio W = 0 then ∅
      else W.support B S hS X) :
    E.weilDivisorClassGroup :=
  QuotientAddGroup.mk (divisorOfSection.{u, z} B S hS hX hdec L s ratio hfin)

/-- **Stacks 0EPU, part (2), well-definedness.** The Weil divisor class of `ℒ` does not depend
on the chosen nonzero meromorphic section: if the ratios of `s` and of `s'` at the generic point
of every prime divisor differ by the image of an invertible rational function `f` — which is the
assertion `f = s/s' ∈ R(X)^*` of Stacks 0EPT — then `div_ℒ(s)` and `div_ℒ(s')` differ by the
principal divisor `div(f)`, hence have the same class in `Cl(X)`. -/
@[stacks 0EPU "part (2): well-definedness, the class of div_ℒ(s) in Cl(X) is independent of the
  nonzero meromorphic section s; this is the appeal to Stacks 0EPT that the source makes, whose
  conclusion div_ℒ(s) = div_ℒ(s') + div(f) is read through the coefficientwise membership
  condition of the subgroup of principal Weil divisors of Stacks 0ENR"]
theorem divisorClassOfSection_eq (L : Modules.{u, max u z} B S hS X hX)
    (s s' : MeromorphicSection.{u, z} B S hS X hX L)
    (ratio : LocalRatioFamily.{u, z} B S hS hX hdec L)
    (hfin : LocallyFinite fun W : PrimeDivisor B S hS X ↦
      if divisorCoefficients.{u, z} B S hS hX hdec L s ratio W = 0 then ∅
      else W.support B S hS X)
    (hfin' : LocallyFinite fun W : PrimeDivisor B S hS X ↦
      if divisorCoefficients.{u, z} B S hS hX hdec L s' ratio W = 0 then ∅
      else W.support B S hS X)
    (f : (rationalFunctions B S hS hX)ˣ)
    (hs : ∀ W : PrimeDivisor B S hS X,
      (ratio W s : W.genericTotalFractionRing B S hS hX hdec) =
        E.emb W (f : rationalFunctions B S hS hX) *
          (ratio W s' : W.genericTotalFractionRing B S hS hX hdec)) :
    divisorClassOfSection.{u, z} B S hS hX hdec E L s ratio hfin =
      divisorClassOfSection.{u, z} B S hS hX hdec E L s' ratio hfin' := by
  refine weilDivisorClass_eq_of_coe_sub_eq_ord B S hS hX hdec E f fun Z ↦ ?_
  have hord : E.ord f Z = Z.ord B S hS hX hdec (E.emb Z (f : rationalFunctions B S hS hX))
      (f.isUnit.map (E.emb Z)) := rfl
  rw [coe_divisorOfSection.{u, z} B S hS hX hdec Z L s ratio hfin,
    coe_divisorOfSection.{u, z} B S hS hX hdec Z L s' ratio hfin', hord,
    orderOfVanishingSection_eq_add_ord.{u, z} B S hS hX hdec Z L s s' (ratio Z) (E.emb Z)
      (f : rationalFunctions B S hS hX) (f.isUnit.map (E.emb Z)) (hs Z)]
  ring

include hX in
/-- **Stacks 0EPU, part (2).** The Weil divisor class of `ℒ`, with the local finiteness that
makes `div_ℒ(s)` a Weil divisor supplied by Stacks 0EPS from a nonempty open subset of `|X|`
containing the generic point of no prime divisor along which `s` has nonzero order — the open
subspace over which the nonzero meromorphic section `s` generates `ℒ`. -/
@[stacks 0EPU "part (2): the Weil divisor class of ℒ in Cl(X), with the local finiteness of the
  support of div_ℒ(s) supplied by Stacks 0EPS from the open subspace U over which s
  generates ℒ"]
def divisorClassOfSectionOfGenerating
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))
    (hirr : IrreducibleSpace (points B S hS X)) (L : Modules.{u, max u z} B S hS X hX)
    (s : MeromorphicSection.{u, z} B S hS X hX L)
    (ratio : LocalRatioFamily.{u, z} B S hS hX hdec L)
    (U : Set (points B S hS X)) (hUopen : IsOpen U) (hUne : U.Nonempty)
    (hgen : ∀ W : PrimeDivisor B S hS X,
      divisorCoefficients.{u, z} B S hS hX hdec L s ratio W ≠ 0 →
        W.genericPoint B S hS X ∈ Uᶜ) :
    E.weilDivisorClassGroup :=
  divisorClassOfSection.{u, z} B S hS hX hdec E L s ratio
    (locallyFinite_divisorCoefficients_ne_zero.{u, z} B S hS hX hdec hN hirr L s ratio U
      hUopen hUne hgen)

/-- The Weil divisor class of `ℒ` built from a generating open subspace is the class of
`div_ℒ(s)`. -/
theorem divisorClassOfSectionOfGenerating_eq
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))
    (hirr : IrreducibleSpace (points B S hS X)) (L : Modules.{u, max u z} B S hS X hX)
    (s : MeromorphicSection.{u, z} B S hS X hX L)
    (ratio : LocalRatioFamily.{u, z} B S hS hX hdec L)
    (U : Set (points B S hS X)) (hUopen : IsOpen U) (hUne : U.Nonempty)
    (hgen : ∀ W : PrimeDivisor B S hS X,
      divisorCoefficients.{u, z} B S hS hX hdec L s ratio W ≠ 0 →
        W.genericPoint B S hS X ∈ Uᶜ)
    (hfin : LocallyFinite fun W : PrimeDivisor B S hS X ↦
      if divisorCoefficients.{u, z} B S hS hX hdec L s ratio W = 0 then ∅
      else W.support B S hS X) :
    divisorClassOfSectionOfGenerating.{u, z} B S hS hX hdec E hN hirr L s ratio U hUopen hUne
        hgen =
      divisorClassOfSection.{u, z} B S hS hX hdec E L s ratio hfin :=
  congrArg QuotientAddGroup.mk (Subtype.ext rfl)

/-! ### Compatibility with the construction of `Pic(X) ⟶ Cl(X)` -/

/-- The Weil divisor class that the construction of Stacks 0EPW assigns to an invertible
`𝒪_X`-module is the Weil divisor class of Stacks 0EPU, part (2), taken at the regular
meromorphic section and the ratio family that construction chooses. -/
theorem PicardDivisorData.divisorClass_eq_divisorClassOfSection
    (D : PicardDivisorData B S hS hX hdec E) (L : Modules.{u, u} B S hS X hX)
    (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L) :
    D.divisorClass L hL =
      divisorClassOfSection.{u, u} B S hS hX hdec E L (D.sect L hL) (D.ratio L hL)
        (locallyFinite_divisorCoefficients_ne_zero.{u, u} B S hS hX hdec
          D.isLocallyNoetherian D.irreducibleSpace L (D.sect L hL) (D.ratio L hL)
          (D.generating L hL).choose (D.generating L hL).choose_spec.1
          (D.generating L hL).choose_spec.2.1 (D.generating L hL).choose_spec.2.2) :=
  rfl

end AlgebraicGeometry.Space

end
