module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DivisorOfMeromorphicSection
public import StacksFrontier.AlgebraicGeometry.Spaces.WeilDivisorClassGroup

/-!
# The Weil divisors of two meromorphic sections of one invertible module

Let `X` be a locally Noetherian integral algebraic space over `S`, let `ℒ` be an invertible
`𝒪_X`-module and let `s, s'` be nonzero meromorphic sections of `ℒ`. Their ratio `f = s/s'` is
an invertible rational function on `X`, and the two Weil divisors of Stacks 0EPU differ by the
principal Weil divisor of `f`:

`div_ℒ(s) = div_ℒ(s') + div(f)` in `Div(X)`.

This is Stacks 0EPT as the source states it, as an identity of Weil divisors.

## Main results

* `AlgebraicGeometry.Space.divisorCoefficients_eq_add_ord` is the identity read on the
  coefficient families over all prime divisors at once, which is the coefficientwise
  Stacks 0EPT, `AlgebraicGeometry.Space.orderOfVanishingSection_eq_add_ord`, taken at every
  prime divisor.
* `AlgebraicGeometry.Space.ord_mem_weilDivisor_of_ratio_eq` is the observation the source's
  proof makes: `div(f)` is a Weil divisor because it is the difference of the two Weil divisors
  `div_ℒ(s)` and `div_ℒ(s')`, whose local finiteness is Stacks 0EPS.
* `AlgebraicGeometry.Space.divisorOfSection_eq_add_principalDivisor` is **Stacks 0EPT** as an
  identity in `Div(X)`.

## Implementation notes

The ratio `s/s'` of the source is not constructed: as in Stacks 0EPR and 0EPT, the
ratio `s / s_ξ` of a meromorphic section against a generator of `ℒ` at the generic point of a
prime divisor is the parameter `ratio`, because the morphism `c_ξ : Spec(𝒪^h_{X, ξ}) → X` along
which the source pulls back a meromorphic section is not available. Accordingly the first
assertion of the source, that `f = s/s'` lies in `R(X)^*`, appears here as the data of an
element `f` of `R(X)^*` together with the hypothesis `hs` that the ratio of `s` is `f` times
the ratio of `s'` at the generic point of every prime divisor; this is the same reading of that
assertion as the field `exists_ratio_eq_of_iso` of
`AlgebraicGeometry.Space.PicardDivisorData`. Both sections are read through one and the same
ratio family, as the source reads both through one generator `s_ξ`.

Nothing about the local finiteness of `div(f)` is assumed at `f = s/s'`:
`AlgebraicGeometry.Space.ord_mem_weilDivisor_of_ratio_eq` derives it from the local finiteness
of `div_ℒ(s)` and of `div_ℒ(s')`, which is Stacks 0EPS, exactly as the source's proof derives
it. The hypothesis `hlf` of
`AlgebraicGeometry.Space.divisorOfSection_eq_add_principalDivisor` is not an assumption about
`f`: it is the standing stand-in for Stacks 0ENN under which this library builds the object
`div(f)` of Stacks 0ENP at all, carried by
`AlgebraicGeometry.Space.GenericFractionEmbedding.principalDivisor` itself and by the form of
Stacks 0ENQ stated in `Div(X)`, and the Weil divisor `div(f)` does not depend on it.

The source states `ord_{Z,ℒ}(s)` and `div_ℒ(s)` for an invertible `ℒ`; invertibility is never
used, here as in Stacks 0EPR, 0EPT and 0EPU, so the statement is for an arbitrary
`𝒪_X`-module.

## References

* [Stacks Project, Tag 0ENP](https://stacks.math.columbia.edu/tag/0ENP)
* [Stacks Project, Tag 0EPS](https://stacks.math.columbia.edu/tag/0EPS)
* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
* [Stacks Project, Tag 0EPU](https://stacks.math.columbia.edu/tag/0EPU)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u z

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
variable (hdec : IsDecentSpace B S hS X)
variable [∀ W : PrimeDivisor B S hS X,
    Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hdec)]
variable [∀ W : PrimeDivisor B S hS X,
    IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hdec)]
variable [∀ W : PrimeDivisor B S hS X,
    Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hdec)]
variable (E : GenericFractionEmbedding B S hS hX hdec)

/-- **Stacks 0EPT, on coefficient families.** If the ratios of `s` and of `s'` at the generic
point of every prime divisor differ by the image of an invertible rational function `f`, then
the coefficient families of `div_ℒ(s)` and of `div_ℒ(s')` differ by that of `div(f)`.

This is the coefficientwise Stacks 0EPT,
`AlgebraicGeometry.Space.orderOfVanishingSection_eq_add_ord`, read at every prime divisor at
once. -/
theorem divisorCoefficients_eq_add_ord (L : Modules.{u, max u z} B S hS X hX)
    (s s' : MeromorphicSection.{u, z} B S hS X hX L)
    (ratio : LocalRatioFamily.{u, z} B S hS hX hdec L)
    (f : (rationalFunctions B S hS hX)ˣ)
    (hs : ∀ W : PrimeDivisor B S hS X,
      (ratio W s : W.genericTotalFractionRing B S hS hX hdec) =
        E.emb W (f : rationalFunctions B S hS hX) *
          (ratio W s' : W.genericTotalFractionRing B S hS hX hdec)) :
    divisorCoefficients.{u, z} B S hS hX hdec L s ratio =
      divisorCoefficients.{u, z} B S hS hX hdec L s' ratio + E.ord f :=
  funext fun W => orderOfVanishingSection_eq_add_ord.{u, z} B S hS hX hdec W L s s' (ratio W)
    (E.emb W) (f : rationalFunctions B S hS hX) (f.isUnit.map (E.emb W)) (hs W)

/-- The coefficient family `Z ↦ ord_Z(f)` of the ratio `f = s/s'` of two meromorphic sections
of `ℒ` is a Weil divisor, being the difference of the Weil divisors `div_ℒ(s)` and
`div_ℒ(s')`.

This is the remark of the source's proof that Stacks 0EPS, which makes the two sums `div_ℒ(s)`
and `div_ℒ(s')` Weil divisors, makes `div(f)` one as well. -/
theorem ord_mem_weilDivisor_of_ratio_eq (L : Modules.{u, max u z} B S hS X hX)
    (s s' : MeromorphicSection.{u, z} B S hS X hX L)
    (ratio : LocalRatioFamily.{u, z} B S hS hX hdec L)
    (f : (rationalFunctions B S hS hX)ˣ)
    (hfin : LocallyFinite fun W : PrimeDivisor B S hS X ↦
      if divisorCoefficients.{u, z} B S hS hX hdec L s ratio W = 0 then ∅
      else W.support B S hS X)
    (hfin' : LocallyFinite fun W : PrimeDivisor B S hS X ↦
      if divisorCoefficients.{u, z} B S hS hX hdec L s' ratio W = 0 then ∅
      else W.support B S hS X)
    (hs : ∀ W : PrimeDivisor B S hS X,
      (ratio W s : W.genericTotalFractionRing B S hS hX hdec) =
        E.emb W (f : rationalFunctions B S hS hX) *
          (ratio W s' : W.genericTotalFractionRing B S hS hX hdec)) :
    E.ord f ∈ WeilDivisor B S hS X := by
  have hdiff : E.ord f = divisorCoefficients.{u, z} B S hS hX hdec L s ratio -
      divisorCoefficients.{u, z} B S hS hX hdec L s' ratio :=
    eq_sub_of_add_eq'
      (divisorCoefficients_eq_add_ord.{u, z} B S hS hX hdec E L s s' ratio f hs).symm
  rw [hdiff]
  exact sub_mem ((mem_weilDivisor_iff B S hS X _).2 hfin)
    ((mem_weilDivisor_iff B S hS X _).2 hfin')

/-- **Stacks 0EPT.** If `s` and `s'` are nonzero meromorphic sections of `ℒ` whose ratios at
the generic point of every prime divisor differ by the invertible rational function
`f = s/s' ∈ R(X)^*`, then their Weil divisors of Stacks 0EPU differ by the principal Weil
divisor of `f`:

`∑ ord_{Z,ℒ}(s) [Z] = ∑ ord_{Z,ℒ}(s') [Z] + div(f)`

as an identity in the group `Div(X)` of Weil divisors on `X`. Coefficientwise at a single prime
divisor this is
`AlgebraicGeometry.Space.orderOfVanishingSection_eq_add_ord`, of which this statement is the
sum over all prime divisors; that `div(f)` is itself a Weil divisor is what Stacks 0EPS gives
in the source, and is here the hypothesis `hlf`, which
`AlgebraicGeometry.Space.ord_mem_weilDivisor_of_ratio_eq` discharges from the local finiteness
of the two divisors. -/
@[stacks 0EPT "the identity in Div(X); the coefficientwise form is
  orderOfVanishingSection_eq_add_ord"]
theorem divisorOfSection_eq_add_principalDivisor
    (hlf : ∀ g : (rationalFunctions B S hS hX)ˣ, E.ord g ∈ WeilDivisor B S hS X)
    (L : Modules.{u, max u z} B S hS X hX)
    (s s' : MeromorphicSection.{u, z} B S hS X hX L)
    (ratio : LocalRatioFamily.{u, z} B S hS hX hdec L)
    (f : (rationalFunctions B S hS hX)ˣ)
    (hfin : LocallyFinite fun W : PrimeDivisor B S hS X ↦
      if divisorCoefficients.{u, z} B S hS hX hdec L s ratio W = 0 then ∅
      else W.support B S hS X)
    (hfin' : LocallyFinite fun W : PrimeDivisor B S hS X ↦
      if divisorCoefficients.{u, z} B S hS hX hdec L s' ratio W = 0 then ∅
      else W.support B S hS X)
    (hs : ∀ W : PrimeDivisor B S hS X,
      (ratio W s : W.genericTotalFractionRing B S hS hX hdec) =
        E.emb W (f : rationalFunctions B S hS hX) *
          (ratio W s' : W.genericTotalFractionRing B S hS hX hdec)) :
    divisorOfSection.{u, z} B S hS hX hdec L s ratio hfin =
      divisorOfSection.{u, z} B S hS hX hdec L s' ratio hfin' + E.principalDivisor hlf f :=
  Subtype.ext (divisorCoefficients_eq_add_ord.{u, z} B S hS hX hdec E L s s' ratio f hs)

end AlgebraicGeometry.Space

end
