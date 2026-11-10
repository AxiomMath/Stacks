module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DivisorOfMeromorphicSection
public import StacksFrontier.AlgebraicGeometry.Spaces.PicardTensorProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.WeilDivisorClassGroup

/-!
# The Weil divisor class of an invertible module on an algebraic space

Let `X` be a locally Noetherian integral algebraic space over `S`. An invertible `𝒪_X`-module
`ℒ` has a regular meromorphic section `s` (Stacks 0EPQ), and `s` has a Weil divisor
`div_ℒ(s) ∈ Div(X)` (Stacks 0EPU, part (1)). Two regular meromorphic sections of `ℒ` have Weil
divisors differing by the principal divisor of their ratio (Stacks 0EPT), so the class of
`div_ℒ(s)` in the Weil divisor class group `Cl(X)` depends only on `ℒ`, and for the same reason
only on the isomorphism class of `ℒ`. The divisor is additive under tensor product (Stacks
0EPV). Therefore `ℒ ↦ [div_ℒ(s)]` is a homomorphism of abelian groups

`Pic(X) ⟶ Cl(X)`,

which is the construction of Stacks 0EPW.

## Main definitions

* `AlgebraicGeometry.Space.PicardDivisorData` collects the standing hypotheses on `X` and the
  choices the construction makes: a regular meromorphic section of every invertible
  `𝒪_X`-module, a generator of that module at the generic point of every prime divisor read as
  the ratio family of Stacks 0EPR, the open subspace over which the section generates the
  module, and the two divisor identities which are the content of Stacks 0EPT and of Stacks
  0EPV.
* `AlgebraicGeometry.Space.PicardDivisorData.divisor` is `div_ℒ(s)` for the chosen section and
  `AlgebraicGeometry.Space.PicardDivisorData.divisorClass` is its class in `Cl(X)`.
* `AlgebraicGeometry.Space.PicardDivisorData.picardToWeilDivisorClassGroup` is the homomorphism
  `Pic(X) ⟶ Cl(X)` of Stacks 0EPW.

## Main results

* `AlgebraicGeometry.Space.orderOfVanishingSection_eq_add_ord_of_ratio_eq`: two meromorphic
  sections whose ratios at the generic point of a prime divisor `Z` differ by an invertible
  rational function `f` have orders of vanishing along `Z` differing by `ord_Z(f)`. This is
  Stacks 0EPT with the two sections allowed to be sections of different modules.
* `AlgebraicGeometry.Space.exists_ord_sub_eq_of_ratio_mul`: a meromorphic section whose ratio at
  the generic point of every prime divisor is the product of the ratios of two others has for
  its Weil divisor the sum of their Weil divisors, which is the field
  `exists_ord_sub_eq_tensorModule` below with `f = 1`. This is Stacks 0EPV with the three
  sections allowed to be sections of three unrelated modules.
* `AlgebraicGeometry.Space.PicardDivisorData.divisorClass_congr`: isomorphic invertible modules
  have the same Weil divisor class.
* `AlgebraicGeometry.Space.PicardDivisorData.divisorClass_picardTensorModule`: the Weil
  divisor class
  is additive under tensor product.
* `AlgebraicGeometry.Space.PicardDivisorData.picardToWeilDivisorClassGroup_picardClass`: the
  homomorphism of Stacks 0EPW sends the class of an invertible module to its Weil divisor
  class, which characterizes it.
* `AlgebraicGeometry.Space.PicardDivisorData.injective_picardToWeilDivisorClassGroup`: the
  homomorphism of Stacks 0EPW is injective on a normal `X`. This is Stacks 0EPX, with the
  claim of that lemma — a regular meromorphic section with vanishing Weil divisor trivializes
  the module — and the rescaling of a regular meromorphic section by an invertible rational
  function as explicit hypotheses.

## Implementation notes

The target `Cl(X)` is `AlgebraicGeometry.Space.GenericFractionEmbedding.weilDivisorClassGroup`
of Stacks 0ENR, which is stated relative to an
`AlgebraicGeometry.Space.GenericFractionEmbedding`, and the parameter `E` below is that datum,
as in Stacks 0ENQ, 0ENR, 0EPR, 0EPS, 0EPT, 0EPU and 0EPV. On the integral, locally
Noetherian `X` of Stacks 0EPW the datum is canonical: the embedding `R(X) → Q(𝒪^h_{X, ξ})` of
Stacks 0ENK is `AlgebraicGeometry.Space.genericFractionEmbedding`, which such an `X` carries.
A regular meromorphic section of every invertible `𝒪_X`-module, the field `sect` below, is
likewise available on such an `X`, as `AlgebraicGeometry.Space.regularMeromorphicSection`
(`StacksFrontier/AlgebraicGeometry/Spaces/PicardWeilDivisorClassIntegral.lean`), and the ratio
family `ratio` as `AlgebraicGeometry.Space.canonicalLocalRatioFamily`
(`StacksFrontier/AlgebraicGeometry/Spaces/Decent/PrimeDivisorCanonicalRatio.lean`).

The two identities those choices satisfy are the fields `exists_ord_sub_eq_of_iso` and
`exists_ord_sub_eq_tensorModule`, which are Stacks 0EPT and Stacks 0EPV in the form this
construction uses. Every consequence drawn from them here — that the class in `Cl(X)` is well
defined on isomorphism classes, that it is additive, and that the two assemble into a group
homomorphism — is proved.

Both fields compare the *Weil divisors* rather than the ratios, and that is not a convenience.
The ratio of a section is taken against a generator chosen at each generic point, independently
for each module, so a trivialisation of `ℒ` and one of `𝒩` at the same point differ by a unit
of the local ring that no construction pins down; a statement relating the two ratios by one
global rational function is therefore not derivable, while the statement about the difference of
the coefficients is, the stray unit having order of vanishing zero
(`AlgebraicGeometry.Space.PrimeDivisor.orderOfVanishingSection_canonicalLocalRatio_eq`). For the
tensor product there is a second reason: the chosen section of `ℒ ⊗ 𝒩` is a section of that
module alone, with no relation to the sections chosen for `ℒ` and for `𝒩`, and two regular
meromorphic sections of one module differ by an element of `R(X)^*` whose divisor is in general
nonzero — so only the *class* of the divisor of a tensor product is additive, which is
`divisorClass_picardTensorModule` and is all that `picardToWeilDivisorClassGroup` uses.

The first assertion of Stacks 0EPT — that the ratio of two regular meromorphic sections of an
invertible `𝒪_X`-module lies in `R(X)^*` as read through the embedding of Stacks 0ENK — is
proved, as
`AlgebraicGeometry.Space.exists_units_rationalFunctions_canonicalLocalRatio_eq_emb_mul`
(`StacksFrontier/AlgebraicGeometry/Spaces/Decent/PrimeDivisorMeromorphicSectionRatio.lean`), and
with it the field `exists_ord_sub_eq_of_iso` holds at the canonical choices with nothing assumed
beyond `X` being locally Noetherian, integral and decent:
`AlgebraicGeometry.Space.exists_divisorCoefficients_canonicalLocalRatioFamily_sub_eq_ord_of_iso`
(`StacksFrontier/AlgebraicGeometry/Spaces/Decent/PrimeDivisorMeromorphicSectionIso.lean`). What an
isomorphism `ℒ ≅ 𝒩` contributes there is the functoriality of the sheaf of meromorphic sections
in the module, `AlgebraicGeometry.Space.meromorphicSectionSheafMap`, together with the
naturality of the pullback of Stacks 0ENC, part (1) in the module,
`AlgebraicGeometry.Space.pullbackMeromorphicSection_sectionsMap`: the two carry the chosen
section of `𝒩` to a regular meromorphic section of `ℒ` whose coefficient at the generic point of
a prime divisor is the coefficient of the original against a transported generator, and the
order of vanishing does not see which free generator is used.

The other field, `exists_ord_sub_eq_tensorModule`, is proved too, and with it the whole
construction: `AlgebraicGeometry.Space.hasCanonicalTensorProductSection`
(`StacksFrontier/AlgebraicGeometry/Spaces/PicardWeilDivisorClassTensor.lean`) produces, for every
pair of invertible modules, a regular meromorphic section of `ℒ ⊗ 𝒩` whose coefficient at the
generic point of every prime divisor is a *unit times* the product of the coefficients of the
chosen sections of `ℒ` and of `𝒩`, and the unit — which measures the discrepancy between the
generator chosen at `ξ` for `ℒ ⊗ 𝒩` and the product of those chosen for `ℒ` and for `𝒩` — has
order of vanishing zero.  The section is the product of two meromorphic sections on an algebraic
space, the space analogue of Stacks 02SL: it is built chartwise
(`AlgebraicGeometry.Space.meromorphicSectionTensorMul`) and amalgamated over the affine charts
(`AlgebraicGeometry.Space.meromorphicSectionTensor`), the scheme-level
`AlgebraicGeometry.tensorMeromorphicSection` being unavailable here — that construction reads a
meromorphic section on an integral scheme as a single element of the stalk at the generic point
(Stacks 01X5, part (2)) and multiplies there, and that identification has no algebraic-space
analogue.

So Stacks 0EPW is stated with no data beyond `X` locally Noetherian, integral and decent:
`AlgebraicGeometry.Space.canonicalPicardToWeilDivisorClassHom`
(`StacksFrontier/AlgebraicGeometry/Spaces/PicardWeilDivisorClassHom.lean`).

The local finiteness that makes `div_ℒ(s)` a Weil divisor is *not* assumed directly: it comes
from `AlgebraicGeometry.Space.locallyFinite_divisorCoefficients_ne_zero`, applied to the open
subspace recorded by the field `generating`, which is the input that lemma takes. What *is*
assumed is that open subspace, in the field `generating`: it is the first sentence of the proof
of Stacks 0EPS, which this library does not establish — the registration of Stacks 0EPS sits on
`AlgebraicGeometry.Space.locallyFinite_divisorCoefficients_ne_zero`, which carries that open
subspace as a hypothesis — so the field cannot be discharged. The implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.DivisorOfMeromorphicSection` say what is missing for it.

Everything is pinned to the module universe `Modules.{u, u}`, the universe of the schemes. This
is forced from outside: `AlgebraicGeometry.Space.IsInvertibleModule` and
`AlgebraicGeometry.Space.picardGroup` are stated at `Modules.{u, u}`, and
`AlgebraicGeometry.Space.modulesMonoidalCategory` records why the tensor product — hence the
Picard group — cannot be had at any other module universe. The meromorphic sections of Stacks
0EN5 are available at `Modules.{u, max u z}`, which at `z = u` is the same category.

A representative invertible module of a class in `Pic(X)` is chosen with
`AlgebraicGeometry.Space.exists_picardClass`, as the scheme-level Stacks 0BE7
(`AlgebraicGeometry.picardToWeilDivisorClassGroup`) chooses one with the skeleton equivalence:
this is a choice of representative of a quotient, and
`AlgebraicGeometry.Space.PicardDivisorData.picardToWeilDivisorClassGroup_picardClass` shows the
result does not depend on it.

Injectivity on a normal `X` (Stacks 0EPX) is proved from two hypotheses, for the same reason
that the ratio `s / s_ξ` is a parameter: the source checks its claim — that a regular
meromorphic section `t` with `div_ℒ(t) = 0` trivializes `ℒ` — étale locally along the morphism
`Spec(𝒪^h_{X, ξ}) → X`, and with the ratio disconnected from the sections no such check is
available here. The claim is therefore the hypothesis `htriv`, and the rescaling `t = f⁻¹ s`
of a regular meromorphic section by an invertible rational function, read on the ratios, is
the hypothesis `hscale`; what is proved is the reduction of the source, that the two give
injectivity. The scheme-level analogue, Stacks 0BE8, is proved unconditionally as
`AlgebraicGeometry.picardToWeilDivisorClassGroup_injective`, where the sections of an
invertible module and their germs at the generic points of the prime divisors are available
directly.

Neither hypothesis can be improved at this generality, but at the *canonical* choices both are
narrowed, in `StacksFrontier/AlgebraicGeometry/Spaces/PicardWeilDivisorClassCanonical.lean`:
`hscale` is discharged outright, and `htriv` is traded for its unit form, whose antecedent is
that the ratio `t / s_ξ` be the image of a unit of `𝒪^h_{X, ξ}` at the generic point of every
prime divisor rather than that the Weil divisor vanish. The two antecedents are equivalent on a
normal `X` — one direction is `orderOfVanishingSection_eq_zero_of_isUnit` below, the other
`exists_isUnit_canonicalGenericRatio_of_orderOfVanishingSection_eq_zero` (in the namespace
`AlgebraicGeometry.Space.PrimeDivisor`), which rests on `𝒪^h_{X, ξ}` being a discrete
valuation ring there — so what remains of the source's claim there carries no order of
vanishing and no arithmetic at all.

## References

* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
* [Stacks Project, Tag 0EPU](https://stacks.math.columbia.edu/tag/0EPU)
* [Stacks Project, Tag 0EPV](https://stacks.math.columbia.edu/tag/0EPV)
* [Stacks Project, Tag 0EPW](https://stacks.math.columbia.edu/tag/0EPW)
* [Stacks Project, Tag 0EPX](https://stacks.math.columbia.edu/tag/0EPX)
* [Stacks Project, Tag 0ENR](https://stacks.math.columbia.edu/tag/0ENR)
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- Two elements of a quotient of an abelian group agree as soon as their difference lies in
the subgroup. -/
private theorem mk_eq_mk_of_sub_mem {G : Type*} [AddCommGroup G] (s : AddSubgroup G) {a b : G}
    (h : a - b ∈ s) : (QuotientAddGroup.mk a : G ⧸ s) = QuotientAddGroup.mk b := by
  rw [QuotientAddGroup.eq]
  have h' := s.neg_mem h
  rwa [neg_sub, sub_eq_neg_add] at h'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
variable (hdec : IsDecentSpace B S hS X)
variable (E : GenericFractionEmbedding B S hS hX hdec)

/-- Two Weil divisors whose coefficient families differ by the order of vanishing of an
invertible rational function have the same class in `Cl(X)`: their difference is a principal
Weil divisor in the sense of Stacks 0ENR. -/
theorem weilDivisorClass_eq_of_coe_sub_eq_ord {Dv Dv' : ↥(WeilDivisor B S hS X)}
    (f : (rationalFunctions B S hS hX)ˣ)
    (h : ∀ Z : PrimeDivisor B S hS X,
      ((Dv : ↥(WeilDivisor B S hS X)) : PrimeDivisor B S hS X → ℤ) Z -
        ((Dv' : ↥(WeilDivisor B S hS X)) : PrimeDivisor B S hS X → ℤ) Z = E.ord f Z) :
    (QuotientAddGroup.mk Dv : E.weilDivisorClassGroup) = QuotientAddGroup.mk Dv' :=
  mk_eq_mk_of_sub_mem _ ⟨f, funext h⟩

variable [∀ W : PrimeDivisor B S hS X,
  Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hdec)]
variable [∀ W : PrimeDivisor B S hS X,
  IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hdec)]
variable [∀ W : PrimeDivisor B S hS X,
  Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hdec)]

/-- The order of vanishing of an invertible rational function along a prime divisor is the order
of vanishing of its image in the total ring of fractions of the henselian local ring there. -/
private theorem ord_eq_primeDivisor_ord (f : (rationalFunctions B S hS hX)ˣ)
    (Z : PrimeDivisor B S hS X) :
    E.ord f Z = Z.ord B S hS hX hdec (E.emb Z (f : rationalFunctions B S hS hX))
      ((f.isUnit).map (E.emb Z)) :=
  rfl

/-- **Stacks 0EPT.** Two meromorphic sections whose ratios at the generic point of a prime
divisor `Z` differ by the image of an invertible rational function `f` have orders of vanishing
along `Z` differing by `ord_Z(f)`.

The two sections need not be sections of the same `𝒪_X`-module: only their ratios at the
generic point of `Z` are compared, and those are elements of one and the same group of units of
`Q(𝒪^h_{X, ξ})`. For two sections of one module, read through one ratio family, this is
`AlgebraicGeometry.Space.orderOfVanishingSection_eq_add_ord`. -/
theorem orderOfVanishingSection_eq_add_ord_of_ratio_eq (Z : PrimeDivisor B S hS X)
    (L N : Modules.{u, u} B S hS X hX)
    (s : MeromorphicSection.{u, u} B S hS X hX L)
    (t : MeromorphicSection.{u, u} B S hS X hX N)
    (ratioL : LocalRatio.{u, u} B S hS hX hdec Z L)
    (ratioN : LocalRatio.{u, u} B S hS hX hdec Z N)
    (f : (rationalFunctions B S hS hX)ˣ)
    (hst : (ratioL s : Z.genericTotalFractionRing B S hS hX hdec) =
      E.emb Z (f : rationalFunctions B S hS hX) *
        (ratioN t : Z.genericTotalFractionRing B S hS hX hdec)) :
    orderOfVanishingSection.{u, u} B S hS hX hdec Z L s ratioL =
      orderOfVanishingSection.{u, u} B S hS hX hdec Z N t ratioN + E.ord f Z := by
  have hfu : IsUnit (E.emb Z (f : rationalFunctions B S hS hX)) := (f.isUnit).map (E.emb Z)
  have hstep : orderOfVanishingSection.{u, u} B S hS hX hdec Z L s ratioL =
      Z.ord B S hS hX hdec (E.emb Z (f : rationalFunctions B S hS hX) *
        (ratioN t : Z.genericTotalFractionRing B S hS hX hdec))
        (hfu.mul (ratioN t).isUnit) :=
    PrimeDivisor.ord_congr B S hS hX hdec Z _ (hfu.mul (ratioN t).isUnit) hst
  rw [hstep, Z.ord_mul B S hS hX hdec _ _ hfu (ratioN t).isUnit,
    ord_eq_primeDivisor_ord B S hS hX hdec E f Z, orderOfVanishingSection]
  ring

/-- **Stacks 0EPV, in the form the construction of Stacks 0EPW uses.** If the ratio of a
meromorphic section of `ℳ` at the generic point of every prime divisor is the product of the
ratios of meromorphic sections of `ℒ` and of `𝒩`, then the Weil divisor of the first and the sum
of the Weil divisors of the other two differ coefficientwise by the divisor of an invertible
rational function — namely of `1`, the two agreeing on the nose.

This is what turns the hypothesis `hst` of Stacks 0EPV, an identity of ratios, into the field
`exists_ord_sub_eq_tensorModule` of `AlgebraicGeometry.Space.PicardDivisorData`, which asks only
for the weaker identity of divisors; `AlgebraicGeometry.Space.orderOfVanishingSection_mul` is
the identity of divisors that the identity of ratios gives. -/
theorem exists_ord_sub_eq_of_ratio_mul (L N M : Modules.{u, u} B S hS X hX)
    (s : MeromorphicSection.{u, u} B S hS X hX L)
    (t : MeromorphicSection.{u, u} B S hS X hX N)
    (st : MeromorphicSection.{u, u} B S hS X hX M)
    (ratioL : LocalRatioFamily.{u, u} B S hS hX hdec L)
    (ratioN : LocalRatioFamily.{u, u} B S hS hX hdec N)
    (ratioM : LocalRatioFamily.{u, u} B S hS hX hdec M)
    (hst : ∀ W : PrimeDivisor B S hS X,
      (ratioM W st : W.genericTotalFractionRing B S hS hX hdec) =
        (ratioL W s : W.genericTotalFractionRing B S hS hX hdec) *
          (ratioN W t : W.genericTotalFractionRing B S hS hX hdec)) :
    ∃ f : (rationalFunctions B S hS hX)ˣ, ∀ W : PrimeDivisor B S hS X,
      divisorCoefficients.{u, u} B S hS hX hdec M st ratioM W -
          (divisorCoefficients.{u, u} B S hS hX hdec L s ratioL W +
            divisorCoefficients.{u, u} B S hS hX hdec N t ratioN W) =
        E.ord f W := by
  refine ⟨1, fun W => ?_⟩
  rw [congrFun E.ord_one W, Pi.zero_apply]
  simp only [divisorCoefficients]
  rw [orderOfVanishingSection_mul.{u, u} B S hS hX hdec W L N M s t st (ratioL W) (ratioN W)
    (ratioM W) (hst W), sub_self]

/-! ### The data of the construction -/

/-- The choices made by the construction of Stacks 0EPW, for every invertible `𝒪_X`-module `ℒ`
at once: a regular meromorphic section of `ℒ` (Stacks 0EPQ), a generator of `ℒ` at the generic
point of every prime divisor read as the ratio family `s ↦ s / s_ξ` of Stacks 0EPR, the local
finiteness of the prime divisors carrying a nonzero coefficient (Stacks 0EPS), and the two
identities between the resulting Weil divisors which are the content of Stacks 0EPT and of
Stacks 0EPV: that the divisors attached to two isomorphic modules, and that the divisor attached
to a tensor product and the sum of the divisors attached to the factors, differ by the divisor
of an invertible rational function. -/
structure PicardDivisorData where
  /-- `X` is locally Noetherian: the standing hypothesis of the source, in the étale-local form
  the library uses. It is an input of
  `AlgebraicGeometry.Space.locallyFinite_divisorCoefficients_ne_zero`. -/
  isLocallyNoetherian :
    HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y)
  /-- `|X|` is irreducible: the part of `X` being integral that
  `AlgebraicGeometry.Space.locallyFinite_divisorCoefficients_ne_zero` uses. -/
  irreducibleSpace : IrreducibleSpace (points B S hS X)
  /-- A regular meromorphic section of every invertible `𝒪_X`-module, which exists by Stacks
  0EPQ. -/
  sect (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L) :
    MeromorphicSection.{u, u} B S hS X hX L
  /-- A generator of `ℒ` at the generic point of every prime divisor, read as the ratio family
  `s ↦ s / s_ξ` of Stacks 0EPR. -/
  ratio (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L) :
    LocalRatioFamily.{u, u} B S hS hX hdec L
  /-- The nonempty open subspace of `X` over which the chosen section generates `ℒ`, recorded
  by the property its complement has: it contains the generic point of every prime divisor
  along which the order of vanishing is nonzero. This is the *first sentence of the proof of*
  Stacks 0EPS, which this library does not establish and therefore assumes here; the local
  finiteness it yields is not assumed, but taken from
  `AlgebraicGeometry.Space.locallyFinite_divisorCoefficients_ne_zero`, the Stacks 0EE5 step of
  that proof. See the implementation notes of
  `StacksFrontier.AlgebraicGeometry.Spaces.DivisorOfMeromorphicSection` for what is missing. -/
  generating (L : Modules.{u, u} B S hS X hX)
    (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L) :
    ∃ U : Set (points B S hS X), IsOpen U ∧ U.Nonempty ∧
      ∀ W : PrimeDivisor B S hS X,
        divisorCoefficients.{u, u} B S hS hX hdec L (sect L hL) (ratio L hL) W ≠ 0 →
          W.genericPoint B S hS X ∈ Uᶜ
  /-- **Stacks 0EPT.** The Weil divisors of the chosen sections of two isomorphic invertible
  `𝒪_X`-modules differ coefficientwise by the divisor of an invertible rational function on `X`.
  This is the consequence of the first assertion of Stacks 0EPT — that `s / s'` lies in
  `R(X)^*` — that the construction of Stacks 0EPW uses.

  It is stated on the difference of the coefficients rather than on the ratios themselves
  because the ratios are taken against a *chosen* generator at each generic point, and for two
  different modules those choices are independent: a trivialisation of `ℒ` and one of `𝒩` at
  the same point differ by a unit of the local ring about which nothing is known, so no single
  rational function can relate the two ratios. That unit is invisible here, its order of
  vanishing being zero. -/
  exists_ord_sub_eq_of_iso (L N : Modules.{u, u} B S hS X hX)
    (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (hN : IsInvertibleModule (B := B) ⟨X, hX⟩ N) (e : L ≅ N) :
    ∃ f : (rationalFunctions B S hS hX)ˣ, ∀ W : PrimeDivisor B S hS X,
      divisorCoefficients.{u, u} B S hS hX hdec L (sect L hL) (ratio L hL) W -
          divisorCoefficients.{u, u} B S hS hX hdec N (sect N hN) (ratio N hN) W =
        E.ord f W
  /-- **Stacks 0EPV.** The Weil divisor of the chosen section of `ℒ ⊗ 𝒩` and the sum of the Weil
  divisors of the chosen sections of `ℒ` and of `𝒩` differ coefficientwise by the divisor of an
  invertible rational function on `X`.

  It is stated on the difference of the coefficients, rather than asking that the ratio of the
  chosen section of `ℒ ⊗ 𝒩` be the product of the ratios of the chosen sections of `ℒ` and of
  `𝒩`, for the reason recorded on `exists_ord_sub_eq_of_iso` and one more: the chosen section of
  `ℒ ⊗ 𝒩` is a section of that module alone, with no relation to the sections chosen for `ℒ`
  and for `𝒩`, and two regular meromorphic sections of one module differ by an element of
  `R(X)^*` whose divisor is in general nonzero. The identity of ratios is therefore not
  derivable, while this is, and it is what `divisorClass_picardTensorModule` needs. -/
  exists_ord_sub_eq_tensorModule (L N : Modules.{u, u} B S hS X hX)
    (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (hN : IsInvertibleModule (B := B) ⟨X, hX⟩ N) :
    ∃ f : (rationalFunctions B S hS hX)ˣ, ∀ W : PrimeDivisor B S hS X,
      divisorCoefficients.{u, u} B S hS hX hdec (picardTensorModule B S hS hX L N)
            (sect _ (isInvertibleModule_picardTensorModule B S hS hX L N hL hN))
            (ratio _ (isInvertibleModule_picardTensorModule B S hS hX L N hL hN)) W -
          (divisorCoefficients.{u, u} B S hS hX hdec L (sect L hL) (ratio L hL) W +
            divisorCoefficients.{u, u} B S hS hX hdec N (sect N hN) (ratio N hN) W) =
        E.ord f W

namespace PicardDivisorData

variable {B S hS hX hdec E}
variable (D : PicardDivisorData B S hS hX hdec E)

/-- **Stacks 0EPU, part (1).** The Weil divisor `div_ℒ(s) = ∑ ord_{Z,ℒ}(s) [Z]` of the chosen
regular meromorphic section of an invertible `𝒪_X`-module. Its support is locally finite by
`AlgebraicGeometry.Space.locallyFinite_divisorCoefficients_ne_zero`, applied to the open
subspace over which the chosen section generates `ℒ` — the field `generating`, which stands in
for Stacks 0EPS. -/
def divisor (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L) :
    ↥(WeilDivisor B S hS X) :=
  divisorOfSection.{u, u} B S hS hX hdec L (D.sect L hL) (D.ratio L hL)
    (locallyFinite_divisorCoefficients_ne_zero.{u, u} B S hS hX hdec D.isLocallyNoetherian
      D.irreducibleSpace L (D.sect L hL) (D.ratio L hL) (D.generating L hL).choose
      (D.generating L hL).choose_spec.1 (D.generating L hL).choose_spec.2.1
      (D.generating L hL).choose_spec.2.2)

/-- The coefficient of `div_ℒ(s)` at a prime divisor `Z` is `ord_{Z,ℒ}(s)`. -/
@[simp]
theorem coe_divisor (L : Modules.{u, u} B S hS X hX)
    (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L) (Z : PrimeDivisor B S hS X) :
    ((D.divisor L hL : ↥(WeilDivisor B S hS X)) : PrimeDivisor B S hS X → ℤ) Z =
      orderOfVanishingSection.{u, u} B S hS hX hdec Z L (D.sect L hL) (D.ratio L hL Z) :=
  rfl

/-- **Stacks 0EPU, part (2).** The *Weil divisor class of an invertible `𝒪_X`-module*: the class
in `Cl(X)` of the Weil divisor of its chosen regular meromorphic section. -/
def divisorClass (L : Modules.{u, u} B S hS X hX)
    (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L) : E.weilDivisorClassGroup :=
  QuotientAddGroup.mk (D.divisor L hL)

/-- **Stacks 0EPT.** Isomorphic invertible `𝒪_X`-modules have the same Weil divisor class: the
Weil divisors of their chosen sections differ by `div(f)` for an invertible rational function
`f`, which is zero in `Cl(X)`. -/
theorem divisorClass_congr (L N : Modules.{u, u} B S hS X hX)
    (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (hN : IsInvertibleModule (B := B) ⟨X, hX⟩ N) (e : L ≅ N) :
    D.divisorClass L hL = D.divisorClass N hN := by
  obtain ⟨f, hf⟩ := D.exists_ord_sub_eq_of_iso L N hL hN e
  exact weilDivisorClass_eq_of_coe_sub_eq_ord B S hS hX hdec E f hf

/-- **Stacks 0EPV, the identity in `Div(X)`.** The Weil divisor of the chosen section of
`ℒ ⊗ 𝒩` is the sum of the Weil divisors of the chosen sections of `ℒ` and of `𝒩`, as soon as
the ratio of the chosen section of the tensor product is the product of the ratios.

This is `div_{ℒ⊗𝒩}(st) = div_ℒ(s) + div_𝒩(t)` as an identity of Weil divisors, on the nose
rather than up to the divisor of a rational function;
`AlgebraicGeometry.Space.orderOfVanishingSection_mul` is the same identity coefficientwise at a
single prime divisor, of which this is the sum over all of them.

The ratio identity `st/(s_ξ t_ξ) = (s/s_ξ)(t/t_ξ)` is the source's own computation, and it is
the argument `hst` here rather than a field of `AlgebraicGeometry.Space.PicardDivisorData`,
exactly as it is the argument `hst` of the coefficientwise
`AlgebraicGeometry.Space.orderOfVanishingSection_mul`. It is not derivable from the data, and
for two independent reasons. The generator chosen at `ξ` for `ℒ ⊗ 𝒩` and the product of the
generators chosen for `ℒ` and for `𝒩` are two free generators of one invertible module, so they
differ by a unit of the local ring that nothing pins to `1` — see the docstring of
`AlgebraicGeometry.Space.HasCanonicalTensorProductSection`, which is why the canonical choices
produce the identity only up to such a unit. And the section chosen for `ℒ ⊗ 𝒩` is a section of
that module alone: it differs from the product of the chosen sections of `ℒ` and of `𝒩` by an
element of `R(X)^*` whose divisor is in general nonzero. What the data does give, with no extra
argument, is the weaker `exists_ord_sub_eq_tensorModule` — the two divisors differ by the
divisor of an invertible rational function — and that is what
`AlgebraicGeometry.Space.PicardDivisorData.divisorClass_picardTensorModule` uses, which is why
only the *class* of the divisor of a tensor product is additive for an arbitrary
`AlgebraicGeometry.Space.PicardDivisorData`. -/
@[stacks 0EPV "the identity div_{ℒ⊗𝒩}(st) = div_ℒ(s) + div_𝒩(t) in Div(X), at the sections and
  ratio families chosen by PicardDivisorData; st/(s_ξ t_ξ) = (s/s_ξ)(t/t_ξ), the source's own
  computation, is the argument hst, as it is in the coefficientwise
  orderOfVanishingSection_mul: the ratio s/s_ξ is a parameter here as in Stacks 0EPR, and the
  generator chosen at ξ for ℒ⊗𝒩 differs from s_ξ ⊗ t_ξ by a unit that no choice pins to 1
  (HasCanonicalTensorProductSection), so hst is not derivable. What the data gives with no
  extra input is the weaker exists_ord_sub_eq_tensorModule, used by
  divisorClass_picardTensorModule"]
theorem divisor_picardTensorModule (L N : Modules.{u, u} B S hS X hX)
    (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (hN : IsInvertibleModule (B := B) ⟨X, hX⟩ N)
    (hst : ∀ W : PrimeDivisor B S hS X,
      (D.ratio (picardTensorModule B S hS hX L N)
          (isInvertibleModule_picardTensorModule B S hS hX L N hL hN) W
          (D.sect _ (isInvertibleModule_picardTensorModule B S hS hX L N hL hN)) :
        W.genericTotalFractionRing B S hS hX hdec) =
        (D.ratio L hL W (D.sect L hL) : W.genericTotalFractionRing B S hS hX hdec) *
          (D.ratio N hN W (D.sect N hN) : W.genericTotalFractionRing B S hS hX hdec)) :
    D.divisor (picardTensorModule B S hS hX L N)
        (isInvertibleModule_picardTensorModule B S hS hX L N hL hN) =
      D.divisor L hL + D.divisor N hN := by
  refine Subtype.ext (funext fun Z => ?_)
  change orderOfVanishingSection.{u, u} B S hS hX hdec Z (picardTensorModule B S hS hX L N)
      (D.sect _ (isInvertibleModule_picardTensorModule B S hS hX L N hL hN))
      (D.ratio _ (isInvertibleModule_picardTensorModule B S hS hX L N hL hN) Z) =
    orderOfVanishingSection.{u, u} B S hS hX hdec Z L (D.sect L hL) (D.ratio L hL Z) +
      orderOfVanishingSection.{u, u} B S hS hX hdec Z N (D.sect N hN) (D.ratio N hN Z)
  exact orderOfVanishingSection_mul.{u, u} B S hS hX hdec Z L N
    (picardTensorModule B S hS hX L N) (D.sect L hL) (D.sect N hN)
    (D.sect _ (isInvertibleModule_picardTensorModule B S hS hX L N hL hN)) (D.ratio L hL Z)
    (D.ratio N hN Z) (D.ratio _ (isInvertibleModule_picardTensorModule B S hS hX L N hL hN) Z)
    (hst Z)

/-- **Stacks 0EPV, the clause in `Cl(X)`.** The Weil divisor class of a tensor product of
invertible `𝒪_X`-modules is the sum of their Weil divisor classes: the Weil divisor of the
chosen section of `ℒ ⊗ 𝒩` and the sum of the Weil divisors of the chosen sections of `ℒ` and of
`𝒩` differ by `div(f)` for an invertible rational function `f`, which is zero in `Cl(X)`.

This is the source's "in particular" clause.  It asks nothing of the three chosen sections, so
unlike `AlgebraicGeometry.Space.PicardDivisorData.divisor_picardTensorModule` it is not an
identity in `Div(X)`. -/
@[stacks 0EPV "the in-particular clause: the Weil divisor class of ℒ ⊗ 𝒩 is the sum of the Weil
  divisor classes of ℒ and of 𝒩, from the field exists_ord_sub_eq_tensorModule and so with
  nothing assumed of the chosen sections; divisor_picardTensorModule is the identity in Div(X),
  which needs the ratio identity. Cl(X) is Stacks 0ENR relative to the embedding
  R(X) → Q(𝒪^h_{X,ξ}) of Stacks 0ENK, which is the parameter E inhabited by
  genericFractionEmbedding"]
theorem divisorClass_picardTensorModule (L N : Modules.{u, u} B S hS X hX)
    (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (hN : IsInvertibleModule (B := B) ⟨X, hX⟩ N) :
    D.divisorClass (picardTensorModule B S hS hX L N)
        (isInvertibleModule_picardTensorModule B S hS hX L N hL hN) =
      D.divisorClass L hL + D.divisorClass N hN := by
  obtain ⟨f, hf⟩ := D.exists_ord_sub_eq_tensorModule L N hL hN
  exact weilDivisorClass_eq_of_coe_sub_eq_ord B S hS hX hdec E
    (Dv' := D.divisor L hL + D.divisor N hN) f hf

/-! ### The homomorphism `Pic(X) ⟶ Cl(X)` -/

/-- A representative invertible `𝒪_X`-module of a class in `Pic(X)`. -/
def picardRepresentative (x : picardGroup (B := B) (S := S) (hS := hS) ⟨X, hX⟩) :
    Modules.{u, u} B S hS X hX :=
  (exists_picardClass (B := B) ⟨X, hX⟩ x).choose

/-- The representative of a class in `Pic(X)` is an invertible `𝒪_X`-module. -/
theorem isInvertibleModule_picardRepresentative
    (x : picardGroup (B := B) (S := S) (hS := hS) ⟨X, hX⟩) :
    IsInvertibleModule (B := B) ⟨X, hX⟩ (picardRepresentative (hX := hX) x) :=
  (exists_picardClass (B := B) ⟨X, hX⟩ x).choose_spec.choose

/-- The representative of a class in `Pic(X)` has that class. -/
theorem picardClass_picardRepresentative
    (x : picardGroup (B := B) (S := S) (hS := hS) ⟨X, hX⟩) :
    picardClass (B := B) ⟨X, hX⟩ (picardRepresentative (hX := hX) x)
        (isInvertibleModule_picardRepresentative (hX := hX) x) = x :=
  (exists_picardClass (B := B) ⟨X, hX⟩ x).choose_spec.choose_spec

/-- The Weil divisor class of a class in `Pic(X)`: the Weil divisor class of any invertible
`𝒪_X`-module representing it, which is well defined by
`AlgebraicGeometry.Space.PicardDivisorData.divisorClass_congr`. -/
def weilDivisorClassOfPicardClass (x : picardGroup (B := B) (S := S) (hS := hS) ⟨X, hX⟩) :
    E.weilDivisorClassGroup :=
  D.divisorClass (picardRepresentative (hX := hX) x)
    (isInvertibleModule_picardRepresentative (hX := hX) x)

/-- The Weil divisor class of the `Pic(X)`-class of an invertible `𝒪_X`-module is its Weil
divisor class: the choice of representative does not matter, by
`AlgebraicGeometry.Space.PicardDivisorData.divisorClass_congr`. -/
theorem weilDivisorClassOfPicardClass_picardClass (L : Modules.{u, u} B S hS X hX)
    (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L) :
    D.weilDivisorClassOfPicardClass (picardClass (B := B) ⟨X, hX⟩ L hL) =
      D.divisorClass L hL := by
  obtain ⟨e⟩ := (picardClass_eq_picardClass_iff (B := B) ⟨X, hX⟩
    (picardRepresentative (hX := hX) (picardClass (B := B) ⟨X, hX⟩ L hL)) L
    (isInvertibleModule_picardRepresentative (hX := hX) (picardClass (B := B) ⟨X, hX⟩ L hL))
    hL).mp (picardClass_picardRepresentative (hX := hX) (picardClass (B := B) ⟨X, hX⟩ L hL))
  exact D.divisorClass_congr _ L _ hL e

/-- The homomorphism of abelian groups

`Pic(X) ⟶ Cl(X)`

which assigns to an invertible `𝒪_X`-module its Weil divisor class, relative to an embedding
`E : GenericFractionEmbedding` and to choices `D : PicardDivisorData` of section and of generator
at each generic point.

Its value on the class of an invertible module is that module's Weil divisor class
(`AlgebraicGeometry.Space.PicardDivisorData.weilDivisorClassOfPicardClass_picardClass`), well
defined on isomorphism classes by Stacks 0EPT in the form
`AlgebraicGeometry.Space.PicardDivisorData.divisorClass_congr`; additivity is Stacks 0EPV in
the form `AlgebraicGeometry.Space.PicardDivisorData.divisorClass_picardTensorModule`, since addition
in `Pic(X)` is tensor product.

Stacks 0EPW is this at the canonical `E` and `D`, which are what a locally Noetherian integral
algebraic space has and the source names:
`AlgebraicGeometry.Space.canonicalPicardToWeilDivisorClassHom`
(`StacksFrontier/AlgebraicGeometry/Spaces/PicardWeilDivisorClassHom.lean`). -/
def picardToWeilDivisorClassGroup :
    picardGroup (B := B) (S := S) (hS := hS) ⟨X, hX⟩ →+ E.weilDivisorClassGroup :=
  AddMonoidHom.mk' D.weilDivisorClassOfPicardClass fun x y => by
    set L := picardRepresentative (hX := hX) x with hLdef
    set N := picardRepresentative (hX := hX) y with hNdef
    have hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L :=
      isInvertibleModule_picardRepresentative (hX := hX) x
    have hN : IsInvertibleModule (B := B) ⟨X, hX⟩ N :=
      isInvertibleModule_picardRepresentative (hX := hX) y
    have hsum : x + y = picardClass (B := B) ⟨X, hX⟩ (picardTensorModule B S hS hX L N)
        (isInvertibleModule_picardTensorModule B S hS hX L N hL hN) := by
      rw [← picardClass_picardRepresentative (hX := hX) x,
        ← picardClass_picardRepresentative (hX := hX) y]
      exact picardClass_add B S hS hX L N hL hN
    rw [hsum, D.weilDivisorClassOfPicardClass_picardClass _
      (isInvertibleModule_picardTensorModule B S hS hX L N hL hN),
      D.divisorClass_picardTensorModule L N hL hN]
    rfl

/-- The homomorphism `Pic(X) ⟶ Cl(X)` sends the class of an invertible `𝒪_X`-module to its Weil
divisor class. This characterizes it, because every class in `Pic(X)` is the class of an
invertible module.

Stacks 0EPW is this at the canonical `E` and `D`:
`AlgebraicGeometry.Space.canonicalPicardToWeilDivisorClassHom_picardClass`. -/
theorem picardToWeilDivisorClassGroup_picardClass (L : Modules.{u, u} B S hS X hX)
    (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L) :
    D.picardToWeilDivisorClassGroup (picardClass (B := B) ⟨X, hX⟩ L hL) =
      D.divisorClass L hL :=
  D.weilDivisorClassOfPicardClass_picardClass L hL

/-! ### Injectivity on a normal space -/

/-- The chosen regular meromorphic section of an invertible `𝒪_X`-module whose Weil divisor
class vanishes has `ord_{Z,ℒ}(s) = ord_Z(f)` along every prime divisor, for a single invertible
rational function `f` on `X`. -/
private theorem exists_orderOfVanishingSection_eq_ord_of_divisorClass_eq_zero
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (h : D.divisorClass L hL = 0) :
    ∃ f : (rationalFunctions B S hS hX)ˣ, ∀ W : PrimeDivisor B S hS X,
      orderOfVanishingSection.{u, u} B S hS hX hdec W L (D.sect L hL) (D.ratio L hL W) =
        E.ord f W := by
  obtain ⟨f, hf⟩ := (QuotientAddGroup.eq_zero_iff (D.divisor L hL)).mp h
  exact ⟨f, fun W => by rw [← D.coe_divisor L hL W, hf]⟩

/-- **The argument of Stacks 0EPX, at arbitrary divisor data.** The homomorphism

`Pic(X) ⟶ Cl(X)`

attached to a `AlgebraicGeometry.Space.PicardDivisorData` is injective, given two hypotheses:
`htriv`, that a regular meromorphic section of an invertible `𝒪_X`-module whose Weil divisor
vanishes trivializes that module, and `hscale`, the rescaling `t = f⁻¹ s` of a regular
meromorphic section by an invertible rational function read on the ratios at the generic points
of the prime divisors. What is proved from these is the argument of the source: if the Weil
divisor class of `ℒ` vanishes then `div_ℒ(s) = div(f)` for some `f ∈ R(X)^*`, so the rescaled
section `t = f⁻¹ s` has `div_ℒ(t) = 0` by Stacks 0EPT, hence `ℒ` is trivial.

Both hypotheses require regularity of the section: without it they are *refutable*, since the
canonical ratio of the zero section is not a unit and so every order of vanishing of the zero
section is zero, which would force `Pic(X) = 0`. Normality of `X` is not a hypothesis here and
enters only through `htriv`.

Stacks 0EPX itself is `AlgebraicGeometry.Space.injective_canonicalPicardToWeilDivisorClassHom`,
which carries the tag: this is the shared argument with the divisor data and the two hypotheses
still free, and so does not prove the tag's statement. Triviality of `ℒ` is written as the
vanishing of its class in `Pic(X)`, which by
`AlgebraicGeometry.Space.picardClass_eq_zero_iff` says that `ℒ` is isomorphic to `𝒪_X`. -/
theorem injective_picardToWeilDivisorClassGroup
    (hscale : ∀ (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
      (f : (rationalFunctions B S hS hX)ˣ),
      ∃ t : MeromorphicSection.{u, u} B S hS X hX L,
        IsRegularMeromorphicSection.{u, u} B S hS X hX L t ∧ ∀ W : PrimeDivisor B S hS X,
        (D.ratio L hL W (D.sect L hL) : W.genericTotalFractionRing B S hS hX hdec) =
          E.emb W (f : rationalFunctions B S hS hX) *
            (D.ratio L hL W t : W.genericTotalFractionRing B S hS hX hdec))
    (htriv : ∀ (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
      (t : MeromorphicSection.{u, u} B S hS X hX L),
      IsRegularMeromorphicSection.{u, u} B S hS X hX L t →
      (∀ W : PrimeDivisor B S hS X,
          orderOfVanishingSection.{u, u} B S hS hX hdec W L t (D.ratio L hL W) = 0) →
        picardClass (B := B) ⟨X, hX⟩ L hL = 0) :
    Function.Injective D.picardToWeilDivisorClassGroup := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  obtain ⟨L, hL, hxL⟩ := exists_picardClass (B := B) ⟨X, hX⟩ x
  have hzero : D.divisorClass L hL = 0 := by
    rw [← D.picardToWeilDivisorClassGroup_picardClass L hL, hxL, hx]
  obtain ⟨f, hf⟩ :=
    D.exists_orderOfVanishingSection_eq_ord_of_divisorClass_eq_zero L hL hzero
  obtain ⟨t, htreg, ht⟩ := hscale L hL f
  rw [← hxL]
  refine htriv L hL t htreg fun W => ?_
  have hadd := orderOfVanishingSection_eq_add_ord_of_ratio_eq B S hS hX hdec E W L L
    (D.sect L hL) t (D.ratio L hL W) (D.ratio L hL W) f (ht W)
  have hsect := hf W
  omega

end PicardDivisorData

end AlgebraicGeometry.Space

end
