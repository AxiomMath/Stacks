module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorFunctionFieldMeromorphic
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorMeromorphicSectionIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorNormalOrderZeroUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionGeneratingOrderZero
public import StacksFrontier.AlgebraicGeometry.Spaces.PicardWeilDivisorClass

/-!
# The data of Stacks 0EPW at the canonical choices

Let `X` be a decent, locally Noetherian, integral algebraic space over a scheme `S`. The
construction of Stacks 0EPW is carried in
`StacksFrontier/AlgebraicGeometry/Spaces/PicardWeilDivisorClass.lean` by an
`AlgebraicGeometry.Space.GenericFractionEmbedding` `E` and an
`AlgebraicGeometry.Space.PicardDivisorData` `D`, neither of which is data the source has: on
such an `X` both are canonical, and this file assembles them from `X`'s own hypotheses.

The embedding is `AlgebraicGeometry.Space.genericFractionEmbedding` (Stacks 0ENK) and the data
is `AlgebraicGeometry.Space.canonicalPicardDivisorData` below, whose seven fields are taken
from:

1. `isLocallyNoetherian` — the hypothesis `hN` of `X`.
2. `irreducibleSpace` — `AlgebraicGeometry.Space.IsIntegralSpace.irreducibleSpace`.
3. `sect` — `AlgebraicGeometry.Space.regularMeromorphicSection`, Stacks 0EPQ on an integral
   locally Noetherian `X`
   (`StacksFrontier/AlgebraicGeometry/Spaces/PicardWeilDivisorClassIntegral.lean`).
4. `ratio` — `AlgebraicGeometry.Space.canonicalLocalRatioFamily`, Stacks 0EPR
   (`StacksFrontier/AlgebraicGeometry/Spaces/Decent/PrimeDivisorCanonicalRatio.lean`).
5. `generating` — `AlgebraicGeometry.Space.exists_isOpen_nonempty_genericPoint_mem_compl_of_isUnit`
   applied to the generating locus, whose one remaining input is
   `AlgebraicGeometry.Space.CanonicalRatioIsUnitOnGeneratingChart` below.
6. `exists_ord_sub_eq_of_iso` — Stacks 0EPT at the canonical choices, which is
   `AlgebraicGeometry.Space.exists_divisorCoefficients_canonicalLocalRatioFamily_sub_eq_ord_of_iso`
   (`StacksFrontier/AlgebraicGeometry/Spaces/Decent/PrimeDivisorMeromorphicSectionIso.lean`).
7. `exists_ord_sub_eq_tensorModule` —
   `AlgebraicGeometry.Space.CanonicalTensorDivisorIdentity` below, Stacks 0EPV at the canonical
   choices.

Five of the seven are discharged from `X` alone inside the definition; the two that are not are
the hypotheses `hunit` and `htensor` of
`AlgebraicGeometry.Space.canonicalPicardDivisorData`, and each is isolated here as a named `Prop`
so that a single instantiation turns the conditional statements of Stacks 0EPW and 0EPX into
unconditional ones.

Both of those are **proved**, so all seven fields come from `X`:
`AlgebraicGeometry.Space.canonicalRatioIsUnitOnGeneratingChart`
(`StacksFrontier/AlgebraicGeometry/Spaces/Decent/PrimeDivisorGenericStalkGeneratingChart.lean`)
proves `AlgebraicGeometry.Space.CanonicalRatioIsUnitOnGeneratingChart` with no hypothesis, and
`AlgebraicGeometry.Space.canonicalTensorDivisorIdentity_of_exists_product` applied to
`AlgebraicGeometry.Space.hasCanonicalTensorProductSection`
(`StacksFrontier/AlgebraicGeometry/Spaces/PicardWeilDivisorClassTensor.lean`) proves
`AlgebraicGeometry.Space.CanonicalTensorDivisorIdentity` with no hypothesis.  The instantiation
is `AlgebraicGeometry.Space.canonicalPicardToWeilDivisorClassHom`
(`StacksFrontier/AlgebraicGeometry/Spaces/PicardWeilDivisorClassHom.lean`), where Stacks 0EPW is
recorded.

For Stacks 0EPX one of the two hypotheses of the conditional
`AlgebraicGeometry.Space.PicardDivisorData.injective_picardToWeilDivisorClassGroup` *is*
discharged here: the rescaling `hscale` is
`AlgebraicGeometry.Space.exists_isRegularMeromorphicSection_canonicalLocalRatio_eq_genericEmb_mul`
(`StacksFrontier/AlgebraicGeometry/Spaces/Decent/PrimeDivisorFunctionFieldMeromorphic.lean`), so
`AlgebraicGeometry.Space.injective_canonicalPicardToWeilDivisorClassGroup` below asks only for
the claim of the source, `htriv`, and it asks for it with no order of vanishing in it: the
antecedent is that the section generate `ℒ` at the generic point of every prime divisor, that
is, that the ratio `t / s_ξ` be the image of a unit of `𝒪^h_{X, ξ}` there. Trading the vanishing
of the Weil divisor for that is where normality of `X` — the source's own hypothesis, carried as
`hNormal` — is used, through the declaration
`PrimeDivisor.exists_isUnit_canonicalGenericRatio_of_orderOfVanishingSection_eq_zero` of the
namespace `AlgebraicGeometry.Space`
(`StacksFrontier/AlgebraicGeometry/Spaces/Decent/PrimeDivisorNormalOrderZeroUnit.lean`), itself
resting on the discrete valuation ring `𝒪^h_{X, ξ}` of
`AlgebraicGeometry.Space.PrimeDivisor.exists_isDiscreteValuationRing_genericHenselianLocalRing`
(`StacksFrontier/AlgebraicGeometry/Spaces/Decent/PrimeDivisorNormalDiscreteValuationRing.lean`).
The two antecedents are equivalent on a normal `X`, the converse being
`AlgebraicGeometry.Space.orderOfVanishingSection_eq_zero_of_isUnit`.

What `htriv` still owes is therefore purely geometric, and is the étale-local trivialisation of
the source: a regular meromorphic section generating `ℒ` at the generic point of every prime
divisor of a normal `X` is a global section generating `ℒ`, hence `ℒ ≅ 𝒪_X`. Nothing in the
library states it; the two statements it needs and does not have are a free generator over a
covering family of étale charts giving `ℒ ≅ 𝒪_X` — available only over a single chart, as
`Stacks.SheafOfModules.overIsoUnitOfBijectiveSmul` — and algebraic Hartogs over an affine
integral normal étale chart, which exists for schemes as
`Stacks.AlgebraicGeometry.UnitsNormalProper.exists_globalSection_of_forall_ord_eq_zero`
(`StacksFrontier/AlgebraicGeometry/UnitsNormalProper/Hartogs.lean`) but has no form reaching the
ratio at `𝒪^h_{X, ξ}`.

## Main definitions

* `AlgebraicGeometry.Space.CanonicalRatioIsUnitOnGeneratingChart`: the remaining content of the
  field `generating` — at the generic point of a prime divisor lying in a chart over which the
  chosen regular meromorphic section generates `ℒ`, the canonical ratio `s / s_ξ` is the image
  of a unit of `𝒪^h_{X, ξ}`.
* `AlgebraicGeometry.Space.CanonicalTensorDivisorIdentity`: the field
  `exists_ord_sub_eq_tensorModule` at the canonical choices, which is Stacks 0EPV in the form
  the construction uses.
* `AlgebraicGeometry.Space.canonicalPicardDivisorData`: the data of the construction of Stacks
  0EPW at the canonical choices, with the five fields listed above discharged.

## Main results

* `AlgebraicGeometry.Space.canonicalRatioIsUnitOnGeneratingChart_of_isUnit_genericStalkCoefficient`
  reduces the obligation `hunit` to a statement about the coefficient of Stacks 0EPR at the
  generic point of a prime divisor — that it is a unit of `𝒪_{U, u}` where the section generates
  `ℒ`. Nothing between that statement and Stacks 0EPW is still owed.
* `AlgebraicGeometry.Space.canonicalPicardToWeilDivisorClassGroup_picardClass`: the value of the
  homomorphism of Stacks 0EPW built from the canonical data on the class of an invertible
  module.
* `AlgebraicGeometry.Space.injective_canonicalPicardToWeilDivisorClassGroup`: Stacks 0EPX for
  the canonical data on a normal `X`, from the geometric claim of the source alone.

## Implementation notes

The three instance hypotheses on the henselian local rings at the generic points — nontriviality,
Noetherianness and Krull dimension at most one — are the conclusions of Stacks 0ENK and hold on
such an `X`; they are carried as instance arguments here, exactly as in
`StacksFrontier/AlgebraicGeometry/Spaces/PicardWeilDivisorClass.lean`, and
`AlgebraicGeometry.Space.PrimeDivisor.nontrivial_genericHenselianLocalRing` and its two
companions discharge them. Being `Prop`-valued classes they are definitionally unique, so the
`haveI`-prefixed statement of Stacks 0EPT at the canonical choices matches the field
it fills with no transport.

## References

* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EPQ](https://stacks.math.columbia.edu/tag/0EPQ)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EPS](https://stacks.math.columbia.edu/tag/0EPS)
* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
* [Stacks Project, Tag 0EPV](https://stacks.math.columbia.edu/tag/0EPV)
* [Stacks Project, Tag 0EPW](https://stacks.math.columbia.edu/tag/0EPW)
* [Stacks Project, Tag 0EPX](https://stacks.math.columbia.edu/tag/0EPX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance] chartMeromorphicAlgebra
attribute [local instance] meromorphicSectionModuleRingedSiteModule
attribute [local instance] PrimeDivisor.genericStalkMeromorphicAlgebra

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
variable (hdec : IsDecentSpace B S hS X)
variable (hInt : IsIntegralSpace B S hS X)
variable (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))

/-! ### The two obligations the canonical choices still carry -/

/-- **The remaining content of the field `generating` of
`AlgebraicGeometry.Space.PicardDivisorData` at the canonical choices.** At the generic point `ξ`
of a prime divisor lying in the image of an étale chart over which the chosen regular
meromorphic section of `ℒ` generates `ℒ`, the canonical ratio `s / s_ξ` of Stacks 0EPR is the
image in `Q(𝒪^h_{X, ξ})` of a unit of `𝒪^h_{X, ξ}`.

This is the hypothesis `hunit` of
`AlgebraicGeometry.Space.exists_isOpen_nonempty_genericPoint_mem_compl_of_isUnit`, which turns
it into the nonempty open subspace that Stacks 0EPS consumes; the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/MeromorphicSectionGeneratingOrderZero.lean` record what
proving it needs. -/
def CanonicalRatioIsUnitOnGeneratingChart : Prop :=
  ∀ (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (W : PrimeDivisor B S hS X) (V : SmallEtale B S hS X),
    W.genericPoint B S hS X ∈ Set.range (pointsMap B S hS
        (yoneda.obj ((SmallEtale.toOver B S hS X).obj V)) V.obj.hom) →
    GeneratesOnChart B S hS hX L (regularMeromorphicSection B S hS hX hInt hN L hL) V →
    ∃ v : ↥(W.genericHenselianLocalRing B S hS hX hdec), IsUnit v ∧
      W.canonicalGenericRatio B S hS hX hdec L hL hInt hN
          (regularMeromorphicSection B S hS hX hInt hN L hL) =
        algebraMap ↥(W.genericHenselianLocalRing B S hS hX hdec)
          (W.genericTotalFractionRing B S hS hX hdec) v

/-! ### The field `generating` reduces to the coefficient at `ξ` -/

include hX hInt hN in
/-- **The field `generating` reduces to unit-ness of the coefficient of Stacks 0EPR.** If, at
the generic point `ξ` of a prime divisor lying in a chart over which the chosen regular
meromorphic section generates `ℒ`, the coefficient of that section against the generator chosen
over `Spec(𝒪_{U, u})` is a unit of `𝒪_{U, u}`, then the canonical ratio `s / s_ξ` is the image
of a unit of `𝒪^h_{X, ξ}`: the ratio is the image of the coefficient under
`Q(𝒪_{U, u}) → Q(𝒪^h_{X, ξ})`, which carries a regular function to its image in `𝒪^h_{X, ξ}`
and a unit to a unit. -/
theorem canonicalRatioIsUnitOnGeneratingChart_of_isUnit_genericStalkCoefficient
    (hcoeff : ∀ (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
      (W : PrimeDivisor B S hS X) (V : SmallEtale B S hS X),
      W.genericPoint B S hS X ∈ Set.range (pointsMap B S hS
          (yoneda.obj ((SmallEtale.toOver B S hS X).obj V)) V.obj.hom) →
      GeneratesOnChart B S hS hX L (regularMeromorphicSection B S hS hX hInt hN L hL) V →
      ∃ w : (structurePresheaf B S hS (W.genericStalkSpace B S hS hX hdec).1).obj
          (op (W.genericStalkChart B S hS hX hdec)),
        IsUnit w ∧ W.genericStalkCoefficient B S hS hX hdec L hL
            (regularMeromorphicSection B S hS hX hInt hN L hL) =
          algebraMap ((structurePresheaf B S hS (W.genericStalkSpace B S hS hX hdec).1).obj
              (op (W.genericStalkChart B S hS hX hdec)))
            ((meromorphicFunctionSheaf B S hS (W.genericStalkSpace B S hS hX hdec).1
              (W.genericStalkSpace B S hS hX hdec).2).obj.obj
                (op (W.genericStalkChart B S hS hX hdec))) w) :
    CanonicalRatioIsUnitOnGeneratingChart B S hS hX hdec hInt hN := by
  intro L hL W V hmem hgen
  obtain ⟨w, hw, hwc⟩ := hcoeff L hL W V hmem hgen
  refine ⟨W.genericStalkSectionsToHenselian B S hS hX hdec w,
    hw.map (W.genericStalkSectionsToHenselian B S hS hX hdec), ?_⟩
  rw [PrimeDivisor.canonicalGenericRatio, hwc,
    W.genericStalkMeromorphicToGeneric_algebraMap B S hS hX hdec hInt hN w]

variable [∀ W : PrimeDivisor B S hS X,
  Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hdec)]
variable [∀ W : PrimeDivisor B S hS X,
  IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hdec)]
variable [∀ W : PrimeDivisor B S hS X,
  Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hdec)]

/-- **Stacks 0EPV in the form the construction of Stacks 0EPW uses, at the canonical choices.**
The Weil divisor of the chosen regular meromorphic section of `ℒ ⊗ 𝒩` and the sum of the Weil
divisors of the chosen sections of `ℒ` and of `𝒩` differ coefficientwise by the divisor of an
invertible rational function on `X`.

This is the field `exists_ord_sub_eq_tensorModule` of
`AlgebraicGeometry.Space.PicardDivisorData` read at
`AlgebraicGeometry.Space.regularMeromorphicSection`,
`AlgebraicGeometry.Space.canonicalLocalRatioFamily` and the embedding of Stacks 0ENK. The
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/PicardWeilDivisorClass.lean` record what proving it needs:
a regular meromorphic section of `ℒ ⊗ 𝒩` whose coefficient at the generic point of every prime
divisor is the product of the coefficients of the chosen sections of `ℒ` and of `𝒩` **up to a
unit of `𝒪_{U, u}`**.  Exact multiplicativity of that coefficient is *not* available: the
generators `AlgebraicGeometry.Space.PrimeDivisor.genericStalkTrivialisation` chooses for `ℒ`,
for `𝒩` and for `ℒ ⊗ 𝒩` are three independent choices and do not agree, so the two sides
differ by a unit, measured by
`AlgebraicGeometry.Space.PrimeDivisor.genericStalkCoefficient_eq_mul_of_eval_eq_smul`.  The unit
is harmless for the Weil divisor, its order of vanishing being zero.

This `Prop` is discharged from the up-to-a-unit input by
`AlgebraicGeometry.Space.canonicalTensorDivisorIdentity_of_exists_product`
(`StacksFrontier/AlgebraicGeometry/Spaces/PicardWeilDivisorClassTensor.lean`), whose hypothesis is
the named `AlgebraicGeometry.Space.HasCanonicalTensorProductSection`. -/
def CanonicalTensorDivisorIdentity : Prop :=
  ∀ (L N : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (hNinv : IsInvertibleModule (B := B) ⟨X, hX⟩ N),
    ∃ f : (rationalFunctions B S hS hX)ˣ, ∀ W : PrimeDivisor B S hS X,
      divisorCoefficients.{u, u} B S hS hX hdec (picardTensorModule B S hS hX L N)
            (regularMeromorphicSection B S hS hX hInt hN _
              (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv))
            (canonicalLocalRatioFamily B S hS hX hdec _
              (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv) hInt hN) W -
          (divisorCoefficients.{u, u} B S hS hX hdec L
              (regularMeromorphicSection B S hS hX hInt hN L hL)
              (canonicalLocalRatioFamily B S hS hX hdec L hL hInt hN) W +
            divisorCoefficients.{u, u} B S hS hX hdec N
              (regularMeromorphicSection B S hS hX hInt hN N hNinv)
              (canonicalLocalRatioFamily B S hS hX hdec N hNinv hInt hN) W) =
        (genericFractionEmbedding B S hS hX hdec hInt hN).ord f W

/-! ### Both obligations reduce to a statement about the coefficient at `ξ` -/

/-! ### The data of the construction at the canonical choices -/

/-- **The choices of the construction of Stacks 0EPW, made canonically on a decent, locally
Noetherian, integral algebraic space.** The section is the one Stacks 0EPQ produces, the ratio
family is the one Stacks 0EPR produces, the two standing hypotheses are `X`'s own, the open
subspace of Stacks 0EPS is the generating locus of the chosen section, and the identity of
Stacks 0EPT is the one proved in this library, at these choices.

The two hypotheses are the two fields that the canonical choices do not discharge from `X`
alone, each a named `Prop` above: `hunit` is what remains of the field `generating` and
`htensor` is the field `exists_ord_sub_eq_tensorModule`. `hunit` is itself proved —
`AlgebraicGeometry.Space.canonicalRatioIsUnitOnGeneratingChart` proves it with no hypothesis —
so what this definition still owes is `htensor` alone. -/
def canonicalPicardDivisorData
    (hunit : CanonicalRatioIsUnitOnGeneratingChart B S hS hX hdec hInt hN)
    (htensor : CanonicalTensorDivisorIdentity B S hS hX hdec hInt hN) :
    PicardDivisorData B S hS hX hdec (genericFractionEmbedding B S hS hX hdec hInt hN) where
  isLocallyNoetherian := hN
  irreducibleSpace := hInt.irreducibleSpace
  sect L hL := regularMeromorphicSection B S hS hX hInt hN L hL
  ratio L hL := canonicalLocalRatioFamily B S hS hX hdec L hL hInt hN
  generating L hL :=
    exists_isOpen_nonempty_genericPoint_mem_compl_of_isUnit B S hS hX hdec hInt hN L hL
      (hunit L hL)
  exists_ord_sub_eq_of_iso L N hL hNinv e :=
    exists_divisorCoefficients_canonicalLocalRatioFamily_sub_eq_ord_of_iso B S hS hX hdec L N
      hL hNinv hInt hN e
  exists_ord_sub_eq_tensorModule L N hL hNinv := htensor L N hL hNinv

/-- The section chosen by the canonical data is the regular meromorphic section of Stacks
0EPQ. -/
@[simp]
theorem sect_canonicalPicardDivisorData
    (hunit : CanonicalRatioIsUnitOnGeneratingChart B S hS hX hdec hInt hN)
    (htensor : CanonicalTensorDivisorIdentity B S hS hX hdec hInt hN)
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L) :
    (canonicalPicardDivisorData B S hS hX hdec hInt hN hunit htensor).sect L hL =
      regularMeromorphicSection B S hS hX hInt hN L hL :=
  rfl

/-- The ratio family chosen by the canonical data is the one of Stacks 0EPR. -/
@[simp]
theorem ratio_canonicalPicardDivisorData
    (hunit : CanonicalRatioIsUnitOnGeneratingChart B S hS hX hdec hInt hN)
    (htensor : CanonicalTensorDivisorIdentity B S hS hX hdec hInt hN)
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L) :
    (canonicalPicardDivisorData B S hS hX hdec hInt hN hunit htensor).ratio L hL =
      canonicalLocalRatioFamily B S hS hX hdec L hL hInt hN :=
  rfl

/-- **The homomorphism of Stacks 0EPW at the canonical choices sends the class of an invertible
`𝒪_X`-module to its Weil divisor class**, the Weil divisor being that of the regular meromorphic
section of Stacks 0EPQ read through the ratio family of Stacks 0EPR. -/
theorem canonicalPicardToWeilDivisorClassGroup_picardClass
    (hunit : CanonicalRatioIsUnitOnGeneratingChart B S hS hX hdec hInt hN)
    (htensor : CanonicalTensorDivisorIdentity B S hS hX hdec hInt hN)
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L) :
    (canonicalPicardDivisorData B S hS hX hdec hInt hN hunit
          htensor).picardToWeilDivisorClassGroup (picardClass (B := B) ⟨X, hX⟩ L hL) =
      (canonicalPicardDivisorData B S hS hX hdec hInt hN hunit htensor).divisorClass L hL :=
  PicardDivisorData.picardToWeilDivisorClassGroup_picardClass _ L hL

/-! ### Injectivity, from the claim of Stacks 0EPX alone -/

include hX hInt hN in
/-- **Stacks 0EPX at the canonical choices, on a normal `X`, from the geometric claim of the
source alone.** The homomorphism `Pic(X) ⟶ Cl(X)` built from the canonical data is injective as
soon as a regular meromorphic section of an invertible `𝒪_X`-module which generates that module
at the generic point of every prime divisor trivializes it, which is the hypothesis `htriv`
here.

Normality of `X` is the source's own hypothesis and is carried, as `hNormal`. What it
discharges is the *arithmetic* half of the claim: the source reads
`0 = ord_{Z, ℒ}(t) = ord_{𝒪^h_{X, ξ}}(f_ξ)` at a codimension-one point and concludes that `f_ξ`
is a unit of the local ring there, which is legitimate because normality makes `𝒪^h_{X, ξ}` a
discrete valuation ring. That step is
`PrimeDivisor.exists_isUnit_canonicalGenericRatio_of_orderOfVanishingSection_eq_zero`
(`StacksFrontier/AlgebraicGeometry/Spaces/Decent/PrimeDivisorNormalOrderZeroUnit.lean`), and it is
what lets `htriv` be stated at the *unit* ratio rather than at the vanishing of the Weil
divisor. On a normal `X` the two antecedents are equivalent — the converse is
`AlgebraicGeometry.Space.orderOfVanishingSection_eq_zero_of_isUnit` — so this is the same claim
with no order of vanishing left in it, and no arithmetic still owed.

The second hypothesis of
`AlgebraicGeometry.Space.PicardDivisorData.injective_picardToWeilDivisorClassGroup`, the
rescaling `t = f⁻¹ s` of a regular meromorphic section by an invertible rational function, is
*not* carried: at the canonical choices it is
`exists_isRegularMeromorphicSection_canonicalLocalRatio_eq_genericEmb_mul`. -/
theorem injective_canonicalPicardToWeilDivisorClassGroup
    (hNormal : IsNormal B S hS X)
    (hunit : CanonicalRatioIsUnitOnGeneratingChart B S hS hX hdec hInt hN)
    (htensor : CanonicalTensorDivisorIdentity B S hS hX hdec hInt hN)
    (htriv : ∀ (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
      (t : MeromorphicSection.{u, u} B S hS X hX L),
      IsRegularMeromorphicSection.{u, u} B S hS X hX L t →
      (∀ W : PrimeDivisor B S hS X,
          ∃ v : ↥(W.genericHenselianLocalRing B S hS hX hdec), IsUnit v ∧
            W.canonicalGenericRatio B S hS hX hdec L hL hInt hN t =
              algebraMap ↥(W.genericHenselianLocalRing B S hS hX hdec)
                (W.genericTotalFractionRing B S hS hX hdec) v) →
        picardClass (B := B) ⟨X, hX⟩ L hL = 0) :
    Function.Injective (canonicalPicardDivisorData B S hS hX hdec hInt hN hunit
      htensor).picardToWeilDivisorClassGroup :=
  PicardDivisorData.injective_picardToWeilDivisorClassGroup _
    (fun L hL f => exists_isRegularMeromorphicSection_canonicalLocalRatio_eq_genericEmb_mul
      B S hS hX hdec hInt hN L hL f)
    (fun L hL t ht hord => htriv L hL t ht fun W =>
      W.exists_isUnit_canonicalGenericRatio_of_orderOfVanishingSection_eq_zero B S hS hX hdec
        hInt hN hNormal L hL t ht (hord W))

end AlgebraicGeometry.Space

end
