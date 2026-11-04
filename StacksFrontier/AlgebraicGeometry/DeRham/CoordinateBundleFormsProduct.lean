module

public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBlowupFormsDirectImage
public import StacksFrontier.AlgebraicGeometry.DeRham.KunnethDegreewise
public import StacksFrontier.AlgebraicGeometry.Limits.ProjectiveSpace

/-!
# The product decomposition of the relative forms of the projective bundle of a coordinate blowup

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes and let `W = X ×_S Y`. The sheaf of
relative differential `d`-forms of `W` over `S` decomposes as a direct sum over `d = r + s`,

`Ω^d_{W/S} ≅ ⨁_{r + s = d} pr₁^*Ω^r_{X/S} ⊗ pr₂^*Ω^s_{Y/S}`,

the `(r, s)` summand being the external tensor product `Ω^r_{X/S} ⊠ Ω^s_{Y/S}` of
[Stacks, Tag 0G46]. This file states that decomposition and instantiates it in the situation of
Section 50.16 of the source — a ring `R`, `S = Spec(R)`, the centre `Z = 𝐀^m_S` of the standard
coordinate blowup of `X = 𝐀^{m+n}_S`, and the projective bundle `P = 𝐏^{n-1}_Z` with its
projection `p : P ⟶ Z` — in which it reads

`Ω^a_{P/S} ≅ ⨁_{r + s = a} pr₁^*Ω^r_{Z/S} ⊗ pr₂^*Ω^s_{𝐏^{n-1}_S/S}`.

This is the opening move of the source's proof of clause (2) of [Stacks, Tag 0FUR], which then
pushes the decomposition forward along `p = pr₁` and finds that only the `s = 0` summand
survives.

**Nothing here carries a `@[stacks]` attribute.** The decomposition is not a tag of the source:
Section 50.16 quotes it from Lemma 50.8.1, whose content in this development is already
[Stacks, Tag 0FMA] in its degreewise form (see below).

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.relativeFormsProductSummand`: the `(r, s)` summand
  `pr₁^*Ω^r_{X/S} ⊗ pr₂^*Ω^s_{Y/S}` of the decomposition.
* `AlgebraicGeometry.Scheme.Hom.relativeFormsProductIso`: **the product decomposition
  `⨁_{r + s = d} pr₁^*Ω^r_{X/S} ⊗ pr₂^*Ω^s_{Y/S} ≅ Ω^d_{X ×_S Y / S}`.**
* `AlgebraicGeometry.Scheme.Hom.relativeFormsPushforwardProductIso`: that decomposition pushed
  forward along the first projection, termwise.
* `Stacks.DeRham.coordinateBundleAmbient`, `Stacks.DeRham.coordinateBundleAmbientToBase`: the
  projective space `𝐏^{n-1}_S` over the base of the standard coordinate blowup, and its
  structure morphism.
* `Stacks.DeRham.coordinateBundleProduct`: the fibre product `Z ×_S 𝐏^{n-1}_S`, which is the
  source's own description of the projective bundle `P`.
* `Stacks.DeRham.coordinateBundleFormsProductIso`: **the product decomposition of
  `Ω^a_{Z ×_S 𝐏^{n-1}_S / S}`**, in every degree `a ≥ 0` and for every `n`.
* `Stacks.DeRham.coordinateBundleFormsPushforwardProductIso`: that decomposition pushed forward
  along `p = pr₁`, termwise.

## Main results

* `AlgebraicGeometry.Scheme.Hom.relativeFormsProductIso_eq`: the decomposition is the
  underlying isomorphism of sheaves of modules of the degreewise de Rham Künneth isomorphism of
  [Stacks, Tag 0FMA].
* `Stacks.DeRham.coordinateBundleProductIso`: the identification
  `Z ×_S 𝐏^{n-1}_S ≅ 𝐏^{n-1}_Z = P` of the source's two descriptions of the projective bundle.
* `Stacks.DeRham.coordinateBundleProductIso_hom_comp_toCentre`: that identification carries the
  first projection of the fibre product to the projection `p : P ⟶ Z`, which is the source's
  assertion that `p = pr₁`.

## Implementation notes

**The general decomposition is [Stacks, Tag 0FMA] read on the underlying sheaves of modules.**
`AlgebraicGeometry.Scheme.Hom.deRhamBoxModuleIso` of
`StacksFrontier.AlgebraicGeometry.DeRham.KunnethDegreewise` already states exactly
`⨁_{r + s = d} (Ω^r_{X/S} ⊠ Ω^s_{Y/S}) ≅ Ω^d_{W/S}`, with the summands presented as terms of the
box-product double complex in the category of finite-order differential operators on `W/S`.
`AlgebraicGeometry.Scheme.Hom.relativeFormsProductIso` below is that isomorphism with the
summands spelled out as external tensor products of sheaves of modules — the two types are
definitionally equal, since every step in between is an `abbrev` — so that a consumer who wants
only the decomposition of the sheaves need not mention the category of differential operators,
the double complex or its total complex. `relativeFormsProductIso_eq` records the identification,
which is what makes the compatibilities proved in
`StacksFrontier.AlgebraicGeometry.DeRham.KunnethWedge` and
`StacksFrontier.AlgebraicGeometry.DeRham.KunnethDegreewise` available here.

**The two descriptions of `P`.** `Stacks.DeRham.coordinateBlowupBundle` is `𝐏^{n-1}_Z`, the base
change of the integral model of projective space to the centre `Z`; the source writes `P` as the
fibre product `Z ×_S 𝐏^{n-1}_S`, which is what the decomposition is about. The two agree by the
base-change identification `AlgebraicGeometry.ProjectiveSpace.baseChangeIso` composed with the
symmetry of a fibre product, and under that identification the first projection of
`Z ×_S 𝐏^{n-1}_S` is the projection `p : P ⟶ Z`. The decomposition is therefore stated for the
fibre product rather than transported to `Ω^a_{P/S}`: transporting would replace `Ω^a_{P/S}` by
its pullback along an isomorphism, which is a weaker and less usable statement than the pair
"decomposition of the fibre product" and "identification of the fibre product with `P`".

**The termwise pushforward is the additivity of `p_*`, and nothing more.** Direct image of
sheaves of modules is a right adjoint, hence additive, hence commutes with a finite direct sum;
that is all that
`AlgebraicGeometry.Scheme.Hom.relativeFormsPushforwardProductIso` says. In particular it does
not identify the pushed-forward `(r, s)` summand with anything simpler.

**What this does not do.** The decomposition alone does not give clause (2) of
[Stacks, Tag 0FUR] for `n > 1`. The source's proof needs two further inputs, and they are in
different states in this development. The projection formula identifying
`p_*(pr₂^*Ω^s_{𝐏^{n-1}_S/S} ⊗ p^*Ω^r_{Z/S})` with `p_*pr₂^*Ω^s_{𝐏^{n-1}_S/S} ⊗ Ω^r_{Z/S}` **is**
available, for an arbitrary morphism of schemes and at a finite locally free module on the
target, as `Stacks.AffineProjectionFormula.isIso_projectionFormulaMap_of_restrict_locally_free`;
it is not invoked here, because the decomposition and the projection formula are independent
statements and this file is about the first. What is **not** available is the vanishing of
`p_*pr₂^*Ω^s_{𝐏^{n-1}_S/S}` for `s > 0`, that is, the degree-zero Hodge cohomology
`H⁰(𝐏^{n-1}, Ω^s) = 0`; the development carries the Hodge cohomology of projective space only
conditionally on an undischarged exterior-power filtration hypothesis. That single vanishing is
what still separates this file from clause (2) in degrees `a > 0`.

## References

* [Stacks Project, Tag 0FUR](https://stacks.math.columbia.edu/tag/0FUR)
* [Stacks Project, Tag 0FMA](https://stacks.math.columbia.edu/tag/0FMA)
* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance] AlgebraicGeometry.hasColimits_sheafOfModules_toRingCat
attribute [local instance] CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- The `(r, s)` summand `pr₁^*Ω^r_{X/S} ⊗ pr₂^*Ω^s_{Y/S}` of the product decomposition of
`Ω^{r+s}_{X ×_S Y/S}`: the external tensor product `Ω^r_{X/S} ⊠ Ω^s_{Y/S}` of
[Stacks, Tag 0G46]. -/
abbrev relativeFormsProductSummand (d : ℕ) (j : deRhamBoxIndex d) : (pullback a b).Modules :=
  externalTensorProduct a b (relativeDifferentialForms a (j.1.1 : ℤ))
    (relativeDifferentialForms b (j.1.2 : ℤ))

/-- **The product decomposition of the sheaves of relative differential forms:**

`⨁_{r + s = d} pr₁^*Ω^r_{X/S} ⊗ pr₂^*Ω^s_{Y/S} ≅ Ω^d_{X ×_S Y / S}`.

This is the degreewise de Rham Künneth isomorphism of [Stacks, Tag 0FMA], read on the underlying
sheaves of modules and with the summands spelled out as external tensor products; see
`AlgebraicGeometry.Scheme.Hom.relativeFormsProductIso_eq`. -/
def relativeFormsProductIso (d : ℕ) :
    (⨁ relativeFormsProductSummand a b d) ≅
      relativeDifferentialForms (pullback.fst a b ≫ a) (d : ℤ) :=
  deRhamBoxModuleIso a b d

/-- The product decomposition of the sheaves of relative differential forms **is** the underlying
isomorphism of sheaves of modules of the degreewise de Rham Künneth isomorphism of
[Stacks, Tag 0FMA]; the two statements differ only in how the summands are spelled. -/
theorem relativeFormsProductIso_eq (d : ℕ) :
    relativeFormsProductIso a b d = deRhamBoxModuleIso a b d := rfl

/-- **The product decomposition pushed forward along the first projection, termwise:**

`pr₁_*Ω^d_{X ×_S Y/S} ≅ ⨁_{r + s = d} pr₁_*(pr₁^*Ω^r_{X/S} ⊗ pr₂^*Ω^s_{Y/S})`.

Direct image is a right adjoint, hence additive, hence commutes with the finite direct sum. This
is the step at which the source's proof of clause (2) of [Stacks, Tag 0FUR] "pushes the
decomposition forward termwise"; what it does **not** supply is the projection formula
identifying the `(r, s)` term with `Ω^r_{X/S} ⊗ pr₁_*pr₂^*Ω^s_{Y/S}`. -/
def relativeFormsPushforwardProductIso (d : ℕ) :
    (⨁ fun j : deRhamBoxIndex d => (Scheme.Modules.pushforward (pullback.fst a b)).obj
        (relativeFormsProductSummand a b d j)) ≅
      (Scheme.Modules.pushforward (pullback.fst a b)).obj
        (relativeDifferentialForms (pullback.fst a b ≫ a) (d : ℤ)) :=
  ((Scheme.Modules.pushforward (pullback.fst a b)).mapBiproduct
      (relativeFormsProductSummand a b d)).symm ≪≫
    (Scheme.Modules.pushforward (pullback.fst a b)).mapIso (relativeFormsProductIso a b d)

end AlgebraicGeometry.Scheme.Hom

namespace Stacks.DeRham

variable (R : Type u) [CommRing R] (m n : ℕ)

/-! ### The projective space `𝐏^{n-1}_S` over the base, and the fibre product `Z ×_S 𝐏^{n-1}_S` -/

/-- The projective space `𝐏^{n-1}_S` over the base of the standard coordinate blowup. -/
abbrev coordinateBundleAmbient : Scheme.{u} :=
  AlgebraicGeometry.projectiveSpaceOver (n - 1) (coordinateBase R)

/-- The structure morphism `𝐏^{n-1}_S ⟶ S` of projective space over the base of the standard
coordinate blowup. -/
abbrev coordinateBundleAmbientToBase : coordinateBundleAmbient R n ⟶ coordinateBase R :=
  (AlgebraicGeometry.projectiveSpaceOver.over (n - 1) (coordinateBase R)).hom

/-- The fibre product `Z ×_S 𝐏^{n-1}_S`, which is the source's description of the projective
bundle `P` of the standard coordinate blowup. -/
abbrev coordinateBundleProduct : Scheme.{u} :=
  pullback (coordinateBlowupCentreToBase R m) (coordinateBundleAmbientToBase R n)

/-- **The source's two descriptions of the projective bundle agree:**
`Z ×_S 𝐏^{n-1}_S ≅ 𝐏^{n-1}_Z = P`. Projective space over `Z` is the base change of projective
space over `S` along `Z ⟶ S`. -/
def coordinateBundleProductIso :
    coordinateBundleProduct R m n ≅ coordinateBlowupBundle R m n :=
  (pullbackSymmetry (coordinateBlowupCentreToBase R m)
      (coordinateBundleAmbientToBase R n)).trans
    (AlgebraicGeometry.ProjectiveSpace.baseChangeIso (n - 1)
      (coordinateBlowupCentreToBase R m))

/-- **Under the identification `Z ×_S 𝐏^{n-1}_S ≅ P` the first projection is the projection
`p : P ⟶ Z`**, which is the source's assertion that `p = pr₁`. -/
theorem coordinateBundleProductIso_hom_comp_toCentre :
    (coordinateBundleProductIso R m n).hom ≫ coordinateBlowupBundleToCentre R m n =
      pullback.fst (coordinateBlowupCentreToBase R m) (coordinateBundleAmbientToBase R n) := by
  change ((pullbackSymmetry (coordinateBlowupCentreToBase R m)
        (AlgebraicGeometry.ProjectiveSpace (n - 1) (coordinateBase R) ↘ coordinateBase R)).hom ≫
      (AlgebraicGeometry.ProjectiveSpace.baseChangeIso (n - 1)
        (coordinateBlowupCentreToBase R m)).hom) ≫
      (AlgebraicGeometry.ProjectiveSpace (n - 1) (coordinateBlowupCentre R m) ↘
        coordinateBlowupCentre R m) =
    pullback.fst (coordinateBlowupCentreToBase R m)
      (AlgebraicGeometry.ProjectiveSpace (n - 1) (coordinateBase R) ↘ coordinateBase R)
  rw [Category.assoc, AlgebraicGeometry.ProjectiveSpace.baseChangeIso_hom_over,
    pullbackSymmetry_hom_comp_snd]

/-! ### The product decomposition in the situation of the coordinate blowup -/

/-- **The product decomposition of the relative forms of the projective bundle of the standard
coordinate blowup**, in every degree `a ≥ 0` and for every `n`:

`Ω^a_{Z ×_S 𝐏^{n-1}_S / S} ≅ ⨁_{r + s = a} pr₁^*Ω^r_{Z/S} ⊗ pr₂^*Ω^s_{𝐏^{n-1}_S/S}`.

This is the opening move of the source's proof of clause (2) of [Stacks, Tag 0FUR]; the fibre
product is the source's `P` by `Stacks.DeRham.coordinateBundleProductIso`. -/
def coordinateBundleFormsProductIso (a : ℕ) :
    (⨁ Scheme.Hom.relativeFormsProductSummand (coordinateBlowupCentreToBase R m)
        (coordinateBundleAmbientToBase R n) a) ≅
      Scheme.Hom.relativeDifferentialForms
        (pullback.fst (coordinateBlowupCentreToBase R m) (coordinateBundleAmbientToBase R n) ≫
          coordinateBlowupCentreToBase R m) (a : ℤ) :=
  Scheme.Hom.relativeFormsProductIso (coordinateBlowupCentreToBase R m)
    (coordinateBundleAmbientToBase R n) a

/-- **The product decomposition of `Ω^a_{Z ×_S 𝐏^{n-1}_S / S}`, pushed forward along `p = pr₁`
termwise**, in every degree `a ≥ 0` and for every `n`. This is as far as the source's proof of
clause (2) of [Stacks, Tag 0FUR] gets without the projection formula. -/
def coordinateBundleFormsPushforwardProductIso (a : ℕ) :
    (⨁ fun j : Scheme.Hom.deRhamBoxIndex a =>
        (Scheme.Modules.pushforward (pullback.fst (coordinateBlowupCentreToBase R m)
          (coordinateBundleAmbientToBase R n))).obj
          (Scheme.Hom.relativeFormsProductSummand (coordinateBlowupCentreToBase R m)
            (coordinateBundleAmbientToBase R n) a j)) ≅
      (Scheme.Modules.pushforward (pullback.fst (coordinateBlowupCentreToBase R m)
        (coordinateBundleAmbientToBase R n))).obj
        (Scheme.Hom.relativeDifferentialForms
          (pullback.fst (coordinateBlowupCentreToBase R m)
            (coordinateBundleAmbientToBase R n) ≫ coordinateBlowupCentreToBase R m) (a : ℤ)) :=
  Scheme.Hom.relativeFormsPushforwardProductIso (coordinateBlowupCentreToBase R m)
    (coordinateBundleAmbientToBase R n) a

end Stacks.DeRham

end
