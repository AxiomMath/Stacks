module

public import StacksFrontier.AlgebraicGeometry.Blowup.CartierCentre
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjOfPolynomialOneVariable
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceZero
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupDifferentialFormsComparison
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.BaseChange
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineTilde
public import StacksCore.Tactic.StacksAttribute

/-!
# Direct images of differential forms along the standard coordinate blowup

Fix a ring `R`, put `S = Spec(R)` and fix integers `0 ≤ m` and `1 ≤ n`. Let

`Z = 𝐀^m_S ⟶ 𝐀^{m+n}_S = X`

be the coordinate closed immersion, let `b : L ⟶ X` be the blowing up of `X` along `Z`, and let
`P = 𝐏^{n-1}_Z` with its projection `p : P ⟶ Z`. This is the standing situation of Section 50.16
of the source, in which [Stacks, Tag 0FUR] compares differential forms upstairs and downstairs.
`StacksFrontier.AlgebraicGeometry.DeRham.BlowupDifferentialFormsComparison` sets up `S`, `X`, `L`
and `b`; this file adds the centre `Z`, the projective bundle `P` and its projection `p`, the two
canonical maps on direct images of relative differential forms

`Ω^a_{X/S} ⟶ b_*Ω^a_{L/S}` and `Ω^a_{Z/S} ⟶ p_*Ω^a_{P/S}`,

and the two clauses of the tag that assert these are isomorphisms, in the case `n = 1`.

Both maps are instances of one construction: the transpose, under `f^* ⊣ f_*`, of the canonical
map `f^*Ω^a_{X/S} ⟶ Ω^a_{Y/S}` of [Stacks, Tag 01UV] attached to a morphism `f : Y ⟶ X` of
schemes over `S`. Whenever `f` is an isomorphism that transpose is an isomorphism, and `n = 1`
is exactly the case in which both `b` and `p` are isomorphisms.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.formsDirectImageComparison`: for `f : Y ⟶ X` over `π : X ⟶ S`,
  the canonical map `Ω^d_{X/S} ⟶ f_*Ω^d_{Y/S}`.
* `Stacks.DeRham.coordinateBlowupCentre`, `Stacks.DeRham.coordinateBlowupCentreToBase`: the
  centre `Z = 𝐀^m_S = Spec R[x₁, …, x_m]` and its structure morphism to `S`.
* `Stacks.DeRham.coordinateBlowupBundle`, `Stacks.DeRham.coordinateBlowupBundleToCentre`: the
  projective bundle `P = 𝐏^{n-1}_Z` and its projection `p : P ⟶ Z`.
* `Stacks.DeRham.coordinateBlowupFormsDirectImage`: the map `Ω^a_{X/S} ⟶ b_*Ω^a_{L/S}` that
  clause (1) of the tag is about.
* `Stacks.DeRham.coordinateBundleFormsDirectImage`: the map `Ω^a_{Z/S} ⟶ p_*Ω^a_{P/S}` that
  clause (2) of the tag is about.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isIso_formsDirectImageComparison_of_isIso`: the canonical map
  `Ω^d_{X/S} ⟶ f_*Ω^d_{Y/S}` is an isomorphism when `f` is an isomorphism of schemes.
* `Stacks.DeRham.isIso_coordinateBlowupFormsDirectImage_of_one`: **clause (1) of
  [Stacks, Tag 0FUR] for `n = 1`**, in every degree `a ≥ 0`.
* `Stacks.DeRham.isIso_coordinateBundleFormsDirectImage_of_one`: **clause (2) of
  [Stacks, Tag 0FUR] for `n = 1`**, in every degree `a ≥ 0`.

## Which clauses of the tag this is, and what is not proved

The tag has three clauses, for every `a ≥ 0`: that `Ω^a_{X/S} ⟶ b_*Ω^a_{L/S}` is an isomorphism,
that `Ω^a_{Z/S} ⟶ p_*Ω^a_{P/S}` is an isomorphism, and that `Rb_*Ω^a_{L/S} ⟶ i_*Rp_*Ω^a_{P/S}`
is an isomorphism on cohomology sheaves in degrees `≥ 1`. What is proved below is the first two
clauses, in **every** degree `a`, but only in the case `n = 1`; the attribute strings say so.
This is the case the source's own proof of clause (1) disposes of first, and the case in which
clause (2) is the statement that `P` is the centre. Clause (2) at general `n` in the single
degree `a = 0` is proved in the sibling file
`StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBundleFormsDegreeZero`.

Three things are **not** proved here.

* **Clauses (1) and (2) for `n > 1`.** The source's proof of clause (2) decomposes
  `Ω^a_{P/S}` as the direct sum over `a = r + s` of `pr₁^*Ω^r_{Z/S} ⊗ pr₂^*Ω^s_{𝐏^{n-1}_S/S}`
  and pushes each summand forward by the projection formula, so that only the `s = 0` summand
  survives. That decomposition of the forms of a product is not available in the development,
  and neither is the projection formula in the shape the argument needs; the one input of the
  argument that does exist is the vanishing of the higher direct images of the twists of the
  structure sheaf of projective space
  (`StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.Vanishing`). The source's
  proof of clause (1) for `n > 1` runs through the affine blowup charts `A[A₊/yᵢ]` and the
  statement that a form on the blowup vanishing off the exceptional divisor vanishes.
  The exception is the single degree `a = 0` of clause (2), where both sides are structure
  sheaves and the assertion is `p_*𝒪_P = 𝒪_Z`. That degree *is* proved, at every `n`, in the
  sibling file `StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBundleFormsDegreeZero`: the
  degree-zero identification `AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsZeroIso`
  is shown there to be compatible with
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsMap`, so that the comparison map below
  is in degree `0` the canonical map on structure sheaves, and that map is an isomorphism
  because the direct image of the structure sheaf of projective space is the structure sheaf of
  the base. What remains unproved in clause (2) at `n > 1` is therefore the degrees `a > 0`.
* **Clause (3), in any case at all.** It is a statement about the cohomology sheaves of the right
  derived pushforwards, and the affine-local computations it rests on
  (`StacksFrontier.RingTheory.DeRham.WeightComparison`, `StacksDraft.RingTheory.DeRham`
  `.LaurentResidue`) are carried only affine-locally, by their own attribute strings; the
  Hodge cohomology of projective space it also needs
  (`StacksFrontier.AlgebraicGeometry.DeRham.ProjectiveSpaceHodgeCohomology`) is carried only
  conditionally on an undischarged filtration hypothesis.
* **The identification of `P` with the exceptional divisor `E` of the blowup.** The tag's
  Situation provides it, and clause (3) uses it; nothing below needs it, so nothing below
  asserts it.

## Implementation notes

The degree of a form is an integer in `AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms`,
while the source's `a` is a natural number bounded below by `0`. The two maps below are therefore
indexed by a natural number cast into `ℤ`, which makes the source's constraint `a ≥ 0` automatic
and the statements below genuinely quantified over every degree the tag speaks about.

`P` is `AlgebraicGeometry.projectiveSpaceOver (n-1) Z`, the fibre product of `Z` with the
integral model `𝐏^{n-1}_ℤ` over the terminal scheme. This is the source's `Z ×_S 𝐏^{n-1}_S`,
because `𝐏^{n-1}_S` is itself the base change of the integral model to `S`, and the source
identifies that fibre product with `𝐏^{n-1}_Z`. Its projection to `Z` is the canonical `Over`
structure, that is, the first projection of the fibre product.

For `n = 1` the centre is cut out on the whole of the affine scheme `X` by the single coordinate
`y₁`, which is a nonzerodivisor, so `Z ⊆ X` is an effective Cartier divisor and `b` is an
isomorphism by [Stacks, Tag 0807]. At `n = 1` the bundle is `P = 𝐏⁰_Z`, the base change of
`Proj` of a polynomial ring in one variable, which is the spectrum of its ring of coefficients
and so terminal; hence `p` is an isomorphism too. The first of those two facts is
`Stacks.DeRham.isIso_coordinateBlowupToAmbient_one`, in the ambient situation file
`StacksFrontier.AlgebraicGeometry.DeRham.BlowupDifferentialFormsComparison`, and is reused from
there rather than restated.

The adjunction unit `ℱ ⟶ f_*f^*ℱ` is an isomorphism when `f` is, because pullback along an
isomorphism is an equivalence of categories
(`AlgebraicGeometry.Scheme.Modules.isEquivalence_pullback_of_isIso`); that is reused rather than
restated.

## References

* [Stacks Project, Tag 0FUR](https://stacks.math.columbia.edu/tag/0FUR)
* [Stacks Project, Tag 0FUB](https://stacks.math.columbia.edu/tag/0FUB)
* [Stacks Project, Tag 0807](https://stacks.math.columbia.edu/tag/0807)
* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- **The canonical map `Ω^d_{X/S} ⟶ f_*Ω^d_{Y/S}`** attached to a morphism `f : Y ⟶ X` of
schemes over `π : X ⟶ S`: the transpose, under `f^* ⊣ f_*`, of the canonical map
`f^*Ω^d_{X/S} ⟶ Ω^d_{Y/S}` of [Stacks, Tag 01UV]. On sections it carries a local `d`-form on `X`
to its pullback to `Y`. -/
def formsDirectImageComparison {X Y S : Scheme.{u}} (f : Y ⟶ X) (π : X ⟶ S) (d : ℤ) :
    relativeDifferentialForms π d ⟶
      (Scheme.Modules.pushforward f).obj (relativeDifferentialForms (f ≫ π) d) :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (relativeDifferentialForms π d) ≫
    (Scheme.Modules.pushforward f).map
      (relativeDifferentialFormsMap f π (f ≫ π) (𝟙 S) (by simp) d)

/-- **Along an isomorphism the comparison map on direct images of forms is an isomorphism.** An
isomorphism of schemes is étale, so the canonical map `f^*Ω^d_{X/S} ⟶ Ω^d_{Y/S}` it is the
transpose of is an isomorphism by [Stacks, Tag 0FLV]; and the unit of `f^* ⊣ f_*` is an
isomorphism because `f^*` is then an equivalence of categories. -/
theorem isIso_formsDirectImageComparison_of_isIso {X Y S : Scheme.{u}} (f : Y ⟶ X) [IsIso f]
    (π : X ⟶ S) (d : ℤ) : IsIso (formsDirectImageComparison f π d) := by
  have hunit : IsIso
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        (relativeDifferentialForms π d)) := inferInstance
  have hmap : IsIso (relativeDifferentialFormsMap f π (f ≫ π) (𝟙 S) (by simp) d) :=
    isIso_relativeDifferentialFormsMap_of_etale f π (f ≫ π) (𝟙 S) (by simp) d
  rw [formsDirectImageComparison]
  infer_instance

end AlgebraicGeometry.Scheme.Hom

namespace Stacks.DeRham

variable (R : Type u) [CommRing R] (m n : ℕ)

/-! ### The centre and the projective bundle -/

/-- The centre `Z = 𝐀^m_S = Spec R[x₁, …, x_m]` of the standard coordinate blowup. -/
abbrev coordinateBlowupCentre : Scheme.{u} := Spec (.of (MvPolynomial (Fin m) R))

/-- The structure morphism `Z ⟶ S` of the centre of the standard coordinate blowup. -/
abbrev coordinateBlowupCentreToBase : coordinateBlowupCentre R m ⟶ coordinateBase R :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin m) R))

/-- The projective bundle `P = 𝐏^{n-1}_Z = Z ×_S 𝐏^{n-1}_S` of the standard coordinate
blowup. -/
abbrev coordinateBlowupBundle : Scheme.{u} :=
  AlgebraicGeometry.projectiveSpaceOver (n - 1) (coordinateBlowupCentre R m)

/-- The projection `p : P ⟶ Z` of the projective bundle onto the centre of the blowup. -/
abbrev coordinateBlowupBundleToCentre :
    coordinateBlowupBundle R m n ⟶ coordinateBlowupCentre R m :=
  (AlgebraicGeometry.projectiveSpaceOver.over (n - 1) (coordinateBlowupCentre R m)).hom

/-! ### The two canonical maps on direct images of differential forms -/

/-- **The map of clause (1) of [Stacks, Tag 0FUR].** The canonical map
`Ω^a_{X/S} ⟶ b_*Ω^a_{L/S}` attached to the blowing-up morphism `b : L ⟶ X` of the standard
coordinate blowup. -/
abbrev coordinateBlowupFormsDirectImage (a : ℕ) :
    Scheme.Hom.relativeDifferentialForms (coordinateAmbientToBase R m n) (a : ℤ) ⟶
      (Scheme.Modules.pushforward (coordinateBlowupToAmbient R m n)).obj
        (Scheme.Hom.relativeDifferentialForms
          (coordinateBlowupToAmbient R m n ≫ coordinateAmbientToBase R m n) (a : ℤ)) :=
  Scheme.Hom.formsDirectImageComparison (coordinateBlowupToAmbient R m n)
    (coordinateAmbientToBase R m n) (a : ℤ)

/-- **The map of clause (2) of [Stacks, Tag 0FUR].** The canonical map
`Ω^a_{Z/S} ⟶ p_*Ω^a_{P/S}` attached to the projection `p : P ⟶ Z` of the projective bundle of
the standard coordinate blowup onto its centre. -/
abbrev coordinateBundleFormsDirectImage (a : ℕ) :
    Scheme.Hom.relativeDifferentialForms (coordinateBlowupCentreToBase R m) (a : ℤ) ⟶
      (Scheme.Modules.pushforward (coordinateBlowupBundleToCentre R m n)).obj
        (Scheme.Hom.relativeDifferentialForms
          (coordinateBlowupBundleToCentre R m n ≫ coordinateBlowupCentreToBase R m) (a : ℤ)) :=
  Scheme.Hom.formsDirectImageComparison (coordinateBlowupBundleToCentre R m n)
    (coordinateBlowupCentreToBase R m) (a : ℤ)

/-! ### The case `n = 1`: both `b` and `p` are isomorphisms -/

section OneCoordinate

open MvPolynomial Stacks.MoreMorphisms

/-- **`𝐏⁰` over the integers is a terminal scheme.** `Proj` of a graded polynomial ring in one
variable is the spectrum of its ring of coefficients, and the spectrum of `ULift ℤ` is
terminal. -/
theorem isIso_terminalFrom_projectiveSpaceAtUniverse_of_zero :
    IsIso (terminal.from (AlgebraicGeometry.projectiveSpaceAtUniverse.{u} 0)) := by
  have hspec : IsIso (terminal.from (Spec (.of (ULift.{u} ℤ)))) :=
    isIso_of_isTerminal specULiftZIsTerminal terminalIsTerminal _
  have e : AlgebraicGeometry.projectiveSpaceAtUniverse.{u} 0 ≅ Spec (.of (ULift.{u} ℤ)) :=
    AlgebraicGeometry.ProjectiveSpace.oneVariableProjIsoSpec (ULift.{u} ℤ)
  have hcomp : terminal.from (AlgebraicGeometry.projectiveSpaceAtUniverse.{u} 0) =
      e.hom ≫ terminal.from (Spec (.of (ULift.{u} ℤ))) := terminal.hom_ext _ _
  rw [hcomp]
  infer_instance

/-- **For `n = 1` the projection `p : P ⟶ Z` is an isomorphism**: the bundle `P = 𝐏⁰_Z` is the
base change of a terminal scheme along the structure morphism of `Z`, so the projection is a
pullback of an isomorphism. This is
`AlgebraicGeometry.projectiveSpaceOver.isIso_zero_over` at the centre of the standard coordinate
blowup. -/
theorem isIso_coordinateBlowupBundleToCentre_of_one :
    IsIso (coordinateBlowupBundleToCentre R m 1) :=
  AlgebraicGeometry.projectiveSpaceOver.isIso_zero_over (coordinateBlowupCentre R m)

/-- **[Stacks, Tag 0FUR], clause (1), in the case `n = 1`.** The canonical map
`Ω^a_{X/S} ⟶ b_*Ω^a_{L/S}` is an isomorphism in every degree `a ≥ 0`, because for `n = 1` the
centre of the blowup is an effective Cartier divisor and so `b` is an isomorphism. This is the
case the source's own proof of clause (1) disposes of first. -/
@[stacks 0FUR "clause (1) for n = 1, in every degree a ≥ 0; n > 1 is not proved"]
theorem isIso_coordinateBlowupFormsDirectImage_of_one (a : ℕ) :
    IsIso (coordinateBlowupFormsDirectImage R m 1 a) :=
  have := isIso_coordinateBlowupToAmbient_one R m
  Scheme.Hom.isIso_formsDirectImageComparison_of_isIso _ _ _

/-- **[Stacks, Tag 0FUR], clause (2), in the case `n = 1`.** The canonical map
`Ω^a_{Z/S} ⟶ p_*Ω^a_{P/S}` is an isomorphism in every degree `a ≥ 0`, because for `n = 1` the
projective bundle `P = 𝐏⁰_Z` is the centre itself. -/
@[stacks 0FUR "clause (2) for n = 1, in every degree a ≥ 0; at general n only the single degree \
a = 0 is proved, by Stacks.DeRham.isIso_coordinateBundleFormsDirectImage_zero in \
StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBundleFormsDegreeZero; the degrees a > 0 at \
general n are not proved"]
theorem isIso_coordinateBundleFormsDirectImage_of_one (a : ℕ) :
    IsIso (coordinateBundleFormsDirectImage R m 1 a) :=
  have := isIso_coordinateBlowupBundleToCentre_of_one R m
  Scheme.Hom.isIso_formsDirectImageComparison_of_isIso _ _ _

end OneCoordinate

end Stacks.DeRham

end
