module

public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DegreeAdditivity

/-!
# Finiteness of coherent cohomology on a proper scheme over a field

For a scheme `X` proper over a field `k` and a coherent `𝒪_X`-module `F`, every cohomology
module `Hⁿ(X, F)` is a finite-dimensional `k`-vector space. This is [Stacks, Tag 02O6] over a
field base. It is **not proved here, but it is proved**, in
`StacksFrontier/AlgebraicGeometry/ProperCohomologyFinite/OverFieldProper.lean`; see the
implementation notes for where that comes from and for why this file does not import it.

That one statement was all that separated the repository from [Stacks, Tag 08AA] and
[Stacks, Tag 0AYS]. Both tags are available with a finite-dimensionality hypothesis on the two
outer terms of the short exact sequence
(`AlgebraicGeometry.eulerCharacteristic_add_of_shortExact_of_finiteDimensional'` and
`AlgebraicGeometry.curveDegree_add_of_shortExact_of_finiteDimensional`), and the point of the
single named `Prop` `AlgebraicGeometry.CohomologyFiniteDimensionalOverField` below is that
restating them with **no hypothesis beyond** it makes "discharge this one statement and both
tags follow" an `exact`. For both tags the discharge has now been carried out, in files
downstream of this one: [Stacks, Tag 08AA] is
`AlgebraicGeometry.eulerCharacteristic_add_of_shortExact` in
`StacksFrontier/AlgebraicGeometry/Variety/EulerChar/AdditivityUnconditional.lean` and
[Stacks, Tag 0AYS] is `AlgebraicGeometry.curveDegree_add_of_shortExact_of_isProper` in
`StacksFrontier/AlgebraicGeometry/Variety/Curve/DegreeAdditivityUnconditional.lean`, both
unconditional and carrying the tag. The forms below still take the `Prop` as an explicit
argument, because the proof of [Stacks, Tag 02O6] cannot be imported here; see the
implementation notes.

Also proved here, and genuinely unconditional, is that the `Prop` only ever has to be checked
in **finitely many** degrees: finite-dimensionality below the affine covering number `t(X)`
already gives it in every degree, because the cohomology vanishes from `t(X)` on.

## Main definitions

* `AlgebraicGeometry.CohomologyFiniteDimensionalOverField`: [Stacks, Tag 02O6] over a field
  base, as a `Prop`.
* `AlgebraicGeometry.CohomologyFiniteDimensionalOverFieldOn`: the same `Prop` at one fixed
  scheme proper over a field.

## Main results

* `AlgebraicGeometry.finiteDimensional_cohomologyOverField_of_forall_lt`: for a quasi-coherent
  module on a scheme proper over a field, finite-dimensionality of the cohomology in the
  degrees below the affine covering number gives it in every degree. Unconditional.
* `AlgebraicGeometry.curveDegree_add_of_shortExact`: the statement of [Stacks, Tag 0AYS],
  taking `CohomologyFiniteDimensionalOverField` as its single hypothesis.
* `AlgebraicGeometry.curveDegree_add_of_shortExact_of_cohomologyFiniteDimensional`: the same
  statement of [Stacks, Tag 0AYS] with the weaker single hypothesis
  `CohomologyFiniteDimensionalOverFieldOn`, [Stacks, Tag 02O6] for the scheme at hand. This is
  what `StacksFrontier/AlgebraicGeometry/Variety/Curve/DegreeAdditivityUnconditional.lean`
  discharges to get the tag.

## Implementation notes

**[Stacks, Tag 08AA] is not attached here.** It is attached, with no qualifier, to
`AlgebraicGeometry.eulerCharacteristic_add_of_shortExact` in
`StacksFrontier/AlgebraicGeometry/Variety/EulerChar/AdditivityUnconditional.lean`, which states the
tag with the one extra hypothesis this file used to put on it,
`CohomologyFiniteDimensionalOverField` — that is [Stacks, Tag 02O6] — supplied from
`AlgebraicGeometry.finiteDimensional_cohomologyOverField_of_isProper` rather than assumed.

**[Stacks, Tag 0AYS] is attached with no qualifier** to
`AlgebraicGeometry.curveDegree_add_of_shortExact_of_isProper` in
`StacksFrontier/AlgebraicGeometry/Variety/Curve/DegreeAdditivityUnconditional.lean`, which applies
`AlgebraicGeometry.curveDegree_add_of_shortExact_of_cohomologyFiniteDimensional` below to the
theorem `AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_isProper` rather than
assuming it. Of the two forms below, the one assuming [Stacks, Tag 02O6] for the scheme in
question keeps its own clause-qualified registration of the tag; the one assuming it for every
proper scheme over every field is left untagged, being stronger than the tag needs.

**Where the hypothesis comes from.** [Stacks, Tag 02O6] is deduced in the source from
[Stacks, Tag 02O5], coherence of the higher direct images of a coherent module under a proper
morphism, read over an affine base. In this repository that deduction is reduced losslessly to
its affine-base case by
`AlgebraicGeometry.ProperCoherentImage.higherDirectImageIsCoherent_iff_overAffineBase`, and the
affine-base case is reduced further to ideal sheaves on integral closed subschemes by
`AlgebraicGeometry.ProperCoherentImage.higherDirectImageIsCoherentOverAffineBase_of_integralIdeals`
and that reduction has two inputs: the dévissage filtration of [Stacks, Tag 01YF] and the
integral-ideal case itself, which the source obtains from Chow's lemma ([Stacks, Tag 0200])
together with coherence of the higher direct images under a projective morphism
([Stacks, Tag 02O4]). All three of those tags now have tagged declarations here:
[Stacks, Tag 01YF] in
`StacksFrontier/AlgebraicGeometry/CoherentDevissage/IdealFiltration.lean`, [Stacks, Tag 0200] in
`StacksFrontier/AlgebraicGeometry/Segre/ChartSurjective.lean`, [Stacks, Tag 02O4] in
`StacksFrontier/AlgebraicGeometry/LocallyProjectiveCoherentImage/Basic.lean`. The vocabulary they
need is this repository's own, pinned Mathlib having no ample invertible module, no relatively
ample module, no projective morphism of schemes and no twisting sheaf: ampleness is
`Stacks.Ample.IsAmple` ([Stacks, Tag 01PS]), relative ampleness is
`Stacks.RelativeAmple.IsRelativelyAmple` ([Stacks, Tag 01VH]), projectivity is
`AlgebraicGeometry.IsProjectiveMorphism` with `AlgebraicGeometry.IsLocallyProjectiveMorphism`
beside it ([Stacks, Tag 01W8]), and twisting is by the tensor powers of an invertible module
([Stacks, Tag 01CU]); the vanishing theorem [Stacks, Tag 02O4] rests on ([Stacks, Tag 02O1]) is
`Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.vanishingOverAffineBase`, and the comparison
`Hⁱ(X, F) ≅ Γ(S, Rⁱf_*F)` of [Stacks, Tag 01XK], which turns coherence of `Rⁱf_*F` over an
affine base into finiteness of `Hⁱ(X, F)`, is in
`StacksFrontier/AlgebraicGeometry/Cohomology/AffineBase.lean`. What assembles them is
`AlgebraicGeometry.ProperCoherenceWitness.moduleFinite_cohomology`, which carries
`@[stacks 02O6]` with no hypothesis, by way of the generic coherent witness of
[Stacks, Tag 01YI]; and
`AlgebraicGeometry.finiteDimensional_cohomologyOverField_of_isProper` is that result for
`S = Spec k`, in the `cohomologyOverField` spelling the Euler characteristic uses.

**Why this file does not import that proof.** Importing
`StacksFrontier/AlgebraicGeometry/ProperCohomologyFinite/OverFieldProper.lean` here would enlarge
the import closure of `StacksFrontier/AlgebraicGeometry/Variety/EulerChar/ProperPushforward.lean`,
which imports this file, and the elaboration of the Leray spectral sequence of a morphism of
schemes there then picks different universe instantiations and fails. So the statements below
keep the `Prop` as a hypothesis, and the discharged form of [Stacks, Tag 08AA] is stated in
`StacksFrontier/AlgebraicGeometry/Variety/EulerChar/AdditivityUnconditional.lean`, downstream of
both.

**Why the `Prop` quantifies over the field and the scheme.** The two consumers are applied to
one fixed `k`, `X` and `f`, but their hypotheses are about two different modules, and
[Stacks, Tag 02O6] is a statement about all of them at once; packaging it as a single closed
`Prop` is what makes "discharge this and both tags follow" a theorem rather than a remark, and
`AlgebraicGeometry.cohomologyFiniteDimensionalOverField_of_isProper` is the discharge. It is the
shape used for [Stacks, Tag 02O5] by
`AlgebraicGeometry.ProperCoherentImage.HigherDirectImageIsCoherent`.

**The coherence predicate** is the root `SheafOfModules.IsCoherent` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/CoherentFinitePresentation.lean`, which is what
`F.IsCoherent` means for `F : X.Modules`;
this branch carries a second constant of the same name under the `Stacks` namespace, so it is
written out explicitly below.

## References

* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 08AA](https://stacks.math.columbia.edu/tag/08AA)
* [Stacks Project, Tag 0AYS](https://stacks.math.columbia.edu/tag/0AYS)
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open Stacks.AlgebraicGeometry.CurveEulerBridge

namespace AlgebraicGeometry

universe u

/-- **[Stacks, Tag 02O6] over a field base.** For every field `k`, every scheme `X` proper over
`Spec k` and every coherent `𝒪_X`-module `F`, the cohomology `Hⁿ(X, F)` is a finite-dimensional
`k`-vector space in every degree.

**This is now a theorem.** It is proved by
`AlgebraicGeometry.cohomologyFiniteDimensionalOverField_of_isProper` in
`StacksFrontier/AlgebraicGeometry/Variety/EulerChar/AdditivityUnconditional.lean`, which
repackages `AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_isProper` of
`StacksFrontier/AlgebraicGeometry/ProperCohomologyFinite/OverFieldProper.lean`; that in turn is
[Stacks, Tag 02O6] itself, in the form
`AlgebraicGeometry.ProperCoherenceWitness.moduleFinite_cohomology`, with its scalars pushed
along `Γ(Spec k, ⊤) ≅ k`. The implementation notes below describe the state of affairs before
that proof existed and are superseded by it.

The `Prop` is kept, and the theorems below still take it as a named hypothesis, because the
proof cannot be imported here: this file is imported by
`StacksFrontier/AlgebraicGeometry/Variety/EulerChar/ProperPushforward.lean`, whose Leray spectral
sequence is elaborated against the locally small derived categories, while the witness files for
[Stacks, Tag 02O5] and [Stacks, Tag 02O6] put `CategoryTheory.HasDerivedCategory.standard` at
the front of instance search. Consumers that can see both discharge the hypothesis by
`exact`, as `AlgebraicGeometry.eulerCharacteristic_eq_finsum_higherDirectImage` does. -/
public def CohomologyFiniteDimensionalOverField : Prop :=
  ∀ (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)), IsProper f →
    ∀ F : X.Modules, _root_.SheafOfModules.IsCoherent F → ∀ n : ℕ,
      FiniteDimensional k (cohomologyOverField k f F n)

/-- **[Stacks, Tag 02O6] over a field base has to be checked in only finitely many degrees.**
For a quasi-coherent module on a scheme proper over a field, finite-dimensionality of the
cohomology in the degrees below the affine covering number `t(X)` already gives it in every
degree: from `t(X)` on the cohomology vanishes, by
`AlgebraicGeometry.isZero_cohomologyOverField_of_affineCoverNum_le`, and a subsingleton module
is finite-dimensional. -/
public theorem finiteDimensional_cohomologyOverField_of_forall_lt (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (F : X.Modules) [F.IsQuasicoherent]
    (h : ∀ n < X.affineCoverNum ⊤, FiniteDimensional k (cohomologyOverField k f F n)) (n : ℕ) :
    FiniteDimensional k (cohomologyOverField k f F n) := by
  rcases lt_or_ge n (X.affineCoverNum ⊤) with hn | hn
  · exact h n hn
  · have : Subsingleton (cohomologyOverField k f F n) := ModuleCat.subsingleton_of_isZero
      (isZero_cohomologyOverField_of_affineCoverNum_le k f F n hn)
    have : Finite (cohomologyOverField k f F n) := Finite.of_subsingleton
    exact Module.Finite.of_finite

/-- **[Stacks, Tag 0AYS], with [Stacks, Tag 02O6] as its single hypothesis.** For a short exact
sequence `0 ⟶ ℰ₁ ⟶ ℰ₂ ⟶ ℰ₃ ⟶ 0` of finite locally free modules of constant ranks `r₁`, `r₂`,
`r₃` on a scheme proper over a field and of dimension at most one,
`deg(ℰ₂) = deg(ℰ₁) + deg(ℰ₃)`.

This is the source's statement verbatim apart from `hfin`, which is
`AlgebraicGeometry.CohomologyFiniteDimensionalOverField`, that is [Stacks, Tag 02O6]; the
remaining inputs — additivity of the Euler characteristic and of the constant rank, and the
degenerate case of the empty scheme — are discharged inside
`AlgebraicGeometry.curveDegree_add_of_shortExact_of_finiteDimensional`. **No `@[stacks 0AYS]`
attribute is attached here**, because this form assumes [Stacks, Tag 02O6] in its global shape,
quantified over every field and every proper scheme, which is strictly more than the tag needs.
The attribute sits instead on
`AlgebraicGeometry.curveDegree_add_of_shortExact_of_cohomologyFiniteDimensional` below, whose
hypothesis is that tag for the single scheme at hand and which is therefore the stronger
statement of the two; `AlgebraicGeometry.CohomologyFiniteDimensionalOverField.on` derives this
form from it. -/
public theorem curveDegree_add_of_shortExact
    (hfin : CohomologyFiniteDimensionalOverField.{u}) (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (hdim : topologicalKrullDim X ≤ 1)
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (r₁ r₂ r₃ : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₁ r₁]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ r₂]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ r₃] :
    curveDegree k f hdim S.X₂ r₂ =
      curveDegree k f hdim S.X₁ r₁ + curveDegree k f hdim S.X₃ r₃ :=
  curveDegree_add_of_shortExact_of_finiteDimensional k f hdim S hS r₁ r₂ r₃
    (fun n _ => hfin k X f inferInstance S.X₁
      (isCoherent_of_isFiniteLocallyFreeOfRank k f S.X₁ r₁) n)
    fun n _ => hfin k X f inferInstance S.X₃
      (isCoherent_of_isFiniteLocallyFreeOfRank k f S.X₃ r₃) n

/-- **[Stacks, Tag 02O6] over a field base, at a single scheme.** Every coherent `𝒪_X`-module on
the scheme `X`, proper over the field `k` along `f`, has finite-dimensional cohomology in every
degree.

This is the content of `AlgebraicGeometry.CohomologyFiniteDimensionalOverField` for the one
morphism `f` instead of for every proper scheme over every field at once. -/
public def CohomologyFiniteDimensionalOverFieldOn (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] : Prop :=
  ∀ F : X.Modules, _root_.SheafOfModules.IsCoherent F → ∀ n : ℕ,
    FiniteDimensional k (cohomologyOverField k f F n)

/-- [Stacks, Tag 02O6] over a field base, in the form quantified over all fields and all proper
schemes, gives its form at each individual scheme proper over a field. -/
public theorem CohomologyFiniteDimensionalOverField.on
    (hfin : CohomologyFiniteDimensionalOverField.{u}) (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] : CohomologyFiniteDimensionalOverFieldOn k f :=
  fun F hF n => hfin k X f inferInstance F hF n

/-- **Additivity of the degree along a short exact sequence.** For a short exact sequence
`0 ⟶ ℰ₁ ⟶ ℰ₂ ⟶ ℰ₃ ⟶ 0` of finite locally free `𝒪_X`-modules of constant ranks `r₁`, `r₂`, `r₃`
on a scheme `X` proper over a field `k` and of dimension at most one,
`deg(ℰ₂) = deg(ℰ₁) + deg(ℰ₃)`.

The single hypothesis `hfin` is [Stacks, Tag 02O6] for `X`; everything else the source uses —
additivity of the Euler characteristic, additivity of the constant rank, and the empty
scheme — is discharged. `hfin` is now itself a theorem, so the tag is additionally registered on
the form that takes no finiteness hypothesis at all,
`AlgebraicGeometry.curveDegree_add_of_shortExact_of_isProper` of
`StacksFrontier/AlgebraicGeometry/Variety/Curve/DegreeAdditivityUnconditional.lean`, which applies
this theorem to
`AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_isProper`. -/
@[stacks 0AYS "deg(ℰ₂) = deg(ℰ₁) + deg(ℰ₃); `hfin` is [Stacks, Tag 02O6] for `X`"]
public theorem curveDegree_add_of_shortExact_of_cohomologyFiniteDimensional (k : Type u)
    [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (hfin : CohomologyFiniteDimensionalOverFieldOn k f) (hdim : topologicalKrullDim X ≤ 1)
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (r₁ r₂ r₃ : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₁ r₁]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ r₂]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ r₃] :
    curveDegree k f hdim S.X₂ r₂ =
      curveDegree k f hdim S.X₁ r₁ + curveDegree k f hdim S.X₃ r₃ :=
  curveDegree_add_of_shortExact_of_finiteDimensional k f hdim S hS r₁ r₂ r₃
    (fun n _ => hfin S.X₁ (isCoherent_of_isFiniteLocallyFreeOfRank k f S.X₁ r₁) n)
    fun n _ => hfin S.X₃ (isCoherent_of_isFiniteLocallyFreeOfRank k f S.X₃ r₃) n

end AlgebraicGeometry

end
