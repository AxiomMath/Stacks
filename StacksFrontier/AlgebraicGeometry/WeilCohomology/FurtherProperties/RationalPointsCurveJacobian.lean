module

public import StacksFrontier.AlgebraicGeometry.Curves.NodalUnramifiedSingularSubscheme
public import
  StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.SeparablyClosedDivisiblePoints
public import StacksFrontier.AlgebraicGeometry.Picard.CurveChowZeroDivisor
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeSmoothness
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ReducedConnected
public import
  StacksFrontier.AlgebraicGeometry.WeilCohomology.FurtherProperties.RationalPointsDimensionInduction
public import StacksFrontier.RingTheory.GeometricallyIntegral.Defs
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The curve case of Stacks Tag 0FH7

Let `k` be a separably closed field and let `n` be an integer invertible in `k`. This file proves
the base case of the induction of Stacks Tag 0FH7: for every proper smooth geometrically
irreducible `k`-scheme `X` of dimension one and every pair `x, x'` of `k`-rational points of `X`,
the class `[x] - [x']` is `n` times a class of `CH_0(X)`. That is
`Stacks.WeilCohomology.RationalPointDifferenceDivisible k n 1`, exactly what
`Stacks.WeilCohomology.rationalPointDifferenceDivisible_of_dimOne` asks for as its hypothesis
`hcurve`.

The argument is the source's. The class `[x] - [x']` is the image under
`AlgebraicGeometry.curvePicardToChowZero` of the degree-zero Picard class of
`𝒪_X(x) ⊗ 𝒪_X(x')^{-1}`, which is
`AlgebraicGeometry.exists_curvePicardToChowZero_eq_rationalPointChowClass_sub`. The degree-zero
Picard group is the group of `k`-rational points of the Jacobian, an abelian variety, and a
`k`-rational point of an abelian variety over a separably closed field is `[n]` of a `k`-rational
point, which is `Stacks.Groupoids.exists_comp_zpow_id_left_eq_of_isSepClosed`. Applying the
homomorphism `Pic(X) ⟶ CH_0(X)` to the resulting equation finishes.

## Main definitions

* `Stacks.WeilCohomology.JacobianParametrization` — the Jacobian input, at one curve: an abelian
  variety `A` over `k` and a map from its `k`-rational points onto the degree-zero part of
  `Pic(X)` that turns `[n]` into multiplication by `n`. **Unproved in this library**; the section
  below says why.
* `Stacks.WeilCohomology.HasJacobianParametrizations` — the same for every curve at once, which is
  the shape the base case consumes.

## Main results

* `Stacks.Curves.smoothOfRelativeDimension_one_of_topologicalKrullDim_eq_one` — a smooth
  geometrically irreducible `k`-scheme of topological dimension one is smooth of relative
  dimension one.
* `Stacks.WeilCohomology.isAbelianVariety_grpTrivial` — the trivial group scheme over `k` is an
  abelian variety.
* `Stacks.WeilCohomology.jacobianParametrization_of_degreeZero_trivial` — the Jacobian input holds
  on a curve whose degree-zero Picard group is trivial, so it is **satisfiable** and not a disguise
  for `False`.
* `Stacks.WeilCohomology.curveHasOneDimensionalSections` — a proper smooth geometrically
  irreducible `k`-scheme has `dim_k H^0(X, 𝒪_X) = 1`, from clause (7) of Stacks Tag 0BUG.
* `Stacks.WeilCohomology.rationalPointDifferenceDivisible_one` — the curve case.

`Stacks.Curves.smoothOfRelativeDimension_one_of_topologicalKrullDim_eq_one` and
`Stacks.WeilCohomology.curveHasOneDimensionalSections` are the two halves of the passage from the
description of a curve by smoothness and dimension one to the description the Picard machinery of
this library is stated for; the section below on that passage says how each is proved. Neither is
a hypothesis of anything any more.

## The carried hypotheses, what each asserts, and where each is consumed

Two hypotheses are carried beyond those of Stacks Tag 0FH7. Neither is proved in this
library; each is consumed exactly once in
`Stacks.WeilCohomology.rationalPointDifferenceDivisible_one`.

### `HasJacobianParametrizations k n`: the Jacobian as a variety

This is the content of Stacks Tag 0BA0, that the degree-zero Picard group `Pic⁰(X)` of a smooth
proper curve is the group of `k`-points of an abelian variety. **No declaration of that tag exists
in any build target of this repository** — searching by conclusion shape rather than by name, there
is no equivalence, isomorphism or bijection anywhere in `StacksCore/` or
`StacksFrontier/AlgebraicGeometry/` between a Picard group and a type of sections of a group scheme,
and no `CategoryTheory.GrpObj` or `AlgebraicGeometry.IsAbelianVariety` instance whose subject is
built from a Picard functor or Picard scheme. The only representability machinery present,
`AlgebraicGeometry.exists_grp_iso_of_representable_openSubfunctor`, is a criterion for an abstract
group-valued functor that nothing in the repository imports, let alone applies to the Picard
functor.

It is stated at the weakest form the proof below actually uses, which is considerably weaker than
Tag 0BA0:

* the map `φ` from `k`-points of `A` to `Pic(X)` is an arbitrary function, not a group
  homomorphism, and no injectivity is asked of it — so this is not an isomorphism
  `Pic⁰(X) ≅ A(k)`, only a parametrization;
* `φ` is required to hit the degree-zero classes only, not all of `Pic(X)`;
* the group law of `A` enters only through one identity, `φ (g' ∘ [n]) = n • φ g'`, and only at
  the integer `n` in question and only for `g, g'` that are sections of the structure morphism;
* the abelian variety is not asked to be the Jacobian, to have dimension the genus, or to be
  related to `X` in any other way.

It is consumed to produce the abelian variety, the point `g` above the degree-zero class, and the
equation that turns the group-side divisibility into divisibility in `Pic(X)`.

`Stacks.WeilCohomology.jacobianParametrization_of_degreeZero_trivial` discharges it on a curve
whose degree-zero Picard group is trivial, taking `A` to be the trivial group scheme — shown to be
an abelian variety by `Stacks.WeilCohomology.isAbelianVariety_grpTrivial` — and `φ` the zero map.
So the hypothesis has a model and is not vacuous.

### `Stacks.Groupoids.EtaleZPowIdOfIsUnit`: the étale clause of Stacks Tag 03RP

Multiplication by an integer invertible in `k` is étale on an abelian variety. This is already
disclosed upstream, at `Stacks.Groupoids.EtaleZPowIdOfIsUnit`, and is carried here in exactly that
form rather than re-disclosed: it is the hypothesis `h03RP`, quantified over the abelian varieties
the Jacobian input produces, and it is handed straight to
`Stacks.Groupoids.exists_comp_zpow_id_left_eq_of_isSepClosed`, which is where it is spent. The
reason it is open there — that
`Stacks.Groupoids.etale_zpow_id_iff_isUnit_intCast_iff_forall_two_le` is a self-reduction carrying
its own conclusion for `n ≥ 2`, and
`Stacks.Groupoids.etale_zpow_id_iff_isUnit_intCast_of_natAbs_le_one` settles only
`d ∈ {0, 1, -1}` — is recorded at its own declaration.

## The passage to the Picard machinery's description of a curve, both halves proved

`Stacks.WeilCohomology.RationalPointDifferenceDivisible` describes its curve as proper, smooth and
geometrically irreducible over `k` with `topologicalKrullDim X = 1`. The Picard and degree
machinery of this library — `AlgebraicGeometry.invertibleCurveDegreeHom`,
`AlgebraicGeometry.curvePicardToChowZero` and
`AlgebraicGeometry.exists_curvePicardToChowZero_eq_rationalPointChowClass_sub` — instead describes
its curve by `AlgebraicGeometry.SmoothOfRelativeDimension 1 f` and by
`Module.finrank k (AlgebraicGeometry.structureSheafCohomology f 0) = 1`. The two descriptions agree
mathematically, and both halves of the passage are now proved here, so neither costs a hypothesis.
Each is used once, to build the instance and to supply the hypothesis that the Chow/Picard
identification demands.

* The relative dimension is **proved** by
  `Stacks.Curves.smoothOfRelativeDimension_one_of_topologicalKrullDim_eq_one`: a morphism smooth
  at `x` is standard smooth on a neighbourhood of `x`, Stacks Tag 01V9 (1) implies (5), and the
  relative dimension of that presentation is the fibre dimension at `x`, Stacks Tag 02G1; over a
  field the fibre at the only point of the base is `X` itself. The three facts that chain
  into it are named at that declaration.
* The sections statement is **proved** by
  `Stacks.WeilCohomology.curveHasOneDimensionalSections`, from clause (7) of Stacks Tag 0BUG as
  `Stacks.AlgebraicGeometry.ProperSectionsGeom.isIso_globalSections_of_isProper` has it: a proper,
  geometrically reduced, geometrically connected scheme over `k` has `k` for its ring of global
  functions. A smooth morphism is geometrically reduced
  (`AlgebraicGeometry.geometricallyReduced_of_smooth`, Stacks Tag 056T) and a geometrically
  irreducible one is geometrically connected, which supplies the two hypotheses of that clause;
  `AlgebraicGeometry.structureSheafCohomologyIsoCohomologyOverField` and
  `AlgebraicGeometry.finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections` turn the
  resulting ring isomorphism into the `k`-dimension statement. The dimension of `X` is not used.

Neither half is stated as a hypothesis-shaped `Prop` definition quantified over all curves, as
both were while they were hypotheses. Once the thing such a definition asserts is proved, its only
remaining role is to be the statement of its own proof, which is a wrapper; and the quantified
shape is narrower than what is proved, since it asks for properness, which the relative-dimension
half does not need, and for dimension one, which the sections half does not need. The two theorems
are stated at their own hypotheses instead.

## What is *not* assumed

Projectivity is not assumed, only properness, which is weaker than Stacks Tag 0FH7's hypothesis
and so makes the result stronger. Integrality of `X` is not assumed; the Picard results used
recover it from the sections condition through
`AlgebraicGeometry.GenusOne.isIntegral`. No genus hypothesis appears.

## Implementation notes

The abelian variety is carried as a bundled `CategoryTheory.Grp (Over (Spec (.of k)))` rather than
as an object of `Over (Spec (.of k))` together with a separate `CategoryTheory.GrpObj` field, so
that the group-object structure travels with it through the existential quantifier and the `zpow`
notation `(𝟙 A.X) ^ n` elaborates without a `letI`.

Multiplication by `n` is written as the source writes it, `(𝟙 A : A ⟶ A) ^ n` in the group
`A ⟶ A` of `CategoryTheory.MonObj`, and its action on a point is composition on the left. No group
structure is placed on the set of `k`-rational points: this library has none, and the one identity
the proof needs is stated directly in terms of that composition.

No `@[stacks]` attribute is attached anywhere in this file. In particular Stacks Tag 0FH7 is not
registered: the results below carry two hypotheses the tag does not, so a registration would
assert something that is not proved. Stacks Tag 0BA0 is not registered either, for the stronger
reason that nothing here proves any part of it. Stacks Tag 0BUG is not registered on
`Stacks.WeilCohomology.curveHasOneDimensionalSections` either: that declaration is a corollary of
the tag's clause (7) at narrower hypotheses — smooth and geometrically irreducible, over a field —
so the registration belongs where it already is, on
`Stacks.AlgebraicGeometry.ProperSectionsGeom.isIso_globalSections_of_isProper` for clause (7) and
on `AlgebraicGeometry.isIso_globalSections_of_geometricallyIntegral` for clause (8). Stacks Tags
01V9 and 02G1 are likewise left where they are rather than moved onto
`Stacks.Curves.smoothOfRelativeDimension_one_of_topologicalKrullDim_eq_one`, for the reason given
at that declaration.

## References

* [Stacks Project, Tag 01V9](https://stacks.math.columbia.edu/tag/01V9)
* [Stacks Project, Tag 02G1](https://stacks.math.columbia.edu/tag/02G1)
* [Stacks Project, Tag 03RP](https://stacks.math.columbia.edu/tag/03RP)
* [Stacks Project, Tag 056T](https://stacks.math.columbia.edu/tag/056T)
* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
* [Stacks Project, Tag 0FH7](https://stacks.math.columbia.edu/tag/0FH7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Stacks.Chow
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Curves

/-! ### Relative dimension one from smoothness and dimension one -/

/-- **A smooth geometrically irreducible scheme of dimension one over a field is smooth of
relative dimension one.** This is the passage from the description of a curve by smoothness
together with `topologicalKrullDim X = 1` to the indexed class
`AlgebraicGeometry.SmoothOfRelativeDimension 1 f` that the Picard and degree machinery of this
library is stated for.

Geometric irreducibility over the one-point base `Spec k` makes `X` irreducible, hence
equidimensional, so `Stacks.Curves.relativeDimension_one_of_equidimensional` turns the dimension
of `X` into relative dimension one of `f` in the sense of Stacks Tag 02NJ, the unique fibre over
a field being `X` itself. `AlgebraicGeometry.topologicalKrullDimAt_fiber_eq_of_relativeDimension`,
applied at the whole of `X` as the open subscheme, reads that off as the fibre dimension at every
point of `X`, which is how Stacks Tag 02G1 describes the relative dimension of a smooth
morphism. Finally `Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq` upgrades a
smooth morphism with constant fibre dimension to one of that relative dimension, its own proof
going through the standard smooth presentation of Stacks Tag 01V9, clause (1) implies clause (5).

Properness is not needed, and geometric irreducibility is used only through equidimensionality
of `X`.

No Stacks tag is registered here: the statement is an application of Stacks Tags 01V9 and 02G1 at
dimension one over a field, not either tag's own statement, and both are already registered in
this library — 01V9 on `Stacks.Tag01V9NumericalCriterion.smoothAt_tfae` and 02G1 on
`AlgebraicGeometry.finrank_stalk_relativeDifferentials_eq_fiberDimensionAt`. -/
theorem smoothOfRelativeDimension_one_of_topologicalKrullDim_eq_one (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f] [GeometricallyIrreducible f]
    (hdim : topologicalKrullDim X = ((1 : ℕ) : WithBot ℕ∞)) :
    SmoothOfRelativeDimension 1 f := by
  have : Subsingleton (Spec (CommRingCat.of k)) := by
    show Subsingleton (PrimeSpectrum k); infer_instance
  have : IrreducibleSpace X := GeometricallyIrreducible.irreducibleSpace_of_subsingleton f
  have hrel : RelativeDimension f 1 :=
    relativeDimension_one_of_equidimensional k f
      (TopologicalSpace.Equidimensional.of_preirreducibleSpace X) (by rw [hdim]; norm_num)
  refine Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq f 1 fun x => ?_
  exact topologicalKrullDimAt_fiber_eq_of_relativeDimension f ⊤ 1
    (RelativeDimension.comp_isOpenImmersion (⊤ : X.Opens).ι f hrel) x trivial

end Stacks.Curves

namespace Stacks.WeilCohomology

/-! ### The trivial group scheme is an abelian variety -/

/-- **A field is geometrically integral over itself.** The identity of `Spec k` is geometrically
integral, because `k ⊗_k k'` is `k'`, a field, for every field extension `k'/k`. -/
theorem geometricallyIntegral_id (k : Type u) [Field k] :
    GeometricallyIntegral (𝟙 (Spec (CommRingCat.of k))) := by
  have h : Algebra.IsGeometricallyIntegral k k :=
    (Algebra.isGeometricallyIntegral_iff_isDomain_tensorProduct k k).2 fun k' _ _ =>
      (Algebra.TensorProduct.lid k k').toRingEquiv.isDomain_iff.mpr inferInstance
  have e : Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 (Spec (CommRingCat.of k)) := by
    simp
  rwa [Algebra.IsGeometricallyIntegral, e] at h

/-- **The trivial group scheme over a field is an abelian variety.** Its structure morphism is the
identity of `Spec k`, which is proper, separated, locally of finite type and quasi-compact with
integral — indeed geometrically integral — source. This is what makes the degenerate witness
`Stacks.WeilCohomology.jacobianParametrization_of_degreeZero_trivial` available, and with it the
non-vacuity of `Stacks.WeilCohomology.JacobianParametrization`. -/
theorem isAbelianVariety_grpTrivial (k : Type u) [Field k] :
    AlgebraicGeometry.IsAbelianVariety k
      (CategoryTheory.Grp.trivial (Over (Spec (CommRingCat.of k)))).X := by
  set T := (CategoryTheory.Grp.trivial (Over (Spec (CommRingCat.of k)))).X
  have : IsProper T.hom := (inferInstance : IsProper (𝟙 (Spec (CommRingCat.of k))))
  have : IsSeparated T.hom := (inferInstance : IsSeparated (𝟙 (Spec (CommRingCat.of k))))
  have : LocallyOfFiniteType T.hom :=
    (inferInstance : LocallyOfFiniteType (𝟙 (Spec (CommRingCat.of k))))
  have : QuasiCompact T.hom := (inferInstance : QuasiCompact (𝟙 (Spec (CommRingCat.of k))))
  have : IsIntegral T.left := (inferInstance : IsIntegral (Spec (CommRingCat.of k)))
  have : GeometricallyIntegral T.hom := geometricallyIntegral_id k
  have : AlgebraicGeometry.IsVariety k T.hom := ⟨⟩
  have : AlgebraicGeometry.IsProperVariety k T.hom := ⟨⟩
  exact ⟨⟩

/-! ### The Jacobian input -/

/-- **The Jacobian of Stacks Tag 0BA0, at the weakest form the curve case uses.**
`JacobianParametrization k n f hdim` says: there is an abelian variety `A` over `k` and a map `φ`
from the morphisms `Spec k ⟶ A` to `Pic(X)` such that

* every class of `Pic(X)` of degree zero is `φ g` for some `k`-rational point `g` of `A`, and
* `φ g = n • φ g'` whenever `g, g'` are `k`-rational points of `A` with `g' ∘ [n] = g`,

where `[n]` is multiplication by `n`, the `n`-th power `(𝟙 A : A ⟶ A) ^ n` of the identity in the
group of endomorphisms of the group object `A`.

This is the half of Stacks Tag 0BA0 that the proof of Stacks Tag 0FH7 cites, weakened in every way
the proof allows: `φ` is a bare function rather than a group isomorphism `Pic⁰(X) ≅ A(k)`, it is
asked to be surjective only onto the degree-zero classes, the group law of `A` is used only through
the displayed identity at the single integer `n`, and `A` is not required to be the Jacobian of `X`
or to be related to `X` at all.

**No declaration of this library proves it**, and the reason is that the Jacobian is absent as a
*variety*: the degree-zero Picard group exists here only as the `AddSubgroup`
`(AlgebraicGeometry.invertibleCurveDegreeHom k f hdim).ker`, no group-scheme structure is attached
to any Picard object anywhere in the build targets, and the one representability criterion present,
`AlgebraicGeometry.exists_grp_iso_of_representable_openSubfunctor`, is never applied — nothing even
imports it.

`Stacks.WeilCohomology.jacobianParametrization_of_degreeZero_trivial` shows the statement is
satisfiable. -/
def JacobianParametrization (k : Type u) [Field k] (n : ℤ) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (hdim : topologicalKrullDim X ≤ 1) : Prop :=
  ∃ (A : CategoryTheory.Grp (Over (Spec (.of k))))
      (_ : AlgebraicGeometry.IsAbelianVariety k A.X)
      (φ : (Spec (.of k) ⟶ A.X.left) → Stacks.Picard.ofScheme X),
    (∀ c : Stacks.Picard.ofScheme X, invertibleCurveDegreeHom k f hdim c = 0 →
        ∃ g : Spec (.of k) ⟶ A.X.left, g ≫ A.X.hom = 𝟙 (Spec (.of k)) ∧ φ g = c) ∧
      ∀ g g' : Spec (.of k) ⟶ A.X.left, g ≫ A.X.hom = 𝟙 (Spec (.of k)) →
        g' ≫ A.X.hom = 𝟙 (Spec (.of k)) →
        g' ≫ ((𝟙 A.X : A.X ⟶ A.X) ^ n).left = g → φ g = n • φ g'

/-- **The Jacobian input is satisfiable.** On a proper scheme of dimension at most one whose
degree-zero Picard classes are all zero — a rational curve, for instance — the hypothesis
`Stacks.WeilCohomology.JacobianParametrization` holds: take `A` to be the trivial group scheme
over `k`, an abelian variety by `Stacks.WeilCohomology.isAbelianVariety_grpTrivial`, and `φ` the
zero map. Surjectivity onto the degree-zero classes is then the triviality hypothesis at the point
`𝟙 (Spec k)`, and the compatibility with `[n]` is `n • 0 = 0`.

So the disclosed hypothesis has a model and is not an unprovable statement in disguise. -/
theorem jacobianParametrization_of_degreeZero_trivial (k : Type u) [Field k] (n : ℤ)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (hdim : topologicalKrullDim X ≤ 1)
    (hker : ∀ c : Stacks.Picard.ofScheme X, invertibleCurveDegreeHom k f hdim c = 0 → c = 0) :
    JacobianParametrization k n f hdim :=
  ⟨CategoryTheory.Grp.trivial (Over (Spec (.of k))), isAbelianVariety_grpTrivial k, fun _ => 0,
    fun c hc => ⟨(𝟙 (Spec (.of k)) :
      Spec (.of k) ⟶ (CategoryTheory.Grp.trivial (Over (Spec (.of k)))).X.left),
      Category.id_comp _, (hker c hc).symm⟩,
    fun _ _ _ _ _ => by rw [smul_zero]⟩

/-- **The Jacobian input, for every curve over `k` at once.** This is the shape
`Stacks.WeilCohomology.rationalPointDifferenceDivisible_one` consumes, the curve case being
quantified over all curves. See `Stacks.WeilCohomology.JacobianParametrization` for what it
asserts, why no declaration of this library proves it, and why it is not vacuous. -/
def HasJacobianParametrizations (k : Type u) [Field k] (n : ℤ) : Prop :=
  ∀ {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [Smooth f]
    [GeometricallyIrreducible f] (hdim : topologicalKrullDim X ≤ 1),
    JacobianParametrization k n f hdim

/-! ### The sections of a proper smooth geometrically irreducible scheme -/

/-- **The global functions on a proper smooth geometrically irreducible `k`-scheme are the
constants.** This is the second half of the passage from the description of a curve used by
`Stacks.WeilCohomology.RationalPointDifferenceDivisible` to the one used by the Picard machinery of
this library, where it is the hypothesis called `h0`.

This is clause (7) of Stacks Tag 0BUG,
`Stacks.AlgebraicGeometry.ProperSectionsGeom.isIso_globalSections_of_isProper`, at the two
hypotheses the smooth geometrically irreducible case supplies: geometric reducedness is
`AlgebraicGeometry.geometricallyReduced_of_smooth` (Stacks Tag 056T), and geometric connectedness
follows from geometric irreducibility because every base change of `f` to a field then has an
irreducible, hence connected, underlying space. That clause gives the ring statement, that
`k ⟶ Γ(X, 𝒪_X)` is an isomorphism; the `k`-dimension statement is read off it through
`AlgebraicGeometry.structureSheafCohomologyIsoCohomologyOverField` in degree zero and
`AlgebraicGeometry.finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections`.

No dimension hypothesis appears: `dim_k H^0(X, 𝒪_X) = 1` holds in every dimension, so the
statement is left at the hypotheses its proof uses rather than at the dimension-one shape
`Stacks.WeilCohomology.RationalPointDifferenceDivisible` hands on. -/
@[sga "1 IX 6.1" "special case", sga "7 X 1.13" "H^0(Y,O_Y)=k"]
theorem curveHasOneDimensionalSections (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [Smooth f] [GeometricallyIrreducible f] :
    Module.finrank k (structureSheafCohomology f 0) = 1 := by
  have : GeometricallyReduced f := geometricallyReduced_of_smooth f
  have : GeometricallyConnected f := by
    rw [GeometricallyConnected.eq_geometrically]
    intro K _ y Z fst snd hpull
    have : IrreducibleSpace Z :=
      GeometricallyIrreducible.geometrically_irreducibleSpace y fst snd hpull
    infer_instance
  have hiso : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) :=
    Stacks.AlgebraicGeometry.ProperSectionsGeom.isIso_globalSections_of_isProper k f
  let : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  have hbij : Function.Bijective (algebraMap k Γ(X, ⊤)) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact ConcreteCategory.bijective_of_isIso _
  rw [(structureSheafCohomologyIsoCohomologyOverField k f 0).toLinearEquiv.finrank_eq,
    finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections k f,
    ← (AlgEquiv.ofBijective (Algebra.ofId k Γ(X, ⊤)) hbij).toLinearEquiv.finrank_eq,
    Module.finrank_self]

/-! ### The curve case -/

/-- **The base case of the induction of Stacks Tag 0FH7: the difference of two rational points on a
curve is divisible by `n`.** Let `k` be separably closed and let `n` be invertible in `k`. Then for
every proper smooth geometrically irreducible `k`-scheme `X` of dimension one and every pair of
`k`-rational points `x, x'` of `X`, the class `[x] - [x']` of `CH_0(X)` is `n` times a class.

This is `Stacks.WeilCohomology.RationalPointDifferenceDivisible k n 1`, which is what
`Stacks.WeilCohomology.rationalPointDifferenceDivisible_of_dimOne` takes as its hypothesis
`hcurve`.

The proof is the source's. The identification
`AlgebraicGeometry.exists_curvePicardToChowZero_eq_rationalPointChowClass_sub`
exhibits `[x] - [x']` as the image of a degree-zero Picard class `c` under
`AlgebraicGeometry.curvePicardToChowZero`; the Jacobian input writes `c` as `φ g` for a
`k`-rational point `g` of an abelian variety `A`;
`Stacks.Groupoids.exists_comp_zpow_id_left_eq_of_isSepClosed` writes `g` as `g' ∘ [n]`; the
Jacobian input's second clause turns that into `c = n • φ g'`; and
`AlgebraicGeometry.curvePicardToChowZero`, being additive, carries it to
`[x] - [x'] = n • (c₁(φ g') ∩ [X]_1)`.

Neither half of the passage to the Picard machinery's description of a curve costs a hypothesis.
The instance `AlgebraicGeometry.SmoothOfRelativeDimension 1 f` is built from smoothness and the
dimension by `Stacks.Curves.smoothOfRelativeDimension_one_of_topologicalKrullDim_eq_one`, which
proves it from Stacks Tags 01V9 and 02G1; the hypothesis `h0` of the Chow/Picard identification is
supplied by `Stacks.WeilCohomology.curveHasOneDimensionalSections`, which proves it from clause
(7) of Stacks Tag 0BUG.

Two hypotheses beyond those of Stacks Tag 0FH7 are carried, and each is used exactly once:

* `h03RP`, the étale clause `Stacks.Groupoids.EtaleZPowIdOfIsUnit` of Stacks Tag 03RP, disclosed
  upstream and propagated unchanged, is consumed by
  `Stacks.Groupoids.exists_comp_zpow_id_left_eq_of_isSepClosed`;
* `hJac : Stacks.WeilCohomology.HasJacobianParametrizations k n`, which would be discharged by
  Stacks Tag 0BA0, is consumed to produce the abelian variety, the point over the degree-zero
  class, and the divisibility in `Pic(X)`.

The two hypotheses of the source, that `k` is separably closed and that `n` is invertible in `k`,
are spent exactly where the source spends them: both inside
`Stacks.Groupoids.exists_comp_zpow_id_left_eq_of_isSepClosed`, the first on the existence of a
rational point of a nonempty étale `k`-scheme and the second on the étaleness of multiplication
by `n`. -/
theorem rationalPointDifferenceDivisible_one (k : Type u) [Field k] [IsSepClosed k] (n : ℤ)
    (hn : IsUnit ((n : ℤ) : k))
    (h03RP : ∀ (A : Over (Spec (.of k))) [CategoryTheory.GrpObj A]
      [AlgebraicGeometry.IsAbelianVariety k A], Stacks.Groupoids.EtaleZPowIdOfIsUnit k A)
    (hJac : HasJacobianParametrizations k n) :
    RationalPointDifferenceDivisible k n 1 := by
  unfold RationalPointDifferenceDivisible
  intro X f _ _ _ hdim x x' hx hx'
  have hdimle : topologicalKrullDim X ≤ 1 := by rw [hdim]; norm_num
  have : SmoothOfRelativeDimension 1 f :=
    Stacks.Curves.smoothOfRelativeDimension_one_of_topologicalKrullDim_eq_one k f hdim
  obtain ⟨c, hdeg, hc⟩ := exists_curvePicardToChowZero_eq_rationalPointChowClass_sub k f hdimle
    (curveHasOneDimensionalSections k f) x x' hx hx'
  obtain ⟨A, hAV, φ, hsurj, hcompat⟩ := hJac f hdimle
  have := hAV
  obtain ⟨g, hg, hφg⟩ := hsurj c hdeg
  obtain ⟨g', hg'sec, hg'eq⟩ := Stacks.Groupoids.exists_comp_zpow_id_left_eq_of_isSepClosed A.X
    (h03RP A.X) n hn g hg
  exact ⟨curvePicardToChowZero k f (φ g'), by
    rw [← hc, ← hφg, hcompat g g' hg hg'sec hg'eq, map_zsmul]⟩

end Stacks.WeilCohomology

end
