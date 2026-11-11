module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHom
public import StacksCore.Tactic.StacksAttribute

/-!
# Perfect objects along a limit of algebraic spaces

In Situation 09RH — a directed inverse system `i ↦ X_i` of quasi-compact and quasi-separated
algebraic spaces over a scheme `S` with affine transition morphisms, a chosen limit `X` and a
chosen index `0` — Stacks 09RJ asserts that

`colim_{i ≥ 0} D_perf(𝒪_{X_i}) ⟶ D_perf(𝒪_X)`

is an equivalence: the category of perfect objects of `D(𝒪_X)` is the colimit of the categories
of perfect objects of the `D(𝒪_{X_i})` along derived pullback.

The source's proof has exactly two halves, and it says so in one sentence: "full faithfulness
holds by Lemma 75.24.2", which is Stacks 09RI, "so we only need to prove essential
surjectivity".  **This file delivers the full-faithfulness half**, read on the categories of
perfect objects, from Stacks 09RI of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitDerivedHom.lean`.  Essential surjectivity is
not delivered; see "What is not here" below, which says why.

## Main definitions

* `AlgebraicGeometry.Space.perfectProperty` is perfectness of an object of `D(𝒪_X)` for an
  algebraic space `X` over the base, packaged as a property of objects of that category.
* `AlgebraicGeometry.Space.PerfectDerivedCategory` is the category `D_perf(𝒪_X)` of Stacks 0F8I
  for an algebraic space: the full subcategory of `D(𝒪_X)` cut out by that property.  It is the
  algebraic-space counterpart of
  `Stacks.Perfect.BoundedLocallyFreeComplexes.PerfectDerivedCategory`.

## Main results

* `AlgebraicGeometry.Space.DescentSituation.exists_descendedHom` is **fullness** of the
  comparison out of the colimit: every morphism `Lf_0^*E₀ ⟶ Lf_0^*K₀` in `D(𝒪_X)` between the
  derived pullbacks of perfect objects `E₀`, `K₀` of `D(𝒪_{X₀})` is the image of a morphism
  `Lf_{i0}^*E₀ ⟶ Lf_{i0}^*K₀` at some stage `i ≥ 0`.
* `AlgebraicGeometry.Space.DescentSituation.eventually_map_eq` is **faithfulness**: two
  morphisms `Lf_{i0}^*E₀ ⟶ Lf_{i0}^*K₀` at a stage `i` with the same image in `D(𝒪_X)` already
  agree at some later stage.

Together these two are the assertion that the hom-sets of `D_perf(𝒪_X)` between objects coming
from the system are the filtered colimits of the hom-sets at the stages, which is what full
faithfulness of the comparison out of the colimit of categories means.  The categories of
perfect objects are *full* subcategories of the ambient derived categories, so a morphism of
perfect objects is a morphism of `D(𝒪_X)` and the two statements are about ambient hom-sets with
no further identification needed; that is the only role `PerfectDerivedCategory` plays in them,
and it is why the perfectness of `E₀` and of `K₀` appears as the `property` field of a bundled
object rather than as a separate hypothesis.

## What is not here

*Essential surjectivity*, that every perfect object of `D(𝒪_X)` is `Lf_i^*` of a perfect object
of `D(𝒪_{X_i})` for some `i`, is the other half of the source's proof and is **not** proved or
assumed anywhere below.  It is not reachable in this library: the source runs the induction
principle of Stacks 08GP over the quasi-compact objects of `(X_0)_{étale}`, uses the glueing
lemma Stacks 08HB at the elementary-distinguished-square step, and settles the affine case by
the *scheme-level* Stacks 09RF through the comparison of Stacks 071Q and Stacks 08HG.  The
scheme-level Stacks 09RF is formalized in
`StacksFrontier/AlgebraicGeometry/Perfect/LimitPerfectObjects.lean` only as its canonical cocone —
the clause labels on `AlgebraicGeometry.DescentSituation.perfectComparison_coherence` and
`AlgebraicGeometry.DescentSituation.perfectTransitionComp_coherence` record that neither full
faithfulness nor essential surjectivity of the comparison is included there — so the base case
of the induction has nothing to reduce to.  Nothing in this file stands in for it, and the
clause labels of the two tagged theorems say so.

Consequently the categorical conclusion "the comparison functor is an equivalence" is not
stated: essential surjectivity is absent, so it could only be stated by assuming it.

The comparison functors `D_perf(𝒪_{X_i}) ⥤ D_perf(𝒪_X)` are constructible, which this note
previously denied. Derived pullback along a morphism of algebraic spaces does preserve
perfectness: that is `AlgebraicGeometry.Space.isPerfect_smallEtaleDerivedModulePullback`, the
algebraic-space form of Stacks 08H6, in
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPullbackPerfect`, which this module does
not currently import. Only essential surjectivity blocks the categorical statement.

## The carried hypotheses

Two hypotheses are carried, and neither is a clause of the conclusion of Stacks 09RJ.

*The affine ring-translation dictionary `model`.*  This is the hypothesis of
Stacks 09RI itself, `AlgebraicGeometry.Space.DescentSituation.RingModel`, passed through
unchanged.  "The carried hypothesis" in the module documentation of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitDerivedHom.lean` says what it is and why it
is an input of the source's proof of Stacks 09RI rather than its conclusion; nothing is added to
it here.

*Quasi-coherence of the cohomology sheaves of `K₀`, `hqcK₀`.*  Stacks 09RI is stated for `E₀`
perfect and `K₀` in `D_QCoh(𝒪_{X₀})`, whereas Stacks 09RJ has `K₀` perfect.  For an algebraic
space a perfect object does lie in `D_QCoh`, but that implication is not in this library at this
spelling: `AlgebraicGeometry.RingedSite.IsPerfect` gives local strictly perfect models and no
result takes those to degreewise `SheafOfModules.IsQuasicoherentOnSite` of the cohomology
sheaves, quasi-coherence on the small étale site being nowhere shown to be a local condition.
So the quasi-coherence that the perfectness of `K₀` ought to supply is taken as a hypothesis.
It is not essential surjectivity, nor a hom-level colimit assertion, nor does it mention the
system: it is one property of the single object `K₀` at the single stage `0`.

## Implementation notes

The statements are at the module universe of the schemes, `Modules.{u, u}`, which is the
universe Stacks 09RI is stated at, and the index universe `v` and the universe `w` of the
derived category of `R`-modules in the dictionary stay independent of it, as there.

The standard model `CategoryTheory.HasDerivedCategory.standard` is selected by a plain
`attribute [local instance]`, as in
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitDerivedHom.lean`: the raised priority and the
hand-written `Abelian` instance of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/ModulesAtSchemeUniverse.lean` are needed only in a
file whose import closure contains `AlgebraicGeometry.derivedTilde` and the locally small models,
and the single import above does not bring either in.

The instance hypotheses on the slices of the small étale site of `X₀` are the ones
`AlgebraicGeometry.RingedSite.IsPerfect` and the derived tensor product ask for and that
`StacksFrontier/AlgebraicGeometry/Spaces/RingedSite.lean` does not already provide at this
universe; they match the statement of Stacks 09RI, which consumes the same ones.

## References

* [Stacks Project, Lemma 75.24.3 (Tag 09RJ)](https://stacks.math.columbia.edu/tag/09RJ)
* [Stacks Project, Situation 75.24.1 (Tag 09RH)](https://stacks.math.columbia.edu/tag/09RH)
* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Lemma 75.9.3 (Tag 08GP)](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Lemma 75.10.8 (Tag 08HB)](https://stacks.math.columbia.edu/tag/08HB)
* [Stacks Project, Lemma 36.29.3 (Tag 09RF)](https://stacks.math.columbia.edu/tag/09RF)
* [Stacks Project, Lemma 75.4.2 (Tag 071Q)](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Lemma 75.13.5 (Tag 08HG)](https://stacks.math.columbia.edu/tag/08HG)
* [Stacks Project, Definition 36.11.1 (Tag 0F8I)](https://stacks.math.columbia.edu/tag/0F8I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

/-! ### The category of perfect objects on an algebraic space -/

section PerfectObjects

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS)
  [∀ U : (smallEtaleRingedSite B S hS X.obj X.property).C,
    HasSheafify ((smallEtaleRingedSite B S hS X.obj X.property).J.over U) AddCommGrpCat.{u}]
  [∀ U : (smallEtaleRingedSite B S hS X.obj X.property).C,
    ((smallEtaleRingedSite B S hS X.obj X.property).J.over U).WEqualsLocallyBijective
      AddCommGrpCat.{u}]
  [∀ U : (smallEtaleRingedSite B S hS X.obj X.property).C,
    ((smallEtaleRingedSite B S hS X.obj X.property).J.over U).HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u})]

/-- Perfectness of an object of `D(𝒪_X)`, for `X` an algebraic space over the base, as a
property of objects of that category.  This is `AlgebraicGeometry.RingedSite.IsPerfect` on the
small étale ringed site of Stacks 04KH, which is the site the source means by `D(𝒪_X)` for an
algebraic space and the spelling at which perfectness is stated in this library. -/
def perfectProperty :
    ObjectProperty (DerivedCategory (Modules.{u, u} B S hS X.obj X.property)) :=
  fun E => (smallEtaleRingedSite B S hS X.obj X.property).IsPerfect E

/-- **The category `D_perf(𝒪_X)` of perfect objects**, for `X` an algebraic space over the base:
the full subcategory of `D(𝒪_X)` cut out by perfectness.  This is the definition of Stacks 0F8I
read on the small étale ringed site, the algebraic-space counterpart of
`Stacks.Perfect.BoundedLocallyFreeComplexes.PerfectDerivedCategory`.

Being a full subcategory, a morphism of `D_perf(𝒪_X)` is a morphism of `D(𝒪_X)`; that is what
makes the two theorems below, which are about morphisms of the ambient derived category,
statements about `D_perf(𝒪_X)`. -/
abbrev PerfectDerivedCategory := (perfectProperty B S hS X).FullSubcategory

end PerfectObjects

/-! ### Full faithfulness of the comparison out of the colimit -/

namespace DescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
  [∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y), (modulePullback B S hS f).Additive]
  {D : DescentSituation B S hS hZ I} (sys : D.DerivedPullbackSystem)

section

variable
  [∀ U : (smallEtaleRingedSite B S hS (D.stage D.base).obj (D.stage D.base).property).C,
    HasSheafify ((smallEtaleRingedSite B S hS (D.stage D.base).obj
      (D.stage D.base).property).J.over U) AddCommGrpCat.{u}]
  [∀ U : (smallEtaleRingedSite B S hS (D.stage D.base).obj (D.stage D.base).property).C,
    ((smallEtaleRingedSite B S hS (D.stage D.base).obj
      (D.stage D.base).property).J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : (smallEtaleRingedSite B S hS (D.stage D.base).obj (D.stage D.base).property).C,
    ((smallEtaleRingedSite B S hS (D.stage D.base).obj
      (D.stage D.base).property).J.over U).HasSheafCompose
        (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (smallEtaleRingedSite B S hS (D.stage D.base).obj (D.stage D.base).property).O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (smallEtaleRingedSite B S hS (D.stage D.base).obj
      (D.stage D.base).property).O).obj M).Additive]
  [∀ (M N : CochainComplex
      (Modules.{u, u} B S hS (D.stage D.base).obj (D.stage D.base).property) ℤ),
    HomologicalComplex.HasMapBifunctor M N
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (smallEtaleRingedSite B S hS (D.stage D.base).obj (D.stage D.base).property).O)
      (ComplexShape.up ℤ)]
  (E₀ K₀ : PerfectDerivedCategory B S hS (D.stage D.base))

/-- Stacks 09RI applied to a pair of perfect objects of `D(𝒪_{X₀})`.  Its hypothesis `hcase` is
taken in its first form, the perfectness of `E₀` together with the quasi-coherence of the
cohomology sheaves of `K₀`; the perfectness of `E₀` is the `property` field of the bundled
object, and `hqcK₀` is what the perfectness of `K₀` would supply, as the module documentation of
this file explains. -/
theorem isHomColimit_of_perfect
    (T : Stacks.SheafOfModules.DerivedTensorProduct
      (smallEtaleRingedSite B S hS (D.stage D.base).obj (D.stage D.base).property))
    (hqcK₀ : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS (D.stage D.base).obj (D.stage D.base).property) n).obj
        K₀.obj).IsQuasicoherentOnSite)
    (R : Type u) [Ring R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (model : RingModel sys E₀.obj K₀.obj R) :
    IsHomColimit sys E₀.obj K₀.obj :=
  isHomColimit_of_ringModel sys E₀.obj K₀.obj T (Or.inl ⟨E₀.property, hqcK₀⟩) R model

/-- **Fullness of the comparison out of the colimit, Stacks 09RJ.**  In Situation 09RH, let `E₀`
and `K₀` be perfect objects of `D(𝒪_{X₀})` and put `E_i = Lf_{i0}^*E₀`, `K_i = Lf_{i0}^*K₀` for
`i ≥ 0` and `E = Lf_0^*E₀`, `K = Lf_0^*K₀`.  Then every morphism `E ⟶ K` of `D(𝒪_X)` is the
image, under the map of Stacks 09RI, of a morphism `E_i ⟶ K_i` at some stage `i ≥ 0`.

The categories of perfect objects are full subcategories of the ambient derived categories, so
this is fullness of the comparison functor out of the colimit of the `D_perf(𝒪_{X_i})`.

This is the first half of the full faithfulness that the source's proof of Stacks 09RJ takes
from Stacks 09RI, and it is deduced from Stacks 09RI here.  The hypotheses `model`
and `hqcK₀` are carried; see "The carried hypotheses" in this file's module documentation. -/
@[stacks 09RJ "fullness of the comparison out of the colimit of the categories of perfect \
objects, which the source's proof takes from Stacks 09RI; essential surjectivity, the other \
half of that proof, is not included"]
theorem exists_descendedHom
    (T : Stacks.SheafOfModules.DerivedTensorProduct
      (smallEtaleRingedSite B S hS (D.stage D.base).obj (D.stage D.base).property))
    (hqcK₀ : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS (D.stage D.base).obj (D.stage D.base).property) n).obj
        K₀.obj).IsQuasicoherentOnSite)
    (R : Type u) [Ring R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (model : RingModel sys E₀.obj K₀.obj R)
    (φ : limitObj sys E₀.obj ⟶ limitObj sys K₀.obj) :
    ∃ (i : D.Stages) (g : stageObj sys E₀.obj i ⟶ stageObj sys K₀.obj i),
      homProjection sys E₀.obj K₀.obj i g = φ :=
  Stacks.IsStagesColimit.exists_stage (isHomColimit_of_perfect sys E₀ K₀ T hqcK₀ R model) φ

/-- **Faithfulness of the comparison out of the colimit, Stacks 09RJ.**  In Situation 09RH, with
`E₀` and `K₀` perfect objects of `D(𝒪_{X₀})` as above, two morphisms `E_i ⟶ K_i` at a stage
`i ≥ 0` whose images `E ⟶ K` in `D(𝒪_X)` agree already have equal images at some later stage.

Together with `AlgebraicGeometry.Space.DescentSituation.exists_descendedHom` this says that the
hom-sets of `D_perf(𝒪_X)` between objects coming from the system are the filtered colimits of
the hom-sets at the stages, which is full faithfulness of the comparison out of the colimit of
the `D_perf(𝒪_{X_i})`.

This is the second half of the full faithfulness that the source's proof of Stacks 09RJ takes
from Stacks 09RI, and it is deduced from Stacks 09RI here.  The hypotheses `model`
and `hqcK₀` are carried; see "The carried hypotheses" in this file's module documentation. -/
@[stacks 09RJ "faithfulness of the comparison out of the colimit of the categories of perfect \
objects, which the source's proof takes from Stacks 09RI; essential surjectivity, the other \
half of that proof, is not included"]
theorem eventually_map_eq
    (T : Stacks.SheafOfModules.DerivedTensorProduct
      (smallEtaleRingedSite B S hS (D.stage D.base).obj (D.stage D.base).property))
    (hqcK₀ : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS (D.stage D.base).obj (D.stage D.base).property) n).obj
        K₀.obj).IsQuasicoherentOnSite)
    (R : Type u) [Ring R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (model : RingModel sys E₀.obj K₀.obj R) (i : D.Stages)
    (g g' : stageObj sys E₀.obj i ⟶ stageObj sys K₀.obj i)
    (hgg : homProjection sys E₀.obj K₀.obj i g = homProjection sys E₀.obj K₀.obj i g') :
    ∃ (j : D.Stages) (h : i ≤ j), homTransition sys E₀.obj K₀.obj i j h g =
      homTransition sys E₀.obj K₀.obj i j h g' :=
  Stacks.IsStagesColimit.exists_trans_eq
    (isHomColimit_of_perfect sys E₀ K₀ T hqcK₀ R model) i g g' hgg

end

end DescentSituation

end AlgebraicGeometry.Space

end
