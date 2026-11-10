module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.CanonicalDerivedTensorCommShiftTwo
public import StacksFrontier.CategoryTheory.Shift.CommShiftTwoPostcomp
public import StacksFrontier.CategoryTheory.Shift.CommShiftTwoOfIso
import StacksCore.Tactic.StacksAttribute

/-!
# The four bifunctors of Tag 079U commute with the shifts in both variables

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces.  [Stacks, Tag 079U] compares the two
bifunctors

`(K, L) ↦ Lf^*(K ⊗^L_{𝒪_Y} L)` and `(K, L) ↦ Lf^*K ⊗^L_{𝒪_X} Lf^*L`

on `D(𝒪_Y) × D(𝒪_Y)`, which this development writes as
`Stacks.Cohomology.DerivedPullbackTensor.pullbackOfTensor` and `tensorOfPullbacks`, and their
restrictions along the K-flat localization `kFlatQPair`.  This file equips all four, in curried
form, with `CategoryTheory.Functor.CommShift₂Int`.

That is what makes a `CategoryTheory.NatTrans.CommShift₂` *statable* for the comparison: Mathlib's
`CategoryTheory.NatTrans.CommShift₂` takes `CommShift₂` structures on the source and target
bifunctors as instance arguments, and it is a class on *curried* bifunctors `C₁ ⥤ C₂ ⥤ D`, while
the comparison of Tag 079U is a transformation of functors on a product.

## Main results

* `Stacks.Cohomology.DerivedPullbackTensor.derivedTensorCommShift₂Int`: the derived tensor product
  of a ringed space commutes with the shifts in both variables.
* `Stacks.Cohomology.DerivedPullbackTensor.curriedPullbackOfTensor` and
  `curriedTensorOfPullbacks`, with `…_commShift₂Int`: the two sides of Tag 079U written in curried
  form at the spelling the shift closure properties match, each with its datum.
* `Stacks.Cohomology.DerivedPullbackTensor.curryPullbackOfTensorIso` and
  `curryTensorOfPullbacksIso`: those curried forms are the curryings of `pullbackOfTensor` and
  `tensorOfPullbacks`.
* `Stacks.Cohomology.DerivedPullbackTensor.curryPullbackOfTensor_commShift₂Int`,
  `curryTensorOfPullbacks_commShift₂Int`, `curryModelsPullbackOfTensor_commShift₂Int`,
  `curryModelsTensorOfPullbacks_commShift₂Int`: **the four data**, the last two over the K-flat
  models, which are the ones `modelsComparison` is a transformation between.
* `Stacks.Cohomology.DerivedPullbackTensor.ModelsComparisonCommShift₂`: **the resulting
  statement** — that `modelsComparison`, curried, is compatible with the shifts in each variable.
  It is stated and *not* proved; the last implementation note says what its proof still owes.

## Implementation notes

**Three obstacles, none of them about signs.**

*The datum the chain reads is the transported one, seated by hand.*  The derived tensor product
carries its datum as the structure field
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.commShift₂`, an instance, whose halves are
`commShift_left`/`commShift_right`.  The chain reads instead
`Stacks.SheafOfModules.DerivedMonoidal.canonicalTensor_commShift₂Int`, which transports
`CochainComplex.KFlatBifunctor.derivedBifunctor`'s datum along the comparison of the two
bifunctors, so that the comparison is shift-compatible by construction; the two data are equal by
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedTensorProduct_commShift₂_eq`, but not
definitionally.  `canonicalTensor_commShift₂Int` is a `def`, not an instance, so
`derivedTensorCommShift₂Int` seats it by hand.

*The two structure-sheaf spellings.*  The pullback development names `𝒪_Y` by
`structureSheafRing` and the tensor development by
`Stacks.SheafOfModules.Tensor.ringSheaf`; the two are the same sheaf by `rfl` but not at
`implicit` transparency.  Every statement here mixes them, since the derived pullback comes from
one development and the derived tensor product from the other.  The cure, found by a predecessor
of this file, is `attribute [local instance_reducible]` on the first *together with* offering
`Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift` as a **local** instance: a
local instance is selected by class name alone and never consulted in the discrimination tree, so
the candidate is always tried and only `isDefEq` — which the reducibility attribute governs — has
to succeed.  The attribute is `local` and local reducibility is not exported, so a consumer of
this file has to repeat the line.

*Currying is not the identity.*  `pullbackOfTensor` is
`CategoryTheory.Functor.uncurry.obj (⊗^L) ⋙ Lf^*`, a functor on a product, and
`CategoryTheory.Functor.curry.obj` of it is *not* syntactically
`⊗^L ⋙ (whiskeringRight _ _ _).obj Lf^*` — the two differ by a `Functor.map_id` and a
`Functor.map_comp`, so they agree only up to an isomorphism which is the identity on every
object.  `curryPullbackOfTensorIso` and `curryTensorOfPullbacksIso` are those isomorphisms and
`CategoryTheory.Functor.CommShift₂.ofIsoInt` transports the data across them.  The same applies
to the restriction along `kFlatQPair`, which is a product functor: there the identity-component
isomorphism absorbs `CategoryTheory.Functor.curryObjProdComp` as well.

**What is pinned in a `def`, and why.**  `curriedPullbackOfTensor` and `curriedTensorOfPullbacks`
are ascribed `def`s rather than inlined terms.  Written inline, the composite of whiskerings
carries its three categories as implicit arguments elaborated afresh at each occurrence, and the
mixed spellings above then make two occurrences of the same bifunctor fail to be recognised as
the same; pinning the spelling once is the standard cure in this chapter (compare
`Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexMu`).

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.DerivedPullbackTensor

universe u

attribute [local instance] HasDerivedCategory.standard

open AlgebraicGeometry.RingedSpace.KFlatDerivedPullback (Modules)

/-! ### The two data that have to be seated before the spellings are bridged

`structureSheafRing` is `@[instance_reducible]`, which is what lets the pullback development's
spelling of `𝒪_Y` meet the tensor development's at instance transparency; that is needed below.
`attribute [local implicit_reducible] structureSheafRing` raises it further and changes the
discrimination-tree keys under that name, and *additivity of the derived pullback*, which
instance search finds unaided, is then no longer found.  So the two inputs that do not need the
further unfolding are seated first, in this section, and the attribute is turned on
afterwards.

`Stacks.SheafOfModules.Tensor.ringSheaf` stands on the same attribute line for the same reason,
and it is the one name there whose own reducibility is not what it looks like: it is a plain,
semireducible `def`, so the tensor development's spelling of `𝒪_Y` does not reach
`Y.presheaf ⋙ forget₂ _ _` on its own and the two developments' spellings never meet.  Raising it
locally is enough, and it is enough for both of the failures that otherwise appear below:
`implicit_reducible` sits above `instance_reducible`, so it mends discrimination-key retrieval as
well as `isDefEq`, and the two `CommShift₂` data that search cannot otherwise assemble and the
eight naturality `simp`s of the four currying isomorphisms — which otherwise make no progress at
all, their two sides being separated by exactly this definition — clear together. -/

/-- **The derived pullback is additive.**  Found by instance search here, before the local
reducibility attribute below changes the keys under `structureSheafRing`. -/
theorem derivedPullbackAdditive {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).Additive :=
  inferInstance

/-! ### The derived tensor product of a ringed space -/

/-- **The derived tensor product of a ringed space commutes with the shifts in both variables.**
This is `Stacks.SheafOfModules.DerivedMonoidal.canonicalTensor_commShift₂Int` at the structure
sheaf of a ringed space, seated by hand because that datum is a `def`, not an instance. -/
@[instance_reducible]
def derivedTensorCommShift₂Int (Z : RingedSpace.{u, u})
    [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf).CommShift₂Int :=
  Stacks.SheafOfModules.DerivedMonoidal.canonicalTensor_commShift₂Int Z.sheaf

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-! ### `Lf^*(- ⊗^L -)`, curried -/

/-- `(K, L) ↦ Lf^*(K ⊗^L_{𝒪_Y} L)` in curried form, with its three categories pinned: the derived
tensor product of `Y` postcomposed with the derived pullback. -/
def curriedPullbackOfTensor :
    DerivedCategory (Modules Y) ⥤ DerivedCategory (Modules Y) ⥤ DerivedCategory (Modules X) :=
  Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf ⋙
    (Functor.whiskeringRight (DerivedCategory (Modules Y)) (DerivedCategory (Modules Y))
      (DerivedCategory (Modules X))).obj
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)

/-- `Lf^*(- ⊗^L -)` commutes with the shifts in both variables: this is
`CategoryTheory.Functor.CommShift₂.postcompInt` at `derivedTensorCommShift₂Int` and
`Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift`, the latter offered as a local
instance so that the two structure-sheaf spellings are compared at `instance` transparency. -/
@[instance_reducible]
def curriedPullbackOfTensor_commShift₂Int : (curriedPullbackOfTensor f).CommShift₂Int :=
  haveI := Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift f
  haveI := derivedPullbackAdditive f
  haveI := derivedTensorCommShift₂Int Y
  Functor.CommShift₂.postcompInt
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)

/-- **The pinned curried form is the currying of `pullbackOfTensor`.**  Both are
`Lf^*((K ⊗^L L))` on objects, by `Iso.refl`; the content is the two naturality squares, where the
difference between `CategoryTheory.Functor.curry.obj` of a composite and the whiskered composite
— a `Functor.map_id` in the first variable and a `Functor.map_comp` in the second — is
discharged. -/
def curryPullbackOfTensorIso :
    curriedPullbackOfTensor f ≅ Functor.curry.obj (pullbackOfTensor f) :=
  NatIso.ofComponents
    (fun _ => NatIso.ofComponents (fun _ => Iso.refl _) (by simp [curriedPullbackOfTensor]))
    (fun _ => by ext; simp [curriedPullbackOfTensor])

/-- The currying of `(K, L) ↦ Lf^*(K ⊗^L_{𝒪_Y} L)` commutes with the shifts in both variables. -/
@[instance_reducible]
def curryPullbackOfTensor_commShift₂Int :
    (Functor.curry.obj (pullbackOfTensor f)).CommShift₂Int :=
  haveI := curriedPullbackOfTensor_commShift₂Int f
  Functor.CommShift₂.ofIsoInt (curryPullbackOfTensorIso f)

/-! ### `Lf^*(-) ⊗^L Lf^*(-)`, curried -/

/-- `(K, L) ↦ Lf^*K ⊗^L_{𝒪_X} Lf^*L` in curried form, with its categories pinned: the derived
tensor product of `X` precomposed with the derived pullback in both variables. -/
def curriedTensorOfPullbacks :
    DerivedCategory (Modules Y) ⥤ DerivedCategory (Modules Y) ⥤ DerivedCategory (Modules X) :=
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f ⋙
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf ⋙
      (Functor.whiskeringLeft (DerivedCategory (Modules Y)) (DerivedCategory (Modules X))
        (DerivedCategory (Modules X))).obj
          (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f))

/-- `Lf^*(-) ⊗^L Lf^*(-)` commutes with the shifts in both variables: this is
`CategoryTheory.Functor.CommShift₂.precomp₁` after `precomp₂` at `derivedTensorCommShift₂Int`
for `X`. -/
@[instance_reducible]
def curriedTensorOfPullbacks_commShift₂Int : (curriedTensorOfPullbacks f).CommShift₂Int :=
  haveI := Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift f
  haveI := derivedPullbackAdditive f
  haveI := derivedTensorCommShift₂Int X
  Functor.CommShift₂.precomp₁
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf ⋙
      (Functor.whiskeringLeft (DerivedCategory (Modules Y)) (DerivedCategory (Modules X))
        (DerivedCategory (Modules X))).obj
          (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f))
    CommShift₂Setup.int

/-- **The pinned curried form is the currying of `tensorOfPullbacks`.** -/
def curryTensorOfPullbacksIso :
    curriedTensorOfPullbacks f ≅ Functor.curry.obj (tensorOfPullbacks f) :=
  NatIso.ofComponents
    (fun _ => NatIso.ofComponents (fun _ => Iso.refl _) (by simp [curriedTensorOfPullbacks]))
    (fun _ => by ext; simp [curriedTensorOfPullbacks])

/-- The currying of `(K, L) ↦ Lf^*K ⊗^L_{𝒪_X} Lf^*L` commutes with the shifts in both
variables. -/
@[instance_reducible]
def curryTensorOfPullbacks_commShift₂Int :
    (Functor.curry.obj (tensorOfPullbacks f)).CommShift₂Int :=
  haveI := curriedTensorOfPullbacks_commShift₂Int f
  Functor.CommShift₂.ofIsoInt (curryTensorOfPullbacksIso f)

/-! ### The same two bifunctors over the K-flat models

`modelsComparison` is a transformation between `kFlatQPair ⋙ pullbackOfTensor f` and
`kFlatQPair ⋙ tensorOfPullbacks f`, so these are the two bifunctors whose data
`CategoryTheory.NatTrans.CommShift₂` consumes.  `kFlatQPair` is `kFlatQY.prod kFlatQY`, so in
curried form the restriction is a precomposition in each variable, which is
`CategoryTheory.Functor.CommShift₂.precomp₁` and `precomp₂`; the shift on the models and
`kFlatQY.CommShift ℤ` are what `StacksFrontier/Homology/KFlat/BifunctorShift.lean` registers. -/

/-- `(M₁, M₂) ↦ Lf^*(QM₁ ⊗^L_{𝒪_Y} QM₂)` on pairs of K-flat models, in curried form. -/
def curriedModelsPullbackOfTensor :
    (CochainComplex.KFlatBifunctor.kFlatObjects
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).FullSubcategory ⥤
      (CochainComplex.KFlatBifunctor.kFlatObjects
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).FullSubcategory ⥤
      DerivedCategory (Modules X) :=
  kFlatQY (Y := Y) ⋙ (curriedPullbackOfTensor f ⋙
    (Functor.whiskeringLeft _ (DerivedCategory (Modules Y)) (DerivedCategory (Modules X))).obj
      (kFlatQY (Y := Y)))

/-- `(M₁, M₂) ↦ Lf^*(QM₁) ⊗^L_{𝒪_X} Lf^*(QM₂)` on pairs of K-flat models, in curried form. -/
def curriedModelsTensorOfPullbacks :
    (CochainComplex.KFlatBifunctor.kFlatObjects
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).FullSubcategory ⥤
      (CochainComplex.KFlatBifunctor.kFlatObjects
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).FullSubcategory ⥤
      DerivedCategory (Modules X) :=
  kFlatQY (Y := Y) ⋙ (curriedTensorOfPullbacks f ⋙
    (Functor.whiskeringLeft _ (DerivedCategory (Modules Y)) (DerivedCategory (Modules X))).obj
      (kFlatQY (Y := Y)))

/-- The restriction of `Lf^*(- ⊗^L -)` to the K-flat models commutes with the shifts in both
variables. -/
@[instance_reducible]
def curriedModelsPullbackOfTensor_commShift₂Int :
    (curriedModelsPullbackOfTensor f).CommShift₂Int :=
  haveI := curriedPullbackOfTensor_commShift₂Int f
  inferInstanceAs (((kFlatQY (Y := Y)) ⋙ (curriedPullbackOfTensor f ⋙
    (Functor.whiskeringLeft _ (DerivedCategory (Modules Y))
      (DerivedCategory (Modules X))).obj (kFlatQY (Y := Y)))).CommShift₂Int)

/-- The restriction of `Lf^*(-) ⊗^L Lf^*(-)` to the K-flat models commutes with the shifts in
both variables. -/
@[instance_reducible]
def curriedModelsTensorOfPullbacks_commShift₂Int :
    (curriedModelsTensorOfPullbacks f).CommShift₂Int :=
  haveI := curriedTensorOfPullbacks_commShift₂Int f
  inferInstanceAs (((kFlatQY (Y := Y)) ⋙ (curriedTensorOfPullbacks f ⋙
    (Functor.whiskeringLeft _ (DerivedCategory (Modules Y))
      (DerivedCategory (Modules X))).obj (kFlatQY (Y := Y)))).CommShift₂Int)

/-- **The pinned models form is the currying of `kFlatQPair ⋙ pullbackOfTensor f`.** -/
def curryModelsPullbackOfTensorIso :
    curriedModelsPullbackOfTensor f ≅
      Functor.curry.obj (kFlatQPair (Y := Y) ⋙ pullbackOfTensor f) :=
  NatIso.ofComponents
    (fun _ => NatIso.ofComponents (fun _ => Iso.refl _)
      (by simp [curriedModelsPullbackOfTensor, curriedPullbackOfTensor]))
    (fun _ => by
      ext
      simp [curriedModelsPullbackOfTensor, curriedPullbackOfTensor])

/-- **The pinned models form is the currying of `kFlatQPair ⋙ tensorOfPullbacks f`.** -/
def curryModelsTensorOfPullbacksIso :
    curriedModelsTensorOfPullbacks f ≅
      Functor.curry.obj (kFlatQPair (Y := Y) ⋙ tensorOfPullbacks f) :=
  NatIso.ofComponents
    (fun _ => NatIso.ofComponents (fun _ => Iso.refl _)
      (by simp [curriedModelsTensorOfPullbacks, curriedTensorOfPullbacks]))
    (fun _ => by
      ext
      simp [curriedModelsTensorOfPullbacks, curriedTensorOfPullbacks])

/-- **The source bifunctor of `modelsComparison`, curried, commutes with the shifts in both
variables.** -/
@[instance_reducible]
def curryModelsPullbackOfTensor_commShift₂Int :
    (Functor.curry.obj (kFlatQPair (Y := Y) ⋙ pullbackOfTensor f)).CommShift₂Int :=
  haveI := curriedModelsPullbackOfTensor_commShift₂Int f
  Functor.CommShift₂.ofIsoInt (curryModelsPullbackOfTensorIso f)

/-- **The target bifunctor of `modelsComparison`, curried, commutes with the shifts in both
variables.** -/
@[instance_reducible]
def curryModelsTensorOfPullbacks_commShift₂Int :
    (Functor.curry.obj (kFlatQPair (Y := Y) ⋙ tensorOfPullbacks f)).CommShift₂Int :=
  haveI := curriedModelsTensorOfPullbacks_commShift₂Int f
  Functor.CommShift₂.ofIsoInt (curryModelsTensorOfPullbacksIso f)

/-! ### What the proof of the statement below still needs

`modelsComparison` is built from three transformations — `derivedPullbackNatTrans`,
`derivedToTensorNatTrans` and `pullbackTensorComplexNatIso` — and the shift compatibility of each
is a separate obligation.  This file does not discharge any of them; what it records, because it
is not visible from the goal, is how close the first one is.

*The first leg, `derivedPullbackNatTrans`, needs no new mathematics.*  Every ingredient is in
place and found by instance search once the two structure-sheaf spellings are bridged: Mathlib's
`CategoryTheory.Functor.commShiftMapCochainComplex` gives `(pullbackComplex f).CommShift ℤ`, the
`Q` versus `Qh ∘ quotient` bridge `DerivedCategory.quotientCompQhIso` and
`CategoryTheory.Functor.mapHomotopyCategoryFactors` both carry a `NatTrans.CommShift`, and
`Stacks.Cohomology.KFlatDerivedPullback.derivedPullbackComparison_commShift` is the counit half of
the total-left-derived shift datum.  Three of the four whiskered factors of the composite
synthesize in isolation.  What blocks the composite is cost, not content: assembled in one search
it exceeds the default `synthInstance` heartbeat budget of 20000, and budget overrides are not
used in this development, so the four factors have to be seated one at a time — and the seat for
`Lf^*`'s own commutation has to sit in the *statement*, since `NatTrans.CommShift` takes the two
functors' structures as instance arguments and they are synthesized before any `haveI` in the
proof is in scope.  The remaining difficulty is that each seat has itself to be stated at a
spelling the next one accepts.

*The second and third legs are where the mathematics is.*  `derivedToTensorNatTrans` is the
`toTensor` field of the canonical derived tensor product, and the `CommShift₂` supplied above is
transported from `CochainComplex.KFlatBifunctor.derivedBifunctor` along
`Stacks.SheafOfModules.DerivedMonoidal.canonicalTensorIso`, whose components at a K-flat pair are
`comparisonRight ≫ (comparison)⁻¹`; so the obligation is the shift compatibility of
`comparisonRight`, the K-flat comparison, which is a statement about the total tensor complex.
`pullbackTensorComplexNatIso` is `totalComplexPairTransport`, i.e.
`CategoryTheory.Functor.mapBifunctorTotalIso`, and its obligation is that the transport of a total
complex along `f^*` commutes with `CochainComplex.mapBifunctorShift₂Iso` — the Koszul sign
`(p * y).negOnePow` of `CochainComplex.ι_mapBifunctorShift₂Iso_hom_f`.

*That third leg is now proved*, in `StacksFrontier/Homology/TotalComplexTransportShift.lean`, at the
generality `mapBifunctorTotalIso` is stated in — any additive `Φ : D ⥤ D'` carrying a bifunctor
`F` to `F'` and preserving the antidiagonal coproducts, so in particular `f^*` and the sheaf
tensor products of `Y` and `X`.  Both variables are covered
(`CategoryTheory.Functor.mapBifunctorTotalIso_commShift₁` and `…_commShift₂`), and
`CategoryTheory.Functor.mapBifunctorTotalBifunctorIso_commShift₂` packages the pair as the
`CategoryTheory.NatTrans.CommShift₂Int` of the curried comparison, which is the shape the
statement below consumes.  The sign is not an obstruction: it is the same unit on both sides of
the square and passes through `Φ.map` because `Φ` is additive.

What `ModelsComparisonCommShift₂` still owes is therefore not a leg but the *assembly*:
`modelsComparison` is not the composite of the three legs but a `NatIso.ofComponents` whose
components conjugate `modelComparison` — itself `leftComparison` followed by the inverse of
`rightComparison` at a K-flat pair — by `kFlatQPairIso`.

*How much of that assembly is done.*
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPullback/PullbackTensorCommShiftReduction.lean`
carries it as far as it goes without new mathematics.  Restricting *both* variables along the
homotopy quotient from the K-flat **complexes** to the K-flat objects — which is essentially
surjective and shift-compatible, so `CategoryTheory.NatTrans.CommShift₂.of_essSurj` tests both
halves of `CategoryTheory.NatTrans.CommShift₂` after it — replaces the chosen cochain
representative by the complex itself, and `kFlatQPairIso` becomes a component of the isomorphism
of *functors* `CochainComplex.KFlatBifunctor.kFlatQuotientCompQIso`.  The identification of
`modelsComparison` there with the conjugate of `leftComparison` and the inverse of
`rightComparison` is then `rfl`.  The passage from an everywhere-invertible transformation to
the compatibility of its inverse is `CategoryTheory.NatTrans.CommShift₂.of_iso_invInt`, which
exists already; the earlier claim here that it was missing was wrong.  What is left is the shift
compatibility of `leftComparison` and of `rightComparison` in each variable, in curried form. -/

/-! ### The statement that the four data make possible -/

/-- **The shift compatibility of the comparison of [Stacks, Tag 079U] on K-flat
representatives**, as a proposition: `Stacks.Cohomology.DerivedPullbackTensor.modelsComparison`,
curried, is compatible with the shifts in each variable separately.

This is the hypothesis that
`CategoryTheory.Localization.lift₂NatIso_hom_commShift₂` consumes, in a *statable* form:
`CategoryTheory.NatTrans.CommShift₂` takes `CommShift₂` data on the
source and target as instance arguments, and those are the six `def`s above.  It is stated here
and **not proved**; see the implementation note below for the obligations it reduces to. -/
def ModelsComparisonCommShift₂ : Prop :=
  haveI := curryModelsPullbackOfTensor_commShift₂Int f
  haveI := curryModelsTensorOfPullbacks_commShift₂Int f
  NatTrans.CommShift₂Int (Functor.curry.map (modelsComparison f).hom)

end Stacks.Cohomology.DerivedPullbackTensor

end
