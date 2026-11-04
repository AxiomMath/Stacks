module

public import StacksFrontier.CategoryTheory.Monoidal.HomTensorComparisonAtDuals
public import StacksFrontier.CategoryTheory.Monoidal.ReseatDualsAndAdjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorSheafHomAdjunctionSlot
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethMapForExt
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCurryingOnARingedSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualLeftDual
import StacksCore.Tactic.StacksAttribute

/-!
# The comparison of Stacks 0FXP is invertible at perfect objects

Let `(Z, 𝒪_Z)` be a ringed space and let `A`, `A'`, `B`, `B'` be objects of `D(𝒪_Z)`.  Stacks
0FXP supplies a canonical morphism

`R𝓗om(A, A') ⊗^𝐋_{𝒪_Z} R𝓗om(B, B') ⟶ R𝓗om(A ⊗^𝐋_{𝒪_Z} B, A' ⊗^𝐋_{𝒪_Z} B')`,

which in the spelling of the Künneth formula for Ext is
`Stacks.Cohomology.DerivedKunnethExt.sheafHomTensorMap`.  **This file proves it is an
isomorphism when `A` and `B` are perfect**, which is the use Stacks 0FXZ makes of it.

The mathematics is not here.  It is
`Stacks.DerivedTensorHomDiagonal.isIso_homTensorComparison`: in a symmetric monoidal category,
given adjunctions `- ⊗ A ⊣ H_A`, `- ⊗ B ⊣ H_B` and `- ⊗ (A ⊗ B) ⊣ H_{A ⊗ B}` and exact pairings
of `A` and of `B` with some objects, the morphism `H_A(A') ⊗ H_B(B') ⟶ H_{A ⊗ B}(A' ⊗ B')`
adjoint to `CategoryTheory.MonoidalCategory.tensorμ` followed by the tensor product of the two
counits is invertible.  What this file does is instantiate that on `D(𝒪_Z)`: it supplies the
three adjunctions, the two exact pairings, and the identification of `sheafHomTensorMap` with
the abstract comparison.

* **The adjunctions** are Stacks 08J8.
  `AlgebraicGeometry.RingedSite.derivedTensorSheafHomAdjunction` is `- ⊗^𝐋_𝒪 B ⊣ R𝓗om(B, -)`
  over `Stacks.SheafOfModules.derivedTensorProductFunctor`, one of the two derived tensor
  products a ringed site carries; the symmetric monoidal structure
  `Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal` whose `tensorμ` the abstract
  comparison uses is seated on the *other* one.  They are compared by
  `Stacks.Cohomology.DerivedKunnethExt.tensorBridge`, and
  `CategoryTheory.MonoidalCategory.reseatTensorRightAdjunction` moves the adjunction across:
  tensoring on the right for a re-seated structure *is* the flip of the prescribed bifunctor, so
  this is `CategoryTheory.Adjunction.ofNatIsoLeft` at the flipped comparison.
* **The exact pairings** are Stacks 0FPC: a perfect object is dualizable, with dual
  `A^∨ = R𝓗om(A, 𝒪_Z)`, by `Stacks.SheafOfModules.exactPairingDerivedDual`.  That is stated for
  `Stacks.SheafOfModules.derivedMonoidalStructure`, which re-seats the monoidal derived category
  of Stacks 0FPT on the first of the two derived tensor products, while
  `canonicalDerivedMonoidal` re-seats *the same* structure on the second.
  `CategoryTheory.MonoidalCategory.reseatExactPairing` transfers the pairing between two such
  re-seatings; no comparison of the two is needed, because the identity functor is monoidal from
  each of them to the common underlying structure.

## Main definitions

* `Stacks.Cohomology.DerivedKunnethExt.sheafHomAdjunction`: Stacks 08J8 as an adjunction
  `- ⊗^𝐋_{𝒪_Z} B ⊣ R𝓗om(B, -)` for the derived tensor product of Stacks 06YU that the symmetric
  monoidal structure of Stacks 0FPT is seated on.
* `Stacks.Cohomology.DerivedKunnethExt.exactPairingCanonical`: the exact pairing of Stacks 0FPC
  for that monoidal structure.

## Main results

* `Stacks.Cohomology.DerivedKunnethExt.sheafHomAdjunction_counit_app`: the counit of the
  adjunction is the evaluation morphism `Stacks.Cohomology.DerivedKunnethExt.sheafHomEval`.
* `Stacks.Cohomology.DerivedKunnethExt.sheafHomEval_eq` and
  `sheafHomAdjunction_homEquiv_curry`: the evaluation morphism and the adjunction's hom-set
  bijection, written at the ringed site's own name for the bijection of Stacks 08DI.
* `Stacks.Cohomology.DerivedKunnethExt.sheafHomTensorMap_eq`: the morphism of Stacks 0FXP is the
  abstract comparison of `Stacks.DerivedTensorHomDiagonal.homTensorComparison` at those three
  adjunctions.
* `Stacks.Cohomology.DerivedKunnethExt.isIso_sheafHomTensorMap_of_isPerfect` and
  `isIso_sheafHomTensorMap_of_isPerfect_space`: **the morphism of Stacks 0FXP is an isomorphism
  when `A` and `B` are perfect**, with perfectness in the ringed-site sense of Stacks 08G5 and
  in the ringed-space sense of Stacks 08CM respectively.

## Implementation notes

*No monoidal structure on `D(𝒪_Z)` is an instance*, and three of them occur here —
`Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal` and its two re-seatings — so every
statement names the one it means by `@`-application, and the two transfer lemmas of
`StacksFrontier/CategoryTheory/Monoidal/ReseatDualsAndAdjunction.lean` take the underlying
structure as an explicit argument rather than as a hypothesis that would never be synthesized.

*One spelling of the bijection, and where its two instances meet.*  Every statement below names
the bijection of Stacks 08DI as `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv` at
`Stacks.SheafOfModules.ringedSite Z.sheaf`, never as
`Stacks.SheafOfModules.derivedSheafHomTensorEquiv Z.sheaf`.  The two are the same function
(`Stacks.SheafOfModules.derivedSheafHomTensorEquiv_eq`, a `rfl`), but the ringed-space name is
declared over `Stacks.SheafOfModules.StructureSheafModules Z.sheaf` and the objects here live in
`Stacks.SheafOfModules.DerivedMonoidal.Mod Z.sheaf`; the two spellings carry *different* `Abelian`
instances — `SheafOfModules.instAbelian ((sheafCompose _ (forget₂ CommRingCat RingCat)).obj
Z.sheaf)` against `Stacks.DerivedTensor.ResolutionByExtensionsByZero.instAbelian Z.sheaf` — and
`CategoryTheory.DerivedCategory` takes that instance as an argument.  A goal naming both is
therefore not type-correct at `implicit` transparency, which is what `rw` checks, so the site's own
name is the one that keeps the instance arguments agreeing syntactically.  This is the discipline
recorded in the implementation notes of
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/InternalHomPullbackInvertibility.lean`;
no reducibility attribute is put on `Stacks.SheafOfModules.Tensor.ringSheaf`.

*Why the proofs below are `conv`-scoped and term-shaped rather than one `rw` list.*  One crossing
is unavoidable: `Stacks.Cohomology.DerivedKunnethExt.sheafHomObj Z B Y` and
`((AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor (Stacks.SheafOfModules.ringedSite
Z.sheaf)).obj (op B)).obj Y` are the same object through the `abbrev`s `sheafHomObj` and
`Stacks.SheafOfModules.derivedSheafHom`, and `Stacks.Cohomology.DerivedKunnethExt.sheafHomEval` is
stated at the first while `AlgebraicGeometry.RingedSite.derivedTensorSheafHomAdjunction`'s counit
is stated at the second.  The crossing is affordable as a conversion check on the
*objects* and on a *statement*, and exceeds `maxRecDepth` inside the motive of any `rw` or `simp
only` on the goals here.  So the crossing is only ever paid where a `have` or an `exact` asks for
it on a small term — `hid` and the final `Eq.trans` of `sheafHomAdjunction_counit_app` — and each
rewrite that would otherwise search the whole equation is scoped with `conv_lhs`/`conv_rhs`.  That
is the reason no `maxRecDepth` option and no rewrite-up-to-defeq tactic appears.

For the same reason the last step of `sheafHomTensorMap_eq` is `DFunLike.congr` over a
`congrArg` rather than `rfl`: the two sides differ only in the last factor of the argument of the
bijection, and `DFunLike.congr` splits the equality into the bijection and its argument, which
localizes each object-level defeq check instead of letting one run through the bijection.

## References

* [Stacks Project, Tag 0FXP](https://stacks.math.columbia.edu/tag/0FXP)
* [Stacks Project, Tag 0FXZ](https://stacks.math.columbia.edu/tag/0FXZ)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 0FPC](https://stacks.math.columbia.edu/tag/0FPC)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry
open Stacks.SheafOfModules.DerivedMonoidal

universe u

namespace Stacks.Cohomology.DerivedKunnethExt

attribute [local instance] HasDerivedCategory.standard

-- Every statement here reaches the ring sheaf through the Mathlib accessor
-- `AlgebraicGeometry.SheafedSpace.sheaf` in the object `Z.sheaf`, while the abelian and
-- derived-category instances are registered at `Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf`,
-- which reduces to `(CategoryTheory.sheafCompose _ _).obj Z.sheaf`; instance search does not reach
-- them through the accessor without these two.  Same line, for the same reason, as in
-- `StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackInvertibility`.
-- Not a spelling bridge: every statement below writes the bijection of [Stacks, Tag 08DI] at the
-- ringed site's own name, which is what makes its instance arguments agree syntactically.
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

section OneSpace

variable (Z : RingedSpace.{u, u})
  [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-! ### Stacks 08J8 as an adjunction for the tensor product of the monoidal structure -/

/-- **Stacks 08J8 as an adjunction for the derived tensor product of Stacks 06YU that the
symmetric monoidal structure of Stacks 0FPT is seated on**: `- ⊗^𝐋_{𝒪_Z} B ⊣ R𝓗om(B, -)`.

`AlgebraicGeometry.RingedSite.derivedTensorSheafHomAdjunction` is this adjunction for the other
of the two derived tensor products a ringed site carries;
`CategoryTheory.MonoidalCategory.reseatTensorRightAdjunction` moves it along
`Stacks.Cohomology.DerivedKunnethExt.tensorBridge`. -/
@[sga "5 IIIB 5.2" "special case"]
def sheafHomAdjunction (B : DerivedCategory (Mod Z.sheaf)) :
    @CategoryTheory.MonoidalCategory.tensorRight (DerivedCategory (Mod Z.sheaf)) _
        (canonicalDerivedMonoidal Z.sheaf) B ⊣
      (AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor
          (Stacks.SheafOfModules.ringedSite Z.sheaf)).obj (op B) :=
  reseatTensorRightAdjunction (derivedMonoidal Z.sheaf) (monoidalTensorCanonicalIso Z.sheaf)
    (canonicalUnitIso Z.sheaf) (tensorBridge Z) B
    (AlgebraicGeometry.RingedSite.derivedTensorSheafHomAdjunction
      (Stacks.SheafOfModules.ringedSite Z.sheaf) B)

/-- **The comparison of the two derived tensor products cancels at `(R𝓗om(B, Y), B)`.**  It is
an isomorphism of bifunctors, so this is `CategoryTheory.Iso.hom_inv_id_app` evaluated at the
second variable.  The identity is at the derived tensor product the bijection of Stacks 08DI is
stated over, which is the source of the comparison. -/
private theorem tensorBridge_hom_inv_app_app (B Y : DerivedCategory (Mod Z.sheaf)) :
    ((tensorBridge Z).hom.app (sheafHomObj Z B Y)).app B ≫
        ((tensorBridge Z).inv.app (sheafHomObj Z B Y)).app B =
      𝟙 (((Stacks.SheafOfModules.derivedTensorProductFunctor
        (Stacks.SheafOfModules.ringedSite Z.sheaf)).obj (sheafHomObj Z B Y)).obj B) := by
  rw [← NatTrans.comp_app, (tensorBridge Z).hom_inv_id_app, NatTrans.id_app]

/-- The evaluation morphism `R𝓗om(B, Y) ⊗^𝐋_{𝒪_Z} B ⟶ Y`, in the ringed-site spelling of the
bijection of Stacks 08DI. -/
theorem sheafHomEval_eq (B Y : DerivedCategory (Mod Z.sheaf)) :
    sheafHomEval Z B Y =
      ((tensorBridge Z).inv.app (sheafHomObj Z B Y)).app B ≫
        AlgebraicGeometry.RingedSite.derivedCurryHomEquiv
          (Stacks.SheafOfModules.ringedSite Z.sheaf) (sheafHomObj Z B Y) B Y
          (𝟙 (sheafHomObj Z B Y)) := by
  rw [sheafHomEval]

/-- The hom-set bijection of `Stacks.Cohomology.DerivedKunnethExt.sheafHomAdjunction` is the
bijection of Stacks 08DI read across the comparison of the two derived tensor products, in the
ringed-site spelling. -/
theorem sheafHomAdjunction_homEquiv_curry (B A Y : DerivedCategory (Mod Z.sheaf))
    (f : tensorObj Z A B ⟶ Y) :
    (sheafHomAdjunction Z B).homEquiv A Y f =
      (AlgebraicGeometry.RingedSite.derivedCurryHomEquiv
        (Stacks.SheafOfModules.ringedSite Z.sheaf) A B Y).symm
        (((tensorBridge Z).hom.app A).app B ≫ f) := by
  rw [sheafHomAdjunction, reseatTensorRightAdjunction_homEquiv,
    AlgebraicGeometry.RingedSite.derivedTensorSheafHomAdjunction,
    Adjunction.mkOfHomEquiv_homEquiv]
  simp only [Equiv.coe_fn_mk]

/-- **The counit of `Stacks.Cohomology.DerivedKunnethExt.sheafHomAdjunction` is the evaluation
morphism** `Stacks.Cohomology.DerivedKunnethExt.sheafHomEval`. -/
theorem sheafHomAdjunction_counit_app (B Y : DerivedCategory (Mod Z.sheaf)) :
    (sheafHomAdjunction Z B).counit.app Y = sheafHomEval Z B Y := by
  have hkey : (sheafHomAdjunction Z B).homEquiv (sheafHomObj Z B Y) Y (sheafHomEval Z B Y) =
      𝟙 (sheafHomObj Z B Y) := by
    rw [sheafHomAdjunction_homEquiv_curry, sheafHomEval_eq, ← Category.assoc,
      tensorBridge_hom_inv_app_app, Category.id_comp]
    exact (AlgebraicGeometry.RingedSite.derivedCurryHomEquiv
      (Stacks.SheafOfModules.ringedSite Z.sheaf) (sheafHomObj Z B Y) B
      Y).symm_apply_apply _
  have h4 : ((sheafHomAdjunction Z B).homEquiv (sheafHomObj Z B Y) Y).symm
      (𝟙 (sheafHomObj Z B Y)) = sheafHomEval Z B Y := by
    rw [← hkey, Equiv.symm_apply_apply]
  have hid : (@CategoryTheory.MonoidalCategory.tensorRight (DerivedCategory (Mod Z.sheaf)) _
          (canonicalDerivedMonoidal Z.sheaf) B).map (𝟙 (sheafHomObj Z B Y)) ≫
        (sheafHomAdjunction Z B).counit.app Y =
      (sheafHomAdjunction Z B).counit.app Y := by
    rw [CategoryTheory.Functor.map_id]
    exact Category.id_comp ((sheafHomAdjunction Z B).counit.app Y)
  exact ((Adjunction.homEquiv_counit (sheafHomAdjunction Z B) (sheafHomObj Z B Y) Y
    (𝟙 (sheafHomObj Z B Y))).trans hid).symm.trans h4

/-! ### The exact pairing of Stacks 0FPC for that monoidal structure -/

/-- **The exact pairing of Stacks 0FPC, for the monoidal structure whose tensor product is the
derived tensor product of Stacks 06YU.**  For a perfect `K` the coevaluation and the evaluation
of `Stacks.SheafOfModules.exactPairingDerivedDual` make `K^∨ = R𝓗om(K, 𝒪_Z)` a left dual of `K`;
that pairing is stated for `Stacks.SheafOfModules.derivedMonoidalStructure`, and both it and
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal` re-seat the monoidal derived
category of Stacks 0FPT along the same unit comparison, so
`CategoryTheory.MonoidalCategory.reseatExactPairing` carries it across. -/
@[instance_reducible]
def exactPairingCanonical (K : DerivedCategory (Mod Z.sheaf))
    (hK : (Stacks.SheafOfModules.ringedSite Z.sheaf).IsPerfect K) :
    @CategoryTheory.ExactPairing (DerivedCategory (Mod Z.sheaf)) _
      (canonicalDerivedMonoidal Z.sheaf) K (Stacks.SheafOfModules.derivedDual Z.sheaf K) :=
  reseatExactPairing (derivedMonoidal Z.sheaf)
    (Stacks.SheafOfModules.derivedTensorMonoidalIso Z.sheaf)
    (monoidalTensorCanonicalIso Z.sheaf) (canonicalUnitIso Z.sheaf) K
    (Stacks.SheafOfModules.derivedDual Z.sheaf K)
    (Stacks.SheafOfModules.exactPairingDerivedDual Z.sheaf K hK)

/-! ### The morphism of Stacks 0FXP is the abstract comparison -/

/-- The flip of the middle two factors `Stacks.Cohomology.DerivedKunnethExt.middleFour` is the
interchange `CategoryTheory.MonoidalCategory.tensorμ` of the re-seated symmetric monoidal
structure. -/
theorem middleFour_eq_tensorMu (H G A B : DerivedCategory (Mod Z.sheaf)) :
    middleFour Z H G A B =
      @tensorμ (DerivedCategory (Mod Z.sheaf)) _ (canonicalDerivedMonoidal Z.sheaf)
        (canonicalDerivedSymmetric Z.sheaf).toBraidedCategory H G A B :=
  rfl

/-- The derived tensor product `Stacks.Cohomology.DerivedKunnethExt.tensorMap` of two morphisms
is their tensor product for the re-seated monoidal structure. -/
theorem tensorMap_eq_tensorHom {A A' B B' : DerivedCategory (Mod Z.sheaf)} (x : A ⟶ A')
    (y : B ⟶ B') :
    tensorMap Z x y =
      @MonoidalCategoryStruct.tensorHom (DerivedCategory (Mod Z.sheaf)) _
        (canonicalDerivedMonoidal Z.sheaf).toMonoidalCategoryStruct _ _ _ _ x y :=
  rfl

/-- The morphism of Stacks 0FXP, in the ringed-site spelling of the bijection of
Stacks 08DI. -/
theorem sheafHomTensorMap_eq_curry (A A' B B' : DerivedCategory (Mod Z.sheaf)) :
    sheafHomTensorMap Z A A' B B' =
      (AlgebraicGeometry.RingedSite.derivedCurryHomEquiv
          (Stacks.SheafOfModules.ringedSite Z.sheaf)
          (tensorObj Z (sheafHomObj Z A A') (sheafHomObj Z B B')) (tensorObj Z A B)
          (tensorObj Z A' B')).toEquiv.symm
        (((tensorBridge Z).hom.app
              (tensorObj Z (sheafHomObj Z A A') (sheafHomObj Z B B'))).app (tensorObj Z A B) ≫
          middleFour Z (sheafHomObj Z A A') (sheafHomObj Z B B') A B ≫
          tensorMap Z (sheafHomEval Z A A') (sheafHomEval Z B B')) := by
  rw [sheafHomTensorMap]

/-- **The morphism of Stacks 0FXP is the comparison of
`Stacks.DerivedTensorHomDiagonal.homTensorComparison` at the three adjunctions of
Stacks 08J8.**  Both are the morphism adjoint to the interchange of the two middle factors
followed by the tensor product of the two evaluations: `middleFour` *is* `tensorμ`, `tensorMap`
*is* the monoidal tensor product of morphisms, and the counit of `sheafHomAdjunction` *is*
`sheafHomEval`. -/
theorem sheafHomTensorMap_eq (A A' B B' : DerivedCategory (Mod Z.sheaf)) :
    sheafHomTensorMap Z A A' B B' =
      @Stacks.DerivedTensorHomDiagonal.homTensorComparison (DerivedCategory (Mod Z.sheaf)) _
        (canonicalDerivedMonoidal Z.sheaf) (canonicalDerivedSymmetric Z.sheaf) A B _ _ _
        (sheafHomAdjunction Z A) (sheafHomAdjunction Z B)
        (sheafHomAdjunction Z (tensorObj Z A B)) A' B' := by
  let := canonicalDerivedMonoidal Z.sheaf
  let := canonicalDerivedSymmetric Z.sheaf
  have hten : tensorMap Z (sheafHomEval Z A A') (sheafHomEval Z B B') =
      @MonoidalCategoryStruct.tensorHom (DerivedCategory (Mod Z.sheaf)) _
        (canonicalDerivedMonoidal Z.sheaf).toMonoidalCategoryStruct _ _ _ _
        ((sheafHomAdjunction Z A).counit.app A') ((sheafHomAdjunction Z B).counit.app B') := by
    conv_rhs => rw [sheafHomAdjunction_counit_app Z B B']
    conv_rhs => rw [sheafHomAdjunction_counit_app Z A A']
    exact tensorMap_eq_tensorHom Z _ _
  unfold Stacks.DerivedTensorHomDiagonal.homTensorComparison
  rw [sheafHomAdjunction_homEquiv_curry, ← middleFour_eq_tensorMu]
  conv_lhs => rw [sheafHomTensorMap_eq_curry]
  exact DFunLike.congr rfl (congrArg (((tensorBridge Z).hom.app
      (tensorObj Z (sheafHomObj Z A A') (sheafHomObj Z B B'))).app (tensorObj Z A B) ≫
    middleFour Z (sheafHomObj Z A A') (sheafHomObj Z B B') A B ≫ ·) hten)

/-! ### Invertibility at perfect objects -/

/-- **The morphism of Stacks 0FXP is an isomorphism when `A` and `B` are perfect.**  For objects
`A`, `A'`, `B`, `B'` of `D(𝒪_Z)` on a ringed space with `A` and `B` perfect, the canonical
morphism

`R𝓗om(A, A') ⊗^𝐋_{𝒪_Z} R𝓗om(B, B') ⟶ R𝓗om(A ⊗^𝐋_{𝒪_Z} B, A' ⊗^𝐋_{𝒪_Z} B')`

is invertible: a perfect object is dualizable by Stacks 0FPC, and
`Stacks.DerivedTensorHomDiagonal.isIso_homTensorComparison` inverts the comparison at dualizable
objects.  Perfectness is in the ringed-site sense of Stacks 08G5 here; see
`isIso_sheafHomTensorMap_of_isPerfect_space` for the ringed-space sense of Stacks 08CM. -/
theorem isIso_sheafHomTensorMap_of_isPerfect (A A' B B' : DerivedCategory (Mod Z.sheaf))
    (hA : (Stacks.SheafOfModules.ringedSite Z.sheaf).IsPerfect A)
    (hB : (Stacks.SheafOfModules.ringedSite Z.sheaf).IsPerfect B) :
    IsIso (sheafHomTensorMap Z A A' B B') := by
  rw [sheafHomTensorMap_eq]
  exact @Stacks.DerivedTensorHomDiagonal.isIso_homTensorComparison
    (DerivedCategory (Mod Z.sheaf)) _ (canonicalDerivedMonoidal Z.sheaf)
    (canonicalDerivedSymmetric Z.sheaf) A B (Stacks.SheafOfModules.derivedDual Z.sheaf A)
    (Stacks.SheafOfModules.derivedDual Z.sheaf B) (exactPairingCanonical Z A hA)
    (exactPairingCanonical Z B hB) _ _ _ (sheafHomAdjunction Z A) (sheafHomAdjunction Z B)
    (sheafHomAdjunction Z (tensorObj Z A B)) A' B'

/-- **The morphism of Stacks 0FXP is an isomorphism when `A` and `B` are perfect in the sense of
Stacks 08CM**, the perfectness of an object of the derived category of a ringed space.  This is
`isIso_sheafHomTensorMap_of_isPerfect` after
`Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect`. -/
@[sga "5 III 6.3" "more general"]
theorem isIso_sheafHomTensorMap_of_isPerfect_space (A A' B B' : DerivedCategory (Mod Z.sheaf))
    (hA : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Z) A)
    (hB : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Z) B) :
    IsIso (sheafHomTensorMap Z A A' B B') :=
  isIso_sheafHomTensorMap_of_isPerfect Z A A' B B'
    (Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect Z A hA)
    (Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect Z B hB)

end OneSpace

end Stacks.Cohomology.DerivedKunnethExt

end
