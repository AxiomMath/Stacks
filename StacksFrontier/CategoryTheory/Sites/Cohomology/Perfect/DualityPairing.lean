module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurrying
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDual
import StacksCore.Tactic.StacksAttribute

/-! # The duality pairing of an object of `D(O)` and its dual

Let `(C, O)` be a ringed site and let `K` be an object of `D(O)` with dual
`K^∨ = RSheafHom(K, O)` (`AlgebraicGeometry.RingedSite.derivedDual`). **Stacks 0FPU** names two
morphisms attached to this pair,

`ε : K^∨ ⊗^L_O K ⟶ O`  and  `η : O ⟶ K ⊗^L_O K^∨`,

and asserts that `(K^∨, η, ε)` is a left dual of `K` when `K` is perfect.

The **evaluation** `ε` is constructed here, for an arbitrary object `K`, with no perfectness
hypothesis: it is the morphism which the tensor–internal-Hom bijection of Stacks 08J8,
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv`, matches with the identity of `K^∨`. That is
the defining property of evaluation, and it is what `derivedDualEvaluation_eq` records. The
source's parenthetical "to construct it you can use Lemma 0A98 for example" offers a different
route and does not pin `ε` to it; the two are not compared below.

The **coevaluation** `η` is the section corresponding to `id_K` under the comparison
`K ⊗^L_O K^∨ ⟶ RSheafHom(K, K)`, which the source asserts to be an isomorphism by citing
Stacks 08JJ. It is constructed here from the invertibility of that comparison taken as a
hypothesis, so the construction applies to an arbitrary object and carries no tag. That
hypothesis is **discharged** for a perfect `K`, by
`AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_of_isPerfect` of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCompositionPerfect`, which is the
third assertion of Stacks 08JJ/08DQ; the resulting unconditional coevaluation of a perfect
object, on a ringed space, is `Stacks.SheafOfModules.derivedDualCoevaluation` of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectCoevaluation`, the coevaluation of
Example 0FPC (`Stacks.SheafOfModules.derivedDual_isLeftDual`).

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedStructureSheafGlobalSectionsEquiv`: morphisms `O ⟶ Z` in
  `D(O)` are the degree-zero global hypercohomology classes of `Z`.
* `AlgebraicGeometry.RingedSite.derivedIdentitySection`: the morphism `O ⟶ RSheafHom(K, K)`
  corresponding to `id_K`, that is, "the section corresponding to `id_K`" of the source.
* `AlgebraicGeometry.RingedSite.derivedDualEvaluation`: **Stacks 0FPU**, the evaluation
  `ε : K^∨ ⊗^L_O K ⟶ O`.
* `AlgebraicGeometry.RingedSite.derivedDualCoevaluation`: the coevaluation
  `η : O ⟶ K ⊗^L_O K^∨`, given that the comparison `K ⊗^L_O K^∨ ⟶ RSheafHom(K, K)` of
  Stacks 08JD is invertible.

## Main results

* `AlgebraicGeometry.RingedSite.derivedIdentitySection_eq`: `derivedIdentitySection` is the
  class of `id_K` under the two identifications of Stacks 08JA.
* `AlgebraicGeometry.RingedSite.derivedDualEvaluation_eq`: the evaluation is the morphism
  matched with `id_{K^∨}` by Stacks 08J8. This pins it down: it is not an unconstrained morphism
  of its type.
* `AlgebraicGeometry.RingedSite.derivedDualCoevaluation_comp`: the coevaluation followed by the
  comparison of Stacks 08JD is `derivedIdentitySection`. This pins it down in the same way, and
  is the source's defining property of `η`.

## The three further assertions, and where they are

Stacks 0FPU has three further assertions beyond the two morphisms. **All three are proved**, over
an arbitrary ringed site, in
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DerivedDualLeftDual`:
`AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_self`,
`AlgebraicGeometry.RingedSite.coevaluation` and the two triangle identities
`AlgebraicGeometry.RingedSite.evaluation_coevaluation` and
`AlgebraicGeometry.RingedSite.coevaluation_evaluation`, which assemble into the left-dual
assertion `AlgebraicGeometry.RingedSite.derivedDualExactPairing`.  None of them is restated here,
for the reason each item below gives: this file is about an arbitrary object of `D(O)` and takes
the invertibility of the comparison as a hypothesis precisely so as not to depend on
perfectness.

* that the comparison `K ⊗^L_O K^∨ ⟶ RSheafHom(K, K)` is an isomorphism for perfect `K`. This
  is the third assertion of Stacks 08JJ, which the source cites rather than proves. It **is** in
  this library, as
  `AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_of_isPerfect` of
  `StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCompositionPerfect`, for an
  arbitrary derived tensor product datum and with perfectness of the source as the only
  hypothesis. (The route it takes is not the source's step (5) but the replacement of
  invertibility of the derived morphism by quasi-isomorphy of a morphism of complexes at one
  choice of models, which is local on the site; the "What this file does not contain" note of
  `StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.Duals`, which recorded the bridge from
  the module-level statement as the missing input, is superseded by it.) It is not restated
  here, because this file is about an arbitrary object and takes invertibility as a hypothesis
  precisely so as not to depend on perfectness.
* that `η` exists for every perfect `K`. `derivedDualCoevaluation` below takes the invertibility
  of the comparison as a hypothesis, so it is stated for an arbitrary object and carries no
  `@[stacks 0FPU]` attribute; feeding it the previous item gives the source's statement, and on
  a ringed space that assembly is `Stacks.SheafOfModules.derivedDualCoevaluation` of
  `StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectCoevaluation`. It is a
  construction with a real body rather than a choice from an existence statement, and
  `derivedDualCoevaluation_comp` identifies it.
* the two triangle identities `(1 ⊗ ε) ∘ (η ⊗ 1) = id_K` and `(ε ⊗ 1) ∘ (1 ⊗ η) = id_{K^∨}`,
  hence also the left-dual assertion itself. On a ringed space, in the monoidal structure of
  Stacks 0FPT, they are `Stacks.SheafOfModules.derivedDual_isLeftDual`.

Only the evaluation is therefore tagged here, under the suffix `"evaluation"`; the suffixes
`"coevaluation"` and `"left_dual"` are carried by
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DerivedDualLeftDual`.

## Implementation notes

The derived tensor product is the canonical one,
`Stacks.SheafOfModules.canonicalDerivedTensorProduct`, whose bifunctor is
`Stacks.SheafOfModules.derivedTensorProductFunctor`. It is instantiated rather than carried as a
parameter because the two inputs meet only there: Stacks 08J8,
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv`, is stated for that bifunctor, while
`AlgebraicGeometry.RingedSite.derivedTensorDualToSheafHom` is stated for an arbitrary derived
tensor product datum, so `derivedDualEvaluation` and `derivedDualCoevaluation` have tensor
factors of the same spelling only at the canonical datum.

The identification of morphisms out of the structure sheaf with global hypercohomology classes
is Stacks 08JA, `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv`, at source the
structure sheaf, transported along `RSheafHom(O, -) ≅ 𝟭`
(`AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso`). It is the same route by which
Stacks 08JD passes from the comparison morphism to its map on morphism groups, so no second
spelling of `H⁰(C, -)` enters.

`derivedIdentitySection_eq` and `derivedDualEvaluation_eq` state the pinning in the forward
direction, as definitional equations, rather than as round trips such as
`(derivedCurryHomEquiv …).symm (derivedDualEvaluation X K) = 𝟙 _`. A round trip is the same fact,
the identifications being bijections, but elaborating it applies the coercion of a morphism-group
`AddEquiv` to a term that is itself such an application, and at these arguments that exhausts the
recursion depth; raising the limit with an option is a workaround this development does not
accept. This is the same obstruction that
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedDiagonal` records for the
corresponding equation of Stacks 0A99, and the reason it names the definition itself as what
pins the morphism down.

The universes are the diagonal `RingedSite.{u, u, u}` of the whole derived-internal-Hom cluster,
with the derived category the standard one; this is what Stacks 08JA, Stacks 08J8 and
Stacks 08JD are stated at, and is not a narrowing introduced here.

## References

* [Stacks Project, Tag 0FPU](https://stacks.math.columbia.edu/tag/0FPU)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 08JD](https://stacks.math.columbia.edu/tag/08JD)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 0A98](https://stacks.math.columbia.edu/tag/0A98)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **Morphisms out of the structure sheaf are global hypercohomology classes.** For an object
`Z` of `D(O)` the group `H⁰(C, Z)` is the group of morphisms `O ⟶ Z` in `D(O)`: this is
Stacks 08JA at source the structure sheaf, read through the identification
`RSheafHom(O, Z) ≅ Z` of the derived internal Hom out of the structure sheaf. -/
def derivedStructureSheafGlobalSectionsEquiv
    (Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
        ((derivedModuleGlobalSections X).obj Z) : Type u) ≃+
      (derivedStructureSheaf X ⟶ Z) :=
  (((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).mapIso
        ((derivedModuleGlobalSections X).mapIso
          (derivedStructureSheafHomIso X Z).symm)).addCommGroupIsoToAddEquiv).trans
    (derivedSheafHomGlobalSectionsEquiv X (derivedStructureSheaf X) Z)

/-- **The section corresponding to `id_K`.** For an object `K` of `D(O)` this is the morphism
`O ⟶ RSheafHom(K, K)` which the identifications `Hom(O, RSheafHom(K, K)) = H⁰(C, RSheafHom(K, K))`
and `H⁰(C, RSheafHom(K, K)) = Hom(K, K)` of Stacks 08JA carry to the identity of `K`. -/
def derivedIdentitySection
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    derivedStructureSheaf X ⟶ ((derivedSheafHomBifunctor X).obj (op K)).obj K :=
  derivedStructureSheafGlobalSectionsEquiv X (((derivedSheafHomBifunctor X).obj (op K)).obj K)
    ((derivedSheafHomGlobalSectionsEquiv X K K).symm (𝟙 K))

/-- **`derivedIdentitySection` is the section corresponding to `id_K`.** It is the class of the
identity of `K` under the two identifications of Stacks 08JA, which pins it down: it is not an
unconstrained morphism of its type, and since both identifications are bijections it is zero
only if the identity of `K` is. -/
theorem derivedIdentitySection_eq
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    derivedIdentitySection X K =
      derivedStructureSheafGlobalSectionsEquiv X
        (((derivedSheafHomBifunctor X).obj (op K)).obj K)
          ((derivedSheafHomGlobalSectionsEquiv X K K).symm (𝟙 K)) :=
  rfl

/-- **Stacks 0FPU: the evaluation map.** For an object `K` of `D(O)` with dual
`K^∨ = RSheafHom(K, O)` the evaluation is the morphism

`ε : K^∨ ⊗^L_O K ⟶ O`

matched with the identity of `K^∨` by the tensor–internal-Hom bijection of Stacks 08J8, under
which morphisms `K^∨ ⊗^L_O K ⟶ O` are morphisms `K^∨ ⟶ RSheafHom(K, O) = K^∨`. No perfectness
hypothesis is needed: evaluation exists for every object of `D(O)`. -/
@[stacks 0FPU "evaluation"]
def derivedDualEvaluation
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj (derivedDual X K)).obj K ⟶
      derivedStructureSheaf X :=
  derivedCurryHomEquiv X (derivedDual X K) K (derivedStructureSheaf X) (𝟙 (derivedDual X K))

/-- **The evaluation map is the image of the identity of `K^∨` under Stacks 08J8.** This pins
`derivedDualEvaluation` down: it is not an unconstrained morphism of its type, and since the
bijection of Stacks 08J8 is injective it is zero only if the identity of `K^∨` is. -/
theorem derivedDualEvaluation_eq
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    derivedDualEvaluation X K =
      derivedCurryHomEquiv X (derivedDual X K) K (derivedStructureSheaf X)
        (𝟙 (derivedDual X K)) :=
  rfl

/-- **The coevaluation map**, given that the comparison of Stacks 08JD at `K` is invertible.
For an object `K` of `D(O)` whose comparison

`K ⊗^L_O K^∨ ⟶ RSheafHom(K, K)`

is an isomorphism, the coevaluation is the morphism `η : O ⟶ K ⊗^L_O K^∨` corresponding to
`id_K`, that is, `derivedIdentitySection` followed by the inverse of the comparison.

Stacks 0FPU states this for a perfect `K`, where the invertibility is the third assertion of
Stacks 08JJ. That assertion is
`AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_of_isPerfect`; the invertibility
is kept as a hypothesis here so that the construction applies to an arbitrary object, and this
declaration therefore carries no `@[stacks 0FPU]` attribute. The assembly for a perfect object
on a ringed space is `Stacks.SheafOfModules.derivedDualCoevaluation` of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectCoevaluation`. -/
def derivedDualCoevaluation
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (h : IsIso (derivedTensorDualToSheafHom X
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) K K)) :
    derivedStructureSheaf X ⟶
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj (derivedDual X K) :=
  haveI := h
  derivedIdentitySection X K ≫
    inv (derivedTensorDualToSheafHom X
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) K K)

/-- **The coevaluation map corresponds to `id_K`.** Composing it with the comparison of
Stacks 08JD gives back the section corresponding to the identity of `K`, which is the source's
defining property of `η`. This pins `derivedDualCoevaluation` down. -/
theorem derivedDualCoevaluation_comp
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (h : IsIso (derivedTensorDualToSheafHom X
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) K K)) :
    derivedDualCoevaluation X K h ≫
        derivedTensorDualToSheafHom X
          (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) K K =
      derivedIdentitySection X K := by
  have := h
  change (derivedIdentitySection X K ≫
      inv (derivedTensorDualToSheafHom X
        (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) K K)) ≫
      derivedTensorDualToSheafHom X
        (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) K K =
    derivedIdentitySection X K
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

end AlgebraicGeometry.RingedSite

end
