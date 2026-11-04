module

public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulExtDegreeZero
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulExtStructureStalkDual
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulIteratedContractionClass
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulSelfExtExteriorCriterion

/-!
# The exterior-power description of self-Ext for a Koszul-regular ideal

Let `Y` be a ringed space, let `𝓘 ⊂ O_Y` be a sheaf of ideals and set `O_X = O_Y/𝓘`. Stacks
0BQY asserts that if `𝓘` is Koszul-regular then composition on `RHom_{O_Y}(O_X, O_X)` defines
isomorphisms

`⋀ⁱ(Ext¹_{O_Y}(O_X, O_X)) ⟶ Extⁱ_{O_Y}(O_X, O_X)`

for every `i`. This file records which parts of that assertion the development establishes, each
against the clause it covers. The parts live in the modules imported above; nothing is restated
here.

**The full assertion is
`Stacks.AlgebraicGeometry.RegularIdealSheaf.isIso_desc_app_isKoszulRegularIdealSheaf` of
`StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulSelfExtKoszulRegular`**, over an arbitrary
Koszul-regular sheaf of ideals on a ringed space and for the model-free self-Ext algebra. The
parts listed below are the pieces of its proof, each stated at the hypothesis it needs: for an
ideal sheaf presented *globally* by a Koszul-regular sequence the comparison of the Koszul model
is an isomorphism in every degree — negative, zero and positive — by
`Stacks.RegularSequence.KoszulChainData.isIso_extComparison_forall`, and on an open where the
tag's own hypothesis holds this is
`Stacks.AlgebraicGeometry.RegularIdealSheaf.forall_isIso_extComparison_of_isKoszulSequenceExactOn`.
Each entry below says which part of the assertion it covers; none of them is registered under
the tag.

## What is established

* `Stacks.RegularSequence.KoszulChainData.extSelfAlgebra` — the sheaf of graded `O_X`-algebras
  that composition defines on the self-Ext sheaves.
* `Stacks.RegularSequence.KoszulChainData.extComparison` and
  `extComparison_app_homogeneousProd` — the comparison map of the tag, and the fact that it is
  the map composition induces.
* `Stacks.RegularSequence.KoszulChainData.squareZero_id_homologyGradedAlgebra` — degree-one
  classes square to zero, which is what lets the comparison factor through the exterior power.
* `Stacks.RegularSequence.KoszulChainData.isExteriorAlgebra_extSelfAlgebra_iff_bijective_stalkMap`
  — the reduction of the tag to bijectivity of the stalk maps of the comparison.
* `Stacks.RegularSequence.KoszulChainData.homogeneousProd_contractionClassOn` and
  `SheafOfModules.TensorExteriorSymmetricAlgebras.listContractionDual_exteriorKoszulStalkEquiv` —
  the two halves of the local computation: a composition product of degree-one contraction classes
  is an iterated contraction on cocycles, and an iterated contraction at a stalk is the duality
  pairing.
* `Stacks.RegularSequence.KoszulChainData.extStructureStalkDualEquiv` — the stalk of `Extⁱ` has
  the shape the tag asserts for it.
* `Stacks.RegularSequence.KoszulChainData.extExteriorPowerZeroIsoExtZero` — in degree zero the two
  sides are isomorphic, by the degree-zero identifications rather than by the comparison map.
* `Stacks.RegularSequence.KoszulChainData.isIso_extComparison_forall` and
  `isExteriorAlgebra_extSelfAlgebra` — the comparison of the Koszul model is an isomorphism in
  every degree, for an ideal sheaf presented globally by a Koszul-regular sequence. The two links
  this needs — evaluating the Ext identification on a class, and the
  linearity of the stalk identification — are proved; the bijectivity of the stalk maps is
  `bijective_stalkMapL_extComparison_succ` and goes through
  `Koszul.bijective_of_listContractionDual_proj_rev`.
* `AlgebraicGeometry.RegularIdealSheaf.forall_isIso_extComparison_of_isKoszulSequenceExactOn` — the
  same conclusion on an open where the tag's own hypothesis, Divisors 063D part (2), holds.

## How the parts above become the tag

Two steps, neither of them in the local computation, and both proved.

**One: from the Koszul model to the model-free algebra.** The pieces of `extSelfAlgebra` are the
Ext sheaves, but its multiplication is the composition product of the internal Hom complex of the
Koszul complex, read through `Stacks.RegularSequence.KoszulChainData.homIso`, whereas the tag's
statement is about the algebra `Stacks.SheafOfModules.selfExtAlgebra` — the composition product
of a chosen K-injective model, which mentions no resolution of the quotient at all.
`Stacks.SheafOfModules.selfExtAlgebraIsoOfStrictlyPerfect` of
`StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulSelfExtKInjectiveModel` identifies the two
for any strictly perfect complex presenting the object, naming neither a K-injective complex nor
a comparison morphism, and the Koszul complex is strictly perfect; the Koszul-side conclusion in
that form is `Stacks.RegularSequence.KoszulChainData.isIso_extComparisonOfKInjectiveModel`.

**Two: gluing the local statements.** `IsKoszulRegularIdealSheaf` hands over, near every point of
the support, an open and a sequence satisfying the hypothesis of
`forall_isIso_extComparison_of_isKoszulSequenceExactOn`, and
`Stacks.AlgebraicGeometry.RegularIdealSheaf.coversTop_koszulPresentation` makes those opens a
covering family of `Y`. Over each of them the restriction of the descended composition-product
algebra is the exterior algebra of its own degree-one piece, and
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.isIso_desc_app_of_coversTop` turns that into
invertibility in every degree on `Y`.

## References

* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
-/

@[expose] public section

end
