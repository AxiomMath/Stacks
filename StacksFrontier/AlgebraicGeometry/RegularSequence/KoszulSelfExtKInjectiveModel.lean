module

public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulSelfExtAlgebraModelDescent
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulSelfExtExteriorLocal
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulStrictPerfection
public import StacksFrontier.Homology.Injectives.KInjective.RealizeDerivedIso

/-!
# The self-Ext algebra of a Koszul-regular quotient needs no chosen comparison morphism

`StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulSelfExtAlgebraModelDescent` transfers the
exterior-algebra conclusion from the Koszul model of the self-Ext algebra to a K-injective one,
but it takes the comparison `κ : cochain Rc K ⟶ I` between the two as a hypothesis: a
quasi-isomorphism from the Koszul cochain complex into the K-injective complex, given by name.
Nothing produced such a morphism, and in the situation the local-to-global step of
[Stacks, Tag 0BQY] is in there is none to name — the K-injective complex there is the restriction
to an open of a resolution chosen on the whole space, and all that is known of it is which object
of the derived category it presents.

This file removes the hypothesis. An isomorphism in the derived category whose target is
K-injective is realized by a quasi-isomorphism of complexes
(`CochainComplex.exists_quasiIso_of_isKInjective_of_iso`), so a derived-category identification
is all that has to be supplied; and the Koszul cochain complex is strictly perfect
(`Stacks.RegularSequence.KoszulChainData.finite_not_isZero_cochain_X` and
`isFiniteFreeSummand_cochain_X`), so the strict-perfection hypotheses are discharged as well.
What is left is a statement about the Koszul chain datum alone, with the K-injective model chosen
canonically by `Stacks.SheafOfModules.kInjectiveModel`.

## Main definitions

* `Stacks.SheafOfModules.selfExtAlgebraIsoOfStrictlyPerfect`: **the self-Ext algebra of an object
  of `D(O_X)` admitting a strictly perfect model is the composition-product algebra of that
  model**, with no K-injective complex and no comparison morphism in the statement.
* `Stacks.RegularSequence.KoszulChainData.kInjectiveComparison`: the chosen quasi-isomorphism from
  the Koszul cochain complex to the canonical K-injective model of the object it presents.
* `Stacks.RegularSequence.KoszulChainData.selfExtAlgebraOfKInjectiveModel`: the self-Ext algebra
  of the quotient over the quotient, with the composition product of that canonical model.
* `Stacks.RegularSequence.KoszulChainData.extComparisonOfKInjectiveModel`: the comparison map of
  Stacks 0BQY for it.

## Main results

* `Stacks.RegularSequence.KoszulChainData.isExteriorAlgebra_selfExtAlgebraOfKInjectiveModel` and
  `Stacks.RegularSequence.KoszulChainData.isIso_extComparisonOfKInjectiveModel`: for an ideal
  sheaf presented globally by a Koszul-regular sequence, the self-Ext algebra read with the
  composition product of a canonical K-injective model is an exterior algebra on its degree-one
  piece, and the comparison map is an isomorphism in every degree. Neither statement mentions a
  model or a comparison morphism.

## Implementation notes

**Why a derived-category identification is the right hypothesis.**
`Stacks.SheafOfModules.extSelfGradedAlgebra` is built from a K-injective complex `I` together with
`ε : Q(I) ≅ A`, so an object of the derived category and a presentation of it are already the
data the construction runs on. Asking in addition for a chain map out of a strictly perfect model
is asking for something the derived-category data determines, and
`CochainComplex.realizeDerivedIso` produces it. The two hypotheses `hbdd` and `hterm` of
`Stacks.SheafOfModules.extSelfComparisonIsoOfStrictlyPerfect` are kept where the complex is
arbitrary, and discharged where it is the Koszul one.

## References

* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace
open AlgebraicGeometry HomologicalComplex Stacks.ChainComplex

universe u

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology ↥X).WEqualsLocallyBijective AddCommGrpCat.{u}]

section DerivedIso

variable (K I : CochainComplex (StructureSheafModules Rc) ℤ) [I.IsKInjective]
  (hbdd : {i : ℤ | ¬ IsZero (K.X i)}.Finite)
  (hterm : ∀ i, RingedSite.IsFiniteFreeSummand (ringedSite Rc) (K.X i))

/-- **The two models of the self-Ext algebra are isomorphic as sheaves of graded algebras, from a
derived-category identification alone.**
`Stacks.SheafOfModules.modelComparisonIsoOfStrictlyPerfect` with its comparison morphism supplied
by `CochainComplex.realizeDerivedIso`. -/
def modelComparisonIsoOfDerivedIso
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj I) :
    homologyGradedAlgebra Rc I ≅ homologyGradedAlgebra Rc K :=
  modelComparisonIsoOfStrictlyPerfect Rc K I (CochainComplex.realizeDerivedIso K I e) hbdd hterm

/-- **The self-Ext algebra of an object presented by a K-injective complex is the
composition-product algebra of any strictly perfect complex presenting the same object.**
`Stacks.SheafOfModules.extSelfComparisonIsoOfStrictlyPerfect` with its comparison morphism
supplied by `CochainComplex.realizeDerivedIso`: the hypothesis is now that `K` and `I` present
the same object of `D(O_X)`, not that a chain map between them has been chosen. -/
def extSelfComparisonIsoOfDerivedIso (A : DerivedCategory (StructureSheafModules Rc))
    (ε : DerivedCategory.Q.obj I ≅ A) (η : DerivedCategory.Q.obj K ≅ A) :
    extSelfGradedAlgebra Rc I A ε ≅ homologyGradedAlgebra Rc K :=
  extSelfComparisonIsoOfStrictlyPerfect Rc K I
    (CochainComplex.realizeDerivedIso K I (η.trans ε.symm)) hbdd hterm A ε

end DerivedIso

/-- **The self-Ext algebra of an object of `D(O_X)` admitting a strictly perfect model is the
composition-product algebra of that model.** `Stacks.SheafOfModules.selfExtAlgebra Rc A`, whose
degree-`n` piece is the Ext sheaf `Ext^n_{O_X}(A, A)` by definition and whose multiplication is
read off the canonical K-injective model `Stacks.SheafOfModules.kInjectiveModel`, is isomorphic as
a sheaf of graded `O_X`-algebras to `Stacks.SheafOfModules.homologyGradedAlgebra Rc K` for any
strictly perfect `K` with `Q(K) ≅ A`.

Neither side mentions a K-injective complex or a comparison morphism: this is
`Stacks.SheafOfModules.extSelfComparisonIsoOfStrictlyPerfect` with both of those discharged. -/
def selfExtAlgebraIsoOfStrictlyPerfect (A : DerivedCategory (StructureSheafModules Rc))
    (K : CochainComplex (StructureSheafModules Rc) ℤ)
    (hbdd : {i : ℤ | ¬ IsZero (K.X i)}.Finite)
    (hterm : ∀ i, RingedSite.IsFiniteFreeSummand (ringedSite Rc) (K.X i))
    (η : DerivedCategory.Q.obj K ≅ A) :
    selfExtAlgebra Rc A ≅ homologyGradedAlgebra Rc K :=
  haveI := isKInjective_kInjectiveModel Rc A
  extSelfComparisonIsoOfDerivedIso Rc K (kInjectiveModel Rc A) hbdd hterm A
    (kInjectiveModelIso Rc A) η

end Stacks.SheafOfModules

namespace Stacks.RegularSequence.KoszulChainData

open Stacks.Sites Stacks.SheafOfModules Stacks.RegularSequence

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology ↥X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (Opens.grothendieckTopology ↥X) CommRingCat.{u}]
  {r : ℕ}
  {A : SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X)
    (koszulFreeSheaf Rc r)}
  {φ : koszulFreeSheaf Rc r ⟶
    SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X) Rc)}
  (K : KoszulChainData.{u, u, u} A φ) [QuasiIso K.augmentation]

/-- **The object of `D(O♯)` that the Koszul complex presents**, namely the quotient `O♯/𝓘` when
the Koszul complex resolves it. -/
abbrev koszulObject : DerivedCategory (StructureSheafModules Rc) :=
  DerivedCategory.Q.obj (cochain Rc K)

/-- **The canonical K-injective model of the object the Koszul complex presents.** -/
abbrev kInjectiveComplex : CochainComplex (StructureSheafModules Rc) ℤ :=
  kInjectiveModel Rc (koszulObject Rc K)

/-- The canonical K-injective model of the Koszul object is K-injective. -/
instance isKInjective_kInjectiveComplex : (kInjectiveComplex Rc K).IsKInjective :=
  isKInjective_kInjectiveModel Rc (koszulObject Rc K)

/-- **The comparison of the Koszul complex with the canonical K-injective model**, a
quasi-isomorphism of complexes realizing the identification
`Stacks.SheafOfModules.kInjectiveModelIso`. -/
def kInjectiveComparison : cochain Rc K ⟶ kInjectiveComplex Rc K :=
  CochainComplex.realizeDerivedIso _ _ (kInjectiveModelIso Rc (koszulObject Rc K)).symm

/-- The comparison of the Koszul complex with its canonical K-injective model is a
quasi-isomorphism. -/
instance quasiIso_kInjectiveComparison : QuasiIso (kInjectiveComparison Rc K) :=
  CochainComplex.quasiIso_realizeDerivedIso _ _ _

/-- **The self-Ext algebra of a Koszul-regular quotient over the quotient, with the composition
product of a canonical K-injective model.**
`Stacks.RegularSequence.KoszulChainData.extSelfAlgebraOfKInjective` with the model, the comparison
morphism and the two strict-perfection hypotheses all supplied: its degree-`n` piece is the Ext
sheaf `Ext^n_{O♯}(O_X, O_X)` read as an `O_X`-module, and nothing but the Koszul chain datum
enters. -/
def selfExtAlgebraOfKInjectiveModel :=
  extSelfAlgebraOfKInjective Rc K (kInjectiveComplex Rc K) (kInjectiveComparison Rc K)
    (finite_not_isZero_cochain_X Rc K) (isFiniteFreeSummand_cochain_X Rc K)
    (koszulObject Rc K) (kInjectiveModelIso Rc (koszulObject Rc K))

/-- **The self-Ext algebra of a Koszul-regular quotient is an exterior algebra on its degree-one
piece, read with the composition product of a canonical K-injective model**, for an ideal sheaf
presented globally by a Koszul-regular sequence.

`Stacks.RegularSequence.KoszulChainData.isExteriorAlgebra_extSelfAlgebraOfKInjective` at the
canonical model, its hypothesis being
`Stacks.RegularSequence.KoszulChainData.isExteriorAlgebra_extSelfAlgebra` for the Koszul model. -/
theorem isExteriorAlgebra_selfExtAlgebraOfKInjectiveModel :
    SheafOfModules.GradedAlgebra.IsExteriorAlgebra (selfExtAlgebraOfKInjectiveModel Rc K)
      (𝟙 ((selfExtAlgebraOfKInjectiveModel Rc K).piece 1)) :=
  isExteriorAlgebra_extSelfAlgebraOfKInjective Rc K (kInjectiveComplex Rc K)
    (kInjectiveComparison Rc K) (finite_not_isZero_cochain_X Rc K)
    (isFiniteFreeSummand_cochain_X Rc K) (koszulObject Rc K)
    (kInjectiveModelIso Rc (koszulObject Rc K)) (isExteriorAlgebra_extSelfAlgebra Rc K)

/-- **The comparison map of Stacks 0BQY for the canonical K-injective model**, in every degree:

`⋀ⁱ_{O_X}(Ext¹_{O♯}(O_X, O_X)) ⟶ Extⁱ_{O♯}(O_X, O_X)`.

`Stacks.RegularSequence.KoszulChainData.extComparisonOfKInjective` with the model, the comparison
morphism and the strict-perfection hypotheses supplied. -/
def extComparisonOfKInjectiveModel (i : ℤ) :=
  extComparisonOfKInjective Rc K (kInjectiveComplex Rc K) (kInjectiveComparison Rc K)
    (finite_not_isZero_cochain_X Rc K) (isFiniteFreeSummand_cochain_X Rc K)
    (koszulObject Rc K) (kInjectiveModelIso Rc (koszulObject Rc K))
    (isExteriorAlgebra_extSelfAlgebra Rc K) i

/-- **The comparison of Stacks 0BQY is an isomorphism in every degree for the canonical
K-injective model**, for an ideal sheaf presented globally by a Koszul-regular sequence of `r`
sections. No model and no comparison morphism appear in the statement. -/
theorem isIso_extComparisonOfKInjectiveModel (i : ℤ) :
    IsIso (extComparisonOfKInjectiveModel Rc K i) :=
  isIso_extComparisonOfKInjective Rc K (kInjectiveComplex Rc K) (kInjectiveComparison Rc K)
    (finite_not_isZero_cochain_X Rc K) (isFiniteFreeSummand_cochain_X Rc K)
    (koszulObject Rc K) (kInjectiveModelIso Rc (koszulObject Rc K))
    (isExteriorAlgebra_extSelfAlgebra Rc K) i

end Stacks.RegularSequence.KoszulChainData

end
