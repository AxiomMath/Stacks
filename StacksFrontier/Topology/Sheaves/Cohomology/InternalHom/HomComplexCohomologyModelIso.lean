module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleAbelian
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.ExtAlgebraFromKInjective
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.HomComplexCohomologyModelComparison

/-!
# The two models of a self-Ext algebra are isomorphic as sheaves of graded algebras

Let `(X, O_X)` be a ringed space, let `K` be a strictly perfect complex of `O_X`-modules, let `I`
be a K-injective one and let `κ : K ⟶ I` be a quasi-isomorphism. The composition product makes
each of `H^*(SheafHom^•(K, K))` and `H^*(SheafHom^•(I, I))` a sheaf of graded `O_X`-algebras,
`Stacks.SheafOfModules.homologyGradedAlgebra`. This file proves that `κ` identifies the two: the
composite

`H^n(SheafHom^•(I, I)) ⟶ H^n(SheafHom^•(K, I)) ⟵ H^n(SheafHom^•(K, K))`

of precomposition with `κ` and the inverse of postcomposition with `κ` is a unital homomorphism
of sheaves of graded algebras, and an isomorphism in every degree.

Consequently the self-Ext algebra `Stacks.SheafOfModules.extSelfGradedAlgebra` of an object of
`D(O_X)` presented by `I`, whose pieces are the Ext sheaves `Ext^n_{O_X}(A, A)`, is isomorphic as
a sheaf of graded algebras to the Koszul-style model `homologyGradedAlgebra Rc K` computed from
any strictly perfect resolution. That is the model independence the two constructions were
missing.

## Main definitions

* `Stacks.SheafOfModules.modelComparison`: **the comparison of the two models**, a unital
  homomorphism `homologyGradedAlgebra Rc I ⟶ homologyGradedAlgebra Rc K`.
* `Stacks.SheafOfModules.modelComparisonIso`: that comparison as an isomorphism in the category
  of sheaves of graded algebras.
* `Stacks.SheafOfModules.extSelfComparison` and
  `Stacks.SheafOfModules.extSelfComparisonIso`: the same comparison read on the Ext sheaves,
  out of `Stacks.SheafOfModules.extSelfGradedAlgebra`.
* `Stacks.SheafOfModules.modelComparisonIsoOfStrictlyPerfect` and
  `Stacks.SheafOfModules.extSelfComparisonIsoOfStrictlyPerfect`: the same two isomorphisms with
  the invertibility of postcomposition discharged from the strict-perfection hypotheses, which
  is the form a consumer uses.

## Main results

* `Stacks.SheafOfModules.homologyMul_homologyMap_targetComparison`: **the two actions on
  `H^*(SheafHom^•(K, I))` agree through the comparison maps** — for `a` a class on
  `SheafHom^•(I, I)` and `c` a class on `SheafHom^•(K, K)`, the product of the image of `a` with
  `c` equals the product of `a` with the image of `c`. This is the associativity of the
  composition pairing read at the class of `κ`, and is what makes the comparison multiplicative.
* `Stacks.SheafOfModules.isIso_modelComparison_app` and
  `Stacks.SheafOfModules.isIso_extSelfComparison_app`: both comparisons are isomorphisms in
  every degree.

## Implementation notes

**The morphism-of-graded-algebras API used is the library's own.**
`SheafOfModules.GradedAlgebra.UnitalHom` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAlgebraPullback` is a degreewise morphism
of sheaves of modules preserving products of homogeneous local sections and the degree-zero
unit, with `UnitalHom.id`, `UnitalHom.comp` and -- for one which is an isomorphism in every
degree -- the two-sided inverse `UnitalHom.inverse`. That is exactly the notion wanted here, so
nothing new is introduced: the three algebra laws are *not* restated as separate equations.
`SheafOfModules.GradedAlgebra.Hom`, which does not ask for the unit, carries the `Category`
instance, and `UnitalHom.toHom` is what makes `modelComparisonIso` an isomorphism of that
category.

**Why the comparison is multiplicative.** Write `s` for the map `H^*(SheafHom^•(I, I)) ⟶
H^*(SheafHom^•(K, I))` induced by precomposition with `κ` and `t` for the one induced by
postcomposition; the comparison is `t⁻¹ ∘ s`. The two module laws
`Stacks.SheafOfModules.homologyMap_sourceComparison_homologyMul` and
`homologyMap_targetComparison_homologyMul` give `s(a · b) = a · s(b)` and `t(c · d) = t(c) · d`,
so multiplicativity of `t⁻¹ ∘ s` reduces, `t` being injective, to
`s(a) · c = a · t(c)` -- which is `homologyMul_homologyMap_targetComparison`. Unitality is the
two identities `s(1) = [κ] = t(1)`.

**The identity `s(a) · c = a · t(c)` is associativity at the class of `κ`.** Each comparison map is
multiplication by the class of `κ` -- on the right for `s`
(`Stacks.SheafOfModules.homologyMul_homologyClassOfHom`) and on the left for `t`
(`homologyClassOfHom_homologyMul`) -- so `s(a) · c = (a · [κ]) · c` and
`a · t(c) = a · ([κ] · c)`, and the two agree by `Stacks.SheafOfModules.homologyMul_assoc` for
the four complexes `(K, K, I, I)` at the degrees `(i, 0, j)`. The degree bookkeeping is the only
work: the two sides of that instance of associativity sit in degrees `(i + 0) + j` and
`i + (0 + j)`, and the two identifications of a comparison map with multiplication by `[κ]`
carry transports along `add_zero` and `zero_add`. `homologyMul_castHom_left` and
`homologyMul_castHom_right` move a transport of one argument out of the pairing, after which
every transport in sight lands in degree `i + j` and `SheafOfModules.heq_castHom` removes
them.

**What this does and does not say about [Stacks, Tag 0BQY].** It removes the model dependence
that the implementation notes of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.ExtAlgebraFromKInjective` record: the
algebra on the Ext sheaves built from a K-injective representative is identified with the one
built from a strictly perfect resolution, and the latter is the shape the Koszul development
computes -- `Stacks.RegularSequence.KoszulChainData.extSelfAlgebra` is
`Stacks.SheafOfModules.homologyGradedAlgebra` of the Koszul complex, descended along
`O_X ⟶ O_X/I`.

The comparison here lives over `O_X`, not over the quotient; pushing it through that descent of
scalars is `Stacks.RegularSequence.KoszulChainData.extSelfAlgebraModelIso` of
`StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulSelfExtAlgebraModelDescent`, which
conjugates it by `SheafOfModules.GradedAlgebra.UnitalHom.descend`.

Two things remain *not* done. This does not construct the intrinsic comparison out of
`Stacks.SheafOfModules.sheafExtProduct`, the derived composition product: both multiplications
compared here are chain-level composition products. And it does not glue the local statements of
`StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulSelfExtExteriorLocal`. **The note that
named the missing input for that gluing was wrong on both halves and is corrected here.** The
compatibility of the composition product with restriction to a slice site is not missing: it is
`AlgebraicGeometry.RingedSite.homologyGradedAlgebraOverHom` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CompositionAlgebraSliceRestriction`, a
unital homomorphism of sheaves of graded algebras invertible in every degree. And the pieces of
`Stacks.SheafOfModules.homologyGradedAlgebra` are the cohomology sheaves of the internal Hom
*complex*, which `Stacks.SheafOfModules.derivedSheafExtRestrictionIso` does not compare — that
compares `Stacks.SheafOfModules.derivedSheafExt`, the cohomology sheaf of the *derived* internal
Hom — so the pieces are carried by `AlgebraicGeometry.RingedSite.sheafHomHomologyOverIso`
instead. What the gluing is actually waiting on is recorded on the 0BQY attribute in
`KoszulSelfExtExteriorLocal`. No declaration here carries the 0BQY attribute.

## References

* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
* [Stacks Project, Tag 0A95](https://stacks.math.columbia.edu/tag/0A95)
* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Category Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

attribute [local implicit_reducible] CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive monoidalSpace' symmetricSpace'
  monoidalPreadditiveSpace' monoidalClosedSpace' preservesColimitTensorRightSpace'
  preservesFiniteColimitsTensorRight' preservesFiniteColimitsTensorLeft'

attribute [local instance] RingedSite.ringSheafSectionsCommRing
  RingedSite.presheafOfModulesMonoidalCategory
  RingedSite.curriedTensorPreservesZeroMorphisms
  RingedSite.curriedTensorObjPreservesZeroMorphisms

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-! ### Moving a degree transport out of the composition pairing -/

section Transport

variable (E F G : CochainComplex (StructureSheafModules Rc) ℤ)

/-- Transporting the first argument of the composition pairing along an equality of degrees is
transporting the product. -/
theorem homologyMul_castHom_left {i i' : ℤ} (h : i = i') (j : ℤ) (V : (Opens ↥X)ᵒᵖ)
    (x : ((homComplex Rc F G).homology i).val.obj V)
    (y : ((homComplex Rc E F).homology j).val.obj V) :
    (homologyMul Rc E F G i' j).app V
        (_root_.SheafOfModules.castHom (fun d => (homComplex Rc F G).homology d) h V x) y =
      _root_.SheafOfModules.castHom (fun d => (homComplex Rc E G).homology d)
        (by rw [h] : i + j = i' + j) V ((homologyMul Rc E F G i j).app V x y) := by
  subst h
  rfl

/-- Transporting the second argument of the composition pairing along an equality of degrees is
transporting the product. -/
theorem homologyMul_castHom_right (i : ℤ) {j j' : ℤ} (h : j = j') (V : (Opens ↥X)ᵒᵖ)
    (x : ((homComplex Rc F G).homology i).val.obj V)
    (y : ((homComplex Rc E F).homology j).val.obj V) :
    (homologyMul Rc E F G i j').app V x
        (_root_.SheafOfModules.castHom (fun d => (homComplex Rc E F).homology d) h V y) =
      _root_.SheafOfModules.castHom (fun d => (homComplex Rc E G).homology d)
        (by rw [h] : i + j = i + j') V ((homologyMul Rc E F G i j).app V x y) := by
  subst h
  rfl

end Transport

section Comparison

variable (K I : CochainComplex (StructureSheafModules Rc) ℤ) (κ : K ⟶ I)

/-! ### The two actions on `H^*(SheafHom^•(K, I))` agree through the comparison maps -/

/-- **The left action of `H^*(SheafHom^•(I, I))` and the right action of
`H^*(SheafHom^•(K, K))` on `H^*(SheafHom^•(K, I))` agree through the comparison maps:**

`cmp_s(a) · c = a · cmp_t(c)`

for `a` a class on `SheafHom^•(I, I)` and `c` a class on `SheafHom^•(K, K)`. Both comparison
maps are multiplication by the class of `κ`, so both sides are the triple product
`a · [κ] · c`, and the identity is `Stacks.SheafOfModules.homologyMul_assoc` for the four
complexes `(K, K, I, I)` at the degrees `(i, 0, j)`. The transports it carries -- along
`add_zero i`, `zero_add j` and `add_assoc i 0 j` -- all land in degree `i + j`, where
`SheafOfModules.heq_castHom` removes them.

This is what upgrades the two module laws of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.HomComplexCohomologyModelComparison` to
multiplicativity of the comparison of the two models. -/
theorem homologyMul_homologyMap_targetComparison (i j : ℤ) (V : (Opens ↥X)ᵒᵖ)
    (x : ((homComplex Rc I I).homology i).val.obj V)
    (z : ((homComplex Rc K K).homology j).val.obj V) :
    (homologyMul Rc K K I i j).app V
        ((HomologicalComplex.homologyMap (sourceComparison Rc K I κ) i).val.app V x) z =
      (homologyMul Rc K I I i j).app V x
        ((HomologicalComplex.homologyMap (targetComparison Rc K I κ) j).val.app V z) := by
  rw [← homologyMul_homologyClassOfHom Rc K I κ i V x,
    ← homologyClassOfHom_homologyMul Rc K I κ j V z,
    homologyMul_castHom_left Rc K K I (add_zero i) j V,
    homologyMul_castHom_right Rc K I I i (zero_add j) V]
  refine eq_of_heq ((_root_.SheafOfModules.heq_castHom
      (fun d => (homComplex Rc K I).homology d) _ V _).trans (HEq.trans ?_
    (_root_.SheafOfModules.heq_castHom (fun d => (homComplex Rc K I).homology d) _ V _).symm))
  exact (_root_.SheafOfModules.heq_castHom (fun d => (homComplex Rc K I).homology d)
      (add_assoc i 0 j) V _).symm.trans
    (heq_of_eq (homologyMul_assoc Rc K K I I i 0 j V x
      ((homologyClassOfHom Rc K I κ).val V) z))

/-! ### The comparison of the two models -/

section Model

variable [hT : ∀ n, IsIso (HomologicalComplex.homologyMap (targetComparison Rc K I κ) n)]

/-- The degree-`n` component of the comparison of the two models: precomposition with `κ`,
followed by the inverse of postcomposition with `κ`. -/
def modelComparisonApp (n : ℤ) : (endComplex Rc I).homology n ⟶ (endComplex Rc K).homology n :=
  HomologicalComplex.homologyMap (sourceComparison Rc K I κ) n ≫
    inv (HomologicalComplex.homologyMap (targetComparison Rc K I κ) n)

/-- The comparison on a local section: precomposition with `κ`, then the inverse of
postcomposition with `κ`. -/
theorem modelComparisonApp_val_app (n : ℤ) (U : (Opens ↥X)ᵒᵖ)
    (w : ((endComplex Rc I).homology n).val.obj U) :
    (modelComparisonApp Rc K I κ n).val.app U w =
      (inv (HomologicalComplex.homologyMap (targetComparison Rc K I κ) n)).val.app U
        ((HomologicalComplex.homologyMap (sourceComparison Rc K I κ) n).val.app U w) :=
  rfl

/-- The comparison sends `x` to `w` as soon as postcomposition sends `w` to the image of `x` under
precomposition. -/
private theorem modelComparisonApp_eq_of_targetComparison_eq (n : ℤ) (U : (Opens ↥X)ᵒᵖ)
    (x : ((endComplex Rc I).homology n).val.obj U) (w : ((endComplex Rc K).homology n).val.obj U)
    (h : (HomologicalComplex.homologyMap (targetComparison Rc K I κ) n).val.app U w =
      (HomologicalComplex.homologyMap (sourceComparison Rc K I κ) n).val.app U x) :
    (modelComparisonApp Rc K I κ n).val.app U x = w := by
  rw [modelComparisonApp_val_app, ← h]
  exact _root_.SheafOfModules.inv_val_app_val_app _ U _

/-- **The comparison of the two models is multiplicative.** Write `s` and `t` for the maps on
cohomology sheaves induced by precomposition and by postcomposition with `κ`, so that the
comparison is `t⁻¹ ∘ s`. Postcomposition is injective on cohomology sheaves, and applying `t` to
the right-hand side gives `t(t⁻¹ s(x)) · t⁻¹ s(y)` by
`homologyMap_targetComparison_homologyMul`, hence `s(x) · t⁻¹ s(y)`, hence
`x · t(t⁻¹ s(y)) = x · s(y)` by `homologyMul_homologyMap_targetComparison`, which is
`s(x · y)` by `homologyMap_sourceComparison_homologyMul`. -/
theorem modelComparisonApp_homologyMul (i j : ℤ) (U : (Opens ↥X)ᵒᵖ)
    (x : ((homComplex Rc I I).homology i).val.obj U)
    (y : ((homComplex Rc I I).homology j).val.obj U) :
    (modelComparisonApp Rc K I κ (i + j)).val.app U ((homologyMul Rc I I I i j).app U x y) =
      (homologyMul Rc K K K i j).app U ((modelComparisonApp Rc K I κ i).val.app U x)
        ((modelComparisonApp Rc K I κ j).val.app U y) := by
  refine modelComparisonApp_eq_of_targetComparison_eq Rc K I κ _ U _ _ ?_
  rw [modelComparisonApp_val_app, modelComparisonApp_val_app,
    homologyMap_targetComparison_homologyMul, _root_.SheafOfModules.val_app_inv_val_app,
    homologyMul_homologyMap_targetComparison, _root_.SheafOfModules.val_app_inv_val_app,
    homologyMap_sourceComparison_homologyMul]

/-- **The comparison of the two models is unital:** both comparison maps send the class of the
identity to the class of `κ`, so the inverse of the second undoes the first on the unit. -/
theorem modelComparisonApp_homologyOne (U : (Opens ↥X)ᵒᵖ) :
    (modelComparisonApp Rc K I κ 0).val.app U ((homologyOne Rc I).val U) =
      (homologyOne Rc K).val U :=
  modelComparisonApp_eq_of_targetComparison_eq Rc K I κ 0 U _ _
    ((homologyMap_targetComparison_homologyOne Rc K I κ U).trans
      (homologyMap_sourceComparison_homologyOne Rc K I κ U).symm)

/-- **The comparison of the two models of the self-Ext algebra**, as a unital homomorphism of
sheaves of graded algebras

`H^*(SheafHom^•(I, I)) ⟶ H^*(SheafHom^•(K, K))`.

Multiplicativity is `modelComparisonApp_homologyMul` and unitality
`modelComparisonApp_homologyOne`. Only invertibility of postcomposition is used, so nothing is
asked of `I` here; quasi-isomorphy of `κ` and K-injectivity of `I` enter in
`isIso_modelComparison_app`. -/
def modelComparison :
    _root_.SheafOfModules.GradedAlgebra.UnitalHom
      (homologyGradedAlgebra Rc I) (homologyGradedAlgebra Rc K) where
  app n := modelComparisonApp Rc K I κ n
  map_mul i j U x y := modelComparisonApp_homologyMul Rc K I κ i j U x y
  map_one U := modelComparisonApp_homologyOne Rc K I κ U

@[simp] theorem modelComparison_app (n : ℤ) :
    (modelComparison Rc K I κ).app n = modelComparisonApp Rc K I κ n :=
  rfl

/-- **The comparison of the two models is an isomorphism in every degree**, for `κ` a
quasi-isomorphism from a strictly perfect complex into a K-injective one: precomposition with
`κ` is then a quasi-isomorphism by Stacks 0A95, and postcomposition is invertible by
hypothesis. -/
instance isIso_modelComparison_app [QuasiIso κ] [I.IsKInjective] (n : ℤ) :
    IsIso ((modelComparison Rc K I κ).app n) := by
  have := quasiIso_sourceComparison Rc K I κ
  have h : IsIso (HomologicalComplex.homologyMap (sourceComparison Rc K I κ) n ≫
      inv (HomologicalComplex.homologyMap (targetComparison Rc K I κ) n)) := inferInstance
  exact h

/-- **The two models of the self-Ext algebra are isomorphic as sheaves of graded algebras.** The
comparison, read in the category of sheaves of graded algebras of
`SheafOfModules.GradedAlgebra.Hom`; its inverse is the degreewise inverse
`SheafOfModules.GradedAlgebra.UnitalHom.inverse`, which is again unital and multiplicative. -/
def modelComparisonIso [QuasiIso κ] [I.IsKInjective] :
    homologyGradedAlgebra Rc I ≅ homologyGradedAlgebra Rc K where
  hom := (modelComparison Rc K I κ).toHom
  inv := (modelComparison Rc K I κ).inverse.toHom
  hom_inv_id := by
    refine _root_.SheafOfModules.GradedAlgebra.Hom.ext fun n => ?_
    simpa using IsIso.hom_inv_id ((modelComparison Rc K I κ).app n)
  inv_hom_id := by
    refine _root_.SheafOfModules.GradedAlgebra.Hom.ext fun n => ?_
    simpa using IsIso.inv_hom_id ((modelComparison Rc K I κ).app n)

end Model

/-! ### Postcomposition with `κ` is invertible on cohomology sheaves -/

/-- Postcomposition with a quasi-isomorphism out of a strictly perfect complex is an isomorphism
on cohomology sheaves in every degree. This is the hypothesis the comparison of the two models
runs on, and it is Stacks 08JH read at `E = K`. -/
theorem isIso_homologyMap_targetComparison [QuasiIso κ]
    (hbdd : {i : ℤ | ¬ IsZero (K.X i)}.Finite)
    (hterm : ∀ i, RingedSite.IsFiniteFreeSummand (ringedSite Rc) (K.X i)) (n : ℤ) :
    IsIso (HomologicalComplex.homologyMap (targetComparison Rc K I κ) n) :=
  haveI := quasiIso_targetComparison Rc K I κ hbdd hterm
  inferInstance

end Comparison

/-! ### The self-Ext algebra of an object of `D(O_X)`, computed on a strictly perfect model -/

section ExtSelf

variable (K I : CochainComplex (StructureSheafModules Rc) ℤ) [I.IsKInjective] (κ : K ⟶ I)
  [QuasiIso κ] [∀ n, IsIso (HomologicalComplex.homologyMap (targetComparison Rc K I κ) n)]
  (A : DerivedCategory (StructureSheafModules Rc)) (ε : DerivedCategory.Q.obj I ≅ A)

/-- **The self-Ext algebra of `A` is the composition-product algebra of a strictly perfect model
of `A`.** The comparison of `Stacks.SheafOfModules.extSelfGradedAlgebra`, whose degree-`n` piece
is the Ext sheaf `Ext^n_{O_X}(A, A)` by definition, with the graded algebra on the cohomology
sheaves of `SheafHom^•(K, K)`: first the transport back onto `H^*(SheafHom^•(I, I))`, which is an
isomorphism of graded algebras by
`SheafOfModules.GradedAlgebra.ofPieceIsoUnitalHom`, then `modelComparison`. -/
def extSelfComparison :
    _root_.SheafOfModules.GradedAlgebra.UnitalHom
      (extSelfGradedAlgebra Rc I A ε) (homologyGradedAlgebra Rc K) :=
  (_root_.SheafOfModules.GradedAlgebra.ofPieceIsoUnitalHom (homologyGradedAlgebra Rc I)
    (derivedSheafExtIsoEndComplexHomology Rc I A ε)).comp (modelComparison Rc K I κ)

/-- **The comparison of the self-Ext algebra with the strictly perfect model is an isomorphism in
every degree.** -/
instance isIso_extSelfComparison_app (n : ℤ) :
    IsIso ((extSelfComparison Rc K I κ A ε).app n) :=
  haveI := isIso_modelComparison_app Rc K I κ n
  haveI := _root_.SheafOfModules.GradedAlgebra.isIso_ofPieceIsoUnitalHom_app
    (homologyGradedAlgebra Rc I) (derivedSheafExtIsoEndComplexHomology Rc I A ε) n
  _root_.SheafOfModules.GradedAlgebra.UnitalHom.isIso_comp_app
    (_root_.SheafOfModules.GradedAlgebra.ofPieceIsoUnitalHom (homologyGradedAlgebra Rc I)
      (derivedSheafExtIsoEndComplexHomology Rc I A ε)) (modelComparison Rc K I κ) n

/-- **The self-Ext algebra of an object of `D(O_X)` presented by a K-injective complex is
isomorphic, as a sheaf of graded algebras, to the composition-product algebra of any strictly
perfect model.** This is the model independence that the implementation notes of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.ExtAlgebraFromKInjective` declined to
assert. -/
def extSelfComparisonIso : extSelfGradedAlgebra Rc I A ε ≅ homologyGradedAlgebra Rc K where
  hom := (extSelfComparison Rc K I κ A ε).toHom
  inv := (extSelfComparison Rc K I κ A ε).inverse.toHom
  hom_inv_id := by
    refine _root_.SheafOfModules.GradedAlgebra.Hom.ext fun n => ?_
    simp
  inv_hom_id := by
    refine _root_.SheafOfModules.GradedAlgebra.Hom.ext fun n => ?_
    simp

end ExtSelf

/-! ### The two comparisons, from the strict-perfection hypotheses themselves -/

section OfStrictlyPerfect

variable (K I : CochainComplex (StructureSheafModules Rc) ℤ) [I.IsKInjective] (κ : K ⟶ I)
  [QuasiIso κ] (hbdd : {i : ℤ | ¬ IsZero (K.X i)}.Finite)
  (hterm : ∀ i, RingedSite.IsFiniteFreeSummand (ringedSite Rc) (K.X i))

/-- **The two models of the self-Ext algebra are isomorphic as sheaves of graded algebras**, for
`κ : K ⟶ I` a quasi-isomorphism from a strictly perfect complex into a K-injective one.
`modelComparisonIso` with the invertibility of postcomposition discharged by Stacks 08JH. -/
def modelComparisonIsoOfStrictlyPerfect :
    homologyGradedAlgebra Rc I ≅ homologyGradedAlgebra Rc K :=
  letI := isIso_homologyMap_targetComparison Rc K I κ hbdd hterm
  modelComparisonIso Rc K I κ

/-- **The self-Ext algebra of an object of `D(O_X)` is the composition-product algebra of a
strictly perfect model.** Let `I` be a K-injective complex presenting `A` by `ε : Q(I) ≅ A`, and
let `κ : K ⟶ I` be a quasi-isomorphism from a strictly perfect complex. Then
`Stacks.SheafOfModules.extSelfGradedAlgebra Rc I A ε`, whose degree-`n` piece is the Ext sheaf
`Ext^n_{O_X}(A, A)`, is isomorphic as a sheaf of graded `O_X`-algebras to
`Stacks.SheafOfModules.homologyGradedAlgebra Rc K`.

The right-hand side does not mention `I`, so this is also the independence of the construction
of `ExtAlgebraFromKInjective` from the K-injective representative, for every object admitting a
strictly perfect model. -/
def extSelfComparisonIsoOfStrictlyPerfect (A : DerivedCategory (StructureSheafModules Rc))
    (ε : DerivedCategory.Q.obj I ≅ A) :
    extSelfGradedAlgebra Rc I A ε ≅ homologyGradedAlgebra Rc K :=
  letI := isIso_homologyMap_targetComparison Rc K I κ hbdd hterm
  extSelfComparisonIso Rc K I κ A ε

end OfStrictlyPerfect

end Stacks.SheafOfModules

end
