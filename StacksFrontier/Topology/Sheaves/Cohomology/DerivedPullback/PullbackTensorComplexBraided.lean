module

public import StacksFrontier.Algebra.Homology.KoszulBraidingTransport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackSheafTensorBraided
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonBraided
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorMonoidalLift
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackComplexMap

/-!
# The pullback–tensor comparison of complexes is braided

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces.
`Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexNatIso` is the comparison

`f^*Tot(K ⊗_{𝒪_Y} L) ≅ Tot(f^*K ⊗_{𝒪_X} f^*L)`

of total tensor complexes, and `CochainComplex.koszulBraiding` is the commutativity constraint
of the Koszul symmetric monoidal structure on complexes of modules.  This file proves that the
comparison commutes with the two Koszul braidings.

This is the complex-level form of
`Stacks.PullbackTensorCoherence.pullbackTensorComparison_braiding`, the statement that the
comparison of [Stacks, Tag 01CD] commutes with the symmetry constraint of [Stacks, Tag 01CA].
It is what the commutativity clause of [Stacks, Tag 0FPT] for the derived pullback needs before
passing to the derived category.

## Main results

* `Stacks.Cohomology.DerivedPullbackTensor.comparisonAppIso_braiding`: **the degreewise
  comparison of [Stacks, Tag 01CD] commutes with the symmetry constraint**, at the re-seated
  spelling of the symmetry and in the form the summandwise computation consumes.
* `Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexIsoOfIsIso_koszulBraiding` and
  `pullbackTensorComplexNatIso_koszulBraiding`: **the comparison of total tensor complexes
  commutes with the Koszul braiding**, on the pointwise comparison and on the comparison as an
  isomorphism of bifunctors.

## Implementation notes

**Two spellings of the symmetry of `Mod(𝒪_Z)`.**  The Koszul braiding on
`CochainComplex (Mod(𝒪_Z)) ℤ` is built from the symmetry of `Mod(𝒪_Z)` for the monoidal
structure whose tensor product is `Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf`
*definitionally*, namely `SheafOfModules.monoidalCategorySheafTensor`; that is forced, because
only then is `K ⊗ L` the total complex `pullbackTensorComplexNatIso` compares.  The module-level
braiding statement, on the other hand, is proved at
`Stacks.PullbackGradedAlgebra.monoidalCategory`, whose tensor product is the tensor product
sheaf of [Stacks, Tag 01CA] on the nose.  The two monoidal structures agree on objects but not
on the whiskerings, so neither statement is available at the other spelling without a bridge.
That bridge is the library's own `Stacks.PullbackSheafTensor.braiding_eq_strict`: both braidings
are the braiding of the *localized* monoidal structure conjugated by the same isomorphism — by
`CategoryTheory.MonoidalCategory.reseatSymmetric_braiding` for the first and by definition
for the second.

**Why the module-level step goes through a generic lemma.**  `comparisonAppIso_braiding` is
`pullbackTensorComparison_braiding` moved across the bridge and rearranged.  Both operations are
performed by `inv_comp_map_comp_eq`, in which every object and morphism is a variable, so
that the passage between the two monoidal spellings is discharged by the conversion check at the
application site rather than by a rewrite inside a goal mentioning both.

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Cohomology.DerivedPullbackTensor

section Braided

attribute [local instance] monoidalModules symmetricModules monoidalPreadditiveModules
  monoidalClosedModules hasTensorModules monoidalComplexes
  modulePullback_preservesAntidiagonalCoproducts

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback

variable (Z : RingedSpace.{u, u})

/-- `Mod(𝒪_Z)` has a zero object, named at `C := Opens Z.carrier` so that the universe
constraint of `Stacks.SheafOfModules.Tensor.hasZeroObject` is written out; left to instance
search it is `max ?u ?v = u` with both unknown, and search stops. -/
local instance hasZeroObjectModules :
    HasZeroObject (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) :=
  Stacks.SheafOfModules.Tensor.hasZeroObject (C := Opens Z.carrier) Z.sheaf

/-- `𝒜 ⊗_{𝒪_Z} -` preserves the empty coproduct, one of the conditions for the graded tensor
product of `Mod(𝒪_Z)` to be monoidal. -/
local instance preservesEmptyTensorLeft :
    ∀ A : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z,
      PreservesColimit
        (Functor.empty.{0} (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z))
        ((curriedTensor (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z)).obj A) :=
  fun _ => inferInstance

/-- `- ⊗_{𝒪_Z} 𝒜` preserves the empty coproduct. -/
local instance preservesEmptyTensorRight :
    ∀ A : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z,
      PreservesColimit
        (Functor.empty.{0} (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z))
        ((curriedTensor
          (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z)).flip.obj A) :=
  fun _ => inferInstance

-- The left- and right-bracketed triple graded tensor products of `𝒪_Z`-modules are good, by
-- `Stacks.Cohomology.DerivedInternalHomPullback.hasGoodTensor₁₂TensorSpace` and
-- `hasGoodTensorTensor₂₃Space`, whose `instance` attributes are local to their module.
attribute [local instance]
  Stacks.Cohomology.DerivedInternalHomPullback.hasGoodTensor₁₂TensorSpace
  Stacks.Cohomology.DerivedInternalHomPullback.hasGoodTensorTensor₂₃Space

/-- A conjugation identity in a bare category: if `P` carries `b'` to a morphism which the
comparison isomorphisms `cA` and `cB` identify with `d'`, then `cA.inv ≫ P(b) ≫ cB.hom` is `d`,
for any `b` equal to `b'` and `d` equal to `d'`.

Every object and morphism here is a variable.  That is the point: the two equalities it takes
pass between two monoidal structures on one category, and keeping them as hypotheses of a
generic lemma leaves the conversion to the elaborator at the application site, instead of
asking a rewrite to find a pattern in a goal written at both spellings at once. -/
private theorem inv_comp_map_comp_eq {C D : Type*} [Category C] [Category D] (P : C ⥤ D)
    {AB BA : C} {PAB PBA : D} (cA : P.obj AB ≅ PAB) (cB : P.obj BA ≅ PBA)
    (b b' : AB ⟶ BA) (d d' : PAB ⟶ PBA) (hb : b = b') (hd : d = d')
    (key : P.map b' ≫ cB.hom = cA.hom ≫ d') :
    cA.inv ≫ P.map b ≫ cB.hom = d := by
  subst hb
  subst hd
  rw [key, cA.inv_hom_id_assoc]

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **The degreewise comparison of [Stacks, Tag 01CD] commutes with the symmetry constraint of
[Stacks, Tag 01CA]**, written at the re-seated spelling of the symmetry and solved for the
symmetry of `Mod(𝒪_X)`.  This is
`Stacks.PullbackTensorCoherence.pullbackTensorComparison_braiding` moved across
`Stacks.PullbackSheafTensor.braiding_eq_strict` on both ringed spaces; it is the shape
`CochainComplex.totalTensorComparison_koszulBraiding` asks for. -/
theorem comparisonAppIso_braiding
    (A B : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) :
    (comparisonAppIso f A B).inv ≫
        (StacksDraft.KFlat.modulePullback f).map (β_ A B).hom ≫
          (comparisonAppIso f B A).hom =
      (β_ ((StacksDraft.KFlat.modulePullback f).obj A)
        ((StacksDraft.KFlat.modulePullback f).obj B)).hom :=
  inv_comp_map_comp_eq (StacksDraft.KFlat.modulePullback f) (comparisonAppIso f A B)
    (comparisonAppIso f B A) _ _ _ _
    (Stacks.PullbackSheafTensor.braiding_eq_strict Y A B)
    (Stacks.PullbackSheafTensor.braiding_eq_strict X
      ((StacksDraft.KFlat.modulePullback f).obj A)
      ((StacksDraft.KFlat.modulePullback f).obj B))
    (Stacks.PullbackTensorCoherence.pullbackTensorComparison_braiding f A B)

/-- **The comparison of total tensor complexes commutes with the Koszul braiding.**  On the
summand of bidegree `(p, q)` both sides are the degreewise comparison composed with the
symmetry of `Mod(𝒪_X)` and scaled by the one Koszul sign `(-1)^(p*q)`, so the signs cancel and
what is left is `comparisonAppIso_braiding` at `(K^p, L^q)`. -/
theorem pullbackTensorComplexIsoOfIsIso_koszulBraiding
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    (pullbackTensorComplexIsoOfIsIso f K L).hom ≫
        (CochainComplex.koszulBraiding ((pullbackComplex f).obj K)
          ((pullbackComplex f).obj L)).hom =
      (pullbackComplex f).map (CochainComplex.koszulBraiding K L).hom ≫
        (pullbackTensorComplexIsoOfIsIso f L K).hom :=
  CochainComplex.totalTensorComparison_koszulBraiding
    (StacksDraft.KFlat.modulePullback f) (comparisonAppIso f)
    (comparisonAppIso_braiding f) (pullbackTensorComplexIsoOfIsIso f)
    (fun K L p q n h => ι_pullbackTensorComplexIsoOfIsIso_hom f K L p q n h)
    (fun K L p q n h => ι_pullbackTensorComplexIsoOfIsIso_inv f K L p q n h) K L

/-- **The comparison of total tensor complexes, as an isomorphism of bifunctors, commutes with
the Koszul braiding.**  This is
`pullbackTensorComplexIsoOfIsIso_koszulBraiding` read on
`Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexNatIso`, which is the form the
commutativity clause of [Stacks, Tag 0FPT] for the derived pullback uses. -/
theorem pullbackTensorComplexNatIso_koszulBraiding
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    (pullbackTensorComplexNatIso f).hom.app (K, L) ≫
        (CochainComplex.koszulBraiding ((pullbackComplex f).obj K)
          ((pullbackComplex f).obj L)).hom =
      (pullbackComplex f).map (CochainComplex.koszulBraiding K L).hom ≫
        (pullbackTensorComplexNatIso f).hom.app (L, K) := by
  rw [pullbackTensorComplexNatIso_hom_app, pullbackTensorComplexNatIso_hom_app]
  exact pullbackTensorComplexIsoOfIsIso_koszulBraiding f K L

end Braided

end Stacks.Cohomology.DerivedPullbackTensor

end
