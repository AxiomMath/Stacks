module

public import StacksFrontier.AlgebraicGeometry.Cohomology.GlobalGeneration.Stalks
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleTransport
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.StalkDerivedTensorTransport

/-!
# The derived stalk of an invertible object of `D(𝒪)` is invertible

Let `(X, 𝒪)` be a ringed space, read as the ringed site of its opens, and let `x : X`. The
derived stalk functor sends an invertible object of `D(𝒪)` to an invertible object of
`D(𝒪_x)`.

## Main results

* `Stacks.SheafOfModules.DerivedTensorStalk.derivedStalkUnitIso`: the derived stalk of the
  structure sheaf in degree zero is the stalk ring in degree zero.
* `Stacks.SheafOfModules.DerivedTensorStalk.isInvertible_derivedStalk_of_isInvertible`: the
  derived stalk functor preserves invertibility.

## Implementation notes

**No monoidal structure on the derived stalk functor is constructed, and none is needed.**
What makes an object invertible is a *single* isomorphism `K ⊗ K' ≅ 𝟙` once the ambient
category is braided (`CategoryTheory.MonoidalCategory.isInvertible_of_tensorIsoUnit`), so
transporting invertibility along a functor needs only the comparison
`F(A ⊗ B) ≅ F A ⊗ F B` at the one pair `(K, K')` and the unit isomorphism
`F(𝟙) ≅ 𝟙` — neither naturality nor the associativity and unitality squares of a
`CategoryTheory.Functor.Monoidal` structure. That reduction is
`CategoryTheory.MonoidalCategory.isInvertible_of_tensorComparison_of_braided`, and it is why
the comparison
`Stacks.SheafOfModules.DerivedTensorStalk.derivedTensorStalkNatIso` of Stacks 01CB — an
isomorphism of bifunctors on `D(𝒪)`, with no coherence attached — already suffices. In
particular `CategoryTheory.MonoidalCategory.IsInvertible.map`, which does consume a
`Functor.Monoidal` structure, is not the route taken here.

**The two monoidal structures are arguments, together with their comparisons.** `D(𝒪)` and
`D(𝒪_x)` each carry several inhabitants of "the" derived tensor product — the localized one
of [Stacks, Tag 0FPT] (`Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal`), the re-seated
one of `Stacks.SheafOfModules.derivedMonoidalStructure`, and at the stalk ring the chosen one
of `DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory` — and they are
isomorphic but not equal. Rather than privileging one, the statement takes each monoidal
structure as an instance argument together with the two data that identify it: a pairwise
comparison of its tensor product with
`CochainComplex.KFlatBifunctor.derivedBifunctor`, and an identification of its unit with the
structure sheaf (resp. the stalk ring) in degree zero. Every inhabitant named above supplies
both, so the statement applies to each of them without a further comparison of monoidal
structures. The comparisons are asked for pairwise, not as isomorphisms of bifunctors, since
that is all the proof uses and it is the weaker hypothesis.

**The unit.** `AlgebraicGeometry.stalkUnitLinearEquiv` is the stalk of the structure sheaf
regarded as a module over itself, and `CategoryTheory.Functor.mapDerivedCategorySingleFunctor`
moves it through the degree-zero inclusion into the derived categories. The stalk ring is the
`RingCat`-valued stalk throughout, which is the spelling
`AlgebraicGeometry.SheafOfModules.stalkFunctor` takes its modules over and the spelling
`Stacks.SheafOfModules.DerivedTensorStalk.derivedTensorStalkNatIso` is stated at.

## References

* [Stacks Project, Lemma 17.16.1 (Tag 01CB)](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 0FFN](https://stacks.math.columbia.edu/tag/0FFN)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace MonoidalCategory
open AlgebraicGeometry.SheafOfModules

universe u

namespace Stacks.SheafOfModules.DerivedTensorStalk

variable {X : TopCat.{u}}
  (R : CategoryTheory.Sheaf.{u, u, u, u + 1} (Opens.grothendieckTopology X) CommRingCat.{u})
  (x : X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)]
  [HasDerivedCategory.{u + 1}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R))]
  [HasDerivedCategory.{u + 1} (ModuleCat.{u} (stalkRing R x))]

attribute [local instance] Stacks.SheafOfModules.KFlatStalkCriterion.monoidalStalkModuleCat
  Stacks.SheafOfModules.KFlatStalkCriterion.monoidalPreadditiveStalkModuleCat
  stalkKFlatQ_isLocalization stalkKFlatQLeft_isLocalization

/-- The derived stalk functor `D(𝒪) ⥤ D(𝒪_x)`, induced by the exact stalk functor. -/
abbrev derivedStalk :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ⥤
      DerivedCategory (ModuleCat.{u} (stalkRing R x)) :=
  (stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).mapDerivedCategory

/-- **The derived stalk of the structure sheaf in degree zero is the stalk ring in degree
zero.** This is `AlgebraicGeometry.stalkUnitLinearEquiv` — the stalk of `𝒪` regarded as a
module over itself is `𝒪_x` regarded as a module over itself — moved through the degree-zero
inclusion by `CategoryTheory.Functor.mapDerivedCategorySingleFunctor`. -/
def derivedStalkUnitIso :
    (derivedStalk R x).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) 0).obj
            (_root_.SheafOfModules.unit
              (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R))) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} (stalkRing R x)) 0).obj
        (ModuleCat.of (stalkRing R x) (stalkRing R x)) :=
  letI := stalkFunctor_preservesFiniteColimits R x
  (((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)
      x).mapDerivedCategorySingleFunctor 0).app _) ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} (stalkRing R x)) 0).mapIso
      (AlgebraicGeometry.stalkUnitLinearEquiv
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).toModuleIso

/-- **The derived stalk functor sends an invertible object of `D(𝒪)` to an invertible object of
`D(𝒪_x)`.**

The two monoidal structures are explicit arguments, each with the two data that identify it:
`cmpX` and `cmpx` compare its tensor product, pairwise, with the derived tensor bifunctor of
[Stacks, Tag 06YU], and `unitX`, `unitx` identify its unit with the structure sheaf
(resp. the stalk ring) in degree zero. They are arguments rather than instances because a
caller has a *named* inhabitant in hand — `.choose` of an existence statement, at the stalk
ring — and instance search does not produce it.

The proof uses the comparison
`Stacks.SheafOfModules.DerivedTensorStalk.derivedTensorStalkObjIso` of Stacks 01CB at a single
pair of objects and nothing else: invertibility in a braided category is one-sided, so
`CategoryTheory.MonoidalCategory.isInvertible_of_tensorComparison_of_braided` asks for no
coherence. -/
theorem isInvertible_derivedStalk_of_isInvertible
    (mX : MonoidalCategory (DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R))))
    (mx : MonoidalCategory (DerivedCategory (ModuleCat.{u} (stalkRing R x))))
    (bx : letI := mx; BraidedCategory (DerivedCategory (ModuleCat.{u} (stalkRing R x))))
    (cmpX : letI := mX; ∀ A B : DerivedCategory
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)),
      A ⊗ B ≅ ((CochainComplex.KFlatBifunctor.derivedBifunctor
        (Stacks.SheafOfModules.Tensor.sheafTensor R)).obj A).obj B)
    (unitX : letI := mX; 𝟙_ (DerivedCategory
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R))) ≅
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) 0).obj
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)))
    (cmpx : letI := mx; ∀ A B : DerivedCategory (ModuleCat.{u} (stalkRing R x)),
      A ⊗ B ≅ ((CochainComplex.KFlatBifunctor.derivedBifunctor
        (curriedTensor (ModuleCat.{u} (stalkRing R x)))).obj A).obj B)
    (unitx : letI := mx; 𝟙_ (DerivedCategory (ModuleCat.{u} (stalkRing R x))) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} (stalkRing R x)) 0).obj
        (ModuleCat.of (stalkRing R x) (stalkRing R x)))
    (K : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)))
    (hK : letI := mX; CategoryTheory.MonoidalCategory.IsInvertible K) :
    letI := mx
    CategoryTheory.MonoidalCategory.IsInvertible ((derivedStalk R x).obj K) :=
  let := mX
  let := mx
  let := bx
  CategoryTheory.MonoidalCategory.isInvertible_of_tensorComparison_of_braided
    (derivedStalk R x)
    (fun A B => (derivedStalk R x).mapIso (cmpX A B) ≪≫
      derivedTensorStalkObjIso R x A B ≪≫ (cmpx _ _).symm)
    ((derivedStalk R x).mapIso unitX ≪≫ derivedStalkUnitIso R x ≪≫ unitx.symm) hK

end Stacks.SheafOfModules.DerivedTensorStalk

end
